"""Compare saved base, cursor-GES, and LBD-GES benchmark runs.

Run with ``python -m tests.compare_benchmarks``. This script reads only result
files referenced by each benchmark index and never invokes the SAT solver.
"""

import argparse
import csv
import math
import statistics
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

from tests import plot
from tests.benchmark import PROJECT_ROOT, load_saved_results, safe_filename
from tests.run import atomic_write_json


DEFAULT_OUTPUT = PROJECT_ROOT / "benchmark_comparison"
METHOD_ORDER = ("base", "ges", "ges_lbd")
METHOD_LABELS = {
    "base": "Base",
    "ges": "GES (cursor)",
    "ges_lbd": "GES (LBD)",
}
PAIRWISE_METHODS = (
    ("base", "ges"),
    ("base", "ges_lbd"),
    ("ges", "ges_lbd"),
)
CSV_FIELDS = (
    "family",
    "problem",
    "base_status",
    "base_wall_seconds",
    "ges_status",
    "ges_wall_seconds",
    "ges_lbd_status",
    "ges_lbd_wall_seconds",
    "ges_minus_base_seconds",
    "ges_speedup_vs_base",
    "ges_lbd_minus_base_seconds",
    "ges_lbd_speedup_vs_base",
    "ges_lbd_minus_ges_seconds",
    "ges_lbd_speedup_vs_ges",
    "all_completed",
    "fastest_completed_method",
)


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compare indexed base, cursor-GES, and LBD-GES benchmark results."
    )
    parser.add_argument(
        "--base", type=Path, default=PROJECT_ROOT / "benchmark_result_base"
    )
    parser.add_argument(
        "--ges", type=Path, default=PROJECT_ROOT / "benchmark_result_ges"
    )
    parser.add_argument(
        "--ges-lbd", type=Path, default=PROJECT_ROOT / "benchmark_result_ges_lbd"
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args(argv)


def indexed_result_map(output: Path) -> Tuple[Dict[str, Any], Dict[str, Dict[str, Any]]]:
    index, results = load_saved_results(output.resolve())
    by_problem: Dict[str, Dict[str, Any]] = {}
    for result in results:
        problem = result.get("problem")
        if not isinstance(problem, str) or not problem:
            raise SystemExit("saved result has no problem key in {}".format(output))
        if problem in by_problem:
            raise SystemExit("duplicate saved result for {} in {}".format(problem, output))
        by_problem[problem] = result
    return index, by_problem


def result_wall_seconds(result: Optional[Mapping[str, Any]]) -> Optional[float]:
    if result is None or result.get("status") == "skipped":
        return None
    value = result.get("wall_seconds")
    if not isinstance(value, (int, float)):
        return None
    seconds = float(value)
    return seconds if math.isfinite(seconds) and seconds >= 0 else None


def completed_wall_seconds(result: Optional[Mapping[str, Any]]) -> Optional[float]:
    if result is None or result.get("status") != "completed":
        return None
    return result_wall_seconds(result)


def format_number(value: Optional[float]) -> str:
    return "" if value is None else "{:.9f}".format(value)


def problem_families(
    methods: Mapping[str, Mapping[str, Mapping[str, Any]]]
) -> Dict[str, str]:
    families: Dict[str, str] = {}
    all_problems = sorted(
        set().union(*(set(results) for results in methods.values()))
    )
    for problem in all_problems:
        observed = {
            str(results[problem]["family"])
            for results in methods.values()
            if problem in results and results[problem].get("family")
        }
        if len(observed) != 1:
            raise SystemExit(
                "inconsistent or missing family for {}: {}".format(
                    problem, sorted(observed)
                )
            )
        families[problem] = next(iter(observed))
    return families


def comparison_rows(
    methods: Mapping[str, Mapping[str, Mapping[str, Any]]],
    families: Mapping[str, str],
) -> List[Dict[str, str]]:
    rows: List[Dict[str, str]] = []
    for problem in sorted(families, key=lambda item: (families[item], item)):
        row = {"family": families[problem], "problem": problem}
        completed_times: Dict[str, float] = {}
        for method in METHOD_ORDER:
            result = methods[method].get(problem)
            status = str(result.get("status", "missing")) if result else "missing"
            wall_seconds = result_wall_seconds(result)
            row["{}_status".format(method)] = status
            row["{}_wall_seconds".format(method)] = format_number(wall_seconds)
            completed = completed_wall_seconds(result)
            if completed is not None:
                completed_times[method] = completed

        for first, second in PAIRWISE_METHODS:
            first_time = completed_times.get(first)
            second_time = completed_times.get(second)
            delta = (
                second_time - first_time
                if first_time is not None and second_time is not None
                else None
            )
            speedup = (
                first_time / second_time
                if first_time is not None
                and second_time is not None
                and second_time > 0
                else None
            )
            row["{}_minus_{}_seconds".format(second, first)] = format_number(delta)
            row["{}_speedup_vs_{}".format(second, first)] = format_number(speedup)

        row["all_completed"] = str(len(completed_times) == len(METHOD_ORDER)).lower()
        row["fastest_completed_method"] = (
            min(completed_times, key=lambda method: (completed_times[method], method))
            if completed_times
            else ""
        )
        rows.append(row)
    return rows


def method_summary(
    results: Mapping[str, Mapping[str, Any]], problems: Sequence[str]
) -> Dict[str, Any]:
    statuses = Counter(
        str(results[problem].get("status", "missing"))
        if problem in results
        else "missing"
        for problem in problems
    )
    completed_times = [
        seconds
        for problem in problems
        for seconds in [completed_wall_seconds(results.get(problem))]
        if seconds is not None
    ]
    return {
        "problems": len(problems),
        "statuses": dict(sorted(statuses.items())),
        "completed_wall_seconds": {
            "total": sum(completed_times),
            "mean": statistics.fmean(completed_times) if completed_times else None,
            "median": statistics.median(completed_times) if completed_times else None,
        },
    }


def pairwise_summary(
    methods: Mapping[str, Mapping[str, Mapping[str, Any]]],
    problems: Sequence[str],
    first: str,
    second: str,
) -> Dict[str, Any]:
    deltas: List[float] = []
    ratios: List[float] = []
    first_faster = 0
    second_faster = 0
    tied = 0
    for problem in problems:
        first_time = completed_wall_seconds(methods[first].get(problem))
        second_time = completed_wall_seconds(methods[second].get(problem))
        if first_time is None or second_time is None:
            continue
        delta = second_time - first_time
        deltas.append(delta)
        if first_time > 0 and second_time > 0:
            ratios.append(first_time / second_time)
        if math.isclose(first_time, second_time, rel_tol=1e-9, abs_tol=1e-9):
            tied += 1
        elif first_time < second_time:
            first_faster += 1
        else:
            second_faster += 1

    return {
        "first": first,
        "second": second,
        "comparable_completed_problems": len(deltas),
        "first_faster": first_faster,
        "second_faster": second_faster,
        "tied": tied,
        "second_minus_first_seconds": {
            "mean": statistics.fmean(deltas) if deltas else None,
            "median": statistics.median(deltas) if deltas else None,
        },
        "second_speedup_vs_first": {
            "geometric_mean": (
                math.exp(statistics.fmean(math.log(ratio) for ratio in ratios))
                if ratios
                else None
            )
        },
    }


def comparison_summary(
    methods: Mapping[str, Mapping[str, Mapping[str, Any]]],
    families: Mapping[str, str],
    source_paths: Mapping[str, Path],
) -> Dict[str, Any]:
    grouped: Dict[str, List[str]] = defaultdict(list)
    for problem, family in families.items():
        grouped[family].append(problem)
    grouped["overall"] = list(families)

    groups: Dict[str, Any] = {}
    for family, problems in sorted(grouped.items()):
        ordered_problems = sorted(problems)
        groups[family] = {
            "methods": {
                method: method_summary(methods[method], ordered_problems)
                for method in METHOD_ORDER
            },
            "pairwise": {
                "{}_vs_{}".format(second, first): pairwise_summary(
                    methods, ordered_problems, first, second
                )
                for first, second in PAIRWISE_METHODS
            },
        }

    return {
        "runtime_comparison_policy": {
            "comparable_status": "completed in both methods",
            "delta_seconds": "second method minus first method; negative is faster",
            "speedup": "first runtime divided by second runtime; greater than 1 is faster",
        },
        "sources": {
            method: {
                "label": METHOD_LABELS[method],
                "path": str(source_paths[method]),
            }
            for method in METHOD_ORDER
        },
        "groups": groups,
    }


def family_timeout(indexes: Mapping[str, Mapping[str, Any]]) -> Optional[float]:
    timeouts: List[float] = []
    for index in indexes.values():
        limits = index.get("limits", {})
        value = limits.get("family_timeout_seconds") if isinstance(limits, dict) else None
        if isinstance(value, (int, float)) and math.isfinite(float(value)) and value > 0:
            timeouts.append(float(value))
    return max(timeouts) if timeouts else None


def plot_overlaid_cactus(
    plt,
    name: str,
    method_results: Mapping[str, Sequence[Mapping[str, Any]]],
    destination: Path,
    timeout_seconds: Optional[float],
) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    figure, axis = plt.subplots(figsize=(10, 7))
    maximum_solved = 0
    maximum_time = timeout_seconds or 0.0

    for method in METHOD_ORDER:
        results = method_results[method]
        solved_counts, wall_times = plot.cactus_coordinates(results)
        solved = solved_counts[-1]
        maximum_solved = max(maximum_solved, solved)
        maximum_time = max(maximum_time, wall_times[-1])
        if timeout_seconds is not None and timeout_seconds > wall_times[-1]:
            solved_counts.append(solved)
            wall_times.append(timeout_seconds)
        axis.step(
            solved_counts,
            wall_times,
            where="post",
            linewidth=2,
            label="{} ({}/{})".format(METHOD_LABELS[method], solved, len(results)),
        )

    if maximum_solved == 0:
        axis.text(
            0.5,
            0.5,
            "No instances solved",
            transform=axis.transAxes,
            ha="center",
            va="center",
            fontsize=12,
        )

    axis.set_xlim(0, max(maximum_solved, 1))
    axis.set_ylim(0, maximum_time if maximum_time > 0 else 1)
    axis.set_xlabel("number of solved instances")
    axis.set_ylabel("individual wall runtime (seconds)")
    axis.set_title("{} — benchmark comparison".format(name))
    axis.legend(loc="lower right")
    axis.grid(alpha=0.25)
    figure.tight_layout()
    figure.savefig(destination, dpi=150, bbox_inches="tight")
    plt.close(figure)


def write_runtime_csv(destination: Path, rows: Sequence[Mapping[str, str]]) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open("w", encoding="utf-8", newline="") as output:
        writer = csv.DictWriter(output, fieldnames=CSV_FIELDS)
        writer.writeheader()
        writer.writerows(rows)


def compare(args: argparse.Namespace) -> int:
    source_paths = {
        "base": args.base.resolve(),
        "ges": args.ges.resolve(),
        "ges_lbd": args.ges_lbd.resolve(),
    }
    indexes: Dict[str, Dict[str, Any]] = {}
    methods: Dict[str, Dict[str, Dict[str, Any]]] = {}
    for method in METHOD_ORDER:
        indexes[method], methods[method] = indexed_result_map(source_paths[method])

    families = problem_families(methods)
    grouped_problems: Dict[str, List[str]] = defaultdict(list)
    for problem, family in families.items():
        grouped_problems[family].append(problem)

    output = args.output.resolve()
    timeout_seconds = family_timeout(indexes)
    pyplot = plot.import_pyplot()
    plot_paths: Dict[str, str] = {}
    plot_groups = dict(grouped_problems)
    plot_groups["overall"] = list(families)
    for family, problems in sorted(plot_groups.items()):
        destination = output / "plots" / "cactus" / (safe_filename(family) + ".png")
        plot_overlaid_cactus(
            pyplot,
            family,
            {
                method: [
                    methods[method][problem]
                    for problem in problems
                    if problem in methods[method]
                ]
                for method in METHOD_ORDER
            },
            destination,
            timeout_seconds,
        )
        plot_paths[family] = str(destination.relative_to(output))
        print("Comparison cactus plot for {}: {}".format(family, destination), flush=True)

    rows = comparison_rows(methods, families)
    csv_path = output / "runtime_differences.csv"
    write_runtime_csv(csv_path, rows)
    summary = comparison_summary(methods, families, source_paths)
    summary["cactus_plots"] = plot_paths
    summary["runtime_differences"] = str(csv_path.relative_to(output))
    atomic_write_json(output / "summary.json", summary)

    print("Runtime differences: {}".format(csv_path), flush=True)
    print("Comparison summary: {}".format(output / "summary.json"), flush=True)
    return 0


def main(argv: Optional[Sequence[str]] = None) -> int:
    return compare(parse_args(argv))


if __name__ == "__main__":
    raise SystemExit(main())
