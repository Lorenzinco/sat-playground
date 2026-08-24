"""Corpus discovery, aggregation, persistence, and CLI orchestration.

The repository's ``main.py`` calls this module by default. It can also be run
as ``python -m tests.benchmark``.
"""

import argparse
import json
import math
import re
import statistics
import time
import zipfile
from collections import defaultdict
from contextlib import ExitStack
from datetime import datetime, timezone
from functools import lru_cache
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple
from xml.etree import ElementTree

from . import plot
from .run import (
    COUNTER_FIELDS,
    RUNTIME_METHODS,
    atomic_write_json,
    result_base,
    run_problem_subprocess,
    run_worker,
)


PROJECT_ROOT = Path(__file__).resolve().parents[1]
TESTS_ROOT = PROJECT_ROOT / "tests"
BENCHMARK_ROOT = TESTS_ROOT / "benchmark"
REFERENCE_SUMMARY = BENCHMARK_ROOT / "summary-july-2024.ods"
DEFAULT_OUTPUT = PROJECT_ROOT / "benchmark_results"
MAX_FAMILY_TIMEOUT_SECONDS = 500.0
METHOD_ORDER = ("base", "ges", "ges_always", "ges_lbd", "ges_random", "ges_par", "ges_vsids")
METHOD_LABELS = {
    "base": "Base (no inprocessing)",
    "ges": "GES (cursor)",
    "ges_always": "GES (always)",
    "ges_lbd": "GES (LBD)",
    "ges_random": "GES (random)",
    "ges_par": "GES (parallel)",
    "ges_vsids": "GES (VSIDS)",
}
REFERENCE_SHEET_FAMILIES = {
    "TSEITIN-GRID": "tseitin-grid",
    "4-REGULAR": "tseitin-4-regular",
    "6-REGULAR": "tseitin-6-regular",
    "RANDOM-XOR": "randkxor",
    "INTERVALS": "intervals",
}
ODS_NAMESPACES = {
    "table": "urn:oasis:names:tc:opendocument:xmlns:table:1.0",
    "text": "urn:oasis:names:tc:opendocument:xmlns:text:1.0",
}
PROCESS_CHOICES = ("bva", "bve", "ges", "ges_always", "ges_lbd", "ges_par", "ges_random", "ges_vsids", "subsumption")
STATUS_NAMES = ("completed", "incorrect", "timeout", "error", "skipped")


def import_tqdm():
    """Lazy Rich factory; retain the historical name for progress mocks."""
    try:
        from .benchmark_progress import BenchmarkProgress
    except ImportError as error:
        raise SystemExit(
            'Benchmark progress requires rich; install with python -m pip install ".[benchmark]"'
        ) from error
    return BenchmarkProgress()


def progress_bar(tqdm, total: int, description: str, position: int):
    return tqdm(
        total=total, desc=description, position=position, leave=position == 0,
        disable=None, unit="item", dynamic_ncols=True,
    )


def progress_status(counts, stage, method, problem, remaining, pending_budget):
    # The last deadline sample is conservative, not a wall-clock completion ETA.
    return {
        "stage": stage, "method": method, "problem": problem,
        "solved": counts["completed"], "timeout": counts["timeout"],
        "skipped": counts["skipped"], "incorrect": counts["incorrect"],
        "error": counts["error"],
        "method-family budget remaining (last sample)": "{:.1f}s".format(remaining),
        "solver budget upper bound (not ETA; excludes plots/overhead)": "{:.1f}s".format(
            remaining + pending_budget
        ),
    }


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Benchmark seven configurations (baseline and all six GES variants), family by family under tests/benchmark."
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--family-timeout", type=float, default=MAX_FAMILY_TIMEOUT_SECONDS,
        help=(
            "Independent wall-clock budget for each configuration on each family "
            "(0–{0:g}s; default: {0:g}s).".format(MAX_FAMILY_TIMEOUT_SECONDS)
        ),
    )
    parser.add_argument(
        "--plot-only", action="store_true",
        help="Regenerate family and overall overlays from saved matrix indexes without solving.",
    )
    parser.add_argument("--algorithm", choices=("cdcl", "dpll"), default="cdcl")
    parser.add_argument(
        "--implication-point", choices=("uip", "dip"), default="dip"
    )
    parser.add_argument("--heuristics", choices=("vsids", "random"), default="vsids")
    parser.add_argument(
        "--preprocess", nargs="*", choices=PROCESS_CHOICES, default=[],
        help="Preprocessing techniques (ges_par runs parallel GES).",
    )
    parser.add_argument(
        "--inprocessing", nargs="*", choices=PROCESS_CHOICES, default=[],
        help="Legacy parser compatibility only; non-empty values are not allowed for the fixed matrix.",
    )

    parser.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--worker-input", type=Path, help=argparse.SUPPRESS)
    parser.add_argument("--worker-output", type=Path, help=argparse.SUPPRESS)
    parser.add_argument("--worker-config", help=argparse.SUPPRESS)
    parser.add_argument("--worker-metadata", help=argparse.SUPPRESS)

    args = parser.parse_args(argv)
    if not math.isfinite(args.family_timeout) or args.family_timeout < 0:
        parser.error("--family-timeout must be finite and non-negative")
    if args.family_timeout > MAX_FAMILY_TIMEOUT_SECONDS:
        parser.error(
            "--family-timeout cannot exceed {:g} seconds".format(MAX_FAMILY_TIMEOUT_SECONDS)
        )
    return args


def _ods_row_values(row: ElementTree.Element, limit: int) -> List[str]:
    values: List[str] = []
    repeat_attribute = "{{{}}}number-columns-repeated".format(ODS_NAMESPACES["table"])
    for cell in row.findall("table:table-cell", ODS_NAMESPACES):
        value = " ".join(
            "".join(paragraph.itertext())
            for paragraph in cell.findall("text:p", ODS_NAMESPACES)
        ).strip()
        repeat = int(cell.attrib.get(repeat_attribute, "1"))
        values.extend([value] * min(repeat, limit - len(values)))
        if len(values) >= limit:
            break
    values.extend([""] * (limit - len(values)))
    return values


@lru_cache(maxsize=1)
def reference_statuses() -> Dict[str, str]:
    """Read explicit reference classifications only, when the optional ODS exists."""
    if not REFERENCE_SUMMARY.is_file():
        return {}
    with zipfile.ZipFile(REFERENCE_SUMMARY) as archive:
        root = ElementTree.fromstring(archive.read("content.xml"))
    table_name_attribute = "{{{}}}name".format(ODS_NAMESPACES["table"])
    status_names = {"SATISFIABLE": "sat", "UNSATISFIABLE": "unsat"}
    statuses: Dict[str, str] = {}
    for table in root.findall(".//table:table", ODS_NAMESPACES):
        family = REFERENCE_SHEET_FAMILIES.get(table.attrib.get(table_name_attribute, ""))
        if family is None:
            continue
        for row in table.findall("table:table-row", ODS_NAMESPACES):
            cells = _ods_row_values(row, 12)
            suffix = ".res.xmaple"
            if not cells[0].endswith(suffix):
                continue
            key = "{}/{}".format(family, cells[0][:-len(suffix)])
            resolved = {
                status_names[status]
                for status in (cells[1], cells[11]) if status in status_names
            }
            previous = statuses.get(key, "unknown")
            if previous != "unknown":
                resolved.add(previous)
            if len(resolved) > 1:
                raise ValueError("conflicting reference statuses for {}".format(key))
            statuses[key] = next(iter(resolved)) if resolved else "unknown"
    return statuses


def expected_status(path: Path) -> str:
    return reference_statuses().get(path.relative_to(BENCHMARK_ROOT).as_posix(), "unknown")


def problem_family(path: Path) -> str:
    relative = path.relative_to(BENCHMARK_ROOT)
    if len(relative.parts) < 2:
        raise ValueError("benchmark problems must be inside a family directory: {}".format(path))
    return relative.parts[0]


def problem_key(path: Path) -> str:
    return path.relative_to(PROJECT_ROOT).as_posix()


def problem_metadata(path: Path) -> Dict[str, str]:
    return {
        "problem": problem_key(path),
        "family": problem_family(path),
        "expected": expected_status(path),
    }


def group_problems_by_family(problems: Iterable[Path]) -> Dict[str, List[Path]]:
    grouped: Dict[str, List[Path]] = defaultdict(list)
    for path in sorted(problems):
        grouped[problem_family(path)].append(path)
    return {family: grouped[family] for family in sorted(grouped)}


def discover_problems() -> List[Path]:
    """Discover immediate family directories, recursively sorting their CNFs."""
    if not BENCHMARK_ROOT.is_dir():
        return []
    return [
        path
        for family in sorted(BENCHMARK_ROOT.iterdir()) if family.is_dir()
        for path in sorted(family.rglob("*.cnf")) if path.is_file()
    ]


def solver_config(args: argparse.Namespace, method: str = "base") -> Dict[str, Any]:
    if method not in METHOD_ORDER:
        raise ValueError("unknown benchmark method: {}".format(method))
    return {
        "algorithm": args.algorithm,
        "implication_point": args.implication_point,
        "heuristics": args.heuristics,
        "preprocess": list(args.preprocess),
        "inprocessing": [] if method == "base" else [method],
    }


def safe_filename(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", name).strip("_") or "aggregate"


def load_saved_results(output: Path) -> Tuple[Dict[str, Any], List[Dict[str, Any]]]:
    """Load only result files referenced by the benchmark index."""
    index_path = output / "index.json"
    if not index_path.is_file():
        raise SystemExit("benchmark index not found: {}".format(index_path))

    with index_path.open("r", encoding="utf-8") as source:
        index = json.load(source)
    if not isinstance(index, dict) or not isinstance(index.get("problems"), dict):
        raise SystemExit("invalid benchmark index: {}".format(index_path))

    results: List[Dict[str, Any]] = []
    for problem, entry in sorted(index["problems"].items()):
        if not isinstance(entry, dict) or not isinstance(entry.get("result"), str):
            raise SystemExit("missing result path for {} in {}".format(problem, index_path))
        result_path = output / entry["result"]
        if not result_path.is_file():
            raise SystemExit("saved result not found: {}".format(result_path))
        with result_path.open("r", encoding="utf-8") as source:
            result = json.load(source)
        if not isinstance(result, dict):
            raise SystemExit("invalid saved result: {}".format(result_path))
        results.append(result)

    return index, results


def result_json_path(output: Path, path: Path) -> Path:
    relative = path.relative_to(TESTS_ROOT).with_suffix(".json")
    return output / "problems" / relative


def result_plot_path(output: Path, result: Mapping[str, Any]) -> Path:
    relative = Path(str(result["problem"])).relative_to("tests").with_suffix(".png")
    return output / "plots" / "problems" / relative


def mean_mapping(
    results: Sequence[Mapping[str, Any]], field: str, keys: Iterable[str]
) -> Dict[str, float]:
    completed = [result for result in results if result.get("status") == "completed"]
    return {
        key: statistics.fmean(
            float(result.get(field, {}).get(key, 0.0)) for result in completed
        )
        if completed
        else 0.0
        for key in keys
    }


def aggregate_results(
    name: str, results: Sequence[Mapping[str, Any]]
) -> Dict[str, Any]:
    statuses = {
        status: sum(result.get("status") == status for result in results)
        for status in STATUS_NAMES
    }
    completed = [result for result in results if result.get("status") == "completed"]
    wall_average = (
        statistics.fmean(float(result.get("wall_seconds", 0.0)) for result in completed)
        if completed
        else 0.0
    )
    return {
        "name": name,
        "problems": len(results),
        "statuses": statuses,
        "completed_problem_keys": [result["problem"] for result in completed],
        "average_wall_seconds": wall_average,
        "average_runtime_seconds": mean_mapping(
            results, "runtime_seconds", (label for label, _ in RUNTIME_METHODS)
        ),
        "average_counters": mean_mapping(results, "counters", COUNTER_FIELDS),
    }


def write_index(
    output: Path,
    started_at: str,
    config: Mapping[str, Any],
    args: argparse.Namespace,
    results: Sequence[Mapping[str, Any]],
    aggregates: Mapping[str, Mapping[str, Any]],
) -> None:
    problem_index = {
        str(result["problem"]): {
            "result": str(
                result_json_path(output, PROJECT_ROOT / str(result["problem"])).relative_to(
                    output
                )
            ),
            "plot": str(result_plot_path(output, result).relative_to(output)),
            "status": result["status"],
            "family": result["family"],
        }
        for result in results
    }
    index = {
        "started_at": started_at,
        "finished_at": datetime.now(timezone.utc).isoformat(),
        "solver_configuration": dict(config),
        "limits": {
            "family_timeout_seconds": args.family_timeout,
        },
        "problems": problem_index,
        "aggregates": {
            name: {
                "summary": "aggregates/{}.json".format(safe_filename(name)),
                "plot": "plots/aggregates/{}.png".format(safe_filename(name)),
            }
            for name in aggregates
        },
    }
    atomic_write_json(output / "index.json", index)


def plot_matrix_cactus(
    pyplot,
    output: Path,
    name: str,
    methods: Mapping[str, Sequence[Mapping[str, Any]]],
    timeout_seconds: float,
) -> str:
    destination = output / "plots" / "cactus" / (safe_filename(name) + ".png")
    plot.plot_comparison_cactus(
        pyplot, name,
        {METHOD_LABELS[method]: methods[method] for method in METHOD_ORDER},
        destination, timeout_seconds,
    )
    return destination.relative_to(output).as_posix()


def write_matrix_index(
    output: Path,
    started_at: str,
    args: argparse.Namespace,
    methods: Mapping[str, Sequence[Mapping[str, Any]]],
    completed_families: Sequence[str],
    cactus_plots: Mapping[str, str],
) -> None:
    summary = {
        "started_at": started_at,
        "updated_at": datetime.now(timezone.utc).isoformat(),
        "limits": {"family_timeout_seconds": args.family_timeout},
        "method_order": list(METHOD_ORDER),
        "completed_families": list(completed_families),
        "methods": {
            method: {
                "label": METHOD_LABELS[method],
                "path": method,
                "index": "{}/index.json".format(method),
                "solver_configuration": solver_config(args, method),
                "summary": aggregate_results("overall", methods[method]),
            }
            for method in METHOD_ORDER
        },
        "cactus_plots": dict(cactus_plots),
    }
    atomic_write_json(output / "summary.json", summary)
    atomic_write_json(output / "index.json", summary)


def plot_saved_matrix(args: argparse.Namespace) -> int:
    """Regenerate overlays using only paths referenced by the saved matrix."""
    output = args.output.resolve()
    index_path = output / "index.json"
    if not index_path.is_file():
        raise SystemExit("benchmark matrix index not found: {}".format(index_path))
    with index_path.open("r", encoding="utf-8") as source:
        index = json.load(source)
    if not isinstance(index, dict) or not isinstance(index.get("methods"), dict):
        raise SystemExit("invalid benchmark matrix index: {}".format(index_path))
    timeout = index.get("limits", {}).get("family_timeout_seconds")
    if not isinstance(timeout, (int, float)) or not math.isfinite(timeout) or not 0 <= timeout <= MAX_FAMILY_TIMEOUT_SECONDS:
        raise SystemExit("invalid saved family timeout in {}".format(index_path))
    methods: Dict[str, List[Dict[str, Any]]] = {}
    for method in METHOD_ORDER:
        entry = index["methods"].get(method)
        if not isinstance(entry, dict) or not isinstance(entry.get("index"), str):
            raise SystemExit("missing method index for {}".format(method))
        method_index = output / entry["index"]
        if method_index.name != "index.json":
            raise SystemExit("invalid method index path: {}".format(method_index))
        _, methods[method] = load_saved_results(method_index.parent)
    pyplot = plot.import_pyplot()
    families = sorted({str(result["family"]) for results in methods.values() for result in results})
    cactus_plots = {}
    tqdm = import_tqdm()
    with progress_bar(tqdm, len(families) + 1, "Regenerate cactus plots", 0) as render_bar:
        for family in families:
            render_bar.set_postfix(stage="rendering", family=family)
            relevant = {
                method: [result for result in results if result["family"] == family]
                for method, results in methods.items()
            }
            cactus_plots[family] = plot_matrix_cactus(pyplot, output, family, relevant, timeout)
            render_bar.update(1)
        render_bar.set_postfix(stage="rendering", family="overall")
        cactus_plots["overall"] = plot_matrix_cactus(pyplot, output, "overall", methods, timeout)
        render_bar.update(1)
        render_bar.set_postfix(stage="done")
    index["cactus_plots"] = cactus_plots
    atomic_write_json(output / "summary.json", index)
    atomic_write_json(index_path, index)
    tqdm.write("Regenerated matrix cactus plots: {}".format(output / "plots" / "cactus"))
    return 0


def benchmark(args: argparse.Namespace) -> int:
    if args.inprocessing:
        raise SystemExit("--inprocessing cannot override the fixed benchmark matrix; omit it")
    if args.plot_only:
        return plot_saved_matrix(args)
    problems = discover_problems()
    if not problems:
        raise SystemExit("no .cnf problems found in family directories under tests/benchmark")
    families = group_problems_by_family(problems)
    # Resolve reference data before starting any method's timed execution.
    metadata_by_path = {path: problem_metadata(path) for path in problems}
    tqdm = import_tqdm()
    pyplot = plot.import_pyplot()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    started_at = datetime.now(timezone.utc).isoformat()
    methods: Dict[str, List[Dict[str, Any]]] = {method: [] for method in METHOD_ORDER}
    aggregates: Dict[str, Dict[str, Dict[str, Any]]] = {method: {} for method in METHOD_ORDER}
    completed_families: List[str] = []
    cactus_plots: Dict[str, str] = {}
    # Reset indexes up front so stale files from an earlier run remain unreferenced.
    for method in METHOD_ORDER:
        write_index(output / method, started_at, solver_config(args, method), args, [], {})
    write_matrix_index(output, started_at, args, methods, completed_families, cactus_plots)
    tqdm.write(
        "Discovered {} problems across {} families; {} configurations, {:.1f}s per configuration per family. "
        "Budget upper bounds exclude plotting/overhead; throughput ETA is estimated and unreliable for SAT.".format(
            len(problems), len(families), len(METHOD_ORDER), args.family_timeout
        )
    )
    totals = dict.fromkeys(STATUS_NAMES, 0)
    pending_pairs = len(families) * len(METHOD_ORDER)
    with ExitStack() as stack:
        global_bar = stack.enter_context(progress_bar(tqdm, len(problems) * len(METHOD_ORDER), "All results", 0))
        for family, paths in families.items():
            family_methods: Dict[str, List[Dict[str, Any]]] = {}
            family_counts = dict.fromkeys(STATUS_NAMES, 0)
            with progress_bar(tqdm, len(paths) * len(METHOD_ORDER), family, 1) as family_bar:
                def show(stage, method, problem, remaining):
                    pending_budget = pending_pairs * args.family_timeout
                    global_bar.set_postfix(progress_status(totals, stage, method, problem, remaining, pending_budget))
                    family_bar.set_postfix(progress_status(family_counts, stage, method, problem, remaining, pending_budget))

                for method in METHOD_ORDER:
                    pending_pairs -= 1
                    config = solver_config(args, method)
                    method_output = output / method
                    temporary_output = method_output / ".worker-result.json"
                    family_results: List[Dict[str, Any]] = []
                    deadline = time.perf_counter() + args.family_timeout
                    try:
                        for path in paths:
                            metadata = metadata_by_path[path]
                            remaining = max(0.0, deadline - time.perf_counter())
                            show("solving", method, metadata["problem"], remaining)
                            if remaining <= 0:
                                result = {
                                    **result_base(metadata, config),
                                    "status": "skipped",
                                    "wall_seconds": 0.0,
                                    "error": "method family deadline exhausted",
                                }
                            else:
                                if temporary_output.exists():
                                    temporary_output.unlink()
                                result = run_problem_subprocess(
                                    path, temporary_output, config, metadata, deadline,
                                    progress_callback=lambda remaining: show(
                                        "solving", method, metadata["problem"], remaining
                                    ),
                                )
                            atomic_write_json(result_json_path(method_output, path), result)
                            family_results.append(result)
                            totals[result["status"]] += 1
                            family_counts[result["status"]] += 1
                            remaining = max(0.0, deadline - time.perf_counter())
                            show("result saved", method, metadata["problem"], remaining)
                            global_bar.update(1)
                            family_bar.update(1)
                    finally:
                        if temporary_output.exists():
                            temporary_output.unlink()
                    show("aggregating", method, "-", 0)
                    methods[method].extend(family_results)
                    family_methods[method] = family_results
                    aggregates[method][family] = aggregate_results(family, family_results)
                    aggregates[method]["overall"] = aggregate_results("overall", methods[method])
                    for name in (family, "overall"):
                        atomic_write_json(method_output / "aggregates" / (safe_filename(name) + ".json"), aggregates[method][name])
                    write_index(method_output, started_at, config, args, methods[method], aggregates[method])
                    # Plotting and aggregation are outside the method's family deadline.
                    with progress_bar(tqdm, len(family_results) + 2, "Render {} / {}".format(family, method), 2) as render_bar:
                        for result in family_results:
                            show("rendering", method, result["problem"], 0)
                            render_bar.set_postfix(problem=result["problem"])
                            plot.plot_problem(pyplot, result, result_plot_path(method_output, result))
                            render_bar.update(1)
                        for name, relevant in ((family, family_results), ("overall", methods[method])):
                            show("rendering aggregate", method, name, 0)
                            render_bar.set_postfix(aggregate=name)
                            plot.plot_aggregate(pyplot, aggregates[method][name], relevant, method_output / "plots" / "aggregates" / (safe_filename(name) + ".png"))
                            render_bar.update(1)
                    tqdm.write("{} / {}: {}".format(family, method, aggregates[method][family]["statuses"]))
                with progress_bar(tqdm, 2, "Render cactus / " + family, 2) as render_bar:
                    for name in (family, "overall"):
                        show("rendering cactus", "all", name, 0)
                        render_bar.set_postfix(aggregate=name)
                        cactus_plots[name] = plot_matrix_cactus(
                            pyplot, output, name, family_methods if name == family else methods, args.family_timeout
                        )
                        render_bar.update(1)
                completed_families.append(family)
                show("saving matrix", "all", "-", 0)
                write_matrix_index(output, started_at, args, methods, completed_families, cactus_plots)
                show("family done", "all", "-", 0)
        global_bar.set_postfix(progress_status(totals, "done", "all", "-", 0, 0))
    tqdm.write("Benchmark complete: {}. Results: {}".format(totals, output))
    return 1 if totals["error"] or totals["incorrect"] else 0


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)
    if args.worker:
        if (
            args.worker_input is None
            or args.worker_output is None
            or args.worker_config is None
            or args.worker_metadata is None
        ):
            raise SystemExit(
                "worker mode requires input, output, configuration, and metadata"
            )
        return run_worker(
            args.worker_input.resolve(),
            args.worker_output.resolve(),
            json.loads(args.worker_config),
            json.loads(args.worker_metadata),
        )
    return benchmark(args)


if __name__ == "__main__":
    raise SystemExit(main())
