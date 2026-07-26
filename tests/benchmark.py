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
from collections import defaultdict, deque
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Deque, Dict, Iterable, List, Mapping, Optional, Sequence

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
DEFAULT_OUTPUT = PROJECT_ROOT / "benchmark_result"
MAX_TOTAL_TIMEOUT_SECONDS = 5.0 * 60.0
MAX_INSTANCE_TIMEOUT_SECONDS = 120.0
PROCESS_CHOICES = ("bva", "bve", "subsumption")
STATUS_NAMES = ("completed", "incorrect", "timeout", "error", "skipped")


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Benchmark clsat on every CNF under tests/sat and tests/unsat."
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--total-timeout",
        type=float,
        default=MAX_TOTAL_TIMEOUT_SECONDS,
        help="Total benchmark solver time, capped at five minutes (default: 300s).",
    )
    parser.add_argument(
        "--instance-timeout",
        type=float,
        default=MAX_INSTANCE_TIMEOUT_SECONDS,
        help="Maximum solver time for one problem, capped at 120 seconds (default: 120s).",
    )
    parser.add_argument("--algorithm", choices=("cdcl", "dpll"), default="cdcl")
    parser.add_argument(
        "--implication-point", choices=("uip", "dip"), default="uip"
    )
    parser.add_argument("--heuristics", choices=("vsids", "random"), default="vsids")
    parser.add_argument(
        "--preprocess", nargs="*", choices=PROCESS_CHOICES, default=[]
    )
    parser.add_argument(
        "--inprocessing", nargs="*", choices=PROCESS_CHOICES, default=[]
    )
    parser.add_argument("--preprocessing-budget", type=float, default=5.0)
    parser.add_argument("--inprocessing-budget", type=float, default=0.075)

    parser.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--worker-input", type=Path, help=argparse.SUPPRESS)
    parser.add_argument("--worker-output", type=Path, help=argparse.SUPPRESS)
    parser.add_argument("--worker-config", help=argparse.SUPPRESS)
    parser.add_argument("--worker-metadata", help=argparse.SUPPRESS)

    args = parser.parse_args(argv)
    for name in (
        "total_timeout",
        "instance_timeout",
        "preprocessing_budget",
        "inprocessing_budget",
    ):
        value = getattr(args, name)
        if not math.isfinite(value) or value < 0:
            parser.error("--{} must be finite and non-negative".format(name.replace("_", "-")))
    if args.total_timeout > MAX_TOTAL_TIMEOUT_SECONDS:
        parser.error(
            "--total-timeout cannot exceed {:.0f} seconds".format(
                MAX_TOTAL_TIMEOUT_SECONDS
            )
        )
    if args.instance_timeout > MAX_INSTANCE_TIMEOUT_SECONDS:
        parser.error(
            "--instance-timeout cannot exceed {:.0f} seconds".format(
                MAX_INSTANCE_TIMEOUT_SECONDS
            )
        )
    return args


def expected_status(path: Path) -> str:
    return path.relative_to(TESTS_ROOT).parts[0]


def problem_family(path: Path) -> str:
    relative = path.relative_to(TESTS_ROOT)
    expected = relative.parts[0]
    within_status = relative.parts[1:]

    if len(within_status) > 1:
        family = within_status[0]
    else:
        stem = path.stem
        if "_" in stem:
            family = stem.split("_", 1)[0]
        elif "-" in stem:
            family = stem.rsplit("-", 1)[0]
        else:
            family = re.sub(r"(?:[-_]?[0-9]+)+$", "", stem) or stem
    return "{}/{}".format(expected, family)


def problem_key(path: Path) -> str:
    return path.relative_to(PROJECT_ROOT).as_posix()


def problem_metadata(path: Path) -> Dict[str, str]:
    return {
        "problem": problem_key(path),
        "family": problem_family(path),
        "expected": expected_status(path),
    }


def round_robin_by_family(problems: Iterable[Path]) -> List[Path]:
    """Prevent one difficult family from consuming the complete budget first."""
    grouped: Dict[str, Deque[Path]] = defaultdict(deque)
    for path in sorted(problems):
        grouped[problem_family(path)].append(path)

    ordered: List[Path] = []
    family_names = sorted(grouped)
    while any(grouped[name] for name in family_names):
        for name in family_names:
            if grouped[name]:
                ordered.append(grouped[name].popleft())
    return ordered


def discover_problems() -> List[Path]:
    problems: List[Path] = []
    for status in ("sat", "unsat"):
        root = TESTS_ROOT / status
        if root.exists():
            problems.extend(sorted(root.rglob("*.cnf")))
    return round_robin_by_family(problems)


def solver_config(args: argparse.Namespace) -> Dict[str, Any]:
    return {
        "algorithm": args.algorithm,
        "implication_point": args.implication_point,
        "heuristics": args.heuristics,
        "preprocess": list(args.preprocess),
        "inprocessing": list(args.inprocessing),
        "preprocessing_budget": args.preprocessing_budget,
        "inprocessing_budget": args.inprocessing_budget,
    }


def safe_filename(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", name).strip("_") or "aggregate"


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
            "total_timeout_seconds": args.total_timeout,
            "instance_timeout_seconds": args.instance_timeout,
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


def benchmark(args: argparse.Namespace) -> int:
    pyplot = plot.import_pyplot()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    temporary_output = output / ".worker-result.json"
    config = solver_config(args)
    problems = discover_problems()
    if not problems:
        raise SystemExit("no .cnf problems found under tests/sat or tests/unsat")

    started_at = datetime.now(timezone.utc).isoformat()
    deadline = time.perf_counter() + args.total_timeout
    results: List[Dict[str, Any]] = []

    print(
        "Discovered {} problems across {} families. Solver budget: {:.1f}s total, "
        "{:.1f}s per instance.".format(
            len(problems),
            len({problem_family(path) for path in problems}),
            args.total_timeout,
            args.instance_timeout,
        ),
        flush=True,
    )

    for index, path in enumerate(problems, 1):
        metadata = problem_metadata(path)
        remaining = deadline - time.perf_counter()
        if remaining <= 0 or args.total_timeout == 0:
            result = {
                **result_base(metadata, config),
                "status": "skipped",
                "wall_seconds": 0.0,
                "error": "global benchmark deadline exhausted",
            }
        else:
            timeout = min(args.instance_timeout, remaining)
            if timeout <= 0:
                result = {
                    **result_base(metadata, config),
                    "status": "skipped",
                    "wall_seconds": 0.0,
                    "error": "instance timeout is zero",
                }
            else:
                print(
                    "[{}/{}] {} (family {}, timeout {:.2f}s)".format(
                        index,
                        len(problems),
                        metadata["problem"],
                        metadata["family"],
                        timeout,
                    ),
                    flush=True,
                )
                if temporary_output.exists():
                    temporary_output.unlink()
                result = run_problem_subprocess(
                    path,
                    temporary_output,
                    config,
                    metadata,
                    timeout,
                    deadline,
                )

        atomic_write_json(result_json_path(output, path), result)
        results.append(result)
        print(
            "  -> {} in {:.3f}s".format(
                result["status"], float(result.get("wall_seconds", 0.0))
            ),
            flush=True,
        )

    if temporary_output.exists():
        temporary_output.unlink()

    grouped: Dict[str, List[Mapping[str, Any]]] = defaultdict(list)
    for result in results:
        grouped[str(result["family"])].append(result)

    aggregates: Dict[str, Dict[str, Any]] = {
        family: aggregate_results(family, family_results)
        for family, family_results in sorted(grouped.items())
    }
    aggregates["overall"] = aggregate_results("overall", results)

    for result in results:
        plot.plot_problem(pyplot, result, result_plot_path(output, result))
    for name, aggregate in aggregates.items():
        atomic_write_json(
            output / "aggregates" / (safe_filename(name) + ".json"), aggregate
        )
        relevant = results if name == "overall" else grouped[name]
        plot.plot_aggregate(
            pyplot,
            aggregate,
            relevant,
            output / "plots" / "aggregates" / (safe_filename(name) + ".png"),
        )

    write_index(output, started_at, config, args, results, aggregates)
    completed = sum(result["status"] == "completed" for result in results)
    incorrect = sum(result["status"] == "incorrect" for result in results)
    timed_out = sum(result["status"] == "timeout" for result in results)
    errors = sum(result["status"] == "error" for result in results)
    print(
        "Benchmark complete: {} completed, {} incorrect, {} timed out, {} errors. "
        "Results: {}".format(completed, incorrect, timed_out, errors, output),
        flush=True,
    )
    return 0 if errors == 0 and incorrect == 0 else 1


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
