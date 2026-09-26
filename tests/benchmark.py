"""Corpus discovery, aggregation, persistence, and CLI orchestration.

The repository's ``main.py`` calls this module by default. It can also be run
as ``python -m tests.benchmark``.
"""

import argparse
import json
import math
import re
import statistics
import subprocess
import sys
import time
import zipfile
from collections import defaultdict
from contextlib import ExitStack
from dataclasses import dataclass
from datetime import datetime, timezone
from functools import lru_cache
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple, cast
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
GES_METHODS = ("ges", "ges_always", "ges_lbd", "ges_random", "ges_par", "ges_vsids", "ges_utility")
METHOD_ORDER = ("base", *GES_METHODS)
METHOD_LABELS = {
    "base": "Base",
    "ges": "GES (cursor)",
    "ges_always": "GES (always)",
    "ges_lbd": "GES (LBD)",
    "ges_random": "GES (random)",
    "ges_par": "GES (parallel)",
    "ges_vsids": "GES (VSIDS)",
    "ges_utility": "GES (utility)",
}


@dataclass(frozen=True)
class BenchmarkProfile:
    name: str
    implication_point: str
    use_bva: bool
    base_only: bool = False


PARALLEL_PROFILES = (
    BenchmarkProfile("uip", "uip", False, base_only=True),
    BenchmarkProfile("uip_bva", "uip", True),
    BenchmarkProfile("dip", "dip", False),
    BenchmarkProfile("dip_bva", "dip", True),
)
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
PROCESS_CHOICES = ("bva", "bve", "ges", "ges_always", "ges_lbd", "ges_par", "ges_random", "ges_vsids", "ges_utility", "ges_compress", "ges_trail", "subsumption")
GES_ADDONS = ("ges_compress", "ges_trail")
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
        description=(
            "Benchmark a baseline and the standalone GES variants. By default, "
            "immediate directories under tests/benchmark are families; --input "
            "treats one directory tree as a single corpus. --parallel runs the UIP, "
            "UIP+BVA, DIP, and DIP+BVA profile matrices concurrently."
        )
    )
    parser.add_argument(
        "--input",
        type=Path,
        help="Recursively benchmark every .cnf under this directory as one corpus.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help=(
            "Result directory for one matrix. With --parallel, this is the parent "
            "for benchmark_uip, benchmark_uip_bva, benchmark_dip, and benchmark_dip_bva."
        ),
    )
    parser.add_argument(
        "--parallel",
        action="store_true",
        help="Run the four UIP/DIP with/without-BVA benchmark matrices concurrently.",
    )
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
    bva = parser.add_mutually_exclusive_group()
    bva.add_argument(
        "--bva",
        dest="use_bva",
        action="store_true",
        help="Run BVA during preprocessing and inprocessing (default for one matrix).",
    )
    bva.add_argument(
        "--no-bva",
        dest="use_bva",
        action="store_false",
        help="Disable the benchmark-managed BVA passes.",
    )
    parser.set_defaults(use_bva=True)
    parser.add_argument("--algorithm", choices=("cdcl", "dpll"), default="cdcl")
    parser.add_argument(
        "--implication-point", choices=("uip", "dip"), default="dip"
    )
    parser.add_argument("--heuristics", choices=("vsids", "random"), default="vsids")
    parser.add_argument(
        "--preprocess", nargs="*", choices=PROCESS_CHOICES, default=[],
        help="Additional preprocessing techniques (ges_par runs parallel GES).",
    )
    parser.add_argument(
        "--ges-addons",
        nargs="*",
        choices=GES_ADDONS,
        default=[],
        help="Modifiers appended to every non-base GES inprocessing configuration.",
    )
    parser.add_argument(
        "--inprocessing", nargs="*", choices=PROCESS_CHOICES, default=[],
        help="Legacy parser compatibility only; non-empty values are not allowed for the fixed matrix.",
    )

    parser.add_argument("--base-only", action="store_true", help=argparse.SUPPRESS)
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


def expected_status(path: Path, input_root: Optional[Path] = None) -> str:
    if input_root is not None:
        return "unknown"
    return reference_statuses().get(path.relative_to(BENCHMARK_ROOT).as_posix(), "unknown")


def problem_family(path: Path, input_root: Optional[Path] = None) -> str:
    if input_root is not None:
        path.relative_to(input_root)
        return input_root.name or "corpus"
    relative = path.relative_to(BENCHMARK_ROOT)
    if len(relative.parts) < 2:
        raise ValueError("benchmark problems must be inside a family directory: {}".format(path))
    return relative.parts[0]


def problem_key(path: Path, input_root: Optional[Path] = None) -> str:
    try:
        return path.relative_to(PROJECT_ROOT).as_posix()
    except ValueError:
        if input_root is None:
            raise
        relative = path.relative_to(input_root)
        return (Path(input_root.name or "corpus") / relative).as_posix()


def problem_metadata(path: Path, input_root: Optional[Path] = None) -> Dict[str, str]:
    return {
        "problem": problem_key(path, input_root),
        "family": problem_family(path, input_root),
        "expected": expected_status(path, input_root),
    }


def group_problems_by_family(
    problems: Iterable[Path], input_root: Optional[Path] = None
) -> Dict[str, List[Path]]:
    grouped: Dict[str, List[Path]] = defaultdict(list)
    for path in sorted(problems):
        grouped[problem_family(path, input_root)].append(path)
    return {family: grouped[family] for family in sorted(grouped)}


def discover_problems(input_root: Optional[Path] = None) -> List[Path]:
    """Discover deterministic recursive CNF inputs in family or single-corpus mode."""
    if input_root is not None:
        if not input_root.is_dir():
            return []
        return sorted(path for path in input_root.rglob("*.cnf") if path.is_file())
    if not BENCHMARK_ROOT.is_dir():
        return []
    return [
        path
        for family in sorted(BENCHMARK_ROOT.iterdir()) if family.is_dir()
        for path in sorted(family.rglob("*.cnf")) if path.is_file()
    ]


def benchmark_methods(args: argparse.Namespace) -> Tuple[str, ...]:
    return ("base",) if args.base_only else METHOD_ORDER


def unique_processes(processes: Iterable[str]) -> List[str]:
    return list(dict.fromkeys(processes))


def solver_config(args: argparse.Namespace, method: str = "base") -> Dict[str, Any]:
    if method not in METHOD_ORDER:
        raise ValueError("unknown benchmark method: {}".format(method))
    managed_bva = ["bva"] if args.use_bva else []
    inprocessing = []
    if method != "base":
        inprocessing.extend([method, *args.ges_addons])
    inprocessing.extend(managed_bva)
    return {
        "algorithm": args.algorithm,
        "implication_point": args.implication_point,
        "heuristics": args.heuristics,
        "preprocess": unique_processes([*managed_bva, *args.preprocess]),
        "inprocessing": unique_processes(inprocessing),
    }


def method_label(args: argparse.Namespace, method: str) -> str:
    parts = [args.implication_point.upper()]
    if args.use_bva:
        parts.append("BVA")
    if method != "base":
        parts.append(METHOD_LABELS[method])
    return " + ".join(parts)


def benchmark_output(args: argparse.Namespace) -> Path:
    return (args.output or DEFAULT_OUTPUT).resolve()


def parallel_profile_output(args: argparse.Namespace, profile: BenchmarkProfile) -> Path:
    parent = args.output.resolve() if args.output is not None else PROJECT_ROOT
    return parent / ("benchmark_" + profile.name)


def parallel_profile_command(
    args: argparse.Namespace, profile: BenchmarkProfile, output: Path
) -> List[str]:
    command = [
        sys.executable,
        str(PROJECT_ROOT / "main.py"),
        "benchmark",
        "--output",
        str(output),
        "--family-timeout",
        str(args.family_timeout),
        "--algorithm",
        args.algorithm,
        "--implication-point",
        profile.implication_point,
        "--heuristics",
        args.heuristics,
        "--bva" if profile.use_bva else "--no-bva",
    ]
    if profile.base_only:
        command.append("--base-only")
    if args.input is not None:
        command.extend(["--input", str(args.input.resolve())])
    if args.plot_only:
        command.append("--plot-only")
    additional_preprocessing = [
        process for process in args.preprocess if process != "bva"
    ]
    if additional_preprocessing:
        command.extend(["--preprocess", *additional_preprocessing])
    if args.ges_addons:
        command.extend(["--ges-addons", *args.ges_addons])
    return command


def stop_parallel_children(children: Sequence[Mapping[str, Any]]) -> None:
    for child in children:
        process = child["process"]
        if process.poll() is None:
            process.terminate()
    for child in children:
        process = child["process"]
        if process.poll() is None:
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()


def run_parallel_benchmarks(args: argparse.Namespace) -> int:
    if args.inprocessing:
        raise SystemExit("--inprocessing cannot override the fixed benchmark matrix; omit it")

    children: List[Dict[str, Any]] = []
    try:
        for profile in PARALLEL_PROFILES:
            output = parallel_profile_output(args, profile)
            output.mkdir(parents=True, exist_ok=True)
            log_path = output / "parallel.log"
            log = log_path.open("w", encoding="utf-8")
            try:
                process = subprocess.Popen(
                    parallel_profile_command(args, profile, output),
                    cwd=PROJECT_ROOT,
                    stdout=log,
                    stderr=subprocess.STDOUT,
                )
            except BaseException:
                log.close()
                raise
            children.append(
                {
                    "profile": profile,
                    "output": output,
                    "log_path": log_path,
                    "log": log,
                    "process": process,
                    "reported": False,
                    "returncode": None,
                }
            )

        tqdm = import_tqdm()
        with progress_bar(tqdm, len(children), "Benchmark profiles", 0) as bar:
            while any(not child["reported"] for child in children):
                changed = False
                running = []
                for child in children:
                    if child["reported"]:
                        continue
                    returncode = child["process"].poll()
                    if returncode is None:
                        running.append(child["profile"].name)
                        continue
                    child["returncode"] = returncode
                    child["reported"] = True
                    child["log"].close()
                    bar.update(1)
                    changed = True
                    tqdm.write(
                        "{}: {} (log: {})".format(
                            child["profile"].name,
                            "completed" if returncode == 0 else "failed ({})".format(returncode),
                            child["log_path"],
                        )
                    )
                bar.set_postfix(running=", ".join(running) or "none")
                if not changed and running:
                    time.sleep(0.2)
    except BaseException:
        stop_parallel_children(children)
        raise
    finally:
        for child in children:
            if not child["log"].closed:
                child["log"].close()

    return 1 if any(child["returncode"] != 0 for child in children) else 0


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


def problem_output_relative(problem: str) -> Path:
    relative = Path(problem)
    if relative.is_absolute() or ".." in relative.parts:
        raise ValueError("problem key must be a safe relative path: {}".format(problem))
    if relative.parts and relative.parts[0] == "tests":
        relative = Path(*relative.parts[1:])
    return relative


def result_json_path(output: Path, problem: str) -> Path:
    return output / "problems" / problem_output_relative(problem).with_suffix(".json")


def result_plot_path(output: Path, result: Mapping[str, Any]) -> Path:
    relative = problem_output_relative(str(result["problem"])).with_suffix(".png")
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
            "result": str(result_json_path(output, str(result["problem"])).relative_to(output)),
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
    labels: Mapping[str, str],
    timeout_seconds: float,
) -> str:
    destination = output / "plots" / "cactus" / (safe_filename(name) + ".png")
    plot.plot_comparison_cactus(
        pyplot,
        name,
        {labels.get(method, method): results for method, results in methods.items()},
        destination,
        timeout_seconds,
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
    method_order = benchmark_methods(args)
    summary = {
        "started_at": started_at,
        "updated_at": datetime.now(timezone.utc).isoformat(),
        "profile": {
            "implication_point": args.implication_point,
            "bva": args.use_bva,
        },
        "limits": {"family_timeout_seconds": args.family_timeout},
        "method_order": list(method_order),
        "completed_families": list(completed_families),
        "methods": {
            method: {
                "label": method_label(args, method),
                "path": method,
                "index": "{}/index.json".format(method),
                "solver_configuration": solver_config(args, method),
                "summary": aggregate_results("overall", methods[method]),
            }
            for method in method_order
        },
        "cactus_plots": dict(cactus_plots),
    }
    atomic_write_json(output / "summary.json", summary)
    atomic_write_json(output / "index.json", summary)


def plot_saved_matrix(args: argparse.Namespace) -> int:
    """Regenerate overlays using only paths referenced by the saved matrix."""
    output = benchmark_output(args)
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
    labels: Dict[str, str] = {}
    for method in index["method_order"]:
        entry = index["methods"].get(method)
        if not isinstance(entry, dict) or not isinstance(entry.get("index"), str):
            raise SystemExit("missing method index for {}".format(method))
        method_index = output / entry["index"]
        if method_index.name != "index.json":
            raise SystemExit("invalid method index path: {}".format(method_index))
        _, methods[method] = load_saved_results(method_index.parent)
        labels[method] = str(entry.get("label", METHOD_LABELS.get(method, method)))
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
            cactus_plots[family] = plot_matrix_cactus(
                pyplot, output, family, relevant, labels, timeout
            )
            render_bar.update(1)
        render_bar.set_postfix(stage="rendering", family="overall")
        cactus_plots["overall"] = plot_matrix_cactus(
            pyplot, output, "overall", methods, labels, timeout
        )
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
    input_root = args.input.resolve() if args.input is not None else None
    if input_root is not None and not input_root.is_dir():
        raise SystemExit("benchmark input directory not found: {}".format(input_root))
    problems = discover_problems(input_root)
    if not problems:
        location = input_root if input_root is not None else "family directories under tests/benchmark"
        raise SystemExit("no .cnf problems found in {}".format(location))
    families = group_problems_by_family(problems, input_root)
    # Resolve reference data before starting any method's timed execution.
    metadata_by_path = {path: problem_metadata(path, input_root) for path in problems}
    tqdm = import_tqdm()
    pyplot = plot.import_pyplot()
    output = benchmark_output(args)
    output.mkdir(parents=True, exist_ok=True)
    started_at = datetime.now(timezone.utc).isoformat()
    method_order = benchmark_methods(args)
    labels = {method: method_label(args, method) for method in method_order}
    methods: Dict[str, List[Dict[str, Any]]] = {method: [] for method in method_order}
    aggregates: Dict[str, Dict[str, Dict[str, Any]]] = {method: {} for method in method_order}
    completed_families: List[str] = []
    cactus_plots: Dict[str, str] = {}
    # Reset indexes up front so stale files from an earlier run remain unreferenced.
    for method in method_order:
        write_index(output / method, started_at, solver_config(args, method), args, [], {})
    write_matrix_index(output, started_at, args, methods, completed_families, cactus_plots)
    tqdm.write(
        "Discovered {} problems across {} families; {} configurations, {:.1f}s per configuration per family. "
        "Budget upper bounds exclude plotting/overhead; throughput ETA is estimated and unreliable for SAT.".format(
            len(problems), len(families), len(method_order), args.family_timeout
        )
    )
    totals = dict.fromkeys(STATUS_NAMES, 0)
    pending_pairs = len(families) * len(method_order)
    with ExitStack() as stack:
        global_bar = stack.enter_context(
            progress_bar(tqdm, len(problems) * len(method_order), "All results", 0)
        )
        for family, paths in families.items():
            family_methods: Dict[str, List[Dict[str, Any]]] = {}
            family_counts = dict.fromkeys(STATUS_NAMES, 0)
            with progress_bar(tqdm, len(paths) * len(method_order), family, 1) as family_bar:
                def show(stage, method, problem, remaining):
                    pending_budget = pending_pairs * args.family_timeout
                    global_bar.set_postfix(progress_status(totals, stage, method, problem, remaining, pending_budget))
                    family_bar.set_postfix(progress_status(family_counts, stage, method, problem, remaining, pending_budget))

                for method in method_order:
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
                            atomic_write_json(
                                result_json_path(method_output, str(result["problem"])), result
                            )
                            family_results.append(result)
                            status = cast(str, result["status"])
                            totals[status] += 1
                            family_counts[status] += 1
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
                            pyplot,
                            output,
                            name,
                            family_methods if name == family else methods,
                            labels,
                            args.family_timeout,
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
    if args.parallel:
        if args.worker or args.base_only:
            raise SystemExit("--parallel cannot be combined with internal worker options")
        return run_parallel_benchmarks(args)
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
