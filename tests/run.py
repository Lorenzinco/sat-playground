"""Execution and hard-timeout support for the SAT benchmark."""

import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Mapping, Sequence, Tuple


PROJECT_ROOT = Path(__file__).resolve().parents[1]

# Several solver timers are nested. Consumers should display them as raw
# measurements rather than summing them into a stacked total.
RUNTIME_METHODS: Tuple[Tuple[str, str], ...] = (
    ("preprocessing", "preprocessing_millis"),
    ("solving", "solving_millis"),
    ("propagation", "propagation_millis"),
    ("conflict analysis", "conflict_analysis_millis"),
    ("clause minimization", "clause_minimization_millis"),
    ("clause learning", "clause_learning_millis"),
    ("database reduction", "db_reduction_millis"),
    ("subsumption", "subsumption_millis"),
    ("restart", "restart_millis"),
    ("inprocessing", "inprocessing_millis"),
)

COUNTER_FIELDS: Tuple[str, ...] = (
    "conflicts",
    "restarts",
    "clauses_learnt",
    "clauses_deleted",
    "clauses_subsumed",
    "subsumption_checks",
    "minimized_literals",
    "clauses_kept",
    "literals_learnt",
    "extension_literals",
    "bva_literals",
    "bve_eliminated_variables",
    "bve_resolvents",
    "avg_clause_length",
)


def parse_dimacs(path: Path) -> Tuple[List[List[int]], Dict[str, int]]:
    """Parse DIMACS correctly even when clauses span physical lines."""
    clauses: List[List[int]] = []
    pending: List[int] = []
    declared_variables = 0
    declared_clauses = 0

    with path.open("r", encoding="utf-8", errors="replace") as source:
        for line_number, raw_line in enumerate(source, 1):
            line = raw_line.strip()
            if not line or line.startswith("c") or line.startswith("%"):
                continue
            if line.startswith("p"):
                fields = line.split()
                if len(fields) >= 4 and fields[1].lower() == "cnf":
                    declared_variables = int(fields[2])
                    declared_clauses = int(fields[3])
                continue

            for token in line.split():
                try:
                    literal = int(token)
                except ValueError as error:
                    raise ValueError(
                        "{}:{}: invalid DIMACS token {!r}".format(path, line_number, token)
                    ) from error
                if literal == 0:
                    clauses.append(pending)
                    pending = []
                else:
                    pending.append(literal)

    if pending:
        raise ValueError("{}: final DIMACS clause is missing its terminating 0".format(path))

    max_variable = max(
        (abs(literal) for clause in clauses for literal in clause), default=0
    )
    return clauses, {
        "declared_variables": declared_variables,
        "declared_clauses": declared_clauses,
        "parsed_variables": max_variable,
        "parsed_clauses": len(clauses),
    }


def validate_model(model: Sequence[bool], clauses: Sequence[Sequence[int]]) -> bool:
    """Validate either a one-based model or a compact zero-based model."""
    max_variable = max(
        (abs(literal) for clause in clauses for literal in clause), default=0
    )
    one_based = len(model) > max_variable
    if len(model) < max_variable:
        return False

    for clause in clauses:
        satisfied = False
        for literal in clause:
            variable = abs(literal)
            model_index = variable if one_based else variable - 1
            value = bool(model[model_index])
            if value != (literal < 0):
                satisfied = True
                break
        if not satisfied:
            return False
    return True


def atomic_write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    with temporary.open("w", encoding="utf-8") as destination:
        json.dump(value, destination, indent=2, sort_keys=True)
        destination.write("\n")
    temporary.replace(path)


def result_base(metadata: Mapping[str, Any], config: Mapping[str, Any]) -> Dict[str, Any]:
    return {
        "problem": metadata["problem"],
        "family": metadata["family"],
        "expected": metadata["expected"],
        "configuration": dict(config),
    }


def run_worker(
    path: Path,
    output: Path,
    config: Mapping[str, Any],
    metadata: Mapping[str, Any],
) -> int:
    """Solve one formula. This function executes only in a subprocess."""
    base = result_base(metadata, config)
    started = time.perf_counter()
    try:
        import clsat

        clauses, dimensions = parse_dimacs(path)
        solver = clsat.Sat(clauses)
        solver.solve(
            algorithm=config["algorithm"],
            implication_point=config["implication_point"],
            preprocess=config["preprocess"],
            inprocessing=config["inprocessing"],
            heuristics=config["heuristics"],
            drat_path=None,
            preprocessing_budget=config["preprocessing_budget"],
            inprocessing_budget=config["inprocessing_budget"],
        )
        elapsed = time.perf_counter() - started
        model = solver.model
        actual = "sat" if model is not None else "unsat"
        model_valid = model is None or validate_model(model, clauses)
        classification_matches = actual == base["expected"]
        status = "completed" if model_valid and classification_matches else "incorrect"
        stats = solver.stats
        if stats is None:
            raise RuntimeError("solver completed without exposing statistics")

        runtime_seconds = {
            label: float(getattr(stats, method)()) / 1000.0
            for label, method in RUNTIME_METHODS
        }
        counters = {
            field: float(getattr(stats, field))
            for field in COUNTER_FIELDS
        }

        result = dict(base)
        result.update(
            {
                "status": status,
                "actual": actual,
                "model_valid": model_valid,
                "correct_classification": classification_matches,
                "wall_seconds": elapsed,
                "dimensions": dimensions,
                "runtime_seconds": runtime_seconds,
                "counters": counters,
            }
        )
        atomic_write_json(output, result)
        return 0 if status == "completed" else 2
    except BaseException as error:
        result = dict(base)
        result.update(
            {
                "status": "error",
                "wall_seconds": time.perf_counter() - started,
                "error": "{}: {}".format(type(error).__name__, error),
            }
        )
        atomic_write_json(output, result)
        return 1


def terminate_process(process: subprocess.Popen) -> None:
    try:
        if os.name == "posix":
            os.killpg(process.pid, signal.SIGKILL)
        else:
            process.kill()
    except ProcessLookupError:
        pass
    except OSError:
        process.kill()


def run_problem_subprocess(
    path: Path,
    worker_output: Path,
    config: Mapping[str, Any],
    metadata: Mapping[str, Any],
    instance_timeout: float,
    global_deadline: float,
) -> Dict[str, Any]:
    """Run one isolated worker bounded by per-instance and global deadlines."""
    command = [
        sys.executable,
        "-m",
        "tests.benchmark",
        "--worker",
        "--worker-input",
        str(path),
        "--worker-output",
        str(worker_output),
        "--worker-config",
        json.dumps(config, separators=(",", ":")),
        "--worker-metadata",
        json.dumps(metadata, separators=(",", ":")),
    ]
    started = time.perf_counter()
    instance_deadline = min(started + instance_timeout, global_deadline)
    process = subprocess.Popen(
        command,
        cwd=str(PROJECT_ROOT),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=(os.name == "posix"),
    )

    allowed = instance_deadline - time.perf_counter()
    if allowed <= 0:
        terminate_process(process)
        _, stderr = process.communicate()
        return {
            **result_base(metadata, config),
            "status": "timeout",
            "wall_seconds": time.perf_counter() - started,
            "timeout_seconds": instance_timeout,
            "stderr": stderr.strip(),
        }

    try:
        _, stderr = process.communicate(timeout=allowed)
    except subprocess.TimeoutExpired:
        terminate_process(process)
        _, stderr = process.communicate()
        return {
            **result_base(metadata, config),
            "status": "timeout",
            "wall_seconds": time.perf_counter() - started,
            "timeout_seconds": instance_timeout,
            "stderr": stderr.strip(),
        }

    if worker_output.exists():
        with worker_output.open("r", encoding="utf-8") as result_file:
            return json.load(result_file)

    return {
        **result_base(metadata, config),
        "status": "error",
        "wall_seconds": time.perf_counter() - started,
        "error": "worker exited with status {} without a result".format(
            process.returncode
        ),
        "stderr": stderr.strip(),
    }
