"""Repository entrypoint.

By default this runs the benchmark orchestrator. The previous single-formula
example remains available as ``python main.py solve-example``.
"""

import sys
from pathlib import Path
from typing import List, Optional, Sequence

import clsat

from tests.benchmark import main as benchmark_main


def parse_dimacs(filename: Path) -> List[List[int]]:
    clauses: List[List[int]] = []
    with filename.open("r", encoding="utf-8") as source:
        for line in source:
            line = line.strip()
            if not line or line.startswith("c") or line.startswith("p"):
                continue
            clause = [int(value) for value in line.split() if value != "0"]
            if clause:
                clauses.append(clause)
    return clauses


def solve_example() -> None:
    clauses = parse_dimacs(Path("tests/benchmark/randkxor/randkxor-3-or-2-n360-s3.cnf"))
    solver = clsat.Sat(clauses)
    print("c Solving SAT problem...", flush=True)
    solver.solve(
        algorithm="cdcl",
        implication_point="dip",
        preprocess=["bva"],
        heuristics="vsids",
        drat_path="proof.drat",
        inprocessing=["bva"],
    )

    if solver.model is not None:
        print("s SATISFIABLE", flush=True)
        solution = ""
        for index, value in enumerate(solver.model):
            solution += "{} ".format(index + 1 if value else -(index + 1))
        print(solution)
    else:
        print("s UNSATISFIABLE", flush=True)

    if solver.stats is not None:
        print(solver.stats)


def main(argv: Optional[Sequence[str]] = None) -> int:
    arguments = list(sys.argv[1:] if argv is None else argv)
    if arguments and arguments[0] == "benchmark":
        return benchmark_main(arguments[1:])
    else:
        solve_example()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
