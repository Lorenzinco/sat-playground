"""Generate reproducible non-gate-dominated benchmark families.

Run: python -m tests.generate_ges_benchmarks
Existing CNFs are verified and preserved, so interrupted generation can resume.
Filenames are zero-padded by the primary size parameter, making lexical order
follow nominal difficulty within each family.
"""

import argparse
import json
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterator, Optional, Tuple

import networkx as nx


ROOT = Path(__file__).resolve().parent / "benchmark"
CNFGEN = Path(sys.executable).with_name("cnfgen")
SEEDS = range(1, 6)
PITFALL_SIZES = range(10, 151, 5)
COLORING_SIZES = range(20, 301, 10)
ISOMORPHISM_SIZES = range(12, 99, 2)


@dataclass(frozen=True)
class Specification:
    family: str
    filename: str
    seed: int
    args: Tuple[str, ...]
    expected: str
    parameters: Dict[str, object]
    graph_pair: Optional[Tuple[int, int]] = None


def specifications() -> Iterator[Specification]:
    # Uniform random 3-SAT around the finite-size phase transition m/n ~= 4.26.
    for variables in range(50, 431, 20):
        clauses = (426 * variables + 50) // 100
        for seed in SEEDS:
            yield Specification(
                "random-3sat-phase",
                "phase3-n{:03d}-m{:04d}-s{}.cnf".format(variables, clauses, seed),
                seed,
                ("randkcnf", "3", str(variables), str(clauses)),
                "unknown",
                {"width": 3, "variables": variables, "clauses": clauses, "ratio": 4.26},
            )

    # Scale the misleading part with the underlying Tseitin graph on a regular
    # grid. Use one deterministic seed because file size reaches about 375 MiB.
    for vertices in PITFALL_SIZES:
        pitfall_variables = max(6, (2 * vertices + 1) // 3)
        safety_variables = max(3, vertices // 9)
        for seed in (1,):
            yield Specification(
                "pitfall",
                "pitfall-v{:03d}-s{}.cnf".format(vertices, seed),
                seed,
                (
                    "pitfall",
                    str(vertices),
                    "4",
                    str(pitfall_variables),
                    str(safety_variables),
                    "4",
                ),
                "unsat",
                {
                    "vertices": vertices,
                    "degree": 4,
                    "pitfall_variables": pitfall_variables,
                    "safety_variables": safety_variables,
                    "copies": 4,
                },
            )

    # Random 5-regular graphs sit close to the 3-colorability transition and
    # avoid changing graph density as n grows. The regular grid extends into
    # the range where plain UIP starts taking tens of seconds.
    for vertices in COLORING_SIZES:
        for seed in SEEDS:
            yield Specification(
                "random-3coloring",
                "color3-reg5-n{:03d}-s{}.cnf".format(vertices, seed),
                seed,
                ("kcolor", "3", "gnd", str(vertices), "5"),
                "unknown",
                {"colors": 3, "vertices": vertices, "graph_degree": 5},
            )

    # Encode pairs of independently generated, explicitly non-isomorphic
    # 3-regular graphs on a regular grid. Equal degrees avoid trivial
    # degree-sequence rejection. Use one deterministic seed because the dense
    # encoding grows quickly. Stop below 100, where CNFgen 0.9.5 misencodes
    # these GML graph pairs.
    for vertices in ISOMORPHISM_SIZES:
        for seed in (1,):
            yield Specification(
                "graph-isomorphism",
                "iso-reg3-n{:03d}-s{}.cnf".format(vertices, seed),
                seed,
                (),
                "unsat",
                {"vertices": vertices, "graph_degree": 3},
                graph_pair=(vertices, 3),
            )


def non_isomorphic_graph_pair(vertices: int, degree: int, seed: int):
    first_seed = vertices * 10_000 + seed * 100
    second_seed = first_seed + 1
    first = nx.random_regular_graph(degree, vertices, seed=first_seed)
    second = nx.random_regular_graph(degree, vertices, seed=second_seed)
    while nx.is_isomorphic(first, second):
        second_seed += 1
        second = nx.random_regular_graph(degree, vertices, seed=second_seed)
    return first, second, first_seed, second_seed


def cnfgen_invocation(spec: Specification, temporary: Path):
    parameters = dict(spec.parameters)
    if spec.graph_pair is None:
        args = spec.args
        display_args = list(args)
    else:
        vertices, degree = spec.graph_pair
        first, second, first_seed, second_seed = non_isomorphic_graph_pair(
            vertices, degree, spec.seed
        )
        first_path = temporary / "first.gml"
        second_path = temporary / "second.gml"
        nx.write_gml(first, first_path)
        nx.write_gml(second, second_path)
        args = ("iso", str(first_path), "-e", str(second_path))
        display_args = [
            "iso",
            "random-regular(n={},d={},seed={})".format(vertices, degree, first_seed),
            "-e",
            "random-regular(n={},d={},seed={})".format(vertices, degree, second_seed),
        ]
        parameters.update(first_graph_seed=first_seed, second_graph_seed=second_seed)

    command = [str(CNFGEN), "--seed", str(spec.seed), *args]
    display_command = ["cnfgen", "--seed", str(spec.seed), *display_args]
    return command, display_command, parameters


def generate(spec: Specification):
    destination = ROOT / spec.family / spec.filename
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="cnfgen-") as temporary_name:
        command, display_command, parameters = cnfgen_invocation(
            spec, Path(temporary_name)
        )
        if not destination.exists():
            temporary_output = destination.with_suffix(".cnf.tmp")
            try:
                with temporary_output.open("w", encoding="utf-8") as output:
                    subprocess.run(
                        command,
                        stdout=output,
                        stderr=subprocess.PIPE,
                        text=True,
                        check=True,
                        timeout=90,
                    )
                temporary_output.replace(destination)
            finally:
                if temporary_output.exists():
                    temporary_output.unlink()

    with destination.open(encoding="utf-8") as source:
        header = next((line.split() for line in source if line.startswith("p cnf ")), None)
    if header is None:
        raise ValueError("Missing DIMACS header: {}".format(destination))
    return spec.family, {
        "file": spec.filename,
        "expected": spec.expected,
        "parameters": parameters,
        "command": display_command,
        "variables": int(header[2]),
        "clauses": int(header[3]),
        "bytes": destination.stat().st_size,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")

    version = subprocess.check_output([str(CNFGEN), "--version"], text=True).strip()
    specs = list(specifications())
    grouped = {}
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for count, (family, result) in enumerate(pool.map(generate, specs), 1):
            grouped.setdefault(family, []).append(result)
            if count % 25 == 0 or count == len(specs):
                print("Generated/verified {}/{}".format(count, len(specs)), flush=True)

    notes = {
        "random-3sat-phase": "Uniform random 3-CNF at clause/variable ratio 4.26; SAT status is intentionally not assumed.",
        "pitfall": "Unsatisfiable Pitfall formulas with scaled misleading and safety variables.",
        "random-3coloring": "3-colorability of random 5-regular graphs near the transition; SAT status is intentionally not assumed.",
        "graph-isomorphism": "Unsatisfiable isomorphism formulas for deterministic non-isomorphic random 3-regular graph pairs.",
    }
    for family, results in grouped.items():
        expected_values = sorted({result["expected"] for result in results})
        manifest = {
            "generator": version,
            "networkx": nx.__version__,
            "expected": expected_values[0] if len(expected_values) == 1 else "mixed",
            "notes": notes[family],
            "instances": results,
        }
        (ROOT / family / "manifest.json").write_text(
            json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
        )
        print(
            "{}: {} instances, {:.1f} MiB".format(
                family,
                len(results),
                sum(result["bytes"] for result in results) / 2**20,
            ),
            flush=True,
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
