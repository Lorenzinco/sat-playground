"""Generate the reproducible OR-substituted Tseitin instances; never runs a solver.

Run: python -m tests.generate_or_benchmarks
Existing files are preserved, allowing interrupted generation to resume.
"""

import argparse
import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path


ROOT = Path(__file__).resolve().parent / "benchmark"
CNFGEN = Path(sys.executable).with_name("cnfgen")


def specifications():
    for n in range(10, 50):
        for seed in range(1, 6):
            yield "tseitin-4-regular-or2", "tseitin-n{:03d}-s{}.cnf".format(n, seed), seed, [
                "tseitin", str(n), "4", "-T", "or", "2"
            ], {"vertices": n, "degree": 4, "seed": seed}

    # Unique rectangular grids, excluding transposed duplicates, ordered by area.
    grids = sorted(
        ((rows, cols) for rows in range(2, 22) for cols in range(rows, 22)),
        key=lambda shape: (shape[0] * shape[1], shape),
    )[:200]
    for rank, (rows, cols) in enumerate(grids, 1):
        yield "tseitin-grid-or2", "grid-{:03d}-{:02d}x{:02d}.cnf".format(rank, rows, cols), 1, [
            "tseitin", "first", "grid", str(rows), str(cols), "-T", "or", "2"
        ], {"rows": rows, "columns": cols, "vertices": rows * cols, "charge": "first"}



def generate(spec):
    family, filename, seed, args, parameters = spec
    destination = ROOT / family / filename
    destination.parent.mkdir(parents=True, exist_ok=True)
    command = [str(CNFGEN), "--seed", str(seed)] + args
    if not destination.exists():
        temporary = destination.with_suffix(".cnf.tmp")
        try:
            with temporary.open("w", encoding="utf-8") as output:
                subprocess.run(command, stdout=output, stderr=subprocess.PIPE,
                               text=True, check=True, timeout=90)
            temporary.replace(destination)
        finally:
            if temporary.exists():
                temporary.unlink()
    with destination.open(encoding="utf-8") as source:
        header = next((line.split() for line in source if line.startswith("p cnf ")), None)
    if header is None:
        raise ValueError("Missing DIMACS header: {}".format(destination))
    return family, {
        "file": filename,
        "expected": "unsat",
        "parameters": parameters,
        "command": ["cnfgen", "--seed", str(seed)] + args,
        "variables": int(header[2]),
        "clauses": int(header[3]),
        "bytes": destination.stat().st_size,
    }


def main():
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
            if count % 50 == 0:
                print("Generated/verified {}/{}".format(count, len(specs)), flush=True)
    for family, results in grouped.items():
        manifest = {
            "generator": version,
            "expected": "unsat",
            "notes": "OR substitution preserves satisfiability; seeded random regular graphs provide independent Tseitin instances.",
            "instances": results,
        }
        (ROOT / family / "manifest.json").write_text(
            json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
        )
        print("{}: {} instances, {:.1f} MiB".format(
            family, len(results), sum(item["bytes"] for item in results) / 2**20
        ), flush=True)


if __name__ == "__main__":
    main()
