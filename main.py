import clsat

def parse_dimacs(filename):
    clauses = []

    with open(filename, "r") as f:
        for line in f:
            line = line.strip()

            if not line or line.startswith("c") or line.startswith("p"):
                continue

            clause = [int(x) for x in line.split() if x != "0"]
            if clause:
                clauses.append(clause)

    return clauses


def main():
    clauses = parse_dimacs("input.dimacs")
    s = clsat.Sat(clauses)

    print("c Solving SAT problem...", flush=True)
    s.solve(
        algorithm="cdcl",
        implication_point="dip",
        preprocess=["bva"],
        heuristics="vsids",
        drat_path="proof.drat"
    )

    if s.model is not None:
        print("s SATISFIABLE", flush=True)
        print(s.model)
    else:
        print("s UNSATISFIABLE", flush=True)

    if s.stats is not None:
        print(s.stats)


if __name__ == "__main__":
    main()