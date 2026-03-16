import clsat
import multiprocessing as mp
import time

def parse_dimacs(filename):
    with open(filename, 'r') as f:
        lines = f.readlines()
    clauses = []
    for line in lines:
        if line.startswith('c') or line.startswith('p'):
            continue
        clause = [int(x) for x in line.split() if x != '0']
        if clause:
            clauses.append(clause)
    return clauses


def solve_sat(clauses):
    s = clsat.Sat(clauses)
    print("Solving SAT problem...",flush=True)
    start = time.time() * 1000
    s.solve(algorithm="dpll")
    end = time.time() * 1000
    print(f"Elapsed: {end-start}ms")
    if s.model is not None:
        print("SAT", flush=True)
    else:
        print("UNSAT",flush=True)

if __name__ == "__main__":
    p = mp.Process(target=solve_sat, args=(parse_dimacs('input.dimacs'),))
    p.start()
    p.join()