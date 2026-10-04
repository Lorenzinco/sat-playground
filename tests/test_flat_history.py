"""Public-API regressions for flat clause history and proof logging.

Rebuild the clsat extension before running this module.
"""

import itertools
from pathlib import Path
import random
import shutil
import subprocess
import tempfile
import unittest

import clsat


DRAT_TRIM = shutil.which("drat-trim")
SETTINGS = (
    ("baseline", (), ()),
    ("pre_bva_ges_bva", ("bva",), ("ges", "bva")),
    (
        "pre_viv_ges_viv_preference_bva",
        ("vivification",),
        ("ges", "vivification", "preference", "bva"),
    ),
)


def brute_force_satisfiable(clauses, variables):
    return any(
        all(
            any(assignment[abs(literal) - 1] == (literal > 0)
                for literal in clause)
            for clause in clauses
        )
        for assignment in itertools.product((False, True), repeat=variables)
    )


def pigeonhole(pigeons, holes):
    def variable(pigeon, hole):
        return pigeon * holes + hole + 1

    clauses = [
        [variable(pigeon, hole) for hole in range(holes)]
        for pigeon in range(pigeons)
    ]
    clauses.extend(
        [-variable(left, hole), -variable(right, hole)]
        for hole in range(holes)
        for left in range(pigeons)
        for right in range(left + 1, pigeons)
    )
    return clauses


class FlatHistoryTests(unittest.TestCase):
    def test_random_formulas_match_brute_force_and_original_models(self):
        rng = random.Random(0xF1A7)
        for case in range(100):
            variables = 3 + case % 4
            clauses = []
            for _ in range(rng.randint(1, 6 * variables)):
                clause_variables = rng.sample(
                    range(1, variables + 1), rng.randint(1, min(3, variables))
                )
                clauses.append([
                    variable if rng.getrandbits(1) else -variable
                    for variable in clause_variables
                ])
            # Keep the full original variable range represented in the input.
            clauses.append([variables, -variables])
            expected = brute_force_satisfiable(clauses, variables)
            for implication_point in ("uip", "dip"):
                for name, preprocess, inprocessing in SETTINGS:
                    with self.subTest(case=case, variables=variables,
                                      mode=implication_point, settings=name):
                        solver = clsat.Sat([clause[:] for clause in clauses])
                        solver.solve(
                            algorithm="cdcl",
                            implication_point=implication_point,
                            heuristics="vsids",
                            preprocess=list(preprocess),
                            inprocessing=list(inprocessing),
                        )
                        self.assertEqual(solver.model is not None, expected,
                                         msg=f"Original clauses: {clauses!r}")
                        if expected:
                            # Public models retain index zero; literal v uses index v.
                            self.assertGreater(len(solver.model), variables)
                            self.assertTrue(all(
                                any(solver.model[abs(literal)] == (literal > 0)
                                    for literal in clause)
                                for clause in clauses
                            ), msg=f"Invalid original model for {clauses!r}")

    def verify_unsat_proof(self, clauses, implication_point, preprocess,
                           inprocessing):
        with tempfile.TemporaryDirectory(prefix="flat-history-") as directory:
            cnf = Path(directory) / "original.cnf"
            proof = Path(directory) / "proof.drat"
            variables = max(abs(literal) for clause in clauses for literal in clause)
            cnf.write_text(
                f"p cnf {variables} {len(clauses)}\n"
                + "".join(" ".join(map(str, clause)) + " 0\n"
                          for clause in clauses),
                encoding="ascii",
            )
            solver = clsat.Sat([clause[:] for clause in clauses])
            solver.solve(
                algorithm="cdcl",
                implication_point=implication_point,
                heuristics="vsids",
                preprocess=list(preprocess),
                inprocessing=list(inprocessing),
                drat_path=str(proof),
            )
            self.assertIsNone(solver.model)
            self.assertTrue(proof.is_file(), "Solver did not write a DRAT proof")
            try:
                result = subprocess.run(
                    [DRAT_TRIM, str(cnf), str(proof)],
                    capture_output=True, text=True, timeout=60, check=False,
                )
            except subprocess.TimeoutExpired as error:
                output = (error.stdout or b"") + (error.stderr or b"")
                if isinstance(output, bytes):
                    output = output.decode("utf-8", errors="replace")
                self.fail("drat-trim timed out after 60 seconds:\n" + output[-8000:])
            output = result.stdout + result.stderr
            diagnostic = "drat-trim output (last 8000 characters):\n" + output[-8000:]
            self.assertEqual(result.returncode, 0, diagnostic)
            self.assertIn("s VERIFIED", output, diagnostic)
            return solver.stats.extension_literals

    @unittest.skipUnless(DRAT_TRIM, "drat-trim is not available on PATH")
    def test_unsat_proofs_against_original_cnf(self):
        fixtures = (
            ("contradictory_units", [[1], [-1]]),
            ("four_binary_xor", [[1, 2], [-1, 2], [1, -2], [-1, -2]]),
            ("pigeonhole_5_4", pigeonhole(5, 4)),
            ("pigeonhole_8_7", pigeonhole(8, 7)),
        )
        for fixture, clauses in fixtures:
            for implication_point in ("uip", "dip"):
                for name, preprocess, inprocessing in SETTINGS:
                    with self.subTest(fixture=fixture, mode=implication_point,
                                      settings=name):
                        self.verify_unsat_proof(
                            clauses, implication_point, preprocess, inprocessing
                        )

    @unittest.skipUnless(DRAT_TRIM, "drat-trim is not available on PATH")
    def test_proof_with_observed_runtime_dip_extensions(self):
        extensions = self.verify_unsat_proof(
            pigeonhole(8, 7), "dip", ("bva",), ("ges", "bva")
        )
        if extensions == 0:
            self.skipTest("PHP 8/7 created no runtime DIP extensions in this build")
        self.assertGreater(extensions, 0)


if __name__ == "__main__":
    unittest.main()
