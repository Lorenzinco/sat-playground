import unittest

import clsat


class SolverApiTests(unittest.TestCase):
    def test_ges_variants_are_accepted(self):
        for process in ("ges", "ges_always", "ges_lbd", "ges_par", "ges_random", "ges_vsids"):
            for phase in ("preprocess", "inprocessing"):
                for clauses, satisfiable in (([[1, 2], [-1, 2]], True), ([[1], [-1]], False)):
                    with self.subTest(process=process, phase=phase, satisfiable=satisfiable):
                        options = {"preprocess": [], "inprocessing": []}
                        options[phase] = [process]
                        solver = clsat.Sat(clauses)
                        solver.solve(
                            algorithm="cdcl", implication_point="uip",
                            heuristics="vsids", **options,
                        )
                        self.assertEqual(solver.model is not None, satisfiable)
                        if satisfiable:
                            self.assertTrue(all(
                                any(solver.model[abs(lit) - 1] == (lit > 0) for lit in clause)
                                for clause in clauses
                            ))

    def test_vsids_improvement_counter_is_zero_readonly_and_displayed(self):
        solver = clsat.Sat([[1]])
        solver.solve(
            algorithm="cdcl", implication_point="uip", heuristics="vsids",
            preprocess=[], inprocessing=[],
        )
        self.assertEqual(solver.stats.ges_vsids_improvements, 0)
        self.assertIn("GES VSIDS improvements", str(solver.stats))
        with self.assertRaises(AttributeError):
            solver.stats.ges_vsids_improvements = 1

    def test_unknown_process_lists_ges_variants(self):
        for phase in ("preprocess", "inprocessing"):
            with self.subTest(phase=phase):
                options = {"preprocess": [], "inprocessing": []}
                options[phase] = ["unknown_process"]
                with self.assertRaises(ValueError) as error:
                    clsat.Sat([[1]]).solve(
                        algorithm="cdcl", implication_point="uip",
                        heuristics="vsids", **options,
                    )
                self.assertIn("unknown_process", str(error.exception))
                self.assertIn("bva, bve, ges, ges_always, ges_lbd, ges_par, ges_random, ges_vsids, subsumption", str(error.exception))
