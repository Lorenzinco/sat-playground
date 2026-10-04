import unittest

import clsat


class SolverApiTests(unittest.TestCase):
    def test_bva_preprocessing_preserves_model_and_reports_factors(self):
        clauses = [[a, b] for a in (1, 2) for b in (3, 4, 5, 6)]
        solver = clsat.Sat(clauses)
        solver.solve(
            algorithm="cdcl", implication_point="uip", heuristics="vsids",
            preprocess=["bva"], inprocessing=["bva"],
        )
        self.assertIsNotNone(solver.model)
        self.assertTrue(all(
            any(solver.model[abs(lit) - 1] == (lit > 0) for lit in clause)
            for clause in clauses
        ))
        self.assertEqual(solver.stats.bva_literals, 1)
        self.assertEqual(solver.stats.bva_budget_exhaustions, 0)

    def test_ges_variants_are_accepted(self):
        for process in ("ges", "ges_always", "ges_lbd", "ges_par", "ges_random", "ges_vsids", "ges_utility", "ges_compress", "ges_trail", "preference"):
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

    def test_vivification_names_and_solve_modes_are_accepted(self):
        for process in ("vivification", "vivify"):
            for phase in ("preprocess", "inprocessing"):
                for mode in ("uip", "dip"):
                    for clauses, satisfiable in (
                        ([[1, 2], [-1, 2]], True),
                        ([[1, 2], [-1, 2], [1, -2], [-1, -2]], False),
                    ):
                        with self.subTest(process=process, phase=phase, mode=mode,
                                          satisfiable=satisfiable):
                            options = {"preprocess": [], "inprocessing": []}
                            options[phase] = [process]
                            solver = clsat.Sat(clauses)
                            solver.solve(algorithm="cdcl", implication_point=mode,
                                         heuristics="vsids", **options)
                            self.assertEqual(solver.model is not None, satisfiable)
                            if satisfiable:
                                self.assertTrue(all(
                                    any(solver.model[abs(lit)] == (lit > 0)
                                        for lit in clause)
                                    for clause in clauses
                                ))

    def test_vivification_counters_are_zero_readonly_and_displayed_by_default(self):
        solver = clsat.Sat([[1]])
        solver.solve(algorithm="cdcl", implication_point="uip", heuristics="vsids",
                     preprocess=[], inprocessing=[])
        for field, label in (
            ("vivification_passes", "Vivification passes"),
            ("vivification_clauses_tried", "Vivification clauses tried"),
            ("vivification_clauses_strengthened", "Vivification strengthened"),
            ("vivification_literals_removed", "Vivification lits removed"),
            ("vivification_propagation_ticks", "Vivification prop ticks"),
            ("vivification_budget_exhaustions", "Vivification budget exhaust"),
            ("vivification_units", "Vivification units"),
        ):
            with self.subTest(field=field):
                self.assertEqual(getattr(solver.stats, field), 0)
                self.assertIn(label, str(solver.stats))
                with self.assertRaises(AttributeError):
                    setattr(solver.stats, field, 1)

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

    def test_ges_literals_added_is_exposed_readonly_and_displayed(self):
        solver = clsat.Sat([[1]])
        solver.solve(
            algorithm="cdcl", implication_point="uip", heuristics="vsids",
            preprocess=[], inprocessing=[],
        )
        self.assertEqual(solver.stats.ges_literals_added, 0)
        self.assertIn("GES literals added", str(solver.stats))
        with self.assertRaises(AttributeError):
            solver.stats.ges_literals_added = 1

    def test_utility_improvement_counter_is_zero_readonly_and_displayed(self):
        solver = clsat.Sat([[1]])
        solver.solve(
            algorithm="cdcl", implication_point="uip", heuristics="vsids",
            preprocess=[], inprocessing=[],
        )
        self.assertEqual(solver.stats.ges_utility_improvements, 0)
        self.assertIn("GES utility improvements", str(solver.stats))
        with self.assertRaises(AttributeError):
            solver.stats.ges_utility_improvements = 1

    def test_preference_counters_are_exposed_and_displayed(self):
        solver = clsat.Sat([[1]])
        solver.solve(
            algorithm="cdcl", implication_point="uip", heuristics="vsids",
            preprocess=[], inprocessing=["preference"],
        )
        for field in (
            "preference_passes", "preference_candidates", "preference_skipped_dependents",
            "preference_skipped_assigned", "preference_root_assigned_true",
            "preference_root_assigned_false", "preference_root_assigned_unique",
            "preference_root_rebuilds", "preference_skipped_unsafe",
            "preference_extensions_retired", "preference_clauses_added",
            "preference_clauses_removed", "preference_learned_positive_dropped",
        ):
            self.assertEqual(getattr(solver.stats, field), 0)
            with self.assertRaises(AttributeError):
                setattr(solver.stats, field, 1)
        self.assertIn("Preference extensions retired", str(solver.stats))

    def test_extension_preference_is_exposed_in_python_stats(self):
        solver = clsat.Sat([[1]])
        solver.solve(
            algorithm="cdcl", implication_point="uip", heuristics="vsids",
            preprocess=[], inprocessing=[],
        )
        self.assertEqual(solver.stats.ges_extension_preference, {})
        self.assertEqual(solver.stats.preference, {})
        self.assertNotIn("GES ext ", str(solver.stats))

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
                self.assertIn("bva, bve, ges, ges_always, ges_lbd, ges_par, ges_random, ges_vsids, ges_utility, ges_compress, ges_trail, preference, subsumption, vivification, vivify", str(error.exception))
