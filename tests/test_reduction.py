import itertools
import json
import tempfile
import unittest
from pathlib import Path
from typing import Any, Dict, List, cast

import reductions
from reductions import Reduction


def satisfies(clauses, assignment):
    return all(
        any(assignment[abs(literal)] == (literal > 0) for literal in clause)
        for clause in clauses
    )


def brute_force_satisfiable(clauses, variables):
    for values in itertools.product((False, True), repeat=variables):
        assignment = {index + 1: value for index, value in enumerate(values)}
        if satisfies(clauses, assignment):
            return True
    return False


def normalized_pair(left, right):
    return tuple(sorted((left, right)))


class ReductionTests(unittest.TestCase):
    def test_package_has_one_public_api(self):
        self.assertEqual(reductions.__all__, ["Reduction"])
        self.assertFalse(hasattr(reductions, "reduction"))

    def test_pigeonhole_encoding(self):
        instance = Reduction("pigehole", 2)

        self.assertEqual(instance.problem, "pigeonhole")
        self.assertEqual(instance.num_variables, 6)
        self.assertEqual(len(instance.clauses), 9)
        self.assertFalse(brute_force_satisfiable(instance.clauses, 6))

    def test_pigeonhole_first_choice_rule_covers_every_pivot(self):
        instance = Reduction("php", 3)
        matrix = cast(
            List[List[int]], instance.extension_guidance["initial_matrix"]
        )

        # Explicitly instantiate every Cook pivot and every reduced cell.
        from_all_pivots = set()
        for pivot_row in range(4):
            for pivot_column in range(3):
                for row in range(4):
                    if row == pivot_row:
                        continue
                    for column in range(3):
                        if column == pivot_column:
                            continue
                        from_all_pivots.add(
                            normalized_pair(
                                matrix[row][pivot_column],
                                matrix[pivot_row][column],
                            )
                        )

        # The compact rule says exactly: two diagonal matrix entries.
        from_compact_rule = set()
        for first_row in range(4):
            for second_row in range(first_row + 1, 4):
                for first_column in range(3):
                    for second_column in range(3):
                        if first_column == second_column:
                            continue
                        from_compact_rule.add(
                            normalized_pair(
                                matrix[first_row][first_column],
                                matrix[second_row][second_column],
                            )
                        )

        self.assertEqual(from_compact_rule, from_all_pivots)
        rule = cast(
            Dict[str, bool], instance.extension_guidance["first_choice_rule"]
        )
        self.assertTrue(rule["emit_both_orientations"]) 

    def test_pigeonhole_guidance_scales_as_rules_not_proof_branches(self):
        small = len(json.dumps(Reduction("php", 10).extension_guidance))
        large = len(json.dumps(Reduction("php", 20).extension_guidance))

        # The matrix is quadratic. Enumerating all recursive pivot plans would
        # instead be combinatorial and would violate this loose growth bound.
        self.assertLess(large, small * 6)

    def test_tseitin_is_cubic_odd_and_unsatisfiable(self):
        instance = Reduction("tseitin", 4, seed=7)
        metadata = instance.metadata

        self.assertEqual(instance.num_variables, 6)
        self.assertEqual(len(instance.clauses), 16)
        incident = cast(
            List[Dict[str, List[int]]], metadata["incident_variables"]
        )
        charges = cast(List[int], metadata["charges"])
        self.assertTrue(all(len(item["variables"]) == 3 for item in incident))
        self.assertEqual(sum(charges) % 2, 1)
        self.assertFalse(brute_force_satisfiable(instance.clauses, 6))

    def test_tseitin_guidance_is_a_valid_dependency_dag(self):
        instance = Reduction("tseitin", 6)
        guidance = instance.extension_guidance
        available = set(range(1, instance.num_variables + 1))

        self.assertEqual(guidance["kind"], "static_and_dag")
        steps = cast(List[Dict[str, Any]], guidance["steps"])
        for step in steps:
            self.assertIn(abs(step["left"]), available)
            self.assertIn(abs(step["right"]), available)
            self.assertNotIn(step["result"], available)
            available.add(step["result"])

    def test_static_extension_step_encodes_signed_and(self):
        instance = Reduction("tseitin", 4)
        steps = cast(
            List[Dict[str, Any]], instance.extension_guidance["steps"]
        )
        step = steps[0]
        left = cast(int, step["left"])
        right = cast(int, step["right"])
        result_variable = cast(int, step["result"])
        clauses = [
            [result_variable, -left, -right],
            [-result_variable, left],
            [-result_variable, right],
        ]

        variables = {abs(left), abs(right), result_variable}
        ordered = sorted(variables)
        for values in itertools.product((False, True), repeat=len(ordered)):
            assignment = dict(zip(ordered, values))
            encoded = satisfies(clauses, assignment)
            left_value = assignment[abs(left)] == (left > 0)
            right_value = assignment[abs(right)] == (right > 0)
            expected = assignment[result_variable] == (left_value and right_value)
            self.assertEqual(encoded, expected)

    def test_rust_data_uses_serializable_primitives(self):
        for instance in (Reduction("php", 4), Reduction("tseitin", 6)):
            encoded = json.dumps(instance.as_rust_data())
            decoded = json.loads(encoded)
            self.assertEqual(decoded["num_variables"], instance.num_variables)
            self.assertEqual(decoded["clauses"], instance.clauses)

    def test_dimacs_header_and_write(self):
        instance = Reduction("tseitin", 4)
        expected_header = "p cnf {} {}".format(
            instance.num_variables, len(instance.clauses)
        )
        self.assertEqual(instance.to_dimacs().splitlines()[0], expected_header)

        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "instance.cnf"
            instance.write_dimacs(path)
            self.assertEqual(path.read_text(encoding="ascii"), instance.to_dimacs())

    def test_invalid_sizes(self):
        with self.assertRaises(ValueError):
            Reduction("pigeonhole", 0)
        with self.assertRaises(ValueError):
            Reduction("tseitin", 5)


if __name__ == "__main__":
    unittest.main()
