import itertools
import json
import tempfile
import unittest
from pathlib import Path
from typing import Any, Dict, List, Set, Tuple, cast

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


def php_matrix(holes):
    return [
        [pigeon * holes + hole + 1 for hole in range(holes)]
        for pigeon in range(holes + 1)
    ]


def php_first_cook_choices(guidance):
    """Interpret the schema-v2 pigeonhole kind's diagonal first-choice rule."""
    if guidance["kind"] != "pigeonhole_cook":
        raise ValueError("unsupported pigeonhole guidance kind")

    holes = cast(int, guidance["holes"])
    matrix = php_matrix(holes)
    choices: Set[Tuple[int, int]] = set()
    for first_row in range(holes + 1):
        for second_row in range(first_row + 1, holes + 1):
            for first_column in range(holes):
                for second_column in range(holes):
                    if first_column != second_column:
                        choices.add(
                            normalized_pair(
                                matrix[first_row][first_column],
                                matrix[second_row][second_column],
                            )
                        )
    return choices


class ReductionTests(unittest.TestCase):
    def test_package_has_one_public_api(self):
        self.assertEqual(reductions.__all__, ["Reduction"])
        namespace: Dict[str, Any] = {}
        exec("from reductions import *", namespace)
        self.assertEqual(
            {name for name in namespace if name != "__builtins__"}, {"Reduction"}
        )
        self.assertFalse(hasattr(reductions, "reduction"))

    def test_pigeonhole_encoding(self):
        instance = Reduction("pigehole", 2)

        self.assertEqual(instance.problem, "pigeonhole")
        self.assertEqual(instance.num_variables, 6)
        self.assertEqual(
            instance.clauses,
            [
                [1, 2],
                [3, 4],
                [5, 6],
                [-1, -3],
                [-1, -5],
                [-3, -5],
                [-2, -4],
                [-2, -6],
                [-4, -6],
            ],
        )
        self.assertFalse(brute_force_satisfiable(instance.clauses, 6))

    def test_pigeonhole_encoding_dimensions(self):
        for holes in range(1, 5):
            instance = Reduction("php", holes)
            pigeons = holes + 1
            expected_clauses = pigeons + holes * pigeons * (pigeons - 1) // 2

            self.assertEqual(instance.num_variables, pigeons * holes)
            self.assertEqual(len(instance.clauses), expected_clauses)
            self.assertEqual(instance.clauses[:pigeons], php_matrix(holes))
            self.assertTrue(
                all(
                    1 <= abs(literal) <= instance.num_variables
                    for clause in instance.clauses
                    for literal in clause
                )
            )

        self.assertFalse(brute_force_satisfiable(Reduction("php", 1).clauses, 2))

    def test_pigeonhole_guidance_has_exact_schema_v2_essentials(self):
        instance = Reduction("php", 3)

        self.assertEqual(
            instance.extension_guidance,
            {"schema_version": 2, "kind": "pigeonhole_cook", "holes": 3},
        )
        self.assertEqual(instance.metadata["variable_matrix"], php_matrix(3))

    def test_pigeonhole_kind_represents_every_first_cook_choice(self):
        instance = Reduction("php", 3)
        matrix = cast(List[List[int]], instance.metadata["variable_matrix"])

        from_all_pivots: Set[Tuple[int, int]] = set()
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

        from_schema_kind = php_first_cook_choices(instance.extension_guidance)
        self.assertEqual(from_schema_kind, from_all_pivots)
        self.assertEqual(len(from_schema_kind), 6 * 3 * 2)

    def test_pigeonhole_guidance_size_only_changes_with_integer_digits(self):
        adjusted_lengths = set()
        for holes in (1, 2, 9, 10, 20):
            guidance = Reduction("php", holes).extension_guidance
            encoded = json.dumps(guidance, separators=(",", ":"))
            adjusted_lengths.add(len(encoded) - len(str(holes)))

        self.assertEqual(len(adjusted_lengths), 1)

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

    def test_tseitin_guidance_has_exact_compact_schema(self):
        instance = Reduction("tseitin", 6)
        guidance = instance.extension_guidance

        self.assertEqual(
            set(guidance),
            {"schema_version", "kind", "original_variables", "operands"},
        )
        self.assertEqual(guidance["schema_version"], 2)
        self.assertEqual(guidance["kind"], "static_and_dag")
        self.assertEqual(guidance["original_variables"], instance.num_variables)

        self.assertNotIn("steps", guidance)
        self.assertNotIn("total_variables", guidance)

    def test_tseitin_implicit_results_form_a_valid_dependency_dag(self):
        instance = Reduction("tseitin", 6)
        guidance = instance.extension_guidance
        original_variables = cast(int, guidance["original_variables"])
        operands = cast(List[List[int]], guidance["operands"])
        available = set(range(1, original_variables + 1))

        self.assertTrue(operands)
        for index, pair in enumerate(operands):
            self.assertEqual(len(pair), 2)
            left, right = pair
            self.assertIsInstance(left, int)
            self.assertIsInstance(right, int)
            self.assertNotEqual(left, 0)
            self.assertNotEqual(right, 0)
            self.assertIn(abs(left), available)
            self.assertIn(abs(right), available)

            implicit_result = original_variables + index + 1
            self.assertNotIn(implicit_result, available)
            available.add(implicit_result)

        self.assertIn(
            abs(cast(int, instance.metadata["global_parity_literal"])), available
        )
        self.assertEqual(len(available), original_variables + len(operands))

    def test_static_extension_operands_encode_signed_and_truth_table(self):
        instance = Reduction("tseitin", 4)
        guidance = instance.extension_guidance
        original_variables = cast(int, guidance["original_variables"])
        operands = cast(List[List[int]], guidance["operands"])
        all_literals = [literal for pair in operands for literal in pair]

        self.assertTrue(any(literal < 0 for literal in all_literals))
        self.assertTrue(any(literal > 0 for literal in all_literals))

        for index, (left, right) in enumerate(operands):
            result = original_variables + index + 1
            clauses = [
                [result, -left, -right],
                [-result, left],
                [-result, right],
            ]
            variables = sorted({abs(left), abs(right), result})

            for values in itertools.product((False, True), repeat=len(variables)):
                assignment = dict(zip(variables, values))
                encoded = satisfies(clauses, assignment)
                left_value = assignment[abs(left)] == (left > 0)
                right_value = assignment[abs(right)] == (right > 0)
                expected = assignment[result] == (left_value and right_value)
                self.assertEqual(encoded, expected)

    def test_rust_data_is_json_serializable(self):
        for instance in (Reduction("php", 4), Reduction("tseitin", 6)):
            data = instance.as_rust_data()
            decoded = json.loads(json.dumps(data))

            self.assertEqual(decoded, data)
            self.assertEqual(decoded["num_variables"], instance.num_variables)
            self.assertEqual(decoded["clauses"], instance.clauses)
            self.assertEqual(decoded["extension_guidance"]["schema_version"], 2)

    def test_dimacs_header_body_and_write(self):
        instance = Reduction("tseitin", 4)
        contents = instance.to_dimacs()
        lines = contents.splitlines()
        expected_header = "p cnf {} {}".format(
            instance.num_variables, len(instance.clauses)
        )

        self.assertTrue(contents.endswith("\n"))
        self.assertEqual(lines[0], expected_header)
        self.assertEqual(len(lines) - 1, len(instance.clauses))
        parsed_clauses = [list(map(int, line.split()[:-1])) for line in lines[1:]]
        self.assertTrue(all(line.split()[-1] == "0" for line in lines[1:]))
        self.assertEqual(parsed_clauses, instance.clauses)

        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "instance.cnf"
            instance.write_dimacs(path)
            self.assertEqual(path.read_text(encoding="ascii"), contents)

    def test_invalid_sizes_and_arguments(self):
        for size in (0, -1):
            with self.assertRaises(ValueError):
                Reduction("pigeonhole", size)
        for size in (-2, 0, 2, 3, 5):
            with self.assertRaises(ValueError):
                Reduction("tseitin", size)

        for size in cast(List[Any], [True, 2.0, "2"]):
            with self.assertRaises(TypeError):
                Reduction("php", size)
        with self.assertRaises(TypeError):
            Reduction(cast(Any, 1), 2)
        with self.assertRaises(TypeError):
            Reduction("tseitin", 4, seed=True)
        with self.assertRaises(ValueError):
            Reduction("unknown", 2)


if __name__ == "__main__":
    unittest.main()
