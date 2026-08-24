import unittest
from typing import Any, cast

import clsat


class SolverApiTests(unittest.TestCase):
    def test_vsids_heuristic_is_accepted(self) -> None:
        solver = clsat.Sat([[1]])

        solver.solve(
            algorithm="cdcl",
            implication_point="uip",
            preprocess=[],
            inprocessing=[],
            heuristics="vsids",
        )

        self.assertIsNotNone(solver.model)

    def test_removed_random_heuristic_is_rejected(self) -> None:
        solver = clsat.Sat([[1]])

        with self.assertRaisesRegex(ValueError, "allowed value is: vsids"):
            solver.solve(
                algorithm="cdcl",
                implication_point="uip",
                preprocess=[],
                inprocessing=[],
                heuristics=cast(Any, "random"),
            )


if __name__ == "__main__":
    unittest.main()
