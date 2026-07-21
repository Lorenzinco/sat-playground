import tempfile
import unittest
from pathlib import Path
from typing import Any, Dict, List, Optional

import clsat

from reductions import Reduction


SOLVE_OPTIONS: Dict[str, Any] = {
    "algorithm": "cdcl",
    "preprocess": [],
    "inprocessing": [],
    "heuristics": "vsids",
}


def require_stats(solver: clsat.Sat) -> clsat.Stats:
    stats = solver.stats
    if stats is None:
        raise AssertionError("solver did not publish stats")
    return stats


class GuidanceIntegrationTests(unittest.TestCase):
    def test_guidance_is_disabled_by_default(self):
        instance = Reduction("php", 2)
        solver = clsat.Sat(instance.clauses)

        solver.solve(implication_point="dip", **SOLVE_OPTIONS)
        stats = require_stats(solver)

        self.assertEqual(stats.guidance_checks, 0)
        self.assertEqual(stats.guidance_matches, 0)
        self.assertEqual(stats.guidance_unique_matches, 0)
        self.assertEqual(stats.guidance_stages_completed, 0)

    def test_dip_extensions_are_observed_and_logged(self):
        instance = Reduction("php", 4)
        solver = clsat.Sat(instance.clauses)

        with tempfile.TemporaryDirectory() as directory:
            log_path = Path(directory) / "guidance.log"
            solver.solve(
                implication_point="dip",
                extension_guidance=instance.extension_guidance,
                extension_guidance_log_path=str(log_path),
                **SOLVE_OPTIONS,
            )

            contents = log_path.read_text(encoding="utf-8")

        stats = require_stats(solver)
        self.assertGreater(stats.guidance_checks, 0)
        self.assertGreater(stats.extension_literals, 0)
        self.assertGreaterEqual(stats.guidance_checks, stats.extension_literals)
        self.assertEqual(
            len(
                [
                    line
                    for line in contents.splitlines()
                    if line.startswith("dip actual=")
                ]
            ),
            stats.guidance_checks,
        )
        self.assertIn("suggestion_before=", contents)
        self.assertIn("summary checks=", contents)

    def test_guidance_without_a_path_tracks_stats_without_creating_a_log(self):
        instance = Reduction("php", 4)
        solver = clsat.Sat(instance.clauses)

        solver.solve(
            implication_point="dip",
            extension_guidance=instance.extension_guidance,
            **SOLVE_OPTIONS,
        )

        self.assertGreater(require_stats(solver).guidance_checks, 0)

    def test_log_path_requires_guidance(self):
        solver = clsat.Sat([[1]])

        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(
                ValueError, "extension_guidance_log_path requires extension_guidance"
            ):
                solver.solve(
                    implication_point="uip",
                    extension_guidance_log_path=str(Path(directory) / "unused.log"),
                    **SOLVE_OPTIONS,
                )

    def test_uip_mode_writes_an_empty_guidance_summary(self):
        instance = Reduction("php", 2)
        solver = clsat.Sat(instance.clauses)

        with tempfile.TemporaryDirectory() as directory:
            log_path = Path(directory) / "uip-guidance.log"
            solver.solve(
                implication_point="uip",
                extension_guidance=instance.extension_guidance,
                extension_guidance_log_path=str(log_path),
                **SOLVE_OPTIONS,
            )
            contents = log_path.read_text(encoding="utf-8")

        self.assertEqual(require_stats(solver).guidance_checks, 0)
        self.assertIn("summary checks=0 matches=0", contents)
        self.assertNotIn("dip actual=", contents)

    def test_malformed_guidance_is_rejected_before_solving(self):
        solver = clsat.Sat([[1]])
        malformed: List[Optional[Dict[str, object]]] = [
            None,
            {"schema_version": 1, "kind": "pigeonhole_cook", "holes": 2},
            {"schema_version": 2, "kind": "pigeonhole_cook", "holes": 0},
            {
                "schema_version": 2,
                "kind": "static_and_dag",
                "original_variables": 2,
                "operands": [[1, 3]],
            },
        ]

        # None is the valid disabled value; every actual malformed dictionary fails.
        solver.solve(
            implication_point="uip",
            extension_guidance=malformed[0],
            **SOLVE_OPTIONS,
        )
        for guidance in malformed[1:]:
            with self.assertRaises(ValueError):
                clsat.Sat([[1]]).solve(
                    implication_point="uip",
                    extension_guidance=guidance,
                    **SOLVE_OPTIONS,
                )


if __name__ == "__main__":
    unittest.main()
