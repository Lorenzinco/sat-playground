import csv
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from tests.compare_benchmarks import (
    comparison_rows,
    main as compare_main,
    pairwise_summary,
    problem_families,
)


class CompareBenchmarksTests(unittest.TestCase):
    def test_runtime_differences_require_both_methods_to_complete(self) -> None:
        problem = "tests/xmaple_paper/family/problem.cnf"
        methods = {
            "base": {
                problem: {
                    "problem": problem,
                    "family": "family",
                    "status": "completed",
                    "wall_seconds": 4.0,
                }
            },
            "ges": {
                problem: {
                    "problem": problem,
                    "family": "family",
                    "status": "completed",
                    "wall_seconds": 2.0,
                }
            },
            "ges_lbd": {
                problem: {
                    "problem": problem,
                    "family": "family",
                    "status": "timeout",
                    "wall_seconds": 10.0,
                }
            },
        }

        rows = comparison_rows(methods, problem_families(methods))

        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["ges_minus_base_seconds"], "-2.000000000")
        self.assertEqual(rows[0]["ges_speedup_vs_base"], "2.000000000")
        self.assertEqual(rows[0]["ges_lbd_wall_seconds"], "10.000000000")
        self.assertEqual(rows[0]["ges_lbd_minus_base_seconds"], "")
        self.assertEqual(rows[0]["ges_lbd_minus_ges_seconds"], "")
        self.assertEqual(rows[0]["all_completed"], "false")
        self.assertEqual(rows[0]["fastest_completed_method"], "ges")

    def test_pairwise_summary_reports_delta_and_geometric_speedup(self) -> None:
        problems = ["a", "b"]
        methods = {
            "base": {
                "a": {"status": "completed", "wall_seconds": 4.0},
                "b": {"status": "completed", "wall_seconds": 8.0},
            },
            "ges": {
                "a": {"status": "completed", "wall_seconds": 2.0},
                "b": {"status": "completed", "wall_seconds": 4.0},
            },
        }

        summary = pairwise_summary(methods, problems, "base", "ges")

        self.assertEqual(summary["comparable_completed_problems"], 2)
        self.assertEqual(summary["second_faster"], 2)
        self.assertEqual(summary["second_minus_first_seconds"]["mean"], -3.0)
        self.assertAlmostEqual(
            summary["second_speedup_vs_first"]["geometric_mean"], 2.0
        )

    def test_script_generates_family_and_overall_outputs_without_solving(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            sources = {
                "base": root / "base",
                "ges": root / "ges",
                "ges_lbd": root / "ges_lbd",
            }
            problem_results = {
                "tests/xmaple_paper/family-a/a.cnf": "family-a",
                "tests/xmaple_paper/family-b/b.cnf": "family-b",
            }
            for method, source in sources.items():
                problem_index = {}
                for position, (problem, family) in enumerate(problem_results.items()):
                    result_path = Path("problems") / (family + ".json")
                    full_result_path = source / result_path
                    full_result_path.parent.mkdir(parents=True, exist_ok=True)
                    full_result_path.write_text(
                        json.dumps(
                            {
                                "problem": problem,
                                "family": family,
                                "status": "completed",
                                "wall_seconds": float(position + 1),
                            }
                        ),
                        encoding="utf-8",
                    )
                    problem_index[problem] = {"result": result_path.as_posix()}
                stale = source / "problems" / "stale.json"
                stale.write_text(
                    json.dumps(
                        {
                            "problem": "stale.cnf",
                            "family": "stale",
                            "status": "completed",
                            "wall_seconds": 0.1,
                        }
                    ),
                    encoding="utf-8",
                )
                (source / "index.json").write_text(
                    json.dumps(
                        {
                            "limits": {"family_timeout_seconds": 5000.0},
                            "problems": problem_index,
                        }
                    ),
                    encoding="utf-8",
                )

            output = root / "comparison"

            def create_plot(
                _pyplot, _name, _method_results, destination, _timeout_seconds
            ):
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(b"plot")

            with patch(
                "tests.compare_benchmarks.plot.import_pyplot", return_value=object()
            ), patch(
                "tests.compare_benchmarks.plot_overlaid_cactus",
                side_effect=create_plot,
            ) as plot_cactus, patch(
                "tests.benchmark.run_problem_subprocess"
            ) as run_problem:
                exit_code = compare_main(
                    [
                        "--base",
                        str(sources["base"]),
                        "--ges",
                        str(sources["ges"]),
                        "--ges-lbd",
                        str(sources["ges_lbd"]),
                        "--output",
                        str(output),
                    ]
                )

            self.assertEqual(exit_code, 0)
            self.assertEqual(plot_cactus.call_count, 3)
            run_problem.assert_not_called()
            self.assertTrue((output / "plots" / "cactus" / "family-a.png").is_file())
            self.assertTrue((output / "plots" / "cactus" / "family-b.png").is_file())
            self.assertTrue((output / "plots" / "cactus" / "overall.png").is_file())

            with (output / "runtime_differences.csv").open(
                "r", encoding="utf-8", newline=""
            ) as source:
                rows = list(csv.DictReader(source))
            self.assertEqual(len(rows), 2)
            self.assertNotIn("stale.cnf", {row["problem"] for row in rows})

            summary = json.loads(
                (output / "summary.json").read_text(encoding="utf-8")
            )
            self.assertEqual(
                set(summary["cactus_plots"]),
                {"family-a", "family-b", "overall"},
            )
            self.assertEqual(
                summary["groups"]["overall"]["methods"]["base"]["problems"], 2
            )


if __name__ == "__main__":
    unittest.main()
