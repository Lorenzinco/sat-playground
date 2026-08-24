import json
import tempfile
import unittest
from collections import Counter
from pathlib import Path
from unittest.mock import patch

from tests.benchmark import (
    BENCHMARK_ROOT,
    MAX_FAMILY_TIMEOUT_SECONDS,
    discover_problems,
    expected_status,
    group_problems_by_family,
    load_saved_results,
    main as benchmark_main,
    parse_args,
    problem_family,
    reference_statuses,
)
from tests.plot import cactus_coordinates
from tests.run import run_worker


class BenchmarkCorpusTests(unittest.TestCase):
    def test_discovers_only_the_xmaple_paper_corpus(self) -> None:
        problems = discover_problems()

        self.assertEqual(len(problems), 987)
        self.assertTrue(all(BENCHMARK_ROOT in path.parents for path in problems))
        families = [problem_family(path) for path in problems]
        self.assertEqual(families, sorted(families))
        self.assertEqual(
            Counter(families),
            {
                "zintervals": 23,
                "randkxor": 785,
                "tseitin-4-regular": 57,
                "tseitin-6-regular": 25,
                "tseitin-grid": 97,
            },
        )
        grouped = group_problems_by_family(reversed(problems))
        self.assertEqual(list(grouped), sorted(grouped))
        self.assertTrue(
            all(paths == sorted(paths) for paths in grouped.values())
        )

    def test_uses_a_separate_five_thousand_second_family_budget(self) -> None:
        args = parse_args([])

        self.assertEqual(args.family_timeout, MAX_FAMILY_TIMEOUT_SECONDS)
        self.assertEqual(args.family_timeout, 5_000.0)
        self.assertFalse(args.plot_cactus)
        self.assertFalse(hasattr(args, "total_timeout"))
        self.assertFalse(hasattr(args, "instance_timeout"))

    def test_parses_plot_cactus_mode(self) -> None:
        self.assertTrue(parse_args(["--plot-cactus"]).plot_cactus)

    def test_cactus_coordinates_are_time_vs_number_solved(self) -> None:
        x_values, y_values = cactus_coordinates(
            [
                {"status": "completed", "wall_seconds": 3},
                {"status": "timeout", "wall_seconds": 10},
                {"status": "completed", "wall_seconds": 1},
                {"status": "completed", "wall_seconds": 2},
            ]
        )

        self.assertEqual(x_values, [0.0, 1.0, 2.0, 3.0])
        self.assertEqual(y_values, [0, 1, 2, 3])
        self.assertEqual(cactus_coordinates([]), ([0.0], [0]))

    def test_saved_result_loader_ignores_unreferenced_json(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            referenced = output / "problems" / "referenced.json"
            referenced.parent.mkdir(parents=True)
            referenced.write_text(
                json.dumps({"problem": "referenced.cnf", "family": "family-a"}),
                encoding="utf-8",
            )
            (referenced.parent / "stale.json").write_text(
                json.dumps({"problem": "stale.cnf", "family": "stale"}),
                encoding="utf-8",
            )
            (output / "index.json").write_text(
                json.dumps(
                    {
                        "problems": {
                            "referenced.cnf": {"result": "problems/referenced.json"}
                        }
                    }
                ),
                encoding="utf-8",
            )

            _, results = load_saved_results(output)

            self.assertEqual([result["problem"] for result in results], ["referenced.cnf"])

    def test_plot_cactus_mode_does_not_run_solver(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            problems = output / "problems"
            problems.mkdir()
            fixtures = {
                "a.json": {
                    "problem": "tests/a.cnf",
                    "family": "family-a",
                    "status": "completed",
                    "wall_seconds": 1.5,
                },
                "b.json": {
                    "problem": "tests/b.cnf",
                    "family": "family-b",
                    "status": "skipped",
                    "wall_seconds": 0.0,
                },
            }
            for filename, result in fixtures.items():
                (problems / filename).write_text(json.dumps(result), encoding="utf-8")
            (output / "index.json").write_text(
                json.dumps(
                    {
                        "limits": {"family_timeout_seconds": 5000.0},
                        "problems": {
                            result["problem"]: {
                                "result": "problems/{}".format(filename)
                            }
                            for filename, result in fixtures.items()
                        },
                    }
                ),
                encoding="utf-8",
            )

            def create_plot(_pyplot, _family, _results, destination, **_kwargs):
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(b"plot")

            with patch("tests.benchmark.plot.import_pyplot", return_value=object()), patch(
                "tests.benchmark.plot.plot_cactus", side_effect=create_plot
            ) as plot_cactus, patch(
                "tests.benchmark.run_problem_subprocess"
            ) as run_problem:
                exit_code = benchmark_main(
                    ["--plot-cactus", "--output", str(output)]
                )

            self.assertEqual(exit_code, 0)
            self.assertEqual(plot_cactus.call_count, 2)
            run_problem.assert_not_called()
            self.assertTrue((output / "plots" / "cactus" / "family-a.png").is_file())
            self.assertTrue((output / "plots" / "cactus" / "family-b.png").is_file())
            index = json.loads((output / "index.json").read_text(encoding="utf-8"))
            self.assertEqual(
                index["cactus_plots"],
                {
                    "family-a": "plots/cactus/family-a.png",
                    "family-b": "plots/cactus/family-b.png",
                },
            )

    def test_loads_reference_statuses_from_the_bundled_summary(self) -> None:
        self.assertEqual(len(reference_statuses()), 987)
        self.assertEqual(
            expected_status(
                BENCHMARK_ROOT / "tseitin-grid" / "first-grid-10-10.cnf"
            ),
            "unsat",
        )
        self.assertEqual(
            expected_status(
                BENCHMARK_ROOT
                / "randkxor"
                / "randkxor-3-or-2-n180-s2.cnf"
            ),
            "sat",
        )
        self.assertEqual(
            expected_status(
                BENCHMARK_ROOT
                / "zintervals"
                / "18416a9ac0909dce5fa96345f784c87e-intervals122.cnf"
            ),
            "unknown",
        )

    def test_unknown_reference_does_not_mark_a_valid_result_incorrect(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            problem = root / "unit.cnf"
            output = root / "result.json"
            problem.write_text("p cnf 1 1\n1 0\n", encoding="utf-8")

            exit_code = run_worker(
                problem,
                output,
                {
                    "algorithm": "cdcl",
                    "implication_point": "uip",
                    "heuristics": "vsids",
                    "preprocess": [],
                    "inprocessing": [],
                },
                {
                    "problem": "tests/xmaple_paper/unit.cnf",
                    "family": "test",
                    "expected": "unknown",
                },
            )

            result = json.loads(output.read_text(encoding="utf-8"))
            self.assertEqual(exit_code, 0)
            self.assertEqual(result["status"], "completed")
            self.assertIsNone(result["correct_classification"])


if __name__ == "__main__":
    unittest.main()
