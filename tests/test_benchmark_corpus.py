import contextlib
from copy import deepcopy
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, call, patch

from tests import benchmark as corpus
from tests import run as runner
from tests.benchmark import PROCESS_CHOICES, parse_args, solver_config
from tests.plot import cactus_coordinates


METHODS = ("base", "ges", "ges_always", "ges_lbd", "ges_random", "ges_par", "ges_vsids", "ges_utility")


class RecordingBar:
    def __init__(self, **options):
        self.options = options
        self.n = 0
        self.closed = False
        self.postfix = {}
        self.history = []

    def __enter__(self):
        return self

    def __exit__(self, *exception):
        self.closed = True

    def update(self, amount):
        self.n += amount
        assert self.n <= self.options["total"]

    def set_postfix(self, values=None, **values_by_name):
        self.postfix = dict(values if values is not None else values_by_name)
        self.history.append(deepcopy(self.postfix))


class WorkerProgressTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.output = self.root / "result.json"
        self.metadata = {"problem": "tests/benchmark/a/one.cnf", "family": "a", "expected": "unknown"}
        self.now = 100.0
        stack = contextlib.ExitStack()
        self.addCleanup(stack.close)
        self.clock = stack.enter_context(patch.object(runner.time, "perf_counter", side_effect=lambda: self.now))
        self.popen = stack.enter_context(patch.object(runner.subprocess, "Popen"))
        self.process = self.popen.return_value
        self.terminate = stack.enter_context(patch.object(runner, "terminate_process"))
        self.callback = Mock()

    def run_worker(self, deadline=102.5, **kwargs):
        return runner.run_problem_subprocess(
            self.root / "one.cnf", self.output, {}, self.metadata, deadline, **kwargs
        )

    def wait_until_deadline(self, timeout=None):
        if timeout is None:
            return None, " worker stderr "
        self.now += timeout
        raise runner.subprocess.TimeoutExpired("worker", timeout)

    def test_default_callback_preserves_single_full_budget_wait(self):
        self.process.communicate.side_effect = self.wait_until_deadline
        result = self.run_worker()
        self.assertEqual(self.process.communicate.call_args_list, [call(timeout=2.5), call()])
        self.terminate.assert_called_once_with(self.process)
        self.assertEqual(result["status"], "timeout")
        self.assertEqual(result["wall_seconds"], 2.5)
        self.assertEqual(self.clock.call_count, 3)

    def test_live_polls_use_fractional_final_wait_and_same_hard_deadline(self):
        self.process.communicate.side_effect = self.wait_until_deadline
        result = self.run_worker(progress_callback=self.callback)
        self.assertEqual(self.callback.call_args_list, [call(1.5), call(0.5)])
        self.assertEqual(self.process.communicate.call_args_list, [call(timeout=1), call(timeout=1), call(timeout=0.5), call()])
        self.terminate.assert_called_once_with(self.process)
        self.assertEqual(self.now, 102.5)
        self.assertEqual(result["status"], "timeout")
        self.assertEqual(result["timeout_seconds"], 2.5)
        self.assertEqual(result["stderr"], "worker stderr")
        self.assertIn("while waiting", result["reason"])
        self.assertEqual(self.clock.call_count, 8)

    def test_completion_after_poll_reads_result_without_termination(self):
        def communicate(timeout=None):
            if self.process.communicate.call_count == 1:
                return self.wait_until_deadline(timeout)
            self.now += 0.25
            self.output.write_text('{"status": "completed"}', encoding="utf-8")
            return None, ""

        self.process.communicate.side_effect = communicate
        self.assertEqual(self.run_worker(progress_callback=self.callback), {"status": "completed"})
        self.callback.assert_called_once_with(1.5)
        self.assertEqual(self.process.communicate.call_args_list, [call(timeout=1), call(timeout=1)])
        self.terminate.assert_not_called()

    def test_callback_time_is_subtracted_from_next_wait(self):
        def refresh(remaining):
            self.now += 0.75

        self.callback.side_effect = refresh
        self.process.communicate.side_effect = self.wait_until_deadline
        result = self.run_worker(progress_callback=self.callback)
        self.assertEqual(self.process.communicate.call_args_list, [call(timeout=1), call(timeout=0.75), call()])
        self.assertEqual(self.now, 102.5)
        self.assertEqual(result["status"], "timeout")
        self.terminate.assert_called_once_with(self.process)

    def test_deadline_exhausted_in_callback_does_not_start_another_wait(self):
        self.callback.side_effect = lambda remaining: setattr(self, "now", 102.5)
        self.process.communicate.side_effect = self.wait_until_deadline
        self.assertEqual(self.run_worker(progress_callback=self.callback)["status"], "timeout")
        self.assertEqual(self.process.communicate.call_args_list, [call(timeout=1), call()])
        self.terminate.assert_called_once_with(self.process)

    def test_callback_failure_terminates_and_reaps_worker(self):
        self.callback.side_effect = RuntimeError("refresh failed")
        self.process.communicate.side_effect = self.wait_until_deadline
        with self.assertRaisesRegex(RuntimeError, "refresh failed"):
            self.run_worker(progress_callback=self.callback)
        self.terminate.assert_called_once_with(self.process)
        self.assertEqual(self.process.communicate.call_args_list, [call(timeout=1), call()])

    def test_exhausted_budget_before_or_during_launch_never_polls(self):
        self.assertEqual(self.run_worker(deadline=100, progress_callback=self.callback)["status"], "timeout")
        self.popen.assert_not_called()
        self.popen.side_effect = lambda *args, **kwargs: (setattr(self, "now", 103) or self.process)
        self.process.communicate.return_value = (None, "")
        result = self.run_worker(progress_callback=self.callback)
        self.assertIn("during worker launch", result["reason"])
        self.process.communicate.assert_called_once_with()
        self.terminate.assert_called_once_with(self.process)
        self.callback.assert_not_called()


class BenchmarkExportTests(unittest.TestCase):
    def test_vsids_improvements_are_exported_and_aggregated(self):
        stats = Mock()
        for field in runner.COUNTER_FIELDS:
            setattr(stats, field, 0)
        stats.ges_vsids_improvements = 7
        for _, method in runner.RUNTIME_METHODS:
            getattr(stats, method).return_value = 0
        solver = Mock(model=[True], stats=stats)
        clsat = Mock()
        clsat.Sat.return_value = solver
        config = solver_config(parse_args(["--no-bva"]), "ges_vsids")
        metadata = {"problem": "family/one.cnf", "family": "family", "expected": "sat"}
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source, output = root / "one.cnf", root / "result.json"
            source.write_text("p cnf 1 1\n1 0\n", encoding="utf-8")
            with patch.dict("sys.modules", {"clsat": clsat}):
                self.assertEqual(runner.run_worker(source, output, config, metadata), 0)
            result = json.loads(output.read_text(encoding="utf-8"))
        self.assertEqual(result["counters"]["ges_vsids_improvements"], 7)
        self.assertEqual(solver.solve.call_args.kwargs["inprocessing"], ["ges_vsids"])
        summary = corpus.aggregate_results("family", [result])
        self.assertEqual(summary["average_counters"]["ges_vsids_improvements"], 7)

    def test_utility_improvements_are_exported_and_aggregated(self):
        stats = Mock()
        for field in runner.COUNTER_FIELDS:
            setattr(stats, field, 0)
        stats.ges_utility_improvements = 11
        for _, method in runner.RUNTIME_METHODS:
            getattr(stats, method).return_value = 0
        solver = Mock(model=[True], stats=stats)
        clsat = Mock()
        clsat.Sat.return_value = solver
        config = solver_config(parse_args(["--no-bva"]), "ges_utility")
        metadata = {"problem": "family/one.cnf", "family": "family", "expected": "sat"}
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source, output = root / "one.cnf", root / "result.json"
            source.write_text("p cnf 1 1\n1 0\n", encoding="utf-8")
            with patch.dict("sys.modules", {"clsat": clsat}):
                self.assertEqual(runner.run_worker(source, output, config, metadata), 0)
            result = json.loads(output.read_text(encoding="utf-8"))
        self.assertEqual(result["counters"]["ges_utility_improvements"], 11)
        self.assertEqual(solver.solve.call_args.kwargs["inprocessing"], ["ges_utility"])
        summary = corpus.aggregate_results("family", [result])
        self.assertEqual(summary["average_counters"]["ges_utility_improvements"], 11)


class BenchmarkParserTests(unittest.TestCase):
    def test_progress_dependency_is_lazy_and_missing_error_is_actionable(self):
        with patch.dict("sys.modules", {"tests.benchmark_progress": None}):
            self.assertEqual(parse_args([]).family_timeout, corpus.MAX_FAMILY_TIMEOUT_SECONDS)
            with self.assertRaisesRegex(SystemExit, r'pip install.*\[benchmark\]'):
                corpus.import_tqdm()

    def test_input_directory_is_preserved_by_parser(self):
        args = parse_args(["--input", "sat_2021", "--output", "benchmark_sat2021"])
        self.assertEqual(args.input, Path("sat_2021"))
        self.assertEqual(args.output, Path("benchmark_sat2021"))

    def test_worker_does_not_import_progress(self):
        with patch.object(corpus, "import_tqdm", side_effect=AssertionError("worker imported progress")), patch.object(corpus, "run_worker", return_value=0):
            self.assertEqual(corpus.main([
                "--worker", "--worker-input", "input.cnf", "--worker-output", "output.json",
                "--worker-config", "{}", "--worker-metadata", "{}",
            ]), 0)
    def test_process_choices_include_all_ges_variants(self):
        self.assertEqual(
            PROCESS_CHOICES,
            ("bva", "bve", "ges", "ges_always", "ges_lbd", "ges_par", "ges_random", "ges_vsids", "ges_utility", "ges_compress", "ges_trail", "preference", "subsumption"),
        )

    def test_ges_variants_are_preserved_by_parser(self):
        for phase in ("preprocess", "inprocessing"):
            for process in METHODS[1:]:
                with self.subTest(phase=phase, process=process):
                    args = parse_args(["--no-bva", "--" + phase, process])
                    self.assertEqual(getattr(args, phase), [process])
                    if phase == "preprocess":
                        self.assertEqual(solver_config(args)[phase], [process])

    def test_multiple_variants_preserve_order(self):
        args = parse_args([
            "--no-bva", "--preprocess", "ges_random", "ges_par", "ges_lbd",
            "--inprocessing", "ges_lbd", "ges", "ges_par", "ges_random",
        ])
        self.assertEqual(solver_config(args)["preprocess"], ["ges_random", "ges_par", "ges_lbd"])
        self.assertEqual(args.inprocessing, ["ges_lbd", "ges", "ges_par", "ges_random"])

    def test_help_describes_parallel_ges(self):
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout), self.assertRaises(SystemExit) as error:
            parse_args(["--help"])
        self.assertEqual(error.exception.code, 0)
        self.assertIn("ges_par runs parallel GES", " ".join(stdout.getvalue().split()))

    def test_unknown_process_error_lists_variants(self):
        for phase in ("preprocess", "inprocessing"):
            with self.subTest(phase=phase):
                stderr = io.StringIO()
                with contextlib.redirect_stderr(stderr), self.assertRaises(SystemExit) as error:
                    parse_args(["--" + phase, "unknown_process"])
                self.assertEqual(error.exception.code, 2)
                for process in METHODS[1:]:
                    self.assertIn(process, stderr.getvalue())

    def test_family_timeout_bounds(self):
        self.assertEqual(parse_args([]).family_timeout, 500)
        for value in ("0", "0.5", "500"):
            with self.subTest(value=value):
                self.assertEqual(parse_args(["--family-timeout", value]).family_timeout, float(value))
        for value in ("-1", "500.1", "nan", "inf", "-inf"):
            with self.subTest(value=value), contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as error:
                    parse_args(["--family-timeout=" + value])
                self.assertEqual(error.exception.code, 2)

    def test_eight_configs_differ_only_in_inprocessing(self):
        self.assertEqual(corpus.METHOD_ORDER, METHODS)
        for preprocess in ([], ["bve", "ges_par", "subsumption"]):
            args = parse_args([
                "--no-bva", "--algorithm", "dpll", "--implication-point", "uip",
                "--heuristics", "random", "--preprocess", *preprocess,
            ])
            for method in METHODS:
                with self.subTest(preprocess=preprocess, method=method):
                    config = solver_config(args, method)
                    self.assertEqual(config, {
                        "algorithm": "dpll", "implication_point": "uip",
                        "heuristics": "random", "preprocess": preprocess,
                        "inprocessing": [] if method == "base" else [method],
                    })
                    self.assertIsNot(config["preprocess"], args.preprocess)
            self.assertEqual(solver_config(args), solver_config(args, "base"))
        with self.assertRaisesRegex(ValueError, "unknown benchmark method"):
            solver_config(parse_args([]), "unknown")

    def test_managed_bva_and_ges_addons_are_composed_without_duplicate_rows(self):
        args = parse_args(["--ges-addons", "ges_trail", "ges_compress"])
        self.assertEqual(corpus.benchmark_methods(args), METHODS)
        self.assertEqual(solver_config(args, "base")["preprocess"], ["bva"])
        self.assertEqual(solver_config(args, "base")["inprocessing"], ["bva"])
        self.assertEqual(
            solver_config(args, "ges_vsids")["inprocessing"],
            ["ges_vsids", "ges_trail", "ges_compress", "bva"],
        )
        self.assertNotIn("ges_trail", corpus.METHOD_ORDER)
        self.assertNotIn("ges_compress", corpus.METHOD_ORDER)

    def test_parallel_profiles_build_the_four_requested_matrices(self):
        with tempfile.TemporaryDirectory() as temporary:
            args = parse_args([
                "--parallel", "--output", temporary, "--family-timeout", "12",
                "--ges-addons", "ges_trail",
            ])
            observed = {}
            for profile in corpus.PARALLEL_PROFILES:
                output = corpus.parallel_profile_output(args, profile)
                command = corpus.parallel_profile_command(args, profile, output)
                child = parse_args(command[3:])
                observed[profile.name] = {
                    "output": output.name,
                    "implication_point": child.implication_point,
                    "bva": child.use_bva,
                    "methods": corpus.benchmark_methods(child),
                    "addons": child.ges_addons,
                }

        self.assertEqual(
            observed,
            {
                "uip": {
                    "output": "benchmark_uip", "implication_point": "uip",
                    "bva": False, "methods": ("base",), "addons": ["ges_trail"],
                },
                "uip_bva": {
                    "output": "benchmark_uip_bva", "implication_point": "uip",
                    "bva": True, "methods": METHODS, "addons": ["ges_trail"],
                },
                "dip": {
                    "output": "benchmark_dip", "implication_point": "dip",
                    "bva": False, "methods": METHODS, "addons": ["ges_trail"],
                },
                "dip_bva": {
                    "output": "benchmark_dip_bva", "implication_point": "dip",
                    "bva": True, "methods": METHODS, "addons": ["ges_trail"],
                },
            },
        )

    def test_parallel_coordinator_spawns_every_profile(self):
        with tempfile.TemporaryDirectory() as temporary:
            args = parse_args(["--parallel", "--output", temporary, "--plot-only"])
            processes = []

            def spawn(*_args, **_kwargs):
                process = Mock()
                process.poll.return_value = 0
                processes.append(process)
                return process

            bars = []
            progress = Mock()
            progress.side_effect = lambda **options: (
                bars.append(RecordingBar(**options)) or bars[-1]
            )
            with patch.object(corpus.subprocess, "Popen", side_effect=spawn) as popen, patch.object(
                corpus, "import_tqdm", return_value=progress
            ):
                self.assertEqual(corpus.run_parallel_benchmarks(args), 0)

            self.assertEqual(popen.call_count, 4)
            self.assertEqual(len(processes), 4)
            self.assertEqual(bars[0].n, 4)
            self.assertTrue(bars[0].closed)
            for profile in corpus.PARALLEL_PROFILES:
                self.assertTrue(
                    (Path(temporary) / ("benchmark_" + profile.name) / "parallel.log").is_file()
                )

    def test_cactus_coordinates_put_solved_instances_before_wall_time(self):
        counts, times = cactus_coordinates([
            {"status": "completed", "wall_seconds": 3},
            {"status": "timeout", "wall_seconds": 10},
            {"status": "completed", "wall_seconds": 1},
            {"status": "completed", "wall_seconds": 2},
        ])
        self.assertEqual(counts, [0, 1, 2, 3])
        self.assertEqual(times, [0.0, 1.0, 2.0, 3.0])

    def test_matrix_rejects_legacy_inprocessing_override(self):
        with patch.object(corpus, "run_problem_subprocess") as worker:
            with self.assertRaisesRegex(SystemExit, "cannot override the fixed benchmark matrix"):
                corpus.benchmark(parse_args(["--inprocessing", "ges"]))
            worker.assert_not_called()


class BenchmarkCorpusTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.tests_root = self.root / "tests"
        self.benchmark_root = self.tests_root / "benchmark"
        self.benchmark_root.mkdir(parents=True)
        self.output = self.root / "results"
        stack = contextlib.ExitStack()
        self.addCleanup(stack.close)
        stack.enter_context(patch.multiple(
            corpus, PROJECT_ROOT=self.root, TESTS_ROOT=self.tests_root,
            BENCHMARK_ROOT=self.benchmark_root,
        ))
        stack.enter_context(patch.object(corpus, "reference_statuses", return_value={}))
        self.pyplot = stack.enter_context(patch.object(corpus.plot, "import_pyplot"))
        self.problem_plot = stack.enter_context(patch.object(corpus.plot, "plot_problem"))
        self.aggregate_plot = stack.enter_context(patch.object(corpus.plot, "plot_aggregate"))
        self.comparison_plot = stack.enter_context(patch.object(corpus.plot, "plot_comparison_cactus"))
        self.overlays = []
        self.comparison_plot.side_effect = lambda pyplot, *args: self.overlays.append((pyplot, *deepcopy(args)))
        self.bars = []
        self.progress = stack.enter_context(patch.object(corpus, "import_tqdm")).return_value

        def make_bar(**options):
            bar = RecordingBar(**options)
            self.bars.append(bar)
            return bar

        self.progress.side_effect = make_bar
        self.now = 100.0
        self.clock = stack.enter_context(patch.object(corpus.time, "perf_counter", side_effect=lambda: self.now))
        self.worker = stack.enter_context(patch.object(corpus, "run_problem_subprocess", side_effect=self.complete))
        stack.enter_context(contextlib.redirect_stdout(io.StringIO()))

    def add_problem(self, relative):
        path = self.tests_root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("p cnf 1 1\n1 0\n", encoding="utf-8")
        return path

    def complete(self, path, worker_output, config, metadata, deadline, progress_callback=None):
        return {
            **corpus.result_base(metadata, config),
            "status": "completed", "wall_seconds": 1.0,
        }

    def run_matrix(self, timeout=10):
        return corpus.main([
            "--no-bva", "--output", str(self.output),
            "--family-timeout", str(timeout),
            "--preprocess", "bve", "subsumption",
        ])

    def read_json(self, path):
        return json.loads(path.read_text(encoding="utf-8"))

    def test_nested_progress_totals_counts_budgets_and_rendering(self):
        for family in ("a", "b"):
            for number in range(3):
                self.add_problem("benchmark/{}/{}.cnf".format(family, number))

        def run(path, worker_output, config, metadata, deadline, progress_callback=None):
            result = self.complete(path, worker_output, config, metadata, deadline)
            self.now += 4 if path.stem == "0" else 6
            result["status"] = "completed" if path.stem == "0" else "timeout"
            return result

        def render(*args):
            self.assertFalse(self.bars[0].closed)
            self.assertNotEqual(self.bars[0].postfix["stage"], "done")
            self.assertIn("rendering", self.bars[0].postfix["stage"])
            self.assertEqual(self.bars[-1].options["position"], 2)
            self.assertFalse(self.bars[-1].closed)
            self.now += 100

        self.worker.side_effect = run
        self.problem_plot.side_effect = render
        self.aggregate_plot.side_effect = render
        self.comparison_plot.side_effect = render
        self.assertEqual(self.run_matrix(), 0)
        global_bar = self.bars[0]
        self.assertEqual(global_bar.n, 6 * len(METHODS))
        self.assertEqual(global_bar.options["total"], 6 * len(METHODS))
        self.assertEqual(global_bar.postfix["stage"], "done")
        for status in ("solved", "timeout", "skipped"):
            self.assertEqual(global_bar.postfix[status], 2 * len(METHODS))
        family_bars = [bar for bar in self.bars if bar.options["position"] == 1]
        self.assertEqual([bar.n for bar in family_bars], [3 * len(METHODS)] * 2)
        self.assertEqual([bar.postfix["skipped"] for bar in family_bars], [len(METHODS)] * 2)
        render_bars = [bar for bar in self.bars if bar.options["position"] == 2]
        self.assertEqual([bar.options["total"] for bar in render_bars], ([5] * len(METHODS) + [2]) * 2)
        for bar in self.bars:
            self.assertTrue(bar.closed)
            self.assertEqual(bar.n, bar.options["total"])
            self.assertIsNone(bar.options["disable"])

        budget_key = "solver budget upper bound (not ETA; excludes plots/overhead)"
        self.assertEqual(global_bar.history[0][budget_key], "{:.1f}s".format(20 * len(METHODS)))
        self.assertEqual(global_bar.history[2][budget_key], "{:.1f}s".format(20 * len(METHODS) - 4))
        self.assertEqual(global_bar.history[0]["method-family budget remaining (last sample)"], "10.0s")
        self.assertEqual(global_bar.history[0]["method"], "base")
        self.assertTrue(global_bar.history[0]["problem"].endswith("a/0.cnf"))
        bounds = [float(state[budget_key][:-1]) for state in global_bar.history]
        self.assertEqual(bounds, sorted(bounds, reverse=True))
        self.assertEqual(bounds[-1], 0)
        # One deadline creation plus pre/post-result samples per path. The clock
        # advances with simulated work, not with UI reads.
        self.assertEqual(self.clock.call_count, 2 * len(METHODS) * 7)
        self.assertEqual(self.progress.write.call_count, 2 * len(METHODS) + 2)

    def test_live_progress_refreshes_both_bars_without_advancing_results(self):
        self.add_problem("benchmark/a/one.cnf")
        budget_key = "method-family budget remaining (last sample)"
        upper_bound_key = "solver budget upper bound (not ETA; excludes plots/overhead)"

        def run(path, worker_output, config, metadata, deadline, progress_callback=None):
            if progress_callback is None:
                self.fail("benchmark did not provide a progress callback")
            global_bar, family_bar = self.bars[0], self.bars[1]
            counts = (global_bar.n, family_bar.n)
            for elapsed in (1, 2):
                self.now += elapsed
                progress_callback(deadline - self.now)
                for bar in (global_bar, family_bar):
                    self.assertEqual(bar.postfix["stage"], "solving")
                    self.assertEqual(bar.postfix["method"], worker_output.parent.name)
                    self.assertEqual(bar.postfix["problem"], metadata["problem"])
                    self.assertEqual(bar.postfix[budget_key], "{:.1f}s".format(deadline - self.now))
                pending = (len(METHODS) - 1 - METHODS.index(worker_output.parent.name)) * 10
                self.assertEqual(global_bar.postfix[upper_bound_key], "{:.1f}s".format(pending + deadline - self.now))
                self.assertEqual((global_bar.n, family_bar.n), counts)
            self.now += 2
            return self.complete(path, worker_output, config, metadata, deadline)

        self.worker.side_effect = run
        self.assertEqual(self.run_matrix(), 0)
        saved = [state for state in self.bars[0].history if state["stage"] == "result saved"]
        self.assertEqual([state[budget_key] for state in saved], ["5.0s"] * len(METHODS))
        self.assertEqual(self.bars[0].n, len(METHODS))

    def test_progress_closes_on_solver_or_render_failure(self):
        self.add_problem("benchmark/a/one.cnf")
        for failing_mock in (self.worker, self.problem_plot, self.aggregate_plot, self.comparison_plot):
            with self.subTest(failure=failing_mock):
                self.bars.clear()
                original = failing_mock.side_effect
                def fail(*args, **kwargs):
                    if failing_mock is self.worker:
                        args[1].write_text("partial worker output", encoding="utf-8")
                    raise RuntimeError("injected failure")

                failing_mock.side_effect = fail
                try:
                    with self.assertRaisesRegex(RuntimeError, "injected failure"):
                        self.run_matrix()
                finally:
                    failing_mock.side_effect = original
                self.assertTrue(self.bars)
                self.assertTrue(all(bar.closed for bar in self.bars))
                self.assertNotEqual(self.bars[0].postfix["stage"], "done")
                self.assertFalse(list(self.output.glob("*/.worker-result.json")))

    def test_discovery_is_recursive_sorted_and_excludes_legacy_and_root_files(self):
        z = self.add_problem("benchmark/z-family/z.cnf")
        nested = self.add_problem("benchmark/a-family/nested/b.cnf")
        a = self.add_problem("benchmark/a-family/a.cnf")
        for relative in ("sat/legacy.cnf", "unsat/legacy.cnf", "benchmark/root.cnf", "benchmark/a-family/notes.txt"):
            self.add_problem(relative)
        (self.benchmark_root / "empty").mkdir()
        (self.benchmark_root / "a-family" / "directory.cnf").mkdir()
        self.assertEqual(corpus.discover_problems(), [a, nested, z])
        grouped = corpus.group_problems_by_family([z, nested, a])
        self.assertEqual(list(grouped), ["a-family", "z-family"])
        self.assertEqual(grouped, {"a-family": [a, nested], "z-family": [z]})
        self.assertEqual(corpus.problem_metadata(nested), {
            "problem": "tests/benchmark/a-family/nested/b.cnf",
            "family": "a-family", "expected": "unknown",
        })
        with self.assertRaisesRegex(ValueError, "family directory"):
            corpus.problem_family(self.benchmark_root / "root.cnf")

    def test_explicit_input_is_one_recursive_corpus_with_safe_output_paths(self):
        input_root = self.root / "sat_2021"
        root_problem = input_root / "root.cnf"
        nested_problem = input_root / "nested" / "hard.cnf"
        nested_problem.parent.mkdir(parents=True)
        for path in (root_problem, nested_problem):
            path.write_text("p cnf 1 1\n1 0\n", encoding="utf-8")
        (input_root / "ignored.cnf.xz").write_text("compressed", encoding="utf-8")
        (input_root / "directory.cnf").mkdir()

        problems = corpus.discover_problems(input_root)
        self.assertEqual(problems, [nested_problem, root_problem])
        self.assertEqual(
            corpus.group_problems_by_family(reversed(problems), input_root),
            {"sat_2021": [nested_problem, root_problem]},
        )
        self.assertEqual(
            corpus.problem_metadata(nested_problem, input_root),
            {
                "problem": "sat_2021/nested/hard.cnf",
                "family": "sat_2021",
                "expected": "unknown",
            },
        )
        self.assertEqual(
            corpus.result_json_path(self.output, "sat_2021/nested/hard.cnf"),
            self.output / "problems/sat_2021/nested/hard.json",
        )

        self.assertEqual(
            corpus.main([
                "--input", str(input_root), "--output", str(self.output),
                "--family-timeout", "0",
            ]),
            0,
        )
        index = self.read_json(self.output / "index.json")
        self.assertEqual(index["completed_families"], ["sat_2021"])
        for method in METHODS:
            _, results = corpus.load_saved_results(self.output / method)
            self.assertEqual(len(results), 2)
            self.assertTrue(all(result["family"] == "sat_2021" for result in results))
            self.assertTrue(all(result["status"] == "skipped" for result in results))

    def test_missing_or_empty_explicit_input_is_reported(self):
        empty = self.root / "empty_sat_2021"
        empty.mkdir()
        for input_root, message in (
            (self.root / "missing_sat_2021", "input directory not found"),
            (empty, "no .cnf problems found"),
        ):
            with self.subTest(input_root=input_root), self.assertRaisesRegex(SystemExit, message):
                corpus.main([
                    "--input", str(input_root), "--output", str(self.output),
                    "--family-timeout", "0",
                ])
        self.worker.assert_not_called()

    def test_missing_or_empty_corpus_does_not_fall_back_to_legacy(self):
        self.add_problem("sat/legacy.cnf")
        self.add_problem("unsat/legacy.cnf")
        for root in (self.benchmark_root, self.root / "missing"):
            with self.subTest(root=root), patch.object(corpus, "BENCHMARK_ROOT", root):
                self.assertEqual(corpus.discover_problems(), [])
                with self.assertRaisesRegex(SystemExit, "no .cnf problems"):
                    self.run_matrix()
        self.worker.assert_not_called()

    def test_deadlines_are_independent_and_exhaustion_skips_only_rest_of_pair(self):
        for family in ("a", "b"):
            for number in range(4):
                self.add_problem("benchmark/{}/{}.cnf".format(family, number))
        calls = []

        def run(path, worker_output, config, metadata, deadline, progress_callback=None):
            calls.append((metadata["family"], worker_output.parent.name, path.name, self.now, deadline))
            result = self.complete(path, worker_output, config, metadata, deadline)
            duration = 6 if path.stem == "0" else 4
            self.now += duration
            result.update(status="completed" if path.stem == "0" else "timeout", wall_seconds=duration)
            return result

        def render(*args):
            # Rendering time must not eat into the next method/family budget.
            self.now += 100

        self.worker.side_effect = run
        self.problem_plot.side_effect = render
        self.assertEqual(self.run_matrix(), 0)
        self.assertEqual(len(calls), 4 * len(METHODS))
        for index, (family, method) in enumerate((f, m) for f in ("a", "b") for m in METHODS):
            first, second = calls[2 * index:2 * index + 2]
            with self.subTest(family=family, method=method):
                self.assertEqual(first[:3], (family, method, "0.cnf"))
                self.assertEqual(second[:3], (family, method, "1.cnf"))
                self.assertEqual(first[4], first[3] + 10)
                self.assertEqual(second[4], first[4])
                self.assertEqual(second[4] - second[3], 4)
                _, results = corpus.load_saved_results(self.output / method)
                relevant = [result for result in results if result["family"] == family]
                self.assertEqual([result["status"] for result in relevant], ["completed", "timeout", "skipped", "skipped"])
                for result in relevant[2:]:
                    self.assertEqual(result["wall_seconds"], 0)
                    self.assertIn("deadline exhausted", result["error"])

    def test_no_instance_time_or_count_cap_within_family_budget(self):
        for number in range(12):
            self.add_problem("benchmark/a/{:02d}.cnf".format(number))
        observed = []

        def run(path, worker_output, config, metadata, deadline, progress_callback=None):
            observed.append((worker_output.parent.name, self.now, deadline))
            self.now += 40
            result = self.complete(path, worker_output, config, metadata, deadline)
            result["wall_seconds"] = 40
            return result

        self.worker.side_effect = run
        self.assertEqual(self.run_matrix(timeout=corpus.MAX_FAMILY_TIMEOUT_SECONDS), 0)
        self.assertEqual(self.worker.call_count, 12 * len(METHODS))
        for index, method in enumerate(METHODS):
            batch = observed[index * 12:(index + 1) * 12]
            deadline = batch[0][1] + corpus.MAX_FAMILY_TIMEOUT_SECONDS
            self.assertEqual([entry[0] for entry in batch], [method] * 12)
            self.assertEqual([entry[2] for entry in batch], [deadline] * 12)
            _, results = corpus.load_saved_results(self.output / method)
            self.assertTrue(all(result["status"] == "completed" for result in results))

    def test_zero_budget_persists_skips_for_all_methods_and_families(self):
        for family in ("a", "b"):
            self.add_problem("benchmark/{}/one.cnf".format(family))
        self.assertEqual(self.run_matrix(timeout=0), 0)
        self.worker.assert_not_called()
        self.assertEqual(self.bars[0].n, 2 * len(METHODS))
        self.assertEqual(self.bars[0].postfix["skipped"], 2 * len(METHODS))
        self.assertEqual(self.bars[0].postfix["solved"], 0)
        self.assertTrue(all(bar.closed for bar in self.bars))
        for method in METHODS:
            _, results = corpus.load_saved_results(self.output / method)
            self.assertEqual([r["status"] for r in results], ["skipped", "skipped"])
            self.assertEqual([r["family"] for r in results], ["a", "b"])

    def test_persistence_and_overlays_include_all_eight_configurations(self):
        paths = [self.add_problem("benchmark/{}/nested/one.cnf".format(family)) for family in ("a", "b")]
        self.assertEqual(self.run_matrix(), 0)
        index = self.read_json(self.output / "index.json")
        self.assertEqual(index, self.read_json(self.output / "summary.json"))
        self.assertEqual(index["method_order"], list(METHODS))
        self.assertEqual(set(index["methods"]), set(METHODS))
        self.assertEqual(index["completed_families"], ["a", "b"])
        self.assertEqual(index["limits"], {"family_timeout_seconds": 10})
        self.assertEqual(index["cactus_plots"], {name: "plots/cactus/{}.png".format(name) for name in ("a", "b", "overall")})
        keys = [corpus.problem_key(path) for path in paths]
        for method in METHODS:
            with self.subTest(method=method):
                entry = index["methods"][method]
                self.assertEqual(
                    entry["label"],
                    "DIP" if method == "base" else "DIP + " + corpus.METHOD_LABELS[method],
                )
                self.assertEqual(entry["path"], method)
                self.assertEqual(entry["index"], method + "/index.json")
                method_output = self.output / method
                method_index, results = corpus.load_saved_results(method_output)
                config = entry["solver_configuration"]
                self.assertEqual(config["preprocess"], ["bve", "subsumption"])
                self.assertEqual(config["inprocessing"], [] if method == "base" else [method])
                self.assertEqual(method_index["solver_configuration"], config)
                self.assertEqual(method_index["limits"], index["limits"])
                self.assertEqual(sorted(method_index["problems"]), keys)
                self.assertEqual([result["problem"] for result in results], keys)
                self.assertTrue(all(result["configuration"] == config for result in results))
                for key, saved in method_index["problems"].items():
                    self.assertEqual(saved["result"], "problems/" + str(Path(key).relative_to("tests").with_suffix(".json")))
                    self.assertEqual(saved["plot"], "plots/problems/" + str(Path(key).relative_to("tests").with_suffix(".png")))
                    self.assertEqual(saved["status"], "completed")
                self.assertEqual(set(method_index["aggregates"]), {"a", "b", "overall"})
                for name, saved in method_index["aggregates"].items():
                    summary = self.read_json(method_output / saved["summary"])
                    self.assertEqual(summary["problems"], 2 if name == "overall" else 1)
                    self.assertEqual(summary["statuses"]["completed"], summary["problems"])
                self.assertEqual(entry["summary"], self.read_json(method_output / "aggregates/overall.json"))
        self.assertEqual(self.problem_plot.call_count, 2 * len(METHODS))
        self.assertEqual(self.aggregate_plot.call_count, 4 * len(METHODS))
        self.assert_overlays(["a", "overall", "b", "overall"], [1, 1, 1, 2], 10)

    def assert_overlays(self, names, counts, timeout):
        self.assertEqual(self.comparison_plot.call_count, len(names))
        for call, name, count in zip(self.overlays, names, counts):
            pyplot, actual_name, methods, destination, actual_timeout = call
            self.assertIs(pyplot, self.pyplot.return_value)
            self.assertEqual(actual_name, name)
            self.assertEqual(
                list(methods),
                [
                    "DIP" if method == "base" else "DIP + " + corpus.METHOD_LABELS[method]
                    for method in METHODS
                ],
            )
            self.assertEqual(destination, self.output / "plots/cactus" / (name + ".png"))
            self.assertEqual(actual_timeout, timeout)
            for method, results in zip(METHODS, methods.values()):
                self.assertEqual(len(results), count)
                self.assertTrue(all(r["configuration"]["inprocessing"] == ([] if method == "base" else [method]) for r in results))
                if name != "overall":
                    self.assertTrue(all(r["family"] == name for r in results))

    def test_cactus_plot_uses_only_the_available_methods_in_their_saved_order(self):
        methods = {"base": [], "ges": []}

        labels = {method: corpus.METHOD_LABELS[method] for method in methods}
        path = corpus.plot_matrix_cactus(
            self.pyplot.return_value, self.output, "legacy", methods, labels, 17
        )

        self.assertEqual(path, "plots/cactus/legacy.png")
        _, name, plotted_methods, destination, timeout = self.overlays[-1]
        self.assertEqual(name, "legacy")
        self.assertEqual(list(plotted_methods), [
            corpus.METHOD_LABELS["base"], corpus.METHOD_LABELS["ges"],
        ])
        self.assertEqual(destination, self.output / "plots/cactus/legacy.png")
        self.assertEqual(timeout, 17)

    def test_plot_only_uses_saved_indexes_never_solver_or_corpus(self):
        for family in ("a", "b"):
            self.add_problem("benchmark/{}/one.cnf".format(family))
        self.assertEqual(self.run_matrix(timeout=17), 0)
        # A stale, unindexed file must not leak into regenerated overlays.
        for method in METHODS:
            (self.output / method / "problems/stale.json").write_text("not JSON", encoding="utf-8")
        for mock in (self.worker, self.clock, self.problem_plot, self.aggregate_plot, self.comparison_plot):
            mock.reset_mock()
        self.overlays.clear()
        self.worker.side_effect = AssertionError("plot-only launched a solver")
        with patch.object(corpus, "discover_problems", side_effect=AssertionError("plot-only discovered corpus")), patch.object(corpus, "run_worker") as worker:
            self.assertEqual(corpus.main(["--plot-only", "--output", str(self.output), "--family-timeout", "1"]), 0)
            worker.assert_not_called()
        self.worker.assert_not_called()
        self.clock.assert_not_called()
        self.problem_plot.assert_not_called()
        self.aggregate_plot.assert_not_called()
        self.assert_overlays(["a", "b", "overall"], [1, 1, 2], 17)
        self.assertEqual(self.bars[-1].options["total"], 3)
        self.assertEqual(self.bars[-1].n, 3)
        self.assertTrue(self.bars[-1].closed)
        self.assertEqual(self.bars[-1].postfix["stage"], "done")
        self.assertEqual(self.read_json(self.output / "index.json"), self.read_json(self.output / "summary.json"))


class BenchmarkEntrypointTests(unittest.TestCase):
    def test_repository_benchmark_subcommand_forwards_arguments_and_exit_code(self):
        import main as entrypoint

        arguments = ["benchmark", "--plot-only", "--output", "saved-matrix"]
        with patch.object(entrypoint, "benchmark_main", return_value=7) as benchmark_main, patch.object(entrypoint, "solve_example") as example:
            self.assertEqual(entrypoint.main(arguments), 7)
            benchmark_main.assert_called_once_with(arguments[1:])
            example.assert_not_called()
        with patch.object(entrypoint.sys, "argv", ["main.py", *arguments]), patch.object(entrypoint, "benchmark_main", return_value=3) as benchmark_main:
            self.assertEqual(entrypoint.main(), 3)
            benchmark_main.assert_called_once_with(arguments[1:])
