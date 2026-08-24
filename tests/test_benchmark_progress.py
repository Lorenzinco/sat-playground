import io
import unittest
from unittest.mock import patch

from rich.console import Console
from rich.text import Text

from tests.benchmark import progress_bar, progress_status
from tests.benchmark_progress import BenchmarkProgress


class BenchmarkProgressTests(unittest.TestCase):
    def dashboard(self, terminal=True, width=80):
        stream = io.StringIO()
        console = Console(file=stream, force_terminal=terminal, width=width,
                          color_system="auto", _environ={})
        return BenchmarkProgress(console), stream

    def status(self):
        return progress_status(dict(completed=2, timeout=1, skipped=3, incorrect=1, error=1),
                               "solving", "ges_par", "very-long-family/" + "x" * 200 + ".cnf", 12, 30)

    def test_nested_dashboard_shares_live_and_removes_tasks(self):
        dashboard, stream = self.dashboard()
        progress = dashboard.progress
        with patch.object(progress, "start", wraps=progress.start) as start, patch.object(progress, "stop", wraps=progress.stop) as stop:
            with progress_bar(dashboard, 8, "All results", 0) as outer:
                outer.set_postfix(self.status())
                with progress_bar(dashboard, 8, "Family", 1) as family:
                    family.set_postfix(self.status())
                    with progress_bar(dashboard, 2, "Render", 2) as render:
                        render.update(1)
                        self.assertEqual(len(progress.tasks), 3)
                        self.assertTrue(progress.live.is_started)
                        dashboard.write("literal [red] message")
                    self.assertEqual(len(progress.tasks), 2)
                self.assertEqual(len(progress.tasks), 1)
                outer.update(8)
            self.assertEqual(start.call_count, 1)
            self.assertEqual(stop.call_count, 1)
        self.assertFalse(progress.live.is_started)
        self.assertEqual(progress.tasks, [])
        self.assertEqual(dashboard.handles, [])
        self.assertIn("literal [red] message", stream.getvalue())
        self.assertIn("\x1b[", stream.getvalue())

    def test_narrow_terminal_has_cropped_activity_and_compact_status(self):
        for width in (40, 60, 80):
            with self.subTest(width=width):
                dashboard, stream = self.dashboard(width=width)
                with progress_bar(dashboard, 8, "All results", 0) as outer:
                    outer.set_postfix(self.status())
                    with progress_bar(dashboard, 8, "a" * 100, 1):
                        with progress_bar(dashboard, 3, "Render " + "b" * 100, 2):
                            snapshot = io.StringIO()
                            Console(file=snapshot, width=width, color_system=None).print(dashboard.progress)
                            plain = snapshot.getvalue()
                            self.assertTrue(all(len(line) <= width for line in plain.splitlines()))
                            activity = next(line for line in plain.splitlines() if "solving" in line)
                            self.assertIn("ges_par", activity)
                            self.assertIn("…", activity)
                            self.assertNotIn("x" * 100, plain)
                            for label in ("solved 2", "timeout 1", "skipped 3", "incorrect 1", "error 1", "Pair budget:", "Solver budget", "ETA~"):
                                self.assertIn(label, plain)

    def test_non_terminal_emits_only_final_snapshot_without_control_codes(self):
        dashboard, stream = self.dashboard(terminal=False)
        self.assertFalse(dashboard.progress.live.auto_refresh)
        with progress_bar(dashboard, 8, "All results", 0) as outer:
            for _ in range(8):
                outer.set_postfix(self.status())
                outer.update()
            self.assertEqual(stream.getvalue(), "")
        output = stream.getvalue()
        self.assertNotIn("\x1b", output)
        self.assertEqual(output.count("All results"), 1)
        self.assertIn("8/8", output.replace(" ", ""))
        self.assertIn("solved 2", output)

    def test_no_color_removes_color_styles(self):
        stream = io.StringIO()
        console = Console(file=stream, force_terminal=True, width=80,
                          _environ={"NO_COLOR": "1"})
        dashboard = BenchmarkProgress(console)
        self.assertTrue(console.no_color)
        with progress_bar(dashboard, 1, "Render", 0) as bar:
            bar.update()
        self.assertNotRegex(stream.getvalue(), r"\x1b\[(?:3[0-7]|9[0-7])m")

    def test_exceptions_close_live_and_allow_reuse(self):
        for depth in (1, 2, 3):
            dashboard, stream = self.dashboard()
            from contextlib import ExitStack
            with self.assertRaisesRegex(RuntimeError, "injected"):
                with ExitStack() as stack:
                    handles = [stack.enter_context(progress_bar(dashboard, 1, "task", pos)) for pos in range(depth)]
                    raise RuntimeError("injected")
            self.assertTrue(all(handle.closed for handle in handles))
            self.assertFalse(dashboard.progress.live.is_started)
            self.assertEqual(dashboard.progress.tasks, [])
            self.assertEqual(dashboard.handles, [])
            self.assertIn("interrupted", Text.from_ansi(stream.getvalue()).plain)
            with progress_bar(dashboard, 1, "Regenerate cactus plots", 0) as bar:
                bar.set_postfix(stage="rendering", family="overall")
                bar.update()
            self.assertFalse(dashboard.progress.live.is_started)

    def test_default_console_uses_stderr(self):
        with patch("sys.stderr", new_callable=io.StringIO) as stderr:
            dashboard = BenchmarkProgress()
            dashboard.write("hello")
            self.assertEqual(stderr.getvalue(), "hello\n")


if __name__ == "__main__":
    unittest.main()
