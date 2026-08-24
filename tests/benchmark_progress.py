"""A single Rich live display behind the benchmark's small tqdm-style API."""

from rich.console import Console
from rich.progress import (
    BarColumn, MofNCompleteColumn, Progress, SpinnerColumn, TextColumn,
    TimeElapsedColumn, TimeRemainingColumn,
)
from rich.table import Column
from rich.text import Text


FAMILY_BUDGET = "method-family budget remaining (last sample)"
TOTAL_BUDGET = "solver budget upper bound (not ETA; excludes plots/overhead)"
STATUS_STYLES = (
    ("solved", "green"), ("timeout", "yellow"), ("skipped", "dim"),
    ("incorrect", "bold red"), ("error", "red"),
)


class EstimatedRemainingColumn(TimeRemainingColumn):
    def render(self, task):
        value = super().render(task)
        value.plain = "ETA~ " + value.plain
        return value


class DashboardProgress(Progress):
    def get_renderables(self):
        tasks = self.tasks
        yield self.make_tasks_table(tasks)
        if not tasks:
            return
        # The outer task carries the authoritative activity and budget sample.
        status = tasks[0].fields.get("status", {})
        if status:
            activity = " · ".join(str(status[key]) for key in
                                  ("stage", "method", "problem", "family", "aggregate")
                                  if status.get(key))
            yield Text(activity, style="cyan", no_wrap=True, overflow="ellipsis")
        for task in tasks:
            counts = task.fields.get("status", {})
            if "solved" not in counts:
                continue
            summary = Text("All: " if task.fields["position"] == 0 else "Family: ", style="bold")
            for key, style in STATUS_STYLES:
                summary.append("{} {}  ".format(key, counts.get(key, 0)), style=style)
            yield summary
        if FAMILY_BUDGET in status:
            yield Text("Pair budget: {} (last sample)".format(status[FAMILY_BUDGET]), style="magenta")
            yield Text("Solver budget ≤ {} (not ETA; no plots/overhead)".format(status[TOTAL_BUDGET]), style="dim magenta")
        yield Text("ETA~ estimated; unreliable for SAT", style="dim")


class BenchmarkProgress:
    """Callable bar factory; the outermost handle owns the live lifetime.

    Non-terminal streams get only the final dashboard and explicit writes, not
    repeated snapshots. Rich handles terminal detection and NO_COLOR itself.
    """

    def __init__(self, console=None):
        self.console = console if console is not None else Console(stderr=True)
        self.progress = DashboardProgress(
            SpinnerColumn(style="cyan"),
            TextColumn("{task.description}", markup=False,
                       table_column=Column(width=min(24, max(6, self.console.width // 4)),
                                                                  no_wrap=True, overflow="ellipsis")),
            BarColumn(bar_width=None, style="bright_black", complete_style="cyan", finished_style="green"),
            MofNCompleteColumn(),
            TimeElapsedColumn(),
            EstimatedRemainingColumn(),
            console=self.console, expand=True, refresh_per_second=8,
            auto_refresh=self.console.is_terminal, redirect_stdout=False, redirect_stderr=False,
        )
        self.handles = []

    def __call__(self, total, desc, position=0, leave=True, **options):
        return ProgressHandle(self, total, desc, position, leave)

    def write(self, message):
        self.console.print(Text(str(message)))


class ProgressHandle:
    def __init__(self, dashboard, total, description, position, leave):
        self.dashboard = dashboard
        self.total = total
        self.description = description
        self.position = position
        self.leave = leave
        self.task_id = None
        self.closed = False
        self.n = 0
        self.postfix = {}

    def __enter__(self):
        progress = self.dashboard.progress
        self.task_id = progress.add_task(self.description, total=self.total,
                                         position=self.position, status={})
        self.dashboard.handles.append(self)
        if len(self.dashboard.handles) == 1:
            try:
                progress.start()
            except BaseException:
                try:
                    progress.stop()
                finally:
                    progress.remove_task(self.task_id)
                    self.dashboard.handles.remove(self)
                    self.closed = True
                raise
        return self

    def update(self, amount=1):
        self.n += amount
        self.dashboard.progress.update(self.task_id, advance=amount)

    def set_postfix(self, values=None, **values_by_name):
        self.postfix = dict(values if values is not None else values_by_name)
        self.dashboard.progress.update(self.task_id, status=self.postfix)

    def __exit__(self, exc_type, exc_value, traceback):
        progress = self.dashboard.progress
        try:
            if exc_type is not None:
                self.set_postfix(dict(self.postfix, stage="interrupted"))
            progress.stop_task(self.task_id)
            if len(self.dashboard.handles) == 1:
                progress.stop()
        finally:
            progress.remove_task(self.task_id)
            self.dashboard.handles.remove(self)
            self.closed = True
        return False
