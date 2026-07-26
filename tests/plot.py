"""Matplotlib rendering for SAT benchmark results.

This module intentionally contains no corpus discovery, solver execution,
subprocess management, aggregation, or result persistence.
"""

from pathlib import Path
from typing import Any, Mapping, Sequence, Tuple

from .run import COUNTER_FIELDS, RUNTIME_METHODS


STATUS_COLORS = {
    "completed": "#2ca02c",
    "incorrect": "#e377c2",
    "timeout": "#d62728",
    "error": "#ff7f0e",
    "skipped": "#7f7f7f",
}


def import_pyplot():
    try:
        import matplotlib

        matplotlib.use("Agg")
        import matplotlib.pyplot as plt

        return plt
    except ImportError as error:
        raise SystemExit(
            "matplotlib is required for benchmark plots. Install it with:\n"
            "  .venv/bin/python -m pip install matplotlib\n"
            "or install the project's benchmark extra."
        ) from error


def nonzero_limits(values: Sequence[float]) -> Tuple[float, float]:
    maximum = max(values, default=0.0)
    return 0.0, maximum * 1.12 if maximum > 0 else 1.0


def annotate_horizontal_bars(axis, bars, values: Sequence[float], digits: int = 3) -> None:
    maximum = max(values, default=0.0)
    offset = maximum * 0.01 if maximum > 0 else 0.01
    for bar, value in zip(bars, values):
        axis.text(
            value + offset,
            bar.get_y() + bar.get_height() / 2,
            ("{:.%df}" % digits).format(value),
            va="center",
            fontsize=8,
        )


def plot_problem(plt, result: Mapping[str, Any], destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    figure, axes = plt.subplots(1, 2, figsize=(15, 7))
    status = str(result["status"])
    title = "{} — {}".format(result["problem"], status)
    if status in ("completed", "incorrect"):
        title += " ({})".format(result.get("actual", "unknown"))
    figure.suptitle(title, fontsize=13)

    runtime = dict(result.get("runtime_seconds", {}))
    runtime_labels = ["wall"] + [label for label, _ in RUNTIME_METHODS]
    runtime_values = [float(result.get("wall_seconds", 0.0))] + [
        float(runtime.get(label, 0.0)) for label, _ in RUNTIME_METHODS
    ]
    colors = [STATUS_COLORS.get(status, "#1f77b4")] + ["#1f77b4"] * len(
        RUNTIME_METHODS
    )
    bars = axes[0].barh(runtime_labels, runtime_values, color=colors)
    axes[0].invert_yaxis()
    axes[0].set_xlabel("seconds")
    axes[0].set_title("Runtime profile (raw timers; some are nested)")
    axes[0].set_xlim(*nonzero_limits(runtime_values))
    annotate_horizontal_bars(axes[0], bars, runtime_values)
    axes[0].grid(axis="x", alpha=0.25)

    counters = dict(result.get("counters", {}))
    counter_labels = list(COUNTER_FIELDS)
    counter_values = [float(counters.get(label, 0.0)) for label in counter_labels]
    bars = axes[1].barh(counter_labels, counter_values, color="#9467bd")
    axes[1].invert_yaxis()
    axes[1].set_xlabel("count / value")
    axes[1].set_title("Solver statistics")
    axes[1].set_xlim(*nonzero_limits(counter_values))
    annotate_horizontal_bars(axes[1], bars, counter_values, digits=2)
    axes[1].grid(axis="x", alpha=0.25)

    if status != "completed":
        if status == "incorrect":
            message = "incorrect result: expected {}, actual {}, model valid={}".format(
                result.get("expected"),
                result.get("actual"),
                result.get("model_valid"),
            )
        else:
            message = result.get("error") or "deadline reached after {:.3f}s".format(
                float(result.get("wall_seconds", 0.0))
            )
        figure.text(
            0.5,
            0.01,
            str(message),
            ha="center",
            color=STATUS_COLORS.get(status, "#d62728"),
        )

    figure.tight_layout(rect=(0, 0.03, 1, 0.95))
    figure.savefig(destination, dpi=150, bbox_inches="tight")
    plt.close(figure)


def plot_aggregate(
    plt,
    aggregate: Mapping[str, Any],
    results: Sequence[Mapping[str, Any]],
    destination: Path,
) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    figure, axes = plt.subplots(1, 3, figsize=(21, 7))
    statuses = aggregate["statuses"]
    figure.suptitle(
        "{} — {} completed, {} incorrect, {} timed out, {} errors, {} skipped".format(
            aggregate["name"],
            statuses["completed"],
            statuses["incorrect"],
            statuses["timeout"],
            statuses["error"],
            statuses["skipped"],
        ),
        fontsize=13,
    )

    average_runtime = aggregate["average_runtime_seconds"]
    runtime_labels = ["wall"] + [label for label, _ in RUNTIME_METHODS]
    runtime_values = [float(aggregate["average_wall_seconds"])] + [
        float(average_runtime.get(label, 0.0)) for label, _ in RUNTIME_METHODS
    ]
    bars = axes[0].barh(runtime_labels, runtime_values, color="#1f77b4")
    axes[0].invert_yaxis()
    axes[0].set_xlabel("average seconds")
    axes[0].set_title("Average runtime profile\n(raw timers; some are nested)")
    axes[0].set_xlim(*nonzero_limits(runtime_values))
    annotate_horizontal_bars(axes[0], bars, runtime_values)
    axes[0].grid(axis="x", alpha=0.25)

    average_counters = aggregate["average_counters"]
    counter_labels = list(COUNTER_FIELDS)
    counter_values = [float(average_counters.get(key, 0.0)) for key in counter_labels]
    bars = axes[1].barh(counter_labels, counter_values, color="#9467bd")
    axes[1].invert_yaxis()
    axes[1].set_xlabel("average count / value")
    axes[1].set_title("Average solver statistics")
    axes[1].set_xlim(*nonzero_limits(counter_values))
    annotate_horizontal_bars(axes[1], bars, counter_values, digits=2)
    axes[1].grid(axis="x", alpha=0.25)

    completed_times = sorted(
        float(result.get("wall_seconds", 0.0))
        for result in results
        if result.get("status") == "completed"
    )
    if completed_times:
        axes[2].step(
            range(1, len(completed_times) + 1),
            completed_times,
            where="post",
            label="completed",
            color=STATUS_COLORS["completed"],
        )
        axes[2].legend()
    axes[2].set_xlabel("number of solved problems")
    axes[2].set_ylabel("wall seconds")
    axes[2].set_title("Cactus runtime plot")
    axes[2].grid(alpha=0.25)

    figure.tight_layout(rect=(0, 0.02, 1, 0.94))
    figure.savefig(destination, dpi=150, bbox_inches="tight")
    plt.close(figure)
