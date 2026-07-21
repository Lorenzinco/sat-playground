"""Construction of static AND-extension circuits."""

from dataclasses import dataclass
from typing import Dict, List, Tuple

from reductions.data import Clause, RustMap


LiteralPair = Tuple[int, int]


def ordered_pair(left: int, right: int) -> LiteralPair:
    return (left, right) if left <= right else (right, left)


@dataclass(frozen=True)
class ExtensionStep:
    left: int
    right: int
    result: int
    stage: str
    purpose: str

    def clauses(self) -> List[Clause]:
        return [
            [self.result, -self.left, -self.right],
            [-self.result, self.left],
            [-self.result, self.right],
        ]

    def as_rust_data(self) -> RustMap:
        return {
            "left": self.left,
            "right": self.right,
            "result": self.result,
            "stage": self.stage,
            "purpose": self.purpose,
        }


class ExtensionPlanBuilder:
    """Build a deduplicated DAG of ``result <-> left AND right`` steps."""

    def __init__(self, original_variables: int):
        self._next_variable = original_variables + 1
        self._steps: List[ExtensionStep] = []
        self._and_cache: Dict[LiteralPair, int] = {}

    @property
    def steps(self) -> List[ExtensionStep]:
        return list(self._steps)

    @property
    def total_variables(self) -> int:
        return self._next_variable - 1

    def and_gate(self, left: int, right: int, stage: str, purpose: str) -> int:
        key = ordered_pair(left, right)
        cached = self._and_cache.get(key)
        if cached is not None:
            return cached

        result = self._next_variable
        self._next_variable += 1
        self._steps.append(ExtensionStep(left, right, result, stage, purpose))
        self._and_cache[key] = result
        return result

    def xor_gate(self, left: int, right: int, stage: str, purpose: str) -> int:
        both_false = self.and_gate(
            -left, -right, stage, purpose + ": both inputs false"
        )
        both_true = self.and_gate(left, right, stage, purpose + ": both inputs true")
        return self.and_gate(
            -both_false,
            -both_true,
            stage,
            purpose + ": neither equal case (XOR output)",
        )


def static_dag_guidance(
    original_variables: int, builder: ExtensionPlanBuilder
) -> RustMap:
    return {
        "schema_version": 1,
        "kind": "static_and_dag",
        "connective": "and",
        "choice_policy": "any_ready_step",
        "original_variables": original_variables,
        "total_variables": builder.total_variables,
        "steps": [step.as_rust_data() for step in builder.steps],
    }
