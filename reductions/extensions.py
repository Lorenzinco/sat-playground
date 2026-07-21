"""Construction of static AND-extension circuits."""

from dataclasses import dataclass
from typing import Dict, List, Tuple

from reductions.data import Clause


LiteralPair = Tuple[int, int]


def ordered_pair(left: int, right: int) -> LiteralPair:
    return (left, right) if left <= right else (right, left)


@dataclass(frozen=True)
class ExtensionStep:
    left: int
    right: int
    result: int

    def clauses(self) -> List[Clause]:
        return [
            [self.result, -self.left, -self.right],
            [-self.result, self.left],
            [-self.result, self.right],
        ]


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

    def and_gate(self, left: int, right: int) -> int:
        key = ordered_pair(left, right)
        cached = self._and_cache.get(key)
        if cached is not None:
            return cached

        result = self._next_variable
        self._next_variable += 1
        self._steps.append(ExtensionStep(left, right, result))
        self._and_cache[key] = result
        return result

    def xor_gate(self, left: int, right: int) -> int:
        both_false = self.and_gate(-left, -right)
        both_true = self.and_gate(left, right)
        return self.and_gate(-both_false, -both_true)


def static_dag_guidance(
    original_variables: int, builder: ExtensionPlanBuilder
) -> Dict[str, object]:
    return {
        "schema_version": 2,
        "kind": "static_and_dag",
        "original_variables": original_variables,
        "operands": [[step.left, step.right] for step in builder.steps],
    }
