"""Unary pigeonhole CNF and Cook induction guidance."""

from itertools import combinations
from typing import List

from reductions.data import Clause, ReductionData, RustMap


def _variable(pigeon: int, hole: int, holes: int) -> int:
    return pigeon * holes + hole + 1


def _variable_matrix(holes: int) -> List[List[int]]:
    return [
        [_variable(pigeon, hole, holes) for hole in range(holes)]
        for pigeon in range(holes + 1)
    ]


def _cook_guidance(holes: int) -> RustMap:
    """Describe the Cook reduction interpreted by the Rust consumer."""
    return {
        "schema_version": 2,
        "kind": "pigeonhole_cook",
        "holes": holes,
    }


def build(size: int) -> ReductionData:
    if size < 1:
        raise ValueError("pigeonhole size must be at least 1")

    holes = size
    pigeons = holes + 1
    matrix = _variable_matrix(holes)
    clauses: List[Clause] = []

    for pigeon in range(pigeons):
        clauses.append(list(matrix[pigeon]))

    for hole in range(holes):
        for first, second in combinations(range(pigeons), 2):
            clauses.append([-matrix[first][hole], -matrix[second][hole]])

    return ReductionData(
        problem="pigeonhole",
        size=size,
        num_variables=pigeons * holes,
        clauses=clauses,
        extension_guidance=_cook_guidance(holes),
        metadata={
            "encoding": "unary_weak_pigeonhole",
            "pigeons": pigeons,
            "holes": holes,
            "variable_matrix": [list(row) for row in matrix],
        },
    )
