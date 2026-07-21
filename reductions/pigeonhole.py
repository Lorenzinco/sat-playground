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


def _cook_guidance(matrix: List[List[int]]) -> RustMap:
    """Return a compact machine-readable grammar for every Cook reduction.

    At a state with an ``(m+1) x m`` literal matrix, any row and any column may
    be the removed pivot.  For every non-pivot cell ``(row, column)``:

    collision = matrix[row][pivot_column] AND matrix[pivot_row][column]
    merge     = -matrix[row][column] AND -collision
    next[row][column] = -merge

    The first extension may therefore be any two matrix cells in different
    rows and different columns.  Both diagonal orientations remain possible
    proof contexts, and the Rust consumer can retain both until later choices
    distinguish them.
    """
    return {
        "schema_version": 1,
        "kind": "pigeonhole_cook_state_machine",
        "connective": "and",
        "index_base": 0,
        "initial_matrix": [list(row) for row in matrix],
        "base_case_holes": 1,
        "pivot_policy": "any_row_and_any_column",
        "first_choice_rule": {
            "opcode": "matrix_diagonal",
            "different_rows": True,
            "different_columns": True,
            "emit_both_orientations": True,
        },
        "stage_domain": {
            "row": "all_except_pivot_row",
            "column": "all_except_pivot_column",
        },
        "stage_rules": [
            {
                "opcode": "define_collision",
                "left": {
                    "source": "matrix",
                    "row": "row",
                    "column": "pivot_column",
                    "sign": 1,
                },
                "right": {
                    "source": "matrix",
                    "row": "pivot_row",
                    "column": "column",
                    "sign": 1,
                },
                "store": "collision[row,column]",
            },
            {
                "opcode": "define_merge",
                "depends_on": "collision[row,column]",
                "left": {
                    "source": "matrix",
                    "row": "row",
                    "column": "column",
                    "sign": -1,
                },
                "right": {
                    "source": "collision",
                    "row": "row",
                    "column": "column",
                    "sign": -1,
                },
                "store": "merge[row,column]",
            },
        ],
        "transition": {
            "when": "all_non_pivot_cells_merged",
            "remove_pivot_row": True,
            "remove_pivot_column": True,
            "next_matrix_source": "merge",
            "next_matrix_sign": -1,
        },
        "success": {
            "when_holes": 1,
            "criterion": "PHP(2,1)",
        },
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
        extension_guidance=_cook_guidance(matrix),
        metadata={
            "encoding": "unary_weak_pigeonhole",
            "pigeons": pigeons,
            "holes": holes,
            "variable_matrix": [list(row) for row in matrix],
        },
    )
