"""Tseitin contradictions and parity-extension guidance."""

from itertools import product
from random import Random
from typing import Dict, List, Optional, Sequence, Set, Tuple

from reductions.data import Clause, ReductionData
from reductions.extensions import (
    ExtensionPlanBuilder,
    ordered_pair,
    static_dag_guidance,
)


Edge = Tuple[int, int]


def _cubic_edges(vertices: int, seed: int) -> List[Edge]:
    cycle = {
        ordered_pair(vertex, vertex % vertices + 1)
        for vertex in range(1, vertices + 1)
    }
    random = Random(seed)
    labels = list(range(1, vertices + 1))
    matching: Optional[Set[Edge]] = None

    for _ in range(1000):
        random.shuffle(labels)
        candidate = {
            ordered_pair(labels[index], labels[index + 1])
            for index in range(0, vertices, 2)
        }
        if candidate.isdisjoint(cycle):
            matching = candidate
            break

    if matching is None:
        half = vertices // 2
        matching = {
            (vertex, vertex + half) for vertex in range(1, half + 1)
        }

    return sorted(cycle | matching)


def _parity_clauses(variables: Sequence[int], parity: int) -> List[Clause]:
    clauses: List[Clause] = []
    for assignment in product((0, 1), repeat=len(variables)):
        if sum(assignment) % 2 == parity:
            continue
        clauses.append(
            [
                -variable if value else variable
                for variable, value in zip(variables, assignment)
            ]
        )
    return clauses


def build(size: int, seed: int) -> ReductionData:
    if size < 4 or size % 2 != 0:
        raise ValueError("tseitin size must be an even integer of at least 4")

    vertices = size
    edges = _cubic_edges(vertices, seed)
    edge_variables = {edge: index for index, edge in enumerate(edges, start=1)}
    incident: Dict[int, List[int]] = {
        vertex: [] for vertex in range(1, vertices + 1)
    }
    for (first, second), variable in edge_variables.items():
        incident[first].append(variable)
        incident[second].append(variable)
    for variables in incident.values():
        variables.sort()
        if len(variables) != 3:
            raise RuntimeError("internal error: generated graph is not cubic")

    charges = {vertex: int(vertex == 1) for vertex in incident}
    clauses: List[Clause] = []
    for vertex in range(1, vertices + 1):
        clauses.extend(_parity_clauses(incident[vertex], charges[vertex]))

    num_variables = len(edges)
    plan = ExtensionPlanBuilder(num_variables)
    vertex_parities: Dict[int, int] = {}

    for vertex in range(1, vertices + 1):
        variables = incident[vertex]
        accumulator = variables[0]
        for offset, variable in enumerate(variables[1:], start=2):
            accumulator = plan.xor_gate(
                accumulator,
                variable,
                "vertex_{}_parity".format(vertex),
                "xor_incident_edge_{}_of_3".format(offset),
            )
        vertex_parities[vertex] = accumulator

    global_parity = vertex_parities[1]
    for vertex in range(2, vertices + 1):
        global_parity = plan.xor_gate(
            global_parity,
            vertex_parities[vertex],
            "global_parity",
            "xor_vertex_equations_through_{}".format(vertex),
        )

    guidance = static_dag_guidance(num_variables, plan)
    guidance["success"] = {
        "literal": global_parity,
        "forced_by_charges": 1,
        "forced_by_edge_cancellation": 0,
    }

    return ReductionData(
        problem="tseitin",
        size=size,
        num_variables=num_variables,
        clauses=clauses,
        extension_guidance=guidance,
        metadata={
            "encoding": "tseitin_parity_on_cubic_graph",
            "vertices": vertices,
            "edges": [
                {"first": edge[0], "second": edge[1], "variable": variable}
                for edge, variable in edge_variables.items()
            ],
            "incident_variables": [
                {"vertex": vertex, "variables": list(incident[vertex])}
                for vertex in range(1, vertices + 1)
            ],
            "charges": [charges[vertex] for vertex in range(1, vertices + 1)],
            "vertex_parity_literals": [
                vertex_parities[vertex] for vertex in range(1, vertices + 1)
            ],
            "global_parity_literal": global_parity,
        },
    )
