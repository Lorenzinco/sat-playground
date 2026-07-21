"""Internal transport model shared by reduction generators."""

from dataclasses import dataclass
from typing import Dict, List


Clause = List[int]
RustMap = Dict[str, object]


@dataclass(frozen=True)
class ReductionData:
    problem: str
    size: int
    num_variables: int
    clauses: List[Clause]
    extension_guidance: RustMap
    metadata: RustMap
