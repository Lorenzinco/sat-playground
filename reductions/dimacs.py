"""DIMACS serialization helpers."""

from os import PathLike
from pathlib import Path
from typing import List, Union

from reductions.data import Clause


PathValue = Union[str, PathLike[str]]


def serialize(clauses: List[Clause], num_variables: int) -> str:
    lines = ["p cnf {} {}".format(num_variables, len(clauses))]
    lines.extend("{} 0".format(" ".join(map(str, clause))) for clause in clauses)
    return "\n".join(lines) + "\n"


def write(path: PathValue, contents: str) -> None:
    Path(path).write_text(contents, encoding="ascii")
