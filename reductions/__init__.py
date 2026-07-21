"""Single public API for SAT reduction generators."""

from importlib import import_module
from typing import Callable, List, cast

import reductions.dimacs as dimacs
from reductions.data import Clause, ReductionData, RustMap


class Reduction:
    """Generate a SAT reduction and machine-readable ER guidance.

    ``size`` is the number of holes for pigeonhole and the even number of
    vertices for Tseitin.  Every value returned by :meth:`as_rust_data` is a
    plain bool, integer, string, list, or string-keyed dictionary so it can be
    converted directly through PyO3 or serialized before crossing the FFI.

    Clause, metadata, and guidance properties are read-only-by-convention views
    of the generated data. Avoiding deep copies keeps large PHP transfers from
    temporarily using roughly twice their normal Python memory.
    """

    _ALIASES = {
        "php": "pigeonhole",
        "pigeonhole": "pigeonhole",
        "pigeon-hole": "pigeonhole",
        "pigeonhole-principle": "pigeonhole",
        "pigehole": "pigeonhole",
        "tseitin": "tseitin",
    }

    def __init__(self, problem: str, size: int, seed: int = 0):
        if not isinstance(problem, str):
            raise TypeError("problem must be a string")
        if not isinstance(size, int) or isinstance(size, bool):
            raise TypeError("size must be an integer")
        if not isinstance(seed, int) or isinstance(seed, bool):
            raise TypeError("seed must be an integer")

        normalized = problem.strip().lower().replace("_", " ").replace(" ", "-")
        try:
            problem_name = self._ALIASES[normalized]
        except KeyError as error:
            raise ValueError(
                "unknown problem {!r}; supported problems: pigeonhole, tseitin".format(
                    problem
                )
            ) from error

        module = import_module("reductions." + problem_name)
        if problem_name == "pigeonhole":
            builder = cast(Callable[[int], ReductionData], getattr(module, "build"))
            self._data = builder(size)
        else:
            seeded_builder = cast(
                Callable[[int, int], ReductionData], getattr(module, "build")
            )
            self._data = seeded_builder(size, seed)
        self.seed = seed

    @property
    def problem(self) -> str:
        return self._data.problem

    @property
    def size(self) -> int:
        return self._data.size

    @property
    def num_variables(self) -> int:
        return self._data.num_variables

    @property
    def clauses(self) -> List[Clause]:
        return self._data.clauses

    @property
    def extension_guidance(self) -> RustMap:
        return self._data.extension_guidance

    @property
    def metadata(self) -> RustMap:
        return self._data.metadata

    def get_sat_encoding(self) -> List[Clause]:
        return self.clauses

    def as_rust_data(self) -> RustMap:
        """Return the complete reduction using only FFI-friendly values."""
        return {
            "schema_version": 1,
            "problem": self.problem,
            "size": self.size,
            "seed": self.seed,
            "num_variables": self.num_variables,
            "clauses": self.clauses,
            "extension_guidance": self.extension_guidance,
            "metadata": self.metadata,
        }

    def to_dimacs(self) -> str:
        return dimacs.serialize(self._data.clauses, self.num_variables)

    def write_dimacs(self, path: dimacs.PathValue) -> None:
        dimacs.write(path, self.to_dimacs())


__all__ = ["Reduction"]
