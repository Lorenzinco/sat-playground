from typing import Literal
class Sat:
    """
    Class representing a SAT problem. It is initialized as a list of clauses and can be modified by adding new clauses. The solve method returns a solution to the problem, if it exists.
    :param clauses: A list of clauses, where each clause is a list of integers representing literals. Positive integers represent positive literals, while negative integers represent negated literals.
    """

    @property
    def model(self)->list[bool] | None: ...
    """
    A list of booleans representing the solution to the problem.
    """

    @property
    def stats(self)->Stats|None: ...
    """
    Retrieve the stats of the execution.
    """

    def __init__(self, clauses: list[list[int]]) -> None: ...
    def add_clause(self, clause: list[int]) -> None:
        """Adds a new clause to the SAT problem.

        Args:
            clause: A list of integers representing a clause, where positive integers represent positive literals and negative integers represent negated literals.
        """
        ...
    def solve(
        self, 
        algorithm: Literal["dpll", "cdcl"], 
        implication_point: Literal["uip","dip"], 
        preprocess: list[Literal["bva","bve","subsumption"]], 
        inprocessing: list[Literal["bva","bve","subsumption"]],
        heuristics: Literal["vsids","random"], 
        drat_path: str|None = None
        ) -> None:
        """Solve the SAT problem.

        Args:
            algorithm: The algorithm to use ("dpll" or "cdcl").
            implication_point: UIP/DIP mode for CDCL.
            preprocess: Preprocessing techniques to apply.
            heuristics: Literal selection heuristic.
            drat_path: If given, write a DRAT proof to this path.
        """
        ...

class Stats:
    """
    Class representing the subclass inside sat to retrieve the stats of the execution, do not use it by itself.
    """

    @property
    def conflicts(self)-> int: ...
    """
    Retrieves the number of conflicts during the execution of the solver.
    """

    @property
    def restarts(self)-> int: ...
    """
    Retrieves the number of CDCL restarts during the execution of the solver.
    """

    @property
    def clauses_learnt(self)->int: ...
    """
    The number of clauses learned during CDCL sat solving. It is 0 if the solver was DPLL.
    """

    @property
    def clauses_deleted(self)->int: ...
    """
    The number of learnt clauses deleted during clause database reduction.
    """

    @property
    def clauses_subsumed(self)->int: ...
    """
    The number of clauses removed by subsumption preprocessing/inprocessing.
    """

    @property
    def subsumption_checks(self)->int: ...
    """
    The number of exact subset checks performed by lazy subsumption.
    """

    @property
    def minimized_literals(self)->int: ...
    """
    The number of literals removed by learned-clause minimization.
    """

    @property
    def clauses_kept(self)->int: ...
    """
    The number of learnt clauses still kept after clause database reductions.
    """

    @property
    def literals_learnt(self)->int: ...
    """
    The total number of auxiliary literals added by extension/DIP and BVA.
    """

    @property
    def extension_literals(self)->int: ...
    """
    The number of auxiliary extension literals added by DIP learning.
    """

    @property
    def bva_literals(self)->int: ...
    """
    The number of auxiliary literals added by bounded variable addition.
    """

    @property
    def avg_clause_length(self)->float:...
    """
    The average length of the clauses learnt, it is often a good measure of relevance of the conflicts.
    """

    def elapsed_secs(self)->int:...
    """
    Returns the elapsed time of the solving in seconds.
    """

    def elapsed_nanos(self)->int:...
    """
    Returns the elapsed time of the solving in nanoseconds.
    """

    def elapsed_millis(self)->int:...
    """
    Returns the elapsed time of the solving in milliseconds.
    """

    def preprocessing_millis(self)->float:...
    def solving_millis(self)->float:...
    def propagation_millis(self)->float:...
    def conflict_analysis_millis(self)->float:...
    def clause_minimization_millis(self)->float:...
    def clause_learning_millis(self)->float:...
    def db_reduction_millis(self)->float:...
    def subsumption_millis(self)->float:...
    def restart_millis(self)->float:...
    def inprocessing_millis(self)->float:...

    def __str__(self)->str:...
    """
    Prints a formatted view of all the stats.
    """
