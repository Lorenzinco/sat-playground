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
        """
        Adds a new clause to the SAT problem.
        :param clause: A list of integers representing a clause, where positive integers represent positive literals and negative integers represent negated literals.
        """
        ...
    def solve(self, algorithm: Literal["dpll", "cdcl"], implication_point: Literal["uip","dip"]) -> None: 
        """
        Solves the SAT problem, to see the solution please inspect the model field of the class.
        :param algorithm: The algorithm to use for solving the SAT problem. Currently, only "dpll" and "cdcl" are supported.
        :param implication_point: The implication point mode to use when using the CDCL algorithm, dip is used to use the extended resolution proof system.
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
    def clauses_learnt(self)->int: ...
    """
    The number of clauses learned during CDCL sat solving. It is 0 if the solver was DPLL.
    """
    
    @property
    def avg_clause_length(self)->int:...
    """
    The average length of the clauses learnet, it is often a good measure of relevance of the conflicts.
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
    
    def __str__(self)->str:...
    """
    Prints a formatted view of all the stats.
    """