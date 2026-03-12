from typing import Literal
class Sat:
    """
    Class representing a SAT problem. It is initialized as a list of clauses and can be modified by adding new clauses. The solve method returns a solution to the problem, if it exists.
    :param clauses: A list of clauses, where each clause is a list of integers representing literals. Positive integers represent positive literals, while negative integers represent negated literals.
    """
    def __init__(self, clauses: list[list[int]]) -> None: ...
    def add_clause(self, clause: list[int]) -> None: 
        """
        Adds a new clause to the SAT problem.
        :param clause: A list of integers representing a clause, where positive integers represent positive literals and negative integers represent negated literals.
        """
        ...
    def solve(self, algorithm: Literal["dpll", "cdcl"]) -> None: 
        """
        Solves the SAT problem, to see the solution please inspect the model field of the class.
        :param algorithm: The algorithm to use for solving the SAT problem. Currently, only "dpll" and "cdcl" are supported.
        """
        ...