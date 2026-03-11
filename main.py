import clsat

clauses = [[1, -2, 3], [-1, 2, 4], [7, 2, 3], [-3, 2 , 4], [1, -2, -3], [-1, 2, -4], [-7, -2, -3], [3, 2 , 4]]

s = clsat.Sat(clauses)
s.add_clause([1, -2, 3])
s.solve()
print(s.model)