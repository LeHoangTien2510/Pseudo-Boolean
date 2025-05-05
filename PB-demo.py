from pysat.pb import PBEnc

lits = [1, 2, 3]

cnf = PBEnc.atmost(lits=lits, bound=2, encoding=0)

for clause in cnf.clauses:
    print(clause)
