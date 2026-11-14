from sympy import symbols, to_cnf
from pysat.solvers import Solver
from pysat.formula import CNF
import time
import os
import csv

def save_as_lrat_file(proof_steps, filename="proof.lrat"):
    """Takes the list of proof steps from PySAT and writes them 

    out in a formatted text structure.
    """
    with open(filename, "w", encoding="utf-8") as f:
        # LRAT steps usually require an incremental line index
        for index, clause in enumerate(proof_steps, start=1):
            # Format: <line_number> <clause_literals> 0 <antecedents> 0
            # For direct solver outputs, we convert literals to a space-separated string
            clause_str = " ".join(map(str, clause))
            # Write out standard LRAT line format
            f.write(f"{index} {clause_str} 0 \n")

def solve_formula(path, rs):
    formula = CNF(from_file=path)
    with Solver(name='Cadical195', bootstrap_with=formula, use_timer=True, ) as solver:
        solver.configure({
            "seed":rs,
            "lrat":1
        })
        python_start = time.perf_counter() 
        
        result = solver.solve()
        
        python_end = time.perf_counter()


        # 4. Extract Timing Data
        # solver.time() retrieves the time spent *specifically* during the last solve call
        internal_solve_time = solver.time()
        python_total_time = python_end - python_start

        proof_steps = solver.get_proof()
        save_as_lrat_file(proof_steps, "proof.lrat")
        size = os.path.getsize("proof.lrat")
        os.remove("proof.lrat")
        return python_total_time, size

print(solve_formula("bv_decide_queries/BB72_x_dist.cnf", 12))
