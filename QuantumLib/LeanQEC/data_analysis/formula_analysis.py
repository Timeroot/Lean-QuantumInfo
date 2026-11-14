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
                    
def benchmark_lrat_physical_size(file_path: str):
    if not os.path.exists(file_path):
        print("Certificate file not found.")
        return

    # Get size in bytes
    size_bytes = os.path.getsize(file_path)
    
    # Convert to readable formats
    size_kb = size_bytes / 1024
    size_mb = size_kb / 1024

    print(f"--- Physical Certificate Benchmark ---")
    print(f"File Path: {file_path}")
    print(f"Size: {size_bytes} Bytes")
    print(f"Size: {size_kb:.2f} KB")
    print(f"Size: {size_mb:.2f} MB")

def analyze_solve_formula(path):
    formula = CNF(from_file=path)
    num_vars = formula.nv
    num_clauses = len(formula.clauses)
    print("--- Formula Statistics ---")
    print(f"File Loaded : {path}")
    print(f"Variables   : {num_vars}")
    print(f"Clauses     : {num_clauses}")
    print("--------------------------\n")
    with Solver(name='Cadical195', bootstrap_with=formula, use_timer=True) as solver:
        print("Solving...")
        # Optional: Track total wall-clock time in Python as an alternative reference
        python_start = time.perf_counter() 
        
        result = solver.solve()
        
        python_end = time.perf_counter()


        # 4. Extract Timing Data
        # solver.time() retrieves the time spent *specifically* during the last solve call
        internal_solve_time = solver.time()
        python_total_time = python_end - python_start

        proof_steps = solver.get_proof()

        save_as_lrat_file(proof_steps, "proof.lrat")
        
        os.remove("proof.lrat")

        print("\n--- Results & Performance ---")
        print(f"Result              : {'SATISFIABLE' if result else 'UNSATISFIABLE'}")
        print(f"Solver Internal Time: {internal_solve_time:.4f} seconds")
        print(f"Python Wrapper Time : {python_total_time:.4f} seconds")
        print("-----------------------------")
        return path, internal_solve_time, num_vars, num_clauses, size_bytes

results = ["file", "solve_time", "num_vars", "num_clauses"]
for f in os.scandir("bv_decide_queries"):
    results.append(analyze_solve_formula(f.path))
with open('formulas.csv', 'w', newline='') as f:
    writer = csv.writer(f)
    writer.writerows(results)