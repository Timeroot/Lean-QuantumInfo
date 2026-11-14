# Sorry inventory

Last updated: 2026-05-06.

Scope: active `sorry`/`admit` occurrences under `LeanQEC/**/*.lean`, excluding line comments and block comments.

Current active unresolved count: 0.

## Notes

- The remaining textual matches from `rg "sorry|admit" LeanQEC` are inside block comments.
- In `LeanQEC/ComputerAlgebra/BitVecCorrectness.lean`, the old runtime-indexed `row_bv_correct` / `mutually_orth_correct` path is commented out. The maintained distance examples use `mutually_orth_nat_correct`.
- In `LeanQEC/Channels/Pauli_Channels.lean`, the unfinished `of_kraus_prob_unitary` sketch is commented out because it is outside the maintained distance-theorem dependency path.
