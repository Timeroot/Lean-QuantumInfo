# Quantum Error Correction in Lean

[![CI](https://github.com/VerifiedQC/Lean-QEC/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/VerifiedQC/Lean-QEC/actions/workflows/lean_action_ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
[![arXiv](https://img.shields.io/badge/arXiv-2605.16523-b31b1b.svg)](https://arxiv.org/abs/2605.16523)
[![Lean](https://img.shields.io/badge/Lean-v4.30.0--rc2-black.svg)](https://github.com/leanprover/lean4/releases/tag/v4.30.0-rc2)

This project formalizes and verifies the theory of Quantum Error Correction in Lean in an end-to-end fashion, from basic Quantum theory to abstract properties. Some accomplishments include:
 * Formalizing basic quantum computing concepts such as Qubits, Quantum States, and the Pauli Group.
 * Verifying the link between the Pauli Group and the Binary Symplectic Representation.
 * Formalizing Stabilizer Codes and CSS codes, reasoning about their code properties.
 * A SAT-assisted computer algebra pipeline for the verification of Stabilizer Code properties like code distance.
 * Concrete distance verification for a number of codes such as large codes belonging to the Bivariate Bicycle family.

This project is built on top of Mathlib4.

 ## Distance Verification

The primary innovation of Lean-QEC is its set of tools for automatic verification of code properties such as code distance. This is accomplished through a novel code parameters-to-SAT translation fully verified in Lean, allowing for full confidence in values previously only known through opaque calculation.

 ## Major Theorems

 ```lean
theorem BinSympMatrix.distance_eq_distance {k n : ℕ} (B : BinSympMatrix k n) (h_comm : B.isCommuting) (hk : 0 < k) :
  (StabCode_of_BinSympMatrix B h_comm).distance = B.distance hk
```

This theorem proves the relationship between the binary symplectic formulation of distance and the stabilizer-theoretic notion.

 ```lean
theorem bitvec_sat_translation_correct
  {n k₁ k₂ xkersize zkersize : ℕ} [NeZero n] [NeZero k₁] [NeZero k₂] [NeZero (n - k₁)] [NeZero (n - k₂)]
  (css : CSS_pair n k₁ k₂)
  (xker : Matrix (Fin xkersize) (Fin n) (ZMod 2))
  (xker_correct : xker.is_ker_for css.H₂)
  (zker : Matrix (Fin zkersize) (Fin n) (ZMod 2))
  (zker_correct : zker.is_ker_for css.H₁)
  {dist : ℕ}
  (dist_le : dist ≤ n)
   :
  lt_dist_sat (flatten_matrix css.H₁) (flatten_matrix xker) (dist - 1) (Nat.clog 2 n) →
  lt_dist_sat (flatten_matrix css.H₂) (flatten_matrix zker) (dist - 1) (Nat.clog 2 n) →
  dist ≤ css.toBSM.distance (by apply NeZero.pos)
```

This theorem links the Binary Symplectic distance of a CSS code to the SAT formulation of the distance, allowing for automatic distance verification.

```lean
theorem BB72_dist_6 : 6 ≤ BB72_css.toBSM.distance (by norm_num)
```

This theorem gives a lower bound for the distance of the 72-qubit bivariate bicycle code.

 ## Installing Lean-QEC
 - Clone this repository.
 - In a terminal in the top-level directory, run `lake exe cache get` to fetch Mathlib and dependencies.
 - Run `lake build` to build the project.
 - Open the directory in VSCode for infoview access to files.

 ## Future Directions
 - Figure out how far the framework currently scales, and where the bottlenecks are.
   Then, push further until we reach the $$[[144, 12, 12]]$$ BB code, or even $$[[288, 12, 18]]$$.
 - Formalization of codes with pen-and-paper-proof-based distance specifications like the Toric Code.
 - Including different error channels and proving the correctness of code distance under them.
 - Expansion to qudit codes.

 ## Citation

If you use Lean-QEC in your research, please cite the accompanying paper, [End-to-End Formalization of Quantum Error Correction](https://arxiv.org/abs/2605.16523) ([`CITATION.bib`](CITATION.bib)):

```bibtex
@article{ehatamm2026endtoend,
  title         = {End-to-End Formalization of Quantum Error Correction},
  author        = {Ehatamm, Mattias and Lee, Yi and Wu, Xiaodi and Tao, Runzhou},
  year          = {2026},
  eprint        = {2605.16523},
  archivePrefix = {arXiv},
  primaryClass  = {quant-ph},
  journal       = {arXiv preprint arXiv:2605.16523}
}
```

 ## License

This project is licensed under the Apache License 2.0. See the [LICENSE](LICENSE) file for the full text and [NOTICE](NOTICE) for attribution.
