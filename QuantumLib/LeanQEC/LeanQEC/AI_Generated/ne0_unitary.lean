/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

The following was proved by Aristotle:

- lemma ne0_unitary t [Nonempty t] [Fintype t] [DecidableEq t]
  (m : Matrix t t ℂ) (unitary_m : m ∈ Matrix.unitaryGroup t ℂ) :
  m ≠ 0
-/

import Mathlib


lemma ne0_unitary t [Nonempty t] [Fintype t] [DecidableEq t]
  (m : Matrix t t ℂ) (unitary_m : m ∈ Matrix.unitaryGroup t ℂ) :
  m ≠ 0 := by
    -- If $m$ were the zero matrix, then its determinant would be zero, contradicting the fact that it is unitary.
    by_contra h_zero;
    have := unitary_m.2;
    apply_fun Matrix.det at this; simp_all [Matrix.det_zero];
