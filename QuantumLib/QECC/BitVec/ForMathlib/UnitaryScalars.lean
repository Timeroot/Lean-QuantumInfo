/-
Copyright (c) 2026 The Lean-QEC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mattias Ehatamm, Runzhou Tao
-/

import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Scalar multiples of matrices

Elementary facts about rescaling a nonzero matrix by a complex scalar, and about moving a
unit-norm scalar across an equation.  These are used to pin down the phase ambiguity in the
Pauli group.
-/

lemma raw_uphase_eq_is_1 {T U}
  [Nonempty T] [Nonempty U] [Fintype T] [Fintype U]
  {u : Matrix T U ℂ} (ne0_u : u ≠ 0)
  {z : ℂ}
  (eq : z • u = u) :
  z = 1 := by
    obtain ⟨i, j, hij⟩ : ∃ i j, u i j ≠ 0 := by
      by_contra h_contra
      push Not at h_contra
      exact ne0_u (by ext i j; exact h_contra i j)
    have hz_eq_one : z * u i j = u i j :=
      congr_fun (congr_fun eq i) j
    field_simp [hij] at hz_eq_one ⊢
    exact hz_eq_one

lemma raw_phase_star_move (a b c : ℂ)
  (norm_b : ‖b‖ = 1) :
  a * star b = c ↔ a = b * c := by
    have hb : b * star b = 1 := by
      simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_b]
    constructor
    · rintro rfl
      rw [mul_left_comm, hb, mul_one]
    · rintro rfl
      rw [mul_right_comm, hb, one_mul]

lemma raw_uphase_div {T U}
  [Nonempty T] [Nonempty U] [Fintype T] [Fintype U]
  (z z' : ℂ) (u u' : Matrix T U ℂ)
  (norm_z' : ‖z'‖ = 1)
  (eq : z • u = z' • u') :
  let r := z * star z'
  r • u = u' := by
    have hz' : z' * star z' = 1 := by
      simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_z']
    show (z * star z') • u = u'
    rw [mul_comm, mul_smul, eq, smul_smul, mul_comm, hz', one_smul]
