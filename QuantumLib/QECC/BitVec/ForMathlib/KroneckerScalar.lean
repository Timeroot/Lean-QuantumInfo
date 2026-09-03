/-
Copyright (c) 2026 The Lean-QEC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mattias Ehatamm
-/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.LinearCombination

/-!
# Rigidity of the Kronecker product

A Kronecker product of nonzero matrices determines its two factors up to a reciprocal pair of
scalars.
-/

lemma kron_injective_up_to_scalar {T₁ U₁ T₂ U₂}
    [Fintype T₁] [Fintype T₂] [Fintype U₁] [Fintype U₂]
    {M₁ M₁' : Matrix T₁ U₁ ℂ} {M₂ M₂' : Matrix T₂ U₂ ℂ}
    (eq_krons : M₁.kronecker M₂ = M₁'.kronecker M₂')
    (ne0_M1 : M₁ ≠ 0) (ne0_M2 : M₂ ≠ 0) :
    ∃ z : ℂˣ, M₁ = z • M₁' ∧ M₂ = z⁻¹ • M₂' := by
  have h_eq : ∀ a b i j, M₁ a b * M₂ i j = M₁' a b * M₂' i j := fun a b i j => by
    simpa [Matrix.kronecker_apply] using congr_fun (congr_fun eq_krons (a, i)) (b, j)
  obtain ⟨i, j, hij⟩ : ∃ i j, M₂ i j ≠ 0 := by
    by_contra h
    push Not at h
    exact ne0_M2 (by ext i j; exact h i j)
  obtain ⟨k, l, hkl⟩ : ∃ k l, M₁ k l ≠ 0 := by
    by_contra h
    push Not at h
    exact ne0_M1 (by ext k l; exact h k l)
  set c : ℂ := M₂' i j / M₂ i j with hc_def
  have hM₁ : M₁ = c • M₁' := by
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul, hc_def, div_mul_eq_mul_div, eq_div_iff hij]
    linear_combination h_eq a b i j
  have hc : c ≠ 0 := by
    rintro hc0
    exact hkl (by simp [hM₁, hc0])
  have hM₁'kl : M₁' k l ≠ 0 := fun h => hkl (by simp [hM₁, h])
  refine ⟨Units.mk0 c hc, hM₁, ?_⟩
  ext p q
  simp only [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, Matrix.smul_apply,
    smul_eq_mul]
  rw [eq_inv_mul_iff_mul_eq₀ hc]
  refine mul_left_cancel₀ hM₁'kl ?_
  have h := h_eq k l p q
  rw [hM₁] at h
  simp only [Matrix.smul_apply, smul_eq_mul] at h
  linear_combination h
