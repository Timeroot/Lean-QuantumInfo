/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import QuantumInfo.ForMathlib.HermitianMat.CFC
import QuantumInfo.ForMathlib.HermitianMat.Order
import QuantumInfo.ForMathlib.Misc

/-!
Facts connecting matrices, their ordering, and when they commute or not. This probably could be
reorganized to belong in other files better, but in the absence of a clear import hierarchy this
seems okay for now.
-/

theorem Commute.exists_HermitianMat_cfc {d : Type*} [Fintype d] [DecidableEq d]
  (A B : HermitianMat d ℂ) (hAB : Commute A.toMat B.toMat) :
    ∃ C : HermitianMat d ℂ, (∃ f : ℝ → ℝ, A = C.cfc f) ∧ (∃ g : ℝ → ℝ, B = C.cfc g) := by
  obtain ⟨C, ⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ := hAB.exists_cfc A.H B.H
  by_cases hC : C.IsHermitian
  · use ⟨C, hC⟩
    constructor
    · exact ⟨g₁, by simp [HermitianMat.ext_iff, hg₁]⟩
    · exact ⟨g₂, by simp [HermitianMat.ext_iff, hg₂]⟩
  · change ¬(IsSelfAdjoint C) at hC
    rw [cfc_apply_of_not_predicate C hC] at hg₁ hg₂
    use 0
    constructor
    · exact ⟨0, by simp [HermitianMat.ext_iff, hg₁]⟩
    · exact ⟨0, by simp [HermitianMat.ext_iff, hg₂]⟩

namespace HermitianMat

open ComplexOrder

theorem cfc_le_cfc_of_PosDef {d : Type*} [Fintype d] [DecidableEq d]
  {f g : ℝ → ℝ} (hfg : ∀ i, 0 < i → f i ≤ g i) (A : HermitianMat d ℂ) (hA : A.toMat.PosDef) :
    A.cfc f ≤ A.cfc g := by
  rw [← sub_nonneg, ← HermitianMat.cfc_sub, HermitianMat.zero_le_cfc]
  intro i
  rw [Pi.sub_apply, sub_nonneg]
  rw [A.H.posDef_iff_eigenvalues_pos] at hA
  apply hfg
  apply hA

theorem cfc_commute {d : Type*} [Fintype d] [DecidableEq d]
  (A B : HermitianMat d ℂ) (f g : ℝ → ℝ) (hAB : Commute A.toMat B.toMat) :
    Commute (A.cfc f).toMat (B.cfc g).toMat := by
  obtain ⟨C, ⟨h₁, rfl⟩, ⟨h₂, rfl⟩⟩ := hAB.exists_HermitianMat_cfc
  rw [commute_iff_eq, ← HermitianMat.cfc_comp, ← HermitianMat.cfc_comp, ← HermitianMat.coe_cfc_mul, ← HermitianMat.coe_cfc_mul, mul_comm (f ∘ h₁) (g ∘ h₂)]

theorem cfc_self_commute {d : Type*} [Fintype d] [DecidableEq d]
  (A : HermitianMat d ℂ) (f g : ℝ → ℝ) :
    Commute (A.cfc f).toMat (A.cfc g).toMat := by
  rw [commute_iff_eq, ← HermitianMat.coe_cfc_mul, ← HermitianMat.coe_cfc_mul, mul_comm f g]

/- TODO: Write a version of this that holds more broadly for some sets. Esp closed intervals of reals,
which correspond nicely to closed intervals of matrices. Write the specialization to Set.univ (Monotone
instead of MonotoneOn). Also a version that works for StrictMonoOn. -/
theorem cfc_le_cfc_of_commute_monoOn {d : Type*} [Fintype d] [DecidableEq d]
  {f : ℝ → ℝ} (hf : MonotoneOn f (Set.Ioi 0)) {A B : HermitianMat d ℂ} (hAB₁ : Commute A.toMat B.toMat)
  (hAB₂ : A ≤ B) (hA : A.toMat.PosDef) (hB : B.toMat.PosDef) :
    A.cfc f ≤ B.cfc f := by
  obtain ⟨C, ⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩ := hAB₁.exists_HermitianMat_cfc
  -- Need to show that g₁ ≤ g₂ on spectrum ℝ C
  rw [← C.cfc_comp, ← C.cfc_comp]
  rw [← sub_nonneg, ← C.cfc_sub, C.zero_le_cfc] at hAB₂ ⊢
  intro i
  simp only [HermitianMat.val_eq_coe, Pi.sub_apply, Function.comp_apply, sub_nonneg]
  apply hf
  · rw [HermitianMat.cfc_PosDef] at hA
    exact hA i
  · rw [HermitianMat.cfc_PosDef] at hB
    exact hB i
  · simpa using hAB₂ i

/-- TODO: See above -/
theorem cfc_le_cfc_of_commute {d : Type*} [Fintype d] [DecidableEq d]
  {f : ℝ → ℝ} (hf : Monotone f) {A B : HermitianMat d ℂ} (hAB₁ : Commute A.toMat B.toMat)
  (hAB₂ : A ≤ B) :
    A.cfc f ≤ B.cfc f := by
  obtain ⟨C, ⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩ := hAB₁.exists_HermitianMat_cfc
  -- Need to show that g₁ ≤ g₂ on spectrum ℝ C
  rw [← C.cfc_comp, ← C.cfc_comp]
  rw [← sub_nonneg, ← C.cfc_sub, C.zero_le_cfc] at hAB₂ ⊢
  intro i
  simp only [HermitianMat.val_eq_coe, Pi.sub_apply, Function.comp_apply, sub_nonneg]
  apply hf
  simpa using hAB₂ i

--This is the more general version that requires operator concave functions but doesn't require the inputs
-- to commute. Requires the correct statement of operator convexity though, which we don't have right now.
proof_wanted cfc_monoOn_pos_of_monoOn_posDef {d : Type*} [Fintype d] [DecidableEq d]
  {f : ℝ → ℝ} (hf_is_operator_convex : False) :
    MonotoneOn (HermitianMat.cfc · f) { A : HermitianMat d ℂ | A.toMat.PosDef }

proof_wanted log_monoOn_posDef {d : Type*} [Fintype d] [DecidableEq d] :
    MonotoneOn HermitianMat.log { A : HermitianMat d ℂ | A.toMat.PosDef }

/-- Monotonicity of log on commuting operators. -/
theorem log_le_log_of_commute {d : Type*} [Fintype d] [DecidableEq d]
  {A B : HermitianMat d ℂ} (hAB₁ : Commute A.toMat B.toMat) (hAB₂ : A ≤ B) (hA : A.toMat.PosDef) :
    A.log ≤ B.log := by
  refine HermitianMat.cfc_le_cfc_of_commute_monoOn ?_ hAB₁ hAB₂ hA ?_
  · exact Real.strictMonoOn_log.monotoneOn
  · --The fact that `A ≤ B` and `A.PosDef` implies `B.PosDef`. Should be a theorem, TODO
    -- This almost works but not quite:
    -- rw [← Matrix.isStrictlyPositive_iff_posDef] at hA ⊢
    -- exact hA.of_le hAB₂
    simpa using Matrix.PosDef.add_posSemidef hA hAB₂ --ew. abuse

/-- Monotonicity of exp on commuting operators. -/
theorem exp_le_exp_of_commute {d : Type*} [Fintype d] [DecidableEq d]
  {A B : HermitianMat d ℂ} (hAB₁ : Commute A.toMat B.toMat) (hAB₂ : A.cfc Real.exp ≤ B.cfc Real.exp) :
    A ≤ B := by
  have hA : A = (A.cfc Real.exp).cfc Real.log := by simp [← HermitianMat.cfc_comp]
  have hB : B = (B.cfc Real.exp).cfc Real.log := by simp [← HermitianMat.cfc_comp]
  rw [hA, hB]
  apply HermitianMat.log_le_log_of_commute
  · apply HermitianMat.cfc_commute
    exact hAB₁
  · exact hAB₂
  · rw [HermitianMat.cfc_PosDef]
    intro
    positivity

end HermitianMat
