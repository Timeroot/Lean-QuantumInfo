/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.Trace

namespace HermitianMat

open ComplexOrder

variable {α : Type*} [RCLike α]
variable {n : Type*} [Fintype n]
variable  {A B C : HermitianMat n α} {M N : Matrix n n α}

open MatrixOrder in
/-- The `MatrixOrder` instance for Matrix (the Loewner order) we keep open for
HermitianMat, always. -/
instance : PartialOrder (HermitianMat n α) :=
  inferInstance

theorem le_iff : A ≤ B ↔ (B - A).toMat.PosSemidef := by
  rfl

theorem zero_le_iff : 0 ≤ A ↔ A.toMat.PosSemidef := by
  rw [← propext_iff]
  apply congrArg Matrix.PosSemidef (sub_zero _)

theorem le_iff_mulVec_le : A ≤ B ↔ ∀ x, star x ⬝ᵥ A.toMat.mulVec x ≤ star x ⬝ᵥ B.toMat.mulVec x := by
  have hH : (B.toMat - A.toMat).IsHermitian := Matrix.IsHermitian.sub B.H A.H
  simp [le_iff, Matrix.PosSemidef, hH, Matrix.sub_mulVec]

instance [DecidableEq n] : ZeroLEOneClass (HermitianMat n ℂ) where
  zero_le_one := by
    rw [HermitianMat.zero_le_iff]
    exact Matrix.PosSemidef.one

theorem lt_iff_posdef : A < B ↔ (B - A).toMat.PosSemidef ∧ A ≠ B :=
  lt_iff_le_and_ne

instance : IsStrictOrderedModule ℝ (HermitianMat n α) where
    smul_lt_smul_of_pos_left a ha b b₂ hb := by
      rw [HermitianMat.lt_iff_posdef] at hb ⊢
      simp only [← smul_sub, selfAdjoint.val_smul, val_eq_coe, AddSubgroupClass.coe_sub, ne_eq,
        smul_right_inj ha.ne']
      exact ⟨hb.left.smul ha.le, hb.right⟩
    smul_lt_smul_of_pos_right a ha b b2 hb := by
      rw [HermitianMat.lt_iff_posdef] at ha ⊢
      rw [sub_zero] at ha
      rw [← sub_pos] at hb
      convert And.intro (ha.left.smul hb.le) ha.right using 1
      · simp [← sub_smul]
      simp only [ne_eq, not_iff_not]
      constructor
      · intro h
        rw [eq_comm, ← sub_eq_zero, ← sub_smul] at h
        simpa [eq_comm, hb.ne'] using h
      · rintro rfl; simp

--Without these shortcut instances, `gcongr` fails to close certain goals...? Why? TODO
instance : PosSMulMono ℝ (HermitianMat n α) := inferInstance
instance : SMulPosMono ℝ (HermitianMat n α) := inferInstance

theorem le_trace_smul_one [DecidableEq n] (hA : 0 ≤ A) : A ≤ (A.trace : ℝ) • 1 := by
  have hA' : A.toMat.PosSemidef := zero_le_iff.mp hA
  refine (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hA'.1 A.trace).mp ?_
  rw [← A.sum_eigenvalues_eq_trace]
  intro i
  exact Finset.single_le_sum (fun j _ ↦ hA'.eigenvalues_nonneg j) (Finset.mem_univ i)

theorem conj_le (hA : 0 ≤ A) [Fintype m] (M : Matrix m n α) : 0 ≤ A.conj M := by
  rw [zero_le_iff] at hA ⊢
  exact Matrix.PosSemidef.mul_mul_conjTranspose_same hA M

theorem convex_cone (hA : 0 ≤ A) (hB : 0 ≤ B) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    : 0 ≤ (c₁ • A + c₂ • B) := by
  rw [zero_le_iff] at hA hB ⊢
  exact (hA.smul hc₁).add (hB.smul hc₂)

theorem sq_nonneg [DecidableEq n] : 0 ≤ A^2 := by
  simp [zero_le_iff, pow_two]
  nth_rewrite 1 [←Matrix.IsHermitian.eq A.H]
  exact Matrix.posSemidef_conjTranspose_mul_self A.toMat

theorem ker_antitone [DecidableEq n] (hA : 0 ≤ A) : A ≤ B → B.ker ≤ A.ker := fun h x hB ↦ by
  rw [HermitianMat.mem_ker_iff_mulVec_zero] at *
  replace h := (le_iff_mulVec_le.mp h) x
  rw [hB, dotProduct_zero] at h
  apply (Matrix.PosSemidef.dotProduct_mulVec_zero_iff (zero_le_iff.mp hA) x).mp
  exact eq_of_le_of_ge h ((zero_le_iff.mp hA).2 x)
