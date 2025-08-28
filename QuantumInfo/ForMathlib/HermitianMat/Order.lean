import QuantumInfo.ForMathlib.HermitianMat.Inner

namespace HermitianMat

section possemidef
open ComplexOrder

variable {α : Type*} [RCLike α]
variable {n : Type*} [Fintype n]
variable  {A B C : HermitianMat n α} {M N : Matrix n n α}

theorem le_iff : A ≤ B ↔ (B - A).toMat.PosSemidef := by
  rfl

theorem zero_le_iff : 0 ≤ A ↔ A.toMat.PosSemidef := by
  rw [← propext_iff]
  apply congrArg Matrix.PosSemidef (sub_zero _)

theorem inner_mul_nonneg (h : 0 ≤ A.toMat * B.toMat) : 0 ≤ A.inner B := by
  rw [Matrix.PosSemidef.zero_le_iff_posSemidef] at h
  exact (RCLike.nonneg_iff.mp h.trace_nonneg).left

instance [DecidableEq n] : ZeroLEOneClass (HermitianMat n ℂ) where
  zero_le_one := by
    rw [HermitianMat.zero_le_iff]
    exact Matrix.PosSemidef.one

/-- The inner product for PSD matrices is nonnegative. -/
theorem inner_ge_zero (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ A.inner B := by
  rw [zero_le_iff] at hA hB
  open Classical in
  rw [inner_eq_re_trace, ← hA.sqrt_mul_self, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  nth_rewrite 1 [← hA.posSemidef_sqrt.left]
  exact (RCLike.nonneg_iff.mp (hB.conjTranspose_mul_mul_same _).trace_nonneg).left

theorem le_trace_smul_one [DecidableEq n] (hA : 0 ≤ A) : A ≤ (A.trace : ℝ) • 1 := by
  --mostly a copy of Matrix.PosSemidef.le_trace_smul_one from ForMathlib.Matrix.lean
  sorry
  -- have h : ∀ i, hA.1.eigenvalues i ≤ hA.1.rtrace := fun i ↦ by
  --   rw [←IsHermitian.sum_eigenvalues_eq_rtrace hA.1]
  --   convert @Finset.sum_le_sum_of_subset_of_nonneg n ℝ _ hA.1.eigenvalues {i} Finset.univ _ _
  --   · rw [Finset.sum_singleton]
  --   · exact Finset.subset_univ {i}
  --   · exact fun j _ _ ↦ eigenvalues_nonneg hA j
  -- exact (le_smul_one_of_eigenvalues_iff hA hA.1.rtrace).mp h

theorem inner_mono (hA : 0 ≤ A): B ≤ C → A.inner B ≤ A.inner C := fun hBC ↦ by
  classical have hTr : 0 ≤ A.inner (C - B) := inner_ge_zero hA (zero_le_iff.mpr hBC)
  rw [inner_left_sub] at hTr
  linarith

theorem inner_mono' (hA : 0 ≤ A) : B ≤ C → B.inner A ≤ C.inner A := fun hBC ↦ by
  -- classical have hTr : 0 ≤ A.inner (C - B) := inner_ge_zero hA (zero_le_iff.mpr hBC)
  -- rw [inner_left_sub] at hTr
  -- linarith
  rw [inner_comm B A, inner_comm C A]
  exact inner_mono hA hBC

theorem conj_le (hA : 0 ≤ A) [Fintype m] (M : Matrix m n α) : 0 ≤ A.conj M := by
  rw [zero_le_iff] at hA ⊢
  exact Matrix.PosSemidef.mul_mul_conjTranspose_same hA M

/-- The inner product for PSD matrices is at most the product of their traces. -/
theorem inner_le_mul_trace (hA : 0 ≤ A) (hB : 0 ≤ B) : A.inner B ≤ A.trace * B.trace := by
  classical convert inner_mono hA (le_trace_smul_one hB)
  simp [mul_comm]

/-- The inner product of two PSD matrices is zero iff they have disjoint support, i.e., each lives entirely
in the other's kernel. -/
theorem inner_zero_iff [DecidableEq n] (hA₁ : 0 ≤ A) (hB₁ : 0 ≤ B)
    : A.inner B = 0 ↔ (A.support ≤ B.ker) ∧ (B.support ≤ A.ker) :=
  sorry

theorem convex_cone (hA : 0 ≤ A) (hB : 0 ≤ B) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    : 0 ≤ (c₁ • A + c₂ • B) := by
  rw [zero_le_iff] at hA hB ⊢
  convert (hA.smul (RCLike.ofReal_nonneg.mpr hc₁)).add (hB.smul (RCLike.ofReal_nonneg.mpr hc₂))
  simp

theorem sq_nonneg [DecidableEq n] : 0 ≤ A^2 := by
  simp [zero_le_iff, pow_two]
  nth_rewrite 1 [←Matrix.IsHermitian.eq A.H]
  exact Matrix.posSemidef_conjTranspose_mul_self A.toMat

end possemidef
