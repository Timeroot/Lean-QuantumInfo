import QuantumInfo.ForMathlib.HermitianMat.Trace

namespace HermitianMat

open ComplexOrder

variable {α : Type*} [RCLike α]
variable {n : Type*} [Fintype n]
variable  {A B C : HermitianMat n α} {M N : Matrix n n α}

theorem le_iff : A ≤ B ↔ (B - A).toMat.PosSemidef := by
  rfl

theorem zero_le_iff : 0 ≤ A ↔ A.toMat.PosSemidef := by
  rw [← propext_iff]
  apply congrArg Matrix.PosSemidef (sub_zero _)

instance [DecidableEq n] : ZeroLEOneClass (HermitianMat n ℂ) where
  zero_le_one := by
    rw [HermitianMat.zero_le_iff]
    exact Matrix.PosSemidef.one

theorem lt_iff_posdef : A < B ↔ (B - A).toMat.PosSemidef ∧ A ≠ B :=
  lt_iff_le_and_ne

instance : OrderedSMul ℝ (HermitianMat n α) where
  smul_lt_smul_of_pos hab hc := by
    rw [HermitianMat.lt_iff_posdef] at hab ⊢
    simp [← smul_sub, smul_right_inj hc.ne']
    exact ⟨hab.left.smul hc.le, hab.right⟩
  lt_of_smul_lt_smul_of_pos hab hc := by
    rw [HermitianMat.lt_iff_posdef] at hab ⊢
    convert And.intro (hab.left.smul (inv_pos_of_pos hc).le) hab.right using 1
    · simp [← smul_sub, smul_smul, inv_mul_cancel₀ hc.ne']
    · simp [smul_right_inj hc.ne']

--Without these shortcut instances, `gcongr` fails to close certain goals...? Why?
instance : PosSMulMono ℝ (HermitianMat n α) := inferInstance
instance : SMulPosMono ℝ (HermitianMat n α) := inferInstance

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
