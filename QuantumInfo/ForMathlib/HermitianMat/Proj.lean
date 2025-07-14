import QuantumInfo.ForMathlib.HermitianMat.Basic

/-!
The positive parts, or equivalently the projections, of Hermitian matrices onto each other.
-/

noncomputable section
open HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Projector onto the non-negative eigenspace of `B - A`. Accessible by the notation
`{A ≤ₚ B}`, which is scoped to `HermitianMat`. This is the unique maximum operator `P`
such that `P^2 = P` and `P * A * P ≤ P * B * P` in the Loewner order. -/
def proj_le (A B : HermitianMat n 𝕜) : HermitianMat n 𝕜 :=
  (B - A).cfc (fun x ↦ if 0 ≤ x then 1 else 0)

-- Note this is in the opposite direction as in the Stein's Lemma paper, which uses `≥ₚ`
-- as the default ordering. We offer the `≥ₚ` notation which is the same with the arguments
-- flipped, similar to how `GT.gt` is defeq to `LT.lt` with arguments flipped.
scoped[HermitianMat] notation "{" A " ≤ₚ " B "}" => proj_le A B
scoped[HermitianMat] notation "{" A " ≥ₚ " B "}" => proj_le B A

variable (A B : HermitianMat n 𝕜)

theorem proj_le_cfc : {A ≤ₚ B} = cfc (fun x ↦ if 0 ≤ x then (1 : ℝ) else 0) (B - A).toMat := by
  simp only [proj_le, ← Matrix.IsHermitian.cfc_eq, HermitianMat.cfc]

theorem proj_le_sq : {A ≤ₚ B}^2 = {A ≤ₚ B} := by
  ext1
  simp only [HermitianMat.val_eq_coe, selfAdjoint.val_pow, proj_le_cfc]
  rw [← cfc_pow (hf := _)]
  · simp only [ge_iff_le, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, AddSubgroupClass.coe_sub, HermitianMat.val_eq_coe]
  · simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology, implies_true]

theorem proj_le_nonneg : 0 ≤ {A ≤ₚ B} := by
  rw [← proj_le_sq]
  exact HermitianMat.sq_nonneg

theorem proj_le_le_one : {A ≤ₚ B} ≤ 1 := by
  sorry

theorem proj_le_mul_nonneg : 0 ≤ {A ≤ₚ B}.toMat * (B - A).toMat := by
  rw [proj_le_cfc]
  nth_rewrite 2 [←cfc_id ℝ (B - A).toMat]
  rw [← cfc_mul (hf := _) (hg := _)]
  · apply cfc_nonneg
    intro x hx
    simp only [ge_iff_le, id_eq, ite_mul, one_mul, zero_mul]
    exact dite_nonneg (by simp only [imp_self]) (by simp only [not_le, le_refl, implies_true])
  · simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology, implies_true]
  · simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology, implies_true]

theorem proj_le_mul_le : {A ≤ₚ B}.toMat * A.toMat ≤ {A ≤ₚ B}.toMat * B.toMat := by
  rw [← sub_nonneg, ← mul_sub_left_distrib]
  convert proj_le_mul_nonneg A B

theorem proj_le_inner_nonneg : 0 ≤ {A ≤ₚ B}.inner (B - A) :=
  HermitianMat.inner_mul_nonneg (proj_le_mul_nonneg A B)

theorem proj_le_inner_le : {A ≤ₚ B}.inner A ≤ {A ≤ₚ B}.inner B := by
  rw [← sub_nonneg, ← HermitianMat.inner_left_sub]
  exact proj_le_inner_nonneg A B
