import QuantumInfo.ForMathlib.HermitianMat.CFC
import QuantumInfo.ForMathlib.HermitianMat.Inner

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
  simp only [proj_le, HermitianMat.cfc]

theorem proj_le_sq : {A ≤ₚ B}^2 = {A ≤ₚ B} := by
  ext1
  simp only [HermitianMat.val_eq_coe, selfAdjoint.val_pow, proj_le_cfc]
  rw [← cfc_pow _ 2 (hf := _)]
  · simp
  · simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology]

theorem proj_le_nonneg : 0 ≤ {A ≤ₚ B} := by
  rw [← proj_le_sq]
  exact HermitianMat.sq_nonneg

theorem proj_le_le_one : {A ≤ₚ B} ≤ 1 := by
  --The whole `rw` line is a defeq, i.e. `change _root_.cfc _ (B - A).toMat ≤ 1` works too.
  --TODO better API.
  rw [← Subtype.coe_le_coe, val_eq_coe, selfAdjoint.val_one, proj_le_cfc]
  apply cfc_le_one (f := fun x ↦ if 0 ≤ x then 1 else 0)
  intros; split <;> norm_num

theorem proj_le_mul_nonneg : 0 ≤ {A ≤ₚ B}.toMat * (B - A).toMat := by
  rw [proj_le_cfc]
  nth_rewrite 2 [← cfc_id ℝ (B - A).toMat]
  rw [← cfc_mul (hf := _) (hg := _)]
  · apply cfc_nonneg
    aesop
  · --TODO: It's a failure that cfc_cont_tac doesn't use these theorems. We could add
    -- them to the `CStarAlgebra` aesop rule_set, but even then `fun_prop` doesn't try
    -- the discharger once if it's stuck at the root, so we'd also need cfc_cont_tac
    -- to try the aesop once itself first.
    simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology]
  · simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology]

theorem proj_le_mul_le : {A ≤ₚ B}.toMat * A.toMat ≤ {A ≤ₚ B}.toMat * B.toMat := by
  rw [← sub_nonneg, ← mul_sub_left_distrib]
  exact proj_le_mul_nonneg A B

theorem proj_le_inner_nonneg : 0 ≤ {A ≤ₚ B}.inner (B - A) :=
  HermitianMat.inner_mul_nonneg (proj_le_mul_nonneg A B)

theorem proj_le_inner_le : {A ≤ₚ B}.inner A ≤ {A ≤ₚ B}.inner B := by
  rw [← sub_nonneg, ← HermitianMat.inner_left_sub]
  exact proj_le_inner_nonneg A B
