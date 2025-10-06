import QuantumInfo.ForMathlib.HermitianMat.CFC

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

/-!
The positive parts, or equivalently the projections, of Hermitian matrices onto each other.
-/

noncomputable section
namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Projector onto the non-negative eigenspace of `B - A`. Accessible by the notation
`{A ≤ₚ B}`, which is scoped to `HermitianMat`. This is the unique maximum operator `P`
such that `P^2 = P` and `P * A * P ≤ P * B * P` in the Loewner order. -/
def proj_le (A B : HermitianMat n 𝕜) : HermitianMat n 𝕜 :=
  (B - A).cfc (fun x ↦ if 0 ≤ x then 1 else 0)

/-- Projector onto the positive eigenspace of `B - A`. Accessible by the notation
`{A <ₚ B}`, which is scoped to `HermitianMat`. Compare with `proj_le`. -/
noncomputable def proj_lt (A B : HermitianMat n 𝕜) : HermitianMat n 𝕜 :=
  (B - A).cfc (fun x ↦ if 0 < x then 1 else 0)

-- Note this is in the opposite direction as in the Stein's Lemma paper, which uses `≥ₚ`
-- as the default ordering. We offer the `≥ₚ` notation which is the same with the arguments
-- flipped, similar to how `GT.gt` is defeq to `LT.lt` with arguments flipped.
-- We put the ≥ₚ first, since both can delaborate and we want to show the ≤ₚ one.
scoped notation "{" A " ≥ₚ " B "}" => proj_le B A
scoped notation "{" A " ≤ₚ " B "}" => proj_le A B

scoped notation "{" A " >ₚ " B "}" => proj_lt B A
scoped notation "{" A " <ₚ " B "}" => proj_lt A B

variable (A B : HermitianMat n 𝕜)

theorem proj_le_def : {A ≤ₚ B} = (B - A).cfc (fun x ↦ if 0 ≤ x then 1 else 0) := by
  rfl

theorem proj_lt_def : {A <ₚ B} = (B - A).cfc (fun x ↦ if 0 < x then 1 else 0) := by
  rfl

theorem proj_le_sq : {A ≤ₚ B}^2 = {A ≤ₚ B} := by
  rw [proj_le_def]
  --TODO: Should do a `HermitianMat.cfc_pow`.
  ext1
  simp only [selfAdjoint.val_pow, cfc]
  rw [← cfc_pow _ 2 (hf := _)]
  · simp
  · simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology]

theorem proj_lt_sq : {A <ₚ B}^2 = {A <ₚ B} := by
  rw [proj_lt_def]
  --TODO: Should do a `HermitianMat.cfc_pow`.
  ext1
  simp only [selfAdjoint.val_pow, cfc]
  rw [← cfc_pow _ 2 (hf := _)]
  · simp
  · simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology]

theorem proj_zero_le_cfc : {0 ≤ₚ A} = cfc A (fun x ↦ if 0 ≤ x then 1 else 0) := by
  simp only [proj_le, sub_zero]

theorem proj_zero_lt_cfc : {0 <ₚ A} = cfc A (fun x ↦ if 0 < x then 1 else 0) := by
  simp only [proj_lt, sub_zero]

theorem proj_le_zero_cfc : {A ≤ₚ 0} = cfc A (fun x ↦ if x ≤ 0 then 1 else 0) := by
  simp only [proj_le, zero_sub]
  --TODO: Should do a `HermitianMat.cfc_comp_neg`.
  nth_rw 1 [← cfc_id A]
  rw [← cfc_neg, ← cfc_comp]
  congr! 2 with x
  simp

theorem proj_lt_zero_cfc : {A <ₚ 0} = cfc A (fun x ↦ if x < 0 then 1 else 0) := by
  simp only [proj_lt, zero_sub]
  --TODO: Should do a `HermitianMat.cfc_comp_neg`.
  nth_rw 1 [← cfc_id A]
  rw [← cfc_neg, ← cfc_comp]
  congr! 2 with x
  simp

theorem proj_le_nonneg : 0 ≤ {A ≤ₚ B} := by
  rw [proj_le, zero_le_cfc]
  intro i
  apply ite_nonneg <;> norm_num

theorem proj_lt_nonneg : 0 ≤ {A <ₚ B} := by
  rw [proj_lt, zero_le_cfc]
  intro i
  apply ite_nonneg <;> norm_num

theorem proj_le_le_one : {A ≤ₚ B} ≤ 1 := by
  --The whole `rw` line is a defeq, i.e. `change _root_.cfc _ (B - A).toMat ≤ 1` works too.
  --TODO better API.
  rw [← Subtype.coe_le_coe, val_eq_coe, selfAdjoint.val_one]
  apply cfc_le_one (f := fun x ↦ if 0 ≤ x then 1 else 0)
  intros; split <;> norm_num

theorem proj_le_mul_nonneg : 0 ≤ {A ≤ₚ B}.toMat * (B - A).toMat := by
  rw [proj_le]
  nth_rewrite 2 [← cfc_id (B - A)]
  rw [← coe_cfc_mul]
  apply cfc_nonneg
  aesop

theorem proj_le_mul_le : {A ≤ₚ B}.toMat * A.toMat ≤ {A ≤ₚ B}.toMat * B.toMat := by
  rw [← sub_nonneg, ← mul_sub_left_distrib]
  exact proj_le_mul_nonneg A B

@[simp]
theorem proj_le_add_lt : {A <ₚ B} + {B ≤ₚ A} = 1 := by
  rw [proj_le, proj_lt]
  rw [← neg_sub A B]
  nth_rw 1 [← cfc_id (A - B)]
  rw[← cfc_neg, ← cfc_comp, ← cfc_add]
  convert cfc_const (A - B) 1 with x
  · simp; grind
  · simp

theorem conj_lt_add_conj_le : A.conj {A <ₚ 0} + A.conj {0 ≤ₚ A} = A := by
  rw (occs := [2, 4, 5]) [← cfc_id A]
  rw [proj_lt_zero_cfc, proj_zero_le_cfc, cfc_conj, cfc_conj, ← cfc_add]
  congr; ext
  simp; grind

/-- The positive part of a Hermitian matrix: the projection onto its positive eigenvalues. -/
def proj_pos : HermitianMat n 𝕜 :=
  A.cfc (fun x ↦ x ⊔ 0)

/-- The negative part of a Hermitian matrix: the projection onto its negative eigenvalues. -/
def proj_neg : HermitianMat n 𝕜 :=
  A.cfc (fun x ↦ -x ⊔ 0)

instance : PosPart (HermitianMat n 𝕜) where
  posPart := proj_pos

instance : NegPart (HermitianMat n 𝕜) where
  negPart := proj_neg

theorem posPart_eq_cfc_max : A⁺ = A.cfc (fun x ↦ x ⊔ 0) := by
  rfl

theorem negPart_eq_cfc_min : A⁻ = A.cfc (fun x ↦ -x ⊔ 0) := by
  rfl

theorem posPart_eq_cfc_ite : A⁺ = A.cfc (fun x ↦ if 0 ≤ x then x else 0) := by
  simp only [← max_def', posPart_eq_cfc_max]

theorem negPart_eq_cfc_ite : A⁻ = A.cfc (fun x ↦ if x ≤ 0 then -x else 0) := by
  simp only [negPart_eq_cfc_min, max_def]
  congr; ext
  split <;> split <;> grind

/-- There is an existing (very slow) `PosPart` instance on `Matrix n n 𝕜`, this shows
that this is equal. -/
theorem posPart_eq_posPart_toMat : A⁺ = A.toMat⁺ := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc]
  rfl

/-- There is an existing (very slow) `PosPart` instance on `Matrix n n 𝕜`, this shows
that this is equal. -/
theorem negPart_eq_negPart_toMat : A⁻ = A.toMat⁻ := by
  rw [CFC.negPart_def, cfcₙ_eq_cfc]
  rfl

/-- The positive part can be equivalently described as the nonnegative part. -/
theorem posPart_eq_cfc_lt : A⁺ = A.cfc (fun x ↦ if 0 < x then x else 0) := by
  rw [posPart_eq_cfc_ite]
  congr with x
  rcases lt_trichotomy x 0 <;> grind

/-- The negative part can be equivalently described as the nonpositive part. -/
theorem negPart_eq_cfc_lt : A⁻ = A.cfc (fun x ↦ if x < 0 then -x else 0) := by
  rw [negPart_eq_cfc_ite]
  congr with x
  rcases lt_trichotomy x 0 <;> grind

theorem posPart_add_negPart : A⁺ - A⁻ = A := by
  rw [posPart_eq_cfc_ite, negPart_eq_cfc_lt, ← cfc_sub]
  convert cfc_id A
  ext; dsimp; grind

theorem zero_le_posPart : 0 ≤ A⁺ := by
  rw [posPart_eq_cfc_ite, zero_le_cfc]
  intro; split <;> order

theorem negPart_le_zero : 0 ≤ A⁻ := by
  rw [negPart_eq_cfc_ite, zero_le_cfc]
  intro; split <;> grind

theorem posPart_le : A ≤ A⁺ := by
  nth_rw 1 [← cfc_id A]
  rw [posPart_eq_cfc_ite, ← sub_nonneg, ← cfc_sub, zero_le_cfc]
  intro; simp; split <;> order

theorem posPart_mul_negPart : A⁺.toMat * A⁻.toMat = 0 := by
  rw [posPart_eq_cfc_ite, negPart_eq_cfc_ite, ← coe_cfc_mul]
  convert congrArg toMat (cfc_const A 0)
  · simp; order
  · simp

theorem proj_le_inner_nonneg  : 0 ≤ {A ≤ₚ B}.inner (B - A) :=
  --This inner is equal to `(B - A)⁺.trace`, could be better way to describe it
  HermitianMat.inner_mul_nonneg (proj_le_mul_nonneg A B)

theorem proj_le_inner_le : {A ≤ₚ B}.inner A ≤ {A ≤ₚ B}.inner B := by
  rw [← sub_nonneg, ← HermitianMat.inner_left_sub]
  exact proj_le_inner_nonneg A B

open RealInnerProductSpace in
theorem inner_proj_le_nonneg : 0 ≤ ⟪{A ≤ₚ B}, (B - A)⟫ :=
  proj_le_inner_nonneg A B

open RealInnerProductSpace in
theorem inner_proj_le_le : ⟪{A ≤ₚ B}, A⟫ ≤ ⟪{A ≤ₚ B}, B⟫ :=
  proj_le_inner_le A B

--TODO: When we upgrade `cfc_continuous` from 𝕜 to ℂ, we upgrade these too.
@[fun_prop]
theorem posPart_Continuous : Continuous (·⁺ : HermitianMat n ℂ → _) := by
  simp_rw [posPart_eq_cfc_max]
  fun_prop

@[fun_prop]
theorem negPart_Continuous : Continuous (·⁻ : HermitianMat n ℂ → _) := by
  simp_rw [negPart_eq_cfc_min]
  fun_prop

proof_wanted posPart_le_zero_iff : A⁺ ≤ 0 ↔ A ≤ 0

proof_wanted posPart_eq_zero_iff : A⁺ = 0 ↔ A ≤ 0
/- := by
   rw [← posPart_le_zero_iff]
   have := zero_le_posPart A
   constructor <;> order
-/

--Many missing lemmas: see `Mathlib.Algebra.Order.Group.PosPart` for examples
-- (They don't apply here since it's not a Lattice, and there's no well-defined `max` in
--   the Loewner order.)
-- PosPart is Monotone (so `A ≤ B` implies `A⁺ ≤ B⁺`), as is NegPart
-- PosPart and NegPart commute with nonnegative scalar muliptlication
-- `A⁺ ≤ 0 ↔ A⁺ = 0 ↔ A = 0`
-- `0 ≤ A → A⁺ = A`
-- `0 < A → 0 < A⁺` (this is not the PosDef version, this is `≤ && ≠`)
-- `A.PosDef → A⁺.PosDef`
-- versions of those ^^ for negPart
-- simp: 0⁺ = 0, 0⁻ = 0, 1⁺ = 1, 1⁻ = 0
--   (-A)⁺ = A⁻, (-A)⁻ = A⁺
--  A⁺⁺ = A⁺, A⁺⁻ = 0
