/-
Copyright (c) 2025 Leonardo A Lessa. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Leonardo A Lessa, Alex Meiburg
-/
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
  simp only [cfc, mat_pow, mat_mk]
  rw [← cfc_pow _ 2 (hf := by cfc_cont_tac)]
  simp

theorem proj_lt_sq : {A <ₚ B}^2 = {A <ₚ B} := by
  rw [proj_lt_def]
  --TODO: Should do a `HermitianMat.cfc_pow`.
  ext1
  simp only [cfc, mat_pow, mat_mk]
  rw [← cfc_pow _ 2 (hf := by cfc_cont_tac)]
  simp

theorem proj_zero_le_cfc : {0 ≤ₚ A} = cfc A (fun x ↦ if 0 ≤ x then 1 else 0) := by
  simp only [proj_le, sub_zero]

theorem proj_zero_lt_cfc : {0 <ₚ A} = cfc A (fun x ↦ if 0 < x then 1 else 0) := by
  simp only [proj_lt, sub_zero]

theorem proj_le_zero_cfc : {A ≤ₚ 0} = cfc A (fun x ↦ if x ≤ 0 then 1 else 0) := by
  simp only [proj_le, zero_sub]
  --TODO: Should do a `HermitianMat.cfc_comp_neg`?
  nth_rw 1 [← cfc_id A]
  rw [← cfc_neg, ← cfc_comp]
  congr! 2 with x
  simp

theorem proj_lt_zero_cfc : {A <ₚ 0} = cfc A (fun x ↦ if x < 0 then 1 else 0) := by
  simp only [proj_lt, zero_sub]
  --TODO: Should do a `HermitianMat.cfc_comp_neg`?
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
  --The whole `rw` line is a defeq, i.e. `change _root_.cfc _ (B - A).mat ≤ 1` works too.
  --TODO better API.
  open MatrixOrder in
  rw [← Subtype.coe_le_coe, val_eq_coe, selfAdjoint.val_one]
  apply cfc_le_one (f := fun x ↦ if 0 ≤ x then 1 else 0)
  intros; split <;> norm_num

open MatrixOrder in
theorem proj_le_mul_nonneg : 0 ≤ {A ≤ₚ B}.mat * (B - A).mat := by
  rw [proj_le]
  nth_rewrite 2 [← cfc_id (B - A)]
  rw [← mat_cfc_mul]
  apply cfc_nonneg
  aesop

open MatrixOrder in
theorem proj_le_mul_le : {A ≤ₚ B}.mat * A.mat ≤ {A ≤ₚ B}.mat * B.mat := by
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
theorem posPart_eq_posPart_toMat : A⁺ = A.mat⁺ := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc]
  rfl

/-- There is an existing (very slow) `PosPart` instance on `Matrix n n 𝕜`, this shows
that this is equal. -/
theorem negPart_eq_negPart_toMat : A⁻ = A.mat⁻ := by
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

theorem posPart_mul_negPart : A⁺.mat * A⁻.mat = 0 := by
  rw [posPart_eq_cfc_ite, negPart_eq_cfc_ite, ← mat_cfc_mul]
  convert congrArg mat (cfc_const A 0)
  · grind [Pi.mul_apply, mul_eq_zero]
  · simp

open RealInnerProductSpace

theorem proj_le_inner_nonneg  : 0 ≤ ⟪{A ≤ₚ B}, (B - A)⟫ :=
  --This inner is equal to `(B - A)⁺.trace`, could be better way to describe it
  inner_mul_nonneg (proj_le_mul_nonneg A B)

theorem proj_le_inner_le : ⟪{A ≤ₚ B}, A⟫ ≤ ⟪{A ≤ₚ B}, B⟫ := by
  rw [← sub_nonneg, ← inner_sub_right]
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

-- variable {d : Type*} [Fintype d] [DecidableEq d] (A B : HermitianMat d ℂ)

theorem one_sub_proj_le : 1 - {B ≤ₚ A} = {A <ₚ B} := by
  rw [sub_eq_iff_eq_add, proj_le_add_lt]

open MatrixOrder ComplexOrder

theorem proj_lt_mul_nonneg : 0 ≤ {A <ₚ B}.mat * (B - A).mat := by
  rw [proj_lt]
  nth_rewrite 2 [← cfc_id (B - A)]
  rw [← mat_cfc_mul]
  apply cfc_nonneg
  intros
  simp only [Pi.mul_apply, id_eq, ite_mul, one_mul, zero_mul]
  split <;> order

theorem proj_lt_mul_lt : {A <ₚ B}.mat * A.mat ≤ {A <ₚ B}.mat * B.mat := by
  rw [← sub_nonneg, ← mul_sub_left_distrib]
  exact A.proj_lt_mul_nonneg B

theorem inner_negPart_nonpos : ⟪A, A⁻⟫ ≤ 0 := by
  rw [← neg_le_neg_iff, neg_zero, ← inner_neg_right]
  apply inner_mul_nonneg
  nth_rw 1 [← A.cfc_id]
  rw [negPart_eq_cfc_ite]
  rw [← cfc_neg]
  rw [← mat_cfc_mul]
  change 0 ≤ A.cfc _
  rw [zero_le_cfc]
  intro i
  dsimp
  split_ifs with h
  · rw [neg_neg]
    exact mul_self_nonneg _
  · simp

@[simp]
theorem posPart_inner_negPart_zero : ⟪A⁺, A⁻⟫ = 0 := by
  have hi := inner_eq_trace_rc A⁺ A⁻
  rw [posPart_mul_negPart, Matrix.trace_zero] at hi
  simpa only [map_eq_zero] using hi

theorem inner_negPart_zero_iff : ⟪A, A⁻⟫ = 0 ↔ 0 ≤ A := by
  constructor
  · intro h
    nth_rw 1 [← posPart_add_negPart A] at h
    rw [inner_sub_left, sub_eq_zero, posPart_inner_negPart_zero, eq_comm, inner_self_eq_zero] at h
    rw [← zero_smul ℝ 1, ← cfc_const A, negPart_eq_cfc_ite] at h --TODO cfc_zero
    rw [cfc_eq_cfc_iff_eqOn, A.H.spectrum_real_eq_range_eigenvalues] at h
    simp only [Set.eqOn_range] at h
    replace h (i) := congrFun h i
    simp only [Function.comp_apply, ite_eq_right_iff, neg_eq_zero] at h
    rw [zero_le_iff, A.H.posSemidef_iff_eigenvalues_nonneg]
    intro i
    contrapose! h
    use i, h.le, h.ne
  · intro h
    apply le_antisymm
    · exact inner_negPart_nonpos A
    · exact inner_ge_zero h (negPart_le_zero A)

theorem inner_negPart_neg_iff : ⟪A, A⁻⟫ < 0 ↔ ¬0 ≤ A := by
  simp [← inner_negPart_zero_iff, lt_iff_le_and_ne, inner_negPart_nonpos A]

/-- The self-duality of the PSD cone: a matrix is PSD iff its inner product with all
nonnegative matrices is non-negative. -/
theorem zero_le_iff_inner_pos (A : HermitianMat n 𝕜) :
    0 ≤ A ↔ ∀ B, 0 ≤ B → 0 ≤ ⟪A, B⟫ := by
  use fun h _ ↦ inner_ge_zero h
  intro h
  contrapose! h
  classical
  use A⁻, negPart_le_zero A
  rwa [inner_negPart_neg_iff]
