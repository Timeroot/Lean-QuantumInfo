/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Security.Extractor

/-!
# Collision averaging for two-universal extractors

Finite algebraic lemmas for the two-universal hashing step of the
randomness-extraction proof route.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT.Security

universe uF uZ uS ue

noncomputable section

variable {F : Type uF} {Z : Type uZ} {S : Type uS} {e : Type ue}
variable [Fintype F] [DecidableEq F]
variable [Fintype Z] [DecidableEq Z]
variable [Fintype S] [DecidableEq S]
variable [Fintype e] [DecidableEq e]

namespace HashFamily

variable (H : HashFamily F Z S)

/-- Weighted probability that two inputs collide under a sampled hash seed. -/
def collisionProbability (z z' : Z) : ℝ≥0 :=
  ∑ s, H.collisionWeight z z' s

omit [DecidableEq F] [Fintype Z] [DecidableEq Z] in
@[simp]
theorem collisionProbability_eq_sum (z z' : Z) :
    H.collisionProbability z z' = ∑ s, H.collisionWeight z z' s :=
  rfl

omit [DecidableEq F] [Fintype Z] [DecidableEq Z] in
/-- A seed always collides an input with itself. -/
theorem collisionProbability_self (z : Z) :
    H.collisionProbability z z = 1 := by
  unfold collisionProbability collisionWeight
  rw [Finset.sum_comm]
  calc
    (∑ f : F, ∑ s : S,
        if H.hash f z = s ∧ H.hash f z = s then H.prob f else 0) =
        ∑ f : F, H.prob f := by
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Finset.sum_eq_single_of_mem (H.hash f z) (Finset.mem_univ _)]
      · simp
      · intro s _ hs
        have hne : H.hash f z ≠ s := fun h => hs h.symm
        simp [hne]
    _ = 1 := H.prob_sum

omit [DecidableEq F] [Fintype Z] [DecidableEq Z] in
/-- The two-universal predicate bounds off-diagonal collision probability. -/
theorem collisionProbability_le_of_twoUniversal (hH : H.TwoUniversal)
    {z z' : Z} (hzz : z ≠ z') :
    H.collisionProbability z z' ≤ (Fintype.card S : ℝ≥0)⁻¹ :=
  hH z z' hzz

omit [DecidableEq F] [Fintype Z] [DecidableEq Z] in
/--
Collision probability as Tomamichel's seed average of the equality indicator
`δ_{f(z),f(z')}`.

[Tomamichel2015FiniteResources, apps.tex:312-315]
-/
theorem collisionProbability_eq_sum_hash_eq (z z' : Z) :
    H.collisionProbability z z' =
      ∑ f : F, (if H.hash f z = H.hash f z' then H.prob f else 0 : ℝ≥0) := by
  classical
  unfold collisionProbability collisionWeight
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases h : H.hash f z = H.hash f z'
  · rw [Finset.sum_eq_single_of_mem (H.hash f z) (Finset.mem_univ _)]
    · simp [h]
    · intro s _ hs
      have hne : H.hash f z ≠ s := fun hz => hs hz.symm
      simp [hne]
  · rw [Finset.sum_eq_single_of_mem (H.hash f z) (Finset.mem_univ _)]
    · have hsym : H.hash f z' ≠ H.hash f z := fun h' => h h'.symm
      simp [h, hsym]
    · intro s _ hs
      have hne : H.hash f z ≠ s := fun hz => hs hz.symm
      simp [hne]

/--
Source-shaped collision uniformity for weighted hash families.

Tomamichel's direct leftover-hash setup uses the exact off-diagonal
collision probability `1 / |S|`.  The existing `TwoUniversal` predicate keeps
the weaker `≤` form; this predicate records the equality form needed for the
centered quadratic cancellation in the direct proof route.
-/
def CollisionUniform : Prop :=
  ∀ z z' : Z, z ≠ z' ->
    H.collisionProbability z z' = (Fintype.card S : ℝ≥0)⁻¹

omit [DecidableEq F] [Fintype Z] [DecidableEq Z] in
/-- Collision-uniform hash families are two-universal. -/
theorem CollisionUniform.toTwoUniversal (hH : H.CollisionUniform) :
    H.TwoUniversal := by
  intro z z' hzz
  simpa [collisionProbability] using le_of_eq (hH z z' hzz)

omit [DecidableEq F] in
/--
Pair-sum collision averaging for a nonnegative kernel.

This is the finite algebraic core consumed by the extractor proof: diagonal
terms collide with probability one, and off-diagonal terms are bounded by the
two-universal collision probability.
-/
theorem twoUniversal_pairCollisionAverage_le (hH : H.TwoUniversal)
    (K : Z -> Z -> ℝ≥0) :
    (∑ z : Z, ∑ z' : Z, K z z' * H.collisionProbability z z') ≤
      ∑ z : Z, ∑ z' : Z,
        if z = z' then K z z' else K z z' * (Fintype.card S : ℝ≥0)⁻¹ := by
  refine Finset.sum_le_sum fun z _ => ?_
  refine Finset.sum_le_sum fun z' _ => ?_
  by_cases hzz : z = z'
  · subst z'
    rw [collisionProbability_self]
    simp
  · rw [if_neg hzz]
    exact mul_le_mul_right (collisionProbability_le_of_twoUniversal H hH hzz) (K z z')

end HashFamily

section FullFunctionHashFamily

variable {Z : Type uZ} {S : Type uS}
variable [Fintype Z] [DecidableEq Z]
variable [Fintype S] [DecidableEq S] [Nonempty S]

private def fullFunctionCollisionEquiv (z z' : Z) (hzz : z ≠ z') :
    {f : Z -> S // f z = f z'} ≃ ({x : Z // x ≠ z'} -> S) where
  toFun f := fun x => f.1 x.1
  invFun g :=
    ⟨fun x => if hx : x = z' then g ⟨z, hzz⟩ else g ⟨x, hx⟩, by
      simp [hzz]⟩
  left_inv f := by
    ext x
    by_cases hx : x = z'
    · subst x
      simp [f.2]
    · simp [hx]
  right_inv g := by
    ext x
    simp [x.2]

omit [Nonempty S] in
private theorem fullFunctionCollisionSubtype_card (z z' : Z) (hzz : z ≠ z') :
    Fintype.card {f : Z -> S // f z = f z'} =
      Fintype.card S ^ (Fintype.card Z - 1) := by
  classical
  calc
    Fintype.card {f : Z -> S // f z = f z'} =
        Fintype.card ({x : Z // x ≠ z'} -> S) := by
          exact Fintype.card_congr (fullFunctionCollisionEquiv (S := S) z z' hzz)
    _ = Fintype.card S ^ Fintype.card {x : Z // x ≠ z'} := by
          rw [Fintype.card_fun]
    _ = Fintype.card S ^ (Fintype.card Z - 1) := by
          congr 1
          simp

omit [DecidableEq S] in
private theorem fullFunctionCollisionRatio (z : Z) :
    ((Fintype.card S ^ (Fintype.card Z - 1) : Nat) : ℝ≥0) *
        ((Fintype.card (Z -> S) : Nat) : ℝ≥0)⁻¹ =
      (Fintype.card S : ℝ≥0)⁻¹ := by
  classical
  have hcard_fun : Fintype.card (Z -> S) = Fintype.card S ^ Fintype.card Z := by
    rw [Fintype.card_fun]
  have ha : (Fintype.card S : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card S ≠ 0)
  have hn : 0 < Fintype.card Z := by
    exact Fintype.card_pos_iff.mpr ⟨z⟩
  have hpow :
      (Fintype.card S : ℝ≥0) ^ Fintype.card Z =
        (Fintype.card S : ℝ≥0) ^ (Fintype.card Z - 1) *
          (Fintype.card S : ℝ≥0) := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt hn)]
  rw [hcard_fun]
  norm_num [Nat.cast_pow]
  calc
    (Fintype.card S : ℝ≥0) ^ (Fintype.card Z - 1) *
        ((Fintype.card S : ℝ≥0) ^ Fintype.card Z)⁻¹ =
        (Fintype.card S : ℝ≥0) ^ (Fintype.card Z - 1) *
          (((Fintype.card S : ℝ≥0) ^ (Fintype.card Z - 1) *
            (Fintype.card S : ℝ≥0))⁻¹) := by rw [hpow]
    _ = (Fintype.card S : ℝ≥0) ^ (Fintype.card Z - 1) *
          ((Fintype.card S : ℝ≥0)⁻¹ *
            ((Fintype.card S : ℝ≥0) ^ (Fintype.card Z - 1))⁻¹) := by
          rw [mul_inv_rev]
    _ = ((Fintype.card S : ℝ≥0) ^ (Fintype.card Z - 1) *
          ((Fintype.card S : ℝ≥0) ^ (Fintype.card Z - 1))⁻¹) *
          (Fintype.card S : ℝ≥0)⁻¹ := by
          ac_rfl
    _ = (Fintype.card S : ℝ≥0)⁻¹ := by
          rw [mul_inv_cancel₀ (pow_ne_zero _ ha), one_mul]

omit [Nonempty S] in
private theorem fullFunctionCollisionIndicator_sum (z z' : Z) :
    (∑ f : Z -> S,
      (if f z = f z' then (Fintype.card (Z -> S) : ℝ≥0)⁻¹ else 0 : ℝ≥0)) =
      (Fintype.card {f : Z -> S // f z = f z'} : ℝ≥0) *
        (Fintype.card (Z -> S) : ℝ≥0)⁻¹ := by
  classical
  rw [← Finset.sum_filter]
  simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_subtype]

/--
The uniformly seeded full function family has exact off-diagonal collision
probability `1 / |S|`.

[Tomamichel2015FiniteResources, apps.tex:312-315]
-/
theorem fullFunctionHashFamily_collisionProbability (z z' : Z) (hzz : z ≠ z') :
    (FullFunctionHashFamily (Z := Z) (S := S)).collisionProbability z z' =
      (Fintype.card S : ℝ≥0)⁻¹ := by
  rw [HashFamily.collisionProbability_eq_sum_hash_eq]
  simp only [fullFunctionHashFamily_hash, fullFunctionHashFamily_prob]
  rw [fullFunctionCollisionIndicator_sum (S := S) z z']
  rw [fullFunctionCollisionSubtype_card (S := S) z z' hzz]
  exact fullFunctionCollisionRatio (S := S) z

/-- The uniformly seeded full function family is collision-uniform. -/
theorem fullFunctionHashFamily_collisionUniform :
    (FullFunctionHashFamily (Z := Z) (S := S)).CollisionUniform := by
  intro z z' hzz
  exact fullFunctionHashFamily_collisionProbability (S := S) z z' hzz

/-- The uniformly seeded full function family is two-universal. -/
theorem fullFunctionHashFamily_twoUniversal :
    (FullFunctionHashFamily (Z := Z) (S := S)).TwoUniversal :=
  fullFunctionHashFamily_collisionUniform (Z := Z) (S := S) |>.toTwoUniversal

omit [Fintype S] [DecidableEq S] [Nonempty S] in
/-- `Fin ell` specialization of full-function collision uniformity. -/
theorem finFullFunctionHashFamily_collisionUniform
    {Z : Type uZ} [Fintype Z] [DecidableEq Z] {ell : Nat} (hell : 0 < ell) :
    (FinFullFunctionHashFamily (Z := Z) ell hell).CollisionUniform := by
  letI : Nonempty (Fin ell) := ⟨⟨0, hell⟩⟩
  exact fullFunctionHashFamily_collisionUniform (Z := Z) (S := Fin ell)

omit [Fintype S] [DecidableEq S] [Nonempty S] in
/-- `Fin ell` specialization of full-function two-universality. -/
theorem finFullFunctionHashFamily_twoUniversal
    {Z : Type uZ} [Fintype Z] [DecidableEq Z] {ell : Nat} (hell : 0 < ell) :
    (FinFullFunctionHashFamily (Z := Z) ell hell).TwoUniversal :=
  (finFullFunctionHashFamily_collisionUniform (Z := Z) hell).toTwoUniversal

end FullFunctionHashFamily

variable [Nonempty F]
variable (H : HashFamily F Z S)

/-- Per-seed extractor output matrix on `S × E`, without the public seed register. -/
def extractorSeedOutputMatrix (E : Ensemble Z e) (f : F) : CMatrix (S × e) :=
  ∑ z, (E.probs z) •
    Matrix.kronecker
      (Matrix.single (H.hash f z) (H.hash f z) (1 : ℂ))
      (E.states z).matrix

omit [DecidableEq F] [DecidableEq Z] [Fintype S] [Nonempty F] in
@[simp]
theorem extractorSeedOutputMatrix_eq_sum (E : Ensemble Z e) (f : F) :
    extractorSeedOutputMatrix H E f =
      ∑ z, (E.probs z) •
        Matrix.kronecker
          (Matrix.single (H.hash f z) (H.hash f z) (1 : ℂ))
          (E.states z).matrix :=
  rfl

/-- The `f`-seed block of the full extractor output matrix, retaining `S × E`. -/
def extractorOutputSeedBlock (E : Ensemble Z e) (f : F) : CMatrix (S × e) :=
  fun se se' => extractorOutputMatrix H E (se.1, (f, se.2)) (se'.1, (f, se'.2))

omit [DecidableEq Z] [Fintype S] [Nonempty F] in
/-- The seed block of the full `S × (F × E)` output matrix as an explicit finite sum. -/
theorem extractorOutputSeedBlock_eq_sum (E : Ensemble Z e) (f : F) :
    extractorOutputSeedBlock H E f =
      ∑ z, (E.probs z * H.prob f) •
        Matrix.kronecker
          (Matrix.single (H.hash f z) (H.hash f z) (1 : ℂ))
          (E.states z).matrix := by
  ext se se'
  simp only [extractorOutputSeedBlock, extractorOutputMatrix,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_eq_single_of_mem f (Finset.mem_univ _)]
  · simp
  · intro f' _ hf'
    have hsingle : Matrix.single f' f' (1 : ℂ) f f = 0 := by
      rw [Matrix.single_apply]
      simp [hf']
    simp [hsingle]

end

end QIT.Security
