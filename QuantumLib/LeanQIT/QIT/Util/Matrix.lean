/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Init
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Complex.Basic

/-!
# Matrix utilities

Matrix helper definitions for finite-dimensional QIT. The partial trace names
follow the source notation `Tr_A` and `Tr_B`: `partialTraceA` traces out the
`A` system and leaves the `B` system, while `partialTraceB` traces out `B` and
leaves `A` [Wilde2011Qst, qit-notes.tex:7690-7706].

The partial transpose names follow the same subsystem convention on product
indices: `partialTransposeA` transposes only the `A` indices and
`partialTransposeB` transposes only the `B` indices, matching the product-basis
PPT convention [Horodecki2007Entanglement, ent-review-last.tex:2234-2290].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

/-- Complex square matrices over a finite system label type. -/
abbrev CMatrix (a : Type u) :=
  Matrix a a Complex

/-- Scalar multiplication as an explicit matrix-valued function. -/
def matrixScale {a : Type u} (c : Complex) (M : CMatrix a) : CMatrix a :=
  fun i j => c * M i j

variable {a : Type u} {b : Type v}

/-- `Tr_A`: trace out the first system of a bipartite matrix. -/
def partialTraceA [Fintype a] (X : CMatrix (Prod a b)) : CMatrix b :=
  fun j j' => Finset.univ.sum fun i : a => X (i, j) (i, j')

/-- `Tr_B`: trace out the second system of a bipartite matrix. -/
def partialTraceB [Fintype b] (X : CMatrix (Prod a b)) : CMatrix a :=
  fun i i' => Finset.univ.sum fun j : b => X (i, j) (i', j)

/-- Partial transpose on the first subsystem of a bipartite matrix. -/
def partialTransposeA (X : CMatrix (Prod a b)) : CMatrix (Prod a b) :=
  fun x y => X (y.1, x.2) (x.1, y.2)

/-- Partial transpose on the second subsystem of a bipartite matrix. -/
def partialTransposeB (X : CMatrix (Prod a b)) : CMatrix (Prod a b) :=
  fun x y => X (x.1, y.2) (y.1, x.2)

@[simp]
theorem partialTransposeA_apply (X : CMatrix (Prod a b)) (i i' : a) (j j' : b) :
    partialTransposeA X (i, j) (i', j') = X (i', j) (i, j') :=
  rfl

@[simp]
theorem partialTransposeB_apply (X : CMatrix (Prod a b)) (i i' : a) (j j' : b) :
    partialTransposeB X (i, j) (i', j') = X (i, j') (i', j) :=
  rfl

/-- `Tr_A` is additive. -/
theorem partialTraceA_add [Fintype a] (X Y : CMatrix (Prod a b)) :
    partialTraceA (X + Y) = partialTraceA X + partialTraceA Y := by
  ext j j'; simp [partialTraceA, Finset.sum_add_distrib]

/-- `Tr_A` commutes with scalar multiplication. -/
theorem partialTraceA_smul [Fintype a] (c : ℂ) (X : CMatrix (Prod a b)) :
    partialTraceA (c • X) = c • partialTraceA X := by
  ext j j'
  simp only [partialTraceA, Matrix.smul_apply, smul_eq_mul]
  exact (Finset.mul_sum _ _ _).symm

/-- `Tr_B` is additive. -/
theorem partialTraceB_add [Fintype b] (X Y : CMatrix (Prod a b)) :
    partialTraceB (X + Y) = partialTraceB X + partialTraceB Y := by
  ext i i'; simp [partialTraceB, Finset.sum_add_distrib]

/-- `Tr_B` commutes with scalar multiplication. -/
theorem partialTraceB_smul [Fintype b] (c : ℂ) (X : CMatrix (Prod a b)) :
    partialTraceB (c • X) = c • partialTraceB X := by
  ext i i'
  simp only [partialTraceB, Matrix.smul_apply, smul_eq_mul]
  exact (Finset.mul_sum _ _ _).symm

/-- `Tr_A` commutes with subtraction. -/
theorem partialTraceA_sub [Fintype a] (X Y : CMatrix (Prod a b)) :
    partialTraceA (X - Y) = partialTraceA X - partialTraceA Y := by
  ext j j'
  simp [partialTraceA, Finset.sum_sub_distrib]

/-- `Tr_B` commutes with subtraction. -/
theorem partialTraceB_sub [Fintype b] (X Y : CMatrix (Prod a b)) :
    partialTraceB (X - Y) = partialTraceB X - partialTraceB Y := by
  ext i i'
  simp [partialTraceB, Finset.sum_sub_distrib]

/-- Nonnegative real scalar multiplication preserves the Loewner order on
complex matrices (real `SMul ℝ` action form). -/
theorem cMatrix_real_smul_le_smul {a : Type u} [Fintype a] [DecidableEq a]
    {A B : CMatrix a} {t : ℝ} (ht : 0 ≤ t) (hAB : A ≤ B) :
    (t • A) ≤ (t • B) := by
  rw [Matrix.le_iff] at hAB ⊢
  have hdiff : (t • B - t • A : CMatrix a) = t • (B - A) := by
    ext i j
    simp [sub_eq_add_neg, Complex.real_smul]
  rw [hdiff]
  exact hAB.smul ht

/-- Nonnegative real scalar multiplication preserves the Loewner order on
complex matrices (complex-coercion form, with the scalar cast to `ℂ`). -/
theorem cMatrix_ofReal_smul_le_smul {a : Type u} [Fintype a] [DecidableEq a]
    {A B : CMatrix a} {c : ℝ} (hc : 0 ≤ c) (hAB : A ≤ B) :
    ((c : ℂ) • A) ≤ ((c : ℂ) • B) := by
  rw [Matrix.le_iff] at hAB ⊢
  simpa [sub_eq_add_neg, smul_add, smul_neg] using hAB.smul hc

/-- Taking `Tr_A` preserves the full matrix trace. -/
theorem partialTraceA_trace [Fintype a] [Fintype b] (X : CMatrix (Prod a b)) :
    (partialTraceA (a := a) (b := b) X).trace = X.trace := by
  rw [Matrix.trace, Matrix.trace]
  simp [partialTraceA, Matrix.diag]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- Multiplication by a right Kronecker factor commutes with tracing out the
left subsystem. -/
theorem partialTraceA_mul_kronecker_one_right [Fintype a] [Fintype b] [DecidableEq a]
    (X : CMatrix (Prod a b)) (U : CMatrix b) :
    partialTraceA (a := a) (b := b) (X * Matrix.kronecker (1 : CMatrix a) U) =
      partialTraceA (a := a) (b := b) X * U := by
  ext j j'
  simp [partialTraceA, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Trace pairing against `I_A ⊗ U` can be computed after tracing out `A`. -/
theorem partialTraceA_mul_trace_eq_trace_mul_kronecker_one_right
    [Fintype a] [Fintype b] [DecidableEq a]
    (X : CMatrix (Prod a b)) (U : CMatrix b) :
    ((partialTraceA (a := a) (b := b) X) * U).trace =
      (X * Matrix.kronecker (1 : CMatrix a) U).trace := by
  rw [← partialTraceA_mul_kronecker_one_right X U]
  exact partialTraceA_trace (a := a) (b := b)
    (X * Matrix.kronecker (1 : CMatrix a) U)

/-- Trace pairing against a left identity Kronecker factor reduces to the
partial trace over the left subsystem. -/
theorem trace_kronecker_one_mul_eq_trace_mul_partialTraceA
    [Fintype a] [Fintype b] [DecidableEq a]
    (M : CMatrix (Prod a b)) (T : CMatrix b) :
    (Matrix.kronecker (1 : CMatrix a) T * M).trace =
      (T * partialTraceA (a := a) (b := b) M).trace := by
  calc
    (Matrix.kronecker (1 : CMatrix a) T * M).trace =
        (M * Matrix.kronecker (1 : CMatrix a) T).trace := by
      rw [Matrix.trace_mul_comm]
    _ = ((partialTraceA (a := a) (b := b) M) * T).trace := by
      exact (partialTraceA_mul_trace_eq_trace_mul_kronecker_one_right
        (a := a) (b := b) M T).symm
    _ = (T * partialTraceA (a := a) (b := b) M).trace := by
      rw [Matrix.trace_mul_comm]

/-- Taking `Tr_B` preserves the full matrix trace. -/
theorem partialTraceB_trace [Fintype a] [Fintype b] (X : CMatrix (Prod a b)) :
    (partialTraceB (a := a) (b := b) X).trace = X.trace := by
  rw [Matrix.trace, Matrix.trace]
  simp [partialTraceB, Matrix.diag]
  rw [Fintype.sum_prod_type]

/-- Partial transpose on the first subsystem is involutive. -/
@[simp]
theorem partialTransposeA_involutive (X : CMatrix (Prod a b)) :
    partialTransposeA (partialTransposeA X) = X := by
  ext x y
  cases x
  cases y
  rfl

/-- Partial transpose on the second subsystem is involutive. -/
@[simp]
theorem partialTransposeB_involutive (X : CMatrix (Prod a b)) :
    partialTransposeB (partialTransposeB X) = X := by
  ext x y
  cases x
  cases y
  rfl

/-- Partial transpose on the first subsystem preserves the full matrix trace. -/
theorem partialTransposeA_trace [Fintype a] [Fintype b] (X : CMatrix (Prod a b)) :
    (partialTransposeA X).trace = X.trace := by
  rw [Matrix.trace, Matrix.trace]
  rfl

/-- Partial transpose on the second subsystem preserves the full matrix trace. -/
theorem partialTransposeB_trace [Fintype a] [Fintype b] (X : CMatrix (Prod a b)) :
    (partialTransposeB X).trace = X.trace := by
  rw [Matrix.trace, Matrix.trace]
  rfl

/-- Conjugate transpose commutes with partial transpose on the first subsystem. -/
theorem partialTransposeA_conjTranspose (X : CMatrix (Prod a b)) :
    Matrix.conjTranspose (partialTransposeA X) =
      partialTransposeA (Matrix.conjTranspose X) := by
  ext x y
  cases x
  cases y
  rfl

/-- Conjugate transpose commutes with partial transpose on the second subsystem. -/
theorem partialTransposeB_conjTranspose (X : CMatrix (Prod a b)) :
    Matrix.conjTranspose (partialTransposeB X) =
      partialTransposeB (Matrix.conjTranspose X) := by
  ext x y
  cases x
  cases y
  rfl

/-- Partial transpose on the first subsystem preserves Hermitian matrices. -/
theorem partialTransposeA_isHermitian {X : CMatrix (Prod a b)} (hX : X.IsHermitian) :
    (partialTransposeA X).IsHermitian := by
  rw [Matrix.IsHermitian, partialTransposeA_conjTranspose, hX]

/-- Partial transpose on the second subsystem preserves Hermitian matrices. -/
theorem partialTransposeB_isHermitian {X : CMatrix (Prod a b)} (hX : X.IsHermitian) :
    (partialTransposeB X).IsHermitian := by
  rw [Matrix.IsHermitian, partialTransposeB_conjTranspose, hX]

/-- Conjugate transpose commutes with partial trace on the first subsystem. -/
theorem partialTraceA_conjTranspose [Fintype a] (X : CMatrix (Prod a b)) :
    Matrix.conjTranspose (partialTraceA X) = partialTraceA (Matrix.conjTranspose X) := by
  ext j j'
  simp only [partialTraceA, Matrix.conjTranspose_apply, star_sum]

/-- Partial trace on the first subsystem preserves Hermitian matrices. -/
theorem partialTraceA_isHermitian [Fintype a] {X : CMatrix (Prod a b)}
    (hX : X.IsHermitian) : (partialTraceA X).IsHermitian := by
  rw [Matrix.IsHermitian, partialTraceA_conjTranspose, hX]

/-- Conjugate transpose commutes with partial trace on the second subsystem. -/
theorem partialTraceB_conjTranspose [Fintype b] (X : CMatrix (Prod a b)) :
    Matrix.conjTranspose (partialTraceB X) = partialTraceB (Matrix.conjTranspose X) := by
  ext i i'
  simp only [partialTraceB, Matrix.conjTranspose_apply, star_sum]

/-- Partial trace on the second subsystem preserves Hermitian matrices. -/
theorem partialTraceB_isHermitian [Fintype b] {X : CMatrix (Prod a b)}
    (hX : X.IsHermitian) : (partialTraceB X).IsHermitian := by
  rw [Matrix.IsHermitian, partialTraceB_conjTranspose, hX]

/-- Partial trace on the first subsystem preserves positive semidefiniteness. -/
theorem partialTraceA_posSemidef [Fintype a] [Fintype b]
    {M : CMatrix (Prod a b)} (hM : M.PosSemidef) :
    (partialTraceA M).PosSemidef := by
  let block : a → CMatrix b := fun i => M.submatrix (fun j : b => (i, j)) (fun j : b => (i, j))
  have hsum : (∑ i : a, block i).PosSemidef := by
    classical
    refine Finset.induction_on (s := Finset.univ) ?_ ?_
    · simpa using (Matrix.PosSemidef.zero : (0 : CMatrix b).PosSemidef)
    · intro i s his hs
      simpa [Finset.sum_insert his, block] using
        (hM.submatrix (fun j : b => (i, j))).add hs
  convert hsum using 1
  ext j j'
  simp [partialTraceA, block, Matrix.sum_apply]

/-- Reindex a triple finite sum over `a × b × b` to move the `a`-sum outermost. -/
theorem finset_sum_b_b_a_reorder {a : Type u} {b : Type v} [Fintype a] [Fintype b]
    {R : Type*} [AddCommMonoid R] (F : a → b → b → R) :
    (∑ j : b, ∑ k : b, ∑ i : a, F i j k) =
      ∑ i : a, ∑ j : b, ∑ k : b, F i j k := by
  calc
    (∑ j : b, ∑ k : b, ∑ i : a, F i j k) =
        ∑ k : b, ∑ j : b, ∑ i : a, F i j k := by
      rw [Finset.sum_comm]
    _ = ∑ k : b, ∑ i : a, ∑ j : b, F i j k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = ∑ i : a, ∑ k : b, ∑ j : b, F i j k := by
      rw [Finset.sum_comm]
    _ = ∑ i : a, ∑ j : b, ∑ k : b, F i j k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]

/-- The quadratic form of a first-subsystem partial trace expands as the sum of
the slice quadratic forms. -/
theorem partialTraceA_quadratic_eq_sum_slice {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b]
    (M : CMatrix (Prod a b)) (y : b → ℂ) :
    let z : a → Prod a b → ℂ := fun i p => if p.1 = i then y p.2 else 0
    star y ⬝ᵥ (partialTraceA (a := a) (b := b) M).mulVec y =
      ∑ i, star (z i) ⬝ᵥ M.mulVec (z i) := by
  intro z
  simp [z, partialTraceA, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul, apply_ite]
  rw [finset_sum_b_b_a_reorder (a := a) (b := b)
    (F := fun i j k => starRingEnd ℂ (y j) * (M (i, j) (i, k) * y k))]

/-- The partial trace over a nonempty first subsystem of a positive definite
matrix is positive definite. -/
theorem partialTraceA_posDef_of_posDef {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [Nonempty a]
    {M : CMatrix (Prod a b)} (hM : M.PosDef) :
    (partialTraceA (a := a) (b := b) M).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (partialTraceA_posSemidef (a := a) (b := b) hM.posSemidef).1 ?_
  intro y hy
  let z : a → Prod a b → ℂ := fun i p => if p.1 = i then y p.2 else 0
  have hz (i : a) : z i ≠ 0 := by
    intro hzi
    apply hy
    funext j
    have h := congr_fun hzi (i, j)
    simpa [z] using h
  have hnonneg : ∀ i : a, 0 ≤ star (z i) ⬝ᵥ M.mulVec (z i) := by
    intro i
    exact hM.posSemidef.dotProduct_mulVec_nonneg (z i)
  have hpos :
      0 < star (z (Classical.choice inferInstance)) ⬝ᵥ
        M.mulVec (z (Classical.choice inferInstance)) :=
    hM.dotProduct_mulVec_pos (hz (Classical.choice inferInstance))
  rw [partialTraceA_quadratic_eq_sum_slice (M := M) (y := y)]
  exact Finset.sum_pos' (fun i _ => hnonneg i)
    ⟨Classical.choice inferInstance, Finset.mem_univ _, hpos⟩

/-- Partial trace on the second subsystem preserves positive semidefiniteness. -/
theorem partialTraceB_posSemidef [Fintype a] [Fintype b]
    {M : CMatrix (Prod a b)} (hM : M.PosSemidef) :
    (partialTraceB M).PosSemidef := by
  let block : b → CMatrix a := fun j => M.submatrix (fun i : a => (i, j)) (fun i : a => (i, j))
  have hsum : (∑ j : b, block j).PosSemidef := by
    classical
    refine Finset.induction_on (s := Finset.univ) ?_ ?_
    · simpa using (Matrix.PosSemidef.zero : (0 : CMatrix a).PosSemidef)
    · intro j s hjs hs
      simpa [Finset.sum_insert hjs, block] using
        (hM.submatrix (fun i : a => (i, j))).add hs
  convert hsum using 1
  ext i i'
  simp [partialTraceB, block, Matrix.sum_apply]

/-- `matrixScale 1` is the identity. -/
theorem matrixScale_one (M : CMatrix a) : matrixScale 1 M = M := by
  ext i j'; simp [matrixScale]

/-- The classical projector |x><x| = Matrix.single x x 1 is positive semidefinite. -/
theorem posSemidef_single [Fintype a] [DecidableEq a] (x : a) :
    Matrix.PosSemidef (Matrix.single x x (1 : ℂ)) := by
  rw [← Matrix.diagonal_single x (1 : ℂ)]
  exact Matrix.PosSemidef.diagonal fun y => by
    by_cases h : y = x <;> simp [Pi.single_apply, h]

/-- Taking `Tr_A` of a Kronecker product leaves the second factor scaled by
the trace of the first factor [Wilde2011Qst, qit-notes.tex:7754-7762]. -/
theorem partialTraceA_kronecker [Fintype a] (M : CMatrix a) (N : CMatrix b) :
    partialTraceA (a := a) (b := b) (Matrix.kronecker M N) = matrixScale M.trace N := by
  ext j j'
  simp [partialTraceA, matrixScale, Matrix.trace, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Finset.sum_mul]

/-- Taking `Tr_B` of a Kronecker product leaves the first factor scaled by the
trace of the second factor [Wilde2011Qst, qit-notes.tex:7754-7762]. -/
theorem partialTraceB_kronecker [Fintype b] (M : CMatrix a) (N : CMatrix b) :
    partialTraceB (a := a) (b := b) (Matrix.kronecker M N) = matrixScale N.trace M := by
  ext i i'
  change (Finset.univ.sum fun j : b => M i i' * N j j) =
    (Finset.univ.sum fun j : b => N j j) * M i i'
  calc
    (Finset.univ.sum fun j : b => M i i' * N j j) =
        M i i' * (Finset.univ.sum fun j : b => N j j) := by
      simpa using (Finset.mul_sum Finset.univ (fun j : b => N j j) (M i i')).symm
    _ = (Finset.univ.sum fun j : b => N j j) * M i i' := by
      rw [mul_comm]

/-- Partial transpose on the first subsystem transposes the first Kronecker factor. -/
theorem partialTransposeA_kronecker (M : CMatrix a) (N : CMatrix b) :
    partialTransposeA (a := a) (b := b) (Matrix.kronecker M N) =
      Matrix.kronecker (Matrix.transpose M) N := by
  ext x y
  cases x
  cases y
  rfl

/-- Partial transpose on the second subsystem transposes the second Kronecker factor. -/
theorem partialTransposeB_kronecker (M : CMatrix a) (N : CMatrix b) :
    partialTransposeB (a := a) (b := b) (Matrix.kronecker M N) =
      Matrix.kronecker M (Matrix.transpose N) := by
  ext x y
  cases x
  cases y
  rfl

/-- A matrix unit on a product index is a Kronecker product of matrix units. -/
theorem single_prod_eq_kronecker_single [DecidableEq a] [DecidableEq b]
    (i i' : a) (j j' : b) :
    Matrix.single (i, j) (i', j') (1 : Complex) =
      Matrix.kronecker (Matrix.single i i' (1 : Complex))
        (Matrix.single j j' (1 : Complex)) := by
  ext x y
  cases x with
  | mk x1 x2 =>
    cases y with
    | mk y1 y2 =>
      by_cases hi : i = x1 <;> by_cases hj : j = x2 <;>
        by_cases hi' : i' = y1 <;> by_cases hj' : j' = y2 <;>
        simp [Matrix.single, Matrix.kronecker, Matrix.kroneckerMap_apply,
          Prod.ext_iff, hi, hj, hi', hj']

/-- Trace of a diagonal matrix unit. -/
theorem trace_single_one [Fintype a] [DecidableEq a] (i i' : a) :
    (Matrix.single i i' (1 : Complex)).trace = if i = i' then 1 else 0 := by
  by_cases h : i = i'
  · subst h
    simp [Matrix.trace, Matrix.single]
  · have hzero : forall x : a, Matrix.single i i' (1 : Complex) x x = 0 := by
      intro x
      by_cases hx : i = x
      · subst hx
        have hne : i' ≠ i := by
          intro h'
          exact h h'.symm
        simp [Matrix.single, hne]
      · simp [Matrix.single, hx]
    rw [Matrix.trace]
    simp [h]

/-- Delta collapse for the trace of product-index matrix units. -/
theorem sum_delta_trace [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) :
    (∑ ab : Prod a b, ∑ ab' : Prod a b,
      X ab ab' * ((if ab.1 = ab'.1 then (1 : Complex) else 0) *
        (if ab.2 = ab'.2 then (1 : Complex) else 0))) = X.trace := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl ?_
  intro ab _
  calc
    (∑ ab' : Prod a b,
      X ab ab' * ((if ab.1 = ab'.1 then (1 : Complex) else 0) *
        (if ab.2 = ab'.2 then (1 : Complex) else 0))) =
        X ab ab * ((if ab.1 = ab.1 then (1 : Complex) else 0) *
          (if ab.2 = ab.2 then (1 : Complex) else 0)) := by
      refine Finset.sum_eq_single ab ?_ ?_
      · intro ab' _ hne
        by_cases h1 : ab.1 = ab'.1
        · by_cases h2 : ab.2 = ab'.2
          · exact False.elim (hne (Prod.ext h1.symm h2.symm))
          · simp [h1, h2]
        · simp [h1]
      · intro hnot
        simp at hnot
    _ = X ab ab := by
      simp

end

end QIT
