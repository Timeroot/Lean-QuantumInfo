/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Init
public import QuantumInfo.ForMathlib.Matrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Complex.Basic

/-!
# Matrix utilities

Matrix helper definitions for finite-dimensional QIT. Partial traces are
`Matrix.traceLeft` and `Matrix.traceRight`: the source notation `Tr_A` traces
out the `A` system and leaves the `B` system, so it is `Matrix.traceLeft`,
while `Tr_B` traces out `B` and leaves `A`, so it is `Matrix.traceRight`
[Wilde2011Qst, qit-notes.tex:7690-7706].

The partial transpose names follow the same subsystem convention on product
indices: `partialTransposeA` transposes only the `A` indices and
`partialTransposeB` transposes only the `B` indices, matching the product-basis
PPT convention [Horodecki2007Entanglement, ent-review-last.tex:2234-2290].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

namespace QIT

universe u v

noncomputable section

/-- Complex square matrices over a finite system label type. -/
abbrev CMatrix (a : Type u) :=
  Matrix a a ℂ

/-- Scalar multiplication as an explicit matrix-valued function. -/
def matrixScale {a : Type u} (c : ℂ) (M : CMatrix a) : CMatrix a :=
  fun i j => c * M i j

variable {a : Type u} {b : Type v}

/-- Partial transpose on the first subsystem of a bipartite matrix. -/
def partialTransposeA (X : CMatrix (a × b)) : CMatrix (a × b) :=
  fun x y => X (y.1, x.2) (x.1, y.2)

/-- Partial transpose on the second subsystem of a bipartite matrix. -/
def partialTransposeB (X : CMatrix (a × b)) : CMatrix (a × b) :=
  fun x y => X (x.1, y.2) (y.1, x.2)

@[simp]
theorem partialTransposeA_apply (X : CMatrix (a × b)) (i i' : a) (j j' : b) :
    partialTransposeA X (i, j) (i', j') = X (i', j) (i, j') :=
  rfl

@[simp]
theorem partialTransposeB_apply (X : CMatrix (a × b)) (i i' : a) (j j' : b) :
    partialTransposeB X (i, j) (i', j') = X (i, j') (i', j) :=
  rfl

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

/-- The real part of the trace is monotone for the Loewner order. -/
theorem cMatrix_trace_re_le_of_le {ι : Type*} [Fintype ι] {X Y : CMatrix ι}
    (hXY : X ≤ Y) :
    X.trace.re ≤ Y.trace.re := by
  have hnon : 0 ≤ (Y - X).trace.re := (Matrix.PosSemidef.trace_nonneg hXY).1
  have htrace : (Y - X).trace.re = Y.trace.re - X.trace.re := by
    simp [Matrix.trace_sub]
  linarith

/-- Multiplication by a right Kronecker factor commutes with tracing out the
left subsystem. -/
theorem traceLeft_mul_kronecker_one_right [Fintype a] [Fintype b] [DecidableEq a]
    (X : CMatrix (a × b)) (U : CMatrix b) :
    Matrix.traceLeft (X * ((1 : CMatrix a) ⊗ₖ U)) = Matrix.traceLeft X * U := by
  ext j j'
  simp [Matrix.traceLeft, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Multiplication by a right Kronecker factor on the left commutes with tracing
out the left subsystem. -/
theorem traceLeft_kronecker_one_right_mul [Fintype a] [Fintype b] [DecidableEq a]
    (X : CMatrix (a × b)) (V : CMatrix b) :
    Matrix.traceLeft (((1 : CMatrix a) ⊗ₖ V) * X) = V * Matrix.traceLeft X := by
  ext j j'
  simp [Matrix.traceLeft, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Trace pairing against `I_A ⊗ U` can be computed after tracing out `A`. -/
theorem traceLeft_mul_trace_eq_trace_mul_kronecker_one_right
    [Fintype a] [Fintype b] [DecidableEq a]
    (X : CMatrix (a × b)) (U : CMatrix b) :
    (Matrix.traceLeft X * U).trace = (X * ((1 : CMatrix a) ⊗ₖ U)).trace :=
  (Matrix.trace_mul_one_kron_right X U).symm

/-- Trace pairing against a left identity Kronecker factor reduces to the
partial trace over the left subsystem. -/
theorem trace_kronecker_one_mul_eq_trace_mul_traceLeft
    [Fintype a] [Fintype b] [DecidableEq a]
    (M : CMatrix (a × b)) (T : CMatrix b) :
    (((1 : CMatrix a) ⊗ₖ T) * M).trace = (T * Matrix.traceLeft M).trace := by
  calc
    (((1 : CMatrix a) ⊗ₖ T) * M).trace =
        (M * ((1 : CMatrix a) ⊗ₖ T)).trace := by
      rw [Matrix.trace_mul_comm]
    _ = (Matrix.traceLeft M * T).trace := by
      exact (traceLeft_mul_trace_eq_trace_mul_kronecker_one_right M T).symm
    _ = (T * Matrix.traceLeft M).trace := by
      rw [Matrix.trace_mul_comm]

/-- Partial transpose on the first subsystem is involutive. -/
@[simp]
theorem partialTransposeA_involutive (X : CMatrix (a × b)) :
    partialTransposeA (partialTransposeA X) = X := by
  ext x y
  cases x
  cases y
  rfl

/-- Partial transpose on the second subsystem is involutive. -/
@[simp]
theorem partialTransposeB_involutive (X : CMatrix (a × b)) :
    partialTransposeB (partialTransposeB X) = X := by
  ext x y
  cases x
  cases y
  rfl

/-- Partial transpose on the first subsystem preserves the full matrix trace. -/
theorem partialTransposeA_trace [Fintype a] [Fintype b] (X : CMatrix (a × b)) :
    (partialTransposeA X).trace = X.trace := by
  rw [Matrix.trace, Matrix.trace]
  rfl

/-- Partial transpose on the second subsystem preserves the full matrix trace. -/
theorem partialTransposeB_trace [Fintype a] [Fintype b] (X : CMatrix (a × b)) :
    (partialTransposeB X).trace = X.trace := by
  rw [Matrix.trace, Matrix.trace]
  rfl

/-- Conjugate transpose commutes with partial transpose on the first subsystem. -/
theorem partialTransposeA_conjTranspose (X : CMatrix (a × b)) :
    Matrix.conjTranspose (partialTransposeA X) =
      partialTransposeA (Matrix.conjTranspose X) := by
  ext x y
  cases x
  cases y
  rfl

/-- Conjugate transpose commutes with partial transpose on the second subsystem. -/
theorem partialTransposeB_conjTranspose (X : CMatrix (a × b)) :
    Matrix.conjTranspose (partialTransposeB X) =
      partialTransposeB (Matrix.conjTranspose X) := by
  ext x y
  cases x
  cases y
  rfl

/-- Partial transpose on the first subsystem preserves Hermitian matrices. -/
theorem partialTransposeA_isHermitian {X : CMatrix (a × b)} (hX : X.IsHermitian) :
    (partialTransposeA X).IsHermitian := by
  rw [Matrix.IsHermitian, partialTransposeA_conjTranspose, hX]

/-- Partial transpose on the second subsystem preserves Hermitian matrices. -/
theorem partialTransposeB_isHermitian {X : CMatrix (a × b)} (hX : X.IsHermitian) :
    (partialTransposeB X).IsHermitian := by
  rw [Matrix.IsHermitian, partialTransposeB_conjTranspose, hX]

/-- Conjugate transpose commutes with partial trace on the first subsystem. -/
theorem traceLeft_conjTranspose [Fintype a] (X : CMatrix (a × b)) :
    Matrix.conjTranspose (Matrix.traceLeft X) = Matrix.traceLeft (Matrix.conjTranspose X) := by
  ext j j'
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.conjTranspose_apply, star_sum]

/-- Conjugate transpose commutes with partial trace on the second subsystem. -/
theorem traceRight_conjTranspose [Fintype b] (X : CMatrix (a × b)) :
    Matrix.conjTranspose (Matrix.traceRight X) = Matrix.traceRight (Matrix.conjTranspose X) := by
  ext i i'
  simp only [Matrix.traceRight, Matrix.of_apply, Matrix.conjTranspose_apply, star_sum]

/-- Partial trace on the first subsystem preserves positive semidefiniteness. This is
`Matrix.PosSemidef.traceLeft` without its `DecidableEq` hypothesis. -/
theorem traceLeft_posSemidef [Fintype a] [Fintype b]
    {M : CMatrix (a × b)} (hM : M.PosSemidef) :
    (Matrix.traceLeft M).PosSemidef := by
  classical
  exact hM.traceLeft

/-- Partial trace on the first subsystem is monotone for the Loewner order. -/
theorem traceLeft_mono [Fintype a] [Fintype b] {X Y : CMatrix (a × b)} (hXY : X ≤ Y) :
    Matrix.traceLeft X ≤ Matrix.traceLeft Y := by
  rw [Matrix.le_iff] at hXY ⊢
  have hdiff := traceLeft_posSemidef (a := a) (b := b) hXY
  have heq : Matrix.traceLeft (Y - X) = Matrix.traceLeft Y - Matrix.traceLeft X := by
    ext i j
    simp [Matrix.traceLeft, Matrix.sub_apply, Finset.sum_sub_distrib]
  rwa [heq] at hdiff

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

/-- A triple finite sum whose innermost factor is independent of the two outer
indices factors as a product of sums. -/
theorem sum_sum_sum_mul_right {ι κ lam : Type*} [Fintype ι] [Fintype κ] [Fintype lam]
    (f : ι → κ → ℂ) (g : lam → ℂ) :
    (∑ i : ι, ∑ j : κ, ∑ k : lam, f i j * g k) =
      (∑ k : lam, g k) * (∑ i : ι, ∑ j : κ, f i j) := by
  calc
    (∑ i : ι, ∑ j : κ, ∑ k : lam, f i j * g k) =
        ∑ i : ι, ∑ j : κ, f i j * (∑ k : lam, g k) := by
      simp [Finset.mul_sum]
    _ = (∑ i : ι, ∑ j : κ, f i j) * (∑ k : lam, g k) := by
      simp [Finset.sum_mul]
    _ = (∑ k : lam, g k) * (∑ i : ι, ∑ j : κ, f i j) := by
      ring

/-- The quadratic form of a first-subsystem partial trace expands as the sum of
the slice quadratic forms. -/
theorem traceLeft_quadratic_eq_sum_slice {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b]
    (M : CMatrix (a × b)) (y : b → ℂ) :
    let z : a → a × b → ℂ := fun i p => if p.1 = i then y p.2 else 0
    star y ⬝ᵥ (Matrix.traceLeft M).mulVec y =
      ∑ i, star (z i) ⬝ᵥ M.mulVec (z i) := by
  intro z
  simp [z, Matrix.traceLeft, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul, apply_ite]
  rw [finset_sum_b_b_a_reorder (a := a) (b := b)
    (F := fun i j k => starRingEnd ℂ (y j) * (M (i, j) (i, k) * y k))]

/-- The partial trace over a nonempty first subsystem of a positive definite
matrix is positive definite. -/
theorem traceLeft_posDef_of_posDef {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [Nonempty a]
    {M : CMatrix (a × b)} (hM : M.PosDef) :
    (Matrix.traceLeft M).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (traceLeft_posSemidef (a := a) (b := b) hM.posSemidef).1 ?_
  intro y hy
  let z : a → a × b → ℂ := fun i p => if p.1 = i then y p.2 else 0
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
  rw [traceLeft_quadratic_eq_sum_slice (M := M) (y := y)]
  exact Finset.sum_pos' (fun i _ => hnonneg i)
    ⟨Classical.choice inferInstance, Finset.mem_univ _, hpos⟩

/-- Partial trace on the second subsystem preserves positive semidefiniteness. This is
`Matrix.PosSemidef.traceRight` without its `DecidableEq` hypothesis. -/
theorem traceRight_posSemidef [Fintype a] [Fintype b]
    {M : CMatrix (a × b)} (hM : M.PosSemidef) :
    (Matrix.traceRight M).PosSemidef := by
  classical
  exact hM.traceRight

/-- Partial trace on the second subsystem is monotone for the Loewner order. -/
theorem traceRight_mono [Fintype a] [Fintype b] {X Y : CMatrix (a × b)} (hXY : X ≤ Y) :
    Matrix.traceRight X ≤ Matrix.traceRight Y := by
  rw [Matrix.le_iff] at hXY ⊢
  have hdiff := traceRight_posSemidef (a := a) (b := b) hXY
  have heq : Matrix.traceRight (Y - X) = Matrix.traceRight Y - Matrix.traceRight X := by
    ext i j
    simp [Matrix.traceRight, Matrix.sub_apply, Finset.sum_sub_distrib]
  rwa [heq] at hdiff

/-- `matrixScale 1` is the identity. -/
theorem matrixScale_one (M : CMatrix a) : matrixScale 1 M = M := by
  ext i j'
  simp [matrixScale]

/-- A diagonal left factor reduces the trace of a product to a weighted sum of
the right factor's diagonal. -/
theorem trace_diagonal_mul_eq_sum [Fintype a] [DecidableEq a] (d : a → ℂ) (M : CMatrix a) :
    (Matrix.diagonal d * M).trace = ∑ i, d i * M i i := by
  simp [Matrix.trace, Matrix.diagonal_mul]

/-- The classical projector |x><x| = Matrix.single x x 1 is positive semidefinite. -/
theorem posSemidef_single [Fintype a] [DecidableEq a] (x : a) :
    Matrix.PosSemidef (Matrix.single x x (1 : ℂ)) := by
  rw [← Matrix.diagonal_single x (1 : ℂ)]
  exact Matrix.PosSemidef.diagonal fun y => by
    by_cases h : y = x <;> simp [h]

/-- A positive semidefinite matrix with a zero diagonal entry has zero row and
column at that index: the quadratic form `eᵢ† A eᵢ = Aᵢᵢ` vanishes, so `A eᵢ = 0`
by `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`, and Hermiticity transposes
the vanishing column into the row. -/
theorem _root_.Matrix.PosSemidef.zero_diag_zero_row_col [Fintype a] [DecidableEq a]
    {A : CMatrix a} (hA : A.PosSemidef) {i : a} (hii : A i i = 0) (j : a) :
    A i j = 0 ∧ A j i = 0 := by
  set e : a → ℂ := Pi.single i 1 with he
  have hei : e i = (1 : ℂ) := by
    rw [he, Pi.single_apply, if_pos rfl]
  have hek : ∀ k, k ≠ i → e k = 0 := fun k hk => by
    rw [he, Pi.single_apply, if_neg hk]
  have hmulVec : Matrix.mulVec A e = fun k => A k i := by
    ext k
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
    · simp [hei]
    · intro m _ hm
      simp [hek m hm]
    · simp [hei]
  have hform : dotProduct (star e) (Matrix.mulVec A e) = A i i := by
    rw [hmulVec, dotProduct, Finset.sum_eq_single i]
    · simp [hei]
    · intro k _ hk
      simp [hek k hk]
    · simp [hei]
  have hcol : Matrix.mulVec A e = 0 :=
    (hA.dotProduct_mulVec_zero_iff e).mp (by rw [hform, hii])
  have hji : A j i = 0 := by
    have h1 : (fun k => A k i) j = 0 := by
      rw [← hmulVec, hcol]
      simp
    exact h1
  refine ⟨?_, hji⟩
  have hherm : star A = A := hA.isHermitian.eq
  have hij : A i j = star (A j i) := by
    rw [show A i j = star A i j from by rw [hherm], Matrix.star_apply A i j]
  rw [hij, hji, star_zero]

/-- Taking `Tr_A` of a Kronecker product leaves the second factor scaled by
the trace of the first factor [Wilde2011Qst, qit-notes.tex:7754-7762]. -/
theorem traceLeft_kronecker [Fintype a] (M : CMatrix a) (N : CMatrix b) :
    Matrix.traceLeft (M ⊗ₖ N) = matrixScale M.trace N := by
  ext j j'
  simp [Matrix.traceLeft, matrixScale, Matrix.trace, Matrix.kroneckerMap_apply, Finset.sum_mul]

/-- Taking `Tr_B` of a Kronecker product leaves the first factor scaled by the
trace of the second factor [Wilde2011Qst, qit-notes.tex:7754-7762]. -/
theorem traceRight_kronecker [Fintype b] (M : CMatrix a) (N : CMatrix b) :
    Matrix.traceRight (M ⊗ₖ N) = matrixScale N.trace M := by
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
    partialTransposeA (a := a) (b := b) (M ⊗ₖ N) =
      (Matrix.transpose M) ⊗ₖ N := by
  ext x y
  cases x
  cases y
  rfl

/-- Partial transpose on the second subsystem transposes the second Kronecker factor. -/
theorem partialTransposeB_kronecker (M : CMatrix a) (N : CMatrix b) :
    partialTransposeB (a := a) (b := b) (M ⊗ₖ N) =
      M ⊗ₖ (Matrix.transpose N) := by
  ext x y
  cases x
  cases y
  rfl

/-- A matrix unit on a product index is a Kronecker product of matrix units. -/
theorem single_prod_eq_kronecker_single [DecidableEq a] [DecidableEq b]
    (i i' : a) (j j' : b) :
    Matrix.single (i, j) (i', j') (1 : ℂ) =
      (Matrix.single i i' (1 : ℂ)) ⊗ₖ
        (Matrix.single j j' (1 : ℂ)) := by
  rw [Matrix.single_kronecker_single, one_mul]

/-- Trace of a diagonal matrix unit. -/
theorem trace_single_one [Fintype a] [DecidableEq a] (i i' : a) :
    (Matrix.single i i' (1 : ℂ)).trace = if i = i' then 1 else 0 := by
  by_cases h : i = i'
  · subst h
    simp [Matrix.trace, Matrix.single]
  · have hzero : ∀ x : a, Matrix.single i i' (1 : ℂ) x x = 0 := by
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

/-- Relabelling a product along a finite equivalence relabels each factor. -/
theorem submatrix_equiv_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A B : CMatrix κ) :
    (A * B).submatrix e e = A.submatrix e e * B.submatrix e e :=
  (Matrix.submatrix_mul_equiv A B e e e).symm

/-- Trace pairings are invariant under simultaneous finite relabelling. -/
theorem trace_mul_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M U : CMatrix κ) :
    ((M.submatrix e e) * (U.submatrix e e)).trace = (M * U).trace := by
  rw [Matrix.submatrix_mul_equiv, Matrix.trace_submatrix]

/-- Relabelling along a finite equivalence leaves the trace unchanged. -/
theorem cMatrix_trace_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A : CMatrix ι) :
    (Matrix.reindex e e A).trace = A.trace := by
  rw [Matrix.trace, Matrix.trace]
  exact Fintype.sum_equiv e.symm
    (fun i : κ => Matrix.reindex e e A i i)
    (fun i : ι => A i i)
    (by intro i; simp [Matrix.reindex_apply, Matrix.submatrix_apply])

/-- Partial-trace pairing for a left identity factor:
`Tr_B[X (U ⊗ 1)] = Tr_B[X] U`. -/
theorem traceRight_mul_kronecker_one_left [Fintype a] [Fintype b] [DecidableEq b]
    (X : CMatrix (a × b)) (U : CMatrix a) :
    Matrix.traceRight (X * (U ⊗ₖ (1 : CMatrix b))) =
      Matrix.traceRight X * U := by
  ext i i'
  simp [Matrix.traceRight, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Trace pairing against a right identity Kronecker factor reduces to the
partial trace over the right subsystem. -/
theorem trace_mul_kronecker_one_right_eq_traceRight
    [Fintype a] [Fintype b] [DecidableEq b]
    (X : CMatrix (a × b)) (U : CMatrix a) :
    (X * (U ⊗ₖ (1 : CMatrix b))).trace =
      (Matrix.traceRight X * U).trace := by
  rw [← traceRight_mul_kronecker_one_left X U, Matrix.traceRight_trace]

/-- Trace pairing against an observable supported on the left tensor factor
reduces to the partial trace over the right subsystem. -/
theorem trace_kronecker_one_right_mul_eq_trace_mul_traceRight
    [Fintype a] [Fintype b] [DecidableEq b]
    (M : CMatrix (a × b)) (T : CMatrix a) :
    ((T ⊗ₖ (1 : CMatrix b)) * M).trace = (T * Matrix.traceRight M).trace := by
  calc
    ((T ⊗ₖ (1 : CMatrix b)) * M).trace =
        (M * (T ⊗ₖ (1 : CMatrix b))).trace := by
      rw [Matrix.trace_mul_comm]
    _ = (Matrix.traceRight M * T).trace :=
      trace_mul_kronecker_one_right_eq_traceRight M T
    _ = (T * Matrix.traceRight M).trace := by
      rw [Matrix.trace_mul_comm]

/-- A positive real scalar multiple of the identity is positive definite. -/
theorem cMatrix_real_smul_one_posDef [DecidableEq a] {r : ℝ} (hr : 0 < r) :
    (r • (1 : CMatrix a)).PosDef := by
  rw [show r • (1 : CMatrix a) = Matrix.diagonal (fun _ : a => (r : ℂ)) by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]]
  rw [Matrix.posDef_diagonal_iff]
  intro i
  exact_mod_cast hr

/-- Reindexing a unitary matrix by a finite equivalence leaves it unitary. -/
theorem cMatrix_reindex_mem_unitary {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.reindex e e (U : CMatrix ι) ∈ Matrix.unitaryGroup κ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  have hU := Matrix.mem_unitaryGroup_iff.mp U.2
  have happ := congrFun (congrFun hU (e.symm i)) (e.symm j)
  simp [Matrix.mul_apply, Matrix.star_apply] at happ ⊢
  have hsum :
      (∑ x : κ, (U : CMatrix ι) (e.symm i) (e.symm x) *
          starRingEnd ℂ ((U : CMatrix ι) (e.symm j) (e.symm x))) =
        ∑ y : ι, (U : CMatrix ι) (e.symm i) y *
          starRingEnd ℂ ((U : CMatrix ι) (e.symm j) y) := by
    exact Fintype.sum_equiv e.symm
      (fun x : κ => (U : CMatrix ι) (e.symm i) (e.symm x) *
        starRingEnd ℂ ((U : CMatrix ι) (e.symm j) (e.symm x)))
      (fun y : ι => (U : CMatrix ι) (e.symm i) y *
        starRingEnd ℂ ((U : CMatrix ι) (e.symm j) y))
      (by intro x; rfl)
  rw [hsum]
  simpa [Matrix.one_apply] using happ

/-- The complement of an idempotent matrix is idempotent. -/
theorem projection_complement_idempotent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : CMatrix ι} (hPidem : P * P = P) :
    (1 - P) * (1 - P) = 1 - P := by
  calc
    (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    _ = 1 - P := by
      rw [hPidem]
      abel

end

end QIT
