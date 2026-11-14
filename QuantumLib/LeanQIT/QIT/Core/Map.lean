/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.State

/-!
# Matrix maps

Finite-dimensional linear maps between matrix spaces. The Choi matrix is the
finite-dimensional representation used to state complete positivity, following
the finite-resource Choi characterization and inverse formula
[Tomamichel2015FiniteResources, prelim.tex:915-931].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- A complex-linear map between finite matrix spaces. -/
abbrev MatrixMap (a : Type u) (b : Type v) [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] :=
  CMatrix a →ₗ[Complex] CMatrix b

namespace MatrixMap

/-- Choi matrix of a finite-dimensional matrix map. -/
def choi (Phi : MatrixMap a b) : CMatrix (Prod a b) :=
  fun ij kl => Phi (Matrix.single ij.1 kl.1 (1 : Complex)) ij.2 kl.2

/-- Choi-positive formulation of complete positivity. -/
def IsCompletelyPositive (Phi : MatrixMap a b) : Prop :=
  (choi Phi).PosSemidef

/-- Trace-preserving condition. -/
def IsTracePreserving (Phi : MatrixMap a b) : Prop :=
  forall X : CMatrix a, (Phi X).trace = X.trace

/-- The matrix map whose Choi matrix is the prescribed finite matrix.

This is the explicit inverse to `MatrixMap.choi`, obtained by expanding the
input matrix in matrix units. -/
def ofChoiMatrix (J : CMatrix (Prod a b)) : MatrixMap a b where
  toFun X := fun j j' => ∑ i : a, ∑ i' : a, X i i' * J (i, j) (i', j')
  map_add' X Y := by
    ext j j'
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    ext j j'
    simp [Finset.mul_sum, mul_assoc]

@[simp]
theorem ofChoiMatrix_apply (J : CMatrix (Prod a b)) (X : CMatrix a)
    (j j' : b) :
    ofChoiMatrix J X j j' =
      ∑ i : a, ∑ i' : a, X i i' * J (i, j) (i', j') := by
  rfl

/-- `ofChoiMatrix` is a right inverse to the Choi construction. -/
theorem choi_ofChoiMatrix (J : CMatrix (Prod a b)) :
    choi (ofChoiMatrix J) = J := by
  ext ij kl
  rcases ij with ⟨i, j⟩
  rcases kl with ⟨i', j'⟩
  simp only [choi, ofChoiMatrix, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i']
    · simp [Matrix.single]
    · intro y _ hy
      have hy' : i' ≠ y := hy.symm
      simp [Matrix.single, hy']
    · intro hnot
      simp at hnot
  · intro x _ hx
    have hxi : i ≠ x := hx.symm
    simp [Matrix.single, hxi]
  · intro hnot
    simp at hnot

/-- A positive semidefinite Choi matrix defines a completely positive map. -/
theorem ofChoiMatrix_isCompletelyPositive {J : CMatrix (Prod a b)}
    (hJ : J.PosSemidef) :
    IsCompletelyPositive (ofChoiMatrix J) := by
  rwa [IsCompletelyPositive, choi_ofChoiMatrix]

/-- The unique linear matrix map between unit systems. -/
def unit : MatrixMap PUnit.{u + 1} PUnit.{v + 1} where
  toFun X := fun _ _ => X PUnit.unit PUnit.unit
  map_add' X Y := by
    ext i j
    rfl
  map_smul' r X := by
    ext i j
    rfl

/-- The unit-system matrix map is Choi-positive. -/
theorem unit_isCompletelyPositive :
    IsCompletelyPositive (unit : MatrixMap PUnit.{u + 1} PUnit.{v + 1}) := by
  change (choi (unit : MatrixMap PUnit.{u + 1} PUnit.{v + 1})).PosSemidef
  have hchoi :
      choi (unit : MatrixMap PUnit.{u + 1} PUnit.{v + 1}) =
        (1 : CMatrix (PUnit.{u + 1} × PUnit.{v + 1})) := by
    ext x y
    cases x
    cases y
    simp [choi, unit, Matrix.single]
  rw [hchoi]
  exact Matrix.PosSemidef.one

/-- The unit-system matrix map is trace-preserving. -/
theorem unit_isTracePreserving :
    IsTracePreserving (unit : MatrixMap PUnit.{u + 1} PUnit.{v + 1}) := by
  intro X
  simp [unit, Matrix.trace]

/-- The unit-system matrix map preserves positive semidefinite matrices. -/
theorem unit_mapsPositive :
    forall X : CMatrix PUnit.{u + 1}, X.PosSemidef ->
      ((unit : MatrixMap PUnit.{u + 1} PUnit.{v + 1}) X).PosSemidef := by
  intro X hX
  have hsub :
      (unit : MatrixMap PUnit.{u + 1} PUnit.{v + 1}) X =
        X.submatrix (fun _ : PUnit.{v + 1} => PUnit.unit)
          (fun _ : PUnit.{v + 1} => PUnit.unit) := by
    ext i j
    rfl
  rw [hsub]
  exact hX.submatrix _

/-- Expand a matrix map over matrix units. -/
theorem map_eq_sum_single (Phi : MatrixMap a b) (X : CMatrix a) :
    Phi X = ∑ i : a, ∑ i' : a,
      X i i' • Phi (Matrix.single i i' (1 : Complex)) := by
  calc
    Phi X = Phi (∑ i : a, ∑ i' : a, Matrix.single i i' (X i i')) := by
      congr
      exact Matrix.matrix_eq_sum_single X
    _ = ∑ i : a, ∑ i' : a,
        X i i' • Phi (Matrix.single i i' (1 : Complex)) := by
      simp only [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro i' _
      have hsingle :
          Matrix.single i i' (X i i') =
            X i i' • Matrix.single i i' (1 : Complex) := by
        ext r s
        simp [Matrix.single]
      rw [hsingle, map_smul]

/-- Trace expansion of a matrix map over matrix units. -/
theorem trace_map_eq_sum_single (Phi : MatrixMap a b) (X : CMatrix a) :
    (Phi X).trace = ∑ i : a, ∑ i' : a,
      X i i' * (Phi (Matrix.single i i' (1 : Complex))).trace := by
  rw [map_eq_sum_single Phi X]
  simp [Matrix.trace_sum, Matrix.trace_smul]

/-- Kraus-form matrix map `X ↦ ∑ k, K k * X * (K k)ᴴ`. -/
def ofKraus {κ : Type w} [Fintype κ] (K : κ -> Matrix b a Complex) : MatrixMap a b where
  toFun X := ∑ k : κ, K k * X * (K k).conjTranspose
  map_add' X Y := by
    ext i j
    simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' r X := by
    ext i j
    simp [Matrix.sum_apply, Matrix.mul_apply, Finset.mul_sum]

/-- Kraus-form maps preserve positive semidefinite matrices. -/
theorem ofKraus_mapsPositive {κ : Type w} [Fintype κ] (K : κ -> Matrix b a Complex) :
    forall X : CMatrix a, X.PosSemidef -> (ofKraus K X).PosSemidef := by
  intro X hX
  rw [ofKraus]
  exact Matrix.posSemidef_sum Finset.univ
    (fun k _ => hX.mul_mul_conjTranspose_same (K k))

/-- Heisenberg adjoint of a Kraus-form map. -/
def krausAdjoint {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ) (E : CMatrix b) : CMatrix a :=
  ∑ k : κ, Matrix.conjTranspose (K k) * E * K k

omit [DecidableEq a] [DecidableEq b] in
/-- Kraus Heisenberg adjoints preserve positive semidefinite effects. -/
theorem krausAdjoint_mapsPositive {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ) :
    ∀ E : CMatrix b, E.PosSemidef → (krausAdjoint K E).PosSemidef := by
  intro E hE
  rw [krausAdjoint]
  exact Matrix.posSemidef_sum Finset.univ fun k _ =>
    Matrix.PosSemidef.conjTranspose_mul_mul_same hE (K k)

omit [Fintype a] [DecidableEq a] [DecidableEq b] in
/-- Kraus Heisenberg adjoints commute with subtraction. -/
theorem krausAdjoint_sub_apply {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ) (E F : CMatrix b) :
    krausAdjoint K (E - F) = krausAdjoint K E - krausAdjoint K F := by
  ext i j
  simp [krausAdjoint, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq a] [DecidableEq b] in
/-- Kraus Heisenberg adjoints are monotone on effects. -/
theorem krausAdjoint_mono {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ) {E F : CMatrix b} (hEF : E ≤ F) :
    krausAdjoint K E ≤ krausAdjoint K F := by
  rw [Matrix.le_iff] at hEF ⊢
  have hpsd := krausAdjoint_mapsPositive K (F - E) hEF
  simpa [krausAdjoint_sub_apply] using hpsd

/-- Trace duality between a Kraus map and its Heisenberg adjoint. -/
theorem ofKraus_trace_duality {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ) (X : CMatrix a) (E : CMatrix b) :
    (((ofKraus K) X) * E).trace = (X * krausAdjoint K E).trace := by
  simp [ofKraus, krausAdjoint, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  let Kk : Matrix b a ℂ := K k
  let KkH : Matrix a b ℂ := Matrix.conjTranspose Kk
  calc
    ((K k * X * Matrix.conjTranspose (K k)) * E).trace =
        ((Kk * X * KkH) * E).trace := by rfl
    _ = (E * (Kk * X * KkH)).trace := by rw [Matrix.trace_mul_comm]
    _ = ((E * Kk) * (X * KkH)).trace := by
          simp only [Matrix.mul_assoc]
    _ = ((X * KkH) * (E * Kk)).trace := by rw [Matrix.trace_mul_comm]
    _ = (X * (KkH * E * Kk)).trace := by
          simp only [Matrix.mul_assoc]
    _ = (X * (Matrix.conjTranspose (K k) * E * K k)).trace := by rfl

/-- Conjugating each Kraus operator on the output/input sides conjugates the
corresponding Kraus map around the original map. -/
theorem ofKraus_conjugated_apply {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ) (T : CMatrix b) (S X : CMatrix a) :
    ofKraus (fun k => T * K k * S) X =
      T * ofKraus K (S * X * star S) * star T := by
  change (∑ k, (T * K k * S) * X * Matrix.conjTranspose (T * K k * S)) =
    T * (∑ k, K k * (S * X * star S) * Matrix.conjTranspose (K k)) * star T
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hTct : Matrix.conjTranspose T = star T := by
    rw [← Matrix.star_eq_conjTranspose]
  have hSct : Matrix.conjTranspose S = star S := by
    rw [← Matrix.star_eq_conjTranspose]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSct, hTct]
  simp [Matrix.mul_assoc]

/-- A trace-preserving Kraus map has unital Heisenberg adjoint. -/
theorem krausAdjoint_one_of_tracePreserving {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ) (hTP : IsTracePreserving (ofKraus K)) :
    krausAdjoint K (1 : CMatrix b) = 1 := by
  apply Matrix.ext
  intro i j
  let X : CMatrix a := Matrix.single j i (1 : ℂ)
  have htrace := hTP X
  have hdual :
      (((ofKraus K) X) * (1 : CMatrix b)).trace =
        (X * krausAdjoint K (1 : CMatrix b)).trace :=
    ofKraus_trace_duality K X (1 : CMatrix b)
  rw [Matrix.mul_one] at hdual
  rw [hdual] at htrace
  have hsingle_trace :
      (X * krausAdjoint K (1 : CMatrix b)).trace =
        (krausAdjoint K (1 : CMatrix b)) i j := by
    simp [X, Matrix.trace_single_mul]
  have hXtrace : X.trace = if j = i then (1 : ℂ) else 0 := by
    by_cases hji : j = i
    · subst hji
      simp [X, Matrix.trace, Matrix.single]
    · have hij : i ≠ j := by
        intro hij
        exact hji hij.symm
      simp [X, Matrix.trace, Matrix.single, hji, hij]
  have hOne : (1 : CMatrix a) i j = if j = i then (1 : ℂ) else 0 := by
    by_cases hji : j = i
    · subst hji
      simp
    · have hij : i ≠ j := by
        intro hij
        exact hji hij.symm
      simp [hji, hij]
  calc
    krausAdjoint K (1 : CMatrix b) i j =
        (X * krausAdjoint K (1 : CMatrix b)).trace := hsingle_trace.symm
    _ = X.trace := htrace
    _ = (1 : CMatrix a) i j := by rw [hXtrace, hOne]

/-- A Kraus map is trace-preserving when its Heisenberg adjoint is unital. -/
theorem ofKraus_isTracePreserving_of_krausAdjoint_one {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ) (hK : krausAdjoint K (1 : CMatrix b) = 1) :
    IsTracePreserving (ofKraus K) := by
  intro X
  have hdual := ofKraus_trace_duality K X (1 : CMatrix b)
  rw [Matrix.mul_one] at hdual
  rw [hK, Matrix.mul_one] at hdual
  exact hdual

/-- A trace-preserving Kraus map has a unital positive Heisenberg adjoint, so
effects are pulled back to effects. -/
theorem krausAdjoint_effect_of_tracePreserving {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ) (hTP : IsTracePreserving (ofKraus K))
    {E : CMatrix b} (hEpos : E.PosSemidef) (hEle : E ≤ 1) :
    (krausAdjoint K E).PosSemidef ∧ krausAdjoint K E ≤ 1 := by
  refine ⟨krausAdjoint_mapsPositive K E hEpos, ?_⟩
  rw [Matrix.le_iff]
  have hcomp : (1 - E).PosSemidef := by
    rwa [← Matrix.le_iff]
  have hcompAdj : (krausAdjoint K (1 - E)).PosSemidef :=
    krausAdjoint_mapsPositive K (1 - E) hcomp
  have hone := krausAdjoint_one_of_tracePreserving K hTP
  have hsub := krausAdjoint_sub_apply K (1 : CMatrix b) E
  rw [hone] at hsub
  rwa [← hsub]

section KrausKadison

variable {κ : Type w} [Fintype κ] [DecidableEq κ]

/-- A PSD idempotent has PSD complement. -/
theorem posSemidef_one_sub_of_posSemidef_idempotent
    {ι : Type*} [Fintype ι] [DecidableEq ι] (P : CMatrix ι)
    (hPpos : P.PosSemidef) (hPid : P * P = P) :
    (1 - P).PosSemidef := by
  let Q : CMatrix ι := 1 - P
  have hPherm : P.IsHermitian := hPpos.isHermitian
  have hQherm : Q.IsHermitian := by
    dsimp [Q]
    exact Matrix.IsHermitian.sub (by simp [Matrix.IsHermitian]) hPherm
  have hQid : Q * Q = Q := by
    dsimp [Q]
    calc
      (1 - P) * (1 - P) = (1 - P) * 1 - (1 - P) * P := by
        rw [Matrix.mul_sub]
      _ = (1 - P) - (1 * P - P * P) := by
        rw [Matrix.mul_one, Matrix.sub_mul]
      _ = 1 - P := by
        rw [Matrix.one_mul, hPid]
        abel
  have hPSD : (Matrix.conjTranspose Q * Q).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self Q
  convert hPSD using 1
  rw [hQherm.eq, hQid]

/-- Stinespring stack matrix associated to a Kraus family. -/
def krausStinespringMatrix (K : κ → Matrix b a ℂ) : Matrix (b × κ) a ℂ :=
  fun yk x => K yk.2 yk.1 x

omit [Fintype a] [DecidableEq κ] in
/-- The Stinespring stack is an isometry exactly when the Kraus adjoint is
unital. -/
theorem krausStinespringMatrix_isometry_of_krausAdjoint_one
    (K : κ → Matrix b a ℂ) (hK : krausAdjoint K (1 : CMatrix b) = 1) :
    Matrix.conjTranspose (krausStinespringMatrix K) *
        krausStinespringMatrix K = (1 : CMatrix a) := by
  ext i j
  have hentry := congrFun (congrFun hK i) j
  simp only [krausAdjoint, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply] at hentry
  simp only [krausStinespringMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simpa [mul_comm] using hentry

/-- The Stinespring projection associated to a unital Kraus adjoint has a PSD
orthogonal complement. This is the projection-positivity core behind the
Kadison/variance step in the sandwiched Renyi variational route. -/
theorem krausStinespringMatrix_projection_complement_posSemidef
    (K : κ → Matrix b a ℂ) (hK : krausAdjoint K (1 : CMatrix b) = 1) :
    (1 - krausStinespringMatrix K * Matrix.conjTranspose (krausStinespringMatrix K)
      ).PosSemidef := by
  let S : Matrix (b × κ) a ℂ := krausStinespringMatrix K
  have hS : Matrix.conjTranspose S * S = (1 : CMatrix a) := by
    simpa [S] using krausStinespringMatrix_isometry_of_krausAdjoint_one K hK
  have hPpos : (S * Matrix.conjTranspose S).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self (Matrix.conjTranspose S)
  have hPid : (S * Matrix.conjTranspose S) * (S * Matrix.conjTranspose S) =
      S * Matrix.conjTranspose S := by
    calc
      (S * Matrix.conjTranspose S) * (S * Matrix.conjTranspose S) =
          S * (Matrix.conjTranspose S * (S * Matrix.conjTranspose S)) := by
            exact Matrix.mul_assoc S (Matrix.conjTranspose S) (S * Matrix.conjTranspose S)
      _ = S * ((Matrix.conjTranspose S * S) * Matrix.conjTranspose S) := by
            exact congrArg (fun M => S * M)
              (Matrix.mul_assoc (Matrix.conjTranspose S) S (Matrix.conjTranspose S)).symm
      _ = S * ((1 : CMatrix a) * Matrix.conjTranspose S) := by
            exact congrArg (fun M : CMatrix a => S * (M * Matrix.conjTranspose S)) hS
      _ = S * Matrix.conjTranspose S := by
            exact congrArg (fun M => S * M)
              (Matrix.one_mul (Matrix.conjTranspose S))
  simpa [S] using
    posSemidef_one_sub_of_posSemidef_idempotent
      (S * Matrix.conjTranspose S) hPpos hPid

omit [Fintype a] [DecidableEq a] [DecidableEq b] in
/-- Kraus Heisenberg adjoints are Stinespring compressions. -/
theorem krausAdjoint_eq_stinespring
    (K : κ → Matrix b a ℂ) (E : CMatrix b) :
    krausAdjoint K E =
      Matrix.conjTranspose (krausStinespringMatrix K) *
        Matrix.kronecker E (1 : CMatrix κ) *
          krausStinespringMatrix K := by
  ext i j
  simp [krausAdjoint, krausStinespringMatrix, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.mul_sum, mul_comm]
  rw [Finset.sum_comm]

omit [DecidableEq b] in
/-- Squaring a Stinespring block observable squares the observed operator. -/
theorem krausStinespring_observable_sq
    (E : CMatrix b) :
    Matrix.kronecker E (1 : CMatrix κ) *
        Matrix.kronecker E (1 : CMatrix κ) =
      Matrix.kronecker (E * E) (1 : CMatrix κ) := by
  simpa using
    (Matrix.mul_kronecker_mul E E (1 : CMatrix κ) (1 : CMatrix κ)).symm

omit [Fintype b] [DecidableEq b] [Fintype κ] in
/-- A Stinespring block observable is Hermitian when the observed operator is
Hermitian. -/
theorem krausStinespring_observable_isHermitian
    {E : CMatrix b} (hE : E.IsHermitian) :
    (Matrix.kronecker E (1 : CMatrix κ)).IsHermitian := by
  rw [Matrix.IsHermitian]
  calc
    Matrix.conjTranspose (Matrix.kronecker E (1 : CMatrix κ)) =
        Matrix.kronecker (Matrix.conjTranspose E) (Matrix.conjTranspose (1 : CMatrix κ)) := by
          simpa [Matrix.kronecker] using
            Matrix.conjTranspose_kronecker E (1 : CMatrix κ)
    _ = Matrix.kronecker E (1 : CMatrix κ) := by
          rw [hE.eq]
          simp

/-- Positivity of the Stinespring variance term
`(T S)ᴴ (I - S Sᴴ) (T S)`.

Together with the Stinespring compression identity, this is the positive part of
Kadison's inequality for unital Kraus adjoints. -/
theorem krausStinespring_varianceTerm_posSemidef
    (K : κ → Matrix b a ℂ) (hK : krausAdjoint K (1 : CMatrix b) = 1)
    (T : CMatrix (b × κ)) :
    (Matrix.conjTranspose (T * krausStinespringMatrix K) *
        (1 - krausStinespringMatrix K * Matrix.conjTranspose (krausStinespringMatrix K)) *
          (T * krausStinespringMatrix K)).PosSemidef := by
  exact Matrix.PosSemidef.conjTranspose_mul_mul_same
    (krausStinespringMatrix_projection_complement_posSemidef K hK)
    (T * krausStinespringMatrix K)

omit [DecidableEq b] in
/-- Multiplying a Stinespring block observable by its adjoint multiplies the
observed operators in the same order. -/
theorem krausStinespring_observable_conjTranspose_mul
    (E : CMatrix b) :
    Matrix.conjTranspose (Matrix.kronecker E (1 : CMatrix κ)) *
        Matrix.kronecker E (1 : CMatrix κ) =
      Matrix.kronecker (Matrix.conjTranspose E * E) (1 : CMatrix κ) := by
  have hct :
      Matrix.conjTranspose (Matrix.kronecker E (1 : CMatrix κ)) =
        Matrix.kronecker (Matrix.conjTranspose E) (Matrix.conjTranspose (1 : CMatrix κ)) := by
    simpa [Matrix.kronecker] using Matrix.conjTranspose_kronecker E (1 : CMatrix κ)
  calc
    Matrix.conjTranspose (Matrix.kronecker E (1 : CMatrix κ)) *
        Matrix.kronecker E (1 : CMatrix κ) =
        Matrix.kronecker (Matrix.conjTranspose E) (Matrix.conjTranspose (1 : CMatrix κ)) *
          Matrix.kronecker E (1 : CMatrix κ) := by
            rw [hct]
    _ = Matrix.kronecker (Matrix.conjTranspose E * E)
        (Matrix.conjTranspose (1 : CMatrix κ) * (1 : CMatrix κ)) := by
            exact (Matrix.mul_kronecker_mul (Matrix.conjTranspose E) E
              (Matrix.conjTranspose (1 : CMatrix κ)) (1 : CMatrix κ)).symm
    _ = Matrix.kronecker (Matrix.conjTranspose E * E) (1 : CMatrix κ) := by
            simp

/-- Kadison-Schwarz inequality for a unital Kraus Heisenberg adjoint:
`Φ†(E)ᴴ Φ†(E) ≤ Φ†(EᴴE)` for arbitrary `E`. -/
theorem krausAdjoint_conjTranspose_mul_self_le_of_krausAdjoint_one
    (K : κ → Matrix b a ℂ) (hK : krausAdjoint K (1 : CMatrix b) = 1)
    (E : CMatrix b) :
    Matrix.conjTranspose (krausAdjoint K E) * krausAdjoint K E ≤
      krausAdjoint K (Matrix.conjTranspose E * E) := by
  let S : Matrix (b × κ) a ℂ := krausStinespringMatrix K
  let T : CMatrix (b × κ) := Matrix.kronecker E (1 : CMatrix κ)
  have hTstarT :
      Matrix.conjTranspose T * T =
        Matrix.kronecker (Matrix.conjTranspose E * E) (1 : CMatrix κ) := by
    simpa [T] using krausStinespring_observable_conjTranspose_mul (κ := κ) E
  have hmain :
      (Matrix.conjTranspose (T * S) * (1 - S * Matrix.conjTranspose S) * (T * S)
        ).PosSemidef := by
    simpa [S] using krausStinespring_varianceTerm_posSemidef K hK T
  have hdiff :
      krausAdjoint K (Matrix.conjTranspose E * E) -
          Matrix.conjTranspose (krausAdjoint K E) * krausAdjoint K E =
        Matrix.conjTranspose (T * S) * (1 - S * Matrix.conjTranspose S) * (T * S) := by
    calc
      krausAdjoint K (Matrix.conjTranspose E * E) -
          Matrix.conjTranspose (krausAdjoint K E) * krausAdjoint K E =
          (Matrix.conjTranspose S * (Matrix.conjTranspose T * T) * S) -
            Matrix.conjTranspose (Matrix.conjTranspose S * T * S) *
              (Matrix.conjTranspose S * T * S) := by
            rw [krausAdjoint_eq_stinespring K (Matrix.conjTranspose E * E),
              krausAdjoint_eq_stinespring K E]
            change Matrix.conjTranspose S *
                Matrix.kronecker (Matrix.conjTranspose E * E) (1 : CMatrix κ) * S -
                Matrix.conjTranspose (Matrix.conjTranspose S * T * S) *
                  (Matrix.conjTranspose S * T * S) =
                Matrix.conjTranspose S * (Matrix.conjTranspose T * T) * S -
                Matrix.conjTranspose (Matrix.conjTranspose S * T * S) *
                  (Matrix.conjTranspose S * T * S)
            rw [← hTstarT]
      _ = Matrix.conjTranspose S * Matrix.conjTranspose T *
            (1 - S * Matrix.conjTranspose S) * T * S := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
      _ = Matrix.conjTranspose (T * S) * (1 - S * Matrix.conjTranspose S) *
            (T * S) := by
            rw [Matrix.conjTranspose_mul]
            simp [Matrix.mul_assoc]
  rw [Matrix.le_iff, hdiff]
  exact hmain

/-- Kadison-Schwarz inequality for trace-preserving Kraus maps, stated from
the Schrödinger-picture trace-preservation hypothesis. -/
theorem krausAdjoint_conjTranspose_mul_self_le_of_tracePreserving
    (K : κ → Matrix b a ℂ) (hTP : IsTracePreserving (ofKraus K))
    (E : CMatrix b) :
    Matrix.conjTranspose (krausAdjoint K E) * krausAdjoint K E ≤
      krausAdjoint K (Matrix.conjTranspose E * E) :=
  krausAdjoint_conjTranspose_mul_self_le_of_krausAdjoint_one K
    (krausAdjoint_one_of_tracePreserving K hTP) E

/-- Kadison inequality for a unital Kraus Heisenberg adjoint:
`Φ†(E)^2 ≤ Φ†(E^2)` for Hermitian `E`. -/
theorem krausAdjoint_mul_self_le_of_krausAdjoint_one
    (K : κ → Matrix b a ℂ) (hK : krausAdjoint K (1 : CMatrix b) = 1)
    {E : CMatrix b} (hE : E.IsHermitian) :
    krausAdjoint K E * krausAdjoint K E ≤ krausAdjoint K (E * E) := by
  let S : Matrix (b × κ) a ℂ := krausStinespringMatrix K
  let T : CMatrix (b × κ) := Matrix.kronecker E (1 : CMatrix κ)
  have hTstar : Matrix.conjTranspose T = T := by
    exact (krausStinespring_observable_isHermitian (κ := κ) hE).eq
  have hTsq : T * T = Matrix.kronecker (E * E) (1 : CMatrix κ) := by
    simpa [T] using krausStinespring_observable_sq (κ := κ) E
  have hmain :
      (Matrix.conjTranspose (T * S) * (1 - S * Matrix.conjTranspose S) * (T * S)
        ).PosSemidef := by
    simpa [S] using krausStinespring_varianceTerm_posSemidef K hK T
  have hdiff :
      krausAdjoint K (E * E) - krausAdjoint K E * krausAdjoint K E =
        Matrix.conjTranspose (T * S) * (1 - S * Matrix.conjTranspose S) * (T * S) := by
    calc
      krausAdjoint K (E * E) - krausAdjoint K E * krausAdjoint K E =
          (Matrix.conjTranspose S * (T * T) * S) -
            (Matrix.conjTranspose S * T * S) *
              (Matrix.conjTranspose S * T * S) := by
            rw [krausAdjoint_eq_stinespring K (E * E),
              krausAdjoint_eq_stinespring K E]
            change Matrix.conjTranspose S *
                Matrix.kronecker (E * E) (1 : CMatrix κ) * S -
                (Matrix.conjTranspose S * T * S) *
                  (Matrix.conjTranspose S * T * S) =
                Matrix.conjTranspose S * (T * T) * S -
                Matrix.conjTranspose S * T * S * (Matrix.conjTranspose S * T * S)
            rw [← hTsq]
      _ = Matrix.conjTranspose S * T * (1 - S * Matrix.conjTranspose S) * T * S := by
            simp [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      _ = Matrix.conjTranspose (T * S) * (1 - S * Matrix.conjTranspose S) * (T * S) := by
            rw [Matrix.conjTranspose_mul, hTstar]
            simp [Matrix.mul_assoc]
  rw [Matrix.le_iff, hdiff]
  exact hmain

/-- Kadison inequality for trace-preserving Kraus maps, stated directly from
the Schrödinger-picture trace-preservation hypothesis. -/
theorem krausAdjoint_mul_self_le_of_tracePreserving
    (K : κ → Matrix b a ℂ) (hTP : IsTracePreserving (ofKraus K))
    {E : CMatrix b} (hE : E.IsHermitian) :
    krausAdjoint K E * krausAdjoint K E ≤ krausAdjoint K (E * E) :=
  krausAdjoint_mul_self_le_of_krausAdjoint_one K
    (krausAdjoint_one_of_tracePreserving K hTP) hE

/-- Kadison inequality specialized to positive semidefinite effects. -/
theorem krausAdjoint_posSemidef_mul_self_le_of_tracePreserving
    (K : κ → Matrix b a ℂ) (hTP : IsTracePreserving (ofKraus K))
    {E : CMatrix b} (hE : E.PosSemidef) :
    krausAdjoint K E * krausAdjoint K E ≤ krausAdjoint K (E * E) :=
  krausAdjoint_mul_self_le_of_tracePreserving K hTP hE.isHermitian

end KrausKadison

/-- Choi matrix of a Kraus-form matrix map, as a sum of rank-one projectors. -/
theorem choi_ofKraus {κ : Type w} [Fintype κ] (K : κ -> Matrix b a Complex) :
    choi (ofKraus K) =
      ∑ k : κ, Matrix.vecMulVec
        (fun x : a × b => K k x.2 x.1)
        (fun x : a × b => star (K k x.2 x.1)) := by
  ext x y
  simp only [choi, ofKraus, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.single,
    Matrix.vecMulVec]
  refine Finset.sum_congr rfl ?_
  intro k _
  refine (Finset.sum_eq_single y.1 ?_ ?_).trans ?_
  · intro y' _ hy'
    simp [hy', eq_comm]
  · intro hnot
    simp at hnot
  · have hsum :
        (∑ x' : a, K k x.2 x' *
          (if x.1 = x' ∧ y.1 = y.1 then (1 : Complex) else 0)) =
          K k x.2 x.1 := by
      calc
        (∑ x' : a, K k x.2 x' *
          (if x.1 = x' ∧ y.1 = y.1 then (1 : Complex) else 0)) =
            K k x.2 x.1 *
              (if x.1 = x.1 ∧ y.1 = y.1 then (1 : Complex) else 0) := by
          refine Finset.sum_eq_single x.1 ?_ ?_
          · intro x' _ hx'
            have hxne : x.1 ≠ x' := by
              intro h
              exact hx' h.symm
            simp [hxne]
          · intro hnot
            simp at hnot
        _ = K k x.2 x.1 := by
          simp
    rw [hsum]

/-- Kraus-form maps are completely positive in the Choi-positive formulation. -/
theorem ofKraus_completelyPositive {κ : Type w} [Fintype κ]
    (K : κ -> Matrix b a Complex) :
    IsCompletelyPositive (ofKraus K) := by
  rw [IsCompletelyPositive, choi_ofKraus]
  exact Matrix.posSemidef_sum Finset.univ (fun _ _ =>
    Matrix.posSemidef_vecMulVec_self_star _)

/-- Choi matrices determine finite-dimensional matrix maps. -/
theorem choi_inj {Phi Psi : MatrixMap a b} (h : choi Phi = choi Psi) :
    Phi = Psi := by
  apply LinearMap.ext
  intro X
  rw [map_eq_sum_single Phi X, map_eq_sum_single Psi X]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro i' _
  have hbasis :
      Phi (Matrix.single i i' (1 : Complex)) =
        Psi (Matrix.single i i' (1 : Complex)) := by
    ext p q
    have hij := congrFun (congrFun h (i, p)) (i', q)
    simpa [choi] using hij
  rw [hbasis]

/-- Choi-positive maps have a finite Kraus representation
[Wilde2011Qst, qit-notes.tex:8242-8262]. -/
theorem exists_kraus_of_choi_psd (Phi : MatrixMap a b)
    (hPhi : IsCompletelyPositive Phi) :
    ∃ K : (a × b) -> Matrix b a Complex, Phi = ofKraus K := by
  let K : (a × b) -> Matrix b a Complex := fun k y x =>
    (hPhi.1.eigenvectorUnitary.val : Matrix (a × b) (a × b) Complex) (x, y) k *
      (Real.sqrt (hPhi.1.eigenvalues k) : Complex)
  use K
  apply choi_inj
  rw [choi_ofKraus]
  convert Matrix.IsHermitian.spectral_theorem hPhi.1 using 1
  ext x y
  simp [K, Matrix.mul_apply, Matrix.vecMulVec]
  ring_nf
  simp [Matrix.sum_apply, Matrix.diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsqrt :
      ((Real.sqrt (hPhi.1.eigenvalues k) : Complex) ^ 2) =
        (hPhi.1.eigenvalues k : Complex) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (hPhi.eigenvalues_nonneg k)]
  rw [hsqrt]

/-- Choi-positive complete positivity maps positive semidefinite inputs to
positive semidefinite outputs via the finite Kraus representation. -/
theorem isCompletelyPositive_mapsPositive (Phi : MatrixMap a b)
    (hPhi : IsCompletelyPositive Phi) :
    forall X : CMatrix a, X.PosSemidef -> (Phi X).PosSemidef := by
  obtain ⟨K, hK⟩ := exists_kraus_of_choi_psd Phi hPhi
  intro X hX
  rw [hK]
  exact ofKraus_mapsPositive K X hX

variable {c : Type w}
variable [Fintype c] [DecidableEq c]

/-- Composition of Kraus-form maps is again a Kraus-form map, with pairwise
products of Kraus operators. -/
theorem ofKraus_comp_ofKraus {κ : Type x} {ι : Type y} [Fintype κ] [Fintype ι]
    (L : ι -> Matrix c b Complex) (K : κ -> Matrix b a Complex) :
    (ofKraus L).comp (ofKraus K) =
      ofKraus (fun kl : κ × ι => L kl.2 * K kl.1) := by
  ext X i j
  simp [ofKraus, LinearMap.comp_apply, Matrix.sum_apply, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]
  rw [← Finset.univ_product_univ, Finset.sum_product]

/-- Complete positivity is stable under composition of finite matrix maps. -/
theorem isCompletelyPositive_comp (Psi : MatrixMap b c) (Phi : MatrixMap a b)
    (hPsi : IsCompletelyPositive Psi) (hPhi : IsCompletelyPositive Phi) :
    IsCompletelyPositive (Psi.comp Phi) := by
  obtain ⟨K, hK⟩ := exists_kraus_of_choi_psd Phi hPhi
  obtain ⟨L, hL⟩ := exists_kraus_of_choi_psd Psi hPsi
  rw [hL, hK, ofKraus_comp_ofKraus]
  exact ofKraus_completelyPositive _

/-- Trace preservation is stable under composition of finite matrix maps. -/
theorem isTracePreserving_comp (Psi : MatrixMap b c) (Phi : MatrixMap a b)
    (hPsi : IsTracePreserving Psi) (hPhi : IsTracePreserving Phi) :
    IsTracePreserving (Psi.comp Phi) := by
  intro X
  exact (hPsi (Phi X)).trans (hPhi X)

variable {c : Type w} {d : Type x}
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

/-- Matrix-map Kronecker product. This is the linear-map layer for
tensor-product channels [HolevoGiovannetti2012QuantumChannels,
arxive.tex:965-974]. -/
def kron (Phi : MatrixMap a b) (Psi : MatrixMap c d) : MatrixMap (Prod a c) (Prod b d) where
  toFun X := fun bd bd' =>
    Finset.univ.sum fun j : c =>
    Finset.univ.sum fun j' : c =>
    Finset.univ.sum fun i : a =>
    Finset.univ.sum fun i' : a =>
      X (i, j) (i', j') * Phi (Matrix.single i i' (1 : Complex)) bd.1 bd'.1 *
        Psi (Matrix.single j j' (1 : Complex)) bd.2 bd'.2
  map_add' X Y := by
    ext bd bd'
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' r X := by
    ext bd bd'
    simp [mul_assoc, Finset.mul_sum]

/-- The Kronecker product of matrix maps acts componentwise on Kronecker
products of matrices. -/
theorem kron_apply_kronecker (Phi : MatrixMap a b) (Psi : MatrixMap c d)
    (X : CMatrix a) (Y : CMatrix c) :
    kron Phi Psi (Matrix.kronecker X Y) =
      Matrix.kronecker (Phi X) (Psi Y) := by
  ext bd bd'
  have hPhi := congrFun (congrFun (map_eq_sum_single Phi X) bd.1) bd'.1
  have hPsi := congrFun (congrFun (map_eq_sum_single Psi Y) bd.2) bd'.2
  simp only [Matrix.sum_apply] at hPhi hPsi
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [hPhi, hPsi]
  simp [kron, Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_left_comm]

/-- Trace of the product map on a product matrix unit. -/
theorem trace_kron_single (Phi : MatrixMap a b) (Psi : MatrixMap c d)
    (i i' : a) (j j' : c) :
    (kron Phi Psi (Matrix.single (i, j) (i', j') (1 : Complex))).trace =
      (Phi (Matrix.single i i' (1 : Complex))).trace *
        (Psi (Matrix.single j j' (1 : Complex))).trace := by
  rw [single_prod_eq_kronecker_single, kron_apply_kronecker]
  exact Matrix.trace_kronecker _ _

/-- Trace preservation is stable under the Kronecker product of matrix maps. -/
theorem isTracePreserving_kron (Phi : MatrixMap a b) (Psi : MatrixMap c d)
    (hPhi : IsTracePreserving Phi) (hPsi : IsTracePreserving Psi) :
    IsTracePreserving (kron Phi Psi) := by
  intro X
  rw [trace_map_eq_sum_single (kron Phi Psi) X]
  calc
    (∑ ac : Prod a c, ∑ ac' : Prod a c,
        X ac ac' * (kron Phi Psi
          (Matrix.single ac ac' (1 : Complex))).trace) =
        ∑ ac : Prod a c, ∑ ac' : Prod a c,
          X ac ac' * ((if ac.1 = ac'.1 then (1 : Complex) else 0) *
            (if ac.2 = ac'.2 then (1 : Complex) else 0)) := by
      refine Finset.sum_congr rfl ?_
      intro ac _
      refine Finset.sum_congr rfl ?_
      intro ac' _
      cases ac with
      | mk i j =>
        cases ac' with
        | mk i' j' =>
          rw [trace_kron_single, hPhi, hPsi, trace_single_one, trace_single_one]
    _ = X.trace := sum_delta_trace X

/-- Choi matrix of a Kronecker product of matrix maps, up to the product-index
reordering between `((a × c) × (b × d))` and `((a × b) × (c × d))`. -/
theorem choi_kron (Phi : MatrixMap a b) (Psi : MatrixMap c d) :
    choi (kron Phi Psi) =
      (Matrix.kronecker (choi Phi) (choi Psi)).submatrix
        (fun x : (a × c) × (b × d) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
        (fun x : (a × c) × (b × d) => ((x.1.1, x.2.1), (x.1.2, x.2.2))) := by
  ext acbd acbd'
  simp only [choi, Matrix.submatrix_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [single_prod_eq_kronecker_single acbd.1.1 acbd'.1.1 acbd.1.2 acbd'.1.2,
    kron_apply_kronecker]
  rfl

/-- Complete positivity is stable under the Kronecker product of matrix maps
in the Choi-positive formulation. -/
theorem isCompletelyPositive_kron (Phi : MatrixMap a b) (Psi : MatrixMap c d)
    (hPhi : IsCompletelyPositive Phi) (hPsi : IsCompletelyPositive Psi) :
    IsCompletelyPositive (kron Phi Psi) := by
  rw [IsCompletelyPositive, choi_kron]
  exact (hPhi.kronecker hPsi).submatrix _

end MatrixMap

end

end QIT
