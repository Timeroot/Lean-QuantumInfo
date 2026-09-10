/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Core.State
public import QuantumInfo.Channels.Unbundled

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

/-- A complex-linear map between finite matrix spaces: physlib's `MatrixMap` over `ℂ`, with the
finiteness assumptions that the rest of Lean-QIT works under. Complete positivity and trace
preservation are physlib's `MatrixMap.IsCompletelyPositive` and `MatrixMap.IsTracePreserving`. -/
abbrev MatrixMap (a : Type u) (b : Type v) [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] :=
  _root_.MatrixMap a b ℂ

namespace MatrixMap

/-- Choi matrix of a finite-dimensional matrix map. -/
def choi (Phi : MatrixMap a b) : CMatrix (a × b) :=
  fun ij kl => Phi (Matrix.single ij.1 kl.1 (1 : ℂ)) ij.2 kl.2

/-- The matrix map whose Choi matrix is the prescribed finite matrix.

This is the explicit inverse to `MatrixMap.choi`, obtained by expanding the
input matrix in matrix units. -/
def ofChoiMatrix (J : CMatrix (a × b)) : MatrixMap a b where
  toFun X := Matrix.of fun j j' => ∑ i : a, ∑ i' : a, X i i' * J (i, j) (i', j')
  map_add' X Y := by
    ext j j'
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    ext j j'
    simp [Finset.mul_sum, mul_assoc]

@[simp]
theorem ofChoiMatrix_apply (J : CMatrix (a × b)) (X : CMatrix a)
    (j j' : b) :
    ofChoiMatrix J X j j' =
      ∑ i : a, ∑ i' : a, X i i' * J (i, j) (i', j') := by
  rfl

/-- Lean-QIT indexes the Choi matrix by `input × output` and physlib by `output × input`, so the two
differ by `Prod.swap` on both indices. -/
theorem choi_eq_submatrix (Phi : MatrixMap a b) :
    Phi.choi = (_root_.MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap :=
  rfl

/-- The mirror image of `QIT.MatrixMap.choi_eq_submatrix`. -/
theorem choi_matrix_eq_submatrix (Phi : MatrixMap a b) :
    _root_.MatrixMap.choi_matrix Phi = Phi.choi.submatrix Prod.swap Prod.swap :=
  rfl

/-- Reconstructing a map from a Choi matrix agrees on the two conventions. -/
theorem ofChoiMatrix_eq (J : CMatrix (a × b)) :
    ofChoiMatrix J = _root_.MatrixMap.of_choi_matrix (J.submatrix Prod.swap Prod.swap) := by
  ext X j j'
  rfl

/-- Complete positivity, which physlib states as positivity of every ampliation, is positive
semidefiniteness of the Choi matrix in Lean-QIT's index convention. -/
theorem isCompletelyPositive_iff_choi (Phi : MatrixMap a b) :
    MatrixMap.IsCompletelyPositive Phi ↔ Phi.choi.PosSemidef := by
  rw [_root_.MatrixMap.choi_PSD_iff_CP_map, choi_eq_submatrix]
  exact ⟨fun h => h.submatrix Prod.swap, fun h => by simpa using h.submatrix Prod.swap⟩

/-- `ofChoiMatrix` is a right inverse to the Choi construction. -/
theorem choi_ofChoiMatrix (J : CMatrix (a × b)) :
    choi (ofChoiMatrix J) = J := by
  rw [choi_eq_submatrix, ofChoiMatrix_eq, _root_.MatrixMap.map_choi_inv]
  ext ⟨i, j⟩ ⟨i', j'⟩
  rfl

/-- A positive semidefinite Choi matrix defines a completely positive map. -/
theorem ofChoiMatrix_isCompletelyPositive {J : CMatrix (a × b)}
    (hJ : J.PosSemidef) :
    MatrixMap.IsCompletelyPositive (ofChoiMatrix J) := by
  rwa [isCompletelyPositive_iff_choi, choi_ofChoiMatrix]

/-- The unique linear matrix map between unit systems. -/
def unit : MatrixMap PUnit.{u + 1} PUnit.{v + 1} where
  toFun X := Matrix.of fun _ _ => X PUnit.unit PUnit.unit
  map_add' X Y := by
    ext i j
    rfl
  map_smul' r X := by
    ext i j
    rfl

/-- The unit-system matrix map is completely positive. -/
theorem unit_isCompletelyPositive :
    MatrixMap.IsCompletelyPositive (unit : MatrixMap PUnit.{u + 1} PUnit.{v + 1}) := by
  rw [isCompletelyPositive_iff_choi]
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
    MatrixMap.IsTracePreserving (unit : MatrixMap PUnit.{u + 1} PUnit.{v + 1}) := by
  intro X
  simp [unit, Matrix.trace]

/-- Expand a matrix map over matrix units. -/
theorem map_eq_sum_single (Phi : MatrixMap a b) (X : CMatrix a) :
    Phi X = ∑ i : a, ∑ i' : a,
      X i i' • Phi (Matrix.single i i' (1 : ℂ)) := by
  calc
    Phi X = Phi (∑ i : a, ∑ i' : a, Matrix.single i i' (X i i')) := by
      congr
      exact Matrix.matrix_eq_sum_single X
    _ = ∑ i : a, ∑ i' : a,
        X i i' • Phi (Matrix.single i i' (1 : ℂ)) := by
      simp only [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro i' _
      have hsingle :
          Matrix.single i i' (X i i') =
            X i i' • Matrix.single i i' (1 : ℂ) := by
        ext r s
        simp [Matrix.single]
      rw [hsingle, map_smul]

/-- Trace expansion of a matrix map over matrix units. -/
theorem trace_map_eq_sum_single (Phi : MatrixMap a b) (X : CMatrix a) :
    (Phi X).trace = ∑ i : a, ∑ i' : a,
      X i i' * (Phi (Matrix.single i i' (1 : ℂ))).trace := by
  rw [map_eq_sum_single Phi X]
  simp [Matrix.trace_sum, Matrix.trace_smul]

/-- Kraus-form matrix map `X ↦ ∑ k, K k * X * (K k)ᴴ`. -/
def ofKraus {κ : Type w} [Fintype κ] (K : κ → Matrix b a ℂ) : MatrixMap a b where
  toFun X := ∑ k : κ, K k * X * (K k).conjTranspose
  map_add' X Y := by
    ext i j
    simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' r X := by
    ext i j
    simp [Matrix.sum_apply, Matrix.mul_apply, Finset.mul_sum]

/-- Lean-QIT's one-family Kraus form is physlib's two-family form with both families equal. -/
theorem ofKraus_eq_of_kraus {κ : Type w} [Fintype κ] (K : κ → Matrix b a ℂ) :
    ofKraus K = _root_.MatrixMap.of_kraus K K :=
  LinearMap.ext fun X => (_root_.MatrixMap.of_kraus_apply K K X).symm

/-- Kraus-form maps preserve positive semidefinite matrices. -/
theorem ofKraus_mapsPositive {κ : Type w} [Fintype κ] (K : κ → Matrix b a ℂ) :
    ∀ X : CMatrix a, X.PosSemidef → (ofKraus K X).PosSemidef := fun _ hX => by
  rw [ofKraus_eq_of_kraus]
  exact _root_.MatrixMap.of_kraus_isPositive K hX

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
    (K : κ → Matrix b a ℂ) (hTP : MatrixMap.IsTracePreserving (ofKraus K)) :
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
    MatrixMap.IsTracePreserving (ofKraus K) := by
  intro X
  have hdual := ofKraus_trace_duality K X (1 : CMatrix b)
  rw [Matrix.mul_one] at hdual
  rw [hK, Matrix.mul_one] at hdual
  exact hdual

/-- A trace-preserving Kraus map has a unital positive Heisenberg adjoint, so
effects are pulled back to effects. -/
theorem krausAdjoint_effect_of_tracePreserving {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ) (hTP : MatrixMap.IsTracePreserving (ofKraus K))
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
  have hQid : Q * Q = Q := projection_complement_idempotent hPid
  have hPSD : (Matrix.conjTranspose Q * Q).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self Q
  convert hPSD using 1
  rw [hQherm.eq, hQid]

/-- Stinespring stack matrix associated to a Kraus family. -/
def krausStinespringMatrix (K : κ → Matrix b a ℂ) : Matrix (b × κ) a ℂ :=
  Matrix.of fun yk x => K yk.2 yk.1 x

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
    (K : κ → Matrix b a ℂ) (hTP : MatrixMap.IsTracePreserving (ofKraus K))
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
    (K : κ → Matrix b a ℂ) (hTP : MatrixMap.IsTracePreserving (ofKraus K))
    {E : CMatrix b} (hE : E.IsHermitian) :
    krausAdjoint K E * krausAdjoint K E ≤ krausAdjoint K (E * E) :=
  krausAdjoint_mul_self_le_of_krausAdjoint_one K
    (krausAdjoint_one_of_tracePreserving K hTP) hE

/-- Kadison inequality specialized to positive semidefinite effects. -/
theorem krausAdjoint_posSemidef_mul_self_le_of_tracePreserving
    (K : κ → Matrix b a ℂ) (hTP : MatrixMap.IsTracePreserving (ofKraus K))
    {E : CMatrix b} (hE : E.PosSemidef) :
    krausAdjoint K E * krausAdjoint K E ≤ krausAdjoint K (E * E) :=
  krausAdjoint_mul_self_le_of_tracePreserving K hTP hE.isHermitian

end KrausKadison

/-- Choi matrix of a Kraus-form matrix map, as a sum of rank-one projectors. -/
theorem choi_ofKraus {κ : Type w} [Fintype κ] (K : κ → Matrix b a ℂ) :
    choi (ofKraus K) =
      ∑ k : κ, Matrix.vecMulVec
        (fun x : a × b => K k x.2 x.1)
        (fun x : a × b => star (K k x.2 x.1)) := by
  rw [choi_eq_submatrix, ofKraus_eq_of_kraus, _root_.MatrixMap.choi_of_kraus]
  ext x y
  simp [Matrix.sum_apply, Matrix.vecMulVec]

/-- Kraus-form maps are completely positive. -/
theorem ofKraus_completelyPositive {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ) :
    MatrixMap.IsCompletelyPositive (ofKraus K) := by
  rw [ofKraus_eq_of_kraus]
  exact _root_.MatrixMap.of_kraus_isCompletelyPositive K

/-- Choi matrices determine finite-dimensional matrix maps. -/
theorem choi_inj {Phi Psi : MatrixMap a b} (h : choi Phi = choi Psi) :
    Phi = Psi :=
  _root_.MatrixMap.choi_matrix_inj <| by
    rw [choi_matrix_eq_submatrix, choi_matrix_eq_submatrix, h]

/-- Completely positive maps have a finite Kraus representation
[Wilde2011Qst, qit-notes.tex:8242-8262]. -/
theorem exists_kraus_of_choi_psd (Phi : MatrixMap a b)
    (hPhi : MatrixMap.IsCompletelyPositive Phi) :
    ∃ K : (a × b) → Matrix b a ℂ, Phi = ofKraus K := by
  obtain ⟨K, hK⟩ :=
    _root_.MatrixMap.IsCompletelyPositive.exists_kraus Phi hPhi
  refine ⟨K ∘ ⇑(Equiv.prodComm a b), ?_⟩
  rw [hK, ofKraus_eq_of_kraus]
  exact (_root_.MatrixMap.of_kraus_comp_equiv (Equiv.prodComm a b) K K).symm

/-- A completely positive map takes positive semidefinite inputs to positive
semidefinite outputs. -/
theorem isCompletelyPositive_mapsPositive (Phi : MatrixMap a b)
    (hPhi : MatrixMap.IsCompletelyPositive Phi) :
    ∀ X : CMatrix a, X.PosSemidef → (Phi X).PosSemidef :=
  fun _ hX => hPhi.IsPositive hX

variable {c : Type w}
variable [Fintype c] [DecidableEq c]

/-- Composition of Kraus-form maps is again a Kraus-form map, with pairwise
products of Kraus operators. -/
theorem ofKraus_comp_ofKraus {κ : Type x} {ι : Type y} [Fintype κ] [Fintype ι]
    (L : ι → Matrix c b ℂ) (K : κ → Matrix b a ℂ) :
    (ofKraus L).comp (ofKraus K) =
      ofKraus (fun kl : κ × ι => L kl.2 * K kl.1) := by
  ext X i j
  simp [ofKraus, LinearMap.comp_apply, Matrix.sum_apply, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]
  rw [← Finset.univ_product_univ, Finset.sum_product]

/-- Complete positivity is stable under composition of finite matrix maps. -/
theorem isCompletelyPositive_comp (Psi : MatrixMap b c) (Phi : MatrixMap a b)
    (hPsi : MatrixMap.IsCompletelyPositive Psi) (hPhi : MatrixMap.IsCompletelyPositive Phi) :
    MatrixMap.IsCompletelyPositive (Psi.comp Phi) :=
  hPhi.comp hPsi

/-- Trace preservation is stable under composition of finite matrix maps. -/
theorem isTracePreserving_comp (Psi : MatrixMap b c) (Phi : MatrixMap a b)
    (hPsi : MatrixMap.IsTracePreserving Psi) (hPhi : MatrixMap.IsTracePreserving Phi) :
    MatrixMap.IsTracePreserving (Psi.comp Phi) :=
  _root_.MatrixMap.IsTracePreserving.comp hPhi hPsi

variable {c : Type w} {d : Type x}
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

/-- Entrywise action of a Kronecker product of matrix maps, with the output indices given by
their projections rather than as explicit pairs. This is `MatrixMap.kron_def` reassociated so
that the input entry comes first. -/
theorem kron_apply (Phi : MatrixMap a b) (Psi : MatrixMap c d) (X : CMatrix (a × c))
    (bd bd' : b × d) :
    MatrixMap.kron Phi Psi X bd bd' =
      ∑ j : c, ∑ j' : c, ∑ i : a, ∑ i' : a,
        X (i, j) (i', j') * Phi (Matrix.single i i' (1 : ℂ)) bd.1 bd'.1 *
          Psi (Matrix.single j j' (1 : ℂ)) bd.2 bd'.2 := by
  obtain ⟨y, w⟩ := bd
  obtain ⟨y', w'⟩ := bd'
  rw [MatrixMap.kron_def]
  symm
  simp only [Finset.sum_comm (s := (Finset.univ : Finset c)) (t := (Finset.univ : Finset a))]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Entrywise action of a matrix map tensored with the identity map: the
`((j, r0), (l, s0))` entry is the sum of the `((i, r0), (i', s0))` entries
weighted by the `(j, l)` entries of the images of the matrix units. -/
theorem kron_id_apply (Phi : MatrixMap a b) (X : CMatrix (a × c))
    (j l : b) (r0 s0 : c) :
    MatrixMap.kron Phi LinearMap.id X (j, r0) (l, s0) =
      ∑ i : a, ∑ i' : a, X (i, r0) (i', s0) *
        (Phi (Matrix.single i i' (1 : ℂ))) j l := by
  rw [MatrixMap.kron_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.sum_eq_single r0]
  · rw [Finset.sum_eq_single s0]
    · simp [Matrix.single, mul_comm]
    · intro s1 _ hs1
      simp [Matrix.single, hs1]
    · intro hnot
      simp at hnot
  · intro r1 _ hr1
    refine Finset.sum_eq_zero fun s1 _ => ?_
    simp [Matrix.single, hr1]
  · intro hnot
    simp at hnot

/-- Trace of the product map on a product matrix unit. -/
theorem trace_kron_single (Phi : MatrixMap a b) (Psi : MatrixMap c d)
    (i i' : a) (j j' : c) :
    (MatrixMap.kron Phi Psi (Matrix.single (i, j) (i', j') (1 : ℂ))).trace =
      (Phi (Matrix.single i i' (1 : ℂ))).trace *
        (Psi (Matrix.single j j' (1 : ℂ))).trace := by
  rw [single_prod_eq_kronecker_single]
  simp only [Matrix.kronecker]
  rw [MatrixMap.kron_map_of_kron_state]
  exact Matrix.trace_kronecker _ _

/-- Choi matrix of a Kronecker product of matrix maps, up to the product-index
reordering between `((a × c) × (b × d))` and `((a × b) × (c × d))`. -/
theorem choi_kron (Phi : MatrixMap a b) (Psi : MatrixMap c d) :
    choi (MatrixMap.kron Phi Psi) =
      (Matrix.kronecker (choi Phi) (choi Psi)).submatrix
        (fun x : (a × c) × (b × d) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
        (fun x : (a × c) × (b × d) => ((x.1.1, x.2.1), (x.1.2, x.2.2))) := by
  ext acbd acbd'
  simp only [choi, Matrix.submatrix_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [single_prod_eq_kronecker_single acbd.1.1 acbd'.1.1 acbd.1.2 acbd'.1.2]
  simp only [Matrix.kronecker]
  rw [MatrixMap.kron_map_of_kron_state]
  rfl

/-- The Kronecker product distributes over a finite sum in its left factor. -/
theorem kron_sum_left {ι : Type y} [Fintype ι]
    (Phi : ι → MatrixMap a b) (Psi : MatrixMap c d) :
    MatrixMap.kron (∑ i, Phi i) Psi = ∑ i, MatrixMap.kron (Phi i) Psi := by
  classical
  have hsum : ∀ s : Finset ι,
      MatrixMap.kron (∑ i ∈ s, Phi i) Psi = ∑ i ∈ s, MatrixMap.kron (Phi i) Psi := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [MatrixMap.zero_kron]
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        rw [MatrixMap.add_kron, ih]
  simpa using hsum Finset.univ

end MatrixMap

end

end QIT
