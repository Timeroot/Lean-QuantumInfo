/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.SmoothEndpoint.Normalized

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal Pointwise
open scoped Topology
open Matrix
open Set Filter

namespace QIT

universe u v w x

noncomputable section


namespace ReferenceIsometry

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]


private theorem submatrix_equiv_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A B : CMatrix κ) :
    (A * B).submatrix e e = A.submatrix e e * B.submatrix e e := by
  classical
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  exact (Fintype.sum_equiv e
    (fun x => A (e i) (e x) * B (e x) (e j))
    (fun y => A (e i) y * B y (e j))
    (by simp)).symm

private theorem eq_of_submatrix_equiv_eq {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    {A B : CMatrix κ} (h : A.submatrix e e = B.submatrix e e) :
    A = B := by
  ext i j
  have hij := congrFun (congrFun h (e.symm i)) (e.symm j)
  simpa using hij

private theorem applyMatrixRight_sumInr_sandwich_submatrix_prodSumRightEquiv
    {extra : Type w} [Fintype extra] [DecidableEq extra]
    (A : CMatrix (Prod a b)) (Y : CMatrix (Prod a (Sum extra b))) :
    (((ReferenceIsometry.sumInr extra b).applyMatrixRight A) * Y *
        ((ReferenceIsometry.sumInr extra b).applyMatrixRight A)).submatrix
        (prodSumRightEquiv a extra b) (prodSumRightEquiv a extra b) =
      Matrix.fromBlocks (0 : CMatrix (Prod a extra)) 0 0
        (A * Matrix.sumBlock22 (Y.submatrix
          (prodSumRightEquiv a extra b) (prodSumRightEquiv a extra b)) * A) := by
  rw [submatrix_equiv_mul, submatrix_equiv_mul]
  rw [applyMatrixRight_sumInr_submatrix_prodSumRightEquiv]
  rw [← Matrix.fromBlocks_sumBlocks
    (Y.submatrix (prodSumRightEquiv a extra b) (prodSumRightEquiv a extra b))]
  rw [Matrix.fromBlocks_multiply]
  rw [Matrix.fromBlocks_multiply]
  ext x y
  cases x <;> cases y
  all_goals
    simp [Matrix.sumBlock11, Matrix.sumBlock12, Matrix.sumBlock21, Matrix.sumBlock22,
      Matrix.fromBlocks, Matrix.submatrix]

private theorem applyMatrixRight_sumInr_sandwich
    {extra : Type w} [Fintype extra] [DecidableEq extra]
    (A : CMatrix (Prod a b)) (Y : CMatrix (Prod a (Sum extra b))) :
    ((ReferenceIsometry.sumInr extra b).applyMatrixRight A) * Y *
        ((ReferenceIsometry.sumInr extra b).applyMatrixRight A) =
      (ReferenceIsometry.sumInr extra b).applyMatrixRight
        (A * Matrix.sumBlock22 (Y.submatrix
          (prodSumRightEquiv a extra b) (prodSumRightEquiv a extra b)) * A) := by
  apply eq_of_submatrix_equiv_eq (prodSumRightEquiv a extra b)
  rw [applyMatrixRight_sumInr_sandwich_submatrix_prodSumRightEquiv]
  rw [applyMatrixRight_sumInr_submatrix_prodSumRightEquiv]

end ReferenceIsometry

namespace SubnormalizedState

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Every subnormalized finite-dimensional state is bounded above by the
identity operator. -/
theorem matrix_le_one (ρ : SubnormalizedState a) :
    ρ.matrix ≤ 1 := by
  have htrace :
      ρ.matrix ≤ (((ρ.matrix.trace.re : ℝ) : ℂ) • (1 : CMatrix a)) :=
    State.posSemidef_le_trace_re_smul_one ρ.pos
  have htrace_le_one :
      (((ρ.matrix.trace.re : ℝ) : ℂ) • (1 : CMatrix a)) ≤ 1 := by
    rw [Matrix.le_iff]
    have hdiff :
        (1 : CMatrix a) - (((ρ.matrix.trace.re : ℝ) : ℂ) • (1 : CMatrix a)) =
          (((1 - ρ.matrix.trace.re : ℝ) : ℂ) • (1 : CMatrix a)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    rw [hdiff]
    have hscalar : (0 : ℂ) ≤ (((1 - ρ.matrix.trace.re : ℝ) : ℝ) : ℂ) := by
      exact_mod_cast sub_nonneg.mpr ρ.trace_le_one
    exact Matrix.PosSemidef.smul Matrix.PosSemidef.one hscalar
  exact le_trans htrace htrace_le_one

/-! ## Subnormalized conditional min-entropy scale -/

/-- Feasibility for the raw side-operator form of subnormalized conditional
min-entropy:
`ρ_AB ≤ I_A ⊗ T_B`, with `T_B ≥ 0`. -/
def ConditionalMinEntropyScaleFeasible
    (ρ : SubnormalizedState (Prod a b)) (T : CMatrix b) : Prop :=
  T.PosSemidef ∧ ρ.matrix ≤ Matrix.kronecker (1 : CMatrix a) T

@[simp]
theorem ConditionalMinEntropyScaleFeasible_eq
    (ρ : SubnormalizedState (Prod a b)) (T : CMatrix b) :
    ConditionalMinEntropyScaleFeasible (a := a) ρ T ↔
      T.PosSemidef ∧ ρ.matrix ≤ Matrix.kronecker (1 : CMatrix a) T :=
  Iff.rfl

/-- Conditioning-register isometries transport raw subnormalized
conditional-min feasible side operators. -/
theorem ConditionalMinEntropyScaleFeasible.apply_conditioningIsometry
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    {ρ : SubnormalizedState (Prod a b)} {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T)
    (V : ReferenceIsometry b bPlus) :
    ConditionalMinEntropyScaleFeasible (a := a) (ρ.conditioningIsometryApply V)
      (MatrixMap.ofReferenceIsometry V T) := by
  constructor
  · exact MatrixMap.isCompletelyPositive_mapsPositive
      (MatrixMap.ofReferenceIsometry V)
      (MatrixMap.ofReferenceIsometry_isCompletelyPositive V) T hT.1
  · let Φ : MatrixMap (Prod a b) (Prod a bPlus) :=
      MatrixMap.kron (Channel.idChannel a).map (MatrixMap.ofReferenceIsometry V)
    have hCP : MatrixMap.IsCompletelyPositive Φ :=
      MatrixMap.isCompletelyPositive_kron (Channel.idChannel a).map
        (MatrixMap.ofReferenceIsometry V)
        (Channel.idChannel a).completelyPositive
        (MatrixMap.ofReferenceIsometry_isCompletelyPositive V)
    have hdiff : (Matrix.kronecker (1 : CMatrix a) T - ρ.matrix).PosSemidef := hT.2
    have hmap := MatrixMap.isCompletelyPositive_mapsPositive Φ hCP
      (Matrix.kronecker (1 : CMatrix a) T - ρ.matrix) hdiff
    change ((Matrix.kronecker (1 : CMatrix a)
        (MatrixMap.ofReferenceIsometry V T)) -
        (ρ.conditioningIsometryApply V).matrix).PosSemidef
    rw [conditioningIsometryApply_matrix]
    convert hmap using 1
    simp only [Φ, map_sub]
    rw [MatrixMap.kron_apply_kronecker]
    rw [MatrixMap.kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight]
    simp [Channel.idChannel, MatrixMap.ofKraus]

private theorem trace_re_mul_le_trace_re_mul_of_le
    {c : Type*} [Fintype c] [DecidableEq c]
    {D X Y : CMatrix c} (hD : D.PosSemidef) (hXY : X ≤ Y) :
    ((D * X).trace).re ≤ ((D * Y).trace).re := by
  have hdiff : (Y - X).PosSemidef := Matrix.le_iff.mp hXY
  have hnonneg : 0 ≤ ((D * (Y - X)).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg hD hdiff
  have htrace :
      ((D * (Y - X)).trace).re =
        ((D * Y).trace).re - ((D * X).trace).re := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  linarith

private theorem referenceIsometry_rangeProjection_le_one
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (V : ReferenceIsometry b bPlus) :
    V.matrix * Matrix.conjTranspose V.matrix ≤ (1 : CMatrix bPlus) := by
  rw [Matrix.le_iff]
  exact MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent
    (V.matrix * Matrix.conjTranspose V.matrix)
    (Matrix.posSemidef_self_mul_conjTranspose V.matrix)
    (by
      calc
        (V.matrix * Matrix.conjTranspose V.matrix) *
            (V.matrix * Matrix.conjTranspose V.matrix) =
          V.matrix * (Matrix.conjTranspose V.matrix * V.matrix) *
            Matrix.conjTranspose V.matrix := by
            simp [Matrix.mul_assoc]
        _ = V.matrix * Matrix.conjTranspose V.matrix := by
            rw [V.isometry]
            simp)

omit [Fintype b] [DecidableEq b] in
private theorem referenceIsometry_applyMatrix_kronecker_one_right_eq
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    (V : ReferenceIsometry a aPlus) (T : CMatrix b) :
    V.applyMatrix (Matrix.kronecker (1 : CMatrix a) T) =
      Matrix.kronecker (V.matrix * Matrix.conjTranspose V.matrix) T := by
  ext x y
  simp [ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.mul_apply,
    Matrix.one_apply, mul_assoc, mul_comm]
  rw [Finset.mul_sum]

omit [DecidableEq b] in
private theorem referenceIsometry_applyMatrix_kronecker_one_right_le
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    (V : ReferenceIsometry a aPlus) {T : CMatrix b} (hT : T.PosSemidef) :
    V.applyMatrix (Matrix.kronecker (1 : CMatrix a) T) ≤
      Matrix.kronecker (1 : CMatrix aPlus) T := by
  rw [Matrix.le_iff]
  have hproj :
      ((1 : CMatrix aPlus) - V.matrix * Matrix.conjTranspose V.matrix).PosSemidef := by
    simpa [Matrix.le_iff] using
      (referenceIsometry_rangeProjection_le_one (b := a) V)
  have hkr : (Matrix.kronecker
      ((1 : CMatrix aPlus) - V.matrix * Matrix.conjTranspose V.matrix) T).PosSemidef :=
    hproj.kronecker hT
  rw [referenceIsometry_applyMatrix_kronecker_one_right_eq]
  convert hkr using 1
  ext x y
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sub_apply, sub_mul]

/-- Apply a finite reference isometry to the source/left register of a
subnormalized state on `A × B`. -/
def sourceIsometryApply
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry a aPlus) :
    SubnormalizedState (Prod aPlus b) :=
  ρ.applyTraceNonincreasingCP
    (MatrixMap.kron (MatrixMap.ofReferenceIsometry V) (Channel.idChannel b).map)
    (MatrixMap.traceNonincreasingCP_kron_id
      (a := b) (hΦ := MatrixMap.ofReferenceIsometry_traceNonincreasingCP V))

@[simp]
theorem sourceIsometryApply_matrix
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry a aPlus) :
    (ρ.sourceIsometryApply V).matrix = V.applyMatrix ρ.matrix := by
  simp [sourceIsometryApply,
    MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft]

@[simp]
theorem sourceIsometryApply_trace_re
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry a aPlus) :
    (ρ.sourceIsometryApply V).matrix.trace.re = ρ.matrix.trace.re := by
  rw [sourceIsometryApply, applyTraceNonincreasingCP_matrix]
  have hTP := MatrixMap.isTracePreserving_kron (MatrixMap.ofReferenceIsometry V)
    (Channel.idChannel b).map
    (MatrixMap.ofReferenceIsometry_isTracePreserving V)
    (Channel.idChannel b).tracePreserving
  exact congrArg Complex.re (hTP ρ.matrix)

/-- Source-register isometries transport raw subnormalized conditional-min
feasible side operators without changing the side operator. -/
theorem ConditionalMinEntropyScaleFeasible.apply_sourceIsometry
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    {ρ : SubnormalizedState (Prod a b)} {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T)
    (V : ReferenceIsometry a aPlus) :
    ConditionalMinEntropyScaleFeasible (a := aPlus) (ρ.sourceIsometryApply V) T := by
  constructor
  · exact hT.1
  · let Φ : MatrixMap (Prod a b) (Prod aPlus b) :=
      MatrixMap.kron (MatrixMap.ofReferenceIsometry V) (Channel.idChannel b).map
    have hCP : MatrixMap.IsCompletelyPositive Φ :=
      MatrixMap.isCompletelyPositive_kron (MatrixMap.ofReferenceIsometry V)
        (Channel.idChannel b).map
        (MatrixMap.ofReferenceIsometry_isCompletelyPositive V)
        (Channel.idChannel b).completelyPositive
    have hdiff : (Matrix.kronecker (1 : CMatrix a) T - ρ.matrix).PosSemidef := hT.2
    have hmap := MatrixMap.isCompletelyPositive_mapsPositive Φ hCP
      (Matrix.kronecker (1 : CMatrix a) T - ρ.matrix) hdiff
    have himage :
        (V.applyMatrix (Matrix.kronecker (1 : CMatrix a) T) -
          (ρ.sourceIsometryApply V).matrix).PosSemidef := by
      convert hmap using 1
      simp only [Φ, map_sub]
      rw [MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft]
      rw [MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft]
      rw [sourceIsometryApply_matrix]
    have hsource_le :
        (ρ.sourceIsometryApply V).matrix ≤
          V.applyMatrix (Matrix.kronecker (1 : CMatrix a) T) := by
      simpa [Matrix.le_iff] using himage
    exact hsource_le.trans
      (referenceIsometry_applyMatrix_kronecker_one_right_le (a := a) V hT.1)

/-- Compressing a PSD side operator along an isometric range cannot increase
its trace. -/
theorem trace_re_conjTranspose_referenceIsometry_le
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (V : ReferenceIsometry b bPlus) {TPlus : CMatrix bPlus}
    (hT : TPlus.PosSemidef) :
    ((Matrix.conjTranspose V.matrix * TPlus * V.matrix).trace).re ≤
      TPlus.trace.re := by
  have hle :=
    trace_re_mul_le_trace_re_mul_of_le (D := TPlus)
      (X := V.matrix * Matrix.conjTranspose V.matrix)
      (Y := 1) hT (referenceIsometry_rangeProjection_le_one V)
  rw [Matrix.mul_one] at hle
  calc
    ((Matrix.conjTranspose V.matrix * TPlus * V.matrix).trace).re =
        ((V.matrix * Matrix.conjTranspose V.matrix * TPlus).trace).re := by
      rw [Matrix.trace_mul_cycle]
    _ = ((TPlus * (V.matrix * Matrix.conjTranspose V.matrix)).trace).re := by
      rw [Matrix.trace_mul_comm]
    _ ≤ TPlus.trace.re := hle

theorem referenceIsometry_conjTranspose_traceNonincreasingCP
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (V : ReferenceIsometry b bPlus) :
    MatrixMap.TraceNonincreasingCP
      (MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix)) where
  completelyPositive :=
    MatrixMap.ofKraus_completelyPositive
      (fun _ : Unit => Matrix.conjTranspose V.matrix)
  traceNonincreasing := by
    intro X hX
    simpa [MatrixMap.ofKraus] using
      trace_re_conjTranspose_referenceIsometry_le V hX

omit [Fintype a] [DecidableEq a] in
private theorem referenceIsometry_rightBlock_applyMatrixRight
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (V : ReferenceIsometry b bPlus) (X : CMatrix (Prod a b)) (i j : a) :
    ReferenceIsometry.rightBlock (V.applyMatrixRight X) i j =
      V.matrix * ReferenceIsometry.rightBlock X i j * Matrix.conjTranspose V.matrix := by
  rfl

private theorem referenceIsometry_rightCompression_applyMatrixRight
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (V : ReferenceIsometry b bPlus) (X : CMatrix (Prod a b)) :
    MatrixMap.kron (Channel.idChannel a).map
        (MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix))
        (V.applyMatrixRight X) =
      X := by
  ext x y
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  let B : CMatrix b := ReferenceIsometry.rightBlock X x.1 y.1
  have hblock :
      ReferenceIsometry.rightBlock (V.applyMatrixRight X) x.1 y.1 =
        V.matrix * B * Matrix.conjTranspose V.matrix := by
    rfl
  have hcompress :
      MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix)
          (V.matrix * B * Matrix.conjTranspose V.matrix) =
        B := by
    calc
      MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix)
          (V.matrix * B * Matrix.conjTranspose V.matrix) =
        Matrix.conjTranspose V.matrix *
          (V.matrix * B * Matrix.conjTranspose V.matrix) *
          V.matrix := by
          simp [MatrixMap.ofKraus]
      _ = B := by
          calc
            Matrix.conjTranspose V.matrix *
                (V.matrix * B * Matrix.conjTranspose V.matrix) *
                V.matrix =
              Matrix.conjTranspose V.matrix *
                (V.matrix * B * (Matrix.conjTranspose V.matrix * V.matrix)) := by
                simp [Matrix.mul_assoc]
            _ = Matrix.conjTranspose V.matrix * (V.matrix * B * (1 : CMatrix b)) := by
                rw [V.isometry]
            _ = Matrix.conjTranspose V.matrix * (V.matrix * B) := by
                simp
            _ = (Matrix.conjTranspose V.matrix * V.matrix) * B := by
                rw [Matrix.mul_assoc]
            _ = (1 : CMatrix b) * B := by
                rw [V.isometry]
            _ = B := by
                simp
  change (MatrixMap.ofKraus
      (fun _ : Unit => Matrix.conjTranspose V.matrix)
      (ReferenceIsometry.rightBlock (V.applyMatrixRight X) x.1 y.1)) x.2 y.2 =
    X x y
  rw [hblock, hcompress]
  rfl

private theorem referenceIsometry_leftCompression_applyMatrix
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    (V : ReferenceIsometry a aPlus) (X : CMatrix (Prod a b)) :
    MatrixMap.kron
        (MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix))
        (Channel.idChannel b).map (V.applyMatrix X) =
      X := by
  ext x y
  rw [MatrixMap.kron_idChannel_apply_slice]
  let B : CMatrix a := ReferenceIsometry.targetBlock X x.2 y.2
  have hblock :
      ReferenceIsometry.targetBlock (V.applyMatrix X) x.2 y.2 =
        V.matrix * B * Matrix.conjTranspose V.matrix := by
    rfl
  have hcompress :
      MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix)
          (V.matrix * B * Matrix.conjTranspose V.matrix) =
        B := by
    calc
      MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix)
          (V.matrix * B * Matrix.conjTranspose V.matrix) =
        Matrix.conjTranspose V.matrix *
          (V.matrix * B * Matrix.conjTranspose V.matrix) *
          V.matrix := by
          simp [MatrixMap.ofKraus]
      _ = B := by
          calc
            Matrix.conjTranspose V.matrix *
                (V.matrix * B * Matrix.conjTranspose V.matrix) *
                V.matrix =
              Matrix.conjTranspose V.matrix *
                (V.matrix * B * (Matrix.conjTranspose V.matrix * V.matrix)) := by
                simp [Matrix.mul_assoc]
            _ = Matrix.conjTranspose V.matrix * (V.matrix * B * (1 : CMatrix a)) := by
                rw [V.isometry]
            _ = Matrix.conjTranspose V.matrix * (V.matrix * B) := by
                simp
            _ = (Matrix.conjTranspose V.matrix * V.matrix) * B := by
                rw [Matrix.mul_assoc]
            _ = (1 : CMatrix a) * B := by
                rw [V.isometry]
            _ = B := by
                simp
  change (MatrixMap.ofKraus
      (fun _ : Unit => Matrix.conjTranspose V.matrix)
      (ReferenceIsometry.targetBlock (V.applyMatrix X) x.2 y.2)) x.1 y.1 =
    X x y
  rw [hblock, hcompress]
  rfl

/-- Compress a source-register reference isometry back to the original source
side using the CP map `X ↦ V† X V` on the left tensor factor. -/
def sourceIsometryCompressed
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    (ρPlus : SubnormalizedState (Prod aPlus b)) (V : ReferenceIsometry a aPlus) :
    SubnormalizedState (Prod a b) :=
  ρPlus.applyTraceNonincreasingCP
    (MatrixMap.kron
      (MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix))
      (Channel.idChannel b).map)
    (MatrixMap.traceNonincreasingCP_kron_id (a := b)
      (hΦ := referenceIsometry_conjTranspose_traceNonincreasingCP V))

@[simp]
theorem sourceIsometryCompressed_matrix
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    (ρPlus : SubnormalizedState (Prod aPlus b)) (V : ReferenceIsometry a aPlus) :
    (ρPlus.sourceIsometryCompressed V).matrix =
      MatrixMap.kron
        (MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix))
        (Channel.idChannel b).map ρPlus.matrix :=
  rfl

@[simp]
theorem sourceIsometryCompressed_sourceIsometryApply
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry a aPlus) :
    (ρ.sourceIsometryApply V).sourceIsometryCompressed V = ρ := by
  apply SubnormalizedState.ext
  rw [sourceIsometryCompressed_matrix, sourceIsometryApply_matrix]
  exact referenceIsometry_leftCompression_applyMatrix V ρ.matrix

/-- Feasible side operators on an arbitrarily isometrically enlarged
conditioning register compress back by `T ↦ V† T V`. -/
theorem ConditionalMinEntropyScaleFeasible.compress_conditioningIsometry
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    {ρ : SubnormalizedState (Prod a b)} {TPlus : CMatrix bPlus}
    (V : ReferenceIsometry b bPlus)
    (hT : ConditionalMinEntropyScaleFeasible (a := a)
      (ρ.conditioningIsometryApply V) TPlus) :
    ConditionalMinEntropyScaleFeasible (a := a) ρ
      (Matrix.conjTranspose V.matrix * TPlus * V.matrix) := by
  constructor
  · exact Matrix.PosSemidef.conjTranspose_mul_mul_same hT.1 V.matrix
  · let Γ : MatrixMap bPlus b :=
      MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix)
    let Φ : MatrixMap (Prod a bPlus) (Prod a b) :=
      MatrixMap.kron (Channel.idChannel a).map Γ
    have hCP : MatrixMap.IsCompletelyPositive Φ :=
      MatrixMap.isCompletelyPositive_kron (Channel.idChannel a).map Γ
        (Channel.idChannel a).completelyPositive
        (MatrixMap.ofKraus_completelyPositive
          (fun _ : Unit => Matrix.conjTranspose V.matrix))
    have hdiff :
        (Matrix.kronecker (1 : CMatrix a) TPlus -
          (ρ.conditioningIsometryApply V).matrix).PosSemidef := hT.2
    have hmap := MatrixMap.isCompletelyPositive_mapsPositive Φ hCP
      (Matrix.kronecker (1 : CMatrix a) TPlus -
        (ρ.conditioningIsometryApply V).matrix) hdiff
    change (Matrix.kronecker (1 : CMatrix a)
        (Matrix.conjTranspose V.matrix * TPlus * V.matrix) -
        ρ.matrix).PosSemidef
    convert hmap using 1
    rw [conditioningIsometryApply_matrix]
    simp only [Φ, Γ, map_sub]
    rw [MatrixMap.kron_apply_kronecker]
    rw [referenceIsometry_rightCompression_applyMatrixRight]
    simp [Channel.idChannel, MatrixMap.ofKraus]

private theorem referenceIsometry_leftCompression_one
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    (V : ReferenceIsometry a aPlus) :
    MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix)
      (1 : CMatrix aPlus) = (1 : CMatrix a) := by
  simp [MatrixMap.ofKraus, V.isometry]

/-- Feasible side operators on an arbitrarily isometrically enlarged source
register compress back without changing the conditioning side operator. -/
theorem ConditionalMinEntropyScaleFeasible.sourceIsometryCompressed
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    {ρPlus : SubnormalizedState (Prod aPlus b)} {T : CMatrix b}
    (V : ReferenceIsometry a aPlus)
    (hT : ConditionalMinEntropyScaleFeasible (a := aPlus) ρPlus T) :
    ConditionalMinEntropyScaleFeasible (a := a) (ρPlus.sourceIsometryCompressed V) T := by
  constructor
  · exact hT.1
  · let Γ : MatrixMap aPlus a :=
      MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix)
    let Φ : MatrixMap (Prod aPlus b) (Prod a b) :=
      MatrixMap.kron Γ (Channel.idChannel b).map
    have hCP : MatrixMap.IsCompletelyPositive Φ :=
      MatrixMap.isCompletelyPositive_kron Γ (Channel.idChannel b).map
        (MatrixMap.ofKraus_completelyPositive
          (fun _ : Unit => Matrix.conjTranspose V.matrix))
        (Channel.idChannel b).completelyPositive
    have hdiff :
        (Matrix.kronecker (1 : CMatrix aPlus) T - ρPlus.matrix).PosSemidef := hT.2
    have hmap := MatrixMap.isCompletelyPositive_mapsPositive Φ hCP
      (Matrix.kronecker (1 : CMatrix aPlus) T - ρPlus.matrix) hdiff
    change (Matrix.kronecker (1 : CMatrix a) T -
        (ρPlus.sourceIsometryCompressed V).matrix).PosSemidef
    convert hmap using 1
    rw [sourceIsometryCompressed_matrix]
    simp only [Φ, Γ, map_sub]
    rw [MatrixMap.kron_apply_kronecker]
    rw [referenceIsometry_leftCompression_one]
    simp [Channel.idChannel, MatrixMap.ofKraus]

/-- For concrete right-summand padding, feasible enlarged side operators
compress back to feasible old side operators by taking the lower-right block. -/
theorem ConditionalMinEntropyScaleFeasible.compress_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {ρ : SubnormalizedState (Prod a b)} {TPlus : CMatrix (Sum extra b)}
    (hT : ConditionalMinEntropyScaleFeasible (a := a)
      (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)) TPlus) :
    ConditionalMinEntropyScaleFeasible (a := a) ρ (Matrix.sumBlock22 TPlus) := by
  constructor
  · exact Matrix.sumBlock22_posSemidef hT.1
  · have hsub := hT.2.submatrix (fun x : Prod a b => (x.1, Sum.inr x.2))
    change (Matrix.kronecker (1 : CMatrix a) (Matrix.sumBlock22 TPlus) -
      ρ.matrix).PosSemidef
    convert hsub using 1
    ext x y
    simp [Matrix.kronecker, Matrix.sumBlock22, conditioningIsometryApply_matrix,
      ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
      ReferenceIsometry.sumInr, Matrix.mul_apply]

/-- Compressing an arbitrary concrete right-summand conditioning register
preserves raw subnormalized conditional-min feasibility. -/
theorem ConditionalMinEntropyScaleFeasible.conditioningSumInrCompressed
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {ρPlus : SubnormalizedState (Prod a (Sum extra b))}
    {TPlus : CMatrix (Sum extra b)}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρPlus TPlus) :
    ConditionalMinEntropyScaleFeasible (a := a) ρPlus.conditioningSumInrCompressed
      (MatrixMap.sumInrBlockCompression (extra := extra) (α := b) TPlus) := by
  constructor
  · exact (MatrixMap.sumInrBlockCompression_traceNonincreasingCP
      (extra := extra) (α := b)).mapsPositive TPlus hT.1
  · let Φ : MatrixMap (Prod a (Sum extra b)) (Prod a b) :=
      MatrixMap.kron (Channel.idChannel a).map
        (MatrixMap.sumInrBlockCompression (extra := extra) (α := b))
    have hCP : MatrixMap.IsCompletelyPositive Φ :=
      MatrixMap.isCompletelyPositive_kron (Channel.idChannel a).map
        (MatrixMap.sumInrBlockCompression (extra := extra) (α := b))
        (Channel.idChannel a).completelyPositive
        (MatrixMap.sumInrBlockCompression_traceNonincreasingCP
          (extra := extra) (α := b)).completelyPositive
    have hdiff : (Matrix.kronecker (1 : CMatrix a) TPlus - ρPlus.matrix).PosSemidef := hT.2
    have hmap := MatrixMap.isCompletelyPositive_mapsPositive Φ hCP
      (Matrix.kronecker (1 : CMatrix a) TPlus - ρPlus.matrix) hdiff
    change (Matrix.kronecker (1 : CMatrix a)
        (MatrixMap.sumInrBlockCompression (extra := extra) (α := b) TPlus) -
        ρPlus.conditioningSumInrCompressed.matrix).PosSemidef
    rw [conditioningSumInrCompressed_matrix]
    convert hmap using 1
    simp only [Φ, map_sub]
    rw [MatrixMap.kron_apply_kronecker]
    simp [Channel.idChannel, MatrixMap.ofKraus]

/-- The raw endpoint scale
`inf {Tr T_B | T_B ≥ 0, ρ_AB ≤ I_A ⊗ T_B}` for subnormalized states. -/
def conditionalMinEntropyScale (ρ : SubnormalizedState (Prod a b)) : ℝ :=
  sInf {t : ℝ | ∃ T : CMatrix b,
    ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re}

@[simp]
theorem conditionalMinEntropyScale_eq (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMinEntropyScale =
      sInf {t : ℝ | ∃ T : CMatrix b,
        ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re} :=
  rfl

/-- The raw side-operator scale values
`Tr T_B` with `T_B ≥ 0` and `ρ_AB ≤ I_A ⊗ T_B`. -/
def conditionalMinEntropyScaleValueSet (ρ : SubnormalizedState (Prod a b)) : Set ℝ :=
  {t : ℝ | ∃ T : CMatrix b,
    ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re}

@[simp]
theorem conditionalMinEntropyScaleValueSet_eq (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMinEntropyScaleValueSet (a := a) =
      {t : ℝ | ∃ T : CMatrix b,
        ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re} :=
  rfl

theorem conditionalMinEntropyScale_eq_sInf_scaleValueSet
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMinEntropyScale =
      sInf (ρ.conditionalMinEntropyScaleValueSet (a := a)) :=
  rfl

theorem conditionalMinEntropyScaleFeasible_trace_nonneg
    {ρ : SubnormalizedState (Prod a b)} {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T) :
    0 ≤ T.trace.re :=
  (Matrix.PosSemidef.trace_nonneg hT.1).1

theorem conditionalMinEntropyScaleValueSet_nonempty
    (ρ : SubnormalizedState (Prod a b)) :
    (ρ.conditionalMinEntropyScaleValueSet (a := a)).Nonempty := by
  let T : CMatrix b := 1
  refine ⟨T.trace.re, T, ?_, rfl⟩
  constructor
  · exact Matrix.PosSemidef.one
  · simpa [T, Matrix.one_kronecker_one] using ρ.matrix_le_one

theorem conditionalMinEntropyScaleValueSet_nonneg
    {ρ : SubnormalizedState (Prod a b)} {t : ℝ}
    (ht : t ∈ ρ.conditionalMinEntropyScaleValueSet (a := a)) :
    0 ≤ t := by
  rcases ht with ⟨T, hT, rfl⟩
  exact conditionalMinEntropyScaleFeasible_trace_nonneg (a := a) hT

theorem conditionalMinEntropyScaleValueSet_bddBelow
    (ρ : SubnormalizedState (Prod a b)) :
    BddBelow (ρ.conditionalMinEntropyScaleValueSet (a := a)) := by
  refine ⟨0, ?_⟩
  intro t ht
  exact conditionalMinEntropyScaleValueSet_nonneg (a := a) ht

theorem conditionalMinEntropyScale_nonneg
    (ρ : SubnormalizedState (Prod a b)) :
    0 ≤ ρ.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  exact le_csInf (ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a))
    (fun t ht => conditionalMinEntropyScaleValueSet_nonneg (a := a) ht)

/-- Enlarging the conditioning register by an isometry cannot increase the raw
subnormalized conditional-min endpoint scale. -/
theorem conditionalMinEntropyScale_conditioningIsometryApply_le
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).conditionalMinEntropyScale (a := a) ≤
      ρ.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf (ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
  intro t ht
  rcases ht with ⟨T, hT, rfl⟩
  have hbddNew :
      BddBelow ((ρ.conditioningIsometryApply V).conditionalMinEntropyScaleValueSet
        (a := a)) :=
    (ρ.conditioningIsometryApply V).conditionalMinEntropyScaleValueSet_bddBelow
      (a := a)
  exact csInf_le hbddNew
    ⟨MatrixMap.ofReferenceIsometry V T,
      hT.apply_conditioningIsometry V,
      (State.trace_ofReferenceIsometry_apply V T).symm⟩

/-- Enlarging the source register by an isometry cannot increase the raw
subnormalized conditional-min endpoint scale. -/
theorem conditionalMinEntropyScale_sourceIsometryApply_le
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry a aPlus) :
    (ρ.sourceIsometryApply V).conditionalMinEntropyScale (a := aPlus) ≤
      ρ.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf (ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
  intro t ht
  rcases ht with ⟨T, hT, rfl⟩
  have hbddNew :
      BddBelow ((ρ.sourceIsometryApply V).conditionalMinEntropyScaleValueSet
        (a := aPlus)) :=
    (ρ.sourceIsometryApply V).conditionalMinEntropyScaleValueSet_bddBelow
      (a := aPlus)
  exact csInf_le hbddNew ⟨T, hT.apply_sourceIsometry V, rfl⟩

/-- For concrete right-summand padding, the raw subnormalized conditional-min
endpoint scale also cannot decrease. -/
theorem conditionalMinEntropyScale_le_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMinEntropyScale (a := a) ≤
      (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropyScale
        (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf
    ((ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropyScaleValueSet_nonempty
      (a := a)) ?_
  intro t ht
  rcases ht with ⟨TPlus, hTPlus, rfl⟩
  have hbddOld : BddBelow (ρ.conditionalMinEntropyScaleValueSet (a := a)) :=
    ρ.conditionalMinEntropyScaleValueSet_bddBelow (a := a)
  exact le_trans
    (csInf_le hbddOld
      ⟨Matrix.sumBlock22 TPlus, hTPlus.compress_sumInr, rfl⟩)
    (State.sumBlock22_trace_re_le_of_posSemidef TPlus hTPlus.1)

/-- The raw subnormalized conditional-min endpoint scale cannot decrease when
compressing side operators back from an arbitrary conditioning-register
isometry. -/
theorem conditionalMinEntropyScale_le_conditioningIsometryApply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry b bPlus) :
    ρ.conditionalMinEntropyScale (a := a) ≤
      (ρ.conditioningIsometryApply V).conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf
    ((ρ.conditioningIsometryApply V).conditionalMinEntropyScaleValueSet_nonempty
      (a := a)) ?_
  intro t ht
  rcases ht with ⟨TPlus, hTPlus, rfl⟩
  have hbddOld : BddBelow (ρ.conditionalMinEntropyScaleValueSet (a := a)) :=
    ρ.conditionalMinEntropyScaleValueSet_bddBelow (a := a)
  exact le_trans
    (csInf_le hbddOld
      ⟨Matrix.conjTranspose V.matrix * TPlus * V.matrix,
        hTPlus.compress_conditioningIsometry V, rfl⟩)
    (trace_re_conjTranspose_referenceIsometry_le V hTPlus.1)

/-- The raw subnormalized conditional-min endpoint scale cannot decrease when
compressing source-register isometries back to the original source. -/
theorem conditionalMinEntropyScale_le_sourceIsometryApply
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry a aPlus) :
    ρ.conditionalMinEntropyScale (a := a) ≤
      (ρ.sourceIsometryApply V).conditionalMinEntropyScale (a := aPlus) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf
    ((ρ.sourceIsometryApply V).conditionalMinEntropyScaleValueSet_nonempty
      (a := aPlus)) ?_
  intro t ht
  rcases ht with ⟨TPlus, hTPlus, rfl⟩
  have hbddOld : BddBelow (ρ.conditionalMinEntropyScaleValueSet (a := a)) :=
    ρ.conditionalMinEntropyScaleValueSet_bddBelow (a := a)
  have hcompressed : ConditionalMinEntropyScaleFeasible (a := a) ρ TPlus := by
    simpa using hTPlus.sourceIsometryCompressed V
  exact csInf_le hbddOld ⟨TPlus, hcompressed, rfl⟩

/-- Compressing an arbitrary right-summand conditioning register cannot raise
the raw subnormalized conditional-min endpoint scale. -/
theorem conditionalMinEntropyScale_conditioningSumInrCompressed_le
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρPlus : SubnormalizedState (Prod a (Sum extra b))) :
    ρPlus.conditioningSumInrCompressed.conditionalMinEntropyScale (a := a) ≤
      ρPlus.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf (ρPlus.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
  intro t ht
  rcases ht with ⟨TPlus, hTPlus, rfl⟩
  have hbddCompressed :
      BddBelow
        (ρPlus.conditioningSumInrCompressed.conditionalMinEntropyScaleValueSet
          (a := a)) :=
    ρPlus.conditioningSumInrCompressed.conditionalMinEntropyScaleValueSet_bddBelow
      (a := a)
  have htrace_le :
      ((MatrixMap.sumInrBlockCompression (extra := extra) (α := b) TPlus).trace.re) ≤
        TPlus.trace.re :=
    (MatrixMap.sumInrBlockCompression_traceNonincreasingCP
      (extra := extra) (α := b)).traceNonincreasing TPlus hTPlus.1
  exact le_trans
    (csInf_le hbddCompressed
      ⟨MatrixMap.sumInrBlockCompression (extra := extra) (α := b) TPlus,
        hTPlus.conditioningSumInrCompressed (a := a), rfl⟩)
    htrace_le

theorem conditionalMinEntropyScaleFeasible_trace_lower_bound [Nonempty a]
    {ρ : SubnormalizedState (Prod a b)} {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T) :
    ρ.matrix.trace.re / (Fintype.card a : ℝ) ≤ T.trace.re := by
  have htrace := State.trace_re_le_of_le hT.2
  have hright :
      (Matrix.kronecker (1 : CMatrix a) T).trace.re =
        (Fintype.card a : ℝ) * T.trace.re := by
    rw [show Matrix.kronecker (1 : CMatrix a) T =
        Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix a) T by rfl]
    rw [Matrix.trace_kronecker, Matrix.trace_one]
    simp [Complex.mul_re]
  rw [hright] at htrace
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  exact (div_le_iff₀ hcard_pos).mpr (by simpa [mul_comm] using htrace)

theorem conditionalMinEntropyScale_pos_of_trace_pos [Nonempty a]
    {ρ : SubnormalizedState (Prod a b)}
    (hρ : 0 < ρ.matrix.trace.re) :
    0 < ρ.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  have hne := ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a)
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hbound :
      ∀ x ∈ ρ.conditionalMinEntropyScaleValueSet (a := a),
        ρ.matrix.trace.re / (Fintype.card a : ℝ) ≤ x := by
    intro x hx
    rcases hx with ⟨T, hT, rfl⟩
    exact conditionalMinEntropyScaleFeasible_trace_lower_bound (a := a) hT
  exact lt_of_lt_of_le (div_pos hρ hcard_pos) (le_csInf hne hbound)

/-- Feasible conditional-min exponents for subnormalized states. -/
def conditionalMinEntropyFeasibleExponentValueSet
    (ρ : SubnormalizedState (Prod a b)) : Set ℝ :=
  {lam : ℝ | ∃ σ : SubnormalizedState b,
    ConditionalMinEntropyFeasible (a := a) ρ σ lam}

@[simp]
theorem conditionalMinEntropyFeasibleExponentValueSet_eq
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMinEntropyFeasibleExponentValueSet (a := a) =
      {lam : ℝ | ∃ σ : SubnormalizedState b,
        ConditionalMinEntropyFeasible (a := a) ρ σ lam} :=
  rfl

/-- A subnormalized conditional-min feasible pair gives a raw scale-feasible
side operator. Its trace may be smaller than `2^{-λ}` because the side state is
only subnormalized. -/
theorem conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible
    {ρ : SubnormalizedState (Prod a b)} {σ : SubnormalizedState b} {lam : ℝ}
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    ConditionalMinEntropyScaleFeasible (a := a) ρ
      ((Real.rpow 2 (-lam) : ℂ) • σ.matrix) := by
  constructor
  · have hscale : (0 : ℂ) ≤ ((Real.rpow 2 (-lam) : ℝ) : ℂ) := by
      exact_mod_cast (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-lam))
    exact Matrix.PosSemidef.smul σ.pos hscale
  · simpa [ConditionalMinEntropyFeasible, ConditionalMinEntropyScaleFeasible,
      identityTensorStateMatrix, Matrix.kronecker_smul] using h

theorem trace_conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible
    {ρ : SubnormalizedState (Prod a b)} {σ : SubnormalizedState b} {lam : ℝ}
    (_h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    (((Real.rpow 2 (-lam) : ℂ) • σ.matrix).trace).re =
      Real.rpow 2 (-lam) * σ.matrix.trace.re := by
  rw [Matrix.trace_smul]
  simp [Complex.mul_re, σ.trace_im_zero]

theorem conditionalMinEntropyScaleValue_le_exponentScale_of_conditionalMinEntropyFeasible
    {ρ : SubnormalizedState (Prod a b)} {σ : SubnormalizedState b} {lam : ℝ} :
    ConditionalMinEntropyFeasible (a := a) ρ σ lam →
      (((Real.rpow 2 (-lam) : ℂ) • σ.matrix).trace).re ≤ Real.rpow 2 (-lam) := by
  intro h
  rw [trace_conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible
    (a := a) h]
  have hscale_nonneg : 0 ≤ Real.rpow 2 (-lam) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-lam)
  nlinarith [σ.trace_nonneg, σ.trace_le_one, hscale_nonneg]

theorem identityTensorStateMatrix_posSemidef (σ : SubnormalizedState b) :
    (identityTensorStateMatrix (a := a) σ).PosSemidef := by
  change (Matrix.kronecker (1 : CMatrix a) σ.matrix).PosSemidef
  exact Matrix.PosSemidef.one.kronecker σ.pos

/-- A positive-trace raw scale feasible side operator gives a subnormalized
conditional-min feasible exponent at `-log₂ Tr T`. -/
theorem ConditionalMinEntropyFeasible.of_scaleFeasible_trace_pos
    {ρ : SubnormalizedState (Prod a b)} {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T)
    (htr : 0 < T.trace.re) :
    ConditionalMinEntropyFeasible (a := a) ρ
      (State.ofPosSemidefTracePos T hT.1 htr).toSubnormalized
      (-log2 T.trace.re) := by
  rw [ConditionalMinEntropyFeasible]
  have hrpow : Real.rpow 2 (-(-log2 T.trace.re)) = T.trace.re := by
    simpa using rpow_two_log2_pos htr
  have hside :
      ((T.trace.re : ℂ) •
          identityTensorStateMatrix (a := a)
            (State.ofPosSemidefTracePos T hT.1 htr).toSubnormalized) =
        Matrix.kronecker (1 : CMatrix a) T := by
    ext x y
    have htrC : ((T.trace.re : ℂ) ≠ 0) := by
      exact_mod_cast htr.ne'
    simp [identityTensorStateMatrix, State.toSubnormalized,
      State.ofPosSemidefTracePos, Matrix.kronecker, Matrix.kroneckerMap_apply]
    field_simp [htrC]
  rw [hrpow, hside]
  exact hT.2

theorem negLog2_image_conditionalMinEntropyScaleValueSet_eq_of_trace_pos
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b))
    (hρ : 0 < ρ.matrix.trace.re) :
    (fun t : ℝ => -log2 t) ''
        ρ.conditionalMinEntropyScaleValueSet (a := a) =
      ρ.conditionalMinEntropyFeasibleExponentValueSet (a := a) := by
  ext lam
  constructor
  · rintro ⟨t, ⟨T, hT, rfl⟩, rfl⟩
    have htr_pos : 0 < T.trace.re := by
      have hcard_pos : 0 < (Fintype.card a : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
      exact lt_of_lt_of_le (div_pos hρ hcard_pos)
        (conditionalMinEntropyScaleFeasible_trace_lower_bound (a := a) hT)
    exact ⟨(State.ofPosSemidefTracePos T hT.1 htr_pos).toSubnormalized,
      ConditionalMinEntropyFeasible.of_scaleFeasible_trace_pos (a := a) hT htr_pos⟩
  · rintro ⟨σ, hfeas⟩
    let c : ℝ := Real.rpow 2 (-lam)
    let m : State b := State.maximallyMixed b
    let pad : ℝ := c * (1 - σ.matrix.trace.re)
    let T : CMatrix b := (c : ℂ) • σ.matrix + (pad : ℂ) • m.matrix
    have hc_nonneg : 0 ≤ c := by
      dsimp [c]
      exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-lam)
    have hc_pos : 0 < c := by
      dsimp [c]
      exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-lam)
    have hpad_nonneg : 0 ≤ pad := by
      dsimp [pad]
      nlinarith [hc_nonneg, σ.trace_le_one]
    have hTpos : T.PosSemidef := by
      dsimp [T]
      exact Matrix.PosSemidef.add (Matrix.PosSemidef.smul σ.pos hc_nonneg)
        (Matrix.PosSemidef.smul m.pos hpad_nonneg)
    have hpad_id_pos :
        ((pad : ℂ) • identityTensorStateMatrix (a := a) m.toSubnormalized).PosSemidef := by
      have hpadC : (0 : ℂ) ≤ (pad : ℂ) := by exact_mod_cast hpad_nonneg
      exact Matrix.PosSemidef.smul
        (identityTensorStateMatrix_posSemidef (a := a) m.toSubnormalized) hpadC
    have hkr :
        Matrix.kronecker (1 : CMatrix a) T =
          (c : ℂ) • identityTensorStateMatrix (a := a) σ +
            (pad : ℂ) • identityTensorStateMatrix (a := a) m.toSubnormalized := by
      ext x y
      simp [T, identityTensorStateMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
        State.toSubnormalized, mul_add]
      ring
    have hle :
        ρ.matrix ≤ Matrix.kronecker (1 : CMatrix a) T := by
      refine le_trans hfeas ?_
      rw [hkr]
      exact le_add_of_nonneg_right (by simpa [Matrix.le_iff] using hpad_id_pos)
    have htr : T.trace.re = c := by
      dsimp [T, pad]
      rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, m.trace_eq_one]
      simp [Complex.real_smul, σ.trace_im_zero]
      ring
    refine ⟨T.trace.re, ?_, ?_⟩
    · exact ⟨T, ⟨hTpos, hle⟩, rfl⟩
    · rw [htr]
      exact neg_log2_rpow_two_neg lam

theorem conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b))
    (hρ : 0 < ρ.matrix.trace.re) :
    ρ.conditionalMinEntropyRaw =
      -log2 (ρ.conditionalMinEntropyScale (a := a)) := by
  rw [conditionalMinEntropyRaw, conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  change sSup (ρ.conditionalMinEntropyFeasibleExponentValueSet (a := a)) =
    -log2 (sInf (ρ.conditionalMinEntropyScaleValueSet (a := a)))
  rw [← negLog2_image_conditionalMinEntropyScaleValueSet_eq_of_trace_pos (a := a) ρ hρ]
  exact neg_log2_sInf_image_eq
    (ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a))
    (ρ.conditionalMinEntropyScaleValueSet_bddBelow (a := a))
    (ρ.conditionalMinEntropyScale_pos_of_trace_pos (a := a) hρ)

/-- Compressing an arbitrary right-summand conditioning register can only
increase subnormalized conditional min-entropy, when both traces are positive. -/
theorem conditionalMinEntropy_le_conditioningSumInrCompressed
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρPlus : SubnormalizedState (Prod a (Sum extra b)))
    (hPlus : 0 < ρPlus.matrix.trace.re)
    (hCompressed : 0 < ρPlus.conditioningSumInrCompressed.matrix.trace.re) :
    ρPlus.conditionalMinEntropyRaw ≤
      ρPlus.conditioningSumInrCompressed.conditionalMinEntropyRaw := by
  rw [ρPlus.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a) hPlus,
    ρPlus.conditioningSumInrCompressed.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a) hCompressed]
  have hscale_le :=
    ρPlus.conditionalMinEntropyScale_conditioningSumInrCompressed_le
      (a := a) (extra := extra)
  have hcompressed_pos :
      0 <
        ρPlus.conditioningSumInrCompressed.conditionalMinEntropyScale
          (a := a) :=
    ρPlus.conditioningSumInrCompressed.conditionalMinEntropyScale_pos_of_trace_pos
      (a := a) hCompressed
  have hlog :
      log2
          (ρPlus.conditioningSumInrCompressed.conditionalMinEntropyScale
            (a := a)) ≤
        log2 (ρPlus.conditionalMinEntropyScale (a := a)) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hcompressed_pos hscale_le)
      (le_of_lt (Real.log_pos one_lt_two))
  exact neg_le_neg hlog

/-- Subnormalized conditional min-entropy is invariant under the concrete
right-summand reference padding used by embedded purification-ball transport,
for positive-trace states. -/
theorem conditionalMinEntropy_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) (hρ : 0 < ρ.matrix.trace.re) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropyRaw =
      ρ.conditionalMinEntropyRaw := by
  rw [(ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a) (by
        rw [conditioningIsometryApply_trace_re]
        exact hρ),
    ρ.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos (a := a) hρ]
  have hle₁ := ρ.conditionalMinEntropyScale_conditioningIsometryApply_le
    (a := a) (V := ReferenceIsometry.sumInr extra b)
  have hle₂ := ρ.conditionalMinEntropyScale_le_conditioningIsometryApply_sumInr
    (a := a) (extra := extra)
  rw [le_antisymm hle₁ hle₂]

/-- Subnormalized conditional min-entropy is invariant under an arbitrary
conditioning-register reference isometry, for positive-trace states. -/
theorem conditionalMinEntropy_conditioningIsometryApply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    [Nonempty a] [Nonempty b] [Nonempty bPlus]
    (ρ : SubnormalizedState (Prod a b)) (hρ : 0 < ρ.matrix.trace.re)
    (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).conditionalMinEntropyRaw =
      ρ.conditionalMinEntropyRaw := by
  rw [(ρ.conditioningIsometryApply V).conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a) (by
        rw [conditioningIsometryApply_trace_re]
        exact hρ),
    ρ.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos (a := a) hρ]
  have hle₁ := ρ.conditionalMinEntropyScale_conditioningIsometryApply_le
    (a := a) V
  have hle₂ := ρ.conditionalMinEntropyScale_le_conditioningIsometryApply
    (a := a) V
  rw [le_antisymm hle₁ hle₂]

/-- Subnormalized conditional min-entropy is invariant under an arbitrary
source-register reference isometry, for positive-trace states. -/
theorem conditionalMinEntropy_sourceIsometryApply
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    [Nonempty a] [Nonempty b] [Nonempty aPlus]
    (ρ : SubnormalizedState (Prod a b)) (hρ : 0 < ρ.matrix.trace.re)
    (V : ReferenceIsometry a aPlus) :
    (ρ.sourceIsometryApply V).conditionalMinEntropyRaw =
      ρ.conditionalMinEntropyRaw := by
  rw [(ρ.sourceIsometryApply V).conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := aPlus) (by
        rw [sourceIsometryApply_trace_re]
        exact hρ),
    ρ.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos (a := a) hρ]
  have hle₁ := ρ.conditionalMinEntropyScale_sourceIsometryApply_le
    (a := a) V
  have hle₂ := ρ.conditionalMinEntropyScale_le_sourceIsometryApply
    (a := a) V
  rw [le_antisymm hle₁ hle₂]

/-- The subnormalized identity tensor matrix is the constant block-diagonal
matrix with the side-state matrix in every source block. -/
theorem identityTensorStateMatrix_eq_blockDiagonal (σ : SubnormalizedState b) :
    identityTensorStateMatrix (a := a) σ =
      Classical.blockDiagonal fun _ : a => σ.matrix := by
  exact Classical.identityTensor_eq_blockDiagonal σ.matrix

/-- A raw scale-feasible side operator bounds every diagonal source block. -/
theorem block_le_of_conditionalMinEntropyScaleFeasible
    (ρ : SubnormalizedState (Prod a b)) (T : CMatrix b) (x : a)
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T) :
    Classical.block ρ.matrix x x ≤ T := by
  rw [Matrix.le_iff]
  have hdiff :
      (Matrix.kronecker (1 : CMatrix a) T - ρ.matrix).PosSemidef := by
    simpa [Matrix.le_iff] using hT.2
  have hblock := hdiff.submatrix (fun i : b => (x, i))
  have hblock_eq :
      Matrix.submatrix
          (Matrix.kronecker (1 : CMatrix a) T - ρ.matrix)
          (fun i : b => (x, i)) (fun i : b => (x, i)) =
        T - Classical.block ρ.matrix x x := by
    ext i j
    simp [Classical.block, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rwa [hblock_eq] at hblock

/-- Build a subnormalized classical-quantum state from positive semidefinite
diagonal blocks whose total trace is at most one. -/
def ofClassicalBlocks (blocks : a → CMatrix b)
    (hpos : ∀ x, (blocks x).PosSemidef)
    (htrace : (∑ x, (blocks x).trace).re ≤ 1) :
    SubnormalizedState (Prod a b) where
  matrix := Classical.blockDiagonal blocks
  pos := Classical.blockDiagonal_posSemidef blocks hpos
  trace_le_one := by
    simpa using htrace

@[simp]
theorem ofClassicalBlocks_matrix (blocks : a → CMatrix b)
    (hpos : ∀ x, (blocks x).PosSemidef)
    (htrace : (∑ x, (blocks x).trace).re ≤ 1) :
    (ofClassicalBlocks blocks hpos htrace).matrix =
      Classical.blockDiagonal blocks :=
  rfl

@[simp]
theorem ofClassicalBlocks_block_self (blocks : a → CMatrix b)
    (hpos : ∀ x, (blocks x).PosSemidef)
    (htrace : (∑ x, (blocks x).trace).re ≤ 1) (x : a) :
    Classical.block (ofClassicalBlocks blocks hpos htrace).matrix x x =
      blocks x := by
  simp [ofClassicalBlocks]

private def sourceDeterministicPostprocessKraus
    {c : Type*} [Fintype c] [DecidableEq c]
    (g : a → c) (x : a) :
    Matrix (Prod c b) (Prod a b) ℂ :=
  fun out inp => if inp.1 = x ∧ out = (g x, inp.2) then 1 else 0

/-- Matrix map for deterministic coarse-graining of the source classical
register, summing diagonal source blocks along the fibers of `g`. -/
noncomputable def sourceDeterministicPostprocessMap
    {c : Type*} [Fintype c] [DecidableEq c]
    (g : a → c) :
    MatrixMap (Prod a b) (Prod c b) where
  toFun X := fun yi yj =>
    if yi.1 = yj.1 then
      ∑ x : a, if g x = yi.1 then X (x, yi.2) (x, yj.2) else 0
    else 0
  map_add' := by
    intro X Y
    ext yi yj
    rcases yi with ⟨y, i⟩
    rcases yj with ⟨y', j⟩
    by_cases hyy : y = y'
    · subst y'
      simp only [if_true, Matrix.add_apply]
      calc
        (∑ x : a, if g x = y then X (x, i) (x, j) + Y (x, i) (x, j) else 0)
            =
            ∑ x : a,
              ((if g x = y then X (x, i) (x, j) else 0) +
                (if g x = y then Y (x, i) (x, j) else 0)) := by
              refine Finset.sum_congr rfl fun x _ => ?_
              by_cases hx : g x = y <;> simp [hx]
        _ =
            (∑ x : a, if g x = y then X (x, i) (x, j) else 0) +
              ∑ x : a, if g x = y then Y (x, i) (x, j) else 0 := by
              rw [Finset.sum_add_distrib]
    · simp [hyy]
  map_smul' := by
    intro z X
    ext yi yj
    rcases yi with ⟨y, i⟩
    rcases yj with ⟨y', j⟩
    by_cases hyy : y = y'
    · subst y'
      simp only [if_true, Matrix.smul_apply]
      calc
        (∑ x : a, if g x = y then z * X (x, i) (x, j) else 0)
            =
            ∑ x : a, z * (if g x = y then X (x, i) (x, j) else 0) := by
              refine Finset.sum_congr rfl fun x _ => ?_
              by_cases hx : g x = y <;> simp [hx]
        _ =
            z * ∑ x : a, if g x = y then X (x, i) (x, j) else 0 := by
              rw [Finset.mul_sum]
    · simp [hyy]

private theorem sourceDeterministicPostprocessMap_eq_ofKraus
    {c : Type*} [Fintype c] [DecidableEq c]
    (g : a → c) :
    MatrixMap.ofKraus
        (sourceDeterministicPostprocessKraus (a := a) (b := b) g) =
      sourceDeterministicPostprocessMap (a := a) (b := b) g := by
  apply LinearMap.ext
  intro X
  ext yi yj
  rcases yi with ⟨y, i⟩
  rcases yj with ⟨y', j⟩
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    sourceDeterministicPostprocessKraus, sourceDeterministicPostprocessMap]
  simp only [Prod.mk.injEq, ite_mul, zero_mul, one_mul]
  by_cases hyy : y = y'
  · subst y'
    rw [if_pos rfl]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hg : g x = y
    · rw [Finset.sum_eq_single ((x, j) : Prod a b)]
      · rw [Finset.sum_eq_single ((x, i) : Prod a b)]
        · simp [hg]
        · intro inp _ hinp
          rcases inp with ⟨x', i'⟩
          by_cases hleft : x' = x ∧ y = g x ∧ i = i'
          · exact False.elim (hinp (Prod.ext hleft.1 hleft.2.2.symm))
          · simp [hleft]
        · intro hmem
          simp at hmem
      · intro out _ hout
        rcases out with ⟨x', j'⟩
        by_cases hright : x' = x ∧ y = g x ∧ j = j'
        · exact False.elim (hout (Prod.ext hright.1 hright.2.2.symm))
        · simp [hright]
      · intro hmem
        simp at hmem
    · calc
        (∑ out : Prod a b,
            (∑ inp : Prod a b,
                if inp.1 = x ∧ y = g x ∧ i = inp.2 then X inp out else 0) *
              star (if out.1 = x ∧ y = g x ∧ j = out.2 then 1 else 0)) = 0 := by
            apply Finset.sum_eq_zero
            intro out _
            by_cases hright : out.1 = x ∧ y = g x ∧ j = out.2
            · exact False.elim (hg hright.2.1.symm)
            · simp [hright]
        _ = (if g x = y then X (x, i) (x, j) else 0) := by
            simp [hg]
  · rw [if_neg hyy]
    apply Finset.sum_eq_zero
    intro x _
    apply Finset.sum_eq_zero
    intro out _
    by_cases hright : out.1 = x ∧ y' = g x ∧ j = out.2
    · have hleft_none :
          ∀ inp : Prod a b, ¬ (inp.1 = x ∧ y = g x ∧ i = inp.2) := by
        intro inp hleft
        exact hyy (hleft.2.1.trans hright.2.1.symm)
      have hinner :
          (∑ inp : Prod a b,
              if inp.1 = x ∧ y = g x ∧ i = inp.2 then X inp out else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro inp _
        simp [hleft_none inp]
      simp [hright, hinner]
    · simp [hright]

theorem sourceDeterministicPostprocessMap_completelyPositive
    {c : Type*} [Fintype c] [DecidableEq c]
    (g : a → c) :
    MatrixMap.IsCompletelyPositive
      (sourceDeterministicPostprocessMap (a := a) (b := b) g) := by
  rw [← sourceDeterministicPostprocessMap_eq_ofKraus (a := a) (b := b) g]
  exact MatrixMap.ofKraus_completelyPositive _

/-- Deterministic source coarse-graining is the block-diagonal matrix of
fiber sums of the input diagonal source blocks. -/
theorem sourceDeterministicPostprocessMap_apply_eq_blockDiagonal
    {c : Type*} [Fintype c] [DecidableEq c]
    (g : a → c) (X : CMatrix (Prod a b)) :
    sourceDeterministicPostprocessMap (a := a) (b := b) g X =
      Classical.blockDiagonal
        (fun y : c => ∑ x : a, if g x = y then Classical.block X x x else 0) := by
  ext yi yj
  rcases yi with ⟨y, i⟩
  rcases yj with ⟨y', j⟩
  by_cases hyy : y = y'
  · subst y'
    have hblock :=
      congrFun (congrFun
        (Classical.blockDiagonal_block_self
          (fun y : c => ∑ x : a, if g x = y then Classical.block X x x else 0) y) i) j
    calc
      (sourceDeterministicPostprocessMap (a := a) (b := b) g X) (y, i) (y, j) =
          (∑ x : a, if g x = y then Classical.block X x x else 0) i j := by
          simp only [sourceDeterministicPostprocessMap, LinearMap.coe_mk, AddHom.coe_mk,
            Matrix.sum_apply]
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hx : g x = y <;> simp [hx, Classical.block]
      _ = Classical.blockDiagonal
            (fun y : c => ∑ x : a, if g x = y then Classical.block X x x else 0)
            (y, i) (y, j) := hblock.symm
  · have hblock :=
      congrFun (congrFun
        (Classical.blockDiagonal_block_ne
          (fun y : c => ∑ x : a, if g x = y then Classical.block X x x else 0)
          hyy) i) j
    simpa [sourceDeterministicPostprocessMap, Classical.block, hyy] using hblock.symm

theorem sourceDeterministicPostprocessMap_tracePreserving
    {c : Type*} [Fintype c] [DecidableEq c]
    (g : a → c) :
    MatrixMap.IsTracePreserving
      (sourceDeterministicPostprocessMap (a := a) (b := b) g) := by
  intro X
  rw [sourceDeterministicPostprocessMap_apply_eq_blockDiagonal,
    Classical.blockDiagonal_trace]
  calc
    (∑ y : c,
        (∑ x : a, if g x = y then Classical.block X x x else 0).trace) =
        ∑ y : c, ∑ x : a,
          (if g x = y then Classical.block X x x else 0).trace := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Matrix.trace_sum]
    _ = ∑ x : a, ∑ y : c,
          (if g x = y then Classical.block X x x else 0).trace := by
        rw [Finset.sum_comm]
    _ = ∑ x : a, (Classical.block X x x).trace := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_eq_single (g x)]
        · simp
        · intro y _ hy
          rw [if_neg (fun h => hy h.symm)]
          simp
        · simp
    _ = X.trace := Classical.sum_block_trace X

theorem sourceDeterministicPostprocessMap_traceNonincreasingCP
    {c : Type*} [Fintype c] [DecidableEq c]
    (g : a → c) :
    MatrixMap.TraceNonincreasingCP
      (sourceDeterministicPostprocessMap (a := a) (b := b) g) :=
  MatrixMap.traceNonincreasingCP_of_tracePreserving
    (sourceDeterministicPostprocessMap_completelyPositive (a := a) (b := b) g)
    (sourceDeterministicPostprocessMap_tracePreserving (a := a) (b := b) g)

/-- Deterministically coarse-grain the source classical register of a
subnormalized state by summing its diagonal source blocks along `g`. -/
def sourceDeterministicPostprocess
    {c : Type*} [Fintype c] [DecidableEq c]
    (ρ : SubnormalizedState (Prod a b)) (g : a → c) :
    SubnormalizedState (Prod c b) :=
  ofClassicalBlocks
    (fun y => ∑ x, if g x = y then Classical.block ρ.matrix x x else 0)
    (by
      intro y
      exact Matrix.posSemidef_sum Finset.univ fun x _ => by
        by_cases hx : g x = y
        · exact by
            simpa [hx] using ρ.pos.submatrix (fun i : b => (x, i))
        · simpa [hx] using (Matrix.PosSemidef.zero : (0 : CMatrix b).PosSemidef))
    (by
      have htrace :
          (∑ y : c,
              (∑ x : a,
                if g x = y then Classical.block ρ.matrix x x else 0).trace) =
            ∑ x : a, (Classical.block ρ.matrix x x).trace := by
        calc
          (∑ y : c,
              (∑ x : a,
                if g x = y then Classical.block ρ.matrix x x else 0).trace) =
              ∑ y : c, ∑ x : a,
                (if g x = y then Classical.block ρ.matrix x x else 0).trace := by
                refine Finset.sum_congr rfl fun y _ => ?_
                rw [Matrix.trace_sum]
          _ = ∑ x : a, ∑ y : c,
                (if g x = y then Classical.block ρ.matrix x x else 0).trace := by
                rw [Finset.sum_comm]
          _ = ∑ x : a, (Classical.block ρ.matrix x x).trace := by
                refine Finset.sum_congr rfl fun x _ => ?_
                rw [Finset.sum_eq_single (g x)]
                · simp
                · intro y _ hy
                  rw [if_neg (fun h => hy h.symm)]
                  simp
                · simp
      rw [htrace, Classical.sum_block_trace]
      exact ρ.trace_le_one)

@[simp]
theorem sourceDeterministicPostprocess_matrix
    {c : Type*} [Fintype c] [DecidableEq c]
    (ρ : SubnormalizedState (Prod a b)) (g : a → c) :
    (ρ.sourceDeterministicPostprocess g).matrix =
      Classical.blockDiagonal
        (fun y => ∑ x, if g x = y then Classical.block ρ.matrix x x else 0) :=
  rfl

theorem sourceDeterministicPostprocessMap_apply_matrix
    {c : Type*} [Fintype c] [DecidableEq c]
    (ρ : SubnormalizedState (Prod a b)) (g : a → c) :
    sourceDeterministicPostprocessMap (a := a) (b := b) g ρ.matrix =
      (ρ.sourceDeterministicPostprocess g).matrix := by
  rw [sourceDeterministicPostprocessMap_apply_eq_blockDiagonal,
    sourceDeterministicPostprocess_matrix]

/-- The output block of deterministic source coarse-graining is the sum of the
input blocks in that fiber. -/
theorem sourceDeterministicPostprocess_block
    {c : Type*} [Fintype c] [DecidableEq c]
    (ρ : SubnormalizedState (Prod a b)) (g : a → c) (y : c) :
    Classical.block (ρ.sourceDeterministicPostprocess g).matrix y y =
      ∑ x, if g x = y then Classical.block ρ.matrix x x else 0 := by
  simp [sourceDeterministicPostprocess]

/-- Deterministic source coarse-graining preserves the total trace. -/
theorem sourceDeterministicPostprocess_trace
    {c : Type*} [Fintype c] [DecidableEq c]
    (ρ : SubnormalizedState (Prod a b)) (g : a → c) :
    (ρ.sourceDeterministicPostprocess g).matrix.trace = ρ.matrix.trace := by
  rw [sourceDeterministicPostprocess_matrix, Classical.blockDiagonal_trace]
  calc
    (∑ y : c,
        (∑ x : a,
          if g x = y then Classical.block ρ.matrix x x else 0).trace) =
        ∑ y : c, ∑ x : a,
          (if g x = y then Classical.block ρ.matrix x x else 0).trace := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Matrix.trace_sum]
    _ = ∑ x : a, ∑ y : c,
          (if g x = y then Classical.block ρ.matrix x x else 0).trace := by
        rw [Finset.sum_comm]
    _ = ∑ x : a, (Classical.block ρ.matrix x x).trace := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_eq_single (g x)]
        · simp
        · intro y _ hy
          rw [if_neg (fun h => hy h.symm)]
          simp
        · simp
    _ = ρ.matrix.trace := Classical.sum_block_trace ρ.matrix

@[simp]
theorem sourceDeterministicPostprocess_trace_re
    {c : Type*} [Fintype c] [DecidableEq c]
    (ρ : SubnormalizedState (Prod a b)) (g : a → c) :
    (ρ.sourceDeterministicPostprocess g).matrix.trace.re = ρ.matrix.trace.re := by
  exact congrArg Complex.re (ρ.sourceDeterministicPostprocess_trace g)

/-- Each input source block is dominated by the output block of its image under
deterministic source coarse-graining. -/
theorem sourceBlock_le_sourceDeterministicPostprocess_block
    {c : Type*} [Fintype c] [DecidableEq c]
    (ρ : SubnormalizedState (Prod a b)) (g : a → c) (x : a) :
    Classical.block ρ.matrix x x ≤
      Classical.block (ρ.sourceDeterministicPostprocess g).matrix (g x) (g x) := by
  classical
  rw [sourceDeterministicPostprocess_block]
  have hxmem : x ∈ (Finset.univ : Finset a) := Finset.mem_univ x
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hxmem]
  simp only [if_true]
  exact le_add_of_nonneg_right (by
    have hrest_psd :
        (∑ x' ∈ (Finset.univ : Finset a).erase x,
          if g x' = g x then Classical.block ρ.matrix x' x' else 0).PosSemidef := by
      exact Matrix.posSemidef_sum ((Finset.univ : Finset a).erase x) fun x' _ => by
        by_cases hx' : g x' = g x
        · simpa [hx'] using ρ.pos.submatrix (fun i : b => (x', i))
        · simpa [hx'] using (Matrix.PosSemidef.zero : (0 : CMatrix b).PosSemidef)
    simpa [Matrix.le_iff] using hrest_psd)

/-- Matrix map that keeps exactly the diagonal source blocks whose source
label satisfies `p`, and drops all source off-diagonal blocks. -/
def sourceBlockFilterMap (p : a → Prop) [DecidablePred p] :
    MatrixMap (Prod a b) (Prod a b) where
  toFun X := fun xi xj =>
    if xi.1 = xj.1 ∧ p xi.1 then X (xi.1, xi.2) (xi.1, xj.2) else 0
  map_add' X Y := by
    ext xi xj
    rcases xi with ⟨x, i⟩
    rcases xj with ⟨y, j⟩
    by_cases hxy : x = y
    · subst y
      by_cases hp : p x <;> simp [hp]
    · simp [hxy]
  map_smul' c X := by
    ext xi xj
    rcases xi with ⟨x, i⟩
    rcases xj with ⟨y, j⟩
    by_cases hxy : x = y
    · subst y
      by_cases hp : p x <;> simp [hp]
    · simp [hxy]

private def sourceBlockFilterKraus (p : a → Prop) [DecidablePred p] (x : a) :
    Matrix (Prod a b) (Prod a b) ℂ :=
  fun out inp => if p x ∧ out = inp ∧ out.1 = x then 1 else 0

private theorem sourceBlockFilterMap_eq_ofKraus
    (p : a → Prop) [DecidablePred p] :
    MatrixMap.ofKraus (sourceBlockFilterKraus (a := a) (b := b) p) =
      sourceBlockFilterMap (a := a) (b := b) p := by
  apply LinearMap.ext
  intro X
  ext xi xj
  rcases xi with ⟨x, i⟩
  rcases xj with ⟨y, j⟩
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    sourceBlockFilterKraus, sourceBlockFilterMap]
  simp only [ite_mul, zero_mul, one_mul]
  by_cases hxy : x = y
  · subst y
    by_cases hp : p x
    · rw [Finset.sum_eq_single x]
      · simp [hp]
      · intro z _ hz
        have hxz : ¬ x = z := fun h => hz h.symm
        simp [hxz]
      · intro hx
        simp at hx
    · calc
        (∑ x_1,
            ∑ x_2,
              (∑ x_3, if p x_1 ∧ (x, i) = x_3 ∧ x = x_1 then X x_3 x_2 else 0) *
                star (if p x_1 ∧ (x, j) = x_2 ∧ x = x_1 then 1 else 0)) = 0 := by
            apply Finset.sum_eq_zero
            intro z _
            by_cases hz : z = x
            · subst z
              simp [hp]
            · have hxz : ¬ x = z := fun h => hz h.symm
              simp [hxz]
        _ = (if x = x ∧ p x then X (x, i) (x, j) else 0) := by
            simp [hp]
  · calc
      (∑ x_1,
          ∑ x_2,
            (∑ x_3, if p x_1 ∧ (x, i) = x_3 ∧ x = x_1 then X x_3 x_2 else 0) *
              star (if p x_1 ∧ (y, j) = x_2 ∧ y = x_1 then 1 else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro z _
          by_cases hxz : x = z
          · subst z
            have hyx : ¬ y = x := fun h => hxy h.symm
            simp [hyx]
          · simp [hxz]
      _ = (if x = y ∧ p x then X (x, i) (x, j) else 0) := by
          simp [hxy]

theorem sourceBlockFilterMap_completelyPositive
    (p : a → Prop) [DecidablePred p] :
    MatrixMap.IsCompletelyPositive (sourceBlockFilterMap (a := a) (b := b) p) := by
  rw [← sourceBlockFilterMap_eq_ofKraus (a := a) (b := b) p]
  exact MatrixMap.ofKraus_completelyPositive _

/-- The source-block filter is the block-diagonal matrix of the selected
diagonal source blocks. -/
theorem sourceBlockFilterMap_apply_eq_blockDiagonal
    (p : a → Prop) [DecidablePred p] (X : CMatrix (Prod a b)) :
    sourceBlockFilterMap (a := a) (b := b) p X =
      Classical.blockDiagonal
        (fun x : a => if p x then Classical.block X x x else 0) := by
  ext xi xj
  rcases xi with ⟨x, i⟩
  rcases xj with ⟨y, j⟩
  by_cases hxy : x = y
  · subst y
    have hblock :=
      congrFun (congrFun
        (Classical.blockDiagonal_block_self
          (fun x : a => if p x then Classical.block X x x else 0) x) i) j
    by_cases hp : p x
    · simpa [sourceBlockFilterMap, Classical.block, hp] using hblock.symm
    · simpa [sourceBlockFilterMap, Classical.block, hp] using hblock.symm
  · have hblock :=
      congrFun (congrFun
        (Classical.blockDiagonal_block_ne
          (fun x : a => if p x then Classical.block X x x else 0)
          hxy) i) j
    simpa [sourceBlockFilterMap, Classical.block, hxy] using hblock.symm

private theorem sourceBlockFilterMap_trace_re_le
    (p : a → Prop) [DecidablePred p] {X : CMatrix (Prod a b)}
    (hX : X.PosSemidef) :
    ((sourceBlockFilterMap (a := a) (b := b) p X).trace).re ≤ X.trace.re := by
  rw [sourceBlockFilterMap_apply_eq_blockDiagonal, Classical.blockDiagonal_trace]
  calc
    (∑ x : a, (if p x then Classical.block X x x else 0).trace).re =
        ∑ x : a, ((if p x then Classical.block X x x else 0 : CMatrix b).trace).re := by
        simp
    _ ≤ ∑ x : a, (Classical.block X x x).trace.re := by
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases hp : p x
        · simp [hp]
        · have hblock_pos :
              (Classical.block X x x).PosSemidef :=
            hX.submatrix (fun i : b => (x, i))
          have htrace_nonneg :
              0 ≤ (Classical.block X x x).trace.re :=
            (Matrix.PosSemidef.trace_nonneg hblock_pos).1
          simpa [hp] using htrace_nonneg
    _ = (∑ x : a, (Classical.block X x x).trace).re := by
        simp
    _ = X.trace.re := by
        exact congrArg Complex.re (Classical.sum_block_trace X)

/-- Source-block filtering is trace-nonincreasing completely positive. -/
theorem sourceBlockFilterMap_traceNonincreasingCP
    (p : a → Prop) [DecidablePred p] :
    MatrixMap.TraceNonincreasingCP (sourceBlockFilterMap (a := a) (b := b) p) where
  completelyPositive := sourceBlockFilterMap_completelyPositive (a := a) (b := b) p
  traceNonincreasing := by
    intro X hX
    exact sourceBlockFilterMap_trace_re_le (a := a) (b := b) p hX

/-- Restrict a subnormalized state to selected diagonal blocks of the source
classical register.  This pinches the source register and discards all labels
not satisfying `p`. -/
def sourceBlockFilter (ρ : SubnormalizedState (Prod a b))
    (p : a → Prop) [DecidablePred p] :
    SubnormalizedState (Prod a b) :=
  ρ.applyTraceNonincreasingCP
    (sourceBlockFilterMap (a := a) (b := b) p)
    (sourceBlockFilterMap_traceNonincreasingCP (a := a) (b := b) p)

@[simp]
theorem sourceBlockFilter_matrix (ρ : SubnormalizedState (Prod a b))
    (p : a → Prop) [DecidablePred p] :
    (ρ.sourceBlockFilter p).matrix =
      sourceBlockFilterMap (a := a) (b := b) p ρ.matrix :=
  rfl

theorem sourceBlockFilter_matrix_eq_blockDiagonal
    (ρ : SubnormalizedState (Prod a b)) (p : a → Prop) [DecidablePred p] :
    (ρ.sourceBlockFilter p).matrix =
      Classical.blockDiagonal
        (fun x : a => if p x then Classical.block ρ.matrix x x else 0) := by
  rw [sourceBlockFilter_matrix, sourceBlockFilterMap_apply_eq_blockDiagonal]

theorem sourceBlockFilter_trace_re_le
    (ρ : SubnormalizedState (Prod a b)) (p : a → Prop) [DecidablePred p] :
    (ρ.sourceBlockFilter p).matrix.trace.re ≤ ρ.matrix.trace.re :=
  sourceBlockFilterMap_trace_re_le (a := a) (b := b) p ρ.pos

/-- If the center is already fixed by a source-block filter, filtering a
nearby witness stays in the same purified-distance ball. -/
theorem purifiedBall_sourceBlockFilter_of_fixed
    (ρ : SubnormalizedState (Prod a b)) (p : a → Prop) [DecidablePred p]
    {σ : SubnormalizedState (Prod a b)} {ε : ℝ}
    (hρ : ρ.sourceBlockFilter p = ρ) (hball : ρ.purifiedBall ε σ) :
    ρ.purifiedBall ε (σ.sourceBlockFilter p) := by
  have hfiltered :
      (ρ.sourceBlockFilter p).purifiedBall ε (σ.sourceBlockFilter p) := by
    simpa [sourceBlockFilter] using
      (SubnormalizedState.purifiedBall_of_traceNonincreasingCP
        (ρ := ρ) (σ := σ)
        (sourceBlockFilterMap (a := a) (b := b) p)
        (sourceBlockFilterMap_traceNonincreasingCP (a := a) (b := b) p)
        hball)
  rwa [hρ] at hfiltered

/-- Filtering source blocks preserves every raw side operator feasible for
subnormalized conditional min-entropy. -/
theorem ConditionalMinEntropyScaleFeasible.sourceBlockFilter
    {ρ : SubnormalizedState (Prod a b)} {T : CMatrix b}
    (p : a → Prop) [DecidablePred p]
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T) :
    ConditionalMinEntropyScaleFeasible (a := a) (ρ.sourceBlockFilter p) T := by
  constructor
  · exact hT.1
  · rw [Matrix.le_iff]
    have hblocks :
        ∀ x : a, (if p x then T - Classical.block ρ.matrix x x else T).PosSemidef := by
      intro x
      by_cases hp : p x
      · simpa [hp, Matrix.le_iff] using
          block_le_of_conditionalMinEntropyScaleFeasible ρ T x hT
      · simpa [hp] using hT.1
    have hmatrix :
        Matrix.kronecker (1 : CMatrix a) T - (ρ.sourceBlockFilter p).matrix =
          Classical.blockDiagonal
            (fun x : a => if p x then T - Classical.block ρ.matrix x x else T) := by
      calc
        Matrix.kronecker (1 : CMatrix a) T - (ρ.sourceBlockFilter p).matrix =
            Classical.blockDiagonal (fun _ : a => T) -
              Classical.blockDiagonal
                (fun x : a => if p x then Classical.block ρ.matrix x x else 0) := by
              rw [Classical.identityTensor_eq_blockDiagonal,
                sourceBlockFilter_matrix_eq_blockDiagonal]
        _ = Classical.blockDiagonal
              (fun x : a => T -
                (if p x then Classical.block ρ.matrix x x else 0)) := by
              rw [← Classical.blockDiagonal_sub]
        _ = Classical.blockDiagonal
              (fun x : a => if p x then T - Classical.block ρ.matrix x x else T) := by
              congr with x
              by_cases hp : p x <;> simp [hp]
    rw [hmatrix]
    exact Classical.blockDiagonal_posSemidef
      (fun x : a => if p x then T - Classical.block ρ.matrix x x else T)
      hblocks

/-- Source-block filtering cannot increase the raw subnormalized
conditional-min endpoint scale. -/
theorem conditionalMinEntropyScale_sourceBlockFilter_le
    (ρ : SubnormalizedState (Prod a b)) (p : a → Prop) [DecidablePred p] :
    (ρ.sourceBlockFilter p).conditionalMinEntropyScale (a := a) ≤
      ρ.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf (ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
  intro t ht
  rcases ht with ⟨T, hT, rfl⟩
  have hbddFiltered :
      BddBelow ((ρ.sourceBlockFilter p).conditionalMinEntropyScaleValueSet
        (a := a)) :=
    (ρ.sourceBlockFilter p).conditionalMinEntropyScaleValueSet_bddBelow
      (a := a)
  exact csInf_le hbddFiltered
    ⟨T, hT.sourceBlockFilter (a := a) p, rfl⟩

/-- Source-block filtering can only increase subnormalized conditional
min-entropy when both the original and filtered states have positive trace. -/
theorem conditionalMinEntropy_le_sourceBlockFilter_of_trace_pos
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) (p : a → Prop) [DecidablePred p]
    (hρ : 0 < ρ.matrix.trace.re)
    (hfilter : 0 < (ρ.sourceBlockFilter p).matrix.trace.re) :
    ρ.conditionalMinEntropyRaw ≤ (ρ.sourceBlockFilter p).conditionalMinEntropyRaw := by
  rw [ρ.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos (a := a) hρ,
    (ρ.sourceBlockFilter p).conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a) hfilter]
  have hscale_le := ρ.conditionalMinEntropyScale_sourceBlockFilter_le (a := a) p
  have hfiltered_scale_pos :
      0 < (ρ.sourceBlockFilter p).conditionalMinEntropyScale (a := a) :=
    (ρ.sourceBlockFilter p).conditionalMinEntropyScale_pos_of_trace_pos
      (a := a) hfilter
  have hlog :
      log2 ((ρ.sourceBlockFilter p).conditionalMinEntropyScale (a := a)) ≤
        log2 (ρ.conditionalMinEntropyScale (a := a)) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hfiltered_scale_pos hscale_le)
      (le_of_lt (Real.log_pos one_lt_two))
  exact neg_le_neg hlog

/-- Coordinate pinching of the source register, implemented as the standard
coordinate measurement on the source tensor the identity channel on the
conditioning register. -/
def sourceCoordinatePinchChannel : Channel (Prod a b) (Prod a b) :=
  (Channel.measure (POVM.coordinate a)).prod (Channel.idChannel b)

private theorem coordinateMeasure_map_one :
    (Channel.measure (POVM.coordinate a)).map (1 : CMatrix a) = 1 := by
  rw [Channel.measure_map]
  simpa [POVM.coordinate, trace_single_one] using (POVM.coordinate a).sum_eq_one

private theorem coordinateMeasure_map_single (x : a) :
    (Channel.measure (POVM.coordinate a)).map (Matrix.single x x (1 : ℂ)) =
      Matrix.single x x (1 : ℂ) := by
  rw [Channel.measure_map]
  rw [Finset.sum_eq_single x]
  · have hmul :
        Matrix.single x x (1 : ℂ) * (POVM.coordinate a).effects x =
          Matrix.single x x (1 : ℂ) := by
      rw [POVM.coordinate_effects, Matrix.single_mul_single_same]
      simp
    rw [hmul, trace_single_one, if_pos rfl]
    simp
  · intro y _ hy
    have hmul :
        Matrix.single x x (1 : ℂ) * (POVM.coordinate a).effects y = 0 := by
      have hxy : x ≠ y := fun h => hy h.symm
      ext i j
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = x
      · subst k
        simp [POVM.coordinate, Matrix.single_apply, hy]
      · have hxk : x ≠ k := fun h => hk h.symm
        simp [POVM.coordinate, Matrix.single_apply, hxk]
    rw [hmul]
    simp
  · intro hx
    simp at hx

private theorem coordinateMeasure_map_apply (X : CMatrix a) (x x' : a) :
    (Channel.measure (POVM.coordinate a)).map X x x' =
      if x = x' then X x x else 0 := by
  classical
  rw [Channel.measure_map]
  simp only [Matrix.sum_apply, Matrix.smul_apply, POVM.coordinate_effects]
  by_cases hxx' : x = x'
  · subst x'
    rw [if_pos rfl]
    rw [Finset.sum_eq_single x]
    · rw [Matrix.trace_mul_single]
      simp
    · intro y _ hy
      have hyx : y ≠ x := hy
      simp [hyx]
    · intro hx
      simp at hx
  · rw [if_neg hxx']
    refine Finset.sum_eq_zero fun y _ => ?_
    have hnot : ¬ (y = x ∧ y = x') := by
      intro hy
      exact hxx' (hy.1.symm.trans hy.2)
    simp [hnot]

private theorem idChannel_map_eq_self (X : CMatrix b) :
    (Channel.idChannel b).map X = X := by
  change MatrixMap.ofKraus (fun _ : Unit => (1 : CMatrix b)) X = X
  simp [MatrixMap.ofKraus]

/-- Source-coordinate pinching fixes every side-operator tensor `I_A ⊗ T_B`. -/
theorem sourceCoordinatePinchChannel_map_identityTensor (T : CMatrix b) :
    (sourceCoordinatePinchChannel (a := a) (b := b)).map
        (Matrix.kronecker (1 : CMatrix a) T) =
      Matrix.kronecker (1 : CMatrix a) T := by
  dsimp [sourceCoordinatePinchChannel]
  change (((Channel.measure (POVM.coordinate a)).prod (Channel.idChannel b)).map
      (Matrix.kronecker (1 : CMatrix a) T)) =
    Matrix.kronecker (1 : CMatrix a) T
  rw [Channel.prod_map_kronecker]
  rw [coordinateMeasure_map_one]
  rw [idChannel_map_eq_self]

/-- Source-coordinate pinching fixes a diagonal source block tensor. -/
theorem sourceCoordinatePinchChannel_map_singleTensor (x : a) (T : CMatrix b) :
    (sourceCoordinatePinchChannel (a := a) (b := b)).map
        (Matrix.kronecker (Matrix.single x x (1 : ℂ)) T) =
      Matrix.kronecker (Matrix.single x x (1 : ℂ)) T := by
  dsimp [sourceCoordinatePinchChannel]
  change (((Channel.measure (POVM.coordinate a)).prod (Channel.idChannel b)).map
      (Matrix.kronecker (Matrix.single x x (1 : ℂ)) T)) =
    Matrix.kronecker (Matrix.single x x (1 : ℂ)) T
  rw [Channel.prod_map_kronecker]
  rw [coordinateMeasure_map_single]
  rw [idChannel_map_eq_self]

/-- Pinch a subnormalized bipartite state in the source register's coordinate
basis. -/
def sourceCoordinatePinch (ρ : SubnormalizedState (Prod a b)) :
    SubnormalizedState (Prod a b) :=
  ρ.applyTraceNonincreasingCP
    (sourceCoordinatePinchChannel (a := a) (b := b)).map
    (MatrixMap.traceNonincreasingCP_of_tracePreserving
      (sourceCoordinatePinchChannel (a := a) (b := b)).completelyPositive
      (sourceCoordinatePinchChannel (a := a) (b := b)).tracePreserving)

@[simp]
theorem sourceCoordinatePinch_matrix (ρ : SubnormalizedState (Prod a b)) :
    ρ.sourceCoordinatePinch.matrix =
      (sourceCoordinatePinchChannel (a := a) (b := b)).map ρ.matrix :=
  rfl

/-- Source-coordinate pinching is the block-diagonal matrix of the original
diagonal source blocks. -/
theorem sourceCoordinatePinch_matrix_eq_blockDiagonal
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.sourceCoordinatePinch.matrix =
      Classical.blockDiagonal (fun x => Classical.block ρ.matrix x x) := by
  ext xi xj
  rcases xi with ⟨x, i⟩
  rcases xj with ⟨x', j⟩
  rw [sourceCoordinatePinch_matrix]
  change MatrixMap.kron (Channel.measure (POVM.coordinate a)).map
      (Channel.idChannel b).map ρ.matrix (x, i) (x', j) =
    Classical.blockDiagonal (fun x => Classical.block ρ.matrix x x) (x, i) (x', j)
  rw [MatrixMap.kron_idChannel_apply_slice]
  rw [coordinateMeasure_map_apply]
  by_cases hxx' : x = x'
  · subst x'
    have hblock :=
      congrFun (congrFun
        (Classical.blockDiagonal_block_self
          (fun x => Classical.block ρ.matrix x x) x) i) j
    simpa [Classical.block] using hblock.symm
  · have hblock :=
      congrFun (congrFun
        (Classical.blockDiagonal_block_ne
          (fun x => Classical.block ρ.matrix x x) hxx') i) j
    simpa [hxx', Classical.block] using hblock.symm

/-- Source-coordinate pinching is idempotent. -/
@[simp]
theorem sourceCoordinatePinch_sourceCoordinatePinch
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.sourceCoordinatePinch.sourceCoordinatePinch = ρ.sourceCoordinatePinch := by
  apply SubnormalizedState.ext
  rw [sourceCoordinatePinch_matrix_eq_blockDiagonal,
    sourceCoordinatePinch_matrix_eq_blockDiagonal]
  congr with x
  simp

/-- Deterministic source coarse-graining only depends on diagonal source
blocks, so precomposing it with source-coordinate pinching has no effect. -/
@[simp]
theorem sourceDeterministicPostprocess_sourceCoordinatePinch
    {c : Type*} [Fintype c] [DecidableEq c]
    (ρ : SubnormalizedState (Prod a b)) (g : a → c) :
    ρ.sourceCoordinatePinch.sourceDeterministicPostprocess g =
      ρ.sourceDeterministicPostprocess g := by
  apply SubnormalizedState.ext
  rw [sourceDeterministicPostprocess_matrix, sourceDeterministicPostprocess_matrix]
  have hblocks :
      (fun y : c =>
          ∑ x : a,
            if g x = y then Classical.block ρ.sourceCoordinatePinch.matrix x x else 0) =
        (fun y : c =>
          ∑ x : a,
            if g x = y then Classical.block ρ.matrix x x else 0) := by
    funext y
    refine Finset.sum_congr rfl fun x _ => ?_
    have hblock :
        Classical.block
            ((sourceCoordinatePinchChannel (a := a) (b := b)).map ρ.matrix) x x =
          Classical.block ρ.matrix x x := by
      change Classical.block ρ.sourceCoordinatePinch.matrix x x =
        Classical.block ρ.matrix x x
      rw [sourceCoordinatePinch_matrix_eq_blockDiagonal]
      exact Classical.blockDiagonal_block_self
        (fun x => Classical.block ρ.matrix x x) x
    by_cases hx : g x = y <;> simp [hx, hblock]
  rw [hblocks]

/-- A side operator that is raw scale-feasible for deterministic source
coarse-graining is also raw scale-feasible for source-coordinate pinching of
the original state. -/
theorem ConditionalMinEntropyScaleFeasible.sourceCoordinatePinch_of_sourceDeterministicPostprocess
    {c : Type*} [Fintype c] [DecidableEq c]
    {ρ : SubnormalizedState (Prod a b)} (g : a → c) {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := c)
      (ρ.sourceDeterministicPostprocess g) T) :
    ConditionalMinEntropyScaleFeasible (a := a) ρ.sourceCoordinatePinch T := by
  constructor
  · exact hT.1
  · rw [Matrix.le_iff]
    have hblocks : ∀ x, (T - Classical.block ρ.matrix x x).PosSemidef := by
      intro x
      rw [← Matrix.le_iff]
      exact (ρ.sourceBlock_le_sourceDeterministicPostprocess_block g x).trans
        (block_le_of_conditionalMinEntropyScaleFeasible
          (ρ.sourceDeterministicPostprocess g) T (g x) hT)
    have hmatrix :
        Matrix.kronecker (1 : CMatrix a) T - ρ.sourceCoordinatePinch.matrix =
          Classical.blockDiagonal (fun x => T - Classical.block ρ.matrix x x) := by
      calc
        Matrix.kronecker (1 : CMatrix a) T - ρ.sourceCoordinatePinch.matrix =
            Classical.blockDiagonal (fun _ : a => T) -
              Classical.blockDiagonal (fun x => Classical.block ρ.matrix x x) := by
              rw [Classical.identityTensor_eq_blockDiagonal,
                sourceCoordinatePinch_matrix_eq_blockDiagonal]
        _ = Classical.blockDiagonal (fun x => T - Classical.block ρ.matrix x x) := by
              rw [← Classical.blockDiagonal_sub]
    rw [hmatrix]
    exact Classical.blockDiagonal_posSemidef
      (fun x => T - Classical.block ρ.matrix x x) hblocks

/-- Deterministic coarse-graining of the source register can only raise the
raw conditional-min endpoint scale relative to the source-coordinate pinched
state. -/
theorem conditionalMinEntropyScale_sourceCoordinatePinch_le_sourceDeterministicPostprocess
    {c : Type*} [Fintype c] [DecidableEq c]
    (ρ : SubnormalizedState (Prod a b)) (g : a → c) :
    ρ.sourceCoordinatePinch.conditionalMinEntropyScale (a := a) ≤
      (ρ.sourceDeterministicPostprocess g).conditionalMinEntropyScale (a := c) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf
    ((ρ.sourceDeterministicPostprocess g).conditionalMinEntropyScaleValueSet_nonempty
      (a := c)) ?_
  intro t ht
  rcases ht with ⟨T, hT, rfl⟩
  have hbdd :
      BddBelow (ρ.sourceCoordinatePinch.conditionalMinEntropyScaleValueSet
        (a := a)) :=
    ρ.sourceCoordinatePinch.conditionalMinEntropyScaleValueSet_bddBelow
      (a := a)
  exact csInf_le hbdd
    ⟨T, hT.sourceCoordinatePinch_of_sourceDeterministicPostprocess
      (ρ := ρ) g, rfl⟩

@[simp]
theorem sourceCoordinatePinch_trace_re (ρ : SubnormalizedState (Prod a b)) :
    ρ.sourceCoordinatePinch.matrix.trace.re = ρ.matrix.trace.re := by
  exact congrArg Complex.re
    ((sourceCoordinatePinchChannel (a := a) (b := b)).tracePreserving ρ.matrix)

/-- Source-coordinate pinching preserves every raw side operator feasible for
subnormalized conditional min-entropy. -/
theorem ConditionalMinEntropyScaleFeasible.sourceCoordinatePinch
    {ρ : SubnormalizedState (Prod a b)} {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T) :
    ConditionalMinEntropyScaleFeasible (a := a) ρ.sourceCoordinatePinch T := by
  constructor
  · exact hT.1
  · let Φ : MatrixMap (Prod a b) (Prod a b) :=
      (sourceCoordinatePinchChannel (a := a) (b := b)).map
    have hdiff : (Matrix.kronecker (1 : CMatrix a) T - ρ.matrix).PosSemidef :=
      hT.2
    have hmap := MatrixMap.isCompletelyPositive_mapsPositive Φ
      (sourceCoordinatePinchChannel (a := a) (b := b)).completelyPositive
      (Matrix.kronecker (1 : CMatrix a) T - ρ.matrix) hdiff
    change (Matrix.kronecker (1 : CMatrix a) T - ρ.sourceCoordinatePinch.matrix).PosSemidef
    rw [sourceCoordinatePinch_matrix]
    convert hmap using 1
    simp only [Φ, map_sub]
    rw [sourceCoordinatePinchChannel_map_identityTensor]

/-- Source-coordinate pinching cannot increase the raw subnormalized
conditional-min endpoint scale. -/
theorem conditionalMinEntropyScale_sourceCoordinatePinch_le
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.sourceCoordinatePinch.conditionalMinEntropyScale (a := a) ≤
      ρ.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf (ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
  intro t ht
  rcases ht with ⟨T, hT, rfl⟩
  have hbddPinched :
      BddBelow (ρ.sourceCoordinatePinch.conditionalMinEntropyScaleValueSet
        (a := a)) :=
    ρ.sourceCoordinatePinch.conditionalMinEntropyScaleValueSet_bddBelow
      (a := a)
  exact csInf_le hbddPinched
    ⟨T, hT.sourceCoordinatePinch (a := a), rfl⟩

/-- Pinching the source register in the coordinate basis can only increase
subnormalized conditional min-entropy, for positive-trace states. -/
theorem conditionalMinEntropy_le_sourceCoordinatePinch_of_trace_pos
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) (hρ : 0 < ρ.matrix.trace.re) :
    ρ.conditionalMinEntropyRaw ≤ ρ.sourceCoordinatePinch.conditionalMinEntropyRaw := by
  rw [ρ.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos (a := a) hρ,
    ρ.sourceCoordinatePinch.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a) (by
        rw [sourceCoordinatePinch_trace_re]
        exact hρ)]
  have hscale_le := ρ.conditionalMinEntropyScale_sourceCoordinatePinch_le
    (a := a)
  have hpinched_scale_pos :
      0 < ρ.sourceCoordinatePinch.conditionalMinEntropyScale (a := a) :=
    ρ.sourceCoordinatePinch.conditionalMinEntropyScale_pos_of_trace_pos
      (a := a) (by
        rw [sourceCoordinatePinch_trace_re]
        exact hρ)
  have hlog :
      log2 (ρ.sourceCoordinatePinch.conditionalMinEntropyScale (a := a)) ≤
        log2 (ρ.conditionalMinEntropyScale (a := a)) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hpinched_scale_pos hscale_le)
      (le_of_lt (Real.log_pos one_lt_two))
  exact neg_le_neg hlog

/-- Deterministic source coarse-graining cannot increase ordinary
subnormalized conditional min-entropy, once the original witness is pinched in
the source coordinate basis. -/
theorem conditionalMinEntropy_sourceDeterministicPostprocess_le_sourceCoordinatePinch_of_trace_pos
    {c : Type*} [Fintype c] [DecidableEq c]
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) (g : a → c)
    (hρ : 0 < ρ.matrix.trace.re) :
    (ρ.sourceDeterministicPostprocess g).conditionalMinEntropyRaw ≤
      ρ.sourceCoordinatePinch.conditionalMinEntropyRaw := by
  letI : Nonempty c := ⟨g (Classical.choice (inferInstance : Nonempty a))⟩
  have hpost : 0 < (ρ.sourceDeterministicPostprocess g).matrix.trace.re := by
    rw [sourceDeterministicPostprocess_trace_re]
    exact hρ
  have hpinch : 0 < ρ.sourceCoordinatePinch.matrix.trace.re := by
    rw [sourceCoordinatePinch_trace_re]
    exact hρ
  rw [(ρ.sourceDeterministicPostprocess g).conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := c) hpost,
    ρ.sourceCoordinatePinch.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a) hpinch]
  have hscale_le :=
    ρ.conditionalMinEntropyScale_sourceCoordinatePinch_le_sourceDeterministicPostprocess
      (a := a) g
  have hscale_pinch_pos :
      0 < ρ.sourceCoordinatePinch.conditionalMinEntropyScale (a := a) :=
    ρ.sourceCoordinatePinch.conditionalMinEntropyScale_pos_of_trace_pos
      (a := a) hpinch
  have hlog :
      log2 (ρ.sourceCoordinatePinch.conditionalMinEntropyScale (a := a)) ≤
        log2 ((ρ.sourceDeterministicPostprocess g).conditionalMinEntropyScale
          (a := c)) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hscale_pinch_pos hscale_le)
      (le_of_lt (Real.log_pos one_lt_two))
  exact neg_le_neg hlog

/-- If the center is already fixed by source-coordinate pinching, then pinching
a nearby witness stays in the same purified-distance ball. -/
theorem purifiedBall_sourceCoordinatePinch_of_fixed
    (ρ : SubnormalizedState (Prod a b)) {σ : SubnormalizedState (Prod a b)} {ε : ℝ}
    (hρ : ρ.sourceCoordinatePinch = ρ) (hball : ρ.purifiedBall ε σ) :
    ρ.purifiedBall ε σ.sourceCoordinatePinch := by
  have hpinched :
      ρ.sourceCoordinatePinch.purifiedBall ε σ.sourceCoordinatePinch := by
    simpa [sourceCoordinatePinch] using
      (SubnormalizedState.purifiedBall_of_traceNonincreasingCP
        (ρ := ρ) (σ := σ)
        ((sourceCoordinatePinchChannel (a := a) (b := b)).map)
        (MatrixMap.traceNonincreasingCP_of_tracePreserving
          (sourceCoordinatePinchChannel (a := a) (b := b)).completelyPositive
          (sourceCoordinatePinchChannel (a := a) (b := b)).tracePreserving)
        hball)
  rwa [hρ] at hpinched

/-- Compress an arbitrary conditioning-register reference isometry back to the
source side using the CP map `X ↦ V† X V`. -/
def conditioningIsometryCompressed
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (ρPlus : SubnormalizedState (Prod a bPlus)) (V : ReferenceIsometry b bPlus) :
    SubnormalizedState (Prod a b) :=
  ρPlus.applyTraceNonincreasingCP
    (MatrixMap.kron (Channel.idChannel a).map
      (MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix)))
    (MatrixMap.traceNonincreasingCP_id_kron (a := a)
      (hΦ := referenceIsometry_conjTranspose_traceNonincreasingCP V))

@[simp]
theorem conditioningIsometryCompressed_matrix
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (ρPlus : SubnormalizedState (Prod a bPlus)) (V : ReferenceIsometry b bPlus) :
    (ρPlus.conditioningIsometryCompressed V).matrix =
      MatrixMap.kron (Channel.idChannel a).map
        (MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix))
        ρPlus.matrix :=
  rfl

@[simp]
theorem conditioningIsometryCompressed_conditioningIsometryApply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).conditioningIsometryCompressed V = ρ := by
  apply SubnormalizedState.ext
  rw [conditioningIsometryCompressed_matrix, conditioningIsometryApply_matrix]
  exact referenceIsometry_rightCompression_applyMatrixRight V ρ.matrix

/-- Compressing an arbitrary conditioning-register isometry preserves raw
subnormalized conditional-min feasibility. -/
theorem ConditionalMinEntropyScaleFeasible.conditioningIsometryCompressed
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    {ρPlus : SubnormalizedState (Prod a bPlus)}
    {TPlus : CMatrix bPlus}
    (V : ReferenceIsometry b bPlus)
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρPlus TPlus) :
    ConditionalMinEntropyScaleFeasible (a := a) (ρPlus.conditioningIsometryCompressed V)
      (Matrix.conjTranspose V.matrix * TPlus * V.matrix) := by
  constructor
  · exact Matrix.PosSemidef.conjTranspose_mul_mul_same hT.1 V.matrix
  · let Γ : MatrixMap bPlus b :=
      MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix)
    let Φ : MatrixMap (Prod a bPlus) (Prod a b) :=
      MatrixMap.kron (Channel.idChannel a).map Γ
    have hCP : MatrixMap.IsCompletelyPositive Φ :=
      MatrixMap.isCompletelyPositive_kron (Channel.idChannel a).map Γ
        (Channel.idChannel a).completelyPositive
        (MatrixMap.ofKraus_completelyPositive
          (fun _ : Unit => Matrix.conjTranspose V.matrix))
    have hdiff : (Matrix.kronecker (1 : CMatrix a) TPlus - ρPlus.matrix).PosSemidef :=
      hT.2
    have hmap := MatrixMap.isCompletelyPositive_mapsPositive Φ hCP
      (Matrix.kronecker (1 : CMatrix a) TPlus - ρPlus.matrix) hdiff
    change (Matrix.kronecker (1 : CMatrix a)
        (Matrix.conjTranspose V.matrix * TPlus * V.matrix) -
        (ρPlus.conditioningIsometryCompressed V).matrix).PosSemidef
    rw [conditioningIsometryCompressed_matrix]
    convert hmap using 1
    simp only [Φ, Γ, map_sub]
    rw [MatrixMap.kron_apply_kronecker]
    simp [Channel.idChannel, MatrixMap.ofKraus]

/-- Compressing an arbitrary conditioning-register isometry cannot raise the
raw subnormalized conditional-min endpoint scale. -/
theorem conditionalMinEntropyScale_conditioningIsometryCompressed_le
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (ρPlus : SubnormalizedState (Prod a bPlus)) (V : ReferenceIsometry b bPlus) :
    (ρPlus.conditioningIsometryCompressed V).conditionalMinEntropyScale (a := a) ≤
      ρPlus.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf (ρPlus.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
  intro t ht
  rcases ht with ⟨TPlus, hTPlus, rfl⟩
  have hbddCompressed :
      BddBelow
        ((ρPlus.conditioningIsometryCompressed V).conditionalMinEntropyScaleValueSet
          (a := a)) :=
    (ρPlus.conditioningIsometryCompressed V).conditionalMinEntropyScaleValueSet_bddBelow
      (a := a)
  have htrace_le :
      ((Matrix.conjTranspose V.matrix * TPlus * V.matrix).trace).re ≤
        TPlus.trace.re :=
    trace_re_conjTranspose_referenceIsometry_le V hTPlus.1
  exact le_trans
    (csInf_le hbddCompressed
      ⟨Matrix.conjTranspose V.matrix * TPlus * V.matrix,
        hTPlus.conditioningIsometryCompressed V, rfl⟩)
    htrace_le

/-- Compressing an arbitrary source-register isometry cannot raise the raw
subnormalized conditional-min endpoint scale. -/
theorem conditionalMinEntropyScale_sourceIsometryCompressed_le
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    (ρPlus : SubnormalizedState (Prod aPlus b)) (V : ReferenceIsometry a aPlus) :
    (ρPlus.sourceIsometryCompressed V).conditionalMinEntropyScale (a := a) ≤
      ρPlus.conditionalMinEntropyScale (a := aPlus) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf (ρPlus.conditionalMinEntropyScaleValueSet_nonempty (a := aPlus)) ?_
  intro t ht
  rcases ht with ⟨TPlus, hTPlus, rfl⟩
  have hbddCompressed :
      BddBelow
        ((ρPlus.sourceIsometryCompressed V).conditionalMinEntropyScaleValueSet
          (a := a)) :=
    (ρPlus.sourceIsometryCompressed V).conditionalMinEntropyScaleValueSet_bddBelow
      (a := a)
  exact csInf_le hbddCompressed
    ⟨TPlus, hTPlus.sourceIsometryCompressed V, rfl⟩

/-- Compressing an arbitrary conditioning-register isometry can only increase
subnormalized conditional min-entropy, when both traces are positive. -/
theorem conditionalMinEntropy_le_conditioningIsometryCompressed
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    [Nonempty a] [Nonempty b] [Nonempty bPlus]
    (ρPlus : SubnormalizedState (Prod a bPlus)) (V : ReferenceIsometry b bPlus)
    (hPlus : 0 < ρPlus.matrix.trace.re)
    (hCompressed : 0 < (ρPlus.conditioningIsometryCompressed V).matrix.trace.re) :
    ρPlus.conditionalMinEntropyRaw ≤
      (ρPlus.conditioningIsometryCompressed V).conditionalMinEntropyRaw := by
  rw [ρPlus.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a) hPlus,
    (ρPlus.conditioningIsometryCompressed V).conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a) hCompressed]
  have hscale_le :=
    ρPlus.conditionalMinEntropyScale_conditioningIsometryCompressed_le
      (a := a) V
  have hcompressed_pos :
      0 <
        (ρPlus.conditioningIsometryCompressed V).conditionalMinEntropyScale
          (a := a) :=
    (ρPlus.conditioningIsometryCompressed V).conditionalMinEntropyScale_pos_of_trace_pos
      (a := a) hCompressed
  have hlog :
      log2
          ((ρPlus.conditioningIsometryCompressed V).conditionalMinEntropyScale
            (a := a)) ≤
        log2 (ρPlus.conditionalMinEntropyScale (a := a)) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hcompressed_pos hscale_le)
      (le_of_lt (Real.log_pos one_lt_two))
  exact neg_le_neg hlog

/-- Compressing an arbitrary source-register isometry can only increase
subnormalized conditional min-entropy, when both traces are positive. -/
theorem conditionalMinEntropy_le_sourceIsometryCompressed
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    [Nonempty a] [Nonempty b] [Nonempty aPlus]
    (ρPlus : SubnormalizedState (Prod aPlus b)) (V : ReferenceIsometry a aPlus)
    (hPlus : 0 < ρPlus.matrix.trace.re)
    (hCompressed : 0 < (ρPlus.sourceIsometryCompressed V).matrix.trace.re) :
    ρPlus.conditionalMinEntropyRaw ≤
      (ρPlus.sourceIsometryCompressed V).conditionalMinEntropyRaw := by
  rw [ρPlus.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := aPlus) hPlus,
    (ρPlus.sourceIsometryCompressed V).conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a) hCompressed]
  have hscale_le :=
    ρPlus.conditionalMinEntropyScale_sourceIsometryCompressed_le
      (a := a) V
  have hcompressed_pos :
      0 <
        (ρPlus.sourceIsometryCompressed V).conditionalMinEntropyScale
          (a := a) :=
    (ρPlus.sourceIsometryCompressed V).conditionalMinEntropyScale_pos_of_trace_pos
      (a := a) hCompressed
  have hlog :
      log2
          ((ρPlus.sourceIsometryCompressed V).conditionalMinEntropyScale
            (a := a)) ≤
        log2 (ρPlus.conditionalMinEntropyScale (a := aPlus)) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hcompressed_pos hscale_le)
      (le_of_lt (Real.log_pos one_lt_two))
  exact neg_le_neg hlog

/-- Applying an arbitrary conditioning-register reference isometry transports
subnormalized purified-distance balls. -/
theorem purifiedBall_conditioningIsometryApply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    {ρ σ : SubnormalizedState (Prod a b)} {ε : ℝ}
    (V : ReferenceIsometry b bPlus)
    (hball : ρ.purifiedBall ε σ) :
    (ρ.conditioningIsometryApply V).purifiedBall ε
      (σ.conditioningIsometryApply V) := by
  simpa [conditioningIsometryApply] using
    (SubnormalizedState.purifiedBall_of_traceNonincreasingCP
      (ρ := ρ) (σ := σ) (ε := ε)
      (MatrixMap.kron (Channel.idChannel a).map
        (MatrixMap.ofReferenceIsometry V))
      (MatrixMap.traceNonincreasingCP_id_kron (a := a)
        (hΦ := MatrixMap.ofReferenceIsometry_traceNonincreasingCP V))
      hball)

/-- Applying an arbitrary source-register reference isometry transports
subnormalized purified-distance balls. -/
theorem purifiedBall_sourceIsometryApply
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    {ρ σ : SubnormalizedState (Prod a b)} {ε : ℝ}
    (V : ReferenceIsometry a aPlus)
    (hball : ρ.purifiedBall ε σ) :
    (ρ.sourceIsometryApply V).purifiedBall ε
      (σ.sourceIsometryApply V) := by
  simpa [sourceIsometryApply] using
    (SubnormalizedState.purifiedBall_of_traceNonincreasingCP
      (ρ := ρ) (σ := σ) (ε := ε)
      (MatrixMap.kron (MatrixMap.ofReferenceIsometry V)
        (Channel.idChannel b).map)
      (MatrixMap.traceNonincreasingCP_kron_id
        (a := b) (hΦ := MatrixMap.ofReferenceIsometry_traceNonincreasingCP V))
      hball)

/-- Exact concrete right-summand padding transports subnormalized
purified-distance balls. -/
theorem purifiedBall_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {ρ σ : SubnormalizedState (Prod a b)} {ε : ℝ}
    (hball : ρ.purifiedBall ε σ) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).purifiedBall ε
      (σ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)) := by
  simpa [conditioningIsometryApply] using
    (SubnormalizedState.purifiedBall_of_traceNonincreasingCP
      (ρ := ρ) (σ := σ) (ε := ε)
      (MatrixMap.kron (Channel.idChannel a).map
        (MatrixMap.ofReferenceIsometry (ReferenceIsometry.sumInr extra b)))
      (MatrixMap.traceNonincreasingCP_id_kron (a := a)
        (hΦ := MatrixMap.ofReferenceIsometry_traceNonincreasingCP
          (ReferenceIsometry.sumInr extra b)))
      hball)

/-- Compressing the concrete right-summand padding transports a purified ball
back to the source conditioning register. -/
theorem purifiedBall_conditioningSumInrCompressed_of_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {ρ : SubnormalizedState (Prod a b)}
    {ρPlus : SubnormalizedState (Prod a (Sum extra b))} {ε : ℝ}
    (hball :
      (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).purifiedBall ε ρPlus) :
    ρ.purifiedBall ε ρPlus.conditioningSumInrCompressed := by
  have hcompressed :=
    SubnormalizedState.purifiedBall_of_traceNonincreasingCP
      (ρ := ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b))
      (σ := ρPlus) (ε := ε)
      (MatrixMap.kron (Channel.idChannel a).map
        (MatrixMap.sumInrBlockCompression (extra := extra) (α := b)))
      (MatrixMap.traceNonincreasingCP_id_kron (a := a)
        (hΦ := MatrixMap.sumInrBlockCompression_traceNonincreasingCP
          (extra := extra) (α := b)))
      hball
  change ((ρ.conditioningIsometryApply
      (ReferenceIsometry.sumInr extra b)).conditioningSumInrCompressed).purifiedBall ε
    ρPlus.conditioningSumInrCompressed at hcompressed
  simpa [conditioningSumInrCompressed_conditioningIsometryApply_sumInr] using hcompressed

/-- Compressing an arbitrary conditioning-register reference isometry transports
a purified ball back to the source conditioning register. -/
theorem purifiedBall_conditioningIsometryCompressed_of_conditioningIsometryApply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    {ρ : SubnormalizedState (Prod a b)}
    {ρPlus : SubnormalizedState (Prod a bPlus)} {ε : ℝ}
    (V : ReferenceIsometry b bPlus)
    (hball : (ρ.conditioningIsometryApply V).purifiedBall ε ρPlus) :
    ρ.purifiedBall ε (ρPlus.conditioningIsometryCompressed V) := by
  have hcompressed :=
    SubnormalizedState.purifiedBall_of_traceNonincreasingCP
      (ρ := ρ.conditioningIsometryApply V)
      (σ := ρPlus) (ε := ε)
      (MatrixMap.kron (Channel.idChannel a).map
        (MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix)))
      (MatrixMap.traceNonincreasingCP_id_kron (a := a)
        (hΦ := referenceIsometry_conjTranspose_traceNonincreasingCP V))
      hball
  change ((ρ.conditioningIsometryApply V).conditioningIsometryCompressed V).purifiedBall ε
    (ρPlus.conditioningIsometryCompressed V) at hcompressed
  simpa using hcompressed

/-- Compressing an arbitrary source-register reference isometry transports a
purified ball back to the source register. -/
theorem purifiedBall_sourceIsometryCompressed_of_sourceIsometryApply
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    {ρ : SubnormalizedState (Prod a b)}
    {ρPlus : SubnormalizedState (Prod aPlus b)} {ε : ℝ}
    (V : ReferenceIsometry a aPlus)
    (hball : (ρ.sourceIsometryApply V).purifiedBall ε ρPlus) :
    ρ.purifiedBall ε (ρPlus.sourceIsometryCompressed V) := by
  have hcompressed :=
    SubnormalizedState.purifiedBall_of_traceNonincreasingCP
      (ρ := ρ.sourceIsometryApply V)
      (σ := ρPlus) (ε := ε)
      (MatrixMap.kron
        (MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix))
        (Channel.idChannel b).map)
      (MatrixMap.traceNonincreasingCP_kron_id (a := b)
        (hΦ := referenceIsometry_conjTranspose_traceNonincreasingCP V))
      hball
  change ((ρ.sourceIsometryApply V).sourceIsometryCompressed V).purifiedBall ε
    (ρPlus.sourceIsometryCompressed V) at hcompressed
  simpa using hcompressed

/-! ## Subnormalized conditional max-entropy exponent -/

theorem psdSqrt_trace_re_pos_of_trace_pos [Nonempty a]
    {ρ : SubnormalizedState a} (hρ : 0 < ρ.matrix.trace.re) :
    0 < (psdSqrt ρ.matrix).trace.re := by
  have hnon : 0 ≤ (psdSqrt ρ.matrix).trace.re :=
    (Matrix.PosSemidef.trace_nonneg (psdSqrt_pos ρ.matrix)).1
  by_contra hnot
  have hle : (psdSqrt ρ.matrix).trace.re ≤ 0 := le_of_not_gt hnot
  have hre : (psdSqrt ρ.matrix).trace.re = 0 := le_antisymm hle hnon
  have htr : (psdSqrt ρ.matrix).trace = 0 := by
    apply Complex.ext
    · exact hre
    · exact (Matrix.PosSemidef.trace_nonneg (psdSqrt_pos ρ.matrix)).2.symm
  have hsqrt_zero : psdSqrt ρ.matrix = 0 :=
    (Matrix.PosSemidef.trace_eq_zero_iff (psdSqrt_pos ρ.matrix)).mp htr
  have hrho_zero : ρ.matrix = 0 := by
    rw [← psdSqrt_mul_self_of_posSemidef ρ.pos, hsqrt_zero]
    simp
  have htrace : ρ.matrix.trace.re = 0 := by simp [hrho_zero]
  linarith

/-- The raw squared-fidelity expression optimized by subnormalized
conditional max-entropy, before applying `log₂`. -/
def conditionalMaxEntropyExponentCandidate
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) : ℝ :=
  (traceNorm (psdSqrt ρ.matrix *
    psdSqrt (identityTensorStateMatrix (a := a) σ))) ^ 2

@[simp]
theorem conditionalMaxEntropyExponentCandidate_eq
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) :
    ρ.conditionalMaxEntropyExponentCandidate σ =
      (traceNorm (psdSqrt ρ.matrix *
        psdSqrt (identityTensorStateMatrix (a := a) σ))) ^ 2 :=
  rfl

/-- The existing subnormalized conditional max-entropy candidate is the
logarithm of the raw endpoint candidate. -/
theorem conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) :
    ρ.conditionalMaxEntropyFidelityCandidate σ =
      log2 (ρ.conditionalMaxEntropyExponentCandidate (a := a) σ) :=
  rfl

omit [Fintype a] in
private theorem rightBlock_identityTensorStateMatrix
    (σ : SubnormalizedState b) (i j : a) :
    ReferenceIsometry.rightBlock (identityTensorStateMatrix (a := a) σ) i j =
      (((1 : CMatrix a) i j) • σ.matrix) := by
  ext x y
  simp [identityTensorStateMatrix, ReferenceIsometry.rightBlock,
    Matrix.kronecker, Matrix.kroneckerMap_apply]

omit [Fintype a] in
@[simp]
theorem identityTensorStateMatrix_referenceIsometryApply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (σ : SubnormalizedState b) (V : ReferenceIsometry b bPlus) :
    identityTensorStateMatrix (a := a) (σ.referenceIsometryApply V) =
      V.applyMatrixRight (identityTensorStateMatrix (a := a) σ) := by
  ext x y
  rw [ReferenceIsometry.applyMatrixRight]
  rw [rightBlock_identityTensorStateMatrix]
  simp [identityTensorStateMatrix, MatrixMap.ofReferenceIsometry_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply]

@[simp]
theorem identityTensorStateMatrix_sumInrCompressedSide
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (σPlus : SubnormalizedState (Sum extra b)) :
    identityTensorStateMatrix (a := a) σPlus.sumInrCompressedSide =
      MatrixMap.kron (Channel.idChannel a).map
        (MatrixMap.sumInrBlockCompression (extra := extra) (α := b))
        (identityTensorStateMatrix (a := a) σPlus) := by
  ext x y
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  simp [identityTensorStateMatrix, sumInrCompressedSide, MatrixMap.sumInrBlockCompression,
    Matrix.kronecker, Matrix.kroneckerMap_apply]

omit [Fintype a] in
private theorem sumBlock22_identityTensorStateMatrix_submatrix_prodSumRightEquiv
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (σPlus : SubnormalizedState (Sum extra b)) :
    Matrix.sumBlock22 ((identityTensorStateMatrix (a := a) σPlus).submatrix
      (ReferenceIsometry.prodSumRightEquiv a extra b)
      (ReferenceIsometry.prodSumRightEquiv a extra b)) =
      identityTensorStateMatrix (a := a) σPlus.sumInrCompressedSide := by
  ext x y
  simp [Matrix.sumBlock22, ReferenceIsometry.prodSumRightEquiv,
    identityTensorStateMatrix, sumInrCompressedSide, MatrixMap.sumInrBlockCompression,
    Matrix.kronecker, Matrix.kroneckerMap_apply]

private theorem sumBlock22_conditioning_matrix_submatrix_prodSumRightEquiv
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρPlus : SubnormalizedState (Prod a (Sum extra b))) :
    Matrix.sumBlock22 (ρPlus.matrix.submatrix
      (ReferenceIsometry.prodSumRightEquiv a extra b)
      (ReferenceIsometry.prodSumRightEquiv a extra b)) =
      ρPlus.conditioningSumInrCompressed.matrix := by
  ext x y
  rw [conditioningSumInrCompressed_matrix]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  simp [Matrix.sumBlock22, ReferenceIsometry.prodSumRightEquiv,
    MatrixMap.sumInrBlockCompression]

/-- The raw trace-norm factor in subnormalized max entropy is unchanged when
the joint state is padded by `sumInr` and an arbitrary padded side candidate is
compressed back to the success block. -/
theorem traceNorm_conditioningIsometryApply_sumInr_mul_sqrt_identityTensorStateMatrix
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) (σPlus : SubnormalizedState (Sum extra b)) :
    traceNorm
        (psdSqrt (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).matrix *
          psdSqrt (identityTensorStateMatrix (a := a) σPlus)) =
      traceNorm
        (psdSqrt ρ.matrix *
          psdSqrt (identityTensorStateMatrix (a := a) σPlus.sumInrCompressedSide)) := by
  let V : ReferenceIsometry b (Sum extra b) := ReferenceIsometry.sumInr extra b
  let A : CMatrix (Prod a b) := psdSqrt ρ.matrix
  let Y : CMatrix (Prod a (Sum extra b)) := identityTensorStateMatrix (a := a) σPlus
  let Yc : CMatrix (Prod a b) :=
    identityTensorStateMatrix (a := a) σPlus.sumInrCompressedSide
  let VA : CMatrix (Prod a (Sum extra b)) := V.applyMatrixRight A
  let VYc : CMatrix (Prod a (Sum extra b)) := V.applyMatrixRight Yc
  let VsqrtYc : CMatrix (Prod a (Sum extra b)) := V.applyMatrixRight (psdSqrt Yc)
  have hleft_sqrt :
      psdSqrt (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).matrix = VA := by
    dsimp [VA, V, A]
    rw [conditioningIsometryApply_matrix]
    exact ReferenceIsometry.psdSqrt_applyMatrixRight_sumInr (a := a) ρ.pos
  have hVA_h : Matrix.conjTranspose VA = VA := by
    rw [← hleft_sqrt]
    exact (psdSqrt_isHermitian
      (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).matrix).eq
  have hsY_h : Matrix.conjTranspose (psdSqrt Y) = psdSqrt Y := by
    exact (psdSqrt_isHermitian Y).eq
  have hVsYc_h : Matrix.conjTranspose VsqrtYc = VsqrtYc := by
    dsimp [VsqrtYc, V]
    rw [← ReferenceIsometry.psdSqrt_applyMatrixRight_sumInr (a := a)
      (identityTensorStateMatrix_posSemidef (a := a) σPlus.sumInrCompressedSide)]
    exact (psdSqrt_isHermitian
      ((ReferenceIsometry.sumInr extra b).applyMatrixRight Yc)).eq
  have hYc_block :
      Matrix.sumBlock22 (Y.submatrix
        (ReferenceIsometry.prodSumRightEquiv a extra b)
        (ReferenceIsometry.prodSumRightEquiv a extra b)) = Yc := by
    dsimp [Y, Yc]
    exact sumBlock22_identityTensorStateMatrix_submatrix_prodSumRightEquiv
      (a := a) σPlus
  have hM :
      (VA * psdSqrt Y) * Matrix.conjTranspose (VA * psdSqrt Y) =
        VA * Y * VA := by
    rw [Matrix.conjTranspose_mul, hsY_h, hVA_h]
    have hsqY : psdSqrt Y * psdSqrt Y = Y := by
      dsimp [Y]
      exact psdSqrt_mul_self_of_posSemidef
        (identityTensorStateMatrix_posSemidef (a := a) σPlus)
    calc
      (VA * psdSqrt Y) * (psdSqrt Y * VA) =
          VA * (psdSqrt Y * psdSqrt Y) * VA := by
            simp [Matrix.mul_assoc]
      _ = VA * Y * VA := by rw [hsqY]
  have hN :
      (VA * VsqrtYc) * Matrix.conjTranspose (VA * VsqrtYc) =
        VA * VYc * VA := by
    rw [Matrix.conjTranspose_mul, hVsYc_h, hVA_h]
    have hsq : VsqrtYc * VsqrtYc = VYc := by
      dsimp [VsqrtYc, VYc, V, Yc]
      rw [ReferenceIsometry.applyMatrixRight_mul]
      rw [psdSqrt_mul_self_of_posSemidef
        (identityTensorStateMatrix_posSemidef (a := a) σPlus.sumInrCompressedSide)]
    calc
      (VA * VsqrtYc) * (VsqrtYc * VA) =
          VA * (VsqrtYc * VsqrtYc) * VA := by
            simp [Matrix.mul_assoc]
      _ = VA * VYc * VA := by rw [hsq]
  have hMN :
      (VA * psdSqrt Y) * Matrix.conjTranspose (VA * psdSqrt Y) =
        (VA * VsqrtYc) * Matrix.conjTranspose (VA * VsqrtYc) := by
    rw [hM, hN]
    calc
      VA * Y * VA =
          V.applyMatrixRight (A * Yc * A) := by
            dsimp [VA, V, A, Y]
            rw [ReferenceIsometry.applyMatrixRight_sumInr_sandwich]
            rw [hYc_block]
      _ = VA * VYc * VA := by
            dsimp [VA, VYc, V]
            rw [ReferenceIsometry.applyMatrixRight_mul]
            rw [ReferenceIsometry.applyMatrixRight_mul]
  rw [hleft_sqrt]
  calc
    traceNorm (VA * psdSqrt Y) =
        traceNorm (VA * VsqrtYc) :=
          traceNorm_eq_of_mul_conjTranspose_eq hMN
    _ = traceNorm (V.applyMatrixRight (A * psdSqrt Yc)) := by
          dsimp [VA, VsqrtYc, V, A]
          rw [ReferenceIsometry.applyMatrixRight_mul]
    _ = traceNorm (A * psdSqrt Yc) := by
          dsimp [V]
          rw [ReferenceIsometry.traceNorm_applyMatrixRight_sumInr]
    _ = traceNorm (psdSqrt ρ.matrix *
          psdSqrt (identityTensorStateMatrix (a := a) σPlus.sumInrCompressedSide)) := by
          rfl

/-- A right-summand-supported side candidate tests an arbitrary enlarged joint
state through exactly the compressed joint block. -/
theorem traceNorm_conditioningSumInrCompressed_mul_sqrt_identityTensorStateMatrix_referenceIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρPlus : SubnormalizedState (Prod a (Sum extra b))) (σ : SubnormalizedState b) :
    traceNorm
        (psdSqrt ρPlus.conditioningSumInrCompressed.matrix *
          psdSqrt (identityTensorStateMatrix (a := a) σ)) =
      traceNorm
        (psdSqrt ρPlus.matrix *
          psdSqrt (identityTensorStateMatrix (a := a)
            (σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b)))) := by
  let V : ReferenceIsometry b (Sum extra b) := ReferenceIsometry.sumInr extra b
  let A : CMatrix (Prod a b) := psdSqrt ρPlus.conditioningSumInrCompressed.matrix
  let Y : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let VA : CMatrix (Prod a (Sum extra b)) := V.applyMatrixRight A
  let VsqrtY : CMatrix (Prod a (Sum extra b)) := V.applyMatrixRight (psdSqrt Y)
  have hside :
      psdSqrt (identityTensorStateMatrix (a := a)
          (σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b))) =
        VsqrtY := by
    dsimp [VsqrtY, V, Y]
    rw [identityTensorStateMatrix_referenceIsometryApply]
    exact ReferenceIsometry.psdSqrt_applyMatrixRight_sumInr (a := a)
      (identityTensorStateMatrix_posSemidef (a := a) σ)
  have hVA_h : Matrix.conjTranspose VA = VA := by
    dsimp [VA, V, A]
    change Matrix.conjTranspose
        ((ReferenceIsometry.sumInr extra b).applyMatrixRight
          (psdSqrt ρPlus.conditioningSumInrCompressed.matrix)) =
      (ReferenceIsometry.sumInr extra b).applyMatrixRight
        (psdSqrt ρPlus.conditioningSumInrCompressed.matrix)
    rw [← ReferenceIsometry.psdSqrt_applyMatrixRight_sumInr (a := a)
      ρPlus.conditioningSumInrCompressed.pos]
    exact (psdSqrt_isHermitian
      ((ReferenceIsometry.sumInr extra b).applyMatrixRight
        ρPlus.conditioningSumInrCompressed.matrix)).eq
  have hVsqrtY_h : Matrix.conjTranspose VsqrtY = VsqrtY := by
    dsimp [VsqrtY, V, Y]
    rw [← ReferenceIsometry.psdSqrt_applyMatrixRight_sumInr (a := a)
      (identityTensorStateMatrix_posSemidef (a := a) σ)]
    exact (psdSqrt_isHermitian
      ((ReferenceIsometry.sumInr extra b).applyMatrixRight Y)).eq
  have hVAA :
      VA * VA =
        V.applyMatrixRight ρPlus.conditioningSumInrCompressed.matrix := by
    dsimp [VA, V, A]
    change (ReferenceIsometry.sumInr extra b).applyMatrixRight
        (psdSqrt ρPlus.conditioningSumInrCompressed.matrix) *
        (ReferenceIsometry.sumInr extra b).applyMatrixRight
          (psdSqrt ρPlus.conditioningSumInrCompressed.matrix) =
      (ReferenceIsometry.sumInr extra b).applyMatrixRight
        ρPlus.conditioningSumInrCompressed.matrix
    rw [ReferenceIsometry.applyMatrixRight_mul]
    rw [psdSqrt_mul_self_of_posSemidef ρPlus.conditioningSumInrCompressed.pos]
  have hsandwich :
      VsqrtY * ρPlus.matrix * VsqrtY =
        VsqrtY *
          (V.applyMatrixRight ρPlus.conditioningSumInrCompressed.matrix) *
            VsqrtY := by
    calc
      VsqrtY * ρPlus.matrix * VsqrtY =
          V.applyMatrixRight
            (psdSqrt Y *
              Matrix.sumBlock22 (ρPlus.matrix.submatrix
                (ReferenceIsometry.prodSumRightEquiv a extra b)
                (ReferenceIsometry.prodSumRightEquiv a extra b)) *
              psdSqrt Y) := by
            dsimp [VsqrtY, V]
            rw [ReferenceIsometry.applyMatrixRight_sumInr_sandwich]
      _ = V.applyMatrixRight
            (psdSqrt Y * ρPlus.conditioningSumInrCompressed.matrix * psdSqrt Y) := by
            rw [sumBlock22_conditioning_matrix_submatrix_prodSumRightEquiv
              ρPlus]
      _ = VsqrtY *
          (V.applyMatrixRight ρPlus.conditioningSumInrCompressed.matrix) *
            VsqrtY := by
            dsimp [VsqrtY, V]
            rw [ReferenceIsometry.applyMatrixRight_mul]
            rw [ReferenceIsometry.applyMatrixRight_mul]
  rw [← ReferenceIsometry.traceNorm_applyMatrixRight_sumInr
      (a := a) (extra := extra)
      (psdSqrt ρPlus.conditioningSumInrCompressed.matrix *
        psdSqrt (identityTensorStateMatrix (a := a) σ))]
  rw [← ReferenceIsometry.applyMatrixRight_mul]
  change traceNorm (VA * VsqrtY) =
    traceNorm (psdSqrt ρPlus.matrix * psdSqrt (identityTensorStateMatrix (a := a)
      (σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b))))
  rw [hside]
  apply traceNorm_eq_of_conjTranspose_mul_eq
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hVA_h, hVsqrtY_h]
  rw [psdSqrt_isHermitian ρPlus.matrix]
  calc
    VsqrtY * VA * (VA * VsqrtY) =
        VsqrtY * (VA * VA) * VsqrtY := by simp [Matrix.mul_assoc]
    _ = VsqrtY * (V.applyMatrixRight ρPlus.conditioningSumInrCompressed.matrix) *
          VsqrtY := by rw [hVAA]
    _ = VsqrtY * ρPlus.matrix * VsqrtY := by rw [← hsandwich]
    _ = VsqrtY * psdSqrt ρPlus.matrix * (psdSqrt ρPlus.matrix * VsqrtY) := by
          have hsqrt :
              ρPlus.matrix = psdSqrt ρPlus.matrix * psdSqrt ρPlus.matrix :=
            (psdSqrt_mul_self_of_posSemidef ρPlus.pos).symm
          conv_lhs => rw [hsqrt]
          simp [Matrix.mul_assoc]

/-- Applying the same concrete right-summand padding to the joint state and the
side candidate preserves the subnormalized max-entropy exponent candidate. -/
theorem conditionalMaxEntropyExponentCandidate_referenceIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMaxEntropyExponentCandidate
        (a := a) (σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b)) =
      ρ.conditionalMaxEntropyExponentCandidate (a := a) σ := by
  rw [conditionalMaxEntropyExponentCandidate_eq, conditionalMaxEntropyExponentCandidate_eq]
  have hleft :
      psdSqrt (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).matrix =
        (ReferenceIsometry.sumInr extra b).applyMatrixRight (psdSqrt ρ.matrix) := by
    rw [conditioningIsometryApply_matrix]
    exact ReferenceIsometry.psdSqrt_applyMatrixRight_sumInr (a := a) ρ.pos
  have hside :
      psdSqrt (identityTensorStateMatrix (a := a)
          (σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b))) =
        (ReferenceIsometry.sumInr extra b).applyMatrixRight
          (psdSqrt (identityTensorStateMatrix (a := a) σ)) := by
    rw [identityTensorStateMatrix_referenceIsometryApply]
    exact ReferenceIsometry.psdSqrt_applyMatrixRight_sumInr (a := a)
      (identityTensorStateMatrix_posSemidef (a := a) σ)
  rw [hleft, hside]
  rw [ReferenceIsometry.applyMatrixRight_mul]
  rw [ReferenceIsometry.traceNorm_applyMatrixRight_sumInr]

/-- A padded joint state tested against an arbitrary padded side candidate has
the same raw max-entropy exponent candidate as the source joint state tested
against the compressed side candidate. -/
theorem conditionalMaxEntropyExponentCandidate_conditioningIsometryApply_sumInr_compressedSide
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) (σPlus : SubnormalizedState (Sum extra b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMaxEntropyExponentCandidate
        (a := a) σPlus =
      ρ.conditionalMaxEntropyExponentCandidate (a := a) σPlus.sumInrCompressedSide := by
  rw [conditionalMaxEntropyExponentCandidate_eq, conditionalMaxEntropyExponentCandidate_eq]
  rw [traceNorm_conditioningIsometryApply_sumInr_mul_sqrt_identityTensorStateMatrix]

/-- Testing an arbitrary enlarged joint state against a side candidate
supported on the right summand is exactly testing the compressed joint state. -/
theorem conditionalMaxEntropyExponentCandidate_conditioningSumInrCompressed_referenceIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρPlus : SubnormalizedState (Prod a (Sum extra b))) (σ : SubnormalizedState b) :
    ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyExponentCandidate
        (a := a) σ =
      ρPlus.conditionalMaxEntropyExponentCandidate (a := a)
        (σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b)) := by
  rw [conditionalMaxEntropyExponentCandidate_eq, conditionalMaxEntropyExponentCandidate_eq]
  rw [traceNorm_conditioningSumInrCompressed_mul_sqrt_identityTensorStateMatrix_referenceIsometryApply_sumInr]

/-- The logarithmic max-entropy candidate is unchanged after testing a padded
joint state against an arbitrary padded side candidate and compressing the side
candidate back to the source register. -/
theorem conditionalMaxEntropyFidelityCandidate_conditioningIsometryApply_sumInr_compressedSide
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) (σPlus : SubnormalizedState (Sum extra b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMaxEntropyFidelityCandidate
        (a := a) σPlus =
      ρ.conditionalMaxEntropyFidelityCandidate (a := a) σPlus.sumInrCompressedSide := by
  rw [conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate,
    conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate,
    conditionalMaxEntropyExponentCandidate_conditioningIsometryApply_sumInr_compressedSide]

/-- The raw endpoint exponent
`sup_σ ‖√ρ_AB √(I_A ⊗ σ_B)‖₁²` for subnormalized side states. -/
def conditionalMaxEntropyExponentValueSet
    (ρ : SubnormalizedState (Prod a b)) : Set ℝ :=
  {x : ℝ | ∃ σ : SubnormalizedState b,
    x = ρ.conditionalMaxEntropyExponentCandidate (a := a) σ}

@[simp]
theorem conditionalMaxEntropyExponentValueSet_eq
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMaxEntropyExponentValueSet (a := a) =
      {x : ℝ | ∃ σ : SubnormalizedState b,
        x = ρ.conditionalMaxEntropyExponentCandidate (a := a) σ} :=
  rfl

/-- Positive raw max-entropy exponent candidate values for subnormalized
states. The positivity filter is required for logarithmic endpoint bridges. -/
def conditionalMaxEntropyPositiveExponentValueSet
    (ρ : SubnormalizedState (Prod a b)) : Set ℝ :=
  {x : ℝ | ∃ σ : SubnormalizedState b,
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
      x = ρ.conditionalMaxEntropyExponentCandidate (a := a) σ}

@[simp]
theorem conditionalMaxEntropyPositiveExponentValueSet_eq
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a) =
      {x : ℝ | ∃ σ : SubnormalizedState b,
        0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
          x = ρ.conditionalMaxEntropyExponentCandidate (a := a) σ} :=
  rfl

/-- The positive-candidate raw endpoint exponent for subnormalized states. -/
def conditionalMaxEntropyPositiveExponent
    (ρ : SubnormalizedState (Prod a b)) : ℝ :=
  sSup (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a))

@[simp]
theorem conditionalMaxEntropyPositiveExponent_eq
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMaxEntropyPositiveExponent =
      sSup (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)) :=
  rfl

/-- Definition-level max-entropy candidates whose raw exponent is strictly
positive. -/
def conditionalMaxEntropyPositiveValueSet
    (ρ : SubnormalizedState (Prod a b)) : Set ℝ :=
  {h : ℝ | ∃ σ : SubnormalizedState b,
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
      h = ρ.conditionalMaxEntropyFidelityCandidate σ}

@[simp]
theorem conditionalMaxEntropyPositiveValueSet_eq
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMaxEntropyPositiveValueSet (a := a) =
      {h : ℝ | ∃ σ : SubnormalizedState b,
        0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
          h = ρ.conditionalMaxEntropyFidelityCandidate σ} :=
  rfl

/-- Concrete right-summand padding preserves the positive raw endpoint exponent
candidate set for subnormalized max-entropy. -/
theorem conditionalMaxEntropyPositiveExponentValueSet_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMaxEntropyPositiveExponentValueSet
        (a := a) =
      ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a) := by
  ext x
  constructor
  · rintro ⟨σPlus, hpos, rfl⟩
    refine ⟨σPlus.sumInrCompressedSide, ?_, ?_⟩
    · rwa [← conditionalMaxEntropyExponentCandidate_conditioningIsometryApply_sumInr_compressedSide
        (a := a) ρ σPlus]
    · rw [conditionalMaxEntropyExponentCandidate_conditioningIsometryApply_sumInr_compressedSide
        (a := a) ρ σPlus]
  · rintro ⟨σ, hpos, rfl⟩
    refine ⟨σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b), ?_, ?_⟩
    · rwa [conditionalMaxEntropyExponentCandidate_referenceIsometryApply_sumInr
        (a := a) (extra := extra) ρ σ]
    · rw [conditionalMaxEntropyExponentCandidate_referenceIsometryApply_sumInr
        (a := a) (extra := extra) ρ σ]

/-- Compatibility name for the positive-candidate subnormalized conditional
max-entropy. -/
def conditionalMaxEntropyPositive (ρ : SubnormalizedState (Prod a b)) : ℝ :=
  sSup (ρ.conditionalMaxEntropyPositiveValueSet (a := a))

@[simp]
theorem conditionalMaxEntropyPositive_eq
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMaxEntropyPositive =
      sSup (ρ.conditionalMaxEntropyPositiveValueSet (a := a)) :=
  rfl

/-- Concrete right-summand padding preserves the positive logarithmic
max-entropy candidate set. -/
theorem conditionalMaxEntropyPositiveValueSet_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMaxEntropyPositiveValueSet
        (a := a) =
      ρ.conditionalMaxEntropyPositiveValueSet (a := a) := by
  ext h
  constructor
  · rintro ⟨σPlus, hpos, rfl⟩
    refine ⟨σPlus.sumInrCompressedSide, ?_, ?_⟩
    · rwa [← conditionalMaxEntropyExponentCandidate_conditioningIsometryApply_sumInr_compressedSide
        (a := a) ρ σPlus]
    · rw [conditionalMaxEntropyFidelityCandidate_conditioningIsometryApply_sumInr_compressedSide
        (a := a) ρ σPlus]
  · rintro ⟨σ, hpos, rfl⟩
    refine ⟨σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b), ?_, ?_⟩
    · rwa [conditionalMaxEntropyExponentCandidate_referenceIsometryApply_sumInr
        (a := a) (extra := extra) ρ σ]
    · rw [conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate,
        conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate,
        conditionalMaxEntropyExponentCandidate_referenceIsometryApply_sumInr]

/-- Concrete right-summand padding preserves the positive raw endpoint exponent
for subnormalized max-entropy. -/
theorem conditionalMaxEntropyPositiveExponent_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMaxEntropyPositiveExponent
        (a := a) =
      ρ.conditionalMaxEntropyPositiveExponent (a := a) := by
  rw [conditionalMaxEntropyPositiveExponent_eq, conditionalMaxEntropyPositiveExponent_eq,
    conditionalMaxEntropyPositiveExponentValueSet_conditioningIsometryApply_sumInr]

/-- Concrete right-summand padding preserves subnormalized conditional
max-entropy. -/
theorem conditionalMaxEntropy_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMaxEntropyRaw =
      ρ.conditionalMaxEntropyRaw := by
  change sSup ((ρ.conditioningIsometryApply
      (ReferenceIsometry.sumInr extra b)).conditionalMaxEntropyPositiveValueSet (a := a)) =
    sSup (ρ.conditionalMaxEntropyPositiveValueSet (a := a))
  rw [conditionalMaxEntropyPositiveValueSet_conditioningIsometryApply_sumInr]

/-- Exact-padding smooth min-entropy candidates: the smoothing witness lives in
the source register and is then padded by the concrete right-summand embedding. -/
def SumInrExactSmoothConditionalMinEntropyCandidate
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) (ε h : ℝ) : Prop :=
  ∃ ρ' : SubnormalizedState (Prod a b),
    ρ.purifiedBall ε ρ' ∧
      h = (ρ'.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropyRaw

/-- Exact-padding smooth max-entropy candidates: the smoothing witness lives in
the source register and is then padded by the concrete right-summand embedding. -/
def SumInrExactSmoothConditionalMaxEntropyCandidate
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) (ε h : ℝ) : Prop :=
  ∃ ρ' : SubnormalizedState (Prod a b),
    ρ.purifiedBall ε ρ' ∧
      h = (ρ'.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMaxEntropyRaw

/-- Any smooth min-entropy witness for the padded conditioning register
compresses to a source-register witness with at least as large endpoint value,
under the small-radius positive-trace condition. -/
theorem SmoothConditionalMinEntropyCandidateRaw.conditioningIsometryApply_sumInr_compress
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε h : ℝ}
    (hε : ε < Real.sqrt ρ.matrix.trace.re)
    (hcand :
      SmoothConditionalMinEntropyCandidateRaw (a := a)
        (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)) ε h) :
    ∃ h' : ℝ, SmoothConditionalMinEntropyCandidateRaw (a := a) ρ ε h' ∧ h ≤ h' := by
  rcases hcand with ⟨ρPlus', hball, rfl⟩
  have hballCompressed :
      ρ.purifiedBall ε ρPlus'.conditioningSumInrCompressed :=
    purifiedBall_conditioningSumInrCompressed_of_conditioningIsometryApply_sumInr
      (a := a) (extra := extra) hball
  have hplus_pos :
      0 < ρPlus'.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)) ρPlus'
      (by
        rw [conditioningIsometryApply_trace_re]
        exact hε)
      hball
  have hcompressed_pos :
      0 < ρPlus'.conditioningSumInrCompressed.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace ρ
      ρPlus'.conditioningSumInrCompressed hε hballCompressed
  refine ⟨ρPlus'.conditioningSumInrCompressed.conditionalMinEntropyRaw,
    ⟨ρPlus'.conditioningSumInrCompressed, hballCompressed, rfl⟩, ?_⟩
  exact conditionalMinEntropy_le_conditioningSumInrCompressed
    (a := a) (extra := extra) ρPlus' hplus_pos hcompressed_pos

/-- Any smooth min-entropy witness for an arbitrarily isometrically enlarged
conditioning register compresses to a source-register witness with at least as
large endpoint value, under the small-radius positive-trace condition. -/
theorem SmoothConditionalMinEntropyCandidateRaw.conditioningIsometryApply_compress
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    [Nonempty a] [Nonempty b] [Nonempty bPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry b bPlus) {ε h : ℝ}
    (hε : ε < Real.sqrt ρ.matrix.trace.re)
    (hcand :
      SmoothConditionalMinEntropyCandidateRaw (a := a)
        (ρ.conditioningIsometryApply V) ε h) :
    ∃ h' : ℝ, SmoothConditionalMinEntropyCandidateRaw (a := a) ρ ε h' ∧ h ≤ h' := by
  rcases hcand with ⟨ρPlus', hball, rfl⟩
  have hballCompressed :
      ρ.purifiedBall ε (ρPlus'.conditioningIsometryCompressed V) :=
    purifiedBall_conditioningIsometryCompressed_of_conditioningIsometryApply
      (a := a) V hball
  have hplus_pos :
      0 < ρPlus'.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      (ρ.conditioningIsometryApply V) ρPlus'
      (by
        rw [conditioningIsometryApply_trace_re]
        exact hε)
      hball
  have hcompressed_pos :
      0 < (ρPlus'.conditioningIsometryCompressed V).matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace ρ
      (ρPlus'.conditioningIsometryCompressed V) hε hballCompressed
  refine ⟨(ρPlus'.conditioningIsometryCompressed V).conditionalMinEntropyRaw,
    ⟨ρPlus'.conditioningIsometryCompressed V, hballCompressed, rfl⟩, ?_⟩
  exact conditionalMinEntropy_le_conditioningIsometryCompressed
    (a := a) ρPlus' V hplus_pos hcompressed_pos

/-- Smooth min-entropy candidates transport forward along an arbitrary
conditioning-register reference isometry with the same endpoint value. -/
theorem SmoothConditionalMinEntropyCandidateRaw.conditioningIsometryApply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    [Nonempty a] [Nonempty b] [Nonempty bPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry b bPlus) {ε h : ℝ}
    (hε : ε < Real.sqrt ρ.matrix.trace.re)
    (hcand : SmoothConditionalMinEntropyCandidateRaw (a := a) ρ ε h) :
    SmoothConditionalMinEntropyCandidateRaw (a := a) (ρ.conditioningIsometryApply V) ε h := by
  rcases hcand with ⟨ρ', hball, rfl⟩
  have hρ' : 0 < ρ'.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace ρ ρ' hε hball
  refine ⟨ρ'.conditioningIsometryApply V,
    purifiedBall_conditioningIsometryApply (a := a) V hball, ?_⟩
  rw [conditionalMinEntropy_conditioningIsometryApply (a := a) ρ' hρ' V]

/-- Any smooth min-entropy witness for an arbitrarily isometrically enlarged
source register compresses to a source-register witness with at least as large
endpoint value, under the small-radius positive-trace condition. -/
theorem SmoothConditionalMinEntropyCandidateRaw.sourceIsometryApply_compress
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    [Nonempty a] [Nonempty b] [Nonempty aPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry a aPlus) {ε h : ℝ}
    (hε : ε < Real.sqrt ρ.matrix.trace.re)
    (hcand :
      SmoothConditionalMinEntropyCandidateRaw (a := aPlus)
        (ρ.sourceIsometryApply V) ε h) :
    ∃ h' : ℝ, SmoothConditionalMinEntropyCandidateRaw (a := a) ρ ε h' ∧ h ≤ h' := by
  rcases hcand with ⟨ρPlus', hball, rfl⟩
  have hballCompressed :
      ρ.purifiedBall ε (ρPlus'.sourceIsometryCompressed V) :=
    purifiedBall_sourceIsometryCompressed_of_sourceIsometryApply
      (a := a) V hball
  have hplus_pos :
      0 < ρPlus'.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      (ρ.sourceIsometryApply V) ρPlus'
      (by
        rw [sourceIsometryApply_trace_re]
        exact hε)
      hball
  have hcompressed_pos :
      0 < (ρPlus'.sourceIsometryCompressed V).matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace ρ
      (ρPlus'.sourceIsometryCompressed V) hε hballCompressed
  refine ⟨(ρPlus'.sourceIsometryCompressed V).conditionalMinEntropyRaw,
    ⟨ρPlus'.sourceIsometryCompressed V, hballCompressed, rfl⟩, ?_⟩
  exact conditionalMinEntropy_le_sourceIsometryCompressed
    (a := a) ρPlus' V hplus_pos hcompressed_pos

/-- Smooth min-entropy candidates transport forward along an arbitrary
source-register reference isometry with the same endpoint value. -/
theorem SmoothConditionalMinEntropyCandidateRaw.sourceIsometryApply
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    [Nonempty a] [Nonempty b] [Nonempty aPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry a aPlus) {ε h : ℝ}
    (hε : ε < Real.sqrt ρ.matrix.trace.re)
    (hcand : SmoothConditionalMinEntropyCandidateRaw (a := a) ρ ε h) :
    SmoothConditionalMinEntropyCandidateRaw (a := aPlus) (ρ.sourceIsometryApply V) ε h := by
  rcases hcand with ⟨ρ', hball, rfl⟩
  have hρ' : 0 < ρ'.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace ρ ρ' hε hball
  refine ⟨ρ'.sourceIsometryApply V,
    purifiedBall_sourceIsometryApply (a := a) V hball, ?_⟩
  rw [conditionalMinEntropy_sourceIsometryApply (a := a) ρ' hρ' V]

/-- If the center is fixed by source-coordinate pinching, every smooth
min-entropy candidate can be replaced by a pinched candidate with no smaller
ordinary endpoint value. This is the candidate-level classical-smoothing
regularization step. -/
theorem SmoothConditionalMinEntropyCandidateRaw.sourceCoordinatePinch_of_fixed
    [Nonempty a] [Nonempty b]
    {ρ : SubnormalizedState (Prod a b)} {ε h : ℝ}
    (hρ : ρ.sourceCoordinatePinch = ρ)
    (hε : ε < Real.sqrt ρ.matrix.trace.re)
    (hcand : SmoothConditionalMinEntropyCandidateRaw (a := a) ρ ε h) :
    ∃ h' : ℝ, SmoothConditionalMinEntropyCandidateRaw (a := a) ρ ε h' ∧ h ≤ h' := by
  rcases hcand with ⟨ρ', hball, rfl⟩
  have hρ' : 0 < ρ'.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace ρ ρ' hε hball
  refine ⟨ρ'.sourceCoordinatePinch.conditionalMinEntropyRaw,
    ⟨ρ'.sourceCoordinatePinch,
      ρ.purifiedBall_sourceCoordinatePinch_of_fixed hρ hball, rfl⟩, ?_⟩
  exact ρ'.conditionalMinEntropy_le_sourceCoordinatePinch_of_trace_pos hρ'

/-- Under the small-radius condition used by the scaled-pure smooth-duality
surface, exact `sumInr` padding does not change smooth min-entropy candidates. -/
theorem sumInrExactSmoothConditionalMinEntropyCandidate_iff
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε h : ℝ}
    (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    SumInrExactSmoothConditionalMinEntropyCandidate (a := a) (extra := extra) ρ ε h ↔
      SmoothConditionalMinEntropyCandidateRaw (a := a) ρ ε h := by
  constructor
  · rintro ⟨ρ', hball, rfl⟩
    refine ⟨ρ', hball, ?_⟩
    rw [conditionalMinEntropy_conditioningIsometryApply_sumInr (a := a)
      (extra := extra) ρ'
      (SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace ρ ρ' hε hball)]
  · rintro ⟨ρ', hball, rfl⟩
    refine ⟨ρ', hball, ?_⟩
    rw [conditionalMinEntropy_conditioningIsometryApply_sumInr (a := a)
      (extra := extra) ρ'
      (SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace ρ ρ' hε hball)]

/-- Exact `sumInr` padding does not change smooth max-entropy candidates. -/
theorem sumInrExactSmoothConditionalMaxEntropyCandidate_iff
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (ρ : SubnormalizedState (Prod a b)) {ε h : ℝ} :
    SumInrExactSmoothConditionalMaxEntropyCandidate (a := a) (extra := extra) ρ ε h ↔
      SmoothConditionalMaxEntropyCandidateRaw (a := a) ρ ε h := by
  constructor
  · rintro ⟨ρ', hball, rfl⟩
    refine ⟨ρ', hball, ?_⟩
    rw [conditionalMaxEntropy_conditioningIsometryApply_sumInr (a := a)
      (extra := extra) ρ']
  · rintro ⟨ρ', hball, rfl⟩
    refine ⟨ρ', hball, ?_⟩
    rw [conditionalMaxEntropy_conditioningIsometryApply_sumInr (a := a)
      (extra := extra) ρ']

theorem conditionalMaxEntropyExponentCandidate_nonneg
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) :
    0 ≤ ρ.conditionalMaxEntropyExponentCandidate (a := a) σ := by
  exact sq_nonneg _

omit [Fintype a] in
theorem identityTensorStateMatrix_normalize_smul
    (σ : SubnormalizedState b) (hσ : σ.matrix.trace.re ≠ 0) :
    identityTensorStateMatrix (a := a) σ =
      (σ.matrix.trace.re : ℂ) •
        State.identityTensorStateMatrix (a := a) (σ.normalize hσ) := by
  ext x y
  have hσC : ((σ.matrix.trace.re : ℂ) ≠ 0) := by
    exact_mod_cast hσ
  simp [identityTensorStateMatrix, State.identityTensorStateMatrix,
    SubnormalizedState.normalize_matrix, Matrix.kronecker, Matrix.kroneckerMap_apply]
  field_simp [hσC]

theorem conditionalMaxEntropyExponentCandidate_eq_zero_of_side_trace_zero
    (ρ : SubnormalizedState (Prod a b)) {σ : SubnormalizedState b}
    (hσ : σ.matrix.trace.re = 0) :
    ρ.conditionalMaxEntropyExponentCandidate (a := a) σ = 0 := by
  have htrace : σ.matrix.trace = 0 := by
    apply Complex.ext
    · exact hσ
    · exact σ.trace_im_zero
  have hσ_zero : σ.matrix = 0 :=
    (Matrix.PosSemidef.trace_eq_zero_iff σ.pos).mp htrace
  have hside : identityTensorStateMatrix (a := a) σ = 0 := by
    ext x y
    simp [identityTensorStateMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
      hσ_zero]
  unfold conditionalMaxEntropyExponentCandidate
  rw [hside]
  simp

theorem conditionalMaxEntropyExponentCandidate_ofStateScale_normalize
    (ρ : State (Prod a b)) (σ : SubnormalizedState b)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hσ : 0 < σ.matrix.trace.re) :
    (SubnormalizedState.ofStateScale ρ t ht.le ht1).conditionalMaxEntropyExponentCandidate
        (a := a) σ =
      t * σ.matrix.trace.re *
        ρ.conditionalMaxEntropyExponentCandidate (a := a) (σ.normalize hσ.ne') := by
  let s : ℝ := σ.matrix.trace.re
  let M : CMatrix (Prod a b) :=
    ρ.sqrtMatrix * psdSqrt (State.identityTensorStateMatrix (a := a)
      (σ.normalize hσ.ne'))
  have hs_nonneg : 0 ≤ s := le_of_lt hσ
  have hsqrt_left :
      psdSqrt (SubnormalizedState.ofStateScale ρ t ht.le ht1).matrix =
        ((Real.sqrt t : ℝ) : ℂ) • ρ.sqrtMatrix := by
    rw [SubnormalizedState.ofStateScale_matrix]
    simpa [State.sqrtMatrix] using
      (psdSqrt_real_smul (a := Prod a b) ht.le (M := ρ.matrix) ρ.pos)
  have hside :
      identityTensorStateMatrix (a := a) σ =
        (s : ℂ) • State.identityTensorStateMatrix (a := a) (σ.normalize hσ.ne') := by
    dsimp [s]
    exact identityTensorStateMatrix_normalize_smul (a := a) σ hσ.ne'
  have hsqrt_side :
      psdSqrt (identityTensorStateMatrix (a := a) σ) =
        ((Real.sqrt s : ℝ) : ℂ) •
          psdSqrt (State.identityTensorStateMatrix (a := a) (σ.normalize hσ.ne')) := by
    rw [hside]
    exact psdSqrt_real_smul (a := Prod a b) hs_nonneg
      (M := State.identityTensorStateMatrix (a := a) (σ.normalize hσ.ne'))
      (State.identityTensorStateMatrix_posSemidef (a := a) (σ.normalize hσ.ne'))
  have hproduct :
      psdSqrt (SubnormalizedState.ofStateScale ρ t ht.le ht1).matrix *
          psdSqrt (identityTensorStateMatrix (a := a) σ) =
        (((Real.sqrt t * Real.sqrt s : ℝ) : ℂ) • M) := by
    rw [hsqrt_left, hsqrt_side]
    dsimp [M]
    ext x y
    simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc, mul_left_comm]
  rw [conditionalMaxEntropyExponentCandidate_eq,
    State.conditionalMaxEntropyExponentCandidate_eq]
  rw [hproduct]
  rw [traceNorm_real_smul_eq (mul_nonneg (Real.sqrt_nonneg t) (Real.sqrt_nonneg s)) M]
  have hsqrt_t_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  have hsqrt_s_sq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs_nonneg
  let n : ℝ := traceNorm M
  calc
    (Real.sqrt t * Real.sqrt s * n) ^ 2 =
        (Real.sqrt t) ^ 2 * (Real.sqrt s) ^ 2 * n ^ 2 := by ring
    _ = t * s * n ^ 2 := by rw [hsqrt_t_sq, hsqrt_s_sq]

theorem conditionalMaxEntropyExponentCandidate_ofStateScale_toSubnormalized
    (ρ : State (Prod a b)) (τ : State b)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (SubnormalizedState.ofStateScale ρ t ht.le ht1).conditionalMaxEntropyExponentCandidate
        (a := a) τ.toSubnormalized =
      t * ρ.conditionalMaxEntropyExponentCandidate (a := a) τ := by
  have hτtr_pos : 0 < τ.toSubnormalized.matrix.trace.re := by
    rw [State.toSubnormalized_trace]
    norm_num
  have hnorm : τ.toSubnormalized.normalize hτtr_pos.ne' = τ := by
    apply State.ext
    rw [SubnormalizedState.normalize_matrix, State.toSubnormalized_matrix,
      τ.trace_eq_one]
    simp
  rw [conditionalMaxEntropyExponentCandidate_ofStateScale_normalize
    (a := a) ρ τ.toSubnormalized ht ht1 hτtr_pos, hnorm]
  rw [State.toSubnormalized_trace]
  norm_num

theorem conditionalMaxEntropyExponentCandidate_maximallyMixed_pos_of_trace_pos
    [Nonempty a] [Nonempty b] {ρ : SubnormalizedState (Prod a b)}
    (hρ : 0 < ρ.matrix.trace.re) :
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := a)
      (State.maximallyMixed b).toSubnormalized := by
  let c : ℝ := (Fintype.card b : ℝ)⁻¹
  have hc_nonneg : 0 ≤ c := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hc_pos : 0 < Real.sqrt c := by
    have hcard_pos : 0 < (Fintype.card b : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    exact Real.sqrt_pos.mpr (inv_pos.mpr hcard_pos)
  have hsqrt_id :
      psdSqrt (identityTensorStateMatrix (a := a)
          (State.maximallyMixed b).toSubnormalized) =
        (((Real.sqrt c : ℝ) : ℂ) • (1 : CMatrix (Prod a b))) := by
    have hid :
        identityTensorStateMatrix (a := a) (State.maximallyMixed b).toSubnormalized =
          ((((Fintype.card b : ℝ)⁻¹ : ℝ) : ℂ) •
            (1 : CMatrix (Prod a b))) := by
      ext x y
      by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;>
        simp [identityTensorStateMatrix, State.maximallyMixed, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff, h1, h2]
    rw [hid]
    exact psdSqrt_real_smul_one (a := Prod a b) hc_nonneg
  have htrace_eq :
      (psdSqrt ρ.matrix *
          psdSqrt (identityTensorStateMatrix (a := a)
            (State.maximallyMixed b).toSubnormalized)).trace =
        ((Real.sqrt c : ℝ) : ℂ) * (psdSqrt ρ.matrix).trace := by
    rw [hsqrt_id]
    simp [Matrix.trace_smul]
  have htrace_abs_pos :
      0 < Complex.abs ((psdSqrt ρ.matrix *
          psdSqrt (identityTensorStateMatrix (a := a)
            (State.maximallyMixed b).toSubnormalized)).trace) := by
    rw [htrace_eq]
    change 0 < ‖((Real.sqrt c : ℝ) : ℂ) * (psdSqrt ρ.matrix).trace‖
    rw [norm_mul]
    have htr_ne : (psdSqrt ρ.matrix).trace ≠ 0 := by
      intro hzero
      have hre : (psdSqrt ρ.matrix).trace.re = 0 := by rw [hzero]; rfl
      have hpos : 0 < (psdSqrt ρ.matrix).trace.re :=
        psdSqrt_trace_re_pos_of_trace_pos (a := Prod a b) hρ
      linarith
    have hc_ne : (((Real.sqrt c : ℝ) : ℂ) : ℂ) ≠ 0 := by
      exact_mod_cast hc_pos.ne'
    exact mul_pos (norm_pos_iff.mpr hc_ne) (norm_pos_iff.mpr htr_ne)
  have htn_pos :
      0 < traceNorm (psdSqrt ρ.matrix *
        psdSqrt (identityTensorStateMatrix (a := a)
          (State.maximallyMixed b).toSubnormalized)) :=
    lt_of_lt_of_le htrace_abs_pos (trace_abs_le_traceNorm _)
  unfold conditionalMaxEntropyExponentCandidate
  exact sq_pos_of_pos htn_pos

theorem conditionalMaxEntropyPositiveExponentValueSet_nonempty_of_trace_pos
    [Nonempty a] [Nonempty b] {ρ : SubnormalizedState (Prod a b)}
    (hρ : 0 < ρ.matrix.trace.re) :
    (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)).Nonempty :=
  ⟨ρ.conditionalMaxEntropyExponentCandidate (a := a)
      (State.maximallyMixed b).toSubnormalized,
    (State.maximallyMixed b).toSubnormalized,
    ρ.conditionalMaxEntropyExponentCandidate_maximallyMixed_pos_of_trace_pos
      (a := a) hρ,
    rfl⟩

theorem conditionalMaxEntropyExponentValueSet_nonempty_of_trace_pos
    [Nonempty a] [Nonempty b] {ρ : SubnormalizedState (Prod a b)}
    (_hρ : 0 < ρ.matrix.trace.re) :
    (ρ.conditionalMaxEntropyExponentValueSet (a := a)).Nonempty :=
  ⟨ρ.conditionalMaxEntropyExponentCandidate (a := a)
      (State.maximallyMixed b).toSubnormalized,
    (State.maximallyMixed b).toSubnormalized,
    rfl⟩

theorem conditionalMaxEntropyPositiveValueSet_nonempty_of_trace_pos
    [Nonempty a] [Nonempty b] {ρ : SubnormalizedState (Prod a b)}
    (hρ : 0 < ρ.matrix.trace.re) :
    (ρ.conditionalMaxEntropyPositiveValueSet (a := a)).Nonempty :=
  ⟨ρ.conditionalMaxEntropyFidelityCandidate
      (a := a) (State.maximallyMixed b).toSubnormalized,
    (State.maximallyMixed b).toSubnormalized,
    ρ.conditionalMaxEntropyExponentCandidate_maximallyMixed_pos_of_trace_pos
      (a := a) hρ,
    rfl⟩

theorem conditionalMaxEntropyPositiveValueSet_eq_log2_image
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMaxEntropyPositiveValueSet (a := a) =
      log2 '' ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a) := by
  ext h
  constructor
  · rintro ⟨σ, hpos, rfl⟩
    refine ⟨ρ.conditionalMaxEntropyExponentCandidate (a := a) σ, ?_, ?_⟩
    · exact ⟨σ, hpos, rfl⟩
    · exact (ρ.conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate σ).symm
  · rintro ⟨x, ⟨σ, hpos, rfl⟩, rfl⟩
    exact ⟨σ, hpos,
      ρ.conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate σ⟩

theorem conditionalMaxEntropy_eq_sSup_positiveValueSet
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMaxEntropyRaw =
      sSup (ρ.conditionalMaxEntropyPositiveValueSet (a := a)) :=
  rfl

theorem conditionalMaxEntropy_eq_positive
    (ρ : SubnormalizedState (Prod a b)) :
    ρ.conditionalMaxEntropyRaw = ρ.conditionalMaxEntropyPositive :=
  rfl

theorem conditionalMaxEntropyPositiveExponentValueSet_ofStateScale_le
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) {t x : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hx : x ∈
      (SubnormalizedState.ofStateScale ρ t ht.le ht1).conditionalMaxEntropyPositiveExponentValueSet
        (a := a)) :
    x ≤ t * ρ.conditionalMaxEntropyExponent (a := a) := by
  rcases hx with ⟨σ, hσpos, rfl⟩
  by_cases hσzero : σ.matrix.trace.re = 0
  · have hzero :=
      conditionalMaxEntropyExponentCandidate_eq_zero_of_side_trace_zero
        (a := a) (SubnormalizedState.ofStateScale ρ t ht.le ht1) hσzero
    linarith
  · have hσtrace_pos : 0 < σ.matrix.trace.re := by
      exact lt_of_le_of_ne σ.trace_nonneg (Ne.symm hσzero)
    rw [conditionalMaxEntropyExponentCandidate_ofStateScale_normalize
      (a := a) ρ σ ht ht1 hσtrace_pos]
    have hstate_le :
        ρ.conditionalMaxEntropyExponentCandidate (a := a)
            (σ.normalize hσtrace_pos.ne') ≤
          ρ.conditionalMaxEntropyExponent (a := a) := by
      rw [State.conditionalMaxEntropyExponent]
      exact le_csSup (ρ.conditionalMaxEntropyExponentValueSet_bddAbove (a := a))
        ⟨σ.normalize hσtrace_pos.ne', rfl⟩
    have hstate_nonneg :
        0 ≤ ρ.conditionalMaxEntropyExponentCandidate (a := a)
            (σ.normalize hσtrace_pos.ne') :=
      State.conditionalMaxEntropyExponentCandidate_nonneg (a := a) ρ
        (σ.normalize hσtrace_pos.ne')
    have hmul :
        σ.matrix.trace.re *
            ρ.conditionalMaxEntropyExponentCandidate (a := a)
              (σ.normalize hσtrace_pos.ne') ≤
          ρ.conditionalMaxEntropyExponent (a := a) := by
      calc
        σ.matrix.trace.re *
            ρ.conditionalMaxEntropyExponentCandidate (a := a)
              (σ.normalize hσtrace_pos.ne') ≤
            1 *
              ρ.conditionalMaxEntropyExponentCandidate (a := a)
                (σ.normalize hσtrace_pos.ne') := by
              exact mul_le_mul_of_nonneg_right σ.trace_le_one hstate_nonneg
        _ ≤ ρ.conditionalMaxEntropyExponent (a := a) := by
              simpa using hstate_le
    nlinarith [ht.le, hmul]

theorem conditionalMaxEntropyPositiveExponentValueSet_bddAbove_ofStateScale
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    BddAbove
      ((SubnormalizedState.ofStateScale ρ t ht.le ht1).conditionalMaxEntropyPositiveExponentValueSet
        (a := a)) := by
  exact ⟨t * ρ.conditionalMaxEntropyExponent (a := a),
    fun x hx => conditionalMaxEntropyPositiveExponentValueSet_ofStateScale_le
      (a := a) ρ ht ht1 hx⟩

theorem conditionalMaxEntropyPositiveExponentValueSet_bddAbove_of_trace_pos
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) (hρ : 0 < ρ.matrix.trace.re) :
    BddAbove (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)) := by
  rw [← ofStateScale_normalize_trace_eq ρ hρ]
  exact conditionalMaxEntropyPositiveExponentValueSet_bddAbove_ofStateScale
    (a := a) (ρ.normalize hρ.ne') hρ ρ.trace_le_one

theorem conditionalMaxEntropyPositiveExponent_conditioningSumInrCompressed_le
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρPlus : SubnormalizedState (Prod a (Sum extra b)))
    (hPlus : 0 < ρPlus.matrix.trace.re)
    (hCompressed : 0 < ρPlus.conditioningSumInrCompressed.matrix.trace.re) :
    ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyPositiveExponent
        (a := a) ≤
      ρPlus.conditionalMaxEntropyPositiveExponent (a := a) := by
  rw [conditionalMaxEntropyPositiveExponent_eq, conditionalMaxEntropyPositiveExponent_eq]
  have hneCompressed :
      (ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyPositiveExponentValueSet
        (a := a)).Nonempty :=
    ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyPositiveExponentValueSet_nonempty_of_trace_pos
      (a := a) hCompressed
  refine csSup_le hneCompressed ?_
  intro x hx
  rcases hx with ⟨σ, hσpos, rfl⟩
  have hcand :=
    conditionalMaxEntropyExponentCandidate_conditioningSumInrCompressed_referenceIsometryApply_sumInr
      (a := a) (extra := extra) ρPlus σ
  have hmem :
      ρPlus.conditionalMaxEntropyExponentCandidate (a := a)
          (σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b)) ∈
        ρPlus.conditionalMaxEntropyPositiveExponentValueSet (a := a) := by
    refine ⟨σ.referenceIsometryApply (ReferenceIsometry.sumInr extra b), ?_, rfl⟩
    rwa [← hcand]
  rw [hcand]
  exact le_csSup
    (ρPlus.conditionalMaxEntropyPositiveExponentValueSet_bddAbove_of_trace_pos
      (a := a) hPlus) hmem

theorem conditionalMaxEntropyPositiveExponent_ofStateScale
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (SubnormalizedState.ofStateScale ρ t ht.le ht1).conditionalMaxEntropyPositiveExponent
        (a := a) =
      t * ρ.conditionalMaxEntropyExponent (a := a) := by
  let ρt : SubnormalizedState (Prod a b) :=
    SubnormalizedState.ofStateScale ρ t ht.le ht1
  have htrace_pos : 0 < ρt.matrix.trace.re := by
    dsimp [ρt]
    rw [Matrix.trace_smul, ρ.trace_eq_one]
    simpa [Complex.real_smul] using ht
  have hne :
      (ρt.conditionalMaxEntropyPositiveExponentValueSet (a := a)).Nonempty :=
    ρt.conditionalMaxEntropyPositiveExponentValueSet_nonempty_of_trace_pos
      (a := a) htrace_pos
  have hbdd :
      BddAbove (ρt.conditionalMaxEntropyPositiveExponentValueSet (a := a)) := by
    dsimp [ρt]
    exact conditionalMaxEntropyPositiveExponentValueSet_bddAbove_ofStateScale
      (a := a) ρ ht ht1
  refine le_antisymm ?_ ?_
  · rw [conditionalMaxEntropyPositiveExponent]
    exact csSup_le hne (by
      intro x hx
      exact conditionalMaxEntropyPositiveExponentValueSet_ofStateScale_le
        (a := a) ρ ht ht1 hx)
  · have hlower :
        sSup ((fun x : ℝ => t * x) ''
            ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)) ≤
          ρt.conditionalMaxEntropyPositiveExponent (a := a) := by
      refine csSup_le
        (Set.Nonempty.image _ (ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty
          (a := a))) ?_
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      rcases hx with ⟨τ, hτpos, rfl⟩
      rw [conditionalMaxEntropyPositiveExponent]
      exact le_csSup hbdd
        ⟨τ.toSubnormalized, by
          rw [conditionalMaxEntropyExponentCandidate_ofStateScale_toSubnormalized
            (a := a) ρ τ ht ht1]
          exact mul_pos ht hτpos, by
          rw [conditionalMaxEntropyExponentCandidate_ofStateScale_toSubnormalized
            (a := a) ρ τ ht ht1]⟩
    have hsup_image :
        sSup ((fun x : ℝ => t * x) ''
            ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)) =
          t * ρ.conditionalMaxEntropyPositiveExponent (a := a) := by
      rw [State.conditionalMaxEntropyPositiveExponent]
      exact mul_sSup_image_eq
        (ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty (a := a))
        (ρ.conditionalMaxEntropyPositiveExponentValueSet_bddAbove (a := a)) ht
    rw [ρ.conditionalMaxEntropyExponent_eq_positiveExponent (a := a), ← hsup_image]
    exact hlower

theorem conditionalMaxEntropyPositive_eq_log2_positiveExponent
    (ρ : SubnormalizedState (Prod a b))
    (hne : (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)).Nonempty)
    (hbdd : BddAbove (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a))) :
    ρ.conditionalMaxEntropyPositive =
      log2 (ρ.conditionalMaxEntropyPositiveExponent (a := a)) := by
  have hpos : ∀ x ∈ ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a), 0 < x := by
    intro x hx
    rcases hx with ⟨σ, hσpos, rfl⟩
    exact hσpos
  rw [conditionalMaxEntropyPositive, conditionalMaxEntropyPositiveExponent,
    conditionalMaxEntropyPositiveValueSet_eq_log2_image]
  exact log2_sSup_image_eq hne hbdd hpos

/-- Compressing an arbitrary right-summand conditioning register can only
decrease subnormalized conditional max-entropy, when both traces are positive. -/
theorem conditionalMaxEntropy_conditioningSumInrCompressed_le
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρPlus : SubnormalizedState (Prod a (Sum extra b)))
    (hPlus : 0 < ρPlus.matrix.trace.re)
    (hCompressed : 0 < ρPlus.conditioningSumInrCompressed.matrix.trace.re) :
    ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyRaw ≤
      ρPlus.conditionalMaxEntropyRaw := by
  have hneCompressed :
      (ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyPositiveExponentValueSet
        (a := a)).Nonempty :=
    ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyPositiveExponentValueSet_nonempty_of_trace_pos
      (a := a) hCompressed
  have hbddCompressed :
      BddAbove
        (ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyPositiveExponentValueSet
          (a := a)) :=
    ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyPositiveExponentValueSet_bddAbove_of_trace_pos
      (a := a) hCompressed
  have hnePlus :
      (ρPlus.conditionalMaxEntropyPositiveExponentValueSet (a := a)).Nonempty :=
    ρPlus.conditionalMaxEntropyPositiveExponentValueSet_nonempty_of_trace_pos
      (a := a) hPlus
  have hbddPlus :
      BddAbove (ρPlus.conditionalMaxEntropyPositiveExponentValueSet (a := a)) :=
    ρPlus.conditionalMaxEntropyPositiveExponentValueSet_bddAbove_of_trace_pos
      (a := a) hPlus
  rw [conditionalMaxEntropy_eq_positive,
    conditionalMaxEntropy_eq_positive,
    conditionalMaxEntropyPositive_eq_log2_positiveExponent
      (a := a) ρPlus.conditioningSumInrCompressed hneCompressed hbddCompressed,
    conditionalMaxEntropyPositive_eq_log2_positiveExponent
      (a := a) ρPlus hnePlus hbddPlus]
  have hexp_le :=
    ρPlus.conditionalMaxEntropyPositiveExponent_conditioningSumInrCompressed_le
      (a := a) (extra := extra) hPlus hCompressed
  have hexp_pos :
      0 <
        ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyPositiveExponent
          (a := a) := by
    rcases hneCompressed with ⟨x, hx⟩
    have hxpos : 0 < x := by
      rcases hx with ⟨σ, hσpos, rfl⟩
      exact hσpos
    have hxle :
        x ≤
          ρPlus.conditioningSumInrCompressed.conditionalMaxEntropyPositiveExponent
            (a := a) := by
      rw [conditionalMaxEntropyPositiveExponent]
      exact le_csSup hbddCompressed hx
    exact lt_of_lt_of_le hxpos hxle
  unfold log2
  exact div_le_div_of_nonneg_right
    (Real.log_le_log hexp_pos hexp_le)
    (le_of_lt (Real.log_pos one_lt_two))

/-- Any smooth max-entropy witness for the padded conditioning register
compresses to a source-register witness with no larger endpoint value, under
the small-radius positive-trace condition. -/
theorem SmoothConditionalMaxEntropyCandidateRaw.conditioningIsometryApply_sumInr_compress
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε h : ℝ}
    (hε : ε < Real.sqrt ρ.matrix.trace.re)
    (hcand :
      SmoothConditionalMaxEntropyCandidateRaw (a := a)
        (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)) ε h) :
    ∃ h' : ℝ, SmoothConditionalMaxEntropyCandidateRaw (a := a) ρ ε h' ∧ h' ≤ h := by
  rcases hcand with ⟨ρPlus', hball, rfl⟩
  have hballCompressed :
      ρ.purifiedBall ε ρPlus'.conditioningSumInrCompressed :=
    purifiedBall_conditioningSumInrCompressed_of_conditioningIsometryApply_sumInr
      (a := a) (extra := extra) hball
  have hplus_pos :
      0 < ρPlus'.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)) ρPlus'
      (by
        rw [conditioningIsometryApply_trace_re]
        exact hε)
      hball
  have hcompressed_pos :
      0 < ρPlus'.conditioningSumInrCompressed.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace ρ
      ρPlus'.conditioningSumInrCompressed hε hballCompressed
  refine ⟨ρPlus'.conditioningSumInrCompressed.conditionalMaxEntropyRaw,
    ⟨ρPlus'.conditioningSumInrCompressed, hballCompressed, rfl⟩, ?_⟩
  exact conditionalMaxEntropy_conditioningSumInrCompressed_le
    (a := a) (extra := extra) ρPlus' hplus_pos hcompressed_pos

theorem conditionalMaxEntropy_ofStateScale
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (SubnormalizedState.ofStateScale ρ t ht.le ht1).conditionalMaxEntropyRaw =
      ρ.conditionalMaxEntropy + log2 t := by
  let ρt : SubnormalizedState (Prod a b) :=
    SubnormalizedState.ofStateScale ρ t ht.le ht1
  have htrace_pos : 0 < ρt.matrix.trace.re := by
    dsimp [ρt]
    rw [Matrix.trace_smul, ρ.trace_eq_one]
    simpa [Complex.real_smul] using ht
  have hne :
      (ρt.conditionalMaxEntropyPositiveExponentValueSet (a := a)).Nonempty :=
    ρt.conditionalMaxEntropyPositiveExponentValueSet_nonempty_of_trace_pos
      (a := a) htrace_pos
  have hbdd :
      BddAbove (ρt.conditionalMaxEntropyPositiveExponentValueSet (a := a)) := by
    dsimp [ρt]
    exact conditionalMaxEntropyPositiveExponentValueSet_bddAbove_ofStateScale
      (a := a) ρ ht ht1
  have hρexp_pos : 0 < ρ.conditionalMaxEntropyExponent (a := a) :=
    ρ.conditionalMaxEntropyExponent_pos (a := a)
  rw [conditionalMaxEntropy_eq_positive,
    conditionalMaxEntropyPositive_eq_log2_positiveExponent (a := a) ρt hne hbdd,
    conditionalMaxEntropyPositiveExponent_ofStateScale (a := a) ρ ht ht1,
    State.conditionalMaxEntropy_eq_positive (a := a),
    State.conditionalMaxEntropyPositive_eq_log2_exponent_of_nonempty (a := a)]
  unfold log2
  rw [Real.log_mul ht.ne' hρexp_pos.ne']
  ring

theorem ConditionalMinEntropyScaleFeasible.ofStateScale
    {ρ : State (Prod a b)} {T : CMatrix b} {t : ℝ}
    (hT : State.ConditionalMinEntropyScaleFeasible (a := a) ρ T)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ConditionalMinEntropyScaleFeasible (a := a)
      (SubnormalizedState.ofStateScale ρ t ht0 ht1) (t • T) := by
  constructor
  · exact Matrix.PosSemidef.smul hT.1 ht0
  · have hscaled := cMatrix_real_smul_le_smul (A := ρ.matrix)
      (B := Matrix.kronecker (1 : CMatrix a) T) ht0 hT.2
    convert hscaled using 1
    ext i j
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.real_smul]
    ring

theorem ConditionalMinEntropyScaleFeasible.toStateScale
    {ρ : State (Prod a b)} {T : CMatrix b} {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hT : ConditionalMinEntropyScaleFeasible (a := a)
      (SubnormalizedState.ofStateScale ρ t ht.le ht1) T) :
    State.ConditionalMinEntropyScaleFeasible (a := a) ρ (t⁻¹ • T) := by
  constructor
  · exact Matrix.PosSemidef.smul hT.1 (inv_nonneg.mpr ht.le)
  · have hscaled := cMatrix_real_smul_le_smul
      (A := (SubnormalizedState.ofStateScale ρ t ht.le ht1).matrix)
      (B := Matrix.kronecker (1 : CMatrix a) T)
      (inv_nonneg.mpr ht.le) hT.2
    convert hscaled using 1
    · simp [smul_smul, ht.ne']
    · ext i j
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.real_smul]
      ring

theorem conditionalMinEntropyScaleValueSet_ofStateScale
    (ρ : State (Prod a b)) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (SubnormalizedState.ofStateScale ρ t ht.le ht1).conditionalMinEntropyScaleValueSet (a := a) =
      (fun r : ℝ => t * r) '' ρ.conditionalMinEntropyScaleValueSet (a := a) := by
  ext x
  constructor
  · rintro ⟨T, hT, rfl⟩
    refine ⟨(t⁻¹ • T).trace.re, ?_, ?_⟩
    · exact ⟨t⁻¹ • T,
        ConditionalMinEntropyScaleFeasible.toStateScale (a := a) ht ht1 hT, rfl⟩
    · rw [Matrix.trace_smul]
      simp [Complex.real_smul]
      field_simp [ht.ne']
  · rintro ⟨r, ⟨T, hT, rfl⟩, rfl⟩
    refine ⟨t • T,
      ConditionalMinEntropyScaleFeasible.ofStateScale (a := a) hT ht.le ht1, ?_⟩
    rw [Matrix.trace_smul]
    simp [Complex.real_smul]

theorem conditionalMinEntropyScale_ofStateScale
    (ρ : State (Prod a b)) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (SubnormalizedState.ofStateScale ρ t ht.le ht1).conditionalMinEntropyScale (a := a) =
      t * ρ.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    State.conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScaleValueSet_ofStateScale (a := a) ρ ht ht1]
  let s : Set ℝ := ρ.conditionalMinEntropyScaleValueSet (a := a)
  have himage : (fun r : ℝ => t * r) '' s = t • s := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact Set.mem_smul_set.mpr ⟨r, hr, by rw [smul_eq_mul]⟩
    · intro hx
      rcases Set.mem_smul_set.mp hx with ⟨r, hr, htx⟩
      exact ⟨r, hr, by simpa [smul_eq_mul] using htx⟩
  rw [himage, Real.sInf_smul_of_nonneg ht.le]
  simp [s, smul_eq_mul]

theorem conditionalMinEntropy_ofStateScale
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (SubnormalizedState.ofStateScale ρ t ht.le ht1).conditionalMinEntropyRaw =
      ρ.conditionalMinEntropy - log2 t := by
  have htrace_pos :
      0 < (SubnormalizedState.ofStateScale ρ t ht.le ht1).matrix.trace.re := by
    rw [ofStateScale_trace_re]
    exact ht
  rw [conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos (a := a)
      (SubnormalizedState.ofStateScale ρ t ht.le ht1) htrace_pos,
    State.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a),
    conditionalMinEntropyScale_ofStateScale (a := a) ρ ht ht1]
  have hscale_pos : 0 < ρ.conditionalMinEntropyScale (a := a) := by
    rw [ρ.conditionalMinEntropyScale_eq_normalizedScale (a := a)]
    exact ρ.conditionalMinEntropyNormalizedScale_inf_pos (a := a)
  unfold log2
  rw [Real.log_mul ht.ne' hscale_pos.ne']
  ring

/-- Normalize a positive-trace subnormalized state inside conditional
min-entropy, exposing the trace penalty used in the AEP upper-bound route. -/
theorem conditionalMinEntropy_eq_normalize_sub_log2_trace
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) (hρ : 0 < ρ.matrix.trace.re) :
    ρ.conditionalMinEntropyRaw =
      (ρ.normalize hρ.ne').conditionalMinEntropy - log2 ρ.matrix.trace.re := by
  have hscale :
      (SubnormalizedState.ofStateScale (ρ.normalize hρ.ne')
          ρ.matrix.trace.re hρ.le ρ.trace_le_one).conditionalMinEntropyRaw =
        (ρ.normalize hρ.ne').conditionalMinEntropy - log2 ρ.matrix.trace.re :=
    conditionalMinEntropy_ofStateScale
      (a := a) (b := b) (ρ.normalize hρ.ne') hρ ρ.trace_le_one
  have hstate :
      SubnormalizedState.ofStateScale (ρ.normalize hρ.ne')
          ρ.matrix.trace.re hρ.le ρ.trace_le_one = ρ :=
    SubnormalizedState.ofStateScale_normalize_trace_eq ρ hρ
  simpa [hstate] using hscale

theorem generalizedFidelity_toSubnormalized_ofStateScale
    (ρ σ : State a) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ρ.toSubnormalized.generalizedFidelity
        (SubnormalizedState.ofStateScale σ t ht0 ht1) =
      t * ρ.squaredFidelity σ := by
  rw [SubnormalizedState.generalizedFidelity_eq,
    State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq]
  have hρtr : ρ.matrix.trace.re = 1 := by
    rw [ρ.trace_eq_one]
    norm_num
  have hσtr :
      (SubnormalizedState.ofStateScale σ t ht0 ht1).matrix.trace.re = t := by
    rw [SubnormalizedState.ofStateScale_trace_re]
  have hsqrt :
      psdSqrt (SubnormalizedState.ofStateScale σ t ht0 ht1).matrix =
        ((Real.sqrt t : ℝ) : ℂ) • σ.sqrtMatrix := by
    rw [SubnormalizedState.ofStateScale_matrix, State.sqrtMatrix]
    exact psdSqrt_real_smul ht0 σ.pos
  rw [State.toSubnormalized_matrix, hsqrt, hρtr, hσtr]
  rw [Matrix.mul_smul, traceNorm_real_smul_eq (Real.sqrt_nonneg t)]
  simp [State.sqrtMatrix]
  nlinarith [Real.sq_sqrt ht0]

/-- Normalizing a positive-trace subnormalized witness around a normalized
center does not increase the purified distance to that center.

For a trace-one center the generalized fidelity of the scaled witness is
`t F(ρ, τ̂)^2`; since `t ≤ 1`, the normalized witness is at least as close in
purified distance. This is the source smoothing bridge used in the AFW upper
half of the asymptotic AEP. -/
theorem purifiedDistance_normalize_le_of_toSubnormalized
    (ρ : State a) (τ : SubnormalizedState a) (hτ : 0 < τ.matrix.trace.re) :
    ρ.purifiedDistance (τ.normalize hτ.ne') ≤
      ρ.toSubnormalized.purifiedDistance τ := by
  let τhat : State a := τ.normalize hτ.ne'
  let t : ℝ := τ.matrix.trace.re
  have hstate :
      SubnormalizedState.ofStateScale τhat t hτ.le τ.trace_le_one = τ := by
    simpa [τhat, t] using SubnormalizedState.ofStateScale_normalize_trace_eq τ hτ
  have hgf :
      ρ.toSubnormalized.generalizedFidelity
          (SubnormalizedState.ofStateScale τhat t hτ.le τ.trace_le_one) =
        t * ρ.squaredFidelity τhat :=
    generalizedFidelity_toSubnormalized_ofStateScale ρ τhat hτ.le τ.trace_le_one
  have hfid_nonneg : 0 ≤ ρ.squaredFidelity τhat :=
    State.squaredFidelity_nonneg ρ τhat
  have hinside :
      1 - ρ.squaredFidelity τhat ≤
        1 - t * ρ.squaredFidelity τhat := by
    have hmul : t * ρ.squaredFidelity τhat ≤ ρ.squaredFidelity τhat := by
      simpa [one_mul] using
        mul_le_mul_of_nonneg_right τ.trace_le_one hfid_nonneg
    linarith
  calc
    ρ.purifiedDistance (τ.normalize hτ.ne') =
        Real.sqrt (1 - ρ.squaredFidelity τhat) := by
          simp [τhat, State.purifiedDistance_eq]
    _ ≤ Real.sqrt (1 - t * ρ.squaredFidelity τhat) :=
        Real.sqrt_le_sqrt hinside
    _ = ρ.toSubnormalized.purifiedDistance
        (SubnormalizedState.ofStateScale τhat t hτ.le τ.trace_le_one) := by
          rw [SubnormalizedState.purifiedDistance_eq, hgf]
    _ = ρ.toSubnormalized.purifiedDistance τ := by
          rw [hstate]

theorem purifiedBall_normalize_of_toSubnormalized_purifiedBall
    {ρ : State a} {τ : SubnormalizedState a} {ε : ℝ}
    (hτ : 0 < τ.matrix.trace.re)
    (hball : ρ.toSubnormalized.purifiedBall ε τ) :
    ρ.purifiedBall ε (τ.normalize hτ.ne') :=
  le_trans (purifiedDistance_normalize_le_of_toSubnormalized ρ τ hτ) hball

private theorem rpow_two_neg_sub_log2 (t lam : ℝ) (ht : 0 < t) :
    Real.rpow 2 (-(lam - log2 t)) = t * Real.rpow 2 (-lam) := by
  calc
    Real.rpow 2 (-(lam - log2 t)) =
        Real.rpow 2 (log2 t + -lam) := by ring_nf
    _ = Real.rpow 2 (log2 t) * Real.rpow 2 (-lam) := by
        exact Real.rpow_add (by norm_num : (0 : ℝ) < 2) (log2 t) (-lam)
    _ = t * Real.rpow 2 (-lam) := by rw [rpow_two_log2_pos ht]

theorem ConditionalMinEntropyFeasible.ofStateScale_shift
    {ρ : State (Prod a b)} {σ : State b} {t lam : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1)
    (h : State.ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    ConditionalMinEntropyFeasible (a := a)
      (ofStateScale ρ t ht.le ht1) σ.toSubnormalized (lam - log2 t) := by
  change ρ.matrix ≤
      (Real.rpow 2 (-lam) : ℂ) • State.identityTensorStateMatrix (a := a) σ at h
  change t • ρ.matrix ≤
      (Real.rpow 2 (-(lam - log2 t)) : ℂ) •
        identityTensorStateMatrix (a := a) σ.toSubnormalized
  have hscaled := cMatrix_real_smul_le_smul (A := ρ.matrix)
    (B := (Real.rpow 2 (-lam) : ℂ) • State.identityTensorStateMatrix (a := a) σ)
    ht.le h
  convert hscaled using 1
  rw [rpow_two_neg_sub_log2 t lam ht]
  ext i j
  simp [State.toSubnormalized_identityTensorStateMatrix_eq]
  ring

theorem conditionalMinEntropyFeasibleExponentValueSet_shift_subset_ofStateScale
    (ρ : State (Prod a b)) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (fun lam : ℝ => lam - log2 t) ''
        State.conditionalMinEntropyFeasibleExponentValueSet (a := a) ρ ⊆
      {mu : ℝ | ∃ σ : SubnormalizedState b,
        ConditionalMinEntropyFeasible (a := a)
          (ofStateScale ρ t ht.le ht1) σ mu} := by
  rintro mu ⟨lam, ⟨σ, hσ⟩, rfl⟩
  exact ⟨σ.toSubnormalized,
    ConditionalMinEntropyFeasible.ofStateScale_shift (a := a)
      (ρ := ρ) (σ := σ) ht ht1 hσ⟩

end SubnormalizedState
end

end QIT
