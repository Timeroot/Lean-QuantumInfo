/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Core.State
public import QuantumLib.QIT.Core.Pure
public import QuantumLib.QIT.Core.Map
public import QuantumLib.QIT.Core.Channel
public import QuantumLib.QIT.Util.Matrix
public import QuantumLib.QIT.States.Subnormalized
public import QuantumLib.QIT.States.Purification.ReferenceIsometry
public import QuantumLib.QIT.Channels.Diamond
public import QuantumLib.QIT.States.Schatten

/-!
# Conditioning-register compression

Operational definitions for compressing the conditioning (right) register of a
bipartite state to the positive spectral support of a PSD right-register
reference. The cluster comprises the conditioning-register isometry action
(`conditioningIsometryApply`), the PSD support reference isometry
(`psdSupportReferenceIsometry`), and the support-compressed state
(`conditioningSupportCompressedState`), together with the right-register
compression and marginal-support helpers they are built from. Their consumer
is the conditional Petz-Rényi bound layer; keeping them at L1 lets the L2
information modules reach them through a downward edge rather than an upward
L3 bridge.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

noncomputable section
universe u v w
variable {a : Type u} [Fintype a] [DecidableEq a]

open QIT

namespace MState

variable {b : Type v} [Fintype b] [DecidableEq b]

variable {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]

/-! ## Conditioning-register isometries -/

/-- Apply a finite reference isometry to the conditioning/right register of a
state on `A × B`. -/
def conditioningIsometryApply (ρ : MState (a × b)) (V : ReferenceIsometry b bPlus) :
    MState (a × bPlus) := .ofMatrix
  (matrix := V.applyMatrixRight ρ.m)
  (pos := by
    rw [← MatrixMap.kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight
      (a := a) V ρ.m]
    exact MatrixMap.isCompletelyPositive_mapsPositive
      (MatrixMap.kron (CPTPOp.id (dIn := a)).map (MatrixMap.ofReferenceIsometry V))
      (MatrixMap.IsCompletelyPositive.kron (CPTPOp.id (dIn := a)).map_cp
        (MatrixMap.ofReferenceIsometry_isCompletelyPositive V))
      ρ.m ρ.psd)
  (trace_eq_one := by
    rw [← MatrixMap.kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight
      (a := a) V ρ.m]
    have hTP := MatrixMap.IsTracePreserving.kron (CPTPOp.id (dIn := a)).map_TP
      (MatrixMap.ofReferenceIsometry_isTracePreserving V)
    rw [hTP ρ.m, ρ.tr'])

@[simp]
theorem conditioningIsometryApply_matrix (ρ : MState (a × b))
    (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).m = V.applyMatrixRight ρ.m :=
  MState.matrix_ofMatrix _ _ _

theorem conditioningIsometryApply_matrix_eq_kronecker_conj
    (ρ : MState (a × b)) (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).m =
      Matrix.kronecker (1 : CMatrix a) V.matrix * ρ.m *
        Matrix.conjTranspose (Matrix.kronecker (1 : CMatrix a) V.matrix) := by
  ext x y
  simp [conditioningIsometryApply_matrix, ReferenceIsometry.applyMatrixRight,
    ReferenceIsometry.rightBlock, Matrix.mul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.conjTranspose_kronecker,
    Fintype.sum_prod_type, Finset.mul_sum,
    Finset.sum_ite_eq', apply_ite, mul_comm]

theorem conditioningIsometryApply_traceRight (ρ : MState (a × b))
    (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).traceRight = ρ.traceRight := by
  apply MState.ext
  rw [MState.traceRight_m, MState.traceRight_m, conditioningIsometryApply_matrix]
  exact V.traceRight_applyMatrixRight ρ.m

theorem conditioningIsometryApply_traceLeft_matrix (ρ : MState (a × b))
    (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).traceLeft.m =
      V.matrix * ρ.traceLeft.m * Matrix.conjTranspose V.matrix := by
  rw [MState.traceLeft_m, MState.traceLeft_m, conditioningIsometryApply_matrix]
  exact V.traceLeft_applyMatrixRight ρ.m

/-- The support isometry of a PSD right-register reference, as a
`ReferenceIsometry` from the compressed support register into the original
right register. -/
noncomputable def psdSupportReferenceIsometry
    (N : CMatrix b) (hN : N.PosSemidef) :
    ReferenceIsometry (psdSupportIndex N hN) b where
  matrix := psdSupportIsometry N hN
  isometry := psdSupportIsometry_isometry N hN

/-- Compress the right register of a bipartite matrix to the positive spectral
support of a PSD right-register reference. -/
noncomputable def psdSupportCompressRight
    (N : CMatrix b) (hN : N.PosSemidef)
    (X : CMatrix (a × b)) :
    CMatrix (a × psdSupportIndex N hN) :=
  fun x y =>
    (Matrix.conjTranspose (psdSupportIsometry N hN) *
      ReferenceIsometry.rightBlock X x.1 y.1 *
      psdSupportIsometry N hN) x.2 y.2

theorem psdSupportCompressRight_eq_conj
    (N : CMatrix b) (hN : N.PosSemidef)
    (X : CMatrix (a × b)) :
    psdSupportCompressRight (a := a) N hN X =
      Matrix.conjTranspose
        (Matrix.kronecker (1 : CMatrix a) (psdSupportIsometry N hN)) *
        X * Matrix.kronecker (1 : CMatrix a) (psdSupportIsometry N hN) := by
  classical
  ext x y
  simp [psdSupportCompressRight, ReferenceIsometry.rightBlock, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.sum_ite_eq',
    apply_ite]

omit [DecidableEq a] in
theorem traceLeft_psdSupportCompressRight
    (N : CMatrix b) (hN : N.PosSemidef)
    (X : CMatrix (a × b)) :
    Matrix.traceLeft
        (psdSupportCompressRight (a := a) N hN X) =
      psdSupportCompress N hN (Matrix.traceLeft X) := by
  classical
  ext i j
  simp [Matrix.traceLeft, psdSupportCompressRight, psdSupportCompress,
    ReferenceIsometry.rightBlock, Matrix.mul_apply, Finset.sum_mul,
    Finset.mul_sum]
  have hswap_outer :
      (∑ x : a, ∑ y : b, ∑ i₁ : b,
          (starRingEnd ℂ) (psdSupportIsometry N hN i₁ i) *
            X (x, i₁) (x, y) * psdSupportIsometry N hN y j) =
        ∑ y : b, ∑ x : a, ∑ i₁ : b,
          (starRingEnd ℂ) (psdSupportIsometry N hN i₁ i) *
            X (x, i₁) (x, y) * psdSupportIsometry N hN y j := by
    simpa using
      (Finset.sum_comm
        (s := (Finset.univ : Finset a)) (t := (Finset.univ : Finset b))
        (β := ℂ)
        (f := fun (x : a) (y : b) =>
          ∑ i₁ : b, (starRingEnd ℂ) (psdSupportIsometry N hN i₁ i) *
            X (x, i₁) (x, y) * psdSupportIsometry N hN y j))
  have hswap_inner :
      (∑ y : b, ∑ x : a, ∑ i₁ : b,
          (starRingEnd ℂ) (psdSupportIsometry N hN i₁ i) *
            X (x, i₁) (x, y) * psdSupportIsometry N hN y j) =
        ∑ y : b, ∑ i₁ : b, ∑ x : a,
          (starRingEnd ℂ) (psdSupportIsometry N hN i₁ i) *
            X (x, i₁) (x, y) * psdSupportIsometry N hN y j := by
    refine Finset.sum_congr rfl fun (y : b) _ => ?_
    simpa using
      (Finset.sum_comm
        (s := (Finset.univ : Finset a)) (t := (Finset.univ : Finset b))
        (β := ℂ)
        (f := fun (x : a) (i₁ : b) =>
          (starRingEnd ℂ) (psdSupportIsometry N hN i₁ i) *
            X (x, i₁) (x, y) * psdSupportIsometry N hN y j))
  rw [hswap_outer, hswap_inner]

/-- A bipartite state is supported by the identity tensor its right marginal. -/
theorem matrix_supports_identityTensor_traceLeft (ρ : MState (a × b)) :
    Matrix.Supports ρ.m
      (Matrix.kronecker (1 : CMatrix a) ρ.traceLeft.m) := by
  classical
  have hρ : Matrix.Supports ρ.m (ρ.traceRight.prod ρ.traceLeft).m :=
    ρ.matrix_supports_prod_marginals
  have hprod :
      Matrix.Supports (ρ.traceRight.prod ρ.traceLeft).m
        (Matrix.kronecker (1 : CMatrix a) ρ.traceLeft.m) := by
    intro v hv
    let L : CMatrix (a × b) :=
      Matrix.kronecker (1 : CMatrix a) ρ.traceLeft.m
    let K : CMatrix (a × b) :=
      Matrix.kronecker ρ.traceRight.m (1 : CMatrix b)
    have hfactor : (ρ.traceRight.prod ρ.traceLeft).m = K * L := by
      rw [MState.prod_m]
      simpa [K, L] using
        (Matrix.mul_kronecker_mul ρ.traceRight.m (1 : CMatrix a)
          (1 : CMatrix b) ρ.traceLeft.m)
    calc
      Matrix.mulVec (ρ.traceRight.prod ρ.traceLeft).m v =
          Matrix.mulVec (K * L) v := by rw [hfactor]
      _ = Matrix.mulVec K (Matrix.mulVec L v) := by
          rw [Matrix.mulVec_mulVec]
      _ = 0 := by
          rw [show Matrix.mulVec L v = 0 from by simpa [L] using hv]
          simp
  exact Matrix.Supports.trans hρ hprod

/-- Every fixed right-register block of a bipartite state is supported by the
right marginal. -/
theorem rightBlock_supports_traceLeft
    (ρ : MState (a × b)) (x y : a) :
    Matrix.Supports (ReferenceIsometry.rightBlock ρ.m x y)
      ρ.traceLeft.m := by
  classical
  intro v hv
  let w : a × b → ℂ := fun z => if z.1 = y then v z.2 else 0
  have hNw :
      Matrix.mulVec (Matrix.kronecker (1 : CMatrix a) ρ.traceLeft.m) w = 0 := by
    ext z
    by_cases hzy : z.1 = y
    ·
      simpa [w, Matrix.mulVec, dotProduct, Matrix.kronecker,
        Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
        Finset.sum_ite_eq', hzy] using congrFun hv z.2
    · simp [w, Matrix.mulVec, dotProduct, Matrix.kronecker,
        Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
        Finset.sum_ite_eq', hzy]
  have hSupport := matrix_supports_identityTensor_traceLeft (a := a) (b := b) ρ
  have hMw := hSupport w hNw
  ext k
  have hk := congrFun hMw (x, k)
  simpa [ReferenceIsometry.rightBlock, Matrix.mulVec, dotProduct, w,
    Fintype.sum_prod_type, Finset.sum_ite_eq'] using hk

theorem rightBlock_conjTranspose
    (ρ : MState (a × b)) (x y : a) :
    Matrix.conjTranspose (ReferenceIsometry.rightBlock ρ.m x y) =
      ReferenceIsometry.rightBlock ρ.m y x := by
  ext i j
  have h := congrFun (congrFun ρ.psd.isHermitian.eq (y, i)) (x, j)
  simpa [ReferenceIsometry.rightBlock, Matrix.conjTranspose_apply] using h

/-- Compress a bipartite state to the positive spectral support of its right
marginal. -/
noncomputable def conditioningSupportCompressedState
    (ρ : MState (a × b)) :
    MState (a × psdSupportIndex ρ.traceLeft.m ρ.traceLeft.psd) := .ofMatrix
  (matrix :=
    psdSupportCompressRight (a := a) ρ.traceLeft.m ρ.traceLeft.psd ρ.m)
  (pos := by
    rw [psdSupportCompressRight_eq_conj]
    exact Matrix.PosSemidef.conjTranspose_mul_mul_same ρ.psd
      (Matrix.kronecker (1 : CMatrix a)
        (psdSupportIsometry ρ.traceLeft.m ρ.traceLeft.psd)))
  (trace_eq_one := by
    let X : CMatrix (a × psdSupportIndex ρ.traceLeft.m ρ.traceLeft.psd) :=
      psdSupportCompressRight (a := a) ρ.traceLeft.m ρ.traceLeft.psd ρ.m
    calc
      X.trace =
          (Matrix.traceLeft X).trace := by
          rw [Matrix.traceLeft_trace]
      _ = (psdSupportCompress ρ.traceLeft.m ρ.traceLeft.psd
            ρ.traceLeft.m).trace := by
          rw [traceLeft_psdSupportCompressRight]
          simp
      _ = ρ.traceLeft.m.trace := by
          rw [psdSupportCompress_trace_self]
      _ = 1 := ρ.traceLeft.tr')

@[simp]
theorem conditioningSupportCompressedState_matrix
    (ρ : MState (a × b)) :
    ρ.conditioningSupportCompressedState.m =
      psdSupportCompressRight (a := a)
        ρ.traceLeft.m ρ.traceLeft.psd ρ.m :=
  MState.matrix_ofMatrix _ _ _

theorem conditioningSupportCompressedState_traceLeft_matrix
    (ρ : MState (a × b)) :
    ρ.conditioningSupportCompressedState.traceLeft.m =
      psdSupportCompress ρ.traceLeft.m ρ.traceLeft.psd
        ρ.traceLeft.m := by
  conv_lhs => rw [MState.traceLeft_m, conditioningSupportCompressedState_matrix]
  rw [traceLeft_psdSupportCompressRight, ← MState.traceLeft_m]

theorem conditioningSupportCompressedState_traceLeft_posDef
    (ρ : MState (a × b)) :
    ρ.conditioningSupportCompressedState.traceLeft.m.PosDef := by
  rw [conditioningSupportCompressedState_traceLeft_matrix]
  exact psdSupportCompress_self_posDef ρ.traceLeft.m ρ.traceLeft.psd

@[simp]
theorem conditioningSupportCompressedState_conditioningIsometryApply
    (ρ : MState (a × b)) :
    ρ.conditioningSupportCompressedState.conditioningIsometryApply
      (psdSupportReferenceIsometry ρ.traceLeft.m ρ.traceLeft.psd) = ρ := by
  apply MState.ext
  rw [conditioningIsometryApply_matrix, conditioningSupportCompressedState_matrix]
  ext x y
  let N : CMatrix b := ρ.traceLeft.m
  let hN : N.PosSemidef := ρ.traceLeft.psd
  let B : CMatrix b := ReferenceIsometry.rightBlock ρ.m x.1 y.1
  have hB : Matrix.Supports B N := by
    simpa [B, N] using rightBlock_supports_traceLeft (a := a) (b := b) ρ x.1 y.1
  have hBstar : Matrix.Supports (Matrix.conjTranspose B) N := by
    rw [show Matrix.conjTranspose B =
        ReferenceIsometry.rightBlock ρ.m y.1 x.1 from by
      simpa [B] using rightBlock_conjTranspose (a := a) (b := b) ρ x.1 y.1]
    simpa [N] using rightBlock_supports_traceLeft (a := a) (b := b) ρ y.1 x.1
  have hrec :=
    psdSupportCompress_reconstruct_of_supports_right_and_conjTranspose
      (M := B) (N := N) hN hB hBstar
  have hentry := congrFun (congrFun hrec x.2) y.2
  exact hentry

/-- Feasibility predicate for the conditional min-entropy order constraint
`ρ_AB ≤ 2^{-λ} • (I_A ⊗ σ_B)` in the local bits convention. -/
def ConditionalMinEntropyFeasible (ρ : MState (a × b)) (σ : MState b) (lam : ℝ) :
    Prop :=
  ρ.m ≤ (Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ

@[simp]
theorem ConditionalMinEntropyFeasible_eq (ρ : MState (a × b)) (σ : MState b)
    (lam : ℝ) :
    ConditionalMinEntropyFeasible (a := a) ρ σ lam ↔
      ρ.m ≤ (Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ :=
  Iff.rfl

end MState

namespace QIT

namespace SubnormalizedState

variable {a : Type u} [Fintype a] [DecidableEq a]

variable {b : Type v} [Fintype b] [DecidableEq b]

variable {c : Type*} [Fintype c] [DecidableEq c]

/-! ## Scaled-state carriers -/

/-- Scale a normalized state by a real weight in `[0,1]`, yielding a
subnormalized state. This is the local smooth-entropy version of the scaled
pure-state carrier used by the subnormalized duality route. -/
def ofStateScale (ρ : MState a) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SubnormalizedState a where
  matrix := t • ρ.m
  pos := Matrix.PosSemidef.smul ρ.psd ht0
  trace_le_one := by
    rw [Matrix.trace_smul, ρ.tr']
    simpa [Complex.real_smul] using ht1

@[simp]
theorem ofStateScale_matrix (ρ : MState a) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (ofStateScale ρ t ht0 ht1).matrix = t • ρ.m :=
  rfl

theorem ofStateScale_trace (ρ : MState a) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (ofStateScale ρ t ht0 ht1).matrix.trace = (t : ℂ) := by
  rw [ofStateScale_matrix, Matrix.trace_smul, ρ.tr']
  simp [Complex.real_smul]

theorem ofStateScale_trace_re (ρ : MState a) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (ofStateScale ρ t ht0 ht1).matrix.trace.re = t := by
  rw [ofStateScale_trace]
  simp

/-- The `AB` marginal of a scaled pure tripartite state on left-associated
`ABC`. -/
def abMarginalFromScaledTripartitePure
    (ψ : Ket ((a × b) × c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SubnormalizedState (a × b) :=
  ofStateScale ψ.state.marginalAB t ht0 ht1

@[simp]
theorem abMarginalFromScaledTripartitePure_matrix
    (ψ : Ket ((a × b) × c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
      ψ t ht0 ht1).matrix = t • ψ.state.marginalAB.m :=
  rfl

/-- The `AC` marginal of a scaled pure tripartite state on left-associated
`ABC`. -/
def acMarginalFromScaledTripartitePure
    (ψ : Ket ((a × b) × c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SubnormalizedState (a × c) :=
  ofStateScale ψ.state.marginalAC t ht0 ht1

@[simp]
theorem acMarginalFromScaledTripartitePure_matrix
    (ψ : Ket ((a × b) × c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
      ψ t ht0 ht1).matrix = t • ψ.state.marginalAC.m :=
  rfl

/-- The matrix `I_A ⊗ σ_B` used in subnormalized conditional entropy definitions.

Here `σ_B` is subnormalized, matching
[Tomamichel2015FiniteResources, calculus.tex:81-89] and
[Tomamichel2015FiniteResources, calculus.tex:191-198]. -/
def identityTensorStateMatrix (σ : SubnormalizedState b) : CMatrix (a × b) :=
  Matrix.kronecker (1 : CMatrix a) σ.matrix

/-- Feasibility predicate for subnormalized conditional min-entropy in the
local bits convention: `ρ_AB ≤ 2^{-λ} • (I_A ⊗ σ_B)` with
`σ_B ∈ S_≤(B)`. -/
def ConditionalMinEntropyFeasible
    (ρ : SubnormalizedState (a × b)) (σ : SubnormalizedState b) (lam : ℝ) :
    Prop :=
  ρ.matrix ≤ (Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ

@[simp]
theorem ConditionalMinEntropyFeasible_eq
    (ρ : SubnormalizedState (a × b)) (σ : SubnormalizedState b) (lam : ℝ) :
    ConditionalMinEntropyFeasible (a := a) ρ σ lam ↔
      ρ.matrix ≤ (Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ :=
  Iff.rfl

end SubnormalizedState

end QIT
