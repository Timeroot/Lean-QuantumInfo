/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.State
public import QIT.Core.Pure
public import QIT.Core.Map
public import QIT.Core.Channel
public import QIT.Util.Matrix
public import QIT.States.Subnormalized
public import QIT.States.Purification.ReferenceIsometry
public import QIT.Channels.Diamond
public import QIT.States.Schatten

/-!
# Conditioning-register compression

Operational definitions for compressing the conditioning (right) register of a
bipartite state to the positive spectral support of a PSD right-register
reference. The cluster comprises the conditioning-register isometry action
(`conditioningIsometryApply`), the PSD support reference isometry
(`psdSupportReferenceIsometry`), and the support-compressed state
(`conditioningSupportCompressedState`), together with the right-register
compression and marginal-support helpers they are built from. These
definitions are consumed by the conditional Petz-Rényi bounds and were
relocated here from `OneShot.Smooth` so that the L2 information module reaches
them through a downward L1 edge rather than an upward L3 bridge.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

namespace State

variable {b : Type v} [Fintype b] [DecidableEq b]

variable {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]

/-! ## Conditioning-register isometries -/

/-- Apply a finite reference isometry to the conditioning/right register of a
state on `A × B`. -/
def conditioningIsometryApply (ρ : State (Prod a b)) (V : ReferenceIsometry b bPlus) :
    State (Prod a bPlus) where
  matrix := V.applyMatrixRight ρ.matrix
  pos := by
    rw [← MatrixMap.kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight
      (a := a) V ρ.matrix]
    exact MatrixMap.isCompletelyPositive_mapsPositive
      (MatrixMap.kron (Channel.idChannel a).map (MatrixMap.ofReferenceIsometry V))
      (MatrixMap.isCompletelyPositive_kron (Channel.idChannel a).map
        (MatrixMap.ofReferenceIsometry V)
        (Channel.idChannel a).completelyPositive
        (MatrixMap.ofReferenceIsometry_isCompletelyPositive V))
      ρ.matrix ρ.pos
  trace_eq_one := by
    rw [← MatrixMap.kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight
      (a := a) V ρ.matrix]
    have hTP := MatrixMap.isTracePreserving_kron (Channel.idChannel a).map
      (MatrixMap.ofReferenceIsometry V)
      (Channel.idChannel a).tracePreserving
      (MatrixMap.ofReferenceIsometry_isTracePreserving V)
    rw [hTP ρ.matrix, ρ.trace_eq_one]

@[simp]
theorem conditioningIsometryApply_matrix (ρ : State (Prod a b))
    (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).matrix = V.applyMatrixRight ρ.matrix :=
  rfl

theorem conditioningIsometryApply_matrix_eq_kronecker_conj
    (ρ : State (Prod a b)) (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).matrix =
      Matrix.kronecker (1 : CMatrix a) V.matrix * ρ.matrix *
        Matrix.conjTranspose (Matrix.kronecker (1 : CMatrix a) V.matrix) := by
  ext x y
  simp [conditioningIsometryApply_matrix, ReferenceIsometry.applyMatrixRight,
    ReferenceIsometry.rightBlock, Matrix.mul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.conjTranspose_kronecker,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_ite_eq', apply_ite, mul_assoc, mul_comm]

theorem conditioningIsometryApply_marginalA (ρ : State (Prod a b))
    (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).marginalA = ρ.marginalA := by
  apply State.ext
  rw [State.marginalA_matrix, State.marginalA_matrix, conditioningIsometryApply_matrix]
  exact V.partialTraceB_applyMatrixRight ρ.matrix

theorem conditioningIsometryApply_marginalB_matrix (ρ : State (Prod a b))
    (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).marginalB.matrix =
      V.matrix * ρ.marginalB.matrix * Matrix.conjTranspose V.matrix := by
  rw [State.marginalB_matrix, State.marginalB_matrix, conditioningIsometryApply_matrix]
  exact V.partialTraceA_applyMatrixRight ρ.matrix

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
    (X : CMatrix (Prod a b)) :
    CMatrix (Prod a (psdSupportIndex N hN)) :=
  fun x y =>
    (Matrix.conjTranspose (psdSupportIsometry N hN) *
      ReferenceIsometry.rightBlock X x.1 y.1 *
      psdSupportIsometry N hN) x.2 y.2

theorem psdSupportCompressRight_eq_conj
    (N : CMatrix b) (hN : N.PosSemidef)
    (X : CMatrix (Prod a b)) :
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
theorem partialTraceA_psdSupportCompressRight
    (N : CMatrix b) (hN : N.PosSemidef)
    (X : CMatrix (Prod a b)) :
    partialTraceA (a := a) (b := psdSupportIndex N hN)
        (psdSupportCompressRight (a := a) N hN X) =
      psdSupportCompress N hN (partialTraceA (a := a) (b := b) X) := by
  classical
  ext i j
  simp [partialTraceA, psdSupportCompressRight, psdSupportCompress,
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
theorem matrix_supports_identityTensor_marginalB (ρ : State (Prod a b)) :
    Matrix.Supports ρ.matrix
      (Matrix.kronecker (1 : CMatrix a) ρ.marginalB.matrix) := by
  classical
  have hρ : Matrix.Supports ρ.matrix (ρ.marginalA.prod ρ.marginalB).matrix :=
    ρ.matrix_supports_prod_marginals
  have hprod :
      Matrix.Supports (ρ.marginalA.prod ρ.marginalB).matrix
        (Matrix.kronecker (1 : CMatrix a) ρ.marginalB.matrix) := by
    intro v hv
    let L : CMatrix (Prod a b) :=
      Matrix.kronecker (1 : CMatrix a) ρ.marginalB.matrix
    let K : CMatrix (Prod a b) :=
      Matrix.kronecker ρ.marginalA.matrix (1 : CMatrix b)
    have hfactor : (ρ.marginalA.prod ρ.marginalB).matrix = K * L := by
      change Matrix.kronecker ρ.marginalA.matrix ρ.marginalB.matrix = K * L
      simpa [K, L] using
        (Matrix.mul_kronecker_mul ρ.marginalA.matrix (1 : CMatrix a)
          (1 : CMatrix b) ρ.marginalB.matrix)
    calc
      Matrix.mulVec (ρ.marginalA.prod ρ.marginalB).matrix v =
          Matrix.mulVec (K * L) v := by rw [hfactor]
      _ = Matrix.mulVec K (Matrix.mulVec L v) := by
          rw [Matrix.mulVec_mulVec]
      _ = 0 := by
          rw [show Matrix.mulVec L v = 0 from by simpa [L] using hv]
          simp
  exact Matrix.Supports.trans hρ hprod

/-- Every fixed right-register block of a bipartite state is supported by the
right marginal. -/
theorem rightBlock_supports_marginalB
    (ρ : State (Prod a b)) (x y : a) :
    Matrix.Supports (ReferenceIsometry.rightBlock ρ.matrix x y)
      ρ.marginalB.matrix := by
  classical
  intro v hv
  let w : Prod a b → ℂ := fun z => if z.1 = y then v z.2 else 0
  have hNw :
      Matrix.mulVec (Matrix.kronecker (1 : CMatrix a) ρ.marginalB.matrix) w = 0 := by
    ext z
    by_cases hzy : z.1 = y
    ·
      simpa [w, Matrix.mulVec, dotProduct, Matrix.kronecker,
        Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
        Finset.sum_ite_eq', hzy] using congrFun hv z.2
    · simp [w, Matrix.mulVec, dotProduct, Matrix.kronecker,
        Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
        Finset.sum_ite_eq', hzy]
  have hSupport := matrix_supports_identityTensor_marginalB (a := a) (b := b) ρ
  have hMw := hSupport w hNw
  ext k
  have hk := congrFun hMw (x, k)
  simpa [ReferenceIsometry.rightBlock, Matrix.mulVec, dotProduct, w,
    Fintype.sum_prod_type, Finset.sum_ite_eq'] using hk

theorem rightBlock_conjTranspose
    (ρ : State (Prod a b)) (x y : a) :
    Matrix.conjTranspose (ReferenceIsometry.rightBlock ρ.matrix x y) =
      ReferenceIsometry.rightBlock ρ.matrix y x := by
  ext i j
  have h := congrFun (congrFun ρ.pos.isHermitian.eq (y, i)) (x, j)
  simpa [ReferenceIsometry.rightBlock, Matrix.conjTranspose_apply] using h

/-- Compress a bipartite state to the positive spectral support of its right
marginal. -/
noncomputable def conditioningSupportCompressedState
    (ρ : State (Prod a b)) :
    State (Prod a (psdSupportIndex ρ.marginalB.matrix ρ.marginalB.pos)) where
  matrix :=
    psdSupportCompressRight (a := a) ρ.marginalB.matrix ρ.marginalB.pos ρ.matrix
  pos := by
    rw [psdSupportCompressRight_eq_conj]
    exact Matrix.PosSemidef.conjTranspose_mul_mul_same ρ.pos
      (Matrix.kronecker (1 : CMatrix a)
        (psdSupportIsometry ρ.marginalB.matrix ρ.marginalB.pos))
  trace_eq_one := by
    let X : CMatrix (Prod a (psdSupportIndex ρ.marginalB.matrix ρ.marginalB.pos)) :=
      psdSupportCompressRight (a := a) ρ.marginalB.matrix ρ.marginalB.pos ρ.matrix
    calc
      X.trace =
          (partialTraceA (a := a)
            (b := psdSupportIndex ρ.marginalB.matrix ρ.marginalB.pos) X).trace := by
          rw [partialTraceA_trace]
      _ = (psdSupportCompress ρ.marginalB.matrix ρ.marginalB.pos
            ρ.marginalB.matrix).trace := by
          rw [partialTraceA_psdSupportCompressRight]
          simp
      _ = ρ.marginalB.matrix.trace := by
          rw [psdSupportCompress_trace_self]
      _ = 1 := ρ.marginalB.trace_eq_one

@[simp]
theorem conditioningSupportCompressedState_matrix
    (ρ : State (Prod a b)) :
    ρ.conditioningSupportCompressedState.matrix =
      psdSupportCompressRight (a := a)
        ρ.marginalB.matrix ρ.marginalB.pos ρ.matrix := rfl

@[simp]
theorem conditioningSupportCompressedState_marginalB_matrix
    (ρ : State (Prod a b)) :
    ρ.conditioningSupportCompressedState.marginalB.matrix =
      psdSupportCompress ρ.marginalB.matrix ρ.marginalB.pos
        ρ.marginalB.matrix := by
  change partialTraceA
      (psdSupportCompressRight (a := a)
        ρ.marginalB.matrix ρ.marginalB.pos ρ.matrix) =
      psdSupportCompress ρ.marginalB.matrix ρ.marginalB.pos
        ρ.marginalB.matrix
  rw [partialTraceA_psdSupportCompressRight]
  rfl

theorem conditioningSupportCompressedState_marginalB_posDef
    (ρ : State (Prod a b)) :
    ρ.conditioningSupportCompressedState.marginalB.matrix.PosDef := by
  rw [conditioningSupportCompressedState_marginalB_matrix]
  exact psdSupportCompress_self_posDef ρ.marginalB.matrix ρ.marginalB.pos

@[simp]
theorem conditioningSupportCompressedState_conditioningIsometryApply
    (ρ : State (Prod a b)) :
    ρ.conditioningSupportCompressedState.conditioningIsometryApply
      (psdSupportReferenceIsometry ρ.marginalB.matrix ρ.marginalB.pos) = ρ := by
  apply State.ext
  ext x y
  let N : CMatrix b := ρ.marginalB.matrix
  let hN : N.PosSemidef := ρ.marginalB.pos
  let B : CMatrix b := ReferenceIsometry.rightBlock ρ.matrix x.1 y.1
  have hB : Matrix.Supports B N := by
    simpa [B, N] using rightBlock_supports_marginalB (a := a) (b := b) ρ x.1 y.1
  have hBstar : Matrix.Supports (Matrix.conjTranspose B) N := by
    rw [show Matrix.conjTranspose B =
        ReferenceIsometry.rightBlock ρ.matrix y.1 x.1 from by
      simpa [B] using rightBlock_conjTranspose (a := a) (b := b) ρ x.1 y.1]
    simpa [N] using rightBlock_supports_marginalB (a := a) (b := b) ρ y.1 x.1
  have hrec :=
    psdSupportCompress_reconstruct_of_supports_right_and_conjTranspose
      (M := B) (N := N) hN hB hBstar
  have hentry := congrFun (congrFun hrec x.2) y.2
  simpa [conditioningIsometryApply_matrix, ReferenceIsometry.applyMatrixRight,
    conditioningSupportCompressedState_matrix, psdSupportReferenceIsometry,
    psdSupportCompressRight, ReferenceIsometry.rightBlock, psdSupportCompress,
    B, N, hN] using hentry

/-- Feasibility predicate for the conditional min-entropy order constraint
`ρ_AB ≤ 2^{-λ} • (I_A ⊗ σ_B)` in the local bits convention. -/
def ConditionalMinEntropyFeasible (ρ : State (Prod a b)) (σ : State b) (lam : ℝ) :
    Prop :=
  ρ.matrix ≤ (Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ

@[simp]
theorem ConditionalMinEntropyFeasible_eq (ρ : State (Prod a b)) (σ : State b)
    (lam : ℝ) :
    ConditionalMinEntropyFeasible (a := a) ρ σ lam ↔
      ρ.matrix ≤ (Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ :=
  Iff.rfl

end State

namespace SubnormalizedState

variable {a : Type u} [Fintype a] [DecidableEq a]

variable {b : Type v} [Fintype b] [DecidableEq b]

variable {c : Type*} [Fintype c] [DecidableEq c]

/-! ## Scaled-state carriers -/

/-- Scale a normalized state by a real weight in `[0,1]`, yielding a
subnormalized state. This is the local smooth-entropy version of the scaled
pure-state carrier used by the subnormalized duality route. -/
def ofStateScale (ρ : State a) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SubnormalizedState a where
  matrix := t • ρ.matrix
  pos := Matrix.PosSemidef.smul ρ.pos ht0
  trace_le_one := by
    rw [Matrix.trace_smul, ρ.trace_eq_one]
    simpa [Complex.real_smul] using ht1

@[simp]
theorem ofStateScale_matrix (ρ : State a) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (ofStateScale ρ t ht0 ht1).matrix = t • ρ.matrix :=
  rfl

@[simp]
theorem ofStateScale_trace (ρ : State a) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (ofStateScale ρ t ht0 ht1).matrix.trace = (t : ℂ) := by
  rw [ofStateScale_matrix, Matrix.trace_smul, ρ.trace_eq_one]
  simp [Complex.real_smul]

@[simp]
theorem ofStateScale_trace_re (ρ : State a) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (ofStateScale ρ t ht0 ht1).matrix.trace.re = t := by
  rw [ofStateScale_trace]
  simp

/-- The `AB` marginal of a scaled pure tripartite state on left-associated
`ABC`. -/
def abMarginalFromScaledTripartitePure
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SubnormalizedState (Prod a b) :=
  ofStateScale ψ.state.marginalAB t ht0 ht1

@[simp]
theorem abMarginalFromScaledTripartitePure_matrix
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
      ψ t ht0 ht1).matrix = t • ψ.state.marginalAB.matrix :=
  rfl

/-- The `AC` marginal of a scaled pure tripartite state on left-associated
`ABC`. -/
def acMarginalFromScaledTripartitePure
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SubnormalizedState (Prod a c) :=
  ofStateScale ψ.state.marginalAC t ht0 ht1

@[simp]
theorem acMarginalFromScaledTripartitePure_matrix
    (ψ : PureVector (Prod (Prod a b) c)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
      ψ t ht0 ht1).matrix = t • ψ.state.marginalAC.matrix :=
  rfl

/-- The matrix `I_A ⊗ σ_B` used in subnormalized conditional entropy definitions.

Here `σ_B` is subnormalized, matching
[Tomamichel2015FiniteResources, calculus.tex:81-89] and
[Tomamichel2015FiniteResources, calculus.tex:191-198]. -/
def identityTensorStateMatrix (σ : SubnormalizedState b) : CMatrix (Prod a b) :=
  Matrix.kronecker (1 : CMatrix a) σ.matrix

/-- Feasibility predicate for subnormalized conditional min-entropy in the
local bits convention: `ρ_AB ≤ 2^{-λ} • (I_A ⊗ σ_B)` with
`σ_B ∈ S_≤(B)`. -/
def ConditionalMinEntropyFeasible
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) (lam : ℝ) :
    Prop :=
  ρ.matrix ≤ (Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ

@[simp]
theorem ConditionalMinEntropyFeasible_eq
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) (lam : ℝ) :
    ConditionalMinEntropyFeasible (a := a) ρ σ lam ↔
      ρ.matrix ≤ (Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ :=
  Iff.rfl

end SubnormalizedState

end

end QIT
