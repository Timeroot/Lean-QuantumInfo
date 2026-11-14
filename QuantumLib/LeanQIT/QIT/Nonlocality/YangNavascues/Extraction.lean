/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Nonlocality.SelfTesting
public import QIT.Nonlocality.YangNavascues.Action

/-!
# Yang-Navascues extraction bridge

This module connects the explicit CGS branch-sum action layer to the
self-testing extraction predicate.  The remaining source-strength YN work is
the residual tensor calculation proving that the branch sum is the advertised
`garbage tensor target` matrix.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

namespace QIT
namespace YangNavascues

universe u v w

noncomputable section

namespace YNData

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

variable (data : YNData ι HA HB)

/--
The source residual/garbage vector from the CGS calculation:
`c_0^{-1} P_A^(0) |ψ⟩`.
-/
def cgsExtraVector (ψ : PureVector (HA × HB)) : HA × HB → ℂ :=
  (((data.target.coeff data.target.base)⁻¹ : ℝ) : ℂ) • data.baseBranchVector ψ

/--
Package the source residual vector as a pure vector once its normalization has
been proved from the YN hypotheses.
-/
def cgsExtraPureVectorOfTrace (ψ : PureVector (HA × HB))
    (hTrace : (rankOneMatrix (data.cgsExtraVector ψ)).trace = 1) :
    PureVector (HA × HB) where
  amp := data.cgsExtraVector ψ
  trace_rankOne_eq_one := hTrace

/--
The source target vector, reindexed into the concrete ancilla basis used by
the assembled CGS local isometry.
-/
def cgsTargetPureVector (B : SchmidtTarget.BaseReindexToFin data.target) :
    PureVector (Fin (Fintype.card ι) × Fin (Fintype.card ι)) :=
  data.target.pureVector.reindex (Equiv.prodCongr B.toEquiv B.toEquiv)

/-- Coordinate form of the reindexed diagonal target vector. -/
theorem cgsTargetPureVector_amp_apply
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (ka kb : Fin (Fintype.card ι)) :
    (data.cgsTargetPureVector B).amp (ka, kb) =
      if ka = kb then (data.target.coeff (B.toEquiv.symm ka) : ℂ) else 0 := by
  by_cases h : ka = kb
  · subst kb
    simp [cgsTargetPureVector, SchmidtTarget.amp]
  · simp [cgsTargetPureVector, SchmidtTarget.amp, h]

/-- The source target state in the concrete CGS ancilla basis. -/
def cgsTargetState (B : SchmidtTarget.BaseReindexToFin data.target) :
    State (Fin (Fintype.card ι) × Fin (Fintype.card ι)) :=
  (data.cgsTargetPureVector B).state

/--
The residual tensor output vector in local-isometry output order:
physical garbage on `(HA × HB)` tensored with the reindexed target ancillas.
-/
def cgsResidualTensorVector
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (extra : PureVector (HA × HB)) :
    CGSOutput ι HA HB → ℂ :=
  fun x =>
    extra.amp (x.1.1, x.2.1) *
      (data.cgsTargetPureVector B).amp (x.1.2, x.2.2)

/--
The explicit residual tensor vector has exactly the matrix representation used
by the source-strength auxiliary extraction predicate.
-/
theorem garbageTensorTargetState_matrix_eq_rankOne_cgsResidualTensorVector
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (extra : PureVector (HA × HB)) :
    (Bell.garbageTensorTargetState extra.state (data.cgsTargetState B)).matrix =
      rankOneMatrix (data.cgsResidualTensorVector B extra) := by
  ext x y
  rcases x with ⟨⟨ha, ka⟩, ⟨hb, kb⟩⟩
  rcases y with ⟨⟨ha', ka'⟩, ⟨hb', kb'⟩⟩
  simp [Bell.garbageTensorTargetState, Bell.reindexState,
    Bell.garbageTensorTargetEquiv, State.prod, cgsTargetState,
    cgsTargetPureVector, cgsResidualTensorVector, PureVector.state,
    rankOneMatrix_apply, Matrix.kronecker]
  ring

/--
Residual tensor algebra bridge: once the CGS action vector has the explicit
`extra ⊗ target` form, the branch-sum density is the advertised
garbage-tensor-target matrix.
-/
theorem cgsActionBranchSumMatrix_eq_garbageTensorTargetState_of_actionVector_eq
    {rho : State (HA × HB)}
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (W : BobLocalOrthogonalization data rho) (ψ : PureVector (HA × HB))
    (extra : PureVector (HA × HB))
    (hVec :
      data.cgsActionVector B W ψ =
        data.cgsResidualTensorVector B extra) :
    data.cgsActionBranchSumMatrix B W ψ =
      (Bell.garbageTensorTargetState extra.state (data.cgsTargetState B)).matrix := by
  rw [data.cgsActionBranchSumMatrix_eq_rankOneActionVector B W ψ]
  rw [hVec]
  rw [← data.garbageTensorTargetState_matrix_eq_rankOne_cgsResidualTensorVector B extra]

/--
Source-shaped residual tensor bridge with the CGS garbage vector
`c_0^{-1} P_A^0 ψ`.
-/
theorem cgsActionBranchSumMatrix_eq_garbageTensorTargetState_of_extraActionVector_eq
    {rho : State (HA × HB)}
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (W : BobLocalOrthogonalization data rho) (ψ : PureVector (HA × HB))
    (hTrace : (rankOneMatrix (data.cgsExtraVector ψ)).trace = 1)
    (hVec :
      data.cgsActionVector B W ψ =
        data.cgsResidualTensorVector B (data.cgsExtraPureVectorOfTrace ψ hTrace)) :
    data.cgsActionBranchSumMatrix B W ψ =
      (Bell.garbageTensorTargetState
        (data.cgsExtraPureVectorOfTrace ψ hTrace).state
        (data.cgsTargetState B)).matrix :=
  data.cgsActionBranchSumMatrix_eq_garbageTensorTargetState_of_actionVector_eq
    B W ψ (data.cgsExtraPureVectorOfTrace ψ hTrace) hVec

end YNData

namespace YNPhaseAlignedConditions

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
variable {data : YNData ι HA HB} {ψ : PureVector (HA × HB)}

/-- The source residual vector `c_0^{-1} P_A^0 ψ` is normalized. -/
theorem cgsExtraVector_trace_rankOne
    (h : YNPhaseAlignedConditions data ψ) :
    (rankOneMatrix (data.cgsExtraVector ψ)).trace = 1 := by
  unfold YNData.cgsExtraVector
  rw [rankOneMatrix_trace]
  have hbase := h.baseBranchVector_trace_rankOne
  rw [rankOneMatrix_trace] at hbase
  let r : ℂ := (((data.target.coeff data.target.base)⁻¹ : ℝ) : ℂ)
  let v : HA × HB → ℂ := data.baseBranchVector ψ
  change (r • v) ⬝ᵥ (fun i => star ((r • v) i)) = 1
  have hscaled :
      (r • v) ⬝ᵥ (fun i => star ((r • v) i)) =
        r * star r * (v ⬝ᵥ fun i => star (v i)) := by
    simp [dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [hscaled]
  have hbase' : v ⬝ᵥ (fun i => star (v i)) =
      (((data.target.coeff data.target.base) ^ 2 : ℝ) : ℂ) := by
    simpa [v] using hbase
  rw [hbase']
  simp [r]
  have hbase_ne : data.target.coeff data.target.base ≠ 0 :=
    ne_of_gt (data.target.coeff_pos data.target.base)
  field_simp [hbase_ne]

/-- The normalized CGS residual/garbage pure vector. -/
def cgsExtraPureVector (h : YNPhaseAlignedConditions data ψ) :
    PureVector (HA × HB) :=
  data.cgsExtraPureVectorOfTrace ψ h.cgsExtraVector_trace_rankOne

/--
Conditional bridge from the YN branch-sum calculation to the source-strength
auxiliary extraction predicate.

The nontrivial downstream theorem is the supplied `hTensor`, identifying the
explicit branch-sum matrix with `garbage tensor target`.
-/
theorem extractsBipartiteStateWithAux_of_actionBranchSum_eq
    (h : YNPhaseAlignedConditions data ψ)
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (garbage : State (HA × HB))
    (targetState : State (Fin (Fintype.card ι) × Fin (Fintype.card ι)))
    (hTensor :
      data.cgsActionBranchSumMatrix B h.toBobLocalOrthogonalization ψ =
        (Bell.garbageTensorTargetState garbage targetState).matrix) :
    Bell.ExtractsBipartiteStateWithAux ψ.state garbage targetState := by
  refine ⟨data.cgsLocalIsometry B h.toBobLocalOrthogonalization, ?_⟩
  apply State.ext
  rw [TwoQubit.LocalIsometry.applyState_matrix]
  rw [h.cgsLocalIsometry_applyMatrix_eq_actionBranchSum B]
  exact hTensor

/--
Structured residual-tensor extraction bridge.

This replaces the raw matrix hypothesis in
`extractsBipartiteStateWithAux_of_actionBranchSum_eq` with the source-shaped
vector claim that the CGS action is `extra ⊗ target` in output order.
-/
theorem extractsBipartiteStateWithAux_of_actionVector_eq
    (h : YNPhaseAlignedConditions data ψ)
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (extra : PureVector (HA × HB))
    (hVec :
      data.cgsActionVector B h.toBobLocalOrthogonalization ψ =
        data.cgsResidualTensorVector B extra) :
    Bell.ExtractsBipartiteStateWithAux ψ.state extra.state (data.cgsTargetState B) := by
  apply h.extractsBipartiteStateWithAux_of_actionBranchSum_eq
    B extra.state (data.cgsTargetState B)
  exact data.cgsActionBranchSumMatrix_eq_garbageTensorTargetState_of_actionVector_eq
    B h.toBobLocalOrthogonalization ψ extra hVec

/--
Source-shaped extraction bridge using the CGS garbage vector
`c_0^{-1} P_A^0 ψ`.
-/
theorem extractsBipartiteStateWithAux_of_extraActionVector_eq
    (h : YNPhaseAlignedConditions data ψ)
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (hTrace : (rankOneMatrix (data.cgsExtraVector ψ)).trace = 1)
    (hVec :
      data.cgsActionVector B h.toBobLocalOrthogonalization ψ =
        data.cgsResidualTensorVector B (data.cgsExtraPureVectorOfTrace ψ hTrace)) :
    Bell.ExtractsBipartiteStateWithAux ψ.state
      (data.cgsExtraPureVectorOfTrace ψ hTrace).state (data.cgsTargetState B) := by
  apply h.extractsBipartiteStateWithAux_of_actionBranchSum_eq
    B (data.cgsExtraPureVectorOfTrace ψ hTrace).state (data.cgsTargetState B)
  exact data.cgsActionBranchSumMatrix_eq_garbageTensorTargetState_of_extraActionVector_eq
    B h.toBobLocalOrthogonalization ψ hTrace hVec

/--
Normalized source-shaped extraction bridge using the CGS garbage vector
`c_0^{-1} P_A^0 ψ`, with normalization derived from the YN hypotheses.
-/
theorem extractsBipartiteStateWithAux_of_normalizedExtraActionVector_eq
    (h : YNPhaseAlignedConditions data ψ)
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (hVec :
      data.cgsActionVector B h.toBobLocalOrthogonalization ψ =
        data.cgsResidualTensorVector B h.cgsExtraPureVector) :
    Bell.ExtractsBipartiteStateWithAux ψ.state
      h.cgsExtraPureVector.state (data.cgsTargetState B) := by
  exact h.extractsBipartiteStateWithAux_of_actionVector_eq
    B h.cgsExtraPureVector hVec

private theorem aliceProjectionOp_mul_bobLocalBranch_mulVec
    (h : YNPhaseAlignedConditions data ψ) (i j : ι) :
    ((data.aliceProjectionOp i *
        data.bobLocalOp ((h.toBobLocalOrthogonalization.bobLocal j).matrix)).mulVec ψ.amp) =
      if i = j then (data.aliceProjectionOp i).mulVec ψ.amp else 0 := by
  rw [← Matrix.mulVec_mulVec]
  change Matrix.mulVec (data.aliceProjectionOp i)
      (Matrix.mulVec (bobLocalOp HA h.toBobLocalOrthogonalization.bobLocal j) ψ.amp) =
    if i = j then Matrix.mulVec (data.aliceProjectionOp i) ψ.amp else 0
  rw [h.bobLocalOrthogonalization_mulVec_eq_bobProjectionOp j]
  rw [← h.projectionAligned j]
  rw [Matrix.mulVec_mulVec]
  by_cases hij : i = j
  · subst j
    rw [data.aliceProjectionOp_idempotent i]
    simp
  · rw [data.aliceProjectionOp_orthogonal i j hij]
    simp [hij]

private theorem aliceProjectionOp_mul_bobLocalComplement_mulVec
    (h : YNPhaseAlignedConditions data ψ)
    (B : SchmidtTarget.BaseReindexToFin data.target) (i : ι) :
    ((data.aliceProjectionOp i *
        (1 - ∑ l : Fin (Fintype.card ι),
          data.bobLocalOp
            ((h.toBobLocalOrthogonalization.bobLocal (B.toEquiv.symm l)).matrix))).mulVec
        ψ.amp) = 0 := by
  classical
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_sum]
  rw [Matrix.sub_mulVec, Matrix.sum_mulVec]
  have hsingle :
      (∑ l : Fin (Fintype.card ι),
          ((data.aliceProjectionOp i *
            data.bobLocalOp
              ((h.toBobLocalOrthogonalization.bobLocal (B.toEquiv.symm l)).matrix)).mulVec
              ψ.amp)) =
        (data.aliceProjectionOp i).mulVec ψ.amp := by
    rw [Finset.sum_eq_single (B.toEquiv i)]
    · have hbranch :=
        aliceProjectionOp_mul_bobLocalBranch_mulVec (h := h) i (B.toEquiv.symm (B.toEquiv i))
      simpa using hbranch
    · intro l _ hl
      have hne : i ≠ B.toEquiv.symm l := by
        intro hEq
        apply hl
        apply B.toEquiv.symm.injective
        simpa using hEq.symm
      have hbranch :=
        aliceProjectionOp_mul_bobLocalBranch_mulVec (h := h) i (B.toEquiv.symm l)
      simpa [hne] using hbranch
    · intro hmem
      exact (hmem (Finset.mem_univ (B.toEquiv i))).elim
  rw [hsingle]
  ext x
  simp

private theorem aliceProjection_kronecker_bobMatrix_eq
    (R : CMatrix HB) (i : ι) :
    Matrix.kroneckerMap (fun x1 x2 : ℂ => x1 * x2)
        (data.aliceProjection.effects i) R =
      data.aliceProjectionOp i * data.bobLocalOp R := by
  simp [YNData.aliceProjectionOp, YNData.bobLocalOp, ← Matrix.mul_kronecker_mul]

private theorem aliceProjection_kronecker_bobLocalBranch_mulVec
    (h : YNPhaseAlignedConditions data ψ) (i j : ι) :
    (Matrix.kroneckerMap (fun x1 x2 : ℂ => x1 * x2)
        (data.aliceProjection.effects i)
        ((h.toBobLocalOrthogonalization.bobLocal j).matrix)).mulVec ψ.amp =
      if i = j then (data.aliceProjectionOp i).mulVec ψ.amp else 0 := by
  rw [aliceProjection_kronecker_bobMatrix_eq (data := data)]
  exact aliceProjectionOp_mul_bobLocalBranch_mulVec (h := h) i j

private theorem aliceProjection_kronecker_bobLocalComplement_mulVec
    (h : YNPhaseAlignedConditions data ψ)
    (B : SchmidtTarget.BaseReindexToFin data.target) (i : ι) :
    (Matrix.kroneckerMap (fun x1 x2 : ℂ => x1 * x2)
        (data.aliceProjection.effects i)
        (1 - ∑ l : Fin (Fintype.card ι),
          (h.toBobLocalOrthogonalization.bobLocal (B.toEquiv.symm l)).matrix)).mulVec
        ψ.amp = 0 := by
  rw [aliceProjection_kronecker_bobMatrix_eq (data := data)]
  have hBob :
      data.bobLocalOp
          (1 - ∑ l : Fin (Fintype.card ι),
            (h.toBobLocalOrthogonalization.bobLocal (B.toEquiv.symm l)).matrix) =
        1 - ∑ l : Fin (Fintype.card ι),
          data.bobLocalOp
            ((h.toBobLocalOrthogonalization.bobLocal (B.toEquiv.symm l)).matrix) := by
    ext x y
    rcases x with ⟨ha, hb⟩
    rcases y with ⟨ha', hb'⟩
    by_cases hha : ha = ha'
    · subst ha'
      by_cases hhb : hb = hb'
      · subst hb'
        simp [YNData.bobLocalOp, Matrix.kronecker, Matrix.sub_apply, Matrix.sum_apply]
      · simp [YNData.bobLocalOp, Matrix.kronecker, Matrix.sub_apply, Matrix.sum_apply, hhb]
    · simp [YNData.bobLocalOp, Matrix.kronecker, Matrix.sub_apply, Matrix.sum_apply, hha]
  rw [hBob]
  exact aliceProjectionOp_mul_bobLocalComplement_mulVec (h := h) B i

private theorem aliceBobBranchOperator_mulVec_eq_transformedBobProjectionOp
    (h : YNPhaseAlignedConditions data ψ)
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (k : Fin (Fintype.card ι)) :
    ((data.aliceBranchOperator B k ⊗ₖ
        h.toBobLocalOrthogonalization.bobBranchOperator B k).mulVec ψ.amp) =
      (data.transformedBobProjectionOp (B.toEquiv.symm k)).mulVec ψ.amp := by
  classical
  by_cases hkbase : k = data.target.baseIndex
  · subst k
    rw [BobLocalOrthogonalization.bobBranchOperator_base]
    have hbase_symm : B.toEquiv.symm data.target.baseIndex = data.target.base := by
      apply B.toEquiv.injective
      simp [SchmidtTarget.BaseReindexToFin.toEquiv_base]
    simp only [YNData.aliceBranchOperator, hbase_symm]
    rw [Matrix.mul_kronecker_mul]
    simp only [YNData.transformedBobProjectionOp_eq, YNData.unitaryOp]
    rw [← Matrix.mulVec_mulVec]
    have hinner :
        (Matrix.kroneckerMap (fun x1 x2 : ℂ => x1 * x2)
            (data.aliceProjection.effects data.target.base)
            ((h.toBobLocalOrthogonalization.bobLocal data.target.base).matrix +
              (1 - ∑ l : Fin (Fintype.card ι),
                (h.toBobLocalOrthogonalization.bobLocal (B.toEquiv.symm l)).matrix))).mulVec
            ψ.amp =
          (data.bobProjectionOp data.target.base).mulVec ψ.amp := by
      rw [Matrix.kronecker_add, Matrix.add_mulVec]
      rw [aliceProjection_kronecker_bobLocalBranch_mulVec (h := h)
        data.target.base data.target.base]
      rw [aliceProjection_kronecker_bobLocalComplement_mulVec (h := h) B data.target.base]
      simpa [YNData.aliceProjectionOp, YNData.bobProjectionOp] using
        h.projectionAligned data.target.base
    rw [hinner]
    rw [Matrix.mulVec_mulVec]
    simp [Matrix.kronecker]
  · rw [h.toBobLocalOrthogonalization.bobBranchOperator_ne_base B k hkbase]
    simp only [YNData.aliceBranchOperator]
    rw [Matrix.mul_kronecker_mul]
    simp only [YNData.transformedBobProjectionOp_eq, YNData.unitaryOp]
    rw [← Matrix.mulVec_mulVec]
    have hinner :
        (Matrix.kroneckerMap (fun x1 x2 : ℂ => x1 * x2)
            (data.aliceProjection.effects (B.toEquiv.symm k))
            (h.toBobLocalOrthogonalization.bobLocal (B.toEquiv.symm k)).matrix).mulVec
            ψ.amp =
          (data.bobProjectionOp (B.toEquiv.symm k)).mulVec ψ.amp := by
      rw [aliceProjection_kronecker_bobLocalBranch_mulVec (h := h)
        (B.toEquiv.symm k) (B.toEquiv.symm k)]
      simpa [YNData.aliceProjectionOp, YNData.bobProjectionOp] using
        h.projectionAligned (B.toEquiv.symm k)
    rw [hinner]
    rw [Matrix.mulVec_mulVec]
    simp [Matrix.kronecker]

private theorem aliceBobBranchOperator_mulVec_eq_zero_of_ne
    (h : YNPhaseAlignedConditions data ψ)
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (ka kb : Fin (Fintype.card ι)) (hneq : ka ≠ kb) :
    ((data.aliceBranchOperator B ka ⊗ₖ
        h.toBobLocalOrthogonalization.bobBranchOperator B kb).mulVec ψ.amp) = 0 := by
  classical
  by_cases hkbbase : kb = data.target.baseIndex
  · subst kb
    rw [BobLocalOrthogonalization.bobBranchOperator_base]
    have hbase_symm : B.toEquiv.symm data.target.baseIndex = data.target.base := by
      apply B.toEquiv.injective
      simp [SchmidtTarget.BaseReindexToFin.toEquiv_base]
    simp only [YNData.aliceBranchOperator]
    rw [Matrix.mul_kronecker_mul]
    rw [← Matrix.mulVec_mulVec]
    have hidx_ne : B.toEquiv.symm ka ≠ data.target.base := by
      intro hEq
      apply hneq
      apply B.toEquiv.symm.injective
      simpa [hbase_symm] using hEq
    have hinner :
        (Matrix.kroneckerMap (fun x1 x2 : ℂ => x1 * x2)
            (data.aliceProjection.effects (B.toEquiv.symm ka))
            ((h.toBobLocalOrthogonalization.bobLocal data.target.base).matrix +
              (1 - ∑ l : Fin (Fintype.card ι),
                (h.toBobLocalOrthogonalization.bobLocal (B.toEquiv.symm l)).matrix))).mulVec
            ψ.amp = 0 := by
      rw [Matrix.kronecker_add, Matrix.add_mulVec]
      rw [aliceProjection_kronecker_bobLocalBranch_mulVec (h := h)
        (B.toEquiv.symm ka) data.target.base]
      rw [aliceProjection_kronecker_bobLocalComplement_mulVec (h := h) B (B.toEquiv.symm ka)]
      simp [hidx_ne]
    rw [hinner]
    simp
  · rw [h.toBobLocalOrthogonalization.bobBranchOperator_ne_base B kb hkbbase]
    simp only [YNData.aliceBranchOperator]
    rw [Matrix.mul_kronecker_mul]
    rw [← Matrix.mulVec_mulVec]
    have hsymm_ne : B.toEquiv.symm ka ≠ B.toEquiv.symm kb := by
      intro hEq
      exact hneq (B.toEquiv.symm.injective hEq)
    have hinner :
        (Matrix.kroneckerMap (fun x1 x2 : ℂ => x1 * x2)
            (data.aliceProjection.effects (B.toEquiv.symm ka))
            (h.toBobLocalOrthogonalization.bobLocal (B.toEquiv.symm kb)).matrix).mulVec
            ψ.amp = 0 := by
      rw [aliceProjection_kronecker_bobLocalBranch_mulVec (h := h)
        (B.toEquiv.symm ka) (B.toEquiv.symm kb)]
      simp [hsymm_ne]
    rw [hinner]
    simp

/--
The phase-aligned YN vector conditions identify the assembled CGS action
vector with the residual garbage tensor target vector.
-/
theorem cgsActionVector_eq_residualTensorVector
    (h : YNPhaseAlignedConditions data ψ)
    (B : SchmidtTarget.BaseReindexToFin data.target) :
    data.cgsActionVector B h.toBobLocalOrthogonalization ψ =
      data.cgsResidualTensorVector B h.cgsExtraPureVector := by
  classical
  ext x
  rcases x with ⟨⟨ha, ka⟩, ⟨hb, kb⟩⟩
  rw [data.cgsActionVector_apply_branchOperators B h.toBobLocalOrthogonalization ψ ha hb ka kb]
  by_cases hkk : ka = kb
  · subst kb
    rw [aliceBobBranchOperator_mulVec_eq_transformedBobProjectionOp (h := h) B ka]
    rw [h.phaseAligned (B.toEquiv.symm ka)]
    simp [YNData.cgsResidualTensorVector, YNData.cgsTargetPureVector_amp_apply,
      cgsExtraPureVector, YNData.cgsExtraPureVectorOfTrace, YNData.cgsExtraVector]
    ring_nf
  · rw [aliceBobBranchOperator_mulVec_eq_zero_of_ne (h := h) B ka kb hkk]
    simp [YNData.cgsResidualTensorVector, YNData.cgsTargetPureVector_amp_apply, hkk]

/--
The phase-aligned YN source hypotheses extract the target state with the CGS
garbage vector as auxiliary state.
-/
theorem extractsBipartiteStateWithAux
    (h : YNPhaseAlignedConditions data ψ)
    (B : SchmidtTarget.BaseReindexToFin data.target) :
    Bell.ExtractsBipartiteStateWithAux ψ.state h.cgsExtraPureVector.state
      (data.cgsTargetState B) := by
  exact h.extractsBipartiteStateWithAux_of_normalizedExtraActionVector_eq B
    (h.cgsActionVector_eq_residualTensorVector B)

end YNPhaseAlignedConditions

end

end YangNavascues
end QIT
