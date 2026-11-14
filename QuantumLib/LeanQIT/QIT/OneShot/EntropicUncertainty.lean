/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.ConditionalRenyiExtendedDuality
public import QIT.OneShot.EntropicUncertaintyComparison
public import QIT.States.Purification.Canonical

/-!
# Tripartite entropic uncertainty

This module formalizes Tomamichel's tripartite uncertainty relation from
`apps.tex:183-215`.  The pure-state proof combines the coherent-measurement
comparison with closed-order conditional Renyi duality.  The mixed-state
proof purifies the input and discards the purifying register by conditioning
data processing.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal
open Matrix

namespace QIT

universe u v w z

noncomputable section

namespace ProjectiveMeasurement.IsRankOne

variable {x : Type u} {y : Type v} {a : Type w} {b : Type z}
variable {c : Type*}
variable [Fintype x] [DecidableEq x]
variable [Fintype y] [DecidableEq y]
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]
variable {X : ProjectiveMeasurement x a} {Y : ProjectiveMeasurement y a}

def coherentPureGroupingEquiv :
    Prod (Prod (Prod y y) b) c ≃ Prod (Prod y (Prod y b)) c :=
  Equiv.prodCongr (Equiv.prodAssoc y y b) (Equiv.refl c)

/-- The coherent `Y,Y'` dilation with registers grouped as
`(Y x (Y' x B)) x C`, the association used by conditional duality. -/
def coherentGroupedPureVector (hY : Y.IsRankOne)
    (psi : PureVector (Prod (Prod a b) c)) :
    PureVector (Prod (Prod y (Prod y b)) c) :=
  hY.coherentGroupedSideIsometry.applyPureVector psi

theorem coherentGroupedPureVector_eq_reindex
    (hY : Y.IsRankOne) (psi : PureVector (Prod (Prod a b) c)) :
    hY.coherentGroupedPureVector psi =
      (hY.coherentPureVector psi).reindex coherentPureGroupingEquiv := by
  apply PureVector.ext_amp
  funext out
  rcases out with ⟨⟨outcome, copy, k⟩, l⟩
  simp [coherentGroupedPureVector, coherentPureGroupingEquiv,
    ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
    Matrix.mulVec, dotProduct, coherentGroupedSideIsometry_matrix,
    coherentPureVector_amp]
  by_cases hdiag : outcome = copy
  · subst copy
    simp [Fintype.sum_prod_type]
  · simp [hdiag]

private theorem partialTraceB_applyMatrix
    {r1 r2 t : Type*} [Fintype r1] [DecidableEq r1]
    [Fintype r2] [DecidableEq r2] [Fintype t]
    (V : ReferenceIsometry r1 r2) (M : CMatrix (Prod r1 t)) :
    partialTraceB (V.applyMatrix M) =
      V.matrix * partialTraceB M * Matrix.conjTranspose V.matrix := by
  ext i j
  simp [partialTraceB, ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]

/-- The `Y(Y'B)` marginal of the grouped coherent purification is the
coherent measurement of the original `AB` marginal. -/
theorem coherentGroupedPureVector_marginalAB
    (hY : Y.IsRankOne) (psi : PureVector (Prod (Prod a b) c)) :
    (hY.coherentGroupedPureVector psi).state.marginalAB =
      hY.coherentMeasurementState psi.state.marginalAB := by
  apply State.ext
  change
    partialTraceB
        (rankOneMatrix (hY.coherentGroupedSideIsometry.applyAmp psi.amp)) =
      MatrixMap.ofReferenceIsometry hY.coherentGroupedSideIsometry
        (partialTraceB (rankOneMatrix psi.amp))
  rw [hY.coherentGroupedSideIsometry.rankOne_applyAmp,
    partialTraceB_applyMatrix, MatrixMap.ofReferenceIsometry_apply]

/-- The complementary `YC` marginal of the grouped coherent purification is
the ordinary `Y` measurement of the original `AC` marginal. -/
theorem coherentGroupedPureVector_marginalAC
    (hY : Y.IsRankOne) (psi : PureVector (Prod (Prod a b) c)) :
    (hY.coherentGroupedPureVector psi).state.marginalAC =
      measureSubsystemState Y.toPOVM psi.state.marginalAC := by
  rw [← hY.coherentYCMarginal_eq_measure psi]
  rw [coherentGroupedPureVector_eq_reindex]
  apply State.ext
  ext i j
  change
    (∑ k : Prod y b,
      (hY.coherentPureVector psi).state.matrix
        (((i.1, k.1), k.2), i.2) (((j.1, k.1), k.2), j.2)) =
      ∑ copy : y, ∑ k : b,
        (hY.coherentPureVector psi).state.matrix
          (((i.1, copy), k), i.2) (((j.1, copy), k), j.2)
  rw [Fintype.sum_prod_type]

end ProjectiveMeasurement.IsRankOne

namespace PureVector

variable {x : Type u} {y : Type v} {a : Type w} {b : Type z}
variable {c : Type*}
variable [Fintype x] [DecidableEq x]
variable [Fintype y] [DecidableEq y]
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]
variable {X : ProjectiveMeasurement x a} {Y : ProjectiveMeasurement y a}

/-- The pure-state case of Tomamichel's tripartite entropic uncertainty
relation.  This is the direct combination of `eq:ucr-dual` with conditional
sandwiched-Renyi duality. -/
theorem tripartiteEntropicUncertainty
    (psi : PureVector (Prod (Prod a b) c))
    (hX : X.IsRankOne) (hY : Y.IsRankOne)
    (alpha beta : RenyiOrder) (hconj : alpha.recip + beta.recip = 2) :
    -log2 (X.rankOneTraceOverlap Y) <=
      State.conditionalSandwichedRenyiUpExtendedOrder
          (measureSubsystemState X.toPOVM psi.state.marginalAB) alpha +
        State.conditionalSandwichedRenyiUpExtendedOrder
          (measureSubsystemState Y.toPOVM psi.state.marginalAC) beta := by
  let omega := hY.coherentGroupedPureVector psi
  letI : Nonempty c := by
    rcases omega.state.nonempty with ⟨⟨_, side⟩⟩
    exact ⟨side⟩
  letI : Nonempty (Prod y b) := by
    rcases omega.state.nonempty with ⟨⟨⟨_, side⟩, _⟩⟩
    exact ⟨side⟩
  have hcomparison :=
    State.conditionalSandwichedRenyiUpExtendedOrder_coherentMeasurementComparison
      hX hY psi.state.marginalAB alpha
  have hduality :=
    omega.conditionalSandwichedRenyiUpExtendedOrder_duality alpha beta hconj
  rw [hY.coherentGroupedPureVector_marginalAB psi,
    hY.coherentGroupedPureVector_marginalAC psi] at hduality
  linarith

end PureVector

namespace State

variable {x : Type u} {y : Type v} {a : Type w} {b : Type z}
variable {c : Type*}
variable [Fintype x] [DecidableEq x]
variable [Fintype y] [DecidableEq y]
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]
variable {X : ProjectiveMeasurement x a} {Y : ProjectiveMeasurement y a}

/-- A canonical purification of `rho_ABC`, regrouped as the pure state
`A B (C R)`.  The reference is attached to `C` so the mixed-state reduction
is exactly conditioning data processing on `C R -> C`. -/
def entropicUncertaintyPurification (rho : State (Prod (Prod a b) c)) :
    PureVector
      (Prod (Prod a b) (Prod c (Prod (Prod a b) c))) :=
  (rho.canonicalPurification.reindex
      (Equiv.prodComm (Prod (Prod a b) c) (Prod (Prod a b) c))).reindex
    (Equiv.prodAssoc (Prod a b) c (Prod (Prod a b) c))

private theorem canonicalPurificationSwap_marginalA
    (rho : State (Prod (Prod a b) c)) :
    (rho.canonicalPurification.reindex
      (Equiv.prodComm (Prod (Prod a b) c) (Prod (Prod a b) c))).state.marginalA =
      rho := by
  apply State.ext
  ext i j
  have hp :
      partialTraceA rho.canonicalPurification.state.matrix = rho.matrix :=
    PureVector.partialTraceA_state_matrix_eq_of_purifies
      rho.canonicalPurification_purifies
  have hpij := congrFun (congrFun hp i) j
  simpa [State.marginalA, partialTraceB, partialTraceA,
    PureVector.reindex_state, State.reindex] using hpij

private theorem marginalA_reindex_prodAssoc
    {d e f : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e] [Fintype f] [DecidableEq f]
    (tau : State (Prod (Prod d e) f)) :
    (tau.reindex (Equiv.prodAssoc d e f)).marginalA =
      tau.marginalA.marginalA := by
  apply State.ext
  ext i j
  simp [State.marginalA, State.reindex, partialTraceB,
    Fintype.sum_prod_type]

/-- The `AB` marginal of the regrouped canonical purification is the original
`rho_AB`. -/
theorem entropicUncertaintyPurification_marginalAB
    (rho : State (Prod (Prod a b) c)) :
    (rho.entropicUncertaintyPurification).state.marginalAB = rho.marginalAB := by
  rw [entropicUncertaintyPurification, PureVector.reindex_state,
    State.marginalAB_eq_marginalA, marginalA_reindex_prodAssoc,
    canonicalPurificationSwap_marginalA]
  rfl

private theorem discardReference_marginalAC_reindex_prodAssoc
    {r : Type*} [Fintype r] [DecidableEq r]
    (tau : State (Prod (Prod (Prod a b) c) r)) :
    (((Channel.idChannel a).prod (Channel.traceOutRight c r)).applyState
      ((tau.reindex (Equiv.prodAssoc (Prod a b) c r)).marginalAC)) =
      tau.marginalA.marginalAC := by
  apply State.ext
  ext i j
  change
    MatrixMap.kron (Channel.idChannel a).map (Channel.traceOutRight c r).map
        (tau.reindex (Equiv.prodAssoc (Prod a b) c r)).marginalAC.matrix i j =
      tau.marginalA.marginalAC.matrix i j
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  simp only [Channel.traceOutRight, MatrixMap.partialTraceB_apply]
  change
    (∑ ref : r, ∑ side : b,
      tau.matrix (((i.1, side), i.2), ref) (((j.1, side), j.2), ref)) =
      ∑ side : b, ∑ ref : r,
        tau.matrix (((i.1, side), i.2), ref) (((j.1, side), j.2), ref)
  rw [Finset.sum_comm]

/-- Discarding the canonical reference from the `A(CR)` marginal recovers
the original `AC` marginal. -/
theorem entropicUncertaintyPurification_marginalAC_discardReference
    (rho : State (Prod (Prod a b) c)) :
    (((Channel.idChannel a).prod
        (Channel.traceOutRight c (Prod (Prod a b) c))).applyState
      rho.entropicUncertaintyPurification.state.marginalAC) = rho.marginalAC := by
  change
    (((Channel.idChannel a).prod
        (Channel.traceOutRight c (Prod (Prod a b) c))).applyState
      (((rho.canonicalPurification.reindex
        (Equiv.prodComm (Prod (Prod a b) c) (Prod (Prod a b) c))).state.reindex
          (Equiv.prodAssoc (Prod a b) c (Prod (Prod a b) c))).marginalAC)) =
      rho.marginalAC
  rw [discardReference_marginalAC_reindex_prodAssoc]
  rw [canonicalPurificationSwap_marginalA]

private theorem measureSubsystemState_discardRight
    {r : Type*} [Fintype r] [DecidableEq r]
    (M : POVM y a) (tau : State (Prod a (Prod c r))) :
    (((Channel.idChannel y).prod (Channel.traceOutRight c r)).applyState
      (measureSubsystemState M tau)) =
      measureSubsystemState M
        (((Channel.idChannel a).prod (Channel.traceOutRight c r)).applyState tau) := by
  apply State.ext
  ext i j
  rcases i with ⟨iy, ic⟩
  rcases j with ⟨jy, jc⟩
  change
    MatrixMap.kron (Channel.idChannel y).map (Channel.traceOutRight c r).map
        (MatrixMap.kron (Channel.measure M).map
          (Channel.idChannel (Prod c r)).map tau.matrix) (iy, ic) (jy, jc) =
      MatrixMap.kron (Channel.measure M).map (Channel.idChannel c).map
        (MatrixMap.kron (Channel.idChannel a).map
          (Channel.traceOutRight c r).map tau.matrix) (iy, ic) (jy, jc)
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  rw [MatrixMap.kron_idChannel_apply_slice]
  simp only [Channel.traceOutRight, MatrixMap.partialTraceB_apply]
  simp [partialTraceB, MatrixMap.kron_idChannel_apply_slice,
    MatrixMap.kron_idChannel_left_apply_slice]
  by_cases hij : iy = jy
  · subst jy
    simp only [Matrix.trace, Matrix.sum_apply]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single_of_mem iy (Finset.mem_univ iy)]
    · simp only [Matrix.single_apply, and_self, if_true]
      rw [Finset.sum_eq_single_of_mem iy (Finset.mem_univ iy)]
      · simp only [if_true]
        simp only [Matrix.diag_apply, Matrix.mul_apply]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun inputRow _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun inputColumn _ => ?_
        rw [Finset.sum_mul]
      · intro outcome _ houtcome
        split
        · rename_i h
          exact (houtcome h).elim
        · rfl
    · intro outcome _ houtcome
      apply Finset.sum_eq_zero
      intro reference _
      rw [Matrix.single_apply, if_neg]
      intro hdiag
      exact houtcome hdiag.1
  · have hnone : ∀ outcome : y, ¬ (outcome = iy ∧ outcome = jy) := by
      intro outcome houtcome
      exact hij (houtcome.1.symm.trans houtcome.2)
    simp [Matrix.sum_apply, hnone]

/-- Measuring `A` and then discarding the canonical reference gives the
ordinary measured `YC` state of `rho_AC`. -/
theorem entropicUncertaintyPurification_measure_marginalAC_discardReference
    (rho : State (Prod (Prod a b) c)) :
    (((Channel.idChannel y).prod
        (Channel.traceOutRight c (Prod (Prod a b) c))).applyState
      (measureSubsystemState Y.toPOVM
        rho.entropicUncertaintyPurification.state.marginalAC)) =
      measureSubsystemState Y.toPOVM rho.marginalAC := by
  rw [measureSubsystemState_discardRight]
  rw [entropicUncertaintyPurification_marginalAC_discardReference]

/-- Tomamichel's tripartite entropic uncertainty relation for an arbitrary
normalized state.  The pure-state result is applied to the canonical
purification, after which conditioning data processing discards the
purifying reference. -/
theorem tripartiteEntropicUncertainty
    (rho : State (Prod (Prod a b) c))
    (hX : X.IsRankOne) (hY : Y.IsRankOne)
    (alpha beta : RenyiOrder) (hconj : alpha.recip + beta.recip = 2) :
    -log2 (X.rankOneTraceOverlap Y) <=
      conditionalSandwichedRenyiUpExtendedOrder
          (measureSubsystemState X.toPOVM rho.marginalAB) alpha +
        conditionalSandwichedRenyiUpExtendedOrder
          (measureSubsystemState Y.toPOVM rho.marginalAC) beta := by
  have hpure :=
    rho.entropicUncertaintyPurification.tripartiteEntropicUncertainty
      hX hY alpha beta hconj
  rw [entropicUncertaintyPurification_marginalAB] at hpure
  have hdpi :=
    conditionalSandwichedRenyiUpExtendedOrder_dataProcessing_discardRight
      (measureSubsystemState Y.toPOVM
        rho.entropicUncertaintyPurification.state.marginalAC) beta
  rw [entropicUncertaintyPurification_measure_marginalAC_discardReference] at hdpi
  linarith

end State

end

end QIT
