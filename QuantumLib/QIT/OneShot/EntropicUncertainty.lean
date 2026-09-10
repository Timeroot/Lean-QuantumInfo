/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.OneShot.ConditionalRenyiExtendedDuality
public import QuantumLib.QIT.OneShot.EntropicUncertaintyComparison
public import QuantumLib.QIT.States.Purification.Canonical

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

noncomputable section
universe u v w z

open QIT

namespace QIT

namespace ProjectiveMeasurement.IsRankOne

variable {x : Type u} {y : Type v} {a : Type w} {b : Type z}
variable {c : Type*}
variable [Fintype x] [DecidableEq x]
variable [Fintype y] [DecidableEq y]
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]
variable {X : ProjectiveMeasurement x a} {Y : ProjectiveMeasurement y a}

/-- Reassociating the coherent dilation registers: `((y × y) × b) × c ≃ (y × (y × b)) × c`. -/
def coherentPureGroupingEquiv :
    (((y × y) × b) × c) ≃ ((y × (y × b)) × c) :=
  Equiv.prodCongr (Equiv.prodAssoc y y b) (Equiv.refl c)

/-- The coherent `Y,Y'` dilation with registers grouped as
`(Y x (Y' x B)) x C`, the association used by conditional duality. -/
def coherentGroupedKet (hY : Y.IsRankOne)
    (psi : Ket ((a × b) × c)) :
    Ket ((y × (y × b)) × c) :=
  hY.coherentGroupedSideIsometry.applyKet psi

theorem coherentGroupedKet_eq_reindex
    (hY : Y.IsRankOne) (psi : Ket ((a × b) × c)) :
    hY.coherentGroupedKet psi =
      (hY.coherentKet psi).reindex coherentPureGroupingEquiv := by
  apply Ket.ext_vec
  funext out
  rcases out with ⟨⟨outcome, copy, k⟩, l⟩
  simp [coherentGroupedKet, coherentPureGroupingEquiv,
    ReferenceIsometry.applyKet_vec, ReferenceIsometry.applyAmp,
    Matrix.mulVec, dotProduct, coherentGroupedSideIsometry_matrix,
    coherentKet_vec]
  by_cases hdiag : outcome = copy
  · subst copy
    simp [Fintype.sum_prod_type]
  · simp [hdiag]

/-- The `Y(Y'B)` marginal of the grouped coherent purification is the
coherent measurement of the original `AB` marginal. -/
theorem coherentGroupedKet_marginalAB
    (hY : Y.IsRankOne) (psi : Ket ((a × b) × c)) :
    (hY.coherentGroupedKet psi).state.marginalAB =
      hY.coherentMeasurementState psi.state.marginalAB := by
  apply MState.ext
  simp only [MState.marginalAB_eq_traceRight, MState.traceRight_m, Ket.state_matrix,
    coherentGroupedKet, ReferenceIsometry.applyKet_vec,
    coherentMeasurementState, CPTPOp.mat_coe_eq_apply_mat,
    CPTPOp.ofReferenceIsometry_map]
  rw [hY.coherentGroupedSideIsometry.rankOne_applyAmp,
    ReferenceIsometry.traceRight_applyMatrix, MatrixMap.ofReferenceIsometry_apply]

/-- The complementary `YC` marginal of the grouped coherent purification is
the ordinary `Y` measurement of the original `AC` marginal. -/
theorem coherentGroupedKet_marginalAC
    (hY : Y.IsRankOne) (psi : Ket ((a × b) × c)) :
    (hY.coherentGroupedKet psi).state.marginalAC =
      measureSubsystemState Y.toPOVM psi.state.marginalAC := by
  rw [← hY.coherentYCMarginal_eq_measure psi]
  rw [coherentGroupedKet_eq_reindex]
  apply MState.ext
  ext i j
  simp only [Ket.reindex_state, MState.marginalAC_matrix, MState.reindex_matrix,
    coherentYCMarginal, Matrix.of_apply, Matrix.submatrix_apply]
  change
    (∑ k : y × b,
      (hY.coherentKet psi).state.m
        (((i.1, k.1), k.2), i.2) (((j.1, k.1), k.2), j.2)) =
      ∑ copy : y, ∑ k : b,
        (hY.coherentKet psi).state.m
          (((i.1, copy), k), i.2) (((j.1, copy), k), j.2)
  rw [Fintype.sum_prod_type]

end ProjectiveMeasurement.IsRankOne

end QIT

namespace Ket

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
    (psi : Ket ((a × b) × c))
    (hX : X.IsRankOne) (hY : Y.IsRankOne)
    (alpha beta : RenyiOrder) (hconj : alpha.recip + beta.recip = 2) :
    -log2 (X.rankOneTraceOverlap Y) ≤
      MState.conditionalSandwichedRenyiUpExtendedOrder
          (measureSubsystemState X.toPOVM psi.state.marginalAB) alpha +
        MState.conditionalSandwichedRenyiUpExtendedOrder
          (measureSubsystemState Y.toPOVM psi.state.marginalAC) beta := by
  let omega := hY.coherentGroupedKet psi
  let : Nonempty c := by
    rcases omega.state.nonempty with ⟨⟨_, side⟩⟩
    exact ⟨side⟩
  let : Nonempty (y × b) := by
    rcases omega.state.nonempty with ⟨⟨⟨_, side⟩, _⟩⟩
    exact ⟨side⟩
  have hcomparison :=
    MState.conditionalSandwichedRenyiUpExtendedOrder_coherentMeasurementComparison
      hX hY psi.state.marginalAB alpha
  have hduality :=
    omega.conditionalSandwichedRenyiUpExtendedOrder_duality alpha beta hconj
  rw [hY.coherentGroupedKet_marginalAB psi,
    hY.coherentGroupedKet_marginalAC psi] at hduality
  linarith

end Ket

namespace MState

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
is exactly conditioning data processing on `C R → C`. -/
def entropicUncertaintyPurification (rho : MState ((a × b) × c)) :
    Ket
      ((a × b) × (c × ((a × b) × c))) :=
  (rho.canonicalPurification.reindex
      (Equiv.prodComm ((a × b) × c) ((a × b) × c))).reindex
    (Equiv.prodAssoc (a × b) c ((a × b) × c))

private theorem canonicalPurificationSwap_traceRight
    (rho : MState ((a × b) × c)) :
    (rho.canonicalPurification.reindex
      (Equiv.prodComm ((a × b) × c) ((a × b) × c))).state.traceRight =
      rho := by
  apply MState.ext
  ext i j
  have hp :
      Matrix.traceLeft rho.canonicalPurification.state.m = rho.m :=
    Ket.traceLeft_state_matrix_eq_of_purifies
      rho.canonicalPurification_purifies
  have hpij := congrFun (congrFun hp i) j
  simpa [Matrix.traceRight, Matrix.traceLeft,
    Ket.reindex_state] using hpij

private theorem traceRight_reindex_prodAssoc
    {d e f : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e] [Fintype f] [DecidableEq f]
    (tau : MState ((d × e) × f)) :
    (tau.reindex (Equiv.prodAssoc d e f)).traceRight =
      tau.traceRight.traceRight := by
  apply MState.ext
  ext i j
  simp [Matrix.traceRight,
    Fintype.sum_prod_type]

/-- The `AB` marginal of the regrouped canonical purification is the original
`rho_AB`. -/
theorem entropicUncertaintyPurification_marginalAB
    (rho : MState ((a × b) × c)) :
    (rho.entropicUncertaintyPurification).state.marginalAB = rho.marginalAB := by
  rw [entropicUncertaintyPurification, Ket.reindex_state,
    MState.marginalAB_eq_traceRight, traceRight_reindex_prodAssoc,
    canonicalPurificationSwap_traceRight]
  rfl

private theorem discardReference_marginalAC_reindex_prodAssoc
    {r : Type*} [Fintype r] [DecidableEq r]
    (tau : MState (((a × b) × c) × r)) :
    (((CPTPOp.id (dIn := a)).prod (CPTPOp.traceOutRight c r))
      ((tau.reindex (Equiv.prodAssoc (a × b) c r)).marginalAC)) =
      tau.traceRight.marginalAC := by
  apply MState.ext
  ext i j
  simp only [CPTPOp.mat_coe_eq_apply_mat, CPTPOp.prod_map]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  simp only [CPTPOp.traceOutRight, CPTPOp.map_ofMat, MatrixMap.traceRight_apply,
    Matrix.traceRight, MState.marginalAC_matrix, MState.reindex_matrix,
    MState.traceRight_m, Matrix.of_apply, Matrix.submatrix_apply]
  change
    (∑ ref : r, ∑ side : b,
      tau.m (((i.1, side), i.2), ref) (((j.1, side), j.2), ref)) =
      ∑ side : b, ∑ ref : r,
        tau.m (((i.1, side), i.2), ref) (((j.1, side), j.2), ref)
  rw [Finset.sum_comm]

/-- Discarding the canonical reference from the `A(CR)` marginal recovers
the original `AC` marginal. -/
theorem entropicUncertaintyPurification_marginalAC_discardReference
    (rho : MState ((a × b) × c)) :
    (((CPTPOp.id (dIn := a)).prod
        (CPTPOp.traceOutRight c ((a × b) × c)))
      rho.entropicUncertaintyPurification.state.marginalAC) = rho.marginalAC := by
  simp only [entropicUncertaintyPurification]
  rw [Ket.reindex_state, discardReference_marginalAC_reindex_prodAssoc,
    canonicalPurificationSwap_traceRight]

private theorem measureSubsystemState_discardRight
    {r : Type*} [Fintype r] [DecidableEq r]
    (M : POVM y a) (tau : MState (a × (c × r))) :
    (((CPTPOp.id (dIn := y)).prod (CPTPOp.traceOutRight c r))
      (measureSubsystemState M tau)) =
      measureSubsystemState M
        (((CPTPOp.id (dIn := a)).prod (CPTPOp.traceOutRight c r)) tau) := by
  apply MState.ext
  ext i j
  rcases i with ⟨iy, ic⟩
  rcases j with ⟨jy, jc⟩
  simp only [measureSubsystemState, CPTPOp.mat_coe_eq_apply_mat, CPTPOp.prod_map]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  rw [MatrixMap.kron_idChannel_apply_slice]
  simp only [CPTPOp.traceOutRight, CPTPOp.map_ofMat, MatrixMap.traceRight_apply]
  simp [Matrix.traceRight, MatrixMap.kron_idChannel_apply_slice,
    MatrixMap.kron_idChannel_left_apply_slice, -CPTPOp.id_map]
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
        simp only [Matrix.of_apply]
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
    (rho : MState ((a × b) × c)) :
    (((CPTPOp.id (dIn := y)).prod
        (CPTPOp.traceOutRight c ((a × b) × c)))
      (measureSubsystemState Y.toPOVM
        rho.entropicUncertaintyPurification.state.marginalAC)) =
      measureSubsystemState Y.toPOVM rho.marginalAC := by
  rw [measureSubsystemState_discardRight]
  rw [entropicUncertaintyPurification_marginalAC_discardReference]

set_option maxRecDepth 4000 in
/-- Tomamichel's tripartite entropic uncertainty relation for an arbitrary
normalized state.  The pure-state result is applied to the canonical
purification, after which conditioning data processing discards the
purifying reference. -/
theorem tripartiteEntropicUncertainty
    (rho : MState ((a × b) × c))
    (hX : X.IsRankOne) (hY : Y.IsRankOne)
    (alpha beta : RenyiOrder) (hconj : alpha.recip + beta.recip = 2) :
    -log2 (X.rankOneTraceOverlap Y) ≤
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

end MState
