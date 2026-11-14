/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

import Mathlib.Algebra.Order.CompleteField
public import QIT.Information.Renyi.ConditionalRenyiClassical
public import QIT.Information.Renyi.SandwichedRenyiOptimizedUSC
public import QIT.Information.Renyi.ConditionalSandwichedRenyiDuality
public import QIT.Information.Renyi.ConditionalSandwichedRenyiAdditivity
public import QIT.Measurements.Projective
public import QIT.OneShot.CQGuessing

/-!
# cq/block algebra

Responsibility layer of the sandwiched conditional Renyi classical-conditioning
source route.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Pointwise
open Matrix

namespace QIT

universe u v w

noncomputable section

variable {A : Type u} {B : Type v} {Y : Type w}
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable [Fintype Y] [DecidableEq Y]

namespace State

/-! ### Coordinate pinching of a classical register -/

/-- The coordinate projector selecting the `y`-block of `Y × D`. -/
def coordinateYProjector (y : Y) (D : Type*) [Fintype D] [DecidableEq D] :
    CMatrix (Y × D) :=
  Matrix.diagonal (fun x => if x.1 = y then (1 : ℂ) else 0)

/-- Coordinate dephasing in the classical `Y` basis. -/
def coordinateYDephase {D : Type*} [Fintype D] [DecidableEq D]
    (M : CMatrix (Y × D)) : CMatrix (Y × D) :=
  ∑ y, coordinateYProjector y D * M * coordinateYProjector y D

omit [Fintype Y] in
@[simp]
theorem coordinateYProjector_apply_same {D : Type*} [Fintype D] [DecidableEq D]
    (y : Y) (x : Y × D) :
    coordinateYProjector y D x x = if x.1 = y then (1 : ℂ) else 0 := by
  simp [coordinateYProjector]

omit [Fintype Y] in
@[simp]
theorem coordinateYProjector_apply_ne {D : Type*} [Fintype D] [DecidableEq D]
    (y : Y) {x x' : Y × D} (h : x ≠ x') :
    coordinateYProjector y D x x' = 0 := by
  simp [coordinateYProjector, h]

@[simp]
theorem coordinateYDephase_blockDiagonal {D : Type*} [Fintype D]
    [DecidableEq D] (blocks : Y → CMatrix D) :
    coordinateYDephase (Classical.blockDiagonal blocks) =
      Classical.blockDiagonal blocks := by
  ext x x'
  rcases x with ⟨y, d⟩
  rcases x' with ⟨y', d'⟩
  rw [coordinateYDephase, Matrix.sum_apply]
  by_cases hyy : y = y'
  · subst y'
    rw [Finset.sum_eq_single y]
    · simp [coordinateYProjector, Classical.blockDiagonal,
        Matrix.mul_apply, Matrix.diagonal]
    · intro z hz hzy
      have hyz : y ≠ z := Ne.symm hzy
      simp [coordinateYProjector, Classical.blockDiagonal,
        Matrix.mul_apply, Matrix.diagonal, hyz]
    · simp
  · have hblock :
        Classical.blockDiagonal blocks (y, d) (y', d') = 0 := by
      unfold Classical.blockDiagonal
      rw [Matrix.sum_apply]
      apply (Finset.sum_eq_zero (s := (Finset.univ : Finset Y)))
      intro z hz
      by_cases hzy : z = y
      · by_cases hzy' : z = y'
        · exact False.elim (hyy (hzy.symm.trans hzy'))
        · simp [hzy, hyy]
      · simp [hzy]
    rw [hblock]
    refine Finset.sum_eq_zero (s := (Finset.univ : Finset Y)) ?_
    intro z hz
    by_cases hyz : y = z
    · subst z
      have hy'y : y' ≠ y := Ne.symm hyy
      simp [coordinateYProjector, Classical.blockDiagonal,
        Matrix.mul_apply, Matrix.diagonal, hy'y]
    · simp [coordinateYProjector, Classical.blockDiagonal,
        Matrix.mul_apply, Matrix.diagonal, hyz]

/-- The `Y`-coordinate PVM on the internal order `A × (B × Y)`. -/
def coordinateYProjectiveMeasurement :
    ProjectiveMeasurement Y (A × (B × Y)) where
  effects := fun y =>
    Matrix.diagonal (fun x => if x.2.2 = y then (1 : ℂ) else 0)
  isHermitian := by
    intro y
    rw [Matrix.IsHermitian]
    ext x x'
    by_cases hxx : x = x'
    · subst x'
      simp [Matrix.diagonal]
    · have hxx' : x' ≠ x := Ne.symm hxx
      simp [Matrix.diagonal, hxx, hxx']
  idempotent := by
    intro y
    ext x x'
    by_cases hxx : x = x'
    · subst x'
      simp [Matrix.mul_apply, Matrix.diagonal]
    · simp [Matrix.mul_apply, Matrix.diagonal, hxx]
  orthogonal := by
    intro y y' hyy
    ext x x'
    by_cases hxx : x = x'
    · subst x'
      by_cases hxy : x.2.2 = y
      · have hxy' : x.2.2 ≠ y' := by
          intro hx
          exact hyy (hxy.symm.trans hx)
        have hyy' : y ≠ y' := hyy
        simp [Matrix.mul_apply, Matrix.diagonal, hxy, hyy']
      · simp [Matrix.mul_apply, Matrix.diagonal, hxy]
    · simp [Matrix.mul_apply, Matrix.diagonal, hxx]
  sum_eq_one := by
    ext x x'
    by_cases hxx : x = x'
    · subst x'
      simp [Matrix.sum_apply, Matrix.diagonal]
    · simp [Matrix.sum_apply, Matrix.diagonal, hxx]

theorem coordinateYProjectiveMeasurement_apply_cq
    (E : Ensemble Y (A × B)) :
    (coordinateYProjectiveMeasurement (A := A) (B := B) (Y := Y)).pinchingChannel.applyState
        (State.cqConditioningState E) = State.cqConditioningState E := by
  apply State.ext
  rw [ProjectiveMeasurement.pinchingChannel_applyState_matrix,
    conditionalRenyiState_eq_rightBlockDiagonal E]
  ext x x'
  rcases x with ⟨a, b, y⟩
  rcases x' with ⟨a', b', y'⟩
  by_cases hyy : y = y'
  · subst y'
    simp [coordinateYProjectiveMeasurement, conditionalRenyiRightBlockDiagonal,
      Matrix.mul_apply, Matrix.diagonal, Matrix.sum_apply]
  · have hblock :
    Classical.blockDiagonal (conditionalRenyiBlock E)
            (y, (a, b)) (y', (a', b')) = 0 := by
      have hoff := Classical.blockDiagonal_block_ne
        (conditionalRenyiBlock E) hyy
      have hoff' := congrArg (fun M => M (a, b) (a', b')) hoff
      simpa [Classical.block] using hoff'
    simp [coordinateYProjectiveMeasurement, conditionalRenyiRightBlockDiagonal,
      Matrix.mul_apply, Matrix.diagonal, Matrix.sum_apply, hblock]

/-! The same coordinate measurement on the public `B × Y` reference system.

This is kept local to the source route so that the tensor identity used by the
reference is visible in the pinching proof. -/

def coordinateYProjectiveMeasurementRight :
    ProjectiveMeasurement Y (B × Y) where
  effects := fun y =>
    Matrix.diagonal (fun x => if x.2 = y then (1 : ℂ) else 0)
  isHermitian := by
    intro y
    rw [Matrix.IsHermitian]
    ext x x'
    by_cases hxx : x = x'
    · subst x'
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hxx, Ne.symm hxx]
  idempotent := by
    intro y
    ext x x'
    by_cases hxx : x = x'
    · subst x'
      simp [Matrix.mul_apply, Matrix.diagonal]
    · simp [Matrix.mul_apply, Matrix.diagonal, hxx]
  orthogonal := by
    intro y y' hyy
    ext x x'
    by_cases hxx : x = x'
    · subst x'
      by_cases hxy : x.2 = y
      · have hxy' : x.2 ≠ y' := by
          intro hx
          exact hyy (hxy.symm.trans hx)
        simp [Matrix.mul_apply, Matrix.diagonal, hxy, hyy]
      · simp [Matrix.mul_apply, Matrix.diagonal, hxy]
    · simp [Matrix.mul_apply, Matrix.diagonal, hxx]
  sum_eq_one := by
    ext x x'
    by_cases hxx : x = x'
    · subst x'
      simp [Matrix.sum_apply, Matrix.diagonal]
    · simp [Matrix.sum_apply, Matrix.diagonal, hxx]

def coordinateYPinchedState (σ : State (B × Y)) : State (B × Y) :=
  (coordinateYProjectiveMeasurementRight (B := B) (Y := Y)).pinchingChannel.applyState σ

private theorem coordinateYPinchedState_maximallyMixed_fixed
    [Nonempty (B × Y)] :
    coordinateYPinchedState (State.maximallyMixed (B × Y)) =
      State.maximallyMixed (B × Y) := by
  apply State.ext
  change (coordinateYProjectiveMeasurementRight (B := B) (Y := Y)).pinchingMap
      (State.maximallyMixed (B × Y)).matrix = _
  rw [State.maximallyMixed_matrix]
  apply ProjectiveMeasurement.pinchingMap_eq_self_of_commute
  intro outcome
  simp

theorem coordinateYPinchedState_regularized_maximallyMixed_fixed
    [Nonempty (B × Y)]
    (σ : State (B × Y)) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    coordinateYPinchedState
        (fullRankApproxState (coordinateYPinchedState σ)
          (State.maximallyMixed (B × Y)) δ hδ0 hδ1) =
      fullRankApproxState (coordinateYPinchedState σ)
        (State.maximallyMixed (B × Y)) δ hδ0 hδ1 := by
  apply State.ext
  change (coordinateYProjectiveMeasurementRight (B := B) (Y := Y)).pinchingMap
      (fullRankApproxState (coordinateYPinchedState σ)
        (State.maximallyMixed (B × Y)) δ hδ0 hδ1).matrix = _
  rw [fullRankApproxState_matrix]
  unfold fullRankApproxMatrix regularizedStateMatrix
  rw [map_add, map_smul, map_smul]
  have hσ : (coordinateYPinchedState σ).matrix =
      (coordinateYProjectiveMeasurementRight (B := B) (Y := Y)).pinchingMap σ.matrix := by
    rfl
  have hμ : (State.maximallyMixed (B × Y)).matrix =
      (coordinateYProjectiveMeasurementRight (B := B) (Y := Y)).pinchingMap
        (State.maximallyMixed (B × Y)).matrix := by
    exact (congrArg State.matrix coordinateYPinchedState_maximallyMixed_fixed).symm
  rw [hσ, ← hμ]
  rw [ProjectiveMeasurement.pinchingMap_idempotent]

theorem coordinateYPinchedState_fixed (σ : State (B × Y)) :
    coordinateYPinchedState (coordinateYPinchedState σ) =
      coordinateYPinchedState σ := by
  apply State.ext
  change (coordinateYProjectiveMeasurementRight (B := B) (Y := Y)).pinchingMap
      ((coordinateYProjectiveMeasurementRight (B := B) (Y := Y)).pinchingMap σ.matrix) =
        (coordinateYProjectiveMeasurementRight (B := B) (Y := Y)).pinchingMap σ.matrix
  rw [ProjectiveMeasurement.pinchingMap_idempotent]

/-- The source-coordinate ensemble of a reference after reindexing its
classical coordinate to the first position.  This is the reference-side
counterpart of the public input ensemble `E : Ensemble Y (A × B)`. -/
def coordinateYPinchedEnsemble [Nonempty B] (σ : State (B × Y)) : Ensemble Y B :=
  (σ.reindex (Equiv.prodComm B Y)).sourceCoordinatePinchEnsemble

theorem coordinateYPinchedEnsemble_cqState_reindex [Nonempty B]
    (σ : State (B × Y)) :
    (coordinateYPinchedEnsemble (B := B) (Y := Y) σ).cqState.reindex
        (Equiv.prodComm Y B) = coordinateYPinchedState σ := by
  classical
  apply State.ext
  rw [State.reindex_matrix, coordinateYPinchedState,
    ProjectiveMeasurement.pinchingChannel_applyState_matrix]
  have hsource := sourceCoordinatePinchEnsemble_cqState_toSubnormalized
    (ρ := σ.reindex (Equiv.prodComm B Y))
  have hsource_matrix := congrArg SubnormalizedState.matrix hsource
  rw [State.toSubnormalized_matrix,
    SubnormalizedState.sourceCoordinatePinch_matrix_eq_blockDiagonal] at hsource_matrix
  rw [Classical.cqState_eq_blockDiagonal] at hsource_matrix
  have hcq :
      (coordinateYPinchedEnsemble (B := B) (Y := Y) σ).cqState.matrix =
        Classical.blockDiagonal (fun x =>
          ((coordinateYPinchedEnsemble (B := B) (Y := Y) σ).probs x : ℂ) •
            ((coordinateYPinchedEnsemble (B := B) (Y := Y) σ).states x).matrix) := by
    exact Classical.cqState_eq_blockDiagonal
      (coordinateYPinchedEnsemble (B := B) (Y := Y) σ)
  rw [hcq]
  ext ⟨b, y⟩ ⟨b', y'⟩
  by_cases hyy : y = y'
  · subst y'
    change Classical.block (Classical.blockDiagonal (fun x =>
      ((coordinateYPinchedEnsemble (B := B) (Y := Y) σ).probs x : ℂ) •
        ((coordinateYPinchedEnsemble (B := B) (Y := Y) σ).states x).matrix))
        y y b b' = _
    rw [Classical.blockDiagonal_block_self]
    have hblock := congrFun (congrFun hsource_matrix (y, b)) (y, b')
    simp [Classical.blockDiagonal, Matrix.sum_apply, Matrix.single_apply,
      State.toSubnormalized_matrix] at hblock
    have hpinch :
        Classical.block (σ.reindex (Equiv.prodComm B Y)).matrix y y b b' =
          (∑ c, (coordinateYProjectiveMeasurementRight (B := B) (Y := Y)).effects c *
            σ.matrix * (coordinateYProjectiveMeasurementRight (B := B) (Y := Y)).effects c)
            (b, y) (b', y) := by
      change σ.matrix (b, y) (b', y) = _
      rw [Matrix.sum_apply]
      show σ.matrix (b, y) (b', y) =
        ∑ c, ((coordinateYProjectiveMeasurementRight (B := B) (Y := Y)).effects c *
          σ.matrix * (coordinateYProjectiveMeasurementRight (B := B) (Y := Y)).effects c)
          (b, y) (b', y)
      rw [Finset.sum_eq_single y]
      · simp [coordinateYProjectiveMeasurementRight, Matrix.mul_apply,
          Matrix.diagonal]
      · intro c hc hcy
        have hyc : y ≠ c := Ne.symm hcy
        simp [coordinateYProjectiveMeasurementRight, Matrix.mul_apply,
          Matrix.diagonal, hyc]
      · simp
    simpa [coordinateYPinchedEnsemble, State.reindex_matrix,
      Matrix.submatrix] using hblock.trans hpinch
  · change Classical.block (Classical.blockDiagonal (fun x =>
      ((coordinateYPinchedEnsemble (B := B) (Y := Y) σ).probs x : ℂ) •
        ((coordinateYPinchedEnsemble (B := B) (Y := Y) σ).states x).matrix))
        y y' b b' = _
    rw [Classical.blockDiagonal_block_ne _ hyy]
    change (0 : ℂ) = _
    symm
    rw [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro c hc
    simp [coordinateYProjectiveMeasurementRight, Matrix.mul_apply,
      Matrix.diagonal]
    intro hy' hy
    exact (hyy (hy.trans hy'.symm)).elim

theorem coordinateYPinchedFullRankPath_posDef
    [Nonempty B] (σ : State (B × Y)) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ((coordinateYPinchedEnsemble (B := B) (Y := Y)
      (fullRankApproxMaximallyMixedStatePath
        (coordinateYPinchedState σ) δ)).cqState.reindex
          (Equiv.prodComm Y B)).matrix.PosDef := by
  letI : Nonempty Y := by
    rcases σ.nonempty with ⟨⟨b, y⟩⟩
    exact ⟨y⟩
  rw [coordinateYPinchedEnsemble_cqState_reindex]
  rw [fullRankApproxMaximallyMixedStatePath, fullRankApproxStatePath,
    dif_pos hδ]
  rw [coordinateYPinchedState_regularized_maximallyMixed_fixed]
  exact fullRankApproxState_posDef_of_noise
    (coordinateYPinchedState σ) (State.maximallyMixed (B × Y))
    State.maximallyMixed_posDef hδ.1.le hδ.2.le hδ.1

theorem identityTensorStateMatrix_coordinateYPinching
    (σ : State (B × Y)) :
    (coordinateYProjectiveMeasurement (A := A) (B := B) (Y := Y)).pinchingChannel.map
        (identityTensorStateMatrix (a := A) σ) =
      identityTensorStateMatrix (a := A)
        (coordinateYPinchedState σ) := by
  rw [ProjectiveMeasurement.pinchingChannel_map]
  rw [coordinateYPinchedState]
  change _ = Matrix.kronecker (1 : CMatrix A)
    (((coordinateYProjectiveMeasurementRight (B := B) (Y := Y)).pinchingChannel).applyState σ).matrix
  rw [ProjectiveMeasurement.pinchingChannel_applyState_matrix]
  ext ⟨a, b, y⟩ ⟨a', b', y'⟩
  by_cases haa : a = a'
  · subst a'
    by_cases hyy : y = y'
    · subst y'
      simp [coordinateYProjectiveMeasurement,
        coordinateYProjectiveMeasurementRight, identityTensorStateMatrix,
        Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.mul_apply,
        Matrix.diagonal, Matrix.sum_apply]
    · simp [coordinateYProjectiveMeasurement,
        coordinateYProjectiveMeasurementRight, identityTensorStateMatrix,
        Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.mul_apply,
        Matrix.diagonal, Matrix.sum_apply, hyy]
  · simp [coordinateYProjectiveMeasurement,
      coordinateYProjectiveMeasurementRight, identityTensorStateMatrix,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.mul_apply,
      Matrix.diagonal, Matrix.sum_apply, haa]

theorem conditionalSandwichedRenyiUp_candidate_le_of_coordinateYPinching
    (E : Ensemble Y (A × B)) (σ : State (B × Y)) (α : ℝ)
    (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) :
    -sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ) α ≤
      -sandwichedRenyiPSDReferenceE
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A)
          (coordinateYPinchedState σ))
        (identityTensorStateMatrix_posSemidef_of_state (a := A)
          (coordinateYPinchedState σ)) α := by
  have hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α := by
    rcases lt_or_gt_of_ne hα_ne_one with hlt | hgt
    · exact Or.inl ⟨hα, hlt⟩
    · exact Or.inr hgt
  let P := coordinateYProjectiveMeasurement (A := A) (B := B) (Y := Y)
  let Φ : Channel (A × (B × Y)) (A × (B × Y)) := P.pinchingChannel
  have hρfix : Φ.applyState (State.cqConditioningState E) =
      State.cqConditioningState E := by
    exact coordinateYProjectiveMeasurement_apply_cq E
  have hσmap : Φ.map (identityTensorStateMatrix (a := A) σ) =
      identityTensorStateMatrix (a := A)
        (coordinateYPinchedState σ) := by
    exact identityTensorStateMatrix_coordinateYPinching σ
  have hDPI :=
    sandwichedRenyiPSDReferenceE_dataProcessing_channel_ge_of_half_le_lt_one_or_one_lt
      (State.cqConditioningState E)
      (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
      Φ α hα_range
  have hDPI' :
      sandwichedRenyiPSDReferenceE
          (State.cqConditioningState E)
          (identityTensorStateMatrix (a := A) σ)
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σ) α ≥
        sandwichedRenyiPSDReferenceE
          (State.cqConditioningState E)
          (identityTensorStateMatrix (a := A) (coordinateYPinchedState σ))
          (identityTensorStateMatrix_posSemidef_of_state (a := A)
            (coordinateYPinchedState σ)) α := by
    simpa only [hρfix, hσmap] using hDPI
  exact EReal.neg_le_neg_iff.mpr hDPI'

/-! ### The source `Q` decomposition -/

/-! The reference used by the down-arrow has the same right-block structure as
the cq input.  We keep the proof entrywise so that a zero probability is
handled as a zero block before any power or logarithm is introduced. -/

theorem sandwiched_conditionalReference_blockDiagonal
    (E : Ensemble Y (A × B)) :
    identityTensorStateMatrix (a := A) (State.cqConditioningState E).marginalB =
      conditionalRenyiRightBlockDiagonal (fun y =>
        (E.probs y : ℂ) • identityTensorStateMatrix (a := A)
          (E.states y).marginalB) := by
  rw [Ensemble.conditionalRenyiState_marginalB_eq_conditionalMarginalBYState]
  ext ⟨a, b, y⟩ ⟨a', b', y'⟩
  by_cases hyy : y = y'
  · subst y'
    simp [conditionalRenyiRightBlockDiagonal, identityTensorStateMatrix,
      Ensemble.conditionalMarginalBYState, Ensemble.conditionalMarginalB,
      Ensemble.cqState_matrix, State.reindex_matrix, Matrix.kronecker,
      Matrix.kroneckerMap_apply, State.classicalConditioningEquiv_symm_apply,
      partialTraceA, Matrix.sum_apply]
    simp only [Matrix.one_apply]
    rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y)]
    · conv_rhs =>
        unfold Classical.blockDiagonal
        rw [Matrix.sum_apply]
        rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y) (by
          intro z _ hzy
          simp [hzy])]
      simp [Matrix.kronecker,
        Matrix.kroneckerMap_apply, partialTraceA]
      by_cases haa : a = a'
      · subst a'
        rw [NNReal.smul_def]
        simp [Complex.real_smul]
      · simp [haa]
    · intro z _ hzy
      simp [hzy]
  · have hxy : ∀ x : Y, ¬(x = y ∧ x = y') := by
      intro x h
      exact hyy (h.1.symm.trans h.2)
    simp [conditionalRenyiRightBlockDiagonal, identityTensorStateMatrix,
      Ensemble.conditionalMarginalBYState, Ensemble.conditionalMarginalB,
      Ensemble.cqState_matrix, State.reindex_matrix,
      Matrix.kronecker, Matrix.kroneckerMap_apply,
      State.classicalConditioningEquiv_symm_apply, partialTraceA,
      Matrix.sum_apply, Classical.blockDiagonal, hxy]

omit [Fintype A] in
theorem sandwiched_reference_cq_blockDiagonal
    (F : Ensemble Y B) :
    identityTensorStateMatrix (a := A)
        (F.cqState.reindex (Equiv.prodComm Y B)) =
      conditionalRenyiRightBlockDiagonal (fun y =>
        (F.probs y : ℂ) • identityTensorStateMatrix (a := A) (F.states y)) := by
  ext ⟨a, b, y⟩ ⟨a', b', y'⟩
  by_cases haa : a = a'
  · subst a'
    by_cases hyy : y = y'
    · subst y'
      simp [conditionalRenyiRightBlockDiagonal, identityTensorStateMatrix,
        Ensemble.cqState_matrix, State.reindex_matrix, Matrix.kronecker,
        Matrix.kroneckerMap_apply, Matrix.sum_apply,
        Classical.blockDiagonal, Matrix.single_apply]
      rw [NNReal.smul_def]
      simp
    · simp [conditionalRenyiRightBlockDiagonal, identityTensorStateMatrix,
        Ensemble.cqState_matrix, State.reindex_matrix, Matrix.kronecker,
        Matrix.kroneckerMap_apply, Matrix.sum_apply,
        Classical.blockDiagonal, Matrix.single_apply]
      apply Finset.sum_congr rfl
      intro x hx
      simp [NNReal.smul_def]
  · simp [conditionalRenyiRightBlockDiagonal, identityTensorStateMatrix,
      Ensemble.cqState_matrix, State.reindex_matrix, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.sum_apply,
      Classical.blockDiagonal, Matrix.single_apply, haa]

/-! A positive-definite cq reference has positive-definite weighted blocks.
This is the finite-dimensional principal-submatrix fact needed before the
source full-rank candidate can be applied branch by branch. -/

theorem classical_blockDiagonal_posDef
    {ι D : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype D] [DecidableEq D]
    (blocks : ι → CMatrix D) (hblocks : ∀ i, (blocks i).PosDef) :
    (Classical.blockDiagonal blocks).PosDef := by
  let d : ι → D → ℝ := fun i => (hblocks i).isHermitian.eigenvalues
  let U : ι → Matrix.unitaryGroup D ℂ :=
    fun i => (hblocks i).isHermitian.eigenvectorUnitary
  let Ubig : Matrix.unitaryGroup (ι × D) ℂ :=
    ⟨Classical.blockDiagonal (fun i => (U i : CMatrix D)), by
      rw [Matrix.mem_unitaryGroup_iff]
      simp only [star_eq_conjTranspose]
      rw [Classical.blockDiagonal_conjTranspose,
        Classical.blockDiagonal_mul]
      rw [show (1 : CMatrix (ι × D)) =
          Matrix.kronecker (1 : CMatrix ι) (1 : CMatrix D) by simp]
      rw [Classical.identityTensor_eq_blockDiagonal (ι := ι) (a := D)
        (1 : CMatrix D)]
      apply congrArg Classical.blockDiagonal
      funext i
      exact Matrix.mem_unitaryGroup_iff.mp (U i).2⟩
  let diagonalBlocks : ι → CMatrix D := fun i =>
    Matrix.diagonal (fun j => (d i j : ℂ))
  have hspec : Classical.blockDiagonal blocks =
      (Ubig : CMatrix (ι × D)) *
        Classical.blockDiagonal diagonalBlocks *
        star (Ubig : CMatrix (ι × D)) := by
    have hi : ∀ i, blocks i =
        (U i : CMatrix D) * diagonalBlocks i * star (U i : CMatrix D) := by
      intro i
      simpa [d, U, diagonalBlocks, Unitary.conjStarAlgAut_apply,
        Matrix.mul_assoc] using (hblocks i).isHermitian.spectral_theorem
    change Classical.blockDiagonal blocks =
      (Classical.blockDiagonal (fun i => (U i : CMatrix D))) *
        Classical.blockDiagonal diagonalBlocks *
        star (Classical.blockDiagonal (fun i => (U i : CMatrix D)))
    rw [show star (Classical.blockDiagonal (fun i => (U i : CMatrix D))) =
        Classical.blockDiagonal (fun i => star (U i : CMatrix D)) by
      exact Classical.blockDiagonal_conjTranspose _]
    rw [Classical.blockDiagonal_mul, Classical.blockDiagonal_mul]
    apply congrArg Classical.blockDiagonal
    funext i
    simp [diagonalBlocks, hi i]
  have hdiag : (Classical.blockDiagonal diagonalBlocks).PosDef := by
    have hdiag' : (Matrix.diagonal (fun p : ι × D =>
        (d p.1 p.2 : ℂ))).PosDef :=
      Matrix.PosDef.diagonal (fun p => by
        change (0 : ℂ) < (d p.1 p.2 : ℂ)
        exact_mod_cast (hblocks p.1).eigenvalues_pos p.2)
    have hdiag_eq : Classical.blockDiagonal diagonalBlocks =
        Matrix.diagonal (fun p : ι × D => (d p.1 p.2 : ℂ)) := by
      ext ⟨i, j⟩ ⟨i', j'⟩
      by_cases hii : i = i'
      · subst i'
        change Classical.block (Classical.blockDiagonal diagonalBlocks)
            i i j j' = _
        rw [Classical.blockDiagonal_block_self]
        simp [diagonalBlocks, Matrix.diagonal]
      · change Classical.block (Classical.blockDiagonal diagonalBlocks)
          i i' j j' = _
        rw [Classical.blockDiagonal_block_ne diagonalBlocks hii]
        simp [Matrix.diagonal, hii]
    rw [hdiag_eq]
    exact hdiag'
  rw [hspec]
  rw [Matrix.IsUnit.posDef_star_right_conjugate_iff
    (Unitary.isUnit_coe : IsUnit (Ubig : CMatrix (ι × D)))]
  exact hdiag

theorem sandwiched_reference_cq_block_posDef
    (F : Ensemble Y B)
    (hF : (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef)
    (y : Y) :
    ((F.probs y : ℂ) • (F.states y).matrix).PosDef := by
  have hinj : Function.Injective (fun b : B => (b, y)) := by
    intro b b' h
    exact congrArg Prod.fst h
  have hsub := hF.submatrix hinj
  simpa [State.reindex_matrix, State.reindex, Ensemble.cqState_matrix,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.submatrix,
    Fintype.sum_prod_type, Matrix.sum_apply, Matrix.single_apply,
        smul_eq_mul] using hsub

theorem sandwiched_reference_cq_posDef_of_positive
    (F : Ensemble Y B) (hprob : ∀ y, 0 < F.probs y)
    (hstate : ∀ y, (F.states y).matrix.PosDef) :
    (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef := by
  have hblocks : ∀ y,
      ((F.probs y : ℂ) • (F.states y).matrix).PosDef := by
    intro y
    exact (hstate y).smul (by exact_mod_cast hprob y)
  have hbd := classical_blockDiagonal_posDef
    (fun y => (F.probs y : ℂ) • (F.states y).matrix) hblocks
  have hcq : F.cqState.matrix.PosDef := by
    rw [Classical.cqState_eq_blockDiagonal]
    exact hbd
  exact State.reindex_posDef_of_posDef F.cqState hcq (Equiv.prodComm Y B)

theorem sandwiched_reference_cq_prob_pos
    (F : Ensemble Y B)
    (hF : (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef)
    (y : Y) :
    0 < F.probs y := by
  letI : Nonempty B := (F.states y).nonempty
  have hblock := sandwiched_reference_cq_block_posDef F hF y
  have htrace := Matrix.PosDef.trace_pos hblock
  have htrace_re : 0 < (((F.probs y : ℂ) • (F.states y).matrix).trace).re := by
    exact (Complex.pos_iff.mp htrace).1
  have hstate_trace : ((F.states y).matrix.trace).re = 1 := by
    rw [(F.states y).trace_eq_one]
    norm_num
  have htrace_re' : 0 < (F.probs y : ℝ) * 1 := by
    simpa [Matrix.trace_smul, Complex.real_smul, hstate_trace] using htrace_re
  exact_mod_cast (by simpa using htrace_re' : 0 < (F.probs y : ℝ))

theorem sandwiched_reference_cq_state_posDef
    (F : Ensemble Y B)
    (hF : (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef)
    (y : Y) :
    (F.states y).matrix.PosDef := by
  letI : Nonempty B := (F.states y).nonempty
  have hqNN : 0 < F.probs y := sandwiched_reference_cq_prob_pos F hF y
  have hq : 0 < (F.probs y : ℝ) := by exact_mod_cast hqNN
  have hblock := sandwiched_reference_cq_block_posDef F hF y
  have hqC : 0 < (F.probs y : ℂ) := by exact_mod_cast hq
  have hinv : 0 < ((F.probs y : ℂ)⁻¹) := inv_pos.mpr hqC
  have hscaled := hblock.smul hinv
  change (((F.probs y : ℂ)⁻¹) •
    ((F.probs y : ℂ) • (F.states y).matrix)).PosDef at hscaled
  simpa only [smul_smul, inv_mul_cancel₀ hqC.ne', one_smul] using hscaled

/-- The sandwich exponent used by the matrix-level sandwiched `Q` functional. -/
def sandwichedConditioningExponent (α : ℝ) : ℝ :=
  (1 - α) / (2 * α)

theorem sandwichedConditioningExponent_nonneg {α : ℝ}
    (hα_pos : 0 < α) (hα_lt_one : α ≤ 1) :
    0 ≤ sandwichedConditioningExponent α := by
  unfold sandwichedConditioningExponent
  exact div_nonneg (sub_nonneg.mpr hα_lt_one)
    (mul_nonneg (by norm_num) (le_of_lt hα_pos))

private theorem matrixBlockDiagonal_rpow
    (blocks : Y → CMatrix (A × B))
    (hblocks : ∀ y, (blocks y).PosSemidef) (s : ℝ) :
    CFC.rpow (Matrix.blockDiagonal blocks) s =
      Matrix.blockDiagonal (fun y => CFC.rpow (blocks y) s) := by
  classical
  let U : Y → Matrix.unitaryGroup (A × B) ℂ := fun y =>
    (hblocks y).isHermitian.eigenvectorUnitary
  let d : Y → (A × B) → ℝ := fun y =>
    (hblocks y).isHermitian.eigenvalues
  have hd : ∀ y i, 0 ≤ d y i := by
    intro y i
    exact (hblocks y).eigenvalues_nonneg i
  have hspec : ∀ y, blocks y =
      (U y : CMatrix (A × B)) *
          Matrix.diagonal (fun i => (d y i : ℂ)) *
        star (U y : CMatrix (A × B)) := by
    intro y
    simpa [U, d, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using
      (hblocks y).isHermitian.spectral_theorem
  let Ubig : Matrix.unitaryGroup ((A × B) × Y) ℂ :=
    ⟨Matrix.blockDiagonal (fun y => (U y : CMatrix (A × B))), by
      rw [Matrix.mem_unitaryGroup_iff']
      change Matrix.conjTranspose (Matrix.blockDiagonal
        (fun y => (U y : CMatrix (A × B)))) *
          Matrix.blockDiagonal (fun y => (U y : CMatrix (A × B))) = 1
      rw [Matrix.blockDiagonal_conjTranspose]
      rw [← Matrix.blockDiagonal_mul
        (fun y => Matrix.conjTranspose (U y : CMatrix (A × B)))
        (fun y => (U y : CMatrix (A × B)))]
      have hpoint : (fun y => Matrix.conjTranspose (U y : CMatrix (A × B)) *
          (U y : CMatrix (A × B))) =
          (1 : Y → CMatrix (A × B)) := by
        funext y
        simpa [Matrix.star_eq_conjTranspose] using
          (Unitary.coe_star_mul_self (U y))
      rw [hpoint, Matrix.blockDiagonal_one]⟩
  let dBig : ((A × B) × Y) → ℝ := fun iy => d iy.2 iy.1
  have hD :
      Matrix.blockDiagonal (fun y =>
          Matrix.diagonal (fun i => (d y i : ℂ))) =
        Matrix.diagonal (fun iy => (dBig iy : ℂ)) := by
    simp [dBig]
  have hconj :
      Matrix.blockDiagonal blocks =
        (Ubig : CMatrix ((A × B) × Y)) *
            Matrix.diagonal (fun iy => (dBig iy : ℂ)) *
          star (Ubig : CMatrix ((A × B) × Y)) := by
    calc
      Matrix.blockDiagonal blocks = Matrix.blockDiagonal (fun y =>
          (U y : CMatrix (A × B)) *
              Matrix.diagonal (fun i => (d y i : ℂ)) *
            star (U y : CMatrix (A × B))) := by
          congr 1
          funext y
          exact hspec y
      _ = Matrix.blockDiagonal (fun y => (U y : CMatrix (A × B))) *
          Matrix.blockDiagonal (fun y =>
            Matrix.diagonal (fun i => (d y i : ℂ))) *
          star (Matrix.blockDiagonal (fun y => (U y : CMatrix (A × B)))) := by
            rw [show star (Matrix.blockDiagonal (fun y =>
              (U y : CMatrix (A × B)))) =
                Matrix.blockDiagonal (fun y => star (U y : CMatrix (A × B))) by
              change Matrix.conjTranspose (Matrix.blockDiagonal
                (fun y => (U y : CMatrix (A × B)))) = _
              exact Matrix.blockDiagonal_conjTranspose _]
            rw [← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]
      _ = (Ubig : CMatrix ((A × B) × Y)) *
            Matrix.diagonal (fun iy => (dBig iy : ℂ)) *
          star (Ubig : CMatrix ((A × B) × Y)) := by
            rw [hD]
  have hpow : ∀ y, CFC.rpow (blocks y) s =
      (U y : CMatrix (A × B)) *
          Matrix.diagonal (fun i => (((d y i) ^ s : ℝ) : ℂ)) *
        star (U y : CMatrix (A × B)) := by
    intro y
    rw [hspec y]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal
      (U y) (d y) (hd y) s
  have hDpow :
      Matrix.blockDiagonal (fun y =>
          Matrix.diagonal (fun i => (((d y i) ^ s : ℝ) : ℂ))) =
        Matrix.diagonal (fun iy => (((dBig iy) ^ s : ℝ) : ℂ)) := by
    simp [dBig]
  have hconjpow :
      Matrix.blockDiagonal (fun y => CFC.rpow (blocks y) s) =
        (Ubig : CMatrix ((A × B) × Y)) *
            Matrix.diagonal (fun iy => (((dBig iy) ^ s : ℝ) : ℂ)) *
          star (Ubig : CMatrix ((A × B) × Y)) := by
    calc
      Matrix.blockDiagonal (fun y => CFC.rpow (blocks y) s) =
          Matrix.blockDiagonal (fun y =>
            (U y : CMatrix (A × B)) *
                Matrix.diagonal (fun i => (((d y i) ^ s : ℝ) : ℂ)) *
              star (U y : CMatrix (A × B))) := by
            congr 1
            funext y
            exact hpow y
      _ = Matrix.blockDiagonal (fun y => (U y : CMatrix (A × B))) *
          Matrix.blockDiagonal (fun y =>
            Matrix.diagonal (fun i => (((d y i) ^ s : ℝ) : ℂ))) *
          star (Matrix.blockDiagonal (fun y => (U y : CMatrix (A × B)))) := by
            rw [show star (Matrix.blockDiagonal (fun y =>
              (U y : CMatrix (A × B)))) =
                Matrix.blockDiagonal (fun y => star (U y : CMatrix (A × B))) by
              change Matrix.conjTranspose (Matrix.blockDiagonal
                (fun y => (U y : CMatrix (A × B)))) = _
              exact Matrix.blockDiagonal_conjTranspose _]
            rw [← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]
      _ = (Ubig : CMatrix ((A × B) × Y)) *
            Matrix.diagonal (fun iy => (((dBig iy) ^ s : ℝ) : ℂ)) *
          star (Ubig : CMatrix ((A × B) × Y)) := by
            rw [hDpow]
  rw [hconj]
  exact (cMatrix_rpow_unitary_conj_diagonal_ofReal Ubig dBig
    (fun iy => hd iy.2 iy.1) s).trans hconjpow.symm

private theorem matrixBlockDiagonal_rpow_nonneg
    (blocks : Y → CMatrix (A × B))
    (hblocks : ∀ y, (blocks y).PosSemidef) {s : ℝ} (_hs : 0 ≤ s) :
    CFC.rpow (Matrix.blockDiagonal blocks) s =
      Matrix.blockDiagonal (fun y => CFC.rpow (blocks y) s) :=
  matrixBlockDiagonal_rpow blocks hblocks s

private theorem conditionalRightBlockDiagonal_rpow_nonneg
    (blocks : Y → CMatrix (A × B))
    (hblocks : ∀ y, (blocks y).PosSemidef) {s : ℝ} (hs : 0 ≤ s) :
    CFC.rpow (conditionalRenyiRightBlockDiagonal blocks) s =
      conditionalRenyiRightBlockDiagonal (fun y => CFC.rpow (blocks y) s) := by
  let e : (A × B) × Y ≃ Y × (A × B) := Equiv.prodComm (A × B) Y
  have hblock :
      (Matrix.blockDiagonal blocks).submatrix e.symm e.symm =
        Classical.blockDiagonal blocks := by
    simpa [e] using conditionalRenyi_blockDiagonal_reindex blocks
  have hmath_pos : (Matrix.blockDiagonal blocks).PosSemidef := by
    have hclassical := Classical.blockDiagonal_posSemidef blocks hblocks
    have hreindexed := hclassical.submatrix e
    simpa only [← hblock] using hreindexed
  have hclassical_rpow :
      CFC.rpow (Classical.blockDiagonal blocks) s =
        Classical.blockDiagonal (fun y => CFC.rpow (blocks y) s) := by
    calc
      CFC.rpow (Classical.blockDiagonal blocks) s =
          CFC.rpow ((Matrix.blockDiagonal blocks).submatrix e.symm e.symm) s := by
            rw [hblock]
      _ = (CFC.rpow (Matrix.blockDiagonal blocks) s).submatrix e.symm e.symm :=
        conditionalRenyi_rpow_reindex_nonneg
          (Matrix.blockDiagonal blocks) hmath_pos e.symm hs
      _ = (Matrix.blockDiagonal (fun y => CFC.rpow (blocks y) s)).submatrix
          e.symm e.symm := by
            rw [matrixBlockDiagonal_rpow_nonneg blocks hblocks hs]
      _ = Classical.blockDiagonal (fun y => CFC.rpow (blocks y) s) :=
        conditionalRenyi_blockDiagonal_reindex
          (fun y => CFC.rpow (blocks y) s)
  rw [conditionalRenyiRightBlockDiagonal_rpow_reindex_nonneg
    blocks hblocks hs, hclassical_rpow]
  rfl

theorem sandwichedRenyiQ_fixedReference_blockDiagonal_lowAlpha
    (rho sigma : Y → CMatrix (A × B))
    (hrho : ∀ y, (rho y).PosSemidef)
    (hsigma : ∀ y, (sigma y).PosSemidef)
    {α : ℝ} (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ (conditionalRenyiRightBlockDiagonal rho)
        (conditionalRenyiRightBlockDiagonal sigma)
        (conditionalRenyiRightBlockDiagonal_posSemidef rho hrho)
        (conditionalRenyiRightBlockDiagonal_posSemidef sigma hsigma) α =
      ∑ y, sandwichedRenyiQ (rho y) (sigma y) (hrho y) (hsigma y) α := by
  have hα_pos : 0 < α := by linarith
  have hα_nonneg : 0 ≤ α := le_of_lt hα_pos
  have hs_nonneg : 0 ≤ sandwichedConditioningExponent α :=
    sandwichedConditioningExponent_nonneg hα_pos (le_of_lt hα_lt_one)
  have hinner : ∀ y,
      (CFC.rpow (sigma y) (sandwichedConditioningExponent α) *
        rho y * CFC.rpow (sigma y) (sandwichedConditioningExponent α)).PosSemidef := by
    intro y
    simpa [sandwichedRenyiQInner, sandwichedConditioningExponent] using
      (sandwichedRenyiQInner_posSemidef (hrho y) (hsigma y) α)
  have hinner_power : ∀ y,
      (CFC.rpow (CFC.rpow (sigma y) (sandwichedConditioningExponent α) *
        rho y * CFC.rpow (sigma y) (sandwichedConditioningExponent α)) α).PosSemidef := by
    intro y
    exact cMatrix_rpow_posSemidef (A :=
      CFC.rpow (sigma y) (sandwichedConditioningExponent α) *
        rho y * CFC.rpow (sigma y) (sandwichedConditioningExponent α))
      (s := α) (hinner y)
  have hglobal_inner :
      CFC.rpow
          (CFC.rpow (conditionalRenyiRightBlockDiagonal sigma)
              (sandwichedConditioningExponent α) *
            conditionalRenyiRightBlockDiagonal rho *
            CFC.rpow (conditionalRenyiRightBlockDiagonal sigma)
              (sandwichedConditioningExponent α)) α =
        conditionalRenyiRightBlockDiagonal (fun y =>
          CFC.rpow (CFC.rpow (sigma y) (sandwichedConditioningExponent α) *
            rho y * CFC.rpow (sigma y) (sandwichedConditioningExponent α)) α) := by
    rw [conditionalRightBlockDiagonal_rpow_nonneg sigma hsigma hs_nonneg]
    rw [conditionalRenyiRightBlockDiagonal_mul,
      conditionalRenyiRightBlockDiagonal_mul]
    rw [conditionalRightBlockDiagonal_rpow_nonneg
      (fun y => CFC.rpow (sigma y) (sandwichedConditioningExponent α) *
        rho y * CFC.rpow (sigma y) (sandwichedConditioningExponent α))
      hinner hα_nonneg]
  dsimp [sandwichedRenyiQ]
  change
    (CFC.rpow
        (CFC.rpow (conditionalRenyiRightBlockDiagonal sigma)
            (sandwichedConditioningExponent α) *
          conditionalRenyiRightBlockDiagonal rho *
          CFC.rpow (conditionalRenyiRightBlockDiagonal sigma)
            (sandwichedConditioningExponent α)) α).trace.re =
      ∑ y, (CFC.rpow
        (CFC.rpow (sigma y) (sandwichedConditioningExponent α) *
          rho y * CFC.rpow (sigma y) (sandwichedConditioningExponent α)) α).trace.re
  rw [hglobal_inner, conditionalRenyiRightBlockDiagonal_trace]
  rw [Complex.re_sum]

/-! The same block calculation is valid on the high-order branch.  The only
extra point is that the sandwich exponent may be negative; the shared
support-aware power theorem is used throughout, so a zero block is never
turned into an informal `0 * infinity` expression. -/

theorem sandwichedRenyiQ_fixedReference_blockDiagonal
    (rho sigma : Y → CMatrix (A × B))
    (hrho : ∀ y, (rho y).PosSemidef)
    (hsigma : ∀ y, (sigma y).PosSemidef)
    {α : ℝ} (hα_pos : 0 < α) :
    sandwichedRenyiQ (conditionalRenyiRightBlockDiagonal rho)
        (conditionalRenyiRightBlockDiagonal sigma)
        (conditionalRenyiRightBlockDiagonal_posSemidef rho hrho)
        (conditionalRenyiRightBlockDiagonal_posSemidef sigma hsigma) α =
      ∑ y, sandwichedRenyiQ (rho y) (sigma y) (hrho y) (hsigma y) α := by
  have hα_nonneg : 0 ≤ α := hα_pos.le
  have hinner : ∀ y,
      (CFC.rpow (sigma y) (sandwichedConditioningExponent α) *
        rho y * CFC.rpow (sigma y) (sandwichedConditioningExponent α)).PosSemidef := by
    intro y
    simpa [sandwichedRenyiQInner, sandwichedConditioningExponent] using
      (sandwichedRenyiQInner_posSemidef (hrho y) (hsigma y) α)
  have hinner_power : ∀ y,
      (CFC.rpow (CFC.rpow (sigma y) (sandwichedConditioningExponent α) *
        rho y * CFC.rpow (sigma y) (sandwichedConditioningExponent α)) α).PosSemidef := by
    intro y
    exact cMatrix_rpow_posSemidef (A :=
      CFC.rpow (sigma y) (sandwichedConditioningExponent α) *
        rho y * CFC.rpow (sigma y) (sandwichedConditioningExponent α))
      (s := α) (hinner y)
  have hglobal_inner :
      CFC.rpow
          (CFC.rpow (conditionalRenyiRightBlockDiagonal sigma)
              (sandwichedConditioningExponent α) *
            conditionalRenyiRightBlockDiagonal rho *
            CFC.rpow (conditionalRenyiRightBlockDiagonal sigma)
              (sandwichedConditioningExponent α)) α =
        conditionalRenyiRightBlockDiagonal (fun y =>
          CFC.rpow (CFC.rpow (sigma y) (sandwichedConditioningExponent α) *
            rho y * CFC.rpow (sigma y) (sandwichedConditioningExponent α)) α) := by
    rw [conditionalRenyiRightBlockDiagonal_rpow_support sigma hsigma
        (sandwichedConditioningExponent α)]
    rw [conditionalRenyiRightBlockDiagonal_mul,
      conditionalRenyiRightBlockDiagonal_mul]
    rw [conditionalRenyiRightBlockDiagonal_rpow_support
      (fun y => CFC.rpow (sigma y) (sandwichedConditioningExponent α) *
        rho y * CFC.rpow (sigma y) (sandwichedConditioningExponent α))
      hinner α]
  dsimp [sandwichedRenyiQ]
  change
    (CFC.rpow
        (CFC.rpow (conditionalRenyiRightBlockDiagonal sigma)
            (sandwichedConditioningExponent α) *
          conditionalRenyiRightBlockDiagonal rho *
          CFC.rpow (conditionalRenyiRightBlockDiagonal sigma)
            (sandwichedConditioningExponent α)) α).trace.re =
      ∑ y, (CFC.rpow
        (CFC.rpow (sigma y) (sandwichedConditioningExponent α) *
          rho y * CFC.rpow (sigma y) (sandwichedConditioningExponent α)) α).trace.re
  rw [hglobal_inner, conditionalRenyiRightBlockDiagonal_trace]
  rw [Complex.re_sum]

/-! Scaling both arguments by the same classical weight produces exactly one
copy of that weight.  This is the sandwiched analogue of the scalar step in
`eq:qc-div`; proving it at matrix level also covers a zero-probability block
without forming a logarithm. -/

theorem sandwichedQ_real_smul_both
    {X : Type*} [Fintype X] [DecidableEq X]
    (M N : CMatrix X) (hM : M.PosSemidef) (hN : N.PosSemidef)
    (p : ℝ≥0) {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ((p : ℂ) • M) ((p : ℂ) • N)
        (hM.smul (by exact_mod_cast p.coe_nonneg))
        (hN.smul (by exact_mod_cast p.coe_nonneg)) α =
      (p : ℝ) * sandwichedRenyiQ M N hM hN α := by
  have hp_nonneg : 0 ≤ (p : ℝ) := p.coe_nonneg
  by_cases hp_zero : p = 0
  · subst p
    have hs_ne : sandwichedConditioningExponent α ≠ 0 :=
      ne_of_gt (div_pos (sub_pos.mpr hα_lt_one)
        (mul_pos two_pos hα_pos))
    have hα_ne : α ≠ 0 := ne_of_gt hα_pos
    dsimp [sandwichedRenyiQ]
    simp only [zero_smul]
    change (CFC.rpow
      (CFC.rpow (0 : CMatrix X) (sandwichedConditioningExponent α) * 0 *
        CFC.rpow (0 : CMatrix X) (sandwichedConditioningExponent α)) α).trace.re =
      0 * (CFC.rpow
        (CFC.rpow N (sandwichedConditioningExponent α) * M *
          CFC.rpow N (sandwichedConditioningExponent α)) α).trace.re
    rw [CFC.zero_rpow (A := CMatrix X) hs_ne]
    simp only [zero_mul, mul_zero]
    rw [CFC.zero_rpow (A := CMatrix X) hα_ne]
    simp
  · have hp_pos : 0 < (p : ℝ) := by
      exact_mod_cast (pos_of_ne_zero hp_zero)
    let s : ℝ := sandwichedConditioningExponent α
    have hs_pos : 0 < s := by
      exact div_pos (sub_pos.mpr hα_lt_one) (mul_pos two_pos hα_pos)
    have hscale :
        ((p : ℂ) • N : CMatrix X) = (p : ℝ) • N := by simp
    have hscaleM :
        ((p : ℂ) • M : CMatrix X) = (p : ℝ) • M := by simp
    have hfactor :
        (((p : ℝ) ^ s * (p : ℝ) * (p : ℝ) ^ s) ^ α) = (p : ℝ) := by
      have hmul :
          (p : ℝ) ^ s * (p : ℝ) ^ s = (p : ℝ) ^ (s + s) := by
        rw [Real.rpow_add hp_pos]
      calc
        ((p : ℝ) ^ s * (p : ℝ) * (p : ℝ) ^ s) ^ α =
            (((p : ℝ) ^ s * (p : ℝ) ^ s) * (p : ℝ)) ^ α := by ring
        _ = ((p : ℝ) ^ (s + s) * (p : ℝ)) ^ α := by rw [hmul]
        _ = ((p : ℝ) ^ (s + s)) ^ α * (p : ℝ) ^ α := by
          rw [Real.mul_rpow (Real.rpow_nonneg hp_nonneg _) hp_nonneg]
        _ = (p : ℝ) ^ ((s + s) * α) * (p : ℝ) ^ α := by
          rw [← Real.rpow_mul hp_nonneg]
        _ = (p : ℝ) ^ (((s + s) * α) + α) := by
          rw [← Real.rpow_add hp_pos]
        _ = (p : ℝ) := by
          have he : ((s + s) * α) + α = 1 := by
            dsimp [s, sandwichedConditioningExponent]
            field_simp [ne_of_gt hα_pos]
            ring
          rw [he, Real.rpow_one]
    unfold sandwichedRenyiQ
    change (CFC.rpow
      (CFC.rpow ((p : ℝ) • N) s * ((p : ℝ) • M) *
        CFC.rpow ((p : ℝ) • N) s) α).trace.re =
      (p : ℝ) * (CFC.rpow
        (CFC.rpow N s * M * CFC.rpow N s) α).trace.re
    rw [cMatrix_rpow_real_smul_posSemidef_schatten hN hp_nonneg]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hscalar :
        (p : ℝ) ^ s * ((p : ℝ) * (p : ℝ) ^ s) =
          (p : ℝ) ^ s * (p : ℝ) * (p : ℝ) ^ s := by ring
    rw [hscalar]
    have hinner :
        (CFC.rpow N s * M * CFC.rpow N s).PosSemidef := by
      dsimp [s, sandwichedConditioningExponent]
      exact sandwichedRenyiQInner_posSemidef hM hN α
    rw [cMatrix_rpow_real_smul_posSemidef_schatten
      (A := CFC.rpow N s * M * CFC.rpow N s) hinner
      (lambda := (p : ℝ) ^ s * (p : ℝ) * (p : ℝ) ^ s)
      (s := α)
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg hp_nonneg _) hp_nonneg)
        (Real.rpow_nonneg hp_nonneg _))]
    rw [Matrix.trace_smul, Complex.real_smul]
    rw [hfactor]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-! The upward block calculation needs independent weights on the state and
reference blocks.  This is the matrix form of
`Q_alpha(p rho || q sigma) = p^alpha q^(1-alpha) Q_alpha(rho || sigma)`.
The zero cases are discharged before any logarithm or negative power is
introduced. -/

theorem sandwichedQ_real_smul_left_right
    {X : Type*} [Fintype X] [DecidableEq X]
    (M N : CMatrix X) (hM : M.PosSemidef) (hN : N.PosSemidef)
    (p q : ℝ≥0) {α : ℝ} (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyiQ ((p : ℂ) • M) ((q : ℂ) • N)
        (hM.smul (by exact_mod_cast p.coe_nonneg))
        (hN.smul (by exact_mod_cast q.coe_nonneg)) α =
      (p : ℝ) ^ α * (q : ℝ) ^ (1 - α) *
        sandwichedRenyiQ M N hM hN α := by
  have hp_nonneg : 0 ≤ (p : ℝ) := p.coe_nonneg
  have hq_nonneg : 0 ≤ (q : ℝ) := q.coe_nonneg
  let s : ℝ := sandwichedConditioningExponent α
  have hs_ne : s ≠ 0 := by
    dsimp [s, sandwichedConditioningExponent]
    apply div_ne_zero
    · exact sub_ne_zero.mpr hα_ne_one.symm
    · exact mul_ne_zero two_ne_zero hα_pos.ne'
  by_cases hp_zero : p = 0
  · subst p
    dsimp [sandwichedRenyiQ]
    simp only [zero_smul]
    change (CFC.rpow
      (CFC.rpow ((q : ℂ) • N) s * 0 *
        CFC.rpow ((q : ℂ) • N) s) α).trace.re =
      (0 : ℝ) ^ α * (q : ℝ) ^ (1 - α) *
        (CFC.rpow (CFC.rpow N s * M * CFC.rpow N s) α).trace.re
    rw [show CFC.rpow ((q : ℂ) • N) s =
        CFC.rpow ((q : ℝ) • N) s by simp]
    simp only [mul_zero, zero_mul]
    rw [CFC.zero_rpow (A := CMatrix X) hα_pos.ne']
    simp [Real.zero_rpow hα_pos.ne']
  · have hp_pos : 0 < (p : ℝ) := by
      exact_mod_cast (pos_of_ne_zero hp_zero)
    by_cases hq_zero : q = 0
    · subst q
      dsimp [sandwichedRenyiQ]
      simp only [zero_smul]
      change (CFC.rpow
        (CFC.rpow (0 : CMatrix X) s * ((p : ℂ) • M) *
          CFC.rpow (0 : CMatrix X) s) α).trace.re =
        (p : ℝ) ^ α * (0 : ℝ) ^ (1 - α) *
          (CFC.rpow (CFC.rpow N s * M * CFC.rpow N s) α).trace.re
      rw [CFC.zero_rpow (A := CMatrix X) hs_ne]
      simp only [zero_mul, mul_zero]
      rw [CFC.zero_rpow (A := CMatrix X) hα_pos.ne']
      simp [Real.zero_rpow (sub_ne_zero.mpr hα_ne_one.symm)]
    · have hq_pos : 0 < (q : ℝ) := by
        exact_mod_cast (pos_of_ne_zero hq_zero)
      have hs_scale_q :
          CFC.rpow ((q : ℂ) • N) s =
            (q : ℝ) ^ s • CFC.rpow N s := by
        simp only [show ((q : ℂ) • N : CMatrix X) = (q : ℝ) • N by simp]
        exact cMatrix_rpow_real_smul_posSemidef_schatten hN hq_nonneg
      have hs_scale_q_real :
          CFC.rpow ((q : ℝ) • N) s =
            (q : ℝ) ^ s • CFC.rpow N s := by
        exact cMatrix_rpow_real_smul_posSemidef_schatten hN hq_nonneg
      have hinner :
          (CFC.rpow N s * M * CFC.rpow N s).PosSemidef := by
        dsimp [s, sandwichedConditioningExponent]
        exact sandwichedRenyiQInner_posSemidef hM hN α
      have hfactor :
          ((q : ℝ) ^ s * (p : ℝ) * (q : ℝ) ^ s) ^ α =
            (p : ℝ) ^ α * (q : ℝ) ^ (1 - α) := by
        have hmul : (q : ℝ) ^ s * (q : ℝ) ^ s =
            (q : ℝ) ^ (s + s) := by
          rw [Real.rpow_add hq_pos]
        calc
          ((q : ℝ) ^ s * (p : ℝ) * (q : ℝ) ^ s) ^ α =
              ((q : ℝ) ^ s * (q : ℝ) ^ s * (p : ℝ)) ^ α := by ring
          _ = ((q : ℝ) ^ (s + s) * (p : ℝ)) ^ α := by rw [hmul]
          _ = (q : ℝ) ^ ((s + s) * α) * (p : ℝ) ^ α := by
            rw [Real.mul_rpow (Real.rpow_nonneg hq_nonneg _) hp_nonneg,
              ← Real.rpow_mul hq_nonneg]
          _ = (p : ℝ) ^ α * (q : ℝ) ^ (1 - α) := by
            have he : (s + s) * α = 1 - α := by
              dsimp [s, sandwichedConditioningExponent]
              field_simp [hα_pos.ne']
              ring
            rw [he]
            ring
      unfold sandwichedRenyiQ
      change (CFC.rpow
        (CFC.rpow ((q : ℝ) • N) s * ((p : ℝ) • M) *
          CFC.rpow ((q : ℝ) • N) s) α).trace.re = _
      rw [hs_scale_q_real]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have hscalar :
          (q : ℝ) ^ s * ((p : ℝ) * (q : ℝ) ^ s) =
            (q : ℝ) ^ s * (p : ℝ) * (q : ℝ) ^ s := by ring
      rw [hscalar]
      rw [cMatrix_rpow_real_smul_posSemidef_schatten hinner
        (lambda := (q : ℝ) ^ s * (p : ℝ) * (q : ℝ) ^ s)
        (s := α)
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hq_nonneg _) hp_nonneg)
          (Real.rpow_nonneg hq_nonneg _))]
      rw [Matrix.trace_smul, Complex.real_smul, hfactor]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      dsimp [s, sandwichedConditioningExponent]
      simp


end State

end

end QIT
