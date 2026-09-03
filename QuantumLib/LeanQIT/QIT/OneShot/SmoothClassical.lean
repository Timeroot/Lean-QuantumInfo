/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.SmoothEndpoint
public import QIT.OneShot.SmoothAttainment
public import QIT.OneShot.SmoothNormalizedExtension
public import QIT.OneShot.SmoothSupportRestriction
public import QIT.OneShot.SmoothIsometry
public import QIT.States.TraceNorm.BlockMatrix
public import QIT.Measurements.Projective
public import QIT.States.Subnormalized
public import QIT.States.Geometry.PurifiedDistance

/-!
# Smooth classical registers

Block-diagonal predicates and the associated two-register coordinate pinch for
states on `((a × x) × (y × b))`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Pointwise
open Matrix

namespace QIT

universe u v w z

noncomputable section

namespace SubnormalizedState

variable {a : Type u} {x : Type v} {y : Type w} {b : Type z}
variable [Fintype a] [DecidableEq a]
variable [Fintype x] [DecidableEq x]
variable [Fintype y] [DecidableEq y]
variable [Fintype b] [DecidableEq b]

/-! ## Public classicality predicates -/

/-- The `X` coordinate is classical: all off-diagonal `X` blocks vanish. -/
def classicalOnX (rho : SubnormalizedState ((a × x) × (y × b))) : Prop :=
  ∀ i j, i.1.2 ≠ j.1.2 → rho.matrix i j = 0

/-- The `Y` coordinate is classical: all off-diagonal `Y` blocks vanish. -/
def classicalOnY (rho : SubnormalizedState ((a × x) × (y × b))) : Prop :=
  ∀ i j, i.2.1 ≠ j.2.1 → rho.matrix i j = 0

/-- Both designated coordinates are classical. -/
def classicalOnXY (rho : SubnormalizedState ((a × x) × (y × b))) : Prop :=
  classicalOnX rho ∧ classicalOnY rho

/-! ## Private two-register coordinate pinching -/

private def classicalXYProjector (k : x × y) :
    CMatrix ((a × x) × (y × b)) :=
  Matrix.diagonal (fun i =>
    if i.1.2 = k.1 ∧ i.2.1 = k.2 then (1 : ℂ) else 0)

private def classicalXYMeasurement :
    ProjectiveMeasurement (x × y) ((a × x) × (y × b)) where
  effects := classicalXYProjector
  isHermitian := by
    intro k
    rw [Matrix.IsHermitian]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [classicalXYProjector]
    · simp [classicalXYProjector, hij, Ne.symm hij]
  idempotent := by
    intro k
    rw [classicalXYProjector, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hik : i.1.2 = k.1 ∧ i.2.1 = k.2 <;>
        simp [hik]
    · simp [hij]
  orthogonal := by
    intro k l hkl
    rw [classicalXYProjector, classicalXYProjector, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hik : i.1.2 = k.1 ∧ i.2.1 = k.2
      · by_cases hil : i.1.2 = l.1 ∧ i.2.1 = l.2
        · exfalso
          apply hkl
          exact Prod.ext (hik.1.symm.trans hil.1) (hik.2.symm.trans hil.2)
        · by_cases hkl1 : k.1 = l.1
          · have hkl2 : k.2 ≠ l.2 := by
              intro h
              apply hkl
              exact Prod.ext hkl1 h
            simp [Matrix.diagonal, hik, hkl1, hkl2]
          · simp [Matrix.diagonal, hik, hkl1]
      · simp [hik]
    · simp [hij]
  sum_eq_one := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.sum_apply]
      rw [Finset.sum_eq_single (i.1.2, i.2.1)]
      · simp [classicalXYProjector]
      · intro k _ hk
        have hnot : ¬ (i.1.2 = k.1 ∧ i.2.1 = k.2) := by
          intro h
          apply hk
          exact Prod.ext h.1.symm h.2.symm
        simp [classicalXYProjector, hnot]
      · simp
    · simp [classicalXYProjector, Matrix.sum_apply, hij]

private def classicalPinch (rho : SubnormalizedState ((a × x) × (y × b))) :
    SubnormalizedState ((a × x) × (y × b)) :=
  rho.applyTraceNonincreasingCP
    classicalXYMeasurement.pinchingChannel.map
    classicalXYMeasurement.pinchingChannel.traceNonincreasingCP_map

private theorem classicalXYProjector_sandwich_apply
    (k : x × y) (M : CMatrix ((a × x) × (y × b))) (i j) :
    ((classicalXYProjector k * M * classicalXYProjector k :
        CMatrix ((a × x) × (y × b))) i j) =
      if i.1.2 = k.1 ∧ i.2.1 = k.2 ∧
          j.1.2 = k.1 ∧ j.2.1 = k.2 then M i j else 0 := by
  rw [classicalXYProjector, Matrix.mul_assoc, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  by_cases hix : i.1.2 = k.1 <;>
    by_cases hiy : i.2.1 = k.2 <;>
    by_cases hjx : j.1.2 = k.1 <;>
    by_cases hjy : j.2.1 = k.2 <;>
    simp [hix, hiy, hjx, hjy]

private theorem classicalPinch_matrix_apply
    (rho : SubnormalizedState ((a × x) × (y × b))) (i j) :
    (classicalPinch rho).matrix i j =
      if i.1.2 = j.1.2 ∧ i.2.1 = j.2.1 then rho.matrix i j else 0 := by
  change classicalXYMeasurement.pinchingChannel.map rho.matrix i j = _
  rw [ProjectiveMeasurement.pinchingChannel_map]
  rw [show classicalXYMeasurement.effects = classicalXYProjector from rfl]
  rw [Matrix.sum_apply]
  change (∑ k : x × y,
      ((classicalXYProjector k * rho.matrix * classicalXYProjector k :
        CMatrix ((a × x) × (y × b))) i j)) = _
  simp_rw [classicalXYProjector_sandwich_apply]
  by_cases hcoord : i.1.2 = j.1.2 ∧ i.2.1 = j.2.1
  · rw [Finset.sum_eq_single (i.1.2, i.2.1)]
    · simp [hcoord]
    · intro k _ hk
      have hnot : ¬ (j.1.2 = k.1 ∧ j.2.1 = k.2) := by
        intro h
        apply hk
        exact Prod.ext (hcoord.1.trans h.1).symm (hcoord.2.trans h.2).symm
      simp [hnot]
    · simp
  · rw [if_neg hcoord]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hj : j.1.2 = k.1 ∧ j.2.1 = k.2
    · have hi : ¬ (i.1.2 = k.1 ∧ i.2.1 = k.2) := by
        intro h
        exact hcoord ⟨h.1.trans hj.1.symm, h.2.trans hj.2.symm⟩
      simp [hj, hi]
    · simp [hj]

private theorem classicalPinch_matrix_eq_self_of_classicalOnXY
    {rho : SubnormalizedState ((a × x) × (y × b))}
    (hclassical : classicalOnXY rho) :
    (classicalPinch rho).matrix = rho.matrix := by
  ext i j
  by_cases hx : i.1.2 = j.1.2
  · by_cases hy : i.2.1 = j.2.1
    · simp [classicalPinch_matrix_apply, hx, hy]
    · have hzero := hclassical.2 i j hy
      simp [classicalPinch_matrix_apply, hx, hy, hzero]
  · have hzero := hclassical.1 i j hx
    simp [classicalPinch_matrix_apply, hx, hzero]

private theorem classicalPinch_classicalOnXY
    (rho : SubnormalizedState ((a × x) × (y × b))) :
    classicalOnXY (classicalPinch rho) := by
  constructor
  · intro i j hij
    simp [classicalPinch_matrix_apply, hij]
  · intro i j hij
    simp [classicalPinch_matrix_apply, hij]

private theorem purifiedBall_classicalPinch_of_classical_center
    {rho sigma : SubnormalizedState ((a × x) × (y × b))} {epsilon : ℝ}
    (hclassical : classicalOnXY rho)
    (hball : rho.purifiedBall epsilon sigma) :
    rho.purifiedBall epsilon (classicalPinch sigma) := by
  have hpinched := SubnormalizedState.purifiedBall_of_traceNonincreasingCP
    (ρ := rho) (σ := sigma) (ε := epsilon)
    classicalXYMeasurement.pinchingChannel.map
    classicalXYMeasurement.pinchingChannel.traceNonincreasingCP_map hball
  have hfix : classicalPinch rho = rho := by
    apply SubnormalizedState.ext
    exact classicalPinch_matrix_eq_self_of_classicalOnXY hclassical
  change (classicalPinch rho).purifiedBall epsilon (classicalPinch sigma) at hpinched
  rw [hfix] at hpinched
  exact hpinched

/-! ## Min-entropy witness transport -/

private def classicalConditioningPinch (T : CMatrix (y × b)) : CMatrix (y × b) :=
  (sourceCoordinatePinchChannel (a := y) (b := b)).map T

private theorem classicalCoordinateMeasure_map_apply (X : CMatrix y) (i j : y) :
    (Channel.measure (POVM.coordinate y)).map X i j =
      if i = j then X i j else 0 := by
  classical
  rw [Channel.measure_map]
  simp only [Matrix.sum_apply, Matrix.smul_apply, POVM.coordinate_effects]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    rw [Finset.sum_eq_single i]
    · rw [Matrix.trace_mul_single]
      simp
    · intro k _ hki
      simp [hki]
    · intro hi
      simp at hi
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hnot : ¬ (k = i ∧ k = j) := by
      intro h
      exact hij (h.1.symm.trans h.2)
    simp [hnot]

private theorem sourceCoordinatePinchChannel_map_apply
    (T : CMatrix (y × b)) (i j : y × b) :
    (sourceCoordinatePinchChannel (a := y) (b := b)).map T i j =
      if i.1 = j.1 then T i j else 0 := by
  change MatrixMap.kron (Channel.measure (POVM.coordinate y)).map
      (Channel.idChannel b).map T i j = _
  rw [MatrixMap.kron_idChannel_apply_slice]
  rw [classicalCoordinateMeasure_map_apply]

private theorem classicalPinching_map_apply
    (M : CMatrix ((a × x) × (y × b))) (i j) :
    classicalXYMeasurement.pinchingChannel.map M i j =
      if i.1.2 = j.1.2 ∧ i.2.1 = j.2.1 then M i j else 0 := by
  rw [ProjectiveMeasurement.pinchingChannel_map]
  rw [Matrix.sum_apply]
  change (∑ k : x × y,
      ((classicalXYProjector k * M * classicalXYProjector k :
        CMatrix ((a × x) × (y × b))) i j)) = _
  simp_rw [classicalXYProjector_sandwich_apply]
  by_cases hcoord : i.1.2 = j.1.2 ∧ i.2.1 = j.2.1
  · rw [Finset.sum_eq_single (i.1.2, i.2.1)]
    · simp [hcoord]
    · intro k _ hk
      have hnot : ¬ (j.1.2 = k.1 ∧ j.2.1 = k.2) := by
        intro h
        apply hk
        exact Prod.ext (hcoord.1.trans h.1).symm (hcoord.2.trans h.2).symm
      simp [hnot]
    · simp
  · rw [if_neg hcoord]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hj : j.1.2 = k.1 ∧ j.2.1 = k.2
    · have hi : ¬ (i.1.2 = k.1 ∧ i.2.1 = k.2) := by
        intro h
        exact hcoord ⟨h.1.trans hj.1.symm, h.2.trans hj.2.symm⟩
      simp [hj, hi]
    · simp [hj]

private theorem classicalPinching_map_identityTensor (T : CMatrix (y × b)) :
    classicalXYMeasurement.pinchingChannel.map
        (Matrix.kronecker (1 : CMatrix (a × x)) T) =
      Matrix.kronecker (1 : CMatrix (a × x)) (classicalConditioningPinch T) := by
  ext i j
  simp only [classicalConditioningPinch]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [classicalPinching_map_apply, sourceCoordinatePinchChannel_map_apply]
  by_cases hsource : i.1 = j.1
  · by_cases hy : i.2.1 = j.2.1
    · simp [hsource, hy]
    · simp [hsource, hy]
  · simp [hsource]

private theorem ConditionalMinEntropyScaleFeasible.classicalPinch
    {rho : SubnormalizedState ((a × x) × (y × b))} {T : CMatrix (y × b)}
    (hT : ConditionalMinEntropyScaleFeasible (a := a × x) rho T) :
    ConditionalMinEntropyScaleFeasible (a := a × x) (classicalPinch rho)
      (classicalConditioningPinch T) := by
  constructor
  · exact MatrixMap.isCompletelyPositive_mapsPositive
      (sourceCoordinatePinchChannel (a := y) (b := b)).map
      (sourceCoordinatePinchChannel (a := y) (b := b)).completelyPositive T hT.1
  · have hdiff :
        (Matrix.kronecker (1 : CMatrix (a × x)) T - rho.matrix).PosSemidef :=
      hT.2
    have hmap := MatrixMap.isCompletelyPositive_mapsPositive
      classicalXYMeasurement.pinchingChannel.map
      classicalXYMeasurement.pinchingChannel.completelyPositive
      (Matrix.kronecker (1 : CMatrix (a × x)) T - rho.matrix) hdiff
    change (Matrix.kronecker (1 : CMatrix (a × x))
        (classicalConditioningPinch T) -
        classicalXYMeasurement.pinchingChannel.map rho.matrix).PosSemidef
    convert hmap using 1
    simp only [map_sub]
    rw [classicalPinching_map_identityTensor]

private theorem nonempty_of_trace_pos
    {c : Type*} [Fintype c] [DecidableEq c]
    (M : CMatrix c) (hM : 0 < M.trace.re) : Nonempty c := by
  classical
  by_contra hne
  haveI : IsEmpty c := not_nonempty_iff.mp hne
  simp at hM

private theorem classicalPinch_trace_re
    (rho : SubnormalizedState ((a × x) × (y × b))) :
    (classicalPinch rho).matrix.trace.re = rho.matrix.trace.re := by
  change (classicalXYMeasurement.pinchingChannel.map rho.matrix).trace.re = _
  exact congrArg Complex.re
    (classicalXYMeasurement.pinchingChannel.tracePreserving rho.matrix)

private theorem conditionalMinEntropyScale_classicalPinch_le
    (rho : SubnormalizedState ((a × x) × (y × b))) :
    (classicalPinch rho).conditionalMinEntropyScale (a := a × x) ≤
      rho.conditionalMinEntropyScale (a := a × x) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf (rho.conditionalMinEntropyScaleValueSet_nonempty (a := a × x)) ?_
  intro t ht
  rcases ht with ⟨T, hT, rfl⟩
  have hbddPinched :
      BddBelow ((classicalPinch rho).conditionalMinEntropyScaleValueSet
        (a := a × x)) :=
    (classicalPinch rho).conditionalMinEntropyScaleValueSet_bddBelow (a := a × x)
  exact csInf_le hbddPinched
    ⟨classicalConditioningPinch T, hT.classicalPinch,
      by
        change T.trace.re = ((sourceCoordinatePinchChannel (a := y) (b := b)).map T).trace.re
        exact congrArg Complex.re
          ((sourceCoordinatePinchChannel (a := y) (b := b)).tracePreserving T).symm⟩

private theorem conditionalMinEntropyRaw_le_classicalPinch_of_trace_pos
    [Nonempty a] [Nonempty b]
    (rho : SubnormalizedState ((a × x) × (y × b)))
    (hρ : 0 < rho.matrix.trace.re) :
    rho.conditionalMinEntropyRaw ≤ (classicalPinch rho).conditionalMinEntropyRaw := by
  have hfull : Nonempty ((a × x) × (y × b)) :=
    nonempty_of_trace_pos rho.matrix hρ
  letI : Nonempty (a × x) := by
    rcases hfull with ⟨i⟩
    exact ⟨i.1⟩
  letI : Nonempty (y × b) := by
    rcases hfull with ⟨i⟩
    exact ⟨i.2⟩
  have hpinched : 0 < (classicalPinch rho).matrix.trace.re := by
    rw [classicalPinch_trace_re]
    exact hρ
  rw [rho.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a × x) hρ,
    (classicalPinch rho).conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a × x) hpinched]
  have hscale_le := conditionalMinEntropyScale_classicalPinch_le rho
  have hpinched_scale_pos :=
    (classicalPinch rho).conditionalMinEntropyScale_pos_of_trace_pos
      (a := a × x) hpinched
  have hlog :
      log2 ((classicalPinch rho).conditionalMinEntropyScale (a := a × x)) ≤
        log2 (rho.conditionalMinEntropyScale (a := a × x)) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hpinched_scale_pos hscale_le)
      (le_of_lt (Real.log_pos one_lt_two))
  exact neg_le_neg hlog

private def classicalConditioningPinchState
    (sigma : SubnormalizedState (y × b)) : SubnormalizedState (y × b) :=
  sigma.applyTraceNonincreasingCP
    (sourceCoordinatePinchChannel (a := y) (b := b)).map
    (sourceCoordinatePinchChannel (a := y) (b := b)).traceNonincreasingCP_map

private theorem classicalConditioningPinchState_matrix
    (sigma : SubnormalizedState (y × b)) :
    (classicalConditioningPinchState (y := y) (b := b) sigma).matrix =
      classicalConditioningPinch sigma.matrix := by
  ext i j
  simp [classicalConditioningPinchState,
    SubnormalizedState.applyTraceNonincreasingCP_matrix,
    classicalConditioningPinch, sourceCoordinatePinchChannel_map_apply]

private theorem conditionalMaxEntropyRaw_le_classicalPinch_of_trace_pos
    [Nonempty a] [Nonempty b]
    (rho : SubnormalizedState ((a × x) × (y × b)))
    (hρ : 0 < rho.matrix.trace.re) :
    rho.conditionalMaxEntropyRaw ≤ (classicalPinch rho).conditionalMaxEntropyRaw := by
  let rhoP := classicalPinch rho
  have hρP : 0 < rhoP.matrix.trace.re := by
    rw [classicalPinch_trace_re]
    exact hρ
  have hfull : Nonempty ((a × x) × (y × b)) :=
    nonempty_of_trace_pos rho.matrix hρ
  letI : Nonempty (a × x) := by
    rcases hfull with ⟨i⟩
    exact ⟨i.1⟩
  letI : Nonempty (y × b) := by
    rcases hfull with ⟨i⟩
    exact ⟨i.2⟩
  have hne := rho.conditionalMaxEntropyPositiveExponentValueSet_nonempty_of_trace_pos
    (a := a × x) hρ
  have hneP := rhoP.conditionalMaxEntropyPositiveExponentValueSet_nonempty_of_trace_pos
    (a := a × x) hρP
  have hbdd := rho.conditionalMaxEntropyPositiveExponentValueSet_bddAbove_of_trace_pos
    (a := a × x) hρ
  have hbddP := rhoP.conditionalMaxEntropyPositiveExponentValueSet_bddAbove_of_trace_pos
    (a := a × x) hρP
  rw [conditionalMaxEntropy_eq_positive,
    conditionalMaxEntropy_eq_positive,
    conditionalMaxEntropyPositive_eq_log2_positiveExponent
      (a := a × x) rho hne hbdd,
    conditionalMaxEntropyPositive_eq_log2_positiveExponent
      (a := a × x) rhoP hneP hbddP]
  have hexp :
      rho.conditionalMaxEntropyPositiveExponent (a := a × x) ≤
        rhoP.conditionalMaxEntropyPositiveExponent (a := a × x) := by
    rw [conditionalMaxEntropyPositiveExponent_eq,
      conditionalMaxEntropyPositiveExponent_eq]
    refine csSup_le hne ?_
    intro z hz
    rcases hz with ⟨sigma, hsigma, rfl⟩
    let sigmaP := classicalConditioningPinchState (y := y) (b := b) sigma
    have hsigmaTrace : 0 < sigma.matrix.trace.re := by
      by_contra hnot
      have hz : sigma.matrix.trace.re = 0 :=
        le_antisymm (le_of_not_gt hnot) sigma.trace_nonneg
      exact (ne_of_gt hsigma)
        (rho.conditionalMaxEntropyExponentCandidate_eq_zero_of_side_trace_zero hz)
    have hsigmaP : 0 < sigmaP.matrix.trace.re := by
      dsimp [sigmaP]
      change 0 < ((sourceCoordinatePinchChannel (a := y) (b := b)).map
        sigma.matrix).trace.re
      rw [(sourceCoordinatePinchChannel (a := y) (b := b)).tracePreserving]
      exact hsigmaTrace
    let hρN : State ((a × x) × (y × b)) := rho.normalize hρ.ne'
    let hρPN : State ((a × x) × (y × b)) := rhoP.normalize hρP.ne'
    let hσN : State (y × b) := sigma.normalize hsigmaTrace.ne'
    let hσPN : State (y × b) := sigmaP.normalize hsigmaP.ne'
    have hmapρ : hρPN = classicalXYMeasurement.pinchingChannel.applyState hρN := by
      apply State.ext
      change (rhoP.normalize hρP.ne').matrix =
        classicalXYMeasurement.pinchingChannel.map
          (rho.normalize hρ.ne').matrix
      rw [SubnormalizedState.normalize_matrix,
        SubnormalizedState.normalize_matrix,
        LinearMap.map_smul_of_tower]
      rw [show rhoP.matrix.trace.re = rho.matrix.trace.re by
        rw [classicalPinch_trace_re]]
      rfl
    have hmapσ : hσPN =
        (sourceCoordinatePinchChannel (a := y) (b := b)).applyState hσN := by
      apply State.ext
      change (sigmaP.normalize hsigmaP.ne').matrix =
        (sourceCoordinatePinchChannel (a := y) (b := b)).map
          (sigma.normalize hsigmaTrace.ne').matrix
      rw [SubnormalizedState.normalize_matrix,
        SubnormalizedState.normalize_matrix,
        LinearMap.map_smul_of_tower]
      rw [show sigmaP.matrix.trace.re = sigma.matrix.trace.re by
        dsimp [sigmaP]
        change ((sourceCoordinatePinchChannel (a := y) (b := b)).map
          sigma.matrix).trace.re = sigma.matrix.trace.re
        exact congrArg Complex.re
          ((sourceCoordinatePinchChannel (a := y) (b := b)).tracePreserving sigma.matrix)]
      rfl
    have hprod : classicalXYMeasurement.pinchingChannel.applyState
          ((State.maximallyMixed (a × x)).prod hσN) =
        (State.maximallyMixed (a × x)).prod hσPN := by
      apply State.ext
      ext i j
      change classicalXYMeasurement.pinchingChannel.map
          (Matrix.kronecker (State.maximallyMixed (a × x)).matrix hσN.matrix) i j =
        (Matrix.kronecker (State.maximallyMixed (a × x)).matrix hσPN.matrix) i j
      change classicalXYMeasurement.pinchingChannel.map
          (Matrix.kroneckerMap (fun z w : ℂ => z * w)
            (State.maximallyMixed (a × x)).matrix hσN.matrix) i j =
        (Matrix.kroneckerMap (fun z w : ℂ => z * w)
          (State.maximallyMixed (a × x)).matrix hσPN.matrix) i j
      rw [State.maximallyMixed_matrix]
      simp only [Matrix.smul_kronecker]
      rw [LinearMap.map_smul]
      have hid := classicalPinching_map_identityTensor (a := a) (x := x)
        (y := y) (b := b) hσN.matrix
      change classicalXYMeasurement.pinchingChannel.map
          (Matrix.kroneckerMap (fun z w : ℂ => z * w)
            (1 : CMatrix (a × x)) hσN.matrix) =
        Matrix.kroneckerMap (fun z w : ℂ => z * w)
          (1 : CMatrix (a × x)) (classicalConditioningPinch hσN.matrix) at hid
      rw [hid]
      have hmapσ_matrix := congrArg State.matrix hmapσ
      have hmapσ_matrix' : classicalConditioningPinch hσN.matrix = hσPN.matrix := by
        change (sourceCoordinatePinchChannel (a := y) (b := b)).map hσN.matrix =
          hσPN.matrix
        simpa only [Channel.applyState] using hmapσ_matrix.symm
      rw [hmapσ_matrix']
    have hcandidate :
        rho.conditionalMaxEntropyExponentCandidate (a := a × x) sigma ≤
          rhoP.conditionalMaxEntropyExponentCandidate (a := a × x) sigmaP := by
      have hfid := State.squaredFidelity_le_applyState_squaredFidelity
        classicalXYMeasurement.pinchingChannel
        ((State.maximallyMixed (a × x)).prod hσN) hρN
      rw [hprod, ← hmapρ] at hfid
      have hscaleR := conditionalMaxEntropyExponentCandidate_ofStateScale_normalize
        (a := a × x) hρN sigma hρ rho.trace_le_one hsigmaTrace
      have hscaleP := conditionalMaxEntropyExponentCandidate_ofStateScale_normalize
        (a := a × x) hρPN sigmaP hρP rhoP.trace_le_one hsigmaP
      have hρscale :
          SubnormalizedState.ofStateScale hρN rho.matrix.trace.re hρ.le rho.trace_le_one = rho := by
        simpa [hρN] using
          (SubnormalizedState.ofStateScale_normalize_trace_eq rho hρ)
      have hρPscale :
          SubnormalizedState.ofStateScale hρPN rhoP.matrix.trace.re hρP.le rhoP.trace_le_one = rhoP := by
        simpa [hρPN] using
          (SubnormalizedState.ofStateScale_normalize_trace_eq rhoP hρP)
      have hscaleR' :
          rho.conditionalMaxEntropyExponentCandidate (a := a × x) sigma =
            rho.matrix.trace.re * sigma.matrix.trace.re *
              hρN.conditionalMaxEntropyExponentCandidate (a := a × x)
                (sigma.normalize hsigmaTrace.ne') := by
        rw [← hρscale]
        simpa [hρscale, SubnormalizedState.ofStateScale_trace_re] using hscaleR
      have hscaleP' :
          rhoP.conditionalMaxEntropyExponentCandidate (a := a × x) sigmaP =
            rhoP.matrix.trace.re * sigmaP.matrix.trace.re *
              hρPN.conditionalMaxEntropyExponentCandidate (a := a × x)
                (sigmaP.normalize hsigmaP.ne') := by
        rw [← hρPscale]
        simpa [hρPscale, SubnormalizedState.ofStateScale_trace_re] using hscaleP
      rw [hscaleR', hscaleP']
      have htraceR : rhoP.matrix.trace.re = rho.matrix.trace.re := by
        rw [classicalPinch_trace_re]
      have htraceS : sigmaP.matrix.trace.re = sigma.matrix.trace.re := by
        dsimp [sigmaP]
        change ((sourceCoordinatePinchChannel (a := y) (b := b)).map
          sigma.matrix).trace.re = sigma.matrix.trace.re
        exact congrArg Complex.re
          ((sourceCoordinatePinchChannel (a := y) (b := b)).tracePreserving sigma.matrix)
      have hfid' :
          hρN.conditionalMaxEntropyExponentCandidate (a := a × x) hσN ≤
            hρPN.conditionalMaxEntropyExponentCandidate (a := a × x) hσPN := by
        have hfid_oriented :
            hρN.squaredFidelity ((State.maximallyMixed (a × x)).prod hσN) ≤
              hρPN.squaredFidelity ((State.maximallyMixed (a × x)).prod hσPN) := by
          calc
            hρN.squaredFidelity ((State.maximallyMixed (a × x)).prod hσN) =
                ((State.maximallyMixed (a × x)).prod hσN).squaredFidelity hρN :=
              State.squaredFidelity_comm_of_uhlmann _ _
            _ ≤ ((State.maximallyMixed (a × x)).prod hσPN).squaredFidelity hρPN := hfid
            _ = hρPN.squaredFidelity ((State.maximallyMixed (a × x)).prod hσPN) :=
              (State.squaredFidelity_comm_of_uhlmann _ _).symm
        rw [State.conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity,
          State.conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity]
        exact mul_le_mul_of_nonneg_left hfid_oriented (by positivity)
      have hscale_nonneg : 0 ≤ rho.matrix.trace.re * sigma.matrix.trace.re :=
        mul_nonneg rho.trace_nonneg sigma.trace_nonneg
      simpa [htraceR, htraceS] using
        (mul_le_mul_of_nonneg_left hfid' hscale_nonneg)
    exact hcandidate.trans (le_csSup hbddP
      ⟨sigmaP, lt_of_lt_of_le hsigma hcandidate, rfl⟩)
  have hpos : 0 < rho.conditionalMaxEntropyPositiveExponent (a := a × x) := by
    rcases hne with ⟨z, hz⟩
    rcases hz with ⟨sigma, hsigma, rfl⟩
    exact lt_of_lt_of_le hsigma (le_csSup hbdd ⟨sigma, hsigma, rfl⟩)
  unfold log2
  exact div_le_div_of_nonneg_right
    (Real.log_le_log hpos hexp)
    (le_of_lt (Real.log_pos one_lt_two))

/-- Smooth conditional min-entropy has a classical optimizer whenever its center
is classical on the designated `X` and `Y` coordinates. -/
theorem smoothConditionalMinEntropy_exists_classical_optimizer
    [Nonempty a] [Nonempty b]
    (rho : SubnormalizedState ((a × x) × (y × b))) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < Real.sqrt rho.matrix.trace.re)
    (hclassical : rho.classicalOnXY) :
    ∃ tau : SubnormalizedState ((a × x) × (y × b)),
      ∃ htau : tau.matrix ≠ 0,
      rho.purifiedBall ε tau ∧ tau.classicalOnXY ∧
        tau.conditionalMinEntropyFinite htau =
          rho.smoothConditionalMinEntropy ε hε0 hε := by
  have hρ : 0 < rho.matrix.trace.re :=
    Real.sqrt_pos.mp (lt_of_le_of_lt hε0 hε)
  have hfull : Nonempty ((a × x) × (y × b)) :=
    nonempty_of_trace_pos rho.matrix hρ
  letI : Nonempty (a × x) := by
    rcases hfull with ⟨i⟩
    exact ⟨i.1⟩
  letI : Nonempty (y × b) := by
    rcases hfull with ⟨i⟩
    exact ⟨i.2⟩
  rcases smoothConditionalMinEntropy_exists_optimizer
      (a := a × x) (b := y × b) rho hε0 hε with
    ⟨rhoMin, hρminne, hball, hmin_eq, hoptimizer⟩
  have hρmin : 0 < rhoMin.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      rho rhoMin hε hball
  have hballPinch := purifiedBall_classicalPinch_of_classical_center hclassical hball
  have hρpinch : 0 < (classicalPinch rhoMin).matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      rho (classicalPinch rhoMin) hε hballPinch
  have hpinchne : (classicalPinch rhoMin).matrix ≠ 0 := by
    intro hzero
    rw [hzero] at hρpinch
    simp at hρpinch
  refine ⟨classicalPinch rhoMin, hpinchne,
    hballPinch,
    classicalPinch_classicalOnXY rhoMin, ?_⟩
  apply le_antisymm
  · calc
      (classicalPinch rhoMin).conditionalMinEntropyRaw ≤
          rhoMin.conditionalMinEntropyRaw :=
        hoptimizer (classicalPinch rhoMin) hpinchne hballPinch
      _ = rho.smoothConditionalMinEntropy ε hε0 hε := hmin_eq.symm
  · calc
      rho.smoothConditionalMinEntropy ε hε0 hε =
          rhoMin.conditionalMinEntropyRaw := hmin_eq
      _ ≤ (classicalPinch rhoMin).conditionalMinEntropyRaw :=
        conditionalMinEntropyRaw_le_classicalPinch_of_trace_pos rhoMin hρmin

/-! ## Canonical complementary marginal seam for the max route -/

/-! ## Classical-coherent projection for the max route

The source proof applies the `XX'` equality projector together with the
coordinate pinching on `Y'`.  The following private map packages both
operations as one Kraus map.  Its Kraus operators are the diagonal
projectors indexed by `Y'`; the equality condition on `X,X'` is built into
each projector.
-/

private def classicalCoherentProjector
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] (k : y') :
    CMatrix ((a × x) × (c × x × y')) :=
  Matrix.diagonal (fun i =>
    if i.1.2 = i.2.2.1 ∧ i.2.2.2 = k then (1 : ℂ) else 0)

private def classicalCoherentMap
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] :
    MatrixMap ((a × x) × (c × x × y')) ((a × x) × (c × x × y')) :=
  MatrixMap.ofKraus (fun k : y' =>
    classicalCoherentProjector (a := a) (x := x) (c := c) k)

omit [Fintype a] [Fintype x] in
private theorem classicalCoherentProjector_conjTranspose
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] (k : y') :
    Matrix.conjTranspose
        (classicalCoherentProjector (a := a) (x := x) (c := c) k) =
      classicalCoherentProjector (a := a) (x := x) (c := c) k := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [classicalCoherentProjector]
  · simp [classicalCoherentProjector, Matrix.conjTranspose_apply,
       hij, Ne.symm hij]

private theorem classicalCoherentProjector_idempotent
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] (k : y') :
    classicalCoherentProjector (a := a) (x := x) (c := c) k *
        classicalCoherentProjector (a := a) (x := x) (c := c) k =
      classicalCoherentProjector (a := a) (x := x) (c := c) k := by
  rw [classicalCoherentProjector, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases h : i.1.2 = i.2.2.1 ∧ i.2.2.2 = k <;> simp [h]
  · simp [hij]

private theorem classicalCoherentKrausAdjoint_sum_apply
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (i j : (a × x) × (c × x × y')) :
    MatrixMap.krausAdjoint (fun k : y' =>
        classicalCoherentProjector (a := a) (x := x) (c := c) k)
        (1 : CMatrix ((a × x) × (c × x × y'))) i j =
      if i = j ∧ i.1.2 = i.2.2.1 then (1 : ℂ) else 0 := by
  rw [MatrixMap.krausAdjoint]
  simp only [classicalCoherentProjector_conjTranspose
      (a := a) (x := x) (c := c), Matrix.mul_one]
  simp_rw [classicalCoherentProjector_idempotent
      (a := a) (x := x) (c := c)]
  rw [show (∑ k : y', classicalCoherentProjector
      (a := a) (x := x) (c := c) k) i j =
      if i = j ∧ i.1.2 = i.2.2.1 then (1 : ℂ) else 0 by
    simp only [Matrix.sum_apply, classicalCoherentProjector,
      Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst j
      by_cases hcopy : i.1.2 = i.2.2.1
      · rw [Finset.sum_eq_single i.2.2.2]
        · simp [hcopy]
        · intro k _ hk
          simp [hcopy, Ne.symm hk]
        · simp
      · simp [hcopy]
    · simp [hij]]

private theorem classicalCoherentKrausAdjoint_sum_le_one
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] :
    MatrixMap.krausAdjoint (fun k : y' =>
        classicalCoherentProjector (a := a) (x := x) (c := c) k)
      (1 : CMatrix ((a × x) × (c × x × y'))) ≤ 1 := by
  have hK : MatrixMap.krausAdjoint (fun k : y' =>
      classicalCoherentProjector (a := a) (x := x) (c := c) k)
      (1 : CMatrix ((a × x) × (c × x × y'))) =
      Matrix.diagonal (fun i =>
        if i.1.2 = i.2.2.1 then (1 : ℂ) else 0) := by
    ext i j
    rw [classicalCoherentKrausAdjoint_sum_apply]
    by_cases hij : i = j <;> simp [ hij]
  rw [hK, Matrix.le_iff]
  have hsub :
      (1 : CMatrix ((a × x) × (c × x × y'))) -
          Matrix.diagonal (fun i =>
            if i.1.2 = i.2.2.1 then (1 : ℂ) else 0) =
        Matrix.diagonal (fun i =>
          if i.1.2 = i.2.2.1 then (0 : ℂ) else 1) := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hcopy : i.1.2 = i.2.2.1 <;> simp [hcopy]
    · simp [hij]
  rw [hsub, Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases hcopy : i.1.2 = i.2.2.1 <;> simp [hcopy]

private theorem classicalCoherentMap_completelyPositive
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] :
    MatrixMap.IsCompletelyPositive
      (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')) := by
  exact MatrixMap.ofKraus_isCompletelyPositive _

private theorem classicalCoherentMap_traceNonincreasing
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] :
    MatrixMap.IsTraceNonincreasing
      (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')) := by
  intro M hM
  have hdual := MatrixMap.ofKraus_trace_duality
    (fun k : y' => classicalCoherentProjector
      (a := a) (x := x) (c := c) k) M
      (1 : CMatrix ((a × x) × (c × x × y')))
  rw [Matrix.mul_one] at hdual
  change ((MatrixMap.ofKraus (fun k : y' => classicalCoherentProjector
      (a := a) (x := x) (c := c) k) M).trace).re ≤ M.trace.re
  rw [hdual]
  have hcomp : (1 - MatrixMap.krausAdjoint (fun k : y' =>
      classicalCoherentProjector (a := a) (x := x) (c := c) k)
      (1 : CMatrix ((a × x) × (c × x × y')))).PosSemidef := by
    exact Matrix.le_iff.mp (classicalCoherentKrausAdjoint_sum_le_one
      (a := a) (x := x) (c := c) (y' := y'))
  have hnonneg := cMatrix_trace_mul_posSemidef_re_nonneg_schatten hM hcomp
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at hnonneg
  have hnonneg' : 0 ≤ (trace M).re -
      (M * MatrixMap.krausAdjoint (fun k : y' =>
        classicalCoherentProjector (a := a) (x := x) (c := c) k)
        (1 : CMatrix ((a × x) × (c × x × y')))).trace.re := by
    simpa only [Matrix.mul_one] using hnonneg
  exact sub_nonneg.mp hnonneg'

private def classicalCoherentMapTraceNonincreasingCP
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] :
    MatrixMap.TraceNonincreasingCP
      (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')) :=
  ⟨classicalCoherentMap_completelyPositive (a := a) (x := x) (c := c)
      (y' := y'),
    classicalCoherentMap_traceNonincreasing (a := a) (x := x) (c := c)
      (y' := y')⟩

private theorem classicalCoherentProjector_sandwich_apply
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] (k : y')
    (M : CMatrix ((a × x) × (c × x × y'))) (i j) :
    ((classicalCoherentProjector (a := a) (x := x) (c := c) k * M *
        classicalCoherentProjector (a := a) (x := x) (c := c) k :
        CMatrix ((a × x) × (c × x × y'))) i j) =
      if i.1.2 = i.2.2.1 ∧ i.2.2.2 = k ∧
          j.1.2 = j.2.2.1 ∧ j.2.2.2 = k then M i j else 0 := by
  rw [classicalCoherentProjector, Matrix.mul_assoc, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  by_cases hix : i.1.2 = i.2.2.1 <;>
    by_cases hik : i.2.2.2 = k <;>
    by_cases hjx : j.1.2 = j.2.2.1 <;>
    by_cases hjk : j.2.2.2 = k <;>
    simp [hix, hik, hjx, hjk]

private theorem classicalCoherentMap_apply
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (M : CMatrix ((a × x) × (c × x × y'))) (i j) :
    (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')) M i j =
      if i.1.2 = i.2.2.1 ∧ j.1.2 = j.2.2.1 ∧
          i.2.2.2 = j.2.2.2 then M i j else 0 := by
  rw [classicalCoherentMap, MatrixMap.ofKraus]
  change (∑ k : y',
      (classicalCoherentProjector (a := a) (x := x) (c := c) k) * M *
        (classicalCoherentProjector (a := a) (x := x) (c := c) k).conjTranspose) i j = _
  rw [Matrix.sum_apply]
  simp_rw [classicalCoherentProjector_conjTranspose
    (a := a) (x := x) (c := c)]
  simp_rw [classicalCoherentProjector_sandwich_apply]
  by_cases hcoord : i.1.2 = i.2.2.1 ∧ j.1.2 = j.2.2.1 ∧
      i.2.2.2 = j.2.2.2
  · rw [Finset.sum_eq_single i.2.2.2]
    · simp [hcoord]
    · intro k _ hk
      have hnot : ¬ (j.1.2 = j.2.2.1 ∧ j.2.2.2 = k) := by
        intro h
        apply hk
        exact (hcoord.2.2.trans h.2).symm
      simp [hnot]
    · simp
  · rw [if_neg hcoord]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hj : j.1.2 = j.2.2.1 ∧ j.2.2.2 = k
    · by_cases hi : i.1.2 = i.2.2.1 ∧ i.2.2.2 = k
      · exact False.elim (hcoord ⟨hi.1, hj.1, hi.2.trans hj.2.symm⟩)
      · simp [hj, hi]
    · simp [hj]

private def classicalCoherentOn
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (rho : SubnormalizedState ((a × x) × (c × x × y'))) : Prop :=
  ∀ i j, (i.1.2 ≠ i.2.2.1 ∨ j.1.2 ≠ j.2.2.1 ∨
    i.2.2.2 ≠ j.2.2.2) → rho.matrix i j = 0

/-! The source projector keeps the equality `X = X'` as a genuine
coordinate projection.  In particular, the Kraus index contains both the
copied classical value and the `Y'` value; using only the latter would leave
coherences between different `X` blocks. -/

private def sourceCoherentProjector
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] (p : x) (k : y') :
    CMatrix ((a × x) × (c × x × y')) :=
  Matrix.diagonal (fun i =>
    if i.1.2 = p ∧ i.2.2.1 = p ∧ i.2.2.2 = k then (1 : ℂ) else 0)

private def sourceCoherentMap
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] :
    MatrixMap ((a × x) × (c × x × y')) ((a × x) × (c × x × y')) :=
  MatrixMap.ofKraus (fun pk : x × y' =>
    sourceCoherentProjector (a := a) (x := x) (c := c) pk.1 pk.2)

omit [Fintype a] [Fintype x] in
private theorem sourceCoherentProjector_conjTranspose
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] (p : x) (k : y') :
    Matrix.conjTranspose
        (sourceCoherentProjector (a := a) (x := x) (c := c) p k) =
      sourceCoherentProjector (a := a) (x := x) (c := c) p k := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [sourceCoherentProjector]
  · simp [sourceCoherentProjector, Matrix.conjTranspose_apply,
       hij, Ne.symm hij]

private theorem sourceCoherentProjector_idempotent
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] (p : x) (k : y') :
    sourceCoherentProjector (a := a) (x := x) (c := c) p k *
        sourceCoherentProjector (a := a) (x := x) (c := c) p k =
      sourceCoherentProjector (a := a) (x := x) (c := c) p k := by
  rw [sourceCoherentProjector, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases h : i.1.2 = p ∧ i.2.2.1 = p ∧ i.2.2.2 = k <;> simp [h]
  · simp [hij]

private theorem sourceCoherentKrausAdjoint_sum_le_one
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] :
    MatrixMap.krausAdjoint (fun pk : x × y' =>
        sourceCoherentProjector (a := a) (x := x) (c := c) pk.1 pk.2)
      (1 : CMatrix ((a × x) × (c × x × y'))) ≤ 1 := by
  have hK : MatrixMap.krausAdjoint (fun pk : x × y' =>
      sourceCoherentProjector (a := a) (x := x) (c := c) pk.1 pk.2)
      (1 : CMatrix ((a × x) × (c × x × y'))) =
      Matrix.diagonal (fun i =>
        if i.1.2 = i.2.2.1 then (1 : ℂ) else 0) := by
    ext i j
    rw [MatrixMap.krausAdjoint]
    simp only [sourceCoherentProjector_conjTranspose
      (a := a) (x := x) (c := c), Matrix.mul_one]
    simp_rw [sourceCoherentProjector_idempotent
      (a := a) (x := x) (c := c)]
    rw [show (∑ pk : x × y', sourceCoherentProjector
        (a := a) (x := x) (c := c) pk.1 pk.2) i j =
        if i = j ∧ i.1.2 = i.2.2.1 then (1 : ℂ) else 0 by
      simp only [Matrix.sum_apply, sourceCoherentProjector,
        Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst j
        by_cases hcopy : i.1.2 = i.2.2.1
        · rw [Finset.sum_eq_single (i.1.2, i.2.2.2)]
          · simp [hcopy]
          · intro pk _ hpk
            have hnot : ¬ (i.2.2.1 = pk.1 ∧ i.2.2.2 = pk.2) := by
              intro h
              apply hpk
              exact Prod.ext (hcopy.trans h.1).symm h.2.symm
            simp [hcopy, hnot]
          · simp
        · have hcopy' : i.2.2.1 ≠ i.1.2 := Ne.symm hcopy
          simp [hcopy, hcopy']
      · simp [hij]]
    by_cases hij : i = j
    · subst j
      simp
    · simp [ hij]
  rw [hK, Matrix.le_iff]
  have hsub :
      (1 : CMatrix ((a × x) × (c × x × y'))) -
          Matrix.diagonal (fun i =>
            if i.1.2 = i.2.2.1 then (1 : ℂ) else 0) =
        Matrix.diagonal (fun i =>
          if i.1.2 = i.2.2.1 then (0 : ℂ) else 1) := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hcopy : i.1.2 = i.2.2.1 <;> simp [hcopy]
    · simp [hij]
  rw [hsub, Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases hcopy : i.1.2 = i.2.2.1 <;> simp [hcopy]

private theorem sourceCoherentMap_completelyPositive
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] :
    MatrixMap.IsCompletelyPositive
      (sourceCoherentMap (a := a) (x := x) (c := c) (y' := y')) := by
  exact MatrixMap.ofKraus_isCompletelyPositive _

private theorem sourceCoherentMap_traceNonincreasing
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] :
    MatrixMap.IsTraceNonincreasing
      (sourceCoherentMap (a := a) (x := x) (c := c) (y' := y')) := by
  intro M hM
  have hdual := MatrixMap.ofKraus_trace_duality
    (fun pk : x × y' => sourceCoherentProjector
      (a := a) (x := x) (c := c) pk.1 pk.2) M
      (1 : CMatrix ((a × x) × (c × x × y')))
  rw [Matrix.mul_one] at hdual
  change ((MatrixMap.ofKraus (fun pk : x × y' => sourceCoherentProjector
      (a := a) (x := x) (c := c) pk.1 pk.2) M).trace).re ≤ M.trace.re
  rw [hdual]
  have hcomp : (1 - MatrixMap.krausAdjoint (fun pk : x × y' =>
      sourceCoherentProjector (a := a) (x := x) (c := c) pk.1 pk.2)
      (1 : CMatrix ((a × x) × (c × x × y')))).PosSemidef := by
    exact Matrix.le_iff.mp (sourceCoherentKrausAdjoint_sum_le_one
      (a := a) (x := x) (c := c) (y' := y'))
  have hnonneg := cMatrix_trace_mul_posSemidef_re_nonneg_schatten hM hcomp
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at hnonneg
  have hnonneg' : 0 ≤ (trace M).re -
      (M * MatrixMap.krausAdjoint (fun pk : x × y' =>
        sourceCoherentProjector (a := a) (x := x) (c := c) pk.1 pk.2)
        (1 : CMatrix ((a × x) × (c × x × y')))).trace.re := by
    simpa only [Matrix.mul_one] using hnonneg
  exact sub_nonneg.mp hnonneg'

private def sourceCoherentMapTraceNonincreasingCP
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] :
    MatrixMap.TraceNonincreasingCP
      (sourceCoherentMap (a := a) (x := x) (c := c) (y' := y')) :=
  ⟨sourceCoherentMap_completelyPositive (a := a) (x := x) (c := c)
      (y' := y'),
    sourceCoherentMap_traceNonincreasing (a := a) (x := x) (c := c)
      (y' := y')⟩

private theorem sourceCoherentMap_apply
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (M : CMatrix ((a × x) × (c × x × y'))) (i j) :
    sourceCoherentMap (a := a) (x := x) (c := c) (y' := y') M i j =
      if i.1.2 = i.2.2.1 ∧ j.1.2 = j.2.2.1 ∧
          i.1.2 = j.1.2 ∧ i.2.2.2 = j.2.2.2 then M i j else 0 := by
  rw [sourceCoherentMap, MatrixMap.ofKraus]
  change (∑ pk : x × y',
      sourceCoherentProjector (a := a) (x := x) (c := c) pk.1 pk.2 * M *
        (sourceCoherentProjector (a := a) (x := x) (c := c) pk.1 pk.2).conjTranspose) i j = _
  rw [Matrix.sum_apply]
  simp_rw [sourceCoherentProjector_conjTranspose
    (a := a) (x := x) (c := c)]
  simp_rw [show ∀ (pk : x × y'),
      (sourceCoherentProjector (a := a) (x := x) (c := c) pk.1 pk.2 * M *
        sourceCoherentProjector (a := a) (x := x) (c := c) pk.1 pk.2) i j =
      if i.1.2 = pk.1 ∧ i.2.2.1 = pk.1 ∧ i.2.2.2 = pk.2 ∧
          j.1.2 = pk.1 ∧ j.2.2.1 = pk.1 ∧ j.2.2.2 = pk.2 then M i j else 0 by
    intro pk
    rw [sourceCoherentProjector, Matrix.mul_assoc, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    by_cases h1 : i.1.2 = pk.1 <;>
      by_cases h2 : i.2.2.1 = pk.1 <;>
      by_cases h3 : i.2.2.2 = pk.2 <;>
      by_cases h4 : j.1.2 = pk.1 <;>
      by_cases h5 : j.2.2.1 = pk.1 <;>
      by_cases h6 : j.2.2.2 = pk.2 <;>
      simp [h1, h2, h3, h4, h5, h6]]
  by_cases h : i.1.2 = i.2.2.1 ∧ j.1.2 = j.2.2.1 ∧
      i.1.2 = j.1.2 ∧ i.2.2.2 = j.2.2.2
  · rw [Finset.sum_eq_single (i.1.2, i.2.2.2)]
    · by_cases hsymm : j.2.2.1 = i.2.2.1
      · simp [h, hsymm]
      · simp [h, hsymm, Ne.symm hsymm]
    · intro pk _ hpk
      have hnot : ¬ (i.1.2 = pk.1 ∧ i.2.2.1 = pk.1 ∧
          i.2.2.2 = pk.2 ∧ j.1.2 = pk.1 ∧ j.2.2.1 = pk.1 ∧
          j.2.2.2 = pk.2) := by
        intro hall
        apply hpk
        rcases hall with ⟨hi1, hi2, hiy, hj1, hj2, hjy⟩
        exact Prod.ext hi1.symm hiy.symm
      simp [hnot]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro pk _
    by_cases hk : i.1.2 = pk.1 ∧ i.2.2.1 = pk.1 ∧ i.2.2.2 = pk.2 ∧
        j.1.2 = pk.1 ∧ j.2.2.1 = pk.1 ∧ j.2.2.2 = pk.2
    · exfalso
      apply h
      rcases hk with ⟨hi1, hi2, hiy, hj1, hj2, hjy⟩
      exact ⟨hi1.trans hi2.symm, hj1.trans hj2.symm,
        hi1.trans hj1.symm, hiy.trans hjy.symm⟩
    · simp [hk]

/-! Canonical purification with explicit `X'` and `Y'` copies. -/

private def xyABReindexEquiv :
    ((a × x) × (y × b)) ≃ ((x × y) × (a × b)) where
  toFun i := ((i.1.2, i.2.1), (i.1.1, i.2.2))
  invFun i := ((i.2.1, i.1.1), (i.1.2, i.2.2))
  left_inv i := by rcases i with ⟨⟨a, x⟩, ⟨y, b⟩⟩; rfl
  right_inv i := by rcases i with ⟨⟨x, y⟩, ⟨a, b⟩⟩; rfl

private def xyABReferenceEquiv :
    ((x × y) × (a × b)) ≃ ((a × b) × (x × y)) := Equiv.prodComm _ _

private def canonicalXYCoherentPurification
    (rho : State ((a × x) × (y × b))) :
    PureVector (Prod ((a × b) × (x × y)) ((a × x) × (y × b))) :=
  let rhoXY := rho.reindex (xyABReindexEquiv (a := a) (x := x) (y := y) (b := b))
  let psiXY := rhoXY.canonicalPurification
  let e := Equiv.prodCongr
    (xyABReferenceEquiv (a := a) (x := x) (y := y) (b := b))
    (xyABReindexEquiv (a := a) (x := x) (y := y) (b := b)).symm
  psiXY.reindex e

private theorem reindex_purifies_marginalB_prodCongr
    {r r' s s' : Type*} [Fintype r] [DecidableEq r]
    [Fintype r'] [DecidableEq r'] [Fintype s] [DecidableEq s]
    [Fintype s'] [DecidableEq s']
    (psi : PureVector (Prod r s)) (rho : State s)
    (hpsi : psi.Purifies rho) (er : r ≃ r') (es : s ≃ s') :
    (psi.reindex (Equiv.prodCongr er es)).Purifies (rho.reindex es) := by
  rw [PureVector.purifies_iff] at hpsi ⊢
  ext i j
  have hentry := congrArg (fun M : CMatrix s => M (es.symm i) (es.symm j)) hpsi
  have hsum :
      (∑ x : r, psi.amp (x, es.symm i) * star (psi.amp (x, es.symm j))) =
        ∑ x : r', psi.amp (er.symm x, es.symm i) *
          star (psi.amp (er.symm x, es.symm j)) := by
    exact Fintype.sum_equiv er _ _ (fun x => by simp)
  simpa [PureVector.reindex_state, State.reindex, partialTraceA,
    PureVector.state_matrix, rankOneMatrix_apply, Equiv.prodCongr] using
    (hsum.symm.trans hentry)

private theorem canonicalXYCoherentPurification_purifies
    (rho : State ((a × x) × (y × b))) :
    (canonicalXYCoherentPurification (a := a) (x := x) (y := y) (b := b) rho).Purifies rho := by
  let rhoXY := rho.reindex
    (xyABReindexEquiv (a := a) (x := x) (y := y) (b := b))
  let psiXY := rhoXY.canonicalPurification
  have hpsiXY : psiXY.Purifies rhoXY :=
    State.canonicalPurification_purifies rhoXY
  have h := reindex_purifies_marginalB_prodCongr psiXY rhoXY hpsiXY
    (xyABReferenceEquiv (a := a) (x := x) (y := y) (b := b))
    (xyABReindexEquiv (a := a) (x := x) (y := y) (b := b)).symm
  have hback :
      rhoXY.reindex
          (xyABReindexEquiv (a := a) (x := x) (y := y) (b := b)).symm = rho := by
    apply State.ext
    ext i j
    simp [rhoXY, State.reindex, xyABReindexEquiv]
  simpa [canonicalXYCoherentPurification, rhoXY, psiXY, hback] using h

private def canonicalXYComplementaryState
    (rho : State ((a × x) × (y × b))) :
    State ((a × x) × ((a × b) × (x × y))) :=
  State.acMarginalFromABPurification
    (canonicalXYCoherentPurification (a := a) (x := x) (y := y) (b := b) rho)

private theorem reindexed_classical_blockDiagonal
    (rho : State ((a × x) × (y × b)))
    (hclassical : (rho.toSubnormalized).classicalOnXY) :
    let rhoXY := rho.reindex
      (xyABReindexEquiv (a := a) (x := x) (y := y) (b := b))
    rhoXY.matrix = Classical.blockDiagonal (fun q : x × y =>
      Classical.block rhoXY.matrix q q) := by
  dsimp
  let rhoXY := rho.reindex
    (xyABReindexEquiv (a := a) (x := x) (y := y) (b := b))
  have hxy : ∀ i j : (x × y) × (a × b), i.1 ≠ j.1 → rhoXY.matrix i j = 0 := by
    intro i j hij
    rcases i with ⟨⟨xi, yi⟩, ⟨ai, bi⟩⟩
    rcases j with ⟨⟨xj, yj⟩, ⟨aj, bj⟩⟩
    by_cases hx : xi ≠ xj
    · have hz := hclassical.1
        ((xyABReindexEquiv (a := a) (x := x) (y := y) (b := b)).symm
          ((xi, yi), (ai, bi)))
        ((xyABReindexEquiv (a := a) (x := x) (y := y) (b := b)).symm
          ((xj, yj), (aj, bj))) hx
      simpa [rhoXY, State.reindex_matrix, xyABReindexEquiv] using hz
    · have hy : yi ≠ yj := by
        intro h
        apply hij
        exact Prod.ext (not_ne_iff.mp hx) h
      have hz := hclassical.2
        ((xyABReindexEquiv (a := a) (x := x) (y := y) (b := b)).symm
          ((xi, yi), (ai, bi)))
        ((xyABReindexEquiv (a := a) (x := x) (y := y) (b := b)).symm
          ((xj, yj), (aj, bj))) hy
      simpa [rhoXY, State.reindex_matrix, xyABReindexEquiv] using hz
  ext ⟨q, i⟩ ⟨q', j⟩
  change rhoXY.matrix (q, i) (q', j) =
    Classical.blockDiagonal (fun q : x × y => Classical.block rhoXY.matrix q q)
      (q, i) (q', j)
  by_cases hq : q = q'
  · subst q'
    change rhoXY.matrix (q, i) (q, j) =
      (Classical.block (Classical.blockDiagonal
        (fun q : x × y => Classical.block rhoXY.matrix q q)) q q) i j
    rw [Classical.blockDiagonal_block_self]
    rfl
  · have hz := hxy (q, i) (q', j) hq
    change rhoXY.matrix (q, i) (q', j) =
      (Classical.block (Classical.blockDiagonal
        (fun q : x × y => Classical.block rhoXY.matrix q q)) q q') i j
    rw [Classical.blockDiagonal_block_ne _ hq]
    simp [hz]

private theorem canonicalXYCoherentPurification_amp_zero_of_copy_mismatch
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY)
    (r : (a × b) × (x × y)) (i : (a × x) × (y × b))
    (hcopy : r.2 ≠ (i.1.2, i.2.1)) :
    (canonicalXYCoherentPurification (a := a) (x := x) (y := y) (b := b) rho).amp
      (r, i) = 0 := by
  let rhoXY := rho.reindex
    (xyABReindexEquiv (a := a) (x := x) (y := y) (b := b))
  have hblock := reindexed_classical_blockDiagonal
    (a := a) (x := x) (y := y) (b := b) rho hclassical
  have hblock' : rhoXY.matrix = Classical.blockDiagonal (fun q : x × y =>
      Classical.block rhoXY.matrix q q) := by
    simpa [rhoXY] using hblock
  have hsqrt := Classical.blockDiagonal_psdSqrt
    (fun q : x × y => Classical.block rhoXY.matrix q q)
    (fun q => by
      exact Matrix.PosSemidef.submatrix rhoXY.pos (fun i => (q, i)))
  have hsqrt' : rhoXY.sqrtMatrix = Classical.blockDiagonal (fun q : x × y =>
      psdSqrt (Classical.block rhoXY.matrix q q)) := by
    rw [State.sqrtMatrix, hblock']
    simpa only [Classical.blockDiagonal_block_self] using hsqrt
  change rhoXY.sqrtMatrix ((i.1.2, i.2.1), (i.1.1, i.2.2)) r.swap = 0
  rw [hsqrt']
  simp only [Classical.blockDiagonal]
  rw [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro q _hq
  by_cases hq : q = (i.1.2, i.2.1)
  · subst q
    simp [Matrix.single]
    intro h
    exact (hcopy h.symm).elim
  · simp [hq]

private theorem canonicalXYComplementaryState_classicalCoherentOn
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    classicalCoherentOn
      (canonicalXYComplementaryState (a := a) (x := x) (y := y) (b := b) rho
        |>.toSubnormalized) := by
  intro i j hij
  change (canonicalXYComplementaryState
      (a := a) (x := x) (y := y) (b := b) rho).matrix i j = 0
  simp [canonicalXYComplementaryState, State.acMarginalFromABPurification,
     State.marginalB,
    PureVector.state_matrix, partialTraceA, rankOneMatrix_apply,
    PureVector.reindex]
  apply Finset.sum_eq_zero
  intro k _hk
  by_cases hxi : i.1.2 ≠ i.2.2.1
  · apply mul_eq_zero.mpr
    left
    have hcopyi : i.2.2 ≠ (i.1.2, k.1) := by
      intro h
      have hx : i.2.2.1 = i.1.2 := by
        simpa using congrArg Prod.fst h
      exact hxi hx.symm
    have hz := canonicalXYCoherentPurification_amp_zero_of_copy_mismatch
      (a := a) (x := x) (y := y) (b := b) rho hclassical
      i.2 (i.1, k) hcopyi
    simpa [State.abToACReferenceEquiv] using hz
  · by_cases hxj : j.1.2 ≠ j.2.2.1
    · apply mul_eq_zero.mpr
      right
      have hcopyj : j.2.2 ≠ (j.1.2, k.1) := by
        intro h
        have hx : j.2.2.1 = j.1.2 := by
          simpa using congrArg Prod.fst h
        exact hxj hx.symm
      have hz := canonicalXYCoherentPurification_amp_zero_of_copy_mismatch
        (a := a) (x := x) (y := y) (b := b) rho hclassical
        j.2 (j.1, k) hcopyj
      simpa [State.abToACReferenceEquiv] using hz
    · by_cases hy : i.2.2.2 ≠ j.2.2.2
      · by_cases hk : k.1 = i.2.2.2
        · apply mul_eq_zero.mpr
          right
          have hcopyj : j.2.2 ≠ (j.1.2, k.1) := by
            intro h
            exact hy (hk.symm.trans (congrArg Prod.snd h).symm)
          have hz := canonicalXYCoherentPurification_amp_zero_of_copy_mismatch
            (a := a) (x := x) (y := y) (b := b) rho hclassical
            j.2 (j.1, k) hcopyj
          simpa [State.abToACReferenceEquiv] using hz
        · apply mul_eq_zero.mpr
          left
          have hcopyi : i.2.2 ≠ (i.1.2, k.1) := by
            intro h
            exact hk (by simpa using (congrArg Prod.snd h).symm)
          have hz := canonicalXYCoherentPurification_amp_zero_of_copy_mismatch
            (a := a) (x := x) (y := y) (b := b) rho hclassical
            i.2 (i.1, k) hcopyi
          simpa [State.abToACReferenceEquiv] using hz
      · rcases hij with hi | hj | hyy
        · exact (hxi hi).elim
        · exact (hxj hj).elim
        · exact (hy hyy).elim

/-! The following amplitude lift is the purification part of the source
proof.  It copies the already-classical `Y'` coordinate into the reference;
the Gram and overlap identities are kept explicit so that no normalized-state
shortcut is used. -/

private def coherentLiftAmplitude
  {r : Type*} [Fintype r] [DecidableEq r]
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
  (Psi : PureVector (Prod r ((a × x) × (c × x × y')))) :
    Matrix ((a × x) × (c × x × y')) (r × y') ℂ :=
  fun i rk => if i.1.2 = i.2.2.1 ∧ i.2.2.2 = rk.2 then
      Psi.amplitudeMatrix i rk.1 else 0

private theorem coherentLiftAmplitude_gram
    {r : Type*} [Fintype r] [DecidableEq r]
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (Psi : PureVector (Prod r ((a × x) × (c × x × y'))))
    (hfixed : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) =
      Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) :
    coherentLiftAmplitude (a := a) (x := x) Psi *
        (coherentLiftAmplitude (a := a) (x := x) Psi).conjTranspose =
      Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    coherentLiftAmplitude]
  rw [Fintype.sum_prod_type]
  by_cases hcopyi : i.1.2 = i.2.2.1
  · by_cases hcopyj : j.1.2 = j.2.2.1
    · by_cases hy : i.2.2.2 = j.2.2.2
      · simp [hcopyi, hcopyj, hy]
      · have hentry := congrArg
          (fun M : CMatrix ((a × x) × (c × x × y')) => M i j) hfixed
        have hy' : j.2.2.2 ≠ i.2.2.2 := fun h => hy h.symm
        change classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
            (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) i j =
          (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) i j at hentry
        rw [classicalCoherentMap_apply] at hentry
        simp [hcopyi, hcopyj, hy] at hentry ⊢
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
          PureVector.amplitudeMatrix, hcopyi, hcopyj, hy, hy'] using hentry
    · have hentry := congrArg
        (fun M : CMatrix ((a × x) × (c × x × y')) => M i j) hfixed
      change classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
          (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) i j =
        (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) i j at hentry
      rw [classicalCoherentMap_apply] at hentry
      simp [hcopyi, hcopyj] at hentry ⊢
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
        PureVector.amplitudeMatrix, hcopyi, hcopyj] using hentry
  · have hentry := congrArg
      (fun M : CMatrix ((a × x) × (c × x × y')) => M i j) hfixed
    change classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
        (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) i j =
      (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) i j at hentry
    rw [classicalCoherentMap_apply] at hentry
    simp [hcopyi] at hentry ⊢
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
      PureVector.amplitudeMatrix, hcopyi] using hentry

private theorem coherentLiftAmplitude_trace
    {r : Type*} [Fintype r] [DecidableEq r]
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (Psi : PureVector (Prod r ((a × x) × (c × x × y'))))
    (hfixed : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) =
      Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) :
    (coherentLiftAmplitude (a := a) (x := x) Psi *
        (coherentLiftAmplitude (a := a) (x := x) Psi).conjTranspose).trace = 1 := by
  rw [coherentLiftAmplitude_gram Psi hfixed]
  calc
    (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose).trace =
        ∑ i : (a × x) × (c × x × y'), ∑ j : r,
          Psi.amplitudeMatrix i j * star (Psi.amplitudeMatrix i j) := by
      simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]
    _ = ∑ j : r, ∑ i : (a × x) × (c × x × y'),
          Psi.amplitudeMatrix i j * star (Psi.amplitudeMatrix i j) := by
      rw [Finset.sum_comm]
    _ = (rankOneMatrix Psi.amp).trace := by
      simp [PureVector.amplitudeMatrix, Matrix.trace, rankOneMatrix_apply,
        Fintype.sum_prod_type]
    _ = 1 := Psi.trace_rankOne_eq_one

private def coherentLiftOfFixed
    {r : Type*} [Fintype r] [DecidableEq r]
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (Psi : PureVector (Prod r ((a × x) × (c × x × y'))))
    (hfixed : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) =
      Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) :
    PureVector (Prod (r × y') ((a × x) × (c × x × y'))) :=
  PureVector.ofAmplitudeMatrix (coherentLiftAmplitude (a := a) (x := x) Psi)
    (coherentLiftAmplitude_trace Psi hfixed)

private theorem coherentLiftOfFixed_target_matrix
    {r : Type*} [Fintype r] [DecidableEq r]
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (Psi : PureVector (Prod r ((a × x) × (c × x × y'))))
    (hfixed : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) =
      Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) :
    (coherentLiftOfFixed Psi hfixed).state.marginalB.matrix =
      Psi.state.marginalB.matrix := by
  rw [State.marginalB_matrix, State.marginalB_matrix]
  rw [PureVector.state_matrix, PureVector.state_matrix]
  rw [PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose,
    PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose]
  simp [coherentLiftOfFixed, PureVector.ofAmplitudeMatrix_amplitudeMatrix]
  exact coherentLiftAmplitude_gram Psi hfixed

private theorem coherentLift_row_zero_of_not_copy
    {r : Type*} [Fintype r] [DecidableEq r]
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (Psi : PureVector (Prod r ((a × x) × (c × x × y'))))
    (hfixed : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) =
      Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose)
    {i : (a × x) × (c × x × y')}
    (hi : i.1.2 ≠ i.2.2.1) :
    ∀ r₁, Psi.amplitudeMatrix i r₁ = 0 := by
  intro r₁
  have hentry := congrArg
      (fun M : CMatrix ((a × x) × (c × x × y')) => M i i) hfixed
  change classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) i i =
    (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) i i at hentry
  rw [classicalCoherentMap_apply] at hentry
  simp [hi] at hentry
  have hzero : (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) i i = 0 :=
    hentry.symm
  have hsum : ∑ r₂ : r,
      (Psi.amplitudeMatrix i r₂ * star (Psi.amplitudeMatrix i r₂)).re = 0 := by
    have := congrArg Complex.re hzero
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_re] using this
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun r₂ _ => by
        simpa [Complex.mul_re] using
          (Complex.normSq_nonneg (Psi.amplitudeMatrix i r₂)))).mp
      hsum r₁ (Finset.mem_univ r₁)
  have hzprod :
      Psi.amplitudeMatrix i r₁ * star (Psi.amplitudeMatrix i r₁) = 0 := by
    apply Complex.ext
    · exact hterm
    · rw [Complex.mul_im]
      change (Psi.amplitudeMatrix i r₁).re *
          (-(Psi.amplitudeMatrix i r₁).im) +
          (Psi.amplitudeMatrix i r₁).im *
            (Psi.amplitudeMatrix i r₁).re = 0
      ring
  exact (CStarRing.mul_star_self_eq_zero_iff _).mp hzprod

private theorem coherentLiftAmplitude_overlap
    {r : Type*} [Fintype r] [DecidableEq r]
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (Psi Phi : PureVector (Prod r ((a × x) × (c × x × y'))))
    (hPsi : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) =
      Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose)
    (hPhi : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) =
      Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) :
    (Matrix.conjTranspose (coherentLiftAmplitude (a := a) (x := x) Psi) *
        coherentLiftAmplitude (a := a) (x := x) Phi).trace =
      (Matrix.conjTranspose Psi.amplitudeMatrix * Phi.amplitudeMatrix).trace := by
  simp only [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.diag, coherentLiftAmplitude]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr (M := ℂ)
    (s₁ := Finset.univ) (s₂ := Finset.univ) rfl ?_
  intro r₁ hr₁
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hcopy : i.1.2 = i.2.2.1
  · rw [Finset.sum_eq_single i.2.2.2]
    · simp [hcopy]
    · intro k hk hne
      have hne' : i.2.2.2 ≠ k := Ne.symm hne
      simp [hcopy, hne']
    · simp
  · have hP := coherentLift_row_zero_of_not_copy Psi hPsi hcopy
    have hQ := coherentLift_row_zero_of_not_copy Phi hPhi hcopy
    have hP' := hP r₁
    have hQ' := hQ r₁
    simp only [PureVector.amplitudeMatrix] at hP' hQ'
    simp [hcopy, hP', hQ']

private theorem coherentLiftOfFixed_overlap
    {r : Type*} [Fintype r] [DecidableEq r]
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (Psi Phi : PureVector (Prod r ((a × x) × (c × x × y'))))
    (hPsi : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) =
      Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose)
    (hPhi : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) =
      Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) :
    (coherentLiftOfFixed Psi hPsi).overlap (coherentLiftOfFixed Phi hPhi) =
      Psi.overlap Phi := by
  rw [PureVector.overlap_eq_trace_conjTranspose_amplitudeMatrix_mul,
    PureVector.overlap_eq_trace_conjTranspose_amplitudeMatrix_mul]
  simp [coherentLiftOfFixed, PureVector.ofAmplitudeMatrix_amplitudeMatrix]
  exact coherentLiftAmplitude_overlap Psi Phi hPsi hPhi

/-! Reordering the lifted reference turns the `AC` purification from the
source duality route into an `AX|YB` purification. -/

private def coherentMaxSwapEquiv
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] :
    Prod (c × x × y') (Prod (a × x) (b × y')) ≃
      Prod (c × x × y') (Prod (a × x) (y' × b)) where
  toFun t := (t.1, (t.2.1, (t.2.2.2, t.2.2.1)))
  invFun t := (t.1, (t.2.1, (t.2.2.2, t.2.2.1)))
  left_inv := by intro t; cases t with | mk cax ab => cases cax; cases ab; rfl
  right_inv := by intro t; cases t with | mk cax yb => cases cax; cases yb; rfl

private def coherentMaxPure
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (Phi : PureVector (Prod b ((a × x) × (c × x × y'))))
    (hfixed : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) =
      Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) :
    PureVector (Prod ((a × x) × (y' × b)) (c × x × y')) := by
  let lifted := coherentLiftOfFixed (a := a) (x := x) Phi hfixed
  let e₁ := State.acToABReferenceEquiv (b × y') (a × x) (c × x × y')
  let e₂ := coherentMaxSwapEquiv (a := a) (x := x) (b := b) (c := c) (y' := y')
  let e₃ := Equiv.prodComm (c × x × y') ((a × x) × (y' × b))
  exact (lifted.reindex (e₁.trans e₂)).reindex e₃

private theorem coherentMaxPure_amp_X
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (Phi : PureVector (Prod b ((a × x) × (c × x × y'))))
    (hfixed : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) =
      Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose)
    (i j : (a × x) × (y' × b)) (hij : i.1.2 ≠ j.1.2) :
    ∑ k : c × x × y',
      (coherentMaxPure (a := a) (x := x) (b := b) Phi hfixed).amp (i, k) *
        star ((coherentMaxPure (a := a) (x := x) (b := b) Phi hfixed).amp (j, k)) = 0 := by
  classical
  simp [coherentMaxPure, coherentLiftOfFixed, coherentLiftAmplitude,
    State.acToABReferenceEquiv, coherentMaxSwapEquiv, PureVector.reindex,
    PureVector.ofAmplitudeMatrix,
    Equiv.prodComm]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hi : i.1.2 = k.2.1 ∧ k.2.2 = i.2.1
  · by_cases hj : j.1.2 = k.2.1 ∧ k.2.2 = j.2.1
    · exact (hij (hi.1.trans hj.1.symm)).elim
    · rw [if_pos hi, if_neg hj]
      simp
  · rw [if_neg hi]

private theorem coherentMaxPure_amp_Y
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (Phi : PureVector (Prod b ((a × x) × (c × x × y'))))
    (hfixed : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) =
      Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose)
    (i j : (a × x) × (y' × b)) (hij : i.2.1 ≠ j.2.1) :
    ∑ k : c × x × y',
      (coherentMaxPure (a := a) (x := x) (b := b) Phi hfixed).amp (i, k) *
        star ((coherentMaxPure (a := a) (x := x) (b := b) Phi hfixed).amp (j, k)) = 0 := by
  classical
  simp [coherentMaxPure, coherentLiftOfFixed, coherentLiftAmplitude,
    State.acToABReferenceEquiv, coherentMaxSwapEquiv, PureVector.reindex,
    PureVector.ofAmplitudeMatrix,
    Equiv.prodComm]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hi : i.1.2 = k.2.1 ∧ k.2.2 = i.2.1
  · by_cases hj : j.1.2 = k.2.1 ∧ k.2.2 = j.2.1
    · exact (hij (hi.2.symm.trans hj.2)).elim
    · rw [if_pos hi, if_neg hj]
      simp
  · rw [if_neg hi]

private theorem coherentMaxPure_acMarginal
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (Phi : PureVector (Prod b ((a × x) × (c × x × y'))))
    (hfixed : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) =
      Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) :
    (coherentMaxPure (a := a) (x := x) (b := b) Phi hfixed).state.marginalAC =
      Phi.state.marginalB := by
  apply State.ext
  ext i j
  simp [coherentMaxPure, coherentLiftOfFixed, coherentLiftAmplitude,
    State.acToABReferenceEquiv, coherentMaxSwapEquiv, PureVector.reindex,

    State.marginalB, partialTraceA, PureVector.state_matrix,
    rankOneMatrix_apply, PureVector.ofAmplitudeMatrix,
    Equiv.prodComm]
  rw [Fintype.sum_prod_type]
  by_cases hcopyi : i.1.2 = i.2.2.1
  · by_cases hcopyj : j.1.2 = j.2.2.1
    · by_cases hy : i.2.2.2 = j.2.2.2
      · simp [hcopyi, hcopyj, hy]
      · have hentry := congrArg
          (fun M : CMatrix ((a × x) × (c × x × y')) => M i j) hfixed
        change classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
            (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) i j =
          (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) i j at hentry
        rw [classicalCoherentMap_apply] at hentry
        simp [hcopyi, hcopyj, hy] at hentry ⊢
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
          PureVector.amplitudeMatrix, hcopyi, hcopyj, hy,
          Ne.symm hy] using hentry
    · have hentry := congrArg
          (fun M : CMatrix ((a × x) × (c × x × y')) => M i j) hfixed
      change classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
          (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) i j =
        (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) i j at hentry
      rw [classicalCoherentMap_apply] at hentry
      simp [hcopyi, hcopyj] at hentry ⊢
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
        PureVector.amplitudeMatrix, hcopyi, hcopyj] using hentry
  · have hentry := congrArg
        (fun M : CMatrix ((a × x) × (c × x × y')) => M i j) hfixed
    change classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
        (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) i j =
      (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) i j at hentry
    rw [classicalCoherentMap_apply] at hentry
    simp [hcopyi] at hentry ⊢
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
      PureVector.amplitudeMatrix, hcopyi] using hentry

private theorem coherentMaxPure_complementaryPureMarginalRel
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (Phi : PureVector (Prod b ((a × x) × (c × x × y'))))
    (hfixed : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) =
      Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) :
    ComplementaryPureMarginalRel
      (a := a × x) (b := y' × b) (c := c × x × y')
      (coherentMaxPure (a := a) (x := x) (b := b) Phi hfixed).state.marginalA.toSubnormalized
      Phi.state.marginalB.toSubnormalized := by
  let Omega := coherentMaxPure (a := a) (x := x) (b := b) Phi hfixed
  refine ⟨Omega, 1, by norm_num, by norm_num, ?_, ?_⟩
  · apply SubnormalizedState.ext
    simp [Omega, abMarginalFromScaledTripartitePure, SubnormalizedState.ofStateScale,
      State.toSubnormalized_matrix, State.marginalAB_eq_marginalA]
  · apply SubnormalizedState.ext
    simp [Omega, acMarginalFromScaledTripartitePure, SubnormalizedState.ofStateScale,
      State.toSubnormalized_matrix, coherentMaxPure_acMarginal (a := a) (x := x)
        (b := b) Phi hfixed]

private theorem coherentMaxPure_scaledComplementaryPureMarginalRel
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (Phi : PureVector (Prod b ((a × x) × (c × x × y'))))
    (hfixed : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) =
      Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    ComplementaryPureMarginalRel
      (a := a × x) (b := y' × b) (c := c × x × y')
      (SubnormalizedState.ofStateScale
        (coherentMaxPure (a := a) (x := x) (b := b) Phi hfixed).state.marginalA
        t ht.le ht1)
      (SubnormalizedState.ofStateScale Phi.state.marginalB t ht.le ht1) := by
  let Omega := coherentMaxPure (a := a) (x := x) (b := b) Phi hfixed
  refine ⟨Omega, t, ht, ht1, ?_, ?_⟩
  · apply SubnormalizedState.ext
    simp [Omega, abMarginalFromScaledTripartitePure, SubnormalizedState.ofStateScale,
       State.marginalAB_eq_marginalA]
  · apply SubnormalizedState.ext
    simp [Omega, acMarginalFromScaledTripartitePure, SubnormalizedState.ofStateScale,
       coherentMaxPure_acMarginal (a := a) (x := x)
        (b := b) Phi hfixed]

private theorem coherentMaxPure_overlapSq
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (Psi Phi : PureVector (Prod b ((a × x) × (c × x × y'))))
    (hPsi : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) =
      Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose)
    (hPhi : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) =
      Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) :
    (coherentMaxPure (a := a) (x := x) (b := b) Psi hPsi).overlapSq
        (coherentMaxPure (a := a) (x := x) (b := b) Phi hPhi) =
      Psi.overlapSq Phi := by
  rw [coherentMaxPure, coherentMaxPure]
  rw [PureVector.overlapSq_reindex, PureVector.overlapSq_reindex]
  exact congrArg Complex.normSq (coherentLiftOfFixed_overlap Psi Phi hPsi hPhi)

private theorem classicalMaxCandidate_of_coherent_purifications
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    [Nonempty a] [Nonempty x] [Nonempty b] [Nonempty c] [Nonempty y']
    (center : State ((a × x) × (y' × b)))
    (etaCenter eta : State ((a × x) × (c × x × y')))
    (Psi Phi : PureVector (Prod b ((a × x) × (c × x × y'))))
    (hPsi : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) =
      Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose)
    (hPhi : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) =
      Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose)
    (hPhiEta : Phi.state.marginalB = eta)
    (hPsiCenter :
      (coherentMaxPure (a := a) (x := x) (b := b) Psi hPsi).state.marginalA = center)
    {ε : ℝ}
    (hball : etaCenter.toSubnormalized.purifiedBall ε eta.toSubnormalized)
    (hoverlap : Psi.overlapSq Phi = etaCenter.squaredFidelity eta) :
    ∃ tau : SubnormalizedState ((a × x) × (y' × b)),
      center.toSubnormalized.purifiedBall ε tau ∧ tau.classicalOnXY ∧
        tau.conditionalMaxEntropyRaw =
          -eta.toSubnormalized.conditionalMinEntropyRaw := by
  let PsiMax := coherentMaxPure (a := a) (x := x) (b := b) Psi hPsi
  let PhiMax := coherentMaxPure (a := a) (x := x) (b := b) Phi hPhi
  have hη : etaCenter.purifiedBall ε eta :=
    (State.purifiedBall_iff_toSubnormalized_purifiedBall
      etaCenter eta ε).mpr hball
  have hF : etaCenter.squaredFidelity eta ≤ PsiMax.state.squaredFidelity PhiMax.state := by
    calc
      etaCenter.squaredFidelity eta = Psi.overlapSq Phi := hoverlap.symm
      _ = PsiMax.overlapSq PhiMax :=
        (coherentMaxPure_overlapSq (a := a) (x := x) (b := b)
          Psi Phi hPsi hPhi).symm
      _ ≤ PsiMax.state.squaredFidelity PhiMax.state :=
        PureVector.overlapSq_le_state_squaredFidelity PsiMax PhiMax
  have hstateBall : PsiMax.state.purifiedBall ε PhiMax.state :=
    State.purifiedBall_of_squaredFidelity_le hF hη
  have hmarginBall : center.purifiedBall ε PhiMax.state.marginalA := by
    have hm := State.purifiedBall_marginalA_of_purifiedBall hstateBall
    rw [hPsiCenter] at hm
    exact hm
  let tau : SubnormalizedState ((a × x) × (y' × b)) :=
    PhiMax.state.marginalA.toSubnormalized
  have htauX : tau.classicalOnX := by
    intro i j hij
    change PhiMax.state.marginalA.matrix i j = 0
    rw [State.marginalA_matrix]
    simp only [partialTraceB, PureVector.state_matrix,
      rankOneMatrix_apply]
    exact coherentMaxPure_amp_X (a := a) (x := x) (b := b) Phi hPhi i j hij
  have htauY : tau.classicalOnY := by
    intro i j hij
    change PhiMax.state.marginalA.matrix i j = 0
    rw [State.marginalA_matrix]
    simp only [partialTraceB, PureVector.state_matrix,
      rankOneMatrix_apply]
    exact coherentMaxPure_amp_Y (a := a) (x := x) (b := b) Phi hPhi i j hij
  have hrel := coherentMaxPure_complementaryPureMarginalRel
    (a := a) (x := x) (b := b) Phi hPhi
  have hent :=
    (conditionalMinMaxEntropyDualOn_complementaryPureMarginals
      (a := a × x) (b := y' × b) (c := c × x × y'))
      tau eta.toSubnormalized (by simpa [tau, PhiMax, hPhiEta] using hrel)
  refine ⟨tau, ?_, ⟨htauX, htauY⟩, hent⟩
  exact (State.purifiedBall_iff_toSubnormalized_purifiedBall
    center PhiMax.state.marginalA ε).mp hmarginBall

private theorem classicalCoherentMap_classicalCoherentOn
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (rho : SubnormalizedState ((a × x) × (c × x × y'))) :
    classicalCoherentOn (rho.applyTraceNonincreasingCP
      (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y'))
      (classicalCoherentMapTraceNonincreasingCP
        (a := a) (x := x) (c := c) (y' := y'))) := by
  intro i j hij
  by_cases hcopyi : i.1.2 = i.2.2.1
  · by_cases hcopyj : j.1.2 = j.2.2.1
    · by_cases hy : i.2.2.2 = j.2.2.2
      · rcases hij with hij | hij | hij
        · exact (hij hcopyi).elim
        · exact (hij hcopyj).elim
        · exact (hij hy).elim
      · simp [SubnormalizedState.applyTraceNonincreasingCP,
          classicalCoherentMap_apply, hcopyi, hcopyj, hy]
    · simp [SubnormalizedState.applyTraceNonincreasingCP,
        classicalCoherentMap_apply, hcopyi, hcopyj]
  · simp [SubnormalizedState.applyTraceNonincreasingCP,
      classicalCoherentMap_apply, hcopyi]

private theorem classicalCoherentMap_fixed
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    {rho : SubnormalizedState ((a × x) × (c × x × y'))}
    (hclassical : classicalCoherentOn rho) :
    rho.applyTraceNonincreasingCP
      (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y'))
      (classicalCoherentMapTraceNonincreasingCP
        (a := a) (x := x) (c := c) (y' := y')) = rho := by
  apply SubnormalizedState.ext
  ext i j
  simp only [SubnormalizedState.applyTraceNonincreasingCP, classicalCoherentMap_apply]
  by_cases hcopyi : i.1.2 = i.2.2.1
  · by_cases hcopyj : j.1.2 = j.2.2.1
    · by_cases hy : i.2.2.2 = j.2.2.2
      · simp [hcopyi, hcopyj, hy]
      · have hz := hclassical i j (Or.inr (Or.inr hy))
        rw [if_neg]
        · exact hz.symm
        · intro hall
          exact hy hall.2.2
    · have hz := hclassical i j (Or.inr (Or.inl hcopyj))
      rw [if_neg]
      · exact hz.symm
      · intro hall
        exact hcopyj hall.2.1
  · have hz := hclassical i j (Or.inl hcopyi)
    rw [if_neg]
    · exact hz.symm
    · intro hall
      exact hcopyi hall.1

private theorem pureVector_classicalCoherent_fixed
    {r : Type*} [Fintype r] [DecidableEq r]
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (Phi : PureVector (Prod r ((a × x) × (c × x × y'))))
    (eta : State ((a × x) × (c × x × y')))
    (hPhi : Phi.Purifies eta)
    (hclassical : classicalCoherentOn eta.toSubnormalized) :
    classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
        (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) =
      Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose := by
  have hmarg : Phi.state.marginalB = eta := by
    apply State.ext
    simpa [State.marginalB_matrix] using hPhi
  have hgram :
      (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose :
        CMatrix ((a × x) × (c × x × y'))) =
      Phi.state.marginalB.matrix := by
    rw [State.marginalB_matrix, PureVector.state_matrix,
      PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose]
  change classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) =
    Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose
  rw [hgram, hmarg]
  have hfixed := classicalCoherentMap_fixed (a := a) (x := x)
    (c := c) (y' := y') hclassical
  have hfixedMatrix := congrArg SubnormalizedState.matrix hfixed
  simpa [SubnormalizedState.applyTraceNonincreasingCP_matrix] using hfixedMatrix

private theorem purifiedBall_classicalCoherentMap_of_classical_center
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    {rho sigma : SubnormalizedState ((a × x) × (c × x × y'))} {epsilon : ℝ}
    (hclassical : classicalCoherentOn rho)
    (hball : rho.purifiedBall epsilon sigma) :
    rho.purifiedBall epsilon
      (sigma.applyTraceNonincreasingCP
        (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y'))
        (classicalCoherentMapTraceNonincreasingCP
          (a := a) (x := x) (c := c) (y' := y'))) := by
  have hpinched := SubnormalizedState.purifiedBall_of_traceNonincreasingCP
    (ρ := rho) (σ := sigma) (ε := epsilon)
    (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y'))
    (classicalCoherentMapTraceNonincreasingCP
      (a := a) (x := x) (c := c) (y' := y')) hball
  change (rho.applyTraceNonincreasingCP
      (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y'))
      (classicalCoherentMapTraceNonincreasingCP
        (a := a) (x := x) (c := c) (y' := y'))).purifiedBall epsilon _ at hpinched
  rw [classicalCoherentMap_fixed hclassical] at hpinched
  exact hpinched

private def classicalCoherentConditioningProjector
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] (k : x × y') :
    CMatrix (c × x × y') :=
  Matrix.diagonal (fun i => if i.2 = k then (1 : ℂ) else 0)

private def classicalCoherentConditioningMeasurement
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] :
    ProjectiveMeasurement (x × y') (c × x × y') where
  effects := classicalCoherentConditioningProjector
  isHermitian := by
    intro k
    rw [Matrix.IsHermitian]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [classicalCoherentConditioningProjector]
    · simp [classicalCoherentConditioningProjector,
        Matrix.conjTranspose_apply, hij, Ne.symm hij]
  idempotent := by
    intro k
    rw [classicalCoherentConditioningProjector, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases h : i.2 = k <;> simp [h]
    · simp [hij]
  orthogonal := by
    intro k l hkl
    rw [classicalCoherentConditioningProjector,
      classicalCoherentConditioningProjector, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hik : i.2 = k
      · have hkl' : k ≠ l := hkl
        have hil : i.2 ≠ l := by
          intro h
          exact hkl' (hik.symm.trans h)
        simp [hik, hkl]
      · simp [hik]
    · simp [hij]
  sum_eq_one := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.sum_apply]
      rw [Finset.sum_eq_single i.2]
      · simp [classicalCoherentConditioningProjector]
      · intro k _ hk
        have hnot : ¬ i.2 = k := fun h => hk h.symm
        simp [classicalCoherentConditioningProjector, hnot]
      · simp
    · simp [classicalCoherentConditioningProjector, Matrix.sum_apply, hij
        ]

private def classicalCoherentConditioningPinch
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (T : CMatrix (c × x × y')) : CMatrix (c × x × y') :=
  classicalCoherentConditioningMeasurement
    (c := c) (x := x) (y' := y').pinchingChannel.map T

private theorem classicalCoherentConditioningPinch_apply
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (T : CMatrix (c × x × y')) (i j) :
    classicalCoherentConditioningPinch (x := x) T i j =
      if i.2.1 = j.2.1 ∧ i.2.2 = j.2.2 then T i j else 0 := by
  change classicalCoherentConditioningMeasurement
      (c := c) (x := x) (y' := y').pinchingChannel.map T i j = _
  rw [ProjectiveMeasurement.pinchingChannel_map, Matrix.sum_apply]
  rcases i with ⟨ic, ix, iy⟩
  rcases j with ⟨jc, jx, jy⟩
  simp [classicalCoherentConditioningMeasurement,
    classicalCoherentConditioningProjector,
     Prod.ext_iff]
  rw [Finset.sum_eq_single (jx, jy)]
  · simp
  · intro k _ hk
    have hneq : ¬ (jx = k.1 ∧ jy = k.2) := by
      intro h
      exact hk (Prod.ext h.1 h.2).symm
    simp [hneq]
  · simp

private def classicalCoherentBlockProjector
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] (p q : x) (k : y') :
    CMatrix ((a × x) × (c × x × y')) :=
  Matrix.diagonal (fun i =>
    if i.1.2 = p ∧ i.2.2.1 = q ∧ i.2.2.2 = k then (1 : ℂ) else 0)

omit [Fintype a] [Fintype x] in
private theorem classicalCoherentBlockProjector_conjTranspose
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] (p q : x) (k : y') :
    Matrix.conjTranspose (classicalCoherentBlockProjector
      (a := a) (x := x) (c := c) p q k) =
      classicalCoherentBlockProjector (a := a) (x := x) (c := c) p q k := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [classicalCoherentBlockProjector]
  · simp [classicalCoherentBlockProjector, Matrix.conjTranspose_apply,
      hij, Ne.symm hij]

private theorem classicalCoherentBlockProjector_sandwich_apply
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] (p q : x) (k : y')
    (M : CMatrix ((a × x) × (c × x × y'))) (i j) :
    ((classicalCoherentBlockProjector (a := a) (x := x) (c := c) p q k * M *
        classicalCoherentBlockProjector (a := a) (x := x) (c := c) p q k :
        CMatrix ((a × x) × (c × x × y'))) i j) =
      if i.1.2 = p ∧ i.2.2.1 = q ∧ i.2.2.2 = k ∧
          j.1.2 = p ∧ j.2.2.1 = q ∧ j.2.2.2 = k then M i j else 0 := by
  rw [classicalCoherentBlockProjector, Matrix.mul_assoc,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h₁ : i.1.2 = p <;> by_cases h₂ : i.2.2.1 = q <;>
    by_cases h₃ : i.2.2.2 = k <;> by_cases h₄ : j.1.2 = p <;>
    by_cases h₅ : j.2.2.1 = q <;> by_cases h₆ : j.2.2.2 = k <;>
    simp [h₁, h₂, h₃, h₄, h₅, h₆]

private theorem classicalCoherentBlockProjector_sandwich_posSemidef
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (T : CMatrix (c × x × y')) (hT : T.PosSemidef) (p q : x) (k : y') :
    (classicalCoherentBlockProjector (a := a) (x := x) (c := c) p q k *
        Matrix.kronecker (1 : CMatrix (a × x)) T *
          classicalCoherentBlockProjector (a := a) (x := x) (c := c) p q k).PosSemidef := by
  have hM : (Matrix.kronecker (1 : CMatrix (a × x)) T).PosSemidef :=
    Matrix.PosSemidef.one.kronecker hT
  simpa only [classicalCoherentBlockProjector_conjTranspose] using
    hM.conjTranspose_mul_mul_same
      (classicalCoherentBlockProjector (a := a) (x := x) (c := c) p q k)

private theorem classicalCoherentMap_reference_residual
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (T : CMatrix (c × x × y')) (i j) :
    ((Matrix.kronecker (1 : CMatrix (a × x))
        (classicalCoherentConditioningPinch (x := x) T) -
        classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
          (Matrix.kronecker (1 : CMatrix (a × x)) T)) i j) =
      (∑ p : x, ∑ q ∈ Finset.univ.erase p, ∑ k : y',
        classicalCoherentBlockProjector (a := a) (x := x) (c := c) p q k *
          Matrix.kronecker (1 : CMatrix (a × x)) T *
          classicalCoherentBlockProjector (a := a) (x := x) (c := c) p q k) i j := by
  classical
  simp only [Matrix.sub_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    classicalCoherentConditioningPinch_apply, classicalCoherentMap_apply,
    Matrix.sum_apply]
  simp_rw [classicalCoherentBlockProjector_sandwich_apply]
  simp only [Matrix.one_apply, Matrix.kroneckerMap_apply]
  by_cases houter : i.1 = j.1
  · have houterx : i.1.2 = j.1.2 := congrArg Prod.snd houter
    simp only [if_pos houter, one_mul]
    by_cases htx : i.2.2.1 = j.2.2.1
    · by_cases hy : i.2.2.2 = j.2.2.2
      · have hcoord : i.2.2.1 = j.2.2.1 ∧
            i.2.2.2 = j.2.2.2 := ⟨htx, hy⟩
        rw [if_pos hcoord]
        have hcoh :
            (i.1.2 = i.2.2.1 ∧ j.1.2 = j.2.2.1 ∧
              i.2.2.2 = j.2.2.2) ↔ i.1.2 = i.2.2.1 := by
          constructor
          · exact fun h => h.1
          · intro h
            exact ⟨h, houterx.symm.trans h |>.trans htx, hy⟩
        by_cases hcopy : i.1.2 = i.2.2.1
        · rw [if_pos (hcoh.mpr hcopy)]
          rw [sub_self]
          symm
          apply Finset.sum_eq_zero
          intro p _
          apply Finset.sum_eq_zero
          intro q hq
          apply Finset.sum_eq_zero
          intro k _
          have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
          have hzero : ¬ (i.1.2 = p ∧ i.2.2.1 = q ∧
              i.2.2.2 = k ∧ j.1.2 = p ∧ j.2.2.1 = q ∧
              j.2.2.2 = k) := by
            intro h
            exact hqp (h.2.1.symm.trans (hcopy.symm.trans h.1))
          rw [if_neg hzero]
        · rw [if_neg (fun h => hcopy (hcoh.mp h))]
          rw [Finset.sum_eq_single i.1.2]
          · rw [Finset.sum_eq_single i.2.2.1]
            · rw [Finset.sum_eq_single i.2.2.2]
              · simp [ houterx, htx, hy]
              · intro k _ hki
                have hki' : i.2.2.2 ≠ k := Ne.symm hki
                have hzero : ¬ (i.1.2 = i.1.2 ∧
                    i.2.2.1 = i.2.2.1 ∧ i.2.2.2 = k ∧
                    j.1.2 = i.1.2 ∧ j.2.2.1 = i.2.2.1 ∧
                    j.2.2.2 = k) := by
                  intro h
                  exact hki h.2.2.1.symm
                rw [if_neg hzero]
              · intro hnot
                exact (hnot (Finset.mem_univ _)).elim
            · intro q hq hqi
              have hqi' : i.2.2.1 ≠ q := Ne.symm hqi
              simp [ hqi']
            · have hcopy' : i.2.2.1 ≠ i.1.2 := Ne.symm hcopy
              simp [ hcopy']
          · intro p _ hpi
            have hpi' : i.1.2 ≠ p := Ne.symm hpi
            simp [ hpi']
          · simp
      · have hcoord : ¬ (i.2.2.1 = j.2.2.1 ∧
            i.2.2.2 = j.2.2.2) := fun h => hy h.2
        have hcoh : ¬ (i.1.2 = i.2.2.1 ∧ j.1.2 = j.2.2.1 ∧
            i.2.2.2 = j.2.2.2) := fun h => hy h.2.2
        rw [if_neg hcoord, if_neg hcoh]
        simp only [sub_zero]
        symm
        apply Finset.sum_eq_zero
        intro p _
        apply Finset.sum_eq_zero
        intro q _
        apply Finset.sum_eq_zero
        intro k _
        have hzero : ¬ (i.1.2 = p ∧ i.2.2.1 = q ∧
            i.2.2.2 = k ∧ j.1.2 = p ∧ j.2.2.1 = q ∧
            j.2.2.2 = k) := by
          intro h
          rcases h with ⟨_, _, hik, _, _, hjk⟩
          exact hy (hik.trans hjk.symm)
        rw [if_neg hzero]
    · have hcoord : ¬ (i.2.2.1 = j.2.2.1 ∧
          i.2.2.2 = j.2.2.2) := fun h => htx h.1
      have hcoh : ¬ (i.1.2 = i.2.2.1 ∧ j.1.2 = j.2.2.1 ∧
          i.2.2.2 = j.2.2.2) := by
        intro h
        exact htx (h.1.symm.trans (houterx.trans h.2.1))
      rw [if_neg hcoord, if_neg hcoh]
      simp only [sub_zero]
      symm
      apply Finset.sum_eq_zero
      intro p _
      apply Finset.sum_eq_zero
      intro q _
      apply Finset.sum_eq_zero
      intro k _
      have hzero : ¬ (i.1.2 = p ∧ i.2.2.1 = q ∧
          i.2.2.2 = k ∧ j.1.2 = p ∧ j.2.2.1 = q ∧
          j.2.2.2 = k) := by
        intro h
        rcases h with ⟨_, hitx, _, _, hjtx, _⟩
        exact htx (hitx.trans hjtx.symm)
      rw [if_neg hzero]
  · simp [houter]

private theorem classicalCoherentMap_reference_le
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (T : CMatrix (c × x × y')) (hT : T.PosSemidef) :
    classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
        (Matrix.kronecker (1 : CMatrix (a × x)) T) ≤
      Matrix.kronecker (1 : CMatrix (a × x))
        (classicalCoherentConditioningPinch (x := x) T) := by
  rw [Matrix.le_iff]
  have hres :
      Matrix.kronecker (1 : CMatrix (a × x))
          (classicalCoherentConditioningPinch (x := x) T) -
        classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
          (Matrix.kronecker (1 : CMatrix (a × x)) T) =
      ∑ p : x, ∑ q ∈ Finset.univ.erase p, ∑ k : y',
        classicalCoherentBlockProjector (a := a) (x := x) (c := c) p q k *
          Matrix.kronecker (1 : CMatrix (a × x)) T *
          classicalCoherentBlockProjector (a := a) (x := x) (c := c) p q k := by
    ext i j
    exact classicalCoherentMap_reference_residual T i j
  rw [hres]
  exact Matrix.posSemidef_sum Finset.univ fun p _ =>
    Matrix.posSemidef_sum (Finset.univ.erase p) fun q _ =>
      Matrix.posSemidef_sum Finset.univ fun k _ =>
        classicalCoherentBlockProjector_sandwich_posSemidef T hT p q k

private theorem ConditionalMinEntropyScaleFeasible.classicalCoherentPinch
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    {rho : SubnormalizedState ((a × x) × (c × x × y'))}
    {T : CMatrix (c × x × y')}
    (hT : ConditionalMinEntropyScaleFeasible (a := a × x) rho T) :
    ConditionalMinEntropyScaleFeasible (a := a × x)
      (rho.applyTraceNonincreasingCP
        (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y'))
        (classicalCoherentMapTraceNonincreasingCP
          (a := a) (x := x) (c := c) (y' := y')))
      (classicalCoherentConditioningPinch (x := x) T) := by
  constructor
  · exact MatrixMap.isCompletelyPositive_mapsPositive
      (classicalCoherentConditioningMeasurement
        (c := c) (x := x) (y' := y')).pinchingChannel.map
      (classicalCoherentConditioningMeasurement
        (c := c) (x := x) (y' := y')).pinchingChannel.completelyPositive T hT.1
  · have hdiff :
        (Matrix.kronecker (1 : CMatrix (a × x)) T - rho.matrix).PosSemidef :=
      hT.2
    have hmap := MatrixMap.isCompletelyPositive_mapsPositive
      (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y'))
      (classicalCoherentMap_completelyPositive
        (a := a) (x := x) (c := c) (y' := y'))
      (Matrix.kronecker (1 : CMatrix (a × x)) T - rho.matrix) hdiff
    have href := classicalCoherentMap_reference_le (a := a) (x := x)
      (c := c) (y' := y') T hT.1
    have hrefPsd :
        (Matrix.kronecker (1 : CMatrix (a × x))
            (classicalCoherentConditioningPinch (x := x) T) -
          classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
            (Matrix.kronecker (1 : CMatrix (a × x)) T)).PosSemidef :=
      Matrix.le_iff.mp href
    have hsum :
        (Matrix.kronecker (1 : CMatrix (a × x))
            (classicalCoherentConditioningPinch (x := x) T) -
          classicalCoherentMap (a := a) (x := x) (c := c) (y' := y') rho.matrix).PosSemidef := by
      have hmap' :
          (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
              (Matrix.kronecker (1 : CMatrix (a × x)) T) -
            classicalCoherentMap (a := a) (x := x) (c := c) (y' := y') rho.matrix).PosSemidef := by
        simpa only [map_sub] using hmap
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        hrefPsd.add hmap'
    change (Matrix.kronecker (1 : CMatrix (a × x))
        (classicalCoherentConditioningPinch (x := x) T) -
      (rho.applyTraceNonincreasingCP
        (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y'))
        (classicalCoherentMapTraceNonincreasingCP
          (a := a) (x := x) (c := c) (y' := y'))).matrix).PosSemidef
    simpa only [SubnormalizedState.applyTraceNonincreasingCP] using hsum

private theorem classicalCoherentMap_trace_re
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    {rho : SubnormalizedState ((a × x) × (c × x × y'))}
    (hclassical : classicalCoherentOn rho) :
    (rho.applyTraceNonincreasingCP
      (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y'))
      (classicalCoherentMapTraceNonincreasingCP
        (a := a) (x := x) (c := c) (y' := y'))).matrix.trace.re =
      rho.matrix.trace.re := by
  exact congrArg
    (fun s : SubnormalizedState ((a × x) × (c × x × y')) => s.matrix.trace.re)
    (classicalCoherentMap_fixed hclassical)

private theorem conditionalMinEntropyScale_classicalCoherentMap_le
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (rho : SubnormalizedState ((a × x) × (c × x × y'))) :
    (rho.applyTraceNonincreasingCP
      (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y'))
      (classicalCoherentMapTraceNonincreasingCP
        (a := a) (x := x) (c := c) (y' := y'))).conditionalMinEntropyScale
        (a := a × x) ≤ rho.conditionalMinEntropyScale (a := a × x) := by
  let rhoPinch := rho.applyTraceNonincreasingCP
    (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y'))
    (classicalCoherentMapTraceNonincreasingCP
      (a := a) (x := x) (c := c) (y' := y'))
  change rhoPinch.conditionalMinEntropyScale (a := a × x) ≤
    rho.conditionalMinEntropyScale (a := a × x)
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf (rho.conditionalMinEntropyScaleValueSet_nonempty
      (a := a × x)) ?_
  intro t ht
  rcases ht with ⟨T, hT, rfl⟩
  have hbdd := rhoPinch.conditionalMinEntropyScaleValueSet_bddBelow
      (a := a × x)
  exact csInf_le hbdd ⟨classicalCoherentConditioningPinch (x := x) T,
    hT.classicalCoherentPinch, by
      change T.trace.re =
        ((classicalCoherentConditioningMeasurement
          (c := c) (x := x) (y' := y')).pinchingChannel.map T).trace.re
      exact congrArg Complex.re
        ((classicalCoherentConditioningMeasurement
          (c := c) (x := x) (y' := y')).pinchingChannel.tracePreserving T).symm⟩

private theorem conditionalMinEntropyRaw_le_classicalCoherentMap_of_trace_pos
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    [Nonempty a] [Nonempty x] [Nonempty c] [Nonempty y']
    (rho : SubnormalizedState ((a × x) × (c × x × y')))
    (hρ : 0 < rho.matrix.trace.re)
    (hρpinch : 0 <
      (rho.applyTraceNonincreasingCP
        (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y'))
        (classicalCoherentMapTraceNonincreasingCP
          (a := a) (x := x) (c := c) (y' := y'))).matrix.trace.re) :
    rho.conditionalMinEntropyRaw ≤
      (rho.applyTraceNonincreasingCP
        (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y'))
        (classicalCoherentMapTraceNonincreasingCP
          (a := a) (x := x) (c := c) (y' := y'))).conditionalMinEntropyRaw := by
  let rhoPinch := rho.applyTraceNonincreasingCP
    (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y'))
    (classicalCoherentMapTraceNonincreasingCP
      (a := a) (x := x) (c := c) (y' := y'))
  change rho.conditionalMinEntropyRaw ≤ rhoPinch.conditionalMinEntropyRaw
  rw [rho.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a × x) hρ,
    rhoPinch.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a × x) hρpinch]
  have hscale_le := conditionalMinEntropyScale_classicalCoherentMap_le rho
  have hscale_pos :=
    rhoPinch.conditionalMinEntropyScale_pos_of_trace_pos
      (a := a × x) hρpinch
  have hlog :
      log2 (rhoPinch.conditionalMinEntropyScale (a := a × x)) ≤
        log2 (rho.conditionalMinEntropyScale (a := a × x)) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hscale_pos hscale_le)
      (le_of_lt (Real.log_pos one_lt_two))
  exact neg_le_neg hlog

private theorem smoothConditionalMinEntropy_exists_classicalCoherent_optimizer
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    [Nonempty a] [Nonempty x] [Nonempty c] [Nonempty y']
    (rho : SubnormalizedState ((a × x) × (c × x × y'))) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < Real.sqrt rho.matrix.trace.re)
    (hclassical : classicalCoherentOn rho) :
    ∃ tau : SubnormalizedState ((a × x) × (c × x × y')),
      rho.purifiedBall ε tau ∧ classicalCoherentOn tau ∧
        tau.conditionalMinEntropyRaw = rho.smoothConditionalMinEntropy ε hε0 hε := by
  have hρ : 0 < rho.matrix.trace.re :=
    Real.sqrt_pos.mp (lt_of_le_of_lt hε0 hε)
  rcases smoothConditionalMinEntropy_exists_optimizer
      (a := a × x) (b := c × x × y') rho hε0 hε with
    ⟨rhoMin, hρminne, hball, hmin_eq, hoptimizer⟩
  let tau := rhoMin.applyTraceNonincreasingCP
    (classicalCoherentMap (a := a) (x := x) (c := c) (y' := y'))
    (classicalCoherentMapTraceNonincreasingCP
      (a := a) (x := x) (c := c) (y' := y'))
  have hballTau := purifiedBall_classicalCoherentMap_of_classical_center
    hclassical hball
  have hρmin : 0 < rhoMin.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      rho rhoMin hε hball
  have hτ : tau.matrix ≠ 0 := by
    have hpos := SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      rho tau hε hballTau
    intro hzero
    rw [hzero] at hpos
    simp at hpos
  refine ⟨tau, hballTau,
    classicalCoherentMap_classicalCoherentOn rhoMin, ?_⟩
  apply le_antisymm
  · calc
      tau.conditionalMinEntropyRaw ≤ rhoMin.conditionalMinEntropyRaw :=
        hoptimizer tau hτ hballTau
      _ = rho.smoothConditionalMinEntropy ε hε0 hε := hmin_eq.symm
  · calc
      rho.smoothConditionalMinEntropy ε hε0 hε = rhoMin.conditionalMinEntropyRaw := hmin_eq
      _ ≤ tau.conditionalMinEntropyRaw :=
        conditionalMinEntropyRaw_le_classicalCoherentMap_of_trace_pos
          rhoMin hρmin
          (SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
            rho tau hε hballTau)

private def canonicalComplementaryPurification
    (rho : State ((a × x) × (y × b))) :
    PureVector (Prod (y × b) ((a × x) × ((a × x) × (y × b)))) :=
  rho.canonicalPurification.reindex
    (State.abToACReferenceEquiv ((a × x) × (y × b)) (a × x) (y × b))

private def canonicalComplementaryMarginal
    (rho : State ((a × x) × (y × b))) :
    State ((a × x) × ((a × x) × (y × b))) :=
  State.acMarginalFromABPurification rho.canonicalPurification

private theorem canonicalComplementaryPurification_purifies
    (rho : State ((a × x) × (y × b))) :
    (canonicalComplementaryPurification rho).Purifies
      (canonicalComplementaryMarginal rho) := by
  exact PureVector.purifies_marginalB (canonicalComplementaryPurification rho)

/-! ## Uhlmann max-candidate seam

The source max proof chooses the purification block by block.  The ball part
of that argument is independent of the block choice and can be isolated here.
The two block-orthogonality hypotheses below are the exact amplitude form of
the source's `X` and `Y` projectors; they are what turns the chosen
purification into a classical-on-`X,Y` complementary marginal.
-/

private theorem complementaryMaxCandidate_of_classical_block_amplitude
    {r : Type*} {a' : Type*} {x' : Type*} {y' : Type*} {b' : Type*}
    [Fintype r] [DecidableEq r]
    [Nonempty r]
    [Fintype a'] [DecidableEq a']
    [Fintype x'] [DecidableEq x']
    [Fintype y'] [DecidableEq y']
    [Fintype b'] [DecidableEq b']
    {ε : ℝ}
    (center : State ((a' × x') × (y' × b')))
    (etaCenter : State r)
    (Ψ : PureVector (Prod ((a' × x') × (y' × b')) r))
    (hΨ : Ψ.Purifies etaCenter)
    (hΨcenter : Ψ.state.marginalA = center)
    (eta : State r)
    (hball : etaCenter.toSubnormalized.purifiedBall
      ε eta.toSubnormalized)
    (Φ : PureVector (Prod ((a' × x') × (y' × b')) r))
    (_hΦ : Φ.Purifies eta)
    (hoverlap : Ψ.overlapSq Φ = etaCenter.squaredFidelity eta)
    (hampX : ∀ i j, i.1.2 ≠ j.1.2 →
      ∑ k : r, Φ.amp (i, k) * star (Φ.amp (j, k)) = 0)
    (hampY : ∀ i j, i.2.1 ≠ j.2.1 →
      ∑ k : r, Φ.amp (i, k) * star (Φ.amp (j, k)) = 0) :
    ∃ tau : SubnormalizedState ((a' × x') × (y' × b')),
      center.toSubnormalized.purifiedBall ε tau ∧ tau.classicalOnXY := by
  have hΨB : Ψ.state.marginalB = etaCenter := by
    apply State.ext
    simpa [State.marginalB_matrix] using hΨ
  have hstateBall : Ψ.state.purifiedBall ε Φ.state := by
    have hη : etaCenter.purifiedBall ε eta :=
      (State.purifiedBall_iff_toSubnormalized_purifiedBall
        etaCenter eta ε).mpr hball
    have hF : etaCenter.squaredFidelity eta ≤
        Ψ.state.squaredFidelity Φ.state := by
      calc
        etaCenter.squaredFidelity eta = Ψ.overlapSq Φ := hoverlap.symm
        _ ≤ Ψ.state.squaredFidelity Φ.state :=
          PureVector.overlapSq_le_state_squaredFidelity Ψ Φ
    exact State.purifiedBall_of_squaredFidelity_le hF hη
  have hcenterBall : center.toSubnormalized.purifiedBall ε
      Φ.state.marginalA.toSubnormalized := by
    have hmargin := State.purifiedBall_marginalA_of_purifiedBall hstateBall
    rw [hΨcenter] at hmargin
    exact (State.purifiedBall_iff_toSubnormalized_purifiedBall
      center Φ.state.marginalA ε).mp hmargin
  let tau : SubnormalizedState ((a' × x') × (y' × b')) :=
    Φ.state.marginalA.toSubnormalized
  have htauX : tau.classicalOnX := by
    intro i j hij
    change Φ.state.marginalA.matrix i j = 0
    rw [State.marginalA_matrix]
    simp only [partialTraceB, PureVector.state_matrix,
      rankOneMatrix_apply]
    exact hampX i j hij
  have htauY : tau.classicalOnY := by
    intro i j hij
    change Φ.state.marginalA.matrix i j = 0
    rw [State.marginalA_matrix]
    simp only [partialTraceB, PureVector.state_matrix,
      rankOneMatrix_apply]
    exact hampY i j hij
  refine ⟨tau, hcenterBall, ⟨htauX, htauY⟩⟩

/-! The hat-extension route has a deliberately separate intermediate target.
The success-block API produces an enlarged `AB⁺` reference, so its classical
register statement cannot yet be phrased as `classicalOnXY` on the original
`(a × x) × (y' × b)` space.  This lemma records the exact candidate and entropy
handoff before the later compression/coherent-purification step. -/

omit [Fintype x] [DecidableEq x] in
private theorem maxCandidate_of_embeddedAC_candidate
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    [Nonempty a] [Nonempty x] [Nonempty b] [Nonempty c] [Nonempty y']
    {ψ : PureVector (Prod (Prod a b) c)} {t ε : ℝ}
    {ρAC' : SubnormalizedState (Prod a c)}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : EmbeddedACToABSmoothCandidate (a := a) (b := b) (c := c)
      ψ t ht0 ht1 ε ρAC')
    (hρ : 0 < ρAC'.matrix.trace.re) :
    ∃ ρABPlus' : SubnormalizedState (Prod a (ABPlusReference a b c)),
      SmoothConditionalMaxEntropyCandidateRaw (a := a)
        (embeddedABPlusBaseFromScaledPure (a := a) (b := b) (c := c)
          ψ t ht0 ht1) ε ρABPlus'.conditionalMaxEntropyRaw ∧
      ComplementaryPureMarginalRel (a := a) (b := ABPlusReference a b c)
        (c := c) ρABPlus' ρAC' ∧
      ρABPlus'.conditionalMaxEntropyRaw = -ρAC'.conditionalMinEntropyRaw := by
  obtain ⟨ρABPlus', hball, hrel⟩ :=
    h.exists_complementaryPureMarginalRel
      (a := a) (b := b) (c := c) hρ
  refine ⟨ρABPlus', ?_, hrel, ?_⟩
  · exact ⟨ρABPlus', hball, rfl⟩
  exact
    (conditionalMinMaxEntropyDualOn_complementaryPureMarginals
      (a := a) (b := ABPlusReference a b c) (c := c))
      ρABPlus' ρAC' hrel

/-! ## Normalized-extension source bridge

The following private lemmas isolate the normalized part of Tomamichel's
max-entropy route.  The failure summand is added to the joint source
`a × x`; choosing it as `extra × x` lets the resulting source be reindexed as
`(Sum extra a) × x`, so the classical `x` coordinate is retained explicitly.
The remaining fixed-point and source-compression hypotheses are deliberately
arguments of the bridge: they are the mathematical obligations left by the
`XX'`/`Y'` projector calculation, rather than facts that can be inferred from
an arbitrary hatted purification.
-/

private def sourceExtensionXEquiv
    {extra : Type*} [Fintype extra] [DecidableEq extra] :
    Sum (extra × x) (a × x) ≃ (Sum extra a) × x where
  toFun
    | Sum.inl ex => (Sum.inl ex.1, ex.2)
    | Sum.inr ax => (Sum.inr ax.1, ax.2)
  invFun
    | (Sum.inl e, k) => Sum.inl (e, k)
    | (Sum.inr i, k) => Sum.inr (i, k)
  left_inv z := by cases z <;> rfl
  right_inv z := by rcases z with ⟨e | i, k⟩ <;> rfl

private def sourceExtensionStateEquiv
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {r : Type*} [Fintype r] [DecidableEq r] :
    (Sum (extra × x) (a × x)) × r ≃ ((Sum extra a) × x) × r :=
  Equiv.prodCongr (sourceExtensionXEquiv (a := a) (x := x) (extra := extra))
    (Equiv.refl r)

private theorem State.reindex_toSubnormalized_eq_sourceIsometryApply
    {s s' r : Type*} [Fintype s] [DecidableEq s]
    [Fintype s'] [DecidableEq s'] [Fintype r] [DecidableEq r]
    (rho : State (s × r)) (e : s ≃ s') :
    (rho.reindex (Equiv.prodCongr e (Equiv.refl r))).toSubnormalized =
      rho.toSubnormalized.sourceIsometryApply (ReferenceIsometry.ofEquiv e) := by
  apply SubnormalizedState.ext
  ext i j
  rcases i with ⟨i1, i2⟩
  rcases j with ⟨j1, j2⟩
  simp only [State.toSubnormalized_matrix, State.reindex_matrix,
    SubnormalizedState.sourceIsometryApply_matrix,
    ReferenceIsometry.applyMatrix, ReferenceIsometry.ofEquiv,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (e.symm j1)]
  · rw [Finset.sum_eq_single (e.symm i1)]
    · simp [ReferenceIsometry.targetBlock]
    · intro x _ hxe
      by_cases h : i1 = e x
      · exact (hxe (by simpa using (congrArg e.symm h).symm)).elim
      · simp [h]
    · simp
  · intro x _ hxe
    by_cases h : j1 = e x
    · exact (hxe (by simpa using (congrArg e.symm h).symm)).elim
    · simp [h]
  · simp

private def sourceExtensionEmbedding
    {extra : Type*} [Fintype extra] [DecidableEq extra] :
    ReferenceIsometry (a × x) ((Sum extra a) × x) :=
  ReferenceIsometry.ofInjective
    (fun i : a × x => (Sum.inr i.1, i.2)) (by
      intro i j h
      have ha : i.1 = j.1 := by
        exact Sum.inr.inj (congrArg Prod.fst h)
      have hx : i.2 = j.2 :=
        congrArg (fun z : (Sum extra a) × x => z.2) h
      exact Prod.ext ha hx)

private def sourceNormalizedExtension
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {r : Type*} [Fintype r] [DecidableEq r]
    (rho : SubnormalizedState ((a × x) × r))
    (failure : State ((extra × x) × r)) :
    State (((Sum extra a) × x) × r) :=
  (SmoothNormalizedExtension.blockExtensionState rho failure).reindex
    (sourceExtensionStateEquiv (a := a) (x := x) (extra := extra) (r := r))

/-
set_option maxHeartbeats 8000000 in
private theorem sourceNormalizedExtension_center
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {r : Type*} [Fintype r] [DecidableEq r]
    (rho : State ((a × x) × r))
    (failure : State ((extra × x) × r)) :
    (sourceNormalizedExtension (a := a) (x := x) rho.toSubnormalized failure).toSubnormalized =
      rho.toSubnormalized.sourceIsometryApply
        (sourceExtensionEmbedding (a := a) (x := x) (extra := extra)) := by
  rw [sourceNormalizedExtension, State.toSubnormalized_reindex_eq,
    SmoothNormalizedExtension.blockExtensionState_toSubnormalized_center]
  apply SubnormalizedState.ext
  ext i j
  rcases i with ⟨i, ir⟩
  rcases j with ⟨j, jr⟩
  cases i <;> cases j <;>
    simp [SubnormalizedState.applyTraceNonincreasingCP_matrix,
      Channel.reindex, MatrixMap.ofReferenceIsometry_apply,
      ReferenceIsometry.ofEquiv, sourceExtensionStateEquiv,
      sourceExtensionXEquiv, sourceExtensionEmbedding,
      ReferenceIsometry.ofInjective, ReferenceIsometry.applyMatrix,
      ReferenceIsometry.targetBlock, ReferenceIsometry.sumInr,
      Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_sum_type, Fintype.sum_prod_type,
      Finset.sum_ite_eq', apply_ite, eq_comm, Prod.ext_iff,
      mul_assoc, mul_comm]

private def sourceExtensionIdentityIsometry
    {s : Type*} [Fintype s] [DecidableEq s] :
    ReferenceIsometry s s :=
  ReferenceIsometry.ofInjective (fun i : s => i) (by intro i j h; exact h)

private def sourceExtensionAXIsometry
    {extra : Type*} [Fintype extra] [DecidableEq extra] :
    ReferenceIsometry (a × x) ((Sum extra a) × x) :=
  (ReferenceIsometry.sumInr extra a).prod
    (sourceExtensionIdentityIsometry (s := x))

private def sourceExtensionEtaIsometry
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] :
    ReferenceIsometry ((a × x) × (c × x × y'))
      (((Sum extra a) × x) × (c × x × y')) :=
  (sourceExtensionAXIsometry (a := a) (x := x) (extra := extra)).prod
    (sourceExtensionIdentityIsometry (s := c × x × y'))

private theorem sourceNormalizedExtension_classicalOnXY
-/

private theorem sourceNormalizedExtension_classicalOnXY
    {extra : Type*} [Fintype extra] [DecidableEq extra] [Nonempty extra]
    (rho : SubnormalizedState ((a × x) × (y × b)))
    (failure : State ((extra × x) × (y × b)))
    (hρ : rho.classicalOnXY)
    (hf : failure.toSubnormalized.classicalOnXY) :
    (sourceNormalizedExtension (a := a) (x := x) rho failure).toSubnormalized.classicalOnXY := by
  constructor
  · intro i j hij
    change (sourceNormalizedExtension (a := a) (x := x) rho failure).matrix i j = 0
    rw [sourceNormalizedExtension, State.reindex_matrix]
    change (SmoothNormalizedExtension.blockExtensionState rho failure).matrix
        ((sourceExtensionStateEquiv (a := a) (x := x) (extra := extra)
          (r := y × b)).symm i)
        ((sourceExtensionStateEquiv (a := a) (x := x) (extra := extra)
          (r := y × b)).symm j) = 0
    dsimp [sourceExtensionStateEquiv, sourceExtensionXEquiv]
    rcases i with ⟨⟨ei | ai, xi⟩, yi, bi⟩ <;>
      rcases j with ⟨⟨ej | aj, xj⟩, yj, bj⟩
    · by_cases h : xi = xj
      · exact (hij (by simp [h])).elim
      · simpa [SmoothNormalizedExtension.blockExtensionState_matrix,
          SmoothNormalizedExtension.sourceSumEquiv] using
          (Or.inr (hf.1 ((ei, xi), (yi, bi)) ((ej, xj), (yj, bj)) h))
    · simp [
        SmoothNormalizedExtension.sourceSumEquiv]
    · by_cases h : xi = xj
      · exact (hij (by simp [h])).elim
      · simp [SmoothNormalizedExtension.sourceSumEquiv]
    · by_cases h : xi = xj
      · exact (hij (by simp [h])).elim
      · simpa [SmoothNormalizedExtension.blockExtensionState_matrix,
          SmoothNormalizedExtension.sourceSumEquiv] using
          (hρ.1 ((ai, xi), (yi, bi)) ((aj, xj), (yj, bj)) h)
  · intro i j hij
    change (sourceNormalizedExtension (a := a) (x := x) rho failure).matrix i j = 0
    rw [sourceNormalizedExtension, State.reindex_matrix]
    change (SmoothNormalizedExtension.blockExtensionState rho failure).matrix
        ((sourceExtensionStateEquiv (a := a) (x := x) (extra := extra)
          (r := y × b)).symm i)
        ((sourceExtensionStateEquiv (a := a) (x := x) (extra := extra)
          (r := y × b)).symm j) = 0
    dsimp [sourceExtensionStateEquiv, sourceExtensionXEquiv]
    rcases i with ⟨⟨ei | ai, xi⟩, yi, bi⟩ <;>
      rcases j with ⟨⟨ej | aj, xj⟩, yj, bj⟩
    · by_cases h : yi = yj
      · exact (hij (by simp [h])).elim
      · simpa [SmoothNormalizedExtension.blockExtensionState_matrix,
          SmoothNormalizedExtension.sourceSumEquiv] using
          (Or.inr (hf.2 ((ei, xi), (yi, bi)) ((ej, xj), (yj, bj)) h))
    · simp [
        SmoothNormalizedExtension.sourceSumEquiv]
    · simp [
        SmoothNormalizedExtension.sourceSumEquiv]
    · by_cases h : yi = yj
      · exact (hij (by simp [h])).elim
      · simpa [SmoothNormalizedExtension.blockExtensionState_matrix,
          SmoothNormalizedExtension.sourceSumEquiv] using
          (hρ.2 ((ai, xi), (yi, bi)) ((aj, xj), (yj, bj)) h)

private theorem sourceNormalizedExtension_classicalCoherentOn
    {extra : Type*} [Fintype extra] [DecidableEq extra] [Nonempty extra]
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (rho : SubnormalizedState ((a × x) × (c × x × y')))
    (failure : State ((extra × x) × (c × x × y')))
    (hρ : classicalCoherentOn rho)
    (hf : classicalCoherentOn failure.toSubnormalized) :
    classicalCoherentOn
      (sourceNormalizedExtension (a := a) (x := x) rho failure).toSubnormalized := by
  intro i j hij
  change (sourceNormalizedExtension (a := a) (x := x) rho failure).matrix i j = 0
  rw [sourceNormalizedExtension, State.reindex_matrix]
  change (SmoothNormalizedExtension.blockExtensionState rho failure).matrix
      ((sourceExtensionStateEquiv (a := a) (x := x) (extra := extra)
        (r := c × x × y')).symm i)
      ((sourceExtensionStateEquiv (a := a) (x := x) (extra := extra)
        (r := c × x × y')).symm j) = 0
  dsimp [sourceExtensionStateEquiv, sourceExtensionXEquiv]
  rcases i with ⟨⟨ei | ai, xi⟩, ci, xci, yi⟩ <;>
    rcases j with ⟨⟨ej | aj, xj⟩, cj, xcj, yj⟩
  · rcases hij with hxi | hxj | hy
    · simpa [SmoothNormalizedExtension.blockExtensionState_matrix,
        SmoothNormalizedExtension.sourceSumEquiv] using
        (Or.inr (hf ((ei, xi), (ci, xci, yi)) ((ej, xj), (cj, xcj, yj))
          (Or.inl hxi)))
    · simpa [SmoothNormalizedExtension.blockExtensionState_matrix,
        SmoothNormalizedExtension.sourceSumEquiv] using
        (Or.inr (hf ((ei, xi), (ci, xci, yi)) ((ej, xj), (cj, xcj, yj))
          (Or.inr (Or.inl hxj))))
    · simpa [SmoothNormalizedExtension.blockExtensionState_matrix,
        SmoothNormalizedExtension.sourceSumEquiv] using
        (Or.inr (hf ((ei, xi), (ci, xci, yi)) ((ej, xj), (cj, xcj, yj))
          (Or.inr (Or.inr hy))))
  · simp [
      SmoothNormalizedExtension.sourceSumEquiv]
  · simp [
      SmoothNormalizedExtension.sourceSumEquiv]
  · rcases hij with hxi | hxj | hy
    · simpa [SmoothNormalizedExtension.blockExtensionState_matrix,
        SmoothNormalizedExtension.sourceSumEquiv] using
        hρ ((ai, xi), (ci, xci, yi)) ((aj, xj), (cj, xcj, yj)) (Or.inl hxi)
    · simpa [SmoothNormalizedExtension.blockExtensionState_matrix,
        SmoothNormalizedExtension.sourceSumEquiv] using
        hρ ((ai, xi), (ci, xci, yi)) ((aj, xj), (cj, xcj, yj))
          (Or.inr (Or.inl hxj))
    · simpa [SmoothNormalizedExtension.blockExtensionState_matrix,
        SmoothNormalizedExtension.sourceSumEquiv] using
        hρ ((ai, xi), (ci, xci, yi)) ((aj, xj), (cj, xcj, yj))
          (Or.inr (Or.inr hy))

/-
private theorem sourceNormalizedExtension_center_fixed
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {r : Type*} [Fintype r] [DecidableEq r]
    (rho : State ((a × x) × r))
    (failure : State ((extra × x) × r)) :
    (sourceNormalizedExtension (a := a) (x := x) rho.toSubnormalized failure).toSubnormalized =
      rho.toSubnormalized.sourceIsometryApply
        (sourceExtensionEmbedding (a := a) (x := x) (extra := extra)) := by
  rw [sourceNormalizedExtension, State.toSubnormalized_reindex_eq,
    SmoothNormalizedExtension.blockExtensionState_toSubnormalized_center]
  apply SubnormalizedState.ext
  ext i j
  rcases i with ⟨i, ir⟩
  rcases j with ⟨j, jr⟩
  cases i <;> cases j <;>
    simp [SubnormalizedState.applyTraceNonincreasingCP_matrix,
      Channel.reindex, MatrixMap.ofReferenceIsometry_apply,
      ReferenceIsometry.ofEquiv, sourceExtensionStateEquiv,
      sourceExtensionXEquiv, sourceExtensionEmbedding,
      ReferenceIsometry.ofInjective, ReferenceIsometry.applyMatrix,
      ReferenceIsometry.targetBlock, ReferenceIsometry.sumInr,
      Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_sum_type, Fintype.sum_prod_type,
      Finset.sum_ite_eq', apply_ite, eq_comm, Prod.ext_iff,
      mul_assoc, mul_comm]
 -/

private theorem blockExtensionState_fidelity_subnormalized
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (rho sigma : SubnormalizedState ((a × x) × (c × x × y')))
    (failure : State (Prod (extra × x) (c × x × y'))) :
    (SmoothNormalizedExtension.blockExtensionState rho failure).fidelity
        (SmoothNormalizedExtension.blockExtensionState sigma failure) =
      traceNorm (psdSqrt rho.matrix * psdSqrt sigma.matrix) +
        Real.sqrt ((1 - rho.matrix.trace.re) *
          (1 - sigma.matrix.trace.re)) := by
  rw [SmoothNormalizedExtension.blockExtensionState,
    SmoothNormalizedExtension.blockExtensionState,
    SmoothNormalizedExtension.State.fidelity_reindex, State.fidelity]
  change traceNorm
      (psdSqrt (SmoothNormalizedExtension.blockExtensionCoarseState rho failure).matrix *
        psdSqrt (SmoothNormalizedExtension.blockExtensionCoarseState sigma failure).matrix) = _
  rw [SmoothNormalizedExtension.blockExtensionCoarseState_matrix,
    SmoothNormalizedExtension.blockExtensionCoarseState_matrix]
  have hr : 0 ≤ 1 - rho.matrix.trace.re := sub_nonneg.mpr rho.trace_le_one
  have hs : 0 ≤ 1 - sigma.matrix.trace.re := sub_nonneg.mpr sigma.trace_le_one
  rw [Matrix.fromBlocks_diagonal_psdSqrt
      (Matrix.PosSemidef.smul failure.pos hr) rho.pos,
    Matrix.fromBlocks_diagonal_psdSqrt
      (Matrix.PosSemidef.smul failure.pos hs) sigma.pos,
    Matrix.fromBlocks_multiply]
  have hrsmul : (1 - rho.matrix.trace.re) • failure.matrix =
      (((1 - rho.matrix.trace.re : ℝ) : ℂ) • failure.matrix) := by
    ext i j
    simp
  have hssmul : (1 - sigma.matrix.trace.re) • failure.matrix =
      (((1 - sigma.matrix.trace.re : ℝ) : ℂ) • failure.matrix) := by
    ext i j
    simp
  rw [hrsmul, hssmul]
  rw [psdSqrt_real_smul (M := failure.matrix) hr failure.pos,
    psdSqrt_real_smul (M := failure.matrix) hs failure.pos]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [Matrix.traceNorm_fromBlocks_diagonal]
  have hfailure : traceNorm (psdSqrt failure.matrix * psdSqrt failure.matrix) = 1 := by
    rw [psdSqrt_mul_self_of_posSemidef failure.pos,
      traceNorm_posSemidef_eq_trace_re failure.matrix failure.pos,
      failure.trace_eq_one]
    norm_num
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hcoeff :
      ((Real.sqrt (1 - sigma.matrix.trace.re) : ℝ) : ℂ) *
          ((Real.sqrt (1 - rho.matrix.trace.re) : ℝ) : ℂ) =
        ((Real.sqrt ((1 - sigma.matrix.trace.re) *
          (1 - rho.matrix.trace.re)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul hs]
  rw [hcoeff,
    traceNorm_real_smul_eq
      (Real.sqrt_nonneg ((1 - sigma.matrix.trace.re) *
        (1 - rho.matrix.trace.re)))]
  simp [hfailure, Real.sqrt_mul hr,
    mul_comm, add_comm]

private theorem blockExtensionState_purifiedDistance_subnormalized
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (rho sigma : SubnormalizedState ((a × x) × (c × x × y')))
    (failure : State (Prod (extra × x) (c × x × y'))) :
    (SmoothNormalizedExtension.blockExtensionState rho failure).purifiedDistance
        (SmoothNormalizedExtension.blockExtensionState sigma failure) =
      rho.purifiedDistance sigma := by
  rw [State.purifiedDistance_eq, SubnormalizedState.purifiedDistance_eq,
    State.squaredFidelity_eq_fidelity_sq,
    blockExtensionState_fidelity_subnormalized]
  simp [SubnormalizedState.generalizedFidelity_eq]

private theorem sourceNormalizedExtension_purifiedBall_subnormalized
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    (rho sigma : SubnormalizedState ((a × x) × (c × x × y')))
    (failure : State (Prod (extra × x) (c × x × y'))) {epsilon : ℝ}
    (hball : rho.purifiedBall epsilon sigma) :
    (sourceNormalizedExtension (a := a) (x := x) rho failure).toSubnormalized.purifiedBall
        epsilon
      (sourceNormalizedExtension (a := a) (x := x) sigma failure).toSubnormalized := by
  let e := sourceExtensionStateEquiv (a := a) (x := x) (extra := extra)
    (r := c × x × y')
  have hblock :
      (SmoothNormalizedExtension.blockExtensionState rho failure).purifiedBall epsilon
        (SmoothNormalizedExtension.blockExtensionState sigma failure) := by
    rw [State.purifiedBall_eq,
      blockExtensionState_purifiedDistance_subnormalized]
    exact hball
  have hblockSub :
      (SmoothNormalizedExtension.blockExtensionState rho failure).toSubnormalized.purifiedBall
        epsilon
      (SmoothNormalizedExtension.blockExtensionState sigma failure).toSubnormalized :=
    (State.purifiedBall_iff_toSubnormalized_purifiedBall
      (SmoothNormalizedExtension.blockExtensionState rho failure)
      (SmoothNormalizedExtension.blockExtensionState sigma failure) epsilon).mp hblock
  simpa [sourceNormalizedExtension, e] using
    (State.toSubnormalized_purifiedBall_reindex e hblockSub)

private theorem sourceNormalizedExtension_purifiedBall
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {r : Type*} [Fintype r] [DecidableEq r]
    (rho : State ((a × x) × r))
    (sigma : SubnormalizedState ((a × x) × r))
    (failure : State ((extra × x) × r)) {epsilon : ℝ}
    (hball : rho.toSubnormalized.purifiedBall epsilon sigma) :
    (sourceNormalizedExtension (a := a) (x := x) rho.toSubnormalized failure).toSubnormalized.purifiedBall
        epsilon
      (sourceNormalizedExtension (a := a) (x := x) sigma failure).toSubnormalized := by
  let e := sourceExtensionStateEquiv (a := a) (x := x) (extra := extra) (r := r)
  have hblock :
      (SmoothNormalizedExtension.blockExtensionState rho.toSubnormalized failure).purifiedBall
        epsilon (SmoothNormalizedExtension.blockExtensionState sigma failure) :=
    SmoothNormalizedExtension.blockExtensionState_purifiedBall
      rho sigma failure hball
  have hblockSub :
      (SmoothNormalizedExtension.blockExtensionState rho.toSubnormalized failure).toSubnormalized.purifiedBall
        epsilon (SmoothNormalizedExtension.blockExtensionState sigma failure).toSubnormalized :=
    (State.purifiedBall_iff_toSubnormalized_purifiedBall
      (SmoothNormalizedExtension.blockExtensionState rho.toSubnormalized failure)
      (SmoothNormalizedExtension.blockExtensionState sigma failure) epsilon).mp hblock
  simpa [sourceNormalizedExtension, e] using
    (State.toSubnormalized_purifiedBall_reindex e hblockSub)

private theorem classicalMaxCandidate_of_sourceNormalizedExtension_subnormalized
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    [Nonempty a] [Nonempty x] [Nonempty b] [Nonempty c] [Nonempty y']
    (center : State (((Sum extra a) × x) × (y' × b)))
    (etaCenter eta : SubnormalizedState ((a × x) × (c × x × y')))
    (failure : State ((extra × x) × (c × x × y')))
    (Psi Phi : PureVector (Prod b (((Sum extra a) × x) × (c × x × y'))))
    (hPsi : classicalCoherentMap (a := Sum extra a) (x := x) (c := c) (y' := y')
      (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) =
      Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose)
    (hPhi : classicalCoherentMap (a := Sum extra a) (x := x) (c := c) (y' := y')
      (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) =
      Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose)
    (hPhiEta : Phi.state.marginalB =
      sourceNormalizedExtension (a := a) (x := x) eta failure)
    (hPsiCenter :
      (coherentMaxPure (a := Sum extra a) (x := x) (b := b) Psi hPsi).state.marginalA =
        center)
    {epsilon : ℝ}
    (hball : etaCenter.purifiedBall epsilon eta)
    (hoverlap : Psi.overlapSq Phi =
      (sourceNormalizedExtension (a := a) (x := x) etaCenter failure).squaredFidelity
        (sourceNormalizedExtension (a := a) (x := x) eta failure)) :
    ∃ tau : SubnormalizedState (((Sum extra a) × x) × (y' × b)),
      center.toSubnormalized.purifiedBall epsilon tau ∧
        tau.classicalOnXY ∧
        tau.conditionalMaxEntropyRaw =
          -SubnormalizedState.conditionalMinEntropyRaw
            ((sourceNormalizedExtension (a := a) (x := x) eta failure).toSubnormalized) := by
  have hballExt := sourceNormalizedExtension_purifiedBall_subnormalized
    (a := a) (x := x) etaCenter eta failure hball
  exact classicalMaxCandidate_of_coherent_purifications
    (a := Sum extra a) (x := x) (b := b) (c := c) (y' := y')
    center
    (sourceNormalizedExtension (a := a) (x := x) etaCenter failure)
    (sourceNormalizedExtension (a := a) (x := x) eta failure)
    Psi Phi hPsi hPhi hPhiEta hPsiCenter hballExt hoverlap

private theorem classicalMaxCandidate_of_sourceNormalizedExtension
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    [Nonempty a] [Nonempty x] [Nonempty b] [Nonempty c] [Nonempty y']
    (center : State (((Sum extra a) × x) × (y' × b)))
    (etaCenter : State ((a × x) × (c × x × y')))
    (eta : SubnormalizedState ((a × x) × (c × x × y')))
    (failure : State ((extra × x) × (c × x × y')))
    (Psi Phi : PureVector (Prod b (((Sum extra a) × x) × (c × x × y'))))
    (hPsi : classicalCoherentMap (a := Sum extra a) (x := x) (c := c) (y' := y')
      (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) =
      Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose)
    (hPhi : classicalCoherentMap (a := Sum extra a) (x := x) (c := c) (y' := y')
      (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) =
      Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose)
    (hPhiEta : Phi.state.marginalB =
      sourceNormalizedExtension (a := a) (x := x) eta failure)
    (hPsiCenter :
      (coherentMaxPure (a := Sum extra a) (x := x) (b := b) Psi hPsi).state.marginalA =
        center)
    {epsilon : ℝ}
    (hball : etaCenter.toSubnormalized.purifiedBall epsilon eta)
    (hoverlap : Psi.overlapSq Phi =
      (sourceNormalizedExtension (a := a) (x := x) etaCenter.toSubnormalized failure).squaredFidelity
        (sourceNormalizedExtension (a := a) (x := x) eta failure)) :
    ∃ tau : SubnormalizedState (((Sum extra a) × x) × (y' × b)),
      center.toSubnormalized.purifiedBall epsilon tau ∧
        tau.classicalOnXY ∧
        tau.conditionalMaxEntropyRaw =
          -SubnormalizedState.conditionalMinEntropyRaw
            ((sourceNormalizedExtension (a := a) (x := x) eta failure).toSubnormalized) := by
  have hballExt := sourceNormalizedExtension_purifiedBall
    (a := a) (x := x) (extra := extra) etaCenter eta failure hball
  exact classicalMaxCandidate_of_coherent_purifications
    (a := Sum extra a) (x := x) (b := b) (c := c) (y' := y')
    center
    (sourceNormalizedExtension (a := a) (x := x) etaCenter.toSubnormalized failure)
    (sourceNormalizedExtension (a := a) (x := x) eta failure)
    Psi Phi hPsi hPhi hPhiEta hPsiCenter hballExt hoverlap

/-! Reindex the canonical `XY` purification into the source-duality layout.
The `Y` copy is supplied by `coherentLiftOfFixed`; the pure vector below is
therefore the canonical amplitude with that copy removed. -/

private def canonicalXYMaxAmplitude
    (rho : State ((a × x) × (y × b))) :
    Matrix ((a × x) × ((a × b) × (x × y))) (y × b) ℂ :=
  fun i k =>
    if i.2.2.2 = k.1 then
      (canonicalXYCoherentPurification (a := a) (x := x) (y := y) (b := b) rho).amp
        ((i.2.1, (i.2.2.1, i.2.2.2)), (i.1, (k.1, k.2)))
    else 0

private theorem canonicalXYMaxAmplitude_trace
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    (canonicalXYMaxAmplitude (a := a) (x := x) (y := y) (b := b) rho *
      (canonicalXYMaxAmplitude (a := a) (x := x) (y := y) (b := b) rho).conjTranspose).trace = 1 := by
  classical
  let psi := canonicalXYCoherentPurification
    (a := a) (x := x) (y := y) (b := b) rho
  have hzero := canonicalXYCoherentPurification_amp_zero_of_copy_mismatch
    (a := a) (x := x) (y := y) (b := b) rho hclassical
  have htrace := psi.trace_rankOne_eq_one
  rw [Matrix.trace] at htrace ⊢
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    rankOneMatrix_apply, canonicalXYMaxAmplitude, psi] at htrace ⊢
  simp only [Fintype.sum_prod_type] at htrace
  let amp := fun (ab : a × b) (xx : x) (yy : y)
      (ax : a × x) (ys : y) (bb : b) =>
    psi.amp (((ab.1, ab.2), xx, yy), ((ax.1, ax.2), ys, bb)) *
      star (psi.amp (((ab.1, ab.2), xx, yy), ((ax.1, ax.2), ys, bb)))
  have htrace' :
      (∑ ab : a × b, ∑ xx : x, ∑ yy : y, ∑ ax : a × x,
        ∑ ys : y, ∑ bb : b, amp ab xx yy ax ys bb) = 1 := by
    simp only [Fintype.sum_prod_type]
    simpa [amp, psi] using htrace
  have hcollapse (ab : a × b) (xx : x) (yy : y) (ax : a × x) :
      (∑ ys : y, ∑ bb : b, amp ab xx yy ax ys bb) =
        ∑ bb : b, amp ab xx yy ax yy bb := by
    rw [Finset.sum_eq_single yy]
    · intro ys _ hys
      apply Finset.sum_eq_zero
      intro bb _hbb
      dsimp [amp]
      have hcopy : ¬ ((xx, yy) = (ax.2, ys)) := by
        intro h
        exact hys (by simpa using (congrArg Prod.snd h).symm)
      have hz := hzero (ab, (xx, yy)) (ax, (ys, bb)) hcopy
      simpa using congrArg (fun z : ℂ => z * star z) hz
    · simp
  have htrace'' :
      (∑ ab : a × b, ∑ xx : x, ∑ yy : y, ∑ ax : a × x,
        ∑ bb : b, amp ab xx yy ax yy bb) = 1 := by
    simpa only [hcollapse] using htrace'
  have hreorder :
      (∑ ax : a × x, ∑ ab : a × b, ∑ xx : x, ∑ yy : y,
        ∑ bb : b, amp ab xx yy ax yy bb) = 1 := by
    calc
      _ = ∑ ab : a × b, ∑ ax : a × x, ∑ xx : x, ∑ yy : y,
          ∑ bb : b, amp ab xx yy ax yy bb := by rw [Finset.sum_comm]
      _ = ∑ ab : a × b, ∑ xx : x, ∑ ax : a × x, ∑ yy : y,
          ∑ bb : b, amp ab xx yy ax yy bb := by
            congr 1
            funext ab
            rw [Finset.sum_comm]
      _ = ∑ ab : a × b, ∑ xx : x, ∑ yy : y, ∑ ax : a × x,
          ∑ bb : b, amp ab xx yy ax yy bb := by
            congr 1
            funext ab
            congr 1
            funext xx
            rw [Finset.sum_comm]
      _ = 1 := htrace''
  simpa [amp, psi, Fintype.sum_prod_type] using hreorder

private def canonicalXYMaxPurification
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    PureVector (Prod (y × b) ((a × x) × ((a × b) × (x × y)))) :=
  PureVector.ofAmplitudeMatrix
    (canonicalXYMaxAmplitude (a := a) (x := x) (y := y) (b := b) rho)
    (canonicalXYMaxAmplitude_trace (a := a) (x := x) (y := y) (b := b) rho hclassical)

private theorem canonicalXYMaxPurification_purifies
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := b) rho hclassical).Purifies
      (canonicalXYComplementaryState (a := a) (x := x) (y := y) (b := b) rho) := by
  rw [PureVector.purifies_iff]
  simp only [canonicalXYMaxPurification, PureVector.ofAmplitudeMatrix
    ]
  ext i j
  simp only [ PureVector.state_matrix,

    partialTraceA, rankOneMatrix_apply]
  simp only [canonicalXYComplementaryState, State.acMarginalFromABPurification,
    State.marginalB, PureVector.state_matrix,
    partialTraceA, rankOneMatrix_apply,
    PureVector.reindex_amp,
    Fintype.sum_prod_type]
  simp only [canonicalXYMaxAmplitude, State.abToACReferenceEquiv]
  dsimp [State.abToACReferenceEquiv]
  have hzero := canonicalXYCoherentPurification_amp_zero_of_copy_mismatch
    (a := a) (x := x) (y := y) (b := b) rho hclassical
  apply Finset.sum_congr rfl
  intro yy _hyy
  apply Finset.sum_congr rfl
  intro bb _hbb
  by_cases hi : i.2.2.2 = yy
  · by_cases hj : j.2.2.2 = yy
    · subst yy
      rw [if_pos hj]
      simp
    · have hcopyj : j.2.2 ≠ (j.1.2, yy) := by
        intro h
        apply hj
        simpa using congrArg Prod.snd h
      have hz := hzero j.2 (j.1, (yy, bb)) hcopyj
      simp [hi, hj, hz]
  · have hcopyi : i.2.2 ≠ (i.1.2, yy) := by
      intro h
      apply hi
      simpa using congrArg Prod.snd h
    have hz := hzero i.2 (i.1, (yy, bb)) hcopyi
    simp [hi, hz]

private theorem canonicalXYMaxPurification_fixed
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    classicalCoherentMap (a := a) (x := x) (c := a × b) (y' := y)
      ((canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := b) rho hclassical).amplitudeMatrix *
        (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := b) rho hclassical).amplitudeMatrix.conjTranspose) =
      (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := b) rho hclassical).amplitudeMatrix *
        (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := b) rho hclassical).amplitudeMatrix.conjTranspose := by
  let psi := canonicalXYMaxPurification
    (a := a) (x := x) (y := y) (b := b) rho hclassical
  let etaCenter := canonicalXYComplementaryState
    (a := a) (x := x) (y := y) (b := b) rho
  have hpur : psi.Purifies etaCenter := by
    simpa [psi, etaCenter] using
      canonicalXYMaxPurification_purifies (a := a) (x := x) (y := y) (b := b) rho hclassical
  have hmarg : psi.state.marginalB = etaCenter := by
    apply State.ext
    simpa [State.marginalB_matrix] using hpur
  have hgram :
      (psi.amplitudeMatrix * psi.amplitudeMatrix.conjTranspose :
        CMatrix ((a × x) × ((a × b) × (x × y)))) =
      psi.state.marginalB.matrix := by
    rw [State.marginalB_matrix, PureVector.state_matrix,
      PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose]
  have hclass := canonicalXYComplementaryState_classicalCoherentOn
    (a := a) (x := x) (y := y) (b := b) rho hclassical
  change classicalCoherentMap (a := a) (x := x) (c := a × b) (y' := y)
      (psi.amplitudeMatrix * psi.amplitudeMatrix.conjTranspose) =
      psi.amplitudeMatrix * psi.amplitudeMatrix.conjTranspose
  rw [hgram, hmarg]
  have hfixed := classicalCoherentMap_fixed hclass
  have hfixedMatrix := congrArg SubnormalizedState.matrix hfixed
  simpa [SubnormalizedState.applyTraceNonincreasingCP_matrix] using hfixedMatrix

/-
/-! A source-shaped purification for the max route.  The original canonical
purification has an `X,Y` copy on its reference.  For a classical center the
matching copies can be identified, leaving only the physical `B` register on
the purifying side. -/

private def sourceMaxAmplitude
    (rho : State ((a × x) × (y × b))) :
    Matrix ((a × x) × ((a × b) × (x × y))) b ℂ :=
  fun i k =>
    (canonicalXYCoherentPurification (a := a) (x := x) (y := y) (b := b) rho).amp
      ((i.2.1, i.2.2), (i.1, (i.2.2.2, k)))

private theorem sourceMaxAmplitude_trace
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    (sourceMaxAmplitude (a := a) (x := x) (y := y) (b := b) rho *
      (sourceMaxAmplitude (a := a) (x := x) (y := y) (b := b) rho).conjTranspose).trace = 1 := by
  classical
  let psi := canonicalXYCoherentPurification
    (a := a) (x := x) (y := y) (b := b) rho
  have hzero := canonicalXYCoherentPurification_amp_zero_of_copy_mismatch
    (a := a) (x := x) (y := y) (b := b) rho hclassical
  have htrace := psi.trace_rankOne_eq_one
  rw [Matrix.trace] at htrace ⊢
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    rankOneMatrix_apply, sourceMaxAmplitude, psi, PureVector.amp] at htrace ⊢
  simp only [Fintype.sum_prod_type] at htrace ⊢
  have hcollapse (ab : a × b) (xy : x × y) (ax : a × x) :
      (∑ yy : y, ∑ bb : b,
        psi.amp ((ab, xy), (ax, (yy, bb))) *
          star (psi.amp ((ab, xy), (ax, (yy, bb))))) =
        ∑ bb : b, psi.amp ((ab, (xy.1, xy.2)),
          (ax, (xy.2, bb))) * star (psi.amp ((ab, (xy.1, xy.2)),
            (ax, (xy.2, bb)))) := by
    apply Finset.sum_eq_single xy.2
    · intro yy _hyy hne
      apply Finset.sum_eq_zero
      intro bb _hbb
      have hz := hzero (ab, xy) (ax, (yy, bb)) (by
        intro h
        exact hne (by simpa using (congrArg Prod.snd h).symm))
      simpa [psi] using hz
    · simp
  have hsource :
      (∑ ax : a × x, ∑ ab : a × b, ∑ xy : x × y, ∑ bb : b,
        psi.amp ((ab, xy), (ax, (xy.2, bb))) *
          star (psi.amp ((ab, xy), (ax, (xy.2, bb))))) = 1 := by
    calc
      _ = ∑ ax : a × x, ∑ ab : a × b, ∑ xy : x × y,
          ∑ yy : y, ∑ bb : b,
            psi.amp ((ab, xy), (ax, (yy, bb))) *
              star (psi.amp ((ab, xy), (ax, (yy, bb)))) := by
        congr 1
        funext ax
        congr 1
        funext ab
        congr 1
        funext xy
        exact (hcollapse ab xy ax).symm
      _ = ∑ ab : a × b, ∑ xy : x × y, ∑ ax : a × x,
          ∑ yy : y, ∑ bb : b,
            psi.amp ((ab, xy), (ax, (yy, bb))) *
              star (psi.amp ((ab, xy), (ax, (yy, bb)))) := by
        calc
          _ = ∑ ab : a × b, ∑ ax : a × x, ∑ xy : x × y,
              ∑ yy : y, ∑ bb : b,
                psi.amp ((ab, xy), (ax, (yy, bb))) *
                  star (psi.amp ((ab, xy), (ax, (yy, bb)))) := by
            simpa using (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
              (f := fun ax ab => ∑ xy : x × y, ∑ yy : y, ∑ bb : b,
                psi.amp ((ab, xy), (ax, (yy, bb))) *
                  star (psi.amp ((ab, xy), (ax, (yy, bb))))))
          _ = _ := by
            congr 1
            funext ab
            rw [Finset.sum_comm]
      _ = 1 := by simpa [Fintype.sum_prod_type] using htrace
  simpa [sourceMaxAmplitude, psi, Fintype.sum_prod_type] using hsource

private def sourceMaxPurification
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    PureVector (Prod b ((a × x) × ((a × b) × (x × y)))) :=
  PureVector.ofAmplitudeMatrix
    (sourceMaxAmplitude (a := a) (x := x) (y := y) (b := b) rho)
    (sourceMaxAmplitude_trace (a := a) (x := x) (y := y) (b := b) rho hclassical)

private theorem sourceMaxPurification_purifies
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    (sourceMaxPurification (a := a) (x := x) (y := y) (b := b) rho hclassical).Purifies
      (canonicalXYComplementaryState (a := a) (x := x) (y := y) (b := b) rho) := by
  rw [PureVector.purifies_iff]
  simp only [sourceMaxPurification, PureVector.ofAmplitudeMatrix,
    PureVector.ofAmplitudeMatrix_amplitudeMatrix]
  ext i j
  simp only [State.marginalB_matrix, PureVector.state_matrix,
    PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose,
    partialTraceA, Matrix.sum_apply, rankOneMatrix_apply]
  simp only [canonicalXYComplementaryState, State.acMarginalFromABPurification,
    State.marginalB, State.reindex, PureVector.state_matrix,
    partialTraceA, Matrix.sum_apply, rankOneMatrix_apply,
    PureVector.reindex_amp, xyABReferenceEquiv, xyABReindexEquiv,
    Fintype.sum_prod_type]
  simp only [sourceMaxAmplitude]
  let psi := canonicalXYCoherentPurification
    (a := a) (x := x) (y := y) (b := b) rho
  have hzero := canonicalXYCoherentPurification_amp_zero_of_copy_mismatch
    (a := a) (x := x) (y := y) (b := b) rho hclassical
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr (ι := b) (M := ℂ)
    (s₁ := Finset.univ) (s₂ := Finset.univ) rfl ?_
  intro k _hk
  rw [Finset.sum_eq_single i.2.2.2]
  · by_cases hy : i.2.2.2 = j.2.2.2
    · simp [hy, psi, State.abToACReferenceEquiv]
    · have hzj := hzero j.2 (j.1, (i.2.2.2, k)) (by
        intro h
        apply hy
        simpa using (congrArg Prod.snd h).symm)
      have hzj' : (starRingEnd ℂ)
          ((canonicalXYCoherentPurification (a := a) (x := x)
            (y := y) (b := b) rho).amp
            (j.2, (j.1, (i.2.2.2, k)))) = 0 := by
        simpa using congrArg star hzj
      have hprod :
          (canonicalXYCoherentPurification (a := a) (x := x)
            (y := y) (b := b) rho).amp
            (i.2, (i.1, (i.2.2.2, k))) *
            (starRingEnd ℂ)
              ((canonicalXYCoherentPurification (a := a) (x := x)
                (y := y) (b := b) rho).amp
                (j.2, (j.1, (i.2.2.2, k)))) = 0 := by
        rw [hzj']
        simp
      have hzi := hzero i.2 (i.1, (j.2.2.2, k)) (by
        intro h
        apply hy
        simpa using (congrArg Prod.snd h))
      have hzi' : (canonicalXYCoherentPurification (a := a) (x := x)
          (y := y) (b := b) rho).amp
          (i.2, (i.1, (j.2.2.2, k))) = 0 := by
        simpa using hzi
      dsimp [psi, State.abToACReferenceEquiv]
      rw [hzi']
      simp
  · intro yy _hyy hne
    apply mul_eq_zero.mpr
    left
    let z := (State.abToACReferenceEquiv ((a × b) × x × y)
      (a × x) (y × b)).symm ((yy, k), i)
    have hz := hzero z.1 z.2 (by
      intro h
      apply hne
      simpa [z, State.abToACReferenceEquiv] using (congrArg Prod.snd h).symm)
    simpa [z, psi, State.abToACReferenceEquiv] using hz
  · simp

private theorem sourceMaxPurification_fixed
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    classicalCoherentMap (a := a) (x := x) (c := a × b) (y' := y)
      ((sourceMaxPurification (a := a) (x := x) (y := y) (b := b) rho hclassical).amplitudeMatrix *
        (sourceMaxPurification (a := a) (x := x) (y := y) (b := b) rho hclassical).amplitudeMatrix.conjTranspose) =
      (sourceMaxPurification (a := a) (x := x) (y := y) (b := b) rho hclassical).amplitudeMatrix *
        (sourceMaxPurification (a := a) (x := x) (y := y) (b := b) rho hclassical).amplitudeMatrix.conjTranspose := by
  let psi := sourceMaxPurification
    (a := a) (x := x) (y := y) (b := b) rho hclassical
  have hpur : psi.Purifies (canonicalXYComplementaryState
      (a := a) (x := x) (y := y) (b := b) rho) := by
    simpa [psi] using sourceMaxPurification_purifies
      (a := a) (x := x) (y := y) (b := b) rho hclassical
  have hmarg : psi.state.marginalB = canonicalXYComplementaryState
      (a := a) (x := x) (y := y) (b := b) rho := by
    apply State.ext
    simpa [State.marginalB_matrix] using hpur
  have hgram :
      (psi.amplitudeMatrix * psi.amplitudeMatrix.conjTranspose :
        CMatrix ((a × x) × ((a × b) × (x × y)))) =
      psi.state.marginalB.matrix := by
    rw [State.marginalB_matrix, PureVector.state_matrix,
      PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose]
  have hclass := canonicalXYComplementaryState_classicalCoherentOn
    (a := a) (x := x) (y := y) (b := b) rho hclassical
  change classicalCoherentMap (a := a) (x := x) (c := a × b) (y' := y)
      (psi.amplitudeMatrix * psi.amplitudeMatrix.conjTranspose) =
      psi.amplitudeMatrix * psi.amplitudeMatrix.conjTranspose
  rw [hgram, hmarg]
  have hfixed := classicalCoherentMap_fixed hclass
  have hfixedMatrix := congrArg SubnormalizedState.matrix hfixed
  simpa [SubnormalizedState.applyTraceNonincreasingCP_matrix] using hfixedMatrix

private theorem sourceMaxPurification_center
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    (coherentMaxPure (a := a) (x := x) (b := b)
      (sourceMaxPurification (a := a) (x := x) (y := y) (b := b) rho hclassical)
      (sourceMaxPurification_fixed (a := a) (x := x) (y := y) (b := b) rho hclassical)).state.marginalA = rho := by
  apply State.ext
  ext i j
  simp [coherentMaxPure, coherentLiftOfFixed, coherentLiftAmplitude,
    State.acToABReferenceEquiv, coherentMaxSwapEquiv, PureVector.reindex,
    PureVector.reindex_state, State.reindex, State.marginalA,
    partialTraceA, partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
    PureVector.ofAmplitudeMatrix, Equiv.prodComm, sourceMaxPurification,
    sourceMaxAmplitude]
  have hpur := canonicalXYCoherentPurification_purifies
    (a := a) (x := x) (y := y) (b := b) rho
  rw [PureVector.purifies_iff] at hpur
  rw [← hpur]
  simp [canonicalXYCoherentPurification, State.canonicalPurification,
    State.marginalB, State.marginalA, partialTraceA, partialTraceB,
    Matrix.sum_apply, rankOneMatrix_apply, Fintype.sum_prod_type,
    Finset.sum_ite_eq', apply_ite, eq_comm, Prod.ext_iff]

 -/

/-! A finite reference reserve for the source route.  The `Sum.inl` branch
contains the original `Y × B` reference and the other branch is large enough
to host an arbitrary purification of the complementary candidate. -/

private theorem finite_pair_selector
    {u v : Type*} [Fintype u] [DecidableEq u]
    [Fintype v] [DecidableEq v]
    (p : u) (q : v) (f : u → v → ℂ) :
    (∑ i : u, ∑ j : v, if i = p ∧ j = q then f i j else 0) = f p q := by
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp [hi]
  · simp

private theorem finite_quad_selector
    {u v w z : Type*} [Fintype u] [DecidableEq u]
    [Fintype v] [DecidableEq v] [Fintype w] [DecidableEq w]
    [Fintype z] [DecidableEq z]
    (p : u) (q : v) (r : w) (s : z)
    (f : u → v → w → z → ℂ) :
    (∑ i : u, ∑ j : v, ∑ k : w, ∑ l : z,
      if i = p ∧ j = q ∧ k = r ∧ l = s then f i j k l else 0) =
        f p q r s := by
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · rw [Finset.sum_eq_single r]
      · rw [Finset.sum_eq_single s]
        · simp
        · intro l _ hl
          simp [hl]
        · simp
      · intro k _ hk
        apply Finset.sum_eq_zero
        intro l _
        simp [hk]
      · simp
    · intro j _ hj
      apply Finset.sum_eq_zero
      intro k _
      apply Finset.sum_eq_zero
      intro l _
      simp [hj]
    · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro l _
    simp [hi]
  · simp

private abbrev maxReferenceType
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus] : Type _ :=
  y × Sum (y × bPlus) ((a × x) × ((a × bPlus) × (x × y)))

private instance maxReferenceTypeFintype
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus] :
    Fintype (maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus)) := by
  dsimp [maxReferenceType]
  infer_instance

private instance maxReferenceTypeDecidableEq
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus] :
    DecidableEq (maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus)) := by
  exact Classical.decEq _

omit [DecidableEq a] [DecidableEq x] [DecidableEq y] in
private theorem maxReferenceType_card_ge_complement
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    [Nonempty y] :
    Fintype.card ((a × x) × ((a × bPlus) × (x × y))) ≤
      Fintype.card (maxReferenceType (a := a) (x := x) (y := y)
        (bPlus := bPlus)) := by
  let y0 : y := Classical.choice (inferInstance : Nonempty y)
  apply Fintype.card_le_of_injective
    (fun z : (a × x) × ((a × bPlus) × (x × y)) =>
      (y0, Sum.inr z))
  intro p q h
  have hs : Sum.inr p = Sum.inr q := congrArg Prod.snd h
  exact by cases hs; rfl

private theorem maxReferenceUhlmann
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    [Nonempty y]
    {etaCenter eta : State ((a × x) × ((a × bPlus) × (x × y)))}
    (Psi : PureVector
      (Prod (maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus))
        ((a × x) × ((a × bPlus) × (x × y)))))
    (hPsi : Psi.Purifies etaCenter) :
    ∃ Phi : PureVector
      (Prod (maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus))
        ((a × x) × ((a × bPlus) × (x × y)))),
      Phi.Purifies eta ∧ Psi.overlapSq Phi = etaCenter.squaredFidelity eta := by
  exact PureVector.exists_purification_with_overlapSq_eq_squaredFidelity
    (ρ := etaCenter) (σ := eta) hPsi
      (maxReferenceType_card_ge_complement (a := a) (x := x) (y := y)
        (bPlus := bPlus))

private def maxReferenceEmbedding
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus] :
    ReferenceIsometry (y × bPlus) (maxReferenceType (a := a) (x := x) (y := y)
      (bPlus := bPlus)) :=
  ReferenceIsometry.ofInjective
    (α := y × bPlus)
    (β := y × Sum (y × bPlus) ((a × x) × ((a × bPlus) × (x × y))))
    (fun (p : y × bPlus) => (p.1, Sum.inl p)) (by
      intro p q h
      have hy : p.1 = q.1 :=
        congrArg (fun z : y × Sum (y × bPlus)
          ((a × x) × ((a × bPlus) × (x × y))) => z.1) h
      have hs : Sum.inl p = Sum.inl q :=
        congrArg (fun z : y × Sum (y × bPlus)
          ((a × x) × ((a × bPlus) × (x × y))) => z.2) h
      exact Prod.ext hy (by cases hs; rfl))

private def maxConditioningEmbedding
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus] :
    ReferenceIsometry (y × bPlus)
      (y × maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus)) :=
  ReferenceIsometry.ofInjective
    (α := y × bPlus)
    (β := y × (y × Sum (y × bPlus) ((a × x) × ((a × bPlus) × (x × y)))))
    (fun (p : y × bPlus) => (p.1, (p.1, Sum.inl p))) (by
      intro p q h
      have hy : p.1 = q.1 :=
        congrArg (fun z : y × (y × Sum (y × bPlus)
          ((a × x) × ((a × bPlus) × (x × y)))) => z.1) h
      have hs : Sum.inl p = Sum.inl q :=
        congrArg (fun z : y × (y × Sum (y × bPlus)
          ((a × x) × ((a × bPlus) × (x × y)))) => z.2.2) h
      exact Prod.ext hy (by cases hs; rfl))

private def maxLiftedCanonicalPurification
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (rho : State ((a × x) × (y × bPlus)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    PureVector (Prod (maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus))
      ((a × x) × ((a × bPlus) × (x × y)))) :=
  (maxReferenceEmbedding (bPlus := bPlus)).applyPureVector
    (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := bPlus) rho hclassical)

private theorem maxLiftedCanonicalPurification_fixed
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (rho : State ((a × x) × (y × bPlus)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    classicalCoherentMap (a := a) (x := x) (c := a × bPlus) (y' := y)
      ((maxLiftedCanonicalPurification (a := a) (x := x) (y := y) (bPlus := bPlus)
        rho hclassical).amplitudeMatrix *
        (maxLiftedCanonicalPurification (a := a) (x := x) (y := y) (bPlus := bPlus)
          rho hclassical).amplitudeMatrix.conjTranspose) =
      (maxLiftedCanonicalPurification (a := a) (x := x) (y := y) (bPlus := bPlus)
        rho hclassical).amplitudeMatrix *
        (maxLiftedCanonicalPurification (a := a) (x := x) (y := y) (bPlus := bPlus)
          rho hclassical).amplitudeMatrix.conjTranspose := by
  let psi : PureVector (Prod (maxReferenceType (a := a) (x := x) (y := y)
      (bPlus := bPlus)) ((a × x) × ((a × bPlus) × (x × y)))) :=
    maxLiftedCanonicalPurification
    (a := a) (x := x) (y := y) (bPlus := bPlus) rho hclassical
  have hpur : psi.Purifies (canonicalXYComplementaryState
      (a := a) (x := x) (y := y) (b := bPlus) rho) := by
    exact (maxReferenceEmbedding (bPlus := bPlus)).applyPureVector_purifies
      (canonicalXYMaxPurification_purifies (a := a) (x := x) (y := y)
        (b := bPlus) rho hclassical)
  have hmarg : psi.state.marginalB = canonicalXYComplementaryState
      (a := a) (x := x) (y := y) (b := bPlus) rho := by
    apply State.ext
    simpa [State.marginalB_matrix] using hpur
  have hgram :
      (psi.amplitudeMatrix * psi.amplitudeMatrix.conjTranspose :
        CMatrix ((a × x) × ((a × bPlus) × (x × y)))) =
      psi.state.marginalB.matrix := by
    rw [State.marginalB_matrix, PureVector.state_matrix,
      PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose]
  have hclass := canonicalXYComplementaryState_classicalCoherentOn
    (a := a) (x := x) (y := y) (b := bPlus) rho hclassical
  change classicalCoherentMap (a := a) (x := x) (c := a × bPlus) (y' := y)
      (psi.amplitudeMatrix * psi.amplitudeMatrix.conjTranspose) =
      psi.amplitudeMatrix * psi.amplitudeMatrix.conjTranspose
  rw [hgram, hmarg]
  have hfixed := classicalCoherentMap_fixed hclass
  have hfixedMatrix := congrArg SubnormalizedState.matrix hfixed
  simpa [SubnormalizedState.applyTraceNonincreasingCP_matrix] using hfixedMatrix

/-
private theorem coherentMaxPure_canonical_eq_reindex
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    coherentMaxPure (a := a) (x := x) (b := y × b) (c := a × b) (y' := y)
        (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := b)
          rho hclassical)
        (canonicalXYMaxPurification_fixed (a := a) (x := x) (y := y) (b := b)
          rho hclassical) =
      (canonicalXYCoherentPurification (a := a) (x := x) (y := y) (b := b) rho).reindex
        (Equiv.prodComm ((a × b) × (x × y)) ((a × x) × (y × b))) := by
  apply PureVector.ext_amp
  funext z
  simp [coherentMaxPure, coherentLiftOfFixed, coherentLiftAmplitude,
    State.acToABReferenceEquiv, coherentMaxSwapEquiv,
    PureVector.reindex, PureVector.reindex_amp,
    canonicalXYMaxPurification, canonicalXYCoherentPurification,
    PureVector.ofAmplitudeMatrix, Equiv.prodComm, Equiv.prodComm_apply,
    Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_apply_apply,
    Equiv.symm_symm, Prod.swap_prod_mk,
    Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_ite_eq', apply_ite, eq_comm, Prod.ext_iff,
    mul_assoc, mul_comm]

private theorem maxLifted_coherentMaxPure_eq_apply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (rho : State ((a × x) × (y × bPlus)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    coherentMaxPure (a := a) (x := x) (b := y × bPlus)
        (c := a × bPlus) (y' := y)
        (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
          (bPlus := bPlus) rho hclassical)
        (maxLiftedCanonicalPurification_fixed (a := a) (x := x) (y := y)
          (bPlus := bPlus) rho hclassical) =
      (ReferenceIsometry.prod
        (ReferenceIsometry.ofEquiv (Equiv.refl (a × x)))
        (maxConditioningEmbedding (a := a) (x := x) (y := y)
          (bPlus := bPlus))).applyPureVector
        (coherentMaxPure (a := a) (x := x) (b := y × bPlus)
          (c := a × bPlus) (y' := y)
          (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := bPlus)
            rho hclassical)
          (canonicalXYMaxPurification_fixed (a := a) (x := x) (y := y) (b := bPlus)
            rho hclassical)) := by
  apply PureVector.ext_amp
  funext z
  simp [maxLiftedCanonicalPurification, maxReferenceEmbedding,
    maxConditioningEmbedding, coherentMaxPure, coherentLiftOfFixed,
    coherentLiftAmplitude, State.acToABReferenceEquiv,
    coherentMaxSwapEquiv, PureVector.reindex, PureVector.reindex_amp,
    ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.ofInjective,
    ReferenceIsometry.prod, ReferenceIsometry.ofEquiv, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum, Finset.sum_ite_eq', apply_ite, eq_comm,
    Prod.ext_iff, mul_assoc, mul_comm]
-/

private theorem smoothClassical_sum_ite_pair
    {α β γ : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [AddCommMonoid γ]
    (f : α → β → γ) (a : α) (b : β) :
    (∑ x : α, ∑ y : β, if x = a ∧ y = b then f x y else 0) = f a b := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro y _ hy
      simp [hy]
    · simp
  · intro x _ hx
    apply Finset.sum_eq_zero
    intro y _
    simp [hx]
  · simp

private theorem smoothClassical_sum_ite_pair_rev
    {α β γ : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [AddCommMonoid γ]
    (f : α → β → γ) (a : α) (b : β) :
    (∑ x : α, ∑ y : β, if a = x ∧ b = y then f x y else 0) = f a b := by
  simpa [eq_comm] using smoothClassical_sum_ite_pair f a b

private theorem smoothClassical_if_pair3_zero
    {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    [Zero γ] (p q : α) (s : β) (z : α) (w : β) (u : γ)
    (hbad : ¬ (p = z ∧ q = z)) :
    (if p = z ∧ q = z ∧ s = w then u else 0) = 0 := by
  by_cases hp : p = z
  · by_cases hq : q = z
    · exact False.elim (hbad ⟨hp, hq⟩)
    · simp [hp, hq]
  · simp [hp]

private theorem smoothClassical_if_pair4_zero
    {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    [Zero γ] (p q r : α) (s : β) (z : α) (w : β) (u : γ)
    (hbad : ¬ (q = z ∧ r = z)) :
    (if p = z ∧ q = z ∧ r = z ∧ s = w then u else 0) = 0 := by
  by_cases hp : p = z
  · by_cases hq : q = z
    · by_cases hr : r = z
      · exact False.elim (hbad ⟨hq, hr⟩)
      · simp [hp, hq, hr]
    · simp [hp, hq]
  · simp [hp]

/-
private theorem coherentMaxPure_canonical_eq_reindex
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    coherentMaxPure
        (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := b)
          rho hclassical)
        (canonicalXYMaxPurification_fixed (a := a) (x := x) (y := y) (b := b)
          rho hclassical) =
      (canonicalXYCoherentPurification (a := a) (x := x) (y := y) (b := b) rho).reindex
        (Equiv.prodComm ((a × b) × (x × y)) ((a × x) × (y × b))) := by
  apply PureVector.ext_amp
  funext z
  simp [coherentMaxPure, coherentLiftOfFixed, coherentLiftAmplitude,
    State.acToABReferenceEquiv, coherentMaxSwapEquiv,
    PureVector.reindex, PureVector.reindex_amp,
    canonicalXYMaxPurification, canonicalXYCoherentPurification,
    PureVector.ofAmplitudeMatrix, Equiv.prodComm,
    Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_ite_eq', apply_ite, eq_comm, Prod.ext_iff,
    mul_assoc, mul_comm]

private theorem smoothClassical_referenceIsometry_partialTraceB_applyMatrix
    {r r' s : Type*} [Fintype r] [DecidableEq r]
    [Fintype r'] [DecidableEq r'] [Fintype s] [DecidableEq s]
    (V : ReferenceIsometry r r') (X : CMatrix (Prod r s)) :
    partialTraceB (a := r') (b := s) (V.applyMatrix X) =
      V.matrix * partialTraceB (a := r) (b := s) X *
        Matrix.conjTranspose V.matrix := by
  ext i j
  simp [partialTraceB, ReferenceIsometry.applyMatrix,
    ReferenceIsometry.targetBlock, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

private theorem smoothClassical_referenceIsometry_marginalA_applyPureVector
    {r r' s : Type*} [Fintype r] [DecidableEq r]
    [Fintype r'] [DecidableEq r'] [Fintype s] [DecidableEq s]
    (V : ReferenceIsometry r r') (Psi : PureVector (Prod r s)) :
    (V.applyPureVector Psi).state.marginalA.matrix =
      V.matrix * Psi.state.marginalA.matrix * Matrix.conjTranspose V.matrix := by
  rw [State.marginalA_matrix, PureVector.state_matrix,
    ReferenceIsometry.applyPureVector_amp, V.rankOne_applyAmp]
  rw [smoothClassical_referenceIsometry_partialTraceB_applyMatrix]
  rfl

private theorem smoothClassical_referenceIsometry_prod_refl_applyMatrix
    {s r r' : Type*} [Fintype s] [DecidableEq s]
    [Fintype r] [DecidableEq r] [Fintype r'] [DecidableEq r']
    (V : ReferenceIsometry r r') (X : CMatrix (Prod s r)) :
    (ReferenceIsometry.prod (ReferenceIsometry.ofEquiv (Equiv.refl s)) V).applyMatrix X =
      V.applyMatrixRight X := by
  ext i j
  simp [ReferenceIsometry.prod, ReferenceIsometry.ofEquiv,
    ReferenceIsometry.applyMatrix, ReferenceIsometry.applyMatrixRight,
    ReferenceIsometry.targetBlock, ReferenceIsometry.rightBlock,
    Matrix.kronecker, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum,
    mul_assoc, mul_comm]
-/

private theorem canonicalXYCoherentPurification_reindex_marginalA
    (rho : State ((a × x) × (y × b))) :
    ((canonicalXYCoherentPurification (a := a) (x := x) (y := y) (b := b) rho).reindex
      (Equiv.prodComm ((a × b) × (x × y)) ((a × x) × (y × b)))).state.marginalA =
      rho := by
  have hpur := canonicalXYCoherentPurification_purifies
    (a := a) (x := x) (y := y) (b := b) rho
  rw [PureVector.purifies_iff] at hpur
  apply State.ext
  simpa [PureVector.reindex_state, State.reindex, State.marginalA,
    partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
    Equiv.prodComm] using hpur

private theorem canonicalXYMaxAmplitude_gram_eq
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY)
    (ia ja : a) (ix : x) (iy : y) (ib jb : b) :
    (∑ q : a × b,
      canonicalXYMaxAmplitude (a := a) (x := x) (y := y) (b := b) rho
        ((ia, ix), (q, (ix, iy))) (iy, ib) *
        star (canonicalXYMaxAmplitude (a := a) (x := x) (y := y) (b := b) rho
          ((ja, ix), (q, (ix, iy))) (iy, jb))) =
      rho.matrix ((ia, ix), (iy, ib)) ((ja, ix), (iy, jb)) := by
  have hpur := canonicalXYCoherentPurification_purifies
    (a := a) (x := x) (y := y) (b := b) rho
  rw [PureVector.purifies_iff] at hpur
  have hentry := congrArg
    (fun M : CMatrix ((a × x) × (y × b)) =>
      M ((ia, ix), (iy, ib)) ((ja, ix), (iy, jb))) hpur
  have hzero := canonicalXYCoherentPurification_amp_zero_of_copy_mismatch
    (a := a) (x := x) (y := y) (b := b) rho hclassical
  have hentry' :
      rho.matrix ((ia, ix), (iy, ib)) ((ja, ix), (iy, jb)) =
        ∑ r : (a × b) × (x × y),
          (canonicalXYCoherentPurification (a := a) (x := x) (y := y)
            (b := b) rho).amp
            (r, ((ia, ix), (iy, ib))) *
          star ((canonicalXYCoherentPurification (a := a) (x := x) (y := y)
            (b := b) rho).amp (r, ((ja, ix), (iy, jb)))) := by
    simpa [State.marginalB_matrix, PureVector.state_matrix, partialTraceA,
      rankOneMatrix_apply, canonicalXYCoherentPurification,
      State.reindex, PureVector.reindex, xyABReferenceEquiv,
      xyABReindexEquiv] using hentry.symm
  rw [Fintype.sum_prod_type] at hentry'
  have hcollapse (q : a × b) :
      (∑ r : x × y,
        (canonicalXYCoherentPurification (a := a) (x := x) (y := y)
          (b := b) rho).amp
            ((q, r), ((ia, ix), (iy, ib))) *
        star ((canonicalXYCoherentPurification (a := a) (x := x) (y := y)
          (b := b) rho).amp ((q, r), ((ja, ix), (iy, jb))))) =
        (canonicalXYCoherentPurification (a := a) (x := x) (y := y)
          (b := b) rho).amp
            ((q, (ix, iy)), ((ia, ix), (iy, ib))) *
        star ((canonicalXYCoherentPurification (a := a) (x := x) (y := y)
          (b := b) rho).amp ((q, (ix, iy)), ((ja, ix), (iy, jb)))) := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single ix]
    · rw [Finset.sum_eq_single iy]
      · intro iy' _ hiy'
        have hz := hzero (q, (ix, iy')) ((ia, ix), (iy, ib)) (by
          intro h
          apply hiy'
          exact congrArg Prod.snd h)
        simp [hz]
      · simp
    · intro ix' _ hix'
      apply Finset.sum_eq_zero
      intro iy' _
      have hz := hzero (q, (ix', iy')) ((ia, ix), (iy, ib)) (by
        intro h
        apply hix'
        exact congrArg Prod.fst h)
      simp [hz]
    · simp
  simp_rw [hcollapse] at hentry'
  simpa [canonicalXYMaxAmplitude, Prod.ext_iff, mul_assoc, mul_comm]
    using hentry'.symm

/-
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private theorem maxLiftedCanonicalPurification_center
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (rho : State ((a × x) × (y × bPlus)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    (coherentMaxPure (a := a) (x := x)
      (b := maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus))
      (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
        (bPlus := bPlus) rho hclassical)
    (maxLiftedCanonicalPurification_fixed (a := a) (x := x) (y := y)
        (bPlus := bPlus) rho hclassical)).state.marginalA =
      rho.conditioningIsometryApply (maxConditioningEmbedding
        (a := a) (x := x) (y := y) (bPlus := bPlus)) := by
  apply State.ext
  ext i j
  let psi := maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
    (bPlus := bPlus) rho hclassical
  let hpsi := maxLiftedCanonicalPurification_fixed (a := a) (x := x)
    (y := y) (bPlus := bPlus) rho hclassical
  let omega := coherentMaxPure (a := a) (x := x)
    (b := maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus))
    psi hpsi
  have hLx (h : i.1.2 ≠ j.1.2) : omega.state.marginalA.matrix i j = 0 := by
    rw [State.marginalA_matrix]
    simpa [omega, PureVector.state_matrix, rankOneMatrix_apply] using
      (coherentMaxPure_amp_X (a := a) (x := x)
        (b := maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus))
        (c := a × bPlus) (y' := y) psi hpsi i j h)
  have hLy (h : i.2.1 ≠ j.2.1) : omega.state.marginalA.matrix i j = 0 := by
    rw [State.marginalA_matrix]
    simpa [omega, PureVector.state_matrix, rankOneMatrix_apply] using
      (coherentMaxPure_amp_Y (a := a) (x := x)
        (b := maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus))
        (c := a × bPlus) (y' := y) psi hpsi i j h)
  let V := maxConditioningEmbedding (a := a) (x := x) (y := y)
    (bPlus := bPlus)
  have hV : ∀ q p, q.1 ≠ p.1 → V.matrix q p = 0 := by
    intro q p hqp
    have hne : q ≠ (p.1, (p.1, Sum.inl p)) := by
      intro heq
      exact hqp (congrArg Prod.fst heq)
    simp [V, maxConditioningEmbedding, ReferenceIsometry.ofInjective, hne]
  have hRx (h : i.1.2 ≠ j.1.2) :
      (rho.conditioningIsometryApply V).matrix i j = 0 := by
    rw [State.conditioningIsometryApply_matrix]
    change (V.matrix * ReferenceIsometry.rightBlock rho.matrix i.1 j.1 *
      Matrix.conjTranspose V.matrix) i.2 j.2 = 0
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [mul_eq_zero]
    left
    apply Finset.sum_eq_zero
    intro l _
    simp only [ReferenceIsometry.rightBlock]
    have hz := hclassical.1 (i.1, l) (j.1, k) h
    rw [show rho.matrix (i.1, l) (j.1, k) = 0 by simpa using hz]
    simp
  have hRy (h : i.2.1 ≠ j.2.1) :
      (rho.conditioningIsometryApply V).matrix i j = 0 := by
    rw [State.conditioningIsometryApply_matrix]
    change (V.matrix * ReferenceIsometry.rightBlock rho.matrix i.1 j.1 *
      Matrix.conjTranspose V.matrix) i.2 j.2 = 0
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : j.2.1 = k.1
    · rw [mul_eq_zero]
      left
      apply Finset.sum_eq_zero
      intro l _
      simp only [ReferenceIsometry.rightBlock]
      by_cases hl : i.2.1 = l.1
      · have hy : l.1 ≠ k.1 := by
          intro hEq
          apply h
          exact hl.trans (hEq.trans hk.symm)
        have hz := hclassical.2 (i.1, l) (j.1, k) hy
        rw [show rho.matrix (i.1, l) (j.1, k) = 0 by simpa using hz]
        simp
      · rw [show V.matrix i.2 l = 0 by apply hV; exact hl]
        simp
    · rw [mul_eq_zero]
      right
      rw [show V.matrix j.2 k = 0 by apply hV; exact hk]
      simp
  by_cases hix : i.1.2 ≠ j.1.2
  · simpa [omega, V] using (hLx hix).trans (hRx hix).symm
  · by_cases hiy : i.2.1 ≠ j.2.1
    · simpa [omega, V] using (hLy hiy).trans (hRy hiy).symm
    · simp only [not_not] at hix hiy
      rcases i with ⟨⟨ia, ix⟩, ⟨iy, ⟨iy2, iTag⟩⟩⟩
      rcases j with ⟨⟨ja, jx⟩, ⟨jy, ⟨jy2, jTag⟩⟩⟩
      have hx : ix = jx := by simpa using hix
      have hy : iy = jy := by simpa using hiy
      subst jx
      subst jy
      rcases iTag with ⟨iy', ib⟩ | iExtra
      · rcases jTag with ⟨jy', jb⟩ | jExtra
        · simp [omega, V, hix, hiy, coherentMaxPure, coherentLiftOfFixed,
            coherentLiftAmplitude, State.acToABReferenceEquiv,
            coherentMaxSwapEquiv, PureVector.reindex,
            PureVector.reindex_state, State.reindex, State.marginalA,
            partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
            PureVector.ofAmplitudeMatrix, Equiv.prodComm,
            maxLiftedCanonicalPurification, maxReferenceEmbedding,
            maxConditioningEmbedding, canonicalXYMaxPurification,
            ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
            ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
            ReferenceIsometry.ofInjective, Matrix.mul_apply,
            Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
            Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_mul,
            Finset.mul_sum, Finset.sum_ite_eq', apply_ite, eq_comm,
            Prod.ext_iff, mul_assoc, mul_comm]
          by_cases hi2 : iy = iy2
          · by_cases hi' : iy = iy'
            · by_cases hj2 : iy = jy2
              · by_cases hj' : iy = jy'
                · simp only [hi2, hi', hj2, hj']
                  simpa [canonicalXYMaxAmplitude, canonicalXYCoherentPurification,
                    Fintype.sum_prod_type, Finset.sum_ite_eq', Finset.sum_ite_eq,
                    Finset.sum_mul, Finset.mul_sum, apply_ite, eq_comm,
                    Prod.ext_iff, mul_assoc, mul_comm] using
                    (canonicalXYMaxAmplitude_gram_eq
                      (a := a) (x := x) (y := y) (b := bPlus) rho hclassical
                      ia ja ix iy2 ib jb)
                · have hno : ∀ z : y, ¬ (jy2 = z ∧ jy' = z) := by
                    intro z hz
                    exact hj' (hj2.trans (hz.1.trans hz.2.symm))
                  have hzeroL (z : y) (w : bPlus) (u : ℂ) :
                      (if iy2 = z ∧ jy2 = z ∧ jy' = z ∧ jb = w then u else 0) = 0 :=
                    smoothClassical_if_pair4_zero iy2 jy2 jy' jb z w u (hno z)
                  have hzeroR (z : y) (w : bPlus) (u : ℂ) :
                      (if jy2 = z ∧ jy' = z ∧ jb = w then u else 0) = 0 :=
                    smoothClassical_if_pair3_zero jy2 jy' jb z w u (hno z)
                  simp_rw [hzeroL, hzeroR]
                  simp
              · have hno : ∀ z : y, ¬ (iy2 = z ∧ jy2 = z) := by
                  intro z hz
                  exact hj2 (hi2.trans (hz.1.trans hz.2.symm))
                have hzeroL (z : y) (w : bPlus) (u : ℂ) :
                    (if iy2 = z ∧ jy2 = z ∧ jy' = z ∧ jb = w then u else 0) = 0 :=
                  smoothClassical_if_pair4_zero iy2 jy2 jy' jb z w u (hno z)
                have hcross : iy2 ≠ jy2 := by
                  intro h
                  exact hj2 (hi2.trans h)
                have hzeroR (z : x) (w : y) (u : ℂ)
                    (g : y → bPlus → ℂ) :
                    (if ix = z ∧ iy2 = w then
                      if ix = z ∧ iy2 = w then
                        u * (∑ z' : y, ∑ w' : bPlus,
                          if jy2 = z' ∧ jy' = z' ∧ jb = w' then
                            if w = z' then g z' w' else 0 else 0)
                      else 0 else 0) = 0 := by
                  by_cases hx' : ix = z
                  · by_cases hw' : iy2 = w
                    · have hsum :
                          (∑ z' : y, ∑ w' : bPlus,
                            if jy2 = z' ∧ jy' = z' ∧ jb = w' then
                              if w = z' then g z' w' else 0 else 0) = 0 := by
                        apply Finset.sum_eq_zero
                        intro z' _
                        apply Finset.sum_eq_zero
                        intro w' _
                        by_cases h1 : jy2 = z' <;> by_cases h2 : jy' = z'
                        · have h3 : w ≠ z' := by
                            intro h3
                            apply hcross
                            exact hw'.trans (h3.trans h1.symm)
                          simp [h1, h2, h3]
                        · simp [h1, h2]
                        · simp [h1, h2]
                        · simp [h1, h2]
                      simp [hx', hw', hsum]
                    · simp [hx', hw']
                  · simp [hx']
                simp_rw [hzeroL, hzeroR]
                simp
            · have hno : ∀ z : y, ¬ (iy2 = z ∧ iy' = z) := by
                intro z hz
                exact hi' (hi2.trans (hz.1.trans hz.2.symm))
              have hzero (z : y) (w : bPlus) (u : ℂ) :
                  (if iy2 = z ∧ iy' = z ∧ ib = w then u else 0) = 0 :=
                smoothClassical_if_pair3_zero iy2 iy' ib z w u (hno z)
              simp_rw [hzero]
              simp
          · have hno : ∀ z : y, ¬ (iy = z ∧ iy2 = z) := by
              intro z hz
              exact hi2 (hz.1.trans hz.2.symm)
            have hzeroL (z : y) (w : bPlus) (u : ℂ) :
                (if iy = z ∧ iy2 = z ∧ iy' = z ∧ ib = w then u else 0) = 0 :=
              smoothClassical_if_pair4_zero iy iy2 iy' ib z w u (hno z)
            have hcross : iy ≠ iy2 := by
              intro h
              exact hi2 h
            have hzeroR (z : x) (w : y) (u : ℂ)
                (g : y → bPlus → ℂ) :
                (if ix = z ∧ iy = w then
                  if ix = z ∧ iy = w then
                    (∑ z' : y, ∑ w' : bPlus,
                      if iy2 = z' ∧ iy' = z' ∧ ib = w' then
                        if w = z' then g z' w' else 0 else 0) * u
                  else 0 else 0) = 0 := by
              by_cases hx' : ix = z
              · by_cases hw' : iy = w
                · have hsum :
                      (∑ z' : y, ∑ w' : bPlus,
                        if iy2 = z' ∧ iy' = z' ∧ ib = w' then
                          if w = z' then g z' w' else 0 else 0) = 0 := by
                    apply Finset.sum_eq_zero
                    intro z' _
                    apply Finset.sum_eq_zero
                    intro w' _
                    by_cases h1 : iy2 = z' <;> by_cases h2 : iy' = z'
                    · have h3 : w ≠ z' := by
                        intro h3
                        apply hcross
                        exact hw'.trans (h3.trans h1.symm)
                      simp [h1, h2, h3]
                    · simp [h1, h2]
                    · simp [h1, h2]
                    · simp [h1, h2]
                  simp [hx', hw', hsum]
                · simp [hx', hw']
              · simp [hx']
            simp_rw [hzeroL, hzeroR]
            simp
        · simp [omega, V, hix, hiy, coherentMaxPure, coherentLiftOfFixed,
            coherentLiftAmplitude, State.acToABReferenceEquiv,
            coherentMaxSwapEquiv, PureVector.reindex,
            PureVector.reindex_state, State.reindex, State.marginalA,
            partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
            PureVector.ofAmplitudeMatrix, Equiv.prodComm,
            maxLiftedCanonicalPurification, maxReferenceEmbedding,
            maxConditioningEmbedding, canonicalXYMaxPurification,
            ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
            ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
            ReferenceIsometry.ofInjective, Matrix.mul_apply,
            Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
            Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_mul,
            Finset.mul_sum, Finset.sum_ite_eq', apply_ite, eq_comm,
            Prod.ext_iff, mul_assoc, mul_comm]
-/

/-
private theorem smoothClassical_maxLifted_coherentMaxPure_eq_apply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (rho : State ((a × x) × (y × bPlus)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    coherentMaxPure
        (a := a) (x := x)
        (b := maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus))
        (c := a × bPlus) (y' := y)
        (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
          (bPlus := bPlus) rho hclassical)
        (maxLiftedCanonicalPurification_fixed (a := a) (x := x) (y := y)
          (bPlus := bPlus) rho hclassical) =
      (ReferenceIsometry.prod
        (ReferenceIsometry.ofEquiv (Equiv.refl (a × x)))
        (maxConditioningEmbedding (a := a) (x := x) (y := y)
        (bPlus := bPlus))).applyPureVector
        (coherentMaxPure
          (a := a) (x := x) (b := y × bPlus) (c := a × bPlus) (y' := y)
          (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := bPlus)
            rho hclassical)
          (canonicalXYMaxPurification_fixed (a := a) (x := x) (y := y) (b := bPlus)
            rho hclassical)) := by
  apply PureVector.ext_amp
  funext z
  simp [maxLiftedCanonicalPurification, maxReferenceEmbedding,
    maxConditioningEmbedding, coherentMaxPure, coherentLiftOfFixed,
    coherentLiftAmplitude, State.acToABReferenceEquiv,
    coherentMaxSwapEquiv, PureVector.reindex, PureVector.reindex_amp,
    ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.ofInjective,
    ReferenceIsometry.prod, ReferenceIsometry.ofEquiv, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum, Finset.sum_ite_eq', apply_ite, eq_comm,
    Prod.ext_iff, mul_assoc, mul_comm]

private theorem smoothClassical_referenceIsometry_marginalA_applyPureVector
    {r r' s : Type*} [Fintype r] [DecidableEq r]
    [Fintype r'] [DecidableEq r'] [Fintype s] [DecidableEq s]
    (V : ReferenceIsometry r r') (Psi : PureVector (Prod r s)) :
    (V.applyPureVector Psi).state.marginalA.matrix =
      V.matrix * Psi.state.marginalA.matrix * Matrix.conjTranspose V.matrix := by
  rw [State.marginalA_matrix, PureVector.state_matrix,
    ReferenceIsometry.applyPureVector_amp, V.rankOne_applyAmp]
  ext i j
  simp [partialTraceB, ReferenceIsometry.applyMatrix,
    ReferenceIsometry.targetBlock, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

private theorem smoothClassical_referenceIsometry_prod_refl_applyMatrix
    {s r r' : Type*} [Fintype s] [DecidableEq s]
    [Fintype r] [DecidableEq r] [Fintype r'] [DecidableEq r']
    (V : ReferenceIsometry r r') (X : CMatrix (Prod s r)) :
    (ReferenceIsometry.prod
      (ReferenceIsometry.ofEquiv (Equiv.refl s) : ReferenceIsometry s s) V).applyMatrix X =
      V.applyMatrixRight X := by
  ext i j
  simp [ReferenceIsometry.prod, ReferenceIsometry.ofEquiv,
    ReferenceIsometry.applyMatrix, ReferenceIsometry.applyMatrixRight,
    ReferenceIsometry.targetBlock, ReferenceIsometry.rightBlock,
    Matrix.kronecker, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum,
    mul_assoc, mul_comm]

private theorem maxLiftedCanonicalPurification_center_fast
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (rho : State ((a × x) × (y × bPlus)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    (coherentMaxPure (a := a) (x := x)
      (b := maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus))
      (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
        (bPlus := bPlus) rho hclassical)
      (maxLiftedCanonicalPurification_fixed (a := a) (x := x) (y := y)
        (bPlus := bPlus) rho hclassical)).state.marginalA =
      rho.conditioningIsometryApply (maxConditioningEmbedding
        (a := a) (x := x) (y := y) (bPlus := bPlus)) := by
  let omega0 := coherentMaxPure
    (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := bPlus)
      rho hclassical)
    (canonicalXYMaxPurification_fixed (a := a) (x := x) (y := y) (b := bPlus)
      rho hclassical)
  let W := ReferenceIsometry.prod
    (ReferenceIsometry.ofEquiv (Equiv.refl (a × x)))
    (maxConditioningEmbedding (a := a) (x := x) (y := y) (bPlus := bPlus))
  have hbridge := maxLifted_coherentMaxPure_eq_apply
    (a := a) (x := x) (y := y) (bPlus := bPlus) rho hclassical
  have hcanonical := coherentMaxPure_canonical_eq_reindex
    (a := a) (x := x) (y := y) (b := bPlus) rho hclassical
  have hcanonicalMarg : omega0.state.marginalA = rho := by
    calc
      omega0.state.marginalA =
          ((canonicalXYCoherentPurification (a := a) (x := x)
            (y := y) (b := bPlus) rho).reindex
            (Equiv.prodComm ((a × bPlus) × (x × y))
              ((a × x) × (y × bPlus)))).state.marginalA := by
        exact congrArg (fun Psi : PureVector
          (Prod ((a × x) × (y × bPlus)) ((a × bPlus) × (x × y))) =>
          Psi.state.marginalA) hcanonical
      _ = rho := canonicalXYCoherentPurification_reindex_marginalA
        (a := a) (x := x) (y := y) (b := bPlus) rho
  apply State.ext
  have hW := smoothClassical_referenceIsometry_marginalA_applyPureVector W omega0
  have hWmatrix := smoothClassical_referenceIsometry_prod_refl_applyMatrix
    (s := a × x)
    (maxConditioningEmbedding (a := a) (x := x) (y := y) (bPlus := bPlus))
    omega0.state.marginalA.matrix
  have hstate :
      (coherentMaxPure (a := a) (x := x)
        (b := maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus))
        (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
          (bPlus := bPlus) rho hclassical)
        (maxLiftedCanonicalPurification_fixed (a := a) (x := x) (y := y)
          (bPlus := bPlus) rho hclassical)).state.marginalA.matrix =
      (W.applyPureVector omega0).state.marginalA.matrix := by
    exact congrArg (fun Psi : PureVector
      (Prod ((a × x) × (y × maxReferenceType (a := a) (x := x)
        (y := y) (bPlus := bPlus))) ((a × bPlus) × (x × y))) =>
      Psi.state.marginalA.matrix) hbridge
  rw [hstate, hW, hcanonicalMarg, hWmatrix]
  rfl

 -/
/-
set_option maxHeartbeats 100000000 in
private theorem maxLiftedCanonicalPurification_center_simple
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (rho : State ((a × x) × (y × bPlus)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    (coherentMaxPure (a := a) (x := x)
      (b := maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus))
      (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
        (bPlus := bPlus) rho hclassical)
      (maxLiftedCanonicalPurification_fixed (a := a) (x := x) (y := y)
        (bPlus := bPlus) rho hclassical)).state.marginalA =
      rho.conditioningIsometryApply (maxConditioningEmbedding
        (a := a) (x := x) (y := y) (bPlus := bPlus)) := by
  let omega0 := coherentMaxPure
    (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := bPlus)
      rho hclassical)
    (canonicalXYMaxPurification_fixed (a := a) (x := x) (y := y) (b := bPlus)
      rho hclassical)
  let W := ReferenceIsometry.prod
    (ReferenceIsometry.ofEquiv (Equiv.refl (a × x)))
    (maxConditioningEmbedding (a := a) (x := x) (y := y) (bPlus := bPlus))
  have hbridge := maxLifted_coherentMaxPure_eq_apply
    (a := a) (x := x) (y := y) (bPlus := bPlus) rho hclassical
  have hcanonical := coherentMaxPure_canonical_eq_reindex
    (a := a) (x := x) (y := y) (b := bPlus) rho hclassical
  have hcanonicalMarg : omega0.state.marginalA = rho := by
    calc
      omega0.state.marginalA =
          ((canonicalXYCoherentPurification (a := a) (x := x)
            (y := y) (b := bPlus) rho).reindex
            (Equiv.prodComm ((a × bPlus) × (x × y))
              ((a × x) × (y × bPlus)))).state.marginalA := by
        exact congrArg (fun Psi : PureVector
          (Prod ((a × x) × (y × bPlus)) ((a × bPlus) × (x × y))) =>
          Psi.state.marginalA) hcanonical
      _ = rho := canonicalXYCoherentPurification_reindex_marginalA
        (a := a) (x := x) (y := y) (b := bPlus) rho
  apply State.ext
  have hW := smoothClassical_referenceIsometry_marginalA_applyPureVector W omega0
  have hWmatrix := smoothClassical_referenceIsometry_prod_refl_applyMatrix
    (s := a × x)
    (maxConditioningEmbedding (a := a) (x := x) (y := y) (bPlus := bPlus))
    omega0.state.marginalA.matrix
  have hstate :
      (coherentMaxPure (a := a) (x := x)
        (b := maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus))
        (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
          (bPlus := bPlus) rho hclassical)
        (maxLiftedCanonicalPurification_fixed (a := a) (x := x) (y := y)
          (bPlus := bPlus) rho hclassical)).state.marginalA.matrix =
      (W.applyPureVector omega0).state.marginalA.matrix := by
    exact congrArg (fun Psi : PureVector
      (Prod ((a × x) × (y × maxReferenceType (a := a) (x := x)
        (y := y) (bPlus := bPlus))) ((a × bPlus) × (x × y))) =>
      Psi.state.marginalA.matrix) hbridge
  rw [hstate, hW, hcanonicalMarg, hWmatrix]
  rfl

-/

/-
private theorem maxLiftedCanonicalPurification_center
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (rho : State ((a × x) × (y × bPlus)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    (coherentMaxPure (a := a) (x := x)
      (b := maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus))
      (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
        (bPlus := bPlus) rho hclassical)
      (maxLiftedCanonicalPurification_fixed (a := a) (x := x) (y := y)
        (bPlus := bPlus) rho hclassical)).state.marginalA =
      rho.conditioningIsometryApply (maxConditioningEmbedding
        (a := a) (x := x) (y := y) (bPlus := bPlus)) := by
  let phi := canonicalXYMaxPurification
    (a := a) (x := x) (y := y) (b := bPlus) rho hclassical
  let hphi := canonicalXYMaxPurification_fixed
    (a := a) (x := x) (y := y) (b := bPlus) rho hclassical
  let omega0 := coherentMaxPure phi hphi
  let V := maxConditioningEmbedding (a := a) (x := x) (y := y)
    (bPlus := bPlus)
  let W := ReferenceIsometry.prod
    (ReferenceIsometry.ofEquiv (Equiv.refl (a × x))) V
  have hbridge := maxLifted_coherentMaxPure_eq_apply
    (a := a) (x := x) (y := y) (bPlus := bPlus) rho hclassical
  have hcanonical := coherentMaxPure_canonical_eq_reindex
    (a := a) (x := x) (y := y) (b := bPlus) rho hclassical
  have hcanonicalMarg : omega0.state.marginalA = rho := by
    calc
      omega0.state.marginalA =
          (canonicalXYCoherentPurification (a := a) (x := x)
            (y := y) (b := bPlus) rho).reindex
            (Equiv.prodComm ((a × bPlus) × (x × y))
              ((a × x) × (y × bPlus))).state.marginalA := by
        exact congrArg (fun Psi : PureVector
          (Prod ((a × x) × (y × bPlus)) ((a × bPlus) × (x × y))) =>
          Psi.state.marginalA) hcanonical
      _ = rho := canonicalXYCoherentPurification_reindex_marginalA
        (a := a) (x := x) (y := y) (b := bPlus) rho
  have hW := smoothClassical_referenceIsometry_marginalA_applyPureVector
    W omega0
  have hWmatrix := smoothClassical_referenceIsometry_prod_refl_applyMatrix
    (s := a × x) V omega0.state.marginalA.matrix
  have hstate :
      (coherentMaxPure (a := a) (x := x)
        (b := maxReferenceType (a := a) (x := x) (y := y)
          (bPlus := bPlus))
        (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
          (bPlus := bPlus) rho hclassical)
        (maxLiftedCanonicalPurification_fixed (a := a) (x := x) (y := y)
          (bPlus := bPlus) rho hclassical)).state.marginalA.matrix =
      (W.applyPureVector omega0).state.marginalA.matrix := by
    exact congrArg (fun Psi : PureVector
      (Prod ((a × x) × (y × maxReferenceType (a := a) (x := x)
        (y := y) (bPlus := bPlus))) ((a × bPlus) × (x × y))) =>
      Psi.state.marginalA.matrix) hbridge
  apply State.ext
  ext i j
  rw [hstate, hW]
  rw [hcanonicalMarg]
  rw [hWmatrix]
  rw [State.conditioningIsometryApply_matrix]
  rfl
-/

/-
      · rcases jTag with ⟨jy', jb⟩ | jExtra <;>
          simp [omega, V, hix, hiy, coherentMaxPure, coherentLiftOfFixed,
            coherentLiftAmplitude, State.acToABReferenceEquiv,
            coherentMaxSwapEquiv, PureVector.reindex,
            PureVector.reindex_state, State.reindex, State.marginalA,
            partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
            PureVector.ofAmplitudeMatrix, Equiv.prodComm,
            maxLiftedCanonicalPurification, maxReferenceEmbedding,
            maxConditioningEmbedding, canonicalXYMaxPurification,
            ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
            ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
            ReferenceIsometry.ofInjective, Matrix.mul_apply,
            Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
            Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_mul,
            Finset.mul_sum, Finset.sum_ite_eq', apply_ite, eq_comm,
            Prod.ext_iff, mul_assoc, mul_comm]
      /-
      rcases i with ⟨⟨ia, ix⟩, ⟨iy, ⟨iy2, iTag⟩⟩⟩
      rcases j with ⟨⟨ja, jx⟩, ⟨jy, ⟨jy2, jTag⟩⟩⟩
      rcases iTag with ⟨iy', ib⟩ | iExtra
      · rcases jTag with ⟨jy', jb⟩ | jExtra
        · by_cases hi2 : iy = iy2 <;>
            by_cases hi' : iy = iy' <;>
            by_cases hj2 : jy = jy2 <;>
            by_cases hj' : jy = jy' <;>
            simp [omega, V, hix, hiy, hi2, hi', hj2, hj',
              coherentMaxPure, coherentLiftOfFixed, coherentLiftAmplitude,
              State.acToABReferenceEquiv, coherentMaxSwapEquiv,
              PureVector.reindex, PureVector.reindex_state, State.reindex,
              State.marginalA, partialTraceB, PureVector.state_matrix,
              rankOneMatrix_apply, PureVector.ofAmplitudeMatrix,
              Equiv.prodComm, maxLiftedCanonicalPurification,
              maxReferenceEmbedding, maxConditioningEmbedding,
              canonicalXYMaxPurification,
              ReferenceIsometry.applyPureVector_amp,
              ReferenceIsometry.applyAmp, ReferenceIsometry.applyMatrixRight,
              ReferenceIsometry.rightBlock, ReferenceIsometry.ofInjective,
              Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec,
              dotProduct, Matrix.sum_apply, Fintype.sum_prod_type,
              Finset.sum_mul, Finset.mul_sum, Finset.sum_ite_eq', apply_ite,
              eq_comm, Prod.ext_iff, mul_assoc, mul_comm]
        · simp [omega, V, hix, hiy, coherentMaxPure, coherentLiftOfFixed,
            coherentLiftAmplitude, State.acToABReferenceEquiv,
            coherentMaxSwapEquiv, PureVector.reindex,
            PureVector.reindex_state, State.reindex, State.marginalA,
            partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
            PureVector.ofAmplitudeMatrix, Equiv.prodComm,
            maxLiftedCanonicalPurification, maxReferenceEmbedding,
            maxConditioningEmbedding, canonicalXYMaxPurification,
            ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
            ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
            ReferenceIsometry.ofInjective, Matrix.mul_apply,
            Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
            Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_mul,
            Finset.mul_sum, Finset.sum_ite_eq', apply_ite, eq_comm,
            Prod.ext_iff, mul_assoc, mul_comm]
      · rcases jTag with ⟨jy', jb⟩ | jExtra <;>
          simp [omega, V, hix, hiy, coherentMaxPure, coherentLiftOfFixed,
            coherentLiftAmplitude, State.acToABReferenceEquiv,
            coherentMaxSwapEquiv, PureVector.reindex,
            PureVector.reindex_state, State.reindex, State.marginalA,
            partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
            PureVector.ofAmplitudeMatrix, Equiv.prodComm,
            maxLiftedCanonicalPurification, maxReferenceEmbedding,
            maxConditioningEmbedding, canonicalXYMaxPurification,
            ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
            ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
            ReferenceIsometry.ofInjective, Matrix.mul_apply,
            Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
            Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_mul,
            Finset.mul_sum, Finset.sum_ite_eq', apply_ite, eq_comm,
            Prod.ext_iff, mul_assoc, mul_comm]
      -/
  /-
  · simp [coherentMaxPure, coherentLiftOfFixed, coherentLiftAmplitude,
    State.acToABReferenceEquiv, coherentMaxSwapEquiv, PureVector.reindex,
    PureVector.reindex_state, State.reindex, State.marginalA,
    partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
    PureVector.ofAmplitudeMatrix, Equiv.prodComm, Equiv.prodComm_apply,
    Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_apply_apply,
    Equiv.symm_symm, Prod.swap_prod_mk,
    maxLiftedCanonicalPurification, maxReferenceEmbedding,
    maxConditioningEmbedding, canonicalXYMaxPurification,
    canonicalXYCoherentPurification,
    ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
    ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
    ReferenceIsometry.ofInjective, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum]
  · simp [coherentMaxPure, coherentLiftOfFixed, coherentLiftAmplitude,
      State.acToABReferenceEquiv, coherentMaxSwapEquiv, PureVector.reindex,
      PureVector.reindex_state, State.marginalA, partialTraceA, partialTraceB,
      PureVector.state_matrix, rankOneMatrix_apply,
      PureVector.ofAmplitudeMatrix, Equiv.prodComm,
      maxLiftedCanonicalPurification, maxReferenceEmbedding,
      maxConditioningEmbedding, canonicalXYMaxPurification,
      canonicalXYCoherentPurification,
      ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
      ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
      ReferenceIsometry.ofInjective, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
      Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_mul,
      Finset.mul_sum]
  -/
-/

/-
private theorem coherentMaxPure_marginalB_eq
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    {rho : State ((a × x) × ((a × bPlus) × (x × y)))}
    (Phi : PureVector (Prod (maxReferenceType (a := a) (x := x)
      (y := y) (bPlus := bPlus)) ((a × x) × ((a × bPlus) × (x × y)))))
    (hPhi : Phi.Purifies rho) :
    Phi.state.marginalB = rho := by
  apply State.ext
  simpa [State.marginalB_matrix] using hPhi

private theorem coherentMaxPure_center_duality
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    [Nonempty a] [Nonempty x] [Nonempty bPlus] [Nonempty y]
    (rho : State ((a × x) × (y × bPlus)))
    (hclassical : rho.toSubnormalized.classicalOnXY) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < 1) :
    let psi := maxLiftedCanonicalPurification
      (a := a) (x := x) (y := y) (bPlus := bPlus) rho hclassical
    let hpsi := maxLiftedCanonicalPurification_fixed
      (a := a) (x := x) (y := y) (bPlus := bPlus) rho hclassical
    let omega := coherentMaxPure (a := a) (x := x)
      (b := maxReferenceType (a := a) (x := x) (y := y)
        (bPlus := bPlus)) psi hpsi
    (rho.conditioningIsometryApply (maxConditioningEmbedding
        (a := a) (x := x) (y := y) (bPlus := bPlus))).toSubnormalized
        .smoothConditionalMaxEntropy
        (a := a × x) (b := y × maxReferenceType
          (a := a) (x := x) (y := y) (bPlus := bPlus))
        ε hε0 (by simpa using hε) =
      - (canonicalXYComplementaryState (a := a) (x := x) (y := y)
        (b := bPlus) rho).toSubnormalized.smoothConditionalMinEntropy
        (a := a × x) (b := (a × bPlus) × (x × y))
        ε hε0 (by simpa using hε) := by
  dsimp
  let psi := maxLiftedCanonicalPurification
    (a := a) (x := x) (y := y) (bPlus := bPlus) rho hclassical
  let hpsi := maxLiftedCanonicalPurification_fixed
    (a := a) (x := x) (y := y) (bPlus := bPlus) rho hclassical
  let omega := coherentMaxPure (a := a) (x := x)
    (b := maxReferenceType (a := a) (x := x) (y := y)
      (bPlus := bPlus)) psi hpsi
  have hrel := coherentMaxPure_complementaryPureMarginalRel
    (a := a) (x := x)
    (b := maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus))
    (c := (a × bPlus) × (x × y)) psi hpsi
  have hdu := smoothConditionalMaxEntropy_marginalAB_eq_neg_smoothConditionalMinEntropy_marginalAC_of_scaled_pure
    (a := a × x)
    (b := y × maxReferenceType (a := a) (x := x) (y := y)
      (bPlus := bPlus))
    (c := (a × bPlus) × (x × y))
    omega (t := 1) (ε := ε) (by norm_num) (by norm_num) hε0 hε
  have hAB :
      omega.state.marginalAB = rho.conditioningIsometryApply
        (maxConditioningEmbedding (a := a) (x := x) (y := y)
          (bPlus := bPlus)) := by
    simpa [omega] using maxLiftedCanonicalPurification_center
      (a := a) (x := x) (y := y) (bPlus := bPlus) rho hclassical
  have hAC :
      omega.state.marginalAC = canonicalXYComplementaryState
        (a := a) (x := x) (y := y) (b := bPlus) rho := by
    simpa [omega] using coherentMaxPure_acMarginal
      (a := a) (x := x)
      (b := maxReferenceType (a := a) (x := x) (y := y)
        (bPlus := bPlus))
      (c := a × bPlus) (y' := y)
      psi hpsi
  rw [hAB, hAC] at hdu
  simpa [SubnormalizedState.smoothConditionalMaxEntropy_eq_raw,
    SubnormalizedState.smoothConditionalMinEntropy_eq_raw] using hdu
 -/
/-
private theorem canonicalXYMaxPurification_center
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    (coherentMaxPure (a := a) (x := x) (b := b)
      (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := b)
        rho hclassical)
      (canonicalXYMaxPurification_fixed (a := a) (x := x) (y := y) (b := b)
        rho hclassical)).state.marginalA = rho := by
  apply State.ext
  ext i j
    simp [coherentMaxPure, coherentLiftOfFixed, coherentLiftAmplitude,
    State.acToABReferenceEquiv, coherentMaxSwapEquiv, PureVector.reindex,
    PureVector.reindex_state, State.reindex, State.marginalA,
    partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
    PureVector.ofAmplitudeMatrix, Equiv.prodComm,
    canonicalXYMaxPurification]
-/
/-! ## Local hat success-block helpers for the coherent max route

The success branch is normalized before it is reindexed into the
classical-coherent purification shape.  These lemmas keep that normalization
calculation explicit, including the positive-trace hypothesis. -/

set_option maxHeartbeats 100000000 in
private theorem maxLiftedCanonicalPurification_center_fast
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (rho : State ((a × x) × (y × bPlus)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    (coherentMaxPure (a := a) (x := x)
      (b := maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus))
      (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
        (bPlus := bPlus) rho hclassical)
      (maxLiftedCanonicalPurification_fixed (a := a) (x := x) (y := y)
        (bPlus := bPlus) rho hclassical)).state.marginalA =
      rho.conditioningIsometryApply (maxConditioningEmbedding
        (a := a) (x := x) (y := y) (bPlus := bPlus)) := by
  apply State.ext
  ext i j
  rcases i with ⟨⟨ia, ix⟩, iy, ⟨i0, iTag⟩⟩
  rcases j with ⟨⟨ja, jx⟩, jy, ⟨j0, jTag⟩⟩
  have hselect : ∀ (u : y) (v : y × bPlus) (f : y × bPlus → ℂ),
      (∑ z : y × bPlus,
        (if (u, (Sum.inl v : Sum (y × bPlus)
            ((a × x) × ((a × bPlus) × (x × y))))) =
            (z.1, (Sum.inl z : Sum (y × bPlus)
              ((a × x) × ((a × bPlus) × (x × y))))) then 1 else 0) * f z) =
        if u = v.1 then f v else 0 := by
    intro u v f
    by_cases huv : u = v.1
    · subst u
      rw [Finset.sum_eq_single v]
      · simp
      · intro z _ hz
        by_cases hEq : (v.1, (Sum.inl v : Sum (y × bPlus)
            ((a × x) × ((a × bPlus) × (x × y))))) =
            (z.1, (Sum.inl z : Sum (y × bPlus)
              ((a × x) × ((a × bPlus) × (x × y)))))
        · have hvz : v = z := Sum.inl.inj (congrArg Prod.snd hEq)
          exact (hz hvz.symm).elim
        · simp [hEq]
      · simp
    · rw [if_neg huv]
      apply Finset.sum_eq_zero
      intro z _
      by_cases hz : (u, (Sum.inl v : Sum (y × bPlus)
          ((a × x) × ((a × bPlus) × (x × y))))) =
          (z.1, (Sum.inl z : Sum (y × bPlus)
            ((a × x) × ((a × bPlus) × (x × y)))))
      · have huz : u = z.1 := congrArg Prod.fst hz
        have hvz : v = z := Sum.inl.inj (congrArg Prod.snd hz)
        exact (huv (huz.trans ((congrArg Prod.fst hvz).symm))).elim
      · simp [hz]
  cases iTag with
  | inl iv =>
    cases jTag with
    | inl jv =>
      simp only [coherentMaxPure, coherentLiftOfFixed, coherentLiftAmplitude,
        State.acToABReferenceEquiv, coherentMaxSwapEquiv, PureVector.reindex,
         State.marginalA,
        partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
        PureVector.ofAmplitudeMatrix, Equiv.prodComm,
         Equiv.symm_trans_apply,

        maxLiftedCanonicalPurification, maxReferenceEmbedding,
        maxConditioningEmbedding, canonicalXYMaxPurification,


        ReferenceIsometry.ofInjective,

         Fintype.sum_prod_type
        ]
      dsimp
      simp only [ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
         Matrix.mulVec, dotProduct, hselect]
      by_cases hi : i0 = iv.1
      · by_cases hj : j0 = jv.1
        · by_cases hix : ix = jx
          · by_cases hiy : iy = jy
            · subst jx
              subst jy
              subst i0
              subst j0
              have hcollapse (q : a) (xx : bPlus) :
                  (∑ u : x, ∑ v : y,
                    (if ix = u ∧ v = iy then
                        canonicalXYMaxAmplitude rho
                          ((ia, ix), (q, xx), u, v) iv else 0) *
                      (starRingEnd ℂ) (if ix = u ∧ v = iy then
                        canonicalXYMaxAmplitude rho
                          ((ja, ix), (q, xx), u, v) jv else 0)) =
                    canonicalXYMaxAmplitude rho
                      ((ia, ix), (q, xx), ix, iy) iv *
                      (starRingEnd ℂ) (canonicalXYMaxAmplitude rho
                        ((ja, ix), (q, xx), ix, iy) jv) := by
                calc
                  _ = ∑ u : x, ∑ v : y,
                      if ix = u ∧ v = iy then
                        canonicalXYMaxAmplitude rho
                          ((ia, ix), (q, xx), u, v) iv *
                          (starRingEnd ℂ) (canonicalXYMaxAmplitude rho
                            ((ja, ix), (q, xx), u, v) jv) else 0 := by
                    apply Finset.sum_congr rfl
                    intro u _
                    apply Finset.sum_congr rfl
                    intro v _
                    by_cases h : ix = u ∧ v = iy <;> simp [h]
                  _ = _ := by
                    simpa [eq_comm] using
                      (smoothClassical_sum_ite_pair_rev
                        (f := fun u v =>
                          canonicalXYMaxAmplitude rho
                              ((ia, ix), (q, xx), u, v) iv *
                            (starRingEnd ℂ) (canonicalXYMaxAmplitude rho
                              ((ja, ix), (q, xx), u, v) jv)) ix iy)
              have hL :
                  (∑ q : a, ∑ xx : bPlus, ∑ u : x, ∑ v : y,
                    (if ix = u ∧ v = iy then
                        canonicalXYMaxAmplitude rho
                          ((ia, ix), (q, xx), u, v) iv else 0) *
                        (starRingEnd ℂ) (if ix = u ∧ v = iy then
                        canonicalXYMaxAmplitude rho
                          ((ja, ix), (q, xx), u, v) jv else 0)) =
                    ∑ q : a, ∑ xx : bPlus,
                      canonicalXYMaxAmplitude rho
                        ((ia, ix), (q, xx), ix, iy) iv *
                        (starRingEnd ℂ) (canonicalXYMaxAmplitude rho
                          ((ja, ix), (q, xx), ix, iy) jv) := by
                congr 1
                funext q
                congr 1
                funext xx
                exact hcollapse q xx
              simp only [eq_self, if_true]
              change
                (∑ q : a, ∑ xx : bPlus, ∑ u : x, ∑ v : y,
                  (if ix = u ∧ v = iy then
                      canonicalXYMaxAmplitude rho
                        ((ia, ix), (q, xx), u, v) iv else 0) *
                    (starRingEnd ℂ) (if ix = u ∧ v = iy then
                      canonicalXYMaxAmplitude rho
                        ((ja, ix), (q, xx), u, v) jv else 0)) = _
              rw [hL]
              rcases iv with ⟨ivY, ivB⟩
              rcases jv with ⟨jvY, jvB⟩
              by_cases hiv : ivY = iy
              · subst ivY
                by_cases hjv : jvY = iy
                · subst jvY
                  have hR :
                      (rho.conditioningIsometryApply
                        (maxConditioningEmbedding (a := a) (x := x)
                          (y := y) (bPlus := bPlus))).matrix
                          ((ia, ix), iy, iy, Sum.inl (iy, ivB))
                          ((ja, ix), iy, iy, Sum.inl (iy, jvB)) =
                        rho.matrix ((ia, ix), (iy, ivB))
                          ((ja, ix), (iy, jvB)) := by
                    rw [State.conditioningIsometryApply_matrix]
                    change
                      ((maxConditioningEmbedding (a := a) (x := x)
                        (y := y) (bPlus := bPlus)).matrix *
                        ReferenceIsometry.rightBlock rho.matrix
                          (ia, ix) (ja, ix) *
                        Matrix.conjTranspose
                          (maxConditioningEmbedding (a := a) (x := x)
                            (y := y) (bPlus := bPlus)).matrix)
                        (iy, (iy, Sum.inl (iy, ivB)))
                        (iy, (iy, Sum.inl (iy, jvB))) = _
                    simp only [maxConditioningEmbedding, ReferenceIsometry.rightBlock,
                      ReferenceIsometry.ofInjective, Matrix.mul_apply,
                      Matrix.conjTranspose_apply, Fintype.sum_prod_type,
                      Finset.sum_mul]
                    rw [Finset.sum_eq_single iy]
                    · rw [Finset.sum_eq_single jvB]
                      · rw [Finset.sum_eq_single iy]
                        · rw [Finset.sum_eq_single ivB]
                          · simp
                          · intro z _ hz
                            simp [ Ne.symm hz]
                          · simp
                        · intro z _ hz
                          simp [ Ne.symm hz]
                        · simp
                      · intro z _ hz
                        simp [ Ne.symm hz]
                      · simp
                    · intro z _ hz
                      simp [ Ne.symm hz]
                    · simp
                  simp
                  change _ =
                    (rho.conditioningIsometryApply
                      (maxConditioningEmbedding (a := a) (x := x)
                        (y := y) (bPlus := bPlus))).matrix
                      ((ia, ix), iy, iy, Sum.inl (iy, ivB))
                      ((ja, ix), iy, iy, Sum.inl (iy, jvB))
                  rw [hR]
                  simpa [Fintype.sum_prod_type] using
                    (canonicalXYMaxAmplitude_gram_eq
                      (a := a) (x := x) (y := y) (b := bPlus) rho hclassical
                      ia ja ix iy ivB jvB)
                · simp [canonicalXYMaxAmplitude, Ne.symm hjv,

                    ReferenceIsometry.applyMatrixRight,
                    ReferenceIsometry.rightBlock,
                     Matrix.mul_apply,
                    Matrix.conjTranspose_apply, Fintype.sum_prod_type,
                     Finset.mul_sum,
                    apply_ite, eq_comm, Prod.ext_iff,
                     mul_comm]
                  apply Eq.symm
                  rw [Finset.sum_eq_zero]
                  intro u _
                  rw [Finset.sum_eq_zero]
                  intro v _
                  by_cases h : iy = u ∧ jvY = u ∧ jvB = v
                  · exact (hjv (h.1.trans h.2.1.symm).symm).elim
                  · simp [h]
              · simp [canonicalXYMaxAmplitude, Ne.symm hiv,

                  ReferenceIsometry.applyMatrixRight,
                  ReferenceIsometry.rightBlock,
                   Matrix.mul_apply,
                  Matrix.conjTranspose_apply, Fintype.sum_prod_type,
                   Finset.mul_sum,
                  apply_ite, eq_comm, Prod.ext_iff,
                   mul_comm]
                apply Eq.symm
                rw [Finset.sum_eq_zero]
                intro u _
                rw [Finset.sum_eq_zero]
                intro v _
                by_cases ho : iy = u ∧ jvY = u ∧ jvB = v
                · rw [if_pos ho]
                  rw [Finset.sum_eq_zero]
                  intro u' _
                  rw [Finset.sum_eq_zero]
                  intro v' _
                  by_cases hi' : iy = u' ∧ ivY = u' ∧ ivB = v'
                  · exact (hiv (hi'.2.1.trans hi'.1.symm)).elim
                  · simp [hi']
                · simp [ho]
            · have hz := hclassical.2
                ((ia, ix), (iy, iv.2)) ((ja, ix), (jy, jv.2)) hiy
              simp [hi, hj, hix,

                ReferenceIsometry.applyMatrixRight,
                ReferenceIsometry.rightBlock,
                 Matrix.mul_apply,
                Matrix.conjTranspose_apply, Fintype.sum_prod_type,
                 Finset.mul_sum,
                apply_ite, eq_comm, Prod.ext_iff,
                 mul_comm]
              apply Eq.trans
              · rw [Finset.sum_eq_zero]
                intro u _
                rw [Finset.sum_eq_zero]
                intro v _
                by_cases ho : jy = u ∧ u = jv.1 ∧ v = jv.2
                · rw [if_pos ho]
                  rw [Finset.sum_eq_zero]
                  intro u' _
                  rw [Finset.sum_eq_zero]
                  intro v' _
                  by_cases hi' : iy = u' ∧ u' = iv.1 ∧ v' = iv.2
                  · have hz' := hclassical.2
                      ((ia, ix), (iy, iv.2)) ((ja, ix), (jy, jv.2)) hiy
                    simpa [hi'.1, hi'.2.1, hi'.2.2,
                      ho.1, ho.2.1, ho.2.2, hix] using hz'
                  · simp [hi']
                · simp [ho]
              · symm
                rw [Finset.sum_eq_zero]
                intro u _
                rw [Finset.sum_eq_zero]
                intro v _
                rw [Finset.sum_eq_zero]
                intro u' _
                rw [Finset.sum_eq_zero]
                intro v' _
                by_cases houter : jx = u' ∧ jy = v'
                · rw [if_pos houter]
                  by_cases hinner : jx = u' ∧ iy = v'
                  · exact (hiy (hinner.2.trans houter.2.symm)).elim
                  · simp [hinner]
                · simp [houter]
          · have hz := hclassical.1
              ((ia, ix), (iy, iv.2)) ((ja, jx), (jy, jv.2)) hix
            simp [hi, hj,

              ReferenceIsometry.applyMatrixRight,
              ReferenceIsometry.rightBlock,
               Matrix.mul_apply,
              Matrix.conjTranspose_apply, Fintype.sum_prod_type,
               Finset.mul_sum,
              apply_ite, eq_comm, Prod.ext_iff,
               mul_comm]
            apply Eq.trans
            · rw [Finset.sum_eq_zero]
              intro u _
              rw [Finset.sum_eq_zero]
              intro v _
              by_cases ho : jy = u ∧ u = jv.1 ∧ v = jv.2
              · rw [if_pos ho]
                rw [Finset.sum_eq_zero]
                intro u' _
                rw [Finset.sum_eq_zero]
                intro v' _
                by_cases hi' : iy = u' ∧ u' = iv.1 ∧ v' = iv.2
                · have hz' := hclassical.1
                    ((ia, ix), (iy, iv.2)) ((ja, jx), (jy, jv.2)) hix
                  simpa [hi'.1, hi'.2.1, hi'.2.2,
                    ho.1, ho.2.1, ho.2.2] using hz'
                · simp [hi']
              · simp [ho]
            · symm
              rw [Finset.sum_eq_zero]
              intro u _
              rw [Finset.sum_eq_zero]
              intro v _
              rw [Finset.sum_eq_zero]
              intro u' _
              rw [Finset.sum_eq_zero]
              intro v' _
              by_cases houter : jx = u' ∧ jy = v'
              · rw [if_pos houter]
                by_cases hinner : ix = u' ∧ iy = v'
                · exact (hix (hinner.1.trans houter.1.symm)).elim
                · simp [hinner]
              · simp [houter]
        · simp [hi, hj,
            ReferenceIsometry.applyMatrixRight,
            ReferenceIsometry.rightBlock,
             Matrix.mul_apply,
            Matrix.conjTranspose_apply, Fintype.sum_prod_type,
             Finset.mul_sum,
            apply_ite, eq_comm, Prod.ext_iff,
             mul_comm]
          apply Eq.symm
          rw [Finset.sum_eq_zero]
          intro u _
          rw [Finset.sum_eq_zero]
          intro v _
          by_cases h : jy = u ∧ j0 = u ∧ u = jv.1 ∧ v = jv.2
          · exact (hj (h.2.1.trans h.2.2.1)).elim
          · simp [h]
      · simp [hi,
          ReferenceIsometry.applyMatrixRight,
          ReferenceIsometry.rightBlock,
           Matrix.mul_apply,
          Matrix.conjTranspose_apply, Fintype.sum_prod_type,
           Finset.mul_sum,
          apply_ite, eq_comm, Prod.ext_iff,
           mul_comm]
        apply Eq.symm
        rw [Finset.sum_eq_zero]
        intro u _
        rw [Finset.sum_eq_zero]
        intro v _
        by_cases houter : jy = u ∧ j0 = u ∧ u = jv.1 ∧ v = jv.2
        · rw [if_pos houter]
          rw [Finset.sum_eq_zero]
          intro u' _
          rw [Finset.sum_eq_zero]
          intro v' _
          by_cases hinner : iy = u' ∧ i0 = u' ∧ u' = iv.1 ∧ v' = iv.2
          · exact (hi (hinner.2.1.trans hinner.2.2.1)).elim
          · simp [hinner]
        · simp [houter]
    | inr je =>
      simp [coherentMaxPure, coherentLiftOfFixed, coherentLiftAmplitude,
        State.acToABReferenceEquiv, coherentMaxSwapEquiv, PureVector.reindex,
         State.marginalA,
        partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
        PureVector.ofAmplitudeMatrix, Equiv.prodComm,
        maxLiftedCanonicalPurification, maxReferenceEmbedding,
        maxConditioningEmbedding, canonicalXYMaxPurification,
        ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
        ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
        ReferenceIsometry.ofInjective, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
         Fintype.sum_prod_type,
        Finset.mul_sum, apply_ite, eq_comm,
        Prod.ext_iff, mul_comm]
  | inr ie =>
    cases jTag with
    | inl jv =>
      simp [coherentMaxPure, coherentLiftOfFixed, coherentLiftAmplitude,
        State.acToABReferenceEquiv, coherentMaxSwapEquiv, PureVector.reindex,
         State.marginalA,
        partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
        PureVector.ofAmplitudeMatrix, Equiv.prodComm,
        maxLiftedCanonicalPurification, maxReferenceEmbedding,
        maxConditioningEmbedding, canonicalXYMaxPurification,
        ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
        ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
        ReferenceIsometry.ofInjective, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
         Fintype.sum_prod_type,
        Finset.mul_sum, apply_ite, eq_comm,
        Prod.ext_iff]
    | inr je =>
      simp [coherentMaxPure, coherentLiftOfFixed, coherentLiftAmplitude,
        State.acToABReferenceEquiv, coherentMaxSwapEquiv, PureVector.reindex,
         State.marginalA,
        partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
        PureVector.ofAmplitudeMatrix, Equiv.prodComm,
        maxLiftedCanonicalPurification, maxReferenceEmbedding,
        maxConditioningEmbedding, canonicalXYMaxPurification,
        ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
        ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
        ReferenceIsometry.ofInjective, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
         Fintype.sum_prod_type,
         eq_comm,
        Prod.ext_iff]

private theorem exists_scaled_pure_representation
    [Nonempty a] [Nonempty b]
    (rho : SubnormalizedState ((a × x) × (y × b)))
    (htrace : 0 < rho.matrix.trace.re) :
    ∃ (psi : PureVector
      (Prod (Prod (a × x) (y × b)) ((a × b) × (x × y))))
      (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1),
      rho = abMarginalFromScaledTripartitePure
        (a := a × x) (b := y × b) (c := (a × b) × (x × y))
        psi t ht.le ht1 ∧
      psi.state.marginalAC = canonicalXYComplementaryState
        (a := a) (x := x) (y := y) (b := b) (rho.normalize htrace.ne') := by
  let rhoNorm := rho.normalize htrace.ne'
  let psi0 := canonicalXYCoherentPurification
    (a := a) (x := x) (y := y) (b := b) rhoNorm
  let psi := psi0.reindex
    (Equiv.prodComm ((a × b) × (x × y)) ((a × x) × (y × b)))
  have hpsi : psi.state.marginalAB = rhoNorm := by
    rw [State.marginalAB_eq_marginalA]
    apply State.ext
    ext i j
    have hpur := canonicalXYCoherentPurification_purifies
      (a := a) (x := x) (y := y) (b := b) rhoNorm
    rw [PureVector.purifies_iff] at hpur
    simpa [psi, psi0, State.marginalA, partialTraceB,
      partialTraceA, PureVector.reindex_state, State.reindex,
      State.marginalB] using congrFun (congrFun hpur i) j
  have ht : 0 < rho.matrix.trace.re := htrace
  have ht1 : rho.matrix.trace.re ≤ 1 := by
    simpa using rho.trace_le_one
  refine ⟨psi, rho.matrix.trace.re, ht, ht1, ?_, ?_⟩
  rw [abMarginalFromScaledTripartitePure, hpsi]
  · exact (SubnormalizedState.ofStateScale_normalize_trace_eq rho htrace).symm
  · apply State.ext
    ext i j
    simp [psi, psi0, rhoNorm, canonicalXYComplementaryState,
      State.acMarginalFromABPurification, State.marginalB,
       PureVector.reindex, PureVector.state_matrix,
      partialTraceA, rankOneMatrix_apply,
      Fintype.sum_prod_type, Equiv.prodComm, State.abToACReferenceEquiv]

private theorem exists_classical_scaled_pure_representation
    [Nonempty a] [Nonempty b]
    (rho : SubnormalizedState ((a × x) × (y × b)))
    (htrace : 0 < rho.matrix.trace.re)
    (hclassical : rho.classicalOnXY) :
    ∃ (psi : PureVector
      (Prod (Prod (a × x) (y × b)) ((a × b) × (x × y))))
      (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1),
      rho = abMarginalFromScaledTripartitePure
        (a := a × x) (b := y × b) (c := (a × b) × (x × y))
        psi t ht.le ht1 ∧
      classicalCoherentOn
        (acMarginalFromScaledTripartitePure
          (a := a × x) (b := y × b) (c := (a × b) × (x × y))
          psi t ht.le ht1) ∧
      psi.state.marginalAC = canonicalXYComplementaryState
        (a := a) (x := x) (y := y) (b := b) (rho.normalize htrace.ne') := by
  obtain ⟨psi, t, ht, ht1, hrep, hcomp⟩ :=
    exists_scaled_pure_representation (a := a) (x := x) (y := y) (b := b)
      rho htrace
  refine ⟨psi, t, ht, ht1, hrep, ?_, ?_⟩
  let rhoNorm := rho.normalize htrace.ne'
  have hcomp :
      psi.state.marginalAC =
        canonicalXYComplementaryState (a := a) (x := x) (y := y) (b := b)
          rhoNorm := by
    simpa [rhoNorm] using hcomp
  have hclassRhoNorm : rhoNorm.toSubnormalized.classicalOnXY := by
    constructor <;> intro i j hij
    · simp [rhoNorm, SubnormalizedState.normalize_matrix, hclassical.1 i j hij]
    · simp [rhoNorm, SubnormalizedState.normalize_matrix, hclassical.2 i j hij]
  have hclassNorm := canonicalXYComplementaryState_classicalCoherentOn
    (a := a) (x := x) (y := y) (b := b) rhoNorm hclassRhoNorm
  have hclassPsi : classicalCoherentOn psi.state.marginalAC.toSubnormalized := by
    rw [hcomp]
    exact hclassNorm
  · intro i j hij
    change t * psi.state.marginalAC.matrix i j = 0
    rw [mul_eq_zero]
    right
    simpa [State.marginalAC, State.marginalAC_matrix,
      partialTraceB, PureVector.state_matrix, rankOneMatrix_apply]
      using hclassPsi i j hij
  · exact hcomp

private theorem generalizedFidelity_ofStateScale
    {r : Type*} [Fintype r] [DecidableEq r]
    (rho sigma : State r) {t u : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (SubnormalizedState.ofStateScale rho t ht0 ht1).generalizedFidelity
        (SubnormalizedState.ofStateScale sigma u hu0 hu1) =
      (Real.sqrt (t * u) * Real.sqrt (rho.squaredFidelity sigma) +
        Real.sqrt ((1 - t) * (1 - u))) ^ 2 := by
  rw [SubnormalizedState.generalizedFidelity_eq]
  rw [SubnormalizedState.ofStateScale_matrix,
    SubnormalizedState.ofStateScale_matrix]
  have hρ : rho.matrix.trace.re = 1 := by
    rw [rho.trace_eq_one]
    norm_num
  have hσ : sigma.matrix.trace.re = 1 := by
    rw [sigma.trace_eq_one]
    norm_num
  have hsqrtρ :
      psdSqrt (t • rho.matrix) = ((Real.sqrt t : ℝ) : ℂ) • rho.sqrtMatrix := by
    simpa [State.sqrtMatrix] using
      (psdSqrt_real_smul (M := rho.matrix) ht0 rho.pos)
  have hsqrtσ :
      psdSqrt (u • sigma.matrix) = ((Real.sqrt u : ℝ) : ℂ) • sigma.sqrtMatrix := by
    simpa [State.sqrtMatrix] using
      (psdSqrt_real_smul (M := sigma.matrix) hu0 sigma.pos)
  have hproduct :
      psdSqrt (t • rho.matrix) * psdSqrt (u • sigma.matrix) =
        (((Real.sqrt t * Real.sqrt u : ℝ) : ℂ) •
          (rho.sqrtMatrix * sigma.sqrtMatrix)) := by
    rw [hsqrtρ, hsqrtσ]
    ext i j
    simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc, mul_left_comm]
  have htrho : (trace (t • rho.matrix)).re = t := by
    simp [hρ]
  have htsigma : (trace (u • sigma.matrix)).re = u := by
    simp [hσ]
  have hnorm : traceNorm (rho.sqrtMatrix * sigma.sqrtMatrix) =
      Real.sqrt (rho.squaredFidelity sigma) := by
    rw [State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (traceNorm_nonneg _)]
  rw [hproduct, traceNorm_real_smul_eq
    (mul_nonneg (Real.sqrt_nonneg t) (Real.sqrt_nonneg u)), htrho, htsigma,
    hnorm]
  have htu : 0 ≤ t * u := mul_nonneg ht0 hu0
  have hmissing : 0 ≤ (1 - t) * (1 - u) :=
    mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hu1)
  have hsq_t : (Real.sqrt t * Real.sqrt u) ^ 2 = t * u := by
    rw [mul_pow, Real.sq_sqrt ht0, Real.sq_sqrt hu0]
  have hsq_missing : (Real.sqrt (1 - t) * Real.sqrt (1 - u)) ^ 2 =
      (1 - t) * (1 - u) := by
    rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr ht1),
      Real.sq_sqrt (sub_nonneg.mpr hu1)]
  rw [Real.sqrt_mul ht0, Real.sqrt_mul (sub_nonneg.mpr ht1)]

private theorem scaled_purifiedBall_of_squaredFidelity_le
    {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (center eta : State r) (tau upsilon : State s) {t u ε : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hball : (SubnormalizedState.ofStateScale center t ht0 ht1).purifiedBall ε
      (SubnormalizedState.ofStateScale eta u hu0 hu1))
    (hF : center.squaredFidelity eta ≤ tau.squaredFidelity upsilon) :
    (SubnormalizedState.ofStateScale tau t ht0 ht1).purifiedBall ε
      (SubnormalizedState.ofStateScale upsilon u hu0 hu1) := by
  apply SubnormalizedState.purifiedBall_of_generalizedFidelity_le
    (ρ := SubnormalizedState.ofStateScale center t ht0 ht1)
    (σ := SubnormalizedState.ofStateScale eta u hu0 hu1)
    (τ := SubnormalizedState.ofStateScale tau t ht0 ht1)
    (υ := SubnormalizedState.ofStateScale upsilon u hu0 hu1) ?_ hball
  rw [generalizedFidelity_ofStateScale, generalizedFidelity_ofStateScale]
  have hroot : Real.sqrt (center.squaredFidelity eta) ≤
      Real.sqrt (tau.squaredFidelity upsilon) :=
    Real.sqrt_le_sqrt hF
  have hlin :
      Real.sqrt (t * u) * Real.sqrt (center.squaredFidelity eta) +
          Real.sqrt ((1 - t) * (1 - u)) ≤
        Real.sqrt (t * u) * Real.sqrt (tau.squaredFidelity upsilon) +
          Real.sqrt ((1 - t) * (1 - u)) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)) le_rfl
  exact (sq_le_sq₀
    (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _))
    (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _))).mpr hlin

private theorem classicalScaledMaxCandidate_of_coherent_purifications
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y']
    [Nonempty a] [Nonempty x] [Nonempty b] [Nonempty c] [Nonempty y']
    (center : State ((a × x) × (y' × b)))
    (etaCenter eta : State ((a × x) × (c × x × y')))
    (Psi Phi : PureVector (Prod b ((a × x) × (c × x × y'))))
    (hPsi : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose) =
      Psi.amplitudeMatrix * Psi.amplitudeMatrix.conjTranspose)
    (hPhi : classicalCoherentMap (a := a) (x := x) (c := c) (y' := y')
      (Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose) =
      Phi.amplitudeMatrix * Phi.amplitudeMatrix.conjTranspose)
    (hPhiEta : Phi.state.marginalB = eta)
    (hPsiCenter :
      (coherentMaxPure (a := a) (x := x) (b := b) Psi hPsi).state.marginalA = center)
    {t u ε : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hu : 0 < u) (hu1 : u ≤ 1)
      (hball :
      (SubnormalizedState.ofStateScale etaCenter t ht.le ht1).purifiedBall ε
        (SubnormalizedState.ofStateScale eta u hu.le hu1))
    (hoverlap : Psi.overlapSq Phi = etaCenter.squaredFidelity eta) :
    ∃ tau : SubnormalizedState ((a × x) × (y' × b)),
      (SubnormalizedState.ofStateScale center t ht.le ht1).purifiedBall ε tau ∧
      tau.classicalOnXY ∧
        tau.conditionalMaxEntropyRaw =
          - (SubnormalizedState.ofStateScale eta u hu.le hu1).conditionalMinEntropyRaw := by
  let PsiMax := coherentMaxPure (a := a) (x := x) (b := b) Psi hPsi
  let PhiMax := coherentMaxPure (a := a) (x := x) (b := b) Phi hPhi
  let tau : SubnormalizedState ((a × x) × (y' × b)) :=
    SubnormalizedState.ofStateScale PhiMax.state.marginalA u hu.le hu1
  have hFpure : etaCenter.squaredFidelity eta ≤
      PsiMax.state.squaredFidelity PhiMax.state := by
    calc
      etaCenter.squaredFidelity eta = Psi.overlapSq Phi := hoverlap.symm
      _ = PsiMax.overlapSq PhiMax :=
        (coherentMaxPure_overlapSq (a := a) (x := x) (b := b)
          Psi Phi hPsi hPhi).symm
      _ ≤ PsiMax.state.squaredFidelity PhiMax.state :=
        PureVector.overlapSq_le_state_squaredFidelity PsiMax PhiMax
  have hF : etaCenter.squaredFidelity eta ≤
      center.squaredFidelity PhiMax.state.marginalA := by
    calc
      etaCenter.squaredFidelity eta ≤ PsiMax.state.squaredFidelity PhiMax.state := hFpure
      _ ≤ PsiMax.state.marginalA.squaredFidelity PhiMax.state.marginalA :=
        State.squaredFidelity_le_marginalA_squaredFidelity PsiMax.state PhiMax.state
      _ = center.squaredFidelity PhiMax.state.marginalA := by rw [hPsiCenter]
  have hballTau := scaled_purifiedBall_of_squaredFidelity_le
    (center := etaCenter) (eta := eta) (tau := center)
    (upsilon := PhiMax.state.marginalA) ht.le ht1 hu.le hu1 hball hF
  have hrel := coherentMaxPure_scaledComplementaryPureMarginalRel
    (a := a) (x := x) (b := b) (c := c) (y' := y') Phi hPhi
    u hu hu1
  have hent :=
    (conditionalMinMaxEntropyDualOn_complementaryPureMarginals
      (a := a × x) (b := y' × b) (c := c × x × y'))
      tau (SubnormalizedState.ofStateScale Phi.state.marginalB u hu.le hu1)
      (by simpa [tau, PhiMax, hPhiEta] using hrel)
  have htauX : tau.classicalOnX := by
    intro i j hij
    change u * PhiMax.state.marginalA.matrix i j = 0
    rw [State.marginalA_matrix]
    simp only [partialTraceB, PureVector.state_matrix,
      rankOneMatrix_apply]
    rw [mul_eq_zero]
    exact Or.inr (coherentMaxPure_amp_X (a := a) (x := x) (b := b)
      Phi hPhi i j hij)
  have htauY : tau.classicalOnY := by
    intro i j hij
    change u * PhiMax.state.marginalA.matrix i j = 0
    rw [State.marginalA_matrix]
    simp only [partialTraceB, PureVector.state_matrix,
      rankOneMatrix_apply]
    rw [mul_eq_zero]
    exact Or.inr (coherentMaxPure_amp_Y (a := a) (x := x) (b := b)
      Phi hPhi i j hij)
  refine ⟨tau, ?_, ⟨htauX, htauY⟩, ?_⟩
  · simpa [tau] using hballTau
  · simpa [tau, hPhiEta] using hent

private theorem exists_classical_max_candidate_on_enlarged_conditioning
    [Nonempty a] [Nonempty b]
    (rho : SubnormalizedState ((a × x) × (y × b))) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < Real.sqrt rho.matrix.trace.re)
    (hclassical : rho.classicalOnXY) :
    ∃ tauPlus : SubnormalizedState
        ((a × x) × (y × maxReferenceType (a := a) (x := x) (y := y) (bPlus := b))),
      (rho.conditioningIsometryApply
        (maxConditioningEmbedding (a := a) (x := x) (y := y) (bPlus := b))).purifiedBall ε tauPlus ∧
      tauPlus.classicalOnXY ∧
      tauPlus.conditionalMaxEntropyRaw =
        rho.smoothConditionalMaxEntropy ε hε0 hε := by
  have htrace : 0 < rho.matrix.trace.re :=
    Real.sqrt_pos.mp (lt_of_le_of_lt hε0 hε)
  have hfull : Nonempty ((a × x) × (y × b)) :=
    nonempty_of_trace_pos rho.matrix htrace
  letI : Nonempty x := by
    rcases hfull with ⟨i⟩
    exact ⟨i.1.2⟩
  letI : Nonempty y := by
    rcases hfull with ⟨i⟩
    exact ⟨i.2.1⟩
  obtain ⟨psi, t, ht, ht1, hrep, hcoherent, hpsiCenterNorm⟩ :=
    exists_classical_scaled_pure_representation
      (a := a) (x := x) (y := y) (b := b) rho htrace hclassical
  have ht_eq : t = rho.matrix.trace.re := by
    simpa [hrep, abMarginalFromScaledTripartitePure] using
      (SubnormalizedState.ofStateScale_trace_re psi.state.marginalAB t ht.le ht1).symm
  have hεt : ε < Real.sqrt t := by simpa [ht_eq] using hε
  let etaCenterSub : SubnormalizedState
      ((a × x) × ((a × b) × (x × y))) :=
    acMarginalFromScaledTripartitePure
      (a := a × x) (b := y × b) (c := (a × b) × (x × y))
      psi t ht.le ht1
  have hεeta : ε < Real.sqrt etaCenterSub.matrix.trace.re := by
    simpa [etaCenterSub] using
      epsilon_lt_sqrt_trace_acMarginalFromScaledTripartitePure
        (a := a × x) (b := y × b) (c := (a × b) × (x × y))
        psi ht ht1 hεt
  have hclassEtaCenter : classicalCoherentOn etaCenterSub := by
    simpa [etaCenterSub] using hcoherent
  obtain ⟨eta, hball, hetaClass, hetaMin⟩ :=
    smoothConditionalMinEntropy_exists_classicalCoherent_optimizer
      (a := a) (x := x) (c := a × b) (y' := y)
      etaCenterSub hε0 hεeta hclassEtaCenter
  have hetaPos : 0 < eta.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      etaCenterSub eta hεeta hball
  let etaNorm := eta.normalize hetaPos.ne'
  have hetaScale :
      eta = SubnormalizedState.ofStateScale etaNorm eta.matrix.trace.re
        hetaPos.le eta.trace_le_one := by
    exact (SubnormalizedState.ofStateScale_normalize_trace_eq eta hetaPos).symm
  have hclassEtaNorm : classicalCoherentOn etaNorm.toSubnormalized := by
    intro i j hij
    simp [etaNorm, SubnormalizedState.normalize_matrix, hetaClass i j hij]
  let rhoNorm := rho.normalize htrace.ne'
  have hclassRhoNorm : rhoNorm.toSubnormalized.classicalOnXY := by
    constructor <;> intro i j hij
    · simp [rhoNorm, SubnormalizedState.normalize_matrix, hclassical.1 i j hij]
    · simp [rhoNorm, SubnormalizedState.normalize_matrix, hclassical.2 i j hij]
  let etaCenterNorm : State ((a × x) × ((a × b) × (x × y))) :=
    canonicalXYComplementaryState (a := a) (x := x) (y := y) (b := b) rhoNorm
  have hcenterEq :
      SubnormalizedState.ofStateScale etaCenterNorm t ht.le ht1 = etaCenterSub := by
    apply SubnormalizedState.ext
    have hpsiCenterNorm' : psi.state.marginalAC = etaCenterNorm := by
      simpa [etaCenterNorm, rhoNorm] using hpsiCenterNorm
    simp [etaCenterSub, hpsiCenterNorm']
  have hetaEq :
      SubnormalizedState.ofStateScale etaNorm eta.matrix.trace.re
        hetaPos.le eta.trace_le_one = eta := hetaScale.symm
  have hballScaled :
      (SubnormalizedState.ofStateScale etaCenterNorm t ht.le ht1).purifiedBall ε
        (SubnormalizedState.ofStateScale etaNorm eta.matrix.trace.re
          hetaPos.le eta.trace_le_one) := by
    rw [hcenterEq, hetaEq]
    exact hball
  let psiPlus := maxLiftedCanonicalPurification
    (a := a) (x := x) (y := y) (bPlus := b) rhoNorm hclassRhoNorm
  let hpsiPlus := maxLiftedCanonicalPurification_fixed
    (a := a) (x := x) (y := y) (bPlus := b) rhoNorm hclassRhoNorm
  let centerPlus := (coherentMaxPure (a := a) (x := x)
    (b := maxReferenceType (a := a) (x := x) (y := y) (bPlus := b))
    psiPlus hpsiPlus).state.marginalA
  have hcenterPlus : centerPlus =
      rhoNorm.conditioningIsometryApply
        (maxConditioningEmbedding (a := a) (x := x) (y := y) (bPlus := b)) := by
    simpa [centerPlus, psiPlus, hpsiPlus] using
      maxLiftedCanonicalPurification_center_fast
        (a := a) (x := x) (y := y) (bPlus := b) rhoNorm hclassRhoNorm
  have hpsiPurifies : psiPlus.Purifies etaCenterNorm := by
    have h := (maxReferenceEmbedding (a := a) (x := x) (y := y)
      (bPlus := b)).applyPureVector_purifies
      (canonicalXYMaxPurification_purifies
        (a := a) (x := x) (y := y) (b := b) rhoNorm hclassRhoNorm)
    simpa [psiPlus, etaCenterNorm] using h
  obtain ⟨phi, hphiPurifies, hoverlap⟩ :=
    maxReferenceUhlmann (a := a) (x := x) (y := y) (bPlus := b)
      psiPlus hpsiPurifies
  have hphiEta : phi.state.marginalB = etaNorm := by
    apply State.ext
    simpa [State.marginalB_matrix] using hphiPurifies
  have hphiFixed :
      classicalCoherentMap (a := a) (x := x) (c := a × b) (y' := y)
          (phi.amplitudeMatrix * phi.amplitudeMatrix.conjTranspose) =
        phi.amplitudeMatrix * phi.amplitudeMatrix.conjTranspose := by
    exact pureVector_classicalCoherent_fixed phi etaNorm hphiPurifies hclassEtaNorm
  obtain ⟨tauPlus, hballPlus, hclassPlus, hentropyPlus⟩ :=
    classicalScaledMaxCandidate_of_coherent_purifications
      (a := a) (x := x) (c := a × b) (y' := y)
      (b := maxReferenceType (a := a) (x := x) (y := y) (bPlus := b))
      centerPlus etaCenterNorm etaNorm psiPlus phi
      hpsiPlus hphiFixed hphiEta
      (by rfl)
      ht ht1 hetaPos eta.trace_le_one hballScaled (by simpa using hoverlap)
  have hcenterScaled :
      SubnormalizedState.ofStateScale centerPlus t ht.le ht1 =
        rho.conditioningIsometryApply
          (maxConditioningEmbedding (a := a) (x := x) (y := y) (bPlus := b)) := by
    apply SubnormalizedState.ext
    rw [SubnormalizedState.ofStateScale_matrix, hcenterPlus,
      SubnormalizedState.conditioningIsometryApply_matrix]
    rw [ht_eq]
    change (rho.matrix.trace.re : ℂ) •
        (maxConditioningEmbedding (a := a) (x := x) (y := y)
          (bPlus := b)).applyMatrixRight rhoNorm.matrix =
      (maxConditioningEmbedding (a := a) (x := x) (y := y)
        (bPlus := b)).applyMatrixRight rho.matrix
    ext i j
    simp [ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
      rhoNorm, SubnormalizedState.normalize_matrix, htrace.ne',
      Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.mul_sum, mul_assoc, mul_comm]
  refine ⟨tauPlus, ?_, hclassPlus, ?_⟩
  · rw [← hcenterScaled]
    exact hballPlus
  · rw [hentropyPlus]
    calc
      - (SubnormalizedState.ofStateScale etaNorm eta.matrix.trace.re
          hetaPos.le eta.trace_le_one).conditionalMinEntropyRaw =
          -eta.conditionalMinEntropyRaw := by
        exact congrArg Neg.neg
          (congrArg SubnormalizedState.conditionalMinEntropyRaw hetaScale.symm)
      _ = -etaCenterSub.smoothConditionalMinEntropy ε hε0 hεeta :=
        congrArg Neg.neg hetaMin
      _ = rho.smoothConditionalMaxEntropy ε hε0 hε := by
        have hdual :
            rho.smoothConditionalMaxEntropy ε hε0 hε =
              -etaCenterSub.smoothConditionalMinEntropy ε hε0 hεeta := by
          simpa [hrep, etaCenterSub] using
            smoothConditionalMaxEntropy_marginalAB_eq_neg_smoothConditionalMinEntropy_marginalAC_of_scaled_pure
              (a := a × x) (b := y × b) (c := (a × b) × (x × y))
              psi ht ht1 hε0 hεt
        exact hdual.symm

private theorem smoothClassical_fixes_of_supports_projector
    {c : Type*} [Fintype c] [DecidableEq c]
    {M P : CMatrix c} (hM : M.PosSemidef) (hP : P.PosSemidef)
    (hPid : P * P = P) (hSupport : Matrix.Supports M P) :
    P * M = M ∧ M * P = M := by
  have hPcomp : P * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hPid]
    abel
  have hMcomp : M * (1 - P) = 0 := by
    ext i j
    have hv := hSupport (fun k => (1 - P) k j) (by
      ext i'
      change ∑ k, P i' k * (1 - P) k j = 0
      simpa [Matrix.mul_apply] using congrFun (congrFun hPcomp i') j)
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hv i
  have hright : M * P = M := by
    calc
      M * P = M * (1 - (1 - P)) := by noncomm_ring
      _ = M := by rw [Matrix.mul_sub, hMcomp, Matrix.mul_one]; abel
  have hleft : P * M = M := by
    have hconj := congrArg Matrix.conjTranspose hright
    simpa [Matrix.conjTranspose_mul, hP.isHermitian.eq, hM.isHermitian.eq]
      using hconj
  exact ⟨hleft, hright⟩

private theorem smoothClassical_conditioning_support_projector_supports_image
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry b bPlus) :
    Matrix.Supports
      (bipartiteSupportProjector (ρ.conditioningIsometryApply V))
      (Matrix.kronecker (1 : CMatrix a)
        (V.matrix * Matrix.conjTranspose V.matrix)) := by
  let ρPlus := ρ.conditioningIsometryApply V
  let Q : CMatrix bPlus := V.matrix * Matrix.conjTranspose V.matrix
  let P : CMatrix (Prod a bPlus) := bipartiteSupportProjector ρPlus
  have hNB : ρPlus.marginalB.matrix * Q = ρPlus.marginalB.matrix := by
    rw [SubnormalizedState.marginalB_matrix,
      SubnormalizedState.conditioningIsometryApply_matrix]
    rw [V.partialTraceA_applyMatrixRight]
    calc
      (V.matrix * ρ.marginalB.matrix * Matrix.conjTranspose V.matrix) *
          (V.matrix * Matrix.conjTranspose V.matrix) =
        V.matrix * ρ.marginalB.matrix *
          (Matrix.conjTranspose V.matrix * V.matrix) *
            Matrix.conjTranspose V.matrix := by simp [Matrix.mul_assoc]
      _ = V.matrix * ρ.marginalB.matrix * Matrix.conjTranspose V.matrix := by
        rw [V.isometry]
        simp
  let PB : CMatrix bPlus :=
    supportProjector ρPlus.marginalB.matrix ρPlus.marginalB.pos
  have hPBQ : Matrix.Supports PB Q := by
    apply Matrix.Supports.trans
      (supportProjector_supports ρPlus.marginalB.matrix ρPlus.marginalB.pos)
    exact Matrix.Supports.of_mul_right_eq_self hNB
  have hPBfix : Q * PB = PB ∧ PB * Q = PB := by
    have hQpos : Q.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V.matrix
    have hQid : Q * Q = Q := by
      dsimp [Q]
      calc
        (V.matrix * Matrix.conjTranspose V.matrix) *
            (V.matrix * Matrix.conjTranspose V.matrix) =
          V.matrix * (Matrix.conjTranspose V.matrix * V.matrix) *
            Matrix.conjTranspose V.matrix := by simp [Matrix.mul_assoc]
        _ = Q := by rw [V.isometry]; simp [Q]
    exact smoothClassical_fixes_of_supports_projector
      (psdInvSqrt_support_posSemidef ρPlus.marginalB.pos) hQpos hQid hPBQ
  have hPE : Matrix.Supports P (Matrix.kronecker (1 : CMatrix a) Q) := by
    apply Matrix.Supports.of_mul_right_eq_self
    dsimp [P]
    change Matrix.kronecker
        (supportProjector ρPlus.marginalA.matrix ρPlus.marginalA.pos) PB *
        Matrix.kronecker (1 : CMatrix a) Q =
      Matrix.kronecker
        (supportProjector ρPlus.marginalA.matrix ρPlus.marginalA.pos) PB
    calc
      Matrix.kronecker
          (supportProjector ρPlus.marginalA.matrix ρPlus.marginalA.pos) PB *
          Matrix.kronecker (1 : CMatrix a) Q =
        Matrix.kronecker
          (supportProjector ρPlus.marginalA.matrix ρPlus.marginalA.pos * 1)
          (PB * Q) := by
            simpa [Matrix.kronecker] using
              (Matrix.mul_kronecker_mul
                (supportProjector ρPlus.marginalA.matrix ρPlus.marginalA.pos)
                (1 : CMatrix a) PB Q).symm
      _ = Matrix.kronecker
          (supportProjector ρPlus.marginalA.matrix ρPlus.marginalA.pos) PB := by
        rw [mul_one, hPBfix.2]
  simpa [P, Q] using hPE

/-
private theorem smoothClassical_conditioning_support_reconstruct
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (τPlus : SubnormalizedState (Prod a bPlus)) (V : ReferenceIsometry b bPlus)
    {P : CMatrix (Prod a bPlus)}
    (hSupport : Matrix.Supports τPlus.matrix P)
    (hImage : Matrix.Supports P
      (Matrix.kronecker (1 : CMatrix a)
        (V.matrix * Matrix.conjTranspose V.matrix))) :
    (τPlus.conditioningIsometryCompressed V).conditioningIsometryApply V = τPlus := by
  let E : CMatrix (Prod a bPlus) := Matrix.kronecker (1 : CMatrix a)
      (V.matrix * Matrix.conjTranspose V.matrix)
  have hEpos : E.PosSemidef := by
    dsimp [E]
    exact (Matrix.PosSemidef.one).kronecker
      (Matrix.posSemidef_self_mul_conjTranspose V.matrix)
  have hEid : E * E = E := by
    dsimp [E]
    rw [← Matrix.mul_kronecker_mul]
    have hVV : (V.matrix * Matrix.conjTranspose V.matrix) *
        (V.matrix * Matrix.conjTranspose V.matrix) =
      V.matrix * Matrix.conjTranspose V.matrix := by
      calc
        (V.matrix * Matrix.conjTranspose V.matrix) *
            (V.matrix * Matrix.conjTranspose V.matrix) =
          V.matrix * (Matrix.conjTranspose V.matrix * V.matrix) *
            Matrix.conjTranspose V.matrix := by simp [Matrix.mul_assoc]
        _ = V.matrix * Matrix.conjTranspose V.matrix := by
          rw [V.isometry]
          simp
    rw [one_mul, hVV]
  have hτE : Matrix.Supports τPlus.matrix E :=
    hSupport.trans (by simpa [E] using hImage)
  have hfix := smoothClassical_fixes_of_supports_projector
    τPlus.pos hEpos hEid hτE
  apply SubnormalizedState.ext
  rw [smoothClassical_conditioningIsometryCompressed_apply_matrix]
  have hrecon : E * τPlus.matrix * E = τPlus.matrix := by
    calc
      E * τPlus.matrix * E = E * (τPlus.matrix * E) := by simp [Matrix.mul_assoc]
      _ = E * τPlus.matrix := by rw [hfix.2]
      _ = τPlus.matrix := hfix.1
  simpa [E, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_mul] using hrecon
-/

private theorem smoothClassical_conditioningIsometryCompressed_apply_matrix
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (τPlus : SubnormalizedState (Prod a bPlus)) (V : ReferenceIsometry b bPlus) :
    ((τPlus.conditioningIsometryCompressed V).conditioningIsometryApply V).matrix =
      Matrix.kronecker (1 : CMatrix a) (V.matrix * Matrix.conjTranspose V.matrix) *
          τPlus.matrix *
        Matrix.conjTranspose (Matrix.kronecker (1 : CMatrix a)
          (V.matrix * Matrix.conjTranspose V.matrix)) := by
  rw [conditioningIsometryApply_matrix, conditioningIsometryCompressed_matrix]
  let K : Matrix (Prod a bPlus) (Prod a b) ℂ :=
    Matrix.kronecker (1 : CMatrix a) V.matrix
  have hcompress :
      MatrixMap.kron (Channel.idChannel a).map
          (MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix))
          τPlus.matrix = Matrix.conjTranspose K * τPlus.matrix * K := by
    ext i j
    rw [MatrixMap.kron_idChannel_left_apply_slice]
    change MatrixMap.ofKraus
        (fun _ : Unit => Matrix.conjTranspose V.matrix)
        (ReferenceIsometry.rightBlock τPlus.matrix i.1 j.1) i.2 j.2 =
          (Matrix.conjTranspose K * τPlus.matrix * K) i j
    simp [MatrixMap.ofKraus, K, Matrix.kronecker, Matrix.mul_apply,
      Finset.mul_sum, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fintype.sum_prod_type, mul_comm,
      mul_left_comm, Finset.sum_ite_eq',
      ReferenceIsometry.rightBlock]
    have hsum (x : bPlus) :
        (∑ x₁ : a, ∑ x₂ : bPlus,
          τPlus.matrix (x₁, x₂) (j.1, x) *
            (V.matrix x j.2 *
              (starRingEnd ℂ) (if x₁ = i.1 then V.matrix x₂ i.2 else 0))) =
          ∑ x₂ : bPlus, τPlus.matrix (i.1, x₂) (j.1, x) *
            (V.matrix x j.2 * (starRingEnd ℂ) (V.matrix x₂ i.2)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_eq_single_of_mem i.1 (Finset.mem_univ _)]
      · simp
      · intro x _ hx
        simp [hx]
    simp_rw [hsum]
  rw [hcompress]
  rw [ReferenceIsometry.applyMatrixRight_eq_kron_conj (a := a) V]
  change K * (Matrix.conjTranspose K * τPlus.matrix * K) *
      Matrix.conjTranspose K = _
  have hE : K * Matrix.conjTranspose K =
      Matrix.kronecker (1 : CMatrix a) (V.matrix * Matrix.conjTranspose V.matrix) := by
    dsimp [K]
    have hconj : Matrix.conjTranspose (Matrix.kronecker (1 : CMatrix a) V.matrix) =
        Matrix.kronecker (1 : CMatrix a) (Matrix.conjTranspose V.matrix) := by
      simpa [Matrix.kronecker] using
        (Matrix.conjTranspose_kronecker (1 : CMatrix a) V.matrix)
    change Matrix.kronecker (1 : CMatrix a) V.matrix *
        Matrix.conjTranspose (Matrix.kronecker (1 : CMatrix a) V.matrix) = _
    rw [hconj]
    simpa [Matrix.kronecker] using
      (Matrix.mul_kronecker_mul (1 : CMatrix a) (1 : CMatrix a)
        V.matrix (Matrix.conjTranspose V.matrix)).symm
  have hEherm : Matrix.conjTranspose
      (Matrix.kronecker (1 : CMatrix a)
        (V.matrix * Matrix.conjTranspose V.matrix)) =
      Matrix.kronecker (1 : CMatrix a)
        (V.matrix * Matrix.conjTranspose V.matrix) := by
    simp [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_mul]
  calc
    K * (Matrix.conjTranspose K * τPlus.matrix * K) * Matrix.conjTranspose K =
        (K * Matrix.conjTranspose K) * τPlus.matrix *
          (K * Matrix.conjTranspose K) := by simp [Matrix.mul_assoc]
    _ = Matrix.kronecker (1 : CMatrix a)
        (V.matrix * Matrix.conjTranspose V.matrix) * τPlus.matrix *
        Matrix.conjTranspose (Matrix.kronecker (1 : CMatrix a)
          (V.matrix * Matrix.conjTranspose V.matrix)) := by
      rw [hE, hEherm]

private theorem smoothClassical_conditioning_support_reconstruct
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (τPlus : SubnormalizedState (Prod a bPlus)) (V : ReferenceIsometry b bPlus)
    {P : CMatrix (Prod a bPlus)}
    (hSupport : Matrix.Supports τPlus.matrix P)
    (hImage : Matrix.Supports P
      (Matrix.kronecker (1 : CMatrix a)
        (V.matrix * Matrix.conjTranspose V.matrix))) :
    (τPlus.conditioningIsometryCompressed V).conditioningIsometryApply V = τPlus := by
  let E : CMatrix (Prod a bPlus) := Matrix.kronecker (1 : CMatrix a)
      (V.matrix * Matrix.conjTranspose V.matrix)
  have hEpos : E.PosSemidef := by
    dsimp [E]
    exact (Matrix.PosSemidef.one).kronecker
      (Matrix.posSemidef_self_mul_conjTranspose V.matrix)
  have hEid : E * E = E := by
    dsimp [E]
    rw [← Matrix.mul_kronecker_mul]
    have hVV : (V.matrix * Matrix.conjTranspose V.matrix) *
        (V.matrix * Matrix.conjTranspose V.matrix) =
      V.matrix * Matrix.conjTranspose V.matrix := by
      calc
        (V.matrix * Matrix.conjTranspose V.matrix) *
            (V.matrix * Matrix.conjTranspose V.matrix) =
          V.matrix * (Matrix.conjTranspose V.matrix * V.matrix) *
            Matrix.conjTranspose V.matrix := by simp [Matrix.mul_assoc]
        _ = V.matrix * Matrix.conjTranspose V.matrix := by
          rw [V.isometry]
          simp
    rw [one_mul, hVV]
  have hτE : Matrix.Supports τPlus.matrix E :=
    hSupport.trans (by simpa [E] using hImage)
  have hfix := smoothClassical_fixes_of_supports_projector
    τPlus.pos hEpos hEid hτE
  apply SubnormalizedState.ext
  rw [smoothClassical_conditioningIsometryCompressed_apply_matrix]
  have hrecon : E * τPlus.matrix * E = τPlus.matrix := by
    calc
      E * τPlus.matrix * E = E * (τPlus.matrix * E) := by simp [Matrix.mul_assoc]
      _ = E * τPlus.matrix := by rw [hfix.2]
      _ = τPlus.matrix := hfix.1
  simpa [E, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_mul] using hrecon

private theorem smoothClassical_conditioningIsometryCompressed_classicalOnXY
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (τPlus : SubnormalizedState ((a × x) × (y × bPlus)))
    (V : ReferenceIsometry (y × b) (y × bPlus))
    (hτ : τPlus.classicalOnXY)
    (hV : ∀ q p, q.1 ≠ p.1 → V.matrix q p = 0) :
    (τPlus.conditioningIsometryCompressed V).classicalOnXY := by
  constructor
  · intro i j hij
    rw [conditioningIsometryCompressed_matrix]
    change MatrixMap.kron (Channel.idChannel (a × x)).map
        (MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix))
        τPlus.matrix i j = 0
    simp [MatrixMap.kron_idChannel_left_apply_slice, MatrixMap.ofKraus,
       Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.mul_sum, Fintype.sum_prod_type,
       mul_comm, mul_left_comm]
    apply Finset.sum_eq_zero
    intro x₁ _
    apply Finset.sum_eq_zero
    intro y₁ _
    apply Finset.sum_eq_zero
    intro x₂ _
    apply Finset.sum_eq_zero
    intro x₃ _
    rw [hτ.1 (i.1, (x₂, x₃)) (j.1, (x₁, y₁)) hij]
    simp
  · intro i j hij
    rw [conditioningIsometryCompressed_matrix]
    change MatrixMap.kron (Channel.idChannel (a × x)).map
        (MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix))
        τPlus.matrix i j = 0
    simp [MatrixMap.kron_idChannel_left_apply_slice, MatrixMap.ofKraus,
       Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.mul_sum, Fintype.sum_prod_type,
       mul_comm, mul_left_comm]
    apply Finset.sum_eq_zero
    intro x₁ _
    apply Finset.sum_eq_zero
    intro y₁ _
    apply Finset.sum_eq_zero
    intro x₂ _
    apply Finset.sum_eq_zero
    intro x₃ _
    by_cases h₁ : x₁ = j.2.1
    · by_cases h₂ : x₂ = i.2.1
      · subst x₁
        subst x₂
        rw [hτ.2 (i.1, (i.2.1, x₃)) (j.1, (j.2.1, y₁)) hij]
        simp
      · rw [hV (x₂, x₃) i.2 h₂]
        simp
    · rw [hV (x₁, y₁) j.2 h₁]
      simp

private theorem smoothClassical_supportProjector_eq_of_posSemidef_idempotent
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : CMatrix d) (hM : M.PosSemidef) (hId : M * M = M) :
    supportProjector M hM = M := by
  let R : CMatrix d := supportProjector M hM
  have hsupport : Matrix.Supports R M := by
    simpa [R] using supportProjector_supports M hM
  have hRM : R * M = R := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    have hzero : M.mulVec (v - M.mulVec v) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hId]
      simp
    have hz := hsupport (v - M.mulVec v) hzero
    have hz' : R.mulVec v - R.mulVec (M.mulVec v) = 0 := by
      simpa [Matrix.mulVec_sub, Matrix.mulVec_mulVec] using hz
    calc
      (R * M).mulVec v = R.mulVec (M.mulVec v) := by
        rw [Matrix.mulVec_mulVec]
      _ = R.mulVec v := by
        exact (sub_eq_zero.mp hz').symm
  have hfix := supportProjector_fixes_of_supports
    (M := M) (N := M) hM hM (Matrix.Supports.refl _)
  have hMR : M = R := by
    calc
      M = R * M := hfix.1.symm
      _ = R := hRM
  exact hMR.symm

private def rightBlockDiagonal
    {d k : Type*} [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    (blocks : k → CMatrix d) : CMatrix (d × k) :=
  (Classical.blockDiagonal blocks).submatrix
    (Equiv.prodComm d k) (Equiv.prodComm d k)

private theorem rightBlockDiagonal_mul
    {d k : Type*} [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    (blocks blocks' : k → CMatrix d) :
    rightBlockDiagonal blocks * rightBlockDiagonal blocks' =
      rightBlockDiagonal (fun k => blocks k * blocks' k) := by
  unfold rightBlockDiagonal
  rw [Matrix.submatrix_mul_equiv, Classical.blockDiagonal_mul]

private theorem rightBlockDiagonal_posSemidef
    {d k : Type*} [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    (blocks : k → CMatrix d) (hblocks : ∀ k, (blocks k).PosSemidef) :
    (rightBlockDiagonal blocks).PosSemidef := by
  have h := Classical.blockDiagonal_posSemidef blocks hblocks
  simpa [rightBlockDiagonal] using h.submatrix (Equiv.prodComm d k)

private theorem rightBlockDiagonal_of_classical
    {d k : Type*} [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    (M : CMatrix (d × k))
    (hclass : ∀ i j, i.2 ≠ j.2 → M i j = 0) :
    M = rightBlockDiagonal (fun q =>
      Classical.block (M.submatrix (Equiv.prodComm d k).symm
        (Equiv.prodComm d k).symm) q q) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  by_cases h : i₂ = j₂
  · subst j₂
    change M (i₁, i₂) (j₁, i₂) =
        (Classical.blockDiagonal (fun q =>
        Classical.block (M.submatrix (Equiv.prodComm d k).symm
          (Equiv.prodComm d k).symm) q q))
        (i₂, i₁) (i₂, j₁)
    have hh := congrFun (congrFun
      (Classical.blockDiagonal_block_self
        (fun q => Classical.block (M.submatrix (Equiv.prodComm d k).symm
          (Equiv.prodComm d k).symm) q q) i₂) i₁) j₁
    simpa [Classical.block, rightBlockDiagonal, Equiv.prodComm_apply] using hh.symm
  · change M (i₁, i₂) (j₁, j₂) =
      (Classical.blockDiagonal (fun q =>
        Classical.block (M.submatrix (Equiv.prodComm d k).symm
          (Equiv.prodComm d k).symm) q q))
        (i₂, i₁) (j₂, j₁)
    have hh := congrFun (congrFun
      (Classical.blockDiagonal_block_ne
        (fun q => Classical.block (M.submatrix (Equiv.prodComm d k).symm
          (Equiv.prodComm d k).symm) q q) h) i₁) j₁
    change (Classical.blockDiagonal (fun q =>
      Classical.block (M.submatrix (Equiv.prodComm d k).symm
        (Equiv.prodComm d k).symm) q q)) (i₂, i₁) (j₂, j₁) = 0 at hh
    exact (hclass (i₁, i₂) (j₁, j₂) h).trans hh.symm

private theorem classicalBlockDiagonal_apply_ne
    {ι d : Type*} [Fintype ι] [DecidableEq ι]
    (blocks : ι → CMatrix d) {i j : ι × d} (hij : i.1 ≠ j.1) :
    Classical.blockDiagonal blocks i j = 0 := by
  unfold Classical.blockDiagonal
  rw [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro q _
  by_cases hqi : q = i.1
  · subst q
    by_cases h : i.1 = j.1
    · exact False.elim (hij h)
    · simp [Matrix.kronecker, Matrix.kroneckerMap_apply, h]
  · simp [Matrix.kronecker, Matrix.kroneckerMap_apply, hqi]

private theorem classicalBlockDiagonal_apply_eq
    {ι d : Type*} [Fintype ι] [DecidableEq ι]
    (blocks : ι → CMatrix d) (i j : d) (q : ι) :
    Classical.blockDiagonal blocks (q, i) (q, j) = blocks q i j := by
  unfold Classical.blockDiagonal
  rw [Matrix.sum_apply]
  rw [Finset.sum_eq_single q]
  · simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
  · intro q' _ hq'
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply, hq']
  · simp

private theorem classicalBlockDiagonal_mulVec_apply
    {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
    (blocks : ι → CMatrix d) (v : ι × d → ℂ) (q : ι) (i : d) :
    (Classical.blockDiagonal blocks).mulVec v (q, i) =
      (blocks q).mulVec (fun j => v (q, j)) i := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_eq_single q]
  · simp only [classicalBlockDiagonal_apply_eq]
  · intro q' _ hq'
    apply Finset.sum_eq_zero
    intro j _
    rw [classicalBlockDiagonal_apply_ne blocks (Ne.symm hq')]
    simp
  · simp

private theorem rightBlockDiagonal_supportProjector
    {d k : Type*} [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    (blocks : k → CMatrix d) (hblocks : ∀ k, (blocks k).PosSemidef) :
    supportProjector (rightBlockDiagonal blocks)
        (rightBlockDiagonal_posSemidef blocks hblocks) =
      rightBlockDiagonal (fun k => supportProjector (blocks k) (hblocks k)) := by
  let M : CMatrix (d × k) := rightBlockDiagonal blocks
  let Q : CMatrix (d × k) :=
    rightBlockDiagonal (fun k => supportProjector (blocks k) (hblocks k))
  have hM : M.PosSemidef := rightBlockDiagonal_posSemidef blocks hblocks
  have hQ : Q.PosSemidef := by
    apply rightBlockDiagonal_posSemidef
    intro k
    exact psdInvSqrt_support_posSemidef (hblocks k)
  have hQid : Q * Q = Q := by
    rw [rightBlockDiagonal_mul]
    apply congrArg rightBlockDiagonal
    funext k
    exact psdInvSqrt_support_idempotent (hblocks k)
  have hM_mul_Q : M * Q = M := by
    rw [rightBlockDiagonal_mul]
    apply congrArg rightBlockDiagonal
    funext k
    exact (supportProjector_fixes_of_supports (M := blocks k) (N := blocks k)
      (hblocks k) (hblocks k) (Matrix.Supports.refl _)).2
  have hMQ : Matrix.Supports M Q := Matrix.Supports.of_mul_right_eq_self hM_mul_Q
  have hQM : Matrix.Supports Q M := by
    intro v hv
    funext ij
    rcases ij with ⟨i, q⟩
    have hlocal : (blocks q).mulVec (fun j => v (j, q)) = 0 := by
      funext i'
      have hi := congrFun hv (i', q)
      have hiM : (rightBlockDiagonal blocks).mulVec v (i', q) = 0 := by
        simpa [M] using hi
      have hsub := congrFun (Matrix.submatrix_mulVec_equiv
        (Classical.blockDiagonal blocks) v (Equiv.prodComm d k)
          (Equiv.prodComm d k)) (i', q)
      have hdiag := hsub.symm.trans (by
        simpa [rightBlockDiagonal] using hiM)
      have hi' : (Classical.blockDiagonal blocks).mulVec
          (fun p : k × d => v (p.2, p.1)) (q, i') = 0 := by
        simpa [Function.comp_def, Equiv.prodComm_apply] using hdiag
      rw [classicalBlockDiagonal_mulVec_apply] at hi'
      exact hi'
    have hi := (supportProjector_supports (blocks q) (hblocks q))
      (fun j => v (j, q)) hlocal
    have hsub := congrFun (Matrix.submatrix_mulVec_equiv
      (Classical.blockDiagonal (fun k =>
        supportProjector (blocks k) (hblocks k))) v
        (Equiv.prodComm d k) (Equiv.prodComm d k)) (i, q)
    have hQi : Q.mulVec v (i, q) = 0 := by
      change ((Classical.blockDiagonal (fun k =>
        supportProjector (blocks k) (hblocks k))).submatrix
          (Equiv.prodComm d k) (Equiv.prodComm d k) *ᵥ v) (i, q) = 0
      have hdiag : (Classical.blockDiagonal (fun k =>
          supportProjector (blocks k) (hblocks k))).mulVec
          (v ∘ (Equiv.prodComm d k).symm) (q, i) = 0 := by
        rw [classicalBlockDiagonal_mulVec_apply]
        exact congrFun hi i
      exact hsub.trans hdiag
    exact hQi
  have hPM : Matrix.Supports (supportProjector M hM) M :=
    supportProjector_supports M hM
  have hPQ : Matrix.Supports (supportProjector M hM) Q := hPM.trans hMQ
  let P : CMatrix (d × k) := supportProjector M hM
  let R : CMatrix (d × k) := supportProjector Q hQ
  have hPR : Matrix.Supports P Q := by
    exact (supportProjector_supports M hM).trans hMQ
  have hRP : Matrix.Supports R M := by
    exact (supportProjector_supports Q hQ).trans hQM
  have hP_R : P * R = P := by
    simpa [P, R] using supportProjector_right_fixes_of_supports hQ hPR
  have hR_P : R * P = R := by
    simpa [P, R] using supportProjector_right_fixes_of_supports hM hRP
  have hPherm : Matrix.conjTranspose P = P := by
    dsimp [P, supportProjector]
    have hS := psdInvSqrt_support_isHermitian hM
    simp [ hS.eq]
  have hRherm : Matrix.conjTranspose R = R := by
    dsimp [R, supportProjector]
    have hS := psdInvSqrt_support_isHermitian hQ
    simp [ hS.eq]
  have hRQ : R = Q := by
    simpa [R] using smoothClassical_supportProjector_eq_of_posSemidef_idempotent
      Q hQ hQid
  have hEq : P = R := by
    calc
      P = Matrix.conjTranspose P := hPherm.symm
      _ = Matrix.conjTranspose (P * R) := by rw [hP_R]
      _ = R * P := by rw [Matrix.conjTranspose_mul, hPherm, hRherm]
      _ = R := hR_P
  have hPQ : P = Q := hEq.trans hRQ
  change P = Q
  exact hPQ

private def leftBlockDiagonal
    {d k : Type*} [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    (blocks : k → CMatrix d) : CMatrix (k × d) :=
  (rightBlockDiagonal blocks).submatrix (Equiv.prodComm k d)
    (Equiv.prodComm k d)

private theorem leftBlockDiagonal_mul
    {d k : Type*} [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    (blocks blocks' : k → CMatrix d) :
    leftBlockDiagonal blocks * leftBlockDiagonal blocks' =
      leftBlockDiagonal (fun k => blocks k * blocks' k) := by
  unfold leftBlockDiagonal
  rw [Matrix.submatrix_mul_equiv, rightBlockDiagonal_mul]

private theorem leftBlockDiagonal_supportProjector
    {d k : Type*} [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    (blocks : k → CMatrix d) (hblocks : ∀ k, (blocks k).PosSemidef) :
    supportProjector (leftBlockDiagonal blocks)
        (by
          simpa [leftBlockDiagonal] using
            (rightBlockDiagonal_posSemidef blocks hblocks).submatrix
              (Equiv.prodComm k d)) =
      leftBlockDiagonal (fun k => supportProjector (blocks k) (hblocks k)) := by
  let M : CMatrix (k × d) := leftBlockDiagonal blocks
  let Q : CMatrix (k × d) :=
    leftBlockDiagonal (fun k => supportProjector (blocks k) (hblocks k))
  have hM : M.PosSemidef := by
    simpa [M, leftBlockDiagonal] using
      (rightBlockDiagonal_posSemidef blocks hblocks).submatrix
        (Equiv.prodComm k d)
  have hQ : Q.PosSemidef := by
    simpa [Q, leftBlockDiagonal] using
      (rightBlockDiagonal_posSemidef
        (fun k => supportProjector (blocks k) (hblocks k)) (by
          intro k
          exact psdInvSqrt_support_posSemidef (hblocks k))).submatrix
        (Equiv.prodComm k d)
  have hQid : Q * Q = Q := by
    rw [leftBlockDiagonal_mul]
    apply congrArg leftBlockDiagonal
    funext k
    exact psdInvSqrt_support_idempotent (hblocks k)
  have hM_mul_Q : M * Q = M := by
    rw [leftBlockDiagonal_mul]
    apply congrArg leftBlockDiagonal
    funext k
    exact (supportProjector_fixes_of_supports (M := blocks k) (N := blocks k)
      (hblocks k) (hblocks k) (Matrix.Supports.refl _)).2
  have hMQ : Matrix.Supports M Q := Matrix.Supports.of_mul_right_eq_self hM_mul_Q
  have hQM : Matrix.Supports Q M := by
    intro v hv
    funext ij
    rcases ij with ⟨q, i⟩
    have hlocal : (blocks q).mulVec (fun j => v (q, j)) = 0 := by
      funext i'
      have hi := congrFun hv (q, i')
      have hi' : (Classical.blockDiagonal blocks).mulVec v (q, i') = 0 := by
        simpa [M, leftBlockDiagonal, rightBlockDiagonal, Equiv.prodComm_apply] using hi
      rw [classicalBlockDiagonal_mulVec_apply] at hi'
      exact hi'
    have hi := (supportProjector_supports (blocks q) (hblocks q))
      (fun j => v (q, j)) hlocal
    have hi' : (Classical.blockDiagonal (fun k =>
        supportProjector (blocks k) (hblocks k))).mulVec v (q, i) = 0 := by
      rw [classicalBlockDiagonal_mulVec_apply]
      exact congrFun hi i
    simpa [Q, leftBlockDiagonal, rightBlockDiagonal] using hi'
  let P : CMatrix (k × d) := supportProjector M hM
  let R : CMatrix (k × d) := supportProjector Q hQ
  have hPR : Matrix.Supports P Q := by
    exact (supportProjector_supports M hM).trans hMQ
  have hRP : Matrix.Supports R M := by
    exact (supportProjector_supports Q hQ).trans hQM
  have hP_R : P * R = P := by
    simpa [P, R] using supportProjector_right_fixes_of_supports hQ hPR
  have hR_P : R * P = R := by
    simpa [P, R] using supportProjector_right_fixes_of_supports hM hRP
  have hPherm : Matrix.conjTranspose P = P := by
    dsimp [P, supportProjector]
    have hS := psdInvSqrt_support_isHermitian hM
    simp [ hS.eq]
  have hRherm : Matrix.conjTranspose R = R := by
    dsimp [R, supportProjector]
    have hS := psdInvSqrt_support_isHermitian hQ
    simp [ hS.eq]
  have hRQ : R = Q := by
    simpa [R] using smoothClassical_supportProjector_eq_of_posSemidef_idempotent
      Q hQ hQid
  have hEq : P = R := by
    calc
      P = Matrix.conjTranspose P := hPherm.symm
      _ = Matrix.conjTranspose (P * R) := by rw [hP_R]
      _ = R * P := by rw [Matrix.conjTranspose_mul, hPherm, hRherm]
      _ = R := hR_P
  have hPQ : P = Q := hEq.trans hRQ
  change P = Q
  exact hPQ

private theorem supportProjector_congr
    {d : Type*} [Fintype d] [DecidableEq d]
    (M N : CMatrix d) (hM : M.PosSemidef) (hN : N.PosSemidef)
    (hMN : M = N) :
    supportProjector M hM = supportProjector N hN := by
  subst N
  rfl

set_option maxRecDepth 100000 in
private theorem supportProjector_rightBlockDiagonal_of_classical
    {d k : Type*} [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    (M : CMatrix (d × k)) (hM : M.PosSemidef)
    (hclass : ∀ i j, i.2 ≠ j.2 → M i j = 0) :
    supportProjector M hM =
      rightBlockDiagonal (d := d) (k := k) (fun q : k =>
        supportProjector
          (Classical.block (M.submatrix (Equiv.prodComm d k).symm
            (Equiv.prodComm d k).symm) q q)
          (by
            change (M.submatrix (fun i : d => (i, q))
              (fun i : d => (i, q))).PosSemidef
            exact hM.submatrix (fun i : d => (i, q)))) := by
  let blocks : k → CMatrix d := fun q =>
    Classical.block (M.submatrix (Equiv.prodComm d k).symm
      (Equiv.prodComm d k).symm) q q
  have hblocks : ∀ q, (blocks q).PosSemidef := by
    intro q
    change (M.submatrix (fun i : d => (i, q))
      (fun i : d => (i, q))).PosSemidef
    exact hM.submatrix (fun i : d => (i, q))
  have hdecomp : M = rightBlockDiagonal blocks := by
    exact rightBlockDiagonal_of_classical M hclass
  have hM' : (rightBlockDiagonal blocks).PosSemidef := by
    rw [← hdecomp]
    exact hM
  calc
    supportProjector M hM = supportProjector (rightBlockDiagonal blocks) hM' := by
      exact supportProjector_congr M _ hM hM' hdecomp
    _ = rightBlockDiagonal (fun k => supportProjector (blocks k) (hblocks k)) :=
      rightBlockDiagonal_supportProjector blocks hblocks

set_option maxRecDepth 100000 in
private theorem supportProjector_leftBlockDiagonal_of_classical
    {d k : Type*} [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    (M : CMatrix (k × d)) (hM : M.PosSemidef)
    (hclass : ∀ i j, i.1 ≠ j.1 → M i j = 0) :
    supportProjector M hM =
      leftBlockDiagonal (d := d) (k := k) (fun q : k =>
        supportProjector
          (Classical.block M q q)
          (by
            exact hM.submatrix (fun i : d => (q, i)))) := by
  let blocks : k → CMatrix d := fun q => Classical.block M q q
  have hblocks : ∀ q, (blocks q).PosSemidef := by
    intro q
    exact hM.submatrix (fun i : d => (q, i))
  have hdecomp : M = leftBlockDiagonal blocks := by
    ext i j
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    by_cases h : i₁ = j₁
    · subst j₁
      unfold leftBlockDiagonal rightBlockDiagonal
      change M (i₁, i₂) (i₁, j₂) =
        Classical.blockDiagonal blocks (i₁, i₂) (i₁, j₂)
      rw [classicalBlockDiagonal_apply_eq blocks i₂ j₂ i₁]
      rfl
    · unfold leftBlockDiagonal rightBlockDiagonal
      change M (i₁, i₂) (j₁, j₂) =
        Classical.blockDiagonal blocks (i₁, i₂) (j₁, j₂)
      rw [classicalBlockDiagonal_apply_ne blocks h]
      exact hclass _ _ h
  have hM' : (leftBlockDiagonal blocks).PosSemidef := by
    rw [← hdecomp]
    exact hM
  calc
    supportProjector M hM = supportProjector (leftBlockDiagonal blocks) hM' := by
      exact supportProjector_congr M _ hM hM' hdecomp
    _ = leftBlockDiagonal (fun k => supportProjector (blocks k) (hblocks k)) :=
      leftBlockDiagonal_supportProjector blocks hblocks

private theorem rightBlockDiagonal_apply_ne
    {d k : Type*} [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    (blocks : k → CMatrix d) {i j : d × k} (hij : i.2 ≠ j.2) :
    rightBlockDiagonal blocks i j = 0 := by
  unfold rightBlockDiagonal
  change Classical.blockDiagonal blocks (i.2, i.1) (j.2, j.1) = 0
  exact classicalBlockDiagonal_apply_ne blocks hij

private theorem leftBlockDiagonal_apply_ne
    {d k : Type*} [Fintype d] [DecidableEq d]
    [Fintype k] [DecidableEq k]
    (blocks : k → CMatrix d) {i j : k × d} (hij : i.1 ≠ j.1) :
    leftBlockDiagonal blocks i j = 0 := by
  unfold leftBlockDiagonal rightBlockDiagonal
  change Classical.blockDiagonal blocks (i.1, i.2) (j.1, j.2) = 0
  exact classicalBlockDiagonal_apply_ne blocks hij

private theorem sandwich_preserves_offdiag
    {c d : Type*} [Fintype c] [DecidableEq c]
    (P X : CMatrix c) (coord : c → d)
    (hP : ∀ i j, coord i ≠ coord j → P i j = 0)
    (hX : ∀ i j, coord i ≠ coord j → X i j = 0)
    {i j : c} (hij : coord i ≠ coord j) :
    (P * X * Matrix.conjTranspose P) i j = 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [mul_eq_zero]
  by_cases hkj : coord k = coord j
  · left
    apply Finset.sum_eq_zero
    intro l _
    by_cases hil : coord i = coord l
    · have hlk : coord l ≠ coord k := by
        intro h
        apply hij
        exact hil.trans (h.trans hkj)
      rw [hX l k hlk]
      simp
    · rw [show P i l = 0 by apply hP; exact hil]
      simp
  · right
    rw [show P j k = 0 by apply hP; intro h; exact hkj h.symm]
    simp

private theorem supportFilterState_classicalOnXY_of_classical
    (rho tau : SubnormalizedState ((a × x) × (y × b)))
    (hρ : rho.classicalOnXY) (hτ : tau.classicalOnXY) :
    (supportFilterState rho tau).classicalOnXY := by
  have hA : ∀ i j : a × x, i.2 ≠ j.2 →
      tau.marginalA.matrix i j = 0 := by
    intro i j hij
    rw [SubnormalizedState.marginalA_matrix]
    change (∑ k : y × b, tau.matrix (i, k) (j, k)) = 0
    apply Finset.sum_eq_zero
    intro k _
    exact hτ.1 (i, k) (j, k) hij
  have hB : ∀ i j : y × b, i.1 ≠ j.1 →
      tau.marginalB.matrix i j = 0 := by
    intro i j hij
    rw [SubnormalizedState.marginalB_matrix]
    change (∑ k : a × x, tau.matrix (k, i) (k, j)) = 0
    apply Finset.sum_eq_zero
    intro k _
    exact hτ.2 (k, i) (k, j) hij
  have hPA := supportProjector_rightBlockDiagonal_of_classical
    rho.marginalA.matrix rho.marginalA.pos (by
      intro i j hij
      rw [SubnormalizedState.marginalA_matrix]
      change (∑ k : y × b, rho.matrix (i, k) (j, k)) = 0
      apply Finset.sum_eq_zero
      intro k _
      exact hρ.1 (i, k) (j, k) hij)
  have hPB := supportProjector_leftBlockDiagonal_of_classical
    rho.marginalB.matrix rho.marginalB.pos (by
      intro i j hij
      rw [SubnormalizedState.marginalB_matrix]
      change (∑ k : a × x, rho.matrix (k, i) (k, j)) = 0
      apply Finset.sum_eq_zero
      intro k _
      exact hρ.2 (k, i) (k, j) hij)
  let P := bipartiteSupportProjector rho
  have hPX : ∀ i j, i.1.2 ≠ j.1.2 → P i j = 0 := by
    intro i j hij
    change (supportProjector rho.marginalA.matrix rho.marginalA.pos) i.1 j.1 *
      (supportProjector rho.marginalB.matrix rho.marginalB.pos) i.2 j.2 = 0
    rw [hPA, rightBlockDiagonal_apply_ne _ hij]
    simp
  have hPY : ∀ i j, i.2.1 ≠ j.2.1 → P i j = 0 := by
    intro i j hij
    change (supportProjector rho.marginalA.matrix rho.marginalA.pos) i.1 j.1 *
      (supportProjector rho.marginalB.matrix rho.marginalB.pos) i.2 j.2 = 0
    rw [hPB, leftBlockDiagonal_apply_ne _ hij]
    simp
  constructor <;> intro i j hij
  · rw [supportFilterState_matrix]
    simpa [P] using sandwich_preserves_offdiag P tau.matrix
      (fun i : (a × x) × (y × b) => i.1.2) hPX hτ.1 hij
  · rw [supportFilterState_matrix]
    simpa [P] using sandwich_preserves_offdiag P tau.matrix
      (fun i : (a × x) × (y × b) => i.2.1) hPY hτ.2 hij

private theorem smoothClassical_conditioningIsometryApply_classicalOnXY
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (rho : SubnormalizedState ((a × x) × (y × b)))
    (V : ReferenceIsometry (y × b) (y × bPlus))
    (hρ : rho.classicalOnXY)
    (hV : ∀ q p, q.1 ≠ p.1 → V.matrix q p = 0) :
    (rho.conditioningIsometryApply V).classicalOnXY := by
  constructor
  · intro i j hij
    rw [conditioningIsometryApply_matrix]
    change (V.matrix * ReferenceIsometry.rightBlock rho.matrix i.1 j.1 *
      Matrix.conjTranspose V.matrix) i.2 j.2 = 0
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [mul_eq_zero]
    left
    apply Finset.sum_eq_zero
    intro l _
    simp only [ReferenceIsometry.rightBlock]
    rw [hρ.1 (i.1, l) (j.1, k) hij]
    simp
  · intro i j hij
    rw [conditioningIsometryApply_matrix]
    change (V.matrix * ReferenceIsometry.rightBlock rho.matrix i.1 j.1 *
      Matrix.conjTranspose V.matrix) i.2 j.2 = 0
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : j.2.1 = k.1
    · rw [mul_eq_zero]
      left
      apply Finset.sum_eq_zero
      intro l _
      simp only [ReferenceIsometry.rightBlock]
      by_cases hl : i.2.1 = l.1
      · have hy : l.1 ≠ k.1 := by
          intro heq
          exact hij (hl.trans (heq.trans hk.symm))
        rw [hρ.2 (i.1, l) (j.1, k) hy]
        simp
      · rw [show V.matrix i.2 l = 0 by apply hV; exact hl]
        simp
    · rw [mul_eq_zero]
      right
      rw [show V.matrix j.2 k = 0 by apply hV; exact hk]
      simp

/-! ## Public max optimizer and the combined source-shaped statement -/

/-
private theorem maxLiftedCanonicalPurification_center_test
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (rho : State ((a × x) × (y × bPlus)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    (coherentMaxPure (a := a) (x := x)
      (b := maxReferenceType (a := a) (x := x) (y := y) (bPlus := bPlus))
      (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
        (bPlus := bPlus) rho hclassical)
      (maxLiftedCanonicalPurification_fixed (a := a) (x := x) (y := y)
        (bPlus := bPlus) rho hclassical)).state.marginalA =
      rho.conditioningIsometryApply (maxConditioningEmbedding
        (a := a) (x := x) (y := y) (bPlus := bPlus)) := by
  apply State.ext
  ext i j
  simp [coherentMaxPure, coherentLiftOfFixed, coherentLiftAmplitude,
    State.acToABReferenceEquiv, coherentMaxSwapEquiv, PureVector.reindex,
    PureVector.reindex_state, State.reindex, State.marginalA,
    partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
    PureVector.ofAmplitudeMatrix, Equiv.prodComm,
    maxLiftedCanonicalPurification, maxReferenceEmbedding,
    maxConditioningEmbedding, canonicalXYMaxPurification,
    ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
    ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
    ReferenceIsometry.ofInjective, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum]
  simp [Finset.sum_ite_eq', apply_ite, eq_comm, Prod.ext_iff,
    mul_assoc, mul_comm]

private theorem canonicalXYMaxPurification_center_test
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    (coherentMaxPure (a := a) (x := x) (b := b)
      (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := b)
        rho hclassical)
      (canonicalXYMaxPurification_fixed (a := a) (x := x) (y := y) (b := b)
        rho hclassical)).state.marginalA = rho := by
  apply State.ext
  ext i j
  simp [coherentMaxPure, coherentLiftOfFixed, coherentLiftAmplitude,
    State.acToABReferenceEquiv, coherentMaxSwapEquiv, PureVector.reindex,
    PureVector.reindex_state, State.reindex, State.marginalA,
    partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
    PureVector.ofAmplitudeMatrix, Equiv.prodComm,
    canonicalXYMaxPurification, canonicalXYMaxAmplitude,
    ReferenceIsometry.ofInjective, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum]
  simp [Finset.sum_ite_eq', apply_ite, eq_comm, Prod.ext_iff,
    mul_assoc, mul_comm]

private theorem sourceCanonicalMaxPurification_center_test
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY)
    (hfixed : classicalCoherentMap (a := Sum extra a) (x := x)
      (c := a × b) (y' := y)
      ((sourceExtensionEtaIsometry (a := a) (x := x) (extra := extra)
        (c := a × b) (y' := y)).applyPureVectorRight
        (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := b)
          rho hclassical)).amplitudeMatrix *
        ((sourceExtensionEtaIsometry (a := a) (x := x) (extra := extra)
          (c := a × b) (y' := y)).applyPureVectorRight
          (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := b)
            rho hclassical)).amplitudeMatrix.conjTranspose) =
      (sourceExtensionEtaIsometry (a := a) (x := x) (extra := extra)
        (c := a × b) (y' := y)).applyPureVectorRight
        (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := b)
          rho hclassical)).amplitudeMatrix *
        ((sourceExtensionEtaIsometry (a := a) (x := x) (extra := extra)
          (c := a × b) (y' := y)).applyPureVectorRight
            (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := b)
              rho hclassical)).amplitudeMatrix.conjTranspose) :
    (coherentMaxPure (a := Sum extra a) (x := x) (b := b)
      ((sourceExtensionEtaIsometry (a := a) (x := x) (extra := extra)
        (c := a × b) (y' := y)).applyPureVectorRight
        (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := b)
          rho hclassical)) hfixed).state.marginalA =
      rho.toSubnormalized.sourceIsometryApply
        (sourceExtensionAXIsometry (a := a) (x := x) (extra := extra)) := by
  apply State.ext
  ext i j
  simp [coherentMaxPure, coherentLiftOfFixed, coherentLiftAmplitude,
    State.acToABReferenceEquiv, coherentMaxSwapEquiv, PureVector.reindex,
    PureVector.reindex_state, State.reindex, State.marginalA,
    partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
    PureVector.ofAmplitudeMatrix, Equiv.prodComm,
    sourceExtensionEtaIsometry, sourceExtensionAXIsometry,
    sourceExtensionIdentityIsometry, canonicalXYMaxPurification,
    canonicalXYMaxAmplitude, ReferenceIsometry.applyPureVectorRight_amp,
    ReferenceIsometry.applyAmpRight, ReferenceIsometry.applyMatrixRight,
    ReferenceIsometry.rightBlock, ReferenceIsometry.ofInjective,
    SubnormalizedState.sourceIsometryApply_matrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum]
  simp [Finset.sum_ite_eq', apply_ite, eq_comm, Prod.ext_iff,
    mul_assoc, mul_comm]

private theorem sourceExtensionEtaIsometry_fixed
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY) :
    classicalCoherentMap (a := Sum extra a) (x := x) (c := a × b) (y' := y)
      ((sourceExtensionEtaIsometry (a := a) (x := x) (extra := extra)
        (c := a × b) (y' := y)).applyPureVectorRight
        (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
          (bPlus := b) rho hclassical)).amplitudeMatrix *
        ((sourceExtensionEtaIsometry (a := a) (x := x) (extra := extra)
          (c := a × b) (y' := y)).applyPureVectorRight
          (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
            (bPlus := b) rho hclassical)).amplitudeMatrix.conjTranspose =
      ((sourceExtensionEtaIsometry (a := a) (x := x) (extra := extra)
        (c := a × b) (y' := y)).applyPureVectorRight
        (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
          (bPlus := b) rho hclassical)).amplitudeMatrix *
        ((sourceExtensionEtaIsometry (a := a) (x := x) (extra := extra)
          (c := a × b) (y' := y)).applyPureVectorRight
          (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
            (bPlus := b) rho hclassical)).amplitudeMatrix.conjTranspose := by
  apply Matrix.ext
  intro i j
  rw [classicalCoherentMap_apply]
  by_cases hcopy : i.1.2 = i.2.2.1 ∧
      j.1.2 = j.2.2.1 ∧ i.2.2.2 = j.2.2.2
  · simp [hcopy]
  · simp [hcopy]

private theorem maximallyMixed_classicalOnXY
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    :
    (State.maximallyMixed ((extra × x) × (y × b))).toSubnormalized.classicalOnXY := by
  constructor <;> intro i j hij
  · simp [State.maximallyMixed_matrix, Matrix.one_apply]
    exact (hij (by simp)).elim
  · simp [State.maximallyMixed_matrix, Matrix.one_apply]
    exact (hij (by simp)).elim

private theorem maximallyMixed_classicalCoherentOn
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {c : Type*} [Fintype c] [DecidableEq c]
    {y' : Type*} [Fintype y'] [DecidableEq y'] :
    (State.maximallyMixed ((extra × x) × (c × x × y'))).toSubnormalized
      |> classicalCoherentOn := by
  intro i j hij
  simp [State.maximallyMixed_matrix, Matrix.one_apply]
  by_contra hne
  apply hij
  push_neg at hne
  exact Or.inl (by exact hne)

private theorem sourceCanonicalMaxPurification_purifies_extension
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY)
    (failure : State ((extra × x) × ((a × b) × (x × y)))) :
    let etaCenter := canonicalXYComplementaryState
      (a := a) (x := x) (y := y) (b := b) rho
    let psi := (sourceExtensionEtaIsometry (a := a) (x := x)
      (extra := extra) (c := a × b) (y' := y)).applyPureVectorRight
      (canonicalXYMaxPurification (a := a) (x := x) (y := y) (b := b)
        rho hclassical)
    psi.state.marginalB.toSubnormalized =
      (sourceNormalizedExtension (a := a) (x := x)
        etaCenter.toSubnormalized failure).toSubnormalized := by
  dsimp
  apply SubnormalizedState.ext
  ext i j
  simp [sourceNormalizedExtension, State.reindex_matrix,
    sourceExtensionStateEquiv, sourceExtensionXEquiv,
    sourceExtensionEtaIsometry, sourceExtensionAXIsometry,
    sourceExtensionIdentityIsometry, SmoothNormalizedExtension.blockExtensionState_matrix,
    SmoothNormalizedExtension.sourceSumEquiv, State.marginalB_matrix,
    PureVector.state_matrix, PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose,
    ReferenceIsometry.applyPureVectorRight_amp, ReferenceIsometry.applyAmpRight,
    ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
    ReferenceIsometry.ofInjective, canonicalXYMaxPurification,
    canonicalXYMaxAmplitude, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.mulVec, dotProduct, Matrix.sum_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  simp [Finset.sum_ite_eq', apply_ite, eq_comm, Prod.ext_iff,
    mul_assoc, mul_comm]

private theorem sourceMaxLiftedPurification_center_test
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY)
    (hfixed : classicalCoherentMap (a := Sum extra a) (x := x)
      (c := a × b) (y' := y)
      ((sourceExtensionEtaIsometry (a := a) (x := x) (extra := extra)
        (c := a × b) (y' := y)).applyPureVectorRight
        (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
          (bPlus := b) rho hclassical)).amplitudeMatrix *
        ((sourceExtensionEtaIsometry (a := a) (x := x) (extra := extra)
          (c := a × b) (y' := y)).applyPureVectorRight
          (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
            (bPlus := b) rho hclassical)).amplitudeMatrix.conjTranspose) =
      (sourceExtensionEtaIsometry (a := a) (x := x) (extra := extra)
        (c := a × b) (y' := y)).applyPureVectorRight
        (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
          (bPlus := b) rho hclassical)).amplitudeMatrix *
        ((sourceExtensionEtaIsometry (a := a) (x := x) (extra := extra)
          (c := a × b) (y' := y)).applyPureVectorRight
            (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
              (bPlus := b) rho hclassical)).amplitudeMatrix.conjTranspose) :
    (coherentMaxPure (a := Sum extra a) (x := x)
      (b := maxReferenceType (a := a) (x := x) (y := y) (bPlus := b))
      ((sourceExtensionEtaIsometry (a := a) (x := x) (extra := extra)
        (c := a × b) (y' := y)).applyPureVectorRight
        (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
          (bPlus := b) rho hclassical)) hfixed).state.marginalA =
      (rho.conditioningIsometryApply (maxConditioningEmbedding
        (a := a) (x := x) (y := y) (bPlus := b))).toSubnormalized
        |>.sourceIsometryApply
          (sourceExtensionAXIsometry (a := a) (x := x) (extra := extra)) := by
  apply SubnormalizedState.ext
  ext i j
  simp [coherentMaxPure, coherentLiftOfFixed, coherentLiftAmplitude,
    State.acToABReferenceEquiv, coherentMaxSwapEquiv, PureVector.reindex,
    PureVector.reindex_state, State.reindex, State.marginalA,
    partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
    PureVector.ofAmplitudeMatrix, Equiv.prodComm,
    sourceExtensionEtaIsometry, sourceExtensionAXIsometry,
    sourceExtensionIdentityIsometry, maxLiftedCanonicalPurification,
    maxReferenceEmbedding, maxConditioningEmbedding,
    canonicalXYMaxPurification, canonicalXYMaxAmplitude,
    ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
    ReferenceIsometry.applyPureVectorRight_amp,
    ReferenceIsometry.applyAmpRight, ReferenceIsometry.applyMatrixRight,
    ReferenceIsometry.rightBlock, ReferenceIsometry.ofInjective,
    SubnormalizedState.sourceIsometryApply_matrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum]
  simp [Finset.sum_ite_eq', apply_ite, eq_comm, Prod.ext_iff,
    mul_assoc, mul_comm]

private theorem sourceMaxLiftedPurification_purifies_extension
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (rho : State ((a × x) × (y × b)))
    (hclassical : rho.toSubnormalized.classicalOnXY)
    (failure : State ((extra × x) × ((a × b) × (x × y)))) :
    let etaCenter := canonicalXYComplementaryState
      (a := a) (x := x) (y := y) (b := b) rho
    let psi := (sourceExtensionEtaIsometry (a := a) (x := x)
      (extra := extra) (c := a × b) (y' := y)).applyPureVectorRight
      (maxLiftedCanonicalPurification (a := a) (x := x) (y := y)
        (bPlus := b) rho hclassical)
    psi.state.marginalB.toSubnormalized =
      (sourceNormalizedExtension (a := a) (x := x)
        etaCenter.toSubnormalized failure).toSubnormalized := by
  dsimp
  apply SubnormalizedState.ext
  ext i j
  simp [sourceNormalizedExtension, State.reindex_matrix,
    sourceExtensionStateEquiv, sourceExtensionXEquiv,
    sourceExtensionEtaIsometry, sourceExtensionAXIsometry,
    sourceExtensionIdentityIsometry, SmoothNormalizedExtension.blockExtensionState_matrix,
    SmoothNormalizedExtension.sourceSumEquiv, State.marginalB_matrix,
    PureVector.state_matrix, PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose,
    ReferenceIsometry.applyPureVectorRight_amp, ReferenceIsometry.applyAmpRight,
    ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
    ReferenceIsometry.ofInjective, maxLiftedCanonicalPurification,
    maxReferenceEmbedding, canonicalXYMaxPurification,
    canonicalXYMaxAmplitude, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.mulVec, dotProduct, Matrix.sum_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  simp [Finset.sum_ite_eq', apply_ite, eq_comm, Prod.ext_iff,
    mul_assoc, mul_comm]

-/

/-- Smooth conditional max-entropy has a classical optimizer whenever its center
is classical on the designated `X` and `Y` coordinates. -/
theorem smoothConditionalMaxEntropy_exists_classical_optimizer
    [Nonempty a] [Nonempty b]
    (rho : SubnormalizedState ((a × x) × (y × b))) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < Real.sqrt rho.matrix.trace.re)
    (hclassical : rho.classicalOnXY) :
    ∃ tau : SubnormalizedState ((a × x) × (y × b)),
      ∃ htau : tau.matrix ≠ 0,
      rho.purifiedBall ε tau ∧ tau.classicalOnXY ∧
        rho.smoothConditionalMaxEntropy ε hε0 hε =
          tau.conditionalMaxEntropyFinite htau := by
  have hρ : 0 < rho.matrix.trace.re :=
    Real.sqrt_pos.mp (lt_of_le_of_lt hε0 hε)
  have hfull : Nonempty ((a × x) × (y × b)) :=
    nonempty_of_trace_pos rho.matrix hρ
  letI : Nonempty (a × x) := by
    rcases hfull with ⟨i⟩
    exact ⟨i.1⟩
  letI : Nonempty (y × b) := by
    rcases hfull with ⟨i⟩
    exact ⟨i.2⟩
  let V : ReferenceIsometry (y × b)
      (y × maxReferenceType (a := a) (x := x) (y := y) (bPlus := b)) :=
    maxConditioningEmbedding (a := a) (x := x) (y := y) (bPlus := b)
  let rhoPlus := rho.conditioningIsometryApply V
  letI : Nonempty y := by
    rcases hfull with ⟨i⟩
    exact ⟨i.2.1⟩
  let y0 : y := Classical.choice (inferInstance : Nonempty y)
  let b0 : b := Classical.choice (inferInstance : Nonempty b)
  letI : Nonempty (maxReferenceType (a := a) (x := x) (y := y) (bPlus := b)) :=
    ⟨(y0, Sum.inl (y0, b0))⟩
  letI : Nonempty (y × maxReferenceType
      (a := a) (x := x) (y := y) (bPlus := b)) := inferInstance
  have hV : ∀ q p, q.1 ≠ p.1 → V.matrix q p = 0 := by
    intro q p hqp
    have hne : q ≠ (p.1, (p.1, Sum.inl p)) := by
      intro heq
      exact hqp (congrArg Prod.fst heq)
    simp [V, maxConditioningEmbedding, ReferenceIsometry.ofInjective, hne]
  have hclassRhoPlus : rhoPlus.classicalOnXY := by
    simpa [rhoPlus] using
      smoothClassical_conditioningIsometryApply_classicalOnXY
        (a := a) (x := x) (y := y) (b := b) rho V hclassical hV
  have hεPlus : ε < Real.sqrt rhoPlus.matrix.trace.re := by
    change ε < Real.sqrt ((rho.conditioningIsometryApply V).matrix.trace.re)
    rw [conditioningIsometryApply_trace_re]
    exact hε
  obtain ⟨tauPlus, hballPlus, hclassPlus, hplusEq⟩ :=
    exists_classical_max_candidate_on_enlarged_conditioning
      (a := a) (x := x) (y := y) (b := b) rho hε0 hε hclassical
  have hballPlus' : rhoPlus.purifiedBall ε tauPlus := by
    simpa [rhoPlus, V] using hballPlus
  have hplusEq' : rhoPlus.smoothConditionalMaxEntropy ε hε0 hεPlus =
      tauPlus.conditionalMaxEntropyRaw := by
    calc
      rhoPlus.smoothConditionalMaxEntropy ε hε0 hεPlus =
          rho.smoothConditionalMaxEntropy ε hε0 hε := by
        simpa [rhoPlus] using
          smoothConditionalMaxEntropy_conditioningIsometryApply
            (a := a × x) (b := y × b) rho V hε0 hε
      _ = tauPlus.conditionalMaxEntropyRaw := hplusEq.symm
  rcases rhoPlus.smoothConditionalMaxEntropy_exists_optimizer
      (a := a × x) hε0 hεPlus with
    ⟨rhoPlusMax, hρPlusMax, hballMax, hmaxEq, hoptimizer⟩
  let tauProj := supportFilterState rhoPlus tauPlus
  have hclassProj : tauProj.classicalOnXY := by
    exact supportFilterState_classicalOnXY_of_classical
      rhoPlus tauPlus hclassRhoPlus hclassPlus
  have hballProj : rhoPlus.purifiedBall ε tauProj := by
    exact supportFilterState_purifiedBall (supportFilterState_center rhoPlus)
      hballPlus'
  have hτPlus : 0 < tauPlus.matrix.trace.re :=
    rhoPlus.purifiedBall_trace_pos_of_lt_sqrt_trace tauPlus hεPlus hballPlus'
  have hτProj : 0 < tauProj.matrix.trace.re :=
    rhoPlus.purifiedBall_trace_pos_of_lt_sqrt_trace tauProj hεPlus hballProj
  have hτProjNe : tauProj.matrix ≠ 0 := by
    intro hzero
    rw [hzero] at hτProj
    simp at hτProj
  have hfilter_le : tauProj.conditionalMaxEntropyRaw ≤
      tauPlus.conditionalMaxEntropyRaw := by
    exact supportFilter_conditionalMaxEntropyRaw_le rhoPlus tauPlus hτPlus hτProj
  have hfilter_ge : tauPlus.conditionalMaxEntropyRaw ≤
      tauProj.conditionalMaxEntropyRaw := by
    calc
      tauPlus.conditionalMaxEntropyRaw =
          rhoPlus.smoothConditionalMaxEntropy ε hε0 hεPlus := hplusEq'.symm
      _ = rhoPlusMax.conditionalMaxEntropyFinite hρPlusMax := hmaxEq
      _ ≤ tauProj.conditionalMaxEntropyFinite hτProjNe :=
        hoptimizer tauProj hτProjNe hballProj
  have hfilter_eq : tauProj.conditionalMaxEntropyRaw =
      tauPlus.conditionalMaxEntropyRaw := le_antisymm hfilter_le hfilter_ge
  let tauRaw := tauProj.conditioningIsometryCompressed V
  have hballTauRaw : rho.purifiedBall ε tauRaw := by
    exact purifiedBall_conditioningIsometryCompressed_of_conditioningIsometryApply
      (a := a × x) V hballProj
  have hclassTauRaw : tauRaw.classicalOnXY := by
    exact smoothClassical_conditioningIsometryCompressed_classicalOnXY
      tauProj V hclassProj hV
  have hτRaw : 0 < tauRaw.matrix.trace.re :=
    rho.purifiedBall_trace_pos_of_lt_sqrt_trace tauRaw hε hballTauRaw
  have hτRawNe : tauRaw.matrix ≠ 0 := by
    intro hzero
    rw [hzero] at hτRaw
    simp at hτRaw
  have himage := smoothClassical_conditioning_support_projector_supports_image
    (a := a × x) rho V
  have hreconstruct := smoothClassical_conditioning_support_reconstruct
    (a := a × x) tauProj V (supportFilterState_supports_projector rhoPlus tauPlus)
      himage
  have hraw := conditionalMaxEntropyRaw_conditioningIsometryApply_eq
    (a := a × x) tauRaw V
  have hraw' : tauProj.conditionalMaxEntropyRaw = tauRaw.conditionalMaxEntropyRaw := by
    rw [hreconstruct] at hraw
    exact hraw
  refine ⟨tauRaw, hτRawNe, hballTauRaw, hclassTauRaw, ?_⟩
  calc
    rho.smoothConditionalMaxEntropy ε hε0 hε =
        tauPlus.conditionalMaxEntropyRaw := hplusEq.symm
    _ = tauProj.conditionalMaxEntropyRaw := hfilter_eq.symm
    _ = tauRaw.conditionalMaxEntropyFinite hτRawNe := hraw'

/-
/-- Smooth conditional max-entropy has a classical optimizer whenever its center
is classical on the designated `X` and `Y` coordinates. -/
theorem smoothConditionalMaxEntropy_exists_classical_optimizer
    [Nonempty a] [Nonempty b]
    (rho : SubnormalizedState ((a × x) × (y × b))) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < Real.sqrt rho.matrix.trace.re)
    (hclassical : rho.classicalOnXY) :
    ∃ tau : SubnormalizedState ((a × x) × (y × b)),
      rho.purifiedBall ε tau ∧ tau.classicalOnXY ∧
        rho.smoothConditionalMaxEntropy ε hε0 hε =
          tau.conditionalMaxEntropy := by
  have hrho : 0 < rho.matrix.trace.re :=
    Real.sqrt_pos.mp (lt_of_le_of_lt hε0 hε)
  have hfull : Nonempty ((a × x) × (y × b)) :=
    nonempty_of_trace_pos rho.matrix hrho
  letI : Nonempty (a × x) := by
    rcases hfull with ⟨i⟩
    exact ⟨i.1⟩
  letI : Nonempty (y × b) := by
    rcases hfull with ⟨i⟩
    exact ⟨i.2⟩
  rcases rho.smoothConditionalMaxEntropy_exists_optimizer
      (a := a × x) hε0 hε with
    ⟨tau, hball, hmax, hoptimizer⟩
  have htau : 0 < tau.matrix.trace.re :=
    rho.purifiedBall_trace_pos_of_lt_sqrt_trace tau hε hball
  let tauP := classicalPinch tau
  have hballP : rho.purifiedBall ε tauP :=
    purifiedBall_classicalPinch_of_classical_center hclassical hball
  have hclassP : tauP.classicalOnXY := classicalPinch_classicalOnXY tau
  have hpinch : tau.conditionalMaxEntropy ≤ tauP.conditionalMaxEntropy :=
    conditionalMaxEntropy_le_classicalPinch_of_trace_pos tau htau
  refine ⟨tauP, hballP, hclassP, ?_⟩
  apply le_antisymm
  · calc
      rho.smoothConditionalMaxEntropy ε hε0 hε = tau.conditionalMaxEntropy := hmax
      _ ≤ tauP.conditionalMaxEntropy := hpinch
  · calc
      tauP.conditionalMaxEntropy ≤ tau.conditionalMaxEntropy :=
        hoptimizer tauP hballP
      _ = rho.smoothConditionalMaxEntropy ε hε0 hε := hmax.symm

-/

/-- The min and max smooth conditional entropies each have a classical
optimizer candidate for a center which is block diagonal on both classical
registers. -/
theorem smoothConditionalMinMaxEntropy_exists_classical_optimizers
    [Nonempty a] [Nonempty b]
    (rho : SubnormalizedState ((a × x) × (y × b))) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < Real.sqrt rho.matrix.trace.re)
    (hclassical : rho.classicalOnXY) :
    ∃ tauMin tauMax : SubnormalizedState ((a × x) × (y × b)),
      ∃ (htauMin : tauMin.matrix ≠ 0) (htauMax : tauMax.matrix ≠ 0),
      rho.purifiedBall ε tauMin ∧ tauMin.classicalOnXY ∧
      tauMin.conditionalMinEntropyFinite htauMin =
            rho.smoothConditionalMinEntropy ε hε0 hε ∧
      rho.purifiedBall ε tauMax ∧ tauMax.classicalOnXY ∧
          rho.smoothConditionalMaxEntropy ε hε0 hε =
            tauMax.conditionalMaxEntropyFinite htauMax := by
  rcases smoothConditionalMinEntropy_exists_classical_optimizer
      rho hε0 hε hclassical with
    ⟨tauMin, htauMin, hballMin, hclassicalMin, hmin⟩
  rcases smoothConditionalMaxEntropy_exists_classical_optimizer
      rho hε0 hε hclassical with
    ⟨tauMax, htauMax, hballMax, hclassicalMax, hmax⟩
  exact ⟨tauMin, tauMax, htauMin, htauMax, hballMin, hclassicalMin, hmin,
    hballMax, hclassicalMax, hmax⟩

end SubnormalizedState

end
end QIT
