/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.Smooth
public import QIT.OneShot.SmoothAttainment
public import QIT.States.Topology
public import QIT.Util.SDP.HermitianPSDTraceDuality
public import QIT.Util.SDP.StrongDuality
import QIT.Util.CMatrixCLM
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.MetricSpace.Sequences
public import QIT.Information.Entropy.Log2Lemmas

/-!
# CQ guessing probability and conditional min-entropy dual program

This module sets up the finite-dimensional cq state-discrimination primal and
matrix-order dual program used to prove the normalized cq min-entropy
characterization from [Tomamichel2015FiniteResources, calculus.tex:81-89] and
[Tomamichel2015FiniteResources, calculus.tex:348-357].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal
open scoped Topology
open scoped Matrix.Norms.L2Operator
open Set
open Filter

namespace QIT

universe u v

noncomputable section

namespace State

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Compact feasible pairs `(ρ', T_B)` for the normalized conditional-min scale
over a normalized purified-distance ball, with a harmless trace cap on `T_B`. -/
def conditionalMinEntropyScaleFeasiblePairSet
    (ρ : State (Prod a b)) (ε B : ℝ) :
    Set (State (Prod a b) × CMatrix b) :=
  ({ρ' : State (Prod a b) | ρ.purifiedBall ε ρ'} ×ˢ
      SubnormalizedState.psdTraceBoundedMatrixSet b B) ∩
    {p | p.1.matrix ≤ Matrix.kronecker (1 : CMatrix a) p.2}

/-- The matrix-order constraint in the normalized feasible-pair domain is
closed. -/
theorem conditionalMinEntropyScaleFeasiblePair_order_isClosed :
    IsClosed
      ({p : State (Prod a b) × CMatrix b |
        p.1.matrix ≤ Matrix.kronecker (1 : CMatrix a) p.2}) := by
  let f : State (Prod a b) × CMatrix b → CMatrix (Prod a b) :=
    fun p => Matrix.kronecker (1 : CMatrix a) p.2 - p.1.matrix
  have hf : Continuous f := by
    exact ((SubnormalizedState.continuous_kronecker_one_matrix (a := a) (b := b)).comp
        continuous_snd).sub
      (State.continuous_matrix.comp continuous_fst)
  have hset :
      {p : State (Prod a b) × CMatrix b |
        p.1.matrix ≤ Matrix.kronecker (1 : CMatrix a) p.2} =
      {p | f p ∈ ({M : CMatrix (Prod a b) | M.PosSemidef} : Set (CMatrix (Prod a b)))} := by
    ext p
    simp [f, Matrix.le_iff]
  rw [hset]
  exact (psdCone (Prod a b)).isClosed.preimage hf

/-- The normalized feasible-pair domain for the conditional-min scale is
compact. -/
theorem conditionalMinEntropyScaleFeasiblePairSet_isCompact
    (ρ : State (Prod a b)) (ε B : ℝ) :
    IsCompact (conditionalMinEntropyScaleFeasiblePairSet (a := a) (b := b) ρ ε B) := by
  let ball : Set (State (Prod a b)) := {ρ' | ρ.purifiedBall ε ρ'}
  let tset : Set (CMatrix b) := SubnormalizedState.psdTraceBoundedMatrixSet b B
  have hball : IsCompact ball := by
    simpa [ball] using State.purifiedBall_isCompact (a := Prod a b) ρ ε
  have htset : IsCompact tset := by
    simpa [tset] using SubnormalizedState.psdTraceBoundedMatrixSet_isCompact (b := b) (R := B)
  have hbase : IsCompact (ball ×ˢ tset) := hball.prod htset
  have hclosed := conditionalMinEntropyScaleFeasiblePair_order_isClosed (a := a) (b := b)
  simpa [conditionalMinEntropyScaleFeasiblePairSet, ball, tset] using
    hbase.inter_right hclosed

/-- Normalized-candidate smooth conditional min-entropy attains its maximum on
every nonempty normalized purified-distance ball. -/
theorem smoothConditionalMinEntropyNormalizedCandidates_exists_optimizer
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) {ε : ℝ} (hε_nonneg : 0 ≤ ε) :
    ∃ ρmin : State (Prod a b),
      ρ.purifiedBall ε ρmin ∧
        ρ.smoothConditionalMinEntropyNormalizedCandidates ε =
          ρmin.conditionalMinEntropy ∧
          ∀ ρ' : State (Prod a b),
            ρ.purifiedBall ε ρ' →
              ρ'.conditionalMinEntropy ≤ ρmin.conditionalMinEntropy := by
  let B : ℝ := Fintype.card b
  let feasibleSet :=
    conditionalMinEntropyScaleFeasiblePairSet (a := a) (b := b) ρ ε B
  have hcompact : IsCompact feasibleSet := by
    dsimp [feasibleSet]
    exact conditionalMinEntropyScaleFeasiblePairSet_isCompact
      (a := a) (b := b) ρ ε B
  have hnonempty : feasibleSet.Nonempty := by
    refine ⟨(ρ, (1 : CMatrix b)), ?_⟩
    dsimp [feasibleSet, conditionalMinEntropyScaleFeasiblePairSet, B,
      SubnormalizedState.psdTraceBoundedMatrixSet]
    constructor
    · constructor
      · exact ρ.purifiedBall_self_of_nonneg hε_nonneg
      · constructor
        · exact Matrix.PosSemidef.one
        · rw [Matrix.trace_one]
          norm_num
    · simpa [Matrix.one_kronecker_one] using ρ.matrix_le_one
  let traceFun : State (Prod a b) × CMatrix b → ℝ := fun p => p.2.trace.re
  have htraceFun_cont : Continuous traceFun := by
    exact Complex.continuous_re.comp (Continuous.matrix_trace continuous_snd)
  obtain ⟨pmin, hpmin, hpmin_min⟩ :=
    LowerSemicontinuousOn.exists_isMinOn hnonempty hcompact
      (htraceFun_cont.lowerSemicontinuous.lowerSemicontinuousOn feasibleSet)
  let ρmin : State (Prod a b) := pmin.1
  let Tmin : CMatrix b := pmin.2
  rcases hpmin with ⟨⟨hρmin_ball, hTmin_set⟩, hρmin_le_Tmin⟩
  have hTmin_feas :
      ConditionalMinEntropyScaleFeasible (a := a) ρmin Tmin :=
    ⟨hTmin_set.1, hρmin_le_Tmin⟩
  have hTmin_trace_pos : 0 < Tmin.trace.re := by
    have hscale_lb :
        (Fintype.card a : ℝ)⁻¹ ≤ Tmin.trace.re :=
      conditionalMinEntropyScaleFeasible_trace_lower_bound (a := a) hTmin_feas
    have hcard_a_pos : 0 < (Fintype.card a : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    exact lt_of_lt_of_le (inv_pos.mpr hcard_a_pos) hscale_lb
  have hmin_le_trace_of_feasible :
      ∀ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' →
        ∀ T : CMatrix b,
          ConditionalMinEntropyScaleFeasible (a := a) ρ' T →
            Tmin.trace.re ≤ T.trace.re := by
    intro ρ' hball T hT
    by_cases hTcap : T.trace.re ≤ B
    · have hp : (ρ', T) ∈ feasibleSet := by
        dsimp [feasibleSet, conditionalMinEntropyScaleFeasiblePairSet,
          SubnormalizedState.psdTraceBoundedMatrixSet]
        exact ⟨⟨hball, hT.1, hTcap⟩, hT.2⟩
      simpa [traceFun, Tmin] using hpmin_min hp
    · have hB_lt : B < T.trace.re := lt_of_not_ge hTcap
      exact hTmin_set.2.trans (le_of_lt hB_lt)
  have hscale_ge_Tmin :
      ∀ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' →
        Tmin.trace.re ≤ ρ'.conditionalMinEntropyScale (a := a) := by
    intro ρ' hball
    rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
    refine le_csInf (ρ'.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
    intro t ht
    rcases ht with ⟨T, hT, rfl⟩
    exact hmin_le_trace_of_feasible ρ' hball T hT
  have hscale_ρmin_le_Tmin :
      ρmin.conditionalMinEntropyScale (a := a) ≤ Tmin.trace.re := by
    rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
    exact csInf_le (by
      rw [ρmin.conditionalMinEntropyScaleValueSet_eq_normalizedScaleValueSet (a := a)]
      exact ρmin.conditionalMinEntropyNormalizedScaleValueSet_bddBelow (a := a))
      ⟨Tmin, hTmin_feas, rfl⟩
  have hscale_ρmin_eq_Tmin :
      ρmin.conditionalMinEntropyScale (a := a) = Tmin.trace.re :=
    le_antisymm hscale_ρmin_le_Tmin (hscale_ge_Tmin ρmin hρmin_ball)
  have hoptimizer :
      ∀ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' →
        ρ'.conditionalMinEntropy ≤ ρmin.conditionalMinEntropy := by
    intro ρ' hball
    have hscale_ge := hscale_ge_Tmin ρ' hball
    rw [ρ'.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a),
      ρmin.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a),
      hscale_ρmin_eq_Tmin]
    exact neg_log2_antitone_of_pos hTmin_trace_pos hscale_ge
  refine ⟨ρmin, hρmin_ball, ?_, hoptimizer⟩
  rw [smoothConditionalMinEntropyNormalizedCandidates_eq_sSup_candidates]
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · exact ⟨ρ.conditionalMinEntropy, ρ,
        ρ.purifiedBall_self_of_nonneg hε_nonneg, rfl⟩
    · intro h hh
      rcases hh with ⟨ρ', hρ'_ball, rfl⟩
      exact hoptimizer ρ' hρ'_ball
  · refine le_csSup ?_ ⟨ρmin, hρmin_ball, rfl⟩
    refine ⟨log2 (Fintype.card a : ℝ), ?_⟩
    intro h hh
    rcases hh with ⟨ρ', _hρ'_ball, rfl⟩
    exact ρ'.conditionalMinEntropy_le_log2_card_left (a := a) (b := b)

end State

namespace Ensemble

variable {ι : Type u} {b : Type v}
variable [Fintype ι] [DecidableEq ι] [Fintype b] [DecidableEq b]

local instance cMatrixNormedSpaceReal : NormedSpace ℝ (CMatrix b) :=
  inferInstance

noncomputable local instance cMatrixCStarAlgebra : CStarAlgebra (CMatrix b) := {}

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid NormedSpace.toModule
attribute [local instance 1001] PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

/-! ## Primal and dual optimization surfaces -/

/-- The weighted quantum block `p_x rho_x` appearing in a cq ensemble. -/
def cqBlock (E : Ensemble ι b) (x : ι) : CMatrix b :=
  (E.probs x : ℂ) • (E.states x).matrix

omit [DecidableEq ι] in
@[simp]
theorem cqBlock_eq (E : Ensemble ι b) (x : ι) :
    E.cqBlock x = (E.probs x : ℂ) • (E.states x).matrix :=
  rfl

/-- The real-valued primal score of a POVM for cq guessing. -/
def cqPrimalValue (E : Ensemble ι b) (M : POVM ι b) : ℝ :=
  ((E.cqGuessingScore M : ℝ≥0) : ℝ)

@[simp]
theorem cqPrimalValue_eq (E : Ensemble ι b) (M : POVM ι b) :
    E.cqPrimalValue M = ((E.cqGuessingScore M : ℝ≥0) : ℝ) :=
  rfl

/-- The trace-form primal score of a POVM. This is the expression used by
matrix-order duality. -/
def cqPrimalTraceValue (E : Ensemble ι b) (M : POVM ι b) : ℝ :=
  ∑ x, ((E.cqBlock x * M.effects x).trace).re

omit [DecidableEq ι] in
@[simp]
theorem cqPrimalTraceValue_eq (E : Ensemble ι b) (M : POVM ι b) :
    E.cqPrimalTraceValue M = ∑ x, ((E.cqBlock x * M.effects x).trace).re :=
  rfl

/-- The probability-style cq guessing score agrees with its trace form. -/
theorem cqPrimalValue_eq_traceValue (E : Ensemble ι b) (M : POVM ι b) :
    E.cqPrimalValue M = E.cqPrimalTraceValue M := by
  classical
  simp only [cqPrimalValue, cqGuessingScore_eq, cqPrimalTraceValue, cqBlock,
    NNReal.coe_sum, NNReal.coe_mul, POVM.prob_eq_trace_re]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Matrix.trace_smul]

/-- The set of attainable cq guessing scores. -/
def cqPrimalValueSet (E : Ensemble ι b) : Set ℝ :=
  {score : ℝ | ∃ M : POVM ι b, score = E.cqPrimalValue M}

@[simp]
theorem cqPrimalValueSet_eq (E : Ensemble ι b) :
    E.cqPrimalValueSet = {score : ℝ | ∃ M : POVM ι b, score = E.cqPrimalValue M} :=
  rfl

/-- The guessing probability is the supremum of the primal value set. -/
theorem cqGuessingProbability_eq_sSup_primalValueSet (E : Ensemble ι b) :
    E.cqGuessingProbability = sSup E.cqPrimalValueSet :=
  rfl

/-- Dual feasibility for cq discrimination: find a positive semidefinite matrix
dominating every weighted ensemble block. -/
def cqDualFeasible (E : Ensemble ι b) (T : CMatrix b) : Prop :=
  T.PosSemidef ∧ ∀ x, E.cqBlock x ≤ T

omit [DecidableEq ι] in
@[simp]
theorem cqDualFeasible_eq (E : Ensemble ι b) (T : CMatrix b) :
    E.cqDualFeasible T ↔ T.PosSemidef ∧ ∀ x, E.cqBlock x ≤ T :=
  Iff.rfl

/-- The dual objective `Tr T`, read as a real number for Hermitian/psd `T`. -/
def cqDualValue (_E : Ensemble ι b) (T : CMatrix b) : ℝ :=
  T.trace.re

omit [DecidableEq ι] in
@[simp]
theorem cqDualValue_eq (E : Ensemble ι b) (T : CMatrix b) :
    E.cqDualValue T = T.trace.re :=
  rfl

/-- The set of objective values attained by dual-feasible matrices. -/
def cqDualValueSet (E : Ensemble ι b) : Set ℝ :=
  {value : ℝ | ∃ T : CMatrix b, E.cqDualFeasible T ∧ value = E.cqDualValue T}

omit [DecidableEq ι] in
@[simp]
theorem cqDualValueSet_eq (E : Ensemble ι b) :
    E.cqDualValueSet =
      {value : ℝ | ∃ T : CMatrix b, E.cqDualFeasible T ∧ value = E.cqDualValue T} :=
  rfl

/-- The dual optimum as an infimum over feasible matrix traces. -/
def cqDualOptimalValue (E : Ensemble ι b) : ℝ :=
  sInf E.cqDualValueSet

omit [DecidableEq ι] in
@[simp]
theorem cqDualOptimalValue_eq (E : Ensemble ι b) :
    E.cqDualOptimalValue = sInf E.cqDualValueSet :=
  rfl

omit [DecidableEq ι] in
/-- A normalized finite ensemble has at least one classical label. -/
theorem index_nonempty (E : Ensemble ι b) : Nonempty ι := by
  by_contra hne
  haveI : IsEmpty ι := not_nonempty_iff.mp hne
  have hsum : (∑ i, E.probs i) = 0 := by simp
  have hzero : (0 : ℝ≥0) = 1 := by
    simpa [hsum] using E.weights_sum
  exact zero_ne_one hzero

/--
A cq-restricted smooth conditional min-entropy candidate for an ensemble.

The witness is another ensemble on the same classical and side-information
systems, so the nearby smooth state is manifestly cq.
-/
def CqSmoothConditionalMinEntropyCandidate (E : Ensemble ι b) (ε h : ℝ) : Prop :=
  ∃ E' : Ensemble ι b, E.cqState.purifiedBall ε E'.cqState ∧
    h ≤ E'.cqState.conditionalMinEntropy

@[simp]
theorem CqSmoothConditionalMinEntropyCandidate_eq
    (E : Ensemble ι b) (ε h : ℝ) :
    E.CqSmoothConditionalMinEntropyCandidate ε h ↔
      ∃ E' : Ensemble ι b, E.cqState.purifiedBall ε E'.cqState ∧
        h ≤ E'.cqState.conditionalMinEntropy :=
  Iff.rfl

end Ensemble

namespace State

variable {ι : Type u} {b : Type v}
variable [Fintype ι] [DecidableEq ι] [Fintype b] [DecidableEq b] [Nonempty b]

/-- Repackage the source-coordinate pinching of a normalized bipartite state as
a normalized cq ensemble. Zero-trace source blocks get an arbitrary normalized
side state because their probability weight is zero. -/
def sourceCoordinatePinchEnsemble (ρ : State (Prod ι b)) : Ensemble ι b where
  probs := fun x => Real.toNNReal (Classical.block ρ.matrix x x).trace.re
  weights_sum := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sum]
    have hblock_nonneg :
        ∀ x, 0 ≤ (Classical.block ρ.matrix x x).trace.re := by
      intro x
      have htrace_nonneg : 0 ≤ (Classical.block ρ.matrix x x).trace :=
        Matrix.PosSemidef.trace_nonneg
          (by simpa [Classical.block] using ρ.pos.submatrix (fun i : b => (x, i)))
      exact htrace_nonneg.1
    have hsum :=
      congrArg Complex.re (Classical.sum_block_trace (ι := ι) (a := b) ρ.matrix)
    rw [ρ.trace_eq_one] at hsum
    calc
      (∑ x, ↑(Real.toNNReal (Classical.block ρ.matrix x x).trace.re) : ℝ) =
          ∑ x, (Classical.block ρ.matrix x x).trace.re := by
            refine Finset.sum_congr rfl fun x _ => ?_
            exact Real.coe_toNNReal _ (hblock_nonneg x)
      _ = 1 := by simpa using hsum
  states := fun x =>
    if hx : (Classical.block ρ.matrix x x).trace.re = 0 then
      State.maximallyMixed b
    else
      State.normalizePSD (Classical.block ρ.matrix x x)
        (by simpa [Classical.block] using ρ.pos.submatrix (fun i : b => (x, i))) hx

private theorem sourceCoordinatePinchEnsemble_weightedBlock
    (ρ : State (Prod ι b)) (x : ι) :
    ((ρ.sourceCoordinatePinchEnsemble.probs x : ℂ) •
        (ρ.sourceCoordinatePinchEnsemble.states x).matrix) =
      Classical.block ρ.matrix x x := by
    classical
    let B : CMatrix b := Classical.block ρ.matrix x x
    have hBpos : B.PosSemidef := by
      simpa [B, Classical.block] using ρ.pos.submatrix (fun i : b => (x, i))
    have hBtrace_nonneg : 0 ≤ B.trace :=
      Matrix.PosSemidef.trace_nonneg hBpos
    have hBtr_nonneg : 0 ≤ B.trace.re :=
      hBtrace_nonneg.1
    by_cases hzero : B.trace.re = 0
    · have hBtrace : B.trace = 0 := by
        apply Complex.ext
        · exact hzero
        · exact hBtrace_nonneg.2.symm
      have hBzero : B = 0 :=
        (Matrix.PosSemidef.trace_eq_zero_iff hBpos).mp hBtrace
      simp [State.sourceCoordinatePinchEnsemble, B, hBzero]
    · have hprob :
          ((Real.toNNReal B.trace.re : ℝ≥0) : ℂ) = (B.trace.re : ℂ) := by
        norm_num [Real.coe_toNNReal _ hBtr_nonneg]
      have hreal : B.trace.re * (B.trace.re)⁻¹ = 1 :=
        mul_inv_cancel₀ hzero
      have hcomplex : (B.trace.re : ℂ) * (((B.trace.re)⁻¹ : ℝ) : ℂ) = 1 := by
        exact_mod_cast hreal
      have hblock_ne : (Classical.block ρ.matrix x x).trace.re ≠ 0 := by
        simpa [B] using hzero
      simp only [State.sourceCoordinatePinchEnsemble, hblock_ne, dite_false,
        State.normalizePSD_matrix]
      change ((Real.toNNReal B.trace.re : ℝ≥0) : ℂ) • (((B.trace.re)⁻¹ : ℝ) • B) = B
      rw [hprob]
      ext i j
      simp only [Matrix.smul_apply]
      change (B.trace.re : ℂ) * ((((B.trace.re)⁻¹ : ℝ) : ℂ) * B i j) = B i j
      rw [← mul_assoc, hcomplex, one_mul]

/-- The cq state reconstructed from the source-coordinate-pinched ensemble is
exactly the source-coordinate pinching of the original normalized state, after
embedding both as subnormalized states. -/
theorem sourceCoordinatePinchEnsemble_cqState_toSubnormalized
    (ρ : State (Prod ι b)) :
    ρ.sourceCoordinatePinchEnsemble.cqState.toSubnormalized =
      ρ.toSubnormalized.sourceCoordinatePinch := by
  classical
  apply SubnormalizedState.ext
  rw [State.toSubnormalized_matrix,
    SubnormalizedState.sourceCoordinatePinch_matrix_eq_blockDiagonal,
    Classical.cqState_eq_blockDiagonal]
  apply congrArg Classical.blockDiagonal
  funext x
  simpa [State.toSubnormalized_matrix] using
    sourceCoordinatePinchEnsemble_weightedBlock (ρ := ρ) x

end State

namespace Ensemble

variable {ι : Type u} {b : Type v}
variable [Fintype ι] [DecidableEq ι] [Fintype b] [DecidableEq b]

local instance cMatrixNormedSpaceRealReopened : NormedSpace ℝ (CMatrix b) :=
  inferInstance

noncomputable local instance cMatrixCStarAlgebraReopened : CStarAlgebra (CMatrix b) := {}

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid NormedSpace.toModule
attribute [local instance 1001] PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

/-- A normalized cq state is already diagonal in the source coordinate, hence
source-coordinate pinching fixes its subnormalized embedding. -/
theorem cqState_toSubnormalized_sourceCoordinatePinch
    (E : Ensemble ι b) :
    E.cqState.toSubnormalized.sourceCoordinatePinch =
      E.cqState.toSubnormalized := by
  apply SubnormalizedState.ext
  rw [SubnormalizedState.sourceCoordinatePinch_matrix, State.toSubnormalized_matrix]
  change (SubnormalizedState.sourceCoordinatePinchChannel (a := ι) (b := b)).map
      E.cqState.matrix =
    E.cqState.matrix
  rw [Ensemble.cqState_matrix]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  change (SubnormalizedState.sourceCoordinatePinchChannel (a := ι) (b := b)).map
      ((E.probs z : ℂ) •
        Matrix.kronecker (Matrix.single z z (1 : ℂ)) (E.states z).matrix) =
    (E.probs z : ℂ) •
      Matrix.kronecker (Matrix.single z z (1 : ℂ)) (E.states z).matrix
  rw [map_smul]
  rw [SubnormalizedState.sourceCoordinatePinchChannel_map_singleTensor]

omit [DecidableEq ι] in
theorem CqSmoothConditionalMinEntropyCandidate_of_smoothConditionalMinEntropyNormalizedCandidates
    [DecidableEq ι] (E : Ensemble ι b) {ε : ℝ} (hε_nonneg : 0 ≤ ε) :
    E.CqSmoothConditionalMinEntropyCandidate ε
      (E.cqState.smoothConditionalMinEntropyNormalizedCandidates ε) := by
  classical
  haveI : Nonempty ι := E.index_nonempty
  have hprod : Nonempty (Prod ι b) := E.cqState.nonempty
  haveI : Nonempty b := ⟨(Classical.choice hprod).2⟩
  rcases E.cqState.smoothConditionalMinEntropyNormalizedCandidates_exists_optimizer
      (a := ι) (b := b) hε_nonneg with
    ⟨ρmin, hρmin_ball, hsmooth, _hopt⟩
  let E' : Ensemble ι b := ρmin.sourceCoordinatePinchEnsemble
  have hball_sub :
      E.cqState.toSubnormalized.purifiedBall ε ρmin.toSubnormalized :=
    (State.purifiedBall_iff_toSubnormalized_purifiedBall E.cqState ρmin ε).mp
      hρmin_ball
  have hball_pinch :
      E.cqState.toSubnormalized.purifiedBall ε ρmin.toSubnormalized.sourceCoordinatePinch := by
    exact E.cqState.toSubnormalized.purifiedBall_sourceCoordinatePinch_of_fixed
      (E.cqState_toSubnormalized_sourceCoordinatePinch) hball_sub
  have hE'_sub :
      E'.cqState.toSubnormalized = ρmin.toSubnormalized.sourceCoordinatePinch := by
    simpa [E'] using ρmin.sourceCoordinatePinchEnsemble_cqState_toSubnormalized
  have hball_state : E.cqState.purifiedBall ε E'.cqState := by
    rw [State.purifiedBall_iff_toSubnormalized_purifiedBall]
    simpa [hE'_sub] using hball_pinch
  have hρmin_trace_pos : 0 < ρmin.toSubnormalized.matrix.trace.re := by
    rw [State.toSubnormalized_trace]
    norm_num
  have hpinch_entropy :
      ρmin.toSubnormalized.conditionalMinEntropyRaw ≤
        ρmin.toSubnormalized.sourceCoordinatePinch.conditionalMinEntropyRaw :=
    ρmin.toSubnormalized.conditionalMinEntropy_le_sourceCoordinatePinch_of_trace_pos
      (a := ι) hρmin_trace_pos
  have hρmin_entropy :
      ρmin.toSubnormalized.conditionalMinEntropyRaw = ρmin.conditionalMinEntropy := by
    rw [State.toSubnormalized_conditionalMinEntropyRaw_eq]
  have hE'_entropy :
      ρmin.toSubnormalized.sourceCoordinatePinch.conditionalMinEntropyRaw =
        E'.cqState.conditionalMinEntropy := by
    have hsub :=
      State.toSubnormalized_conditionalMinEntropyRaw_eq (a := ι) (b := b)
        (ρ := E'.cqState)
    rw [hE'_sub] at hsub
    exact hsub
  refine ⟨E', hball_state, ?_⟩
  calc
    E.cqState.smoothConditionalMinEntropyNormalizedCandidates ε =
        ρmin.conditionalMinEntropy := hsmooth
    _ = ρmin.toSubnormalized.conditionalMinEntropyRaw := hρmin_entropy.symm
    _ ≤ ρmin.toSubnormalized.sourceCoordinatePinch.conditionalMinEntropyRaw := hpinch_entropy
    _ = E'.cqState.conditionalMinEntropy := hE'_entropy

/-! ## cq SDP embedding -/

/-- Raw families of cq guessing effects, before imposing positivity and the
POVM normalization constraint.  This wrapper avoids instance diamonds between
plain Pi-space and normed Pi-space instances when instantiating conic duality. -/
structure CQEffectFamily (ι : Type u) (b : Type v) [Fintype b] [DecidableEq b] where
  val : ι → CMatrix b

namespace CQEffectFamily

instance : CoeFun (CQEffectFamily ι b) (fun _ => ι → CMatrix b) :=
  ⟨CQEffectFamily.val⟩

omit [Fintype ι] [DecidableEq ι] in
@[ext]
theorem ext {M N : CQEffectFamily ι b} (h : ∀ x, M x = N x) : M = N := by
  cases M with
  | mk M =>
  cases N with
  | mk N =>
  simp only at h
  congr
  exact funext h

instance : Zero (CQEffectFamily ι b) := ⟨⟨0⟩⟩

instance : Add (CQEffectFamily ι b) :=
  ⟨fun M N => ⟨fun x => M x + N x⟩⟩

instance : Neg (CQEffectFamily ι b) :=
  ⟨fun M => ⟨fun x => -M x⟩⟩

instance : Sub (CQEffectFamily ι b) :=
  ⟨fun M N => ⟨fun x => M x - N x⟩⟩

instance : SMul ℕ (CQEffectFamily ι b) :=
  ⟨fun k M => ⟨fun x => k • M x⟩⟩

instance : SMul ℤ (CQEffectFamily ι b) :=
  ⟨fun k M => ⟨fun x => k • M x⟩⟩

instance : SMul ℝ (CQEffectFamily ι b) :=
  ⟨fun c M => ⟨fun x => c • M x⟩⟩

instance : SMul NNReal (CQEffectFamily ι b) :=
  ⟨fun c M => ⟨fun x => c • M x⟩⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem val_zero : (0 : CQEffectFamily ι b).val = 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem val_add (M N : CQEffectFamily ι b) : (M + N).val = M.val + N.val := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem val_neg (M : CQEffectFamily ι b) : (-M).val = -M.val := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem val_sub (M N : CQEffectFamily ι b) : (M - N).val = M.val - N.val := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem val_nsmul (k : ℕ) (M : CQEffectFamily ι b) : (k • M).val = k • M.val := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem val_zsmul (k : ℤ) (M : CQEffectFamily ι b) : (k • M).val = k • M.val := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem val_smul (c : ℝ) (M : CQEffectFamily ι b) : (c • M).val = c • M.val := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem val_nnreal_smul (c : ℝ≥0) (M : CQEffectFamily ι b) :
    (c • M).val = c • M.val := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem val_zero_apply (x : ι) : (0 : CQEffectFamily ι b) x = 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem val_add_apply (M N : CQEffectFamily ι b) (x : ι) : (M + N) x = M x + N x := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem val_neg_apply (M : CQEffectFamily ι b) (x : ι) : (-M) x = -M x := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem val_sub_apply (M N : CQEffectFamily ι b) (x : ι) : (M - N) x = M x - N x := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem val_nsmul_apply (k : ℕ) (M : CQEffectFamily ι b) (x : ι) :
    (k • M) x = k • M x := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem val_zsmul_apply (k : ℤ) (M : CQEffectFamily ι b) (x : ι) :
    (k • M) x = k • M x := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem val_smul_apply (c : ℝ) (M : CQEffectFamily ι b) (x : ι) :
    (c • M) x = c • M x := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem val_nnreal_smul_apply (c : ℝ≥0) (M : CQEffectFamily ι b) (x : ι) :
    (c • M) x = c • M x := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem val_injective : Function.Injective (fun M : CQEffectFamily ι b => M.val) :=
  fun _ _ h => ext (congrFun h)

instance (priority := 50) : AddCommGroup (CQEffectFamily ι b) :=
  Function.Injective.addCommGroup (fun M : CQEffectFamily ι b => M.val) val_injective
    val_zero val_add val_neg val_sub (fun M k => val_nsmul k M) (fun M k => val_zsmul k M)

def toPiAddMonoidHom : CQEffectFamily ι b →+ (ι → CMatrix b) where
  toFun M := M.val
  map_zero' := rfl
  map_add' _ _ := rfl

instance (priority := 50) : Module ℝ (CQEffectFamily ι b) :=
  Function.Injective.module ℝ (toPiAddMonoidHom : CQEffectFamily ι b →+ (ι → CMatrix b))
    val_injective
    (by intro _ _; rfl)

def toPiLinear : CQEffectFamily ι b →ₗ[ℝ] (ι → CMatrix b) where
  toFun M := M.val
  map_add' _ _ := rfl
  map_smul' c M := by
    ext x
    simp

omit [DecidableEq ι] in
theorem toPiLinear_injective :
    Function.Injective (toPiLinear : CQEffectFamily ι b →ₗ[ℝ] (ι → CMatrix b)) :=
  val_injective

local instance piCMatrixNormedAddCommGroup : NormedAddCommGroup (ι → CMatrix b) :=
  Pi.normedAddCommGroup

local instance piCMatrixNormedSpaceReal : NormedSpace ℝ (ι → CMatrix b) :=
  Pi.normedSpace

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (CQEffectFamily ι b) :=
  { NormedAddCommGroup.induced (CQEffectFamily ι b) (ι → CMatrix b)
      (toPiAddMonoidHom : CQEffectFamily ι b →+ (ι → CMatrix b)) val_injective with
    toAddCommGroup := inferInstance }

noncomputable instance instNormedSpaceReal : NormedSpace ℝ (CQEffectFamily ι b) :=
  { NormedSpace.induced ℝ (CQEffectFamily ι b) (ι → CMatrix b)
      (toPiLinear : CQEffectFamily ι b →ₗ[ℝ] (ι → CMatrix b)) with
    toModule := inferInstance }

noncomputable instance instFiniteDimensionalReal : FiniteDimensional ℝ (CQEffectFamily ι b) :=
  FiniteDimensional.of_injective
    (toPiLinear : CQEffectFamily ι b →ₗ[ℝ] (ι → CMatrix b)) toPiLinear_injective

noncomputable def toPiCLM : CQEffectFamily ι b →L[ℝ] (ι → CMatrix b) :=
  LinearMap.toContinuousLinearMap
    (toPiLinear : CQEffectFamily ι b →ₗ[ℝ] (ι → CMatrix b))

noncomputable def evalCLM (x : ι) : CQEffectFamily ι b →L[ℝ] CMatrix b :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun M => M x
       map_add' := by
        intro M N
        rfl
       map_smul' c M := by
        simp } :
      CQEffectFamily ι b →ₗ[ℝ] CMatrix b)

omit [DecidableEq ι] in
@[simp]
theorem evalCLM_apply (x : ι) (M : CQEffectFamily ι b) :
    evalCLM x M = M x :=
  by
    simp [evalCLM]

/-- The raw effect family supported at one classical label. -/
def single (x : ι) (A : CMatrix b) : CQEffectFamily ι b :=
  ⟨fun y => if y = x then A else 0⟩

omit [Fintype ι] in
@[simp]
theorem single_apply_same (x : ι) (A : CMatrix b) :
    single (ι := ι) (b := b) x A x = A := by
  simp [single]

omit [Fintype ι] in
@[simp]
theorem single_apply_ne {x y : ι} (h : y ≠ x) (A : CMatrix b) :
    single (ι := ι) (b := b) x A y = 0 := by
  simp [single, h]

@[simp]
theorem sum_single (x : ι) (A : CMatrix b) :
    (∑ y, single (ι := ι) (b := b) x A y) = A := by
  classical
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [single, hy]
  · intro hx
    simp at hx

end CQEffectFamily

private noncomputable def hermitianInclusionNormed : HermitianMatrix b →L[ℝ] CMatrix b :=
  LinearMap.toContinuousLinearMap
    (HermitianMatrix.toCMatrixLinear : HermitianMatrix b →ₗ[ℝ] CMatrix b)

private theorem isClosed_setOf_zero_le_complex' : IsClosed ({z : ℂ | 0 ≤ z} : Set ℂ) := by
  have h : ({z : ℂ | 0 ≤ z} : Set ℂ) = {z | 0 ≤ z.re} ∩ {z | z.im = 0} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hz
      simp [Complex.le_def] at hz ⊢
      tauto
    · rintro ⟨hre, him⟩
      simp [Complex.le_def]
      exact ⟨hre, him.symm⟩
  rw [h]
  exact (isClosed_Ici.preimage Complex.continuous_re).inter
    (isClosed_singleton.preimage Complex.continuous_im)

private theorem continuous_quadraticForm_normed (x : b →₀ ℂ) :
    Continuous (fun A : CMatrix b =>
      (x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj)) := by
  classical
  simp only [Finsupp.sum, Finsupp.sum]
  exact continuous_finsetSum x.support fun i _ =>
    continuous_finsetSum x.support fun j _ =>
      Continuous.mul (Continuous.mul continuous_const (cMatrixEntryCLM (ι := b) i j).continuous)
        continuous_const

private theorem isClosed_cMatrix_posSemidef_normed :
    IsClosed ({A : CMatrix b | A.PosSemidef} : Set (CMatrix b)) := by
  classical
  have h : ({A : CMatrix b | A.PosSemidef} : Set (CMatrix b)) =
      ({A | A.IsHermitian} ∩
        (⋂ x : b →₀ ℂ,
          {A : CMatrix b | 0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj})) := by
    ext A
    simp [Matrix.PosSemidef, Set.mem_iInter]
  rw [h]
  refine IsClosed.inter ?herm ?quad
  · have hH : ({A : CMatrix b | A.IsHermitian} : Set (CMatrix b)) =
        {A | Matrix.conjTranspose A = A} := by
      ext A
      simp [Matrix.IsHermitian]
    rw [hH]
    exact isClosed_eq (cMatrixConjTransposeCLM (ι := b)).continuous continuous_id
  · exact isClosed_iInter fun x =>
      isClosed_setOf_zero_le_complex'.preimage (continuous_quadraticForm_normed (b := b) x)

set_option maxHeartbeats 800000 in
private theorem cMatrix_norm_le_norm_of_posSemidef_le {A B : CMatrix b}
    (hA : A.PosSemidef) (hAB : A ≤ B) :
    ‖A‖ ≤ ‖B‖ := by
  have hA0 : (0 : CMatrix b) ≤ A := by
    simpa [Matrix.le_iff] using hA
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le
    (A := CMatrix b) (a := A) (b := B) hA0 hAB

/-- The product PSD cone for finite cq effect families. -/
def cqEffectFamilySubmodule : Submodule NNReal (CQEffectFamily ι b) where
  carrier := {M | ∀ x, (M x).PosSemidef}
  zero_mem' := fun _ => Matrix.PosSemidef.zero
  add_mem' := by
    intro M N hM hN x
    exact (hM x).add (hN x)
  smul_mem' := by
    intro c M hM x
    rw [CQEffectFamily.val_nnreal_smul_apply]
    rw [NNReal.smul_def]
    exact (hM x).smul (NNReal.coe_nonneg c)

/-- The product PSD cone for finite cq effect families as a closed proper cone. -/
def cqEffectFamilyCone : ProperCone ℝ (CQEffectFamily ι b) :=
  { cqEffectFamilySubmodule (ι := ι) (b := b) with
    isClosed' := by
      classical
      have h :
          ({M : CQEffectFamily ι b | ∀ x, (M x).PosSemidef} :
              Set (CQEffectFamily ι b)) =
            ⋂ x, {M : CQEffectFamily ι b | (M x).PosSemidef} := by
        ext M
        simp
      change IsClosed ({M : CQEffectFamily ι b | ∀ x, (M x).PosSemidef})
      rw [h]
      exact isClosed_iInter fun x =>
        by
          simpa [CQEffectFamily.evalCLM] using
            (isClosed_cMatrix_posSemidef_normed (b := b)).preimage
              ((CQEffectFamily.evalCLM (ι := ι) (b := b) x).continuous) }

omit [DecidableEq ι] in
theorem cqEffectFamilyCone_mem (M : CQEffectFamily ι b) :
    M ∈ cqEffectFamilyCone (ι := ι) (b := b) ↔ ∀ x, (M x).PosSemidef :=
  Iff.rfl

theorem CQEffectFamily.single_mem_cone {x : ι} {A : CMatrix b} (hA : A.PosSemidef) :
    CQEffectFamily.single (ι := ι) (b := b) x A ∈ cqEffectFamilyCone (ι := ι) (b := b) := by
  intro y
  by_cases hy : y = x
  · subst hy
    simp [CQEffectFamily.single, hA]
  · simp [CQEffectFamily.single, hy, Matrix.PosSemidef.zero]

/-- The effect-family equality-constraint map `M ↦ ∑ x, M_x`. -/
noncomputable def cqEffectFamilySumCLM :
    CQEffectFamily ι b →L[ℝ] CMatrix b :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun M => ∑ x, M x
       map_add' := by
        intro M N
        ext i j
        simp [Finset.sum_add_distrib]
       map_smul' := by
        intro c M
        change (∑ x, (c • M).val x) = c • ∑ x, M.val x
        rw [CQEffectFamily.val_smul]
        exact (Finset.smul_sum.symm : (∑ x, c • M.val x) = c • ∑ x, M.val x) } :
      CQEffectFamily ι b →ₗ[ℝ] CMatrix b)

/-- Real trace pairing against a fixed ambient complex matrix. -/
noncomputable def cMatrixTracePairingCLM (T : CMatrix b) :
    CMatrix b →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (LinearMap.toContinuousLinearMap
      ({ toFun := fun A => (T * A).trace
         map_add' := by
          intro A B
          simp [Matrix.mul_add, Matrix.trace_add]
         map_smul' := by
          intro c A
          simp [Matrix.trace_smul, Complex.real_smul] } :
        CMatrix b →ₗ[ℝ] ℂ))

@[simp]
theorem cMatrixTracePairingCLM_apply (T A : CMatrix b) :
    cMatrixTracePairingCLM T A = ((T * A).trace).re :=
  rfl

/-- The trace-form cq primal objective as a continuous real-linear map on raw
effect families. -/
noncomputable def cqPrimalObjectiveCLM (E : Ensemble ι b) :
    CQEffectFamily ι b →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun M => ∑ x, ((E.cqBlock x * M x).trace).re
       map_add' := by
        intro M N
        simp [Matrix.mul_add, Matrix.trace_add, Finset.sum_add_distrib]
       map_smul' := by
        intro c M
        simp [Matrix.trace_smul, Complex.real_smul, Finset.mul_sum] } :
      CQEffectFamily ι b →ₗ[ℝ] ℝ)

omit [DecidableEq ι] in
@[simp]
theorem cqPrimalObjectiveCLM_apply (E : Ensemble ι b) (M : CQEffectFamily ι b) :
    cqPrimalObjectiveCLM E M = ∑ x, ((E.cqBlock x * M x).trace).re :=
  by
    simp [cqPrimalObjectiveCLM]

/-- The finite-dimensional cq guessing primal SDP:
maximize the trace-form score over PSD effects summing to the identity. -/
noncomputable def cqPrimalProgram (E : Ensemble ι b) :
    QIT.SDP.ContinuousConeProgram (CQEffectFamily ι b) (CMatrix b) where
  K := cqEffectFamilyCone (ι := ι) (b := b)
  A := cqEffectFamilySumCLM (ι := ι) (b := b)
  b := 1
  c := cqPrimalObjectiveCLM E

/-- The conic primal value set is exactly the cq guessing value set. -/
theorem cqPrimalProgram_primalValueSet_eq (E : Ensemble ι b) :
    (cqPrimalProgram E).primalValueSet = E.cqPrimalValueSet := by
  classical
  ext value
  constructor
  · rintro ⟨M, hM, rfl⟩
    let povm : POVM ι b :=
      { effects := M.val
        pos := by
          intro x
          exact hM.1 x
        sum_eq_one := by
          simpa [cqPrimalProgram, cqEffectFamilySumCLM] using hM.2 }
    refine ⟨povm, ?_⟩
    rw [cqPrimalValue_eq_traceValue]
    simp [QIT.SDP.ContinuousConeProgram.primalValue, cqPrimalProgram,
      cqPrimalObjectiveCLM, cqPrimalTraceValue, povm]
  · rintro ⟨povm, rfl⟩
    let M : CQEffectFamily ι b := ⟨povm.effects⟩
    refine ⟨M, ?_, ?_⟩
    · constructor
      · intro x
        exact povm.pos x
      · simp [cqPrimalProgram, cqEffectFamilySumCLM, M]
    · rw [cqPrimalValue_eq_traceValue]
      simp [QIT.SDP.ContinuousConeProgram.primalValue, cqPrimalProgram,
        cqPrimalObjectiveCLM, cqPrimalTraceValue, M]

omit [DecidableEq ι] in
/-- Weighted cq blocks are positive semidefinite. -/
theorem cqBlock_posSemidef (E : Ensemble ι b) (x : ι) :
    (E.cqBlock x).PosSemidef := by
  rw [cqBlock]
  have hx : (0 : ℂ) ≤ (E.probs x : ℂ) := by
    rw [Complex.zero_le_real]
    exact NNReal.coe_nonneg (E.probs x)
  exact (E.states x).pos.smul hx

omit [DecidableEq ι] in
/-- The weighted cq block has trace equal to the corresponding probability. -/
theorem cqBlock_trace (E : Ensemble ι b) (x : ι) :
    (E.cqBlock x).trace = (E.probs x : ℂ) := by
  rw [cqBlock_eq, Matrix.trace_smul, (E.states x).trace_eq_one]
  simp

omit [DecidableEq ι] in
/-- Real trace of the weighted cq block. -/
theorem cqBlock_trace_re (E : Ensemble ι b) (x : ι) :
    (E.cqBlock x).trace.re = (E.probs x : ℝ) := by
  rw [cqBlock_trace]
  simp

/-- A weighted cq block has trace at most one. -/
theorem cqBlock_trace_re_le_one (E : Ensemble ι b) (x : ι) :
    (E.cqBlock x).trace.re ≤ 1 := by
  rw [cqBlock_trace_re]
  exact E.prob_le_one x

/--
The source-style subnormalized side-information block `ρ_B(x)` associated with
an ensemble label.

[Tomamichel2015FiniteResources, apps.tex:256-292]
-/
def cqSubnormalizedBlock (E : Ensemble ι b) (x : ι) : SubnormalizedState b where
  matrix := E.cqBlock x
  pos := E.cqBlock_posSemidef x
  trace_le_one := E.cqBlock_trace_re_le_one x

@[simp]
theorem cqSubnormalizedBlock_matrix (E : Ensemble ι b) (x : ι) :
    (E.cqSubnormalizedBlock x).matrix = E.cqBlock x :=
  rfl

@[simp]
theorem cqSubnormalizedBlock_trace_re (E : Ensemble ι b) (x : ι) :
    (E.cqSubnormalizedBlock x).matrix.trace.re = (E.probs x : ℝ) := by
  simpa using E.cqBlock_trace_re x

/-- The subnormalized cq block is the normalized member state scaled by its probability. -/
theorem cqSubnormalizedBlock_eq_ofStateScale (E : Ensemble ι b) (x : ι) :
    E.cqSubnormalizedBlock x =
      SubnormalizedState.ofStateScale (E.states x) (E.probs x : ℝ)
        (E.prob_nonneg x) (E.prob_le_one x) := by
  apply SubnormalizedState.ext
  rw [cqSubnormalizedBlock_matrix, SubnormalizedState.ofStateScale_matrix, cqBlock_eq]
  ext i j
  simp [Complex.real_smul]

/-- The probability weights of an ensemble define a valid trivial POVM. -/
noncomputable def probabilityPOVM (E : Ensemble ι b) : POVM ι b where
  effects := fun x => (E.probs x : ℂ) • (1 : CMatrix b)
  pos := by
    intro x
    have hx : (0 : ℂ) ≤ (E.probs x : ℂ) := by
      rw [Complex.zero_le_real]
      exact NNReal.coe_nonneg (E.probs x)
    exact Matrix.PosSemidef.one.smul hx
  sum_eq_one := by
    classical
    have hsum : (∑ x, (E.probs x : ℂ)) = 1 := by
      exact_mod_cast E.weights_sum
    calc
      (∑ x, (E.probs x : ℂ) • (1 : CMatrix b)) =
          (∑ x, (E.probs x : ℂ)) • (1 : CMatrix b) := by
            rw [Finset.sum_smul]
      _ = (1 : ℂ) • (1 : CMatrix b) := by
            rw [hsum]
      _ = 1 := by simp

namespace Classical

variable {ι : Type u} {b : Type v}
variable [Fintype ι] [DecidableEq ι] [Fintype b] [DecidableEq b]

omit [DecidableEq b] in
private theorem blockDiagonal_posSemidef (blocks : ι → CMatrix b)
    (hblocks : ∀ x, (blocks x).PosSemidef) :
    (Classical.blockDiagonal blocks).PosSemidef := by
  classical
  unfold Classical.blockDiagonal
  exact Matrix.posSemidef_sum Finset.univ fun x _ =>
    (posSemidef_single x).kronecker (hblocks x)

omit [Fintype b] [DecidableEq b] in
private theorem blockDiagonal_sub (blocks blocks' : ι → CMatrix b) :
    Classical.blockDiagonal (fun x => blocks x - blocks' x) =
      Classical.blockDiagonal blocks - Classical.blockDiagonal blocks' := by
  classical
  unfold Classical.blockDiagonal
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  ext xi xj
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
  ring

omit [Fintype b] [DecidableEq b] in
private theorem blockDiagonal_smul (c : ℂ) (blocks : ι → CMatrix b) :
    Classical.blockDiagonal (fun x => c • blocks x) =
      c • Classical.blockDiagonal blocks := by
  classical
  unfold Classical.blockDiagonal
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ext xi xj
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
  ring

end Classical

private theorem cqState_eq_blockDiagonal_cqBlock (E : Ensemble ι b) :
    E.cqState.matrix = Classical.blockDiagonal fun x => E.cqBlock x := by
  rw [Classical.cqState_eq_blockDiagonal]
  rfl

private theorem identityTensorStateMatrix_eq_blockDiagonal (σ : State b) :
    State.identityTensorStateMatrix (a := ι) σ =
      Classical.blockDiagonal fun _ : ι => σ.matrix := by
  classical
  ext xi xj
  rcases xi with ⟨x, i⟩
  rcases xj with ⟨x', j⟩
  by_cases hxx' : x = x'
  · subst hxx'
    have hblock :=
      congrFun (congrFun (Classical.blockDiagonal_block_self
        (fun _ : ι => σ.matrix) x) i) j
    simp only [Classical.block] at hblock
    simpa [State.identityTensorStateMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply]
      using hblock.symm
  · simp [Classical.blockDiagonal, State.identityTensorStateMatrix, Matrix.kronecker,
      Matrix.kroneckerMap_apply, hxx']
    have hblock :=
      congrFun (congrFun (Classical.blockDiagonal_block_ne
        (fun _ : ι => σ.matrix) hxx') i) j
    simp only [Classical.block] at hblock
    exact hblock.symm

/-- Weak duality for cq guessing: every dual-feasible matrix upper-bounds every
POVM guessing score. -/
theorem cqPrimalValue_le_dualValue (E : Ensemble ι b) (M : POVM ι b) {T : CMatrix b}
    (hT : E.cqDualFeasible T) :
    E.cqPrimalValue M ≤ E.cqDualValue T := by
  classical
  rw [cqPrimalValue_eq_traceValue]
  calc
    E.cqPrimalTraceValue M ≤ ∑ x, ((T * M.effects x).trace).re := by
      simp only [cqPrimalTraceValue]
      refine Finset.sum_le_sum fun x _ => ?_
      have hdiff : (T - E.cqBlock x).PosSemidef := by
        simpa [Matrix.le_iff] using hT.2 x
      have hnonneg := cMatrix_trace_mul_posSemidef_re_nonneg hdiff (M.pos x)
      have htrace :
          (((T - E.cqBlock x) * M.effects x).trace).re =
            ((T * M.effects x).trace).re -
              ((E.cqBlock x * M.effects x).trace).re := by
        simp [Matrix.sub_mul, Matrix.trace_sub]
      linarith
    _ = ((T * (∑ x, M.effects x)).trace).re := by
      rw [← Complex.re_sum]
      congr 1
      calc
        (∑ x, (T * M.effects x).trace) = (∑ x, T * M.effects x).trace := by
          rw [Matrix.trace_sum]
        _ = (T * (∑ x, M.effects x)).trace := by
          congr 1
          simpa using (Matrix.mul_sum Finset.univ M.effects T).symm
    _ = E.cqDualValue T := by
      rw [M.sum_eq_one]
      simp [cqDualValue]

omit [DecidableEq ι] in
/-- A matrix-feasible cq dual point induces a feasible conic dual functional. -/
theorem cqPrimalProgram_dualFeasible_of_cqDualFeasible
    (E : Ensemble ι b) {T : CMatrix b} (hT : E.cqDualFeasible T) :
    (cqPrimalProgram E).IsDualFeasible (cMatrixTracePairingCLM T) := by
  classical
  intro M hM
  calc
    (cqPrimalProgram E).primalValue M =
        ∑ x, ((E.cqBlock x * M x).trace).re := by
          simp [QIT.SDP.ContinuousConeProgram.primalValue, cqPrimalProgram,
            cqPrimalObjectiveCLM]
    _ ≤ ∑ x, ((T * M x).trace).re := by
      refine Finset.sum_le_sum fun x _ => ?_
      have hdiff : (T - E.cqBlock x).PosSemidef := by
        simpa [Matrix.le_iff] using hT.2 x
      have hnonneg := cMatrix_trace_mul_posSemidef_re_nonneg hdiff (hM x)
      have htrace :
          (((T - E.cqBlock x) * M x).trace).re =
            ((T * M x).trace).re - ((E.cqBlock x * M x).trace).re := by
        simp [Matrix.sub_mul, Matrix.trace_sub]
      linarith
    _ = ((T * (∑ x, M x)).trace).re := by
      rw [← Complex.re_sum]
      congr 1
      calc
        (∑ x, (T * M x).trace) = (∑ x, T * M x).trace := by
          rw [Matrix.trace_sum]
        _ = (T * (∑ x, M x)).trace := by
          congr 1
          simpa using (Matrix.mul_sum Finset.univ (fun x => M x) T).symm
    _ = cMatrixTracePairingCLM T ((cqPrimalProgram E).A M) := by
      rw [cMatrixTracePairingCLM_apply]
      have hA : (cqPrimalProgram E).A M = ∑ x, M x := by
        simp [cqPrimalProgram, cqEffectFamilySumCLM]
      rw [hA]

omit [DecidableEq ι] in
/-- Matrix dual values are conic dual values. -/
theorem cqDualValueSet_subset_cqPrimalProgram_dualValueSet (E : Ensemble ι b) :
    E.cqDualValueSet ⊆ (cqPrimalProgram E).dualValueSet := by
  rintro value ⟨T, hT, rfl⟩
  refine ⟨cMatrixTracePairingCLM T, cqPrimalProgram_dualFeasible_of_cqDualFeasible E hT, ?_⟩
  simp [QIT.SDP.ContinuousConeProgram.dualValue, cqPrimalProgram, cqDualValue,
    cMatrixTracePairingCLM]

/-- Testing a conic dual functional on a single label gives the pointwise
matrix-pairing lower bound. -/
theorem cqPrimalProgram_dualFeasible_single_le
    (E : Ensemble ι b) {y : CMatrix b →L[ℝ] ℝ}
    (hy : (cqPrimalProgram E).IsDualFeasible y) (x : ι)
    {A : CMatrix b} (hA : A.PosSemidef) :
    ((E.cqBlock x * A).trace).re ≤ y A := by
  have h := hy (CQEffectFamily.single (ι := ι) (b := b) x A)
    (CQEffectFamily.single_mem_cone (ι := ι) (b := b) hA)
  have hobj :
      (cqPrimalProgram E).primalValue (CQEffectFamily.single (ι := ι) (b := b) x A) =
        ((E.cqBlock x * A).trace).re := by
    simp only [QIT.SDP.ContinuousConeProgram.primalValue, cqPrimalProgram,
      cqPrimalObjectiveCLM_apply]
    rw [Finset.sum_eq_single x]
    · simp
    · intro y hy_ne hx_ne
      simp [CQEffectFamily.single, hx_ne]
    · intro hx_not_mem
      simp at hx_not_mem
  have hmap :
      (cqPrimalProgram E).A (CQEffectFamily.single (ι := ι) (b := b) x A) = A := by
    simp [cqPrimalProgram, cqEffectFamilySumCLM, CQEffectFamily.sum_single]
  simpa [hobj, hmap] using h

/-- Conic dual values are represented by matrix-order cq dual feasible points. -/
theorem cqPrimalProgram_dualValueSet_subset_cqDualValueSet (E : Ensemble ι b) :
    (cqPrimalProgram E).dualValueSet ⊆ E.cqDualValueSet := by
  classical
  letI : Nonempty ι := E.index_nonempty
  rintro value ⟨y, hy, rfl⟩
  let yH : HermitianDual b :=
    y.comp (hermitianInclusionNormed (b := b))
  rcases exists_hermitian_tracePairing_representation (n := b) yH with ⟨T, hTrep⟩
  have hrep_psd (A : CMatrix b) (hA : A.PosSemidef) :
      y A = ((T.val * A).trace).re := by
    let X : HermitianMatrix b := ⟨A, hA.1⟩
    have h := hTrep X
    simpa [yH, X, tracePairing] using h
  refine ⟨T.val, ?_, ?_⟩
  · constructor
    · refine (cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg T.isHermitian).2 ?_
      intro A hA
      let x0 : ι := Classical.choice (inferInstance : Nonempty ι)
      have hsingle := cqPrimalProgram_dualFeasible_single_le E hy x0 hA
      have hblock_nonneg :=
        cMatrix_trace_mul_posSemidef_re_nonneg (cqBlock_posSemidef E x0) hA
      have hrep := hrep_psd A hA
      linarith
    · intro x
      rw [Matrix.le_iff]
      have hHerm : (T.val - E.cqBlock x).IsHermitian :=
        T.isHermitian.sub (cqBlock_posSemidef E x).1
      refine (cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg hHerm).2 ?_
      intro A hA
      have hsingle := cqPrimalProgram_dualFeasible_single_le E hy x hA
      have hrep := hrep_psd A hA
      have htrace :
          (((T.val - E.cqBlock x) * A).trace).re =
            ((T.val * A).trace).re - ((E.cqBlock x * A).trace).re := by
        simp [Matrix.sub_mul, Matrix.trace_sub]
      linarith
  · have hrep_one : y (1 : CMatrix b) = E.cqDualValue T.val := by
      let X : HermitianMatrix b := ⟨1, Matrix.PosSemidef.one.1⟩
      have h := hTrep X
      simpa [yH, X, tracePairing, cqDualValue] using h
    simp [QIT.SDP.ContinuousConeProgram.dualValue, cqPrimalProgram, hrep_one]

/-- The conic and matrix-order cq dual value sets coincide. -/
theorem cqPrimalProgram_dualValueSet_eq (E : Ensemble ι b) :
    (cqPrimalProgram E).dualValueSet = E.cqDualValueSet :=
  Set.Subset.antisymm
    (cqPrimalProgram_dualValueSet_subset_cqDualValueSet E)
    (cqDualValueSet_subset_cqPrimalProgram_dualValueSet E)

omit [DecidableEq ι] in
/-- The cq primal conic program is feasible. -/
theorem cqPrimalProgram_primalValueSet_nonempty (E : Ensemble ι b) :
    (cqPrimalProgram E).primalValueSet.Nonempty := by
  classical
  let M : CQEffectFamily ι b := ⟨(probabilityPOVM E).effects⟩
  refine ⟨(cqPrimalProgram E).primalValue M, M, ?_, rfl⟩
  constructor
  · intro x
    exact (probabilityPOVM E).pos x
  · simp [cqPrimalProgram, cqEffectFamilySumCLM, M]

/-- The sum of all weighted cq blocks is dual feasible. -/
theorem cqDualFeasible_sum_cqBlock (E : Ensemble ι b) :
    E.cqDualFeasible (∑ x, E.cqBlock x) := by
  classical
  constructor
  · exact Matrix.posSemidef_sum Finset.univ fun x _ => cqBlock_posSemidef E x
  · intro x
    rw [Matrix.le_iff]
    have hsum :
        (∑ y, E.cqBlock y) - E.cqBlock x =
          ∑ y ∈ Finset.univ.erase x, E.cqBlock y := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
      abel
    rw [hsum]
    exact Matrix.posSemidef_sum (Finset.univ.erase x) fun y _ => cqBlock_posSemidef E y

/-- A positive cq effect is dominated by the sum of all effects in its family. -/
theorem cqEffectFamily_effect_le_sum {M : CQEffectFamily ι b}
    (hM : ∀ x, (M x).PosSemidef) (x : ι) :
    M x ≤ ∑ y, M y := by
  rw [Matrix.le_iff]
  have hsum :
      (∑ y, M y) - M x =
        ∑ y ∈ Finset.univ.erase x, M y := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
    abel
  rw [hsum]
  exact Matrix.posSemidef_sum (Finset.univ.erase x) fun y _ => hM y

/-- The cq primal conic value set is bounded above by a concrete dual point. -/
theorem cqPrimalProgram_primalValueSet_bddAbove (E : Ensemble ι b) :
    BddAbove (cqPrimalProgram E).primalValueSet := by
  exact (cqPrimalProgram E).primalValueSet_bddAbove_of_dualFeasible
    (cqPrimalProgram_dualFeasible_of_cqDualFeasible E (cqDualFeasible_sum_cqBlock E))

set_option maxHeartbeats 800000 in
/-- The cq primal hypograph is closed: for bounded constraint values, positive
effect witnesses are bounded by their sum in operator norm. -/
theorem cqPrimalProgram_hasClosedPrimalHypograph (E : Ensemble ι b) :
    (cqPrimalProgram E).HasClosedPrimalHypograph := by
  classical
  refine IsSeqClosed.isClosed ?_
  intro ztSeq zt hztSeq hztLim
  choose M hMK hA ht using hztSeq
  have hZLim : Tendsto (fun n => (ztSeq n).1) atTop (𝓝 zt.1) :=
    continuous_fst.tendsto zt |>.comp hztLim
  have hZBounded : Bornology.IsBounded (Set.range fun n => (ztSeq n).1) :=
    Metric.isBounded_range_of_tendsto _ hZLim
  obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le hZBounded
  have hC_nonneg : 0 ≤ C := by
    exact (norm_nonneg ((ztSeq 0).1)).trans (hC ((ztSeq 0).1) (Set.mem_range_self 0))
  have hM_norm_le (n : ℕ) : ‖M n‖ ≤ C := by
    change ‖(M n).val‖ ≤ C
    rw [pi_norm_le_iff_of_nonneg hC_nonneg]
    intro x
    have hMx_le_sum : M n x ≤ ∑ y, M n y :=
      cqEffectFamily_effect_le_sum (fun y => hMK n y) x
    have hsum : (∑ y, M n y) = (ztSeq n).1 := by
      simpa [cqPrimalProgram, cqEffectFamilySumCLM] using (hA n).symm
    have hMx_le_Z : M n x ≤ (ztSeq n).1 := by
      simpa [hsum] using hMx_le_sum
    have hnorm_le_Z : ‖M n x‖ ≤ ‖(ztSeq n).1‖ :=
      cMatrix_norm_le_norm_of_posSemidef_le (hMK n x) hMx_le_Z
    exact hnorm_le_Z.trans (hC ((ztSeq n).1) (Set.mem_range_self n))
  have hM_bounded : Bornology.IsBounded (Set.range M) :=
    (isBounded_iff_forall_norm_le).2
      ⟨C, by
        rintro _ ⟨n, rfl⟩
        exact hM_norm_le n⟩
  obtain ⟨Mlim, -, φ, hφ, hMtend⟩ :=
    tendsto_subseq_of_bounded hM_bounded (x := M) (fun n => Set.mem_range_self n)
  have hMlimK : Mlim ∈ (cqPrimalProgram E).K :=
    (cqPrimalProgram E).K.isClosed.mem_of_tendsto hMtend
      (Eventually.of_forall fun n => hMK (φ n))
  have hZLimSub : Tendsto (fun n => (ztSeq (φ n)).1) atTop (𝓝 zt.1) :=
    hZLim.comp hφ.tendsto_atTop
  have hAMlim :
      Tendsto (fun n => (ztSeq (φ n)).1) atTop
        (𝓝 ((cqPrimalProgram E).A Mlim)) := by
    have hcont :
        Tendsto (fun n => (cqPrimalProgram E).A (M (φ n))) atTop
          (𝓝 ((cqPrimalProgram E).A Mlim)) :=
      (cqPrimalProgram E).A.continuous.continuousAt.tendsto.comp hMtend
    have hfun :
        (fun n => (ztSeq (φ n)).1) =
          fun n => (cqPrimalProgram E).A (M (φ n)) := by
      funext n
      exact hA (φ n)
    simpa [hfun] using hcont
  have hAeq : zt.1 = (cqPrimalProgram E).A Mlim :=
    tendsto_nhds_unique hZLimSub hAMlim
  have htLimSub : Tendsto (fun n => (ztSeq (φ n)).2) atTop (𝓝 zt.2) :=
    (continuous_snd.tendsto zt |>.comp hztLim).comp hφ.tendsto_atTop
  have hValueLim :
      Tendsto (fun n => (cqPrimalProgram E).primalValue (M (φ n))) atTop
        (𝓝 ((cqPrimalProgram E).primalValue Mlim)) :=
    (cqPrimalProgram E).c.continuous.continuousAt.tendsto.comp hMtend
  have htle : zt.2 ≤ (cqPrimalProgram E).primalValue Mlim :=
    le_of_tendsto_of_tendsto' htLimSub hValueLim fun n => ht (φ n)
  exact ⟨Mlim, hMlimK, hAeq, htle⟩

/-- Exact cq SDP strong duality in value-set form. -/
theorem cqGuessingProbability_eq_cqDualOptimalValue (E : Ensemble ι b) :
    E.cqGuessingProbability = E.cqDualOptimalValue := by
  rw [cqGuessingProbability_eq_sSup_primalValueSet, cqDualOptimalValue_eq,
    ← cqPrimalProgram_primalValueSet_eq E, ← cqPrimalProgram_dualValueSet_eq E]
  exact (cqPrimalProgram E).sSup_primalValueSet_eq_sInf_dualValueSet_of_hasClosedPrimalHypograph
    (cqPrimalProgram_hasClosedPrimalHypograph E)
    (cqPrimalProgram_primalValueSet_nonempty E)
    (cqPrimalProgram_primalValueSet_bddAbove E)

/-- Reverse weak duality for cq guessing, obtained from the closed-hypograph
finite-dimensional conic strong-duality bridge. -/
theorem cqDualOptimalValue_le_cqGuessingProbability (E : Ensemble ι b) :
    E.cqDualOptimalValue <= E.cqGuessingProbability := by
  rw [cqGuessingProbability_eq_cqDualOptimalValue]

/-- Every dual-feasible matrix upper-bounds every value in the primal value set. -/
theorem cqPrimalValueSet_le_dualValue (E : Ensemble ι b) {T : CMatrix b}
    (hT : E.cqDualFeasible T) {score : ℝ} (hscore : score ∈ E.cqPrimalValueSet) :
    score ≤ E.cqDualValue T := by
  rcases hscore with ⟨M, rfl⟩
  exact cqPrimalValue_le_dualValue E M hT

/-- Weak duality at the supremum level: any dual-feasible matrix upper-bounds
the cq guessing probability. -/
theorem cqGuessingProbability_le_dualValue (E : Ensemble ι b) {T : CMatrix b}
    (hT : E.cqDualFeasible T) :
    E.cqGuessingProbability ≤ E.cqDualValue T := by
  rw [cqGuessingProbability_eq_sSup_primalValueSet]
  exact Real.sSup_le
    (fun score hscore => cqPrimalValueSet_le_dualValue E hT hscore)
    (Matrix.PosSemidef.trace_nonneg hT.1).1

omit [Fintype ι] in
private theorem identityTensorStateMatrix_block_self (σ : State b) (x : ι) :
    Classical.block (State.identityTensorStateMatrix (a := ι) σ) x x = σ.matrix := by
  ext i j
  simp [Classical.block, State.identityTensorStateMatrix, Matrix.kronecker,
    Matrix.kroneckerMap_apply]

/-- Every conditional-min-entropy feasible pair gives a feasible matrix for the
cq guessing dual program. -/
theorem cqDualFeasible_of_conditionalMinEntropyFeasible (E : Ensemble ι b) (σ : State b)
    (lam : ℝ)
    (h : State.ConditionalMinEntropyFeasible (a := ι) E.cqState σ lam) :
    E.cqDualFeasible ((Real.rpow 2 (-lam) : ℂ) • σ.matrix) := by
  classical
  let c : ℂ := (Real.rpow 2 (-lam) : ℂ)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    rw [Complex.zero_le_real]
    positivity
  refine ⟨σ.pos.smul hc_nonneg, fun x => ?_⟩
  rw [Matrix.le_iff]
  have hdiff :
      (c • State.identityTensorStateMatrix (a := ι) σ - E.cqState.matrix).PosSemidef := by
    simpa [c, State.ConditionalMinEntropyFeasible, Matrix.le_iff] using h
  have hblock := hdiff.submatrix (fun i : b => (x, i))
  have hblock_eq :
      Matrix.submatrix
          (c • State.identityTensorStateMatrix (a := ι) σ - E.cqState.matrix)
          (fun i : b => (x, i)) (fun i : b => (x, i)) =
        c • σ.matrix - E.cqBlock x := by
    ext i j
    have hblock_id := congrFun (congrFun (identityTensorStateMatrix_block_self (σ := σ) x) i) j
    have hblock_cq := congrFun (congrFun (Classical.cqState_block_self E x) i) j
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, cqBlock, smul_eq_mul,
      Classical.block] at hblock_id hblock_cq ⊢
    rw [hblock_id, hblock_cq]
  rw [← hblock_eq]
  exact hblock

/-- Blockwise domination by the same scaled `B` state is exactly the global cq
order constraint used by conditional min-entropy. -/
theorem conditionalMinEntropyFeasible_of_cqBlock_le (E : Ensemble ι b) (σ : State b)
    (lam : ℝ)
    (hblock : ∀ x, E.cqBlock x ≤ (Real.rpow 2 (-lam) : ℂ) • σ.matrix) :
    State.ConditionalMinEntropyFeasible (a := ι) E.cqState σ lam := by
  classical
  let c : ℂ := (Real.rpow 2 (-lam) : ℂ)
  rw [State.ConditionalMinEntropyFeasible_eq, Matrix.le_iff]
  have hblocks : ∀ x, (c • σ.matrix - E.cqBlock x).PosSemidef := by
    intro x
    simpa [c, Matrix.le_iff] using hblock x
  have hmatrix :
      (c • State.identityTensorStateMatrix (a := ι) σ - E.cqState.matrix) =
        Classical.blockDiagonal fun x => c • σ.matrix - E.cqBlock x := by
    calc
      c • State.identityTensorStateMatrix (a := ι) σ - E.cqState.matrix =
          c • Classical.blockDiagonal (fun _ : ι => σ.matrix) -
            Classical.blockDiagonal (fun x => E.cqBlock x) := by
            rw [identityTensorStateMatrix_eq_blockDiagonal, cqState_eq_blockDiagonal_cqBlock]
      _ = Classical.blockDiagonal (fun x => c • σ.matrix) -
            Classical.blockDiagonal (fun x => E.cqBlock x) := by
            rw [← Classical.blockDiagonal_smul]
      _ = Classical.blockDiagonal (fun x => c • σ.matrix - E.cqBlock x) := by
            rw [Classical.blockDiagonal_sub]
  rw [hmatrix]
  exact Classical.blockDiagonal_posSemidef (fun x => c • σ.matrix - E.cqBlock x) hblocks

/-- The state-scaled cq dual constraint implies the conditional-min-entropy
order constraint. -/
theorem conditionalMinEntropyFeasible_of_cqDualFeasible_stateScale
    (E : Ensemble ι b) (σ : State b) (lam : ℝ)
    (hT : E.cqDualFeasible ((Real.rpow 2 (-lam) : ℂ) • σ.matrix)) :
    State.ConditionalMinEntropyFeasible (a := ι) E.cqState σ lam :=
  conditionalMinEntropyFeasible_of_cqBlock_le E σ lam hT.2

/-- Conditional-min-entropy feasibility is equivalent to the corresponding
state-scaled cq guessing dual feasibility. -/
theorem conditionalMinEntropyFeasible_iff_cqDualFeasible_stateScale
    (E : Ensemble ι b) (σ : State b) (lam : ℝ) :
    State.ConditionalMinEntropyFeasible (a := ι) E.cqState σ lam ↔
      E.cqDualFeasible ((Real.rpow 2 (-lam) : ℂ) • σ.matrix) :=
  ⟨cqDualFeasible_of_conditionalMinEntropyFeasible E σ lam,
    conditionalMinEntropyFeasible_of_cqDualFeasible_stateScale E σ lam⟩

/-- Any feasible conditional-min-entropy exponent gives an upper bound on the
cq guessing probability. -/
theorem cqGuessingProbability_le_rpow_neg_of_conditionalMinEntropyFeasible
    (E : Ensemble ι b) (σ : State b) (lam : ℝ)
    (h : State.ConditionalMinEntropyFeasible (a := ι) E.cqState σ lam) :
    E.cqGuessingProbability ≤ Real.rpow 2 (-lam) := by
  let T : CMatrix b := (Real.rpow 2 (-lam) : ℂ) • σ.matrix
  have hT : E.cqDualFeasible T :=
    cqDualFeasible_of_conditionalMinEntropyFeasible E σ lam h
  calc
    E.cqGuessingProbability ≤ E.cqDualValue T :=
      cqGuessingProbability_le_dualValue E hT
    _ = Real.rpow 2 (-lam) := by
      simp [T, cqDualValue, Matrix.trace_smul, σ.trace_eq_one]

/-- For a cq state, feasibility in the guessing-probability dual program is
exactly feasibility in the unnormalized conditional-min-entropy scale program. -/
theorem cqDualFeasible_iff_conditionalMinEntropyScaleFeasible
    (E : Ensemble ι b) (T : CMatrix b) :
    E.cqDualFeasible T ↔
      State.ConditionalMinEntropyScaleFeasible (a := ι) E.cqState T := by
  classical
  constructor
  · intro hT
    refine ⟨hT.1, ?_⟩
    rw [Matrix.le_iff]
    have hblocks : ∀ x, (T - E.cqBlock x).PosSemidef := by
      intro x
      simpa [Matrix.le_iff] using hT.2 x
    have hmatrix :
        Matrix.kronecker (1 : CMatrix ι) T - E.cqState.matrix =
          Classical.blockDiagonal fun x => T - E.cqBlock x := by
      rw [Classical.identityTensor_eq_blockDiagonal, cqState_eq_blockDiagonal_cqBlock,
        ← Classical.blockDiagonal_sub]
    rw [hmatrix]
    exact Classical.blockDiagonal_posSemidef _ hblocks
  · intro hT
    refine ⟨hT.1, fun x => ?_⟩
    rw [Matrix.le_iff]
    have hsub := hT.2.submatrix (fun i : b => (x, i))
    have hmatrix :
        Matrix.kronecker (1 : CMatrix ι) T - E.cqState.matrix =
          Classical.blockDiagonal fun y => T - E.cqBlock y := by
      rw [Classical.identityTensor_eq_blockDiagonal, cqState_eq_blockDiagonal_cqBlock,
        ← Classical.blockDiagonal_sub]
    change
      (Classical.block
        (Matrix.kronecker (1 : CMatrix ι) T - E.cqState.matrix) x x).PosSemidef at hsub
    rw [hmatrix, Classical.blockDiagonal_block_self] at hsub
    exact hsub

/-- The cq guessing dual objective values are exactly the endpoint
conditional-min-entropy scale values. -/
theorem cqDualValueSet_eq_conditionalMinEntropyScaleValueSet (E : Ensemble ι b) :
    E.cqDualValueSet = E.cqState.conditionalMinEntropyScaleValueSet (a := ι) := by
  ext t
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T, (E.cqDualFeasible_iff_conditionalMinEntropyScaleFeasible T).mp hT, rfl⟩
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T, (E.cqDualFeasible_iff_conditionalMinEntropyScaleFeasible T).mpr hT, rfl⟩

/-- The cq guessing probability equals the unnormalized endpoint scale of the
conditional min-entropy of the associated cq state. -/
theorem cqGuessingProbability_eq_conditionalMinEntropyScale (E : Ensemble ι b) :
    E.cqGuessingProbability = E.cqState.conditionalMinEntropyScale (a := ι) := by
  rw [cqGuessingProbability_eq_cqDualOptimalValue, cqDualOptimalValue_eq,
    State.conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    cqDualValueSet_eq_conditionalMinEntropyScaleValueSet]

/-- Operational characterization of normalized cq conditional min-entropy:
`2⁻ᴴᵐⁱⁿ⁽ˣ|ᴮ⁾ = p_guess(X|B)`. -/
theorem rpow_neg_conditionalMinEntropy_eq_cqGuessingProbability (E : Ensemble ι b) :
    Real.rpow 2 (-E.cqState.conditionalMinEntropy) = E.cqGuessingProbability := by
  letI : Nonempty ι := E.index_nonempty
  letI : Nonempty b :=
    (E.states (Classical.choice (inferInstance : Nonempty ι))).nonempty
  have hscale : 0 < E.cqState.conditionalMinEntropyScale (a := ι) := by
    rw [E.cqState.conditionalMinEntropyScale_eq_normalizedScale (a := ι)]
    exact E.cqState.conditionalMinEntropyNormalizedScale_inf_pos (a := ι)
  rw [E.cqState.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := ι)]
  simp only [neg_neg]
  rw [QIT.rpow_two_log2_pos hscale]
  exact E.cqGuessingProbability_eq_conditionalMinEntropyScale.symm

end Ensemble

end

end QIT
