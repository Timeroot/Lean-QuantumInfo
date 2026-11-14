/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.SmoothEndpoint
public import QIT.States.SubnormalizedTopology
public import Mathlib.Topology.Semicontinuity.Basic
public import QIT.Information.Entropy.Log2Lemmas

/-!
# Smooth min/max entropy attainment

This module isolates the compactness and semicontinuity spine that turns the
smooth subnormalized min/max entropy definitions from `sSup`/`sInf` over a
purified-distance ball into source-style attained extrema.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace QIT

universe u v

noncomputable section

namespace SubnormalizedState

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

omit [Fintype a] in
/-- The map `σ_B ↦ I_A ⊗ σ_B` is continuous in the subnormalized-state
topology. -/
theorem continuous_identityTensorStateMatrix :
    Continuous fun σ : SubnormalizedState b => identityTensorStateMatrix (a := a) σ := by
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro j
  simp [identityTensorStateMatrix, Matrix.kronecker]
  exact continuous_const.mul
    ((continuous_apply j.2).comp ((continuous_apply i.2).comp continuous_matrix))

/-- For fixed side information, the raw squared-fidelity max-entropy candidate
is continuous in the optimized subnormalized state. -/
theorem continuous_conditionalMaxEntropyExponentCandidate_left
    (σ : SubnormalizedState b) :
    Continuous fun ρ : SubnormalizedState (Prod a b) =>
      ρ.conditionalMaxEntropyExponentCandidate (a := a) σ := by
  have hmul : Continuous fun ρ : SubnormalizedState (Prod a b) =>
      psdSqrt ρ.matrix * psdSqrt (identityTensorStateMatrix (a := a) σ) :=
    continuous_psdSqrt_matrix.matrix_mul continuous_const
  have hnorm : Continuous fun ρ : SubnormalizedState (Prod a b) =>
      traceNorm (psdSqrt ρ.matrix * psdSqrt (identityTensorStateMatrix (a := a) σ)) :=
    traceNorm_continuous_forTopology.comp hmul
  simpa [conditionalMaxEntropyExponentCandidate] using hnorm.pow 2

/-- Compact feasible pairs `(ρ', T_B)` for the conditional-min scale over a
purified-distance ball, with a harmless trace cap on `T_B`. -/
def conditionalMinEntropyScaleFeasiblePairSet
    (ρ : SubnormalizedState (Prod a b)) (ε B : ℝ) :
    Set (SubnormalizedState (Prod a b) × CMatrix b) :=
  ({ρ' : SubnormalizedState (Prod a b) | ρ.purifiedBall ε ρ'} ×ˢ
      psdTraceBoundedMatrixSet b B) ∩
    {p | p.1.matrix ≤ Matrix.kronecker (1 : CMatrix a) p.2}

/-- The matrix-order constraint in the feasible-pair domain is closed. -/
theorem conditionalMinEntropyScaleFeasiblePair_order_isClosed :
    IsClosed
      ({p : SubnormalizedState (Prod a b) × CMatrix b |
        p.1.matrix ≤ Matrix.kronecker (1 : CMatrix a) p.2}) := by
  let f : SubnormalizedState (Prod a b) × CMatrix b → CMatrix (Prod a b) :=
    fun p => Matrix.kronecker (1 : CMatrix a) p.2 - p.1.matrix
  have hf : Continuous f := by
    exact ((continuous_kronecker_one_matrix (a := a) (b := b)).comp continuous_snd).sub
      (continuous_matrix.comp continuous_fst)
  have hset :
      {p : SubnormalizedState (Prod a b) × CMatrix b |
        p.1.matrix ≤ Matrix.kronecker (1 : CMatrix a) p.2} =
      {p | f p ∈ ({M : CMatrix (Prod a b) | M.PosSemidef} : Set (CMatrix (Prod a b)))} := by
    ext p
    simp [f, Matrix.le_iff]
  rw [hset]
  exact (psdCone (Prod a b)).isClosed.preimage hf

/-- The feasible-pair domain for the conditional-min scale is compact. -/
theorem conditionalMinEntropyScaleFeasiblePairSet_isCompact
    (ρ : SubnormalizedState (Prod a b)) (ε B : ℝ) :
    IsCompact (conditionalMinEntropyScaleFeasiblePairSet (a := a) (b := b) ρ ε B) := by
  let ball : Set (SubnormalizedState (Prod a b)) := {ρ' | ρ.purifiedBall ε ρ'}
  let tset : Set (CMatrix b) := psdTraceBoundedMatrixSet b B
  have hball : IsCompact ball := by
    simpa [ball] using
      SubnormalizedState.purifiedBall_isCompact (a := Prod a b) ρ ε
  have htset : IsCompact tset := by
    simpa [tset] using psdTraceBoundedMatrixSet_isCompact (b := b) (R := B)
  have hbase : IsCompact (ball ×ˢ tset) := hball.prod htset
  have hclosed := conditionalMinEntropyScaleFeasiblePair_order_isClosed (a := a) (b := b)
  simpa [conditionalMinEntropyScaleFeasiblePairSet, ball, tset] using
    hbase.inter_right hclosed

/-- Positive logarithmic max-entropy candidate values are bounded above on
positive-trace subnormalized states. -/
theorem conditionalMaxEntropyPositiveValueSet_bddAbove_of_trace_pos
    [Nonempty a] [Nonempty b] {ρ : SubnormalizedState (Prod a b)}
    (hρ : 0 < ρ.matrix.trace.re) :
    BddAbove (ρ.conditionalMaxEntropyPositiveValueSet (a := a)) := by
  rcases ρ.conditionalMaxEntropyPositiveExponentValueSet_bddAbove_of_trace_pos
      (a := a) hρ with ⟨B, hB⟩
  rcases ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty_of_trace_pos
      (a := a) hρ with ⟨x0, hx0⟩
  have hx0_pos : 0 < x0 := by
    rcases hx0 with ⟨σ0, hpos0, rfl⟩
    exact hpos0
  have hB_pos : 0 < B := lt_of_lt_of_le hx0_pos (hB hx0)
  refine ⟨log2 B, ?_⟩
  intro h hh
  rw [conditionalMaxEntropyPositiveValueSet_eq_log2_image] at hh
  rcases hh with ⟨x, hx, rfl⟩
  have hx_pos : 0 < x := by
    rcases hx with ⟨σ, hpos, rfl⟩
    exact hpos
  unfold log2
  exact div_le_div_of_nonneg_right
    (Real.log_le_log hx_pos (hB hx))
    (le_of_lt (Real.log_pos one_lt_two))

/-- Subnormalized conditional max-entropy is lower semicontinuous on any
positive trace-lower-bound region. -/
theorem conditionalMaxEntropyRaw_lowerSemicontinuousOn_trace_lower_bound
    [Nonempty a] [Nonempty b] {δ : ℝ} (hδ : 0 < δ) :
    LowerSemicontinuousOn
      (fun ρ : SubnormalizedState (Prod a b) => ρ.conditionalMaxEntropyRaw)
      {ρ | δ ≤ ρ.matrix.trace.re} := by
  intro ρ hρ y hy
  have hρ_pos : 0 < ρ.matrix.trace.re := lt_of_lt_of_le hδ hρ
  have hne :
      (ρ.conditionalMaxEntropyPositiveValueSet (a := a)).Nonempty :=
    ρ.conditionalMaxEntropyPositiveValueSet_nonempty_of_trace_pos (a := a) hρ_pos
  change y < ρ.conditionalMaxEntropyRaw at hy
  rw [conditionalMaxEntropy_eq_sSup_positiveValueSet] at hy
  rcases exists_lt_of_lt_csSup hne hy with ⟨h, hh, hyh⟩
  rcases hh with ⟨σ, hpos, rfl⟩
  let f : SubnormalizedState (Prod a b) → ℝ :=
    fun τ => τ.conditionalMaxEntropyExponentCandidate (a := a) σ
  have hf : Continuous f :=
    continuous_conditionalMaxEntropyExponentCandidate_left (a := a) σ
  have hlog :
      ContinuousAt (fun x : ℝ => log2 x) (f ρ) := by
    unfold log2
    exact (Real.continuousAt_log hpos.ne').div_const _
  have hcandidate :
      ContinuousAt (fun τ : SubnormalizedState (Prod a b) =>
        τ.conditionalMaxEntropyFidelityCandidate (a := a) σ) ρ := by
    simpa [f, conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate]
      using hlog.comp (hf.continuousAt (x := ρ))
  have hevent_gt :
      ∀ᶠ τ in 𝓝[{ρ : SubnormalizedState (Prod a b) | δ ≤ ρ.matrix.trace.re}] ρ,
        y < τ.conditionalMaxEntropyFidelityCandidate (a := a) σ :=
    hcandidate.continuousWithinAt.eventually (Ioi_mem_nhds hyh)
  have hevent_pos :
      ∀ᶠ τ in 𝓝[{ρ : SubnormalizedState (Prod a b) | δ ≤ ρ.matrix.trace.re}] ρ,
        0 < τ.conditionalMaxEntropyExponentCandidate (a := a) σ :=
    (hf.continuousAt (x := ρ)).continuousWithinAt.eventually (Ioi_mem_nhds hpos)
  filter_upwards [self_mem_nhdsWithin, hevent_gt, hevent_pos] with τ hτ hyτ hposτ
  have hτ_pos : 0 < τ.matrix.trace.re := lt_of_lt_of_le hδ hτ
  have hbdd :
      BddAbove (τ.conditionalMaxEntropyPositiveValueSet (a := a)) :=
    τ.conditionalMaxEntropyPositiveValueSet_bddAbove_of_trace_pos (a := a) hτ_pos
  have hmem :
      τ.conditionalMaxEntropyFidelityCandidate (a := a) σ ∈
        τ.conditionalMaxEntropyPositiveValueSet (a := a) :=
    ⟨σ, hposτ, rfl⟩
  rw [conditionalMaxEntropy_eq_sSup_positiveValueSet]
  exact lt_of_lt_of_le hyτ (le_csSup hbdd hmem)

/-- Smooth subnormalized conditional max-entropy attains its minimum on every
purified-distance ball with radius below `sqrt (Tr ρ)`. -/
theorem smoothConditionalMaxEntropy_exists_optimizer
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε : ℝ}
    (hε_nonneg : 0 ≤ ε) (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    ∃ ρmax : SubnormalizedState (Prod a b),
      ∃ hρmax : ρmax.matrix ≠ 0,
      ρ.purifiedBall ε ρmax ∧
        ρ.smoothConditionalMaxEntropy ε hε_nonneg hε =
          ρmax.conditionalMaxEntropyFinite hρmax ∧
          ∀ ρ' : SubnormalizedState (Prod a b),
            ∀ hρ' : ρ'.matrix ≠ 0, ρ.purifiedBall ε ρ' →
              ρmax.conditionalMaxEntropyFinite hρmax ≤
                ρ'.conditionalMaxEntropyFinite hρ' := by
  let δ : ℝ := (Real.sqrt ρ.matrix.trace.re - ε) ^ 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact sq_pos_of_pos (sub_pos.mpr hε)
  let ball : Set (SubnormalizedState (Prod a b)) := {ρ' | ρ.purifiedBall ε ρ'}
  have hball_compact : IsCompact ball := by
    simpa [ball] using SubnormalizedState.purifiedBall_isCompact (a := Prod a b) ρ ε
  have hball_nonempty : ball.Nonempty :=
    ⟨ρ, by
      dsimp [ball]
      exact ρ.purifiedBall_self_of_nonneg hε_nonneg⟩
  have hball_subset_trace :
      ball ⊆ {ρ' : SubnormalizedState (Prod a b) | δ ≤ ρ'.matrix.trace.re} := by
    intro ρ' hball
    dsimp [ball] at hball
    dsimp [δ]
    exact ρ.purifiedBall_trace_lower_bound ρ' hε hball
  have hlsc_trace :
      LowerSemicontinuousOn
        (fun ρ' : SubnormalizedState (Prod a b) => ρ'.conditionalMaxEntropyRaw)
        {ρ' | δ ≤ ρ'.matrix.trace.re} :=
    conditionalMaxEntropyRaw_lowerSemicontinuousOn_trace_lower_bound
      (a := a) (b := b) hδ
  have hlsc_ball :
      LowerSemicontinuousOn
        (fun ρ' : SubnormalizedState (Prod a b) => ρ'.conditionalMaxEntropyRaw)
        ball :=
    hlsc_trace.mono hball_subset_trace
  obtain ⟨ρmax, hρmax_ball, hρmax_min⟩ :=
    LowerSemicontinuousOn.exists_isMinOn hball_nonempty hball_compact hlsc_ball
  have hρmax : ρmax.matrix ≠ 0 := by
    have hpos := SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      ρ ρmax hε hρmax_ball
    intro hzero
    rw [hzero] at hpos
    simp at hpos
  refine ⟨ρmax, hρmax, hρmax_ball, ?_, ?_⟩
  · rw [smoothConditionalMaxEntropy_eq_sInf_candidates]
    apply le_antisymm
    · exact csInf_le
        (SubnormalizedState.SmoothConditionalMaxEntropyCandidateRaw_bddBelow_of_lt_sqrt_trace
          (a := a) ρ hε)
        ⟨ρmax, hρmax_ball, rfl⟩
    · refine le_csInf
        (SubnormalizedState.SmoothConditionalMaxEntropyCandidateRaw_set_nonempty_of_nonneg
          (a := a) ρ hε_nonneg) ?_
      intro h hh
      rcases hh with ⟨ρ', hρ'_ball, rfl⟩
      exact hρmax_min hρ'_ball
  · intro ρ' _hρ' hρ'_ball
    exact hρmax_min hρ'_ball

/-- Smooth subnormalized conditional min-entropy attains its maximum together
with an optimal feasible side operator.  This is the source-level witness pair
used by the normalized-extension argument for smooth min/max comparison. -/
theorem smoothConditionalMinEntropy_exists_scale_optimizer
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε : ℝ}
    (hε_nonneg : 0 ≤ ε) (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    ∃ (ρmin : SubnormalizedState (Prod a b)) (Tmin : CMatrix b),
      ∃ hρmin : ρmin.matrix ≠ 0,
      ρ.purifiedBall ε ρmin ∧
        ConditionalMinEntropyScaleFeasible (a := a) ρmin Tmin ∧
          ρmin.conditionalMinEntropyScale (a := a) = Tmin.trace.re ∧
            ρ.smoothConditionalMinEntropy ε hε_nonneg hε =
              ρmin.conditionalMinEntropyFinite hρmin ∧
              ∀ ρ' : SubnormalizedState (Prod a b),
                ∀ hρ' : ρ'.matrix ≠ 0, ρ.purifiedBall ε ρ' →
                  ρ'.conditionalMinEntropyFinite hρ' ≤
                    ρmin.conditionalMinEntropyFinite hρmin := by
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
      psdTraceBoundedMatrixSet]
    constructor
    · constructor
      · exact ρ.purifiedBall_self_of_nonneg hε_nonneg
      · constructor
        · exact Matrix.PosSemidef.one
        · rw [Matrix.trace_one]
          norm_num
    · simpa [Matrix.one_kronecker_one] using ρ.matrix_le_one
  let traceFun : SubnormalizedState (Prod a b) × CMatrix b → ℝ := fun p => p.2.trace.re
  have htraceFun_cont : Continuous traceFun := by
    exact Complex.continuous_re.comp (Continuous.matrix_trace continuous_snd)
  obtain ⟨pmin, hpmin, hpmin_min⟩ :=
    LowerSemicontinuousOn.exists_isMinOn hnonempty hcompact
      (htraceFun_cont.lowerSemicontinuous.lowerSemicontinuousOn feasibleSet)
  let ρmin : SubnormalizedState (Prod a b) := pmin.1
  let Tmin : CMatrix b := pmin.2
  rcases hpmin with ⟨⟨hρmin_ball, hTmin_set⟩, hρmin_le_Tmin⟩
  have hTmin_feas :
      ConditionalMinEntropyScaleFeasible (a := a) ρmin Tmin :=
    ⟨hTmin_set.1, hρmin_le_Tmin⟩
  let δ : ℝ := (Real.sqrt ρ.matrix.trace.re - ε) ^ 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact sq_pos_of_pos (sub_pos.mpr hε)
  have hcard_a_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hρmin_trace_lower : δ ≤ ρmin.matrix.trace.re := by
    dsimp [δ]
    exact ρ.purifiedBall_trace_lower_bound ρmin hε hρmin_ball
  have hTmin_trace_pos : 0 < Tmin.trace.re := by
    have hscale_lb :
        ρmin.matrix.trace.re / (Fintype.card a : ℝ) ≤ Tmin.trace.re :=
      conditionalMinEntropyScaleFeasible_trace_lower_bound (a := a) hTmin_feas
    exact lt_of_lt_of_le (div_pos hδ hcard_a_pos)
      ((div_le_div_of_nonneg_right hρmin_trace_lower
        (le_of_lt hcard_a_pos)).trans hscale_lb)
  have hmin_le_trace_of_feasible :
      ∀ ρ' : SubnormalizedState (Prod a b), ρ.purifiedBall ε ρ' →
        ∀ T : CMatrix b,
          ConditionalMinEntropyScaleFeasible (a := a) ρ' T →
            Tmin.trace.re ≤ T.trace.re := by
    intro ρ' hball T hT
    by_cases hTcap : T.trace.re ≤ B
    · have hp : (ρ', T) ∈ feasibleSet := by
        dsimp [feasibleSet, conditionalMinEntropyScaleFeasiblePairSet,
          psdTraceBoundedMatrixSet]
        exact ⟨⟨hball, hT.1, hTcap⟩, hT.2⟩
      simpa [traceFun, Tmin] using hpmin_min hp
    · have hB_lt : B < T.trace.re := lt_of_not_ge hTcap
      exact hTmin_set.2.trans (le_of_lt hB_lt)
  have hscale_ge_Tmin :
      ∀ ρ' : SubnormalizedState (Prod a b), ρ.purifiedBall ε ρ' →
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
    exact csInf_le (ρmin.conditionalMinEntropyScaleValueSet_bddBelow (a := a))
      ⟨Tmin, hTmin_feas, rfl⟩
  have hscale_ρmin_eq_Tmin :
      ρmin.conditionalMinEntropyScale (a := a) = Tmin.trace.re :=
    le_antisymm hscale_ρmin_le_Tmin (hscale_ge_Tmin ρmin hρmin_ball)
  have hρmin_trace_pos : 0 < ρmin.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace ρ ρmin hε hρmin_ball
  have hρmin : ρmin.matrix ≠ 0 := by
    intro hzero
    rw [hzero] at hρmin_trace_pos
    simp at hρmin_trace_pos
  have hoptimizer :
      ∀ ρ' : SubnormalizedState (Prod a b), ρ.purifiedBall ε ρ' →
        ρ'.conditionalMinEntropyRaw ≤ ρmin.conditionalMinEntropyRaw := by
    intro ρ' hball
    have hρ'_trace_pos : 0 < ρ'.matrix.trace.re :=
      SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace ρ ρ' hε hball
    have hscale_pos :
        0 < ρ'.conditionalMinEntropyScale (a := a) :=
      ρ'.conditionalMinEntropyScale_pos_of_trace_pos (a := a) hρ'_trace_pos
    have hscale_ge := hscale_ge_Tmin ρ' hball
    rw [ρ'.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos (a := a) hρ'_trace_pos,
      ρmin.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
        (a := a) hρmin_trace_pos,
      hscale_ρmin_eq_Tmin]
    exact neg_log2_antitone_of_pos hTmin_trace_pos hscale_ge
  refine ⟨ρmin, Tmin, hρmin, hρmin_ball, hTmin_feas, hscale_ρmin_eq_Tmin, ?_, ?_⟩
  rw [smoothConditionalMinEntropy_eq_sSup_candidates]
  apply le_antisymm
  · refine csSup_le
      (SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw_set_nonempty_of_nonneg
        (a := a) ρ hε_nonneg) ?_
    intro h hh
    rcases hh with ⟨ρ', hρ'_ball, rfl⟩
    exact hoptimizer ρ' hρ'_ball
  · exact le_csSup
      (SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw_bddAbove_of_lt_sqrt_trace
        (a := a) ρ hε)
      ⟨ρmin, hρmin_ball, rfl⟩
  · intro ρ' _hρ' hball
    exact hoptimizer ρ' hball

/-- Smooth subnormalized conditional min-entropy attains its maximum on every
purified-distance ball with radius below `sqrt (Tr ρ)`. -/
theorem smoothConditionalMinEntropy_exists_optimizer
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε : ℝ}
    (hε_nonneg : 0 ≤ ε) (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    ∃ ρmin : SubnormalizedState (Prod a b),
      ∃ hρmin : ρmin.matrix ≠ 0,
      ρ.purifiedBall ε ρmin ∧
        ρ.smoothConditionalMinEntropy ε hε_nonneg hε =
          ρmin.conditionalMinEntropyFinite hρmin ∧
          ∀ ρ' : SubnormalizedState (Prod a b),
            ∀ hρ' : ρ'.matrix ≠ 0, ρ.purifiedBall ε ρ' →
              ρ'.conditionalMinEntropyFinite hρ' ≤
                ρmin.conditionalMinEntropyFinite hρmin := by
  rcases ρ.smoothConditionalMinEntropy_exists_scale_optimizer
      (a := a) hε_nonneg hε with
    ⟨ρmin, _Tmin, hρmin, hρmin_ball, _hTmin_feas, _hscale, hmin_eq, hoptimizer⟩
  exact ⟨ρmin, hρmin, hρmin_ball, hmin_eq, hoptimizer⟩

/-- Combined smooth min/max source-spine theorem: both smooth extrema over the
subnormalized purified-distance ball are attained. -/
theorem smoothConditionalMinMaxEntropy_exists_optimizers
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε : ℝ}
    (hε_nonneg : 0 ≤ ε) (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    ∃ ρmin ρmax : SubnormalizedState (Prod a b),
      ∃ (hρmin : ρmin.matrix ≠ 0) (hρmax : ρmax.matrix ≠ 0),
      ρ.purifiedBall ε ρmin ∧
          ρ.purifiedBall ε ρmax ∧
          ρ.smoothConditionalMinEntropy ε hε_nonneg hε =
              ρmin.conditionalMinEntropyFinite hρmin ∧
            ρ.smoothConditionalMaxEntropy ε hε_nonneg hε =
              ρmax.conditionalMaxEntropyFinite hρmax ∧
              (∀ ρ' : SubnormalizedState (Prod a b),
                ∀ hρ' : ρ'.matrix ≠ 0, ρ.purifiedBall ε ρ' →
                  ρ'.conditionalMinEntropyFinite hρ' ≤
                    ρmin.conditionalMinEntropyFinite hρmin) ∧
                ∀ ρ' : SubnormalizedState (Prod a b),
                  ∀ hρ' : ρ'.matrix ≠ 0, ρ.purifiedBall ε ρ' →
                    ρmax.conditionalMaxEntropyFinite hρmax ≤
                      ρ'.conditionalMaxEntropyFinite hρ' := by
  rcases smoothConditionalMinEntropy_exists_optimizer
      (a := a) (b := b) ρ hε_nonneg hε with
    ⟨ρmin, hρmin, hρmin_ball, hmin_eq, hmin_opt⟩
  rcases smoothConditionalMaxEntropy_exists_optimizer
      (a := a) (b := b) ρ hε_nonneg hε with
    ⟨ρmax, hρmax, hρmax_ball, hmax_eq, hmax_opt⟩
  exact ⟨ρmin, ρmax, hρmin, hρmax, hρmin_ball, hρmax_ball,
    hmin_eq, hmax_eq, hmin_opt, hmax_opt⟩

end SubnormalizedState

end

end QIT
