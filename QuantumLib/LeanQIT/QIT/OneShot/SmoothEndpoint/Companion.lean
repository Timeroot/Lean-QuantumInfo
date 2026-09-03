/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.SmoothEndpoint.Duality

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal Pointwise
open scoped Topology
open Matrix
open Set Filter

namespace QIT

universe u v w x

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace SubnormalizedState

variable {c : Type x} [Fintype c] [DecidableEq c]

/-! ## Canonical subnormalized endpoint values -/

/-- Compatibility alias for the former companion API.  The canonical name now
already has the safe extended-real codomain. -/
@[deprecated conditionalMinEntropy (since := "2026-07-22")]
abbrev conditionalMinEntropyE (ρ : SubnormalizedState (Prod a b)) : EReal :=
  ρ.conditionalMinEntropy

/-- Compatibility alias for the former companion API.  The canonical name now
already has the safe extended-real codomain. -/
@[deprecated conditionalMaxEntropy (since := "2026-07-22")]
abbrev conditionalMaxEntropyE (ρ : SubnormalizedState (Prod a b)) : EReal :=
  ρ.conditionalMaxEntropy

@[deprecated conditionalMinEntropy_eq_top_of_matrix_eq_zero (since := "2026-07-22")]
theorem conditionalMinEntropyE_eq_top_of_matrix_eq_zero
    {ρ : SubnormalizedState (Prod a b)} (hρ : ρ.matrix = 0) :
    ρ.conditionalMinEntropy = ⊤ :=
  ρ.conditionalMinEntropy_eq_top_of_matrix_eq_zero hρ

@[deprecated conditionalMaxEntropy_eq_bot_of_matrix_eq_zero (since := "2026-07-22")]
theorem conditionalMaxEntropyE_eq_bot_of_matrix_eq_zero
    {ρ : SubnormalizedState (Prod a b)} (hρ : ρ.matrix = 0) :
    ρ.conditionalMaxEntropy = ⊥ :=
  ρ.conditionalMaxEntropy_eq_bot_of_matrix_eq_zero hρ

@[deprecated conditionalMinEntropy_eq_coe_finite_of_matrix_ne_zero
    (since := "2026-07-22")]
theorem conditionalMinEntropyE_eq_coe_of_matrix_ne_zero
    {ρ : SubnormalizedState (Prod a b)} (hρ : ρ.matrix ≠ 0) :
    ρ.conditionalMinEntropy = (ρ.conditionalMinEntropyFinite hρ : EReal) :=
  ρ.conditionalMinEntropy_eq_coe_finite_of_matrix_ne_zero hρ

@[deprecated conditionalMaxEntropy_eq_coe_finite_of_matrix_ne_zero
    (since := "2026-07-22")]
theorem conditionalMaxEntropyE_eq_coe_of_matrix_ne_zero
    {ρ : SubnormalizedState (Prod a b)} (hρ : ρ.matrix ≠ 0) :
    ρ.conditionalMaxEntropy = (ρ.conditionalMaxEntropyFinite hρ : EReal) :=
  ρ.conditionalMaxEntropy_eq_coe_finite_of_matrix_ne_zero hρ

theorem conditionalMinEntropy_eq_coe_finite_of_trace_pos
    {ρ : SubnormalizedState (Prod a b)} (hρ : 0 < ρ.matrix.trace.re) :
    ρ.conditionalMinEntropy =
      (ρ.conditionalMinEntropyFinite
        (by intro hzero; rw [hzero] at hρ; simp at hρ) : EReal) := by
  apply ρ.conditionalMinEntropy_eq_coe_finite_of_matrix_ne_zero

theorem conditionalMaxEntropy_eq_coe_finite_of_trace_pos
    {ρ : SubnormalizedState (Prod a b)} (hρ : 0 < ρ.matrix.trace.re) :
    ρ.conditionalMaxEntropy =
      (ρ.conditionalMaxEntropyFinite
        (by intro hzero; rw [hzero] at hρ; simp at hρ) : EReal) := by
  apply ρ.conditionalMaxEntropy_eq_coe_finite_of_matrix_ne_zero

theorem conditionalMinEntropy_eq_coe_finite_of_purifiedBall_lt_sqrt_trace
    {ρ ρ' : SubnormalizedState (Prod a b)} {ε : ℝ}
    (hball : ρ.purifiedBall ε ρ') (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    ∃ hρ' : ρ'.matrix ≠ 0,
      ρ'.conditionalMinEntropy = (ρ'.conditionalMinEntropyFinite hρ' : EReal) := by
  have hpos := SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace ρ ρ' hε hball
  let hne : ρ'.matrix ≠ 0 := by
    intro hzero
    rw [hzero] at hpos
    simp at hpos
  exact ⟨hne, ρ'.conditionalMinEntropy_eq_coe_finite_of_matrix_ne_zero hne⟩

theorem conditionalMaxEntropy_eq_coe_finite_of_purifiedBall_lt_sqrt_trace
    {ρ ρ' : SubnormalizedState (Prod a b)} {ε : ℝ}
    (hball : ρ.purifiedBall ε ρ') (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    ∃ hρ' : ρ'.matrix ≠ 0,
      ρ'.conditionalMaxEntropy = (ρ'.conditionalMaxEntropyFinite hρ' : EReal) := by
  have hpos := SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace ρ ρ' hε hball
  let hne : ρ'.matrix ≠ 0 := by
    intro hzero
    rw [hzero] at hpos
    simp at hpos
  exact ⟨hne, ρ'.conditionalMaxEntropy_eq_coe_finite_of_matrix_ne_zero hne⟩

/-- A subnormalized conditional min-entropy is uniformly bounded above when the
state trace has a positive lower bound. -/
theorem conditionalMinEntropy_le_of_trace_lower_bound
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {δ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ.matrix.trace.re) :
    ρ.conditionalMinEntropyRaw ≤ log2 (Fintype.card a : ℝ) - log2 δ := by
  have hρ : 0 < ρ.matrix.trace.re := lt_of_lt_of_le hδ hδρ
  rw [← SubnormalizedState.ofStateScale_normalize_trace_eq ρ hρ]
  rw [conditionalMinEntropy_ofStateScale
    (a := a) (b := b) (ρ.normalize hρ.ne') hρ ρ.trace_le_one]
  have hnorm :
      (ρ.normalize hρ.ne').conditionalMinEntropy ≤ log2 (Fintype.card a : ℝ) :=
    (ρ.normalize hρ.ne').conditionalMinEntropy_le_log2_card_left (a := a) (b := b)
  have hlog :
      log2 δ ≤ log2 ρ.matrix.trace.re := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hδ hδρ) (le_of_lt (Real.log_pos one_lt_two))
  linarith

/-- A subnormalized conditional max-entropy is uniformly bounded below when the
state trace has a positive lower bound. -/
theorem conditionalMaxEntropy_ge_of_trace_lower_bound
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {δ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ.matrix.trace.re) :
    -log2 (Fintype.card a : ℝ) + log2 δ ≤ ρ.conditionalMaxEntropyRaw := by
  have hρ : 0 < ρ.matrix.trace.re := lt_of_lt_of_le hδ hδρ
  rw [← SubnormalizedState.ofStateScale_normalize_trace_eq ρ hρ]
  rw [conditionalMaxEntropy_ofStateScale
    (a := a) (b := b) (ρ.normalize hρ.ne') hρ ρ.trace_le_one]
  have hnorm :
      -log2 (Fintype.card a : ℝ) ≤ (ρ.normalize hρ.ne').conditionalMaxEntropy :=
    (ρ.normalize hρ.ne').neg_log2_card_left_le_conditionalMaxEntropy (a := a) (b := b)
  have hlog :
      log2 δ ≤ log2 ρ.matrix.trace.re := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hδ hδρ) (le_of_lt (Real.log_pos one_lt_two))
  linarith

/-- Smooth subnormalized min-entropy candidate sets are nonempty for
nonnegative smoothing radius. -/
theorem SmoothConditionalMinEntropyCandidateRaw_set_nonempty_of_nonneg
    (ρ : SubnormalizedState (Prod a b)) {ε : ℝ} (hε : 0 ≤ ε) :
    ({h : ℝ | SmoothConditionalMinEntropyCandidateRaw (a := a) ρ ε h}).Nonempty :=
  ⟨ρ.conditionalMinEntropyRaw, ρ, ρ.purifiedBall_self_of_nonneg hε, rfl⟩

/-- Smooth subnormalized max-entropy candidate sets are nonempty for
nonnegative smoothing radius. -/
theorem SmoothConditionalMaxEntropyCandidateRaw_set_nonempty_of_nonneg
    (ρ : SubnormalizedState (Prod a b)) {ε : ℝ} (hε : 0 ≤ ε) :
    ({h : ℝ | SmoothConditionalMaxEntropyCandidateRaw (a := a) ρ ε h}).Nonempty :=
  ⟨ρ.conditionalMaxEntropyRaw, ρ, ρ.purifiedBall_self_of_nonneg hε, rfl⟩

/-- Smooth subnormalized min-entropy candidates are bounded above in any ball
whose radius is below `sqrt (Tr ρ)`. -/
theorem SmoothConditionalMinEntropyCandidateRaw_bddAbove_of_lt_sqrt_trace
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε : ℝ}
    (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    BddAbove {h : ℝ |
      SmoothConditionalMinEntropyCandidateRaw (a := a) ρ ε h} := by
  let δ : ℝ := (Real.sqrt ρ.matrix.trace.re - ε) ^ 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact sq_pos_of_pos (sub_pos.mpr hε)
  refine ⟨log2 (Fintype.card a : ℝ) - log2 δ, ?_⟩
  intro h hh
  rcases hh with ⟨ρ', hball, rfl⟩
  have hδρ' : δ ≤ ρ'.matrix.trace.re := by
    dsimp [δ]
    exact ρ.purifiedBall_trace_lower_bound ρ' hε hball
  exact ρ'.conditionalMinEntropy_le_of_trace_lower_bound
    (a := a) (b := b) hδ hδρ'

/-- A subnormalized smooth min-entropy candidate gives a lower bound on the
smooth min-entropy supremum when the usual positive-trace radius guard supplies
boundedness of the candidate set. -/
theorem le_smoothConditionalMinEntropy_of_candidate_of_lt_sqrt_trace
    [Nonempty a] [Nonempty b] {ρ : SubnormalizedState (Prod a b)} {ε h : ℝ}
    (hε_nonneg : 0 ≤ ε)
    (hε : ε < Real.sqrt ρ.matrix.trace.re)
    (hcand : SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := a) ρ ε h) :
    h ≤ ρ.smoothConditionalMinEntropy ε hε_nonneg hε := by
  rw [SubnormalizedState.smoothConditionalMinEntropy_eq_sSup_candidates]
  exact le_csSup
    (SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw_bddAbove_of_lt_sqrt_trace
      (a := a) ρ hε)
    hcand

/-- Smooth conditional min-entropy is monotone in the smoothing radius on its
canonical finite domain. -/
theorem smoothConditionalMinEntropy_mono
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε δ : ℝ}
    (hε_nonneg : 0 ≤ ε) (hδ_nonneg : 0 ≤ δ) (hεδ : ε ≤ δ)
    (hε_trace : ε < Real.sqrt ρ.matrix.trace.re)
    (hδ_trace : δ < Real.sqrt ρ.matrix.trace.re) :
    ρ.smoothConditionalMinEntropy ε hε_nonneg hε_trace ≤
      ρ.smoothConditionalMinEntropy δ hδ_nonneg hδ_trace := by
  rw [SubnormalizedState.smoothConditionalMinEntropy_eq_sSup_candidates,
    SubnormalizedState.smoothConditionalMinEntropy_eq_sSup_candidates]
  refine csSup_le
    (SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw_set_nonempty_of_nonneg
      (a := a) ρ hε_nonneg) ?_
  intro h hh
  exact le_csSup
    (SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw_bddAbove_of_lt_sqrt_trace
      (a := a) ρ hδ_trace)
    (SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw_mono hεδ hh)

/-- Raw smooth conditional min-entropy is monotone whenever the two radii lie
in the canonical finite domain. -/
theorem smoothConditionalMinEntropyRaw_mono_of_nonneg_of_lt_sqrt_trace
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε δ : ℝ}
    (hε_nonneg : 0 ≤ ε) (hδ_nonneg : 0 ≤ δ) (hεδ : ε ≤ δ)
    (hε_trace : ε < Real.sqrt ρ.matrix.trace.re)
    (hδ_trace : δ < Real.sqrt ρ.matrix.trace.re) :
    ρ.smoothConditionalMinEntropyRaw ε ≤
      ρ.smoothConditionalMinEntropyRaw δ := by
  simpa only [SubnormalizedState.smoothConditionalMinEntropy_eq_raw] using
    ρ.smoothConditionalMinEntropy_mono hε_nonneg hδ_nonneg hεδ
      hε_trace hδ_trace

/-- Smooth subnormalized max-entropy candidates are bounded below in any ball
whose radius is below `sqrt (Tr ρ)`. -/
theorem SmoothConditionalMaxEntropyCandidateRaw_bddBelow_of_lt_sqrt_trace
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε : ℝ}
    (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    BddBelow {h : ℝ |
      SmoothConditionalMaxEntropyCandidateRaw (a := a) ρ ε h} := by
  let δ : ℝ := (Real.sqrt ρ.matrix.trace.re - ε) ^ 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact sq_pos_of_pos (sub_pos.mpr hε)
  refine ⟨-log2 (Fintype.card a : ℝ) + log2 δ, ?_⟩
  intro h hh
  rcases hh with ⟨ρ', hball, rfl⟩
  have hδρ' : δ ≤ ρ'.matrix.trace.re := by
    dsimp [δ]
    exact ρ.purifiedBall_trace_lower_bound ρ' hε hball
  exact ρ'.conditionalMaxEntropy_ge_of_trace_lower_bound
    (a := a) (b := b) hδ hδρ'

/-- A pointwise lift of smooth min-entropy candidates controls the corresponding
smooth min-entropy suprema. This isolates the order-theoretic endpoint step from
the concrete witness-lifting construction. -/
theorem smoothConditionalMinEntropyRaw_le_of_candidate_lift
    {source : Type w} [Fintype source] [DecidableEq source]
    (ρpost : SubnormalizedState (Prod a b))
    (ρsource : SubnormalizedState (Prod source b)) {ε : ℝ}
    (hpost_nonempty :
      ({h : ℝ | SmoothConditionalMinEntropyCandidateRaw (a := a) ρpost ε h}).Nonempty)
    (hsource_bdd :
      BddAbove {h : ℝ |
        SmoothConditionalMinEntropyCandidateRaw (a := source) ρsource ε h})
    (hlift : ∀ h,
      SmoothConditionalMinEntropyCandidateRaw (a := a) ρpost ε h →
        ∃ h',
          SmoothConditionalMinEntropyCandidateRaw (a := source) ρsource ε h' ∧ h ≤ h') :
    ρpost.smoothConditionalMinEntropyRaw ε ≤
      ρsource.smoothConditionalMinEntropyRaw ε := by
  rw [smoothConditionalMinEntropyRaw_eq_sSup_candidates,
    smoothConditionalMinEntropyRaw_eq_sSup_candidates]
  refine csSup_le hpost_nonempty ?_
  intro h hh
  rcases hlift h hh with ⟨h', hh', hle⟩
  exact hle.trans (le_csSup hsource_bdd hh')

/-- A pointwise lift of smooth min-entropy candidates controls smooth
min-entropy suprema even when the conditioning registers differ. This is the
same order-theoretic endpoint as
`smoothConditionalMinEntropyRaw_le_of_candidate_lift`, with the source side type
kept independent. -/
theorem smoothConditionalMinEntropyRaw_le_of_candidate_lift_diff_side
    {source : Type w} {c : Type x} [Fintype source] [DecidableEq source]
    [Fintype c] [DecidableEq c]
    (ρpost : SubnormalizedState (Prod a b))
    (ρsource : SubnormalizedState (Prod source c)) {ε : ℝ}
    (hpost_nonempty :
      ({h : ℝ | SmoothConditionalMinEntropyCandidateRaw (a := a) ρpost ε h}).Nonempty)
    (hsource_bdd :
      BddAbove {h : ℝ |
        SmoothConditionalMinEntropyCandidateRaw (a := source) ρsource ε h})
    (hlift : ∀ h,
      SmoothConditionalMinEntropyCandidateRaw (a := a) ρpost ε h →
        ∃ h',
          SmoothConditionalMinEntropyCandidateRaw (a := source) ρsource ε h' ∧ h ≤ h') :
    ρpost.smoothConditionalMinEntropyRaw ε ≤
      ρsource.smoothConditionalMinEntropyRaw ε := by
  rw [smoothConditionalMinEntropyRaw_eq_sSup_candidates,
    smoothConditionalMinEntropyRaw_eq_sSup_candidates]
  refine csSup_le hpost_nonempty ?_
  intro h hh
  rcases hlift h hh with ⟨h', hh', hle⟩
  exact hle.trans (le_csSup hsource_bdd hh')

/-- A convenient small-radius form of
`smoothConditionalMinEntropyRaw_le_of_candidate_lift`, discharging the usual
nonempty and boundedness side conditions from the existing smooth-entropy API. -/
theorem smoothConditionalMinEntropyRaw_le_of_candidate_lift_of_lt_sqrt_trace
    {source : Type w} [Fintype source] [DecidableEq source]
    [Nonempty source] [Nonempty b]
    (ρpost : SubnormalizedState (Prod a b))
    (ρsource : SubnormalizedState (Prod source b)) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hεsource : ε < Real.sqrt ρsource.matrix.trace.re)
    (hlift : ∀ h,
      SmoothConditionalMinEntropyCandidateRaw (a := a) ρpost ε h →
        ∃ h',
          SmoothConditionalMinEntropyCandidateRaw (a := source) ρsource ε h' ∧ h ≤ h') :
    ρpost.smoothConditionalMinEntropyRaw ε ≤
      ρsource.smoothConditionalMinEntropyRaw ε :=
  smoothConditionalMinEntropyRaw_le_of_candidate_lift ρpost ρsource
    (SmoothConditionalMinEntropyCandidateRaw_set_nonempty_of_nonneg (a := a) ρpost hε0)
    (SmoothConditionalMinEntropyCandidateRaw_bddAbove_of_lt_sqrt_trace
      (a := source) ρsource hεsource)
    hlift

/-- Small-radius form of
`smoothConditionalMinEntropyRaw_le_of_candidate_lift_diff_side`. -/
theorem smoothConditionalMinEntropyRaw_le_of_candidate_lift_diff_side_of_lt_sqrt_trace
    {source : Type w} {c : Type x} [Fintype source] [DecidableEq source]
    [Fintype c] [DecidableEq c] [Nonempty source] [Nonempty c]
    (ρpost : SubnormalizedState (Prod a b))
    (ρsource : SubnormalizedState (Prod source c)) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hεsource : ε < Real.sqrt ρsource.matrix.trace.re)
    (hlift : ∀ h,
      SmoothConditionalMinEntropyCandidateRaw (a := a) ρpost ε h →
        ∃ h',
          SmoothConditionalMinEntropyCandidateRaw (a := source) ρsource ε h' ∧ h ≤ h') :
    ρpost.smoothConditionalMinEntropyRaw ε ≤
      ρsource.smoothConditionalMinEntropyRaw ε :=
  smoothConditionalMinEntropyRaw_le_of_candidate_lift_diff_side ρpost ρsource
    (SmoothConditionalMinEntropyCandidateRaw_set_nonempty_of_nonneg (a := a) ρpost hε0)
    (SmoothConditionalMinEntropyCandidateRaw_bddAbove_of_lt_sqrt_trace
      (a := source) ρsource hεsource)
    hlift

/-- A witness-level lift of smooth min-entropy candidates controls the
corresponding smooth min-entropy suprema. The hypothesis is phrased directly in
terms of nearby states and ordinary conditional min-entropy values. -/
theorem smoothConditionalMinEntropyRaw_le_of_witness_lift
    {source : Type w} [Fintype source] [DecidableEq source]
    (ρpost : SubnormalizedState (Prod a b))
    (ρsource : SubnormalizedState (Prod source b)) {ε : ℝ}
    (hpost_nonempty :
      ({h : ℝ | SmoothConditionalMinEntropyCandidateRaw (a := a) ρpost ε h}).Nonempty)
    (hsource_bdd :
      BddAbove {h : ℝ |
        SmoothConditionalMinEntropyCandidateRaw (a := source) ρsource ε h})
    (hlift : ∀ ρpost',
      ρpost.purifiedBall ε ρpost' →
        ∃ ρsource',
          ρsource.purifiedBall ε ρsource' ∧
          ρpost'.conditionalMinEntropyRaw ≤ ρsource'.conditionalMinEntropyRaw) :
    ρpost.smoothConditionalMinEntropyRaw ε ≤
      ρsource.smoothConditionalMinEntropyRaw ε := by
  refine smoothConditionalMinEntropyRaw_le_of_candidate_lift ρpost ρsource
    hpost_nonempty hsource_bdd ?_
  intro h hcand
  rcases hcand with ⟨ρpost', hball, rfl⟩
  rcases hlift ρpost' hball with ⟨ρsource', hsourceball, hle⟩
  exact ⟨ρsource'.conditionalMinEntropyRaw, ⟨ρsource', hsourceball, rfl⟩, hle⟩

/-- Witness-level lift for smooth min-entropy suprema with different
conditioning-register types. -/
theorem smoothConditionalMinEntropyRaw_le_of_witness_lift_diff_side
    {source : Type w} {c : Type x} [Fintype source] [DecidableEq source]
    [Fintype c] [DecidableEq c]
    (ρpost : SubnormalizedState (Prod a b))
    (ρsource : SubnormalizedState (Prod source c)) {ε : ℝ}
    (hpost_nonempty :
      ({h : ℝ | SmoothConditionalMinEntropyCandidateRaw (a := a) ρpost ε h}).Nonempty)
    (hsource_bdd :
      BddAbove {h : ℝ |
        SmoothConditionalMinEntropyCandidateRaw (a := source) ρsource ε h})
    (hlift : ∀ ρpost',
      ρpost.purifiedBall ε ρpost' →
        ∃ ρsource',
          ρsource.purifiedBall ε ρsource' ∧
          ρpost'.conditionalMinEntropyRaw ≤ ρsource'.conditionalMinEntropyRaw) :
    ρpost.smoothConditionalMinEntropyRaw ε ≤
      ρsource.smoothConditionalMinEntropyRaw ε := by
  refine smoothConditionalMinEntropyRaw_le_of_candidate_lift_diff_side ρpost ρsource
    hpost_nonempty hsource_bdd ?_
  intro h hcand
  rcases hcand with ⟨ρpost', hball, rfl⟩
  rcases hlift ρpost' hball with ⟨ρsource', hsourceball, hle⟩
  exact ⟨ρsource'.conditionalMinEntropyRaw, ⟨ρsource', hsourceball, rfl⟩, hle⟩

/-- A convenient small-radius form of
`smoothConditionalMinEntropyRaw_le_of_witness_lift`, discharging the usual
nonempty and boundedness side conditions from the existing smooth-entropy API. -/
theorem smoothConditionalMinEntropyRaw_le_of_witness_lift_of_lt_sqrt_trace
    {source : Type w} [Fintype source] [DecidableEq source]
    [Nonempty source] [Nonempty b]
    (ρpost : SubnormalizedState (Prod a b))
    (ρsource : SubnormalizedState (Prod source b)) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hεsource : ε < Real.sqrt ρsource.matrix.trace.re)
    (hlift : ∀ ρpost',
      ρpost.purifiedBall ε ρpost' →
        ∃ ρsource',
          ρsource.purifiedBall ε ρsource' ∧
          ρpost'.conditionalMinEntropyRaw ≤ ρsource'.conditionalMinEntropyRaw) :
    ρpost.smoothConditionalMinEntropyRaw ε ≤
      ρsource.smoothConditionalMinEntropyRaw ε :=
  smoothConditionalMinEntropyRaw_le_of_witness_lift ρpost ρsource
    (SmoothConditionalMinEntropyCandidateRaw_set_nonempty_of_nonneg (a := a) ρpost hε0)
    (SmoothConditionalMinEntropyCandidateRaw_bddAbove_of_lt_sqrt_trace
      (a := source) ρsource hεsource)
    hlift

/-- Small-radius form of
`smoothConditionalMinEntropyRaw_le_of_witness_lift_diff_side`. -/
theorem smoothConditionalMinEntropyRaw_le_of_witness_lift_diff_side_of_lt_sqrt_trace
    {source : Type w} {c : Type x} [Fintype source] [DecidableEq source]
    [Fintype c] [DecidableEq c] [Nonempty source] [Nonempty c]
    (ρpost : SubnormalizedState (Prod a b))
    (ρsource : SubnormalizedState (Prod source c)) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hεsource : ε < Real.sqrt ρsource.matrix.trace.re)
    (hlift : ∀ ρpost',
      ρpost.purifiedBall ε ρpost' →
        ∃ ρsource',
          ρsource.purifiedBall ε ρsource' ∧
          ρpost'.conditionalMinEntropyRaw ≤ ρsource'.conditionalMinEntropyRaw) :
    ρpost.smoothConditionalMinEntropyRaw ε ≤
      ρsource.smoothConditionalMinEntropyRaw ε :=
  smoothConditionalMinEntropyRaw_le_of_witness_lift_diff_side ρpost ρsource
    (SmoothConditionalMinEntropyCandidateRaw_set_nonempty_of_nonneg (a := a) ρpost hε0)
    (SmoothConditionalMinEntropyCandidateRaw_bddAbove_of_lt_sqrt_trace
      (a := source) ρsource hεsource)
    hlift

/-- Subnormalized smooth conditional min-entropy is invariant under arbitrary
conditioning-register reference isometries, with the same smoothing radius and
no regularization. -/
theorem smoothConditionalMinEntropy_conditioningIsometryApply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    [Nonempty a] [Nonempty b] [Nonempty bPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry b bPlus) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    (ρ.conditioningIsometryApply V).smoothConditionalMinEntropy ε hε0
        (by rwa [conditioningIsometryApply_trace_re]) =
      ρ.smoothConditionalMinEntropy ε hε0 hε := by
  change sSup {h : ℝ |
      SmoothConditionalMinEntropyCandidateRaw (a := a) (ρ.conditioningIsometryApply V) ε h} =
    sSup {h : ℝ | SmoothConditionalMinEntropyCandidateRaw (a := a) ρ ε h}
  have hεPlus :
      ε < Real.sqrt (ρ.conditioningIsometryApply V).matrix.trace.re := by
    rwa [conditioningIsometryApply_trace_re]
  have hbddSource :
      BddAbove {h : ℝ | SmoothConditionalMinEntropyCandidateRaw (a := a) ρ ε h} :=
    SmoothConditionalMinEntropyCandidateRaw_bddAbove_of_lt_sqrt_trace
      (a := a) ρ hε
  have hbddPlus :
      BddAbove {h : ℝ |
        SmoothConditionalMinEntropyCandidateRaw (a := a)
          (ρ.conditioningIsometryApply V) ε h} :=
    SmoothConditionalMinEntropyCandidateRaw_bddAbove_of_lt_sqrt_trace
      (a := a) (ρ.conditioningIsometryApply V) hεPlus
  have hnonSource :
      ({h : ℝ | SmoothConditionalMinEntropyCandidateRaw (a := a) ρ ε h}).Nonempty :=
    SmoothConditionalMinEntropyCandidateRaw_set_nonempty_of_nonneg
      (a := a) ρ hε0
  have hnonPlus :
      ({h : ℝ |
        SmoothConditionalMinEntropyCandidateRaw (a := a)
          (ρ.conditioningIsometryApply V) ε h}).Nonempty :=
    SmoothConditionalMinEntropyCandidateRaw_set_nonempty_of_nonneg
      (a := a) (ρ.conditioningIsometryApply V) hε0
  apply le_antisymm
  · refine csSup_le hnonPlus ?_
    intro h hh
    rcases SmoothConditionalMinEntropyCandidateRaw.conditioningIsometryApply_compress
        (a := a) ρ V hε hh with ⟨h', hh', hle⟩
    exact le_trans hle (le_csSup hbddSource hh')
  · refine csSup_le hnonSource ?_
    intro h hh
    exact le_csSup hbddPlus
      (SmoothConditionalMinEntropyCandidateRaw.conditioningIsometryApply
        (a := a) ρ V hε hh)

/-- Subnormalized smooth conditional min-entropy is invariant under arbitrary
source-register reference isometries, with the same smoothing radius and no
regularization. -/
theorem smoothConditionalMinEntropy_sourceIsometryApply
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    [Nonempty a] [Nonempty b] [Nonempty aPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry a aPlus) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    (ρ.sourceIsometryApply V).smoothConditionalMinEntropy ε hε0
        (by rwa [sourceIsometryApply_trace_re]) =
      ρ.smoothConditionalMinEntropy ε hε0 hε := by
  change sSup {h : ℝ |
      SmoothConditionalMinEntropyCandidateRaw (a := aPlus) (ρ.sourceIsometryApply V) ε h} =
    sSup {h : ℝ | SmoothConditionalMinEntropyCandidateRaw (a := a) ρ ε h}
  have hεPlus :
      ε < Real.sqrt (ρ.sourceIsometryApply V).matrix.trace.re := by
    rwa [sourceIsometryApply_trace_re]
  have hbddSource :
      BddAbove {h : ℝ | SmoothConditionalMinEntropyCandidateRaw (a := a) ρ ε h} :=
    SmoothConditionalMinEntropyCandidateRaw_bddAbove_of_lt_sqrt_trace
      (a := a) ρ hε
  have hbddPlus :
      BddAbove {h : ℝ |
        SmoothConditionalMinEntropyCandidateRaw (a := aPlus)
          (ρ.sourceIsometryApply V) ε h} :=
    SmoothConditionalMinEntropyCandidateRaw_bddAbove_of_lt_sqrt_trace
      (a := aPlus) (ρ.sourceIsometryApply V) hεPlus
  have hnonSource :
      ({h : ℝ | SmoothConditionalMinEntropyCandidateRaw (a := a) ρ ε h}).Nonempty :=
    SmoothConditionalMinEntropyCandidateRaw_set_nonempty_of_nonneg
      (a := a) ρ hε0
  have hnonPlus :
      ({h : ℝ |
        SmoothConditionalMinEntropyCandidateRaw (a := aPlus)
          (ρ.sourceIsometryApply V) ε h}).Nonempty :=
    SmoothConditionalMinEntropyCandidateRaw_set_nonempty_of_nonneg
      (a := aPlus) (ρ.sourceIsometryApply V) hε0
  apply le_antisymm
  · refine csSup_le hnonPlus ?_
    intro h hh
    rcases SmoothConditionalMinEntropyCandidateRaw.sourceIsometryApply_compress
        (a := a) ρ V hε hh with ⟨h', hh', hle⟩
    exact le_trans hle (le_csSup hbddSource hh')
  · refine csSup_le hnonSource ?_
    intro h hh
    exact le_csSup hbddPlus
      (SmoothConditionalMinEntropyCandidateRaw.sourceIsometryApply
        (a := a) ρ V hε hh)

/-- Transport the scaled-pure radius condition to the `AB` marginal trace. -/
theorem epsilon_lt_sqrt_trace_abMarginalFromScaledTripartitePure
    (ψ : PureVector (Prod (Prod a b) c)) {t ε : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hε : ε < Real.sqrt t) :
    ε < Real.sqrt
      (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht.le ht1).matrix.trace.re := by
  simpa [abMarginalFromScaledTripartitePure] using
    (show ε < Real.sqrt
        (ofStateScale ψ.state.marginalAB t ht.le ht1).matrix.trace.re by
      rwa [ofStateScale_trace_re])

/-- Transport the scaled-pure radius condition to the `AC` marginal trace. -/
theorem epsilon_lt_sqrt_trace_acMarginalFromScaledTripartitePure
    (ψ : PureVector (Prod (Prod a b) c)) {t ε : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hε : ε < Real.sqrt t) :
    ε < Real.sqrt
      (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht.le ht1).matrix.trace.re := by
  simpa [acMarginalFromScaledTripartitePure] using
    (show ε < Real.sqrt
        (ofStateScale ψ.state.marginalAC t ht.le ht1).matrix.trace.re by
      rwa [ofStateScale_trace_re])

/-- Source-faithful subnormalized smooth min/max duality for a scaled pure
tripartite state.  The public surface is the scaled-pure representation:
`PureVector ψ`, `0 < t`, `t ≤ 1`, `0 ≤ ε`, and `ε < sqrt t`. -/
theorem smoothConditionalMaxEntropy_marginalAB_eq_neg_smoothConditionalMinEntropy_marginalAC_of_scaled_pure
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c)) {t ε : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hε0 : 0 ≤ ε) (hε : ε < Real.sqrt t) :
    (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
      ψ t ht.le ht1).smoothConditionalMaxEntropy ε hε0
        (epsilon_lt_sqrt_trace_abMarginalFromScaledTripartitePure
          (a := a) (b := b) (c := c) ψ ht ht1 hε) =
      - (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht.le ht1).smoothConditionalMinEntropy ε hε0
          (epsilon_lt_sqrt_trace_acMarginalFromScaledTripartitePure
            (a := a) (b := b) (c := c) ψ ht ht1 hε) := by
  classical
  let ρAB : SubnormalizedState (Prod a b) :=
    abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
      ψ t ht.le ht1
  let ρAC : SubnormalizedState (Prod a c) :=
    acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
      ψ t ht.le ht1
  have hABtrace : ρAB.matrix.trace.re = t := by
    simpa [ρAB, abMarginalFromScaledTripartitePure] using
      ofStateScale_trace_re ψ.state.marginalAB t ht.le ht1
  have hACtrace : ρAC.matrix.trace.re = t := by
    simpa [ρAC, acMarginalFromScaledTripartitePure] using
      ofStateScale_trace_re ψ.state.marginalAC t ht.le ht1
  have hεAB : ε < Real.sqrt ρAB.matrix.trace.re := by
    rwa [hABtrace]
  have hεAC : ε < Real.sqrt ρAC.matrix.trace.re := by
    rwa [hACtrace]
  have hpair :
      EmbeddedSmoothConditionalMinMaxPairing (a := a) (b := b) (c := c)
        ψ t ht.le ht1 ε :=
    embeddedSmoothConditionalMinMaxPairing_of_scaled_pure
      (a := a) (b := b) (c := c) ψ t ht.le ht1 ε
  change ρAB.smoothConditionalMaxEntropyRaw ε =
    -ρAC.smoothConditionalMinEntropyRaw ε
  refine smoothConditionalMaxEntropyRaw_eq_neg_smoothConditionalMinEntropyRaw_of_candidate_bounds
    (a := a) (b := b) (c := c)
    (ρAB := ρAB) (ρAC := ρAC) (ε := ε)
    (ρAB.SmoothConditionalMaxEntropyCandidateRaw_set_nonempty_of_nonneg (a := a) hε0)
    (ρAC.SmoothConditionalMinEntropyCandidateRaw_set_nonempty_of_nonneg (a := a) hε0)
    (ρAB.SmoothConditionalMaxEntropyCandidateRaw_bddBelow_of_lt_sqrt_trace (a := a) hεAB)
    (ρAC.SmoothConditionalMinEntropyCandidateRaw_bddAbove_of_lt_sqrt_trace (a := a) hεAC)
    ?_ ?_
  · intro h hcand
    rcases hcand with ⟨ρAB', hballAB, hh⟩
    have hemb :
        EmbeddedABToACSmoothCandidate (a := a) (b := b) (c := c)
          ψ t ht.le ht1 ε ρAB' :=
      hpair.ab_to_ac_of_purifiedBall (a := a) (b := b) (c := c)
        ρAB' (by simpa [ρAB] using hballAB)
    have hρAB' : 0 < ρAB'.matrix.trace.re :=
      SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
        ρAB ρAB' hεAB hballAB
    obtain ⟨ρACPlus', _hballPlus, hrel⟩ :=
      hemb.exists_complementaryPureMarginalRel
        (a := a) (b := b) (c := c) hρAB'
    have hdual :
        ρAB'.conditionalMaxEntropyRaw = -ρACPlus'.conditionalMinEntropyRaw :=
      (conditionalMinMaxEntropyDualOn_complementaryPureMarginals
        (a := a) (b := b) (c := ACPlusReference a b c))
        ρAB' ρACPlus' hrel
    have hbase :
        embeddedACPlusBaseFromScaledPure (a := a) (b := b) (c := c)
          ψ t ht.le ht1 =
          ρAC.conditioningIsometryApply
            (ReferenceIsometry.sumInr (ABHat a b) c) := by
      simpa [ρAC] using
        embeddedACPlusBaseFromScaledPure_eq_conditioningIsometryApply_sumInr
          (a := a) (b := b) (c := c) ψ t ht.le ht1
    have hcandPlus :
        SmoothConditionalMinEntropyCandidateRaw (a := a)
          (ρAC.conditioningIsometryApply
            (ReferenceIsometry.sumInr (ABHat a b) c)) ε (-h) := by
      refine ⟨ρACPlus', ?_, ?_⟩
      · rwa [← hbase]
      · rw [hh, hdual]
        ring
    exact SmoothConditionalMinEntropyCandidateRaw.conditioningIsometryApply_sumInr_compress
      (a := a) (b := c) (extra := ABHat a b) ρAC hεAC hcandPlus
  · intro m hcand
    rcases hcand with ⟨ρAC', hballAC, hm⟩
    have hemb :
        EmbeddedACToABSmoothCandidate (a := a) (b := b) (c := c)
          ψ t ht.le ht1 ε ρAC' :=
      hpair.ac_to_ab_of_purifiedBall (a := a) (b := b) (c := c)
        ρAC' (by simpa [ρAC] using hballAC)
    have hρAC' : 0 < ρAC'.matrix.trace.re :=
      SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
        ρAC ρAC' hεAC hballAC
    obtain ⟨ρABPlus', _hballPlus, hrel⟩ :=
      hemb.exists_complementaryPureMarginalRel
        (a := a) (b := b) (c := c) hρAC'
    have hdual :
        ρABPlus'.conditionalMaxEntropyRaw = -ρAC'.conditionalMinEntropyRaw :=
      (conditionalMinMaxEntropyDualOn_complementaryPureMarginals
        (a := a) (b := ABPlusReference a b c) (c := c))
        ρABPlus' ρAC' hrel
    have hbase :
        embeddedABPlusBaseFromScaledPure (a := a) (b := b) (c := c)
          ψ t ht.le ht1 =
          ρAB.conditioningIsometryApply
            (ReferenceIsometry.sumInr (ACHat a c) b) := by
      simpa [ρAB] using
        embeddedABPlusBaseFromScaledPure_eq_conditioningIsometryApply_sumInr
          (a := a) (b := b) (c := c) ψ t ht.le ht1
    have hcandPlus :
        SmoothConditionalMaxEntropyCandidateRaw (a := a)
          (ρAB.conditioningIsometryApply
            (ReferenceIsometry.sumInr (ACHat a c) b)) ε (-m) := by
      refine ⟨ρABPlus', ?_, ?_⟩
      · rwa [← hbase]
      · rw [hm, hdual]
    exact SmoothConditionalMaxEntropyCandidateRaw.conditioningIsometryApply_sumInr_compress
      (a := a) (b := b) (extra := ACHat a c) ρAB hεAB hcandPlus

end SubnormalizedState

end

end QIT
