/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.SmoothEndpoint.Companion

/-!
# Discarding a finite source register in smooth conditional min-entropy

This module proves the finite-dimensional source-register chain rule used in
step (iv) of the one-shot state-merging converse in
[Berta2009SingleShotStateMerging, diploma_thesis_berta_08_v1.tex:881-902].

For a subnormalized state on `(K x A) x B`, tracing out `K` increases the
conditional min-entropy by at most `log2 |K|`.  The smooth statement transports
nearby states through the same CPTP discard map, using contraction of purified
distance.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u v w

noncomputable section

namespace SubnormalizedState

variable {k : Type u} {a : Type v} {b : Type w}
variable [Fintype k] [DecidableEq k]
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

/-- Reassociate `(K x A) x B` as `K x (A x B)` using the canonical reindexing
channel. -/
def sourceAssocReindex (rho : SubnormalizedState (Prod (Prod k a) b)) :
    SubnormalizedState (Prod k (Prod a b)) :=
  rho.applyTraceNonincreasingCP
    (Channel.reindex (Equiv.prodAssoc k a b)).map
    (Channel.reindex (Equiv.prodAssoc k a b)).traceNonincreasingCP_map

/-- Trace out the first source factor `K` from a state on `(K x A) x B`. -/
def sourceDiscard (rho : SubnormalizedState (Prod (Prod k a) b)) :
    SubnormalizedState (Prod a b) :=
  rho.sourceAssocReindex.marginalB

@[simp]
theorem sourceAssocReindex_matrix (rho : SubnormalizedState (Prod (Prod k a) b)) :
    rho.sourceAssocReindex.matrix =
      rho.matrix.submatrix (Equiv.prodAssoc k a b).symm
        (Equiv.prodAssoc k a b).symm := by
  ext i j
  simp [sourceAssocReindex, Channel.reindex, MatrixMap.ofReferenceIsometry_apply,
    ReferenceIsometry.ofEquiv, Matrix.mul_apply]
  rw [Finset.sum_eq_single ((Equiv.prodAssoc k a b).symm j)]
  · rw [Finset.sum_eq_single ((Equiv.prodAssoc k a b).symm i)]
    · simp
    · intro x _ hx
      have hne : i ≠ (Equiv.prodAssoc k a b) x := by
        intro hi
        apply hx
        simp [hi]
      rw [if_neg]
      intro hi
      exact hne (by simpa [Equiv.prodAssoc] using hi)
    · simp
  · intro x _ hx
    have hne : j ≠ (Equiv.prodAssoc k a b) x := by
      intro hj
      apply hx
      simp [hj]
    rw [if_neg]
    intro hj
    exact hne (by simpa [Equiv.prodAssoc] using hj)
  · simp

@[simp]
theorem sourceDiscard_matrix (rho : SubnormalizedState (Prod (Prod k a) b)) :
    rho.sourceDiscard.matrix =
      partialTraceA (a := k) (b := Prod a b)
        (rho.matrix.submatrix (Equiv.prodAssoc k a b).symm
          (Equiv.prodAssoc k a b).symm) := by
  simp [sourceDiscard]

@[simp]
theorem sourceAssocReindex_trace_re (rho : SubnormalizedState (Prod (Prod k a) b)) :
    rho.sourceAssocReindex.matrix.trace.re = rho.matrix.trace.re := by
  rw [sourceAssocReindex_matrix]
  congr 1
  rw [Matrix.trace]
  apply Fintype.sum_equiv (Equiv.prodAssoc k a b).symm
  intro x
  rfl

@[simp]
theorem sourceDiscard_trace_re (rho : SubnormalizedState (Prod (Prod k a) b)) :
    rho.sourceDiscard.matrix.trace.re = rho.matrix.trace.re := by
  rw [sourceDiscard, marginalB_matrix, partialTraceA_trace,
    sourceAssocReindex_trace_re]

/-- Discarding the first source factor contracts purified distance. -/
theorem purifiedDistance_sourceDiscard_le
    (rho sigma : SubnormalizedState (Prod (Prod k a) b)) :
    rho.sourceDiscard.purifiedDistance sigma.sourceDiscard <=
      rho.purifiedDistance sigma := by
  refine le_trans (SubnormalizedState.purifiedDistance_marginalB_le
    rho.sourceAssocReindex sigma.sourceAssocReindex) ?_
  simpa [sourceAssocReindex] using
    SubnormalizedState.purifiedDistance_mono_traceNonincreasingCP rho sigma
      (Channel.reindex (Equiv.prodAssoc k a b)).map
      (Channel.reindex (Equiv.prodAssoc k a b)).traceNonincreasingCP_map

/-- Purified-distance balls are preserved when the first source factor is
discarded. -/
theorem purifiedBall_sourceDiscard_of_purifiedBall
    {rho sigma : SubnormalizedState (Prod (Prod k a) b)} {epsilon : Real}
    (hball : rho.purifiedBall epsilon sigma) :
    rho.sourceDiscard.purifiedBall epsilon sigma.sourceDiscard :=
  le_trans (purifiedDistance_sourceDiscard_le rho sigma) hball

omit [DecidableEq k] [DecidableEq a] [DecidableEq b] in
private theorem partialTraceA_mono_sourceDiscard
    {X Y : CMatrix (Prod k (Prod a b))} (hXY : X <= Y) :
    partialTraceA (a := k) (b := Prod a b) X <=
      partialTraceA (a := k) (b := Prod a b) Y := by
  rw [Matrix.le_iff] at hXY ⊢
  have hpos := partialTraceA_posSemidef (a := k) (b := Prod a b) hXY
  convert hpos using 1
  ext i j
  simp [partialTraceA, Matrix.sub_apply, Finset.sum_sub_distrib]

omit [Fintype a] [Fintype b] [DecidableEq b] in
private theorem partialTraceA_assoc_identityTensor
    (T : CMatrix b) :
    partialTraceA (a := k) (b := Prod a b)
        ((Matrix.kronecker (1 : CMatrix (Prod k a)) T).submatrix
          (Equiv.prodAssoc k a b).symm (Equiv.prodAssoc k a b).symm) =
      (Fintype.card k : Real) • Matrix.kronecker (1 : CMatrix a) T := by
  ext i j
  rcases i with ⟨iA, iB⟩
  rcases j with ⟨jA, jB⟩
  simp [partialTraceA, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Equiv.prodAssoc, Matrix.one_apply]

/-- A feasible side operator for `(K x A)|B` remains feasible after discarding
`K` when it is multiplied by the source dimension. -/
theorem ConditionalMinEntropyScaleFeasible.sourceDiscard
    {rho : SubnormalizedState (Prod (Prod k a) b)} {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := Prod k a) rho T) :
    ConditionalMinEntropyScaleFeasible (a := a) rho.sourceDiscard
      ((Fintype.card k : Real) • T) := by
  constructor
  · exact Matrix.PosSemidef.smul hT.1 (Nat.cast_nonneg (Fintype.card k))
  · have hAssoc :
        rho.sourceAssocReindex.matrix <=
          (Matrix.kronecker (1 : CMatrix (Prod k a)) T).submatrix
            (Equiv.prodAssoc k a b).symm (Equiv.prodAssoc k a b).symm := by
      rw [sourceAssocReindex_matrix, Matrix.le_iff] at ⊢
      exact hT.2.submatrix (Equiv.prodAssoc k a b).symm
    have hPartial := partialTraceA_mono_sourceDiscard (a := a) (b := b) hAssoc
    change partialTraceA (a := k) (b := Prod a b) rho.sourceAssocReindex.matrix <=
      Matrix.kronecker (1 : CMatrix a) ((Fintype.card k : Real) • T)
    rw [partialTraceA_assoc_identityTensor (k := k) (a := a) (b := b)] at hPartial
    simpa [Matrix.kronecker_smul] using hPartial

/-- The conditional-min endpoint scale after discarding `K` is at most
`|K|` times the original endpoint scale. -/
theorem conditionalMinEntropyScale_sourceDiscard_le_card_mul
    [Nonempty k] (rho : SubnormalizedState (Prod (Prod k a) b)) :
    rho.sourceDiscard.conditionalMinEntropyScale (a := a) <=
      (Fintype.card k : Real) * rho.conditionalMinEntropyScale (a := Prod k a) := by
  let d : Real := Fintype.card k
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hdiv :
      rho.sourceDiscard.conditionalMinEntropyScale (a := a) / d <=
        rho.conditionalMinEntropyScale (a := Prod k a) := by
    rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
    refine le_csInf
      (rho.conditionalMinEntropyScaleValueSet_nonempty (a := Prod k a)) ?_
    intro t ht
    rcases ht with ⟨T, hT, rfl⟩
    apply (div_le_iff₀ hd).2
    have hbdd :
        BddBelow (rho.sourceDiscard.conditionalMinEntropyScaleValueSet (a := a)) :=
      rho.sourceDiscard.conditionalMinEntropyScaleValueSet_bddBelow (a := a)
    have hmem : d * T.trace.re ∈
        rho.sourceDiscard.conditionalMinEntropyScaleValueSet (a := a) := by
      refine ⟨d • T, ?_, ?_⟩
      · simpa [d] using hT.sourceDiscard (k := k) (a := a) (b := b)
      · simp [Matrix.trace_smul, Complex.real_smul]
    simpa [mul_comm] using (csInf_le hbdd hmem)
  have hmul := (div_le_iff₀ hd).1 hdiv
  simpa [d, mul_comm] using hmul

/-- Discarding a finite source register increases subnormalized conditional
min-entropy by at most the logarithm of that register's dimension. -/
theorem conditionalMinEntropyRaw_le_log2_card_add_sourceDiscard
    [Nonempty k] [Nonempty a] [Nonempty b]
    (rho : SubnormalizedState (Prod (Prod k a) b))
    (hrho : 0 < rho.matrix.trace.re) :
    rho.conditionalMinEntropyRaw <=
      log2 (Fintype.card k : Real) + rho.sourceDiscard.conditionalMinEntropyRaw := by
  have hrhoDiscard : 0 < rho.sourceDiscard.matrix.trace.re := by
    rw [sourceDiscard_trace_re]
    exact hrho
  rw [rho.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := Prod k a) hrho,
    rho.sourceDiscard.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a) hrhoDiscard]
  let d : Real := Fintype.card k
  let sourceScale := rho.conditionalMinEntropyScale (a := Prod k a)
  let discardedScale := rho.sourceDiscard.conditionalMinEntropyScale (a := a)
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hsource : 0 < sourceScale := by
    dsimp [sourceScale]
    exact rho.conditionalMinEntropyScale_pos_of_trace_pos (a := Prod k a) hrho
  have hdiscarded : 0 < discardedScale := by
    dsimp [discardedScale]
    exact rho.sourceDiscard.conditionalMinEntropyScale_pos_of_trace_pos
      (a := a) hrhoDiscard
  have hscale : discardedScale <= d * sourceScale := by
    simpa [d, sourceScale, discardedScale] using
      rho.conditionalMinEntropyScale_sourceDiscard_le_card_mul
        (k := k) (a := a) (b := b)
  have hlog : log2 discardedScale <= log2 (d * sourceScale) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hdiscarded hscale) (le_of_lt (Real.log_pos one_lt_two))
  have hlogMul : log2 (d * sourceScale) = log2 d + log2 sourceScale := by
    unfold log2
    rw [Real.log_mul hd.ne' hsource.ne']
    ring
  rw [hlogMul] at hlog
  dsimp [d, sourceScale, discardedScale] at hlog ⊢
  linarith

/-- Finite, source-facing source-discard chain rule.  Positive trace supplies
the nonzero witnesses required by both real-valued entropy accessors. -/
theorem conditionalMinEntropyFinite_le_log2_card_add_sourceDiscard
    [Nonempty k] [Nonempty a] [Nonempty b]
    (rho : SubnormalizedState (Prod (Prod k a) b))
    (hrho : 0 < rho.matrix.trace.re) :
    rho.conditionalMinEntropyFinite (rho.matrix_ne_zero_of_trace_re_pos hrho) <=
      log2 (Fintype.card k : Real) +
        rho.sourceDiscard.conditionalMinEntropyFinite
          (rho.sourceDiscard.matrix_ne_zero_of_trace_re_pos (by
            rwa [sourceDiscard_trace_re])) := by
  simpa [conditionalMinEntropyFinite] using
    rho.conditionalMinEntropyRaw_le_log2_card_add_sourceDiscard
      (k := k) (a := a) (b := b) hrho

/-- Raw smooth source-discard chain rule on the canonical finite radius domain.
Every nearby source state is sent to a nearby discarded state by the same CPTP
map, and the unsmoothed dimension bound is then optimized pointwise. -/
theorem smoothConditionalMinEntropyRaw_le_log2_card_add_sourceDiscard
    [Nonempty k] [Nonempty a] [Nonempty b]
    (rho : SubnormalizedState (Prod (Prod k a) b)) {epsilon : Real}
    (hepsilon0 : 0 <= epsilon)
    (hepsilon : epsilon < Real.sqrt rho.matrix.trace.re) :
    rho.smoothConditionalMinEntropyRaw epsilon <=
      log2 (Fintype.card k : Real) +
        rho.sourceDiscard.smoothConditionalMinEntropyRaw epsilon := by
  rw [smoothConditionalMinEntropyRaw_eq_sSup_candidates]
  refine csSup_le
    (SmoothConditionalMinEntropyCandidateRaw_set_nonempty_of_nonneg
      (a := Prod k a) rho hepsilon0) ?_
  intro h hh
  rcases hh with ⟨rho', hball, rfl⟩
  have hrho' : 0 < rho'.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      rho rho' hepsilon hball
  have hchain :=
    rho'.conditionalMinEntropyRaw_le_log2_card_add_sourceDiscard
      (k := k) (a := a) (b := b) hrho'
  have hepsilonDiscard :
      epsilon < Real.sqrt rho.sourceDiscard.matrix.trace.re := by
    rw [sourceDiscard_trace_re]
    exact hepsilon
  have hdiscardCandidate :
      SmoothConditionalMinEntropyCandidateRaw (a := a) rho.sourceDiscard epsilon
        rho'.sourceDiscard.conditionalMinEntropyRaw :=
    ⟨rho'.sourceDiscard,
      purifiedBall_sourceDiscard_of_purifiedBall hball, rfl⟩
  have hdiscardLe :
      rho'.sourceDiscard.conditionalMinEntropyRaw <=
        rho.sourceDiscard.smoothConditionalMinEntropyRaw epsilon := by
    rw [smoothConditionalMinEntropyRaw_eq_sSup_candidates]
    exact le_csSup
      (SmoothConditionalMinEntropyCandidateRaw_bddAbove_of_lt_sqrt_trace
        (a := a) rho.sourceDiscard hepsilonDiscard)
      hdiscardCandidate
  exact hchain.trans (by
    simpa [add_comm] using
      add_le_add_left hdiscardLe (log2 (Fintype.card k : Real)))

/-- Canonical finite-domain smooth source-discard chain rule. -/
theorem smoothConditionalMinEntropy_le_log2_card_add_sourceDiscard
    [Nonempty k] [Nonempty a] [Nonempty b]
    (rho : SubnormalizedState (Prod (Prod k a) b)) (epsilon : Real)
    (hepsilon0 : 0 <= epsilon)
    (hepsilon : epsilon < Real.sqrt rho.matrix.trace.re) :
    rho.smoothConditionalMinEntropy epsilon hepsilon0 hepsilon <=
      log2 (Fintype.card k : Real) +
        rho.sourceDiscard.smoothConditionalMinEntropy epsilon hepsilon0
          (by rwa [sourceDiscard_trace_re]) := by
  exact rho.smoothConditionalMinEntropyRaw_le_log2_card_add_sourceDiscard
    (k := k) (a := a) (b := b) hepsilon0 hepsilon

end SubnormalizedState

end

end QIT
