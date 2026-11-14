/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Asymptotic.FixedSmoothMinEntropy
public import QIT.OneShot.SmoothComparison

/-!
# Fixed-smoothing fully quantum AEP

This module closes the analysis step from the finite-N AEP to the literal
iterated limit.  For a fixed smoothing radius, the finite-N theorem gives the
lower bound.  Tomamichel's smooth min/max comparison and purification duality
give the matching upper bound, with corrections that vanish after division by
the blocklength.
-/

@[expose] public section

open Filter

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace State

private theorem fixedEpsilon_min_rate_lower_eventually
    (ρ : State (Prod a b)) {ε : ℝ} (hε_pos : 0 < ε) (hε_lt_one : ε < 1) :
    ∀ᶠ n : ℕ in atTop,
      ρ.conditionalEntropy -
          finiteAEPDelta ε ρ.finiteAEPEtaTrace / Real.sqrt (n : ℝ) ≤
        ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
          ε n (le_of_lt hε_pos) hε_lt_one := by
  have hn_ge :
      ∀ᶠ n : ℕ in atTop,
        (8 / 5 : ℝ) * log2 (2 / ε ^ 2) ≤ (n : ℝ) := by
    refine eventually_atTop.2
      ⟨Nat.ceil ((8 / 5 : ℝ) * log2 (2 / ε ^ 2)), ?_⟩
    intro n hn
    exact (Nat.le_ceil ((8 / 5 : ℝ) * log2 (2 / ε ^ 2))).trans
      (by exact_mod_cast hn)
  filter_upwards [hn_ge] with n hn
  exact finiteNAEP_statement_traceEta
    ρ ε (le_of_lt hε_pos) hε_lt_one n hε_pos hn

private theorem fixedEpsilon_min_rate_le_max_rate_add_correction
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) {ε ε' : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hε'0 : 0 ≤ ε') (hε'1 : ε' < 1)
    (hsum : ε + ε' < 1) (n : ℕ) :
    ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
        ε n hε0 hε1 ≤
      ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate
          ε' n hε'0 hε'1 +
        log2 (1 / (1 - (ε + ε') ^ 2)) / (n : ℝ) := by
  have hcomparison :=
    State.smoothConditionalMinEntropy_le_smoothConditionalMaxEntropy_add_epsilonPenalty
      (ρ.tensorPowerBipartite n) hε0 hε1 hε'0 hε'1 hsum
  have hinv : 0 ≤ (1 / (n : ℝ)) := by positivity
  calc
    ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
        ε n hε0 hε1 =
        (1 / (n : ℝ)) *
          (ρ.tensorPowerBipartite n).smoothConditionalMinEntropy ε hε0 hε1 := rfl
    _ ≤ (1 / (n : ℝ)) *
          ((ρ.tensorPowerBipartite n).smoothConditionalMaxEntropy ε' hε'0 hε'1 +
            log2 (1 / (1 - (ε + ε') ^ 2))) :=
      mul_le_mul_of_nonneg_left hcomparison hinv
    _ = ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate
          ε' n hε'0 hε'1 +
        log2 (1 / (1 - (ε + ε') ^ 2)) / (n : ℝ) := by
      change
        (1 / (n : ℝ)) *
            ((ρ.tensorPowerBipartite n).smoothConditionalMaxEntropy ε' hε'0 hε'1 +
              log2 (1 / (1 - (ε + ε') ^ 2))) =
          (1 / (n : ℝ)) *
              (ρ.tensorPowerBipartite n).smoothConditionalMaxEntropy ε' hε'0 hε'1 +
            log2 (1 / (1 - (ε + ε') ^ 2)) / (n : ℝ)
      ring

private theorem canonicalAEPpurification_marginalAB
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
    let Ω : PureVector (Prod (Prod a b) (Prod a b)) :=
      ρ.canonicalPurification.reindex (Equiv.prodComm (Prod a b) (Prod a b))
    Ω.state.marginalAB = ρ := by
  dsimp
  apply State.ext
  simpa [State.marginalAB_eq_marginalA, PureVector.reindex_state, State.reindex,
    State.marginalA, State.marginalB, partialTraceA, partialTraceB,
    PureVector.state_matrix, rankOneMatrix_apply] using
    ρ.canonicalPurification_purifies

/-- At every fixed `0 < ε < 1`, the normalized smooth conditional min-entropy
of the IID tensor power converges to the conditional von Neumann entropy.

The lower squeeze is the finite-N AEP.  The upper squeeze uses the smooth
min/max comparison at `ε' = (1-ε)/2`, smooth duality on a purification, and the
finite-N lower bound on the complementary marginal. -/
theorem tensorPowerSubnormalizedSmoothConditionalMinEntropyRate_tendsto
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_one : ε < 1) :
    Tendsto
      (fun n : ℕ =>
        ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
          ε n (le_of_lt hε_pos) hε_lt_one)
      atTop (nhds ρ.conditionalEntropy) := by
  let ε' : ℝ := (1 - ε) / 2
  have hε'pos : 0 < ε' := by dsimp [ε']; linarith
  have hε'0 : 0 ≤ ε' := le_of_lt hε'pos
  have hε'1 : ε' < 1 := by dsimp [ε']; linarith
  have hsum : ε + ε' < 1 := by dsimp [ε']; linarith
  let Ω : PureVector (Prod (Prod a b) (Prod a b)) :=
    ρ.canonicalPurification.reindex (Equiv.prodComm (Prod a b) (Prod a b))
  let σ : State (Prod a (Prod a b)) := Ω.state.marginalAC
  have hAB : Ω.state.marginalAB = ρ :=
    canonicalAEPpurification_marginalAB ρ
  have hentropyDual : ρ.conditionalEntropy = -σ.conditionalEntropy := by
    have h := State.PureVector.conditionalEntropy_marginalAB_eq_neg_marginalAC Ω
    rw [hAB] at h
    simpa only [σ] using h
  have hlower := fixedEpsilon_min_rate_lower_eventually ρ hε_pos hε_lt_one
  have hcomplementLower :=
    fixedEpsilon_min_rate_lower_eventually σ hε'pos hε'1
  let correction : ℝ := log2 (1 / (1 - (ε + ε') ^ 2))
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
            ε n (le_of_lt hε_pos) hε_lt_one ≤
          ρ.conditionalEntropy +
              finiteAEPDelta ε' σ.finiteAEPEtaTrace / Real.sqrt (n : ℝ) +
            correction / (n : ℝ) := by
    filter_upwards [hcomplementLower] with n hn
    have hcomparison :=
      fixedEpsilon_min_rate_le_max_rate_add_correction
        ρ (le_of_lt hε_pos) hε_lt_one hε'0 hε'1 hsum n
    have hduality :=
      PureVector.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate_marginalAB_eq_neg_min_marginalAC
        Ω hε'0 hε'1 n
    rw [hAB] at hduality
    change
      σ.conditionalEntropy -
          finiteAEPDelta ε' σ.finiteAEPEtaTrace / Real.sqrt (n : ℝ) ≤
        σ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
          ε' n hε'0 hε'1 at hn
    change
      ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate
          ε' n hε'0 hε'1 =
        -σ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
          ε' n hε'0 hε'1 at hduality
    rw [hduality] at hcomparison
    change
      ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
          ε n (le_of_lt hε_pos) hε_lt_one ≤
        ρ.conditionalEntropy +
            finiteAEPDelta ε' σ.finiteAEPEtaTrace / Real.sqrt (n : ℝ) +
          log2 (1 / (1 - (ε + ε') ^ 2)) / (n : ℝ)
    linarith
  have hlowerLimit :
      Tendsto
        (fun n : ℕ =>
          ρ.conditionalEntropy -
            finiteAEPDelta ε ρ.finiteAEPEtaTrace / Real.sqrt (n : ℝ))
        atTop (nhds ρ.conditionalEntropy) := by
    simpa using tendsto_const_nhds.sub
      (finiteAEPDelta_div_sqrt_tendsto_zero ε ρ.finiteAEPEtaTrace)
  have hcorrectionLimit :
      Tendsto (fun n : ℕ => correction / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hupperLimit :
      Tendsto
        (fun n : ℕ =>
          ρ.conditionalEntropy +
              finiteAEPDelta ε' σ.finiteAEPEtaTrace / Real.sqrt (n : ℝ) +
            correction / (n : ℝ))
        atTop (nhds ρ.conditionalEntropy) := by
    simpa using
      (tendsto_const_nhds.add
        (finiteAEPDelta_div_sqrt_tendsto_zero ε' σ.finiteAEPEtaTrace)).add
          hcorrectionLimit
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerLimit hupperLimit hlower hupper

/-- At every fixed `0 < ε < 1`, the normalized smooth conditional max-entropy
of the IID tensor power converges to the conditional von Neumann entropy. -/
theorem tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate_tendsto
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_one : ε < 1) :
    Tendsto
      (fun n : ℕ =>
        ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate
          ε n (le_of_lt hε_pos) hε_lt_one)
      atTop (nhds ρ.conditionalEntropy) := by
  let Ω : PureVector (Prod (Prod a b) (Prod a b)) :=
    ρ.canonicalPurification.reindex (Equiv.prodComm (Prod a b) (Prod a b))
  let σ : State (Prod a (Prod a b)) := Ω.state.marginalAC
  have hAB : Ω.state.marginalAB = ρ :=
    canonicalAEPpurification_marginalAB ρ
  have hrate :
      (fun n : ℕ =>
        ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate
          ε n (le_of_lt hε_pos) hε_lt_one) =
        (fun n : ℕ =>
          -σ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
            ε n (le_of_lt hε_pos) hε_lt_one) := by
    funext n
    have hduality :=
      PureVector.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate_marginalAB_eq_neg_min_marginalAC
        Ω (le_of_lt hε_pos) hε_lt_one n
    rw [hAB] at hduality
    simpa [σ] using hduality
  have hentropy : ρ.conditionalEntropy = -σ.conditionalEntropy := by
    have h := State.PureVector.conditionalEntropy_marginalAB_eq_neg_marginalAC Ω
    rw [hAB] at h
    simpa only [σ] using h
  rw [hrate, hentropy]
  exact (tensorPowerSubnormalizedSmoothConditionalMinEntropyRate_tendsto
    σ ε hε_pos hε_lt_one).neg

/-- Fully quantum asymptotic equipartition property in the literal iterated
limit form stated by TCR 2008, `thm:qaep`. -/
theorem fullyQuantumAsymptoticEquipartitionProperty
    (ρ : State (Prod a b)) :
    QIT.asymptoticAEP_statement ρ := by
  letI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  letI : Nonempty b := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  exact ρ.asymptoticAEP_statement_of_fixed_epsilon_limits
    ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate_tendsto
    ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate_tendsto

end State

end


end QIT
