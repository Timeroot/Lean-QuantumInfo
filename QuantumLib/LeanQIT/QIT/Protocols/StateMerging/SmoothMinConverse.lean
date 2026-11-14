/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Protocols.StateMerging.OneShotConverse
public import QIT.Asymptotic.FixedEpsilonAEP

/-!
# Asymptotic smooth-min-entropy converse for quantum state merging

This module derives the unrestricted canonical state-merging converse from the
fixed-radius one-shot converse and the fixed-smoothing fully quantum AEP.
-/

@[expose] public section

open Filter

namespace QIT

universe u v w x y z p q

noncomputable section

private theorem stateMergingPurifiedRadius_le_half
    {e : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 / 256) :
    Real.sqrt (2 * Real.sqrt e - (Real.sqrt e) ^ 2) ≤ 1 / 2 := by
  have hsqrt0 : 0 ≤ Real.sqrt e := Real.sqrt_nonneg e
  have hsqrtSq : (Real.sqrt e) ^ 2 = e := Real.sq_sqrt he0
  have hsqrtLe : Real.sqrt e ≤ 1 / 16 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · norm_num at he ⊢
      exact he
  have hinner0 : 0 ≤ 2 * Real.sqrt e - (Real.sqrt e) ^ 2 := by
    have hproduct : 0 ≤ Real.sqrt e * (2 - Real.sqrt e) :=
      mul_nonneg hsqrt0 (by linarith)
    nlinarith
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · nlinarith [hsqrtSq, sq_nonneg (Real.sqrt e)]

private theorem rate_lower_bound_of_tendsto_neg
    (H R : ℝ) (f : ℕ → ℝ)
    (hf : Tendsto f atTop (nhds (-H)))
    (hcodes : ∀ delta : ℝ, 0 < delta →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ cost : ℝ, -f n ≤ cost ∧ cost ≤ R + delta) :
    H ≤ R := by
  by_contra hcontra
  push Not at hcontra
  let slack : ℝ := (H - R) / 3
  have hslack : 0 < slack := by
    dsimp only [slack]
    linarith
  have heventually : Filter.Eventually (fun n => |f n - (-H)| < slack) atTop := by
    have hball := hf.eventually (Metric.ball_mem_nhds (-H) hslack)
    exact hball.mono (fun n hn => by simpa [Real.dist_eq] using hn)
  obtain ⟨Nf, hNf⟩ := eventually_atTop.1 heventually
  obtain ⟨Nc, hNc⟩ := hcodes slack hslack
  let n := max Nf Nc
  obtain ⟨cost, hfixed, hrate⟩ := hNc n (le_max_right _ _)
  have hclose := hNf n (le_max_left _ _)
  have hupper : f n < -H + slack := by
    have := lt_of_le_of_lt (le_abs_self (f n - (-H))) hclose
    linarith
  dsimp only [slack] at hslack hrate hupper ⊢
  linarith

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

namespace PureVector

/-- Every unrestricted canonically achievable state-merging rate is at least
the source conditional entropy. -/
theorem conditionalEntropy_le_of_isAchievableStateMergingRate
    (psi : PureVector (Prod (Prod a b) r)) (R : Real)
    (hR : IsAchievableStateMergingRate.{u, v, w, x, y, z, p, q} psi R) :
    psi.state.marginalA.conditionalEntropy ≤ R := by
  letI : Nonempty a := ⟨(Classical.choice psi.state.nonempty).1.1⟩
  letI : Nonempty r := ⟨(Classical.choice psi.state.nonempty).2⟩
  let eta : Real := 1 / 2
  have hetaPos : 0 < eta := by simp [eta]
  have heta0 : 0 ≤ eta := le_of_lt hetaPos
  have heta1 : eta < 1 := by norm_num [eta]
  let H : Real := psi.state.marginalA.conditionalEntropy
  let f : ℕ → Real := fun n =>
    psi.state.marginalAC.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
      eta n heta0 heta1
  have hduality : psi.state.marginalAC.conditionalEntropy = -H := by
    have h := State.PureVector.conditionalEntropy_marginalAB_eq_neg_marginalAC psi
    rw [State.marginalAB_eq_marginalA] at h
    dsimp only [H]
    linarith
  have hf : Tendsto f atTop (nhds (-H)) := by
    simpa only [f, hduality] using
      (State.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate_tendsto
        psi.state.marginalAC eta hetaPos heta1)
  apply rate_lower_bound_of_tendsto_neg H R f hf
  intro delta hdelta
  obtain ⟨N, hcodes⟩ := hR delta hdelta (1 / 256) (by norm_num)
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hnOne : 1 ≤ n := (le_max_left 1 N).trans hn
  have hnN : N ≤ n := (le_max_right 1 N).trans hn
  obtain ⟨kA, kAFintype, kADecidableEq, kANonempty,
      kB, kBFintype, kBDecidableEq,
      lA, lAFintype, lADecidableEq, lANonempty,
      lB, lBFintype, lBDecidableEq,
      outcome, outcomeFintype, outcomeDecidableEq, outcomeNonempty,
      C, hrate, herror⟩ := hcodes n hnN
  letI : Fintype kA := kAFintype
  letI : DecidableEq kA := kADecidableEq
  letI : Nonempty kA := kANonempty
  letI : Fintype kB := kBFintype
  letI : DecidableEq kB := kBDecidableEq
  letI : Fintype lA := lAFintype
  letI : DecidableEq lA := lADecidableEq
  letI : Nonempty lA := lANonempty
  letI : Fintype lB := lBFintype
  letI : DecidableEq lB := lBDecidableEq
  letI : Fintype outcome := outcomeFintype
  letI : DecidableEq outcome := outcomeDecidableEq
  letI : Nonempty outcome := outcomeNonempty
  have hradius : C.oneShotConversePurifiedRadius ≤ eta := by
    simpa only [StateMergingBlockProtocol.oneShotConversePurifiedRadius, eta] using
      stateMergingPurifiedRadius_le_half C.fidelityError_nonneg herror
  refine ⟨C.netEntanglementRate, ?_, hrate⟩
  simpa only [f] using
    C.oneShotSmoothMinEntropyRate_converse eta heta1 hradius
      (Nat.zero_lt_of_lt hnOne)

end PureVector

end

end QIT
