/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.SandwichedRenyiNonNeg
import Quantum.QuantumEntropy.CFCDeriv
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Umegaki relative entropy as the `α → 1` limit

This file extends the Frank–Lieb data-processing programme to the boundary case
`α = 1`, where the sandwiched Rényi divergence degenerates to the **Umegaki
relative entropy**.

It is the companion of the `α = ∞` (max-relative entropy) case, proven in
`Quantum.QuantumEntropy.SandwichedRenyiNonNeg` (`maxRelEntropyNN_monotone`).

## Status

The whole `α = 1` programme (following Müller-Lennert et al., arXiv:1306.3142) is
**fully proven, sorry-free**.

* `umegakiNorm`, `umegakiRelEntropyNN` — explicit definitions.
* `hasDerivAt_sandwichedQuasi_re_one` — the derivative of
  `α ↦ Re Tr((σ^{(1-α)/2α} ρ σ^{(1-α)/2α})^α)` at `α = 1` is `Re Tr(ρ(log ρ − log σ))`.
  Assembled from `hasDerivAt_partB` (conjugating-power term) and `hasDerivAt_partA`
  (outer-power term: fixed-base FTC + averaging with the exp-based joint continuity
  `continuousAt_quasiIntegrand` — no Duhamel needed).
* `sandwichedRenyiDiv_tendsto_umegaki` — the `α → 1⁺` limit equals `umegakiNorm`.
* `umegakiNorm_monotone_pd` — DPI for positive-definite `ρ, σ`.
* `umegakiRelEntropyNN_monotone` — the general **non-negative** DPI, via the
  faithful-perturbation NN→pd reduction (`umegakiNorm_faithfulApprox_le` +
  `tendsto_umegakiNorm_faithful`), with the singular boundary continuity handled by
  the cross-term limit `tendsto_tr_perturb_mul_log_perturb`
  (and `tendsto_tr_faithful_cross` for the faithful path).

## The limit value

For positive-definite `ρ, σ`, L'Hôpital applied to
`D_α(ρ‖σ) = (α−1)⁻¹ · (log (Q_α).re − log (Tr ρ).re)` at `α = 1` gives

  `lim_{α → 1⁺} D_α(ρ‖σ) = (Tr ρ)⁻¹ · Re Tr(ρ (log ρ − log σ))`,

since `Q_1 = Tr ρ` makes the logarithm's argument tend to `1`, so the limit is the
derivative `(log ∘ Q)'(1) = Q'(1) / Q(1)` with
`Q'(1) = Re Tr(ρ(log ρ − log σ))`.

Cf. Frank–Lieb (arXiv:1306.5358v3): the `α = 1` case "follows by continuity in
α / a limiting argument".
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory
open scoped ComplexOrder Topology

universe u

set_option linter.style.longLine false

section Umegaki

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

/-- **Normalised Umegaki relative entropy**
    `(Tr ρ)⁻¹ · Re Tr(ρ (log ρ − log σ))`.

    This is the `α → 1⁺` limit of `sandwichedRenyiDiv α ρ σ`
    (`sandwichedRenyiDiv_tendsto_umegaki`). For `ρ = 0` it evaluates to `0`
    (the `Tr ρ = 0` denominator gives `0 / 0 = 0`), matching the convention that
    the divergence vanishes when `ρ = 0`. -/
noncomputable def umegakiNorm (ρ σ : L ℋ) : ℝ :=
  (Tr (ρ * (CFC.log ρ - CFC.log σ))).re / (Tr ρ).re

/-- **Umegaki relative entropy** for non-negative `ρ, σ` (the `α → 1` boundary of
    the Frank–Lieb extension), as an `EReal`: value `⊤` on the support-mismatch
    region `¬ suppLE ρ σ`, and `umegakiNorm ρ σ` otherwise. -/
noncomputable def umegakiRelEntropyNN (ρ σ : L ℋ) : EReal :=
  letI : Decidable (suppLE ρ σ) := Classical.propDecidable _
  if suppLE ρ σ then ((umegakiNorm ρ σ : ℝ) : EReal) else (⊤ : EReal)

omit [Nontrivial ℋ] in
/-- The quasi-entropy at `α = 1` is `Tr ρ`: the conjugating power
    `σ^{(1−1)/(2·1)} = σ^0 = 1`, leaving `(1 ρ 1)^1 = ρ`. -/
lemma sandwichedQuasi_one_re (ρ σ : L ℋ) (hσ : 0 ≤ σ) (hρ : 0 ≤ ρ) :
    (sandwichedQuasi 1 ρ σ).re = (Tr ρ).re := by
  have h : sandwichedQuasi 1 ρ σ = Tr ρ := by
    unfold sandwichedQuasi
    have hz : CFC.rpow σ ((1 - (1 : ℝ)) / (2 * 1)) = 1 := by
      rw [show ((1 - (1 : ℝ)) / (2 * 1)) = 0 by norm_num]
      exact CFC.rpow_zero σ hσ
    rw [hz, one_mul, mul_one, show CFC.rpow ρ 1 = ρ from CFC.rpow_one ρ hρ]
  rw [h]

omit [Nontrivial ℋ] in
/-- Bridge: a `pdSetLM` operator is strictly positive (nonnegative and a unit). -/
lemma isStrictlyPositive_of_pdSetLM {σ : L ℋ} (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    IsStrictlyPositive σ := ⟨nonneg_of_pdSetLM hσ, isUnit_of_pdSetLM hσ⟩

omit [Nontrivial ℋ] in
/-- **Part B (proven): the conjugating-power contribution.** Differentiating the
    `α = 1` slice `α ↦ Re Tr(ρ · σ^{(1−α)/α})` (fixed base `σ`, exponent
    `(1−α)/α` with derivative `−1` at `α = 1`) gives `−Re Tr(ρ log σ)`.

    Proven from the fixed-base exponent derivative `CFC.hasDerivAt_rpow_exponent`
    (`CFCDeriv`), the chain rule, and `hasDerivAt_reTrace_mul_left`. -/
lemma hasDerivAt_partB {ρ σ : L ℋ} (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    HasDerivAt (fun α => (Tr (ρ * CFC.rpow σ ((1 - α) / α))).re)
      (-(Tr (ρ * CFC.log σ)).re) 1 := by
  have hσsp : IsStrictlyPositive σ := isStrictlyPositive_of_pdSetLM hσ
  have hσnn : (0 : L ℋ) ≤ σ := nonneg_of_pdSetLM hσ
  have ht : HasDerivAt (fun α : ℝ => (1 - α) / α) (-1) 1 := by
    have hu : HasDerivAt (fun α : ℝ => 1 - α) (-1) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).const_sub 1
    have hv : HasDerivAt (fun α : ℝ => α) (1) 1 := hasDerivAt_id 1
    simpa using hu.div hv (by norm_num)
  have hchain := CFC.hasDerivAt_rpow_exponent_comp hσsp ht
  have htr := hasDerivAt_reTrace_mul_left ρ hchain
  convert htr using 1
  have h0 : ((1 : ℝ) - 1) / 1 = 0 := by norm_num
  rw [h0, show CFC.rpow σ 0 = 1 from CFC.rpow_zero σ hσnn, one_mul]
  rw [show ((-1 : ℝ) • CFC.log σ) = -(CFC.log σ) from by simp]
  rw [mul_neg, map_neg, Complex.neg_re]

omit [Nontrivial ℋ] in
/-- **Cyclicity** identifying `Tr(ρ σ^{(1−α)/α})` with the trace of the inner operator
    `K(α) = σ^{(1−α)/(2α)} ρ σ^{(1−α)/(2α)}` of `sandwichedQuasi`. -/
lemma trace_conj_eq_trace_mul_rpow {ρ σ : L ℋ} (hσ : σ ∈ pdSetLM (ℋ := ℋ)) (α : ℝ) :
    Tr (ρ * CFC.rpow σ ((1 - α) / α))
      = Tr (CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α))) := by
  set c := (1 - α) / (2 * α) with hc
  have hσu : IsUnit σ := isUnit_of_pdSetLM hσ
  have hsum : (1 - α) / α = c + c := by rw [hc]; ring
  rw [hsum, show CFC.rpow σ (c + c) = CFC.rpow σ c * CFC.rpow σ c from CFC.rpow_add hσu,
     ← mul_assoc, LinearMap.trace_mul_comm, ← mul_assoc]

omit [Nontrivial ℋ] in
/-- **Fixed-base FTC building block.** For a strictly positive `K`, `s ↦ Re Tr(K^s)`
    has derivative `Re Tr(K^s · log K)` (cornerstone + `hasDerivAt_reTrace_mul_left`). -/
lemma hasDerivAt_trace_rpow_fixed {K : L ℋ} (hK : IsStrictlyPositive K) (s₀ : ℝ) :
    HasDerivAt (fun s => (Tr (CFC.rpow K s)).re)
      ((Tr (CFC.rpow K s₀ * CFC.log K)).re) s₀ := by
  have hd := CFC.hasDerivAt_rpow_exponent hK s₀
  simpa using hasDerivAt_reTrace_mul_left (1 : L ℋ) hd

/-- **Averaging lemma** (general real analysis): if `g` is jointly continuous at `(a, a)`
    with value `L` and each `g α` is interval-integrable on `[a, α]`, then the average
    `(α − a)⁻¹ ∫_a^α g α s ds` tends to `L` as `α → a`. -/
lemma tendsto_average_of_continuousAt {g : ℝ → ℝ → ℝ} {a L : ℝ}
    (hcont : Filter.Tendsto (fun p : ℝ × ℝ => g p.1 p.2) (𝓝 (a, a)) (𝓝 L))
    (hint : ∀ α : ℝ, IntervalIntegrable (g α) volume a α) :
    Filter.Tendsto (fun α => (α - a)⁻¹ * ∫ s in a..α, g α s) (𝓝[≠] a) (𝓝 L) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  rw [Metric.tendsto_nhds_nhds] at hcont
  obtain ⟨δ, hδ, hball⟩ := hcont (ε / 2) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro α hα hdist
  have hαa : α - a ≠ 0 := sub_ne_zero.mpr hα
  have hsplit : ∫ s in a..α, g α s
      = (∫ s in a..α, (g α s - L)) + (α - a) * L := by
    rw [intervalIntegral.integral_sub (hint α) (intervalIntegral.intervalIntegrable_const),
        intervalIntegral.integral_const, smul_eq_mul]; ring
  have hbound : ∀ s ∈ Set.uIoc a α, ‖g α s - L‖ ≤ ε / 2 := by
    intro s hs
    have hs_dist : |s - a| ≤ |α - a| := by
      rcases Set.mem_uIoc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]; linarith
    have hp_dist : dist (α, s) (a, a) < δ := by
      rw [Prod.dist_eq]; simp only [max_lt_iff, Real.dist_eq]
      exact ⟨hdist, lt_of_le_of_lt hs_dist (by rwa [Real.dist_eq] at hdist)⟩
    have hb := hball hp_dist
    rw [Real.dist_eq] at hb
    exact le_of_lt hb
  have hint_bound : ‖∫ s in a..α, (g α s - L)‖ ≤ (ε / 2) * |α - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hval : (α - a)⁻¹ * (∫ s in a..α, g α s) - L
      = (α - a)⁻¹ * (∫ s in a..α, (g α s - L)) := by
    rw [hsplit]; field_simp; ring
  rw [Real.dist_eq, hval, abs_mul, abs_inv]
  have hpos : (0 : ℝ) < |α - a| := abs_pos.mpr hαa
  calc |α - a|⁻¹ * |∫ s in a..α, (g α s - L)|
      ≤ |α - a|⁻¹ * ((ε / 2) * |α - a|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rwa [← Real.norm_eq_abs]
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

omit [Nontrivial ℋ] in
/-- **FTC step.** For a strictly positive `K`, `Re Tr(K^α − K^1)` is the integral of
    `s ↦ Re Tr(K^s · log K)` over `[1, α]` (operator FTC + pushing `Re ∘ Tr` through). -/
lemma trace_rpow_sub_eq_integral {K : L ℋ} (hK : IsStrictlyPositive K) (α : ℝ) :
    (Tr (CFC.rpow K α - CFC.rpow K 1)).re
      = ∫ s in (1:ℝ)..α, (Tr (CFC.rpow K s * CFC.log K)).re := by
  have hcont : Continuous (fun s : ℝ => CFC.rpow K s * CFC.log K) :=
    (CFC.continuous_rpow_exponent hK).mul continuous_const
  have hop : (∫ s in (1:ℝ)..α, CFC.rpow K s * CFC.log K)
      = CFC.rpow K α - CFC.rpow K 1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro s _; exact CFC.hasDerivAt_rpow_exponent hK s
    · exact hcont.intervalIntegrable _ _
  rw [← hop]
  have hii : IntervalIntegrable (fun s : ℝ => CFC.rpow K s * CFC.log K) volume 1 α :=
    hcont.intervalIntegrable 1 α
  have hcomm := (reTraceMulLeft (1 : L ℋ)).toContinuousLinearMap.intervalIntegral_comp_comm hii
  have key : ∀ X : L ℋ, (reTraceMulLeft (1 : L ℋ)).toContinuousLinearMap X = (Tr X).re := by
    intro X; simp [reTraceMulLeft]
  calc (Tr (∫ s in (1:ℝ)..α, CFC.rpow K s * CFC.log K)).re
      = (reTraceMulLeft (1 : L ℋ)).toContinuousLinearMap
          (∫ s in (1:ℝ)..α, CFC.rpow K s * CFC.log K) := (key _).symm
    _ = ∫ s in (1:ℝ)..α,
          (reTraceMulLeft (1 : L ℋ)).toContinuousLinearMap (CFC.rpow K s * CFC.log K) := hcomm.symm
    _ = ∫ s in (1:ℝ)..α, (Tr (CFC.rpow K s * CFC.log K)).re := by simp_rw [key]

omit [Nontrivial ℋ] in
/-- **Joint continuity** at `(1, 1)` of the FTC integrand
    `(α, s) ↦ Re Tr(K(α)^s · log K(α))`, `K(α) = σ^{(1−α)/(2α)} ρ σ^{(1−α)/(2α)}`.
    Proved via the exponential representation `K(α)^s = exp(s • log K(α))`
    (`CFC.rpow_eq_normedSpace_exp_smul_log`): this turns the cfc joint continuity into
    `(continuity of s • log K(α))` composed with the global continuity of `exp`,
    using `CFC.continuousOn_log` for the (element) continuity of `log K(α)`. -/
lemma continuousAt_quasiIntegrand {ρ σ : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    ContinuousAt (fun p : ℝ × ℝ =>
      (Tr (CFC.rpow (CFC.rpow σ ((1 - p.1) / (2 * p.1)) * ρ
              * CFC.rpow σ ((1 - p.1) / (2 * p.1))) p.2
          * CFC.log (CFC.rpow σ ((1 - p.1) / (2 * p.1)) * ρ
              * CFC.rpow σ ((1 - p.1) / (2 * p.1))))).re) (1, 1) := by
  set K : ℝ → L ℋ := fun α =>
    CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α)) with hKdef
  have hKpd : ∀ α, K α ∈ pdSetLM (ℋ := ℋ) := by
    intro α
    have hPpd : CFC.rpow σ ((1 - α) / (2 * α)) ∈ pdSetLM (ℋ := ℋ) := pdSetLM_rpow_ne hσ
    have hPsa : IsSelfAdjoint (CFC.rpow σ ((1 - α) / (2 * α))) :=
      IsSelfAdjoint.of_nonneg (nonneg_of_pdSetLM hPpd)
    have h := pdSetLM_conj hρ (isUnit_of_pdSetLM hPpd)
    rwa [hPsa.star_eq] at h
  have hKsp : ∀ α, IsStrictlyPositive (K α) := fun α =>
    ⟨nonneg_of_pdSetLM (hKpd α), isUnit_of_pdSetLM (hKpd α)⟩
  have hc : ContinuousAt (fun α : ℝ => (1 - α) / (2 * α)) 1 := by
    apply ContinuousAt.div <;> [fun_prop; fun_prop; norm_num]
  have hrpow : ContinuousAt (fun α : ℝ => CFC.rpow σ ((1 - α) / (2 * α))) 1 :=
    (CFC.continuous_rpow_exponent ⟨nonneg_of_pdSetLM hσ, isUnit_of_pdSetLM hσ⟩).continuousAt.comp hc
  have hK : ContinuousAt K 1 := (hrpow.mul continuousAt_const).mul hrpow
  have hmemS : ∀ α, K α ∈ {a : L ℋ | IsSelfAdjoint a ∧ IsUnit a} := fun α =>
    ⟨(hKsp α).1.isSelfAdjoint, (hKsp α).2⟩
  have hlogK : ContinuousAt (fun α => CFC.log (K α)) 1 := by
    have htend : Filter.Tendsto K (𝓝 1) (𝓝[{a : L ℋ | IsSelfAdjoint a ∧ IsUnit a}] (K 1)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hK
        (Filter.Eventually.of_forall hmemS)
    exact (CFC.continuousOn_log (K 1) (hmemS 1)).tendsto.comp htend
  have hfeq : (fun p : ℝ × ℝ => (Tr (CFC.rpow (K p.1) p.2 * CFC.log (K p.1))).re)
      = (fun p : ℝ × ℝ =>
          (Tr (NormedSpace.exp (p.2 • CFC.log (K p.1)) * CFC.log (K p.1))).re) := by
    funext p; rw [CFC.rpow_eq_normedSpace_exp_smul_log (hKsp p.1)]
  change ContinuousAt (fun p : ℝ × ℝ => (Tr (CFC.rpow (K p.1) p.2 * CFC.log (K p.1))).re) (1, 1)
  rw [hfeq]
  have h1 : ContinuousAt (fun p : ℝ × ℝ => CFC.log (K p.1)) ((1:ℝ), (1:ℝ)) :=
    ContinuousAt.comp (g := fun α => CFC.log (K α)) (f := Prod.fst)
      (x := ((1:ℝ), (1:ℝ))) hlogK continuousAt_fst
  have h2 : ContinuousAt (fun p : ℝ × ℝ => p.2 • CFC.log (K p.1)) ((1:ℝ), (1:ℝ)) :=
    continuousAt_snd.smul h1
  have h3 : ContinuousAt (fun p : ℝ × ℝ => NormedSpace.exp (p.2 • CFC.log (K p.1))) ((1:ℝ), (1:ℝ)) :=
    QuantumState.continuous_normedSpace_exp.continuousAt.comp h2
  exact QuantumState.continuous_re_trace.continuousAt.comp (h3.mul h1)

omit [Nontrivial ℋ] in
/-- **Part A** (proven): the outer-power contribution
    `α ↦ Re Tr(K(α)^α) − Re Tr(K(α))` (with `K(α) = σ^{(1−α)/(2α)} ρ σ^{(1−α)/(2α)}`,
    whose trace equals `Re Tr(ρ σ^{(1−α)/α})` by cyclicity) has derivative
    `Re Tr(ρ log ρ)` at `α = 1`.

    Fixed-base FTC + averaging (no Duhamel): `Re Tr(K(α)^α) − Re Tr(K(α))` is the
    integral of `g(α, s) := Re Tr(K(α)^s log K(α))` over `[1, α]`
    (`trace_rpow_sub_eq_integral`), so the difference quotient is the average of `g`,
    which tends to `g(1, 1) = Re Tr(ρ log ρ)` by `tendsto_average_of_continuousAt`
    and the joint continuity `continuousAt_quasiIntegrand`. -/
lemma hasDerivAt_partA {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    HasDerivAt (fun α => (sandwichedQuasi α ρ σ).re
        - (Tr (ρ * CFC.rpow σ ((1 - α) / α))).re) ((Tr (ρ * CFC.log ρ)).re) 1 := by
  set K : ℝ → L ℋ := fun α =>
    CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α)) with hKdef
  have hKpd : ∀ α, K α ∈ pdSetLM (ℋ := ℋ) := by
    intro α
    have hPpd : CFC.rpow σ ((1 - α) / (2 * α)) ∈ pdSetLM (ℋ := ℋ) := pdSetLM_rpow_ne hσ
    have hPsa : IsSelfAdjoint (CFC.rpow σ ((1 - α) / (2 * α))) :=
      IsSelfAdjoint.of_nonneg (nonneg_of_pdSetLM hPpd)
    have h := pdSetLM_conj hρ (isUnit_of_pdSetLM hPpd)
    rwa [hPsa.star_eq] at h
  have hKsp : ∀ α, IsStrictlyPositive (K α) := fun α =>
    ⟨nonneg_of_pdSetLM (hKpd α), isUnit_of_pdSetLM (hKpd α)⟩
  set g : ℝ → ℝ → ℝ := fun α s => (Tr (CFC.rpow (K α) s * CFC.log (K α))).re with hgdef
  have hK1 : K 1 = ρ := by
    have hP1 : CFC.rpow σ ((1 - (1:ℝ)) / (2 * 1)) = 1 := by
      rw [show ((1 - (1:ℝ)) / (2 * 1)) = 0 by norm_num]
      exact CFC.rpow_zero σ (nonneg_of_pdSetLM hσ)
    rw [hKdef]
    change CFC.rpow σ ((1 - (1:ℝ)) / (2 * 1)) * ρ * CFC.rpow σ ((1 - (1:ℝ)) / (2 * 1)) = ρ
    rw [hP1, one_mul, mul_one]
  have hg11 : g 1 1 = (Tr (ρ * CFC.log ρ)).re := by
    simp only [hgdef, hK1]
    rw [show CFC.rpow ρ 1 = ρ from CFC.rpow_one ρ (nonneg_of_pdSetLM hρ)]
  -- joint continuity of g at (1,1)
  have hjoint : ContinuousAt (fun p : ℝ × ℝ => g p.1 p.2) (1, 1) := by
    have := continuousAt_quasiIntegrand hρ hσ
    rwa [hgdef]
  -- integrability of g α
  have hint : ∀ α : ℝ, IntervalIntegrable (g α) volume 1 α := by
    intro α
    apply Continuous.intervalIntegrable
    rw [hgdef]
    exact QuantumState.continuous_re_trace.comp
      ((CFC.continuous_rpow_exponent (hKsp α)).mul continuous_const)
  -- averaging: the difference quotient tends to g 1 1
  have havg := tendsto_average_of_continuousAt hjoint hint
  -- HasDerivAt of the integral form
  have hF : HasDerivAt (fun α => ∫ s in (1:ℝ)..α, g α s) (g 1 1) 1 := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hslope : slope (fun α => ∫ s in (1:ℝ)..α, g α s) 1
        = fun α => (α - 1)⁻¹ * ∫ s in (1:ℝ)..α, g α s := by
      funext α
      rw [slope_def_field, intervalIntegral.integral_same, sub_zero, div_eq_inv_mul]
    rw [hslope]; exact havg
  -- the Part A function equals the integral form
  have hfunc : (fun α => (sandwichedQuasi α ρ σ).re - (Tr (ρ * CFC.rpow σ ((1 - α) / α))).re)
      = (fun α => ∫ s in (1:ℝ)..α, g α s) := by
    funext α
    have hsq : (sandwichedQuasi α ρ σ).re = (Tr (CFC.rpow (K α) α)).re := by rw [hKdef]; rfl
    have hcyc : (Tr (ρ * CFC.rpow σ ((1 - α) / α))).re = (Tr (CFC.rpow (K α) 1)).re := by
      rw [trace_conj_eq_trace_mul_rpow hσ α,
        show CFC.rpow (K α) 1 = K α from CFC.rpow_one (K α) (nonneg_of_pdSetLM (hKpd α)), hKdef]
    rw [hsq, hcyc, ← Complex.sub_re, ← map_sub, trace_rpow_sub_eq_integral (hKsp α) α, hgdef]
  rw [hfunc, ← hg11]
  exact hF

omit [Nontrivial ℋ] in
/-- The derivative at `α = 1` of the real quasi-entropy
    `α ↦ Re Tr((σ^{(1−α)/(2α)} ρ σ^{(1−α)/(2α)})^α)` is `Re Tr(ρ (log ρ − log σ))`.

    Assembled from Part A (`hasDerivAt_partA`) and Part B (`hasDerivAt_partB`):
    the quasi-entropy splits as `(Q − Tr K) + Tr K`, whose derivatives are
    `Re Tr(ρ log ρ)` and `−Re Tr(ρ log σ)`. -/
lemma hasDerivAt_sandwichedQuasi_re_one
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    HasDerivAt (fun α => (sandwichedQuasi α ρ σ).re)
      ((Tr (ρ * (CFC.log ρ - CFC.log σ))).re) 1 := by
  have hB := hasDerivAt_partB (ρ := ρ) hσ
  have hA := hasDerivAt_partA hρ hσ
  have hsum := hA.add hB
  have heq : (fun α => (sandwichedQuasi α ρ σ).re)
      = (fun α => (sandwichedQuasi α ρ σ).re - (Tr (ρ * CFC.rpow σ ((1 - α) / α))).re)
        + (fun α => (Tr (ρ * CFC.rpow σ ((1 - α) / α))).re) := by
    funext α; simp only [Pi.add_apply]; ring
  rw [heq]
  convert hsum using 1
  rw [mul_sub, map_sub, Complex.sub_re]; ring

/-- **The `α → 1⁺` limit of the sandwiched Rényi divergence is the Umegaki
    relative entropy**, for positive-definite `ρ, σ`.

    Fully proven as a difference-quotient limit: with `Q(α) := (Q_α ρ σ).re` and
    `Q(1) = (Tr ρ).re`, one has
    `D_α(ρ‖σ) = (log Q(α) − log Q(1)) / (α − 1) = slope (log ∘ Q) 1 α`, and this
    slope tends to `(log ∘ Q)'(1) = umegakiNorm ρ σ` (by `hasDerivAt_iff_tendsto_slope`,
    restricted to `𝓝[>] 1`). The single derivative input is
    `hasDerivAt_sandwichedQuasi_re_one`. -/
lemma sandwichedRenyiDiv_tendsto_umegaki
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    Filter.Tendsto (fun α => sandwichedRenyiDiv α ρ σ) (𝓝[>] (1 : ℝ))
      (𝓝 (umegakiNorm ρ σ)) := by
  have hρ_nn := nonneg_of_pdSetLM hρ
  have hσ_nn := nonneg_of_pdSetLM hσ
  have hTrρ_pos : 0 < (Tr ρ).re := trace_re_pos_of_pdSetLM hρ
  have hQ1 : (sandwichedQuasi 1 ρ σ).re = (Tr ρ).re := sandwichedQuasi_one_re ρ σ hσ_nn hρ_nn
  have hQ1_ne : (sandwichedQuasi 1 ρ σ).re ≠ 0 := by rw [hQ1]; exact ne_of_gt hTrρ_pos
  -- chain rule for `log ∘ (Q_α).re` at `α = 1`
  have hderiv_f := hasDerivAt_sandwichedQuasi_re_one hρ hσ
  have hderiv_logf : HasDerivAt (fun α => Real.log ((sandwichedQuasi α ρ σ).re))
      (umegakiNorm ρ σ) 1 := by
    have hch := hderiv_f.log hQ1_ne
    rw [hQ1] at hch
    exact hch
  -- a derivative is the limit of the slope; restrict `𝓝[≠] 1` to `𝓝[>] 1`
  rw [hasDerivAt_iff_tendsto_slope] at hderiv_logf
  have h_mono : 𝓝[>] (1 : ℝ) ≤ 𝓝[≠] (1 : ℝ) :=
    nhdsWithin_mono _ (fun x hx => ne_of_gt hx)
  have h_slope := hderiv_logf.mono_left h_mono
  -- on `𝓝[>] 1`, the divergence coincides with that slope
  refine h_slope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with α hα
  have hα1 : (1 : ℝ) < α := hα
  have hα0 : (0 : ℝ) < α := by linarith
  have hfα_ne : (sandwichedQuasi α ρ σ).re ≠ 0 := sandwichedQuasi_re_ne_zero_of_pdSetLM hα0 hρ hσ
  change slope (fun α => Real.log ((sandwichedQuasi α ρ σ).re)) 1 α = sandwichedRenyiDiv α ρ σ
  rw [slope_def_field]
  unfold sandwichedRenyiDiv
  rw [hQ1, Real.log_div hfα_ne (ne_of_gt hTrρ_pos), one_div]
  ring

/-- **Data-processing for the Umegaki relative entropy, positive-definite case.**

    Fully reduced to `sandwichedRenyiDiv_tendsto_umegaki`: the finite-`α`
    monotonicity `sandwichedRenyiDiv_monotone` holds for every `α > 1`, and both
    sides converge to `umegakiNorm` as `α → 1⁺`, so the inequality passes to the
    limit. -/
theorem umegakiNorm_monotone_pd
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (hEρ : E.toFun ρ ∈ pdSetLM (ℋ := 𝒦)) (hEσ : E.toFun σ ∈ pdSetLM (ℋ := 𝒦)) :
    umegakiNorm (E.toFun ρ) (E.toFun σ) ≤ umegakiNorm ρ σ := by
  have hlim1 := sandwichedRenyiDiv_tendsto_umegaki hEρ hEσ
  have hlim2 := sandwichedRenyiDiv_tendsto_umegaki hρ hσ
  refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
  filter_upwards [self_mem_nhdsWithin] with α hα
  have hα1 : (1 : ℝ) < α := hα
  exact sandwichedRenyiDiv_monotone E (by linarith) (ne_of_gt hα1) hρ hσ hEρ hEσ

/-- Boundary continuity of the cross term `Re Tr((ρ+ε)·log(σ+ε)) → Re Tr(ρ·log σ)`
    for nonneg `ρ, σ` with `supp ρ ⊆ supp σ` (finite at singular `σ` since `ρ` kills
    `ker σ`, so the divergent `log ε` on `ker σ` enters only via `ε·log ε → 0`). -/
lemma tendsto_tr_perturb_mul_log_perturb {ρ σ : L ℋ}
    (hσ : 0 ≤ σ) (hsupp : suppLE ρ σ) :
    Filter.Tendsto (fun ε : ℝ => (Tr ((ρ + (ε : ℂ) • 1) * CFC.log (σ + (ε : ℂ) • 1))).re)
      (𝓝[>] (0:ℝ)) (𝓝 ((Tr (ρ * CFC.log σ)).re)) := by
  classical
  have hσ_sa : IsSelfAdjoint σ := IsSelfAdjoint.of_nonneg hσ
  have hσ_pos : σ.IsPositive := (LinearMap.nonneg_iff_isPositive σ).mp hσ
  have hσ_sym := hσ_pos.isSymmetric
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  set b := hσ_sym.eigenvectorBasis hn with hb
  set eig := hσ_sym.eigenvalues hn with heig
  have h_eig_apply : ∀ i, σ (b i) = ((eig i : ℝ) : ℂ) • b i := hσ_sym.apply_eigenvectorBasis hn
  have hb_ne : ∀ i, b i ≠ 0 := fun i => b.orthonormal.ne_zero i
  have hbb : ∀ i, inner ℂ (b i) (b i) = (1 : ℂ) := fun i => b.inner_eq_one i
  set c : Fin n → ℝ := fun i => (inner ℂ (b i) (ρ (b i))).re with hc_def
  have hc0 : ∀ i, eig i = 0 → c i = 0 := by
    intro i hi
    have hbker : b i ∈ LinearMap.ker σ := by rw [LinearMap.mem_ker, h_eig_apply i, hi]; simp
    have hρb : ρ (b i) = 0 := LinearMap.mem_ker.mp (hsupp hbker)
    simp only [hc_def, hρb, inner_zero_right, Complex.zero_re]
  have hev : ∀ (ε : ℝ) (i), (σ + (ε : ℂ) • (1 : L ℋ)) (b i) = ((eig i + ε : ℝ) : ℂ) • b i := by
    intro ε i
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, h_eig_apply i]
    rw [← add_smul]; norm_cast
  have hsa : ∀ (ε : ℝ), IsSelfAdjoint (σ + (ε : ℂ) • (1 : L ℋ)) := by
    intro ε
    rw [IsSelfAdjoint, star_add, hσ_sa.star_eq, star_smul, star_one, Complex.star_def,
      Complex.conj_ofReal]
  have hlog_apply : ∀ (ε : ℝ) (i),
      CFC.log (σ + (ε : ℂ) • 1) (b i) = ((Real.log (eig i + ε) : ℝ) : ℂ) • b i := by
    intro ε i
    exact cfc_real_apply_eigenvector (hsa ε) Real.log (hev ε i)
      (mem_spectrum_real_of_eigenvector (hb_ne i) (hev ε i))
  have hinner : ∀ (ε : ℝ) (i),
      (inner ℂ (b i) ((ρ + (ε : ℂ) • 1) (b i))).re = c i + ε := by
    intro ε i
    rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, inner_add_right,
      inner_smul_right, hbb i, mul_one, Complex.add_re, hc_def, Complex.ofReal_re]
  have hexpand : ∀ ε : ℝ, (Tr ((ρ + (ε : ℂ) • 1) * CFC.log (σ + (ε : ℂ) • 1))).re
      = ∑ i, Real.log (eig i + ε) * (c i + ε) := by
    intro ε
    rw [LinearMap.trace_eq_sum_inner (T := (ρ + (ε : ℂ) • 1) * CFC.log (σ + (ε : ℂ) • 1)) b,
      Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Module.End.mul_apply, hlog_apply ε i, map_smul, inner_smul_right, Complex.re_ofReal_mul,
      hinner ε i]
  have hlimval : (Tr (ρ * CFC.log σ)).re = ∑ i, Real.log (eig i) * c i := by
    have h0 := hexpand 0
    simp only [Complex.ofReal_zero, zero_smul, add_zero] at h0
    exact h0
  rw [hlimval, show (fun ε : ℝ => (Tr ((ρ + (ε : ℂ) • 1) * CFC.log (σ + (ε : ℂ) • 1))).re)
        = (fun ε => ∑ i, Real.log (eig i + ε) * (c i + ε)) from funext hexpand]
  apply tendsto_finset_sum
  intro i _
  have haddci : Filter.Tendsto (fun ε : ℝ => c i + ε) (𝓝[>] (0:ℝ)) (𝓝 (c i)) := by
    have : Filter.Tendsto (fun ε : ℝ => c i + ε) (𝓝 (0:ℝ)) (𝓝 (c i + 0)) :=
      (continuous_const.add continuous_id).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  by_cases hi : eig i = 0
  · rw [hi, hc0 i hi]
    simp only [Real.log_zero, mul_zero, zero_add]
    have hnml : Filter.Tendsto (fun ε : ℝ => Real.log ε * ε) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hc := (Real.continuous_negMulLog.tendsto 0)
      simp only [Real.negMulLog_zero] at hc
      have := hc.neg
      simp only [neg_zero] at this
      refine (this.mono_left nhdsWithin_le_nhds).congr (fun ε => ?_)
      simp [Real.negMulLog, mul_comm]
    exact hnml
  · have heig_pos : 0 < eig i :=
      lt_of_le_of_ne (hσ_pos.nonneg_eigenvalues hn i) (Ne.symm hi)
    have hlog : Filter.Tendsto (fun ε : ℝ => Real.log (eig i + ε)) (𝓝[>] (0:ℝ))
        (𝓝 (Real.log (eig i))) := by
      have : Filter.Tendsto (fun ε : ℝ => Real.log (eig i + ε)) (𝓝 (0:ℝ))
          (𝓝 (Real.log (eig i + 0))) :=
        (Real.continuousAt_log (by simpa using ne_of_gt heig_pos)).comp
          ((continuous_const.add continuous_id).tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    exact hlog.mul haddci

omit [Nontrivial ℋ] in
/-- `Re Tr(ρ + ε•1) → Re Tr ρ` as `ε → 0⁺`. -/
lemma tendsto_tr_perturb {ρ : L ℋ} :
    Filter.Tendsto (fun ε : ℝ => (Tr (ρ + (ε : ℂ) • 1)).re) (𝓝[>] (0:ℝ)) (𝓝 (Tr ρ).re) := by
  have key : (Tr ρ).re = (Tr (ρ + ((0:ℝ) : ℂ) • (1 : L ℋ))).re := by simp
  rw [key]
  exact ((QuantumState.continuous_re_trace.comp
    (by fun_prop : Continuous fun ε : ℝ => ρ + (ε : ℂ) • (1 : L ℋ))).tendsto 0).mono_left
    nhdsWithin_le_nhds

/-- **Boundary continuity (H1)**: `umegakiNorm (ρ+ε) (σ+ε) → umegakiNorm ρ σ` as `ε → 0⁺`,
    for nonneg `ρ ≠ 0`, `σ` with `supp ρ ⊆ supp σ`. Assembles the cross-term continuity
    (numerator) with trace continuity (denominator) via `Tendsto.div`. -/
lemma tendsto_umegakiNorm_perturb {ρ σ : L ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0) (hsupp : suppLE ρ σ) :
    Filter.Tendsto (fun ε : ℝ => umegakiNorm (ρ + (ε : ℂ) • 1) (σ + (ε : ℂ) • 1))
      (𝓝[>] (0:ℝ)) (𝓝 (umegakiNorm ρ σ)) := by
  have hcrossρ := tendsto_tr_perturb_mul_log_perturb (ρ := ρ) (σ := ρ) hρ (le_refl _)
  have hcrossσ := tendsto_tr_perturb_mul_log_perturb (ρ := ρ) (σ := σ) hσ hsupp
  have hnum : Filter.Tendsto
      (fun ε : ℝ => (Tr ((ρ + (ε : ℂ) • 1) *
          (CFC.log (ρ + (ε : ℂ) • 1) - CFC.log (σ + (ε : ℂ) • 1)))).re)
      (𝓝[>] (0:ℝ)) (𝓝 ((Tr (ρ * (CFC.log ρ - CFC.log σ))).re)) := by
    have heqf : (fun ε : ℝ => (Tr ((ρ + (ε : ℂ) • 1) *
          (CFC.log (ρ + (ε : ℂ) • 1) - CFC.log (σ + (ε : ℂ) • 1)))).re)
        = (fun ε : ℝ => (Tr ((ρ + (ε : ℂ) • 1) * CFC.log (ρ + (ε : ℂ) • 1))).re
            - (Tr ((ρ + (ε : ℂ) • 1) * CFC.log (σ + (ε : ℂ) • 1))).re) := by
      funext ε; rw [mul_sub, map_sub, Complex.sub_re]
    rw [heqf, show (Tr (ρ * (CFC.log ρ - CFC.log σ))).re
          = (Tr (ρ * CFC.log ρ)).re - (Tr (ρ * CFC.log σ)).re from by
        rw [mul_sub, map_sub, Complex.sub_re]]
    exact hcrossρ.sub hcrossσ
  have hden0 : (Tr ρ).re ≠ 0 := ne_of_gt (trace_re_pos_of_ne_zero hρ hρ0)
  have hres := hnum.div (tendsto_tr_perturb (ρ := ρ)) hden0
  simpa only [umegakiNorm] using hres

/-- **Continuity of `umegakiNorm` along a path into the strictly-positive operators**
    (no singularity): if `a ε → a₀`, `b ε → b₀` with `a ε, b ε` eventually
    self-adjoint units and `a₀, b₀` self-adjoint units (`Re Tr a₀ ≠ 0`), then
    `umegakiNorm (a ε) (b ε) → umegakiNorm a₀ b₀`. Uses `CFC.continuousOn_log`. -/
lemma tendsto_umegakiNorm_within {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {a b : ℝ → L 𝒦} {a₀ b₀ : L 𝒦} {l : Filter ℝ}
    (ha : Filter.Tendsto a l (𝓝 a₀)) (hb : Filter.Tendsto b l (𝓝 b₀))
    (ha_mem : ∀ᶠ ε in l, IsSelfAdjoint (a ε) ∧ IsUnit (a ε))
    (hb_mem : ∀ᶠ ε in l, IsSelfAdjoint (b ε) ∧ IsUnit (b ε))
    (ha0 : IsSelfAdjoint a₀ ∧ IsUnit a₀) (hb0 : IsSelfAdjoint b₀ ∧ IsUnit b₀)
    (hTra0 : (Tr a₀).re ≠ 0) :
    Filter.Tendsto (fun ε => umegakiNorm (a ε) (b ε)) l (𝓝 (umegakiNorm a₀ b₀)) := by
  have hloga : Filter.Tendsto (fun ε => CFC.log (a ε)) l (𝓝 (CFC.log a₀)) :=
    (CFC.continuousOn_log a₀ ha0).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ha ha_mem)
  have hlogb : Filter.Tendsto (fun ε => CFC.log (b ε)) l (𝓝 (CFC.log b₀)) :=
    (CFC.continuousOn_log b₀ hb0).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hb hb_mem)
  have hnum : Filter.Tendsto (fun ε => (Tr (a ε * (CFC.log (a ε) - CFC.log (b ε)))).re) l
      (𝓝 ((Tr (a₀ * (CFC.log a₀ - CFC.log b₀))).re)) :=
    (QuantumState.continuous_re_trace.tendsto _).comp (ha.mul (hloga.sub hlogb))
  have hden : Filter.Tendsto (fun ε => (Tr (a ε)).re) l (𝓝 (Tr a₀).re) :=
    (QuantumState.continuous_re_trace.tendsto _).comp ha
  simpa only [umegakiNorm] using hnum.div hden hTra0

/-- **step1**: for each faithful parameter `λ ∈ (0,1]`,
    `umegakiNorm (F_λ ρ) (F_λ σ) ≤ umegakiNorm ρ σ`. Proven by perturbing inputs to
    `ρ+ε, σ+ε` (pd), applying the pd DPI `umegakiNorm_monotone_pd`, and taking `ε → 0⁺`
    (RHS via `tendsto_umegakiNorm_perturb`, LHS via `tendsto_umegakiNorm_within` since
    `F_λ` outputs are pd). -/
lemma umegakiNorm_faithfulApprox_le {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0) (hsupp : suppLE ρ σ)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    umegakiNorm ((faithfulApprox E lam hlam0.le hlam1).toFun ρ)
        ((faithfulApprox E lam hlam0.le hlam1).toFun σ) ≤ umegakiNorm ρ σ := by
  have hσ0 : σ ≠ 0 := by
    rintro rfl; apply hρ0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply]
    exact LinearMap.mem_ker.mp (hsupp (LinearMap.mem_ker.mpr (by simp)))
  set F := faithfulApprox E lam hlam0.le hlam1 with hF
  have hFρ : F.toFun ρ ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_pdSetLM E hlam0 hlam1 hρ hρ0
  have hFσ : F.toFun σ ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_pdSetLM E hlam0 hlam1 hσ hσ0
  have hFcont : Continuous (fun ε : ℝ => F.toFun (ρ + (ε : ℂ) • 1)) :=
    (LinearMap.continuous_of_finiteDimensional F.toCompletelyPositiveMap.toLinearMap).comp
      (by fun_prop)
  have hFcontσ : Continuous (fun ε : ℝ => F.toFun (σ + (ε : ℂ) • 1)) :=
    (LinearMap.continuous_of_finiteDimensional F.toCompletelyPositiveMap.toLinearMap).comp
      (by fun_prop)
  have h_pert : ∀ ε : ℝ, 0 < ε →
      umegakiNorm (F.toFun (ρ + (ε : ℂ) • 1)) (F.toFun (σ + (ε : ℂ) • 1))
        ≤ umegakiNorm (ρ + (ε : ℂ) • 1) (σ + (ε : ℂ) • 1) := by
    intro ε hε
    have hρε : ρ + (ε : ℂ) • 1 ∈ pdSetLM (ℋ := ℋ) := pdSetLM_add_nonneg hρ (pos_smul_one_pdSetLM hε)
    have hσε : σ + (ε : ℂ) • 1 ∈ pdSetLM (ℋ := ℋ) := pdSetLM_add_nonneg hσ (pos_smul_one_pdSetLM hε)
    exact umegakiNorm_monotone_pd F hρε hσε
      (faithfulApprox_pdSetLM E hlam0 hlam1 (nonneg_of_pdSetLM hρε) (isUnit_of_pdSetLM hρε).ne_zero)
      (faithfulApprox_pdSetLM E hlam0 hlam1 (nonneg_of_pdSetLM hσε) (isUnit_of_pdSetLM hσε).ne_zero)
  have h_RHS := tendsto_umegakiNorm_perturb hρ hσ hρ0 hsupp
  have h_LHS : Filter.Tendsto
      (fun ε : ℝ => umegakiNorm (F.toFun (ρ + (ε : ℂ) • 1)) (F.toFun (σ + (ε : ℂ) • 1)))
      (𝓝[>] (0:ℝ)) (𝓝 (umegakiNorm (F.toFun ρ) (F.toFun σ))) := by
    have hpd2sa : ∀ {τ : L 𝒦}, τ ∈ pdSetLM (ℋ := 𝒦) → IsSelfAdjoint τ ∧ IsUnit τ :=
      fun hτ => ⟨IsSelfAdjoint.of_nonneg (nonneg_of_pdSetLM hτ), isUnit_of_pdSetLM hτ⟩
    have hKey : F.toFun ρ = F.toFun (ρ + ((0:ℝ) : ℂ) • 1) := by simp
    have hKeyσ : F.toFun σ = F.toFun (σ + ((0:ℝ) : ℂ) • 1) := by simp
    refine tendsto_umegakiNorm_within
      (a := fun ε => F.toFun (ρ + (ε : ℂ) • 1)) (b := fun ε => F.toFun (σ + (ε : ℂ) • 1))
      (a₀ := F.toFun ρ) (b₀ := F.toFun σ)
      (hKey ▸ (hFcont.tendsto 0).mono_left nhdsWithin_le_nhds)
      (hKeyσ ▸ (hFcontσ.tendsto 0).mono_left nhdsWithin_le_nhds)
      ?_ ?_ (hpd2sa hFρ) (hpd2sa hFσ) (ne_of_gt (trace_re_pos_of_pdSetLM hFρ))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hρε : ρ + (ε : ℂ) • 1 ∈ pdSetLM (ℋ := ℋ) := pdSetLM_add_nonneg hρ (pos_smul_one_pdSetLM hε)
      exact hpd2sa (faithfulApprox_pdSetLM E hlam0 hlam1 (nonneg_of_pdSetLM hρε)
        (isUnit_of_pdSetLM hρε).ne_zero)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hσε : σ + (ε : ℂ) • 1 ∈ pdSetLM (ℋ := ℋ) := pdSetLM_add_nonneg hσ (pos_smul_one_pdSetLM hε)
      exact hpd2sa (faithfulApprox_pdSetLM E hlam0 hlam1 (nonneg_of_pdSetLM hσε)
        (isUnit_of_pdSetLM hσε).ne_zero)
  haveI : (𝓝[>] (0:ℝ)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  exact le_of_tendsto_of_tendsto h_LHS h_RHS (Filter.eventually_of_mem self_mem_nhdsWithin h_pert)

lemma tendsto_uloglu : Filter.Tendsto (fun u : ℝ => u * Real.log u) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hc0 := (Real.continuous_negMulLog.tendsto 0)
  simp only [Real.negMulLog_zero] at hc0
  have h := hc0.neg
  simp only [neg_zero] at h
  refine (h.mono_left nhdsWithin_le_nhds).congr (fun u => ?_)
  simp [Real.negMulLog]

lemma tendsto_lam_log_lam_mul {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun lam : ℝ => lam * Real.log (lam * c)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hu : Filter.Tendsto (fun lam : ℝ => lam * c) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using ((continuous_mul_const c).tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with lam hlam
      exact mul_pos hlam hc
  have hcomp := (tendsto_uloglu.comp hu).const_mul (c⁻¹)
  simp only [mul_zero] at hcomp
  refine hcomp.congr fun lam => ?_
  simp only [Function.comp_apply]
  field_simp

lemma tendsto_tr_faithful_cross {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] {A B : L 𝒦}
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hsupp : suppLE B A) {cA cB : ℝ} (hcA : 0 < cA) :
    Filter.Tendsto (fun lam : ℝ =>
        (Tr ((((1 - lam : ℝ) : ℂ) • B + ((lam * cB : ℝ) : ℂ) • 1) *
          CFC.log (((1 - lam : ℝ) : ℂ) • A + ((lam * cA : ℝ) : ℂ) • 1))).re)
      (𝓝[>] (0:ℝ)) (𝓝 ((Tr (B * CFC.log A)).re)) := by
  classical
  have hA_sa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hA_pos : A.IsPositive := (LinearMap.nonneg_iff_isPositive A).mp hA
  have hA_sym := hA_pos.isSymmetric
  set n := Module.finrank ℂ 𝒦 with hn_def
  have hn : Module.finrank ℂ 𝒦 = n := rfl
  set b := hA_sym.eigenvectorBasis hn with hb
  set eig := hA_sym.eigenvalues hn with heig
  have h_eig_apply : ∀ i, A (b i) = ((eig i : ℝ) : ℂ) • b i := hA_sym.apply_eigenvectorBasis hn
  have hb_ne : ∀ i, b i ≠ 0 := fun i => b.orthonormal.ne_zero i
  have hbb : ∀ i, inner ℂ (b i) (b i) = (1 : ℂ) := fun i => b.inner_eq_one i
  set d : Fin n → ℝ := fun i => (inner ℂ (b i) (B (b i))).re with hd_def
  have hd0 : ∀ i, eig i = 0 → d i = 0 := by
    intro i hi
    have hbker : b i ∈ LinearMap.ker A := by rw [LinearMap.mem_ker, h_eig_apply i, hi]; simp
    have hBb : B (b i) = 0 := LinearMap.mem_ker.mp (hsupp hbker)
    simp only [hd_def, hBb, inner_zero_right, Complex.zero_re]
  have hev : ∀ (lam : ℝ) (i),
      (((1 - lam : ℝ) : ℂ) • A + ((lam * cA : ℝ) : ℂ) • (1 : L 𝒦)) (b i)
        = (((1 - lam) * eig i + lam * cA : ℝ) : ℂ) • b i := by
    intro lam i
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, h_eig_apply i,
      smul_smul]
    rw [← add_smul]; push_cast; ring_nf
  have hsa : ∀ (lam : ℝ), IsSelfAdjoint (((1 - lam : ℝ) : ℂ) • A + ((lam * cA : ℝ) : ℂ) • (1 : L 𝒦)) := by
    intro lam
    rw [IsSelfAdjoint, star_add, star_smul, hA_sa.star_eq, star_smul, star_one,
      Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal]
  have hlog_apply : ∀ (lam : ℝ) (i),
      CFC.log (((1 - lam : ℝ) : ℂ) • A + ((lam * cA : ℝ) : ℂ) • 1) (b i)
        = ((Real.log ((1 - lam) * eig i + lam * cA) : ℝ) : ℂ) • b i := by
    intro lam i
    exact cfc_real_apply_eigenvector (hsa lam) Real.log (hev lam i)
      (mem_spectrum_real_of_eigenvector (hb_ne i) (hev lam i))
  have hinner : ∀ (lam : ℝ) (i),
      (inner ℂ (b i) ((((1 - lam : ℝ) : ℂ) • B + ((lam * cB : ℝ) : ℂ) • 1) (b i))).re
        = (1 - lam) * d i + lam * cB := by
    intro lam i
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply,
      inner_add_right, inner_smul_right, inner_smul_right, hbb i, mul_one, Complex.add_re,
      Complex.re_ofReal_mul, Complex.ofReal_re, hd_def]
  have hexpand : ∀ lam : ℝ,
      (Tr ((((1 - lam : ℝ) : ℂ) • B + ((lam * cB : ℝ) : ℂ) • 1) *
          CFC.log (((1 - lam : ℝ) : ℂ) • A + ((lam * cA : ℝ) : ℂ) • 1))).re
        = ∑ i, Real.log ((1 - lam) * eig i + lam * cA) * ((1 - lam) * d i + lam * cB) := by
    intro lam
    rw [LinearMap.trace_eq_sum_inner
        (T := (((1 - lam : ℝ) : ℂ) • B + ((lam * cB : ℝ) : ℂ) • 1) *
          CFC.log (((1 - lam : ℝ) : ℂ) • A + ((lam * cA : ℝ) : ℂ) • 1)) b, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Module.End.mul_apply, hlog_apply lam i, map_smul, inner_smul_right, Complex.re_ofReal_mul,
      hinner lam i]
  have hlimval : (Tr (B * CFC.log A)).re = ∑ i, Real.log (eig i) * d i := by
    have h0 := hexpand 0
    simp only [sub_zero, Complex.ofReal_one, one_smul, zero_mul, Complex.ofReal_zero, zero_smul,
      add_zero, one_mul] at h0
    exact h0
  rw [hlimval, show (fun lam : ℝ =>
        (Tr ((((1 - lam : ℝ) : ℂ) • B + ((lam * cB : ℝ) : ℂ) • 1) *
          CFC.log (((1 - lam : ℝ) : ℂ) • A + ((lam * cA : ℝ) : ℂ) • 1))).re)
      = (fun lam => ∑ i, Real.log ((1 - lam) * eig i + lam * cA) * ((1 - lam) * d i + lam * cB))
        from funext hexpand]
  apply tendsto_finset_sum
  intro i _
  by_cases hi : eig i = 0
  · rw [hi, hd0 i hi]
    simp only [mul_zero, zero_add, Real.log_zero]
    -- term = log(lam*cA) * (lam*cB) → 0 ; target log 0 * 0 = 0
    have : Filter.Tendsto (fun lam : ℝ => Real.log (lam * cA) * (lam * cB)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hh := (tendsto_lam_log_lam_mul hcA).const_mul cB
      simp only [mul_zero] at hh
      refine hh.congr fun lam => ?_
      ring
    simpa using this
  · have heig_pos : 0 < eig i := lt_of_le_of_ne (hA_pos.nonneg_eigenvalues hn i) (Ne.symm hi)
    have hlogt : Filter.Tendsto (fun lam : ℝ => Real.log ((1 - lam) * eig i + lam * cA))
        (𝓝[>] (0:ℝ)) (𝓝 (Real.log (eig i))) := by
      have hin : Filter.Tendsto (fun lam : ℝ => (1 - lam) * eig i + lam * cA) (𝓝 (0:ℝ))
          (𝓝 (eig i)) := by
        have : Filter.Tendsto (fun lam : ℝ => (1 - lam) * eig i + lam * cA) (𝓝 (0:ℝ))
            (𝓝 ((1 - 0) * eig i + 0 * cA)) :=
          (by fun_prop : Continuous fun lam : ℝ => (1 - lam) * eig i + lam * cA).tendsto 0
        simpa using this
      exact ((Real.continuousAt_log (ne_of_gt heig_pos)).tendsto.comp hin).mono_left
        nhdsWithin_le_nhds
    have hdt : Filter.Tendsto (fun lam : ℝ => (1 - lam) * d i + lam * cB) (𝓝[>] (0:ℝ))
        (𝓝 (d i)) := by
      have : Filter.Tendsto (fun lam : ℝ => (1 - lam) * d i + lam * cB) (𝓝 (0:ℝ))
          (𝓝 ((1 - 0) * d i + 0 * cB)) :=
        (by fun_prop : Continuous fun lam : ℝ => (1 - lam) * d i + lam * cB).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    exact hlogt.mul hdt

omit [Nontrivial ℋ] in
/-- Tr of a nonneg operator is real. -/
lemma tr_eq_re {τ : L ℋ} (hτ : 0 ≤ τ) : Tr τ = ((Tr τ).re : ℂ) := by
  have hsym := ((LinearMap.nonneg_iff_isPositive τ).mp hτ).isSymmetric
  have h : Tr τ = ((∑ i, hsym.eigenvalues (rfl : Module.finrank ℂ ℋ = _) i : ℝ) : ℂ) :=
    hsym.trace_eq_sum_eigenvalues rfl
  apply Complex.ext
  · rw [Complex.ofReal_re]
  · rw [h]; simp

-- faithfulApprox.toFun in explicit form
lemma faithfulApprox_toFun_eq {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) {τ : L ℋ} (hτ : 0 ≤ τ) :
    (faithfulApprox E lam h0 h1).toFun τ
      = ((1 - lam : ℝ) : ℂ) • E.toFun τ
        + ((lam * ((Tr τ).re / (Module.finrank ℂ 𝒦 : ℝ)) : ℝ) : ℂ) • (1 : L 𝒦) := by
  have hdepol : ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun τ
      = ((lam * ((Tr τ).re / (Module.finrank ℂ 𝒦 : ℝ)) : ℝ) : ℂ) • (1 : L 𝒦) := by
    change ((lam : ℝ) : ℂ) • ((Tr τ / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)) = _
    rw [smul_smul]
    congr 1
    nth_rewrite 1 [tr_eq_re hτ]
    push_cast
    ring
  change ((1 - lam : ℝ) : ℂ) • E.toFun τ + ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun τ = _
  rw [hdepol]

theorem tendsto_umegakiNorm_faithful_real {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0) (hsupp : suppLE ρ σ) :
    Filter.Tendsto
      (fun lam : ℝ =>
        umegakiNorm (((1 - lam : ℝ) : ℂ) • E.toFun ρ
            + ((lam * ((Tr ρ).re / (Module.finrank ℂ 𝒦 : ℝ)) : ℝ) : ℂ) • 1)
          (((1 - lam : ℝ) : ℂ) • E.toFun σ
            + ((lam * ((Tr σ).re / (Module.finrank ℂ 𝒦 : ℝ)) : ℝ) : ℂ) • 1))
      (𝓝[>] (0:ℝ)) (𝓝 (umegakiNorm (E.toFun ρ) (E.toFun σ))) := by
  have hEρ : (0 : L 𝒦) ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
  have hEσ : (0 : L 𝒦) ≤ E.toFun σ := map_nonneg E.toCompletelyPositiveMap hσ
  have hEsupp : suppLE (E.toFun ρ) (E.toFun σ) := suppLE_of_CPTP E hρ hσ hsupp
  have hEρ0 : E.toFun ρ ≠ 0 := CPTP_toFun_ne_zero E hρ hρ0
  have hσ0 : σ ≠ 0 := by
    rintro rfl; apply hρ0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply]
    exact LinearMap.mem_ker.mp (hsupp (LinearMap.mem_ker.mpr (by simp)))
  have hd_pos : (0 : ℝ) < (Module.finrank ℂ 𝒦 : ℝ) := by exact_mod_cast Module.finrank_pos
  have hcρ : 0 < (Tr ρ).re / (Module.finrank ℂ 𝒦 : ℝ) :=
    div_pos (trace_re_pos_of_ne_zero hρ hρ0) hd_pos
  have hcσ : 0 < (Tr σ).re / (Module.finrank ℂ 𝒦 : ℝ) :=
    div_pos (trace_re_pos_of_ne_zero hσ hσ0) hd_pos
  set cρ := (Tr ρ).re / (Module.finrank ℂ 𝒦 : ℝ) with hcρ_def
  set cσ := (Tr σ).re / (Module.finrank ℂ 𝒦 : ℝ) with hcσ_def
  have hxlogx := tendsto_tr_faithful_cross hEρ hEρ (le_refl _) (cA := cρ) (cB := cρ) hcρ
  have hcross := tendsto_tr_faithful_cross hEσ hEρ hEsupp (cA := cσ) (cB := cρ) hcσ
  have hden : Filter.Tendsto
      (fun lam : ℝ => (Tr (((1 - lam : ℝ) : ℂ) • E.toFun ρ + ((lam * cρ : ℝ) : ℂ) • 1)).re)
      (𝓝[>] (0:ℝ)) (𝓝 (Tr (E.toFun ρ)).re) := by
    have key : (Tr (E.toFun ρ)).re
        = (Tr (((1 - (0:ℝ) : ℝ) : ℂ) • E.toFun ρ + (((0:ℝ) * cρ : ℝ) : ℂ) • 1)).re := by simp
    rw [key]
    exact ((QuantumState.continuous_re_trace.comp
      (by fun_prop : Continuous fun lam : ℝ =>
        ((1 - lam : ℝ) : ℂ) • E.toFun ρ + ((lam * cρ : ℝ) : ℂ) • 1)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have hnum : Filter.Tendsto
      (fun lam : ℝ => (Tr ((((1 - lam : ℝ) : ℂ) • E.toFun ρ + ((lam * cρ : ℝ) : ℂ) • 1) *
          (CFC.log (((1 - lam : ℝ) : ℂ) • E.toFun ρ + ((lam * cρ : ℝ) : ℂ) • 1)
            - CFC.log (((1 - lam : ℝ) : ℂ) • E.toFun σ + ((lam * cσ : ℝ) : ℂ) • 1)))).re)
      (𝓝[>] (0:ℝ))
      (𝓝 ((Tr (E.toFun ρ * (CFC.log (E.toFun ρ) - CFC.log (E.toFun σ)))).re)) := by
    have heqf : (fun lam : ℝ => (Tr ((((1 - lam : ℝ) : ℂ) • E.toFun ρ + ((lam * cρ : ℝ) : ℂ) • 1) *
          (CFC.log (((1 - lam : ℝ) : ℂ) • E.toFun ρ + ((lam * cρ : ℝ) : ℂ) • 1)
            - CFC.log (((1 - lam : ℝ) : ℂ) • E.toFun σ + ((lam * cσ : ℝ) : ℂ) • 1)))).re)
        = (fun lam : ℝ =>
            (Tr ((((1 - lam : ℝ) : ℂ) • E.toFun ρ + ((lam * cρ : ℝ) : ℂ) • 1) *
              CFC.log (((1 - lam : ℝ) : ℂ) • E.toFun ρ + ((lam * cρ : ℝ) : ℂ) • 1))).re
            - (Tr ((((1 - lam : ℝ) : ℂ) • E.toFun ρ + ((lam * cρ : ℝ) : ℂ) • 1) *
              CFC.log (((1 - lam : ℝ) : ℂ) • E.toFun σ + ((lam * cσ : ℝ) : ℂ) • 1))).re) := by
      funext lam; rw [mul_sub, map_sub, Complex.sub_re]
    rw [heqf, show (Tr (E.toFun ρ * (CFC.log (E.toFun ρ) - CFC.log (E.toFun σ)))).re
          = (Tr (E.toFun ρ * CFC.log (E.toFun ρ))).re - (Tr (E.toFun ρ * CFC.log (E.toFun σ))).re
          from by rw [mul_sub, map_sub, Complex.sub_re]]
    exact hxlogx.sub hcross
  have hden0 : (Tr (E.toFun ρ)).re ≠ 0 := ne_of_gt (trace_re_pos_of_ne_zero hEρ hEρ0)
  simpa only [umegakiNorm] using hnum.div hden hden0

theorem tendsto_umegakiNorm_faithful {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0) (hsupp : suppLE ρ σ) :
    Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        umegakiNorm ((faithfulApprox E l.val l.2.1.le l.2.2).toFun ρ)
          ((faithfulApprox E l.val l.2.1.le l.2.2).toFun σ))
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (𝓝[>] (0:ℝ)))
      (𝓝 (umegakiNorm (E.toFun ρ) (E.toFun σ))) := by
  have heq : (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        umegakiNorm ((faithfulApprox E l.val l.2.1.le l.2.2).toFun ρ)
          ((faithfulApprox E l.val l.2.1.le l.2.2).toFun σ))
      = (fun lam : ℝ =>
          umegakiNorm (((1 - lam : ℝ) : ℂ) • E.toFun ρ
              + ((lam * ((Tr ρ).re / (Module.finrank ℂ 𝒦 : ℝ)) : ℝ) : ℂ) • 1)
            (((1 - lam : ℝ) : ℂ) • E.toFun σ
              + ((lam * ((Tr σ).re / (Module.finrank ℂ 𝒦 : ℝ)) : ℝ) : ℂ) • 1))
        ∘ (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) := by
    funext l
    simp only [Function.comp_apply,
      faithfulApprox_toFun_eq E l.2.1.le l.2.2 hρ, faithfulApprox_toFun_eq E l.2.1.le l.2.2 hσ]
  rw [heq]
  exact (tendsto_umegakiNorm_faithful_real E hρ hσ hρ0 hsupp).comp Filter.tendsto_comap

/-- **Core non-negative DPI for `umegakiNorm`** (`supp ρ ⊆ supp σ`): assembled from
    `umegakiNorm_faithfulApprox_le` (each faithful `F_λ` decreases `umegakiNorm`) and the
    faithful limit `tendsto_umegakiNorm_faithful`. -/
theorem umegakiNorm_monotone_nn
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : suppLE ρ σ) :
    umegakiNorm (E.toFun ρ) (E.toFun σ) ≤ umegakiNorm ρ σ := by
  by_cases hρ0 : ρ = 0
  · subst hρ0
    rw [show E.toFun 0 = 0 from map_zero E.toCompletelyPositiveMap.toLinearMap]
    simp only [umegakiNorm, zero_mul, map_zero, Complex.zero_re, zero_div, le_refl]
  · have step1 : ∀ (l : {l : ℝ // 0 < l ∧ l ≤ 1}),
        umegakiNorm ((faithfulApprox E l.val l.2.1.le l.2.2).toFun ρ)
          ((faithfulApprox E l.val l.2.1.le l.2.2).toFun σ) ≤ umegakiNorm ρ σ :=
      fun l => umegakiNorm_faithfulApprox_le E hρ hσ hρ0 hsupp l.2.1 l.2.2
    haveI hNeBot : (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
        (𝓝[>] (0:ℝ))).NeBot := by
      refine Filter.comap_neBot fun t ht => ?_
      obtain ⟨U, hU_open, hU0, hU_sub⟩ := mem_nhdsWithin.mp ht
      obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp (hU_open.mem_nhds hU0)
      have hx_pos : (0 : ℝ) < min (δ / 2) 1 := lt_min (by positivity) one_pos
      refine ⟨⟨min (δ / 2) 1, hx_pos, min_le_right _ _⟩, ?_⟩
      apply hU_sub
      refine ⟨hball ?_, hx_pos⟩
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx_pos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    exact le_of_tendsto (tendsto_umegakiNorm_faithful E hρ hσ hρ0 hsupp)
      (Filter.Eventually.of_forall step1)

/-- **Data-processing for the Umegaki relative entropy on non-negative operators.**
    Off-support the right-hand side is `⊤` (trivial); on-support it reduces to the
    real-valued core DPI `umegakiNorm_monotone_nn`. -/
theorem umegakiRelEntropyNN_monotone
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    umegakiRelEntropyNN (E.toFun ρ) (E.toFun σ) ≤ umegakiRelEntropyNN ρ σ := by
  by_cases hsupp : suppLE ρ σ
  · -- support holds: both sides are real, reduce to the core DPI
    have hEρ : (0 : L 𝒦) ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
    have hEσ : (0 : L 𝒦) ≤ E.toFun σ := map_nonneg E.toCompletelyPositiveMap hσ
    have hEsupp : suppLE (E.toFun ρ) (E.toFun σ) := suppLE_of_CPTP E hρ hσ hsupp
    rw [show umegakiRelEntropyNN (E.toFun ρ) (E.toFun σ)
          = ((umegakiNorm (E.toFun ρ) (E.toFun σ) : ℝ) : EReal) from by
        unfold umegakiRelEntropyNN; rw [if_pos hEsupp],
      show umegakiRelEntropyNN ρ σ = ((umegakiNorm ρ σ : ℝ) : EReal) from by
        unfold umegakiRelEntropyNN; rw [if_pos hsupp],
      EReal.coe_le_coe_iff]
    exact umegakiNorm_monotone_nn E hρ hσ hsupp
  · -- support fails: the right-hand side is `⊤`
    have h_RHS : umegakiRelEntropyNN ρ σ = (⊤ : EReal) := by
      unfold umegakiRelEntropyNN; rw [if_neg hsupp]
    rw [h_RHS]; exact le_top

/-! ### α = ∞ as the `α → ∞` limit (Frank–Lieb limiting argument)

Following the same limiting strategy as the `α = 1` case, we show the sandwiched
Rényi divergence converges, as `α → ∞`, to the max-relative entropy
`log ‖σ^{-1/2} ρ σ^{-1/2}‖`, and re-derive its data-processing inequality from the
finite-`α` monotonicity (`sandwichedRenyiDiv_monotone`) by passing to the limit.

The convergence rests on the elementary squeeze `‖B‖^α ≤ Tr(B^α) ≤ d·‖B‖^α` for a
non-negative operator `B` (with `d = dim ℋ`), i.e. the `ℓ^α → ℓ^∞` collapse of the
spectrum. -/

/-- For a non-negative operator, the operator norm (largest eigenvalue) is bounded
    by the (real) trace (the sum of the eigenvalues). -/
lemma norm_le_re_trace {C : L ℋ} (hC : 0 ≤ C) : ‖C‖ ≤ (Tr C).re := by
  classical
  have hpos : C.IsPositive := (LinearMap.nonneg_iff_isPositive C).mp hC
  have hsym : C.IsSymmetric := hpos.isSymmetric
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  set b := hsym.eigenvectorBasis hn with hb
  set eig := hsym.eigenvalues hn with heig
  have h_eig_nn : ∀ i, 0 ≤ eig i := fun i => hpos.nonneg_eigenvalues hn i
  have h_eig_apply : ∀ i, C (b i) = ((eig i : ℝ) : ℂ) • b i := hsym.apply_eigenvectorBasis hn
  have htr : (Tr C).re = ∑ i, eig i := hsym.re_trace_eq_sum_eigenvalues hn
  -- `‖C‖` is attained as an eigenvalue.
  have hmemℝ : ‖C‖ ∈ spectrum ℝ C := CStarAlgebra.norm_mem_spectrum_of_nonneg hC
  have hmemℂ : (‖C‖ : ℂ) ∈ spectrum ℂ C := by
    have h := hmemℝ; rw [← spectrum.preimage_algebraMap ℂ] at h; simpa using h
  have hev : Module.End.HasEigenvalue C (‖C‖ : ℂ) :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hmemℂ
  obtain ⟨w, hw⟩ := hev.exists_hasEigenvector
  have hCw : C w = (‖C‖ : ℂ) • w := Module.End.mem_eigenspace_iff.mp hw.1
  have hw_ne : w ≠ 0 := hw.2
  obtain ⟨j, hcj⟩ : ∃ j, inner ℂ (b j) w ≠ (0 : ℂ) := by
    by_contra h; push_neg at h
    apply hw_ne
    have hrep : w = ∑ i, inner ℂ (b i) w • b i := (b.sum_repr' w).symm
    rw [hrep]; simp [h]
  have hkey : (eig j : ℂ) * inner ℂ (b j) w = (‖C‖ : ℂ) * inner ℂ (b j) w := by
    have h1 : inner ℂ (b j) (C w) = (‖C‖ : ℂ) * inner ℂ (b j) w := by rw [hCw, inner_smul_right]
    have h2 : inner ℂ (b j) (C w) = (eig j : ℂ) * inner ℂ (b j) w := by
      rw [show inner ℂ (b j) (C w) = inner ℂ (C (b j)) w from (hsym (b j) w).symm,
        h_eig_apply j, inner_smul_left, Complex.conj_ofReal]
    rw [← h1, h2]
  have hej : eig j = ‖C‖ := by exact_mod_cast mul_right_cancel₀ hcj hkey
  rw [htr, ← hej]
  exact Finset.single_le_sum (fun i _ => h_eig_nn i) (Finset.mem_univ j)

omit [Nontrivial ℋ] in
/-- For a non-negative operator, the (real) trace is bounded by `dim ℋ` times the
    operator norm. -/
lemma re_trace_le_finrank_norm {C : L ℋ} (hC : 0 ≤ C) :
    (Tr C).re ≤ (Module.finrank ℂ ℋ : ℝ) * ‖C‖ := by
  have hle : C ≤ algebraMap ℝ (L ℋ) ‖C‖ :=
    IsSelfAdjoint.le_algebraMap_norm_self (IsSelfAdjoint.of_nonneg hC)
  have hdiff : (0 : L ℋ) ≤ algebraMap ℝ (L ℋ) ‖C‖ - C := sub_nonneg.mpr hle
  have htr : 0 ≤ (Tr (algebraMap ℝ (L ℋ) ‖C‖ - C)).re := by
    have h := ((LinearMap.nonneg_iff_isPositive _).mp hdiff).trace_nonneg
    rw [Complex.le_def] at h; exact h.1
  rw [map_sub, Complex.sub_re] at htr
  have htr1 : (Tr (algebraMap ℝ (L ℋ) ‖C‖)).re = (Module.finrank ℂ ℋ : ℝ) * ‖C‖ := by
    rw [show (algebraMap ℝ (L ℋ)) ‖C‖ = ((‖C‖ : ℝ) : ℂ) • (1 : L ℋ) by
      rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul],
      map_smul, smul_eq_mul, LinearMap.trace_one, Complex.mul_re]
    simp [mul_comm]
  rw [htr1] at htr
  linarith

/-- **The `α → ∞` limit.** For positive-definite `ρ, σ`, the sandwiched Rényi
    divergence converges, as `α → ∞`, to the max-relative entropy `maxRelEntropyNN ρ σ`
    (`= log ‖σ^{-1/2} ρ σ^{-1/2}‖`). -/
lemma sandwichedRenyiDiv_tendsto_maxRel
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    Filter.Tendsto (fun α => ((sandwichedRenyiDiv α ρ σ : ℝ) : EReal)) Filter.atTop
      (𝓝 (maxRelEntropyNN ρ σ)) := by
  have hρ_nn := nonneg_of_pdSetLM hρ
  have hσ_nn := nonneg_of_pdSetLM hσ
  have hσ_sp : IsStrictlyPositive σ := ⟨hσ_nn, isUnit_of_pdSetLM hσ⟩
  have hρ0 : ρ ≠ 0 := (isUnit_of_pdSetLM hρ).ne_zero
  have hsupp : suppLE ρ σ := suppLE_of_pdSetLM_right ρ hσ
  rw [maxRelEntropyNN_eq_log_norm hsupp]
  refine EReal.tendsto_coe.mpr ?_
  have hr_pos : 0 < (Tr ρ).re := trace_re_pos_of_pdSetLM hρ
  set r := (Tr ρ).re with hr
  set d := (Module.finrank ℂ ℋ : ℝ) with hd
  have hd_pos : 0 < d := by rw [hd]; exact_mod_cast Module.finrank_pos
  set nA := ‖CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2))‖ with hnA
  have hnA_pos : 0 < nA := by
    rw [hnA, ← sInf_maxRelSet_eq_norm hρ_nn hσ_nn hsupp]
    exact sInf_maxRelSet_pos hρ_nn hσ_nn hρ0 hsupp
  have hg_cont : Continuous (fun s : ℝ => ‖CFC.rpow σ s * ρ * CFC.rpow σ s‖) :=
    (((CFC.continuous_rpow_exponent hσ_sp).mul continuous_const).mul
      (CFC.continuous_rpow_exponent hσ_sp)).norm
  -- `(1-α)/(2α) → -1/2`.
  have hβ : Filter.Tendsto (fun α : ℝ => (1 - α) / (2 * α)) Filter.atTop (𝓝 (-(1/2))) := by
    have heq : (fun α : ℝ => (1 - α) / (2 * α)) =ᶠ[Filter.atTop] (fun α => 1 / (2 * α) - 1/2) := by
      filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with α hα
      have hαne : α ≠ 0 := ne_of_gt hα
      field_simp
    rw [Filter.tendsto_congr' heq]
    have h2α : Filter.Tendsto (fun α : ℝ => 2 * α) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) Filter.tendsto_id
    have h0 : Filter.Tendsto (fun α : ℝ => 1 / (2 * α)) Filter.atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds h2α
    simpa using h0.sub_const (1/2)
  have hm_tendsto : Filter.Tendsto
      (fun α : ℝ => ‖CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α))‖)
      Filter.atTop (𝓝 nA) := by
    have := (hg_cont.tendsto (-(1/2))).comp hβ
    simpa [hnA, Function.comp] using this
  have h_logm : Filter.Tendsto
      (fun α : ℝ => Real.log ‖CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α))‖)
      Filter.atTop (𝓝 (Real.log nA)) :=
    (Real.continuousAt_log (ne_of_gt hnA_pos)).tendsto.comp hm_tendsto
  have h_inv : Filter.Tendsto (fun α : ℝ => 1 / (α - 1)) Filter.atTop (𝓝 0) := by
    have hsub : Filter.Tendsto (fun α : ℝ => α - 1) Filter.atTop Filter.atTop := by
      simpa using Filter.tendsto_atTop_add_const_right Filter.atTop (-1) Filter.tendsto_id
    exact Filter.Tendsto.div_atTop tendsto_const_nhds hsub
  have h_ratio : Filter.Tendsto (fun α : ℝ => α / (α - 1)) Filter.atTop (𝓝 1) := by
    have heq : (fun α : ℝ => α / (α - 1)) =ᶠ[Filter.atTop] (fun α => 1 + 1 / (α - 1)) := by
      filter_upwards [Filter.eventually_gt_atTop (1:ℝ)] with α hα
      have : α - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hα)
      field_simp; ring
    rw [Filter.tendsto_congr' heq]
    simpa using tendsto_const_nhds.add h_inv
  set Lf : ℝ → ℝ := fun α =>
    α / (α - 1) * Real.log ‖CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α))‖
      - 1 / (α - 1) * Real.log r with hLf
  set Uf : ℝ → ℝ := fun α =>
    α / (α - 1) * Real.log ‖CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α))‖
      + 1 / (α - 1) * (Real.log d - Real.log r) with hUf
  have hL : Filter.Tendsto Lf Filter.atTop (𝓝 (Real.log nA)) := by
    rw [hLf]; simpa using (h_ratio.mul h_logm).sub (h_inv.mul_const (Real.log r))
  have hU : Filter.Tendsto Uf Filter.atTop (𝓝 (Real.log nA)) := by
    rw [hUf]; simpa using (h_ratio.mul h_logm).add (h_inv.mul_const (Real.log d - Real.log r))
  have hbounds : ∀ᶠ α : ℝ in Filter.atTop,
      Lf α ≤ sandwichedRenyiDiv α ρ σ ∧ sandwichedRenyiDiv α ρ σ ≤ Uf α := by
    filter_upwards [Filter.eventually_gt_atTop (1:ℝ)] with α hα1
    have hα0 : 0 < α := by linarith
    have hαm1 : 0 < α - 1 := by linarith
    have hinv_nn : 0 ≤ 1 / (α - 1) := le_of_lt (div_pos one_pos hαm1)
    set Mα := CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α)) with hMαdef
    have hMα_pd : Mα ∈ pdSetLM (ℋ := ℋ) := by
      have hPpd : CFC.rpow σ ((1 - α) / (2 * α)) ∈ pdSetLM (ℋ := ℋ) := pdSetLM_rpow_ne hσ
      have hPsa : IsSelfAdjoint (CFC.rpow σ ((1 - α) / (2 * α))) :=
        IsSelfAdjoint.of_nonneg (nonneg_of_pdSetLM hPpd)
      have h := pdSetLM_conj hρ (isUnit_of_pdSetLM hPpd)
      rwa [hPsa.star_eq] at h
    have hMα_nn : (0 : L ℋ) ≤ Mα := nonneg_of_pdSetLM hMα_pd
    have hm_pos : 0 < ‖Mα‖ := norm_pos_iff.mpr (isUnit_of_pdSetLM hMα_pd).ne_zero
    have hCnn : (0 : L ℋ) ≤ CFC.rpow Mα α := CFC.rpow_nonneg
    have hnorm_eq : ‖CFC.rpow Mα α‖ = ‖Mα‖ ^ α := CFC.norm_rpow Mα hα0 hMα_nn
    set q := (sandwichedQuasi α ρ σ).re with hq
    have hq_eq : q = (Tr (CFC.rpow Mα α)).re := by rw [hq]; rfl
    have hq_lo : ‖Mα‖ ^ α ≤ q := by rw [hq_eq, ← hnorm_eq]; exact norm_le_re_trace hCnn
    have hq_hi : q ≤ d * ‖Mα‖ ^ α := by
      rw [hq_eq, ← hnorm_eq]; exact re_trace_le_finrank_norm hCnn
    have hmα_pos : 0 < ‖Mα‖ ^ α := Real.rpow_pos_of_pos hm_pos α
    have hq_pos : 0 < q := lt_of_lt_of_le hmα_pos hq_lo
    have hlogq_lo : α * Real.log ‖Mα‖ ≤ Real.log q := by
      rw [← Real.log_rpow hm_pos]; exact Real.log_le_log hmα_pos hq_lo
    have hlogq_hi : Real.log q ≤ Real.log d + α * Real.log ‖Mα‖ := by
      have h := Real.log_le_log hq_pos hq_hi
      rwa [Real.log_mul (ne_of_gt hd_pos) (ne_of_gt hmα_pos), Real.log_rpow hm_pos] at h
    have hD : sandwichedRenyiDiv α ρ σ = 1 / (α - 1) * (Real.log q - Real.log r) := by
      unfold sandwichedRenyiDiv
      rw [← hq, ← hr, Real.log_div (ne_of_gt hq_pos) (ne_of_gt hr_pos)]
    refine ⟨?_, ?_⟩
    · simp only [hLf]; rw [← hMαdef, hD]
      have key : α * Real.log ‖Mα‖ - Real.log r ≤ Real.log q - Real.log r := by linarith
      have hstep := mul_le_mul_of_nonneg_left key hinv_nn
      calc α / (α - 1) * Real.log ‖Mα‖ - 1 / (α - 1) * Real.log r
            = 1 / (α - 1) * (α * Real.log ‖Mα‖ - Real.log r) := by ring
        _ ≤ 1 / (α - 1) * (Real.log q - Real.log r) := hstep
    · simp only [hUf]; rw [← hMαdef, hD]
      have key : Real.log q - Real.log r ≤ (Real.log d + α * Real.log ‖Mα‖) - Real.log r := by
        linarith
      have hstep := mul_le_mul_of_nonneg_left key hinv_nn
      calc 1 / (α - 1) * (Real.log q - Real.log r)
            ≤ 1 / (α - 1) * ((Real.log d + α * Real.log ‖Mα‖) - Real.log r) := hstep
        _ = α / (α - 1) * Real.log ‖Mα‖ + 1 / (α - 1) * (Real.log d - Real.log r) := by
            ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · exact hbounds.mono (fun α h => h.1)
  · exact hbounds.mono (fun α h => h.2)

/-- **Data-processing for the max-relative entropy, via the `α → ∞` limit**
    (Frank–Lieb's limiting argument; positive-definite case). An alternative proof of
    `maxRelEntropyNN_monotone`: the finite-`α` monotonicity passes to the limit. -/
theorem maxRelEntropyNN_monotone_via_limit
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (hEρ : E.toFun ρ ∈ pdSetLM (ℋ := 𝒦)) (hEσ : E.toFun σ ∈ pdSetLM (ℋ := 𝒦)) :
    maxRelEntropyNN (E.toFun ρ) (E.toFun σ) ≤ maxRelEntropyNN ρ σ := by
  have hlim1 := sandwichedRenyiDiv_tendsto_maxRel hEρ hEσ
  have hlim2 := sandwichedRenyiDiv_tendsto_maxRel hρ hσ
  refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ)] with α hα1
  exact_mod_cast sandwichedRenyiDiv_monotone E (by linarith) (ne_of_gt hα1) hρ hσ hEρ hEσ

/-- **The `α → ∞` limit, positive-semidefinite case.** For non-negative `ρ, σ` with
    `suppLE ρ σ` and `ρ ≠ 0`, the sandwiched Rényi divergence converges, as `α → ∞`, to
    the max-relative entropy `maxRelEntropyNN ρ σ` (`= log ‖σ^{-1/2} ρ σ^{-1/2}‖`,
    Moore–Penrose power). The pd proof carries over: exponent-continuity
    `tendsto_rpow_exponent_atTop` holds even at singular `σ`, and `‖M_α‖ > 0` holds
    *eventually* (it converges to `‖A‖ > 0`). -/
lemma sandwichedRenyiDiv_tendsto_maxRel_nn
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : suppLE ρ σ) (hρ0 : ρ ≠ 0) :
    Filter.Tendsto (fun α => ((sandwichedRenyiDiv α ρ σ : ℝ) : EReal)) Filter.atTop
      (𝓝 (maxRelEntropyNN ρ σ)) := by
  rw [maxRelEntropyNN_eq_log_norm hsupp]
  refine EReal.tendsto_coe.mpr ?_
  have hr_pos : 0 < (Tr ρ).re := trace_re_pos_of_ne_zero hρ hρ0
  set r := (Tr ρ).re with hr
  set d := (Module.finrank ℂ ℋ : ℝ) with hd
  have hd_pos : 0 < d := by rw [hd]; exact_mod_cast Module.finrank_pos
  set nA := ‖CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2))‖ with hnA
  have hnA_pos : 0 < nA := by
    rw [hnA, ← sInf_maxRelSet_eq_norm hρ hσ hsupp]
    exact sInf_maxRelSet_pos hρ hσ hρ0 hsupp
  have hM_tendsto : Filter.Tendsto
      (fun α : ℝ => CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α)))
      Filter.atTop (𝓝 (CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2)))) :=
    ((tendsto_rpow_exponent_atTop hσ).mul tendsto_const_nhds).mul (tendsto_rpow_exponent_atTop hσ)
  have hm_tendsto : Filter.Tendsto
      (fun α : ℝ => ‖CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α))‖)
      Filter.atTop (𝓝 nA) := by rw [hnA]; exact hM_tendsto.norm
  have h_logm : Filter.Tendsto
      (fun α : ℝ => Real.log ‖CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α))‖)
      Filter.atTop (𝓝 (Real.log nA)) :=
    (Real.continuousAt_log (ne_of_gt hnA_pos)).tendsto.comp hm_tendsto
  have hev_pos : ∀ᶠ α : ℝ in Filter.atTop,
      0 < ‖CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α))‖ :=
    hm_tendsto.eventually (eventually_gt_nhds hnA_pos)
  have h_inv : Filter.Tendsto (fun α : ℝ => 1 / (α - 1)) Filter.atTop (𝓝 0) := by
    have hsub : Filter.Tendsto (fun α : ℝ => α - 1) Filter.atTop Filter.atTop := by
      simpa using Filter.tendsto_atTop_add_const_right Filter.atTop (-1) Filter.tendsto_id
    exact Filter.Tendsto.div_atTop tendsto_const_nhds hsub
  have h_ratio : Filter.Tendsto (fun α : ℝ => α / (α - 1)) Filter.atTop (𝓝 1) := by
    have heq : (fun α : ℝ => α / (α - 1)) =ᶠ[Filter.atTop] (fun α => 1 + 1 / (α - 1)) := by
      filter_upwards [Filter.eventually_gt_atTop (1:ℝ)] with α hα
      have : α - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hα)
      field_simp; ring
    rw [Filter.tendsto_congr' heq]
    simpa using tendsto_const_nhds.add h_inv
  set Lf : ℝ → ℝ := fun α =>
    α / (α - 1) * Real.log ‖CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α))‖
      - 1 / (α - 1) * Real.log r with hLf
  set Uf : ℝ → ℝ := fun α =>
    α / (α - 1) * Real.log ‖CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α))‖
      + 1 / (α - 1) * (Real.log d - Real.log r) with hUf
  have hL : Filter.Tendsto Lf Filter.atTop (𝓝 (Real.log nA)) := by
    rw [hLf]; simpa using (h_ratio.mul h_logm).sub (h_inv.mul_const (Real.log r))
  have hU : Filter.Tendsto Uf Filter.atTop (𝓝 (Real.log nA)) := by
    rw [hUf]; simpa using (h_ratio.mul h_logm).add (h_inv.mul_const (Real.log d - Real.log r))
  have hbounds : ∀ᶠ α : ℝ in Filter.atTop,
      Lf α ≤ sandwichedRenyiDiv α ρ σ ∧ sandwichedRenyiDiv α ρ σ ≤ Uf α := by
    filter_upwards [Filter.eventually_gt_atTop (1:ℝ), hev_pos] with α hα1 hm_pos
    have hα0 : 0 < α := by linarith
    have hαm1 : 0 < α - 1 := by linarith
    have hinv_nn : 0 ≤ 1 / (α - 1) := le_of_lt (div_pos one_pos hαm1)
    set Mα := CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α)) with hMαdef
    have hMα_nn : (0 : L ℋ) ≤ Mα := conjugate_nonneg_of_nonneg hρ CFC.rpow_nonneg
    have hCnn : (0 : L ℋ) ≤ CFC.rpow Mα α := CFC.rpow_nonneg
    have hnorm_eq : ‖CFC.rpow Mα α‖ = ‖Mα‖ ^ α := CFC.norm_rpow Mα hα0 hMα_nn
    set q := (sandwichedQuasi α ρ σ).re with hq
    have hq_eq : q = (Tr (CFC.rpow Mα α)).re := by rw [hq]; rfl
    have hq_lo : ‖Mα‖ ^ α ≤ q := by rw [hq_eq, ← hnorm_eq]; exact norm_le_re_trace hCnn
    have hq_hi : q ≤ d * ‖Mα‖ ^ α := by
      rw [hq_eq, ← hnorm_eq]; exact re_trace_le_finrank_norm hCnn
    have hmα_pos : 0 < ‖Mα‖ ^ α := Real.rpow_pos_of_pos hm_pos α
    have hq_pos : 0 < q := lt_of_lt_of_le hmα_pos hq_lo
    have hlogq_lo : α * Real.log ‖Mα‖ ≤ Real.log q := by
      rw [← Real.log_rpow hm_pos]; exact Real.log_le_log hmα_pos hq_lo
    have hlogq_hi : Real.log q ≤ Real.log d + α * Real.log ‖Mα‖ := by
      have h := Real.log_le_log hq_pos hq_hi
      rwa [Real.log_mul (ne_of_gt hd_pos) (ne_of_gt hmα_pos), Real.log_rpow hm_pos] at h
    have hD : sandwichedRenyiDiv α ρ σ = 1 / (α - 1) * (Real.log q - Real.log r) := by
      unfold sandwichedRenyiDiv
      rw [← hq, ← hr, Real.log_div (ne_of_gt hq_pos) (ne_of_gt hr_pos)]
    refine ⟨?_, ?_⟩
    · simp only [hLf]; rw [← hMαdef, hD]
      have key : α * Real.log ‖Mα‖ - Real.log r ≤ Real.log q - Real.log r := by linarith
      have hstep := mul_le_mul_of_nonneg_left key hinv_nn
      calc α / (α - 1) * Real.log ‖Mα‖ - 1 / (α - 1) * Real.log r
            = 1 / (α - 1) * (α * Real.log ‖Mα‖ - Real.log r) := by ring
        _ ≤ 1 / (α - 1) * (Real.log q - Real.log r) := hstep
    · simp only [hUf]; rw [← hMαdef, hD]
      have key : Real.log q - Real.log r ≤ (Real.log d + α * Real.log ‖Mα‖) - Real.log r := by
        linarith
      have hstep := mul_le_mul_of_nonneg_left key hinv_nn
      calc 1 / (α - 1) * (Real.log q - Real.log r)
            ≤ 1 / (α - 1) * ((Real.log d + α * Real.log ‖Mα‖) - Real.log r) := hstep
        _ = α / (α - 1) * Real.log ‖Mα‖ + 1 / (α - 1) * (Real.log d - Real.log r) := by ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · exact hbounds.mono (fun α h => h.1)
  · exact hbounds.mono (fun α h => h.2)

/-- **Data-processing for the max-relative entropy, positive-semidefinite case, via the
    `α → ∞` limit.** The positive-semidefinite analogue of
    `maxRelEntropyNN_monotone_via_limit` (cf. `umegakiRelEntropyNN_monotone` for `α=1`):
    for non-negative `ρ, σ` with `suppLE ρ σ` and a CPTP map `E`,
    `maxRelEntropyNN (Eρ) (Eσ) ≤ maxRelEntropyNN ρ σ`, obtained by passing the finite-`α`
    non-negative monotonicity (`sandwichedRenyiDivNN_monotone`) to the limit. -/
theorem maxRelEntropyNN_monotone_via_limit_nn
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : suppLE ρ σ) :
    maxRelEntropyNN (E.toFun ρ) (E.toFun σ) ≤ maxRelEntropyNN ρ σ := by
  by_cases hρ0 : ρ = 0
  · subst hρ0
    have hEsupp : suppLE (E.toFun (0 : L ℋ)) (E.toFun σ) := suppLE_of_CPTP E hρ hσ hsupp
    rw [maxRelEntropyNN_eq_log_norm hEsupp, maxRelEntropyNN_eq_log_norm hsupp]
    have hE0 : E.toFun (0 : L ℋ) = 0 := map_zero E.toCompletelyPositiveMap.toLinearMap
    rw [hE0]; simp
  · have hEρ : (0 : L 𝒦) ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
    have hEσ : (0 : L 𝒦) ≤ E.toFun σ := map_nonneg E.toCompletelyPositiveMap hσ
    have hEsupp : suppLE (E.toFun ρ) (E.toFun σ) := suppLE_of_CPTP E hρ hσ hsupp
    have hEρ0 : E.toFun ρ ≠ 0 := CPTP_toFun_ne_zero E hρ hρ0
    have hlim1 := sandwichedRenyiDiv_tendsto_maxRel_nn hEρ hEσ hEsupp hEρ0
    have hlim2 := sandwichedRenyiDiv_tendsto_maxRel_nn hρ hσ hsupp hρ0
    refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
    filter_upwards [Filter.eventually_gt_atTop (1:ℝ)] with α hα1
    have hval : ∀ {ℋ'' : Type u} [Qudit ℋ''] [Nontrivial ℋ''] (ρ'' σ'' : L ℋ''),
        suppLE ρ'' σ'' →
        sandwichedRenyiDivNN α ρ'' σ'' = ((sandwichedRenyiDiv α ρ'' σ'' : ℝ) : EReal) := by
      intro ℋ'' _ _ ρ'' σ'' hs
      unfold sandwichedRenyiDivNN
      rw [if_neg]
      rintro (⟨_, hns⟩ | ⟨hlt, _⟩)
      · exact hns hs
      · linarith
    have hmono := sandwichedRenyiDivNN_monotone E (by linarith) (ne_of_gt hα1) hρ hσ
    rw [hval _ _ hEsupp, hval _ _ hsupp] at hmono
    exact hmono

end Umegaki

end SandwichedRenyiRelativeEntropy
