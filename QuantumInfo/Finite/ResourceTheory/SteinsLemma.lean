/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa, Rodolfo R. Soldati
-/
import QuantumInfo.Finite.ResourceTheory.FreeState
import QuantumInfo.Finite.ResourceTheory.HypothesisTesting
import QuantumInfo.Finite.Pinching
import QuantumInfo.ForMathlib.Matrix
import QuantumInfo.ForMathlib.LimSupInf
import QuantumInfo.ForMathlib.HermitianMat.Jordan
import QuantumInfo.ForMathlib.HermitianMat.CfcOrder

import Mathlib.Tactic.Bound

open NNReal
open scoped ENNReal
open ComplexOrder
open Topology
open scoped Prob
open scoped OptimalHypothesisRate
open ResourcePretheory
open FreeStateTheory
open UnitalPretheory
open UnitalFreeStateTheory
open scoped RealInnerProductSpace InnerProductSpace

namespace SteinsLemma

variable {ι : Type*} [UnitalFreeStateTheory ι]
variable {i : ι}

/-- The \tilde{σ}_n defined in Lemma 6, also in equation (S40) in Lemma 7. -/
noncomputable def Lemma6_σn (m : ℕ) (σf : MState (H i)) (σₘ : MState (H (i ^ m))) : (n : ℕ) → MState (H (i ^ n)) :=
  fun n ↦ (σₘ ⊗ᵣ^[n / m] ⊗ᵣ σf ⊗ᵣ^[n % m]).relabel <| .cast <| congrArg H (by
    rw [← pow_mul, ← spacePow_add, Nat.div_add_mod n m]
  )

theorem Lemma6_σn_IsFree {σ₁ : MState (H i)} {σₘ : (m : ℕ) → MState (H (i ^ m))} (hσ₁_free : IsFree σ₁)
    (hσₘ : ∀ (m : ℕ), σₘ m ∈ IsFree) (m n : ℕ) : Lemma6_σn m σ₁ (σₘ m) n ∈ IsFree := by
  rw [Lemma6_σn, relabel_cast_isFree]
  · apply free_prod --pick a better name / alias for this
    · exact (hσₘ m).npow (n / m)
    · exact hσ₁_free.npow (n % m)
  · rw [← pow_mul, ← spacePow_add, Nat.div_add_mod n m]

/-- Lemma 6 from the paper.
We _did_ end up doing the version that "works also in the case of ε = 0", which is nice.
-/
private theorem Lemma6 {m : ℕ} (hm : 0 < m) (ρ σf : MState (H i)) (σₘ : MState (H (i ^ m)))
    [σf.M.NonSingular] {ε : Prob} (hε : ε < 1) :
  Filter.atTop.limsup (fun n ↦ —log β_ ε(ρ ⊗ᵣ^[n]‖{Lemma6_σn m σf σₘ n}) / n) ≤ 𝐃(ρ ⊗ᵣ^[m]‖σₘ) / m
  := by

  set σn := Lemma6_σn m σf σₘ with hσn

  have h_add : ∀ α n, D̃_ α(ρ ⊗ᵣ^[n]‖σn n) = (n/m : ℕ) * D̃_ α(ρ ⊗ᵣ^[m]‖σₘ) + (n%m : ℕ) * D̃_ α(ρ‖σf):= by
    --"Break apart" σn, and apply additivity of `SandwichedRelRentropy`.
    intro α n
    rw [hσn, Lemma6_σn]
    have hnm_add := Nat.div_add_mod n m
    rw [statePow_rw hnm_add.symm, statePow_add_relabel]
    have hnm_eq : (i ^ (m * (n / m)) * i ^ (n % m)) = (i ^ m) ^ (n / m) * i ^ (n % m) := by
      rw [pow_mul]
    have h_Hn_eq : H (i ^ n) = H ((i ^ m) ^ (n / m) * i ^ (n % m)) := by
      rw [← pow_mul, ← pow_add, hnm_add]
    simp only [MState.relabel_relabel, Equiv.cast_trans]
    rw [← sandwichedRelRentropy_statePow]
    rw [← sandwichedRelRentropy_statePow]
    rw [← sandwichedRelRentropy_prodRelabel]

    gcongr
    · rw [MState.eq_relabel_iff]
      simp only [MState.relabel_relabel, Equiv.cast_symm, Equiv.cast_trans]
      rw [prodRelabel_relabel_cast_prod _ _ _ ((pow_mul ..).symm) rfl]
      congr
      rw [statePow_mul_relabel]
      simp
    · simp

  --This will probably need 1 < α actually
  have h_α : ∀ α, (1 < α) → Filter.atTop.limsup (fun n ↦ —log β_ ε(ρ ⊗ᵣ^[n]‖{σn n}) / n) ≤
      D̃_ α(ρ ⊗ᵣ^[m]‖σₘ) / m := by
    intro α hα
    apply le_of_le_of_eq (b := Filter.atTop.limsup (fun n ↦ D̃_ α(ρ ⊗ᵣ^[n]‖σn n) / n))
    · --Apply the "[81] Lemma 5" to ρ⊗^n and σn
      have h_lem5 (n) := OptimalHypothesisRate.Ref81Lem5 (ρ ⊗ᵣ^[n]) (σn n) ε hε α hα

      --Upper-bound β on the LHS with this lemma
      --Distribute the limsup over subtraction
      --The term on the right is a constant, divided by n, which converges to zero.
      --Dropping that leaves the identity
      generalize_proofs pf1 pf2 at h_lem5
      let x n :=  —log β_ ε(ρ ⊗ᵣ^[n]‖{σn n})
      let y n := D̃_ α(ρ ⊗ᵣ^[n]‖σn n)
      set z := —log (1 - ε) * (ENNReal.ofNNReal ⟨α, pf1⟩) / (ENNReal.ofNNReal ⟨α - 1, pf2⟩)

      have hz : z ≠ ⊤ := by
        unfold z
        have hz1 : —log (1 - ε) ≠ ⊤ := by
          --TODO: should be `bound`, ideally
          simp [Subtype.eq_iff]
          have : (ε : ℝ) < 1 := hε
          linarith
        have hz2 : (ENNReal.ofNNReal ⟨α - 1, pf2⟩) ≠ 0 := by
          --TODO: should be `bound`, ideally
          simp [NNReal.eq_iff]
          linarith
        finiteness

      change ∀ n, x n ≤ y n + z at h_lem5
      change Filter.atTop.limsup (fun n ↦ x n / n) ≤ Filter.atTop.limsup (fun n ↦ y n / n)
      exact extracted_limsup_inequality z hz y x h_lem5

    · suffices Filter.atTop.Tendsto (fun n ↦ D̃_ α(ρ ⊗ᵣ^[n]‖σn n) / n)  (𝓝 (D̃_ α(ρ ⊗ᵣ^[m]‖σₘ) / m))by
        exact this.limsup_eq
      conv =>
        enter [1,n]
        equals ((↑(n / m) * D̃_ α(ρ ⊗ᵣ^[m]‖σₘ)) / n + (↑(n % m) * D̃_ α(ρ‖σf)) / n) =>
          simp_rw [h_add, ENNReal.add_div]
      conv => enter [3,1]; apply (add_zero _).symm
      apply Filter.Tendsto.add
      · simp_rw [div_eq_mul_inv, mul_comm, ← mul_assoc]
        conv =>
          enter [3,1]
          apply (one_mul _).symm
        rw [← mul_assoc]
        cases D̃_ α(ρ ⊗ᵣ^[m]‖σₘ)
        · simp
          --This is true for all x past m.
          apply tendsto_nhds_of_eventually_eq
          refine Filter.eventually_atTop.mpr ?_
          use m
          intros
          rw [ENNReal.mul_top]
          apply (ENNReal.mul_pos ?_ ?_).ne'
          · simp only [ne_eq, ENNReal.inv_eq_zero, ENNReal.natCast_ne_top, not_false_eq_true]
          · simp
            omega
        · rename_i v
          suffices Filter.atTop.Tendsto (fun x ↦ (x:ℝ)⁻¹ * ↑(x / m) * (v:ℝ) : ℕ → ℝ) (𝓝 ((1 / m) * (v : ℝ))) by
            --Similar to the "convert ENNReal.tendsto_ofReal this" below. Just push casts through
            convert ENNReal.tendsto_ofReal this
            · rename_i x
              cases x
              · simp
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity)]
              simp
              norm_cast
            · rw [ENNReal.ofReal_mul (by positivity), one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
              simp
          exact (Filter.Tendsto_inv_nat_mul_div_real m).mul tendsto_const_nhds
      · suffices Filter.atTop.Tendsto (fun x ↦ (x % m : ℕ) * (D̃_ α(ρ‖σf)).toReal / x) (𝓝 0) by
          --Convert a Tendsto over ENNReal to one over Real
          convert ENNReal.tendsto_ofReal this
          · rename_i x
            cases x
            · simp
            rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by positivity)]
            congr
            · simp
            · rw [ENNReal.ofReal_toReal (by finiteness)]
            · rw [ENNReal.ofReal_natCast]
          · simp
        apply bdd_le_mul_tendsto_zero (b := 0) (B := m * D̃_ α(ρ‖σf).toReal)
        · exact Filter.Eventually.of_forall (fun _ ↦ by positivity)
        · apply Filter.Eventually.of_forall (fun _ ↦ ?_)
          exact mul_le_mul_of_nonneg_right (mod_cast (Nat.mod_lt _ hm).le) (by positivity)
        · exact tendsto_inverse_atTop_nhds_zero_nat

  --Take the limit as α → 1.
  replace h_α : Filter.atTop.limsup (fun n ↦ —log β_ ε(ρ ⊗ᵣ^[n]‖{σn n}) / n) ≤ 𝐃(ρ ⊗ᵣ^[m]‖σₘ) / m := by
    refine ge_of_tendsto (x :=  (𝓝[>] 1)) ?_ (eventually_nhdsWithin_of_forall h_α)
    apply tendsto_nhdsWithin_of_tendsto_nhds
    convert ContinuousAt.tendsto ?_ using 3
    have _ := ENNReal.continuous_div_const m (by positivity)
    have _ := (sandwichedRelRentropy.continuousOn (ρ ⊗ᵣ^[m]) σₘ).continuousAt (Ioi_mem_nhds zero_lt_one)
    fun_prop

  exact h_α

section Lemma7

open MatrixMap
open Matrix
open PosSemidef

-- TODO: Commutation and order relations about `proj_le` specified in the text
-- between Eqs. (S77) and (S78)

open scoped HermitianMat in
theorem LemmaS2liminf {ε3 : Prob} {ε4 : ℝ≥0} (hε4 : 0 < ε4)
  {d : ℕ → Type*} [∀ n, Fintype (d n)] [∀ n, DecidableEq (d n)] (ρ : (n : ℕ) → MState (d n)) (σ : (n : ℕ) → MState (d n))
  {Rinf : ℝ≥0} (hRinf : Rinf ≥ Filter.atTop.liminf (fun (n : ℕ) ↦ —log β_ ε3(ρ n‖{σ n}) / n))
  :
  (Filter.atTop.liminf (fun (n : ℕ) ↦ ⟪{(ρ n).M ≥ₚ (Real.exp (n * (Rinf + ε4))) • (σ n).M}, (ρ n).M⟫) ≤ 1 - ε3)
  := by
  by_contra h
  push_neg at h
  replace h := Filter.eventually_lt_of_lt_liminf h ?_
  · replace h := Filter.eventually_atTop.mp h
    obtain ⟨n₀, h⟩ := h
    --Can assume that n₀ is positive. Then we don't have to worry about nonzero values down the line
    wlog hn₀ : 0 < n₀
    · exact this hε4 ρ σ hRinf 1 (fun b hb ↦ h _ <| by omega) zero_lt_one
    let T (n : ℕ) := {(ρ n).M ≥ₚ (Real.exp (n * (Rinf + ε4))) • (σ n).M}
    have hT : ∀ n ≥ n₀, (ρ n).exp_val (1 - (T n)) ≤ ε3 := fun n hn ↦ by -- Eq (S23)
      unfold MState.exp_val T
      rw [inner_sub_right, HermitianMat.inner_one, MState.tr,
        HermitianMat.inner_comm, tsub_le_iff_right, add_comm, ← tsub_le_iff_right]
      apply le_of_lt
      exact h n hn
    have hβ : ∀ n ≥ n₀, β_ ε3(ρ n‖{σ n}) ≤ Real.exp (-n * (Rinf + ε4)) := fun n hn ↦ by -- Eq (S25)
      open HermitianMat in
      calc
        β_ ε3(ρ n‖{σ n}) ≤ (σ n).exp_val (T n) := by
          have hβ' := OptimalHypothesisRate.singleton_le_exp_val (σ := σ n) (T n) (hT n hn) ⟨proj_le_nonneg _ _, proj_le_le_one _ _⟩
          simp only [Subtype.coe_le_coe.mpr hβ']
        _ <= ⟪T n, Real.exp (-n * (Rinf + ε4)) • (ρ n).M⟫ := by
          rw [← mul_le_mul_iff_right₀ (Real.exp_pos ((n * (Rinf + ε4)))), HermitianMat.inner_smul_right, neg_mul, Real.exp_neg]
          simp only [isUnit_iff_ne_zero, ne_eq, Real.exp_ne_zero, not_false_eq_true,
            IsUnit.mul_inv_cancel_left]
          rw [MState.exp_val, HermitianMat.inner_comm, ← HermitianMat.inner_smul_right]
          unfold T
          exact proj_le_inner_le (Real.exp (n * (Rinf + ε4)) • (σ n).M) (ρ n).M
        _ <= Real.exp (-n * (Rinf + ε4)) := by
          simp [HermitianMat.inner_smul_right]
          rw [mul_comm]
          apply (mul_le_iff_le_one_left (Real.exp_pos (-(n * (Rinf + ε4))))).mpr
          rw [HermitianMat.inner_comm, ← MState.exp_val]
          exact (ρ n).exp_val_le_one (proj_le_le_one _ _)
    have h' : ∀ n ≥ n₀, Rinf + ε4 ≤ —log β_ ε3(ρ n‖{σ n}) / n:= fun n hn ↦ by -- Eq (S26)
      have : 0 < n := by order
      have hn1 : (n : ℝ≥0∞) ≠ 0 := by positivity
      have hn2 : (n : ℝ≥0∞) ≠ ⊤ := by finiteness
      have hh : n * (Rinf + ε4) = ENNReal.ofReal (n * (Rinf + ε4)) := by
        simp only [Nat.cast_nonneg, ENNReal.ofReal_mul, ENNReal.ofReal_natCast, zero_le_coe,
          ENNReal.ofReal_add, ENNReal.ofReal_coe_nnreal]
      apply (ENNReal.mul_le_mul_left (a := n) (b := Rinf + ε4) (c := —log β_ ε3(ρ n‖{σ n}) / n) hn1 hn2).mp
      rw [ENNReal.mul_div_cancel hn1 hn2, hh]
      apply Prob.le_negLog_of_le_exp
      rw [← neg_mul]
      exact hβ n hn
    have hf : ∀ᶠ (n : ℕ) in Filter.atTop, Rinf + ε4 ≤ —log β_ ε3(ρ n‖{σ n}) / n := by
      rw [Filter.eventually_atTop]
      use n₀
    replace hf := Filter.le_liminf_of_le ?_ hf
    · replace hf := le_trans hf hRinf
      replace hf := tsub_eq_zero_iff_le.mpr hf
      simp_all
    apply Filter.IsCobounded.of_frequently_le (u := ⊤)
    simp [Filter.frequently_atTop]
    intro n; use n
  apply Filter.isBoundedUnder_of
  use 0; intro n
  rw [HermitianMat.inner_comm, ← MState.exp_val]
  exact (ρ n).exp_val_nonneg ((Real.exp (n * (Rinf + ε4)) • (σ n).M).proj_le_nonneg (ρ n).M)

open scoped HermitianMat in
theorem LemmaS2limsup {ε3 : Prob} {ε4 : ℝ≥0} (hε4 : 0 < ε4)
  {d : ℕ → Type*} [∀ n, Fintype (d n)] [∀ n, DecidableEq (d n)] (ρ : (n : ℕ) → MState (d n)) (σ : (n : ℕ) → MState (d n))
  {Rsup : ℝ≥0} (hRsup : Rsup ≥ Filter.atTop.limsup (fun (n : ℕ) ↦ —log β_ ε3(ρ n‖{σ n}) / n))
  :
  (Filter.atTop.limsup (fun (n : ℕ) ↦ ⟪{ρ n ≥ₚ (Real.exp (n * (Rsup + ε4))) • (σ n).M}, ρ n⟫) ≤ 1 - ε3)
  := by
  by_contra h
  push_neg at h
  replace h := Filter.frequently_lt_of_lt_limsup ?_ h
  · replace h := Filter.frequently_atTop.mp h
    let T (n : ℕ) := {(ρ n).M ≥ₚ (Real.exp (n * (Rsup + ε4))) • (σ n).M}
    have hT (n₀) : ∃ n ≥ n₀, (ρ n).exp_val (1 - (T n)) ≤ ε3 := by -- Eq (S30)
      obtain ⟨n, hn, h⟩ := h n₀
      use n, hn
      unfold MState.exp_val T
      rw [inner_sub_right, HermitianMat.inner_one, MState.tr,
        HermitianMat.inner_comm, tsub_le_iff_right, add_comm, ← tsub_le_iff_right]
      apply le_of_lt
      exact h
    have hβ (n₀) : ∃ n ≥ n₀, β_ ε3(ρ n‖{σ n}) ≤ Real.exp (-n * (Rsup + ε4)) := by -- Eq (S32)
      obtain ⟨n, hn, hT⟩ := hT n₀
      use n, hn
      open HermitianMat in
      calc
        β_ ε3(ρ n‖{σ n}) ≤ (σ n).exp_val (T n) := by
          have hβ' := OptimalHypothesisRate.singleton_le_exp_val (σ := σ n) (T n) hT ⟨proj_le_nonneg _ _, proj_le_le_one _ _⟩
          simp only [Subtype.coe_le_coe.mpr hβ']
        _ <= ⟪T n, Real.exp (-n * (Rsup + ε4)) • ρ n⟫ := by
          rw [← mul_le_mul_iff_right₀ (Real.exp_pos ((n * (Rsup + ε4)))), HermitianMat.inner_smul_right, neg_mul, Real.exp_neg]
          simp only [isUnit_iff_ne_zero, ne_eq, Real.exp_ne_zero, not_false_eq_true,
            IsUnit.mul_inv_cancel_left]
          rw [MState.exp_val, HermitianMat.inner_comm, ← HermitianMat.inner_smul_right]
          unfold T
          exact proj_le_inner_le (Real.exp (n * (Rsup + ε4)) • (σ n).M) (ρ n).M
        _ <= Real.exp (-n * (Rsup + ε4)) := by
          simp [HermitianMat.inner_smul_right]
          rw [mul_comm]
          apply (mul_le_iff_le_one_left (Real.exp_pos (-(n * (Rsup + ε4))))).mpr
          rw [HermitianMat.inner_comm, ← MState.exp_val]
          exact (ρ n).exp_val_le_one (proj_le_le_one _ _)
    have h' (n₀) : ∃ n ≥ n₀, Rsup + ε4 ≤ —log β_ ε3(ρ n‖{σ n}) / n := by -- Eq (S33)
      obtain ⟨n, hn, hβ⟩ := hβ (n₀ + 1)
      use n, by linarith
      have hn0 : 0 < n := by omega
      have hn1 : (n : ℝ≥0∞) ≠ 0 := by positivity
      have hn2 : (n : ℝ≥0∞) ≠ ⊤ := by finiteness
      have hh : n * (Rsup + ε4) = ENNReal.ofReal (n * (Rsup + ε4)) := by
        simp [ENNReal.ofReal_add]
      apply (ENNReal.mul_le_mul_left (a := n) (b := Rsup + ε4) (c := —log β_ ε3(ρ n‖{σ n}) / n) hn1 hn2).mp
      rw [ENNReal.mul_div_cancel hn1 hn2, hh]
      apply Prob.le_negLog_of_le_exp
      rwa [← neg_mul]
    have hf : ∃ᶠ (n : ℕ) in Filter.atTop, Rsup + ε4 ≤ —log β_ ε3(ρ n‖{σ n}) / n := by
      rwa [Filter.frequently_atTop]
    replace hf := Filter.le_limsup_of_frequently_le hf (by isBoundedDefault)
    · replace hf := le_trans hf hRsup
      replace hf := tsub_eq_zero_iff_le.mpr hf
      simp_all
  apply Filter.atTop.isCoboundedUnder_le_of_le (x := 0)
  intro n
  rw [HermitianMat.inner_comm, ← MState.exp_val]
  exact (ρ n).exp_val_nonneg ((Real.exp (n * (Rsup + ε4)) • (σ n).M).proj_le_nonneg (ρ n))

private theorem LemmaS3_helper {ε : Prob} {d : ℕ → Type*} [∀ n, Fintype (d n)] [∀ n, DecidableEq (d n)]
  (ρ σ₁ σ₂ : (n : ℕ) → MState (d n))
  (f : ℕ → ℝ≥0) (hσ : ∀ (i : ℕ), Real.exp (-f i) • (σ₂ i).M ≤ (σ₁ i)) (n : ℕ) :
    —log β_ ε(ρ n‖{σ₁ n}) ≤ —log β_ ε(ρ n‖{σ₂ n}) + f n := by
  have h₁ (T : HermitianMat (d n) ℂ) (hT : 0 ≤ T) :
          Real.exp (-f n) * ⟪T, σ₂ n⟫ ≤ ⟪T, σ₁ n⟫ := by
    simpa using HermitianMat.inner_mono hT (hσ n)
  by_cases hσ₂ : β_ ε(ρ n‖{σ₂ n}) = 0
  · simp [hσ₂]
  replace hσ₂ := Prob.zero_lt_coe hσ₂
  have hσ₁ : (0 : ℝ) < β_ ε(ρ n‖{σ₁ n}) := by
    refine OptimalHypothesisRate.rate_pos_of_smul_pos hσ₂ (Real.exp_pos (-f n)) ?_
    exact hσ n --For some reason turning these two lines into one `exact` causes timeouts
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [Prob.negLog_pos_Real, ENNReal.coe_toReal, OptimalHypothesisRate,
    Set.mem_singleton_iff, iSup_iSup_eq_left] at hσ₁ hσ₂ ⊢
  rw [← neg_le_neg_iff]
  simp only [neg_add_rev, neg_neg]
  rw [← Real.log_exp (-f n), ← Real.log_mul (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  simp only [Prob.coe_iInf]
  rw [Real.mul_iInf_of_nonneg (by positivity)]
  apply ciInf_mono
  · use 0
    rintro a ⟨y, rfl⟩
    have := (σ₂ n).exp_val_nonneg y.2.2.1
    positivity
  intro ⟨x, hx₁, hx₂, hx₃⟩
  simp only [MState.exp_val, ← HermitianMat.inner_smul_left]
  exact HermitianMat.inner_mono' hx₂ (hσ n)

/-- Lemma S3 from the paper. What they denote as σₙ and σₙ', we denote as σ₁ and σ₂. The `exp(-o(n))`
we express as a function `f : ℕ → ℝ`, together with the fact that `f` is little-o of `n` (i.e. that
`f =o[.atTop] id`), and then writing `exp(-f)`. We also split LemmaS3 into two parts, the `lim inf` part
and the `lim sup` part. The theorem as written is true for any `f`, but we can restrict to nonnegative
`f` (so, `ℕ → ℝ≥0`) which is easier to work with and more natural in the subsequent proofs. -/
private theorem LemmaS3_inf {ε : Prob}
    {d : ℕ → Type*} [∀ n, Fintype (d n)] [∀ n, DecidableEq (d n)]
    (ρ σ₁ σ₂ : (n : ℕ) → MState (d n))
    (f : ℕ → ℝ≥0) (hf : (f · : ℕ → ℝ) =o[.atTop] (· : ℕ → ℝ))
    (hσ : ∀ i, Real.exp (-f i) • (σ₂ i).M ≤ σ₁ i)
    :
    Filter.atTop.liminf (fun (n : ℕ) ↦ —log β_ ε(ρ n‖{σ₁ n}) / n) ≤
      Filter.atTop.liminf (fun (n : ℕ) ↦ —log β_ ε(ρ n‖{σ₂ n}) / n)
    := by
  --Starting with `helper`, divide by n and take the limits. Since f is o(n),
  --the (f n) / n term will go to zero.
  trans Filter.atTop.liminf fun n ↦ (—log β_ ε(ρ n‖{σ₂ n}) + f n) / n
  · refine Filter.liminf_le_liminf (.of_forall ?_)
    intro
    grw [LemmaS3_helper _ _ _ _ hσ]
  · apply le_of_eq
    simp_rw [ENNReal.add_div]
    apply ENNReal.liminf_add_of_right_tendsto_zero
    convert Asymptotics.IsLittleO.tendsto_div_nhds_zero hf
    rw [← ENNReal.tendsto_toReal_iff_of_eventually_ne_top ?_ ENNReal.zero_ne_top]
    · simp
    · rw [Filter.eventually_atTop]
      use 1
      finiteness

private theorem LemmaS3_sup {ε : Prob}
    {d : ℕ → Type*} [∀ n, Fintype (d n)] [∀ n, DecidableEq (d n)]
    (ρ σ₁ σ₂ : (n : ℕ) → MState (d n))
    (f : ℕ → ℝ≥0) (hf : (f · : ℕ → ℝ) =o[.atTop] (· : ℕ → ℝ))
    (hσ : ∀ i, Real.exp (-f i) • (σ₂ i).M ≤ σ₁ i)
    :
    Filter.atTop.limsup (fun (n : ℕ) ↦ —log β_ ε(ρ n‖{σ₁ n}) / n) ≤
      Filter.atTop.limsup (fun (n : ℕ) ↦ —log β_ ε(ρ n‖{σ₂ n}) / n)
    := by
  --Starting with `helper`, divide by n and take the limits. Since f is o(n),
  --the (f n) / n term will go to zero.
  trans Filter.atTop.limsup fun n ↦ (—log β_ ε(ρ n‖{σ₂ n}) + f n) / n
  · refine Filter.limsup_le_limsup (.of_forall ?_)
    dsimp
    intro x
    grw [LemmaS3_helper _ _ _ _ hσ]
  · apply le_of_eq
    simp_rw [ENNReal.add_div]
    apply ENNReal.limsup_add_of_right_tendsto_zero
    convert Asymptotics.IsLittleO.tendsto_div_nhds_zero hf
    rw [← ENNReal.tendsto_toReal_iff_of_eventually_ne_top ?_ ENNReal.zero_ne_top]
    · simp
    · rw [Filter.eventually_atTop]
      use 1
      finiteness

-- This is not exactly how R_{1, ε} is defined in Eq. (17), but it should be equal due to
-- the monotonicity of log and Lemma 3.
private noncomputable def R1 (ρ : MState (H i)) (ε : Prob) : ℝ≥0∞ :=
  Filter.atTop.liminf fun n ↦ —log β_ ε(ρ ⊗ᵣ^[n]‖IsFree) / n

private noncomputable def R2 (ρ : MState (H i)) : ((n : ℕ) → IsFree (i := i ^ n)) → ℝ≥0∞ :=
  fun σ ↦ Filter.atTop.liminf fun n ↦ 𝐃(ρ ⊗ᵣ^[n]‖σ n) / n

open MatrixOrder

open scoped HermitianMat

section proj_le

variable {d : Type*} [Fintype d] [DecidableEq d] (A B : HermitianMat d ℂ)

private lemma commute_aux (n : ℕ) {x : ℝ}
  {E ℰ σ : HermitianMat d ℂ} (hℰσ : Commute ℰ.mat σ.mat)
  (hE : E = 1 - {Real.exp (n * x) • σ ≤ₚ ℰ})
    : Commute ((1 / n : ℝ) • E).mat (ℰ.log - σ.log).mat := by
  rw [HermitianMat.one_sub_proj_le] at hE
  obtain ⟨C, ⟨f, rfl⟩, ⟨g, rfl⟩⟩ := hℰσ.exists_HermitianMat_cfc
  rw [HermitianMat.log, HermitianMat.log]
  rw [← HermitianMat.cfc_comp, ← HermitianMat.cfc_comp, ← HermitianMat.cfc_sub]
  rw [HermitianMat.proj_lt_def, ← HermitianMat.cfc_const_mul] at hE
  rw [← HermitianMat.cfc_sub, ← HermitianMat.cfc_comp] at hE
  subst E
  rw [← HermitianMat.cfc_const_mul]
  apply HermitianMat.cfc_self_commute

open HermMul in
private lemma rexp_mul_smul_proj_lt_mul_sub_le_mul_sub {n : ℕ} {x : ℝ}
  {E ℰ σ : HermitianMat d ℂ} (hℰσ : Commute ℰ.mat σ.mat) (hx : 0 < x)
  (hℰ : ℰ.mat.PosSemidef) (hσ : σ.mat.PosDef)
  (hE : E = 1 - {Real.exp (n * x) • σ ≤ₚ ℰ})
    : ⟪ℰ, ((1 / n : ℝ) • E) * (ℰ.log - σ.log)⟫ ≤ ⟪ℰ, x • E⟫ := by
  rw [HermitianMat.inner_eq_re_trace, HermitianMat.inner_eq_re_trace]
  rcases n.eq_zero_or_pos with rfl | hn
  · have hE' : 0 ≤ E.mat := by
      rw [hE, HermitianMat.one_sub_proj_le]
      apply HermitianMat.proj_lt_nonneg
    have hℰ : 0 ≤ ℰ := by rwa [HermitianMat.zero_le_iff]
    replace hℰ : 0 ≤ ⟪ℰ, E⟫ := HermitianMat.inner_ge_zero hℰ hE'
    rw [HermMul.mul_eq_symmMul, HermitianMat.symmMul_of_commute]
    · simp only [CharP.cast_eq_zero, div_zero, zero_smul, HermitianMat.mat_zero,
        HermitianMat.mat_sub, zero_mul, mul_zero, Matrix.trace_zero, RCLike.re_to_complex,
        Complex.zero_re, HermitianMat.mat_smul, Algebra.mul_smul_comm, trace_smul, Complex.real_smul,
        RCLike.mul_re, Complex.ofReal_re, RCLike.im_to_complex, Complex.ofReal_im, sub_zero]
      positivity
    · simp
  rw [HermMul.mul_eq_symmMul, HermitianMat.symmMul_of_commute (commute_aux n hℰσ hE)]
  dsimp
  gcongr
  apply Matrix.PosSemidef.trace_mono
  rw [one_div, HermitianMat.mat_smul, smul_mul_assoc, mul_smul_comm]
  rw [inv_smul_le_iff_of_pos (mod_cast hn), HermitianMat.mat_smul]
  rw [mul_smul_comm]
  obtain ⟨C, ⟨f, hf⟩, ⟨g, hg⟩⟩ := hℰσ.exists_HermitianMat_cfc
  rw [hf, hg] at hE ⊢
  rw [HermitianMat.one_sub_proj_le, HermitianMat.proj_lt_def] at hE
  rw [← HermitianMat.cfc_const_mul, ← HermitianMat.cfc_sub] at hE
  rw [← HermitianMat.cfc_comp] at hE
  unfold Function.comp at hE
  dsimp at hE
  rw [HermitianMat.log, HermitianMat.log]
  rw [← HermitianMat.cfc_comp, ← HermitianMat.cfc_comp, smul_smul]
  change _ * (E.mat * HermitianMat.mat (_ - _)) ≤ _
  rw [← HermitianMat.cfc_sub]
  subst E
  rw [← HermitianMat.mat_cfc_mul, ← HermitianMat.mat_cfc_mul]
  rw [← HermitianMat.mat_cfc_mul]
  change _ ≤ HermitianMat.mat ((n * x) • C.cfc _)
  rw [← HermitianMat.cfc_const_mul]
  change (C.cfc _ : HermitianMat _ _) ≤ C.cfc _
  rw [← sub_nonneg, ← HermitianMat.cfc_sub, HermitianMat.zero_le_cfc]
  intro i
  simp only [mul_ite, Pi.sub_apply, Pi.mul_apply, ite_mul]
  rw [ite_sub_ite]
  simp only [sub_pos, mul_one, Function.comp_apply, one_mul, mul_zero, zero_mul, sub_self]
  split_ifs with h; swap
  · rfl
  set fi := f (C.H.eigenvalues i) with hfi
  set gi := g (C.H.eigenvalues i) with hgi
  have hfi₀ : 0 ≤ fi := by
    rw [hf, ← HermitianMat.zero_le_iff, HermitianMat.zero_le_cfc] at hℰ
    exact hℰ i
  have hgi₀ : 0 < gi := by
    rw [hg, HermitianMat.cfc_PosDef] at hσ
    exact hσ i
  rcases hfi₀.eq_or_lt with hfi₂ | hfi₂
  · simp [← hfi₂]
  · simp [mul_comm fi]
    suffices Real.log fi < n * x + Real.log gi by
      grw [this]
      simp only [add_sub_cancel_right, le_refl]
    rw [← Real.log_exp (n * x), ← Real.log_mul (by positivity) (by positivity)]
    apply Real.strictMonoOn_log hfi₂ ?_ h
    change 0 < Real.exp (n * x) * gi
    positivity

private lemma rexp_mul_smul_proj_lt_mul_sub_le_mul_sub' {n : ℕ} {x : ℝ} {y : ℝ}
  {E ℰ σ : HermitianMat d ℂ} (hℰσ : Commute ℰ.mat σ.mat)
  (hℰ : ℰ.mat.PosSemidef) (hσ : σ.mat.PosDef)
  (hE : E = {Real.exp (n * y) • σ ≤ₚ ℰ} - {Real.exp (n * x) • σ ≤ₚ ℰ})
    : (1 / n : ℝ) • E.mat * (ℰ.log.mat - σ.log.mat) ≤ x • E := by
  --Another version of the above. Once we've proved one it's probably very easy to adapt the
  --code for the other. This doesn't suffer from the zero eigenvalue issue as much.
  rcases n.eq_zero_or_pos with rfl | hn
  · simp_all
  obtain ⟨C, ⟨f, hf⟩, ⟨g, hg⟩⟩ := hℰσ.exists_HermitianMat_cfc
  rw [hf, hg] at hE ⊢
  rw [HermitianMat.proj_le_def, HermitianMat.proj_le_def] at hE
  rw [← HermitianMat.cfc_const_mul, ← HermitianMat.cfc_sub] at hE
  rw [← HermitianMat.cfc_comp, ← HermitianMat.cfc_const_mul] at hE
  rw [← HermitianMat.cfc_sub, ← HermitianMat.cfc_comp, ← HermitianMat.cfc_sub] at hE
  subst E
  rw [HermitianMat.log, HermitianMat.log]
  rw [← HermitianMat.cfc_comp, ← HermitianMat.cfc_comp]
  conv =>
    enter [1]
    congr
    · change HermitianMat.mat ((1 / (n : ℝ)) • _)
    · change HermitianMat.mat (_ - _)
  change _ ≤ HermitianMat.mat (x • C.cfc _)
  rw [← HermitianMat.cfc_sub, ← HermitianMat.cfc_const_mul, ← HermitianMat.mat_cfc_mul]
  rw [← HermitianMat.cfc_const_mul, ← sub_nonneg]
  change 0 ≤ HermitianMat.mat (_ - _)
  rw [← HermitianMat.cfc_sub]
  change (0 : HermitianMat d ℂ) ≤ _
  rw [HermitianMat.zero_le_cfc]
  intro i
  simp only [Pi.sub_apply, Function.comp_apply, one_div, Pi.mul_apply]
  set fi := f (C.H.eigenvalues i) with hfi
  set gi := g (C.H.eigenvalues i) with hgi
  have hfi₀ : 0 ≤ fi := by
    rw [hf, ← HermitianMat.zero_le_iff, HermitianMat.zero_le_cfc] at hℰ
    exact hℰ i
  have hgi₀ : 0 < gi := by
    rw [hg, HermitianMat.cfc_PosDef] at hσ
    exact hσ i
  split_ifs with ha hb hb <;> simp only [← hfi, ← hgi] at ha hb ⊢
  · simp
  · simp only [sub_nonneg, not_le, sub_zero, mul_one] at ha hb ⊢
    rw [inv_mul_le_iff₀ (by positivity)]
    rw [← Real.exp_le_exp, Real.exp_sub]
    rw [Real.exp_log (lt_of_lt_of_le (by positivity) ha), Real.exp_log hgi₀]
    rw [div_le_iff₀ hgi₀]
    exact hb.le
  · simp only [sub_nonneg, not_le, zero_sub, mul_neg, mul_one, neg_mul, sub_neg_eq_add,
      le_neg_add_iff_add_le, add_zero] at ha hb ⊢
    rw [le_inv_mul_iff₀ (by positivity)]
    rw [← Real.exp_le_exp, Real.exp_sub]
    rw [Real.exp_log (lt_of_lt_of_le (by positivity) hb), Real.exp_log hgi₀]
    rw [le_div_iff₀ hgi₀]
    exact hb
  · simp

end proj_le

private lemma f_image_bound (mineig : ℝ) (n : ℕ) (h : 0 < mineig) (hn : 0 < n) :
  let c : ℕ → ℝ := fun n ↦ Real.log (1 / mineig) + Real.log 3 / (max n 1);
  let f : ℕ → ℝ → ℝ := fun n lam => ↑⌈Real.log lam / c n⌉ * c n;
  let S : Set ℝ := (fun x => Real.exp (f n x)) '' Set.Icc ((mineig ^ n) / 3) 1;
  (h_le_f : ∀ (n : ℕ) (lam : ℝ), Real.log lam ≤ f n lam) →
  (h_f_le : ∀ (n : ℕ) (lam : ℝ), f n lam < Real.log lam + c n) →
    S.ncard ≤ n + 1 ∧ S.Finite := by
  --Thanks Aristotle. TODO Cleanup
  -- To show that $S$ is finite, we need to show that the function $f$ maps the interval into a finite set.
  have h_finite : Set.Finite (Set.image (fun x => Real.exp (⌈Real.log x / (Real.log (1 / mineig) + Real.log 3 / (max n 1))⌉ * (Real.log (1 / mineig) + Real.log 3 / (max n 1)))) (Set.Icc (mineig^n / 3) 1)) := by
    -- Since the interval [mineig^n / 3, 1] is bounded and the function Real.log is continuous, the values of Real.log x / (Real.log (1 / mineig) + Real.log 3 / (max n 1)) will also be bounded. The ceiling function will then map these values to a finite set of integers.
    have h_bounded : ∃ m M : ℤ, ∀ x ∈ Set.Icc (mineig^n / 3) 1, m ≤ ⌈Real.log x / (Real.log (1 / mineig) + Real.log 3 / (max n 1))⌉ ∧ ⌈Real.log x / (Real.log (1 / mineig) + Real.log 3 / (max n 1))⌉ ≤ M := by
      have h_bounded : ∃ m M : ℝ, ∀ x ∈ Set.Icc (mineig^n / 3) 1, m ≤ Real.log x / (Real.log (1 / mineig) + Real.log 3 / (max n 1)) ∧ Real.log x / (Real.log (1 / mineig) + Real.log 3 / (max n 1)) ≤ M := by
        -- Since the interval [mineig^n / 3, 1] is closed and bounded, and the function Real.log x / (Real.log (1 / mineig) + Real.log 3 / (max n 1)) is continuous on this interval, it must attain a maximum and minimum value on this interval.
        have h_cont : ContinuousOn (fun x => Real.log x / (Real.log (1 / mineig) + Real.log 3 / (max n 1))) (Set.Icc (mineig^n / 3) 1) := by
          -- Since Real.log x is continuous on the interval (0, ∞) and the denominator is a non-zero constant, the function Real.log x / (Real.log (1 / mineig) + Real.log 3 / (max n 1)) is continuous on the interval [mineig^n / 3, 1].
          have h_cont : ContinuousOn Real.log (Set.Icc (mineig^n / 3) 1) := by
            exact continuousOn_of_forall_continuousAt fun x hx => Real.continuousAt_log ( by linarith [ hx.1, pow_pos h n ] );
          exact h_cont.div_const _;
        exact ⟨ ( InfSet.sInf <| ( fun x => Real.log x / ( Real.log ( 1 / mineig ) + Real.log 3 / ( max n 1 ) ) ) '' Set.Icc ( mineig ^ n / 3 ) 1 ), ( SupSet.sSup <| ( fun x => Real.log x / ( Real.log ( 1 / mineig ) + Real.log 3 / ( max n 1 ) ) ) '' Set.Icc ( mineig ^ n / 3 ) 1 ), fun x hx => ⟨ ( csInf_le <| IsCompact.bddBelow <| isCompact_Icc.image_of_continuousOn h_cont ) <| Set.mem_image_of_mem _ hx, ( le_csSup <| IsCompact.bddAbove <| isCompact_Icc.image_of_continuousOn h_cont ) <| Set.mem_image_of_mem _ hx ⟩ ⟩;
      obtain ⟨ m, M, hM ⟩ := h_bounded
      exact ⟨ ⌈m⌉, ⌈M⌉, fun x hx => ⟨ Int.ceil_mono <| hM x hx |>.1, Int.ceil_mono <| hM x hx |>.2 ⟩ ⟩ ;
    cases' h_bounded with m h_bounded
    cases' h_bounded with M h_bounded
    refine Set.Finite.subset ( Set.toFinite ( Finset.image ( fun i : ℤ => Real.exp ( ( i : ℝ ) * ( Real.log ( 1 / mineig ) + Real.log 3 / ( max n 1 : ℝ ) ) ) ) ( Finset.Icc m M ) ) ) ?_
    intro
    intro a_1
    simp_all only [Set.mem_Icc, one_div, Real.log_inv, Nat.cast_max, Nat.cast_one, and_imp, Set.mem_image,
      Finset.coe_image, Finset.coe_Icc]
    obtain ⟨w, ⟨left, rfl⟩⟩ := a_1
    simp_all only [Real.exp_eq_exp, mul_eq_mul_right_iff, Int.cast_inj]
    apply Exists.intro
    · apply And.intro
      on_goal 2 => {
        apply Or.inl
        rfl
      }
      · simp_all only [and_self]
  intro c f S h_le_f h_f_le
  simp_all only [one_div, Real.log_inv, Nat.cast_max, Nat.cast_one, and_true, f, c, S]
  -- Since the interval [(n * log(mineig) - log(3)) / c(n), 0 / c(n)] has length (log(3) - n * log(mineig)) / c(n), and c(n) is positive, the number of distinct integer values that ⌈(log lam) / c(n)⌉ can take is at most n + 1.
  have h_card : Set.ncard (Set.image (fun x => Real.exp (⌈Real.log x / (Real.log (1 / mineig) + Real.log 3 / (max n 1))⌉ * (Real.log (1 / mineig) + Real.log 3 / (max n 1)))) (Set.Icc (mineig^n / 3) 1)) ≤ Set.ncard (Set.image (fun k : ℤ => Real.exp (k * (Real.log (1 / mineig) + Real.log 3 / (max n 1)))) (Set.Icc (⌈(n * Real.log mineig - Real.log 3) / (Real.log (1 / mineig) + Real.log 3 / (max n 1))⌉) 0)) := by
    refine Set.ncard_le_ncard ?_;
    intro
    intro a_1
    simp_all only [one_div, Real.log_inv, Nat.cast_max, Nat.cast_one, Set.mem_image, Set.mem_Icc]
    obtain ⟨w, ⟨⟨left, right_1⟩, rfl⟩⟩ := a_1
    simp_all only [Real.exp_eq_exp, mul_eq_mul_right_iff, Int.cast_inj]
    refine' ⟨_, ⟨_, _ ⟩, Or.inl rfl⟩;
    · gcongr;
      · have := h_f_le n 1 ; norm_num at this ; linarith [ Real.log_le_sub_one_of_pos h ];
      · -- Taking the logarithm of both sides of the inequality $mineig^n / 3 \leq w$, we get $n \log(mineig) - \log(3) \leq \log(w)$.
        have h_log : Real.log (mineig^n / 3) ≤ Real.log w := by
          exact Real.log_le_log ( by positivity ) left;
        rwa [ Real.log_div ( by positivity ) ( by positivity ), Real.log_pow ] at h_log;
    · refine' Int.ceil_le.mpr _;
      rw [ div_le_iff₀ ]
      · simp_all only [Int.cast_zero, zero_mul]
        exact Real.log_nonpos ( by linarith [ pow_pos h n ] ) right_1;
      · have := h_f_le n 1
        simp_all only [Real.log_one, zero_div, Int.ceil_zero, Int.cast_zero, zero_mul, zero_add, lt_neg_add_iff_add_lt, add_zero]
  have h_card_image : Set.ncard (Set.image (fun k : ℤ => Real.exp (k * (Real.log (1 / mineig) + Real.log 3 / (max n 1)))) (Set.Icc (⌈(n * Real.log mineig - Real.log 3) / (Real.log (1 / mineig) + Real.log 3 / (max n 1))⌉) 0)) ≤ Set.ncard (Set.Icc (⌈(n * Real.log mineig - Real.log 3) / (Real.log (1 / mineig) + Real.log 3 / (max n 1))⌉) 0) := by
    apply Set.ncard_image_le;
    exact Set.finite_Icc _ _;
  simp_all +decide [ Set.ncard_eq_toFinset_card' ];
  refine le_trans h_card <| le_trans h_card_image ?_;
  rcases n with _ | n
  · simp at hn
  simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, Nat.cast_add, Nat.cast_one,
    le_add_iff_nonneg_left, Nat.cast_nonneg, sup_of_le_left, Int.toNat_le, tsub_le_iff_right]
  specialize h_f_le ( n + 1 ) 1;
  simp_all only [Real.log_one, Nat.cast_add, Nat.cast_one, le_add_iff_nonneg_left, Nat.cast_nonneg, sup_of_le_left,
    zero_div, Int.ceil_zero, Int.cast_zero, zero_mul, zero_add, lt_neg_add_iff_add_lt, add_zero]
  apply Int.le_of_lt_add_one
  rw [ ← @Int.cast_lt ℝ ]
  push_cast
  nlinarith [ Int.le_ceil ( ( ( n + 1 ) * Real.log mineig - Real.log 3 ) / ( -Real.log mineig + Real.log 3 / ( n + 1 ) ) ),
    mul_div_cancel₀ ( ( n + 1 ) * Real.log mineig - Real.log 3 ) ( show ( -Real.log mineig + Real.log 3 / ( n + 1 ) ) ≠ 0 by
      nlinarith [ Real.log_pos ( show ( 3 : ℝ ) > 1 by norm_num ), mul_div_cancel₀ ( Real.log 3 ) ( show ( n + 1 : ℝ ) ≠ 0 by positivity ) ] ),
        Real.log_pos ( show ( 3 : ℝ ) > 1 by norm_num ), mul_div_cancel₀ ( Real.log 3 ) ( show ( n + 1 : ℝ ) ≠ 0 by positivity ) ]

private lemma c'_bounded {mineig : ℝ} {ε2 : ℕ → ℝ≥0}
    (hε2 : ∀ (n : ℕ), ε2 n < 1) (o : ℝ) :
  let c : ℕ → ℝ := fun n => Real.log (1 / mineig) + Real.log 3 / ↑(max n 1);
  let c' : ℝ → ℕ → ℝ := fun  ε2 n ↦ (c n + (c n) / n) ⊔ (o + ε2);
  (∀ (n : ℕ), 0 < c n) →
    ∃ (C : NNReal), ∀ᶠ (n : ℕ) in Filter.atTop, c' (↑(ε2 n)) n ≤ ↑C := by
  have h_bound : ∃ C : ℝ, ∀ᶠ n in Filter.atTop, Real.log (1 / mineig) + Real.log 3 / (Max.max n 1) + (Real.log (1 / mineig) + Real.log 3 / (Max.max n 1)) / n ≤ C := by
    have h_bound : Filter.Tendsto (fun n => Real.log (1 / mineig) + Real.log 3 / (Max.max n 1) + (Real.log (1 / mineig) + Real.log 3 / (Max.max n 1)) / n) Filter.atTop (nhds (Real.log (1 / mineig) + Real.log 3 / 0 + (Real.log (1 / mineig) + Real.log 3 / 0) / 0)) := by
      exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.add <| Filter.Tendsto.mul tendsto_const_nhds <| Filter.Tendsto.inv_tendsto_atTop <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x + 1, fun y hy => le_max_of_le_left <| by linarith ⟩ ) <| Filter.Tendsto.mul ( tendsto_const_nhds.add <| Filter.Tendsto.mul tendsto_const_nhds <| Filter.Tendsto.inv_tendsto_atTop <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ x + 1, fun y hy => le_max_of_le_left <| by linarith ⟩ ) <| tendsto_inv_atTop_zero ) <| by norm_num;
    exact ⟨ _, h_bound.eventually ( ge_mem_nhds <| lt_add_one _ ) ⟩;
  intro c c' a
  simp_all only [one_div, Real.log_inv, Filter.eventually_atTop, ge_iff_le, Nat.cast_max, Nat.cast_one,
    lt_neg_add_iff_add_lt, add_zero, sup_le_iff, c, c']
  obtain ⟨w, ⟨w_1, h⟩⟩ := h_bound
  use ⌈w⌉₊ + ⌈o⌉₊ + 1, ⌈w_1⌉₊
  intro n hn
  constructor
  · norm_num
    linarith [ Nat.le_ceil w, h n ( Nat.le_of_ceil_le hn ) ]
  · norm_num
    linarith [ Nat.le_ceil o, show ( ε2 n : ℝ ) ≤ 1 by exact_mod_cast le_of_lt ( hε2 n ) ]

noncomputable section sigmas

/- Define the different (sequences of) states needed in the construction and prove their basic
properties. -/

section defs
section σ₁_c_and_f --Stuff that has variable (i) explicit because it only depends on that

variable (i)

private def σ₁ : MState (H i) :=
  Classical.choose (FreeStateTheory.free_fullRank i)

private def σ₁_mineig := ⨅ k, (σ₁ i).M.H.eigenvalues k

/-- The sequence c_n given in (S44). In order to handle when c = 0, we've replaced the
 (Real.log 3) / n term with (Real.log 3) / (max n 1). -/
private def σ₁_c (n : ℕ) : ℝ :=
  Real.log (1 / σ₁_mineig i) + (Real.log 3) / (max n 1)

/-- The function f_n(λ) in (S45). -/
private def f_map (n : ℕ) (lam : ℝ) : ℝ :=
  ⌈Real.log lam / σ₁_c i n⌉ * σ₁_c i n

end σ₁_c_and_f
--From here on, sequences generally depend on other parameters + states.

variable (ρ : MState (H i)) (ε : Prob) (m : ℕ) (σ : (n : ℕ) → IsFree (i := i ^ n))

private def «σ̃» :
    (n : ℕ) → MState (H (i ^ n)) :=
  fun n ↦ Lemma6_σn m (σ₁ i) (σ m) n

private def «σ⋆» : (n : ℕ) → MState (H (i ^ n)) :=
  haveI σ_max_exists (n : ℕ) := IsCompact_IsFree.exists_isMaxOn Set.Nonempty.of_subtype
      (f := fun σ ↦ β_ ε(ρ ⊗ᵣ^[n]‖{σ})) (hf := Continuous.continuousOn (by fun_prop))
  fun n ↦ Classical.choose (σ_max_exists n)

--TODO: would be nice to write a `Mixable` thing for mixing `k` things according to a distribution,
-- in this case `Distribution.uniform (Fin 3)`.
private def σ' : (n : ℕ) → MState (H (i ^ n)) :=
  fun n ↦ ⟨2/3, by norm_num⟩ [⟨1/2, by norm_num⟩ [«σ̃» m σ n ↔ «σ⋆» ρ ε n] ↔ (σ₁ i) ⊗ᵣ^[n]]

private def σ''_unnormalized : (n : ℕ) → HermitianMat (H (i ^ n)) ℂ :=
  fun n ↦ (σ' ρ ε m σ n).M.cfc fun e ↦ Real.exp (f_map i n e)

end defs

section proofs
/- Prove relevant properties about their positivity, trace, etc. -/
section σ₁_c_and_f

variable (i)

private theorem σ₁_pos : (σ₁ i).m.PosDef :=
  (FreeStateTheory.free_fullRank i).choose_spec.left

private theorem σ₁_isFree : IsFree (σ₁ i) :=
  (FreeStateTheory.free_fullRank i).choose_spec.right

private theorem mineig_pos : 0 < σ₁_mineig i := by
  --because σ₁ is PosDef, all eigenvalues are positive, so their minimum is positive
  obtain ⟨i_min, hi_min⟩ := exists_eq_ciInf_of_finite (f := (HermitianMat.H (σ₁ i).M).eigenvalues)
  unfold σ₁_mineig
  rw [← hi_min]
  exact (σ₁_pos i).eigenvalues_pos i_min

private theorem mineig_le_one : σ₁_mineig i ≤ 1 := by
    --all eigenvalues of a state are at most 1. (We might not actually need this fact.)
    obtain ⟨i_min, hi_min⟩ := exists_eq_ciInf_of_finite (f := (HermitianMat.H (σ₁ i).M).eigenvalues)
    unfold σ₁_mineig
    rw [← hi_min]
    exact (σ₁ i).eigenvalue_le_one i_min

private theorem σ₁_c_pos (n) : 0 < σ₁_c i n := by
  rw [σ₁_c]
  have h_min_pos := mineig_pos i
  have h_min_le_one := mineig_le_one i
  have h₁ : 0 ≤ Real.log (1 / σ₁_mineig i) := by bound
  positivity

private theorem σ₁_c_div_lim : Filter.atTop.Tendsto (fun n ↦ (σ₁_c i n) / n) (𝓝 0) := by
  unfold σ₁_c
  have h_const : Filter.atTop.Tendsto (fun n : ℕ ↦ Real.log (1 / σ₁_mineig i) / n) (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop;
  -- We can split the limit into two parts: the constant term and the term involving log(3).
  have h_div : Filter.atTop.Tendsto (fun n : ℕ ↦ Real.log 3 / (max n 1 * n)) (𝓝 0) :=
    tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_mono (fun n ↦ by
      norm_cast; nlinarith [le_max_left n 1, le_max_right n 1]) tendsto_natCast_atTop_atTop
  convert h_const.add h_div using 2 <;> ring

private lemma σ₁_c_identity {n : ℕ} (hn : 0 < n) :
    Real.exp (-σ₁_c i n) * (1 / 3) * σ₁_mineig i ^ n =
    Real.exp (-n * (σ₁_c i n + σ₁_c i n / n)) := by
  have h (x : ℝ) : n * (x / n) = x := by field_simp
  simp only [σ₁_c]
  simp only [neg_mul, show ((max n 1 : ℕ) : ℝ) = n from mod_cast (max_eq_left hn)]
  simp only [Real.exp_add, mul_add, neg_add_rev, mul_assoc, h]
  simp [Real.exp_neg, Real.exp_log, Real.exp_log (mineig_pos i), Real.exp_nat_mul]

theorem σ₁_c_littleO : (fun n : ℕ ↦ σ₁_c i n + Real.log 3) =o[Filter.atTop] (fun x ↦ (x : ℝ)) := by
  apply Asymptotics.IsLittleO.add
  · rw [Asymptotics.isLittleO_iff_tendsto']
    · exact σ₁_c_div_lim i
    simp only [Nat.cast_eq_zero, Filter.eventually_atTop]
    use 1
    grind
  · --This `(fun x => Real.log 3) =o[Filter.atTop] fun x => x` really should be its own fact, TODO
    refine Asymptotics.isLittleO_const_left.2 <| Or.inr ?_
    convert tendsto_natCast_atTop_atTop (R := ℝ)
    ext
    simp

/-- (S46), part 1 -/
private theorem log_le_f (n : ℕ) (lam : ℝ) : Real.log lam ≤ f_map i n lam :=
  calc
  _ ≤ (⌈Real.log lam / (σ₁_c i n)⌉) * σ₁_c i n := by
    rw [← mul_inv_le_iff₀ (σ₁_c_pos i n)]
    apply Int.le_ceil _
  _ = _ := by
    rfl

/-- (S46), part 2 -/
private theorem f_le_log (n : ℕ) (lam : ℝ) : f_map i n lam < Real.log lam + σ₁_c i n :=
  calc
  _ = ⌈Real.log lam / σ₁_c i n⌉ * σ₁_c i n := by
    rfl
  _ < (Real.log lam / σ₁_c i n + 1) * σ₁_c i n := by
    gcongr
    · exact σ₁_c_pos i n
    · exact Int.ceil_lt_add_one _
  _ ≤ _ := by
    have := σ₁_c_pos i n
    field_simp
    rfl

private theorem le_exp_f (n : ℕ) (x : ℝ) (hx : 0 < x) : x ≤ Real.exp (f_map i n x) := by
  convert Real.exp_monotone (log_le_f i n x)
  rw [Real.exp_log hx]

private theorem exp_f_le (n : ℕ) (x : ℝ) (hx : 0 < x) : Real.exp (f_map i n x) < Real.exp (σ₁_c i n) * x := by
  convert Real.exp_strictMono (f_le_log i n x) using 1
  rw [Real.exp_add (Real.log x), Real.exp_log hx, mul_comm]

end σ₁_c_and_f

variable (ρ : MState (H i)) (ε : Prob)
variable (m : ℕ) (σ : (n : ℕ) → IsFree (i := i ^ n)) (n : ℕ)

private theorem «σ̃_isFree» : IsFree («σ̃» m σ n) :=
  Lemma6_σn_IsFree (σ₁_isFree i) (fun n ↦ (σ n).2) m n

private theorem «σ⋆_free» : IsFree («σ⋆» ρ ε n) :=
  haveI σ_max_exists (n : ℕ) := IsCompact_IsFree.exists_isMaxOn Set.Nonempty.of_subtype
      (f := fun σ ↦ β_ ε(ρ ⊗ᵣ^[n]‖{σ})) (hf := Continuous.continuousOn (by fun_prop))
  (σ_max_exists n).choose_spec.left

private theorem «σ⋆_max» :
    IsMaxOn (fun σ ↦ β_ ε(ρ ⊗ᵣ^[n]‖{σ})) IsFree («σ⋆» ρ ε n) :=
  haveI σ_max_exists (n : ℕ) := IsCompact_IsFree.exists_isMaxOn Set.Nonempty.of_subtype
      (f := fun σ ↦ β_ ε(ρ ⊗ᵣ^[n]‖{σ})) (hf := Continuous.continuousOn (by fun_prop))
  (σ_max_exists n).choose_spec.right

private theorem σ'_free : IsFree (σ' ρ ε m σ n) := by
  -- by convexity of `IsFree` and that the three constituents are free
  unfold σ'
  apply IsFree.mix
  · exact («σ̃_isFree» m σ n).mix («σ⋆_free» ρ ε n) _
  · exact (σ₁_isFree i).npow n

private theorem σ'_posdef : (σ' ρ ε m σ n).m.PosDef := by
  --because σ₁ is PosDef, so is σ₁⊗^[n], and so is any convex mixture.
  unfold σ'
  apply MState.PosDef_mix_of_ne_one
  · apply UnitalPretheory.PosDef.npow (σ₁_pos i)
  · norm_num [← Prob.ne_iff]

private theorem hσ'n_eq_sum_third : (σ' ρ ε m σ n).M =
    (1 / 3 : ℝ) • («σ̃» m σ n) + (1 / 3 : ℝ) • («σ⋆» ρ ε n) + (1 / 3 : ℝ) • ((σ₁ i) ⊗ᵣ^[n]) := by
  unfold σ'
  change _ • _ + _ = _
  conv =>
    enter [1, 1, 2]
    change _ + _
  dsimp [Mixable.to_U]
  norm_num only [one_div, Prob.coe_one_minus, smul_add, smul_smul]

private theorem hσ₁_le_σ' : (1 / 3 : ℝ) • ((σ₁ i) ⊗ᵣ^[n]).M ≤ (σ' ρ ε m σ n).M := by
    rw [hσ'n_eq_sum_third]
    apply le_add_of_nonneg_left
    have := («σ⋆» ρ ε n).zero_le
    have := («σ̃» m σ n).zero_le
    positivity

private theorem σ''_unnormalized_PosDef : Matrix.PosDef (σ''_unnormalized ρ ε m σ n).mat := by
  dsimp [σ''_unnormalized]
  rw [HermitianMat.cfc_PosDef]
  intro
  positivity

private theorem σ''_tr_bounds : 1 ≤ (σ''_unnormalized ρ ε m σ n).trace ∧
    (σ''_unnormalized ρ ε m σ n).trace < Real.exp (σ₁_c i n) := by
  have hσ' := (σ' ρ ε m σ n).tr
  constructor
  · rw [← HermitianMat.sum_eigenvalues_eq_trace] at hσ' ⊢
    rw [← hσ']
    obtain ⟨e, he⟩ := (σ' ρ ε m σ n).M.cfc_eigenvalues fun e ↦ Real.exp (f_map i n e)
    rw [he]
    simp only [Function.comp_apply]
    rw [Equiv.sum_comp e (fun k ↦ Real.exp (f_map i n (Matrix.IsHermitian.eigenvalues _ k)))]
    gcongr
    apply le_exp_f i n _
    exact (σ'_posdef ρ ε m σ n).eigenvalues_pos _
  · rw [← HermitianMat.sum_eigenvalues_eq_trace] at hσ' ⊢
    rw [← mul_one (Real.exp (σ₁_c i n)), ← hσ', Finset.mul_sum]
    obtain ⟨e, he⟩ := (σ' ρ ε m σ n).M.cfc_eigenvalues fun e ↦ Real.exp (f_map i n e)
    rw [he]; clear he
    dsimp
    rw [Equiv.sum_comp e (fun k ↦ Real.exp (f_map i n (Matrix.IsHermitian.eigenvalues _ k)))]
    gcongr
    · exact Finset.univ_nonempty
    · apply exp_f_le i n _
      exact (σ'_posdef ρ ε m σ n).eigenvalues_pos _

end proofs

variable (ρ : MState (H i)) (ε : Prob)
variable (m : ℕ) (σ : (n : ℕ) → IsFree (i := i ^ n)) (n : ℕ)

--We're now finally ready to define the main sequence with the properties we want, σ''.
--This is the normalized version of σ''_unnormalized, which gives a state because that sequence is
-- already PosDef
private def σ'' : (n : ℕ) → MState (H (i ^ n)) := fun n ↦ {
  --TODO make this its own definition: Normalizing a matrix to give a tr-1 op.
  M := (σ''_unnormalized ρ ε m σ n).trace⁻¹ • (σ''_unnormalized ρ ε m σ n)
  zero_le := by
    have h1 : 0 < (σ''_unnormalized ρ ε m σ n).trace :=
      zero_lt_one.trans_le (σ''_tr_bounds ρ ε m σ n).left
    have h2 : 0 < σ''_unnormalized ρ ε m σ n :=
      (σ''_unnormalized_PosDef ρ ε m σ n).zero_lt
    positivity
  tr := by
    rw [HermitianMat.trace_smul]
    apply inv_mul_cancel₀
    exact (zero_lt_one.trans_le (σ''_tr_bounds ρ ε m σ n).left).ne'
}

private lemma σ''_posdef n : (σ'' ρ ε m σ n).M.mat.PosDef := by
  apply (σ''_unnormalized_PosDef ρ ε m σ n).smul
  have := (σ''_tr_bounds ρ ε m σ n).left
  positivity

private lemma σ'_le_σ'' (n) : Real.exp (-σ₁_c i n) • (σ' ρ ε m σ n).M ≤ σ'' ρ ε m σ n := by
  dsimp [σ'']
  set x := (σ''_unnormalized ρ ε m σ n).trace
  dsimp [σ''_unnormalized]
  rw [← HermitianMat.cfc_const_mul_id, ← HermitianMat.cfc_const_mul_id,
    ← HermitianMat.cfc_comp]
  rw [← sub_nonneg, ← HermitianMat.cfc_sub, HermitianMat.zero_le_cfc]
  intro k
  set y := (σ' ρ ε m σ n).M.H.eigenvalues k
  have hy : 0 < y := (σ'_posdef ρ ε m σ n).eigenvalues_pos k
  dsimp only [Pi.sub_apply, Function.comp_apply]
  have : 0 < x := zero_lt_one.trans_le (σ''_tr_bounds ρ ε m σ n).left
  grw [← le_exp_f i n y hy]
  rw [← sub_mul]
  suffices 0 ≤ x⁻¹ - Real.exp (-σ₁_c i n) by positivity
  rw [sub_nonneg, ← inv_le_inv₀]
  · simpa [← Real.exp_neg] using (σ''_tr_bounds ρ ε m σ n).right.le
  · positivity
  · positivity

private lemma σ''_le_σ' (n) : σ'' ρ ε m σ n ≤ Real.exp (σ₁_c i n) • (σ' ρ ε m σ n).M := by
    dsimp [σ'']
    set x := (σ''_unnormalized ρ ε m σ n).trace
    dsimp [σ''_unnormalized]
    rw [← HermitianMat.cfc_const_mul_id, ← HermitianMat.cfc_const_mul_id,
      ← HermitianMat.cfc_comp]
    rw [← sub_nonneg, ← HermitianMat.cfc_sub, HermitianMat.zero_le_cfc]
    intro k
    set y := (σ' ρ ε m σ n).M.H.eigenvalues k
    have hy : 0 < y := (σ'_posdef ρ ε m σ n).eigenvalues_pos k
    dsimp only [Pi.sub_apply, Function.comp_apply]
    grw [← exp_f_le i n y hy]
    rw [← one_sub_mul]
    suffices 0 ≤ 1 - x⁻¹ by positivity
    simpa using inv_le_one_of_one_le₀ (σ''_tr_bounds ρ ε m σ n).left

private theorem «σ''_ge_σ⋆» n : σ'' ρ ε m σ n ≥ (Real.exp (-σ₁_c i n) / 3) • («σ⋆» ρ ε n).M := by
    grw [ge_iff_le, ← σ'_le_σ'', div_eq_mul_inv, ← smul_smul, ← one_div]
    rw [smul_le_smul_iff_of_pos_left (by positivity), hσ'n_eq_sum_third]
    apply le_add_of_le_of_nonneg
    · apply le_add_of_nonneg_left
      have := («σ̃» m σ n).zero_le
      positivity
    · have := ((σ₁ i) ⊗ᵣ^[n]).zero_le
      positivity

private theorem «σ''_ge_σ̃» n : σ'' ρ ε m σ n ≥ (Real.exp (-σ₁_c i n) / 3) • («σ̃» m σ n).M := by
    grw [ge_iff_le, ← σ'_le_σ'', div_eq_mul_inv, ← smul_smul, ← one_div]
    rw [smul_le_smul_iff_of_pos_left (by positivity), hσ'n_eq_sum_third]
    apply le_add_of_le_of_nonneg
    · apply le_add_of_nonneg_right
      have := («σ⋆» ρ ε n).zero_le
      positivity
    · have := ((σ₁ i) ⊗ᵣ^[n]).zero_le
      positivity

private theorem σ''_ge_σ₁ n : σ'' ρ ε m σ n ≥ (Real.exp (-σ₁_c i n) / 3) • ((σ₁ i) ⊗ᵣ^[n]).M := by
    grw [ge_iff_le, ← σ'_le_σ'', div_eq_mul_inv, ← smul_smul, ← one_div]
    rw [smul_le_smul_iff_of_pos_left (by positivity)]
    exact hσ₁_le_σ' ρ ε m σ n

private abbrev ε₀_func (ε' : Prob) : ℝ := (R2 ρ σ - R1 ρ ε).toReal * (ε - ε') / (1 - ε)

end sigmas

private theorem EquationS88 (ρ : MState (H i)) (σ : (n : ℕ) → ↑IsFree) {ε ε' : Prob}
  (hR1R2 : R1 ρ ε < R2 ρ σ) (hR1 : R1 ρ ε ≠ ⊤) (hR2 : R2 ρ σ ≠ ⊤) (hε₀_1 : 0 < ε₀_func ρ ε σ ε') (m : ℕ)
  :
  let ℰ := fun n => pinching_map (σ'' ρ ε m σ n);
  let ε₀ := ε₀_func ρ ε σ ε';
    (0 < ε₀) →
    (R1 ρ ε).toReal ≤ (R2 ρ σ).toReal + ε₀ →
      let P1 := fun ε2 (n : ℕ) ↦ {Real.exp (↑n * ((R1 ρ ε).toReal + ε2)) • ↑(σ'' ρ ε m σ n) ≤ₚ ((ℰ n) (ρ ⊗ᵣ^[n]))};
      let P2 := fun ε2 (n : ℕ) ↦ {Real.exp (↑n * ((R2 ρ σ).toReal + ε₀ + ε2)) • ↑(σ'' ρ ε m σ n) ≤ₚ ((ℰ n) (ρ ⊗ᵣ^[n]))};
      let E1 := 1 - P1;
      let E2 := P1 - P2;
      let E3 := P2;
      E1 + E2 + E3 = 1 →
    (∀ (ε2 : ℝ) (n : ℕ), E1 ε2 n = {↑((ℰ n) (ρ ⊗ᵣ^[n])) <ₚ Real.exp (↑n * ((R1 ρ ε).toReal + ε2)) • ↑(σ'' ρ ε m σ n)}) →
    (∀ (ε2 : ℝ) (n : ℕ), E2 ε2 n ≤ {↑((ℰ n) (ρ ⊗ᵣ^[n])) <ₚ Real.exp (↑n * ((R2 ρ σ).toReal + ε₀ + ε2)) • ↑(σ'' ρ ε m σ n)}) →
    (∀ (ε2 : ℝ) (n : ℕ), 0 ≤ E2 ε2 n) →
    let c' : ℝ → ℕ → ℝ := fun ε2 n => max (σ₁_c i n + σ₁_c i n / ↑n) ((R2 ρ σ).toReal + ε₀ + ε2);
    ∀ (ε2 : ℝ) (n : ℕ), 0 < ε2 → 0 < n →
    (1 / n : ℝ) • (E3 ε2 n).mat * ((((ℰ n) (ρ ⊗ᵣ^[n])).M).log - ((σ'' ρ ε m σ n).M).log).mat ≤ c' ε2 n • (E3 ε2 n).mat →

    ENNReal.ofReal
        ((R1 ρ ε).toReal - (R1 ρ ε).toReal * ⟪(ℰ n (ρ ⊗ᵣ^[n])).M, P1 ε2 n⟫ +
                  (ε2 - ε2 * ⟪(ℰ n (ρ ⊗ᵣ^[n])).M, P2 ε2 n⟫) +
                ⟪(ℰ n (ρ ⊗ᵣ^[n])).M, P1 ε2 n⟫ * (R2 ρ σ).toReal +
              ⟪(ℰ n (ρ ⊗ᵣ^[n])).M, P1 ε2 n⟫ * ε₀ +
            (-((R2 ρ σ).toReal * ⟪(ℰ n (ρ ⊗ᵣ^[n])).M, P2 ε2 n⟫) -
              ε₀ * ⟪(ℰ n (ρ ⊗ᵣ^[n])).M, P2 ε2 n⟫) +
          ⟪(ℰ n (ρ ⊗ᵣ^[n])).M, P2 ε2 n⟫ * c' ε2 n) =
      R1 ρ ε + ENNReal.ofReal ε2 +
          ENNReal.ofReal ⟪P1 ε2 n, ℰ n (ρ ⊗ᵣ^[n])⟫ *
            (ENNReal.ofReal ε2 + R2 ρ σ + ENNReal.ofReal ε₀ -
              (R1 ρ ε + ENNReal.ofReal ε2)) +
        ENNReal.ofReal ⟪P2 ε2 n, ℰ n (ρ ⊗ᵣ^[n])⟫ *
          (ENNReal.ofReal (c' ε2 n) -
            (ENNReal.ofReal ε2 + R2 ρ σ + ENNReal.ofReal ε₀)) := by
  intros ℰ ε₀ hε₀ h₁ P1 P2 E1 E2 E3 hE hexp1 hexp2 hE2 c' ε2 n hε2 hn hlog
  repeat rw [HermitianMat.inner_comm (P1 ε2 n)]
  repeat rw [HermitianMat.inner_comm (P2 ε2 n)]
  ring_nf
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_ofReal]; swap
  · apply add_nonneg
    · rw [← mul_one_sub, ← mul_one_sub, add_assoc, add_assoc, add_assoc]
      apply add_nonneg
      · apply mul_nonneg
        · positivity
        · rw [sub_nonneg]
          apply MState.exp_val_le_one
          apply HermitianMat.proj_le_le_one
      · nth_rw 2 [sub_eq_add_neg]
        rw [← add_assoc, add_comm, add_assoc]
        apply add_nonneg
        · apply mul_nonneg
          · positivity
          · rw [sub_nonneg]
            apply MState.exp_val_le_one
            apply HermitianMat.proj_le_le_one
        · rw [← mul_add, ← neg_add, ← mul_add, add_comm, ← sub_eq_add_neg]
          rw [← sub_mul]
          apply mul_nonneg
          · rw [sub_nonneg]
            apply HermitianMat.inner_mono
            · apply MState.zero_le
            · unfold P1 P2
              rw [← sub_nonneg]
              change 0 ≤ E2 ε2 n
              exact hE2 ε2 n
          · positivity
    · apply mul_nonneg
      · apply HermitianMat.inner_ge_zero
        · apply MState.zero_le
        · apply HermitianMat.proj_le_nonneg
      · positivity
  repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  rw [ENNReal.toReal_sub_of_le ?_ (by finiteness)]; swap
  · grw [hR1R2, ← hε₀, ENNReal.ofReal_zero, add_zero, add_comm]
  repeat rw [ENNReal.toReal_ofReal]
  rotate_left
  · apply HermitianMat.inner_ge_zero --TODO: Positivity extension for HermitianMat.inner
    · apply MState.zero_le  --TODO: Positivity extension for MState
    · apply HermitianMat.proj_le_nonneg --TODO: Positivity extension for projections
  · apply HermitianMat.inner_ge_zero
    · apply MState.zero_le
    · apply HermitianMat.proj_le_nonneg
  · exact hε2.le
  rw [ENNReal.toReal_sub_of_le ?_ (by finiteness)]; swap
  · dsimp [c']
    rw [ENNReal.ofReal_max]
    convert le_max_right _ _
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [ENNReal.ofReal_toReal (by finiteness)]
    abel
  repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  repeat rw [ENNReal.toReal_ofReal (by positivity)]
  ring

set_option maxHeartbeats 800000 in
private theorem EquationS62
    (ρ : MState (H i)) (σ : (n : ℕ) → IsFree (i := i ^ n))
    {ε ε' : Prob} (hε'₁ : 0 < ε') (hε'₂ : ε' < ε) (hε : ε < 1)
    (hR1R2 : R1 ρ ε < R2 ρ σ) (hR1 : R1 ρ ε ≠ ⊤) (hR2 : R2 ρ σ ≠ ⊤)
    (hε₀ : 0 < ε₀_func ρ ε σ ε') (hε₀' : (R1 ρ ε).toReal ≤ (R2 ρ σ).toReal + ε₀_func ρ ε σ ε')
    (m : ℕ) (hm : m ≥ 1 ∧ 𝐃(ρ ⊗ᵣ^[m]‖↑(σ m)) / ↑m < R2 ρ σ + (.ofNNReal ⟨ε₀_func ρ ε σ ε', hε₀.le⟩))
    :
  let ℰ n := pinching_map (σ'' ρ ε m σ n);
    Filter.atTop.liminf (fun n ↦ 𝐃(ℰ n (ρ ⊗ᵣ^[n])‖σ'' ρ ε m σ n) / n) - R1 ρ ε ≤
      ↑(1 - ε') * (R2 ρ σ - R1 ρ ε) := by
  intro ℰ
  set ε₀ := ε₀_func ρ ε σ ε'

  have hliminf_le : Filter.atTop.liminf (fun n ↦
      —log β_ ε(ℰ n (ρ ⊗ᵣ^[n])‖{σ'' ρ ε m σ n}) / n) ≤ (R1 ρ ε).toNNReal := by --(S66)
    rw [ENNReal.coe_toNNReal hR1R2.ne_top]
    unfold R1
    calc _ = Filter.atTop.liminf (fun n => —log
      β_ ε(ℰ n (ρ ⊗ᵣ^[n])‖{(pinching_map (σ'' ρ ε m σ n)) (σ'' ρ ε m σ n)}) / ↑n) := by conv =>
        enter [1, 1, n]
        rw [← pinching_self (σ'' ρ ε m σ n)]
    _ ≤ Filter.atTop.liminf (fun n => —log β_ ε(ρ ⊗ᵣ^[n]‖{(σ'' ρ ε m σ n)}) / ↑n) := by --(S67)
      refine Filter.liminf_le_liminf ?_
      apply Filter.Eventually.of_forall
      intro
      apply ENNReal.div_le_div_right
      apply Prob.negLog_Antitone
      apply OptimalHypothesisRate.optimalHypothesisRate_antitone
    _ ≤ Filter.atTop.liminf (fun n => —log β_ ε(ρ ⊗ᵣ^[n]‖{(«σ⋆» ρ ε n)}) / ↑n) := by --(S68)
      apply LemmaS3_inf _ _ _
        (f := fun n ↦ ⟨σ₁_c i n + Real.log 3, add_nonneg (σ₁_c_pos i n).le (Real.log_nonneg (by norm_num))⟩)
        (σ₁_c_littleO i)
      intro n
      rw [coe_mk, neg_add', Real.exp_sub, Real.exp_log (by positivity)]
      exact «σ''_ge_σ⋆» ρ ε m σ n
    _ = _ := by --(S69)
      congr! 4 with n
      rw [← OptimalHypothesisRate.Lemma3 ε IsCompact_IsFree free_convex]
      rw [← iSup_subtype'']
      exact ((«σ⋆_max» ρ ε n).iSup_eq («σ⋆_free» ρ ε n)).symm

  have hlimsup_le (ε1 : Prob) (hε1 : 0 < (ε1 : ℝ) ∧ (ε1 : ℝ) < 1) :
      Filter.atTop.limsup (fun n ↦ —log β_ (1-ε1)(ℰ n (ρ ⊗ᵣ^[n])‖{σ'' ρ ε m σ n}) / n) ≤
        ((R2 ρ σ).toNNReal + ⟨ε₀, hε₀.le⟩ : NNReal) := by --(S70)
    rw [ENNReal.coe_add, ENNReal.coe_toNNReal hR2]
    unfold R2
    calc _ = Filter.atTop.limsup (fun n => —log
      β_ (1-ε1)(ℰ n (ρ ⊗ᵣ^[n])‖{(pinching_map (σ'' ρ ε m σ n)) (σ'' ρ ε m σ n)}) / ↑n) := by conv =>
        enter [1, 1, n]
        rw [← pinching_self (σ'' ρ ε m σ n)]
    _ ≤ Filter.atTop.limsup (fun n => —log β_ (1-ε1)(ρ ⊗ᵣ^[n]‖{(σ'' ρ ε m σ n)}) / ↑n) := by
      refine Filter.limsup_le_limsup ?_
      apply Filter.Eventually.of_forall
      intro
      apply ENNReal.div_le_div_right
      apply Prob.negLog_Antitone
      apply OptimalHypothesisRate.optimalHypothesisRate_antitone
    _ ≤ Filter.atTop.limsup (fun n => —log β_ (1-ε1)(ρ ⊗ᵣ^[n]‖{(«σ̃» m σ n)}) / ↑n) := by --(S71)
      apply LemmaS3_sup _ _ _
        (f := fun n ↦ ⟨σ₁_c i n + Real.log 3, add_nonneg (σ₁_c_pos i n).le (Real.log_nonneg (by norm_num))⟩)
        (σ₁_c_littleO i)
      intro n
      rw [coe_mk, neg_add', Real.exp_sub, Real.exp_log (by positivity)]
      exact «σ''_ge_σ̃» ρ ε m σ n
    _ ≤ _ := by --(S72)
      have _ := HermitianMat.nonSingular_of_posDef (σ₁_pos i)
      apply Lemma6
      · exact hm.left
      · change (_ : ℝ) < _
        simpa using hε1.left
    _ ≤ _ := hm.right.le --(S73)

  let P1 ε2 n := {(ℰ n (ρ ⊗ᵣ^[n])).M ≥ₚ (Real.exp (↑n*((R1 ρ ε).toReal + ε2))) • (σ'' ρ ε m σ n).M}
  let P2 ε2 n := {(ℰ n (ρ ⊗ᵣ^[n])).M ≥ₚ (Real.exp (↑n*((R2 ρ σ).toReal + ε₀ + ε2))) • (σ'' ρ ε m σ n).M}

  have hEComm ε2 n : Commute (((ℰ n) (ρ ⊗ᵣ^[n])).M - Real.exp ((n : ℝ) * ((R2 ρ σ).toReal + ε₀ + ε2)) • (σ'' ρ ε m σ n).M).mat
      (((ℰ n) (ρ ⊗ᵣ^[n])).M - Real.exp ((n : ℝ) * ((R1 ρ ε).toReal + ε2)) • (σ'' ρ ε m σ n).M).mat := by
    simp only [HermitianMat.mat_sub, MState.mat_M, HermitianMat.mat_smul]
    suffices h : Commute (ℰ n (ρ ⊗ᵣ^[n])).m (σ'' ρ ε m σ n).m by
      apply Commute.sub_left
      · exact (Commute.refl _).sub_right (h.smul_right _)
      · exact (h.symm.sub_right ((Commute.refl _).smul_right _)).smul_left _
    exact pinching_commutes (ρ ⊗ᵣ^[n]) (σ'' ρ ε m σ n)

  have hPcomm ε2 n : Commute (P1 ε2 n).mat (P2 ε2 n).mat := by
    simp only [HermitianMat.proj_le, HermitianMat.mat_cfc, P1, P2]
    apply IsSelfAdjoint.commute_cfc
    · apply HermitianMat.H
    symm
    apply IsSelfAdjoint.commute_cfc
    · apply HermitianMat.H
    exact hEComm ε2 n

  let E1 := 1 - P1 -- (S78)
  let E2 := P1 - P2 -- (S79)
  let E3 := P2 -- (S80)

  have hE_pos ε2 n : 0 ≤ E2 ε2 n := by
    dsimp [E2, P2, P1]
    rw [HermitianMat.proj_le_def, HermitianMat.proj_le_def, sub_nonneg]
    apply HermitianMat.cfc_le_cfc_of_commute
    · intro _ _ hxy; grind
    · exact hEComm ε2 n
    · grw [hR1R2, ← hε₀, add_zero]
      · apply MState.zero_le
      · apply MState.zero_le
      · exact hR2
  clear hEComm

  have Esum : E1 + E2 + E3 = 1 := by
    unfold E1 E2 E3
    abel

  have hE1proj ε2 n : E1 ε2 n = {(ℰ n (ρ ⊗ᵣ^[n])).M <ₚ (Real.exp (↑n*((R1 ρ ε).toReal + ε2))) • (σ'' ρ ε m σ n).M} := by
    dsimp [E1, P1]
    rw [sub_eq_iff_eq_add]
    simp only [HermitianMat.proj_le_add_lt]

  have hE2leProj ε2 n : E2 ε2 n ≤ {(ℰ n (ρ ⊗ᵣ^[n])).M <ₚ (Real.exp (↑n*((R2 ρ σ).toReal + ε₀ + ε2))) • (σ'' ρ ε m σ n).M} := by
    dsimp [E2, P1, P2]
    rw [sub_le_iff_le_add]
    simp only [HermitianMat.proj_le_add_lt]
    exact HermitianMat.proj_le_le_one _ _

  -- (S83)
  let c' ε2 n := (σ₁_c i n + (σ₁_c i n) / n) ⊔ ((R2 ρ σ).toReal + ε₀ + ε2)

  have hc' (ε2 : ℕ → ℝ≥0) (hε2 : ∀ n, ε2 n < 1) :
      ∃ (C : ℝ≥0), ∀ᶠ (n : ℕ) in Filter.atTop, c' (ε2 n) n ≤ C := by
    apply c'_bounded hε2 _ (σ₁_c_pos i)

  -- (S84)
  have hσ'' ε2 n : Real.exp (-n * c' ε2 n) • 1 ≤ (σ'' ρ ε m σ n).M := by
    rcases n.eq_zero_or_pos with rfl | hn
    · have _ : Unique (H (i ^ 0)) := by
        rw [spacePow_zero]
        infer_instance
      apply le_of_eq
      simp [Unique.eq_default (σ'' ρ ε m σ 0)]
    calc
      (σ'' ρ ε m σ n).M ≥ Real.exp (- σ₁_c i n) • (σ' ρ ε m σ n).M := σ'_le_σ'' ρ ε m σ n
      _ ≥ (Real.exp (- σ₁_c i n) * (1 / 3)) • ((σ₁ i) ⊗ᵣ^[n]).M := by
        grw [← hσ₁_le_σ' ρ ε m σ n, smul_smul]
      _ ≥ (Real.exp (- σ₁_c i n) * (1 / 3)) • ((iInf ((σ₁ i) ⊗ᵣ^[n]).M.H.eigenvalues) • 1) := by
        apply smul_le_smul_of_nonneg_left
        · exact ((σ₁ i) ⊗ᵣ^[n]).M.H.iInf_eigenvalues_smul_one_le
        · positivity
      _ = (Real.exp (- σ₁_c i n) * (1 / 3) * (σ₁_mineig i)^n) • 1 := by
        dsimp [σ₁_mineig, iInf]
        rw [← Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues]
        rw [← Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues]
        rw [MState.mat_M, sInf_spectrum_spacePow (σ₁ i) n, MState.mat_M, smul_smul]
      _ = Real.exp (- n * (σ₁_c i n + (σ₁_c i n) / n)) • 1 := by
        rw [σ₁_c_identity i hn]
      _ ≥ Real.exp (-n * c' ε2 n) • 1 := by
        apply smul_le_smul_of_nonneg_right
        · apply Real.exp_le_exp_of_le
          simp only [neg_mul, neg_le_neg_iff]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          dsimp [c']
          exact le_sup_left
        · exact zero_le_one

  have hE3commℰ ε2 n : Commute (E3 ε2 n).mat ((ℰ n (ρ ⊗ᵣ^[n])).M.log.mat) := by
    unfold E3 P2
    rw [HermitianMat.proj_le_def]
    apply HermitianMat.cfc_commute
    apply Commute.sub_left
    · simp only [HermitianMat.val_eq_coe, MState.mat_M, Commute.refl]
    · apply Commute.smul_left
      apply Commute.symm
      exact pinching_commutes (ρ ⊗ᵣ^[n]) (σ'' ρ ε m σ n)

  -- Leo: I think there's a typo in the third eq. of this step: ρ should be ρ^n.
  -- The next set of equations also have ρ_n instead of ρ^n.
  -- (S88)
  have hDleq ε2 n (hε2 : 0 < ε2) (hn : 0 < n) : (𝐃(ℰ n (ρ ⊗ᵣ^[n])‖σ'' ρ ε m σ n) / n : ℝ≥0∞) ≤  ((R1 ρ ε) + .ofReal ε2) +
        .ofReal ⟪P1 ε2 n, ℰ n (ρ ⊗ᵣ^[n])⟫ * ((R2 ρ σ + .ofReal ε₀ + .ofReal ε2) - (R1 ρ ε + .ofReal ε2)) +
        .ofReal ⟪P2 ε2 n, ℰ n (ρ ⊗ᵣ^[n])⟫ * (.ofReal (c' ε2 n) - (R2 ρ σ + .ofReal ε₀ + .ofReal ε2)) := by
    -- see (S81) for comments on why that statement had to be changed
    -- (S85)
    -- (first inequality should have $\sigma_n''$ instead of
    -- $\tilde{\sigma}_n''$; corrected in v4, where $\tilde{\sigma}_n'$ takes
    -- the place of $\sigma_n''$) in this and other steps
    have hE3leq : (1/n : ℝ) • (E3 ε2 n).mat * ((ℰ n (ρ ⊗ᵣ^[n])).M.log.mat - (σ'' ρ ε m σ n).M.log.mat) ≤ (c' ε2 n) • (E3 ε2 n).mat := by
      calc
      (1/n : ℝ) • (E3 ε2 n).mat * ((ℰ n (ρ ⊗ᵣ^[n])).M.log.mat - (σ'' ρ ε m σ n).M.log.mat) ≤ (1/n : ℝ) • (E3 ε2 n).mat * (- (σ'' ρ ε m σ n).M.log.mat) := by
        -- first inequality of (S85)
        have hℰρlognonpos : 0 ≤ -(ℰ n (ρ ⊗ᵣ^[n])).M.log.mat := by
          -- log of state is non-positive
          simp only [HermitianMat.log]
          rw [← HermitianMat.mat_neg, ← HermitianMat.cfc_neg (ℰ n (ρ ⊗ᵣ^[n])).M]
          rw [← HermitianMat.mat_zero]
          rw [← HermitianMat.val_eq_coe, ← HermitianMat.val_eq_coe]
          rw [Subtype.coe_le_coe, HermitianMat.zero_le_cfc (ℰ n (ρ ⊗ᵣ^[n])).M (-Real.log)]
          intro i
          simp
          apply Real.log_nonpos
          · apply MState.eigenvalue_nonneg _
          · apply MState.eigenvalue_le_one
        rw [← sub_nonneg, ← mul_sub_left_distrib]
        conv =>
          rhs
          congr; rfl
          rw [← sub_add (-(σ'' ρ ε m σ n).M.log.mat) ((ℰ n (ρ ⊗ᵣ^[n])).M.log.mat) ((σ'' ρ ε m σ n).M.log.mat)]
          rw [add_comm_sub]
          rw [← add_sub_assoc]
          simp [sub_self (σ'' ρ ε m σ n).M.log.mat]
        simp only [Algebra.smul_mul_assoc, one_div]
        have hE3ℰnonneg : 0 ≤ (E3 ε2 n).mat * -(ℰ n (ρ ⊗ᵣ^[n])).M.log.mat := by
          apply Commute.mul_nonneg _ hℰρlognonpos (Commute.neg_right (hE3commℰ ε2 n))
          apply HermitianMat.proj_le_nonneg
        apply smul_nonneg (inv_nonneg_of_nonneg (Nat.cast_nonneg' n)) hE3ℰnonneg
      _ ≤ (1/n : ℝ) • (E3 ε2 n).mat * (- (Real.exp (-n * c' ε2 n) • (1 : HermitianMat (H (i ^ n)) ℂ)).log.mat) := by
        -- intermediate step in 2nd ineq of S85
        simp only [mul_neg, neg_mul, neg_le_neg_iff]
        have h1logleq : (Real.exp (-(n * c' ε2 n)) • 1 : HermitianMat (H (i ^ n)) ℂ).log.mat ≤ ((σ'' ρ ε m σ n).M).log.mat := by
          -- apply hσ'' ε2 n to log by monotonicity
          rw [← HermitianMat.val_eq_coe, ← HermitianMat.val_eq_coe]
          rw [Subtype.coe_le_coe]
          have h_comm : Commute ((Real.exp _ • 1 : HermitianMat _ ℂ).mat) _ :=
            Commute.smul_left (Commute.one_left (σ'' ρ ε m σ n).M.mat) (Real.exp (-(n * c' ε2 n)))
          exact HermitianMat.log_le_log_of_commute h_comm (by simpa using hσ'' ε2 n)
            (Matrix.PosDef.smul Matrix.PosDef.one (Real.exp_pos (-(n * c' ε2 n))))
        rw [← sub_nonneg] at h1logleq
        rw [← sub_nonneg, ← mul_sub_left_distrib]
        simp only [one_div, Algebra.smul_mul_assoc]
        have hE3commlog : Commute (E3 ε2 n).mat ((σ'' ρ ε m σ n).M.log.mat - (Real.exp (-(n * c' ε2 n)) • 1 : HermitianMat _ ℂ).log.mat) := by
          -- projector commutes with logs
          apply Commute.sub_right
          · -- prove Commute (E3 _) (σ'' _).log
            unfold E3 P2
            rw [HermitianMat.proj_le_def]
            apply HermitianMat.cfc_commute
            apply Commute.sub_left
            · exact pinching_commutes (ρ ⊗ᵣ^[n]) (σ'' ρ ε m σ n)
            · apply Commute.smul_left
              · rfl
          · -- prove `Commute (E3 _) (_ 1).log`
            conv_rhs =>
              rw [HermitianMat.log_smul (by positivity)]
              simp only [
                Real.log_exp, neg_smul, HermitianMat.log_one,
                add_zero, NegMemClass.coe_neg,
                HermitianMat.val_eq_coe, selfAdjoint.val_smul,
                selfAdjoint.val_one
                ]
            simp [Commute.neg_right_iff, Commute.smul_right (Commute.one_right _) _]
        apply smul_nonneg (inv_nonneg_of_nonneg (Nat.cast_nonneg' n))
        apply Commute.mul_nonneg _ h1logleq hE3commlog
        apply HermitianMat.proj_le_nonneg
      _ = (c' ε2 n) • (E3 ε2 n).mat := by
        rw [HermitianMat.log_smul (by positivity)]
        simp [smul_smul]
        field_simp
    --Linearly combine S81, S82, S85:
    calc
      𝐃(ℰ n (ρ ⊗ᵣ^[n])‖σ'' ρ ε m σ n) / (n : ENNReal) ≤
        ENNReal.ofReal (⟪(ℰ n (ρ ⊗ᵣ^[n])).M, ((R1 ρ ε).toReal + ε2) • E1 ε2 n⟫
        + ⟪(ℰ n (ρ ⊗ᵣ^[n])).M, ((R2 ρ σ).toReal + ε₀ + ε2) • E2 ε2 n⟫
        + ⟪(ℰ n (ρ ⊗ᵣ^[n])).M, c' ε2 n • E3 ε2 n⟫)
      := by
        -- (S86) to (S88)
        unfold qRelativeEnt SandwichedRelRentropy
        simp only [↓reduceIte]
        have σ''_pd := σ''_posdef ρ ε m σ
        simp only [MState.mat_M] at σ''_pd
        have hker : (σ'' ρ ε m σ n).M.ker ≤ (ℰ n (ρ ⊗ᵣ^[n])).M.ker :=
          ker_le_ker_pinching_of_PosDef (ρ ⊗ᵣ^[n]) (σ'' ρ ε m σ n) (σ''_pd n)
        simp only [hker, ↓reduceDIte]
        have hMulOne : (ℰ n (ρ ⊗ᵣ^[n])).M.mat * (1 : Matrix (H (i ^ n)) (H (i ^ n)) ℂ) = (ℰ n (ρ ⊗ᵣ^[n])).M.mat := Matrix.mul_one (ℰ n (ρ ⊗ᵣ^[n])).M.mat
        have hOneMulCommute : Commute (1 : HermitianMat _ ℂ).mat (ℰ n (ρ ⊗ᵣ^[n])).M.mat := Commute.one_left (ℰ n (ρ ⊗ᵣ^[n])).M.mat
        have hOneIsOne : ∀ (ε : ℝ) (n : ℕ), (1 : ℝ → ℕ → HermitianMat (H (i ^ n)) ℂ) ε n = (1 : HermitianMat (H (i ^ n)) ℂ) := by
          intro ε n; rfl
        /- convert Esum to the HermitianMat equality at point (ε2, n) -/
        have Esum' : (E1 ε2 n).mat + (E2 ε2 n).mat + (E3 ε2 n).mat = 1 :=
          congrArg HermitianMat.mat (congrFun (congrFun Esum ε2) n)
        conv =>
          enter [1, 1, 1, 1]
          rw [HermitianMat.inner_def]
          rw [← hMulOne]
          rw [← Esum']
        -- (S87)
        /- Use hE1leq, hE2leq, hE3leq -/

        /-the next two `have`s are duplicates-/
        -- TODO streamline what's below
        /-it should transform a HermitianMat inequality into a reals inequality with HermitianMat.inner_mono,
        the difficulty here is that inner_mono relies on the entries being HermitianMat, but the inequalities are expressed as matrices-/
        have hE2comm : Commute (E2 ε2 n).mat (((ℰ n (ρ ⊗ᵣ^[n])).M.log - (σ'' ρ ε m σ n).M.log).mat) := by
        -- TODO this needs to be extracted from here, it's badly redundant
          apply Commute.sub_right
          · unfold E2 P1 P2
            simp
            rw [HermitianMat.proj_le_def, HermitianMat.proj_le_def]
            apply Commute.sub_left
            · apply HermitianMat.cfc_commute
              apply Commute.sub_left
              · rfl
              · simp
                apply Commute.symm
                exact pinching_commutes (ρ ⊗ᵣ^[n]) (σ'' ρ ε m σ n)
            · apply HermitianMat.cfc_commute
              apply Commute.sub_left
              · rfl
              · simp
                apply Commute.symm
                exact pinching_commutes (ρ ⊗ᵣ^[n]) (σ'' ρ ε m σ n)
          · unfold E2 P1 P2
            simp
            rw [HermitianMat.proj_le_def, HermitianMat.proj_le_def]
            apply Commute.sub_left
            · apply HermitianMat.cfc_commute
              apply Commute.sub_left
              · exact pinching_commutes (ρ ⊗ᵣ^[n]) (σ'' ρ ε m σ n)
              · simp
            · apply HermitianMat.cfc_commute
              apply Commute.sub_left
              · exact pinching_commutes (ρ ⊗ᵣ^[n]) (σ'' ρ ε m σ n)
              · simp
        have hE2leqInner : (n : ℝ)⁻¹ * ((ℰ n (ρ ⊗ᵣ^[n])).M.mat * (E2 ε2 n).mat * ((ℰ n (ρ ⊗ᵣ^[n])).M.log.mat - (σ'' ρ ε m σ n).M.log.mat)).trace.re ≤
            ((R2 ρ σ).toReal + ε₀ + ε2) * ⟪(ℰ n (ρ ⊗ᵣ^[n])).M, E2 ε2 n⟫ := by
          open HermMul in
          -- (S82) -- see (S81) for comments
          have hE2leq ε2 (n : ℕ) (hε2 : 0 < ε2) : (1/n : ℝ) • (E2 ε2 n).mat * ((ℰ n (ρ ⊗ᵣ^[n])).M.log.mat - (σ'' ρ ε m σ n).M.log.mat) ≤ ((R2 ρ σ).toReal + ε₀ + ε2) • (E2 ε2 n).mat := by
            refine rexp_mul_smul_proj_lt_mul_sub_le_mul_sub'
              (pinching_commutes (ρ ⊗ᵣ^[n]) (σ'' ρ ε m σ n)) ?_ (σ''_posdef ρ ε m σ n) rfl
            rw [← HermitianMat.zero_le_iff]
            apply MState.zero_le
          simp at hE2leq
          rw [← Complex.re_ofReal_mul (↑n)⁻¹, ← smul_eq_mul, ← Matrix.trace_smul]
          rw [← RCLike.re_to_complex]
          conv =>
            enter [1, 2]
            rw [mul_assoc]
            enter [1, 2, 2]
            norm_cast
            rw [← HermitianMat.symmMul_of_commute hE2comm]
          conv at hE2leq =>
            enter [ε2, n, hε2, 1, 2, 2]
            norm_cast
          specialize hE2leq ε2 n hε2
          rw [← HermitianMat.symmMul_of_commute hE2comm] at hE2leq
          rw [← Matrix.mul_smul (ℰ n (ρ ⊗ᵣ^[n])).M.mat (Complex.ofReal (n : ℝ)⁻¹) (HermitianMat.symmMul _ _).mat]
          conv =>
            enter [1, 2, 1, 2]
            equals HermitianMat.mat ((n : ℝ)⁻¹ • (HermitianMat.symmMul (E2 ε2 n)
              ((((ℰ n) (ρ ⊗ᵣ^[n])).M.log - (σ'' ρ ε m σ n).M.log)))) =>
              rfl --TODO: Lemma to work with this better
          rw [← HermitianMat.inner_eq_re_trace (ℰ n (ρ ⊗ᵣ^[n])).M _]
          rw [← HermitianMat.inner_smul_right]
          exact ((HermitianMat.inner_mono ((ℰ n (ρ ⊗ᵣ^[n]))).zero_le) hE2leq)
        simp at hE3leq
        /-this and the `have` above are duplicates-/
        have hE3comm : Commute (E3 ε2 n).mat (((ℰ n (ρ ⊗ᵣ^[n])).M.log - (σ'' ρ ε m σ n).M.log).mat) := by
          apply Commute.sub_right
          · simp [(hE3commℰ ε2 n)]
          · unfold E3 P2
            simp
            rw [HermitianMat.proj_le_def]
            apply HermitianMat.cfc_commute
            apply Commute.sub_left
            · exact pinching_commutes (ρ ⊗ᵣ^[n]) (σ'' ρ ε m σ n)
            · simp
        /- hE3commℰ -/
        have hE3leqInner : (n : ℝ)⁻¹ * ((ℰ n (ρ ⊗ᵣ^[n])).M.mat * (E3 ε2 n).mat * ((ℰ n (ρ ⊗ᵣ^[n])).M.log.mat - (σ'' ρ ε m σ n).M.log.mat)).trace.re ≤ (c' ε2 n) * ⟪(ℰ n (ρ ⊗ᵣ^[n])).M, E3 ε2 n⟫ := by
          open HermMul in
          rw [← Complex.re_ofReal_mul (↑n)⁻¹ _, ← smul_eq_mul, ← Matrix.trace_smul]
          rw [← RCLike.re_to_complex]
          conv =>
            enter [1, 2]
            rw [mul_assoc]
            enter [1, 2, 2, 2]
            norm_cast
          conv =>
            enter [1, 2, 1, 2, 2]
            rw [← HermitianMat.symmMul_of_commute hE3comm]
          conv at hE3leq =>
            enter [1, 2, 2]
            norm_cast
          rw [← HermitianMat.symmMul_of_commute hE3comm] at hE3leq
          conv at hE3leq =>
            lhs
            rw [← HermitianMat.mat_smul (n : ℝ)⁻¹ (HermitianMat.symmMul _ _)]
          conv at hE3leq =>
            rhs
            rw [← HermitianMat.mat_smul _ (E3 ε2 n)]
          rw [← Matrix.mul_smul (ℰ n (ρ ⊗ᵣ^[n])).M.mat (Complex.ofReal (n : ℝ)⁻¹) (HermitianMat.symmMul _ _).mat]
          conv =>
            enter [1, 2, 1, 2]
            equals HermitianMat.mat ((n : ℝ)⁻¹ • (HermitianMat.symmMul (E3 ε2 n)
              ((((ℰ n) (ρ ⊗ᵣ^[n])).M.log - (σ'' ρ ε m σ n).M.log)))) =>
              rfl --TODO: Lemma to work with this better (see above TODO)
          rw [← HermitianMat.inner_eq_re_trace (ℰ n (ρ ⊗ᵣ^[n])).M ((n : ℝ)⁻¹ • (HermitianMat.symmMul _ _))]
          rw [← HermitianMat.inner_smul_right]
          exact ((HermitianMat.inner_mono ((ℰ n (ρ ⊗ᵣ^[n]))).zero_le) hE3leq)
        simp only [IsMaximalSelfAdjoint.RCLike_selfadjMap, MState.mat_M, HermitianMat.mat_sub,
          RCLike.re_to_complex, HermitianMat.inner_smul_right, ge_iff_le]
        conv =>
          enter [1, 1, 1, 1]
          rw [mul_add, mul_add, add_mul, add_mul, trace_add, trace_add]
        simp [← ENNReal.ofReal_coe_nnreal, NNReal.toReal]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos (by simp [hn]), div_eq_inv_mul]
        rw [ENNReal.ofReal_le_ofReal_iff']
        · left
          rw [mul_add, mul_add]
          apply add_le_add_three
          · rw [HermitianMat.inner_def]
            simp

            -- (S81)
            /- A literal translation of the paper would read:
                (1/n : ℝ) • (E1 ε2 n).mat * ((ℰ n (ρ ⊗ᵣ^[n])).M.log.mat - (σ'' n).M.log.mat) ≤ ((R1 ρ ε).toReal + ε2) • (E1 ε2 n).mat
            But this is simply not true! Because what happens when `ℰ n (ρ ⊗ᵣ^[n])` has a zero eigenvalue, which
            it can? Then (S81) is an inequality of operators where the LHS has an operator with a "negative
            infinity" eigenvalue, intuitively. This isn't something very well defined, certainly not supported
            in our definitions. This only becomes mathematically meaningful when we see how it's used later, in
            (S88): both sides are traced against `ℰ n (ρ ⊗ᵣ^[n])`, so that the 0 eigenvalues becomes irrelevant. This
            is the version we state and prove, then.

            Luckily, (S82) and (S85) are correct as written (in a particular interpretation), because
            there the problematic subspaces are indeed projected out by the E₂ and E₃ operators.
            -/
            have hE1leq ε2 (n : ℕ) (hε2 : 0 < ε2) :
                ⟪(ℰ n (ρ ⊗ᵣ^[n])).M, (((1 / (n : ℝ)) • (E1 ε2 n)).symmMul
                  ((((pinching_map (σ'' ρ ε m σ n)) (ρ ⊗ᵣ^[n])).M).log - ((σ'' ρ ε m σ n).M).log : HermitianMat _ ℂ))⟫ ≤
                  ⟪(ℰ n (ρ ⊗ᵣ^[n])).M, ((R1 ρ ε).toReal + ε2) • (E1 ε2 n)⟫ := by
              refine rexp_mul_smul_proj_lt_mul_sub_le_mul_sub
                (pinching_commutes (ρ ⊗ᵣ^[n]) (σ'' ρ ε m σ n)) (by positivity) ?_ (σ''_posdef ρ ε m σ n) rfl
              rw [← HermitianMat.zero_le_iff]
              apply MState.zero_le

            simp only [HermitianMat.inner_def] at hE1leq
            conv at hE1leq =>
              enter [ε2, n, hε2, 1]
              rw [HermitianMat.symmMul_of_commute (commute_aux n (E := E1 ε2 n) (pinching_commutes (ρ ⊗ᵣ^[n]) (σ'' ρ ε m σ n)) rfl)]
            simp at hE1leq
            conv at hE1leq =>
              intro ε2 n hε2
              rw [← mul_assoc]
              pattern (pinching_map (σ'' ρ ε m σ n))
              change ℰ n
            apply (hE1leq ε2 n hε2)
          · apply hE2leqInner
          · apply hE3leqInner
      -- (S88)
      _ = _ := by
        unfold E1 E2 E3
        simp [inner_sub_right]
        ring_nf
        apply EquationS88 <;> assumption

  clear hE_pos

  -- (S91)
  have hliminfDleq : Filter.atTop.liminf (fun n ↦ 𝐃(ℰ n (ρ ⊗ᵣ^[n])‖σ'' ρ ε m σ n) / n) ≤
        (R1 ρ ε) + .ofReal (1 - ε.val) * (R2 ρ σ + .ofReal ε₀ - R1 ρ ε) := by
    --Pick a sequence `ε2 n` that converges slowly enough that we ensure both the P1 and P2 terms,
    -- which otherwise depend on a 'constant' ε₁ and ε₂, both converge to zero as well. We do this
    -- by looking at the max of the P1 and P2 terms.
    have this :=
      exists_liminf_zero_of_forall_liminf_limsup_le_with_UB (1 - ε) 0
      (fun x n ↦ ENNReal.ofNNReal ⟨⟪P1 x n, ℰ n (ρ ⊗ᵣ^[n])⟫,
        HermitianMat.inner_ge_zero (HermitianMat.proj_le_nonneg _ _) (ℰ n (ρ ⊗ᵣ^[n])).zero_le⟩)
      (fun x n ↦ ENNReal.ofNNReal ⟨⟪P2 x n, ℰ n (ρ ⊗ᵣ^[n])⟫,
        HermitianMat.inner_ge_zero (HermitianMat.proj_le_nonneg _ _) (ℰ n (ρ ⊗ᵣ^[n])).zero_le⟩)
      zero_lt_one ?_ ?_; rotate_left
    · have hliminfP1 ε2 (hε2 : 0 < ε2) := --(S76)
        LemmaS2liminf hε2 (fun n ↦ ℰ n (ρ ⊗ᵣ^[n])) (σ'' ρ ε m σ) hliminf_le

      conv at hliminfP1 =>
        enter [ε2, hε2, 1, 1, n, 2]
        change P1 _ _
      --The goal is now hliminfP1, up to stupid casting
      intro x hx
      specialize hliminfP1 ⟨x, hx.le⟩ hx
      apply ENNReal.ofReal_mono at hliminfP1
      convert ← hliminfP1 using 1
      dsimp
      conv =>
        enter [2, 1, n]
        rw [← ENNReal.ofReal_eq_coe_nnreal]
      refine ENNReal.ofReal_mono.map_liminf_of_continuousAt _ ?_ ?_ ?_
      · apply ENNReal.continuous_ofReal.continuousAt
      · use 1
        simp only [Filter.eventually_map, Filter.eventually_atTop,
          forall_exists_index]
        intro a x hx
        apply (hx x le_rfl).trans
        rw [← (ℰ x (ρ ⊗ᵣ^[x])).tr, ← HermitianMat.one_inner]
        apply HermitianMat.inner_mono' (ℰ x (ρ ⊗ᵣ^[x])).zero_le
        apply HermitianMat.proj_le_le_one
      · use 0
        simp only [Filter.eventually_map, Filter.eventually_atTop]
        use 0
        intro _ _
        apply HermitianMat.inner_ge_zero
        · apply HermitianMat.proj_le_nonneg
        · apply MState.zero_le
    · have hlimsupP2' ε2 (hε2 : 0 < ε2) :
          Filter.atTop.limsup (fun n ↦ ⟪P2 ε2 n, ℰ n (ρ ⊗ᵣ^[n])⟫) = 0 := by
        apply le_antisymm
        · apply le_of_forall_pos_le_add
          intro ε1' hε1'
          let ε1 := min ε1' (1/2)
          have hε1 : 0 < (ε1 : ℝ) ∧ (ε1 : ℝ) < 1 := by
            constructor
            · rw [lt_min_iff]
              exact ⟨hε1', by norm_num⟩
            · rw [min_lt_iff]
              exact Or.inr (by norm_num)
          have hlimsupP2  ε2 (hε2 : 0 < ε2) (ε1 : Prob) (hε1 : 0 < (ε1 : ℝ) ∧ (ε1 : ℝ) < 1) := --(S77)
            LemmaS2limsup hε2 (fun n ↦ ℰ n (ρ ⊗ᵣ^[n])) (σ'' ρ ε m σ) (hlimsup_le ε1 hε1)
          specialize hlimsupP2 ⟨ε2, hε2.le⟩ hε2 ⟨ε1, ⟨hε1.1.le, hε1.2.le⟩⟩ hε1
          trans ε1
          · convert hlimsupP2
            simp only [Prob.coe_one_minus, sub_sub_cancel]
          · simp only [one_div, zero_add, inf_le_left, ε1]
        · apply Filter.le_limsup_of_frequently_le ?_ ?_
          · rw [Filter.frequently_atTop]
            intro n
            refine ⟨n, le_rfl, ?_⟩
            exact HermitianMat.inner_ge_zero (HermitianMat.proj_le_nonneg _ _)
              (ℰ n (ρ ⊗ᵣ^[n])).zero_le
          · apply Filter.isBoundedUnder_of
            use 1
            intro n
            rw [← (ℰ n (ρ ⊗ᵣ^[n])).tr, ← HermitianMat.one_inner]
            exact HermitianMat.inner_mono' (ℰ n (ρ ⊗ᵣ^[n])).zero_le
              (HermitianMat.proj_le_le_one _ _)
      --The goal is now hlimsupP2', up to stupid casting
      intro x hx
      specialize hlimsupP2' x hx
      apply le_of_eq at hlimsupP2'
      apply ENNReal.ofReal_mono at hlimsupP2'
      convert ← hlimsupP2' using 1
      swap
      · simp
      dsimp
      conv =>
        enter [2, 1, n]
        exact (ENNReal.ofReal_eq_coe_nnreal _).symm
      refine ENNReal.ofReal_mono.map_limsup_of_continuousAt _ ?_ ?_ ?_
      · apply ENNReal.continuous_ofReal.continuousAt
      · use 1
        simp only [Filter.eventually_map, Filter.eventually_atTop]
        use 0
        intro x hx
        rw [← (ℰ x (ρ ⊗ᵣ^[x])).tr, ← HermitianMat.one_inner]
        apply HermitianMat.inner_mono' (ℰ x (ρ ⊗ᵣ^[x])).zero_le
        apply HermitianMat.proj_le_le_one
      · use 0
        simp only [Filter.eventually_map, Filter.eventually_atTop, forall_exists_index]
        intro a x hx
        grw [← hx x le_rfl]
        apply HermitianMat.inner_ge_zero
        · apply HermitianMat.proj_le_nonneg
        · apply MState.zero_le
    rcases this with ⟨ε2, hg₁, hg₂, hg₃, hliminf_g₁, hliminf_g₂⟩

    replace hDleq := Filter.liminf_le_liminf (Filter.eventually_atTop.mpr ⟨1, fun (n : ℕ) hnge1 ↦ hDleq (ε2 n) n (hg₁ n) hnge1⟩)
    apply le_trans hDleq -- (S89)
    have hP2zero : Filter.atTop.Tendsto (fun n ↦ .ofReal ⟪P2 (ε2 n) n, ℰ n (ρ ⊗ᵣ^[n])⟫ *
        (.ofReal (c' (ε2 n) n) - (R2 ρ σ + .ofReal ε₀ + .ofReal (ε2 n)))) (𝓝 0) := by
      have hf : Filter.atTop.Tendsto (fun n ↦ .ofReal ⟪P2 (ε2 n) n, ℰ n (ρ ⊗ᵣ^[n])⟫) (𝓝 (0 : ℝ≥0∞)) := by
        refine tendsto_of_le_liminf_of_limsup_le bot_le ?_
        convert hliminf_g₂
        apply ENNReal.ofReal_eq_coe_nnreal
      obtain ⟨C, hC⟩ := hc' ε2 hg₂
      refine ENNReal.bdd_le_mul_tendsto_zero (b := C) (by finiteness) hf ?_
      filter_upwards [hC] with a ha
      grw [ha]
      simp
    conv =>
      enter [1, 1]
      rw [← Pi.add_def]
    rw [ENNReal.liminf_add_of_right_tendsto_zero hP2zero _]
    conv =>
      enter [1, 1, n]
      rw [add_assoc]
    rw [liminf_const_add (Filter.atTop) _ (R1 ρ ε) (by isBoundedDefault) (by isBoundedDefault)]
    conv =>
      enter [1, 2, 1]
      rw [← Pi.add_def]
      enter [2, n]
      rw [mul_comm]
    rw [ENNReal.liminf_add_of_left_tendsto_zero ?_ _]
    · rw [ENNReal.add_le_add_iff_left hR1]
      apply le_trans (ENNReal.liminf_mul_le ?_ ?_)
      · rw [mul_comm]
        gcongr
        · -- Alex: This is hard to prove with hliminfP1, because in hliminfP1 the ε2 is fixed inside
          --  the liminf, but here it is allowed to vary with n. We need to 'upgrade' hliminfP1 with
          --  the following fact, which should (in some form) be its own theorem:
          /- (∀ x, x > 0 → liminf (n ↦ f x n) ≤ y) →
            ∃ g : ℕ → ℝ, (∀ x, g x > 0) ∧ (liminf g = 0) ∧ (liminf (n ↦ f (g n) n) ≤ y)
          -/
          --this is stated above as exists_liminf_zero_of_forall_liminf_le.
          -- ... but then this needs to match up with the ε2 ...
          --Ahh, no, so actually this `g` is how we want to pick our `ε2` above!
          convert hliminf_g₁ using 3 with n
          apply ENNReal.ofReal_eq_coe_nnreal
        · conv =>
            enter [1, 1, n]
            rw [ENNReal.add_sub_add_eq_sub_right (by finiteness)]
          rw [Filter.limsup_const]
      · left
        apply ne_bot_of_le_ne_bot (b := ENNReal.ofReal ε₀)
        · rwa [← bot_lt_iff_ne_bot, ENNReal.bot_eq_zero, ENNReal.ofReal_pos]
        apply Filter.le_limsup_of_frequently_le'
        apply Filter.Eventually.frequently
        apply Filter.Eventually.of_forall
        intro x
        rw [add_right_comm, ← ENNReal.sub_add_eq_add_sub (add_le_add_right hR1R2.le _) (by finiteness)]
        exact le_add_self
      · left
        apply ne_top_of_le_ne_top (b := R2 ρ σ + ENNReal.ofReal ε₀ + 1) (by finiteness)
        apply Filter.limsup_le_of_le (by isBoundedDefault) ?_
        apply Filter.Eventually.of_forall
        intro x
        suffices h : ε2 x ≤ 1 by
          nth_grw 1 [h]
          simp
        exact (hg₂ x).le
    · rw [← ENNReal.ofReal_zero ]
      apply ENNReal.tendsto_ofReal
      rw [← NNReal.tendsto_coe] at hg₃
      exact hg₃

  simp only [tsub_le_iff_right]
  convert hliminfDleq using 1
  rw [add_comm, ENNReal.add_right_inj hR1]
  --Rewriting through the ENNReal madness to get (S92)
  conv =>
    rhs
    rw [← ENNReal.sub_add_eq_add_sub hR1R2.le hR1, ← ENNReal.ofReal_toReal hR1,
        ← ENNReal.ofReal_toReal hR2, ← ENNReal.ofReal_sub _ (ENNReal.toReal_nonneg),
        ← ENNReal.ofReal_add (sub_nonneg.mpr (ENNReal.toReal_mono hR2 hR1R2.le)) hε₀.le,
        ← ENNReal.ofReal_mul (by simp)]
    rhs
    rw [← ENNReal.toReal_sub_of_le hR1R2.le hR2]

    equals (1 - ε'.val) * (R2 ρ σ - R1 ρ ε).toReal =>
      unfold ε₀
      field_simp [show 1 - ε.val ≠ 0 from ne_of_gt (sub_pos.mpr hε)]
      ring_nf
  rw [ENNReal.ofReal_mul (by simp), Prob.ofNNReal_toNNReal,
    ENNReal.ofReal_toReal (by simp [hR1, hR2]), Prob.coe_one_minus]

/-- Lemma 7 from the paper. We write `ε'` for their `\tilde{ε}`. -/
private theorem Lemma7 (ρ : MState (H i)) {ε : Prob} (hε : 0 < ε ∧ ε < 1) (σ : (n : ℕ) → IsFree (i := i ^ n)) :
    (R2 ρ σ ≥ R1 ρ ε) →
    ∀ ε' : Prob, (hε' : 0 < ε' ∧ ε' < ε) → -- ε' is written as \tilde{ε} in the paper.
    ∃ σ' : (n : ℕ) → IsFree (i := i ^ n),
    R2 ρ σ' - R1 ρ ε ≤ .ofNNReal (1 - ε' : Prob) * (R2 ρ σ - R1 ρ ε)
    := by
  --This proof naturally splits out into LemmaS62:
  --  `lim inf n→∞ 1/n D(E_n(ρ^⊗n)‖σ''_n) − R1,ϵ ≤ (1 − ˜ϵ)(R2 − R1,ϵ).`
  --which is proved above. Here, set up the preliminiaries (appropriate finiteness
  -- conditions, nonzeroness, etc.) get S62, prove S61, and the conclusion is just `rw [S61] at S62`.

  --First deal with the easy case of R1 = R2.
  intro hR1R2 ε' ⟨hε'₁, hε'₂⟩
  rw [ge_iff_le, le_iff_lt_or_eq, or_comm] at hR1R2
  rcases hR1R2 with hR1R2|hR1R2
  · use σ
    simp [hR1R2]
  --This leaves us with the stronger statement that R1 < R2 strictly.
  --Before proceeding, let's reduce to the case that they're finite.
  have hR1 : R1 ρ ε ≠ ⊤ := hR1R2.ne_top
  rcases eq_or_ne (R2 ρ σ) ⊤ with hR2|hR2
  · rw [hR2, ENNReal.top_sub hR1, ENNReal.mul_top', if_neg]
    · simp
    · have : ε'.val < 1 := hε'₂.trans hε.2
      rcases ε' with ⟨ε', hε'₁, hε'₂⟩
      simp only [Prob.toNNReal, Prob.coe_one_minus, ENNReal.coe_eq_zero]
      rw [Subtype.ext_iff, val_eq_coe, val_eq_coe, coe_zero, coe_mk]
      grind

  let ε₀ : ℝ := (R2 ρ σ - R1 ρ ε).toReal * (ε - ε') / (1 - ε)
  have hε₀ : 0 < ε₀ :=
    have := sub_pos.mpr (show ε.val < 1 from hε.2)
    have := sub_pos.mpr (show ε'.val < ε from hε'₂)
    have : 0 < (SteinsLemma.R2 ρ σ - SteinsLemma.R1 ρ ε).toReal :=
      ENNReal.toReal_pos (tsub_pos_of_lt hR1R2).ne' (ENNReal.sub_ne_top hR2)
    by positivity
  have hε₀' : (R1 ρ ε).toReal ≤ (R2 ρ σ).toReal + ε₀ := by
    dsimp [ε₀]
    rw [← sub_nonneg]
    have _ := sub_pos.mpr (show ε.val < 1 from hε.2)
    have _ := sub_pos.mpr (show ε'.val < ε from hε'₂)
    rw [ENNReal.toReal_sub_of_le hR1R2.le (by finiteness)]
    field_simp
    suffices h : 0 ≤ ((R2 ρ σ).toReal - (R1 ρ ε).toReal) * ((↑ε - ↑ε') + (1 - ↑ε)) by
      convert h using 1
      · exact zero_mul _
      · ring_nf
    rw [← ENNReal.toReal_sub_of_le hR1R2.le (by finiteness)]
    positivity

  -- m exists because R2 + ε₀ is strictly above R2, which is the liminf.
  obtain ⟨m, hm⟩ :=
    have h : R2 ρ σ < R2 ρ σ + .ofNNReal ⟨ε₀, hε₀.le⟩ :=
      ENNReal.lt_add_right hR2 (by simp [← NNReal.coe_eq_zero, hε₀.ne'])
    (Filter.frequently_lt_of_liminf_lt (h := h)).forall_exists_of_atTop 1

  have qRel_σ''_le_σ' n : 𝐃(ρ ⊗ᵣ^[n]‖σ'' ρ ε m σ n) ≤ 𝐃(ρ ⊗ᵣ^[n]‖σ' ρ ε m σ n) + ENNReal.ofReal (σ₁_c i n) := by
    rw [← Real.log_exp (σ₁_c i n)]
    apply qRelEntropy_le_add_of_le_smul
    apply σ''_le_σ'

  have qRel_σ'_le_σ'' n : 𝐃(ρ ⊗ᵣ^[n]‖σ' ρ ε m σ n) ≤ 𝐃(ρ ⊗ᵣ^[n]‖σ'' ρ ε m σ n) + ENNReal.ofReal (σ₁_c i n) := by
    rw [← Real.log_exp (σ₁_c i n)]
    apply qRelEntropy_le_add_of_le_smul
    rw [← inv_smul_le_iff_of_pos (by positivity), ← Real.exp_neg]
    apply σ'_le_σ''

  -- Definition of the pinching map w.r.t. σ'' in Eq. (S55)
  let ℰ n := pinching_map (σ'' ρ ε m σ n)

  -- Number of distinct eigenvalues of σ'' in Eq. (S56) is
  -- Fintype.card (spectrum ℝ (σ'' n).m), which is dₙ in the paper.
  have hdle n : Fintype.card (spectrum ℝ (σ'' ρ ε m σ n).m) ≤ n + 1 := by
    rw [(σ'' ρ ε m σ n).M.H.card_spectrum_eq_image (A := (σ'' ρ ε m σ n).m)]
    rcases n.eq_zero_or_pos with rfl | hn
    · have _ : Unique (H (i ^ 0)) := by
        rw [spacePow_zero]
        infer_instance
      simp
    rw [← Set.ncard_coe_finset]
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    have eq : ∃ (e : Equiv.Perm _), (σ'' ρ ε m σ n).M.H.eigenvalues =
        (fun x ↦ (σ''_unnormalized ρ ε m σ n).trace⁻¹ * Real.exp (f_map i n x)) ∘ (σ' ρ ε m σ n).M.H.eigenvalues ∘ e := by
      convert (σ' ρ ε m σ n).M.cfc_eigenvalues (fun x ↦ (σ''_unnormalized ρ ε m σ n).trace⁻¹ * Real.exp (f_map i n x))
      rw [HermitianMat.cfc_const_mul, ← σ''_unnormalized, σ'']
    rcases eq with ⟨eq, heq⟩
    rw [heq]
    simp only [Set.range_comp, MState.mat_M, EquivLike.range_eq_univ, Set.image_univ, ge_iff_le]
    let S : Set ℝ := (fun x => Real.exp (f_map i n x)) '' Set.Icc ((σ₁_mineig i ^ n) / 3) 1
    have h_card_subs : Set.ncard S ≤ n + 1 ∧ S.Finite := by
      exact f_image_bound (σ₁_mineig i) n (mineig_pos i) hn (log_le_f i) (f_le_log i)
    let S₂ : Set ℝ := (fun x => (σ''_unnormalized ρ ε m σ n).trace⁻¹ * Real.exp (f_map i n x)) '' Set.Icc ((σ₁_mineig i ^ n) / 3) 1
    obtain ⟨h_card_subs₂, h_s₂_finite⟩ : Set.ncard S₂ ≤ n + 1 ∧ S₂.Finite := by
      have hS₂ : S₂ = ((σ''_unnormalized ρ ε m σ n).trace⁻¹ * ·) '' S := by
        simp [S, S₂, Set.image_image]
      constructor
      · rw [hS₂]
        exact (Set.ncard_image_le h_card_subs.right).trans h_card_subs.left
      · rw [hS₂]
        exact h_card_subs.right.image _
    refine (Set.ncard_le_ncard (t := (fun x => (σ''_unnormalized ρ ε m σ n).trace⁻¹ *
      Real.exp (f_map i n x)) '' Set.Icc (((σ₁_mineig i) ^ n) / 3) 1) ?_ h_s₂_finite).trans h_card_subs₂
    apply Set.image_mono
    rintro _ ⟨k, rfl⟩
    refine ⟨?_, MState.eigenvalue_le_one _ _⟩
    refine le_trans ?_ (ciInf_le (Finite.bddBelow_range _) k)
    refine le_trans ?_ ((HermitianMat.H _).iInf_eigenvalues_le (hσ₁_le_σ' ρ ε m σ n) _)
    dsimp [σ₁_mineig, iInf]
    rw [← Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues]
    rw [← Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues]
    rw [HermitianMat.val_eq_coe, HermitianMat.mat_smul]
    rw [spectrum.smul_eq_smul _ _ (CFC.spectrum_nonempty ℝ _ ((σ₁ i) ⊗ᵣ^[n]).M.H)]
    rw [Real.sInf_smul_of_nonneg (by norm_num)]
    simp [MState.mat_M, div_eq_inv_mul, sInf_spectrum_spacePow]

  have hdpos n : 0 < Fintype.card (spectrum ℝ (σ'' ρ ε m σ n).m) := by
    rw [Fintype.card_pos_iff, Set.nonempty_coe_sort]
    apply IsSelfAdjoint.spectrum_nonempty
    exact (σ'' ρ ε m σ n).M.H

  -- Eq. (S60)
  have qRel_ent_bound n : 𝐃(ρ ⊗ᵣ^[n]‖ℰ n (ρ ⊗ᵣ^[n])) ≤ ENNReal.ofReal (Real.log (n + 1)) := calc
    𝐃(ρ ⊗ᵣ^[n]‖ℰ n (ρ ⊗ᵣ^[n])) ≤ ENNReal.ofReal (Real.log (Fintype.card (spectrum ℝ (σ'' ρ ε m σ n).m))) :=
      qRelativeEnt_op_le (by simp [hdpos n]) (pinching_bound ..)
    _ ≤ ENNReal.ofReal (Real.log (n + 1)) := by
      grw [hdle n]
      · exact_mod_cast le_rfl
      · simp [hdpos n]

  -- Eq. (S61)
  have hliminf : Filter.atTop.liminf (fun n ↦ 𝐃(ρ ⊗ᵣ^[n]‖σ' ρ ε m σ n) / n) =
                 Filter.atTop.liminf (fun n ↦ 𝐃(ℰ n (ρ ⊗ᵣ^[n])‖σ'' ρ ε m σ n) / n) := by
    trans Filter.atTop.liminf fun n ↦ 𝐃(ρ ⊗ᵣ^[n]‖σ'' ρ ε m σ n) / n
    · have hg : Filter.atTop.Tendsto (fun n ↦ ENNReal.ofReal (σ₁_c i n) / n) (𝓝 0) := by
        rw [← ENNReal.tendsto_toReal_iff_of_eventually_ne_top ?_ ENNReal.zero_ne_top]
        · simp [ENNReal.toReal_ofReal (σ₁_c_pos i _).le]
          exact σ₁_c_div_lim i
        · rw [Filter.eventually_atTop]
          use 1
          intros
          finiteness
      apply le_antisymm
      · nth_rw 2 [← ENNReal.liminf_add_of_right_tendsto_zero hg]
        conv =>
          enter [2, 1, n]
          rw [Pi.add_apply, ← ENNReal.add_div]
        apply Filter.liminf_le_liminf (β := ℝ≥0∞)
        rw [Filter.eventually_atTop]
        use 1
        intro n _
        exact ENNReal.div_le_div (qRel_σ'_le_σ'' n) (by rfl)
      -- A copy of the · above with σ' and σ'' swapped
      · nth_rw 2 [← ENNReal.liminf_add_of_right_tendsto_zero hg]
        conv =>
          enter [2, 1, n]
          rw [Pi.add_apply, ← ENNReal.add_div]
        apply Filter.liminf_le_liminf (β := ℝ≥0∞)
        rw [Filter.eventually_atTop]
        use 1
        intro n _
        exact ENNReal.div_le_div (qRel_σ''_le_σ' n) (by rfl)
    · -- Eq (S59) has a minus sign, which gets complicated when one of the relative entropies is infinite.
      -- However, I don't think we need this version with the minus sign.
      have h_pinching := fun n ↦ pinching_pythagoras (ρ ⊗ᵣ^[n]) (σ'' ρ ε m σ n)
      simp only [h_pinching, ENNReal.add_div, ← Pi.add_apply]
      conv_lhs =>
        apply ENNReal.liminf_add_of_left_tendsto_zero
        tactic =>
          apply tendsto_of_tendsto_of_tendsto_of_le_of_le
            (g := (0 : ℕ → ℝ≥0∞)) (h := fun n ↦ ENNReal.ofReal (Real.log (n + 1)) / n)
          · exact tendsto_const_nhds
          ·  -- Basically that lim_n→∞ log n / n = 0
            rw [← Filter.tendsto_sub_atTop_iff_nat 1]
            apply Filter.Tendsto.congr' (f₁ := fun (n : ℕ) ↦ ENNReal.ofReal (Real.log n / (n - 1)))
            · simp only [Filter.EventuallyEq, ← ENNReal.ofReal_natCast, Filter.eventually_atTop]
              use 2; intros b hb
              convert ENNReal.ofReal_div_of_pos (y := b - 1) (by rify at b hb; linarith)
              · norm_cast
                omega
              · norm_cast; symm; apply Int.subNatNat_of_le
                omega
            refine Filter.Tendsto.comp (g := fun r ↦ ENNReal.ofReal (Real.log r / (r - 1)))
              ?_ tendsto_natCast_atTop_atTop
            rw [← ENNReal.ofReal_zero]
            apply ENNReal.tendsto_ofReal
            convert Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 (zero_ne_one.symm) using 3
            · simp
            · ring
          · positivity
          · intro n
            exact ENNReal.div_le_div (qRel_ent_bound n) le_rfl

  use fun n ↦ ⟨σ' ρ ε m σ n, σ'_free ρ ε m σ n⟩
  rw [R2, hliminf]
  exact EquationS62 ρ σ hε'₁ hε'₂ hε.2 hR1R2 hR1 hR2 hε₀ hε₀' m hm

/-- Lemma 7 gives us a way to repeatedly "improve" a sequence σ to one with a smaller gap between R2 and R1.
The paper paints this as pretty much immediate from Lemma7, but we need to handle the case where R2 is below
R1. -/
private noncomputable def Lemma7_improver (ρ : MState (H i)) {ε : Prob} (hε : 0 < ε ∧ ε < 1) {ε' : Prob} (hε' : 0 < ε' ∧ ε' < ε) :
    --The parameters above are the "fixed" parameters that we'll improve
    --It takes one sequence of free states, `(n : ℕ) → IsFree (i := i ^ n)`, and gives a new one
    ((n : ℕ) → IsFree (i := i ^ n)) → ((n : ℕ) → IsFree (i := i ^ n)) :=
  fun σ ↦
    if h : R2 ρ σ ≥ R1 ρ ε then
      (Lemma7 ρ hε σ h ε' hε').choose
    else
     σ --The gap was already 0 (or even, negative!) so leave it unchanged.

/-- The Lemma7_improver does its job at shrinking the gap. -/
theorem Lemma7_gap (ρ : MState (H i)) {ε : Prob} (hε : 0 < ε ∧ ε < 1) {ε' : Prob} (hε' : 0 < ε' ∧ ε' < ε) :
    ∀ σ,
      letI σ' := Lemma7_improver ρ hε hε' σ;
      R2 ρ σ' - R1 ρ ε ≤ .ofNNReal (1 - ε' : Prob) * (R2 ρ σ - R1 ρ ε) := by
  intro σ
  dsimp [SteinsLemma.Lemma7_improver]
  split_ifs with h
  · exact (SteinsLemma.Lemma7 ρ hε σ h ε' hε').choose_spec
  · push_neg at h
    rw [tsub_eq_zero_of_le h.le]
    exact zero_le _

end Lemma7

/-- Theorem 1 in https://arxiv.org/pdf/2408.02722v3 -/
theorem GeneralizedQSteinsLemma {i : ι} (ρ : MState (H i)) {ε : Prob} (hε : 0 < ε ∧ ε < 1) :
    Filter.atTop.Tendsto (fun n ↦ —log β_ ε(ρ ⊗ᵣ^[n]‖IsFree) / n) (𝓝 (𝑅ᵣ∞ ρ)) := by

  --It suffices to show limsup LHS ≤ RHS and liminf LHS ≥ RHS.
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · -- the "key part" of the "opposite inequality".
    --We need to pick an ε' (a \tilde{ε} in the paper). The only constraint(?) is that it's strictly
    --less than ε. We take ε' := ε/2.
     --TODO: Should we have an HDiv Prob Nat instance?
    let ε' : Prob := ⟨ε/2, by constructor <;> linarith [ε.zero_le_coe, ε.coe_le_one]⟩
    have hε' : 0 < ε' ∧ ε' < ε := by constructor <;> change (_ : ℝ) < (_ : ℝ) <;> simpa [ε'] using hε.1

    --Take some initial sequence σ₁. We need to pick it so that `R2 ρ σ₁` is finite, otherwise we can't "shrink"
    --it by applying Lemma 7. Taking the full-rank state of dimension `H i` and taking all powers of it, works.
    have ⟨σ_free, hσ_free⟩ := free_fullRank i
    set σ₁ : (n : ℕ) → IsFree (i := i ^ n) := fun n ↦
      ⟨σ_free  ⊗ᵣ^[n], IsFree.npow hσ_free.2 n⟩ with hσ₁
    have hσ₁_top : R2 ρ σ₁ ≠ ⊤ := by
      rw [R2, ← Filter.liminf_nat_add _ 1]
      simp [σ₁, mul_comm _ (qRelativeEnt _ _)]
      conv =>
        enter [1,1,1,n]
        rw [ENNReal.mul_div_cancel_right (by positivity) (by finiteness)]
      have _ := HermitianMat.nonSingular_of_posDef hσ_free.1
      simp [qRelativeEnt_ne_top]
    clear hσ₁
    --Repeat the Lemma7 improvement process to drive the gap down
    let σₖ : ℕ → (n : ℕ) → IsFree (i := i ^ n) := fun k ↦
      (Lemma7_improver ρ hε hε')^[k] σ₁

    --The gap between R_{1,ε} and R2 for `σₖ k` goes to 0 as `k → ∞`.
    have hσₖ_gap : Filter.atTop.Tendsto (fun k ↦ R2 ρ (σₖ k) - R1 ρ ε) (𝓝 0) := by
      suffices h : ∀ (k : ℕ), R2 ρ (σₖ k) - R1 ρ ε ≤ ↑(1 - ε')^k * (R2 ρ σ₁ - R1 ρ ε) by
        refine tendsto_nhds_bot_mono' ?_ h
        conv =>
          enter [3, 1]
          equals 0 * (R2 ρ σ₁ - R1 ρ ε) => simp
        apply ENNReal.Tendsto.mul_const
        · simp only [ENNReal.tendsto_pow_atTop_nhds_zero_iff]
          --This should just be `simp` or `bound` at this point. TODO.
          simp [Prob.toNNReal, ← NNReal.coe_lt_coe, hε'.1]
        · right; exact ENNReal.sub_ne_top hσ₁_top
      suffices h : ∀ (m k : ℕ), R2 ρ (σₖ (m + k)) - R1 ρ ε ≤ (1 - ε')^k * (R2 ρ (σₖ m) - R1 ρ ε) by
        convert h 0; simp
      intro m k; induction k generalizing m
      · simp [σₖ]
      rename_i k ih
      have σₖ_succ (n) : σₖ (n + 1) = Lemma7_improver ρ hε hε' (σₖ n) :=
        Function.iterate_succ_apply' ..
      rw [← add_assoc, σₖ_succ, pow_succ]
      grw [Lemma7_gap ρ hε hε' (σₖ (m + k)), ih m]
      ring_nf
      rfl

    replace hσₖ_gap : Filter.atTop.liminf (fun k ↦ R2 ρ (σₖ k)) ≤ R1 ρ ε := by
      rw [ENNReal.tendsto_sub_const_nhds_zero_iff] at hσₖ_gap
      grw [Filter.liminf_le_limsup, hσₖ_gap]

    rw [R1] at hσₖ_gap
    grw [← hσₖ_gap]; clear hσₖ_gap

    have hReg := RelativeEntResource.tendsto_ennreal ρ
    replace hReg := hReg.liminf_eq
    rw [← hReg]; clear hReg

    unfold R2
    /- The idea is now that: the LHS is the liminf over all n, of the minimum free σ of dimension n;
      the RHS is the liminf over a particular subsequence, given by σₖ, which is free. But then
      the math is complicated a bit by the fact that the RHS is a _double_ liminf. This is what H&Y
      deal with by talking about the sequences `σ_{n_k, ∗} = σ_{n_k, k}` (below Eq (26)). We don't
      actually construct such a subsequence here, we just unfold the bounds repeatedly.
    -/
    refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
    apply Filter.Eventually.of_forall fun _ ↦ ?_
    refine Filter.liminf_le_liminf ?_
    apply Filter.Eventually.of_forall fun _ ↦ ?_
    gcongr
    rw [iInf_subtype']
    exact iInf_le _ _

  · --the "strong converse" part
    conv =>
      enter [1, 1, n, 1, 1]
      rw [← OptimalHypothesisRate.Lemma3 ε IsCompact_IsFree free_convex]

    --Let σₘ be the state minimizing 𝐃(ρ⊗^m‖σₘ) over free states. This is guaranteed to exist since
    -- (1) the divergence is continuous and (2) the set of free states is compact.
    have σₘ_exists (m : ℕ) := IsCompact_IsFree.exists_isMinOn_lowerSemicontinuousOn
      Set.Nonempty.of_subtype (f := fun σ ↦ 𝐃(ρ ⊗ᵣ^[m]‖σ)) (by fun_prop)

    have hσₘ1 (m) := (σₘ_exists m).choose_spec.left
    have hσₘ2 (m) := (σₘ_exists m).choose_spec.right
    generalize σₘ_def : (fun m ↦ (σₘ_exists m).choose) = σₘ
    simp_rw [congrFun σₘ_def] at hσₘ1 hσₘ2
    clear σₘ_def σₘ_exists

    --Let σ₁ be the full-rank free state
    have ⟨σ₁, hσ₁_pos, hσ₁_free⟩ := FreeStateTheory.free_fullRank i

    --`h` is Eq (14)
    have _ := HermitianMat.nonSingular_of_posDef hσ₁_pos
    have h (m : ℕ) (hm : m ≥ 1) := Lemma6 hm ρ σ₁ (σₘ m) hε.2

    --Update `h` to Eq (15)
    have h₂ (m : ℕ) : (fun n ↦ —log β_ ε(ρ ⊗ᵣ^[n]‖IsFree) / n) ≤ᶠ[Filter.atTop]
        (fun n ↦ —log β_ ε(ρ ⊗ᵣ^[n]‖{(Lemma6_σn m σ₁ (σₘ m)) n}) / n) := by
      rw [Filter.EventuallyLE]
      apply Filter.Eventually.of_forall
      intro n
      gcongr
      apply OptimalHypothesisRate.negLog_le_singleton
      apply Lemma6_σn_IsFree hσ₁_free hσₘ1
    replace h (m) (hm) := (Filter.limsup_le_limsup (h₂ m)).trans (h m hm)
    clear h₂

    --Update `h` to Eq (16)
    conv at h =>
      enter [m, hm, 2, 1]
      exact (IsMinOn.iInf_eq (hσₘ1 m) (hσₘ2 m)).symm

    apply tendsto_le_of_eventuallyLE tendsto_const_nhds (RelativeEntResource.tendsto_ennreal ρ)
    rw [Filter.EventuallyLE, Filter.eventually_atTop]
    use 1
    convert h using 7
    · exact OptimalHypothesisRate.Lemma3 ε IsCompact_IsFree free_convex
    · symm
      apply iInf_subtype''

/-- Theorem 4, which is also called the Generalized quantum Stein's lemma in Hayashi & Yamasaki.
What they state as an equality of limits, which don't exist per se in Mathlib, we state as the existence
of a number (which happens to be `RegularizedRelativeEntResource`) to which both sides converge.
-/
theorem limit_hypotesting_eq_limit_rel_entropy (ρ : MState (H i)) (ε : Prob) (hε : 0 < ε ∧ ε < 1) :
    ∃ d : ℝ≥0,
      Filter.atTop.Tendsto (fun n ↦ —log β_ ε(ρ ⊗ᵣ^[n]‖IsFree) / n) (𝓝 d)
      ∧
      Filter.atTop.Tendsto (fun n ↦ (⨅ σ ∈ IsFree, 𝐃(ρ ⊗ᵣ^[n]‖σ)) / n) (𝓝 d)
      := by
  use 𝑅ᵣ∞ ρ -- Regularized relative entropy of resource (RegularizedRelativeEntResource) as an NNReal
  constructor
  · exact GeneralizedQSteinsLemma ρ hε -- Theorem 1 in Hayashi & Yamasaki
  · exact RelativeEntResource.tendsto_ennreal ρ -- The regularized relative entropy of resource is not infinity
