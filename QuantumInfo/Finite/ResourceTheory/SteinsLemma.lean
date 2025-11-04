/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa, Rodolfo R. Soldati
-/
import QuantumInfo.Finite.ResourceTheory.FreeState
import QuantumInfo.Finite.ResourceTheory.HypothesisTesting
import QuantumInfo.Finite.Pinching
import QuantumInfo.ForMathlib.Matrix

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

namespace SteinsLemma

variable {ι : Type*} [UnitalFreeStateTheory ι]
variable {i : ι}

/-- The \tilde{σ}_n defined in Lemma 6, also in equation (S40) in Lemma 7. -/
noncomputable def Lemma6_σn (m : ℕ) (σf : MState (H i)) (σₘ : MState (H (i ^ m))) : (n : ℕ) → MState (H (i ^ n)) :=
  fun n ↦ (σₘ⊗^S[n / m] ⊗ᵣ σf⊗^S[n % m]).relabel <| .cast <| congrArg H (by
    rw [← pow_mul, ← spacePow_add, Nat.div_add_mod n m]
  )

theorem Lemma6_σn_IsFree {σ₁ : MState (H i)} {σₘ : (m : ℕ) → MState (H (i ^ m))} (hσ₁_free : IsFree σ₁)
    (hσₘ : ∀ (m : ℕ), σₘ m ∈ IsFree) (m n : ℕ) : Lemma6_σn m σ₁ (σₘ m) n ∈ IsFree := by
  rw [Lemma6_σn, relabel_cast_isFree]
  · apply free_prod --pick a better name / alias for this
    · exact (hσₘ m).npow (n / m)
    · exact hσ₁_free.npow (n % m)
  · rw [← pow_mul, ← spacePow_add, Nat.div_add_mod n m]

--PULLOUT.
--PR? This is "not specific to our repo", but might be a bit too specialized to be in Mathlib. Not sure.
--Definitely would need to clean up the proof first
theorem extracted_limsup_inequality (z : ℝ≥0∞) (hz : z ≠ ⊤) (y x : ℕ → ℝ≥0∞) (h_lem5 : ∀ (n : ℕ), x n ≤ y n + z)
    : Filter.atTop.limsup (fun n ↦ x n / n) ≤ Filter.atTop.limsup (fun n ↦ y n / n) := by
  --Thanks Aristotle!
  simp? [Filter.limsup_eq] says simp only [Filter.limsup_eq, Filter.eventually_atTop,
    ge_iff_le, le_sInf_iff, Set.mem_setOf_eq, forall_exists_index]
  -- Taking the limit superior of both sides of the inequality x n / n ≤ y_n / n + z / n, we
  -- get limsup x n / n ≤ limsup (y n / n + z / n).
  intro b n h_bn
  have h_le : ∀ m ≥ n, x m / (m : ℝ≥0∞) ≤ b + z / (m : ℝ≥0∞) := by
    intro m hm
    grw [← h_bn m hm, ← ENNReal.add_div, h_lem5 m]
  -- Since z is finite, we have lim z / n = 0.
  have h_z_div_n_zero : Filter.atTop.Tendsto (fun n : ℕ ↦ z / (n : ℝ≥0∞)) (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    rw [gt_iff_lt, ENNReal.lt_iff_exists_real_btwn] at hε
    rcases hε with ⟨ε', hε₁, hε₂⟩
    rw [ENNReal.ofReal_pos] at hε₂
    -- Since z is finite, we can choose k such that for all b ≥ k, z ≤ b * ε'.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ b ≥ k, z ≤ b * ENNReal.ofReal ε' := by
      rcases ENNReal.lt_iff_exists_real_btwn.mp (show z < ⊤ by finiteness) with ⟨a, _, ha, _⟩
      use ⌈a / ε'⌉₊
      intro n hn
      grw [ha.le, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      gcongr
      nlinarith [Nat.ceil_le.mp hn, mul_div_cancel₀ a hε₂.1.ne']
    -- Since z ≤ b * ε' for all b ≥ k, dividing both sides by b (which is positive) gives z / b ≤ ε'.
    rw [Filter.eventually_atTop]
    use k + 1
    intros b _
    grw [ENNReal.div_le_iff_le_mul (by aesop) (by simp), hk b (by omega), mul_comm, hε₂.right.le]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  rcases Filter.eventually_atTop.mp (h_z_div_n_zero.eventually <| gt_mem_nhds hε) with ⟨m, hm⟩
  apply sInf_le
  use n + m
  intro n hn
  grw [h_le n (by omega), (hm n (by omega)).le]


--PULLOUT and PR
open Filter in
/-- Like `Filter.tendsto_add_atTop_iff_nat`, but with nat subtraction. -/
theorem _root_.Filter.tendsto_sub_atTop_iff_nat {α : Type*} {f : ℕ → α} {l : Filter α} (k : ℕ) :
    Tendsto (fun (n : ℕ) ↦ f (n - k)) atTop l ↔ Tendsto f atTop l :=
  show Tendsto (f ∘ fun n ↦ n - k) atTop l ↔ Tendsto f atTop l by
    rw [← tendsto_map'_iff, map_sub_atTop_eq_nat]

--PULLOUT and PR
open ENNReal Filter in
/-- Sort of dual to `ENNReal.tendsto_const_sub_nhds_zero_iff`. Takes a substantially different form though, since
we don't actually have equality of the limits, or even the fact that the other one converges, which is why we
need to use `limsup`. -/
theorem _root_.ENNReal.tendsto_sub_const_nhds_zero_iff {α : Type*} {l : Filter α} {f : α → ℝ≥0∞} {a : ℝ≥0∞}
    : Tendsto (f · - a) l (𝓝 0) ↔ limsup f l ≤ a := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp [tendsto_const_nhds]
  rw [ENNReal.tendsto_nhds_zero, limsup_le_iff']
  simp only [tsub_le_iff_left]
  constructor
  · intro h y hy
    specialize h (y - a) (tsub_pos_of_lt hy)
    rwa [add_comm, tsub_add_cancel_of_le hy.le] at h
  · intro h ε hε
    exact h (a + ε) (lt_add_right ha hε.ne')

--Didn't end up actually needing this for the proof, but I suppose it's a good fact to have
--all the same. On the 1D Hilbert space, the optimal hypothesis testing rate is simply 1 - ε,
--since there's nothing to learn. (More generally this would hold whenever ρ=σ.)
--PULLOUT to HypothesisTesting.lean
theorem optimalHypothesisRate_unique {d : Type*} [Fintype d] [DecidableEq d]
    (ε : Prob) (ρ σ : MState d) [Unique d] : β_ ε(ρ‖{σ}) = 1 - ε := by
  obtain rfl := Unique.eq_default ρ
  obtain rfl := Unique.eq_default σ
  rw [OptimalHypothesisRate.of_singleton]
  apply le_antisymm
  · refine iInf_le_of_le ⟨((1 - ε : Prob) : ℝ) • 1, ⟨?_, ?_, ?_⟩⟩ ?_
    · simp [MState.exp_val_sub]
    · apply smul_nonneg ?_ zero_le_one
      simp
    · apply smul_le_of_le_one_left zero_le_one
      simp
    · simp [-Prob.coe_one_minus]
  · simp
    intro a ha he1 ha0 ha1
    rw [MState.exp_val_sub, MState.exp_val_one, tsub_le_iff_right] at he1
    rw [← tsub_le_iff_left, ← Prob.coe_one_minus] at he1
    exact he1

/-- Lemma 6 from the paper.
We _did_ end up doing the version that "works also in the case of ε = 0", which is nice.
-/
private theorem Lemma6 {m : ℕ} (hm : 0 < m) (ρ σf : MState (H i)) (σₘ : MState (H (i ^ m)))
    (hσf : σf.m.PosDef) {ε : Prob} (hε : ε < 1) :
  Filter.atTop.limsup (fun n ↦ —log β_ ε(ρ⊗^S[n]‖{Lemma6_σn m σf σₘ n}) / n) ≤ 𝐃(ρ⊗^S[m]‖σₘ) / m
  := by

  set σn := Lemma6_σn m σf σₘ with hσn

  have h_add : ∀ α n, D̃_ α(ρ⊗^S[n]‖σn n) = (n/m : ℕ) * D̃_ α(ρ⊗^S[m]‖σₘ) + (n%m : ℕ) * D̃_ α(ρ‖σf):= by
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
  have h_α : ∀ α, (1 < α) → Filter.atTop.limsup (fun n ↦ —log β_ ε(ρ⊗^S[n]‖{σn n}) / n) ≤
      D̃_ α(ρ⊗^S[m]‖σₘ) / m := by
    intro α hα
    apply le_of_le_of_eq (b := Filter.atTop.limsup (fun n ↦ D̃_ α(ρ⊗^S[n]‖σn n) / n))
    · --Apply the "[81] Lemma 5" to ρ⊗^n and σn
      have h_lem5 (n) := OptimalHypothesisRate.Ref81Lem5 (ρ⊗^S[n]) (σn n) ε hε α hα

      --Upper-bound β on the LHS with this lemma
      --Distribute the limsup over subtraction
      --The term on the right is a constant, divided by n, which converges to zero.
      --Dropping that leaves the identity
      generalize_proofs pf1 pf2 at h_lem5
      let x n :=  —log β_ ε(ρ⊗^S[n]‖{σn n})
      let y n := D̃_ α(ρ⊗^S[n]‖σn n)
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

    · suffices Filter.atTop.Tendsto (fun n ↦ D̃_ α(ρ⊗^S[n]‖σn n) / n)  (𝓝 (D̃_ α(ρ⊗^S[m]‖σₘ) / m))by
        exact this.limsup_eq
      conv =>
        enter [1,n]
        equals ((↑(n / m) * D̃_ α(ρ⊗^S[m]‖σₘ)) / n + (↑(n % m) * D̃_ α(ρ‖σf)) / n) =>
          simp_rw [h_add, ENNReal.add_div]
      conv => enter [3,1]; apply (add_zero _).symm
      apply Filter.Tendsto.add
      · simp_rw [div_eq_mul_inv, mul_comm, ← mul_assoc]
        conv =>
          enter [3,1]
          apply (one_mul _).symm
        rw [← mul_assoc]
        cases D̃_ α(ρ⊗^S[m]‖σₘ)
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
  replace h_α : Filter.atTop.limsup (fun n ↦ —log β_ ε(ρ⊗^S[n]‖{σn n}) / n) ≤ 𝐃(ρ⊗^S[m]‖σₘ) / m := by
    refine ge_of_tendsto (x :=  (𝓝[>] 1)) ?_ (eventually_nhdsWithin_of_forall h_α)
    apply tendsto_nhdsWithin_of_tendsto_nhds
    convert ContinuousAt.tendsto ?_ using 3
    have _ := ENNReal.continuous_div_const m (by positivity)
    have _ := (sandwichedRelRentropy.continuousOn (ρ⊗^S[m]) σₘ).continuousAt (Ioi_mem_nhds zero_lt_one)
    fun_prop

  exact h_α

section Lemma7

open MatrixMap
open Matrix
open PosSemidef

variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut] {R : Type*}

-- TODO: Commutation and order relations about `proj_le` specified in the text
-- between Eqs. (S77) and (S78)

open scoped HermitianMat in
theorem LemmaS2liminf {ε3 : Prob} {ε4 : ℝ≥0} (hε4 : 0 < ε4)
  {d : ℕ → Type*} [∀ n, Fintype (d n)] [∀ n, DecidableEq (d n)] (ρ : (n : ℕ) → MState (d n)) (σ : (n : ℕ) → MState (d n))
  {Rinf : ℝ≥0} (hRinf : Rinf ≥ Filter.atTop.liminf (fun (n : ℕ) ↦ —log β_ ε3(ρ n‖{σ n}) / n))
  :
  (Filter.atTop.liminf (fun (n : ℕ) ↦ {(ρ n).M ≥ₚ (Real.exp (n * (Rinf + ε4))) • (σ n).M}.inner (ρ n)) ≤ 1 - ε3)
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
      rw [HermitianMat.inner_left_sub, HermitianMat.inner_one, MState.tr,
        HermitianMat.inner_comm, tsub_le_iff_right, add_comm, ← tsub_le_iff_right]
      apply le_of_lt
      exact h n hn
    have hβ : ∀ n ≥ n₀, β_ ε3(ρ n‖{σ n}) ≤ Real.exp (-n * (Rinf + ε4)) := fun n hn ↦ by -- Eq (S25)
      open HermitianMat in
      calc
        β_ ε3(ρ n‖{σ n}) ≤ (σ n).exp_val (T n) := by
          have hβ' := OptimalHypothesisRate.singleton_le_exp_val (σ := σ n) (T n) (hT n hn) ⟨proj_le_nonneg _ _, proj_le_le_one _ _⟩
          simp only [Subtype.coe_le_coe.mpr hβ']
        _ <= (T n).inner (Real.exp (-n * (Rinf + ε4)) • (ρ n).M) := by
          rw [← mul_le_mul_iff_right₀ (Real.exp_pos ((n * (Rinf + ε4)))), HermitianMat.inner_smul, neg_mul, Real.exp_neg]
          simp only [isUnit_iff_ne_zero, ne_eq, Real.exp_ne_zero, not_false_eq_true,
            IsUnit.mul_inv_cancel_left]
          rw [MState.exp_val, HermitianMat.inner_comm, ← HermitianMat.inner_smul]
          unfold T
          exact proj_le_inner_le (Real.exp (n * (Rinf + ε4)) • (σ n).M) (ρ n).M
        _ <= Real.exp (-n * (Rinf + ε4)) := by
          simp [HermitianMat.inner_smul]
          rw [mul_comm]
          apply (mul_le_iff_le_one_left (Real.exp_pos (-(n * (Rinf + ε4))))).mpr
          rw [HermitianMat.inner_comm, ← MState.exp_val]
          exact MState.exp_val_le_one (proj_le_le_one _ _) (ρ n)
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
  exact MState.exp_val_nonneg (HermitianMat.proj_le_nonneg (Real.exp (n * (Rinf + ε4)) • (σ n).M) (ρ n).M) (ρ n)

open scoped HermitianMat in
theorem LemmaS2limsup {ε3 : Prob} {ε4 : ℝ≥0} (hε4 : 0 < ε4)
  {d : ℕ → Type*} [∀ n, Fintype (d n)] [∀ n, DecidableEq (d n)] (ρ : (n : ℕ) → MState (d n)) (σ : (n : ℕ) → MState (d n))
  {Rsup : ℝ≥0} (hRsup : Rsup ≥ Filter.atTop.limsup (fun (n : ℕ) ↦ —log β_ ε3(ρ n‖{σ n}) / n))
  :
  (Filter.atTop.limsup (fun (n : ℕ) ↦ {(ρ n).M ≥ₚ (Real.exp (n * (Rsup + ε4))) • (σ n).M}.inner (ρ n)) ≤ 1 - ε3)
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
      rw [HermitianMat.inner_left_sub, HermitianMat.inner_one, MState.tr,
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
        _ <= (T n).inner (Real.exp (-n * (Rsup + ε4)) • (ρ n).M) := by
          rw [← mul_le_mul_iff_right₀ (Real.exp_pos ((n * (Rsup + ε4)))), HermitianMat.inner_smul, neg_mul, Real.exp_neg]
          simp only [isUnit_iff_ne_zero, ne_eq, Real.exp_ne_zero, not_false_eq_true,
            IsUnit.mul_inv_cancel_left]
          rw [MState.exp_val, HermitianMat.inner_comm, ← HermitianMat.inner_smul]
          unfold T
          exact proj_le_inner_le (Real.exp (n * (Rsup + ε4)) • (σ n).M) (ρ n).M
        _ <= Real.exp (-n * (Rsup + ε4)) := by
          simp [HermitianMat.inner_smul]
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
  exact MState.exp_val_nonneg (HermitianMat.proj_le_nonneg (Real.exp (n * (Rsup + ε4)) • (σ n).M) (ρ n).M) (ρ n)

private theorem LemmaS3_helper {ε : Prob} {d : ℕ → Type*} [∀ n, Fintype (d n)] [∀ n, DecidableEq (d n)]
  (ρ σ₁ σ₂ : (n : ℕ) → MState (d n))
  (f : ℕ → ℝ≥0) (hσ : ∀ (i : ℕ), Real.exp (-f i) • (σ₂ i).M ≤ (σ₁ i)) (n : ℕ) :
    —log β_ ε(ρ n‖{σ₁ n}) ≤ —log β_ ε(ρ n‖{σ₂ n}) + f n := by
  have h₁ (T : HermitianMat (d n) ℂ) (hT : 0 ≤ T) :
          Real.exp (-f n) * T.inner (σ₂ n).M ≤ T.inner (σ₁ n).M := by
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
  simp only [MState.exp_val, ← HermitianMat.smul_inner]
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
  Filter.atTop.liminf fun n ↦ —log β_ ε(ρ⊗^S[n]‖IsFree) / n

private noncomputable def R2 (ρ : MState (H i)) : ((n : ℕ) → IsFree (i := i ^ n)) → ℝ≥0∞ :=
  fun σ ↦ Filter.atTop.liminf fun n ↦ 𝐃(ρ⊗^S[n]‖σ n) / n

--Without explicitly giving this instance, Lean times out trying to find it in Lemma 7.
--PULLLOUT to ... HermitianMat/Order.lean?
instance {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜] :
    PosSMulReflectLE ℝ (HermitianMat d 𝕜) :=
  PosSMulMono.toPosSMulReflectLE

open MatrixOrder

--PULLOUT
theorem _root_.Matrix.PosDef.zero_lt {n : Type*} [Nonempty n] [Fintype n] {A : Matrix n n ℂ} (hA : A.PosDef) : 0 < A := by
  apply lt_of_le_of_ne
  · replace hA := hA.posSemidef
    rwa [Matrix.nonneg_iff_posSemidef]
  · rintro rfl
    --wtf do better. TODO
    have : ¬(0 < 0) := by trivial
    classical rw [← Matrix.posDef_natCast_iff (n := n) (R := ℂ)] at this
    revert hA
    convert this
    ext; simp
    trans ((0 : ℕ) : ℂ)
    · simp
    classical
    change _ = ite _ _ _
    simp

theorem _root_.HermitianMat.cfc_le_cfc_of_PosDef {d : Type*} [Fintype d] [DecidableEq d]
  {f g : ℝ → ℝ} (hfg : ∀ i, 0 < i → f i ≤ g i) (A : HermitianMat d ℂ) (hA : A.toMat.PosDef) :
    A.cfc f ≤ A.cfc g := by
  rw [← sub_nonneg, ← HermitianMat.cfc_sub, HermitianMat.zero_le_cfc]
  intro i
  rw [Pi.sub_apply, sub_nonneg]
  rw [A.H.posDef_iff_eigenvalues_pos] at hA
  apply hfg
  apply hA

theorem _root_.Commute.exists_HermitianMat_cfc {d : Type*} [Fintype d] [DecidableEq d]
  (A B : HermitianMat d ℂ) (hAB : Commute A.toMat B.toMat) :
    ∃ C : HermitianMat d ℂ, (∃ f : ℝ → ℝ, A = C.cfc f) ∧ (∃ g : ℝ → ℝ, B = C.cfc g) := by
  obtain ⟨C, ⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ := hAB.exists_cfc A.H B.H
  by_cases hC : C.IsHermitian
  · use ⟨C, hC⟩
    constructor
    · exact ⟨g₁, by simp [HermitianMat.ext_iff, hg₁]⟩
    · exact ⟨g₂, by simp [HermitianMat.ext_iff, hg₂]⟩
  · change ¬(IsSelfAdjoint C) at hC
    rw [cfc_apply_of_not_predicate C hC] at hg₁ hg₂
    use 0
    constructor
    · exact ⟨0, by simp [HermitianMat.ext_iff, hg₁]⟩
    · exact ⟨0, by simp [HermitianMat.ext_iff, hg₂]⟩

theorem _root_.HermitianMat.cfc_commute {d : Type*} [Fintype d] [DecidableEq d]
  (A B : HermitianMat d ℂ) (f g : ℝ → ℝ) (hAB : Commute A.toMat B.toMat) :
    Commute (A.cfc f).toMat (B.cfc g).toMat := by
  obtain ⟨C, ⟨h₁, rfl⟩, ⟨h₂, rfl⟩⟩ := hAB.exists_HermitianMat_cfc
  rw [commute_iff_eq, ← HermitianMat.cfc_comp, ← HermitianMat.cfc_comp, ← HermitianMat.coe_cfc_mul, ← HermitianMat.coe_cfc_mul, mul_comm (f ∘ h₁) (g ∘ h₂)]

theorem _root_.HermitianMat.cfc_self_commute {d : Type*} [Fintype d] [DecidableEq d]
  (A : HermitianMat d ℂ) (f g : ℝ → ℝ) :
    Commute (A.cfc f).toMat (A.cfc g).toMat := by
  rw [commute_iff_eq, ← HermitianMat.coe_cfc_mul, ← HermitianMat.coe_cfc_mul, mul_comm f g]

--PULLOUT to HermitianMat/CFC.lean
/- TODO: Write a version of this that holds more broadly for some sets. Esp closed intervals of reals,
which correspond nicely to closed intervals of matrices. Write the specialization to Set.univ (Monotone
instead of MonotoneOn). Also a version that works for StrictMonoOn. -/
theorem _root_.HermitianMat.cfc_le_cfc_of_commute_monoOn {d : Type*} [Fintype d] [DecidableEq d]
  {f : ℝ → ℝ} (hf : MonotoneOn f (Set.Ioi 0)) {A B : HermitianMat d ℂ} (hAB₁ : Commute A.toMat B.toMat)
  (hAB₂ : A ≤ B) (hA : A.toMat.PosDef) (hB : B.toMat.PosDef) :
    A.cfc f ≤ B.cfc f := by
  obtain ⟨C, ⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩ := hAB₁.exists_HermitianMat_cfc
  -- Need to show that g₁ ≤ g₂ on spectrum ℝ C
  rw [← C.cfc_comp, ← C.cfc_comp]
  rw [← sub_nonneg, ← C.cfc_sub, C.zero_le_cfc] at hAB₂ ⊢
  intro i
  simp only [HermitianMat.val_eq_coe, Pi.sub_apply, Function.comp_apply, sub_nonneg]
  apply hf
  · rw [HermitianMat.cfc_PosDef] at hA
    exact hA i
  · rw [HermitianMat.cfc_PosDef] at hB
    exact hB i
  · simpa using hAB₂ i

/-- TODO: See above -/
theorem _root_.HermitianMat.cfc_le_cfc_of_commute {d : Type*} [Fintype d] [DecidableEq d]
  {f : ℝ → ℝ} (hf : Monotone f) {A B : HermitianMat d ℂ} (hAB₁ : Commute A.toMat B.toMat)
  (hAB₂ : A ≤ B) :
    A.cfc f ≤ B.cfc f := by
  obtain ⟨C, ⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩ := hAB₁.exists_HermitianMat_cfc
  -- Need to show that g₁ ≤ g₂ on spectrum ℝ C
  rw [← C.cfc_comp, ← C.cfc_comp]
  rw [← sub_nonneg, ← C.cfc_sub, C.zero_le_cfc] at hAB₂ ⊢
  intro i
  simp only [HermitianMat.val_eq_coe, Pi.sub_apply, Function.comp_apply, sub_nonneg]
  apply hf
  simpa using hAB₂ i

--This is the more general version that requires operator concave functions but doesn't require the inputs
-- to commute. Requires the correct statement of operator convexity though, which we don't have right now.
proof_wanted _root_.HermitianMat.cfc_monoOn_pos_of_monoOn_posDef {d : Type*} [Fintype d] [DecidableEq d]
  {f : ℝ → ℝ} (hf_is_operator_convex : False) :
    MonotoneOn (HermitianMat.cfc · f) { A : HermitianMat d ℂ | A.toMat.PosDef }

proof_wanted _root_.HermitianMat.log_monoOn_posDef {d : Type*} [Fintype d] [DecidableEq d] :
    MonotoneOn HermitianMat.log { A : HermitianMat d ℂ | A.toMat.PosDef }

/-- Monotonicity of log on commuting operators. -/
theorem _root_.HermitianMat.log_le_log_of_commute {d : Type*} [Fintype d] [DecidableEq d]
  {A B : HermitianMat d ℂ} (hAB₁ : Commute A.toMat B.toMat) (hAB₂ : A ≤ B) (hA : A.toMat.PosDef) :
    A.log ≤ B.log := by
  refine HermitianMat.cfc_le_cfc_of_commute_monoOn ?_ hAB₁ hAB₂ hA ?_
  · exact Real.strictMonoOn_log.monotoneOn
  · --The fact that `A ≤ B` and `A.PosDef` implies `B.PosDef`. Should be a theorem, TODO
    -- This almost works but not quite:
    -- rw [← Matrix.isStrictlyPositive_iff_posDef] at hA ⊢
    -- exact hA.of_le hAB₂
    simpa using Matrix.PosDef.add_posSemidef hA hAB₂ --ew. abuse

@[simp]
theorem Real.log_comp_exp : Real.log ∘ Real.exp = _root_.id := by
  ext
  simp

/-- Monotonicity of exp on commuting operators. -/
theorem _root_.HermitianMat.exp_le_exp_of_commute {d : Type*} [Fintype d] [DecidableEq d]
  {A B : HermitianMat d ℂ} (hAB₁ : Commute A.toMat B.toMat) (hAB₂ : A.cfc Real.exp ≤ B.cfc Real.exp) :
    A ≤ B := by
  have hA : A = (A.cfc Real.exp).cfc Real.log := by simp [← HermitianMat.cfc_comp]
  have hB : B = (B.cfc Real.exp).cfc Real.log := by simp [← HermitianMat.cfc_comp]
  rw [hA, hB]
  apply HermitianMat.log_le_log_of_commute
  · sorry--apply HermitianMat.cfc_commute --Need the version for two commuting matrices
  · exact hAB₂
  · rw [HermitianMat.cfc_PosDef]
    intro
    positivity


open scoped HermitianMat

section proj_le

variable {d : Type*} [Fintype d] [DecidableEq d] (A B : HermitianMat d ℂ)

theorem _root_.HermitianMat.proj_lt_mul_nonneg : 0 ≤ {A <ₚ B}.toMat * (B - A).toMat := by
  rw [HermitianMat.proj_lt]
  nth_rewrite 2 [← HermitianMat.cfc_id (B - A)]
  rw [← HermitianMat.coe_cfc_mul]
  apply cfc_nonneg
  intros
  simp only [Pi.mul_apply, id_eq, ite_mul, one_mul, zero_mul]
  split <;> order

theorem _root_.HermitianMat.proj_lt_mul_lt : {A <ₚ B}.toMat * A.toMat ≤ {A <ₚ B}.toMat * B.toMat := by
  rw [← sub_nonneg, ← mul_sub_left_distrib]
  exact A.proj_lt_mul_nonneg B

theorem _root_.HermitianMat.one_sub_proj_le : 1 - {B ≤ₚ A} = {A <ₚ B} := by
  rw [sub_eq_iff_eq_add, HermitianMat.proj_le_add_lt]

noncomputable abbrev HermitianMat.mul_commute {A B : HermitianMat d ℂ} (hAB : Commute A.toMat B.toMat) :
    HermitianMat d ℂ :=
  ⟨A.toMat * B.toMat, (A.H.commute_iff B.H).mp hAB⟩

private lemma commute_aux (n : ℕ) {x : ℝ}
  {E ℰ σ : HermitianMat d ℂ} (hℰσ : Commute ℰ.toMat σ.toMat)
  (hE : E = 1 - {Real.exp (n * x) • σ ≤ₚ ℰ})
    : Commute ((1 / n : ℝ) • E).toMat (ℰ.log - σ.log).toMat := by
  rw [HermitianMat.one_sub_proj_le] at hE
  obtain ⟨C, ⟨f, rfl⟩, ⟨g, rfl⟩⟩ := hℰσ.exists_HermitianMat_cfc
  rw [HermitianMat.log, HermitianMat.log]
  rw [← HermitianMat.cfc_comp, ← HermitianMat.cfc_comp, ← HermitianMat.cfc_sub]
  rw [HermitianMat.proj_lt_def, ← HermitianMat.cfc_const_mul] at hE
  rw [← HermitianMat.cfc_sub, ← HermitianMat.cfc_comp] at hE
  subst E
  rw [← HermitianMat.cfc_const_mul]
  apply HermitianMat.cfc_self_commute

private lemma rexp_mul_smul_proj_lt_mul_sub_le_mul_sub {n : ℕ} {x : ℝ}
  {E ℰ σ : HermitianMat d ℂ} (hℰσ : Commute ℰ.toMat σ.toMat) (hx : 0 < x)
  (hℰ : ℰ.toMat.PosSemidef) (hσ : σ.toMat.PosDef)
  (hE : E = 1 - {Real.exp (n * x) • σ ≤ₚ ℰ})
    : ℰ.inner (HermitianMat.mul_commute (commute_aux n hℰσ hE)) ≤ ℰ.inner (x • E) := by
  rw [HermitianMat.inner_eq_re_trace, HermitianMat.inner_eq_re_trace]
  rcases n.eq_zero_or_pos with rfl | hn
  · have hE' : 0 ≤ E.toMat := by
      rw [hE, HermitianMat.one_sub_proj_le]
      apply HermitianMat.proj_lt_nonneg
    have hℰ : 0 ≤ ℰ := by rwa [HermitianMat.zero_le_iff]
    replace hℰ : 0 ≤ ℰ.inner E := HermitianMat.inner_ge_zero hℰ hE'
    simp [-RCLike.re_to_complex]
    rw [← HermitianMat.inner_eq_re_trace]
    positivity
  dsimp [HermitianMat.mul_commute, HermitianMat.toMat]
  repeat rw [HermitianMat.val_eq_coe]
  gcongr
  apply Matrix.PosSemidef.trace_mono
  rw [one_div, smul_mul_assoc, mul_smul_comm, inv_smul_le_iff_of_pos (by positivity)]
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
  change _ * (E.toMat * HermitianMat.toMat (_ - _)) ≤ _
  rw [← HermitianMat.cfc_sub]
  subst E
  rw [← HermitianMat.coe_cfc_mul, ← HermitianMat.coe_cfc_mul]
  rw [← HermitianMat.coe_cfc_mul]
  change _ ≤ HermitianMat.toMat ((n * x) • C.cfc _)
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
    suffices Real.log fi < n * x + Real.log gi by nlinarith
    rw [← Real.log_exp (n * x), ← Real.log_mul (by positivity) (by positivity)]
    apply Real.strictMonoOn_log hfi₂ ?_ h
    change 0 < Real.exp (n * x) * gi
    positivity

private lemma rexp_mul_smul_proj_lt_mul_sub_le_mul_sub' {n : ℕ} {x : ℝ} {y : ℝ}
  {E ℰ σ : HermitianMat d ℂ} (hℰσ : Commute ℰ.toMat σ.toMat)
  (hℰ : ℰ.toMat.PosSemidef) (hσ : σ.toMat.PosDef)
  (hE : E = {Real.exp (n * y) • σ ≤ₚ ℰ} - {Real.exp (n * x) • σ ≤ₚ ℰ})
    : (1 / n : ℝ) • E.toMat * (ℰ.log.toMat - σ.log.toMat) ≤ x • E := by
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
    · change HermitianMat.toMat ((1 / (n : ℝ)) • _)
    · change HermitianMat.toMat (_ - _)
  change _ ≤ HermitianMat.toMat (x • C.cfc _)
  rw [← HermitianMat.cfc_sub, ← HermitianMat.cfc_const_mul, ← HermitianMat.coe_cfc_mul]
  rw [← HermitianMat.cfc_const_mul, ← sub_nonneg]
  change 0 ≤ HermitianMat.toMat (_ - _)
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

lemma _root_.Matrix.card_spectrum_eq_image {d : Type*} [Fintype d] [DecidableEq d] (A : Matrix d d ℂ)
  (hA : A.IsHermitian) [Fintype (spectrum ℝ A)] :
    Fintype.card (spectrum ℝ A) = (Finset.univ.image hA.eigenvalues).card := by
  trans (Set.univ.image hA.eigenvalues).toFinset.card
  · symm
    convert Set.toFinset_card _
    rw [Set.image_univ]
    exact Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues hA
  · simp

/- (∀ x, x > 0 → liminf (n ↦ f x n) ≤ y) →
  ∃ g : ℕ → ℝ, (∀ x, g x > 0) ∧ (liminf g = 0) ∧ (liminf (n ↦ f (g n) n) ≤ y) -/
lemma exists_liminf_zero_of_forall_liminf_le (y : ℝ≥0) (f : ℝ≥0 → ℕ → ℝ≥0∞)
  (hf : ∀ x > 0, Filter.atTop.liminf (f x) ≤ y) :
    ∃ g : ℕ → ℝ≥0, (∀ x, g x > 0) ∧ Filter.atTop.Tendsto g (𝓝 0) ∧
      Filter.atTop.liminf (fun n ↦ f (g n) n) ≤ y := by
  conv at hf =>
    enter [x, h]
    exact propext (Filter.liminf_le_iff (by isBoundedDefault) (by isBoundedDefault))
  replace hf x hx z hz := Filter.exists_seq_forall_of_frequently (hf x hx z hz)
  choose! c hc hc₂ using hf
  classical
  sorry

/- Version of `exists_liminf_zero_of_forall_liminf_le` that lets you also require `g`
to have an upper bound. -/
lemma exists_liminf_zero_of_forall_liminf_le_with_UB (y : ℝ≥0) (f : ℝ≥0 → ℕ → ℝ≥0∞)
  {z : ℝ≥0} (hz : 0 < z)
  (hf : ∀ x, x > 0 → Filter.atTop.liminf (f x) ≤ y) :
    ∃ g : ℕ → ℝ≥0, (∀ x, g x > 0) ∧ (∀ x, g x < z) ∧ (Filter.atTop.Tendsto g (𝓝 0)) ∧
      (Filter.atTop.liminf (fun n ↦ f (g n) n) ≤ y) := by
  obtain ⟨g, hg₀, hg₁, hg₂⟩ := exists_liminf_zero_of_forall_liminf_le y (fun x n => f x n) hf;
  refine ⟨fun n => min (g n) (z / 2), by bound, by bound, ?_, ?_⟩
  · convert hg₁.min tendsto_const_nhds using 2
    simp
  · beta_reduce
    rwa [Filter.liminf_congr]
    have h := hg₁.eventually (gt_mem_nhds <| half_pos hz)
    peel h with h
    rw [min_eq_left h.le]

/- (∀ x, x > 0 → liminf (n ↦ f x n) ≤ y) →
  ∃ g : ℕ → ℝ, (∀ x, g x > 0) ∧ (liminf g = 0) ∧ (liminf (n ↦ f (g n) n) ≤ y) -/
lemma exists_limsup_zero_of_forall_limsup_le (y : ℝ≥0) (f : ℝ≥0 → ℕ → ℝ≥0∞)
  (hf : ∀ x, x > 0 → Filter.atTop.limsup (f x) ≤ y) :
    ∃ g : ℕ → ℝ≥0, (∀ x, g x > 0) ∧ (Filter.atTop.Tendsto g (𝓝 0)) ∧
      (Filter.atTop.limsup (fun n ↦ f (g n) n) ≤ y) := by
  sorry

/- Version of `exists_liminf_zero_of_forall_liminf_le_with_UB` that lets you stipulate it for
two different functions simultaneously, one with liminf and one with limsup. -/
lemma exists_liminf_zero_of_forall_liminf_limsup_le_with_UB (y₁ y₂ : ℝ≥0) (f₁ f₂ : ℝ≥0 → ℕ → ℝ≥0∞)
  {z : ℝ≥0} (hz : 0 < z)
  (hf₁ : ∀ x > 0, Filter.atTop.liminf (f₁ x) ≤ y₁)
  (hf₂ : ∀ x > 0, Filter.atTop.limsup (f₂ x) ≤ y₂) :
    ∃ g : ℕ → ℝ≥0, (∀ x, g x > 0) ∧ (∀ x, g x < z) ∧
      Filter.atTop.Tendsto g (𝓝 0) ∧
      Filter.atTop.liminf (fun n ↦ f₁ (g n) n) ≤ y₁ ∧
      Filter.atTop.limsup (fun n ↦ f₂ (g n) n) ≤ y₂ := by
  sorry

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

set_option maxHeartbeats 200000 in
lemma sub_iInf_eignevalues {d : Type*} [Fintype d] [DecidableEq d] {A : Matrix d d ℂ}
  (hA : A.IsHermitian) :
    (A - iInf hA.eigenvalues • 1).PosSemidef := by
  constructor;
  · simpa [ Matrix.IsHermitian, sub_eq_add_neg ] using hA
  · intro x
    have h_eigenvalue : ∀ i, hA.eigenvalues i ≥ iInf hA.eigenvalues := by
      -- By definition of infimum, for any eigenvalue $i$, we have $hA.eigenvalues i \geq iInf hA.eigenvalues$.
      intros i
      apply le_of_forall_le
      intro j a
      exact le_trans a (ciInf_le ( Finite.bddBelow_range hA.eigenvalues ) i );
    -- Since $A$ is Hermitian, we can diagonalize it as $A = Q \Lambda Q^*$, where $Q$ is unitary and $\Lambda$ is diagonal with the eigenvalues on the diagonal.
    obtain ⟨Q, Λ, hQ, hΛ⟩ : ∃ Q : Matrix d d ℂ, ∃ Λ : d → ℂ, Q.conjTranspose * Q = 1 ∧ A = Q * Matrix.diagonal Λ * Q.conjTranspose ∧ ∀ i, Λ i = Matrix.IsHermitian.eigenvalues hA i := by
      have := hA.spectral_theorem;
      refine' ⟨ _, _, _, this, _ ⟩;
      · simp [ ← Matrix.ext_iff ];
        intro i j; erw [ Matrix.mul_apply ] ; simp [ Matrix.one_apply ] ;
        have := hA.eigenvectorBasis.orthonormal;
        rw [ orthonormal_iff_ite ] at this;
        rw [← this i j]
        simp [PiLp.inner_apply, mul_comm]
      · simp
    -- Since $Q$ is unitary, we have $Q^* Q = I$, and thus $Q^* (A - \lambda_{\min} I) Q = \Lambda - \lambda_{\min} I$.
    have h_diag : Q.conjTranspose * (A - (iInf (Matrix.IsHermitian.eigenvalues hA)) • 1) * Q = Matrix.diagonal (fun i => Λ i - (iInf (Matrix.IsHermitian.eigenvalues hA))) := by
      simp [ hΛ, mul_sub, sub_mul, mul_assoc, hQ ];
      simp [ ← mul_assoc, hQ];
      ext i j ; by_cases hij : i = j <;> aesop;
    -- Since $Q$ is unitary, we have $Q^* (A - \lambda_{\min} I) Q = \Lambda - \lambda_{\min} I$, and thus $x^* (A - \lambda_{\min} I) x = (Q^* x)^* (\Lambda - \lambda_{\min} I) (Q^* x)$.
    have h_quad_form : Star.star x ⬝ᵥ (A - (iInf (Matrix.IsHermitian.eigenvalues hA)) • 1).mulVec x = Star.star (Q.conjTranspose.mulVec x) ⬝ᵥ (Matrix.diagonal (fun i => Λ i - (iInf (Matrix.IsHermitian.eigenvalues hA)))).mulVec (Q.conjTranspose.mulVec x) := by
      rw [ ← h_diag ];
      simp [ Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.mul_eq_one_comm.mp hQ];
      simp only [mulVec_conjTranspose, star_star, vecMul_vecMul];
      rw [ ← Matrix.mul_assoc, Matrix.mul_eq_one_comm.mp hQ, one_mul ];
    simp_all only [ge_iff_le, dotProduct, Pi.star_apply, RCLike.star_def, mulVec, sub_apply,
      smul_apply, Complex.real_smul, conjTranspose_apply, star_sum, star_mul',
      RingHomCompTriple.comp_apply, RingHom.id_apply];
    simp_all only [implies_true, and_self, diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, ↓reduceIte];
    -- Since the eigenvalues are real and the sums involving Q and x are complex, the product of a complex number and its conjugate is non-negative.
    have h_nonneg : ∀ i, 0 ≤ (∑ x_2, Q x_2 i * star (x x_2)) * (∑ x_2, star (Q x_2 i) * x x_2) := by
      intro i
      have h_nonneg : 0 ≤ (∑ x_2, Q x_2 i * star (x x_2)) * star (∑ x_2, Q x_2 i * star (x x_2)) := by
        exact mul_star_self_nonneg (∑ x_2, Q x_2 i * star (x x_2))
      convert h_nonneg using 1;
      simp [ mul_comm, Finset.mul_sum _ _ _];
    -- Since each term in the sum is a product of a non-negative number and a non-negative eigenvalue difference, the entire sum is non-negative.
    have h_sum_nonneg : ∀ i, 0 ≤ (∑ x_2, Q x_2 i * star (x x_2)) * (((↑(hA.eigenvalues i) : ℂ) - (↑(iInf hA.eigenvalues) : ℂ)) * ∑ x_2, star (Q x_2 i) * x x_2) := by
      intro i
      specialize h_nonneg i
      simp_all only [mul_assoc, mul_comm, mul_left_comm, RCLike.star_def] ;
      rw [ ← mul_assoc ];
      exact mul_nonneg h_nonneg ( sub_nonneg_of_le <| mod_cast h_eigenvalue i );
    convert Finset.sum_nonneg fun i _ => h_sum_nonneg i;
    rw [ hΛ.1 ]

lemma iInf_eigenvalues_le_dotProduct_mulVec {d : Type*} [Fintype d] [DecidableEq d] {A : Matrix d d ℂ}
  (hA : A.IsHermitian) (v : d → ℂ) :
    iInf hA.eigenvalues * (star v ⬝ᵥ v) ≤ star v ⬝ᵥ A *ᵥ v := by
  conv_lhs =>
    equals (star v ⬝ᵥ (iInf hA.eigenvalues • 1) *ᵥ v) =>
      simp only [dotProduct, Pi.star_apply, RCLike.star_def, mul_comm, mulVec]
      simp [Matrix.one_apply, mul_assoc, mul_left_comm, Finset.mul_sum]
  rw [← sub_nonneg, ← dotProduct_sub, ← Matrix.sub_mulVec]
  exact (sub_iInf_eignevalues hA).right v

lemma iInf_eigenvalues_le_of_posSemidef {d : Type*} [Fintype d] [DecidableEq d] {A B : Matrix d d ℂ}
  (hAB : (B - A).PosSemidef) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    iInf hA.eigenvalues ≤ iInf hB.eigenvalues := by
  rcases isEmpty_or_nonempty d
  · simp
  contrapose! hAB
  rw [PosSemidef]
  push_neg
  intro _
  apply exists_lt_of_ciInf_lt at hAB
  rcases hAB with ⟨i, hi⟩
  use WithLp.ofLp (hB.eigenvectorBasis i)
  simp only [sub_mulVec, dotProduct_sub, sub_nonneg]
  rw [hB.mulVec_eigenvectorBasis i]
  simp only [dotProduct_smul, Complex.real_smul]
  nth_rw 2 [dotProduct_comm]
  rw [← EuclideanSpace.inner_eq_star_dotProduct]
  intro h
  replace h := (iInf_eigenvalues_le_dotProduct_mulVec hA _).trans h
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct] at h
  simp only [OrthonormalBasis.inner_eq_one, mul_one, Complex.real_le_real] at h
  order

lemma iInf_eigenvalues_le {d : Type*} [Fintype d] [DecidableEq d] {A B : Matrix d d ℂ}
  (hAB : A ≤ B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    iInf hA.eigenvalues ≤ iInf hB.eigenvalues :=
  iInf_eigenvalues_le_of_posSemidef hAB hA hB

@[simp]
theorem _root_.MState.spectrum_relabel {d d₂ : Type*}
  [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]
  {ρ : MState d} (e : d₂ ≃ d) :
    spectrum ℝ (ρ.relabel e).m = spectrum ℝ ρ.m := by
  ext1 v
  rw [spectrum.mem_iff] --TODO make a plain `Matrix` version of this
  rw [Algebra.algebraMap_eq_smul_one v]
  rw [MState.relabel_m, ← Matrix.submatrix_one_equiv e]
  rw [← smul_apply, ← Matrix.submatrix_smul]
  rw [← sub_apply, ← Matrix.submatrix_sub]
  rw [Matrix.isUnit_submatrix_equiv]
  rw [← Algebra.algebraMap_eq_smul_one v, ← spectrum.mem_iff]

open scoped HermitianMat in
open scoped Pointwise in
theorem HermitianMat.spectrum_prod {d d₂ : Type*}
  [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]
  {A : HermitianMat d ℂ} {B : HermitianMat d₂ ℂ} :
    spectrum ℝ (A ⊗ₖ B).toMat = spectrum ℝ A.toMat * spectrum ℝ B.toMat :=
  Matrix.spectrum_prod A.H B.H

--PULLOUT: Belongs in Mathlib/Algebra/Order/Group/Pointwise/CompleteLattice.lean
-- (after appropriately generalizing to MulPosMono)
open scoped Pointwise in
theorem csInf_mul_nonneg {s t : Set ℝ}
  (hs₀ : s.Nonempty) (hs₁ : ∀ x ∈ s, 0 ≤ x) (ht₀ : t.Nonempty) (ht₁ : ∀ x ∈ t, 0 ≤ x) :
    sInf (s * t) = sInf s * sInf t := by
  --TODO Cleanup
  have h_ge : sInf (s * t) ≥ sInf s * sInf t := by
    have h_lower_bound : ∀ x ∈ s, ∀ y ∈ t, x * y ≥ (sInf s) * (sInf t) := by
      intro x a y a_1
      gcongr
      · apply Real.sInf_nonneg; intro x hx; exact ht₁ x hx;
      · exact hs₁ x a;
      · exact csInf_le ⟨ 0, fun z hz => hs₁ z hz ⟩ a;
      · exact csInf_le ⟨ 0, fun z hz => ht₁ z hz ⟩ a_1;
    have h_inf_le : ∀ z ∈ s * t, z ≥ (sInf s) * (sInf t) := by
      rintro _ ⟨ x, hx, y, hy, rfl ⟩ ; exact h_lower_bound x hx y hy;
    exact le_csInf ( Set.Nonempty.mul hs₀ ht₀ ) h_inf_le
  have h_le : sInf (s * t) ≤ sInf s * sInf t := by
    set a := sInf s
    set b := sInf t
    have h_eps : ∀ ε > 0, ∃ x ∈ s, x < a + ε ∧ ∃ y ∈ t, y < b + ε := by
      exact fun ε ε_pos => by rcases exists_lt_of_csInf_lt ( hs₀ ) ( lt_add_of_pos_right a ε_pos ) with ⟨ x, hx₁, hx₂ ⟩ ; rcases exists_lt_of_csInf_lt ( ht₀ ) ( lt_add_of_pos_right b ε_pos ) with ⟨ y, hy₁, hy₂ ⟩ ; exact ⟨ x, hx₁, hx₂, y, hy₁, hy₂ ⟩ ;
    have h_prod_eps : ∀ ε > 0, ∃ x ∈ s, ∃ y ∈ t, x * y < (a + ε) * (b + ε) := by
      exact fun ε hε => by obtain ⟨ x, hx₁, hx₂, y, hy₁, hy₂ ⟩ := h_eps ε hε; exact ⟨ x, hx₁, y, hy₁, by nlinarith [ hs₁ x hx₁, ht₁ y hy₁ ] ⟩ ;
    have h_lim : Filter.Tendsto (fun ε => (a + ε) * (b + ε)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (a * b)) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) );
    refine' le_of_tendsto_of_tendsto tendsto_const_nhds h_lim _;
    filter_upwards [ self_mem_nhdsWithin ] with ε hε using le_trans ( csInf_le ⟨ 0, by rintro x ⟨ u, hu, v, hv, rfl ⟩ ; exact mul_nonneg ( hs₁ u hu ) ( ht₁ v hv ) ⟩ ⟨ _, h_prod_eps ε hε |> Classical.choose_spec |> And.left, _, h_prod_eps ε hε |> Classical.choose_spec |> And.right |> Classical.choose_spec |> And.left, rfl ⟩ ) ( h_prod_eps ε hε |> Classical.choose_spec |> And.right |> Classical.choose_spec |> And.right |> le_of_lt )
  exact le_antisymm h_le h_ge

theorem sInf_spectrum_prod {d d₂ : Type*}
  [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]
  {ρ : MState d} {σ : MState d₂} :
    sInf (spectrum ℝ (ρ ⊗ σ).m) = sInf (spectrum ℝ ρ.m) * sInf (spectrum ℝ σ.m) := by
  rcases isEmpty_or_nonempty d with _ | _; · simp
  rcases isEmpty_or_nonempty d₂ with _ | _; · simp
  rw [MState.m, MState.prod, HermitianMat.spectrum_prod, ← MState.m, ← MState.m]
  rw [csInf_mul_nonneg]
  · exact IsSelfAdjoint.spectrum_nonempty ρ.M.H
  · rw [MState.m, ρ.M.H.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    apply ρ.eigenvalue_nonneg
  · exact IsSelfAdjoint.spectrum_nonempty σ.M.H
  · rw [MState.m, σ.M.H.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    apply σ.eigenvalue_nonneg

theorem sInf_spectrum_rprod {j : ι} {ρ : MState (H i)} {σ : MState (H j)} :
    sInf (spectrum ℝ (ρ ⊗ᵣ σ).m) = sInf (spectrum ℝ ρ.m) * sInf (spectrum ℝ σ.m) := by
  rw [← sInf_spectrum_prod, prodRelabel, MState.spectrum_relabel]

lemma sInf_spectrum_spacePow (σ : MState (H i)) (n : ℕ) :
    sInf (spectrum ℝ (σ⊗^S[n]).m) = sInf (spectrum ℝ σ.m) ^ n := by
  induction n
  · simp only [statePow_zero, pow_zero]
    conv =>
      enter [1, 1, 2]
      equals 1 =>
        change MState.uniform.m = 1 --TODO simp
        ext i j
        simp [MState.uniform, MState.ofClassical, MState.m, HermitianMat.diagonal]
        rfl
    rw [spectrum.one_eq, csInf_singleton]
  · rename_i n ih
    rw [statePow_succ, sInf_spectrum_rprod, ih, pow_succ]

lemma iInf_eigenvalues_smul_one_le {d : Type*} [Fintype d] [DecidableEq d] {A : Matrix d d ℂ}
  (hA : A.IsHermitian) : iInf hA.eigenvalues • 1 ≤ A :=
  (Matrix.PosSemidef.smul_one_le_of_eigenvalues_iff hA (iInf hA.eigenvalues)).mp (ciInf_le (Finite.bddBelow_range _))

private lemma c_identity {mineig : ℝ} (h_mineig : 0 < mineig) {n : ℕ} (hn : 0 < n):
  let c : ℕ → ℝ := fun n ↦ Real.log (1 / mineig) + Real.log 3 / (max n 1);
    (Real.exp (-c n) * (1 / 3) * mineig ^ n) = Real.exp (-↑n * (c n + c n / ↑n)) := by
  have h (x : ℝ) : n * (x / n) = x := by field_simp
  simp only [neg_mul, show ((max n 1 : ℕ) : ℝ) = n from mod_cast (max_eq_left hn)]
  simp only [Real.exp_add, mul_add, neg_add_rev, mul_assoc, h]
  simp [Real.exp_neg, Real.exp_log, Real.exp_log h_mineig, Real.exp_nat_mul]

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

protected lemma _root_.ENNReal.bdd_le_mul_tendsto_zero
  {α : Type u_2} {l : Filter α} {f g : α → ℝ≥0∞} {b : ℝ≥0∞}
  (hb : b ≠ ⊤) (hf : Filter.Tendsto f l (nhds 0))
  (hg : ∀ᶠ (x : α) in l, g x ≤ b) :
    Filter.Tendsto (fun x => f x * g x) l (nhds 0) := by
  rw [ ENNReal.tendsto_nhds_zero ] at *;
  intro ε hεpos
  by_cases hb_pos : 0 < b;
  · have := hf ( ε := ε / b ) (by simp [hb, hεpos.ne'])
    simp_all only [ne_eq, gt_iff_lt]
    filter_upwards [ this, hg ] with x hx₁ hx₂ using le_trans ( mul_le_mul' hx₁ hx₂ ) ( by rw [ ENNReal.div_mul_cancel ] <;> aesop );
  · simp_all only [ne_eq, gt_iff_lt, not_lt, nonpos_iff_eq_zero, ENNReal.zero_ne_top, not_false_eq_true]
    subst hb_pos
    filter_upwards [ hg ] with x hx
    simp [hx]

set_option maxHeartbeats 600000 in
/-- Lemma 7 from the paper. We write `ε'` for their `\tilde{ε}`. -/
private theorem Lemma7 (ρ : MState (H i)) {ε : Prob} (hε : 0 < ε ∧ ε < 1) (σ : (n : ℕ) → IsFree (i := i ^ n)) :
    (R2 ρ σ ≥ R1 ρ ε) →
    ∀ ε' : Prob, (hε' : 0 < ε' ∧ ε' < ε) → -- ε' is written as \tilde{ε} in the paper.
    ∃ σ' : (n : ℕ) → IsFree (i := i ^ n),
    R2 ρ σ' - R1 ρ ε ≤ .ofNNReal (1 - ε' : Prob) * (R2 ρ σ - R1 ρ ε)
    := by
  --This proof naturally splits out into LemmaS62:
  --  `lim inf n→∞ 1/n D(E_n(ρ^⊗n)‖σ''_n) − R1,ϵ ≤ (1 − ˜ϵ)(R2 − R1,ϵ).`
  --This is proved in appendix C.
  --Then we prove S61, and the conclusion is just `rw [S61] at S62`. But splitting it like
  --this requires first _defining_ the sequence σ''_n.

  --First deal with the easy case of R1 = R2.
  intro hR1R2 ε' ⟨hε'₁, hε'₂⟩
  rw [ge_iff_le, le_iff_lt_or_eq, or_comm] at hR1R2
  rcases hR1R2 with hR1R2|hR1R2
  · rw [hR1R2]
    use σ
    simp
  --This leaves us with the stronger statement that R1 < R2 strictly.
  --Before proceeding, let's reduce to the case that they're finite.
  have hR1 : R1 ρ ε ≠ ⊤ := hR1R2.ne_top
  rcases eq_or_ne (R2 ρ σ) ⊤ with hR2|hR2
  · rw [hR2, ENNReal.top_sub hR1, ENNReal.mul_top', if_neg]
    · simp
    · have : ε'.val < 1 := hε'₂.trans hε.2
      rcases ε' with ⟨ε',hε'₁,hε'₂⟩
      simp only [Prob.toNNReal, Prob.coe_one_minus, ENNReal.coe_eq_zero]
      rw [Subtype.ext_iff, val_eq_coe, val_eq_coe, coe_zero, coe_mk]
      linarith +splitNe

  --Start giving the definitions from the paper. Define ε₀
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

  --Define σ₁
  obtain ⟨σ₁, hσ₁_pos, hσ₁_free⟩ := FreeStateTheory.free_fullRank i

  -- Define σ̃ₙ in terms of σₘ
  let «σ̃» (n) := Lemma6_σn m σ₁ (σ m) n
  have «σ̃_free» (n) : IsFree («σ̃» (n)) := Lemma6_σn_IsFree hσ₁_free (fun n ↦ (σ n).2) m n

  --Define σ⋆
  have σ_max_exists (n : ℕ) := IsCompact_IsFree.exists_isMaxOn Set.Nonempty.of_subtype
      (f := fun σ ↦ β_ ε(ρ⊗^S[n]‖{σ})) (hf := Continuous.continuousOn (by fun_prop))
  let «σ⋆» (n) := Classical.choose (σ_max_exists n)
  have «σ⋆_free» (n) : IsFree («σ⋆» n) := (σ_max_exists n).choose_spec.left
  have «σ⋆_max» (n) : IsMaxOn _ IsFree («σ⋆» n) := (σ_max_exists n).choose_spec.right

  --Finally define σ' as an even mixture of σ̃, σ⋆, and σ_full.
  --TODO: would be nice to write a `Mixable` thing for mixing `k` things according to a distribution,
  -- in this case `Distribution.uniform (Fin 3)`.
  let σ' := fun n ↦ ⟨2/3, by norm_num⟩ [⟨1/2, by norm_num⟩ [«σ̃» n ↔ «σ⋆» n] ↔ σ₁⊗^S[n]]
  have σ'_free (n) : IsFree (σ' n) := by
    --by convexity of `IsFree` and that the three constituents are free
    unfold σ'
    apply IsFree.mix
    · exact («σ̃_free» n).mix («σ⋆_free» n) _
    · exact hσ₁_free.npow n
  have σ'_posdef (n) : (σ' n).m.PosDef := by
    --because σ₁ is PosDef, so is σ₁⊗^[n], and so is any convex mixture.
    unfold σ'
    apply MState.PosDef_mix_of_ne_one
    · apply UnitalPretheory.PosDef.npow hσ₁_pos
    · norm_num [← Prob.ne_iff]

  --Clean up the goal... a bit... still a mess!
  clear «σ̃_free» «σ⋆_max» «σ⋆_free»

  -- λ_full, the minimum eigenvalue of σ_full
  let mineig := ⨅ i, σ₁.M.H.eigenvalues i
  obtain ⟨i_min, hi_min⟩ := exists_eq_ciInf_of_finite (f := (HermitianMat.H σ₁.M).eigenvalues)

  have h_min_pos : 0 < mineig := by
    --because σ₁ is PosDef, all eigenvalues are positive, so their minimum is positive
    unfold mineig
    rw [← hi_min]
    exact hσ₁_pos.eigenvalues_pos i_min

  have h_min_le_one : mineig ≤ 1 := by
    --all eigenvalues of a state are at most 1. (We might not actually need this fact.)
    unfold mineig
    rw [← hi_min]
    exact σ₁.eigenvalue_le_one i_min

  clear i_min hi_min

  -- The sequence c_n given in (S44). In order to handle when c = 0, I've replaced the
  -- (Real.log 3) / n term with (Real.log 3) / (max n 1). I expect this will work down the line.
  let c (n : ℕ) := Real.log (1 / mineig) + (Real.log 3) / (max n 1)
  have hc (n) : 0 < c n := by
    have h₁ : 0 ≤ Real.log (1 / mineig) := by bound
    positivity

  have hc_lim : Filter.atTop.Tendsto (fun n ↦ (c n) / n) (𝓝 0) := by
    have h_const : Filter.atTop.Tendsto (fun n : ℕ ↦ Real.log (1 / mineig) / n) (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop;
    -- We can split the limit into two parts: the constant term and the term involving log(3).
    have h_div : Filter.atTop.Tendsto (fun n : ℕ ↦ Real.log 3 / (max n 1 * n)) (𝓝 0) :=
      tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_mono (fun n ↦ by
        norm_cast; nlinarith [le_max_left n 1, le_max_right n 1]) tendsto_natCast_atTop_atTop
    convert h_const.add h_div using 2 <;> ring

  -- The function f_n(λ) in (S45)
  let f (n : ℕ) (lam : ℝ) := ⌈Real.log lam / c n⌉ * c n
  --(S46)
  have h_le_f (n) (lam) : Real.log lam ≤ f n lam := calc
    _ ≤ (⌈Real.log lam / (c n)⌉) * c n := by
      rw [← mul_inv_le_iff₀ (hc n)]
      apply Int.le_ceil _
    _ = f n lam := by
      rfl
  have h_f_le (n) (lam) : f n lam < Real.log lam + c n := calc
    f n lam = ⌈Real.log lam / c n⌉ * c n := by
      rfl
    _ < (Real.log lam / c n + 1) * c n := by
      specialize hc n
      gcongr
      exact Int.ceil_lt_add_one _
    _ ≤ Real.log lam + c n := by
      specialize hc n
      field_simp
      rfl

  --Define σ'' first as the (unnormalized) cfc image of σ' under `λ → exp (f n λ)`.
  let σ''_unnormalized (n) : HermitianMat (H (i ^ n)) ℂ :=
    (σ' n).M.cfc fun e ↦ Real.exp (f n e)

  have σ''_unnormalized_PosDef (n) : Matrix.PosDef (σ''_unnormalized n).val := by
    dsimp [σ''_unnormalized]
    rw [HermitianMat.cfc_PosDef]
    intro
    positivity

  have h_exp_f (n) (x : ℝ) (hx : 0 < x) : x ≤ Real.exp (f n x) ∧ (Real.exp (f n x) < Real.exp (c n) * x) := by
    constructor
    · convert Real.exp_monotone (h_le_f n x)
      rw [Real.exp_log hx]
    · convert Real.exp_strictMono (h_f_le n x) using 1
      rw [Real.exp_add (Real.log x), Real.exp_log hx, mul_comm]

  have σ''_tr_bounds (n) : 1 ≤ (σ''_unnormalized n).trace ∧ (σ''_unnormalized n).trace < Real.exp (c n) := by
    have hσ' := (σ' n).tr
    constructor
    · rw [← HermitianMat.sum_eigenvalues_eq_trace] at hσ' ⊢
      rw [← hσ']
      obtain ⟨e, he⟩ := (σ' n).M.cfc_eigenvalues fun e ↦ Real.exp (f n e)
      rw [he]
      simp only [HermitianMat.val_eq_coe, MState.toMat_M, Function.comp_apply]
      rw [Equiv.sum_comp e (fun i ↦ Real.exp (f n (Matrix.IsHermitian.eigenvalues _ i)))]
      gcongr
      refine (h_exp_f n _ ?_).left
      exact (σ'_posdef n).eigenvalues_pos _
    · rw [← HermitianMat.sum_eigenvalues_eq_trace] at hσ' ⊢
      rw [← mul_one (Real.exp (c n)), ← hσ', Finset.mul_sum]
      obtain ⟨e, he⟩ := (σ' n).M.cfc_eigenvalues fun e ↦ Real.exp (f n e)
      rw [he]; clear he
      dsimp
      rw [Equiv.sum_comp e (fun i ↦ Real.exp (f n (Matrix.IsHermitian.eigenvalues _ i)))]
      gcongr
      · exact Finset.univ_nonempty
      · refine (h_exp_f n _ ?_).right
        exact (σ'_posdef n).eigenvalues_pos _

  --Then σ'' is the normalized version, which will work because σ''_unnormalized is PosDef
  let σ'' (n) : MState (H (i ^ n)) := {
    --TODO make this its own definition
    M := (σ''_unnormalized n).trace⁻¹ • (σ''_unnormalized n)
    zero_le := by
      have h1 : 0 < (σ''_unnormalized n).trace := zero_lt_one.trans_le (σ''_tr_bounds n).left
      have h2 : 0 < σ''_unnormalized n := (σ''_unnormalized_PosDef n).zero_lt
      exact smul_nonneg (inv_nonneg_of_nonneg h1.le) h2.le
    tr := by
      simp only [HermitianMat.trace_smul]
      apply inv_mul_cancel₀
      exact (zero_lt_one.trans_le (σ''_tr_bounds n).left).ne'
  }

  have σ''_posdef n : (σ'' n).M.toMat.PosDef := by
    apply (σ''_unnormalized_PosDef n).smul
    have := (σ''_tr_bounds n).left
    positivity

  have σ'_le_σ'' (n) : Real.exp (-c n) • (σ' n).M ≤ σ'' n := by
    dsimp [σ'']
    set x := (σ''_unnormalized n).trace
    dsimp [σ''_unnormalized]
    rw [← HermitianMat.cfc_const_mul_id, ← HermitianMat.cfc_const_mul_id,
      ← HermitianMat.cfc_comp]
    rw [← sub_nonneg, ← HermitianMat.cfc_sub, HermitianMat.zero_le_cfc]
    intro i
    set y := (σ' n).M.H.eigenvalues i
    have hy : 0 < y := (σ'_posdef n).eigenvalues_pos i
    dsimp only [Pi.sub_apply, Function.comp_apply]
    have : 0 < x := zero_lt_one.trans_le (σ''_tr_bounds n).left
    grw [ ← (h_exp_f n y hy).left]
    rw [← sub_mul]
    suffices 0 ≤ x⁻¹ - Real.exp (-c n) by positivity
    rw [sub_nonneg, ← inv_le_inv₀]
    · simpa [← Real.exp_neg] using (σ''_tr_bounds n).right.le
    · positivity
    · positivity
  have σ''_le_σ' (n) : σ'' n ≤ Real.exp (c n) • (σ' n).M := by
    dsimp [σ'']
    set x := (σ''_unnormalized n).trace
    dsimp [σ''_unnormalized]
    rw [← HermitianMat.cfc_const_mul_id, ← HermitianMat.cfc_const_mul_id,
      ← HermitianMat.cfc_comp]
    rw [← sub_nonneg, ← HermitianMat.cfc_sub, HermitianMat.zero_le_cfc]
    intro i
    set y := (σ' n).M.H.eigenvalues i
    have hy : 0 < y := (σ'_posdef n).eigenvalues_pos i
    dsimp only [Pi.sub_apply, Function.comp_apply]
    grw [ ← (h_exp_f n y hy).right]
    rw [← one_sub_mul]
    suffices 0 ≤ 1 - x⁻¹ by positivity
    simpa using inv_le_one_of_one_le₀ (σ''_tr_bounds n).left

  have qRel_σ''_le_σ' n : 𝐃(ρ⊗^S[n]‖σ'' n) ≤ 𝐃(ρ⊗^S[n]‖σ' n) + ENNReal.ofReal (c n) := by
    rw [← Real.log_exp (c n)]
    apply qRelEntropy_le_add_of_le_smul
    apply σ''_le_σ'

  have qRel_σ'_le_σ'' n : 𝐃(ρ⊗^S[n]‖σ' n) ≤ 𝐃(ρ⊗^S[n]‖σ'' n) + ENNReal.ofReal (c n) := by
    rw [← Real.log_exp (c n)]
    apply qRelEntropy_le_add_of_le_smul
    rw [← inv_smul_le_iff_of_pos (by positivity), ← Real.exp_neg]
    apply σ'_le_σ''

  -- Definition of the pinching map w.r.t. σ'' in Eq. (S55)
  let ℰ n := pinching_map (σ'' n)

  have hσ'n_eq_sum_third n : (σ' n).M = (1 / 3 : ℝ) • «σ̃» n +
      (1 / 3 : ℝ) • «σ⋆» n + (1 / 3 : ℝ) • (σ₁⊗^S[n]) := by
    unfold σ'
    change _ • _ + _ = _
    conv =>
      enter [1, 1, 2]
      change _ + _
    dsimp [Mixable.to_U]
    norm_num only [one_div, Prob.coe_one_minus, smul_add, smul_smul]

  have hσ₁_le_σ' n : (1 / 3 : ℝ) • (σ₁⊗^S[n]).M ≤ (σ' n).M := by
    rw [hσ'n_eq_sum_third]
    apply le_add_of_nonneg_left
    have := («σ⋆» n).zero_le
    have := («σ̃» n).zero_le
    positivity

  -- Number of distinct eigenvalues of σ'' in Eq. (S56) is
  -- Fintype.card (spectrum ℝ (σ'' n).m), which is dₙ in the paper.
  have hdle n : Fintype.card (spectrum ℝ (σ'' n).m) ≤ n + 1 := by
    rw [Matrix.card_spectrum_eq_image (σ'' n).m (σ'' n).M.H]
    rcases n.eq_zero_or_pos with rfl | hn
    · have _ : Unique (H (i ^ 0)) := by
        rw [spacePow_zero]
        infer_instance
      simp
    rw [← Set.ncard_coe_finset]
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    have eq : ∃ (e : Equiv.Perm _), (σ'' n).M.H.eigenvalues =
        (fun x ↦ (σ''_unnormalized n).trace⁻¹ * Real.exp (f n x)) ∘ (σ' n).M.H.eigenvalues ∘ e := by
      convert (σ' n).M.cfc_eigenvalues (fun x ↦ (σ''_unnormalized n).trace⁻¹ * Real.exp (f n x))
      rw [HermitianMat.cfc_const_mul]
    rcases eq with ⟨eq, heq⟩
    rw [heq]
    simp only [Set.range_comp, MState.toMat_M, EquivLike.range_eq_univ, Set.image_univ, ge_iff_le]
    let S : Set ℝ := (fun x => Real.exp (f n x)) '' Set.Icc ((mineig ^ n) / 3) 1
    have h_card_subs : Set.ncard S ≤ n + 1 ∧ S.Finite := by
      exact f_image_bound mineig n h_min_pos hn h_le_f h_f_le
    let S₂ : Set ℝ := (fun x => (σ''_unnormalized n).trace⁻¹ * Real.exp (f n x)) '' Set.Icc ((mineig ^ n) / 3) 1
    obtain ⟨h_card_subs₂, h_s₂_finite⟩ : Set.ncard S₂ ≤ n + 1 ∧ S₂.Finite := by
      have hS₂ : S₂ = ((σ''_unnormalized n).trace⁻¹ * ·) '' S := by
        simp [S, S₂, Set.image_image]
      constructor
      · rw [hS₂]
        exact (Set.ncard_image_le h_card_subs.right).trans h_card_subs.left
      · rw [hS₂]
        exact h_card_subs.right.image _
    refine (Set.ncard_le_ncard (t := (fun x => (σ''_unnormalized n).trace⁻¹ *
      Real.exp (f n x)) '' Set.Icc ((mineig ^ n) / 3) 1) ?_ h_s₂_finite).trans h_card_subs₂
    apply Set.image_mono
    rintro _ ⟨i, rfl⟩
    refine ⟨?_, MState.eigenvalue_le_one _ _⟩
    refine le_trans ?_ (ciInf_le (Finite.bddBelow_range _) i)
    refine le_trans ?_ (iInf_eigenvalues_le (hσ₁_le_σ' n) (HermitianMat.H _) _)
    dsimp [mineig, iInf]
    rw [← Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues]
    rw [← Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues]
    rw [spectrum.smul_eq_smul _ _ (CFC.spectrum_nonempty ℝ _ (σ₁⊗^S[n]).M.H)]
    rw [Real.sInf_smul_of_nonneg (by norm_num)]
    simp only [MState.toMat_M, smul_eq_mul, div_eq_inv_mul,
      mul_one, inv_pos, Nat.ofNat_pos, mul_le_mul_iff_right₀]
    apply le_of_eq
    -- sInf (spectrum ℝ σ₁.m) ^ n = sInf (spectrum ℝ σ₁⊗^S[n].m)
    symm
    apply sInf_spectrum_spacePow
  have hdpos n : 0 < Fintype.card (spectrum ℝ (σ'' n).m) := by
    rw [Fintype.card_pos_iff, Set.nonempty_coe_sort]
    apply IsSelfAdjoint.spectrum_nonempty
    exact (σ'' n).M.H

  -- Eq (S59) has a minus sign, which gets complicated when one of the relative entropies is infinite.
  -- However, I don't think we need this version with the minus sign.
  have qRel_pinching_pythagoras n : 𝐃(ρ⊗^S[n]‖σ'' n) = 𝐃(ρ⊗^S[n]‖ℰ n (ρ⊗^S[n])) + 𝐃(ℰ n (ρ⊗^S[n])‖σ'' n) := by
    exact pinching_pythagoras (ρ⊗^S[n]) (σ'' n)

  -- Eq. (S60)
  have qRel_ent_bound n : 𝐃(ρ⊗^S[n]‖ℰ n (ρ⊗^S[n])) ≤ ENNReal.ofReal (Real.log (n + 1)) := calc
    𝐃(ρ⊗^S[n]‖ℰ n (ρ⊗^S[n])) ≤ ENNReal.ofReal (Real.log (Fintype.card (spectrum ℝ (σ'' n).m))) :=
      qRelativeEnt_op_le (by simp [hdpos n]) (pinching_bound ..)
    _ ≤ ENNReal.ofReal (Real.log (n + 1)) := by
      grw [hdle n]
      · exact_mod_cast le_rfl
      · simp [hdpos n]

  -- Eq. (S61)
  have hliminf : Filter.atTop.liminf (fun n ↦ 𝐃(ρ⊗^S[n]‖σ' n) / n) =
                 Filter.atTop.liminf (fun n ↦ 𝐃(ℰ n (ρ⊗^S[n])‖σ'' n) / n) := by
    trans Filter.atTop.liminf fun n ↦ 𝐃(ρ⊗^S[n]‖σ'' n) / n
    · have hg : Filter.atTop.Tendsto (fun n ↦ ENNReal.ofReal (c n) / n) (𝓝 0) := by
        rw [← ENNReal.tendsto_toReal_iff_of_eventually_ne_top ?_ ENNReal.zero_ne_top]
        · simpa [ENNReal.toReal_ofReal (hc _).le]
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
    · simp only [qRel_pinching_pythagoras, ENNReal.add_div, ← Pi.add_apply]
      conv =>
        lhs
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

  clear qRel_ent_bound qRel_pinching_pythagoras hdpos hdle qRel_σ'_le_σ'' qRel_σ''_le_σ'

  -- Eq. (S62)
  have hliminfR : Filter.atTop.liminf (fun n ↦ 𝐃(ℰ n (ρ⊗^S[n])‖σ'' n) / n) - R1 ρ ε ≤
      ↑(1 - ε') * (R2 ρ σ - R1 ρ ε) := by
    have «hσ''_ge_σ⋆» n : σ'' n ≥ (Real.exp (-c n) / 3) • («σ⋆» n).M := by
      grw [ge_iff_le, ← σ'_le_σ'', div_eq_mul_inv, ← smul_smul, ← one_div]
      rw [smul_le_smul_iff_of_pos_left (by positivity), hσ'n_eq_sum_third]
      apply le_add_of_le_of_nonneg
      · apply le_add_of_nonneg_left
        have := («σ̃» n).zero_le
        positivity
      · have := (σ₁⊗^S[n]).zero_le
        positivity --TODO: It would be so cool if this could be done by *just* positivity.
    have «hσ''_ge_σ̃» n : σ'' n ≥ (Real.exp (-c n) / 3) • («σ̃» n).M := by
      grw [ge_iff_le, ← σ'_le_σ'', div_eq_mul_inv, ← smul_smul, ← one_div]
      rw [smul_le_smul_iff_of_pos_left (by positivity), hσ'n_eq_sum_third]
      apply le_add_of_le_of_nonneg
      · apply le_add_of_nonneg_right
        have := («σ⋆» n).zero_le
        positivity
      · have := (σ₁⊗^S[n]).zero_le
        positivity --TODO: It would be so cool if this could be done by *just* positivity.
    have hσ''_ge_σ₁ n : σ'' n ≥ (Real.exp (-c n) / 3) • (σ₁⊗^S[n]).M := by
      grw [ge_iff_le, ← σ'_le_σ'', div_eq_mul_inv, ← smul_smul, ← one_div]
      rw [smul_le_smul_iff_of_pos_left (by positivity)]
      exact hσ₁_le_σ' n

    have hc_littleO : (fun n : ℕ ↦ c n + Real.log 3) =o[Filter.atTop] (fun x ↦ (x : ℝ)) := by
      apply Asymptotics.IsLittleO.add
      · rw [Asymptotics.isLittleO_iff_tendsto']
        · exact hc_lim
        simp only [Nat.cast_eq_zero, Filter.eventually_atTop]
        use 1
        grind
      · --This really should be its own fact, TODO
        refine Asymptotics.isLittleO_const_left.2 <| Or.inr ?_
        convert tendsto_natCast_atTop_atTop (R := ℝ)
        ext; simp

    have hliminf_le : Filter.atTop.liminf (fun n ↦
        —log β_ ε(ℰ n (ρ⊗^S[n])‖{σ'' n}) / n) ≤ (R1 ρ ε).toNNReal := by --(S66)
      rw [ENNReal.coe_toNNReal hR1R2.ne_top]
      unfold R1
      calc _ = Filter.atTop.liminf (fun n => —log
        β_ ε((ℰ n) (ρ⊗^S[n])‖{(pinching_map (σ'' n)) (σ'' n)}) / ↑n) := by conv =>
          enter [1, 1, n]
          rw [← pinching_self (σ'' n)]
      _ ≤ Filter.atTop.liminf (fun n => —log β_ ε(ρ⊗^S[n]‖{(σ'' n)}) / ↑n) := by --(S67)
        refine Filter.liminf_le_liminf ?_
        apply Filter.Eventually.of_forall
        intro
        apply ENNReal.div_le_div_right
        apply Prob.negLog_Antitone
        apply OptimalHypothesisRate.optimalHypothesisRate_antitone
      _ ≤ Filter.atTop.liminf (fun n => —log β_ ε(ρ⊗^S[n]‖{(«σ⋆» n)}) / ↑n) := by --(S68)
        apply LemmaS3_inf _ _ _
          (f := fun n ↦ ⟨c n + Real.log 3, add_nonneg (hc n).le (Real.log_nonneg (by norm_num))⟩) hc_littleO
        intro i
        dsimp only [coe_mk]
        rw [neg_add', Real.exp_sub, Real.exp_log (by positivity)]
        exact «hσ''_ge_σ⋆» i
      _ = _ := by --(S69)
        congr! 4 with n
        rw [← OptimalHypothesisRate.Lemma3 ε IsCompact_IsFree free_convex]
        rw [← iSup_subtype'']
        have hs := Classical.choose_spec (σ_max_exists n)
        exact (hs.right.iSup_eq hs.left).symm

    have hlimsup_le (ε1 : Prob) (hε1 : 0 < (ε1 : ℝ) ∧ (ε1 : ℝ) < 1) :
        Filter.atTop.limsup (fun n ↦ —log β_ (1-ε1)(ℰ n (ρ⊗^S[n])‖{σ'' n}) / n) ≤
          ((R2 ρ σ).toNNReal + ⟨ε₀, hε₀.le⟩ : NNReal) := by --(S70)
      rw [ENNReal.coe_add, ENNReal.coe_toNNReal hR2]
      unfold R2
      calc _ = Filter.atTop.limsup (fun n => —log
        β_ (1-ε1)((ℰ n) (ρ⊗^S[n])‖{(pinching_map (σ'' n)) (σ'' n)}) / ↑n) := by conv =>
          enter [1, 1, n]
          rw [← pinching_self (σ'' n)]
      _ ≤ Filter.atTop.limsup (fun n => —log β_ (1-ε1)(ρ⊗^S[n]‖{(σ'' n)}) / ↑n) := by
        refine Filter.limsup_le_limsup ?_
        apply Filter.Eventually.of_forall
        intro
        apply ENNReal.div_le_div_right
        apply Prob.negLog_Antitone
        apply OptimalHypothesisRate.optimalHypothesisRate_antitone
      _ ≤ Filter.atTop.limsup (fun n => —log β_ (1-ε1)(ρ⊗^S[n]‖{(«σ̃» n)}) / ↑n) := by --(S71)
        apply LemmaS3_sup _ _ _
          (f := fun n ↦ ⟨c n + Real.log 3, add_nonneg (hc n).le (Real.log_nonneg (by norm_num))⟩) hc_littleO
        intro i
        dsimp only [coe_mk]
        rw [neg_add', Real.exp_sub, Real.exp_log (by positivity)]
        exact «hσ''_ge_σ̃» i
      _ ≤ _ := by --(S72)
        apply Lemma6
        · exact hm.left
        · exact hσ₁_pos
        · change (_ : ℝ) < _
          simpa using hε1.left
      _ ≤ _ := hm.right.le --(S73)

    let P1 ε2 n := {(ℰ n (ρ⊗^S[n])).M ≥ₚ (Real.exp (↑n*((R1 ρ ε).toReal + ε2))) • (σ'' n).M}
    let P2 ε2 n := {(ℰ n (ρ⊗^S[n])).M ≥ₚ (Real.exp (↑n*((R2 ρ σ).toReal + ε₀ + ε2))) • (σ'' n).M}

    have hPcomm ε2 n : Commute (P1 ε2 n).toMat (P2 ε2 n).toMat := by
      simp only [HermitianMat.proj_le, HermitianMat.cfc_toMat, P1, P2]
      apply IsSelfAdjoint.commute_cfc
      · apply HermitianMat.H
      symm
      apply IsSelfAdjoint.commute_cfc
      · apply HermitianMat.H
      simp only [AddSubgroupClass.coe_sub, MState.toMat_M, selfAdjoint.val_smul]
      suffices h : Commute ((ℰ n) (ρ⊗^S[n])).m (σ'' n).m by
        apply Commute.sub_left
        · exact (Commute.refl _).sub_right (h.smul_right _)
        · exact (h.symm.sub_right ((Commute.refl _).smul_right _)).smul_left _
      exact pinching_commutes (ρ⊗^S[n]) (σ'' n)

    have hliminfP1 ε2 (hε2 : 0 < ε2) := --(S76)
      LemmaS2liminf hε2 (fun n ↦ ℰ n (ρ⊗^S[n])) (σ'') hliminf_le

    conv at hliminfP1 =>
      enter [ε2, hε2, 1, 1, n, 1]
      change P1 _ _

    have hlimsupP2  ε2 (hε2 : 0 < ε2) (ε1 : Prob) (hε1 : 0 < (ε1 : ℝ) ∧ (ε1 : ℝ) < 1) := --(S77)
      LemmaS2limsup hε2 (fun n ↦ ℰ n (ρ⊗^S[n])) (σ'') (hlimsup_le ε1 (by simp [hε1]))

    have hlimsupP2' ε2 (hε2 : 0 < ε2) :
        Filter.atTop.limsup (fun n ↦ (P2 ε2 n).inner (ℰ n (ρ⊗^S[n])).M) = 0 := by
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
        specialize hlimsupP2 ⟨ε2, hε2.le⟩ hε2 ⟨ε1, ⟨hε1.1.le, hε1.2.le⟩⟩ hε1
        trans ε1
        · convert hlimsupP2
          simp only [Prob.coe_one_minus, sub_sub_cancel]
        · simp only [one_div, zero_add, inf_le_left, ε1]
      · apply Filter.le_limsup_of_frequently_le ?_ ?_
        · rw [Filter.frequently_atTop]
          intro n; use n
          exact ⟨by rfl, HermitianMat.inner_ge_zero (HermitianMat.proj_le_nonneg _ _)
                                                    (HermitianMat.zero_le_iff.mpr ((ℰ n) (ρ⊗^S[n])).pos)⟩
        · apply Filter.isBoundedUnder_of
          use 1; intro n
          calc
            (P2 ε2 n).inner ↑((ℰ n) (ρ⊗^S[n])) ≤ HermitianMat.inner 1 ((ℰ n) (ρ⊗^S[n])).M :=
              HermitianMat.inner_mono' (HermitianMat.zero_le_iff.mpr ((ℰ n) (ρ⊗^S[n])).pos)
                                       (HermitianMat.proj_le_le_one _ _)
            _ = ((ℰ n) (ρ⊗^S[n])).M.trace := HermitianMat.one_inner _
            _ = 1 := MState.tr _

    let E1 := 1 - P1 -- (S78)
    let E2 := P1 - P2 -- (S79)
    let E3 := P2 -- (S80)

    have Esum : E1 + E2 + E3 = 1 := by
      unfold E1 E2 E3
      abel

    have hE1proj ε2 n : E1 ε2 n = {(ℰ n (ρ⊗^S[n])).M <ₚ (Real.exp (↑n*((R1 ρ ε).toReal + ε2))) • (σ'' n).M} := by
      dsimp [E1, P1]
      rw [sub_eq_iff_eq_add]
      simp only [HermitianMat.proj_le_add_lt]

    have hE2leProj ε2 n : E2 ε2 n ≤ {(ℰ n (ρ⊗^S[n])).M <ₚ (Real.exp (↑n*((R2 ρ σ).toReal + ε₀ + ε2))) • (σ'' n).M} := by
      dsimp [E2, P1, P2]
      rw [sub_le_iff_le_add]
      simp only [HermitianMat.proj_le_add_lt]
      exact HermitianMat.proj_le_le_one _ _

    -- (S81)
    /- A literal translation of the paper would read:
       (1/n : ℝ) • (E1 ε2 n).toMat * ((ℰ n (ρ⊗^S[n])).M.log.toMat - (σ'' n).M.log.toMat) ≤ ((R1 ρ ε).toReal + ε2) • (E1 ε2 n).toMat
    But this is simply not true! Because what happens when `ℰ n (ρ⊗^S[n])` has a zero eigenvalue, which
    it can? Then (S81) is an inequality of operators where the LHS has an operator with a "negative
    infinity" eigenvalue, intuitively. This isn't something very well defined, certainly not supported
    in our definitions. This only becomes mathematically meaningful when we see how it's used later, in
    (S88): both sides are traced against `ℰ n (ρ⊗^S[n])`, so that the 0 eigenvalues becomes irrelevant. This
    is the version we state and prove, then.

    Luckily, (S82) and (S85) are correct as written (in a particular interpretation), because
    there the problematic subspaces are indeed projected out by the E₂ and E₃ operators.
    -/
    have hE1leq ε2 (n : ℕ) (hε2 : 0 < ε2) :
        (ℰ n (ρ⊗^S[n])).M.inner (HermitianMat.mul_commute
          (commute_aux n (E := E1 ε2 n) (pinching_commutes (ρ⊗^S[n]) (σ'' n)) rfl)) ≤
          (ℰ n (ρ⊗^S[n])).M.inner (((R1 ρ ε).toReal + ε2) • (E1 ε2 n)) := by
      refine rexp_mul_smul_proj_lt_mul_sub_le_mul_sub
        (pinching_commutes (ρ⊗^S[n]) (σ'' n)) (by positivity) ?_ (σ''_posdef n) rfl
      rw [← HermitianMat.zero_le_iff]
      apply MState.zero_le

    -- (S82) -- see (S81) for comments
    have hE2leq ε2 (n : ℕ) (hε2 : 0 < ε2) : (1/n : ℝ) • (E2 ε2 n).toMat * ((ℰ n (ρ⊗^S[n])).M.log.toMat - (σ'' n).M.log.toMat) ≤ ((R2 ρ σ).toReal + ε₀ + ε2) • (E2 ε2 n).toMat := by
      refine rexp_mul_smul_proj_lt_mul_sub_le_mul_sub'
        (pinching_commutes (ρ⊗^S[n]) (σ'' n)) ?_ (σ''_posdef n) rfl
      rw [← HermitianMat.zero_le_iff]
      apply MState.zero_le

    -- (S83)
    let c' ε2 n := (c n + (c n) / n) ⊔ ((R2 ρ σ).toReal + ε₀ + ε2)

    have hc' (ε2 : ℕ → ℝ≥0) (hε2 : ∀ n, ε2 n < 1) :
        ∃ (C : ℝ≥0), ∀ᶠ (n : ℕ) in Filter.atTop, c' (ε2 n) n ≤ C := by
      apply c'_bounded hε2 _ hc

    -- (S84)
    have hσ'' ε2 n : Real.exp (-n * c' ε2 n) • 1 ≤ (σ'' n).M := by
      rcases n.eq_zero_or_pos with rfl | hn
      · have _ : Unique (H (i ^ 0)) := by
          rw [spacePow_zero]
          infer_instance
        apply le_of_eq
        simp [Unique.eq_default (σ'' 0)]
      calc
        (σ'' n).M ≥ Real.exp (- c n) • (σ' n).M := σ'_le_σ'' n
        _ ≥ (Real.exp (- c n) * (1 / 3)) • (σ₁⊗^S[n]).M := by
          grw [← hσ₁_le_σ' n, smul_smul]
        _ ≥ (Real.exp (- c n) * (1 / 3)) • ((iInf (σ₁⊗^S[n]).M.H.eigenvalues) • 1) := by
          apply smul_le_smul_of_nonneg_left
          · exact iInf_eigenvalues_smul_one_le (σ₁⊗^S[n]).M.H
          · positivity
        _ = (Real.exp (- c n) * (1 / 3) * mineig^n) • 1 := by
          dsimp [mineig, iInf]
          rw [← Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues]
          rw [← Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues]
          rw [MState.toMat_M, sInf_spectrum_spacePow σ₁ n, MState.toMat_M, smul_smul]
        _ = Real.exp (- n * (c n + (c n) / n)) • 1 := by
          rw [c_identity h_min_pos hn]
        _ ≥ Real.exp (-n * c' ε2 n) • 1 := by
          apply smul_le_smul_of_nonneg_right
          · apply Real.exp_le_exp_of_le
            simp only [neg_mul, neg_le_neg_iff]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            dsimp [c']
            exact le_sup_left
          · exact zero_le_one

    -- Leo: I think there's a typo in the third eq. of this step: ρ should be ρ^n.
    -- The next set of equations also have ρ_n instead of ρ^n.
    -- (S88)
    have hDleq ε2 n : (𝐃(ℰ n (ρ⊗^S[n])‖σ'' n) / n : ℝ≥0∞) ≤  ((R1 ρ ε) + .ofReal ε2) +
         .ofReal ((P1 ε2 n).inner (ℰ n (ρ⊗^S[n]))) * ((R2 ρ σ + .ofReal ε₀ + .ofReal ε2) - (R1 ρ ε + .ofReal ε2)) +
         .ofReal ((P2 ε2 n).inner (ℰ n (ρ⊗^S[n]))) * (.ofReal (c' ε2 n) - (R2 ρ σ + .ofReal ε₀ + .ofReal ε2)) := by

      -- see (S81) for comments on why that statement had to be changed
      -- (S85)
      -- (first inequality should have $\sigma_n''$ instead of
      -- $\tilde{\sigma}_n''$; corrected in v4, where $\tilde{\sigma}_n'$ takes
      -- the place of $\sigma_n''$) in this and other steps
      have hE3leq ε2 (n : ℕ) (hε2 : 0 < ε2) : (1/n : ℝ) • (E3 ε2 n).toMat * ((ℰ n (ρ⊗^S[n])).M.log.toMat - (σ'' n).M.log.toMat) ≤ (c' ε2 n) • (E3 ε2 n).toMat := by
        rcases n.eq_zero_or_pos with rfl | hn
        swap
        · calc
          (1/n : ℝ) • (E3 ε2 n).toMat * ((ℰ n (ρ⊗^S[n])).M.log.toMat - (σ'' n).M.log.toMat) ≤ (1/n : ℝ) • (E3 ε2 n).toMat * (- (σ'' n).M.log.toMat) := by
            -- first inequality of (S85)
            have hℰρlognonpos : 0 ≤ -(ℰ n (ρ⊗^S[n])).M.log.toMat := by
              -- log of state is non-positive
              simp only [HermitianMat.log]
              rw [← AddSubgroup.coe_neg _, ← HermitianMat.cfc_neg (ℰ n (ρ⊗^S[n])).M]
              change (HermitianMat.toMat 0) ≤ _
              rw [Subtype.coe_le_coe, HermitianMat.zero_le_cfc (ℰ n (ρ⊗^S[n])).M (-Real.log)]
              intro i
              simp
              apply Real.log_nonpos
              · apply MState.eigenvalue_nonneg _
              · apply MState.eigenvalue_le_one
            rw [← sub_nonneg, ← mul_sub_left_distrib]
            conv =>
              rhs
              congr; rfl
              rw [← sub_add (-(σ'' n).M.log.toMat) ((ℰ n (ρ⊗^S[n])).M.log.toMat) ((σ'' n).M.log.toMat)]
              rw [add_comm_sub]
              rw [← add_sub_assoc]
              simp [sub_self (σ'' n).M.log.toMat]
            have hE3commℰ : Commute (E3 ε2 n).toMat ((ℰ n (ρ⊗^S[n])).M.log.toMat) := by
              unfold E3 P2
              rw [HermitianMat.proj_le_def]
              apply HermitianMat.cfc_commute
              apply Commute.sub_left
              · simp only [HermitianMat.val_eq_coe, MState.toMat_M, Commute.refl]
              · apply Commute.smul_left
                apply Commute.symm
                exact pinching_commutes (ρ⊗^S[n]) (σ'' n)
            simp only [Algebra.smul_mul_assoc, one_div]
            have hE3ℰnonneg : 0 ≤ (E3 ε2 n).toMat * -(ℰ n (ρ⊗^S[n])).M.log.toMat := by
              apply Commute.mul_nonneg _ hℰρlognonpos (Commute.neg_right hE3commℰ)
              apply HermitianMat.proj_le_nonneg
            apply smul_nonneg (inv_nonneg_of_nonneg (Nat.cast_nonneg' n)) hE3ℰnonneg
          _ ≤ (1/n : ℝ) • (E3 ε2 n).toMat * (- (Real.exp (-n * c' ε2 n) • (1 : HermitianMat (H (i ^ n)) ℂ)).log.toMat) := by
            -- intermediate step in 2nd ineq of S85
            simp only [mul_neg, neg_mul, neg_le_neg_iff]
            have h1logleq : (Real.exp (-(n * c' ε2 n)) • 1 : HermitianMat (H (i ^ n)) ℂ).log.toMat ≤ ((σ'' n).M).log.toMat := by
              -- apply hσ'' ε2 n to log by monotonicity
              rw [Subtype.coe_le_coe]
              have h_comm : Commute ((Real.exp _ • 1 : HermitianMat _ ℂ).toMat) _ :=
                Commute.smul_left (Commute.one_left (σ'' n).M.toMat) (Real.exp (-(n * c' ε2 n)))
              exact HermitianMat.log_le_log_of_commute h_comm (by simpa using hσ'' ε2 n)
                (Matrix.PosDef.smul Matrix.PosDef.one (Real.exp_pos (-(n * c' ε2 n))))
            rw [← sub_nonneg] at h1logleq
            rw [← sub_nonneg, ← mul_sub_left_distrib]
            simp only [one_div, Algebra.smul_mul_assoc]
            have hE3commlog : Commute (E3 ε2 n).toMat ((σ'' n).M.log.toMat - (Real.exp (-(n * c' ε2 n)) • 1 : HermitianMat _ ℂ).log.toMat) := by
              -- projector commutes with logs
              apply Commute.sub_right
              swap
              -- prove Commute (E3 \_) (\_ 1).log
              · conv =>
                rhs
                simp only [
                  HermitianMat.log_smul (1 : HermitianMat _ ℂ) (Real.exp _),
                  Real.log_exp, neg_smul, HermitianMat.log_one,
                  add_zero, NegMemClass.coe_neg,
                  HermitianMat.val_eq_coe, selfAdjoint.val_smul,
                  selfAdjoint.val_one
                  ]
              simp only [Commute.neg_right_iff, Commute.smul_right (Commute.one_right _) _]
              -- prove Commute (E3 _) (σ'' _).log
              · unfold E3 P2
              rw [HermitianMat.proj_le_def]
              apply HermitianMat.cfc_commute
              -- have hcommℰσ : Commute (((ℰ n) (ρ⊗^S[n]))).M.toMat (σ'' n).M.toMat := by sorry
              apply Commute.sub_left
              · exact pinching_commutes (ρ⊗^S[n]) (σ'' n)
              · apply Commute.smul_left
                · rfl
            have hElognonneg : 0 ≤ (E3 ε2 n).toMat * ((σ'' n).M.log.toMat - (Real.exp (-(n * c' ε2 n)) • 1 : HermitianMat _ ℂ).log.toMat) := by
              -- factors are positive and commute (hE3commlog),
              -- so product is positive too (Commute.mul_nonneg)
              apply Commute.mul_nonneg _ h1logleq hE3commlog
              apply HermitianMat.proj_le_nonneg
            apply smul_nonneg (inv_nonneg_of_nonneg (Nat.cast_nonneg' n)) hElognonneg
          _ = (c' ε2 n) • (E3 ε2 n).toMat := by
            -- simplify log(1)
            conv =>
              lhs; congr; rfl
              simp only [
                neg_mul, HermitianMat.log_smul _ _, Real.log_exp, neg_smul,
                HermitianMat.log_one, add_zero, NegMemClass.coe_neg,
                HermitianMat.val_eq_coe,
                selfAdjoint.val_smul, selfAdjoint.val_one, neg_neg
                ]
              rfl
            simp only [one_div, Algebra.mul_smul_comm, mul_one, smul_smul]
            rw [mul_comm, ← mul_assoc, ← one_div, one_div_mul_cancel, one_mul]
            simp only [ne_eq, Nat.cast_eq_zero, ne_zero_of_lt hn, not_false_eq_true]
        · simp only [CharP.cast_eq_zero, div_zero, zero_smul, statePow_zero, zero_mul]
          apply smul_nonneg
          · simp [c']
            left
            apply (hc 0).le
          · apply HermitianMat.proj_le_nonneg
      --Linearly combine S81, S82, S85:
      --(S86)
      --(S87)
      sorry

    -- (S91)
    have hliminfDleq : Filter.atTop.liminf (fun n ↦ 𝐃(ℰ n (ρ⊗^S[n])‖σ'' n) / n) ≤
         (R1 ρ ε) + .ofReal (1 - ε.val) * (R2 ρ σ + .ofReal ε₀ - R1 ρ ε) := by

      --Pick a sequence `ε2 n` that converges slowly enough that we ensure both the P1 and P2 terms,
      -- which otherwise depend on a 'constant' ε₁ and ε₂, both converge to zero as well. We do this
      -- by looking at the max of the P1 and P2 terms.
      have this :=
        exists_liminf_zero_of_forall_liminf_limsup_le_with_UB (1 - ε) 0
        (fun x n ↦ ENNReal.ofNNReal ⟨(P1 x n).inner (ℰ n (ρ⊗^S[n])).M,
          HermitianMat.inner_ge_zero (HermitianMat.proj_le_nonneg _ _) (ℰ n (ρ⊗^S[n])).zero_le⟩)
        (fun x n ↦ ENNReal.ofNNReal ⟨(P2 x n).inner (ℰ n (ρ⊗^S[n])).M,
          HermitianMat.inner_ge_zero (HermitianMat.proj_le_nonneg _ _) (ℰ n (ρ⊗^S[n])).zero_le⟩)
        zero_lt_one ?_ ?_; rotate_left
      · --hliminfP1, up to stupid casting
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
          simp only [ge_iff_le, Filter.eventually_map, Filter.eventually_atTop,
            forall_exists_index]
          intro a x hx
          apply (hx x le_rfl).trans
          rw [← (ℰ x (ρ⊗^S[x])).tr, ← HermitianMat.one_inner]
          apply HermitianMat.inner_mono' (ℰ x (ρ⊗^S[x])).zero_le
          apply HermitianMat.proj_le_le_one
        · use 0
          simp only [ge_iff_le, Filter.eventually_map, Filter.eventually_atTop]
          use 0
          intro _ _
          apply HermitianMat.inner_ge_zero
          · apply HermitianMat.proj_le_nonneg
          · apply MState.zero_le
      · --hlimsupP2', up to stupid casting
        intro x hx
        specialize hlimsupP2' x hx
        apply le_of_eq at hlimsupP2'
        apply ENNReal.ofReal_mono at hlimsupP2'
        convert ← hlimsupP2' using 1
        dsimp
        conv =>
          enter [2, 1, n]
          exact (ENNReal.ofReal_eq_coe_nnreal _).symm
        swap
        · simp
        refine ENNReal.ofReal_mono.map_limsup_of_continuousAt _ ?_ ?_ ?_
        · apply ENNReal.continuous_ofReal.continuousAt
        · use 1
          simp only [ge_iff_le, Filter.eventually_map, Filter.eventually_atTop]
          use 0
          intro x hx
          rw [← (ℰ x (ρ⊗^S[x])).tr, ← HermitianMat.one_inner]
          apply HermitianMat.inner_mono' (ℰ x (ρ⊗^S[x])).zero_le
          apply HermitianMat.proj_le_le_one
        · use 0
          simp only [ge_iff_le, Filter.eventually_map, Filter.eventually_atTop,
            forall_exists_index]
          intro a x hx
          refine le_trans ?_ (hx x le_rfl)
          apply HermitianMat.inner_ge_zero
          · apply HermitianMat.proj_le_nonneg
          · apply MState.zero_le
      rcases this with ⟨ε2, hg₁, hg₂, hg₃, hliminf_g₁, hliminf_g₂⟩

      replace hDleq := Filter.liminf_le_liminf (Filter.Eventually.of_forall (f := .atTop) (fun (n : ℕ) ↦ hDleq (ε2 n) n))
      apply le_trans hDleq -- (S89)
      have hP2zero : Filter.atTop.Tendsto (fun n ↦ .ofReal ((P2 (ε2 n) n).inner (ℰ n (ρ⊗^S[n]))) *
          (.ofReal (c' (ε2 n) n) - (R2 ρ σ + .ofReal ε₀ + .ofReal (ε2 n)))) (𝓝 0) := by
        have hf : Filter.atTop.Tendsto (fun n ↦ .ofReal ((P2 (ε2 n) n).inner (ℰ n (ρ⊗^S[n])))) (𝓝 (0 : ℝ≥0∞)) := by
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
          · -- apply hliminfP1
            -- Alex: This is hard to prove with hliminfP1, because in hliminfP1 the ε2 is fixed inside
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
        field_simp [show 1 - ε.val ≠ 0 from ne_of_gt (sub_pos.mpr hε.2)]
        ring_nf
    rw [ENNReal.ofReal_mul (by simp), Prob.ofNNReal_toNNReal,
      ENNReal.ofReal_toReal (by simp [hR1, hR2]), Prob.coe_one_minus]

  use fun n ↦ ⟨σ' n, σ'_free n⟩
  rw [R2, hliminf]
  exact hliminfR

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
    Filter.atTop.Tendsto (fun n ↦ —log β_ ε(ρ⊗^S[n]‖IsFree) / n) (𝓝 (𝑅ᵣ∞ ρ)) := by

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
    set σ₁ : (n : ℕ) → IsFree (i := i ^ n) := fun n ↦
      ⟨(free_fullRank i).choose ⊗^S[n], IsFree.npow (free_fullRank i).choose_spec.2 n⟩ with hσ₁
    have hσ₁_top : R2 ρ σ₁ ≠ ⊤ := by
      rw [R2, ← Filter.liminf_nat_add _ 1]
      simp [σ₁, mul_comm _ (qRelativeEnt _ _)]
      conv =>
        enter [1,1,1,n]
        rw [ENNReal.mul_div_cancel_right (by positivity) (by finiteness)]
      simp [qRelativeEnt_ne_top (free_fullRank i).choose_spec.1]
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
      Set.Nonempty.of_subtype (f := fun σ ↦ 𝐃(ρ⊗^S[m]‖σ)) (by fun_prop)

    have hσₘ1 (m) := (σₘ_exists m).choose_spec.left
    have hσₘ2 (m) := (σₘ_exists m).choose_spec.right
    generalize σₘ_def : (fun m ↦ (σₘ_exists m).choose) = σₘ
    simp_rw [congrFun σₘ_def] at hσₘ1 hσₘ2
    clear σₘ_def σₘ_exists

    --Let σ₁ be the full-rank free state
    have ⟨σ₁, hσ₁_pos, hσ₁_free⟩ := FreeStateTheory.free_fullRank i

    --`h` is Eq (14)
    have h (m : ℕ) (hm : m ≥ 1) := Lemma6 hm ρ σ₁ (σₘ m) hσ₁_pos hε.2

    --Update `h` to Eq (15)
    have h₂ (m : ℕ) : (fun n ↦ —log β_ ε(ρ⊗^S[n]‖IsFree) / n) ≤ᶠ[Filter.atTop]
        (fun n ↦ —log β_ ε(ρ⊗^S[n]‖{(Lemma6_σn m σ₁ (σₘ m)) n}) / n) := by
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
      Filter.atTop.Tendsto (fun n ↦ —log β_ ε(ρ⊗^S[n]‖IsFree) / n) (𝓝 d)
      ∧
      Filter.atTop.Tendsto (fun n ↦ (⨅ σ ∈ IsFree, 𝐃(ρ⊗^S[n]‖σ)) / n) (𝓝 d)
      := by
  use 𝑅ᵣ∞ ρ -- Regularized relative entropy of resource (RegularizedRelativeEntResource) as an NNReal
  constructor
  · exact GeneralizedQSteinsLemma ρ hε -- Theorem 1 in Hayashi & Yamasaki
  · exact RelativeEntResource.tendsto_ennreal ρ -- The regularized relative entropy of resource is not infinity
