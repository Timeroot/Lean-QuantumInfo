import QuantumInfo.Finite.ResourceTheory.FreeState
import QuantumInfo.Finite.ResourceTheory.HypothesisTesting
import QuantumInfo.Finite.Pinching

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
  fun n ↦
    let l : ℕ := n / m
    let q : ℕ := (n % m)
    let σr := σf ⊗^S[q]
    if h : n < m then
      σr.relabel <| .cast <| congrArg (H <| i ^ ·) (by simp [q, Nat.mod_eq_of_lt h])
    else
      (σₘ ⊗^S[l] ⊗ᵣ σr).relabel <| .cast <| congrArg H (by
        rw [← pow_mul, ← spacePow_add, Nat.div_add_mod n m]
      )

theorem Lemma6_σn_IsFree {σ₁ : MState (H i)} {σₘ : (m : ℕ) → MState (H (i ^ m))} (hσ₁_free : IsFree σ₁)
    (hσₘ : ∀ (m : ℕ), σₘ m ∈ IsFree) (m n : ℕ) : Lemma6_σn m σ₁ (σₘ m) n ∈ IsFree := by
  rw [Lemma6_σn]
  split_ifs with hnm
  · rw [relabel_cast_isFree]
    · exact hσ₁_free.npow (n % m)
    · rw [Nat.mod_eq_of_lt hnm]
  · rw [relabel_cast_isFree]
    · apply free_prod --pick a better name / alias for this
      · exact (hσₘ m).npow (n / m)
      · exact hσ₁_free.npow (n % m)
    · rw [← pow_mul, ← spacePow_add, Nat.div_add_mod n m]

--PULLOUT.
--PR? This is "not specific to our repo", but might be a bit too specialized to be in Mathlib. Not sure.
--Definitely would need to clean up the proof first
theorem extracted_limsup_inequality (z : ℝ≥0∞) (hz : z ≠ ⊤) (y x : ℕ → ℝ≥0∞) (h_lem5 : ∀ (n : ℕ), x n ≤ y n + z)
    : Filter.atTop.limsup (fun n ↦ x n / n) ≤ Filter.atTop.limsup (fun n ↦ y n / n) := by
  --Thanks Aristotle
  simp_all [Filter.limsup_eq]
  -- Taking the limit superior of both sides of the inequality $x_n / n \leq y_n / n + z / n$, we get $\limsup_{n \to \infty} x_n / n \leq \limsup_{n \to \infty} (y_n / n + z / n)$.
  intro b n h_bn
  have h_le : ∀ m ≥ n, x m / (m : ℝ≥0∞) ≤ b + z / (m : ℝ≥0∞) := by
    intro m hm;
    refine' le_trans (ENNReal.div_le_div_right _ _ ) _
    exact y m + z
    · exact h_lem5 m
    · rw [ ENNReal.add_div ]
      exact add_le_add_right ( h_bn m hm ) _
  -- Since $z$ is finite, we have $\lim_{n \to \infty} z / n = 0$.
  have h_z_div_n_zero : Filter.atTop.Tendsto (fun n : ℕ ↦ z / (n : ℝ≥0∞)) (𝓝 0) := by
    rw [ ENNReal.tendsto_nhds_zero ]
    intro ε hε
    rcases ENNReal.lt_iff_exists_real_btwn.mp hε with ⟨ ε', hε₁, hε₂ ⟩
    simp_all only [ge_iff_le, gt_iff_lt, ENNReal.ofReal_pos, Filter.eventually_atTop]
    obtain ⟨left, right⟩ := hε₂
    -- Since $z$ is finite, we can choose $a$ such that for all $b \geq a$, $z \leq b \cdot \epsilon'$.
    obtain ⟨a, ha⟩ : ∃ a : ℕ, ∀ b : ℕ, a ≤ b → z ≤ b * ENNReal.ofReal ε' := by
      cases' ENNReal.lt_iff_exists_real_btwn.mp ( show z < ⊤ from lt_top_iff_ne_top.mpr hz ) with a ha
      simp_all only [ENNReal.ofReal_lt_top, and_true]
      obtain ⟨left_1, right_1⟩ := ha
      exact ⟨ ⌈a / ε'⌉₊, fun n hn ↦ le_trans right_1.le <| by rw [ ← ENNReal.ofReal_natCast ] ; rw [ ← ENNReal.ofReal_mul ( by positivity ) ] ; exact ENNReal.ofReal_le_ofReal <| by nlinarith [ Nat.ceil_le.mp hn, mul_div_cancel₀ a left.ne' ] ⟩
    -- Since $z \leq b \cdot \epsilon'$ for all $b \geq a$, dividing both sides by $b$ (which is positive) gives $z / b \leq \epsilon'$.
    use a + 1; intros b hb_ge; exact (by
    rw [ ENNReal.div_le_iff_le_mul ]
    · exact le_trans ( ha b ( by linarith ) ) ( by rw [ mul_comm ] ; gcongr )
    · aesop
    · norm_num)
  refine le_of_forall_pos_le_add fun ε ε_pos ↦ ?_
  rcases Filter.eventually_atTop.mp ( h_z_div_n_zero.eventually <| gt_mem_nhds ε_pos ) with ⟨ m, hm ⟩
  refine le_trans ( csInf_le ⟨ 0, ?_ ⟩ ⟨ n + m, fun n hn ↦ le_trans ( h_le _ <| by linarith ) <| add_le_add_left ( le_of_lt <| hm _ <| by linarith ) _ ⟩ ) <| by aesop
  rintro a ⟨ k, hk ⟩
  exact le_trans ( zero_le _ ) ( hk _ le_rfl )

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
    split_ifs with hnm
    · have hnm_div : n / m = 0 := Nat.div_eq_of_lt hnm
      have hnm_mod : n % m = n := Nat.mod_eq_of_lt hnm
      simp [hnm_div, hnm_mod, statePow_rw hnm_mod]
    · have hnm_add := Nat.div_add_mod n m
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
    · unfold SandwichedRelRentropy
      split
      · simp
      · --TODO this should actually be a theorem in Entropy.lean
        simpa [qRelativeEnt]
    · --The sandwiched relative Renyi entropy is continuous in α (at least, at α = 1).
      have _ := ENNReal.continuous_div_const m (by positivity)
      have _ := (SandwichedRelRentropy.continuousOn (ρ⊗^S[m]) σₘ).continuousAt (Ioi_mem_nhds zero_lt_one)
      fun_prop

  exact h_α

section Lemma7

open MatrixMap
open Matrix

variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut] {R : Type*}

-- TODO: Commutation and order relations about `proj_le` specified in the text
-- between Eqs. (S77) and (S78)

open scoped HermitianMat in
theorem LemmaS2 {ε3 : Prob} {ε4 : ℝ≥0} (hε4 : 0 < ε4)
  {d : ℕ → Type*} [∀ n, Fintype (d n)] [∀ n, DecidableEq (d n)] (ρ : (n : ℕ) → MState (d n)) (σ : (n : ℕ) → MState (d n))
  {Rinf : ℝ≥0} (hRinf : Rinf ≥ Filter.atTop.liminf (fun (n : ℕ) ↦ —log β_ ε3(ρ n‖{σ n}) / n))
  {Rsup : ℝ≥0} (hRsup : Rsup ≥ Filter.atTop.limsup (fun (n : ℕ) ↦ —log β_ ε3(ρ n‖{σ n}) / n))
  :
  (Filter.atTop.liminf (fun (n : ℕ) ↦ {(ρ n).M ≥ₚ (Real.exp (n * (Rinf + ε4))) • (σ n).M}.inner (ρ n)) ≤ 1 - ε3) ∧
  (Filter.atTop.limsup (fun (n : ℕ) ↦ {(ρ n).M ≥ₚ (Real.exp (n * (Rsup + ε4))) • (σ n).M}.inner (ρ n)) ≤ 1 - ε3)
  := by
  constructor
  · by_contra h
    push_neg at h
    replace h := Filter.eventually_lt_of_lt_liminf h ?_
    · replace h := Filter.eventually_atTop.mp h
      obtain ⟨n₀, h⟩ := h
      --Can assume that n₀ is positive. Then we don't have to worry about nonzero values down the line
      wlog hn₀ : 0 < n₀
      · exact this hε4 ρ σ hRinf hRsup 1 (fun b hb ↦ h _ <| by omega) zero_lt_one
      let T (n : ℕ) := {(ρ n).M ≥ₚ (Real.exp (n * (Rinf + ε4))) • (σ n).M}
      have hT : ∀ n ≥ n₀, (ρ n).exp_val (1 - (T n)) ≤ ε3 := fun n hn ↦ by -- Eq (S23)
        unfold MState.exp_val T
        rw [HermitianMat.inner_left_sub, HermitianMat.inner_one, MState.tr,
          HermitianMat.inner_comm, tsub_le_iff_right, add_comm, ← tsub_le_iff_right]
        apply le_of_lt
        exact h n hn
      have hβ : ∀ n ≥ n₀, β_ ε3(ρ n‖{σ n}) ≤ Real.exp (-n * (Rinf + ε4)) := fun n hn ↦ by -- Eq (S25)
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
    exact MState.exp_val_nonneg (proj_le_nonneg (Real.exp (n * (Rinf + ε4)) • (σ n).M) (ρ n).M) (ρ n)
  · -- Basically the same proof as the Rinf case, but with liminf → limsup, ∀ᶠ → ∃ᶠ, etc.
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
    exact MState.exp_val_nonneg (proj_le_nonneg (Real.exp (n * (Rsup + ε4)) • (σ n).M) (ρ n).M) (ρ n)

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
  rw [← Real.log_exp (-(f n))]
  rw [← Real.log_mul (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  simp only [Prob.coe_iInf]
  rw [Real.mul_iInf_of_nonneg (by positivity)]
  apply ciInf_mono
  · use 0
    simp_rw [lowerBounds, Set.mem_range]
    rintro a ⟨y, rfl⟩
    have : 0 ≤ (σ₂ n).exp_val y := by
      apply MState.exp_val_nonneg y.2.2.1
    positivity
  intro ⟨x, hx₁, hx₂, hx₃⟩
  simp only [MState.exp_val] --dunno why `rw` won't rewrite the second one
  rw [← HermitianMat.smul_inner]
  --There should be an `inner_mono'` which is inner_mono in the other arguments
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
  · refine Filter.liminf_le_liminf ?_
    apply Filter.Eventually.of_forall
    intro x
    gcongr
    exact LemmaS3_helper _ _ _ _ hσ x
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
  · refine Filter.limsup_le_limsup ?_
    apply Filter.Eventually.of_forall
    intro x
    dsimp
    gcongr
    exact LemmaS3_helper _ _ _ _ hσ x
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
    · simp only [le_top, exists_const]
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

  -- m exists because R2 + ε₀ is strictly above R2, which is the liminf.
  obtain ⟨m, hm⟩ :=
    have h : R2 ρ σ < R2 ρ σ + .ofNNReal ⟨ε₀, hε₀.le⟩ :=
      ENNReal.lt_add_right hR2 (by simp [← NNReal.coe_eq_zero, hε₀.ne'])
    (Filter.frequently_lt_of_liminf_lt (h := h)).exists

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
    sorry

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
  let σ''_unnormalized (n) : HermitianMat (H (i ^ n)) ℂ := --TODO: Define a HermitianMat.cfc function that behaves nicely
    (σ' n).M.cfc fun e ↦ Real.exp (f n e)

  have σ''_unnormalized_PosDef (n) : Matrix.PosDef (σ''_unnormalized n).val := by
    dsimp [σ''_unnormalized]
    rw [HermitianMat.cfc_PosDef]
    intro
    positivity

  have σ''_tr_bounds (n) : 1 ≤ (σ''_unnormalized n).trace ∧ (σ''_unnormalized n).trace ≤ Real.exp (c n) := by
    sorry

  --Then σ'' is the normalized version, which will work because σ''_unnormalized is PosDef
  let σ'' (n) : MState (H (i ^ n)) := {
    --TODO make this its own definition
    M := (σ''_unnormalized n).trace⁻¹ • (σ''_unnormalized n)
    zero_le := sorry
    tr := sorry
  }

  have σ'_le_σ'' (n) : Real.exp (-(c n)) • (σ' n).M ≤ σ'' n := by
    sorry
  have σ''_le_σ' (n) : σ'' n ≤ Real.exp (c n) • (σ' n).M := by
    sorry

  have qRel_σ''_le_σ' (n) : 𝐃(ρ⊗^S[n]‖σ'' n) ≤ 𝐃(ρ⊗^S[n]‖σ' n) + ENNReal.ofReal (c n) := by
    sorry

  have qRel_σ'_le_σ'' (n) : 𝐃(ρ⊗^S[n]‖σ' n) ≤ 𝐃(ρ⊗^S[n]‖σ'' n) + ENNReal.ofReal (c n) := by
    sorry

  -- Definition of the pinching map w.r.t. σ'' in Eq. (S55)
  let ℰ (n) := pinching_map (σ'' n)

  -- Number of distinct eigenvalues of σ'' in Eq. (S56) is
  -- Fintype.card (spectrum ℝ (σ'' n).m), which is dₙ in the paper.
  have hdle : ∀ n, Fintype.card (spectrum ℝ (σ'' n).m) ≤ n + 1 := by
    sorry
  have hdpos : ∀ n, 0 < Fintype.card (spectrum ℝ (σ'' n).m) := by
    sorry

  -- Eq (S59) has a minus sign, which gets complicated when one of the relative entropies is infinite.
  -- However, I don't think we need this version with the minus sign
  -----
  -- have rel_ent_pinching (n) : 𝐃(ρ⊗^S[n]‖ℰ n (ρ⊗^S[n])) = 𝐃(ρ⊗^S[n]‖σ'' n) - 𝐃(ℰ n (ρ⊗^S[n])‖σ'' n) := by
  --   unfold ℰ
  --   rw [pinching_pythagoras (ρ⊗^S[n]) (σ'' n)]
  --   have hDfin : 𝐃((pinching_map (σ'' n)) (ρ⊗^S[n])‖σ'' n) ≠ ∞ := by
  --     sorry
  --   rw [← ENNReal.coe_toNNReal hDfin]
  --   simp only [ENNReal.addLECancellable_iff_ne, ne_eq, ENNReal.coe_ne_top, not_false_eq_true,
  --     AddLECancellable.add_tsub_cancel_right]
  have qRel_pinching_pythagoras (n) : 𝐃(ρ⊗^S[n]‖σ'' n) = 𝐃(ρ⊗^S[n]‖ℰ n (ρ⊗^S[n])) + 𝐃(ℰ n (ρ⊗^S[n])‖σ'' n) := by
    unfold ℰ
    exact pinching_pythagoras (ρ⊗^S[n]) (σ'' n)

  -- Eq. (S60)
  have qRel_ent_bound (n) : 𝐃(ρ⊗^S[n]‖ℰ n (ρ⊗^S[n])) ≤ ENNReal.ofReal (Real.log (n + 1)) := calc
    𝐃(ρ⊗^S[n]‖ℰ n (ρ⊗^S[n])) ≤ ENNReal.ofReal (Real.log (Fintype.card (spectrum ℝ (σ'' n).m))) := by
      unfold ℰ
      exact qRelativeEnt_op_le (by simp only [Nat.cast_pos, hdpos n])
                               (pinching_bound (ρ⊗^S[n]) (σ'' n))
    _ ≤ ENNReal.ofReal (Real.log (n + 1)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.log_le_log
      · simp only [Nat.cast_pos, hdpos n]
      · norm_cast
        exact hdle n

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

  -- Eq. (S62)
  have hliminfR : Filter.atTop.liminf (fun n ↦ 𝐃(ℰ n (ρ⊗^S[n])‖σ'' n) / n) - R1 ρ ε ≤
      ↑(1 - ε') * (R2 ρ σ - R1 ρ ε) := by
    sorry

  use fun n ↦ ⟨σ' n, σ'_free n⟩
  rw [R2]
  dsimp only
  rw [← hliminf] at hliminfR
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
    have σₘ_exists (m : ℕ) := IsCompact_IsFree.exists_isMinOn Set.Nonempty.of_subtype
      (f := fun σ ↦ 𝐃(ρ⊗^S[m]‖σ)) (by fun_prop)

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

/-- Theorem 4, which is _also_ called the Generalized Quantum Stein's Lemma in Hayashi & Yamasaki.
What they state as an equality of limits (which don't exist per se in Mathlib), we state as their
existing a number (which happens to be `RegularizedRelativeEntResource`) which both sides converge to.
-/
theorem limit_hypotesting_eq_limit_rel_entropy (ρ : MState (H i)) (ε : Prob) (hε : 0 < ε ∧ ε < 1) :
    ∃ d : ℝ≥0,
      Filter.atTop.Tendsto (fun n ↦ —log β_ ε(ρ⊗^S[n]‖IsFree) / n) (𝓝 d)
      ∧
      Filter.atTop.Tendsto (fun n ↦ (⨅ σ ∈ IsFree, 𝐃(ρ⊗^S[n]‖σ)) / n) (𝓝 d)
      := by
  use 𝑅ᵣ∞ ρ
  constructor
  · exact GeneralizedQSteinsLemma ρ hε
  · exact RelativeEntResource.tendsto_ennreal ρ
