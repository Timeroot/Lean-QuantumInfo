import QuantumInfo.Finite.ResourceTheory.FreeState
import QuantumInfo.Finite.ResourceTheory.HypothesisTesting

import Mathlib.Tactic.Bound

open NNReal
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

--Move to FreeState.lean
/-- In a `FreeStateTheory`, we have free states of full rank, therefore the minimum relative entropy
of any state `ρ` to a free state is finite. -/
lemma min_free_relent_finite (ρ : MState (H i)) : ⨅ σ ∈ IsFree, 𝐃(ρ‖σ) ≠ ⊤ := by
  simp only [ne_eq, iInf_eq_top, not_forall, Classical.not_imp]
  obtain ⟨σ, hσ₁, hσ₂⟩ := FreeStateTheory.free_fullRank i
  use σ, hσ₂
  rw [qRelativeEnt]
  split_ifs with h
  · simp --should be `finiteness`, TODO debug
  contrapose! h
  convert bot_le
  exact hσ₁.toLin_ker_eq_bot

--PULLOUT
theorem WithTop.untop_eq_untopD {α : Type*} {a : WithTop α} (h : a ≠ ⊤) (d : α) :
    WithTop.untop a h = WithTop.untopD d a := by
  cases a
  · contradiction
  · simp

-- This theorem should follow from "Fekete's subadditive lemma", which can be found in
-- Lemma A.1 of Hayashi's book "Quantum Information Theory - Mathematical Foundation".
--
-- Also, the sequence of states S^(n) mentioned in the paper is implicitly defined here as
-- IsFree (i := i⊗^[n]). It has all the properties we need plus some more (e.g., for this
-- lemma, we don't need convexity).
/-- Lemma 5 -/
theorem limit_rel_entropy_exists (ρ : MState (H i)) :
  ∃ d : ℝ≥0,
    Filter.Tendsto (fun n ↦ (↑n)⁻¹ * ⨅ σ ∈ IsFree (i := i ^ n), 𝐃(ρ⊗^S[n]‖σ))
    .atTop (𝓝 d) := by
  --Fekete's subadditive lemma is in Mathlib:
  have h := (RelativeEntResource.Subadditive ρ)
  have h_bdd : BddBelow (Set.range fun n => (RelativeEntResource (ρ⊗^S[n])).toReal / ↑n) := by
    use 0
    intro x hx
    simp only [Set.mem_range, RelativeEntResource] at hx
    obtain ⟨y, rfl⟩ := hx
    positivity
  have := h.tendsto_lim h_bdd
  use h.lim.toNNReal
  convert this
  /-
  We need to change `this`, which is `@Filter.Tendsto ℕ ℝ`, into our goal, which is
  `@Filter.Tendsto ℕ ENNReal`. This probably needs two steps, one where we go from ℝ to NNReal,
  and then one more from NNReal to ENNReal. Some lemmas that
  might be useful:
  - `Topology.IsClosedEmbedding.tendsto_nhds_iff`
  - `Topology.IsEmbedding.tendsto_nhds_iff`
  - `Filter.tendsto_congr`
  - `tendsto_subtype_rng` (note that `NNReal` is defeq to a `Subtype ℝ`)
  -/
  sorry

/-- The \tilde{σ}_n defined in Lemma 6, also in equation (S40) in Lemma 7.
I've slightly changed the definition here: instead of `n / m` and `n % m`, I use `(n-1) / m` and `(n-1)%m + 1`.
This means that we only ever need ℕ+ powers of states. It *would* be fine to just add the requirement to our
notion of `ResourcePretheory` that we have a 0-dimensional space, so that we can take ℕ powers; or we could
express this with if-statements (e.g. `if m ∣ n then σₘ ⊗^ [ n / m ] else (...) ⊗ᵣ (...)`) but that's messier
to work with. This altered definition is easier to work with and still has all the properties we need. We still
need one `if` statement for when `n ≤ m`, sadly.
-/
noncomputable def Lemma6_σn (m : ℕ) (σf : MState (H i)) (σₘ : MState (H (i ^ m))) : (n : ℕ) → MState (H (i ^ n)) :=
  fun n ↦
    --This needs to be reworked to be compatible with the FreeStateTheory framework.
    let l : ℕ := n / m
    let q : ℕ := (n % m)
    let σr := σf ⊗^S[q]
    if h : n < m then
      σr.relabel <| .cast <| congrArg (H <| i ^ ·) (by simp [q, Nat.mod_eq_of_lt h])
    else
      let σl := σₘ ⊗^S[l]
      (σl ⊗ᵣ σr).relabel <| .cast <| congrArg H (by
        rw [← pow_mul, ← spacePow_add, Nat.div_add_mod n m]
      )

theorem Lemma6_σn_IsFree {σ₁ : MState (H i)} {σₘ : (m : ℕ) → MState (H (i ^ m))} (hσ₁_free : IsFree σ₁)
    (hσₘ1 : ∀ (m : ℕ), σₘ m ∈ IsFree) (m n : ℕ) : Lemma6_σn m σ₁ (σₘ m) n ∈ IsFree := by
  sorry

/-- Lemma 6 from the paper -/
private theorem Lemma6 (m : ℕ) (ρ σf : MState (H i)) (σₘ : MState (H (i ^ m))) (hσf : σf.m.PosDef) (ε : Prob)
    (hε : 0 < ε)
    (hε' : ε < 1) --Not stated in the paper's theorem statement but I think is necessary for the argument to go through
    :
    Filter.atTop.limsup (fun (n : ℕ) ↦ (↑n)⁻¹ * —log β_ ε(ρ⊗^S[n]‖{Lemma6_σn m σf σₘ n})) ≤
    (↑m)⁻¹ * 𝐃(ρ⊗^S[m]‖σₘ)
  := by

  have h_add : ∀ α n, D̃_ α(ρ⊗^S[n]‖Lemma6_σn m σf σₘ n) = (n/m : ℕ) * D̃_ α(ρ⊗^S[m]‖σₘ) + (n%m : ℕ) * D̃_ α(ρ‖σf):= by
    --"Break apart" σn, and apply additivity of `SandwichedRelRentropy`.
    sorry

  stop
  --This will probably need 1 < α actually
  have h_α : ∀ α, (1 < α) → Filter.atTop.limsup (fun n ↦ —log β_ ε(ρ⊗^n‖{σn n}) / n) ≤
      D̃_ α(ρ⊗^m‖σn m) / m := by
    intro α hα
    apply le_of_le_of_eq (b := Filter.atTop.limsup (fun n ↦ D̃_ α(ρ⊗^n‖σn n) / n))
    · --Apply the "[81] Lemma 5" to ρ⊗^n and σn
      have h_lem5 :=
        fun (n:ℕ) ↦ Ref81Lem5 (ρ⊗^n) (σn n) ε α ⟨hε.le,hε'⟩ hα

      --Upper-bound β on the LHS with this lemma
      --Distribute the limsup over subtraction
      --The term on the right is a constant, divided by n, which converges to zero.
      --Dropping that leaves the identity
      sorry

    · suffices Filter.Tendsto (fun n => D̃_ α(ρ⊗^n‖σn n) * ((↑n)⁻¹)) .atTop (𝓝 (D̃_ α(ρ⊗^m‖σn m) / m))by
        exact Filter.Tendsto.limsup_eq this
      conv =>
        enter [1,n]
        equals ( (↑(n / m) * D̃_ α(ρ⊗^m‖σₘ)) * ((↑n)⁻¹) + (↑(n % m) * D̃_ α(ρ‖σf)) * ((↑n)⁻¹)) =>
          simp_rw [h_add, right_distrib]
      conv => enter [3,1]; apply (add_zero _).symm
      apply Filter.Tendsto.add
      · simp_rw [mul_comm, ← mul_assoc]
        simp only [h_add, Nat.mod_self, CharP.cast_eq_zero, zero_mul, add_zero, Nat.div_self hm, Nat.cast_one, one_mul]
        conv =>
          enter [3,1]
          apply (one_mul _).symm
        rw [← ENNReal.mul_comm_div]
        cases D̃_ α(ρ⊗^m‖σₘ)
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
          suffices Filter.Tendsto (fun x => (x:ℝ)⁻¹ * ↑(x / m) * (v:ℝ) : ℕ → ℝ) Filter.atTop (𝓝 ((1 / ↑m) * (v : ℝ))) by
            --Similar to the "convert ENNReal.tendsto_ofReal this" below. Just push casts through
            sorry
          apply Filter.Tendsto.mul ?_ tendsto_const_nhds
          --Should be an easy fact from here: x * (x/m) converges to 1/m.
          sorry
      · suffices Filter.Tendsto (fun x => ↑(x % m) * (D̃_ α(ρ‖σf)).toReal * (↑x)⁻¹) Filter.atTop (𝓝 0) by
          --Convert a Tendsto over ENNReal to one over Real
          convert ENNReal.tendsto_ofReal this
          · rename_i x
            cases x
            · simp
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
            congr
            · simp
            · refine Eq.symm (ENNReal.ofReal_toReal ?_)
              --This should be a lemma - that D̃_α(ρ‖σ) is nonzero when σ is PosDef.
              sorry
            · rw [ENNReal.ofReal_inv_of_pos (by positivity)]
              simp only [Nat.cast_add, Nat.cast_one, inv_inj]
              rw [ENNReal.ofReal_add (by positivity) (zero_le_one' ℝ)]
              simp
          · simp
        apply bdd_le_mul_tendsto_zero (b := 0) (B := m * D̃_ α(ρ‖σf).toReal)
        · exact Filter.Eventually.of_forall (fun _ ↦ by positivity)
        · apply Filter.Eventually.of_forall (fun _ ↦ ?_)
          exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.mod_lt _ hm).le) (by positivity)
        · exact tendsto_inverse_atTop_nhds_zero_nat

  --Take the limit as α → 1.
  sorry

/-- Theorem 4, which is _also_ called the Generalized Quantum Stein's Lemma in Hayashi & Yamasaki -/
theorem limit_hypotesting_eq_limit_rel_entropy (ρ : MState (H i)) (ε : Prob) (hε : 0 < ε ∧ ε < 1) :
    ∃ d : ℝ≥0,
      Filter.Tendsto (fun n ↦ —log β_ ε(ρ⊗^S[n]‖IsFree) / n)
      .atTop (𝓝 d)
      ∧
      Filter.Tendsto (fun n ↦ (↑n)⁻¹ * ⨅ σ ∈ IsFree, 𝐃(ρ⊗^S[n]‖σ))
      .atTop (𝓝 d)
      := by
  sorry

section Lemma7

open MatrixMap
open Matrix

variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut] {R : Type*}

-- TODO: Commutation and order relations about `proj_le` specified in the text
-- between Eqs. (S77) and (S78)

open scoped HermitianMat in
theorem LemmaS2 {ε3 : Prob} {ε4 : ℝ≥0} (hε4 : 0 < ε4)
  {d : PNat → Type*} [∀ n, Fintype (d n)] [∀ n, DecidableEq (d n)] (ρ : (n : PNat) → MState (d n)) (σ : (n : PNat) → MState (d n))
  {Rinf : ℝ≥0} (hRinf : ↑Rinf ≥ Filter.liminf (fun n ↦ (↑n)⁻¹ * —log β_ ε3(ρ n‖{σ n})) Filter.atTop)
  {Rsup : ℝ≥0} (hRsup : ↑Rsup ≥ Filter.limsup (fun n ↦ (↑n)⁻¹ * —log β_ ε3(ρ n‖{σ n})) Filter.atTop)
  :
  (Filter.liminf (fun n ↦ {(ρ n).M ≥ₚ (Real.exp (↑n * (Rinf + ε4))) • (σ n).M}.inner (ρ n)) Filter.atTop ≤ 1 - ε3) ∧
  (Filter.limsup (fun n ↦ {(ρ n).M ≥ₚ (Real.exp (↑n * (Rsup + ε4))) • (σ n).M}.inner (ρ n)) Filter.atTop ≤ 1 - ε3)
  := by
  constructor
  · by_contra h
    push_neg at h
    replace h := Filter.eventually_lt_of_lt_liminf h ?_
    · replace h := Filter.eventually_atTop.mp h
      obtain ⟨n₀, h⟩ := h
      let T := fun n ↦ {(ρ n).M ≥ₚ (Real.exp (↑n * (Rinf + ε4))) • (σ n).M}
      have hT : ∀ n ≥ n₀, (ρ n).exp_val (1 - (T n)) ≤ ε3 := fun n hn ↦ by -- Eq (S23)
        unfold MState.exp_val T
        rw [HermitianMat.inner_left_sub, HermitianMat.inner_one, MState.tr,
          HermitianMat.inner_comm, tsub_le_iff_right, add_comm, ←tsub_le_iff_right]
        apply le_of_lt
        exact h n hn
      have hβ : ∀ n ≥ n₀, β_ ε3(ρ n‖{σ n}) ≤ Real.exp (-↑n * (Rinf + ε4)) := fun n hn ↦ by -- Eq (S25)
        calc
          β_ ε3(ρ n‖{σ n}) ≤ (σ n).exp_val (T n) := by
            have hβ' := OptimalHypothesisRate.singleton_le_exp_val (σ := σ n) (T n) (hT n hn) ⟨proj_le_nonneg _ _, proj_le_le_one _ _⟩
            simp only [Subtype.coe_le_coe.mpr hβ']
          _ <= (T n).inner (Real.exp (-↑n * (Rinf + ε4)) • (ρ n).M) := by
            rw [← mul_le_mul_left (Real.exp_pos ((↑n * (Rinf + ε4)))), HermitianMat.inner_smul, neg_mul, Real.exp_neg]
            simp only [isUnit_iff_ne_zero, ne_eq, Real.exp_ne_zero, not_false_eq_true,
              IsUnit.mul_inv_cancel_left]
            rw [MState.exp_val, HermitianMat.inner_comm, ←HermitianMat.inner_smul]
            unfold T
            exact proj_le_inner_le (Real.exp (↑n * (Rinf + ε4)) • (σ n).M) (ρ n).M
          _ <= Real.exp (-↑n * (Rinf + ε4)) := by
            simp [HermitianMat.inner_smul]
            rw [mul_comm]
            apply (mul_le_iff_le_one_left (Real.exp_pos (-(↑n * (Rinf + ε4))))).mpr
            rw [HermitianMat.inner_comm, ←MState.exp_val]
            exact MState.exp_val_le_one (proj_le_le_one _ _) (ρ n)
      have h' : ∀ n ≥ n₀, ↑Rinf + ↑ε4 ≤ (↑n)⁻¹ * —log β_ ε3(ρ n‖{σ n}):= fun n hn↦ by -- Eq (S26)
        have hn1 : (↑↑n : ENNReal) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true]
        have hn2 : (↑↑n : ENNReal) ≠ ⊤ := by simp only [ne_eq, ENNReal.natCast_ne_top, not_false_eq_true]
        have hh : ↑↑n * (↑Rinf + ↑ε4) = ENNReal.ofReal (n *(Rinf + ε4)) := by
          simp only [Nat.cast_nonneg, ENNReal.ofReal_mul, ENNReal.ofReal_natCast, zero_le_coe,
            ENNReal.ofReal_add, ENNReal.ofReal_coe_nnreal]
        apply (ENNReal.mul_le_mul_left (a := ↑↑n) (b := ↑Rinf + ↑ε4) (c := (↑n)⁻¹ * —log β_ ε3(ρ n‖{σ n})) hn1 hn2).mp
        rw [←mul_assoc, ENNReal.mul_inv_cancel hn1 hn2, one_mul, hh]
        apply Prob.le_negLog_of_le_exp
        rw [←neg_mul]
        exact hβ n hn
      have hf : ∀ᶠ (n : ℕ+) in Filter.atTop, ↑Rinf + ↑ε4 ≤ (↑n)⁻¹ * —log β_ ε3(ρ n‖{σ n}) := by
        rw [Filter.eventually_atTop]
        use n₀
      replace hf := Filter.le_liminf_of_le ?_ hf
      · replace hf := le_trans hf hRinf
        replace hf :=  tsub_eq_zero_iff_le.mpr hf
        simp_all
      apply Filter.IsCobounded.of_frequently_le (u := ⊤)
      simp [Filter.frequently_atTop]
      intro n; use n
    apply Filter.isBoundedUnder_of
    use 0; intro n
    rw [HermitianMat.inner_comm, ←MState.exp_val, ge_iff_le]
    exact MState.exp_val_nonneg (proj_le_nonneg (Real.exp (↑↑n * (↑Rinf + ↑ε4)) • (σ n).M) (ρ n).M) (ρ n)
  · -- Basically the same proof as the Rinf case, but with liminf → limsup, ∀ᶠ → ∃ᶠ, etc.
    by_contra h
    push_neg at h
    replace h := Filter.frequently_lt_of_lt_limsup ?_ h
    · replace h := Filter.frequently_atTop.mp h
      let T := fun n ↦ {(ρ n).M ≥ₚ (Real.exp (↑n * (Rsup + ε4))) • (σ n).M}
      have hT : ∀ n₀, ∃ n ≥ n₀, (ρ n).exp_val (1 - (T n)) ≤ ε3 := fun n₀ ↦ by -- Eq (S30)
        obtain ⟨n, ⟨hn, h⟩⟩ := h n₀
        use n; use hn
        unfold MState.exp_val T
        rw [HermitianMat.inner_left_sub, HermitianMat.inner_one, MState.tr,
          HermitianMat.inner_comm, tsub_le_iff_right, add_comm, ←tsub_le_iff_right]
        apply le_of_lt
        exact h
      have hβ : ∀ n₀, ∃ n ≥ n₀, β_ ε3(ρ n‖{σ n}) ≤ Real.exp (-↑n * (Rsup + ε4)) := fun n₀ ↦ by -- Eq (S32)
        obtain ⟨n, ⟨hn, hT⟩⟩ := hT n₀
        use n; use hn
        calc
          β_ ε3(ρ n‖{σ n}) ≤ (σ n).exp_val (T n) := by
            have hβ' := OptimalHypothesisRate.singleton_le_exp_val (σ := σ n) (T n) hT ⟨proj_le_nonneg _ _, proj_le_le_one _ _⟩
            simp only [Subtype.coe_le_coe.mpr hβ']
          _ <= (T n).inner (Real.exp (-↑n * (Rsup + ε4)) • (ρ n).M) := by
            rw [← mul_le_mul_left (Real.exp_pos ((↑n * (Rsup + ε4)))), HermitianMat.inner_smul, neg_mul, Real.exp_neg]
            simp only [isUnit_iff_ne_zero, ne_eq, Real.exp_ne_zero, not_false_eq_true,
              IsUnit.mul_inv_cancel_left]
            rw [MState.exp_val, HermitianMat.inner_comm, ←HermitianMat.inner_smul]
            unfold T
            exact proj_le_inner_le (Real.exp (↑n * (Rsup + ε4)) • (σ n).M) (ρ n).M
          _ <= Real.exp (-↑n * (Rsup + ε4)) := by
            simp [HermitianMat.inner_smul]
            rw [mul_comm]
            apply (mul_le_iff_le_one_left (Real.exp_pos (-(↑n * (Rsup + ε4))))).mpr
            rw [HermitianMat.inner_comm, ←MState.exp_val]
            exact MState.exp_val_le_one (proj_le_le_one _ _) (ρ n)
      have h' : ∀ n₀, ∃ n ≥ n₀, ↑Rsup + ↑ε4 ≤ (↑n)⁻¹ * —log β_ ε3(ρ n‖{σ n}):= fun n₀ ↦ by -- Eq (S33)
        obtain ⟨n, ⟨hn, hβ⟩⟩ := hβ n₀
        use n; use hn
        have hn1 : (↑↑n : ENNReal) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true]
        have hn2 : (↑↑n : ENNReal) ≠ ⊤ := by simp only [ne_eq, ENNReal.natCast_ne_top, not_false_eq_true]
        have hh : ↑↑n * (↑Rsup + ↑ε4) = ENNReal.ofReal (n *(Rsup + ε4)) := by
          simp only [Nat.cast_nonneg, ENNReal.ofReal_mul, ENNReal.ofReal_natCast, zero_le_coe,
            ENNReal.ofReal_add, ENNReal.ofReal_coe_nnreal]
        apply (ENNReal.mul_le_mul_left (a := ↑↑n) (b := ↑Rsup + ↑ε4) (c := (↑n)⁻¹ * —log β_ ε3(ρ n‖{σ n})) hn1 hn2).mp
        rw [←mul_assoc, ENNReal.mul_inv_cancel hn1 hn2, one_mul, hh]
        apply Prob.le_negLog_of_le_exp
        rw [←neg_mul]
        exact hβ
      have hf : ∃ᶠ (n : ℕ+) in Filter.atTop, ↑Rsup + ↑ε4 ≤ (↑n)⁻¹ * —log β_ ε3(ρ n‖{σ n}) := by
        rw [Filter.frequently_atTop]
        exact h'
      replace hf := Filter.le_limsup_of_frequently_le hf ?_
      · replace hf := le_trans hf hRsup
        replace hf :=  tsub_eq_zero_iff_le.mpr hf
        simp_all
      apply Filter.isBoundedUnder_of
      use ⊤; intro n
      exact le_top
    apply Filter.isCoboundedUnder_le_of_le Filter.atTop (x := 0)
    intro n
    rw [HermitianMat.inner_comm, ←MState.exp_val]
    exact MState.exp_val_nonneg (proj_le_nonneg (Real.exp (↑↑n * (↑Rsup + ↑ε4)) • (σ n).M) (ρ n).M) (ρ n)

private theorem LemmaS3_helper {ε : Prob} {d : ℕ+ → Type*} [∀ n, Fintype (d n)] [∀ n, DecidableEq (d n)]
  (ρ σ₁ σ₂ : (n : ℕ+) → MState (d n))
  (f : ℕ+ → ℝ≥0) (hσ : ∀ (i : ℕ+), Real.exp (-f i) • (σ₂ i).M ≤ (σ₁ i)) (n : ℕ+) :
    —log β_ ε(ρ n‖{σ₁ n}) ≤ —log β_ ε(ρ n‖{σ₂ n}) + ↑(f n) := by
  have h₁ (T : HermitianMat (d n) ℂ) (hT : 0 ≤ T) :
          Real.exp (-f n) * T.inner (σ₂ n).M ≤ T.inner (σ₁ n).M := by
    simpa using HermitianMat.inner_mono hT _ _ (hσ n)
  by_cases hσ₂ : β_ ε(ρ n‖{σ₂ n}) = 0
  · simp [hσ₂]
  replace hσ₂ := Prob.zero_lt_coe hσ₂
  have hσ₁ : (0 : ℝ) < β_ ε(ρ n‖{σ₁ n}) := by
    refine OptimalHypothesisRate.rate_pos_of_smul_pos hσ₂ (Real.exp_pos (-↑(f n))) ?_
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
  rw [HermitianMat.inner_comm _ x, HermitianMat.inner_comm _ x]
  apply HermitianMat.inner_mono hx₂ _ _ (hσ n)

/-- Lemma S3 from the paper. What they denote as σₙ and σₙ', we denote as σ₁ and σ₂. The `exp(-o(n))`
we express as a function `f : ℕ+ → ℝ`, together with the fact that `f` is little-o of `n` (i.e. that
`f =o[.atTop] id`), and then writing `exp(-f)`. We also split LemmaS3 into two parts, the `lim inf` part
and the `lim sup` part. The theorem as written is true for any `f`, but we can restrict to nonnegative
`f` (so, `ℕ+ → ℝ≥0`) which is easier to work with and more natural in the subsequent proofs. -/
private theorem LemmaS3_inf {ε : Prob}
    {d : ℕ+ → Type*} [∀ n, Fintype (d n)] [∀ n, DecidableEq (d n)]
    (ρ σ₁ σ₂ : (n : ℕ+) → MState (d n))
    (f : ℕ+ → ℝ≥0) (hf : (f · : ℕ+ → ℝ) =o[.atTop] (· : ℕ+ → ℝ))
    (hσ : ∀ i, Real.exp (-f i) • (σ₂ i).M ≤ σ₁ i)
    :
    Filter.liminf (fun (n : ℕ+) ↦ (↑n)⁻¹ * —log β_ ε(ρ n‖{σ₁ n})) Filter.atTop ≤
      Filter.liminf (fun (n : ℕ+) ↦ (↑n)⁻¹ * —log β_ ε(ρ n‖{σ₂ n})) Filter.atTop
    := by
  --Starting with `helper`, divide by n and take the limits. Since f is o(n),
  --the (↑n)⁻¹ * f n term will go to zero.
  trans Filter.liminf (fun n => (↑↑n)⁻¹ * (—log β_ ε(ρ n‖{σ₂ n}) + ↑(f n))) Filter.atTop
  · refine Filter.liminf_le_liminf ?_
    apply Filter.Eventually.of_forall
    intro x
    gcongr
    exact LemmaS3_helper _ _ _ _ hσ x
  · apply le_of_eq
    simp_rw [mul_add]
    apply Filter.liminf_add_tendsTo_zero
    convert Asymptotics.IsLittleO.tendsto_div_nhds_zero hf
    rw [← ENNReal.tendsto_toReal_iff (by finiteness) ENNReal.zero_ne_top]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.coe_toReal,
      ENNReal.toReal_zero]
    congr! 2
    ring_nf

private theorem LemmaS3_sup {ε : Prob}
    {d : ℕ+ → Type*} [∀ n, Fintype (d n)] [∀ n, DecidableEq (d n)]
    (ρ σ₁ σ₂ : (n : ℕ+) → MState (d n))
    (f : ℕ+ → ℝ≥0) (hf : (f · : ℕ+ → ℝ) =o[.atTop] (· : ℕ+ → ℝ))
    (hσ : ∀ i, Real.exp (-f i) • (σ₂ i).M ≤ σ₁ i)
    :
    Filter.limsup (fun (n : ℕ+) ↦ (↑n)⁻¹ * —log β_ ε(ρ n‖{σ₁ n})) Filter.atTop ≤
      Filter.limsup (fun (n : ℕ+) ↦ (↑n)⁻¹ * —log β_ ε(ρ n‖{σ₂ n})) Filter.atTop
    := by
  --Starting with `helper`, divide by n and take the limits. Since f is o(n),
  --the (↑n)⁻¹ * f n term will go to zero.
  trans Filter.limsup (fun n => (↑↑n)⁻¹ * (—log β_ ε(ρ n‖{σ₂ n}) + ↑(f n))) Filter.atTop
  · refine Filter.limsup_le_limsup ?_
    apply Filter.Eventually.of_forall
    intro x
    dsimp
    gcongr
    exact LemmaS3_helper _ _ _ _ hσ x
  · apply le_of_eq
    simp_rw [mul_add]
    apply Filter.limsup_add_tendsTo_zero
    convert Asymptotics.IsLittleO.tendsto_div_nhds_zero hf
    rw [← ENNReal.tendsto_toReal_iff (by finiteness) ENNReal.zero_ne_top]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.coe_toReal,
      ENNReal.toReal_zero]
    congr! 2
    ring_nf

-- This is not exactly how R_{1, ε} is defined in Eq. (17), but it should be equal due to
-- the monotonicity of log and Lemma 3.
private noncomputable def R1 (ρ : MState (H i)) (ε : Prob) : ENNReal :=
  Filter.liminf (fun n ↦ —log β_ ε(ρ⊗^S[n]‖IsFree) / n) Filter.atTop

private noncomputable def R2 (ρ : MState (H i)) : ((n : ℕ) → IsFree (i := i ^ n)) → ENNReal :=
  fun σ ↦ Filter.liminf (fun n ↦ 𝐃(ρ⊗^S[n]‖σ n) / n) Filter.atTop

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
  --Then we  prove S61, and the conclusion is just `rw [S61] at S62`. But splitting it like
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
  have σ_max_exists (n : ℕ) := IsCompact.exists_isMaxOn
      (α := ENNReal)
      (s := IsFree (i := i ^ n))
      (hs := IsCompact_IsFree)
      (ne_s := Set.Nonempty.of_subtype)
      (f := fun σ ↦ β_ ε(ρ⊗^S[n]‖{σ}))
      (hf := Continuous.continuousOn (by fun_prop))
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

  --Define σ'' first as the (unnormalized) cfc image of σ' under `λ → exp (f n λ)`.
  let σ''_unnormalized (n) : HermitianMat (H (i ^ n)) ℂ := --TODO: Define a HermitianMat.cfc function that behaves nicely
    (σ' n).M.cfc (fun e ↦ Real.exp (f n e))

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

  sorry

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
      let σ' := Lemma7_improver ρ hε hε' σ;
      R2 ρ σ' - R1 ρ ε ≤ .ofNNReal (1 - ε' : Prob) * (R2 ρ σ - R1 ρ ε) := by
  intro σ
  dsimp [SteinsLemma.Lemma7_improver]
  split_ifs with h
  · exact (SteinsLemma.Lemma7 ρ hε σ h ε' hε').choose_spec
  · push_neg at h
    conv_lhs => equals 0 =>
      exact tsub_eq_zero_of_le h.le
    exact zero_le _

end Lemma7

/-- Strengthening of `tendsto_of_limsup_eq_liminf`: instead of `limsup f = a = liminf f`, it suffices
to just have `limsup f ≤ a ≤ liminf f`. -/
theorem _root_.tendsto_of_limsup_le_liminf {α : Type u_2} {β : Type u_3} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
    [OrderTopology α] {f : Filter β} [f.NeBot] {u : β → α} {a : α}
    (hsup : Filter.limsup u f ≤ a) (hinf : a ≤ Filter.liminf u f)
    (h : Filter.IsBoundedUnder (fun x1 x2 => x1 ≤ x2) f u := by isBoundedDefault)
    (h' : Filter.IsBoundedUnder (fun x1 x2 => x1 ≥ x2) f u := by isBoundedDefault) :
    Filter.Tendsto u f (nhds a) := by
  have h_le := Filter.liminf_le_limsup (u := u) (f := f)
  have h_eq_inf : a = Filter.liminf u f :=
    le_antisymm hinf (h_le.trans hsup)
  have h_eq_sup : Filter.limsup u f = a :=
    le_antisymm hsup (hinf.trans h_le)
  exact tendsto_of_liminf_eq_limsup h_eq_inf.symm h_eq_sup

theorem GeneralizedQSteinsLemma {i : ι} (ρ : MState (H i)) (ε : Prob) (hε : 0 < ε ∧ ε < 1) :
    Filter.Tendsto (fun n ↦
      (↑n)⁻¹ * —log β_ ε(ρ⊗^S[n]‖IsFree)
    ) .atTop (𝓝 (RegularizedRelativeEntResource ρ)) := by
  conv =>
    enter [1, n, 2, 1]
    rw [← OptimalHypothesisRate.Lemma3 ε IsCompact_IsFree free_convex]
  rw [RegularizedRelativeEntResource]
  simp_rw [RelativeEntResource]
  generalize_proofs pf1 pf2 pf3 pf4
  --It suffices to show limsup LHS ≤ RHS and liminf LHS ≥ RHS.
  refine tendsto_of_limsup_le_liminf ?_ ?_
  · --the "strong converse" part first
    --Let σₘ be the state minimizing 𝐃(ρ⊗^m‖σₘ) over free states. This is guaranteed to exist since
    -- (1) the divergence is continuous and (2) the set of free states is compact.
    have σₘ_exists (m : ℕ) := IsCompact.exists_isMinOn
      (α := ENNReal)
      (s := IsFree (i := i ^ m))
      (hs := IsCompact_IsFree)
      (ne_s := Set.Nonempty.of_subtype)
      (f := fun σ ↦ 𝐃(ρ⊗^S[m]‖σ))
      (hf := by fun_prop
      )

    have hσₘ1 := fun m ↦ (σₘ_exists m).choose_spec.left
    have hσₘ2 := fun m ↦ (σₘ_exists m).choose_spec.right
    generalize σₘ_def : (fun m ↦ (σₘ_exists m).choose) = σₘ
    simp_rw [congrFun σₘ_def] at hσₘ1 hσₘ2
    clear σₘ_def σₘ_exists

    --Let σ₁ be the full-rank free state
    have ⟨σ₁, hσ₁_pos, hσ₁_free⟩ := FreeStateTheory.free_fullRank i

    --`h` is Eq (14)
    have h (m : ℕ) := Lemma6 m ρ σ₁ (σₘ m) hσ₁_pos ε hε.1 hε.2

    --Update `h` to Eq (15)
    have h₂ (m : ℕ) : (fun n => (↑n)⁻¹ * —log β_ ε(ρ⊗^S[n]‖IsFree)) ≤ᶠ[Filter.atTop]
        (fun n => (↑n)⁻¹ * —log β_ ε(ρ⊗^S[n]‖{(Lemma6_σn m σ₁ (σₘ m)) n})) := by
      rw [Filter.EventuallyLE]
      apply Filter.Eventually.of_forall
      intro n
      gcongr
      apply OptimalHypothesisRate.negLog_le_singleton
      apply Lemma6_σn_IsFree hσ₁_free hσₘ1
    replace h (m) := (Filter.limsup_le_limsup (h₂ m)).trans (h m)
    clear h₂

    --Update `h` to Eq (16)
    conv at h =>
      enter [m, 2, 2]
      exact (IsMinOn.iInf_eq (hσₘ1 m) (hσₘ2 m)).symm

    obtain ⟨v_lem5, hv_lem5⟩ := limit_rel_entropy_exists ρ --Do we need this...? in this form? Feels wrong
    conv_rhs =>
      equals .ofNNReal v_lem5 =>
        -- ??? ugh
        sorry

    apply le_of_tendsto_of_tendsto' tendsto_const_nhds hv_lem5
    convert h using 6
    · apply OptimalHypothesisRate.Lemma3 ε IsCompact_IsFree free_convex
    · symm
      apply iInf_subtype''

  · --the other direction, the "key part" of the "opposite inequality"
    set R₁ε := Filter.liminf (fun n => —log (⨆ σ ∈ IsFree, β_ ε(ρ⊗^S[n]‖{σ})) / ↑↑n) Filter.atTop
    --We need to pick an ε' (a \tilde{ε} in the paper). The only constraint(?) is that it's strictly
    --less than ε. We take ε' := ε/2.
     --TODO: Should we have an HDiv Prob Nat instance?
    let ε' : Prob := ⟨ε/2, by constructor <;> linarith [ε.zero_le_coe, ε.coe_le_one]⟩
    have hε' : 0 < ε' ∧ ε' < ε := by unfold ε'; constructor <;> change (_ : ℝ) < (_ : ℝ) <;> simpa using hε.1
    have lem7 (σ h) := Lemma7 ρ hε σ h ε' hε'
    --Take some initial sequence σ₁. Can just take the full_rank one from each, if we want (which is the `default`
    -- instance that `Inhabited` derives, but the point is that it doesn't matter)
    generalize (default : (n : ℕ) → IsFree (i := i ^ n)) = σ₁
    --Repeat the Lemma7 improvement process to drive the gap down
    let σₖ : ℕ → (n : ℕ) → IsFree (i := i ^ n) := fun k ↦
      (Lemma7_improver ρ hε hε')^[k] σ₁

    --Should be: the gap between R_{1,ε} and R2 for `σₖ k` goes to 0 as `k → ∞`.
    have hσₖ_gap : False := by
      sorry

    sorry
