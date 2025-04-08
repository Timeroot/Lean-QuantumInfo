import QuantumInfo.Finite.ResourceTheory.FreeState

import Mathlib.Analysis.Subadditive

open ResourcePretheory
open FreeStateTheory
open NNReal
open ComplexOrder
open Topology

namespace SteinsLemma

section hypotesting

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The optimal hypothesis testing rate, for a tolerance ε: given a state ρ and a set of states S,
the optimum distinguishing rate that allows a probability ε of errors. -/
noncomputable def OptimalHypothesisRate (ρ : MState d) (ε : ℝ) (S : Set (MState d)) : Prob :=
  ⨅ T : { m : HermitianMat d ℂ // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1},
    ⨆ σ ∈ S, ⟨_, σ.exp_val_prob T.2.right⟩

scoped notation "β_" ε " (" ρ "‖" S ")" =>  OptimalHypothesisRate ρ ε S

-- TODO: Pull this definition out into another file? Maybe?
/-- Map a probability [0,1] to [0,+∞] with -log p. Special case that 0 maps to +∞ (not 0, as Real.log
does). This makes it `Antitone`.
-/
noncomputable def _root_.Prob.negLog : Prob → ENNReal :=
  fun p ↦ if p = 0 then ⊤ else .ofNNReal ⟨-Real.log p,
    Left.nonneg_neg_iff.mpr (Real.log_nonpos p.2.1 p.2.2)⟩

--TODO: simp lemmas for Prob.negLog when e.g. 0 < p. Obviously one for when p = 0.
--For now can just do `simp [Prob.negLog, hp]`.

theorem _root_.Prob.negLog_Antitone : Antitone Prob.negLog := by
  intro x y h
  dsimp [Prob.negLog]
  split_ifs with h₁ h₂ h₂
  · rfl
  · subst y
    exfalso
    change x.1 ≤ 0 at h
    have : ¬(x.1 = 0) := unitInterval.coe_ne_zero.mpr (by assumption)
    have : 0 ≤ x.1 := Prob.zero_le
    linarith +splitNe
  · exact OrderTop.le_top _
  · rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_mk, coe_mk, neg_le_neg_iff]
    apply (Real.log_le_log_iff _ _).mpr h
    <;> exact lt_of_le_of_ne (Prob.zero_le) (unitInterval.coe_ne_zero.mpr (by assumption)).symm

scoped notation "—log " => Prob.negLog

theorem OptimalHypothesisRate_singleton {ρ σ : MState d} {ε : ℝ}  :
  β_ ε(ρ‖{σ}) =
    ⨅ T : { m : HermitianMat d ℂ // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1},
      ⟨_, σ.exp_val_prob T.2.right⟩
  := by
  simp only [OptimalHypothesisRate, iSup_singleton]

private theorem Lemma3 (ρ : MState d) (ε : ℝ) (S : Set (MState d)) :
    ⨆ σ ∈ S, β_ ε(ρ‖{σ}) = β_ ε(ρ‖S) := by
  --Needs the minimax theorem.
  sorry

/- This is from "Strong converse exponents for a quantum channel discrimination problem and
quantum-feedback-assisted communication", Lemma 5.

This is actually true for all 0 < α (with appropriate modifications at α = 1), but we only need
it for the case of 1 < α.
-/
private theorem Ref81Lem5 (ρ σ : MState d) (ε α : ℝ) (hε : 0 ≤ ε ∧ ε < 1) (hα : 1 < α) :
    —log β_ ε(ρ‖{σ}) ≤ D̃_ α(ρ‖σ) + —log ⟨(1 - ε), by constructor <;> linarith⟩ *
      (.ofNNReal ⟨α, zero_le_one.trans hα.le⟩) / (.ofNNReal ⟨α - 1, sub_nonneg_of_le hα.le⟩)
    := by
  generalize_proofs pf1 pf2 pf3
  --If ρ isn't in the support of σ, the right hand side is just ⊤. (The left hand side is not, necessarily!)
  by_cases h_supp : LinearMap.ker σ.val.toLin' ≤ LinearMap.ker ρ.val.toLin'
  swap
  · simp [SandwichedRelRentropy, h_supp]
  --Note that we actually only need this for 0 < ε, not 0 ≤ ε. This is also how it was proved in the original
  --reference. But Hayashi says it's true for ε = 0. Likely best handled with a special by_cases for ε = 0?
  --If this case is too much of a pain we can drop it.
  by_cases h : ε = 0
  · subst h
    clear hε
    simp [OptimalHypothesisRate]
    --Take m_opt to be the projector of ρ, i.e. 0 on ρ's kernel and 1 elsewhere.
    let m_opt : HermitianMat d ℂ := sorry
    sorry

  rcases hε with ⟨hε₀, hε₁⟩
  replace hε₀ : 0 < ε := lt_of_le_of_ne hε₀ fun a => h a.symm;
  clear h

  --Now we know that ρ.support ≤ σ.support, and 0 < ε. This is the main case we actually care about.
  --Proof from https://link.springer.com/article/10.1007/s00220-016-2645-4 reproduced below.
  /-
  Lemma 5. Let ρ, σ ∈ S (H) be such that supp ρ ⊆ supp σ . For any Q ∈ B(H) such
    that 0 ≤ Q ≤ I , and any α > 1,
    − log Tr[Qσ] ≤ D˜α (ρ‖σ) − α / (α−1) * log Tr[Qρ]. (3.7)
    In particular, for any α > 1 and any ε ∈ (0, 1),
    D^ε_H (ρ‖σ) ≤ D˜α (ρ‖σ) + α / (α−1) * log(1 / (1−ε)). (3.8)
    Proof. Let p ≡ Tr {Qρ} and q ≡ Tr {Qσ}. By the monotonicity of the sandwiched
    Rényi relative entropy for α > 1, we find that
    D˜α (ρ‖σ) ≥ D˜α ((p, 1 − p) ‖ (q, 1 − q)) (3.9)
      = 1 / (α−1) * log[p^α * q^(1−α) + (1−p)^α * (1−q)^(1−α) ] (3.10)
      ≥ 1 / (α−1) * log[p^α * q^(1−α) ] (3.11)
      = α / (α−1) * log p − log q, (3.12)
    from which (3.7) follows. The statement in (3.8) follows by optimizing over all Q such
    that Tr {Qρ} ≥ 1 − ε.
  -/
  -- The "monotonicity of the ..." part here refers to the data processing inequality, and
  -- the (p, 1-p) and (q,1-q) refer to states which are qubits ("coins") of probability p and
  -- q, respectively. The states ρ and σ can be "processed" into these coins by measuring the optimal T.
  let p : Prob := .one_minus ⟨ε, ⟨hε₀.le, hε₁.le⟩⟩
  set q : Prob := β_ ε(ρ‖{σ})
  let p2 : MState (Fin 2) := .ofClassical <| .coin p
  let q2 : MState (Fin 2) := .ofClassical <| .coin q

  have hp : 0 < p := show 0 < 1 - ε by linarith

  --Show there's a lower bound on β_ε, that you can't do perfect discrimination
  --It's possible that we actually don't want this here, that it should "follow"
  --from the main proof.
  have hq : 0 < q := by
    --The optimal hypothesis rate is finite
    simp_rw [q, OptimalHypothesisRate, Set.mem_singleton_iff, iSup_iSup_eq_left]
    sorry

  suffices —log q ≤ D̃_ α(p2‖q2) + —log ⟨1 - ε, pf1⟩ * (.ofNNReal ⟨α, pf2⟩) / (.ofNNReal ⟨α - 1, pf3⟩) by
    refine this.trans (add_le_add_right ?_ _)
    --This part needs the Data Processing Inequality
    sorry

  --The Renyi entropy is finite
  rw [SandwichedRelRentropy, if_pos ?_, if_neg hα.ne']; swap
  · suffices LinearMap.ker q2.val.toLin' = ⊥ by
      simp only [MState.toSubtype_eq_coe, HermitianMat.val_eq_coe, this, bot_le]
    --q2 has eigenvalues β_ ε(ρ‖{σ}) and 1-β_ ε(ρ‖{σ}), so as long as β_ ε(ρ‖{σ}) isn't 0 or 1,
    --this is true.
    sorry

  --The logs are finite
  rw [Prob.negLog, Prob.negLog, if_neg hq.ne', if_neg]
  rotate_left
  · change ¬(_ = Subtype.mk 0 _)
    rw [Subtype.eq_iff]
    dsimp
    linarith

  --Turn the ENNReal problem into a Real problem
  simp only [Prob.toReal_mk]
  have hα₂ : Subtype.mk _ pf3 ≠ 0 := by
    change ¬(_ = Subtype.mk 0 _)
    simp only [mk_zero, Nonneg.mk_eq_zero]
    linarith
  rw [← ENNReal.coe_mul, ← ENNReal.coe_div hα₂, ← ENNReal.coe_add, ENNReal.coe_le_coe]
  clear hα₂
  simp only [← coe_le_coe, coe_mk, NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul, neg_mul]
  clear pf1 pf2 pf3

  rw [← add_div, ← sub_eq_add_neg]
  conv =>
    enter [2,1,1,1]
    equals (p^α * q^(1-α) + (1-p)^α * (1-q)^(1-α) : ℝ)=>
      --This unfolds some of it:
      --simp [HermitianMat.trace_eq_re_trace, p2, q2, MState.ofClassical, MState.M, HermitianMat.conj]
      --Really we need use that
      -- (1) q2 ^ x = Matrix.diagonal [q^x, (1-q)^x]
      -- (2) p2 is also a diagonal
      -- (3) the product of diagonals is the diagonal of the products
      -- (4) the HermitianMat.trace of a diagonal matrix is just the regular trace
      -- (5) Write that trace as a sum of two things
      sorry

  trans (Real.log (p ^ α * q ^ (1 - α)) - Real.log (1 - ε) * α) / (α - 1)
  · rw [Real.log_mul]
    rotate_left
    · exact (Real.rpow_pos_of_pos hp _).ne'
    · exact (Real.rpow_pos_of_pos hq _).ne'
    simp only [p, Prob.coe_one_minus, Prob.toReal_mk]
    rw [Real.log_rpow (by linarith), mul_comm α, add_sub_cancel_left]
    rw [Real.log_rpow (x := q.toReal) hq]
    rw [mul_comm, ← mul_div, mul_comm, show (1 - α) = -(α - 1) by abel]
    simp [-neg_sub, neg_div, div_self (a := α - 1) (by linarith)]
  · rw [div_le_div_iff_of_pos_right (by linarith), tsub_le_iff_right, sub_add_cancel]
    apply Real.log_le_log
    · refine mul_pos (Real.rpow_pos_of_pos hp _) (Real.rpow_pos_of_pos hq _)
    rw [le_add_iff_nonneg_right]
    refine mul_nonneg (Real.rpow_nonneg ?_ _) (Real.rpow_nonneg ?_ _)
    · exact sub_nonneg_of_le p.2.2
    · exact sub_nonneg_of_le q.2.2

end hypotesting

variable {ι : Type*} [FreeStateTheory ι]
variable {i : ι}

--TODO maybe move this lemma outside. To FreeState.lean maybe? Or is it too specific
/-- In a `FreeStateTheory`, we have free states of full rank, therefore the minimum relative entropy
of any state `ρ` to a free state is finite. -/
lemma min_free_relent_finite (ρ : MState (H i)) : ⨅ σ ∈ IsFree, 𝐃(ρ‖σ) ≠ ⊤ := by
  simp only [ne_eq, iInf_eq_top, not_forall, Classical.not_imp]
  obtain ⟨σ, hσ₁, hσ₂⟩ := FreeStateTheory.free_fullRank i
  use σ, hσ₂
  --At this point should be an easy fact (a separate theorem) using hσ₁, it's posdef.
  sorry

-- This theorem should follow from "Fekete's subadditive lemma", which can be found in
-- Lemma A.1 of Hayashi's book "Quantum Information Theory - Mathematical Foundation".
--
-- Also, the sequence of states S^(n) mentioned in the paper is implicitly defined here as
-- IsFree (i := i⊗^[n]). It has all the properties we need plus some more (e.g., for this
-- lemma, we don't need convexity).
/-- Lemma 5 -/
theorem limit_rel_entropy_exists (ρ : MState (H i)) :
  ∃ d : ℝ≥0,
    Filter.Tendsto (fun n ↦ (↑n)⁻¹ * ⨅ σ ∈ IsFree (i := i⊗^[n]), 𝐃(ρ⊗^[n]‖σ))
    .atTop (𝓝 d) := by
  --Fekete's subadditive lemma is in Mathlib:
  have := @Subadditive.tendsto_lim
  --but with slightly different types...
  --Try to unify it with our goal below
  let u : ℕ+ → ENNReal := fun n ↦ ⨅ σ ∈ IsFree, 𝐃(ρ⊗^[n]‖σ)
  let u' : ℕ → ℝ := fun n ↦ if hn : n = 0 then 0 else (u ⟨n, Nat.zero_lt_of_ne_zero hn⟩).toReal
  have hu' : Subadditive u' := by
    intro m n
    unfold u'
    rcases m with _|m
    · simp
    rcases n with _|n
    · simp
    simp [← NNReal.coe_add]
    refine le_trans ?_ ENNReal.toReal_add_le
    apply ENNReal.toReal_mono
    · simpa only [ne_eq, ENNReal.add_eq_top, not_or, u] using
        ⟨min_free_relent_finite _, min_free_relent_finite _⟩
    --This is where we need to *really* show subadditivity.
    sorry
  have hu'_lim_nonneg : 0 ≤ hu'.lim := by
    rw [Subadditive.lim]
    apply le_csInf Set.Nonempty.of_subtype
    intro b hb
    simp only [Set.mem_image, Set.mem_Ici] at hb
    obtain ⟨x, hx₁, rfl⟩ := hb
    unfold u'
    split_ifs
    · simp
    · positivity
  have hu'_bddBelow : BddBelow (Set.range fun n => u' n / ↑n) := by
    use 0
    intro x hx
    simp only [Set.mem_range, u'] at hx
    obtain ⟨y, rfl⟩ := hx
    split_ifs
    · simp
    · positivity
  use ⟨hu'.lim, hu'_lim_nonneg⟩
  have := Subadditive.tendsto_lim hu' hu'_bddBelow
  /-
  Now we need to change `this`, which is `@Filter.Tendsto ℕ ℝ`, into our goal, which is
  `@Filter.Tendsto ℕ+ ENNReal`. This probably needs three steps, one where go from ℕ to ℕ+,
  one where we go from ℝ to NNReal, and then one more from NNReal to ENNReal. Some lemmas that
  might be useful:
  - `Topology.IsClosedEmbedding.tendsto_nhds_iff`
  - `Topology.IsEmbedding.tendsto_nhds_iff`
  - `Filter.tendsto_Ici_atTop` (note that `NNReal` is defeq to `Set.Ici (0 : ℝ)`)
  - `Filter.tendsto_congr`
  - `tendsto_subtype_rng`
  -/
  sorry

variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- Lemma 6 from the paper -/
private theorem Lemma6 (m : ℕ) (hm : 0 < m) (ρ σf : MState d) (σₘ : MState (Fin m → d)) (hσf : σf.m.PosDef) (ε : ℝ)
    (hε : 0 < ε)
    (hε' : ε < 1) --Not stated in the paper's theorem statement but I think is necessary for the argument to go through
    :
    let σn (n : ℕ) : (MState (Fin n → d)) :=
      let l : ℕ := n / m
      let q : ℕ := n % m
      let σl := σₘ ⊗^ l
      let σr := σf ⊗^ q
      let eqv : (Fin n → d) ≃ (Fin l → Fin m → d) × (Fin q → d) :=
        Equiv.piCongrLeft (fun _ ↦ d) ((finCongr (Eq.symm (Nat.div_add_mod' n m))).trans (finSumFinEquiv.symm))
          |>.trans <|
           (Equiv.sumArrowEquivProdArrow ..)
          |>.trans <|
           (Equiv.prodCongr (Equiv.piCongrLeft (fun _ ↦ d) finProdFinEquiv).symm (Equiv.refl _))
          |>.trans <|
          (Equiv.prodCongr (Equiv.curry ..) (Equiv.refl _))
      (σl.prod σr).relabel eqv
    Filter.atTop.limsup (fun n ↦ —log β_ ε(ρ⊗^n‖{σn n}) / n) ≤
    𝐃(ρ⊗^m‖σₘ) / m
  := by
  intro σn
  have h_add : ∀ α n, D̃_ α(ρ⊗^n‖σn n) = ↑(n/m) * D̃_ α(ρ⊗^m‖σₘ) + ↑(n%m) * D̃_ α(ρ‖σf):= by
    --"Break apart" σn, and apply additivity of `SandwichedRelRentropy`.
    sorry

  --<HACK> Clear let value on σn so that it's readable. Cleans up the infoview a lot.
  -- I'm sure there's a "clear_let" tactic or similar? Anyway this can be deleted
  -- when the proof is done
  let ⟨σn',hσn'⟩ := Exists.intro (p := (· = σn)) σn rfl
  rw [← hσn'] at h_add ⊢
  clear σn hσn'
  rename' σn' => σn
  --</HACK>

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
theorem limit_hypotesting_eq_limit_rel_entropy (ρ : MState (H i)) (ε : ℝ) (hε : 0 < ε ∧ ε < 1) :
    ∃ d : ℝ≥0,
      Filter.Tendsto (fun n ↦ —log β_ ε(ρ⊗^[n] ‖ IsFree) / n)
      .atTop (𝓝 d)
      ∧
      Filter.Tendsto (fun n ↦ (↑n)⁻¹ * ⨅ σ ∈ IsFree, 𝐃(ρ⊗^[n]‖σ))
      .atTop (𝓝 d)
      := by
  sorry

section Lemma7

open MatrixMap
open Matrix

variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut]

-- This should be moved to the files about matrix maps as soon as a good definition of "dual channel" can be made.
theorem positive_dual_channel_exists (ℰ : CPTPMap dIn dOut) :
  ∃ ℰdual : CPTPMap dOut dIn, ∀ ρ : MState dIn, ∀ T : HermitianMat dOut ℂ,
  (ℰ ρ).exp_val T  = ρ.exp_val ⟨ℰdual.map T, ℰdual.H T.H⟩ := by
  -- The proof below was valid for a previous wrong version of the theorem. Nevertheless
  -- it could still be useful for this version.
  --------------------------------------------------
  -- have hkraus := IsCompletelyPositive.exists_kraus ℰ.map ℰ.completely_pos
  -- obtain ⟨r, M, hkraus⟩ := hkraus
  -- let T' : Matrix dIn dIn ℂ := ∑ i : Fin r, (M i)ᴴ * T * (M i)
  -- -- Should come from something like Matrix.PosSemidef.sum
  -- have hT' : T'.PosSemidef := by
  --   constructor
  --   · unfold IsHermitian T'
  --     rw [conjTranspose_sum]
  --     simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  --     rw [hT.1]
  --   · intro x
  --     unfold T'
  --     -- rw [AddMonoidHom.finset_sum_apply (mulVec.addMonoidHomLeft : (dIn → ℂ) → (Matrix dIn dIn ℂ) →+ dIn → ℂ)]
  --     sorry
  -- use T', hT'
  -- simp [MState.exp_val, IsHermitian.rinner, CPTPMap.mat_coe_eq_apply_mat, hkraus, of_kraus,
  --   Finset.mul_sum, Finset.sum_mul, ←Matrix.mul_assoc, T']
  -- conv =>
  --   enter [1, 2, x]
  --   rw [trace_mul_cycle, ←Matrix.mul_assoc]
  sorry

set_option pp.proofs true in
/-- Lemma S1 -/
private theorem optimalHypothesisRate_antitone (ρ σ : MState dIn) (ℰ : CPTPMap dIn dOut) (ε3 : ℝ) (hε3 : ε3 ≥ 0) :
  β_ ε3(ρ‖{σ}) ≤ β_ ε3(ℰ ρ‖{ℰ σ}) := by
  repeat rw [OptimalHypothesisRate_singleton]
  obtain ⟨ℰdual, hℰdual⟩ := positive_dual_channel_exists ℰ
  let ℰdualSubtype :
  { m : HermitianMat dOut ℂ // (ℰ ρ).exp_val (1 - m) ≤ ε3 ∧ 0 ≤ m ∧ m ≤ 1} →
  { m : HermitianMat dIn ℂ // ρ.exp_val (1 - m) ≤ ε3 ∧ 0 ≤ m ∧ m ≤ 1} := sorry
  have h : ∀ x, (↑(ℰdualSubtype x) : HermitianMat dIn ℂ) = ⟨ℰdual.map x, ℰdual.H x.1.H⟩ := fun x ↦ by
    ext1
    simp
    sorry
  convert le_iInf_comp _ ℰdualSubtype
  rename_i T'
  specialize h T'
  rw [h, hℰdual]

noncomputable section proj

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

-- Projection onto the non-negative eigenspace of B - A
-- Note this is in the opposite direction as in the paper
def proj_le (A B : HermitianMat n 𝕜) : HermitianMat n 𝕜 :=
  ⟨Matrix.IsHermitian.cfc (B - A).H (fun x ↦ if x ≥ 0 then 1 else 0), by
    rw [←Matrix.IsHermitian.cfc_eq]
    exact IsSelfAdjoint.cfc
  ⟩

scoped notation "{" A "≥ₚ" B "}" => proj_le B A
scoped notation "{" A "≤ₚ" B "}" => proj_le A B

variable (A B : HermitianMat n 𝕜)

theorem proj_le_cfc : {A ≤ₚ B} = cfc (fun x ↦ if x ≥ 0 then (1 : ℝ) else 0) (B - A).toMat := by
  simp only [proj_le, ←Matrix.IsHermitian.cfc_eq]

theorem proj_le_sq : {A ≤ₚ B}^2 = {A ≤ₚ B} := by
  ext1
  simp only [HermitianMat.val_eq_coe, selfAdjoint.val_pow, proj_le_cfc]
  rw [←cfc_pow (hf := _)]
  · simp only [ge_iff_le, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, AddSubgroupClass.coe_sub, HermitianMat.val_eq_coe]
  · simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology, implies_true]

theorem proj_le_nonneg : 0 ≤ {A ≤ₚ B} := by
  rw [←proj_le_sq]
  exact HermitianMat.sq_nonneg

theorem proj_le_mul_nonneg : 0 ≤ {A ≤ₚ B}.toMat * (B - A).toMat := by
  rw [proj_le_cfc]
  nth_rewrite 2 [←cfc_id ℝ (B - A).toMat]
  rw [←cfc_mul (hf := _) (hg := _)]
  · apply cfc_nonneg
    intro x hx
    simp only [ge_iff_le, id_eq, ite_mul, one_mul, zero_mul]
    exact dite_nonneg (by simp only [imp_self]) (by simp only [not_le, le_refl, implies_true])
  · simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology, implies_true]
  · simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology, implies_true]

theorem proj_le_mul_le : {A ≤ₚ B}.toMat * A.toMat ≤ {A ≤ₚ B}.toMat * B.toMat := by
  rw [←sub_nonneg, ←mul_sub_left_distrib]
  convert proj_le_mul_nonneg A B

theorem proj_le_inner_nonneg : 0 ≤ {A ≤ₚ B}.inner (B - A) := HermitianMat.inner_mul_nonneg (proj_le_mul_nonneg A B)

theorem proj_le_inner_le : {A ≤ₚ B}.inner A ≤ {A ≤ₚ B}.inner B := by
  rw [←sub_nonneg, ←HermitianMat.inner_left_sub]
  exact proj_le_inner_nonneg A B

-- TODO: Commutation and order relations specified in the text between Eqs. (S77) and (S78)

end proj

/-- Lemma 7 from the paper -/
private theorem Lemma7 (ρ : MState (H i)) (ε : ℝ) (hε : 0 < ε ∧ ε < 1) (σ : (n : ℕ+) → IsFree (i := i⊗^[n])) :
  -- This is not exactly how R_{1, ε} is defined in Eq. (17), but it should be equal due to
  -- the monotonicity of log and Lemma 3.
  let R1 : ENNReal :=
    Filter.liminf (fun n ↦ —log β_ ε(ρ⊗^[n]‖IsFree) / n) Filter.atTop
  let R2 : ENNReal :=
    Filter.liminf (fun n ↦ 𝐃(ρ⊗^[n]‖σ n) / n) Filter.atTop
  (R2 ≥ R1) →
  ∀ ε' : ℝ, (hε' : 0 < ε' ∧ ε' < ε) → -- ε' is written as \tilde{ε} in the paper.
  ∃ σ' : (n : ℕ+) → IsFree (i := i⊗^[n]),
  let R2' : ENNReal :=
    Filter.liminf (fun n ↦ 𝐃(ρ⊗^[n]‖σ' n) / n) Filter.atTop
  R2' - R1 ≤ ENNReal.ofNNReal (⟨1 - ε', by linarith⟩) * (R2 - R1)
  := by
  sorry

end Lemma7

theorem GeneralizedQSteinsLemma {i : ι} (ρ : MState (H i)) (ε : ℝ) (hε : 0 < ε ∧ ε < 1) :
    Filter.Tendsto (fun n ↦
      —log β_ ε(ρ⊗^[n]‖IsFree) / n
    ) .atTop (𝓝 (RegularizedRelativeEntResource ρ)) := by
  sorry
