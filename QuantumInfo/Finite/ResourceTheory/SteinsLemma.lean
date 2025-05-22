import QuantumInfo.Finite.ResourceTheory.FreeState

open ResourcePretheory
open FreeStateTheory
open NNReal
open ComplexOrder
open Topology

namespace SteinsLemma
open scoped Prob

section hypotesting

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The optimal hypothesis testing rate, for a tolerance ε: given a state ρ and a set of states S,
the optimum distinguishing rate that allows a probability ε of errors. -/
noncomputable def OptimalHypothesisRate (ρ : MState d) (ε : ℝ) (S : Set (MState d)) : Prob :=
  ⨅ T : { m : HermitianMat d ℂ // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1},
    ⨆ σ ∈ S, ⟨_, σ.exp_val_prob T.2.right⟩

scoped notation "β_" ε " (" ρ "‖" S ")" =>  OptimalHypothesisRate ρ ε S

theorem OptimalHypothesisRate_le {ρ : MState d} {ε : ℝ} {S : Set (MState d)}
    (m : HermitianMat d ℂ) (hExp : ρ.exp_val (1 - m) ≤ ε) (hm : 0 ≤ m ∧ m ≤ 1) :
    β_ ε(ρ‖S) ≤ ⨆ σ ∈ S, ⟨_, σ.exp_val_prob hm⟩ := by
  unfold OptimalHypothesisRate
  apply iInf_le_of_le ⟨m, ⟨hExp, hm⟩⟩ _
  simp only [le_refl]

theorem OptimalHypothesisRate_le_of_subset (ρ : MState d) (ε : ℝ) {S1 S2 : Set (MState d)} (h : S1 ⊆ S2) :
    β_ ε(ρ‖S1) ≤ β_ ε(ρ‖S2) :=
  iInf_mono (fun _ ↦ iSup_le_iSup_of_subset h)

theorem OptimalHypothesisRate_singleton {ρ σ : MState d} {ε : ℝ}  :
    β_ ε(ρ‖{σ}) =
      ⨅ T : { m : HermitianMat d ℂ // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1},
        ⟨_, σ.exp_val_prob T.2.right⟩ := by
  simp only [OptimalHypothesisRate, iSup_singleton]

theorem negLog_OptimalHypothesisRate_le_singleton (ρ : MState d) (ε : ℝ) (S : Set (MState d))
    (σ : MState d) (h : σ ∈ S) : —log β_ ε(ρ‖S) ≤ —log β_ ε(ρ‖{σ}) := by
  apply Prob.negLog_Antitone
  apply OptimalHypothesisRate_le_of_subset
  exact Set.singleton_subset_iff.mpr h

theorem OptimalHypothesisRate_le_singleton {ρ σ : MState d} {ε : ℝ} (m : HermitianMat d ℂ)
    (hExp : ρ.exp_val (1 - m) ≤ ε) (hm : 0 ≤ m ∧ m ≤ 1) :
  β_ ε(ρ‖{σ}) ≤ ⟨_, σ.exp_val_prob hm⟩ := by
  rw [OptimalHypothesisRate_singleton]
  apply iInf_le_of_le ⟨m, ⟨hExp, hm⟩⟩ _
  simp only [le_refl]

/-- The minimax theorem, at the level of generality we need. Convex, compact sets,
 and a bilinear function on ℝ. -/
theorem minimax {M : Type*} [AddCommMonoid M] [Module ℝ M] [TopologicalSpace M]
    (f : LinearMap.BilinForm ℝ M) (S : Set M) (T : Set M)
    (hS₁ : IsCompact S) (hT₁ : IsCompact T) (hS₂ : Convex ℝ S) (hT₂ : Convex ℝ T)
    :
    ⨆ x ∈ S, ⨅ y ∈ T, f x y =  ⨅ y ∈ T, ⨆ x ∈ S, f x y := by
  sorry

private theorem Lemma3 {ρ : MState d} {ε : ℝ} {S : Set (MState d)} (hS₁ : IsCompact S) (hS₂ : Convex ℝ (MState.M '' S)) :
    ⨆ σ ∈ S, β_ ε(ρ‖{σ}) = β_ ε(ρ‖S) := by
  --Needs the minimax theorem.
  simp only [OptimalHypothesisRate, Set.mem_singleton_iff, iSup_iSup_eq_left]
  have hmm := minimax (M := HermitianMat d ℂ)
  --This will be the `MState.exp_val` function, but bundled as a bilinear form.
  let f : LinearMap.BilinForm ℝ (HermitianMat d ℂ) := {
      toFun ρ := {
        toFun σ := ρ.inner σ
        map_add' := sorry
        map_smul' := sorry
      }
      map_add' := sorry
      map_smul' := sorry
    }
  let S' : Set (HermitianMat d ℂ) := MState.M '' S
  let T' : Set (HermitianMat d ℂ) := { m | MState.exp_val (1 - m) ρ ≤ ε ∧ 0 ≤ m ∧ m ≤ 1 }
  replace hS₁ : IsCompact S' := by
    dsimp [S']
    sorry
  have hT₁ : IsCompact T' := by
    sorry
  have hT₂ : Convex ℝ T' := by
    --We *could* get this from a more general fact that any linear subspace is convex,
    --and the intersection of convex spaces is convex, and this is an intersection of
    --three convex spaces.
    dsimp [T']
    rintro x ⟨hx₁, hx₂, hx₃⟩ y ⟨hy₁, hy₂, hy₃⟩ a b ha hb hab
    refine And.intro ?_ (And.intro ?_ ?_)
    · sorry
    · sorry
    · sorry
  specialize hmm f S' T' hS₁ hT₁ hS₂ hT₂
  ext
  -- change Subtype.val _ = Subtype.val _
  rw [← iSup_subtype'']
  have hnS : Nonempty S := by
    --Do we need a hypothesis for this?
    sorry

  --This is a terrible mess of unification
  have h_inst :
    let _ : Fact (0 ≤ (1 : ℝ)) := ⟨zero_le_one⟩;
    @CompleteSemilatticeSup.toSupSet Prob CompleteLattice.toCompleteSemilatticeSup
    =
    @ConditionallyCompleteLattice.toSupSet (↑(Set.Icc 0 1)) (
      @CompleteLattice.toConditionallyCompleteLattice _ Set.Icc.completeLattice)
     := by
    --This is terrible. We get two slightly different lattices, that turn out equal
    simp [CompleteLattice.toConditionallyCompleteLattice,
      CompleteLattice.toCompleteSemilatticeSup]
    congr
    simp [CompletelyDistribLattice.toCompleteLattice, CompleteLinearOrder.toCompletelyDistribLattice,
      Prob.instCompleteLinearOrder, Set.Icc.completeLattice]
    congr
    · ext s
      split_ifs with hs
      . simp [hs]
      · simp [hs]
        rfl
    · ext s
      split_ifs with hs₁ hs₂ hs₂
      · simp [hs₂] at hs₁
      · simp [hs₁, hs₂]
        rfl
      · rfl
      · push_neg at hs₁
        simp [hs₁] at hs₂
  -- let f'' : ↑S → Prob := fun i
  --   ↦ ⨅ (T : { m // MState.exp_val (1 - m) ρ ≤ ε ∧ 0 ≤ m ∧ m ≤ 1 }), ⟨MState.exp_val (Subtype.val T) (Subtype.val i),
  --     OptimalHypothesisRate.proof_1 ρ ε T (Subtype.val i)⟩
  -- have h_sub := @Set.Icc.coe_iSup (ι := S) (α := ℝ) (a := 0) (b := 1) _ (zero_le_one) _ (S := f'')
  -- dsimp [f''] at h_sub
  convert Eq.trans (Set.Icc.coe_iSup (ι := S) (zero_le_one (α := ℝ))) ?_
  --No, this is stupid, there has to be a better way
  sorry

theorem Matrix.star_diagonal {T R : Type*} [DecidableEq T] [AddMonoid R] [StarAddMonoid R] (f : T → R) :
    star (Matrix.diagonal f) = Matrix.diagonal (star <| f ·) := by
  ext i j
  simp only [Matrix.star_apply, Matrix.diagonal_apply]
  split <;> simp_all [@eq_comm _ j i]

def HermitianMat.diagonal {T : Type*} [DecidableEq T] (f : T → ℝ) : HermitianMat T ℂ :=
  ⟨Matrix.diagonal (f ·), by simp [selfAdjoint.mem_iff, Matrix.star_diagonal]⟩

theorem HermitianMat.diagonal_pow {T : Type*} [Fintype T] [DecidableEq T] (f : T → ℝ) (p : ℝ) :
    (HermitianMat.diagonal f) ^ p = HermitianMat.diagonal fun i => (f i) ^ p := by
  sorry

@[simp]
theorem MState.coe_ofClassical (d : Distribution d) :
    (MState.ofClassical d).M = HermitianMat.diagonal (d ·) := by
  sorry

theorem MState.ofClassical_pow {T : Type*} [Fintype T] [DecidableEq T] (dist : Distribution T) (p : ℝ) :
    (MState.ofClassical dist).M ^ p = HermitianMat.diagonal (fun i ↦ (dist i) ^ p) := by
  simp
  exact HermitianMat.diagonal_pow (dist ·) p

theorem HermitianMat.diagonal_conj_diagonal {T : Type*} [Fintype T] [DecidableEq T] (f g : T → ℝ) :
    (HermitianMat.diagonal f).conj (HermitianMat.diagonal g) =
    HermitianMat.diagonal (fun i ↦ f i * (g i)^2) := by
  simp [diagonal, HermitianMat.conj]
  intro
  ring

theorem HermitianMat.trace_diagonal {T : Type*} [Fintype T] [DecidableEq T] (f : T → ℝ) :
    (HermitianMat.diagonal f).trace = ∑ i, f i := by
  rw [HermitianMat.trace_eq_re_trace]
  simp [HermitianMat.diagonal, Matrix.trace]

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
  let p : Prob := 1 - ⟨ε, ⟨hε₀.le, hε₁.le⟩⟩
  set q : Prob := β_ ε(ρ‖{σ})
  let p2 : MState (Fin 2) := .ofClassical <| .coin p
  let q2 : MState (Fin 2) := .ofClassical <| .coin q

  have hp : 0 < p := show (0 : ℝ) < p by simp [p, hε₁]

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
    equals (p^α * q^(1-α) + (1-p)^α * (1-q)^(1-α) : ℝ) =>
      unfold q2
      rw [MState.ofClassical_pow]
      unfold p2
      rw [MState.coe_ofClassical]
      rw [HermitianMat.diagonal_conj_diagonal, HermitianMat.diagonal_pow]
      rw [HermitianMat.trace_diagonal]
      simp only [Fin.sum_univ_two, Fin.isValue, Distribution.coin_val_zero,
        Distribution.coin_val_one, Prob.coe_one_minus]
      rw [Real.mul_rpow p.zero_le (by positivity)]
      rw [← Real.rpow_natCast_mul (by have := q.zero_le_coe; positivity)]
      rw [← Real.rpow_mul q.zero_le]
      rw [Real.mul_rpow (sub_nonneg_of_le p.coe_le_one) (by positivity)]
      rw [← Real.rpow_natCast_mul (by have := sub_nonneg_of_le q.coe_le_one; positivity)]
      rw [← Real.rpow_mul (sub_nonneg_of_le q.coe_le_one)]
      field_simp

  trans (Real.log (p ^ α * q ^ (1 - α)) - Real.log (1 - ε) * α) / (α - 1)
  · rw [Real.log_mul]
    rotate_left
    · exact (Real.rpow_pos_of_pos hp _).ne'
    · exact (Real.rpow_pos_of_pos hq _).ne'
    simp only [p, Prob.coe_one_minus]
    rw [Real.log_rpow (by linarith), mul_comm α, add_sub_cancel_left]
    rw [Real.log_rpow (x := q.val) hq]
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
  let u : ℕ+ → ENNReal := fun n ↦ (↑n)⁻¹ * ⨅ σ ∈ IsFree, 𝐃(ρ⊗^[n]‖σ)
  let u' : ℕ → ℝ := fun n ↦ if hn : n = 0 then 0 else (u ⟨n, Nat.zero_lt_of_ne_zero hn⟩).toReal
  have hu' : Subadditive u' := by
    unfold u' u
    have hsub := RelativeEntResource.Subadditive ρ
    dsimp [RelativeEntResource] at hsub
    convert hsub
    rw [ENNReal.toReal_mul]
    congr
    simp
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

/-- The \tilde{σ}_n defined in Lemma 6.
I've slightly changed the definition here: instead of `n / m` and `n % m`, I use `(n-1) / m` and `(n-1)%m + 1`.
This means that we only ever need ℕ+ powers of states. It *would* be fine to just add the requirement to our
notion of `ResourcePretheory` that we have a 0-dimensional space, so that we can take ℕ powers; or we could
express this with if-statements (e.g. `if m ∣ n then σₘ ⊗^ [ n / m ] else (...) ⊗ᵣ (...)`) but that's messier
to work with. This altered definition is easier to work with and still has all the properties we need. We still
need one `if` statement for when `n ≤ m`, sadly.
-/
noncomputable def Lemma6_σn (m : ℕ+) (σf : MState (H i)) (σₘ : MState (H (i ⊗^[m]))) : (n : ℕ+) → (MState (H (i ⊗^[n]))) :=
  fun n ↦
    --This needs to be reworked to be compatible with the FreeStateTheory framework.
    let l : ℕ := n.natPred / m
    let q : ℕ+ := (n.natPred % m).succPNat
    let σr := σf ⊗^[q]
    if h : n ≤ m then
      σr.relabel <| .cast <| congrArg (H <| i⊗^[·]) (by
        apply PNat.eq
        simp [q, PNat.natPred]
        have := (Nat.mod_eq_of_lt (Nat.sub_one_lt_of_le n.2 h)).symm
        rwa [Nat.sub_eq_iff_eq_add n.2] at this
      )
    else
      let σl := σₘ ⊗^[ ⟨l, by simpa [l] using Nat.le_sub_one_of_lt (lt_of_not_ge h)⟩ ];
      (σl ⊗ᵣ σr).relabel <| .cast <| congrArg H <| (by
        --This will require some real twiddling with our FreeStateTheory axioms for `prod`. We'll
        --probably need some kind of monoidal structure ... In this case we just need to show that
        -- i^n = (i^m)^(l) ⊗ i^q. These are both just expressions made from repeated products of
        --the "base" Hilbert space i (remember that `⊗^[·]` is shorthand for iterated applications
        -- of `ResourcePretheory.prod`), but the expressions are shaped differently; associativity of
        --the product should be enough.
        sorry
      )

theorem Lemma6_σn_IsFree {σ₁ : MState (H i)} {σₘ : (m : ℕ+) → MState (H (i⊗^[m]))} (hσ₁_free : IsFree σ₁)
    (hσₘ1 : ∀ (m : ℕ+), σₘ m ∈ IsFree) (m n : ℕ+) : Lemma6_σn m σ₁ (σₘ m) n ∈ IsFree := by
  sorry

/-- Lemma 6 from the paper -/
private theorem Lemma6 (m : ℕ+) (ρ σf : MState (H i)) (σₘ : MState (H (i ⊗^[m]))) (hσf : σf.m.PosDef) (ε : ℝ)
    (hε : 0 < ε)
    (hε' : ε < 1) --Not stated in the paper's theorem statement but I think is necessary for the argument to go through
    :
    Filter.atTop.limsup (fun (n : ℕ+) ↦ (↑n)⁻¹ * —log β_ ε(ρ⊗^[n]‖{Lemma6_σn m σf σₘ n})) ≤
    (↑m)⁻¹ * 𝐃(ρ⊗^[m]‖σₘ)
  := by
  intro σn
  stop
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

variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut] {R : Type*}

set_option pp.proofs true in
/-- Lemma S1 -/
private theorem optimalHypothesisRate_antitone (ρ σ : MState dIn) (ℰ : CPTPMap dIn dOut) (ε₃ : ℝ) :
    β_ ε₃(ρ‖{σ}) ≤ β_ ε₃(ℰ ρ‖{ℰ σ}) := by
  simp only [OptimalHypothesisRate_singleton]
  obtain ⟨ℰdualSubtype, h⟩ :
      ∃ e : ({ m : HermitianMat dOut ℂ // (ℰ ρ).exp_val (1 - m) ≤ ε₃ ∧ 0 ≤ m ∧ m ≤ 1} →
      { m : HermitianMat dIn ℂ // ρ.exp_val (1 - m) ≤ ε₃ ∧ 0 ≤ m ∧ m ≤ 1}),
      ∀ x, e x = ℰ.dual x
       := by
    constructor; swap
    · rintro ⟨m, hm₁, hm₂⟩
      refine ⟨ℰ.dual m, ?_, CPTPMap.dual.PTP_POVM ℰ hm₂⟩
      simpa [ℰ.exp_val_Dual ρ (1 - m)] using hm₁
    · rintro ⟨m, hm₁, hm₂⟩
      rfl
  convert le_iInf_comp _ ℰdualSubtype
  rename_i T'
  specialize h T'
  rw [h, ℰ.exp_val_Dual]

-- TODO: Commutation and order relations about `proj_le` specified in the text
-- between Eqs. (S77) and (S78)

-- The assumption (hε3 : 0 ≤ ε3 ∧ ε3 ≤ 1) stated in the paper was not used
theorem LemmaS2 {ε3 : ℝ} {ε4 : ℝ≥0} (hε4 : 0 < ε4)
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
        rw [HermitianMat.inner_left_sub, HermitianMat.inner_one, MState.tr',
          HermitianMat.inner_comm, tsub_le_iff_right, add_comm, ←tsub_le_iff_right]
        apply le_of_lt
        exact h n hn
      have hβ : ∀ n ≥ n₀, β_ ε3(ρ n‖{σ n}) ≤ Real.exp (-↑n * (Rinf + ε4)) := fun n hn ↦ by -- Eq (S25)
        calc
          β_ ε3(ρ n‖{σ n}) ≤ (σ n).exp_val (T n) := by
            have hβ' := OptimalHypothesisRate_le_singleton (σ := σ n) (T n) (hT n hn) ⟨proj_le_nonneg _ _, proj_le_le_one _ _⟩
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
        rw [HermitianMat.inner_left_sub, HermitianMat.inner_one, MState.tr',
          HermitianMat.inner_comm, tsub_le_iff_right, add_comm, ←tsub_le_iff_right]
        apply le_of_lt
        exact h
      have hβ : ∀ n₀, ∃ n ≥ n₀, β_ ε3(ρ n‖{σ n}) ≤ Real.exp (-↑n * (Rsup + ε4)) := fun n₀ ↦ by -- Eq (S32)
        obtain ⟨n, ⟨hn, hT⟩⟩ := hT n₀
        use n; use hn
        calc
          β_ ε3(ρ n‖{σ n}) ≤ (σ n).exp_val (T n) := by
            have hβ' := OptimalHypothesisRate_le_singleton (σ := σ n) (T n) hT ⟨proj_le_nonneg _ _, proj_le_le_one _ _⟩
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

-- This is not exactly how R_{1, ε} is defined in Eq. (17), but it should be equal due to
-- the monotonicity of log and Lemma 3.
private noncomputable def R1 (ρ : MState (H i)) (ε : ℝ) : ENNReal :=
  Filter.liminf (fun n ↦ —log β_ ε(ρ⊗^[n]‖IsFree) / n) Filter.atTop

private noncomputable def R2 (ρ : MState (H i)) : ((n : ℕ+) → IsFree (i := i⊗^[n])) → ENNReal :=
  fun σ ↦ Filter.liminf (fun n ↦ 𝐃(ρ⊗^[n]‖σ n) / n) Filter.atTop

/-- Lemma 7 from the paper -/
private theorem Lemma7 (ρ : MState (H i)) (ε : ℝ) (hε : 0 < ε ∧ ε < 1) (σ : (n : ℕ+) → IsFree (i := i⊗^[n])) :
    (R2 ρ σ ≥ R1 ρ ε) →
    ∀ ε' : ℝ, (hε' : 0 < ε' ∧ ε' < ε) → -- ε' is written as \tilde{ε} in the paper.
    ∃ σ' : (n : ℕ+) → IsFree (i := i⊗^[n]),
    R2 ρ σ' - R1 ρ ε ≤ .ofNNReal (⟨1 - ε', by linarith⟩) * (R2 ρ σ - R1 ρ ε)
    := by
  sorry

/-- Lemma 7 gives us a way to repeatedly "improve" a sequence σ to one with a smaller gap between R2 and R1.
The paper paints this as pretty much immediate from Lemma7, but we need to handle the case where R2 is below
R1. -/
private noncomputable def Lemma7_improver (ρ : MState (H i)) {ε : ℝ} (hε : 0 < ε ∧ ε < 1) {ε' : ℝ} (hε' : 0 < ε' ∧ ε' < ε) :
    --The parameters above are the "fixed" parameters that we'll improve
    --It takes one sequence of free states, `(n : ℕ+) → IsFree (i := i⊗^[n])`, and gives a new one
    ((n : ℕ+) → IsFree (i := i⊗^[n])) → ((n : ℕ+) → IsFree (i := i⊗^[n])) :=
  fun σ ↦
    if h : R2 ρ σ ≥ R1 ρ ε then
      (Lemma7 ρ ε hε σ h ε' hε').choose
    else
     σ --The gap was already 0 (or even, negative!) so leave it unchanged.

/-- The Lemma7_improver does its job at shrinking the gap. -/
theorem Lemma7_gap (ρ : MState (H i)) {ε : ℝ} (hε : 0 < ε ∧ ε < 1) {ε' : ℝ} (hε' : 0 < ε' ∧ ε' < ε) :
    ∀ σ,
      let σ' := Lemma7_improver ρ hε hε' σ;
      R2 ρ σ' - R1 ρ ε ≤ .ofNNReal (⟨1 - ε', by linarith⟩) * (R2 ρ σ - R1 ρ ε) := by
  intro σ
  dsimp [SteinsLemma.Lemma7_improver]
  split_ifs with h
  · exact (SteinsLemma.Lemma7 ρ ε hε σ h ε' hε').choose_spec
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

theorem GeneralizedQSteinsLemma {i : ι} (ρ : MState (H i)) (ε : ℝ) (hε : 0 < ε ∧ ε < 1) :
    Filter.Tendsto (fun n ↦
      (↑n)⁻¹ * —log β_ ε(ρ⊗^[n]‖IsFree)
    ) .atTop (𝓝 (RegularizedRelativeEntResource ρ)) := by
  conv =>
    enter [1, n, 2, 1]
    rw [← Lemma3 IsCompact_IsFree free_convex]
  rw [RegularizedRelativeEntResource]
  simp only
  generalize_proofs pf1 pf2 pf3
  simp_rw [RelativeEntResource]
  --It suffices to show limsup LHS ≤ RHS and liminf LHS ≥ RHS.
  refine tendsto_of_limsup_le_liminf ?_ ?_
  · --the "strong converse" part first
    --Let σₘ be the state minimizing 𝐃(ρ⊗^m‖σₘ) over free states. This is guaranteed to exist since
    -- (1) the divergence is continuous and (2) the set of free states is compact.
    have σₘ_exists (m : ℕ+) := IsCompact.exists_isMinOn
      (α := ENNReal)
      (s := IsFree (i := i⊗^[m]))
      (hs := IsCompact_IsFree)
      (ne_s := Set.Nonempty.of_subtype)
      (f := fun σ ↦ 𝐃(ρ⊗^[m]‖σ))
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
    have h (m : ℕ+) := Lemma6 m ρ σ₁ (σₘ m) hσ₁_pos ε hε.1 hε.2

    --Update `h` to Eq (15)
    have h₂ (m : ℕ+) : (fun n => (↑n)⁻¹ * —log β_ ε(ρ⊗^[n]‖IsFree)) ≤ᶠ[Filter.atTop]
        (fun n => (↑n)⁻¹ * —log β_ ε(ρ⊗^[n]‖{(Lemma6_σn m σ₁ (σₘ m)) n})) := by
      rw [Filter.EventuallyLE]
      apply Filter.Eventually.of_forall
      intro n
      gcongr
      apply negLog_OptimalHypothesisRate_le_singleton
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
    · apply Lemma3 IsCompact_IsFree free_convex
    · symm
      apply ciInf_subtype''
      · exact Set.Nonempty.of_subtype
      · exact OrderBot.bddBelow _
      · simp

  · --the other direction, the "key part" of the "opposite inequality"
    set R₁ε := Filter.liminf (fun n => —log (⨆ σ ∈ IsFree, β_ ε(ρ⊗^[n]‖{σ})) / ↑↑n) Filter.atTop
    --We need to pick an ε' (a \tilde{ε} in the paper). The only constraint(?) is that it's strictly
    --less than ε. We take ε' := ε/2.
    let ε' := ε/2
    have hε' : 0 < ε' ∧ ε' < ε := by unfold ε'; constructor <;> linarith
    have lem7 (σ h) := Lemma7 ρ ε hε σ h ε' hε'
    dsimp at lem7
    --Take some initial sequence σ₁. Can just take the full_rank one from each, if we want (which is the `default`
    -- instance that `Inhabited` derives, but the point is that it doesn't matter)
    generalize (default : (n : ℕ+) → IsFree (i := i⊗^[n])) = σ₁
    --Repeat the Lemma7 improvement process to drive the gap down
    let σₖ : ℕ → (n : ℕ+) → IsFree (i := i⊗^[n]) := fun k ↦
      (Lemma7_improver ρ hε hε')^[k] σ₁

    --Should be: the gap between R_{1,ε} and R2 for `σₖ k` goes to 0 as `k → ∞`.
    have hσₖ_gap : False := by
      sorry

    sorry
