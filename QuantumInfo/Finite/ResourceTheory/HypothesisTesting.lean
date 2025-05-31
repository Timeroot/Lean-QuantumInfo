import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Analysis.Subadditive
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Data.EReal.Basic

import QuantumInfo.Finite.CPTPMap
import QuantumInfo.Finite.Entropy

/-!
Defines `OptimalHypothesisRate`, the optimal rate of distinguishing an `MState` ρ from a set of other
mixed states `S`, with at most Type I error ε.

That is to say: take a projective measurement (a `POVM`) with elements `{T, 1-T}`, where measuring `T`
will mean we conclude our unknown state was ρ, and measuring `1-T` will mean we think the state was
something in `S`. We only accept T's such that `Tr[(1-T)ρ] ≤ ε`, that is, we have at most an ε
probability of incorrectly concluding it was ρ. The Type II error associated to this T is then
`max_{σ ∈ S} Tr[T σ]`, that is, the (worst possible, over possible states) chance of incorrectly
concluding our state was in `S`. Optimize over `T` to get the lowest possible Type II error rate,
and the resulting error rate is `OptimalHypothesisRate ρ ε S`.

We make this accessible through the notation `β_ ε(ρ‖S)`.

See [The tangled state of quantum hypothesis testing](https://doi.org/10.1038/s41567-023-02289-9) by
Mario Berta et al. for a broader overview.
-/

open NNReal
open ComplexOrder
open Topology

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Provides an `Inhabited` instance for the quantification over `T` in `OptimalHypothesisRate`. Not
an instance, because we need that `0 ≤ ε`. -/
instance iInf_Inhabited (ρ : MState d) (ε : Prob) :
    Inhabited { m // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1 } :=
  ⟨1, by simp⟩

-- have _ : Inhabited {m | MState.exp_val (1 - m) ρ ≤ ε ∧ 0 ≤ m ∧ m ≤ 1}

/-- The optimal hypothesis testing rate, for a tolerance ε: given a state ρ and a set of states S,
the optimum distinguishing rate that allows a probability ε of errors. -/
noncomputable def OptimalHypothesisRate (ρ : MState d) (ε : Prob) (S : Set (MState d)) : Prob :=
  ⨅ T : { m : HermitianMat d ℂ // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1},
    ⨆ σ ∈ S, ⟨_, σ.exp_val_prob T.prop.right⟩

scoped[OptimalHypothesisRate] notation "β_" ε " (" ρ "‖" S ")" =>  OptimalHypothesisRate ρ ε S

namespace OptimalHypothesisRate

-- /-- When `ε < 0`, the type is empty. -/
-- theorem iInf_Empty_of_lt_zero (ρ : MState d) {ε : ℝ} (hε : ε < 0) :
--     IsEmpty { m // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1 } := by
--   by_contra h
--   rw [not_isEmpty_iff, nonempty_subtype] at h
--   let ⟨a, ha₁, ha₂, ha₃⟩ := h
--   replace ha₁ := lt_of_le_of_lt ha₁ hε
--   rw [← not_le] at ha₁
--   rw [← sub_nonneg] at ha₃
--   exact ha₁ (ρ.exp_val_nonneg ha₃)

-- /-- When `ε < 0`, the `OptimalHypothesisRate` becomes 1, as a junk value. -/
-- @[simp]
-- theorem lt_zero {ρ : MState d} {ε : ℝ} {S : Set (MState d)} (hε : ε < 0) : β_ ε(ρ‖S) = 1 := by
--   rw [OptimalHypothesisRate]
--   have _ := iInf_Empty_of_lt_zero ρ hε
--   rw [iInf_of_empty] --TODO: should iInf_of_empty be tagged @[simp]? it feels like it should
--   rfl

/-- When `S` is empty, the optimal hypothesis testing rate is zero. -/
@[simp]
theorem of_empty {ρ : MState d} (ε : Prob) : β_ ε(ρ‖∅) = 0 := by
  simp [OptimalHypothesisRate]
  rfl

theorem le_sup_exp_val {ρ : MState d} (ε : Prob) {S : Set (MState d)}
    (m : HermitianMat d ℂ) (hExp : ρ.exp_val (1 - m) ≤ ε) (hm : 0 ≤ m ∧ m ≤ 1) :
    β_ ε(ρ‖S) ≤ ⨆ σ ∈ S, ⟨_, σ.exp_val_prob hm⟩ := by
  unfold OptimalHypothesisRate
  apply iInf_le_of_le ⟨m, ⟨hExp, hm⟩⟩ _
  simp only [le_refl]

theorem le_of_subset (ρ : MState d) (ε : Prob) {S1 S2 : Set (MState d)} (h : S1 ⊆ S2) :
    β_ ε(ρ‖S1) ≤ β_ ε(ρ‖S2) :=
  iInf_mono (fun _ ↦ iSup_le_iSup_of_subset h)

theorem of_singleton {ρ σ : MState d} {ε : Prob} :
    β_ ε(ρ‖{σ}) =
      ⨅ T : { m : HermitianMat d ℂ // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1},
        ⟨_, σ.exp_val_prob T.2.right⟩ := by
  simp only [OptimalHypothesisRate, iSup_singleton]

open scoped Prob in
theorem negLog_le_singleton (ρ : MState d) (ε : Prob) (S : Set (MState d))
    (σ : MState d) (h : σ ∈ S) : —log β_ ε(ρ‖S) ≤ —log β_ ε(ρ‖{σ}) := by
  apply Prob.negLog_Antitone
  apply le_of_subset
  exact Set.singleton_subset_iff.mpr h

theorem singleton_le_exp_val {ρ σ : MState d} {ε : Prob} (m : HermitianMat d ℂ)
    (hExp : ρ.exp_val (1 - m) ≤ ε) (hm : 0 ≤ m ∧ m ≤ 1) :
  β_ ε(ρ‖{σ}) ≤ ⟨_, σ.exp_val_prob hm⟩ := by
  rw [of_singleton]
  apply iInf_le_of_le ⟨m, ⟨hExp, hm⟩⟩ _
  simp only [le_refl]

--Lemma 3 from Hayashi
theorem Lemma3 {ρ : MState d} (ε : Prob) {S : Set (MState d)} (hS₁ : IsCompact S)
    (hS₂ : Convex ℝ (MState.M '' S)) : ⨆ σ ∈ S, β_ ε(ρ‖{σ}) = β_ ε(ρ‖S) := by

  --Work out the case where S is empty, so we can now assume it's nonempty
  rcases S.eq_empty_or_nonempty with rfl|hnS
  · simpa using bot_eq_zero''
  --Upgrade this fact to an instance
  have _ : Nonempty S := hnS.to_subtype

  --Needs the minimax theorem. ... TODO: I think the statement of `minimax` is actually incorrect and requires
  --some information about the sets `S` and `T` being nonempty. Also, maybe it should change from `⨅ x ∈ S` to
  --`⨅ (x : ↑S)` or something.
  simp only [OptimalHypothesisRate, Set.mem_singleton_iff, iSup_iSup_eq_left]
  have hmm := minimax (M := HermitianMat d ℂ)

  --This will be the `MState.exp_val` function, but bundled as a bilinear form.
  let f : LinearMap.BilinForm ℝ (HermitianMat d ℂ) := HermitianMat.inner_BilinForm
  let S' : Set (HermitianMat d ℂ) := MState.M '' S
  let T' : Set (HermitianMat d ℂ) := { m | MState.exp_val (1 - m) ρ ≤ ε ∧ 0 ≤ m ∧ m ≤ 1 }
  replace hS₁ : IsCompact S' := by
    exact hS₁.image MState.Continuous_Matrix
  have hT₁ : IsCompact T' := by
    have hC₁ : IsCompact {m : HermitianMat d ℂ | 0 ≤ m ∧ m ≤ 1} :=
      HermitianMat.unitInterval_IsCompact
    have hC₂ : IsClosed {m | MState.exp_val (1 - m) ρ ≤ ε} := by
      --This is a linear constraint and so has a closed image
      change IsClosed ((fun m ↦ ρ.M.inner_BilinForm (1 - m)) ⁻¹' (Set.Iic ε))
      refine IsClosed.preimage ?_ isClosed_Iic
      fun_prop
    convert hC₁.inter_left hC₂
  have hT₂ : Convex ℝ T' := by
    --We *could* get this from a more general fact that any linear subspace is convex,
    --and the intersection of convex spaces is convex, and this is an intersection of
    --three convex spaces. That would be more broken-down and lemmaified.
    dsimp [T']
    rintro x ⟨hx₁, hx₂, hx₃⟩ y ⟨hy₁, hy₂, hy₃⟩ a b ha hb hab
    rw [← eq_sub_iff_add_eq'] at hab
    subst b
    refine And.intro ?_ (And.intro ?_ ?_)
    · simp [MState.exp_val, HermitianMat.inner_left_sub, HermitianMat.inner_left_distrib] at hx₁ hy₁ ⊢
      linear_combination a * hx₁ + (1 - a) * hy₁
    · apply HermitianMat.convex_cone <;> assumption
    · rw [← sub_nonneg] at hx₃ hy₃ ⊢
      convert HermitianMat.convex_cone hx₃ hy₃ ha hb using 1
      simp only [sub_smul, one_smul, smul_sub]
      abel

  specialize hmm f S' T' hS₁ hT₁ hS₂ hT₂
  ext
  rw [← iSup_subtype'']

  convert Eq.trans (Set.Icc.coe_iSup (ι := S) (zero_le_one (α := ℝ))) ?_
  · simp only [CompleteLattice.toCompleteSemilatticeSup, Prob.instCompleteLinearOrder,
      CompleteLattice.toConditionallyCompleteLattice]
    congr
    ext
    split_ifs with hs
    . simp [hs]
    · simp [hs]
      rfl
  -- let f'' : ↑S → Prob := fun i
  --   ↦ ⨅ (T : { m // MState.exp_val (1 - m) ρ ≤ ε ∧ 0 ≤ m ∧ m ≤ 1 }), ⟨MState.exp_val (Subtype.val T) (Subtype.val i),
  --     OptimalHypothesisRate.proof_1 ρ ε T (Subtype.val i)⟩
  -- have h_sub := @Set.Icc.coe_iSup (ι := S) (α := ℝ) (a := 0) (b := 1) _ (zero_le_one) _ (S := f'')
  -- dsimp [f''] at h_sub
  --No, this is stupid, there has to be a better way
  sorry

--Maybe should be phrased in terms of `0 < ...` instead? Maybe belongs in another file? It's kiinnnd of specialized..
theorem ker_diagonal_prob_eq_bot {q : Prob} (hq₁ : 0 < q) (hq₂ : q < 1) :
    LinearMap.ker (HermitianMat.diagonal (Distribution.coin q ·)).val.toLin' = ⊥ := by
  have h : (HermitianMat.diagonal (Distribution.coin q ·)).val.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i; fin_cases i
    · simpa
    · simpa [← Complex.ofReal_one, Complex.real_lt_real]
  --Use the fact that m.PosDef → LinearMap.ker M.toLin' = ⊥
  sorry

variable {d₂ : Type*} [Fintype d₂] [DecidableEq d₂] in
/-- Lemma S1 -/
theorem optimalHypothesisRate_antitone (ρ σ : MState d) (ℰ : CPTPMap d d₂) (ε : Prob) :
    β_ ε(ρ‖{σ}) ≤ β_ ε(ℰ ρ‖{ℰ σ}) := by
  simp only [of_singleton]
  obtain ⟨ℰdualSubtype, h⟩ :
      ∃ e : ({ m : HermitianMat d₂ ℂ // (ℰ ρ).exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1} →
      { m : HermitianMat d ℂ // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1}),
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

--PULLOUT
instance : Nontrivial Prob where
  exists_pair_ne := ⟨0, 1, by simp [← Prob.ne_iff]⟩

@[simp]
theorem _root_.Prob.sub_zero (p : Prob) : p - 0 = p := by
  ext1; simp [Prob.coe_sub]

@[simp]
theorem _root_.Prob.negLog_one : Prob.negLog 1 = 0 := by
  simp [Prob.negLog]

open scoped HermitianMat in
open scoped Prob in
/-- This is from [Strong converse exponents for a quantum channel discrimination problem
and quantum-feedback-assisted communication](https://doi.org/10.1007/s00220-016-2645-4), Lemma 5.

It seems like this is actually true for all 0 < α (with appropriate modifications at α = 1), but we only need
it for the case of 1 < α.
-/
theorem Ref81Lem5 (ρ σ : MState d) (ε : Prob) (hε : ε < 1) (α : ℝ) (hα : 1 < α) :
    —log β_ ε(ρ‖{σ}) ≤ D̃_ α(ρ‖σ) + —log (1 - ε) *
      (.ofNNReal ⟨α, zero_le_one.trans hα.le⟩) / (.ofNNReal ⟨α - 1, sub_nonneg_of_le hα.le⟩)
    := by
  generalize_proofs pf1 pf2
  --If ρ isn't in the support of σ, the right hand side is just ⊤. (The left hand side is not, necessarily!)
  by_cases h_supp : LinearMap.ker σ.val.toLin' ≤ LinearMap.ker ρ.val.toLin'
  swap
  · simp [SandwichedRelRentropy, h_supp]
  --Note that we actually only need this for 0 < ε, not 0 ≤ ε. This is also how it was proved in the original
  --reference. But Hayashi says it's true for ε = 0. Likely best handled with a special by_cases for ε = 0?
  --If this case is too much of a pain we can drop it.
  by_cases h : ε = 0
  · subst h
    simp only [OptimalHypothesisRate, Set.Icc.coe_zero, Set.mem_singleton_iff, iSup_iSup_eq_left,
      Prob.sub_zero, Prob.negLog_one, zero_mul, ENNReal.zero_div, add_zero]
    --Take m_opt to be the projector of ρ, i.e. 0 on ρ's kernel and 1 elsewhere.
    let m_opt : HermitianMat d ℂ := {0 ≤ₚ ρ}
    sorry

  replace h : 0 < ε := zero_lt_iff.mpr h
  have h₂ : 0 < 1 - ε.val := by
    change ε.val < 1 at hε
    linarith

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
  let p : Prob := 1 - ε
  set q : Prob := β_ ε(ρ‖{σ})
  let p2 : MState (Fin 2) := .ofClassical <| .coin p
  let q2 : MState (Fin 2) := .ofClassical <| .coin q

  have hp : 0 < p := show (0 : ℝ) < p by simp [p, hε]

  --Show there's a lower bound on β_ε, that you can't do perfect discrimination
  --It's possible that we actually don't want this here, that it should "follow"
  --from the main proof.
  have hq : 0 < q := by
    --The optimal hypothesis rate is positive
    simp_rw [q, OptimalHypothesisRate, Set.mem_singleton_iff, iSup_iSup_eq_left]
    --Assume the converse: that the infimum is zero. The set of such T's is inhabited
    --and closed, so there is some T that attains the value zero. This T has zero
    --inner product with σ (`σ.exp_val T = 0`), and yet (by definition of T's type) we
    --also have that `ρ.exp_val (1 - T) ≤ ε < 1`. So `T` lives entirely in σ's kernel,
    --which (by `h_supp`) is contained in ρ's kernel. So
    --`ρ.exp_val (1 - T) = ρ.exp_val 1 - ρ.exp_val T = ρ.trace - 0 = 1`, a contradiction.
    sorry

  have hq₂ : q < 1 := by
    --The optimal hypothesis rate is finite
    simp_rw [q, OptimalHypothesisRate, Set.mem_singleton_iff, iSup_iSup_eq_left]
    --Assume the converse: the infimum is exactly one. Then all T's get exactly 1. This can
    --only happen if the support of σ is entirely contained in the support of T, where
    --T is 1. By `h_supp`, the support of ρ is contained in the support of σ, so it is
    --also contained, and then `ρ.exp_val T = 1` too, so `ρ.exp_val (1 - T) = 0`. Then
    --we can freely add some more to
    sorry

  suffices —log q ≤ D̃_ α(p2‖q2) + —log (1 - ε) * (.ofNNReal ⟨α, pf1⟩) / (.ofNNReal ⟨α - 1, pf2⟩) by
    refine this.trans (add_le_add_right ?_ _)
    --Show that this is an instance of the Data Processing Inequality
    obtain ⟨Φ, hΦ₁, hΦ₂⟩ : ∃ (Φ : CPTPMap d (Fin 2)), p2 = Φ ρ ∧ q2 = Φ σ := by
      --The relevant map here is to take the T that optimizes inside β_ ε (ρ‖{σ}),
      --and use the projective measurement onto {T, 1 - T}. This achieves the optimum
      --discrimination rate on σ, and so gives the outcome distribution q2. And it
      --is tight on the bound that Tr[ρ T] = ε, which is what gives the outcome distribution
      --p2. Why is it tight? Well, if it's not, then we can find another T' at least as
      --good as T by adding some more that increases its trace up to ε; and this can only
      --ever raise the detection probability on ρ. (The fact that this tight T exists should
      --be its own lemma, probably.)
      sorry
    rw [hΦ₁, hΦ₂]
    exact SandwichedRenyiEntropy.DPI hα ρ σ Φ

  --The Renyi entropy is finite
  rw [SandwichedRelRentropy, if_pos ?_, if_neg hα.ne']; swap
  · suffices LinearMap.ker q2.val.toLin' = ⊥ by
      simp only [MState.toSubtype_eq_coe, HermitianMat.val_eq_coe, this, bot_le]
    --q2 has eigenvalues β_ ε(ρ‖{σ}) and 1-β_ ε(ρ‖{σ}), so as long as β_ ε(ρ‖{σ}) isn't 0 or 1,
    --this is true.
    exact ker_diagonal_prob_eq_bot hq hq₂

  --The logs are finite
  rw [Prob.negLog, Prob.negLog, if_neg hq.ne', if_neg]
  swap
  · simpa [Subtype.eq_iff, Prob.coe_sub] using h₂.ne'

  --Turn the ENNReal problem into a Real problem
  have hα₂ : Subtype.mk _ pf2 ≠ 0 := by
    change ¬(_ = Subtype.mk 0 _)
    simp only [mk_zero, Nonneg.mk_eq_zero]
    linarith
  rw [← ENNReal.coe_mul, ← ENNReal.coe_div hα₂, ← ENNReal.coe_add, ENNReal.coe_le_coe]
  clear hα₂
  simp only [← coe_le_coe, coe_mk, NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul, neg_mul]
  clear pf1 pf2

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

  trans (Real.log (p ^ α * q ^ (1 - α)) - Real.log (1 - ε.val) * α) / (α - 1)
  · rw [Real.log_mul]
    rotate_left
    · exact (Real.rpow_pos_of_pos hp _).ne'
    · exact (Real.rpow_pos_of_pos hq _).ne'
    simp only [p, Prob.coe_one_minus]
    rw [Real.log_rpow (by linarith), mul_comm α, add_sub_cancel_left]
    rw [Real.log_rpow (x := q.val) hq]
    rw [mul_comm, ← mul_div, mul_comm, show (1 - α) = -(α - 1) by abel]
    simp [-neg_sub, neg_div, div_self (a := α - 1) (by linarith)]
  · rw [div_le_div_iff_of_pos_right (by linarith), tsub_le_iff_right]
    nth_rewrite 4 [Prob.coe_sub]
    simp only [Set.Icc.coe_one, sub_nonneg, Prob.coe_le_one, sup_of_le_left, sub_add_cancel]
    apply Real.log_le_log
    · refine mul_pos (Real.rpow_pos_of_pos hp _) (Real.rpow_pos_of_pos hq _)
    rw [le_add_iff_nonneg_right]
    refine mul_nonneg (Real.rpow_nonneg ?_ _) (Real.rpow_nonneg ?_ _)
    · exact sub_nonneg_of_le p.2.2
    · exact sub_nonneg_of_le q.2.2
