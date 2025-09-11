import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Analysis.Subadditive
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Data.EReal.Basic

import QuantumInfo.Finite.CPTPMap
import QuantumInfo.Finite.Entropy
import QuantumInfo.Finite.POVM

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
open Prob

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The optimal hypothesis testing rate, for a tolerance ε: given a state ρ and a set of states S,
the optimum distinguishing rate that allows a probability ε of errors. -/
noncomputable def OptimalHypothesisRate (ρ : MState d) (ε : Prob) (S : Set (MState d)) : Prob :=
  ⨅ T : { m : HermitianMat d ℂ // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1},
    ⨆ σ ∈ S, ⟨_, σ.exp_val_prob T.prop.right⟩

scoped[OptimalHypothesisRate] notation "β_" ε " (" ρ "‖" S ")" =>  OptimalHypothesisRate ρ ε S

namespace OptimalHypothesisRate

/-- The space of strategies `T` in `OptimalHypothesisRate` is inhabited, we always have some valid strategy. -/
instance iInf_Inhabited (ρ : MState d) (ε : Prob) :
    Inhabited { m // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1 } :=
  ⟨1, by simp⟩

instance (ρ : MState d) (ε : Prob) : Inhabited {m | ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1} :=
  iInf_Inhabited ρ ε

/-- The space of strategies `T` in `OptimalHypothesisRate` is compact. -/
theorem iInf_IsCompact (ρ : MState d) (ε : Prob) : IsCompact { m | ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1 } := by
  have hC₁ : IsCompact {m : HermitianMat d ℂ | 0 ≤ m ∧ m ≤ 1} :=
    HermitianMat.unitInterval_IsCompact
  have hC₂ : IsClosed {m | ρ.exp_val (1 - m) ≤ ε} := by
    --This is a linear constraint and so has a closed image
    change IsClosed ((fun m ↦ ρ.M.inner_BilinForm (1 - m)) ⁻¹' (Set.Iic ε))
    refine IsClosed.preimage ?_ isClosed_Iic
    fun_prop
  exact hC₁.inter_left hC₂

/-- The space of strategies `T` in `OptimalHypothesisRate` is convex. -/
theorem iInf_IsConvex (ρ : MState d) (ε : Prob) : Convex ℝ { m | ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1 } := by
  --We *could* get this from a more general fact that any linear subspace is convex,
  --and the intersection of convex spaces is convex, and this is an intersection of
  --three convex spaces. That would be more broken-down and lemmaified.
  rintro x ⟨hx₁, hx₂, hx₃⟩ y ⟨hy₁, hy₂, hy₃⟩ a b ha hb hab
  rw [← eq_sub_iff_add_eq'] at hab
  subst b
  refine And.intro ?_ (And.intro ?_ ?_)
  · simp only [MState.exp_val, HermitianMat.inner_left_sub, HermitianMat.inner_one, MState.tr,
      tsub_le_iff_right, HermitianMat.inner_left_distrib, HermitianMat.inner_smul] at hx₁ hy₁ ⊢
    linear_combination a * hx₁ + (1 - a) * hy₁
  · apply HermitianMat.convex_cone <;> assumption
  · --Something's wrong with type class inference that's taking wayyy longer than it should.
    --DFunLike.coe is being unfolded tonnnnss of times.
    rw [← sub_nonneg] at hx₃ hy₃ ⊢
    convert HermitianMat.convex_cone hx₃ hy₃ ha hb using 1
    simp only [sub_smul, one_smul, smul_sub]
    abel

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

/-- There exists an optimal T for the hypothesis testing, that is, it's a minimum
and not just an infimum. This states we have `1 - ε ≤ ρ.exp_val T`, but we can always
"worsen" T to make that bound tight, which is `exists_min`. -/
theorem exists_min' (ρ : MState d) (ε : Prob) (S : Set (MState d)):
    ∃ (T : { m : HermitianMat d ℂ // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1}),
      (⨆ σ ∈ S, ⟨_, σ.exp_val_prob T.prop.right⟩ = β_ ε(ρ‖S))
      ∧ 1 - ε ≤ ρ.exp_val T := by
  have _ : Nonempty d := ρ.nonempty
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simpa [-Subtype.exists] using ⟨rfl, ⟨1, by simp⟩, by simp⟩
  rw [← Set.nonempty_coe_sort] at hS
  obtain ⟨T, hT₁, hT₂⟩ := IsCompact.exists_isMinOn (α := Prob)
    (isCompact_iff_isCompact_univ.mp (iInf_IsCompact ρ ε)) Set.univ_nonempty
    (f := fun T ↦ ⨆ σ ∈ S, ⟨_, σ.exp_val_prob T.prop.right⟩)
    (by
      have h := HermitianMat.inner_BilinForm.continuous_iSup_fst
        (Bornology.isBounded_induced.mp (Bornology.IsBounded.all S))
      apply Continuous.continuousOn
      simp_rw [← iSup_subtype'', subtype_val_iSup' (ι := S)]
      refine Continuous.subtype_mk ?_ _
      refine Continuous.comp (g := fun T ↦ ⨆ (i : S), i.val.exp_val T) ?_ continuous_subtype_val
      convert h with T
      rw [← sSup_image' (s := S) (f := fun i ↦ i.exp_val T)]
      rw [← sSup_image' (s := (MState.M '' S)) (f := fun i ↦ i.inner_BilinForm T)]
      simp [Set.image, MState.exp_val]
    )
  clear hT₁

  use T
  constructor
  · simp only [isMinOn_univ_iff] at hT₂
    rw [OptimalHypothesisRate]
    --Why is the following three bundled together not a theorem? Is it, and I can't find it? TODO
    apply le_antisymm
    · exact le_iInf hT₂
    · exact iInf_le_iff.mpr fun _ a ↦ a T
  · simpa [MState.exp_val_sub, add_comm (ε : ℝ) _] using T.2.1

--TODO: Maybe we should define these two instances.
-- Then we can get rid of `Prob.sub_zero` and use the generic `tsub_zero`.
-- #synth AddCommMonoid Prob
-- #synth OrderedSub Prob

/-- There exists an optimal T for the hypothesis testing, that is, it's a minimum and
not just an infimum. This tightens the `T` from `exists_min'` to a `⟪ρ,T⟫ = 1 - ε` bound. -/
theorem exists_min (ρ : MState d) (ε : Prob) (S : Set (MState d)):
    ∃ (T : { m : HermitianMat d ℂ // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1}),
      (⨆ σ ∈ S, ⟨_, σ.exp_val_prob T.prop.right⟩ = β_ ε(ρ‖S))
      ∧ ρ.exp_val T = 1 - ε := by
  obtain ⟨T, hT₁, hT₂⟩ := exists_min' ρ ε S

  --Instead of just `use T`, we (may) have to reduce it so that it saturates the ⟪ρ,T⟫ = 1 - ε bound.
  --We do this by multiplying it by a scalar less than 1 to get a `T'`. Since this operator is less
  --than T, it's still optimal in terms of achieving `β_ ε(ρ‖S)`, but it can get the `1 - ε` bound instead.
  set δ := ρ.exp_val ↑T - (1 - ε)-- with δ_def
  by_cases hδ : δ = 0
  · use T, hT₁
    linarith
  replace hδ : 0 < δ := by linarith +splitNe
  have hδ_le : δ ≤ 1 := by
    linarith [ρ.exp_val_le_one T.2.2.2, ε.2]

  have hTr : 0 < ρ.exp_val T := by
    linarith [ε.coe_le_one]

  set T' : HermitianMat d ℂ :=
    (1 - δ / ρ.exp_val T) • T with hT'_def
  have hT'_le : T' ≤ T := by
    rw [← one_smul ℝ T.val, hT'_def]
    gcongr
    · exact T.2.2.1
    · simp; positivity
  have hρT' : ρ.exp_val (1 - T') = ε := by
    simp [T', MState.exp_val_sub, δ, field]

  have hT' : ρ.exp_val (1 - T') ≤ ε ∧ 0 ≤ T' ∧ T' ≤ 1 := by
    use hρT'.le
    constructor
    · simp [T']
      refine smul_nonneg ?_ T.2.2.1
      bound
    · exact hT'_le.trans T.2.2.2
  use ⟨T', hT'⟩

  constructor
  · rw [OptimalHypothesisRate] at hT₁ ⊢
    apply le_antisymm
    · apply le_iInf
      intro i
      refine le_trans ?_ (le_of_eq_of_le hT₁ ?_)
      · gcongr
      · exact iInf_le_iff.mpr fun _ a ↦ a i
    · exact iInf_le_iff.mpr fun _ a ↦ a ⟨T', hT'⟩
  · simp [MState.exp_val_sub, ← hρT']

/-- When the allowed Type I error `ε` is less than 1 (so, we have some limit on our errors),
and the kernel of the state `ρ` contains the kernel of some element in `S`, then the optimal
hypothesis rate is positive - there is some lower bound on the type II errors we'll see. In
other words, under these conditions, we cannot completely avoid type II errors. -/
theorem pos_of_lt_one {ρ : MState d} (S : Set (MState d))
  (hρ : ∃ σ ∈ S, σ.M.ker ≤ ρ.M.ker)
  {ε : Prob} (hε : ε < 1) : 0 < β_ ε(ρ‖S) := by
  obtain ⟨σ, hσ₁, hσ₂⟩ := hρ
  --Assume the converse: that the infimum is zero. The set of such T's is inhabited
  --and closed, so there is some T that attains the value zero. This T has zero
  --inner product with σ (`σ.exp_val T = 0`), and yet (by definition of T's type) we
  --also have that `ρ.exp_val (1 - T) ≤ ε < 1`. So `T` lives entirely in σ's kernel,
  --which (by `h_supp`) is contained in ρ's kernel. So
  --`ρ.exp_val (1 - T) = ρ.exp_val 1 - ρ.exp_val T = ρ.trace - 0 = 1`, a contradiction.
  by_contra h
  obtain ⟨⟨T, hT₁, hT₂, hT₃⟩, hT₄, hT₅⟩ := exists_min ρ ε S
  rw [← bot_eq_zero'', not_bot_lt_iff] at h
  rw [h, iSup_eq_bot, bot_eq_zero''] at hT₄
  specialize hT₄ σ
  simp only [iSup_pos hσ₁, Subtype.ext_iff, Set.Icc.coe_zero, MState.exp_val] at hT₄
  rw [HermitianMat.inner_zero_iff σ.zero_le hT₂] at hT₄
  replace hT₁ : ρ.exp_val (1 - T) ≠ 1 := (lt_of_le_of_lt hT₁ hε).ne
  absurd hT₁
  rw [ρ.exp_val_eq_one_iff ?_, sub_sub_cancel]
  · grw [← hT₄]
    rwa [HermitianMat.ker, HermitianMat.ker, ContinuousLinearMap.ker_le_ker_iff_range_le_range] at hσ₂
    · simp
    · simp
  · exact sub_le_self 1 hT₂

--Lemma 3 from Hayashi
theorem Lemma3 {ρ : MState d} (ε : Prob) {S : Set (MState d)} (hS₁ : IsCompact S)
    (hS₂ : Convex ℝ (MState.M '' S)) : ⨆ σ ∈ S, β_ ε(ρ‖{σ}) = β_ ε(ρ‖S) := by

  --Work out the case where S is empty, so we can now assume it's nonempty
  rcases S.eq_empty_or_nonempty with rfl|hnS
  · simpa using bot_eq_zero''
  --Upgrade this fact to an instance
  have _ : Nonempty S := hnS.to_subtype

  simp only [OptimalHypothesisRate, Set.mem_singleton_iff, iSup_iSup_eq_left]

  --This parts needs the minimax theorem. Set up the relevant sets and hypotheses.
  --The function `f` will be the `MState.exp_val` function, but bundled as a bilinear form.
  let f : LinearMap.BilinForm ℝ (HermitianMat d ℂ) := HermitianMat.inner_BilinForm
  let S' : Set (HermitianMat d ℂ) := MState.M '' S
  let T' : Set (HermitianMat d ℂ) := { m | ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1 }

  have hS'₁ : IsCompact S' := hS₁.image MState.Continuous_HermitianMat

  have hT'₁ : IsCompact T' := iInf_IsCompact ρ ε

  have hT'₂ : Convex ℝ T' := iInf_IsConvex ρ ε

  have hS'₃ : S'.Nonempty := by simpa only [Set.image_nonempty, S']

  have hT'₃ : T'.Nonempty := Set.Nonempty.of_subtype

  ext1 --turn it from Prob equality into ℝ equality
  convert minimax (M := HermitianMat d ℂ) f S' T' hS'₁ hT'₁ hS₂ hT'₂ hS'₃ hT'₃
  --The remaining twiddling is about moving the casts inside the iInf's and iSup's.
  --In a better world, this would be mostly handled by some clever simps or push_cast's.
  · have hi := iSup_range' (ι := S) (fun x ↦ ⨅ (y : T'), (f x) ↑y) (·)
    rw [← Set.image_eq_range] at hi
    rw [← iSup_subtype'', Set.Icc.coe_iSup (zero_le_one), hi]
    congr!
    exact Set.Icc.coe_iInf zero_le_one
  · rw [Set.Icc.coe_iInf (ι := T') zero_le_one]
    congr! 2 with y
    have hi := iSup_range' (ι := S) (fun x ↦ (f x) ↑y) (·)
    rw [← Set.image_eq_range] at hi
    rw [← iSup_subtype'', Set.Icc.coe_iSup zero_le_one, hi]
    rfl

--Maybe should be phrased in terms of `0 < ...` instead? Maybe belongs in another file? It's kiinnnd of specialized..
theorem ker_diagonal_prob_eq_bot {q : Prob} (hq₁ : 0 < q) (hq₂ : q < 1) :
    HermitianMat.ker (.diagonal (Distribution.coin q ·)) = ⊥ := by
  apply Matrix.PosDef.toLin_ker_eq_bot
  apply Matrix.PosDef.diagonal
  intro i; fin_cases i
  · simpa
  · simpa [← Complex.ofReal_one, Complex.real_lt_real]

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
  by_cases h_supp : σ.M.ker ≤ ρ.M.ker
  swap
  · simp [SandwichedRelRentropy, h_supp]

  --Now we know that ρ.support ≤ σ.support. This is the main case we actually care about.
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

  have h₂ : 0 < 1 - ε.val := by
    change ε.val < 1 at hε
    linarith

  let p : Prob := 1 - ε
  set q : Prob := β_ ε(ρ‖{σ})
  let p2 : MState (Fin 2) := .ofClassical <| .coin p
  let q2 : MState (Fin 2) := .ofClassical <| .coin q

  --Show there's a lower bound on β_ε, that you can't do perfect discrimination
  --It's possible that we actually don't want this here, that it should "follow"
  --from the main proof.
  have hq : 0 < q := pos_of_lt_one {σ} ⟨σ, rfl, h_supp⟩ hε

  suffices —log q ≤ D̃_ α(p2‖q2) + —log (1 - ε) * (.ofNNReal ⟨α, pf1⟩) / (.ofNNReal ⟨α - 1, pf2⟩) by
    refine this.trans (add_le_add_right ?_ _)
    --Show that this is an instance of the Data Processing Inequality
    obtain ⟨Φ, hΦ₁, hΦ₂⟩ : ∃ (Φ : CPTPMap d (Fin 2)), p2 = Φ ρ ∧ q2 = Φ σ := by
      --The relevant map here is to take the T that optimizes inside β_ ε (ρ‖{σ}),
      --and use the projective measurement onto {T, 1 - T}. This achieves the optimum
      --discrimination rate on σ, and so gives the outcome distribution q2. And it
      --is tight on the bound that Tr[ρ T] = ε.

      --Get the measurement operator T.
      obtain ⟨T, hT₁, hT₂⟩ := exists_min ρ ε {σ}
      simp only [Set.mem_singleton_iff, iSup_iSup_eq_left] at hT₁
      --Turn it into a POVM (probably want to have lemmas around this ideally)
      let Λ : POVM (Fin 2) d := {
        mats i := if i = 0 then T else 1 - T
        zero_le i := by
          split
          · exact T.prop.2.1
          · exact HermitianMat.zero_le_iff.mpr T.prop.2.2
        normalized := by simp
      }
      use Λ.measureDiscard
      simp only [POVM.measureDiscard_apply, p2, q2]
      constructor
      · congr
        rw [Distribution.coin_eq_iff]
        ext
        dsimp [MState.exp_val] at hT₂
        simp [POVM.measure, Λ, p, Distribution.mk', coe_one_minus, ← hT₂, HermitianMat.inner_comm]
      · congr
        rw [Distribution.coin_eq_iff]
        ext
        dsimp [POVM.measure, Λ, q]
        rw [← hT₁]
        exact HermitianMat.inner_comm _ _
    rw [hΦ₁, hΦ₂]
    exact sandwichedRenyiEntropy_DPI hα.le ρ σ Φ

  --If q = 1, this inequality is trivial
  by_cases hq₂ : q = 1
  · rw [hq₂]
    simp

  replace hq₂ : q < 1 := show q.val < 1 by
    linarith +splitNe [q.coe_le_one, unitInterval.coe_ne_one.mpr hq₂]


  --The Renyi entropy is finite
  rw [SandwichedRelRentropy, if_pos ?_]; swap
  · suffices q2.M.ker = ⊥ by
      simp only [this, bot_le]
    --q2 has eigenvalues β_ ε(ρ‖{σ}) and 1-β_ ε(ρ‖{σ}), so as long as β_ ε(ρ‖{σ}) isn't 0 or 1,
    --this is true.
    exact ker_diagonal_prob_eq_bot hq hq₂

  conv => enter [2, 1, 1, 1]; rw [if_neg hα.ne']

  --The logs are finite
  rw [Prob.negLog, Prob.negLog, if_neg hq.ne']
  rw [if_neg (show 1 - ε ≠ 0 by simpa [Subtype.eq_iff, Prob.coe_sub] using h₂.ne')]

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
      rw [← Real.rpow_natCast_mul (by bound)]
      rw [← Real.rpow_mul q.zero_le]
      rw [Real.mul_rpow (by bound) (by positivity)]
      rw [← Real.rpow_natCast_mul (by bound)]
      rw [← Real.rpow_mul (by bound)]
      congr <;> simp [field]

  by_cases h : ε = 0
  · simp [h, p, @Real.zero_rpow α (by positivity)]
    apply Eq.le
    rw [Real.log_rpow hq]
    have : α - 1 ≠ 0 := by linarith
    field_simp
    ring_nf

  have hp : 0 < p := show (0 : ℝ) < p by simp [p, hε]

  replace h : 0 < ε := zero_lt_iff.mpr h
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

theorem rate_pos_of_smul_pos {ε : Prob} {d : Type*} [Fintype d] [DecidableEq d] {ρ σ₁ σ₂ : MState d}
    (hσ₂ : 0 < β_ ε(ρ‖{σ₂})) {c : ℝ} (hc : 0 < c) (hσ : c • σ₂ ≤ σ₁.M) : 0 < β_ ε(ρ‖{σ₁}) := by
  simp only [of_singleton, lt_iInf_iff] at hσ₂ ⊢
  rcases hσ₂ with ⟨⟨b, _, hb_le⟩, hb_pos, hb⟩
  change 0 < b at hb_pos --TODO simp thm / lemma
  use ⟨(min c 1) * b, by positivity, by bound⟩
  constructor
  · change 0 < (min c 1) * b --TODO simp thm / lemma
    positivity
  intro i
  specialize hb i
  rw [Subtype.mk_le_mk, MState.exp_val] at hb ⊢
  replace hb : c * b ≤ (c • σ₂.M).inner i := by
    rwa [← mul_le_mul_iff_of_pos_left hc, ← HermitianMat.smul_inner] at hb
  grw [min_le_left]
  refine hb.trans (HermitianMat.inner_mono' i.2.2.1 hσ)

@[fun_prop]
theorem rate_Continuous_singleton {ε : Prob} {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) :
    Continuous fun σ ↦ β_ ε(ρ‖{σ}) := by
  have h := LinearMap.BilinForm.continuous_iInf_fst
    HermitianMat.inner_BilinForm.flip (S := { m | ρ.exp_val (1 - m) ≤ ↑ε ∧ 0 ≤ m ∧ m ≤ 1 })
    ((Metric.isBounded_Icc 0 1).subset (Set.setOf_subset_setOf_of_imp fun _ ↦ And.right))
  simp only [of_singleton]
  conv => enter [1, σ]; rw [subtype_val_iInf']
  exact Continuous.subtype_mk (h.comp MState.Continuous_HermitianMat) _
