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

instance (ρ : MState d) (ε : Prob) : Inhabited {m | MState.exp_val (1 - m) ρ ≤ ε ∧ 0 ≤ m ∧ m ≤ 1} :=
  iInf_Inhabited ρ ε

/-- The space of strategies `T` in `OptimalHypothesisRate` is compact. -/
theorem iInf_IsCompact (ρ : MState d) (ε : Prob) : IsCompact { m | MState.exp_val (1 - m) ρ ≤ ε ∧ 0 ≤ m ∧ m ≤ 1 } := by
  have hC₁ : IsCompact {m : HermitianMat d ℂ | 0 ≤ m ∧ m ≤ 1} :=
    HermitianMat.unitInterval_IsCompact
  have hC₂ : IsClosed {m | MState.exp_val (1 - m) ρ ≤ ε} := by
    --This is a linear constraint and so has a closed image
    change IsClosed ((fun m ↦ ρ.M.inner_BilinForm (1 - m)) ⁻¹' (Set.Iic ε))
    refine IsClosed.preimage ?_ isClosed_Iic
    fun_prop
  exact hC₁.inter_left hC₂

/-- The space of strategies `T` in `OptimalHypothesisRate` is convex. -/
theorem iInf_IsConvex (ρ : MState d) (ε : Prob) : Convex ℝ { m | MState.exp_val (1 - m) ρ ≤ ε ∧ 0 ≤ m ∧ m ≤ 1 } := by
  --We *could* get this from a more general fact that any linear subspace is convex,
  --and the intersection of convex spaces is convex, and this is an intersection of
  --three convex spaces. That would be more broken-down and lemmaified.
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
and not just an infimum. -/
theorem exists_min (ρ : MState d) (ε : Prob) (S : Set (MState d)):
    ∃ (T : { m : HermitianMat d ℂ // ρ.exp_val (1 - m) ≤ ε ∧ 0 ≤ m ∧ m ≤ 1}),
      ⨆ σ ∈ S, ⟨_, σ.exp_val_prob T.prop.right⟩ = β_ ε(ρ‖S) := by
  have _ : Nonempty d := ρ.nonempty
  convert IsCompact.exists_isMinOn (α := Prob) (β := {m // MState.exp_val (1 - m) ρ ≤ ε ∧ 0 ≤ m ∧ m ≤ 1}) (s := Set.univ)
    ?_ ?_ (f := fun T ↦ ⨆ σ ∈ S, ⟨_, σ.exp_val_prob T.prop.right⟩) ?_
  · rename_i T
    simp only [Set.mem_univ, true_and]
    constructor
    · simp only [isMinOn_univ_iff]
      intro h T₂
      rw [h, OptimalHypothesisRate, iInf_le_iff]
      exact fun _ a ↦ a T₂
    · intro h
      symm
      convert h.iInf_eq (Set.mem_univ _)
      exact Equiv.iInf_congr (Equiv.Set.univ _).symm (fun _ ↦ by rfl)
  · rw [← isCompact_iff_isCompact_univ ]
    exact iInf_IsCompact ρ ε
  · exact Set.univ_nonempty
  · rw [← continuous_iff_continuousOn_univ]
    suffices Continuous
        (fun (T : { m // MState.exp_val (1 - m) ρ ≤ ↑ε ∧ 0 ≤ m ∧ m ≤ 1 }) ↦ ⨆ σ ∈ S, σ.exp_val T) by
      convert Continuous.subtype_mk this ?_
      · --need the silly h_stupid below
        sorry
      · --this part is REALLY stupid and definitely there's a better way. Maybe that way is making simp lemmas.
        rcases S.eq_empty_or_nonempty with rfl|hnS
        · simp
        intro x
        constructor
        · apply le_ciSup_of_le ?_ ρ
          classical rw [ciSup_eq_ite]
          · split
            · exact (ρ.exp_val_prob x.prop.right).left
            · simp
          use 1; simp [upperBounds]
          all_goals (
            intro y
            classical rw [ciSup_eq_ite]
            split
            · exact (y.exp_val_prob x.prop.right).right
            · simp)
        · rw [ciSup_le_iff]
          swap; use 1; simp [upperBounds]
          all_goals (
            intro y
            classical rw [ciSup_eq_ite]
            split
            · exact (y.exp_val_prob x.prop.right).right
            · simp)
    suffices h : Continuous (fun (T : HermitianMat d ℂ) ↦ ⨆ σ ∈ S, σ.exp_val T) from
      Pi.continuous_restrict_apply _ h
    unfold MState.exp_val
    --Should be something `Continuous (fun x ↦ iSup (fun y ↦ f x y))` from `Continuous f`.
    sorry

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
  obtain ⟨⟨T, hT₁, hT₂, hT₃⟩, hT₄⟩ := exists_min ρ ε S
  rw [← bot_eq_zero'', not_bot_lt_iff] at h
  rw [h, iSup_eq_bot, bot_eq_zero''] at hT₄
  specialize hT₄ σ
  simp only [iSup_pos hσ₁, Subtype.ext_iff, Set.Icc.coe_zero, MState.exp_val] at hT₄
  rw [HermitianMat.inner_zero_iff σ.zero_le hT₂] at hT₄
  simp only [MState.toMat_M] at hT₄
  replace hT₁ : ρ.exp_val (1 - T) ≠ 1 := (lt_of_le_of_lt hT₁ hε).ne
  absurd hT₁
  rw [ρ.exp_val_eq_one_iff (HermitianMat.zero_le_iff.mpr hT₃) (sub_le_self 1 hT₂), sub_sub_cancel]
  sorry
  --fix when we change everything to toEuclideanLin
  -- rw [← Matrix.ker_range_antitone ρ.Hermitian σ.Hermitian] at hσ₂
  -- exact le_trans hσ₂ hT₄.left

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
  let T' : Set (HermitianMat d ℂ) := { m | MState.exp_val (1 - m) ρ ≤ ε ∧ 0 ≤ m ∧ m ≤ 1 }

  have hS'₁ : IsCompact S' := hS₁.image MState.Continuous_HermitianMat

  have hT'₁ : IsCompact T' := iInf_IsCompact ρ ε

  have hT'₂ : Convex ℝ T' := iInf_IsConvex ρ ε

  have hS'₃ : S'.Nonempty := by simpa only [Set.image_nonempty, S']

  have hT'₃ : T'.Nonempty := Set.Nonempty.of_subtype

  --There's some issue below where the lemma `Set.Icc.coe_iSup` uses a particular order instance, and we've
  --defined a different (but propositionally equivalent) one on `Prob`, and we need to convert between these.
  --Someone's who's better with understanding type inference diamonds - or whatever these are called - could
  --surely find a better solution. This hypothesis is implicitly used when we write `· congr` below.
  have h_stupid : Prob.instCompleteLinearOrder = instCompleteLinearOrderElemIccOfFactLe := by
    simp only [Prob.instCompleteLinearOrder, instCompleteLinearOrderElemIccOfFactLe]
    congr
    · ext
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

  ext1 --turn it from Prob equality into ℝ equality
  convert minimax (M := HermitianMat d ℂ) f S' T' hS'₁ hT'₁ hS₂ hT'₂ hS'₃ hT'₃
  --The remaining twiddling is about moving the casts inside the iInf's and iSup's.
  --In a better world, this would be mostly handled by some clever simps or push_cast's.
  · rw [← iSup_subtype'']
    convert Eq.trans (c := ⨆ (x : S'), ⨅ (y : T'), (f ↑x) ↑y) (Set.Icc.coe_iSup (ι := S) (zero_le_one (α := ℝ))) ?_
    · congr
    unfold S'
    have hi := iSup_range' (ι := S) (β := HermitianMat d ℂ) (g := fun x ↦ ⨅ (y : T'), (f x) ↑y) (·)
    rw [← Set.image_eq_range] at hi
    rw [hi]
    congr! 2 with x
    convert Eq.trans (Set.Icc.coe_iInf (ι := T') (zero_le_one (α := ℝ))) ?_
    · congr
    rfl
  · convert Eq.trans (c := ⨅ (y : T'), ⨆ (x : S'), (f ↑x) ↑y) (Set.Icc.coe_iInf (ι := T') (zero_le_one (α := ℝ))) ?_
    · congr
    congr! 2 with y
    rw [← iSup_subtype'']
    convert Eq.trans (Set.Icc.coe_iSup (ι := S) (zero_le_one (α := ℝ))) ?_
    · congr
    have hi := iSup_range' (ι := S) (β := HermitianMat d ℂ) (g := fun x ↦ (f x) ↑y) (·)
    rw [← Set.image_eq_range] at hi
    rw [hi]
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
      --is tight on the bound that Tr[ρ T] = ε, which is what gives the outcome distribution
      --p2. Why is it tight? Well, if it's not, then we can find another T' at least as
      --good as T by adding some more that increases its trace up to ε; and this can only
      --ever raise the detection probability on ρ. (The fact that this tight T exists should
      --be its own lemma, probably.)

      --Get the measurement operator T.
      --We actually need a stronger version of `exists_min` which guarantees that `ρ.exp_val T = ε`
      obtain ⟨T, hT⟩ := exists_min ρ ε {σ}
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
        --Could do `ext` now, would be nice to have a lemma for `Distribution.coin p = f` that
        --requires only checking that `p = f 0`.
        sorry
      · congr
        sorry
    rw [hΦ₁, hΦ₂]
    exact SandwichedRenyiEntropy.DPI hα ρ σ Φ

  --If q = 1, this inequality is trivial
  by_cases hq₂ : q = 1
  · rw [hq₂]
    simp

  replace hq₂ : q < 1 := show q.val < 1 by
    linarith +splitNe [q.coe_le_one, unitInterval.coe_ne_one.mpr hq₂]


  --The Renyi entropy is finite
  rw [SandwichedRelRentropy, if_pos ?_, if_neg hα.ne']; swap
  · suffices q2.M.ker = ⊥ by
      simp only [HermitianMat.val_eq_coe, this, bot_le]
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
