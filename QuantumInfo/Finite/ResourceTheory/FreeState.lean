import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Analysis.Subadditive
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Data.EReal.Basic

import QuantumInfo.Finite.CPTPMap
import QuantumInfo.Finite.Entropy

/-- A `ResourcePretheory` is a family of Hilbert spaces closed under tensor products, with an instance of
`Fintype` and `DecidableEq` for each. It forms a pre-structure then on which to discuss resource
theories. For instance, to talk about "two-party scenarios", we could write `ResourcePretheory (ℕ × ℕ)`,
with `H (a,b) := (Fin a) × (Fin b)`. -/
class ResourcePretheory (ι : Type*) where
  /-- The indexing of each Hilbert space -/
  H : ι → Type*
  /-- Each space is finite -/
  [FinH : ∀ i, Fintype (H i)]
  /-- Each object has decidable equality -/
  [DecEqH : ∀ i, DecidableEq (H i)]
  /-- Each space is nonempty (dimension at least 1) -/
  [NonemptyH : ∀ i, Nonempty (H i)]
  /-- The Hilbert spaces must have a product structure. -/
  prod : ι → ι → ι
  /-- The product structure induces an isomorphism of Hilbert spaces -/
  prodEquiv i j : H (prod i j) ≃ (H i) × (H j)
  --Possible we want some fact like the associativity of `prod` or the existence of an identity space,
  -- which would then imply MonoidalCategory structure later (instead of just Category)

attribute [instance] ResourcePretheory.FinH
attribute [instance] ResourcePretheory.DecEqH
attribute [instance] ResourcePretheory.NonemptyH

namespace ResourcePretheory

variable {ι : Type*} [ResourcePretheory ι]

/-- The `prod` operation of `ResourcePretheory` gives the natural product operation on `MState`s. Accessible
by the notation `ρ₁ ⊗ᵣ ρ₂`. -/
def prodRelabel {i j : ι} (ρ₁ : MState (H i)) (ρ₂ : MState (H j)) : MState (H (prod i j)) :=
  (ρ₁ ⊗ ρ₂).relabel (prodEquiv i j)

scoped notation ρ₁ "⊗ᵣ" ρ₂ => prodRelabel ρ₁ ρ₂

/-- The `prod` operation of `ResourcePretheory` gives the natural product operation on `CPTPMap`s. Accessible
by the notation `M₁ ⊗ᵣ M₂`. -/
noncomputable def prodCPTPMap {i j k l : ι} (M₁ : CPTPMap (H i) (H j)) (M₂ : CPTPMap (H k) (H l)) :
    CPTPMap (H (prod i k)) (H (prod j l)) :=
  (CPTPMap.of_equiv (prodEquiv j l).symm).compose ((M₁ ⊗ₖ M₂).compose (CPTPMap.of_equiv (prodEquiv i k)))

scoped notation M₁ "⊗ₖᵣ" M₂ => prodCPTPMap M₁ M₂

/-- Powers of spaces. Defined for `PNat` so that we don't have zeroth powers. -/
noncomputable def spacePow (i : ι) (n : ℕ+) : ι :=
  n.natPred.rec i (fun _ j ↦ prod i j)

scoped notation i "⊗^[" n "]" => spacePow i n

/-- Powers of states. Defined for `PNat`, so that we don't have zeroth powers -/
noncomputable def statePow {i : ι} (ρ : MState (H i)) (n : ℕ+) : MState (H (i⊗^[n])) :=
  (n.natPred.rec ρ (fun _ σ ↦ ρ ⊗ᵣ σ) : MState (H (i⊗^[n.natPred.succPNat])))

scoped notation ρ "⊗^[" n "]" => statePow ρ n

/-- A ResourcePretheory is `Unital` if it has a Hilbert space of size 1, i.e. `ℂ`. -/
class Unital (ι : Type*) [ResourcePretheory ι] where
  unit : ι
  unit_unique : Unique (H unit)

instance instUnitalUnique [u : Unital ι] : Unique (H u.unit) := u.unit_unique

open ComplexOrder in
theorem PosDef.prod {ι : Type*} [ResourcePretheory ι] {i j : ι}
      {ρ : MState (H i)} {σ : MState (H j)} (hρ : ρ.m.PosDef) (hσ : σ.m.PosDef)
      : (ρ ⊗ᵣ σ).m.PosDef := by
  have : (ρ ⊗ σ).m.PosDef := MState.PosDef.kron hρ hσ
  rw [prodRelabel]
  exact MState.PosDef.relabel this (prodEquiv i j)

open ComplexOrder in
theorem PosDef.npow {ι : Type*} [ResourcePretheory ι] {i : ι}
      {ρ : MState (H i)} (hρ : ρ.m.PosDef) (n : ℕ+)
      : (ρ⊗^[n]).m.PosDef := by
  induction n
  · exact hρ
  · rename_i n ih
    rcases n with ⟨(_|n), hn⟩
    . simp at hn
    exact ResourcePretheory.PosDef.prod hρ ih

@[simp]
theorem qRelEntropy_prodRelabel {i j : ι} (ρ₁ ρ₂ : MState (H i)) (σ₁ σ₂ : MState (H j)):
    𝐃(ρ₁ ⊗ᵣ σ₁‖ρ₂ ⊗ᵣ σ₂) = 𝐃(ρ₁‖ρ₂) + 𝐃(σ₁‖σ₂) := by
  simp [prodRelabel, qRelativeEnt_additive]

/-- Cast from one Hilbert space to another using the associator. -/
def statePow_cast {i : ι} {m n k : ℕ+} (h : m + n = k)
    : MState (H (prod (i⊗^[m]) (i⊗^[n]))) → MState (H (i⊗^[k])) := by
  sorry

@[simp]
theorem statePow_cast_eq_pow {i : ι} {m n k : ℕ+} (ρ : MState (H i)) (h : m + n = k) :
    statePow_cast h (ρ⊗^[m] ⊗ᵣ ρ⊗^[n]) = ρ⊗^[k] := by
  sorry

@[simp]
theorem qRelEntropy_statePow_cast {i : ι} {m n k : ℕ+} (ρ₁ ρ₂ : MState (H (prod (i⊗^[m]) (i⊗^[n]))))
  (h₁ h₂ : m + n = k) :
    𝐃(statePow_cast h₁ ρ₁‖statePow_cast h₂ ρ₂) = 𝐃(ρ₁‖ρ₂) := by
  sorry

end ResourcePretheory

/- FreeStateTheories: theories defining some sets of "free states" within a collection of Hilbert spaces. -/

open ResourcePretheory in
/-- A `FreeStateTheory` is a collection of mixed states (`MState`s) in a `ResourcePretheory` that obeys
some necessary axioms:
 * For each Hilbert space `H i`, the free states are a closed, convex set
 * For each Hilbert space `H i`, there is a free state of full rank
 * If `ρᵢ ∈ H i` and `ρⱼ ∈ H j` are free, then `ρᵢ ⊗ ρⱼ` is free in `H (prod i j)`.
-/
class FreeStateTheory (ι : Type*) extends ResourcePretheory ι where
  /-- The set of states we're calling "free" -/
  IsFree : Set (MState (toResourcePretheory.H i))
  /-- The set F(H) of free states is closed -/
  free_closed : IsClosed (@IsFree i)
  /-- The set F(H) of free states is convex (more precisely, their matrices are) -/
  free_convex : Convex ℝ (MState.M '' (@IsFree i))
  /-- The set of free states is closed under tensor product -/
  free_prod {ρ₁ : MState (H i)} {ρ₂ : MState (H j)} (h₁ : IsFree ρ₁) (h₂ : IsFree ρ₂) : IsFree (ρ₁ ⊗ᵣ ρ₂)
  /-- The set F(H) of free states contains a full-rank state `ρfull`, equivalently `ρfull` is positive definite. -/
  free_fullRank (i : ι) : open ComplexOrder in ∃ (ρ : MState (H i)), ρ.m.PosDef ∧ IsFree ρ

open ResourcePretheory
open FreeStateTheory
open NNReal

namespace FreeStateTheory

variable {ι : Type*} [FreeStateTheory ι] {i : ι}

noncomputable instance Inhabited_IsFree : Inhabited (IsFree (i := i)) :=
  ⟨⟨(free_fullRank i).choose, (free_fullRank i).choose_spec.right⟩⟩

/--The set of free states is compact because it's a closed subset of a compact space. -/
theorem IsCompact_IsFree : IsCompact (IsFree (i := i)) :=
  .of_isClosed_subset isCompact_univ free_closed (Set.subset_univ _)

--Also this needs to be generalized to other convex sets. I think it should work for any
--(well-behaved?) Mixable instance, it certainly works for any `Convex` set (of which `IsFree`
-- is one, the only relevant property here is `free_convex`.
theorem IsFree.mix {ι : Type*} [FreeStateTheory ι] {i : ι} {σ₁ σ₂ : MState (H i)}
    (hσ₁ : IsFree σ₁) (hσ₂ : IsFree σ₂) (p : Prob) : IsFree (p [σ₁ ↔ σ₂]) := by
  obtain ⟨m, hm₁, hm₂⟩ := free_convex (i := i) ⟨σ₁, hσ₁, rfl⟩ ⟨σ₂, hσ₂, rfl⟩ p.zero_le (1 - p).zero_le (by simp)
  simp [Mixable.mix, Mixable.mix_ab, MState.instMixable]
  simp at hm₂
  convert ← hm₁

theorem IsFree.npow {ι : Type*} [FreeStateTheory ι] {i : ι} {ρ : MState (H i)}
    (hρ : IsFree ρ) (n : ℕ+) : IsFree (ρ⊗^[n]) := by
  induction n
  · exact hρ
  · rename_i n ih
    rcases n with ⟨(_|n), hn⟩
    . simp at hn
    exact FreeStateTheory.free_prod hρ ih

@[simp]
theorem statePow_cast_free {i : ι} {m n k : ℕ+} (ρ : MState (H (prod (i⊗^[m]) (i⊗^[n]))))
    (h : m + n = k) : statePow_cast h ρ ∈ IsFree ↔ ρ ∈ IsFree := by
  sorry

end FreeStateTheory

--Things like asymptotically free operations, measures of non-freeness, etc. that can be stated
--entirely in terms of the free states (without referring to operations) go here.

variable {ι : Type*} [FreeStateTheory ι] {i : ι}

lemma relativeEntResource_ne_top (ρ : MState (H i)) : ⨅ σ ∈ IsFree, 𝐃(ρ‖σ) ≠ ⊤ := by
  let ⟨w,h⟩ := free_fullRank i
  apply ne_top_of_le_ne_top _ (iInf_le _ w)
  simp only [ne_eq, iInf_eq_top, Classical.not_imp]
  constructor
  · exact h.2
  · refine ne_of_apply_ne ENNReal.toEReal (qRelativeEnt_ker (ρ := ρ) (?_) ▸ EReal.coe_ne_top _)
    convert @bot_le _ _ (Submodule.instOrderBot) _
    exact h.1.toLin_ker_eq_bot

noncomputable def RelativeEntResource : MState (H i) → ℝ≥0 :=
    fun ρ ↦ (⨅ σ ∈ IsFree, 𝐃(ρ‖σ)).untop (relativeEntResource_ne_top ρ)

theorem exists_isFree_relativeEntResource (ρ : MState (H i)) :
    ∃ σ ∈ IsFree, 𝐃(ρ‖σ) = RelativeEntResource ρ := by
  obtain ⟨σ, hσ₁, hσ₂⟩ := IsCompact_IsFree.exists_isMinOn (s := IsFree (i := i)) (f := fun σ ↦ 𝐃(ρ‖σ))
    Set.Nonempty.of_subtype (by fun_prop)
  use σ, hσ₁
  rw [RelativeEntResource, ← hσ₂.iInf_eq hσ₁, ENNReal.ofNNReal, WithTop.coe_untop, iInf_subtype']

theorem RelativeEntResource.Subadditive (ρ : MState (H i)) : Subadditive fun n ↦
    NNReal.toReal <| if hn : n = 0 then 0 else
      RelativeEntResource (ρ⊗^[⟨n, Nat.zero_lt_of_ne_zero hn⟩]) := by
  intro m n
  rcases m with _|m
  · simp
    apply le_of_eq
    congr!
    · exact Nat.zero_add n
    · exact Nat.zero_add n
  rcases n with _|n
  · simp
  simp [← NNReal.coe_add]
  generalize_proofs pf1 pf2 pf3
  obtain ⟨σ₂, hσ₂f, hσ₂d⟩ := exists_isFree_relativeEntResource (ρ⊗^[⟨_, pf2⟩])
  obtain ⟨σ₃, hσ₃f, hσ₃d⟩ := exists_isFree_relativeEntResource (ρ⊗^[⟨_, pf3⟩])
  rw [← ENNReal.coe_le_coe]
  push_cast
  simp only [RelativeEntResource, ENNReal.ofNNReal, WithTop.coe_untop] at hσ₂d hσ₃d ⊢
  rw [← hσ₂d, ← hσ₃d]
  clear hσ₂d hσ₃d
  refine le_trans (biInf_le (i := ResourcePretheory.statePow_cast (by norm_cast) (σ₂ ⊗ᵣ σ₃)) _ ?_) ?_
  · simpa using free_prod hσ₂f hσ₃f
  · suffices hρp : ρ⊗^[⟨m + 1 + (n + 1), pf1⟩] = statePow_cast rfl (ρ⊗^[⟨m + 1, pf2⟩] ⊗ᵣ ρ⊗^[⟨n + 1, pf3⟩]) by
      simp [hρp, -statePow_cast_eq_pow]
    simp
    congr

noncomputable def RegularizedRelativeEntResource (ρ : MState (H i)) : ℝ≥0 :=
  ⟨(RelativeEntResource.Subadditive ρ).lim, by
    rw [Subadditive.lim]
    apply Real.sInf_nonneg
    rintro x ⟨x, hx, rfl⟩
    positivity⟩

noncomputable def GlobalRobustness {i : ι} : MState (H i) → ℝ≥0 :=
  fun ρ ↦ sInf {s | ∃ σ, (⟨1 / (1+s), by bound⟩ [ρ ↔ σ]) ∈ IsFree}

/-- A sequence of operations `f_n` is asymptotically nongenerating if `lim_{n→∞} RG(f_n(ρ_n)) = 0`, where
RG is `GlobalRobustness` and `ρ_n` is any sequence of free states. Equivalently, we can take the `max` (
over operations and states) on the left-hand side inside the limit.
-/
def IsAsymptoticallyNongenerating (dI dO : ι) (f : (n : ℕ+) → CPTPMap (H (dI⊗^[n])) (H (dO⊗^[n]))) : Prop :=
  ∀ (ρs : (n : ℕ+) → MState (H (dI⊗^[n]))), (∀ n, IsFree (ρs n)) →
  Filter.Tendsto (fun n ↦ GlobalRobustness ((f n) (ρs n))) Filter.atTop (nhds 0)
