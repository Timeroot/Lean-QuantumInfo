import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Data.Real.EReal

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

namespace ResourcePretheory

variable {ι : Type*} [ResourcePretheory ι]

--Having a `ResourcePretheory ι` around should give us access to the `Fintype` and `DecidableEq` instances.
instance instQRT_FintypeH (i : ι) : Fintype (H i) := FinH i
instance instQRT_DecEqH (i : ι) : DecidableEq (H i) := DecEqH i
instance instQRT_NonemptyH (i : ι) : Nonempty (H i) := NonemptyH i

/-- The `prod` operation of `ResourcePretheory` gives the natural product operation on `MState`s. Accessible
by the notation `ρ₁ ⊗ᵣ ρ₂`. -/
def prodRelabel {i j : ι} (ρ₁ : MState (H i)) (ρ₂ : MState (H j)) : MState (H (prod i j)) :=
  (ρ₁ ⊗ ρ₂).relabel (prodEquiv i j)

scoped notation ρ₁ "⊗ᵣ" ρ₂ => prodRelabel ρ₁ ρ₂

/-- The `prod` operation of `ResourcePretheory` gives the natural product operation on `CPTPMap`s. Accessible
by the notation `M₁ ⊗ᵣ M₂`. -/
noncomputable def prodCPTPMap {i j k l : ι} (M₁ : CPTPMap (H i) (H j)) (M₂ : CPTPMap (H k) (H l)) :
    CPTPMap (H (prod i k)) (H (prod j l)) :=
  (CPTPMap.of_equiv (prodEquiv j l).symm).compose ((M₁ ⊗ M₂).compose (CPTPMap.of_equiv (prodEquiv i k)))

scoped notation M₁ "⊗ᵣ" M₂ => prodCPTPMap M₁ M₂

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

instance instUnitalUnique [ResourcePretheory ι] [u : Unital ι] : Unique (H u.unit) := u.unit_unique

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
  IsFree : Set (MState (H i))
  /-- The set F(H) of free states is closed -/
  free_closed : IsClosed (@IsFree i)
  /-- The set F(H) of free states is convex (more precisely, their matrices are) -/
  free_convex : Convex ℝ (MState.m '' (@IsFree i))
  /-- The set of free states is closed under tensor product -/
  free_prod {ρ₁ : MState (H i)} {ρ₂ : MState (H j)} (h₁ : IsFree ρ₁) (h₂ : IsFree ρ₂) : IsFree (ρ₁ ⊗ᵣ ρ₂)
  /-- The set F(H) of free states contains a full-rank state `ρfull`, equivalently `ρfull` is positive definite. -/
  free_fullRank (i : ι) : open ComplexOrder in ∃ (ρ : MState (H i)), ρ.m.PosDef ∧ IsFree ρ

open ResourcePretheory
open FreeStateTheory
open NNReal

--Things like asymptotically free operations, measures of non-freeness, etc. that can be stated
--entirely in terms of the free states (without referring to operations) go here.

variable {ι : Type*} [FreeStateTheory ι]

noncomputable def RelativeEntResource {i : ι} : MState (H i) → ℝ≥0 :=
    fun ρ ↦ (⨅ σ ∈ IsFree, EReal.toENNReal (qRelativeEnt ρ σ)).untop
  (by
    let ⟨w,h⟩ := free_fullRank i
    apply ne_top_of_le_ne_top _ (iInf_le _ w)
    simp only [ne_eq, iInf_eq_top, Classical.not_imp]
    constructor
    · exact h.2
    · dsimp [qRelativeEnt]
      split_ifs with h
      · simpa using ne_of_beq_false rfl
      · absurd h
        rw [ker_bot_of_full_rank]
        · exact OrderBot.bot_le (LinearMap.ker (Matrix.toLin' ρ.m))
        · --should be in mathlib
          sorry
  )

noncomputable def RegularizedRelativeEntResource {i : ι} : MState (H i) → ℝ≥0 :=
  --I want to define a general notion of "regularized quantity" and then use that here. That can then
  --also be used for things like capacity, asymptotic interconversion rates, etc.
  sorry

noncomputable def GlobalRobustness {i : ι} : MState (H i) → ℝ≥0 :=
  fun ρ ↦ sInf {s | ∃ σ, IsFree (
    ⟨1 / (1+s),
      by constructor <;> (first | rw [one_div_nonneg] | rw [one_div_le]) <;> linarith [show 0 ≤ toReal s from s.2]
    ⟩ [ ρ ↔ σ ])}

/-- A sequence of operations `f_n` is asymptotically nongenerating if `lim_{n→∞} RG(f_n(ρ_n)) = 0`, where
RG is `GlobalRobustness` and `ρ_n` is any sequence of free states. Equivalently, we can take the `max` (
over operations and states) on the left-hand side inside the limit.
-/
def IsAsymptoticallyNongenerating (dI dO : ι) (f : (n : ℕ+) → CPTPMap (H (dI⊗^[n])) (H (dO⊗^[n]))) : Prop :=
  ∀ (ρs : (n : ℕ+) → MState (H (dI⊗^[n]))), (∀ n, IsFree (ρs n)) →
  Filter.Tendsto (fun n ↦ GlobalRobustness ((f n) (ρs n))) Filter.atTop (nhds 0)
