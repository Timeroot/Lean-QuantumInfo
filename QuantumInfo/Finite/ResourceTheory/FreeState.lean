import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Analysis.Subadditive
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic

import QuantumInfo.Finite.CPTPMap
import QuantumInfo.Finite.Entropy

open scoped Topology

/-- A `ResourcePretheory` is a family of Hilbert spaces closed under tensor products, with an instance of
`Fintype` and `DecidableEq` for each. It forms a pre-structure then on which to discuss resource
theories. For instance, to talk about "two-party scenarios", we could write `ResourcePretheory (ℕ × ℕ)`,
with `H (a,b) := (Fin a) × (Fin b)`.

The `Semigroup ι` structure means we have a way to take products of our labels of Hilbert spaces
in a way that is associative (with actual equality). The `prodEquiv` lets us reinterpret between
a product-labelled Hilbert spaces, and an actual pair of Hilbert spaces.
-/
class ResourcePretheory (ι : Type*) extends Semigroup ι where
  /-- The indexing of each Hilbert space -/
  H : ι → Type*
  /-- Each space is finite -/
  [FinH : ∀ i, Fintype (H i)]
  /-- Each object has decidable equality -/
  [DecEqH : ∀ i, DecidableEq (H i)]
  /-- Each space is nonempty (dimension at least 1) -/
  [NonemptyH : ∀ i, Nonempty (H i)]
  /-- The product structure induces an isomorphism of Hilbert spaces -/
  prodEquiv i j : H (i * j) ≃ (H i) × (H j)
  --Possible we want some fact like the associativity of `prod` or the existence of an identity space,
  -- which would then imply MonoidalCategory structure later (instead of just Category). For now we
  -- take the (logically equivalent, in the appropriate model) assumption that the associator is
  -- actually an equality. This is captured in the `Semigroup ι` assumption. If we wanted to turn
  -- this into something more flexible, we would replace that with `Mul ι` (dropping `mul_assoc`)
  -- and get an appropriate associator `Equiv` here.
  hAssoc i j k :
    ((prodEquiv (i * j) k).trans <|
      ((prodEquiv i j).prodCongr (Equiv.refl (H k))).trans <|
      (Equiv.prodAssoc _ _ _).trans <|
      ((Equiv.refl (H i)).prodCongr ((prodEquiv j k).symm)).trans
      (prodEquiv i (j * k)).symm
    )
     = Equiv.cast (congrArg H <| mul_assoc i j k)

attribute [instance] ResourcePretheory.FinH
attribute [instance] ResourcePretheory.DecEqH
attribute [instance] ResourcePretheory.NonemptyH

namespace ResourcePretheory

variable {ι : Type*} [ResourcePretheory ι] {i j k l : ι}

/-- The `prod` operation of `ResourcePretheory` gives the natural product operation on `MState`s
that puts us in a new Hilbert space of the category. Accessible by the notation `ρ₁ ⊗ᵣ ρ₂`. -/
noncomputable def prodRelabel (ρ₁ : MState (H i)) (ρ₂ : MState (H j)) : MState (H (i * j)) :=
  (ρ₁ ⊗ ρ₂).relabel (prodEquiv i j)

scoped infixl:65 "⊗ᵣ" => prodRelabel

theorem prodRelabel_assoc (ρ₁ : MState (H i)) (ρ₂ : MState (H j)) (ρ₃ : MState (H k)) :
    ρ₁ ⊗ᵣ ρ₂ ⊗ᵣ ρ₃ ≍ ρ₁ ⊗ᵣ (ρ₂ ⊗ᵣ ρ₃) := by
  simp [prodRelabel, MState.relabel_kron]
  have h_equiv := hAssoc i j k
  rw [← Equiv.trans_assoc, Equiv.trans_cancel_right] at h_equiv
  have h_cong := congrArg (MState.relabel ((ρ₁⊗ρ₂)⊗ρ₃)) h_equiv
  rw [← eq_cast_iff_heq]; swap
  · rw [mul_assoc]
  convert h_cong; clear h_equiv h_cong
  rw [← MState.relabel_cast]; swap
  · rw [mul_assoc]
  rw [MState.kron_relabel, MState.prod_assoc]
  rw [MState.relabel_comp, MState.relabel_comp, MState.relabel_comp]
  rfl

/-- A `MState.relabel` can be distributed across a `prodRelabel`, if you have proofs that the factors
correspond correctly. -/
theorem prodRelabel_relabel_cast_prod
    (ρ₁ : MState (H i)) (ρ₂ : MState (H j))
    (h : H (k * l) = H (i * j)) (hik : k = i) (hlj : l = j) :
    (ρ₁ ⊗ᵣ ρ₂).relabel (Equiv.cast h) =
    (ρ₁.relabel (Equiv.cast (congrArg H hik))) ⊗ᵣ (ρ₂.relabel (Equiv.cast (congrArg H hlj))) := by
  subst hik
  subst hlj
  rfl

open ComplexOrder in
theorem PosDef.prod {ρ : MState (H i)} {σ : MState (H j)} (hρ : ρ.m.PosDef) (hσ : σ.m.PosDef)
    : (ρ ⊗ᵣ σ).m.PosDef := by
  have : (ρ ⊗ σ).m.PosDef := MState.PosDef.kron hρ hσ
  rw [prodRelabel]
  exact MState.PosDef.relabel this (prodEquiv i j)

--BAD old attempt at PNat powers
-- /-- Powers of spaces. Defined for `PNat` so that we don't have zeroth powers. -/
-- noncomputable def spacePow (i : ι) (n : ℕ+) : ι :=
--   n.natPred.rec i (fun _ j ↦ prod j i)

-- scoped notation i "⊗^H[" n "]" => spacePow i n

-- @[simp]
-- theorem spacePow_one (i : ι) : i⊗^H[1] = i :=
--   rfl

-- theorem spacePow_succ (i : ι) (n : ℕ+) : i⊗^H[n + 1] = prod (i⊗^H[n]) i := by
--   rcases n with ⟨_|n, hn⟩
--   · contradiction
--   · rfl

-- /-- Powers of states. Defined for `PNat`, so that we don't have zeroth powers -/
-- noncomputable def statePow {i : ι} (ρ : MState (H i)) (n : ℕ+) : MState (H (i⊗^H[n])) :=
--   (n.natPred.rec ρ (fun _ σ ↦ σ ⊗ᵣ ρ) : MState (H (i⊗^H[n.natPred.succPNat])))

-- scoped notation ρ "⊗^S[" n "]" => statePow ρ n

-- @[simp]
-- theorem statePow_one {i : ι} (ρ : MState (H i)) : ρ⊗^S[1] = ρ :=
--   rfl

-- theorem statePow_succ {i : ι} (ρ : MState (H i)) (n : ℕ+) : ρ⊗^S[n + 1] = ρ⊗^S[n] ⊗ᵣ ρ := by
--   rcases n with ⟨_|n, hn⟩
--   · contradiction
--   · rfl

@[simp]
theorem qRelEntropy_prodRelabel (ρ₁ ρ₂ : MState (H i)) (σ₁ σ₂ : MState (H j)):
    𝐃(ρ₁ ⊗ᵣ σ₁‖ρ₂ ⊗ᵣ σ₂) = 𝐃(ρ₁‖ρ₂) + 𝐃(σ₁‖σ₂) := by
  simp [prodRelabel]

@[simp]
theorem sandwichedRelRentropy_prodRelabel {α : ℝ} (ρ₁ ρ₂ : MState (H i)) (σ₁ σ₂ : MState (H j)):
    D̃_ α(ρ₁ ⊗ᵣ σ₁‖ρ₂ ⊗ᵣ σ₂) = D̃_ α(ρ₁‖ρ₂) + D̃_ α(σ₁‖σ₂) := by
  simp [prodRelabel]

end ResourcePretheory

open ResourcePretheory

/-- A ResourcePretheory is `Unital` if it has a Hilbert space of size 1, i.e. `ℂ`. -/
class UnitalPretheory (ι : Type*) extends ResourcePretheory ι, MulOneClass ι, Unique (H 1) where
  prod_default {i} (ρ : MState (H i)) :
    (toResourcePretheory.prodRelabel ρ (Inhabited.default : MState (H 1))) ≍ ρ
  default_prod {i} (ρ : MState (H i)) :
    (toResourcePretheory.prodRelabel (Inhabited.default : MState (H 1)) ρ) ≍ ρ

namespace UnitalPretheory

variable {ι : Type*} [UnitalPretheory ι] {i j : ι}

instance : Monoid ι where

/-- Powers of spaces.

We define it for `Nat` in a `UnitalPretheory`. In principal this could be done for any
`ResourcePretheory` and be defined for `PNat` so that we don't have zeroth powers. In
anticipation that we might some day want that, and that we might do everything with a
non-equality associator, we keep this as its own definition and keep our own names for
rewriting theorems where possible.-/
noncomputable def spacePow (i : ι) (n : ℕ) : ι :=
  i ^ n

--This notation is less necessary now since we can just write `i ^ n` as long as it's
--a monoid.
scoped notation i "⊗^H[" n "]" => spacePow i n

@[simp]
theorem spacePow_zero (i : ι) : i ^ 0 = 1 := by
  rfl

@[simp]
theorem spacePow_one (i : ι) : i ^ 1 = i := by
  simp

theorem spacePow_succ (i : ι) (n : ℕ) : i ^ (n + 1) = (i ^ n) * i := by
  rfl

theorem spacePow_add (m n : ℕ) :
    i ^ (m + n) = (i ^ m) * (i ^ n) := by
  induction n
  · simp
  · rename_i n ih
    rw [spacePow_succ, ← mul_assoc, ← add_assoc, ← ih, spacePow_succ]

theorem spacePow_mul (m n : ℕ) :
    i ^ (m * n) = (i ^ m) ^ n :=
  pow_mul i m n

/-- Powers of states. Defined for `PNat`, so that we don't have zeroth powers -/
noncomputable def statePow (ρ : MState (H i)) (n : ℕ) : MState (H (i ^ n)) :=
  n.rec default (fun _ σ ↦ σ ⊗ᵣ ρ)

scoped notation ρ "⊗^S[" n "]" => statePow ρ n

@[simp]
theorem statePow_zero (ρ : MState (H i)) : ρ⊗^S[0] = default :=
  rfl

@[simp]
theorem statePow_one (ρ : MState (H i)) : ρ⊗^S[1] ≍ ρ := by
  rw [← eq_cast_iff_heq]; swap
  · rw [spacePow_one]
  · rw [eq_cast_iff_heq, statePow]
    exact default_prod ρ

theorem statePow_succ (ρ : MState (H i)) (n : ℕ) : ρ⊗^S[n + 1] = ρ⊗^S[n] ⊗ᵣ ρ := by
  rfl

theorem statePow_add (ρ : MState (H i)) (m n : ℕ) : ρ⊗^S[m + n] ≍ ρ⊗^S[m] ⊗ᵣ ρ⊗^S[n] := by
  rw [← eq_cast_iff_heq]; swap
  · rw [spacePow_add]
  rw [eq_cast_iff_heq]
  induction n
  · rw [add_zero, statePow_zero]
    exact (prod_default _).symm
  · rename_i n ih
    rw [statePow_succ, ← add_assoc, statePow_succ]
    refine HEq.trans ?_ (prodRelabel_assoc _ _ _)
    congr
    apply spacePow_add

theorem statePow_add_relabel (ρ : MState (H i)) (m n : ℕ) :
    ρ⊗^S[m + n] = (ρ⊗^S[m] ⊗ᵣ ρ⊗^S[n]).relabel (Equiv.cast (by congr; exact pow_add i m n)) := by
  have h := statePow_add ρ m n
  rw [heq_iff_exists_eq_cast] at h
  obtain ⟨h, h₂⟩ := h
  rw [h₂, MState.relabel_cast]

theorem statePow_mul (ρ : MState (H i)) (m n : ℕ) : ρ⊗^S[m * n] ≍ (ρ⊗^S[m])⊗^S[n] := by
  rw [← eq_cast_iff_heq]; swap
  · rw [spacePow_mul]
  rw [eq_cast_iff_heq]
  induction n
  · simp
  · rename_i n ih
    rw [statePow_succ, mul_add]
    --This is TERRIBLE. There has to be a better way
    trans ρ⊗^S[m * n] ⊗ᵣ ρ⊗^S[m * 1]
    · apply statePow_add
    · rw [← eq_cast_iff_heq] at ih; swap
      · congr 2 <;> simp [pow_mul]
      rw [← eq_cast_iff_heq]; swap
      · congr 2 <;> simp [pow_mul]
      rw [← MState.relabel_cast _ (by simp [pow_mul])]
      rw [prodRelabel_relabel_cast_prod]
      · congr
        · rw [ih, MState.relabel_cast]
        · rw [MState.relabel_cast]
          rw [eq_cast_iff_heq]
          · rw [mul_one]
          · rw [mul_one]
      · rw [pow_mul]

theorem statePow_mul_relabel {i : ι} (ρ : MState (H i)) (m n : ℕ) :
   ρ⊗^S[m * n] = (ρ⊗^S[m])⊗^S[n].relabel (Equiv.cast (congrArg H (pow_mul i m n))) := by
  have h := statePow_mul ρ m n
  rw [heq_iff_exists_eq_cast] at h
  obtain ⟨h, h₂⟩ := h
  rw [h₂, MState.relabel_cast]

open ComplexOrder in
theorem PosDef.npow {ρ : MState (H i)} (hρ : ρ.m.PosDef) (n : ℕ)
    : (ρ⊗^S[n]).m.PosDef := by
  induction n
  · rw [statePow_zero, spacePow_zero]
    exact MState.posDef_of_unique default
  · apply ResourcePretheory.PosDef.prod ‹_› hρ

theorem statePow_rw {n m : ℕ} (h : n = m) (ρ : MState (H i)) :
    ρ⊗^S[n] = (ρ⊗^S[m]).relabel (Equiv.cast (by congr)) := by
  subst n
  simp

@[simp]
theorem qRelEntropy_statePow (ρ σ : MState (H i)) (n : ℕ) :
    𝐃(ρ⊗^S[n] ‖ σ ⊗^S[n]) = n * 𝐃(ρ‖σ) := by
  induction n
  · simp
  · rename_i n ih
    rw [statePow_succ, statePow_succ, qRelEntropy_prodRelabel]
    simp [ih, add_mul]

@[simp]
theorem sandwichedRelRentropy_statePow {α : ℝ} (ρ σ : MState (H i)) (n : ℕ) :
    D̃_ α(ρ⊗^S[n] ‖ σ⊗^S[n]) = n * D̃_ α(ρ‖σ) := by
  induction n
  · simp
  · rename_i n ih
    rw [statePow_succ, statePow_succ, sandwichedRelRentropy_prodRelabel]
    simp [ih, add_mul]

theorem sandwichedRelRentropy_heq_congr {α : ℝ}
      {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂) (hρ : ρ₁ ≍ ρ₂) (hσ : σ₁ ≍ σ₂) :
    D̃_ α(ρ₁‖σ₁) = D̃_ α(ρ₂‖σ₂) := by
  rw [heq_iff_exists_eq_cast] at hρ hσ
  obtain ⟨_, rfl⟩ := hρ
  obtain ⟨_, rfl⟩ := hσ
  simp [← MState.relabel_cast _ hd]

@[gcongr]
theorem sandwichedRelRentropy_congr {α : ℝ}
      {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂)
        (hρ : ρ₁ = ρ₂.relabel (Equiv.cast hd)) (hσ : σ₁ = σ₂.relabel (Equiv.cast hd)) :
    D̃_ α(ρ₁‖σ₁) = D̃_ α(ρ₂‖σ₂) := by
  subst ρ₁ σ₁
  simp

end UnitalPretheory

/- FreeStateTheories: theories defining some sets of "free states" within a collection of Hilbert spaces. -/

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

namespace FreeStateTheory

variable {ι : Type*} [FreeStateTheory ι] {i : ι}

noncomputable instance Inhabited_IsFree : Inhabited (IsFree (i := i)) :=
  ⟨⟨(free_fullRank i).choose, (free_fullRank i).choose_spec.right⟩⟩

theorem IsFree.of_unique [Unique (H i)] (ρ : MState (H i)) : ρ ∈ IsFree := by
  obtain ⟨σ, h₁, h₂⟩ := free_fullRank i
  convert h₂
  apply Subsingleton.allEq

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

end FreeStateTheory

open UnitalPretheory
open FreeStateTheory

class UnitalFreeStateTheory (ι : Type*) extends FreeStateTheory ι, UnitalPretheory ι

namespace UnitalFreeStateTheory

--Things like asymptotically free operations, measures of non-freeness, etc. that can be stated
--entirely in terms of the free states (without referring to operations) go here.

variable {ι : Type*} [UnitalFreeStateTheory ι] {i : ι}

theorem _root_.FreeStateTheory.IsFree.npow {i : ι} {ρ : MState (H i)}
    (hρ : IsFree ρ) (n : ℕ) : IsFree (ρ⊗^S[n]) := by
  induction n
  · rw [statePow_zero, spacePow_zero]
    apply IsFree.of_unique
  · rw [statePow_succ]
    exact FreeStateTheory.free_prod ‹_› hρ

@[simp]
theorem relabel_cast_isFree {i j : ι} (ρ : MState (H i)) (h : j = i) {h' : H j = H i}:
    ρ.relabel (Equiv.cast h') ∈ IsFree ↔ ρ ∈ IsFree := by
  subst h
  simp

open NNReal

/-- In a `FreeStateTheory`, we have free states of full rank, therefore the minimum relative entropy
of any state `ρ` to a free state is finite. -/
@[aesop (rule_sets := [finiteness]) safe]
lemma relativeEntResource_ne_top (ρ : MState (H i)) : ⨅ σ ∈ IsFree, 𝐃(ρ‖σ) ≠ ⊤ := by
  let ⟨w,h⟩ := free_fullRank i
  apply ne_top_of_le_ne_top _ (iInf_le _ w)
  simp only [ne_eq, iInf_eq_top, Classical.not_imp]
  constructor
  · exact h.2
  · refine ne_of_apply_ne ENNReal.toEReal (qRelativeEnt_ker (ρ := ρ) (?_) ▸ EReal.coe_ne_top _)
    convert @bot_le _ _ (Submodule.instOrderBot) _
    exact h.1.toLin_ker_eq_bot
  /-
  simp only [ne_eq, iInf_eq_top, not_forall]
  obtain ⟨σ, hσ₁, hσ₂⟩ := FreeStateTheory.free_fullRank i
  use σ, hσ₂
  rw [qRelativeEnt]
  split_ifs with h
  · simp --should be `finiteness`, TODO debug
  contrapose! h
  convert bot_le
  exact hσ₁.toLin_ker_eq_bot
  -/

noncomputable def RelativeEntResource : MState (H i) → ℝ≥0 :=
    fun ρ ↦ (⨅ σ ∈ IsFree, 𝐃(ρ‖σ)).untop (relativeEntResource_ne_top ρ)

scoped notation "𝑅ᵣ" => RelativeEntResource

attribute [fun_prop] LowerSemicontinuousOn
attribute [fun_prop] LowerSemicontinuous.lowerSemicontinuousOn

--PULLOUT
theorem _root_.IsCompact.exists_isMinOn_lowerSemicontinuousOn {α β : Type*}
  [LinearOrder α] [TopologicalSpace α] [TopologicalSpace β] [ClosedIicTopology α]
  {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α} (hf : LowerSemicontinuousOn f s) :
    ∃ x ∈ s, IsMinOn f s x := by
  --Thanks Aristotle
  -- By the Extreme Value Theorem for lower semicontinuous functions on compact sets, there exists x in s such that f(x) is the minimum value of f on s.
  have h_extreme : ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y := by
    by_contra! h;
    choose! g hg using h;
    -- For each $x \in s$, since $f$ is lower semicontinuous at $x$, there exists a neighborhood $U_x$ of $x$ such that $f(y) > f(g(x))$ for all $y \in U_x \cap s$.
    have h_neighborhood : ∀ x ∈ s, ∃ U : Set β, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U ∩ s, f y > f (g x) := by
      intro x hx;
      have := hf x hx;
      rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp ( this ( f ( g x ) ) ( hg x hx |>.2 ) ) with ⟨ U, hU, hU' ⟩;
      exact ⟨ interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hU, fun y hy => hU' ⟨ interior_subset hy.1, hy.2 ⟩ ⟩;
    choose! U hU using h_neighborhood;
    -- Since $s$ is compact, the open cover $\{U_x \cap s \mid x \in s\}$ has a finite subcover.
    obtain ⟨t, ht⟩ : ∃ t : Finset β, (∀ x ∈ t, x ∈ s) ∧ s ⊆ ⋃ x ∈ t, U x ∩ s := by
      -- Since $s$ is compact, the open cover $\{U_x \mid x \in s\}$ has a finite subcover.
      obtain ⟨t, ht⟩ : ∃ t : Finset β, (∀ x ∈ t, x ∈ s) ∧ s ⊆ ⋃ x ∈ t, U x := by
        exact hs.elim_nhds_subcover U fun x hx => IsOpen.mem_nhds ( hU x hx |>.1 ) ( hU x hx |>.2.1 );
      exact ⟨ t, ht.1, fun x hx => by rcases Set.mem_iUnion₂.1 ( ht.2 hx ) with ⟨ y, hy, hy' ⟩ ; exact Set.mem_iUnion₂.2 ⟨ y, hy, ⟨ hy', hx ⟩ ⟩ ⟩;
    -- Since $t$ is finite, there exists $x \in t$ such that $f(g(x))$ is minimal.
    obtain ⟨x, hx⟩ : ∃ x ∈ t, ∀ y ∈ t, f (g x) ≤ f (g y) := by
      apply_rules [ Finset.exists_min_image ];
      -- Since $s$ is nonempty, there exists some $y \in s$.
      obtain ⟨y, hy⟩ : ∃ y, y ∈ s := ne_s;
      exact Exists.elim ( Set.mem_iUnion₂.1 ( ht.2 hy ) ) fun x hx => ⟨ x, hx.1 ⟩;
    obtain ⟨ y, hy ⟩ := ht.2 ( hg x ( ht.1 x hx.1 ) |>.1 );
    simp_all only [Set.mem_inter_iff, and_self, and_true, gt_iff_lt, and_imp, Set.mem_range]
    obtain ⟨left, right⟩ := ht
    obtain ⟨left_1, right_1⟩ := hx
    obtain ⟨⟨w, rfl⟩, right_2⟩ := hy
    simp_all only [Set.mem_iUnion, Set.mem_inter_iff, and_true, exists_prop]
    obtain ⟨left_2, right_2⟩ := right_2
    exact lt_irrefl _ ( lt_of_le_of_lt ( right_1 _ left_2 ) ( hU _ ( left _ left_2 ) |>.2.2 _ right_2 ( hg _ ( left _ left_1 ) ) ) );
  -- By definition of IsMinOn, we need to show that for all y in s, f(x) ≤ f(y). This is exactly what h_extreme provides.
  obtain ⟨x, hx_s, hx_min⟩ := h_extreme;
  use x, hx_s;
  exact hx_min

theorem exists_isFree_relativeEntResource (ρ : MState (H i)) :
    ∃ σ ∈ IsFree, 𝐃(ρ‖σ) = 𝑅ᵣ ρ := by
  obtain ⟨σ, hσ₁, hσ₂⟩ := IsCompact_IsFree.exists_isMinOn_lowerSemicontinuousOn
    (s := IsFree (i := i)) (f := fun σ ↦ 𝐃(ρ‖σ))
    Set.Nonempty.of_subtype (by fun_prop)
  use σ, hσ₁
  rw [RelativeEntResource, ← hσ₂.iInf_eq hσ₁, ENNReal.ofNNReal, WithTop.coe_untop, iInf_subtype']

theorem RelativeEntResource.Subadditive (ρ : MState (H i)) : Subadditive fun n ↦ 𝑅ᵣ (ρ⊗^S[n]) := by
  intro m n
  obtain ⟨σ₂, hσ₂f, hσ₂d⟩ := exists_isFree_relativeEntResource (ρ⊗^S[m])
  obtain ⟨σ₃, hσ₃f, hσ₃d⟩ := exists_isFree_relativeEntResource (ρ⊗^S[n])
  simp only [RelativeEntResource, ← NNReal.coe_add, coe_le_coe]
  rw [← ENNReal.coe_le_coe]
  simp [RelativeEntResource, ENNReal.ofNNReal] at hσ₂d hσ₃d ⊢
  rw [← hσ₂d, ← hσ₃d]
  clear hσ₂d hσ₃d
  have ht₁ : i ^ (m + n) = i ^ m * i ^ n :=
    spacePow_add m n
  have ht := congrArg H ht₁
  refine le_trans (biInf_le (i := (σ₂ ⊗ᵣ σ₃).relabel (Equiv.cast ht)) _ ?_) ?_
  · simpa [ht₁] using free_prod hσ₂f hσ₃f
  · apply le_of_eq
    rw [← qRelEntropy_prodRelabel]
    gcongr
    · apply statePow_add
    · rw [← eq_cast_iff_heq]
      apply MState.relabel_cast

noncomputable def RegularizedRelativeEntResource (ρ : MState (H i)) : ℝ≥0 :=
  ⟨(RelativeEntResource.Subadditive ρ).lim, by
    rw [Subadditive.lim]
    apply Real.sInf_nonneg
    rintro x ⟨x, hx, rfl⟩
    positivity⟩

scoped notation "𝑅ᵣ∞" => RegularizedRelativeEntResource

/-- Lemma 5 -/
theorem RelativeEntResource.tendsto (ρ : MState (H i)) :
    Filter.atTop.Tendsto (fun n ↦ 𝑅ᵣ (ρ⊗^S[n]) / n) (𝓝 (𝑅ᵣ∞ ρ)) := by
  rw [← NNReal.tendsto_coe]
  apply (RelativeEntResource.Subadditive ρ).tendsto_lim
  use 0
  rintro _ ⟨y, rfl⟩
  positivity

/-- Alternate version of Lemma 5 which states the convergence with the `ENNReal`
expression for `RelativeEntResource`, as opposed its `untop`-ped `NNReal` value. -/
theorem RelativeEntResource.tendsto_ennreal (ρ : MState (H i)) :
    Filter.atTop.Tendsto (fun n ↦ (⨅ σ ∈ IsFree, 𝐃(ρ⊗^S[n]‖σ)) / ↑n) (𝓝 (𝑅ᵣ∞ ρ)) := by
  refine Filter.Tendsto.congr' ?_ (ENNReal.tendsto_coe.mpr <| RelativeEntResource.tendsto ρ)
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  use 1; intros
  rw [RelativeEntResource, ENNReal.coe_div (by positivity), ENNReal.coe_natCast]
  congr
  apply WithTop.coe_untop

noncomputable def GlobalRobustness {i : ι} : MState (H i) → ℝ≥0 :=
  fun ρ ↦ sInf {s | ∃ σ, (⟨1 / (1+s), by bound⟩ [ρ ↔ σ]) ∈ IsFree}

/-- A sequence of operations `f_n` is asymptotically nongenerating if `lim_{n→∞} RG(f_n(ρ_n)) = 0`, where
RG is `GlobalRobustness` and `ρ_n` is any sequence of free states. Equivalently, we can take the `max` (
over operations and states) on the left-hand side inside the limit.
-/
def IsAsymptoticallyNongenerating (dI dO : ι) (f : (n : ℕ) → CPTPMap (H (dI⊗^H[n])) (H (dO⊗^H[n]))) : Prop :=
  ∀ (ρs : (n : ℕ) → MState (H (dI⊗^H[n]))), (∀ n, IsFree (ρs n)) →
  Filter.atTop.Tendsto (fun n ↦ GlobalRobustness ((f n) (ρs n))) (𝓝 0)

end UnitalFreeStateTheory
