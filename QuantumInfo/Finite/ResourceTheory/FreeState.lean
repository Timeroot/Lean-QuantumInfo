import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Analysis.Subadditive
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic

import QuantumInfo.Finite.CPTPMap
import QuantumInfo.Finite.Entropy

--stuff that belongs in other files

--PULLOUT
theorem Equiv.trans_cancel_left (α β γ : Type*) (e : α ≃ β) (f : β ≃ γ) (g : α ≃ γ) :
    e.trans f = g ↔ f = e.symm.trans g := by
  constructor <;> (rintro rfl; simp [← Equiv.trans_assoc])

theorem Equiv.trans_cancel_right (α β γ : Type*) (e : α ≃ β) (f : β ≃ γ) (g : α ≃ γ) :
    e.trans f = g ↔ e = g.trans f.symm := by
  constructor <;> (rintro rfl; simp [Equiv.trans_assoc])

--PULLOUT
theorem MState.relabel_comp {d₁ d₂ d₃ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      [Fintype d₃] [DecidableEq d₃] (ρ : MState d₁) (e : d₂ ≃ d₁) (f : d₃ ≃ d₂) :
    (ρ.relabel e).relabel f = ρ.relabel (f.trans e) := by
  ext
  simp

--PULLOUT
@[simp]
theorem MState.relabel_refl {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) :
    ρ.relabel (Equiv.refl d) = ρ := by
  ext
  simp

--PULLOUT
theorem MState.relabel_kron {d₁ d₂ d₃ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      [Fintype d₃] [DecidableEq d₃] (ρ : MState d₁) (σ : MState d₂) (e : d₃ ≃ d₁) :
    ((ρ.relabel e) ⊗ σ) = (ρ ⊗ σ).relabel (e.prodCongr (Equiv.refl d₂)) := by
  ext
  rfl --is this defeq abuse? I don't know

--PULLOUT
theorem MState.kron_relabel {d₁ d₂ d₃ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      [Fintype d₃] [DecidableEq d₃] (ρ : MState d₁) (σ : MState d₂) (e : d₃ ≃ d₂) :
    (ρ ⊗ σ.relabel e) = (ρ ⊗ σ).relabel ((Equiv.refl d₁).prodCongr e) := by
  ext
  rfl

--PULLOUT
theorem MState.prod_assoc {d₁ d₂ d₃ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      [Fintype d₃] [DecidableEq d₃] (ρ : MState d₁) (σ : MState d₂) (τ : MState d₃) :
    (ρ ⊗ σ ⊗ τ) = ((ρ ⊗ σ) ⊗ τ).relabel (Equiv.prodAssoc d₁ d₂ d₃).symm := by
  apply MState.ext
  simp only [MState.prod, MState.relabel, Subtype.mk.injEq]
  symm
  exact Matrix.kronecker_assoc ρ.m σ.m τ.m

--PULLOUT
theorem MState.relabel_cast {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂]
       (ρ : MState d₁) (e : d₂ = d₁) :
    ρ.relabel (Equiv.cast e) = cast (by have := e.symm; congr <;> (apply Subsingleton.helim; congr)) ρ := by
  ext i j
  simp
  rw [eq_comm] at e
  congr
  · apply Subsingleton.helim; congr
  · apply Subsingleton.helim; congr
  · symm; apply cast_heq
  · apply cast_heq
  · apply cast_heq

--PULLOUT
open ComplexOrder in
theorem MState.uniform_posDef {d : Type*} [Nonempty d] [Fintype d] [DecidableEq d] :
    (MState.uniform (d := d)).m.PosDef := by
  simp [uniform, ofClassical, m, HermitianMat.diagonal]
  exact Fintype.card_pos

--PULLOUT
open ComplexOrder in
theorem MState.posDef_of_unique {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) [Unique d] : ρ.m.PosDef := by
  rw [Subsingleton.allEq ρ MState.uniform]
  exact MState.uniform_posDef

--PULLOUT
theorem heq_iff_exists_eq_cast {α β : Sort u} (a : α) (b : β) :
    a ≍ b ↔ ∃ (h : β = α), a = cast h b := by
  use fun h ↦ ⟨type_eq_of_heq h.symm, eq_cast_iff_heq.mpr h⟩
  rintro ⟨rfl, h⟩
  rw [h, cast_eq]

--PULLOUT
@[gcongr]
theorem qRelEntropy_heq_congr {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂) (hρ : ρ₁ ≍ ρ₂) (hσ : σ₁ ≍ σ₂) :
    𝐃(ρ₁‖σ₁) = 𝐃(ρ₂‖σ₂) := by
  rw [heq_iff_exists_eq_cast] at hρ hσ
  obtain ⟨_, rfl⟩ := hρ
  obtain ⟨_, rfl⟩ := hσ
  simp [← MState.relabel_cast _ hd]

--now the actual file...

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
  -- which would then imply MonoidalCategory structure later (instead of just Category). For now we
  -- take the (logically equivalent, in the appropriate model) assumption that the associator is
  -- actually an equality.
  pAssoc i j k : prod (prod i j) k = prod i (prod j k)
  -- heqAssoc {i j k} (ρ : MState )
  hAssoc i j k :
    ((prodEquiv (prod i j) k).trans <|
      ((prodEquiv i j).prodCongr (Equiv.refl (H k))).trans <|
      (Equiv.prodAssoc _ _ _).trans <|
      ((Equiv.refl (H i)).prodCongr ((prodEquiv j k).symm)).trans
      (prodEquiv i (prod j k)).symm
    )
     = Equiv.cast (congrArg H <| pAssoc i j k)

attribute [instance] ResourcePretheory.FinH
attribute [instance] ResourcePretheory.DecEqH
attribute [instance] ResourcePretheory.NonemptyH

namespace ResourcePretheory

variable {ι : Type*} [ResourcePretheory ι]

/-- The `prod` operation of `ResourcePretheory` gives the natural product operation on `MState`s. Accessible
by the notation `ρ₁ ⊗ᵣ ρ₂`. -/
def prodRelabel {i j : ι} (ρ₁ : MState (H i)) (ρ₂ : MState (H j)) : MState (H (prod i j)) :=
  (ρ₁ ⊗ ρ₂).relabel (prodEquiv i j)

scoped infixl:65 "⊗ᵣ" => prodRelabel

theorem prodRelabel_assoc {i j k : ι} (ρ₁ : MState (H i)) (ρ₂ : MState (H j)) (ρ₃ : MState (H k)) :
    ρ₁ ⊗ᵣ ρ₂ ⊗ᵣ ρ₃ ≍ ρ₁ ⊗ᵣ (ρ₂ ⊗ᵣ ρ₃) := by
  simp [prodRelabel]
  simp [MState.relabel_kron, MState.relabel_comp]
  have h_equiv := hAssoc i j k
  rw [← Equiv.trans_assoc, Equiv.trans_cancel_right] at h_equiv
  have h_cong := congrArg (MState.relabel ((ρ₁⊗ρ₂)⊗ρ₃)) h_equiv
  rw [← eq_cast_iff_heq]; swap
  · rw [pAssoc]
  convert h_cong; clear h_equiv h_cong
  rw [← MState.relabel_cast]; swap
  · rw [pAssoc]
  rw [MState.kron_relabel, MState.prod_assoc]
  rw [MState.relabel_comp, MState.relabel_comp, MState.relabel_comp]
  rfl

/-- The `prod` operation of `ResourcePretheory` gives the natural product operation on `CPTPMap`s. Accessible
by the notation `M₁ ⊗ᵣ M₂`. -/
noncomputable def prodCPTPMap {i j k l : ι} (M₁ : CPTPMap (H i) (H j)) (M₂ : CPTPMap (H k) (H l)) :
    CPTPMap (H (prod i k)) (H (prod j l)) :=
  (CPTPMap.of_equiv (prodEquiv j l).symm).compose ((M₁ ⊗ₖ M₂).compose (CPTPMap.of_equiv (prodEquiv i k)))

scoped notation M₁ "⊗ₖᵣ" M₂ => prodCPTPMap M₁ M₂

open ComplexOrder in
theorem PosDef.prod {ι : Type*} [ResourcePretheory ι] {i j : ι}
      {ρ : MState (H i)} {σ : MState (H j)} (hρ : ρ.m.PosDef) (hσ : σ.m.PosDef)
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
theorem qRelEntropy_prodRelabel {i j : ι} (ρ₁ ρ₂ : MState (H i)) (σ₁ σ₂ : MState (H j)):
    𝐃(ρ₁ ⊗ᵣ σ₁‖ρ₂ ⊗ᵣ σ₂) = 𝐃(ρ₁‖ρ₂) + 𝐃(σ₁‖σ₂) := by
  simp [prodRelabel, qRelativeEnt_additive]

end ResourcePretheory

open ResourcePretheory

/-- A ResourcePretheory is `Unital` if it has a Hilbert space of size 1, i.e. `ℂ`. -/
class UnitalPretheory (ι : Type*) extends ResourcePretheory ι, One ι, Unique (H 1) where
  prod_one i : prod i 1 = i
  one_prod i : prod 1 i = i
  prod_default {i} (ρ : MState (H i)) :
    (toResourcePretheory.prodRelabel ρ (Inhabited.default : MState (H 1))) ≍ ρ
  default_prod {i} (ρ : MState (H i)) :
    (toResourcePretheory.prodRelabel (Inhabited.default : MState (H 1)) ρ) ≍ ρ

namespace UnitalPretheory

attribute [simp] prod_one
attribute [simp] one_prod

variable {ι : Type*} [UnitalPretheory ι]

/-- Powers of spaces. Defined for `PNat` so that we don't have zeroth powers. -/
noncomputable def spacePow (i : ι) (n : ℕ) : ι :=
  n.rec 1 (fun _ j ↦ prod j i)

scoped notation i "⊗^H[" n "]" => spacePow i n

@[simp]
theorem spacePow_zero (i : ι) : i⊗^H[0] = 1 := by
  rfl

@[simp]
theorem spacePow_one (i : ι) : i⊗^H[1] = i := by
  exact one_prod i

theorem spacePow_succ (i : ι) (n : ℕ) : i⊗^H[n + 1] = prod (i⊗^H[n]) i := by
  rfl

theorem spacePow_add {i : ι} (m n : ℕ) :
    i⊗^H[m + n] = prod (i⊗^H[m]) (i⊗^H[n]) := by
  induction n
  · simp
  · rename_i n ih
    rw [spacePow_succ, ← pAssoc, ← add_assoc, ← ih, spacePow_succ]

/-- Powers of states. Defined for `PNat`, so that we don't have zeroth powers -/
noncomputable def statePow {i : ι} (ρ : MState (H i)) (n : ℕ) : MState (H (i⊗^H[n])) :=
  n.rec default (fun _ σ ↦ σ ⊗ᵣ ρ)

scoped notation ρ "⊗^S[" n "]" => statePow ρ n

@[simp]
theorem statePow_zero {i : ι} (ρ : MState (H i)) : ρ⊗^S[0] = default :=
  rfl

@[simp]
theorem statePow_one {i : ι} (ρ : MState (H i)) : ρ⊗^S[1] ≍ ρ := by
  rw [← eq_cast_iff_heq]; swap
  · rw [spacePow_one]
  · rw [eq_cast_iff_heq, statePow]
    exact default_prod ρ

theorem statePow_succ {i : ι} (ρ : MState (H i)) (n : ℕ) : ρ⊗^S[n + 1] = ρ⊗^S[n] ⊗ᵣ ρ := by
  rfl

theorem statePow_add {i : ι} (ρ : MState (H i)) (m n : ℕ) : ρ⊗^S[m + n] ≍ ρ⊗^S[m] ⊗ᵣ ρ⊗^S[n] := by
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

set_option maxHeartbeats 800000 in
open ComplexOrder in
theorem PosDef.npow {ι : Type*} [p : UnitalPretheory ι] {i : ι}
      {ρ : MState (H i)} (hρ : ρ.m.PosDef) (n : ℕ)
      : (ρ⊗^S[n]).m.PosDef := by
  induction n
  · simp [MState.posDef_of_unique default]
  · apply ResourcePretheory.PosDef.prod ‹_› hρ

-- /-- Cast from one Hilbert space to another using the associator. -/
-- def statePow_cast {i : ι} {m n k : ℕ} (h : m + n = k)
--     : MState (H (prod (i⊗^H[m]) (i⊗^H[n]))) → MState (H (i⊗^H[k])) := by
--   sorry

-- @[simp]
-- theorem statePow_cast_eq_pow {i : ι} {m n k : ℕ} (ρ : MState (H i)) (h : m + n = k) :
--     statePow_cast h (ρ⊗^S[m] ⊗ᵣ ρ⊗^S[n]) = ρ⊗^S[k] := by
--   sorry

-- @[simp]
-- theorem qRelEntropy_statePow_cast {i : ι} {m n k : ℕ} (ρ₁ ρ₂ : MState (H (prod (i⊗^H[m]) (i⊗^H[n]))))
--   (h₁ h₂ : m + n = k) :
--     𝐃(statePow_cast h₁ ρ₁‖statePow_cast h₂ ρ₂) = 𝐃(ρ₁‖ρ₂) := by
--   sorry

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

theorem IsFree.npow {i : ι} {ρ : MState (H i)}
    (hρ : IsFree ρ) (n : ℕ) : IsFree (ρ⊗^S[n]) := by
  induction n
  · rw [statePow_zero, spacePow_zero]
    apply IsFree.of_unique
  · rw [statePow_succ]
    exact FreeStateTheory.free_prod ‹_› hρ

@[simp]
theorem reabel_cast_isFree {i j : ι} (ρ : MState (H i)) (h : j = i) {h' : H j = H i}:
    ρ.relabel (Equiv.cast h') ∈ IsFree ↔ ρ ∈ IsFree := by
  subst h
  simp

open NNReal

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
    NNReal.toReal <| RelativeEntResource (ρ⊗^S[n]) := by
  intro m n
  obtain ⟨σ₂, hσ₂f, hσ₂d⟩ := exists_isFree_relativeEntResource (ρ⊗^S[m])
  obtain ⟨σ₃, hσ₃f, hσ₃d⟩ := exists_isFree_relativeEntResource (ρ⊗^S[n])
  simp only [RelativeEntResource, ← NNReal.coe_add, coe_le_coe]
  rw [← ENNReal.coe_le_coe]
  simp [RelativeEntResource, ENNReal.ofNNReal] at hσ₂d hσ₃d ⊢
  rw [← hσ₂d, ← hσ₃d]
  clear hσ₂d hσ₃d
  have ht₁ : i⊗^H[m + n] = prod (i⊗^H[m]) (i⊗^H[n]) :=
    spacePow_add m n
  have ht : H (i⊗^H[m + n]) = H (prod (i⊗^H[m]) (i⊗^H[n])) :=
    congrArg H ht₁
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

noncomputable def GlobalRobustness {i : ι} : MState (H i) → ℝ≥0 :=
  fun ρ ↦ sInf {s | ∃ σ, (⟨1 / (1+s), by bound⟩ [ρ ↔ σ]) ∈ IsFree}

/-- A sequence of operations `f_n` is asymptotically nongenerating if `lim_{n→∞} RG(f_n(ρ_n)) = 0`, where
RG is `GlobalRobustness` and `ρ_n` is any sequence of free states. Equivalently, we can take the `max` (
over operations and states) on the left-hand side inside the limit.
-/
def IsAsymptoticallyNongenerating (dI dO : ι) (f : (n : ℕ) → CPTPMap (H (dI⊗^H[n])) (H (dO⊗^H[n]))) : Prop :=
  ∀ (ρs : (n : ℕ) → MState (H (dI⊗^H[n]))), (∀ n, IsFree (ρs n)) →
  Filter.Tendsto (fun n ↦ GlobalRobustness ((f n) (ρs n))) Filter.atTop (nhds 0)

end UnitalFreeStateTheory
