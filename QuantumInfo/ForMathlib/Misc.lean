/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.CompletePartialOrder

--Can this be rewritten more generally? For `finiteness` to work, I don't know how.
@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem ite_eq_top {α : Type*} [Top α] (h : Prop) [Decidable h] {x y : α} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    (if h then x else y) ≠ ⊤ := by
  split <;> assumption

section subtype_val_iSup
/-
When
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/diamond.20in.20ConditionallyCompleteLattice/near/538053239
is fixed, the declarations below should be changed to
```
theorem subtype_val_iSup {ι α : Type*} [ConditionallyCompleteLattice α] {s : Set α} {f : ι → α}
    [Inhabited ↑s] [s.OrdConnected] (h : ∀ i, f i ∈ s) :
    (⨆ i, (⟨f i, h i⟩ : ↑s)).val = ⨆ i, f i := by
  sorry

theorem subtype_val_iSup' {ι α : Type*} [ConditionallyCompleteLattice α] {s : Set α} {f : ι → α}
    [Inhabited ↑s] [s.OrdConnected] (h : ∀ i, f i ∈ s) :
    ⨆ i, (⟨f i, h i⟩ : ↑s) = ⟨⨆ i, f i, by sorry⟩ := by
  rw [Subtype.eq_iff, subtype_val_iSup]
```
Sadly, though, there's a "diamond" and we need it with the other data (the one we specify more narrowly
below).
-/
variable {ι α : Type*} [i : Nonempty ι] [ConditionallyCompleteLattice α]
  {f : ι → α} {a b : α} [Fact (a ≤ b)]

/- This isn't marked as `simp` because rewriting from a sup over a `CompleteLattice` into a
`ConditionallyCompleteLattice` would, pretty often, be undesirable. -/
theorem subtype_val_iSup (h : ∀ i, f i ∈ Set.Icc a b) :
    (⨆ i, (⟨f i, h i⟩ : ↑(Set.Icc a b))).val = ⨆ i, f i := by
  simp only [iSup, sSup, Set.range_eq_empty_iff, not_isEmpty_of_nonempty, reduceDIte]
  congr 1; ext1
  simp

theorem subtype_val_iSup' (h : ∀ i, f i ∈ Set.Icc a b) :
    ⨆ i, (⟨f i, h i⟩ : ↑(Set.Icc a b)) =
      ⟨⨆ i, f i, ⟨(h i.some).1.trans (le_ciSup ⟨b, by intro; grind⟩ _), ciSup_le (h ·|>.2)⟩⟩ := by
  rw [Subtype.eq_iff, subtype_val_iSup]

/- This isn't marked as `simp` because rewriting from a sup over a `CompleteLattice` into a
`ConditionallyCompleteLattice` would, pretty often, be undesirable. -/
theorem subtype_val_iInf (h : ∀ i, f i ∈ Set.Icc a b) :
    (⨅ i, (⟨f i, h i⟩ : ↑(Set.Icc a b))).val = ⨅ i, f i := by
  simp only [iInf, sInf, Set.range_eq_empty_iff, not_isEmpty_of_nonempty, reduceDIte]
  congr 1; ext1
  simp

theorem subtype_val_iInf' (h : ∀ i, f i ∈ Set.Icc a b) :
    ⨅ i, (⟨f i, h i⟩ : ↑(Set.Icc a b)) =
      ⟨⨅ i, f i, ⟨le_ciInf (h ·|>.1), (ciInf_le ⟨a, by intro; grind⟩ _).trans (h i.some).2⟩⟩ := by
  rw [Subtype.eq_iff, subtype_val_iInf]

end subtype_val_iSup

@[simp]
theorem Real.log_comp_exp : Real.log ∘ Real.exp = _root_.id := by
  ext
  simp
