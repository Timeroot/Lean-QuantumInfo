/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Init
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Real.Basic

/-!
# Finite majorization

Finite real-vector majorization is represented by descending prefix sums. This
is reusable order-combinatorics support used by theorem-facing entanglement
modules such as Nielsen pure-state conversion.
-/

@[expose] public section

namespace QIT

universe u

variable {ι : Type u} [Fintype ι]

noncomputable section

/-- Entries of a finite real vector, sorted in descending order. -/
def descEntries (x : ι -> ℝ) : List ℝ :=
  (Finset.univ.toList.map x).mergeSort (fun a b => b ≤ a)

/-- Sum of the first `k` entries after sorting a finite real vector in descending order. -/
def descPrefixSum (x : ι -> ℝ) (k : ℕ) : ℝ :=
  ((descEntries x).take k).sum

/-- Total sum of a finite real vector, computed from its descending entries. -/
def descTotalSum (x : ι -> ℝ) : ℝ :=
  (descEntries x).sum

/-- `Majorizes y x` means that `y` majorizes `x`: every descending prefix sum of
`x` is bounded by the corresponding descending prefix sum of `y`, and the total
sums agree. -/
def Majorizes (y x : ι -> ℝ) : Prop :=
  (∀ k : ℕ, descPrefixSum x k ≤ descPrefixSum y k) ∧ descTotalSum x = descTotalSum y

@[simp]
theorem descPrefixSum_zero (x : ι -> ℝ) :
    descPrefixSum x 0 = 0 := by
  simp [descPrefixSum]

/-- Descending entries are sorted in nonincreasing order. -/
theorem descEntries_sortedGE (x : ι -> ℝ) :
    (descEntries x).SortedGE := by
  unfold descEntries
  exact List.sortedGE_mergeSort

/-- Majorization is reflexive for finite real vectors. -/
theorem majorizes_refl (x : ι -> ℝ) :
    Majorizes x x :=
  ⟨fun _ => le_rfl, rfl⟩

/-- Extract the descending-prefix inequality from a majorization hypothesis. -/
theorem majorizes_prefixSum_le {y x : ι -> ℝ} (h : Majorizes y x) (k : ℕ) :
    descPrefixSum x k ≤ descPrefixSum y k :=
  h.1 k

/-- Extract the total-sum equality from a majorization hypothesis. -/
theorem majorizes_sum_eq {y x : ι -> ℝ} (h : Majorizes y x) :
    descTotalSum x = descTotalSum y :=
  h.2

end

end QIT
