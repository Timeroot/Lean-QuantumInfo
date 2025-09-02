import Mathlib.Order.Notation
import Mathlib.Tactic.Finiteness

import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.UniformSpace.Cauchy

--Can this be rewritten more generally? For `finiteness` to work, I don't know how.
@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem ite_eq_top {α : Type*} [Top α] (h : Prop) [Decidable h] {x y : α} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    (if h then x else y) ≠ ⊤ := by
  split <;> assumption

theorem Equiv.trans_cancel_left (α β γ : Type*) (e : α ≃ β) (f : β ≃ γ) (g : α ≃ γ) :
    e.trans f = g ↔ f = e.symm.trans g := by
  constructor <;> (rintro rfl; simp [← Equiv.trans_assoc])

theorem Equiv.trans_cancel_right (α β γ : Type*) (e : α ≃ β) (f : β ≃ γ) (g : α ≃ γ) :
    e.trans f = g ↔ e = g.trans f.symm := by
  constructor <;> (rintro rfl; simp [Equiv.trans_assoc])

theorem heq_iff_exists_eq_cast {α β : Sort u} (a : α) (b : β) :
    a ≍ b ↔ ∃ (h : β = α), a = cast h b := by
  use fun h ↦ ⟨type_eq_of_heq h.symm, eq_cast_iff_heq.mpr h⟩
  rintro ⟨rfl, h⟩
  rw [h, cast_eq]

/-- Minimizing a bilinear form in one argument over a bounded set, given a continuous function in the
other argument. -/
--This can probably be generalized to rings besides ℝ, and I don't know if CompleteSpace is needed. I
--actually only need it for the finite-dimensional case.
theorem Bornology.IsBounded.continuous_bilinear
  {E : Type*} [AddCommGroup E] [Module ℝ E] [MetricSpace E] [CompleteSpace E]
  (f : LinearMap.BilinForm ℝ E) {S : Set E} (hS : Bornology.IsBounded S) :
    Continuous fun x ↦ ⨆ y : S, f y x := by
  sorry
