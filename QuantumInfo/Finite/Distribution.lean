import Mathlib

import QuantumInfo.Finite.Prob

noncomputable section
open NNReal
open Classical

/--
We define our own (discrete) probability distribution notion here, instead
of using `PMF`, because that uses ENNReals everywhere to maintain compatibility
with `MeasureTheory.measure`.

The probabilities internal to a Distribution are NNReals. This lets us more easily
write the statement that they sum to 1, since NNReals can be added. (Probabilities,
on their own, cannot.) But the FunLke instance gives `Prob` out, which carry the
information that they are all at most one: true probabilities.
-/

def Distribution (α : Type u) [Fintype α] : Type u :=
  { f : α → ℝ≥0 // Finset.sum Finset.univ f = 1 }

namespace Distribution

variable {α β : Type*} [Fintype α] [Fintype β]

theorem val_le_one (d : Distribution α) : ∀ x, d.val x ≤ 1 := by
  intro x
  simp [← d.prop, Fintype.sum_eq_sum_compl_add x]

instance (priority := low) instFunLikeProb : FunLike (Distribution α) α Prob where
  coe p a := ⟨p.1 a, ⟨(p.1 a).2, p.val_le_one a⟩⟩
  coe_injective' _ _ h :=
    Subtype.ext <| funext fun v ↦ by
      simpa only [Subtype.mk.injEq, coe_inj] using congrFun h v

instance instFunLike : FunLike (Distribution α) α NNReal where
  coe p := p.val
  coe_injective' _ _ h := Subtype.eq h

abbrev prob (d : Distribution α) := (d : α → Prob)

@[simp]
theorem funLike_eq_funLike (d : Distribution α) : Prob.toNNReal ∘ (d : α → Prob) = (d : α → ℝ≥0) := by
  rfl

@[simp]
theorem fun_eq_val (d : Distribution α) (x : α): d.val x = d x :=
  rfl

@[ext]
theorem ext {p q : Distribution α} (h : ∀ x, p x = q x) : p = q :=
  DFunLike.ext p q h

theorem ext_iff {p q : Distribution α} : p = q ↔ ∀ x, p x = q x :=
  DFunLike.ext_iff

@[simp]
theorem normalized (d : Distribution α) : Finset.sum Finset.univ d = 1 :=
  d.prop

/-- Make an constant distribution: supported on a single element. This is also called, variously, a
 "One-point distribution", a "Degenerate distribution", a "Deterministic distribution", a
 "Delta function", or a "Point mass distribution". -/
def constant (x : α) : Distribution α :=
  ⟨fun y ↦ if x = y then 1 else 0,
    by simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]⟩

theorem constant_def (x : α) : (constant x : α → ℝ≥0) = fun y ↦ if x = y then 1 else 0 := by
  rfl

@[simp]
theorem constant_eq (x : α) : constant x y = if x = y then 1 else 0 := by
  rfl

@[simp]
theorem constant_def' (x y : α) : (constant x : α → Prob) y = if x = y then 1 else 0 := by
  rw [← Prob.eq_iff_nnreal]
  change (Prob.toNNReal ∘ (constant x)) y = (if x = y then 1 else 0 : Prob)
  rw [funLike_eq_funLike (constant x), constant_def x]
  split_ifs with h
  <;> simp [h]

/-- Make an uniform distribution. -/
def uniform [Nonempty α] : Distribution α :=
  ⟨fun _ ↦ 1 / (Finset.univ.card (α := α)), by
    have : 0 < Finset.univ.card (α := α) :=
      Finset.Nonempty.card_pos (Finset.univ_nonempty_iff.mpr inferInstance)
    field_simp
    ⟩

@[simp]
theorem uniform_def [Nonempty α] (y : α) : uniform y = 1 / (Finset.univ.card (α := α)) :=
  rfl

/-- Make a distribution on a product of two Fintypes. -/
def prod (d1 : Distribution α) (d2 : Distribution β) : Distribution (Prod α β) :=
  ⟨fun x ↦ (d1 x.1) * (d2 x.2), by simp [← Finset.mul_sum]⟩

@[simp]
theorem prod_def (x : α) (y : β) : prod d1 d2 ⟨x, y⟩ = (d1 x) * (d2 y) :=
  rfl

def extend_right (d : Distribution α) : Distribution (α ⊕ β) :=
  ⟨fun x ↦ Sum.casesOn x d.val (Function.const _ 0), by simp⟩

def extend_left (d : Distribution α) : Distribution (β ⊕ α) :=
  ⟨fun x ↦ Sum.casesOn x (Function.const _ 0) d.val, by simp⟩

/-- Make a convex mixture of two distributions on the same set. -/
def mix (d1 : Distribution α) (d2 : Distribution α) (p : ℝ≥0) (hp : p≤1) : Distribution (α) :=
  ⟨fun x ↦ p * (d1.val x) + ⟨1-p, sub_nonneg_of_le hp⟩ * (d2.val x),
    by simp [Finset.sum_add_distrib, ← Finset.mul_sum, ← NNReal.eq_iff]⟩

end Distribution
