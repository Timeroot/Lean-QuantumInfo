import ClassicalInfo.Prob

/-! # Distributions on finite sets

We define the type `Distribution α` on a `Fintype α`. By restricting ourselves to distributoins on finite types,
a lot of notation and casts are greatly simplified. This suffices for (most) finite-dimensional quantum theory.
-/

noncomputable section
open NNReal
open Classical
open BigOperators

/--
We define our own (discrete) probability distribution notion here, instead
of using `PMF` from Mathlib, because that uses ENNReals everywhere to maintain compatibility
with `MeasureTheory.Measure`.

The probabilities internal to a Distribution are NNReals. This lets us more easily
write the statement that they sum to 1, since NNReals can be added. (Probabilities,
on their own, cannot.) But the FunLike instance gives `Prob` out, which carry the
information that they are all in the range [0,1].
-/
def Distribution (α : Type u) [Fintype α] : Type u :=
  { f : α → Prob // Finset.sum Finset.univ (fun i ↦ (f i).toReal) = 1 }

namespace Distribution

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Make a distribution, proving only that the values are nonnegative and that the
sum is 1. The fact that the values are at most 1 is derived as a consequence. -/
def mk' (f : α → ℝ) (h₁ : ∀i, 0 ≤ f i) (hN : ∑ i, f i = 1) : Distribution α :=
  have h₃ : ∀x, f x ≤ 1 := by
    intro x
    simp [← hN, Fintype.sum_eq_sum_compl_add x]
    exact Finset.sum_nonneg' h₁
  ⟨ fun i ↦ ⟨f i, ⟨h₁ i, h₃ i⟩⟩, hN⟩

instance instFunLikeProb : FunLike (Distribution α) α Prob where
  coe p a := p.1 a
  coe_injective' _ _ h :=
    Subtype.ext <| funext fun v ↦ by
      simpa only [Subtype.mk.injEq, coe_inj] using congrFun h v

@[simp]
theorem normalized (d : Distribution α) : Finset.sum Finset.univ (fun i ↦ (d i).toReal) = 1 :=
  d.2

abbrev prob (d : Distribution α) := (d : α → Prob)

@[simp]
theorem fun_eq_val (d : Distribution α) (x : α): d.val x = d x :=
  rfl

@[ext]
theorem ext {p q : Distribution α} (h : ∀ x, p x = q x) : p = q :=
  DFunLike.ext p q h

/-- Make an constant distribution: supported on a single element. This is also called, variously, a
 "One-point distribution", a "Degenerate distribution", a "Deterministic distribution", a
 "Delta function", or a "Point mass distribution". -/
def constant (x : α) : Distribution α :=
  ⟨fun y ↦ if x = y then 1 else 0,
    by simp [apply_ite]⟩

theorem constant_def (x : α) : (constant x : α → Prob) = fun y ↦ if x = y then 1 else 0 := by
  rfl

@[simp]
theorem constant_eq (x : α) : constant x y = if x = y then 1 else 0 := by
  rfl

@[simp]
theorem constant_def' (x y : α) : (constant x : α → Prob) y = if x = y then 1 else 0 := by
  rw [← Prob.eq_iff_nnreal]
  change (Prob.toNNReal ∘ (constant x)) y = (if x = y then 1 else 0 : Prob)
  rw [constant_def x]
  split_ifs with h
  <;> simp [h]

/-- If a distribution has an element with probability 1, the distribution has a constant. -/
theorem constant_of_exists_one {D : Distribution α} {x : α} (h : D x = 1) : D = Distribution.constant x := by
  ext y
  by_cases h₂ : x = y
  · simp [h, ← h₂]
  · simp only [constant_eq, h₂, ↓reduceIte, Prob.toReal_zero]
    by_contra h₃
    replace h₃ : 0 < (D y : ℝ) := by
      linarith (config := {splitNe := true}) only [h₃, @Prob.zero_le_coe (D y)]
    have := D.normalized
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), h, Prob.toReal_one] at this
    rw [← Finset.add_sum_erase _ _ (a := y) (by simpa using (Ne.symm h₂))] at this
    have : 0 ≤ ∑ x ∈ Finset.erase (Finset.erase Finset.univ x) y, (D x : ℝ) :=
      Finset.sum_nonneg' (fun _ ↦ Prob.zero_le_coe)
    linarith

/-- Make an uniform distribution. -/
def uniform [Nonempty α] : Distribution α :=
  ⟨fun _ ↦ ⟨1 / (Finset.univ.card (α := α)), by
    have : 0 < Finset.univ.card (α := α) :=
      Finset.Nonempty.card_pos (Finset.univ_nonempty_iff.mpr inferInstance)
    constructor
    · positivity
    · apply div_le_of_le_mul₀ (Nat.cast_nonneg Finset.univ.card)
      · exact zero_le_one
      · simpa only [one_mul, Nat.one_le_cast] using this
    ⟩, by
    have : 0 < Finset.univ.card (α := α) :=
      Finset.Nonempty.card_pos (Finset.univ_nonempty_iff.mpr inferInstance)
    field_simp
    ⟩

@[simp]
theorem uniform_def [Nonempty α] (y : α) : ((uniform y) : ℝ) = 1 / (Finset.univ.card (α := α)) :=
  rfl

/-- Make a distribution on a product of two Fintypes. -/
def prod (d1 : Distribution α) (d2 : Distribution β) : Distribution (Prod α β) :=
  ⟨fun x ↦ (d1 x.1) * (d2 x.2), by
    simp [← Finset.mul_sum, Fintype.sum_prod_type]⟩

@[simp]
theorem prod_def (x : α) (y : β) : prod d1 d2 ⟨x, y⟩ = (d1 x) * (d2 y) :=
  rfl

/-- Given a distribution on α, extend it to a distribution on `Sum α β` by giving it no support on `β`. -/
def extend_right (d : Distribution α) : Distribution (α ⊕ β) :=
  ⟨fun x ↦ Sum.casesOn x d.val (Function.const _ 0), by simp⟩

/-- Given a distribution on α, extend it to a distribution on `Sum β α` by giving it no support on `β`. -/
def extend_left (d : Distribution α) : Distribution (β ⊕ α) :=
  ⟨fun x ↦ Sum.casesOn x (Function.const _ 0) d.val, by simp⟩

/-- Make a convex mixture of two distributions on the same set. -/
instance instMixable : Mixable (α → ℝ) (Distribution α) :=
  Mixable.instSubtype (inferInstance) (fun _ _ hab hx hy ↦ by
    simp [Mixable.mix_ab, Finset.sum_add_distrib, ← Finset.mul_sum, hab, hx, hy]
  )

/-- Given a distribution on type α and an equivalence to type β, get the corresponding
distribution on type β. -/
def relabel (d : Distribution α) (σ : β ≃ α) : Distribution β :=
  ⟨fun b ↦ d (σ b),
   by rw [Equiv.sum_comp σ (fun a ↦ (d a : ℝ))]; exact d.prop⟩

end Distribution
