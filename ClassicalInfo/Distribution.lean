import ClassicalInfo.Prob

import Mathlib.Analysis.Convex.Combination

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
theorem fun_eq_val (d : Distribution α) : d.val = d :=
  rfl

@[simp]
theorem funlike_apply (d : α → Prob) (h : _) (x : α) :
    DFunLike.coe (self := instFunLikeProb) ⟨d, h⟩ x = d x :=
  rfl

@[ext]
theorem ext {p q : Distribution α} (h : ∀ x, p x = q x) : p = q :=
  DFunLike.ext p q h

/-- A distribution is a witness that d is nonempty. -/
instance nonempty (d : Distribution α) : Nonempty α := by
  by_contra h
  simpa [not_nonempty_iff.mp h] using d.2

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

-- The two properties below (and congrRandVar) follow from the fact that Distribution is a contravariant functor.
-- However, mathlib does not seem to support that outside of the CategoryTheory namespace
/-- Distributions on α and β are equivalent for equivalent types α ≃ β. -/
def congr (σ : α ≃ β) : Distribution α ≃ Distribution β := by
  constructor
  case toFun => exact fun d ↦ relabel d σ.symm
  case invFun => exact fun d ↦ relabel d σ
  case left_inv =>
    intro d
    ext i
    unfold relabel
    simp only [← fun_eq_val, Equiv.symm_apply_apply, Subtype.coe_eta]
  case right_inv =>
    intro d
    ext i
    unfold relabel
    simp only [← fun_eq_val, Equiv.apply_symm_apply, Subtype.coe_eta]

@[simp]
theorem congr_apply (σ : α ≃ β) (d : Distribution α) (j : β): (congr σ d) j = d (σ.symm j) := by
  rfl

/-- The inverse and congruence operations for distributions commute -/
@[simp]
theorem congr_symm_apply (σ : α ≃ β) : (Distribution.congr σ).symm = Distribution.congr σ.symm := by
  rfl

/-- The distribution on Fin 2 corresponding to a coin with probability p. Chance p of 1, 1-p of 0. -/
def coin (p : Prob) : Distribution (Fin 2) :=
  ⟨(if · = 0 then p else p.one_minus), by simp⟩

@[simp]
theorem coin_val_zero (p : Prob) : coin p 0 = p := by
  simp [coin]

@[simp]
theorem coin_val_one (p : Prob) : coin p 1 = p.one_minus := by
  simp [coin]

section randvar

/-- A `T`-valued random variable over `α` is a map `var : α → T` along
with a probability distribution `distr : Distribution α`. -/
structure RandVar (α : Type*) [Fintype α] (T : Type*) where
  var : α → T
  distr : Distribution α

instance instFunctor : Functor (RandVar α) where map f e := ⟨f ∘ e.1, e.2⟩

instance instLawfulFunctor : LawfulFunctor (RandVar α) where
  map_const {α} {β} := by rfl
  id_map _ := by rfl
  comp_map _ _ _ := by rfl

-- `U` is required to be a group just because mix below uses Convex.sum_mem,
-- but it should be provable with just `AddCommMonoid U`
variable {T U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T]

/-- `Distribution.exp_val` is the expectation value of a random variable `X`. Under the hood,
it is the "convex combination over a finite family" on the type `T`, afforded by the `Mixable` instance,
with the probability distribution of `X` as weights. -/
def expect_val (X : RandVar α T) : T := by
  let u : U := ∑ i ∈ Finset.univ, (Prob.toReal (X.distr i)) • (inst.to_U (X.var i))
  have ht : ∃ t : T, inst.to_U t = u := by
    have h₀ : ∀ i ∈ Finset.univ, 0 ≤ Prob.toReal (X.distr i) := by simp only [Finset.mem_univ, Prob.zero_le_coe, implies_true]
    have h₁ : ∑ i ∈ Finset.univ, Prob.toReal (X.distr i) = 1 := by simp only [normalized]
    have hz : ∀ i ∈ Finset.univ, inst.to_U (X.var i) ∈ Set.range inst.to_U := by simp only [Finset.mem_univ, implies_true, Set.mem_range_self]
    have hu : u ∈ Set.range inst.to_U := Convex.sum_mem inst.convex h₀ h₁ hz
    exact Set.mem_range.mp hu
  exact (inst.mkT ht).1

/-- The expectation value of a random variable over `α = Fin 2` is the same as `Mixable.mix`
with probabiliy weight `X.distr 0` -/
theorem expect_val_eq_mixable_mix (d : Distribution (Fin 2)) (x₁ x₂ : T) : expect_val ⟨![x₁, x₂], d⟩ = Mixable.mix (d 0) x₁ x₂ := by
  apply Mixable.to_U_inj
  simp only [Mixable.mix, expect_val, constant, DFunLike.coe, Mixable.to_U_of_mkT]
  calc
    ∑ i : Fin (Nat.succ 0).succ, Prob.toReal (d i) • Mixable.to_U (![x₁, x₂] i) = ∑ i ∈ Finset.range 2, Prob.toReal (d i) • Mixable.to_U (![x₁, x₂] i) := by
      simpa [Finset.range_succ] using add_comm _ _
    _ = ∑ i ∈ Finset.range 1, Prob.toReal (d i) • Mixable.to_U (![x₁, x₂] i) + Prob.toReal (d 1) • Mixable.to_U (![x₁, x₂] 1) :=
      Finset.sum_range_succ (fun i => Prob.toReal (d i) • Mixable.to_U (![x₁, x₂] i)) 1
    _ = Prob.toReal (d 0) • Mixable.to_U (![x₁, x₂] 0) + Prob.toReal (d 1) • Mixable.to_U (![x₁, x₂] 1) := by
      simp [Finset.sum_range_one (fun i => Prob.toReal (d i) • Mixable.to_U (![x₁, x₂] i))]
    _ = Prob.toReal (d 0) • Mixable.to_U x₁ + Prob.toReal (d 0).one_minus • Mixable.to_U x₂ := by
      congr
      simpa only [Subtype.eq_iff, fun_eq_val, Fin.sum_univ_two, ← eq_sub_iff_add_eq'] using d.property

/-- The expectation value of a random variable with constant probability distribution `constant x` is its value at `x` -/
theorem expect_val_constant (x : α) (f : α → T) : expect_val ⟨f, (constant x)⟩ = f x := by
  apply Mixable.to_U_inj
  simp only [expect_val, constant, DFunLike.coe, Mixable.to_U_of_mkT, apply_ite, Prob.toReal_one,
    Prob.toReal_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The expectation value of a nonnegative real random variable is also nonnegative -/
theorem zero_le_expect_val (d : Distribution α) (f : α → ℝ) (hpos : 0 ≤ f) : 0 ≤ expect_val ⟨f, d⟩ := by
  simp only [expect_val, Mixable.mkT, Mixable.to_U, id]
  apply Fintype.sum_nonneg
  intro x
  specialize hpos x
  exact mul_nonneg Prob.zero_le_coe hpos

/-- `T`-valued random variables on `α` and `β` are equivalent if `α ≃ β` -/
def congrRandVar (σ : α ≃ β) : RandVar α T ≃ RandVar β T := by
  constructor
  case toFun => exact fun X ↦ { var := X.var ∘ σ.symm, distr := Distribution.congr σ X.distr }
  case invFun => exact fun X ↦ { var := X.var ∘ σ, distr := Distribution.congr σ.symm X.distr }
  case left_inv =>
    intro e
    simp only
    congr
    · simp only [Function.comp_assoc, Subtype.coe_eta, Equiv.symm_comp_self, Function.comp_id]
    · rw [←Distribution.congr_symm_apply, Equiv.symm_apply_apply]
  case right_inv =>
    intro e
    simp only
    congr
    · simp only [Function.comp_assoc, Subtype.coe_eta, Equiv.self_comp_symm, Function.comp_id]
    · rw [←Distribution.congr_symm_apply, Equiv.apply_symm_apply]

/-- Given a `T`-valued random variable `X` over `α`, mapping over `T` commutes with the equivalence over `α` -/
def map_congr_eq_congr_map {S : Type _} [Mixable U S] (f : T → S) (σ : α ≃ β) (X : RandVar α T) :
  f <$> congrRandVar σ X = congrRandVar σ (f <$> X) := by rfl

/-- The expectation value is invariant under equivalence of random variables -/
@[simp]
theorem expect_val_congr_eq_expect_val (σ : α ≃ β) (X : RandVar α T) : expect_val (congrRandVar σ X) = expect_val X := by
  apply Mixable.to_U_inj
  simp only [expect_val, congrRandVar, Equiv.coe_fn_mk, Function.comp_apply, Mixable.to_U_of_mkT,
    congr_apply]
  rw [Equiv.sum_comp σ.symm (fun i : α ↦ Prob.toReal ↑(X.distr i) • Mixable.to_U (X.var i))]

end randvar

end Distribution
