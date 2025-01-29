import Mathlib.Data.NNReal.Basic
import Mathlib.Analysis.Convex.Mul
import Mathlib.Data.Real.EReal

/-! # Probabilities

This defines a type `Prob`, which is simply any real number in the interval O to 1. This then comes with
additional statements such as its application to convex sets, and it makes useful type alias for
functions that only make sense on probabilities.

A significant application is in the `Mixable` typeclass, also in this file, which is a general notion
of convex combination that applies to types as opposed to sets; elements are `Mixable.mix`ed using `Prob`s.
-/

noncomputable section
open NNReal
open Classical

/-- `Prob` is a real number in the interval [0,1]. Similar to NNReal in many definitions, but this
  allows other nice things more 'safely' such as convex combination. -/
@[reducible]
def Prob := { p : ℝ // 0 ≤ p ∧ p ≤ 1 }

namespace Prob

instance instZero : Zero Prob :=
  ⟨0, by simp⟩

instance instOne : One Prob :=
  ⟨1, by simp⟩

instance instMul : Mul Prob :=
  ⟨fun x y ↦ ⟨x.1 * y.1,
    ⟨mul_nonneg x.2.1 y.2.1, mul_le_one₀ x.2.2 y.2.1 y.2.2⟩⟩⟩

@[simp]
theorem val_zero : (0 : Prob).val = 0 :=
  rfl

@[simp]
theorem val_one : (1 : Prob).val = 1 :=
  rfl

@[simp]
theorem val_mul (x y : Prob) : (x * y).val = x.val * y.val :=
  rfl

@[simp]
theorem val_inf (x y : Prob) : (x ⊓ y).val = x.val ⊓ y.val :=
  rfl

@[simp]
theorem val_sup (x y : Prob) : (x ⊔ y).val = x.val ⊔ y.val :=
  rfl

instance instCommMonoidWithZero : CommMonoidWithZero Prob where
  mul_assoc := by intros; ext; simp [mul_assoc]
  one_mul := by intros; ext; simp
  mul_one := by intros; ext; simp
  mul_comm := by intros; ext; simp [mul_comm]
  mul_zero := by intros; ext; simp
  zero_mul := by intros; ext; simp

instance instLinearOrder : LinearOrder Prob :=
  inferInstance

instance instOrderedCommMonoid : LinearOrderedCommMonoid Prob where
  __ := Prob.instLinearOrder
  mul_le_mul_left := by
    intros a b h c
    rw [← Subtype.coe_le_coe]
    exact mul_le_mul_of_nonneg_left h c.2.1

instance instDenselyOrdered : DenselyOrdered Prob :=
  show DenselyOrdered (Set.Icc 0 1) from Set.instDenselyOrdered

instance instBoundedOrder : BoundedOrder Prob where
  bot := 0
  top := 1
  bot_le a := a.2.1
  le_top a := a.2.2

instance instCompleteLinearOrder : CompleteLinearOrder Prob where
  __ := Prob.instLinearOrder
  __ : DistribLattice Prob := inferInstance
  __ := Prob.instLinearOrder.toBiheytingAlgebra
  sSup s := ⟨sSup (Subtype.val '' s),
    Real.sSup_nonneg fun _ ⟨H1,H2⟩ ↦ H2.2 ▸ H1.2.1,
    Real.sSup_le (fun _ ⟨H1,H2⟩ ↦ H2.2 ▸ H1.2.2) (zero_le_one' ℝ)⟩
  le_sSup s a ha :=
    le_csSup (a := a.val) ⟨1, fun _ ⟨c,d⟩ ↦ d.2 ▸ c.2.2⟩ ⟨a, ha, rfl⟩
  sSup_le s a h :=
    Real.sSup_le (fun _ ⟨p,hp1,hp2⟩ ↦ hp2 ▸ h p hp1) a.2.1
  sInf s := if h : s.Nonempty then ⟨sInf (Subtype.val '' s),
    Real.sInf_nonneg fun _ ⟨H1,H2⟩ ↦ H2.2 ▸ H1.2.1,
      let ⟨x,hx⟩ := h
      csInf_le_of_le ⟨0, fun _ ⟨c,d⟩ ↦ d.2 ▸ c.2.1⟩ ⟨x, hx, rfl⟩ x.2.2
    ⟩ else 1
  sInf_le s a ha := by
    dsimp only [sInf]
    split_ifs with h
    · exact csInf_le (a := a.val) ⟨0, fun _ ⟨c,d⟩ ↦ d.2 ▸ c.2.1⟩ ⟨a, ha, rfl⟩
    · exact (Set.not_mem_empty a (Set.not_nonempty_iff_eq_empty.mp h ▸ ha)).elim
  le_sInf s a h := by
    dsimp only [sInf]
    split_ifs with h₂
    · exact le_csInf (Set.Nonempty.image Subtype.val h₂) fun _ ⟨c,d⟩ ↦ d.2 ▸ h c d.1
    · exact a.2.2

instance instInhabited : Inhabited Prob where
  default := 0

/-- Coercion `Prob → ℝ`. -/
@[coe] def toReal : Prob → ℝ := Subtype.val

instance : Coe Prob ℝ := ⟨toReal⟩

@[simp]
theorem zero_le_coe {p : Prob} : 0 ≤ (p : ℝ) :=
  p.2.1

@[simp]
theorem coe_le_one {p : Prob} : (p : ℝ) ≤ 1 :=
  p.2.2

@[simp]
theorem zero_le {p : Prob} : 0 ≤ p :=
  zero_le_coe

@[simp]
theorem le_one {p : Prob} : p ≤ 1 :=
  coe_le_one

@[simp]
theorem val_eq_coe (n : Prob) : n.val = n :=
  rfl

instance canLift : CanLift ℝ Prob toReal fun r => 0 ≤ r ∧ r ≤ 1 :=
  Subtype.canLift _

@[ext] protected theorem eq {n m : Prob} : (n : ℝ) = (m : ℝ) → n = m :=
  Subtype.eq

theorem ne_iff {x y : Prob} : (x : ℝ) ≠ (y : ℝ) ↔ x ≠ y :=
  not_congr <| Prob.eq_iff.symm

@[simp]
theorem toReal_mk : toReal { val := x, property := hx} = x :=
  rfl

@[simp, norm_cast]
theorem toReal_zero : (0 : Prob) = (0 : ℝ) :=
  rfl

@[simp, norm_cast]
theorem toReal_one : (1 : Prob) = (1 : ℝ) :=
  rfl

@[simp, norm_cast]
theorem toReal_mul (x y : Prob): (x * y : Prob) = (x : ℝ) * (y : ℝ) :=
  rfl

/-- Coercion `Prob → ℝ≥0`. -/
@[coe] def toNNReal : Prob → ℝ≥0 :=
  fun p ↦ ⟨p.val, zero_le_coe⟩

@[simp]
theorem toNNReal_mk : toNNReal { val := x, property := hx} = { val := x, property := hx.1 } :=
  rfl

instance : Coe Prob ℝ≥0 := ⟨toNNReal⟩

instance canLiftNN : CanLift ℝ≥0 Prob toNNReal fun r => r ≤ 1 :=
  ⟨fun x hx ↦ ⟨⟨x, ⟨x.2, hx⟩⟩, rfl⟩⟩

protected theorem eq_iff_nnreal (n m : Prob) : (n : ℝ≥0) = (m : ℝ≥0) ↔ n = m := by
  obtain ⟨n,hn⟩ := n
  obtain ⟨m,hn⟩ := m
  simp only [toNNReal_mk, Subtype.mk.injEq, NNReal]

@[simp, norm_cast]
theorem toNNReal_zero : (0 : Prob) = (0 : ℝ≥0) :=
  rfl

@[simp, norm_cast]
theorem toNNReal_one : (1 : Prob) = (1 : ℝ≥0) :=
  rfl

def NNReal.asProb (p : ℝ≥0) (hp : p ≤ 1) : Prob :=
  ⟨p, ⟨p.2, hp⟩⟩

def NNReal.asProb' (p : ℝ≥0) (hp : p.1 ≤ 1) : Prob :=
  ⟨p, ⟨p.2, hp⟩⟩

def one_minus (p : Prob) : Prob :=
  ⟨1 - p.val,
    ⟨by simp [p.2.2], by simp [p.2.1]⟩⟩

@[simp]
theorem val_one_minus (p : Prob) : p.one_minus.val = 1-p.val :=
  rfl

@[simp, norm_cast]
theorem coe_one_minus (p : Prob) : (p.one_minus : ℝ) = 1-(p : ℝ) :=
  rfl

@[simp]
theorem add_one_minus (p : Prob) : p.val + p.one_minus.val = 1 := by
  simp

end Prob

/-- A `Mixable T` typeclass instance gives a compact way of talking about the action of probabilities
  for forming linear combinations in convex spaces. The notation `p [ x₁ ↔ x₂ ]` means to take a convex
  combination, equal to `x₁` if `p=1` and to `x₂` if `p=0`.

  Mixable is defined by an "underlying" data type `U` with addition and scalar multiplication, and a
  bijection between the `T` and a convex set of `U`. For instance, in `Mixable (Distribution (Fin n))`,
  `U` is `n`-element vectors (which form the probability simplex, degenerate in one dimension). For
  `QuantumInfo.Finite.MState` density matrices in quantum mechanics, which are PSD matrices of trace 1,
  `U` is the underlying matrix.

  Why not just stick with existing notions of `Convex`? `Convex` requires that the type already forms an
  `AddCommMonoid` and `Module ℝ`. But many types, such as `Distribution`, are not: there is no good notion of
  "multiplying a probability distribution by 0.3" to get another distribution. We can coerce the distribution
  into, say, a vector or a function, but then we are not doing arithmetic with distributions. Accordingly,
  the expression `0.3 * distA + 0.7 * distB` cannot represent a distribution on its own. -/
class Mixable (U : outParam (Type u)) (T : Type v) [AddCommMonoid U] [Module ℝ U] where
  /-- Getter for the underlying data -/
  to_U : T → U
  /-- Proof that this getter is injective -/
  to_U_inj : ∀ {T₁ T₂}, to_U T₁ = to_U T₂ → T₁ = T₂
  /-- Proof that this image is convex -/
  convex : Convex ℝ (Set.range to_U)
  /-- Function to get a T from a proof that U is in the set. -/
  mkT : {u : U} → (∃ t, to_U t = u) → { t : T // to_U t = u }

namespace Mixable

variable {T U : Type*} [AddCommMonoid U] [Module ℝ U]

@[reducible]
def mix_ab [inst : Mixable U T] {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (x₁ x₂ : T) : T :=
  inst.mkT <| inst.convex
    (x := to_U x₁) (exists_apply_eq_apply _ _)
    (y := to_U x₂) (exists_apply_eq_apply _ _)
    ha hb hab

/-- `Mixable.mix` represents the notion of "convex combination" on the type `T`, afforded by the `Mixable`
instance. It takes a `Prob`, that is, a `Real` between 0 and 1. For working directly with a Real, use `mix_ab`. -/
def mix [inst : Mixable U T] (p : Prob) (x₁ x₂ : T) : T :=
  inst.mix_ab p.zero_le_coe p.one_minus.zero_le_coe p.add_one_minus x₁ x₂

@[simp]
theorem to_U_of_mkT [inst : Mixable U T] (u : U) {h} : inst.to_U (mkT (u := u) h).1 = u :=
  (mkT (u := u) h).2

notation p "[" x₁:80 "↔" x₂ "]" => mix p x₁ x₂

notation p "[" x₁:80 "↔" x₂ ":" M "]" => mix (inst := M) p x₁ x₂

@[simp]
theorem mix_zero [inst : Mixable U T] (x₁ x₂ : T) : (0 : Prob) [ x₁ ↔ x₂ : inst] = x₂ := by
  apply inst.to_U_inj
  simp [mix, mix_ab]

/--When T is the whole space, and T is a suitable vector space over ℝ, we get a Mixable instance.-/
instance instUniv [AddCommMonoid T] [Module ℝ T] : Mixable T T where
  to_U := id
  to_U_inj := id
  convex := by
    convert convex_univ
    simp only [Set.range_id]
  mkT := fun _ ↦ ⟨_, rfl⟩

@[simp]
theorem mkT_instUniv [AddCommMonoid T] [Module ℝ T] {t : T} (h : ∃ t', to_U t' = t) : instUniv.mkT h = ⟨t, rfl⟩ :=
  rfl

@[simp]
theorem to_U_instUniv [AddCommMonoid T] [Module ℝ T] {t : T} : instUniv.to_U t = t :=
  rfl

variable {D : Type*} {T U : D → Type*} [∀i, AddCommMonoid (U i)] [∀ i, Module ℝ (U i)] [inst : ∀i, Mixable (U i) (T i)] in
/-- Mixable instance on Pi types. -/
instance instPi : Mixable ((i:D) → U i) ((i:D) → T i) where
  to_U x := fun d ↦ (inst d).to_U (x d)
  to_U_inj h := funext fun d ↦ (inst d).to_U_inj (congrFun h d)
  mkT := fun {u} h ↦ ⟨fun d ↦ (inst d).mkT (u := u d) (by
      obtain ⟨t, h⟩ := h
      use t d
      exact congrFun h d),
    by funext d; simp⟩
  convex := by
    simp [Convex, StarConvex]
    intro f₁ f₂ a b ha hb hab
    use fun d ↦ (inst d).mix_ab ha hb hab (f₁ d) (f₂ d)
    funext d
    simp only [to_U_of_mkT, Pi.add_apply, Pi.smul_apply]

@[simp]
theorem val_mkT_instPi (D : Type*) [inst : Mixable U T] {u : D → U} (h : ∃ t, to_U t = u) : (instPi.mkT h).val =
    fun d ↦ (inst.mkT (instPi.proof_3 h d)).val :=
  rfl

@[simp]
theorem to_U_instPi (D : Type*) [inst : Mixable U T] {t : D → T} : (instPi).to_U t = fun d ↦ inst.to_U (t d) :=
  rfl

/-- Mixable instances on subtypes (of other mixable types), assuming that they
 have the correct closure properties. -/
def instSubtype {T : Type*} {P : T → Prop} (inst : Mixable U T)
    (h : ∀{x y:T},
      ∀⦃a b : ℝ⦄, (ha : 0 ≤ a) → (hb : 0 ≤ b) → (hab : a + b = 1) →
      P x → P y → P (inst.mix_ab ha hb hab x y))
    : Mixable U { t // P t} where
  to_U x := inst.to_U (x.val)
  to_U_inj h := Subtype.ext (inst.to_U_inj h)
  mkT := fun {u} h ↦ ⟨by
    have ⟨t,hu⟩ := inst.mkT (u := u) $ h.casesOn fun t h ↦ ⟨t, h⟩
    use t
    have ⟨t₁,ht₁⟩ := h
    exact (inst.to_U_inj $ hu.trans ht₁.symm) ▸ t₁.prop,
    by simp only [to_U_of_mkT]⟩
  convex := by
    have hi := inst.convex
    simp [Convex, StarConvex] at hi ⊢
    intro x hx y hy a b ha hb hab
    let ⟨z, hz⟩ := hi x y ha hb hab
    refine ⟨z, ⟨?_, hz⟩⟩
    convert h ha hb hab hx hy
    apply inst.to_U_inj
    convert hz
    simp only [to_U_of_mkT]

end Mixable

namespace Prob

/-- Probabilities `Prob` themselves are convex. -/
instance instMixable : Mixable ℝ Prob where
  to_U := Prob.toReal
  to_U_inj := Prob.eq
  mkT := fun h ↦ ⟨⟨_, Exists.casesOn h fun t ht => ht ▸ t.prop⟩, rfl⟩
  convex := by
    simp [Convex, StarConvex]
    intro x hx0 hx1 y hy0 hy1 a b ha hb hab
    constructor
    · positivity
    · nlinarith

@[simp]
theorem to_U_mixable [AddCommMonoid T] [SMul ℝ T] (t : Prob) : instMixable.to_U t = t.val :=
  rfl

@[simp]
theorem mkT_mixable (u : ℝ) (h : ∃ t : Prob, Mixable.to_U t = u) : Mixable.mkT h =
    ⟨⟨u,Exists.casesOn h fun t ht ↦ ht ▸ t.2⟩, rfl⟩ :=
  rfl

/-- `Prob.mix` is an alias of `Mixable.mix` so it can be accessed from a probability with
dot notation, e.g. `p.mix x y`. -/
abbrev mix [AddCommMonoid U] [Module ℝ U] [inst : Mixable U T] (p : Prob) (x₁ x₂ : T) := inst.mix p x₁ x₂

end Prob
