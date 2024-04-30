import Mathlib.Data.Real.NNReal
import Mathlib.Analysis.Convex.Mul

/- This defines a type `Prob` which is a real number in the interval O to 1. This then comes with
additional statements such as its application to convex sets, and it makes useful type alias for
functions that only make sense on probabilities. -/

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
    ⟨mul_nonneg x.2.1 y.2.1, mul_le_one x.2.2 y.2.1 y.2.2⟩⟩⟩

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

instance instOrderedCommMonoid : OrderedCommMonoid Prob where
  mul_le_mul_left := by
    intros a b h c
    rw [← Subtype.coe_le_coe]
    exact mul_le_mul_of_nonneg_left h c.2.1

instance instDistribLattice : DistribLattice Prob where
  le_sup_left := by
    intros; rw [← Subtype.coe_le_coe, val_sup]; exact le_sup_left
  le_sup_right := by
    intros; rw [← Subtype.coe_le_coe, val_sup]; exact le_sup_right
  inf_le_left := by
    intros; rw [← Subtype.coe_le_coe, val_inf]; exact inf_le_left
  inf_le_right := by
    intros; rw [← Subtype.coe_le_coe, val_inf]; exact inf_le_right
  sup_le := by
    intros; rw [← Subtype.coe_le_coe, val_sup, sup_le_iff]; exact ⟨‹_›, ‹_›⟩
  le_inf := by
    intros; rw [← Subtype.coe_le_coe, val_inf, le_inf_iff]; exact ⟨‹_›, ‹_›⟩
  le_sup_inf := by
    intros
    simp only [← Subtype.coe_le_coe, val_inf, val_sup, le_sup_iff, inf_le_iff, sup_le_iff, le_refl,
      true_and, le_inf_iff, and_true, or_iff_not_imp_left]
    intro h
    push_neg at h
    constructor <;> {intro; linarith}

instance instInhabited : Inhabited Prob where
  default := 0

instance instDenselyOrdered : DenselyOrdered Prob :=
  show DenselyOrdered (Set.Icc 0 1) from Set.instDenselyOrdered

instance instOrderBot : OrderBot Prob where
  bot := 0
  bot_le a := a.2.1

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

protected theorem eq_iff {n m : Prob} : (n : ℝ) = (m : ℝ) ↔ n = m :=
  Subtype.ext_iff.symm

theorem ne_iff {x y : Prob} : (x : ℝ) ≠ (y : ℝ) ↔ x ≠ y :=
  not_congr <| Prob.eq_iff

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
  simp
  constructor
  · intro h
    sorry
  · intro h
    subst h
    rfl

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
  `MState` density matrices in quantum mechanics, which are PSD matrices of trace 1, `U` is the
  underlying matrix. -/
class Mixable (T : Type*) where
  /-- The underlying data type-/
  U : Type*
  /-- U needs additive and smul operations. We try to find these automatically. -/
  instU1 : AddCommMonoid U := by infer_instance
  instU2 : SMul ℝ U := by infer_instance
  /-- Getter for the underlying data -/
  to_U : T → U
  /-- Proof that this getter is injective -/
  to_U_inj : ∀ {T₁ T₂}, to_U T₁ = to_U T₂ → T₁ = T₂
  /-- Proof that this image is convex -/
  convex : Convex ℝ (Set.range to_U)
  /-- Function to get a T from a proof that U is in the set. `Mixable.default_mkT` always
  works as a default (noncomputable) value, but typically a `T.mk` method will make
  more sense. -/
  mkT : {u : U} → (∃ t, to_U t = u) → { t : T // to_U t = u }

namespace Mixable

variable {T : Type*}

@[reducible]
def mix_ab [inst : Mixable T] {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (x₁ x₂ : T) :=
  let _ := inst.instU1
  let _ := inst.instU2
  inst.mkT <| inst.convex
    (x := to_U x₁) (exists_apply_eq_apply _ _)
    (y := to_U x₂) (exists_apply_eq_apply _ _)
    ha hb hab

def mix [Mixable T] (p : Prob) (x₁ x₂ : T) :=
  mix_ab p.zero_le_coe p.one_minus.zero_le_coe p.add_one_minus x₁ x₂

@[simp]
theorem to_U_of_mkT [Mixable T] (u : U T) {h} : to_U (mkT (u := u) h).1 = u :=
  (mkT (u := u) h).2

notation p "[" x₁ "↔" x₂ "]" => mix p x₁ x₂

/--When T is the whole space U, and T is a suitable vector space over ℝ, we get a Mixable instance.-/
instance instUniv [AddCommMonoid T] [SMul ℝ T] : Mixable T where
  U := T
  to_U := id
  to_U_inj := id
  convex := by
    convert convex_univ
    simp only [Set.range_id]
  mkT := fun _ ↦ ⟨_, rfl⟩

@[simp]
theorem mkT_instUniv [AddCommMonoid T] [SMul ℝ T] (h) : @Mixable.mkT T instUniv t h = ⟨t, rfl⟩ :=
  rfl

@[simp]
theorem to_U_instUniv [AddCommMonoid T] [SMul ℝ T] : @Mixable.to_U T instUniv t = t :=
  rfl

/-- Mixable instance on Pi types. Could be dependent but this is not. -/
instance instPi (D : Type*) [inst : Mixable T] : Mixable (D → T) where
  U := D → inst.U
  instU1 := let k := inst.instU1; Pi.addCommMonoid
  instU2 := let k := inst.instU2; Pi.instSMul
  to_U x := fun d ↦ inst.to_U (x d)
  to_U_inj h := funext fun d ↦ inst.to_U_inj (congrFun h d)
  mkT := fun {t} h ↦ ⟨fun d ↦ inst.mkT (u := t d) (by
      obtain ⟨t₂, h⟩ := h
      use t₂ d
      exact congrFun h d),
    by funext d; simp⟩
  convex := by
    simp [Convex, StarConvex]
    intro f₁ f₂ a b ha hb hab
    use fun d ↦ mix_ab ha hb hab (f₁ d) (f₂ d)
    funext d
    simp only [to_U_of_mkT, Pi.add_apply, Pi.smul_apply]

end Mixable

namespace Prob

instance mixable : Mixable Prob where
  U := ℝ
  to_U := Prob.toReal
  to_U_inj := Prob.eq
  mkT := fun h ↦ ⟨⟨_, Exists.casesOn h fun t ht => ht ▸ t.prop⟩, rfl⟩
  convex := sorry

@[simp]
theorem U_mixable [AddCommMonoid T] [SMul ℝ T] : @Mixable.U Prob mixable = ℝ :=
  rfl

@[simp]
theorem to_U_mixable [AddCommMonoid T] [SMul ℝ T] : @Mixable.to_U Prob mixable t = t :=
  rfl

@[simp]
theorem mkT_mixable : @Mixable.mkT Prob mixable t h = ⟨⟨t, sorry⟩, rfl⟩ :=
  rfl

/-- Alias of `Mixable.mix` so it can be accessed from a probability. -/
abbrev mix [Mixable T] (p : Prob) (x₁ x₂ : T) := Mixable.mix p x₁ x₂

end Prob
