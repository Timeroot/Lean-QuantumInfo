import Mathlib

noncomputable section
open NNReal
open Classical

/-- Prob is a real number in the interval [0,1]. Similar to NNReal in many definitions, but this
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

/-- Coercion `Prob → ℝ≥0`. -/
@[coe] def toNNReal : Prob → ℝ≥0 :=
  fun p ↦ ⟨p.val, zero_le_coe⟩

@[simp]
theorem toNNReal_mk : toNNReal { val := x, property := hx} = { val := x, property := hx.1 } :=
  rfl

instance : Coe Prob ℝ≥0 := ⟨toNNReal⟩

instance canLiftNN : CanLift ℝ≥0 Prob toNNReal fun r => r ≤ 1 :=
  ⟨fun x hx ↦ ⟨⟨x, ⟨x.2, hx⟩⟩, rfl⟩⟩

protected theorem eq_iff_nnreal {n m : Prob} : (n : ℝ≥0) = (m : ℝ≥0) ↔ n = m := by
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
    ⟨by simpa using p.2.2, by simpa using p.2.1⟩⟩

@[simp]
theorem val_one_minus (p : Prob) : p.one_minus.val = 1-p.val :=
  rfl

@[simp, norm_cast]
theorem coe_one_minus (p : Prob) : (p.one_minus : ℝ) = 1-(p : ℝ) :=
  rfl

def mixP (p x y : Prob) : Prob :=
  ⟨p * x + p.one_minus * y,
    ⟨by
      have := x.2.1
      have := y.2.1
      have := p.2.1
      have := p.one_minus.2.1
      positivity,
    sorry
    ⟩⟩

def mix (p : Prob) [HSMul ℝ α α] [CommSemiring α] (x y : α) : α :=
  p.val • x + p.one_minus.val • y

end Prob
