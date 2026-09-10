/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Core.System
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Real.Basic

/-!
# Tensor-power label equivalence

The canonical type equivalence between the right-associated recursive tensor
power `TensorPower a n` and the function type `Fin n → a`, obtained by iterating
the head/tail (`Fin.cons`) decomposition of a finite vector.
-/

@[expose] public section

namespace QIT

universe u v

noncomputable section

variable {a : Type u} [DecidableEq a]

/-- Drop the terminal unit register in a one-fold tensor power. -/
def tensorPowerOneEquiv (q : Type*) : TensorPower q 1 ≃ q where
  toFun x := x.1
  invFun y := (y, PUnit.unit)
  left_inv x := by
    rcases x with ⟨q, u⟩
    cases u
    rfl
  right_inv y := rfl

/-- `TensorPower a n` is canonically equivalent to `Fin n → a` (right-associated
Prod unfolds to a function on `Fin n` via `Fin.cons` head/tail decomposition). -/
def tensorPowerEquiv : (n : ℕ) → TensorPower a n ≃ (Fin n → a)
  | 0 =>
    { toFun := fun _ i => i.elim0,
      invFun := fun _ => ⟨⟩,
      left_inv := fun _ => rfl,
      right_inv := fun _ => by ext i; exact i.elim0 }
  | Nat.succ n =>
    let ih := tensorPowerEquiv n
    ((Equiv.refl a).prodCongr ih).trans
      { toFun := fun (head, tail) => Fin.cons head tail,
        invFun := fun f => (f 0, Fin.tail f),
        left_inv := by
          rintro ⟨head, tail⟩
          ext i <;> simp [Fin.cons_zero, Fin.tail_cons]
        right_inv := by
          intro f
          (ext i; simp) }

omit [DecidableEq a] in
/-- The recursive tensor-power type has the expected cardinality `|a|^n`. -/
theorem tensorPower_card [Fintype a] (n : ℕ) :
    Fintype.card (TensorPower a n) = Fintype.card a ^ n := by
  induction n with
  | zero =>
      rw [pow_zero]
      exact Fintype.card_eq_one_iff.mpr ⟨PUnit.unit, fun _ => rfl⟩
  | succ n ih =>
      calc
        Fintype.card (TensorPower a (n + 1)) =
            Fintype.card (a × TensorPower a n) := rfl
        _ = Fintype.card a * Fintype.card (TensorPower a n) := Fintype.card_prod a (TensorPower a n)
        _ = Fintype.card a * Fintype.card a ^ n := by rw [ih]
        _ = Fintype.card a ^ (n + 1) := by rw [pow_succ']

omit [DecidableEq a] in
/-- Real-valued form of `tensorPower_card`. -/
theorem tensorPower_card_real [Fintype a] (n : ℕ) :
    (Fintype.card (TensorPower a n) : ℝ) = (Fintype.card a : ℝ) ^ n := by
  exact_mod_cast tensorPower_card (a := a) n

omit [DecidableEq a] in
/-- First-coordinate projection of `tensorPowerProdEquiv`, read at a tensor
position. -/
theorem tensorPowerProdEquiv_fst_apply {b : Type v}
    (n : ℕ) (z : TensorPower (a × b) n) (i : Fin n) :
    tensorPowerEquiv (a := a) n ((tensorPowerProdEquiv a b n z).1) i =
      (tensorPowerEquiv (a := a × b) n z i).1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases z with
      | mk _ tail =>
          cases i using Fin.cases with
          | zero => rfl
          | succ i =>
              simp [tensorPowerProdEquiv, tensorPowerEquiv]
              exact ih tail i

omit [DecidableEq a] in
/-- Second-coordinate projection of `tensorPowerProdEquiv`, read at a tensor
position. -/
theorem tensorPowerProdEquiv_snd_apply {b : Type v}
    (n : ℕ) (z : TensorPower (a × b) n) (i : Fin n) :
    tensorPowerEquiv (a := b) n ((tensorPowerProdEquiv a b n z).2) i =
      (tensorPowerEquiv (a := a × b) n z i).2 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases z with
      | mk _ tail =>
          cases i using Fin.cases with
          | zero => rfl
          | succ i =>
              simp [tensorPowerProdEquiv, tensorPowerEquiv]
              exact ih tail i

omit [DecidableEq a] in
/-- The tensor power of a nonempty type is nonempty. -/
theorem tensorPower_nonempty_of_nonempty {α : Type u} [Nonempty α] :
    (n : ℕ) → Nonempty (TensorPower α n)
  | 0 => ⟨PUnit.unit⟩
  | n + 1 =>
      haveI : Nonempty (TensorPower α n) := tensorPower_nonempty_of_nonempty n
      inferInstanceAs (Nonempty (α × TensorPower α n))

end
