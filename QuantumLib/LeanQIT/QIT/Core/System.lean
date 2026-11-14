/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Init
public import Mathlib.Data.Fintype.Prod

/-!
# Finite systems

Finite label types used by the local matrix model. `TensorPower a n` is the
right-associated type-level tensor power used for IID constructions
[Tomamichel2015FiniteResources, prelim.tex:38-43;
Wilde2011Qst, qit-notes.tex:1888-1920].
-/

@[expose] public section

namespace QIT

universe u v

/-- Recursive finite tensor-power label type. -/
def TensorPower (a : Type u) : Nat -> Type u
  | 0 => PUnit
  | n + 1 => Prod a (TensorPower a n)

instance tensorPowerFintype {a : Type u} [Fintype a] (n : Nat) :
    Fintype (TensorPower a n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (Prod a (TensorPower a n)))

instance tensorPowerDecidableEq {a : Type u} [DecidableEq a] (n : Nat) :
    DecidableEq (TensorPower a n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ n ih => exact inferInstanceAs (DecidableEq (Prod a (TensorPower a n)))

/-- Split an IID tensor power of bipartite labels into the two IID tensor powers.

The recursive convention for `TensorPower` stores
`(A × B)^(n+1)` as `(A × B) × (A × B)^n`. This equivalence is the finite-system
bookkeeping bridge used to read that system as `A^(n+1) × B^(n+1)`.
-/
def tensorPowerProdEquiv (a : Type u) (b : Type v) :
    (n : Nat) -> TensorPower (Prod a b) n ≃
      Prod (TensorPower a n) (TensorPower b n)
  | 0 =>
      { toFun := fun _ => (PUnit.unit, PUnit.unit)
        invFun := fun _ => PUnit.unit
        left_inv := by
          intro x
          cases x
          rfl
        right_inv := by
          intro x
          cases x with
          | mk xa xb =>
              cases xa
              cases xb
              rfl }
  | n + 1 =>
      let ih := tensorPowerProdEquiv a b n
      { toFun := fun x => ((x.1.1, (ih x.2).1), (x.1.2, (ih x.2).2))
        invFun := fun y => ((y.1.1, y.2.1), ih.symm (y.1.2, y.2.2))
        left_inv := by
          intro x
          cases x with
          | mk ab rest =>
              cases ab
              simp [ih]
        right_inv := by
          intro y
          cases y with
          | mk xa xb =>
              cases xa
              cases xb
              simp [ih] }

end QIT
