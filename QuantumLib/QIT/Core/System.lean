/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Init
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

universe u v w

/-- Recursive finite tensor-power label type. -/
def TensorPower (a : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => (a × TensorPower a n)

instance tensorPowerFintype {a : Type u} [Fintype a] (n : ℕ) :
    Fintype (TensorPower a n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (a × TensorPower a n))

instance tensorPowerDecidableEq {a : Type u} [DecidableEq a] (n : ℕ) :
    DecidableEq (TensorPower a n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ n ih => exact inferInstanceAs (DecidableEq (a × TensorPower a n))

/-- Split an IID tensor power of bipartite labels into the two IID tensor powers.

The recursive convention for `TensorPower` stores
`(A × B)^(n+1)` as `(A × B) × (A × B)^n`. This equivalence is the finite-system
bookkeeping bridge used to read that system as `A^(n+1) × B^(n+1)`.
-/
def tensorPowerProdEquiv (a : Type u) (b : Type v) :
    (n : ℕ) → TensorPower (a × b) n ≃
      (TensorPower a n × TensorPower b n)
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
              rfl
        right_inv := by
          intro y
          cases y with
          | mk xa xb =>
              cases xa
              cases xb
              simp [ih] }

/-- Regroup the tensor power of a left-associated tripartite system as
`(A^n × B^n) × C^n`. -/
def tensorPowerProdProdEquiv (a : Type u) (b : Type v) (c : Type w) (n : ℕ) :
    TensorPower ((a × b) × c) n ≃
      ((TensorPower a n × TensorPower b n) × TensorPower c n) :=
  (tensorPowerProdEquiv (a × b) c n).trans
    (Equiv.prodCongr (tensorPowerProdEquiv a b n) (Equiv.refl (TensorPower c n)))

/-- Swap the last two factors of a left-associated triple of systems,
reading `(A ⊗ B) ⊗ C` as `(A ⊗ C) ⊗ B`. -/
def prodABCToACBEquiv (a : Type u) (b : Type v) (c : Type w) :
    ((a × b) × c) ≃ ((a × c) × b) where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv x := by rcases x with ⟨⟨_, _⟩, _⟩; rfl
  right_inv x := by rcases x with ⟨⟨_, _⟩, _⟩; rfl

/-- The `(A ⊗ B) ⊗ C` to `(A ⊗ C) ⊗ B` relabelling is inverse to itself with
the last two systems exchanged. -/
theorem prodABCToACBEquiv_symm (a : Type u) (b : Type v) (c : Type w) :
    (prodABCToACBEquiv a b c).symm = prodABCToACBEquiv a c b :=
  rfl

/-- Rotate a right-associated triple of systems, reading `A ⊗ (B ⊗ C)` as
`B ⊗ (C ⊗ A)`. -/
def prodABCToBCAEquiv (a : Type u) (b : Type v) (c : Type w) :
    (a × (b × c)) ≃ (b × (c × a)) where
  toFun x := (x.2.1, (x.2.2, x.1))
  invFun x := (x.2.2, (x.1, x.2.1))
  left_inv x := by rcases x with ⟨_, _, _⟩; rfl
  right_inv x := by rcases x with ⟨_, _, _⟩; rfl

@[simp]
theorem prodABCToBCAEquiv_apply (a : Type u) (b : Type v) (c : Type w)
    (x : a × (b × c)) :
    prodABCToBCAEquiv a b c x = (x.2.1, (x.2.2, x.1)) :=
  rfl

@[simp]
theorem prodABCToBCAEquiv_symm_apply (a : Type u) (b : Type v) (c : Type w)
    (x : b × (c × a)) :
    (prodABCToBCAEquiv a b c).symm x = (x.2.2, (x.1, x.2.1)) :=
  rfl

/-- Reassociate a right-associated triple of systems as a left-associated one
with the first two exchanged, reading `A ⊗ (B ⊗ C)` as `(B ⊗ A) ⊗ C`. -/
def prodABCToBACEquiv (a : Type u) (b : Type v) (c : Type w) :
    (a × (b × c)) ≃ ((b × a) × c) where
  toFun x := ((x.2.1, x.1), x.2.2)
  invFun x := (x.1.2, (x.1.1, x.2))
  left_inv x := by rcases x with ⟨_, _, _⟩; rfl
  right_inv x := by rcases x with ⟨⟨_, _⟩, _⟩; rfl

/-- Interleave two left-associated tripartite systems componentwise, reading
`(A₁ ⊗ B₁ ⊗ C₁) ⊗ (A₂ ⊗ B₂ ⊗ C₂)` as `((A₁ ⊗ A₂) ⊗ (B₁ ⊗ B₂)) ⊗ (C₁ ⊗ C₂)`. -/
def prodTripartiteZipEquiv {a1 b1 c1 a2 b2 c2 : Type*} :
    (((a1 × b1) × c1) × ((a2 × b2) × c2)) ≃
      (((a1 × a2) × (b1 × b2)) × (c1 × c2)) where
  toFun x := (((x.1.1.1, x.2.1.1), (x.1.1.2, x.2.1.2)), (x.1.2, x.2.2))
  invFun x := (((x.1.1.1, x.1.2.1), x.2.1), ((x.1.1.2, x.1.2.2), x.2.2))
  left_inv x := by rcases x with ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩; rfl
  right_inv x := by rcases x with ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩; rfl

end QIT
