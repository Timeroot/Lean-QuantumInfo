/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.State

/-!
# Product states over a finite sequence

The tensor product `⊗_i ρ_i` of a sequence of density states, as a
`State (TensorPower a n)`. The Kronecker-fold construction mirrors
`State.tensorPower`, generalized from a single repeated state to a
position-dependent sequence. Used by conditional typicality (HSW).
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u
noncomputable section
variable {a : Type u} [Fintype a] [DecidableEq a]

/-- The product state `⊗_i ρ_i` over a finite sequence `states : Fin n → State a`.

The tensor product is left-associated across the recursive `TensorPower a n`
label type, matching `State.tensorPower`: the head index `0 : Fin (n + 1)`
pairs with the tail product over `Fin n`. -/
def productState : {n : ℕ} → (states : Fin n → State a) → State (TensorPower a n)
  | 0, _ => State.unit
  | _ + 1, states => (states 0).prod (productState (states ·.succ))

/-- The product state over the empty sequence is the unit-system state. -/
theorem productState_zero (states : Fin 0 → State a) :
    productState states = State.unit := rfl

/-- The product state over a non-empty sequence unfolds as the head state
paired with the tail product. -/
theorem productState_succ (n : ℕ) (states : Fin (n + 1) → State a) :
    productState states = (states 0).prod (productState (states ·.succ)) := rfl

@[simp]
theorem productState_matrix :
    {n : ℕ} → (states : Fin n → State a) →
      (productState states).matrix =
        match n with
        | 0 => State.unit.matrix
        | _ + 1 => Matrix.kronecker (states 0).matrix
          (productState (states ·.succ)).matrix
  | 0, _ => rfl
  | _ + 1, _ => rfl

end
end QIT
