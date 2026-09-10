/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Core.State

/-!
# Product states over a finite sequence

The tensor product `⊗_i ρ_i` of a sequence of density states, as a
`MState (TensorPower a n)`. The Kronecker-fold construction mirrors
`MState.tensorPower`, generalized from a single repeated state to a
position-dependent sequence. Used by conditional typicality (HSW).
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

namespace QIT

universe u
noncomputable section
variable {a : Type u} [Fintype a] [DecidableEq a]

/-- The product state `⊗_i ρ_i` over a finite sequence `states : Fin n → MState a`.

The tensor product is left-associated across the recursive `TensorPower a n`
label type, matching `MState.tensorPower`: the head index `0 : Fin (n + 1)`
pairs with the tail product over `Fin n`. -/
def productState : {n : ℕ} → (states : Fin n → MState a) → MState (TensorPower a n)
  | 0, _ => MState.unit
  | _ + 1, states => (states 0).prod (productState (states ·.succ))

/-- The product state over the empty sequence is the unit-system state. -/
theorem productState_zero (states : Fin 0 → MState a) :
    productState states = MState.unit := rfl

/-- The product state over a non-empty sequence unfolds as the head state
paired with the tail product. -/
theorem productState_succ (n : ℕ) (states : Fin (n + 1) → MState a) :
    productState states = (states 0).prod (productState (states ·.succ)) := rfl

@[simp]
theorem productState_zero_matrix (states : Fin 0 → MState a) :
    (productState states).m = (1 : CMatrix (TensorPower a 0)) :=
  MState.unit_matrix

@[simp]
theorem productState_succ_matrix (n : ℕ) (states : Fin (n + 1) → MState a) :
    (productState states).m =
      (states 0).m ⊗ₖ (productState (states ·.succ)).m :=
  MState.prod_m _ _

end
end QIT
