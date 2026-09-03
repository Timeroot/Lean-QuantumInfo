/-
Copyright (c) 2026 The Lean-QEC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mattias Ehatamm
-/

import QuantumInfo.States.Pure.Braket
import QuantumLib.QECC.BitVec.States.Phase

/-!
# Kets up to a global phase

Multiplication of a ket by a global phase.
-/

variable {k : Type*} [Fintype k]

/-- A form of `Ket.normalized'` stated so that it can be rewritten with. -/
lemma Ket.normalized'' (ψ : Ket k) : ∑ x, ‖ψ x‖^2 = 1 := ψ.normalized'

noncomputable section

/-- Multiply a ket by a global phase. -/
def Ket.phase_mul (ψ : Ket k) (z : phase) : Ket k where
  vec := z.1 • ψ.vec
  normalized' := by
    simp [z.2, ψ.2]

lemma Ket.mul_phase_id {k : Type*} [Fintype k] {ψ : Ket k} : ψ.phase_mul phase_id = ψ := by
  simp [Ket.phase_mul]
