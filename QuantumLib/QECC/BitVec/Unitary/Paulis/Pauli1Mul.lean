/-
Copyright (c) 2026 The Lean-QEC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mattias Ehatamm, Runzhou Tao
-/

import QuantumLib.QECC.BitVec.Unitary.Basic
import QuantumLib.QECC.BitVec.States.Phase
import QuantumLib.QECC.BitVec.Unitary.Paulis.Pauli1
import QuantumLib.QECC.BitVec.Unitary.Paulis.PauliFolding

/-!
# The single-qubit Pauli multiplication table

`mul_Pauli1 P Q` computes the product of two single-qubit Paulis as a pair consisting of a phase
in `pgroup_phases` and a Pauli, and `mul_Pauli1_correct` verifies it against matrix
multiplication.
-/

noncomputable section

@[simp]
def phase_i : phase where
  z := Complex.I
  z_norm := by simp

@[simp]
def phase_ni : phase where
  z := -Complex.I
  z_norm := by simp

def pgphase_i : pgroup_phases := ⟨phase_i, by simp [pgroup_phases]⟩

def pgphase_ni : pgroup_phases := ⟨phase_ni, by simp [pgroup_phases]⟩

/-- The Pauli multiplication table, spelled out. -/
def mul_Pauli1 (P : Pauli) (Q : Pauli) : pgroup_phases × Pauli :=
  if P = Pauli_I then
    (1, Q)
  else if P = Pauli_X then
    if Q = Pauli_I then
      (1, Pauli_X)
    else if Q = Pauli_X then
      (1, Pauli_I)
    else if Q = Pauli_Y then
      (pgphase_i, Pauli_Z)
    else -- Q = Z
      (pgphase_ni, Pauli_Y)
  else if P = Pauli_Y then
    if Q = Pauli_I then
      (1, Pauli_Y)
    else if Q = Pauli_X then
      (pgphase_ni, Pauli_Z)
    else if Q = Pauli_Y then
      (1, Pauli_I)
    else -- Q = Z
      (pgphase_i, Pauli_X)
  else -- P = Z
    if Q = Pauli_I then
      (1, Pauli_Z)
    else if Q = Pauli_X then
      (pgphase_i, Pauli_Y)
    else if Q = Pauli_Y then
      (pgphase_ni, Pauli_X)
    else -- Q = Z
      (1, Pauli_I)

def getmat (P : Pauli) : 𝐔ₙ[1] := P

section Products

open Qubit

lemma pX_sq : pX * pX = 1 := by
  apply Subtype.ext
  simp only [pX, unitary_fin_equiv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qubit.X, beq, BitVec.equivFin, Matrix.mul_apply]

lemma pY_sq : pY * pY = 1 := by
  apply Subtype.ext
  simp only [pY, unitary_fin_equiv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qubit.Y, beq, BitVec.equivFin, Matrix.mul_apply]

lemma pZ_sq : pZ * pZ = 1 := by
  apply Subtype.ext
  simp only [pZ, unitary_fin_equiv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qubit.Z, beq, BitVec.equivFin, Matrix.mul_apply]

lemma pX_mul_pY : pX * pY = U_phase pZ phase_i := by
  unfold pX pY pZ U_phase unitary_fin_equiv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [X, Y, Z, beq, BitVec.equivFin, Matrix.mul_apply]

lemma pY_mul_pZ : pY * pZ = U_phase pX phase_i := by
  unfold pX pY pZ U_phase unitary_fin_equiv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [X, Y, Z, beq, BitVec.equivFin, Matrix.mul_apply]

lemma pZ_mul_pX : pZ * pX = U_phase pY phase_i := by
  unfold pX pY pZ U_phase unitary_fin_equiv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [X, Y, Z, beq, BitVec.equivFin, Matrix.mul_apply]

lemma pY_mul_pX : pY * pX = U_phase pZ phase_ni := by
  unfold pX pY pZ U_phase unitary_fin_equiv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [X, Y, Z, beq, BitVec.equivFin, Matrix.mul_apply]

lemma pZ_mul_pY : pZ * pY = U_phase pX phase_ni := by
  unfold pX pY pZ U_phase unitary_fin_equiv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [X, Y, Z, beq, BitVec.equivFin, Matrix.mul_apply]

lemma pX_mul_pZ : pX * pZ = U_phase pY phase_ni := by
  unfold pX pY pZ U_phase unitary_fin_equiv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [X, Y, Z, beq, BitVec.equivFin, Matrix.mul_apply]

end Products

@[simp] lemma Pauli_X_val : (Pauli_X : 𝐔ₙ[1]) = pX := rfl

@[simp] lemma Pauli_Y_val : (Pauli_Y : 𝐔ₙ[1]) = pY := rfl

@[simp] lemma Pauli_Z_val : (Pauli_Z : 𝐔ₙ[1]) = pZ := rfl

@[simp] lemma Pauli_I_val : (Pauli_I : 𝐔ₙ[1]) = 1 := rfl

@[simp] lemma pgphase_1_val : ((1 : pgroup_phases) : phase) = phase_id := rfl

@[simp] lemma pgphase_i_val : (pgphase_i : phase) = phase_i := rfl

@[simp] lemma pgphase_ni_val : (pgphase_ni : phase) = phase_ni := rfl

lemma mul_Pauli1_correct (P Q : Pauli) :
    let PQ := mul_Pauli1 P Q
    P.val * Q.val = U_phase PQ.2 PQ.1 := by
  intro PQ
  show P.val * Q.val = U_phase (mul_Pauli1 P Q).2 (mul_Pauli1 P Q).1
  clear PQ
  rcases Pauli_cases P with rfl | rfl | rfl | rfl <;>
    rcases Pauli_cases Q with rfl | rfl | rfl | rfl <;>
      simp only [mul_Pauli1, Pauli_X_val, Pauli_Y_val, Pauli_Z_val, Pauli_I_val, pgphase_1_val,
        pgphase_i_val, pgphase_ni_val, pgXnepgI, pgYnepgI, pgZnepgI, pgXnepgY, pgYnepgX,
        pgZnepgX, pgZnepgY, pgInepgX, pgInepgY, if_true, if_false, U_phase_id, one_mul,
        mul_one] <;>
      first
        | rfl
        | exact pX_sq
        | exact pY_sq
        | exact pZ_sq
        | exact pX_mul_pY
        | exact pX_mul_pZ
        | exact pY_mul_pX
        | exact pY_mul_pZ
        | exact pZ_mul_pX
        | exact pZ_mul_pY
