/-
Copyright (c) 2026 The Lean-QEC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eashan Hatti
-/

import QuantumLib.QECC.BitVec.Unitary.Paulis.PauliFolding

/-!
# Traces of Pauli operators

The trace of a tensor product of single-qubit Paulis vanishes unless every factor is the
identity, in which case it is the phase times `2 ^ n`.
-/

open Matrix

noncomputable section

variable {n : ℕ}

lemma trace_pauli_single (p : Pauli) :
    Matrix.trace ((p : 𝐔ₙ[1]).val) = if p = Pauli_I then (2 : ℂ) else 0 := by
  rcases Pauli_cases p with rfl | rfl | rfl | rfl <;>
    [rw [if_neg pgXnepgI]; rw [if_neg pgYnepgI]; rw [if_neg pgZnepgI]; rw [if_pos rfl]] <;>
    simp +decide [Pauli_X, Pauli_Y, Pauli_Z, Pauli_I, pX, pY, pZ, unitary_fin_equiv, Qubit.X,
      Qubit.Y, Qubit.Z, Matrix.trace, beq, BitVec.equivFin, Fintype.card_bitvec]

lemma trace_unitary_nkron {n₁ n₂ : ℕ} (a : 𝐔ₙ[n₁]) (b : 𝐔ₙ[n₂]) :
    Matrix.trace (a ⊗ₙ b).val = Matrix.trace a.val * Matrix.trace b.val := by
  rw [unitary_nkron_valE, ← Matrix.trace_kronecker a.val b.val]
  exact Equiv.sum_comp bits_cat.symm fun p => (a.val.kronecker b.val) p p

lemma trace_unitary_n_nkron (m : Fin n → 𝐔ₙ[1]) :
    Matrix.trace (unitary_n_nkron m).val = ∏ i, Matrix.trace (m i).val := by
  induction n with
  | zero => simp [unitary_n_nkron, Fintype.card_bitvec]
  | succ n ih =>
    rw [unitary_n_nkron, trace_unitary_nkron, ih, Fin.prod_univ_succ, mul_comm]
    rfl

lemma prod_if_pauli_I (m : Fin n → Pauli) :
    (∏ i, (if m i = Pauli_I then (2 : ℂ) else 0))
      = if (∀ i, m i = Pauli_I) then (2 : ℂ) ^ n else 0 := by
  split_ifs <;> simp_all +decide [Finset.prod_ite]

lemma trace_fold_prod (z : pgroup_phases) (m : Fin n → Pauli) :
    Matrix.trace (fold (z, m)).val
      = z.1.z * ∏ i, (if m i = Pauli_I then (2 : ℂ) else 0) := by
  show Matrix.trace (fold_aux z m).val = _
  rw [fold_aux, U_phase, Matrix.trace_smul, smul_eq_mul, trace_unitary_n_nkron]
  exact congrArg _ (Finset.prod_congr rfl fun i _ => trace_pauli_single (m i))

lemma trace_fold_eq (z : pgroup_phases) (m : Fin n → Pauli) :
    Matrix.trace (fold (z, m)).val
      = if (∀ i, m i = Pauli_I) then z.1.z * (2 : ℂ) ^ n else 0 := by
  rw [trace_fold_prod, prod_if_pauli_I]
  split <;> simp

end
