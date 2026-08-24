/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.PiKron
import QuantumLib.QECC.StabilizerGroup

/-!
# Discretisation of errors into Pauli operators

An arbitrary operator acting on at most `t` qubits is a linear combination of Pauli operators of
weight at most `t`. This is the *discretisation of errors* in its Pauli form: it is what turns the
Knill–Laflamme conditions for the finitely many weight-`≤ t` Paulis into correction of arbitrary
errors on `t` qubits.

The two ingredients are that the four single-qubit Paulis span the `2 × 2` matrices, and that an
`n`-qubit Pauli is the Kronecker product of its single-qubit factors, so that the multilinearity of
`piKron` expands an arbitrary error site by site.

## Main results

* `QuantumLib.pauliOp_eq_piKron` — a Pauli operator is a Kronecker product of single-qubit Paulis;
* `QuantumLib.exists_pauli1_expansion` — the four single-qubit Paulis span;
* `QuantumLib.QECC.errMat_mem_span_pauli` — an arbitrary error supported on `S` lies in the span of
  the Pauli operators of weight at most `S.card`.
-/

open scoped Matrix

namespace QuantumLib

/-! ### Single-qubit Paulis -/

/-- The single-qubit Pauli operator `X ^ a Z ^ b`. -/
def pauli1 (a b : ZMod 2) : Matrix (ZMod 2) (ZMod 2) ℂ :=
  Matrix.of fun u v => if u = v + a then (-1 : ℂ) ^ (b * v).val else 0

theorem pauli1_apply (a b u v : ZMod 2) :
    pauli1 a b u v = if u = v + a then (-1 : ℂ) ^ (b * v).val else 0 := rfl

@[simp]
theorem pauli1_zero_zero : pauli1 0 0 = 1 := by
  ext u v
  simp [pauli1, Matrix.one_apply]

/-- **A Pauli operator is a Kronecker product of single-qubit Paulis.** -/
theorem pauliOp_eq_piKron {n : ℕ} (p : PauliSpace n) :
    pauliOp p = piKron fun q => pauli1 (p.1 q) (p.2 q) := by
  ext u v
  rw [piKron_apply]
  simp only [pauliOp, Matrix.of_apply, pauli1_apply]
  by_cases h : u = v + p.1
  · rw [if_pos h]
    refine Finset.prod_congr rfl fun q _ => ?_
    have hq : u q = v q + p.1 q := by
      rw [h]
      rfl
    rw [if_pos hq]
  · rw [if_neg h]
    obtain ⟨q, hq⟩ := Function.ne_iff.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)).symm

/-- A sum over `ZMod 2` is a sum of two terms. -/
theorem sum_zmod_two {α : Type*} [AddCommMonoid α] (f : ZMod 2 → α) : ∑ x, f x = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide, Finset.sum_pair (by decide)]

/-- **The four single-qubit Paulis span the single-qubit operators**: `I` and `Z` give the diagonal,
`X` and `XZ` the off-diagonal entries. -/
theorem exists_pauli1_expansion (M : Matrix (ZMod 2) (ZMod 2) ℂ) :
    ∃ c : ZMod 2 × ZMod 2 → ℂ, M = ∑ k, c k • pauli1 k.1 k.2 := by
  refine ⟨fun k => if k.1 = 0 then (if k.2 = 0 then (M 0 0 + M 1 1) / 2 else (M 0 0 - M 1 1) / 2)
    else if k.2 = 0 then (M 0 1 + M 1 0) / 2 else (M 1 0 - M 0 1) / 2, ?_⟩
  have hcases : ∀ w : ZMod 2, w = 0 ∨ w = 1 := by decide
  have hone : (1 + 1 : ZMod 2) = 0 := by decide
  ext u v
  rcases hcases u with rfl | rfl <;> rcases hcases v with rfl | rfl <;>
    simp [Fintype.sum_prod_type, sum_zmod_two, pauli1, ZMod.val_one, hone] <;> ring

/-! ### Discretisation -/

namespace QECC

variable {n : ℕ}

/-- The Pauli operator, with trivial phase, acting on the qubits of `S` by the single-qubit Paulis
named by `f`. -/
def paulify (S : Finset (Fin n)) (f : Fin n → ZMod 2 × ZMod 2) : PauliOp n where
  phase := 0
  x q := if q ∈ S then (f q).1 else 0
  z q := if q ∈ S then (f q).2 else 0

theorem weight_paulify_le (S : Finset (Fin n)) (f : Fin n → ZMod 2 × ZMod 2) :
    PauliOp.weight (paulify S f) ≤ S.card := by
  refine Finset.card_le_card fun q hq => ?_
  simp only [paulify] at hq
  by_contra hqS
  simp [hqS] at hq

theorem errMat_eq_toMat_paulify (S : Finset (Fin n)) (f : Fin n → ZMod 2 × ZMod 2) :
    errMat S (fun q => pauli1 (f q).1 (f q).2) = PauliOp.toMat (paulify S f) := by
  rw [PauliOp.toMat, pauliOp_eq_piKron, errMat]
  simp only [paulify, ZMod.val_zero, pow_zero, one_smul]
  refine congrArg piKron (funext fun q => ?_)
  by_cases hq : q ∈ S <;> simp [hq]

/-- **Discretisation of errors into Paulis.** An arbitrary error supported on the qubits of `S` is
a linear combination of Pauli operators of weight at most `S.card`. -/
theorem errMat_mem_span_pauli (S : Finset (Fin n)) (A : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) :
    errMat S A ∈ Submodule.span ℂ
      (Set.range fun P : {P : PauliOp n // PauliOp.weight P ≤ S.card} => PauliOp.toMat P.1) :=
  errMat_mem_of_mem (fun k : ZMod 2 × ZMod 2 => pauli1 k.1 k.2) (0, 0) exists_pauli1_expansion S
    (fun f => by
      rw [errMat_eq_toMat_paulify]
      exact Submodule.subset_span ⟨⟨_, weight_paulify_le S f⟩, rfl⟩) A

/-- **Discretisation, keeping track of the support.** An arbitrary error supported on the qubits of
`S` is a linear combination of Pauli operators that are themselves supported on `S`. Recording the
support, and not merely the weight, is what makes the located-error radius `d - 1` instead of
`⌊(d-1)/2⌋`: a product of two Paulis supported on `S` is again supported on `S`. -/
theorem errMat_mem_span_pauli_supported (S : Finset (Fin n))
    (A : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) :
    errMat S A ∈ Submodule.span ℂ (Set.range
      fun P : {P : PauliOp n // ∀ q ∉ S, P.x q = 0 ∧ P.z q = 0} => PauliOp.toMat P.1) :=
  errMat_mem_of_mem (fun k : ZMod 2 × ZMod 2 => pauli1 k.1 k.2) (0, 0) exists_pauli1_expansion S
    (fun f => by
      rw [errMat_eq_toMat_paulify]
      exact Submodule.subset_span ⟨⟨_, fun q hq => ⟨if_neg hq, if_neg hq⟩⟩, rfl⟩) A

end QECC

end QuantumLib
