import QuantumInfo.Finite.CPTPMap

/-!
Quantum theory and operations specific to qubits.
 - Standard named (single-qubit) gates: Z, X, Y, H, S, T
 - Controlled versions of gates
 - Completeness of the PPT test: a state is separable iff it is PPT.
 - Fidelity for qubits: `F(ρ,σ) = 2√(ρ.det * σ.det)`.
 - The singlet/triplet split.
-/

abbrev Qubit := Fin 2

section Mathlib
namespace Matrix

variable [NonUnitalNonAssocSemiring α] [StarRing α]

theorem conjTranspose_fin_one (a : α) : !![a].conjTranspose = !![star a] := by
  ext i j
  fin_cases i; fin_cases j; rfl

theorem conjTranspose_fin_two (a b c d : α) : !![a, b; c, d].conjTranspose = !![star a, star c; star b, star d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end Matrix
end Mathlib

namespace Qubit

/-- The Pauli Z gate on a qubit. -/
def Z : 𝐔[Qubit] := by
  use !![1, 0; 0, -1]
  constructor
  <;> ext i j
  <;> fin_cases i <;> fin_cases j
  <;> simp [star, Matrix.conjTranspose_fin_two, Complex.ext_iff]

/-- The Pauli X gate on a qubit. -/
def X : 𝐔[Qubit] := by
  use !![0, 1; 1, 0]
  constructor
  <;> ext i j
  <;> fin_cases i <;> fin_cases j
  <;> simp [star, Matrix.conjTranspose_fin_two, Complex.ext_iff]

/-- The Pauli Y gate on a qubit. -/
def Y : 𝐔[Qubit] := by
  use !![0, -Complex.I; Complex.I, 0]
  constructor
  <;> ext i j
  <;> fin_cases i <;> fin_cases j
  <;> simp [star, Matrix.conjTranspose_fin_two, Complex.ext_iff]

/-- The H gate, a Hadamard gate, on a qubit. -/
noncomputable def H : 𝐔[Qubit] :=
 by
  use (Real.sqrt (1/2)) • (!![1, 1; 1, -1])
  constructor
  <;> ext i j
  <;> fin_cases i <;> fin_cases j
  <;> field_simp [star, Matrix.conjTranspose_fin_two, Complex.ext_iff, one_add_one_eq_two]

/-- The S gate, or Rz(π/2) rotation on a qubit. -/
def S : 𝐔[Qubit] := by
  use !![1, 0; 0, Complex.I]
  constructor
  <;> ext i j
  <;> fin_cases i <;> fin_cases j
  <;> simp [star, Matrix.conjTranspose_fin_two, Complex.ext_iff]

/-- The T gate, or Rz(π/4) rotation on a qubit. -/
noncomputable def T : 𝐔[Qubit] := by
  use !![1, 0; 0, (1 + Complex.I)/Real.sqrt 2]
  constructor
  <;> ext i j
  <;> fin_cases i <;> fin_cases j
  <;> field_simp [star, Matrix.conjTranspose_fin_two, Complex.ext_iff, one_add_one_eq_two]

/-- Given a unitary `U` on some Hilbert space `T`, we have the controllized version that acts on `Fin 2 ⊗ T`
where `U` is conditionally applied if the first qubit is `1`. -/
def controllize {T : Type*} [Fintype T] [DecidableEq T] (g : 𝐔[T]) : 𝐔[Qubit × T] :=
  ⟨Matrix.of fun (q₁,t₁) (q₂,t₂) ↦
    if (q₁,q₂) = (0,0) then
      (if t₁ = t₂ then 1 else 0)
    else if (q₁,q₂) = (1,1) then
      g t₁ t₂
    else 0
    , by
      rw [Matrix.mem_unitaryGroup_iff]
      ext ⟨qi,ti⟩ ⟨qj,tj⟩
      fin_cases qi
      <;> fin_cases qj
      rotate_right
      · simpa [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type] using congrFun₂ g.2.2 ti tj
      all_goals simp [Matrix.mul_apply, Matrix.one_apply, @Eq.comm _ tj ti, Fintype.sum_prod_type]
    ⟩

end Qubit
