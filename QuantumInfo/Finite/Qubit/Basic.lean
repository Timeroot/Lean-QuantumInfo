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

variable {α : Type*} [NonUnitalNonAssocSemiring α] [StarRing α]

variable {α β : Type*} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

@[simp]
theorem neg_unitary_val (u : 𝐔[α]) : (-u).val = -u := by
  rfl

omit [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] in
open Kronecker in
@[simp]
theorem star_kron (a : Matrix α α ℂ) (b : Matrix β β ℂ) : star (a ⊗ₖ b) = (star a) ⊗ₖ (star b) := by
  ext _ _
  simp

open Kronecker in
theorem kron_unitary (a : 𝐔[α]) (b : 𝐔[β]) : a.val ⊗ₖ b.val ∈ 𝐔[α × β] := by
  simp [Matrix.mem_unitaryGroup_iff, ← Matrix.mul_kronecker_mul]

open Kronecker in
def unitary_kron (a : 𝐔[α]) (b : 𝐔[β]) : 𝐔[α × β] :=
  ⟨_, kron_unitary a b⟩

scoped notation a:60 " ⊗ᵤ " b:60 => unitary_kron a b

@[simp]
theorem unitary_kron_apply (a : 𝐔[α]) (b : 𝐔[β]) (i₁ i₂ : α) (j₁ j₂ : β) :
    (a ⊗ᵤ b) (i₁, j₁) (i₂, j₂) = (a i₁ i₂) * (b j₁ j₂) := by
  rfl

@[simp]
theorem unitary_kron_one_one : (1 : 𝐔[α]) ⊗ᵤ (1 : 𝐔[β]) = (1 : 𝐔[α × β]) := by
  simp [Matrix.unitary_kron]

end Matrix
end Mathlib

open Lean.Parser.Tactic in
open Lean in
/--
Proves goals equating small matrices by expanding out products and simpliying standard Real arithmetic.
-/
syntax (name := matrix_expand) "matrix_expand"
  (" [" ((simpStar <|> simpErase <|> simpLemma),*,?) "]")?
  (" with " rcasesPat+)? : tactic

macro_rules
  | `(tactic| matrix_expand $[[$rules,*]]? $[with $withArg*]?) => do
    let id1 := (withArg.getD ⟨[]⟩).getD 0 (← `(rcasesPat| _))
    let id2 := (withArg.getD ⟨[]⟩).getD 1 (← `(rcasesPat| _))
    let rules' := rules.getD ⟨#[]⟩
    `(tactic| (
      ext i j
      repeat rcases (i : Prod _ _) with ⟨i, $id1⟩
      repeat rcases (j : Prod _ _) with ⟨j, $id2⟩
      fin_cases i
      <;> fin_cases j
      <;> simp [Complex.ext_iff,
        Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply,
        $rules',* ]
      <;> try field_simp
      <;> try ring_nf))

namespace Qubit
open Real
open Complex

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- The Pauli Z gate on a qubit. -/
def Z : 𝐔[Qubit] :=
  ⟨!![1, 0; 0, -1], by constructor <;> matrix_expand⟩

/-- The Pauli X gate on a qubit. -/
def X : 𝐔[Qubit] :=
  ⟨!![0, 1; 1, 0], by constructor <;> matrix_expand⟩

/-- The Pauli Y gate on a qubit. -/
def Y : 𝐔[Qubit] :=
  ⟨!![0, -I; I, 0], by constructor <;> matrix_expand⟩

/-- The H gate, a Hadamard gate, on a qubit. -/
noncomputable def H : 𝐔[Qubit] :=
  ⟨√(1/2) • (!![1, 1; 1, -1]), by constructor <;> matrix_expand⟩

/-- The S gate, or Rz(π/2) rotation on a qubit. -/
def S : 𝐔[Qubit] :=
  ⟨!![1, 0; 0, I], by constructor <;> matrix_expand⟩

/-- The T gate, or Rz(π/4) rotation on a qubit. -/
noncomputable def T : 𝐔[Qubit] :=
  ⟨!![1, 0; 0, (1 + I)/√2], by constructor <;> matrix_expand⟩

@[simp]
theorem Z_sq : Z * Z = 1 := by
  matrix_expand [Z]

@[simp]
theorem X_sq : X * X = 1 := by
  matrix_expand [X]

@[simp]
theorem Y_sq : Y * Y = 1 := by
  matrix_expand [Y]

@[simp]
theorem H_sq : H * H = 1 := by
  matrix_expand [H]

@[simp]
theorem S_sq : S * S = Z := by
  matrix_expand [S, Z]

@[simp]
theorem T_sq : T * T = S := by
  matrix_expand [T, S]

/-- The anticommutator `{X,Y}` is zero. Marked simp as to put Pauli products in a canonical Y-X-Z order. -/
@[simp]
theorem X_Y_anticomm : X * Y = -Y * X := by
  matrix_expand [X, Y]

/-- The anticommutator `{Y,Z}` is zero. -/
theorem Y_Z_anticomm : Z * Y = -Y * Z := by
  matrix_expand [Z, Y]

/-- The anticommutator `{Z,X}` is zero. -/
theorem Z_X_anticomm : Z * X = -X * Z := by
  matrix_expand [Z, X]

@[simp]
theorem H_mul_X_eq_Z_mul_H : H * X = Z * H := by
  matrix_expand [H, X, Z]

@[simp]
theorem H_mul_Z_eq_X_mul_H : H * Z = X * H := by
  matrix_expand [H, X, Z]

@[simp]
theorem S_Z_comm : Z * S = S * Z := by
  simp [← S_sq, mul_assoc]

@[simp]
theorem T_Z_comm : Z * T = T * Z := by
  simp [← S_sq, ← T_sq, mul_assoc]

@[simp]
theorem S_T_comm : S * T = T * S := by
  simp [← T_sq, mul_assoc]

/-- Given a unitary `U` on some Hilbert space `k`, we have the controllized version that acts on `Fin 2 ⊗ k`
where `U` is conditionally applied if the first qubit is `1`. -/
def controllize (g : 𝐔[k]) : 𝐔[Qubit × k] :=
  ⟨Matrix.of fun (q₁,t₁) (q₂,t₂) ↦
    if (q₁,q₂) = (0,0) then
      (if t₁ = t₂ then 1 else 0)
    else if (q₁,q₂) = (1,1) then
      g t₁ t₂
    else 0
    , by
      rw [Matrix.mem_unitaryGroup_iff]
      matrix_expand [-Complex.ext_iff] with ti tj;
      · congr 1
        exact propext eq_comm
      · exact congrFun₂ g.2.2 ti tj
    ⟩

scoped notation "C[" g "]" => controllize g

variable (g : 𝐔[k]) (j₁ j₂ : k)

@[simp]
theorem controllize_apply_zero_zero : C[g] (0, j₁) (0, j₂) = (1 : 𝐔[k]) j₁ j₂ := by
  rfl

@[simp]
theorem controllize_apply_zero_one : C[g] (0, j₁) (1, j₂) = 0 := by
  rfl

@[simp]
theorem controllize_apply_one_zero : C[g] (1, j₁) (0, j₂) = 0 := by
  rfl

@[simp]
theorem controllize_apply_one_one : C[g] (1, j₁) (1, j₂) = g j₁ j₂ := by
  rfl

@[simp]
theorem controllize_mul (g₁ g₂ : 𝐔[k]) : C[g₁] * C[g₂] = C[g₁ * g₂] := by
  matrix_expand

@[simp]
theorem controllize_one : C[(1 : 𝐔[k])] = 1 := by
  matrix_expand

@[simp]
theorem controllize_mul_inv : C[g] * C[g⁻¹] = 1 := by
  simp

open scoped Matrix in
@[simp]
theorem X_controllize_X : (X ⊗ᵤ 1) * C[g] * (X ⊗ᵤ 1) = (1 ⊗ᵤ g) * C[g⁻¹] := by
  matrix_expand [X, -Complex.ext_iff] with ki kj;
  suffices (1 : Matrix k k ℂ) ki kj = (g * g⁻¹) ki kj by
    convert this
  simp

end Qubit
