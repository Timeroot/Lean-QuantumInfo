--Aristotle seems unable to resolve an i m p o r t of a non-mathlib
--file. Thankfully, we can fit most of what we need from LeanQuantumInfo in here.

import Mathlib

noncomputable section

notation "𝐔[" n "]" => Matrix.unitaryGroup n ℂ

variable (d : Type*) [Fintype d]
structure Ket where
  vec : d → ℂ
  normalized' : ∑ x, ‖vec x‖ ^ 2 = 1

namespace Braket

instance instFunLikeKet : FunLike (Ket d) d ℂ where
  coe ψ := ψ.vec
  coe_injective' _ _ h := by rwa [Ket.mk.injEq]

end Braket

theorem Ket.apply (ψ : Ket d) (i : d) : ψ i = ψ.vec i :=
  rfl

@[ext]
theorem Ket.ext {ξ ψ : Ket d} (h : ∀ x, ξ x = ψ x) : ξ = ψ :=
  DFunLike.ext ξ ψ h


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
        Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
        $rules',* ]
      <;> norm_num
      <;> try field_simp
      <;> try ring_nf
      ))

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

namespace Qubit

variable {k : Type*} [Fintype k] [DecidableEq k]

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

/-- The Pauli Z gate on a qubit. -/
def Z : 𝐔[Qubit] :=
  ⟨!![1, 0; 0, -1], by constructor <;> matrix_expand⟩

/-- The Pauli X gate on a qubit. -/
def X : 𝐔[Qubit] :=
  ⟨!![0, 1; 1, 0], by constructor <;> matrix_expand⟩

/-- The Pauli Y gate on a qubit. -/
def Y : 𝐔[Qubit] :=
  ⟨!![0, -Complex.I; Complex.I, 0], by constructor <;> matrix_expand⟩

end Qubit

/- figure out why this doesn't typecheck
abbrev HermitianMat (n : Type*) (α : Type*) [AddGroup α] [StarAddMonoid α] :=
  (selfAdjoint (Matrix n n α) : Type (max u_1 u_2))
-/
