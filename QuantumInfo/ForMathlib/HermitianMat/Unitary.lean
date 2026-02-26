import QuantumInfo.ForMathlib.HermitianMat.Inner
import QuantumInfo.ForMathlib.HermitianMat.NonSingular
import QuantumInfo.ForMathlib.Isometry

notation "𝐔[" n "]" => Matrix.unitaryGroup n ℂ

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
