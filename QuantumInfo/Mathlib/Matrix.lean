import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef

import QuantumInfo.Mathlib.Other

open BigOperators
open Classical

namespace Matrix
variable {n 𝕜 : Type*}
variable [Fintype n] [RCLike 𝕜]
variable (A : Matrix n n 𝕜) (B : Matrix n n 𝕜)

/-- Inner product of two square matrices. TODO: Rectangular? -/
def inner (A : Matrix n n 𝕜) (B : Matrix n n 𝕜) : ℝ :=
  RCLike.re (Aᴴ * B).trace

namespace IsHermitian

variable {A B}
variable (hA : A.IsHermitian) (hB : B.IsHermitian)

@[simp]
theorem re_trace_eq_trace : RCLike.re (A.trace) = A.trace := by
  rw [trace, map_sum, RCLike.ofReal_sum, IsHermitian.coe_re_diag hA]

/-- The inner product for Hermtian matrices is equal to the trace of
  the product. -/
theorem inner_eq_trace_mul : A.inner B = (A * B).trace := by
  have : IsHermitian ((1/2:𝕜) • ((A*B) + (A*B)ᴴ)) := by
    simp only [IsHermitian, one_div, conjTranspose_mul, smul_add, conjTranspose_add,
      conjTranspose_smul, star_inv', star_ofNat, conjTranspose_conjTranspose]
    rw [add_comm]
  have : (A*B)ᴴ.trace = star (A*B).trace := sorry
  let tmp₁ := hA
  let tmp₂ := hB
  sorry

section eigenvalues

/-- The sum of the eigenvalues of a Hermitian matrix is equal to its trace. -/
theorem sum_eigenvalues_eq_trace : ∑ i, hA.eigenvalues i = A.trace := by
  simp_rw [eigenvalues_eq, dotProduct, mulVec, dotProduct, ← map_sum, Finset.mul_sum]
  simp_rw [mul_comm, mul_assoc, star, Matrix.transpose_apply]
  rw [Finset.sum_comm, Finset.sum_comm_3, Finset.sum_comm]
  have hinv := congrFun₂ hA.eigenvectorMatrix_mul_inv
  simp_rw [← conjTranspose_eigenvectorMatrix, Matrix.mul_apply', dotProduct, Matrix.conjTranspose_apply]
    at hinv
  have h1 := congrFun₂ (Matrix.mul_one A)
  simp_rw [Matrix.mul_apply', dotProduct] at h1
  simp_rw [← Finset.mul_sum, hinv, h1, trace]
  rw [← hA.coe_re_diag]
  simp only [map_sum, RCLike.ofReal_sum, diag]

end eigenvalues

end IsHermitian

section Kronecker

open Kronecker

variable [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
variable [Fintype m] [Fintype n]
variable (A : Matrix m m R) (B : Matrix n n R)

theorem kroneckerMap_conjTranspose : (A ⊗ₖ B)ᴴ = (Aᴴ ⊗ₖ Bᴴ) := by
  ext; simp

variable {A : Matrix m m R} {B : Matrix n n R}
variable (hA : A.IsHermitian) (hB : B.IsHermitian)

theorem kroneckerMap_IsHermitian : (A ⊗ₖ B).IsHermitian := by
  exact (hA ▸ hB ▸ kroneckerMap_conjTranspose A B : _ = _)

end Kronecker

namespace PosSemidef

open Classical
open Kronecker
open scoped ComplexOrder

variable {m n 𝕜 : Type*}
variable [Fintype m] [Fintype n]
variable [RCLike 𝕜] [DecidableEq n] [DecidableEq m]

variable {A : Matrix m m 𝕜} {B : Matrix n n 𝕜} {C : Matrix m m 𝕜}
variable (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef)

/-- The inner product for PSD matrices is nonnegative. -/
theorem inner_ge_zero : 0 ≤ A.inner C :=
  let tmp₁ := hA
  let tmp₂ := hB
  sorry

/-- The inner product for PSD matrices is at most the product of their
  traces. -/
theorem inner_le_mul_trace : A.inner C ≤ A.trace * C.trace :=
  let tmp₁ := hA
  let tmp₂ := hB
  sorry

theorem PosSemidef_kronecker : (A ⊗ₖ B).PosSemidef := by
  rw [hA.left.spectral_theorem', hB.left.spectral_theorem']
  rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
  rw [← hA.left.conjTranspose_eigenvectorMatrix]
  rw [← hB.left.conjTranspose_eigenvectorMatrix]
  rw [← kroneckerMap_conjTranspose]
  rw [Matrix.diagonal_kronecker_diagonal]
  apply mul_mul_conjTranspose_same
  rw [posSemidef_diagonal_iff]
  rintro ⟨i₁, i₂⟩
  convert mul_nonneg (hA.eigenvalues_nonneg i₁) (hB.eigenvalues_nonneg i₂)
  rw [RCLike.nonneg_iff]
  simp

theorem diag_nonneg (hA : A.PosSemidef) : ∀i, 0 ≤ A.diag i := by
  intro i
  simpa [Matrix.mulVec, Matrix.dotProduct] using hA.2 (fun j ↦ if i = j then 1 else 0)

lemma sqrt_eq {A B : Matrix m m 𝕜} (h : A = B) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    hA.sqrt = hB.sqrt := by
  congr!

lemma sqrt_eq' {A B : Matrix m m 𝕜} (h : A = B) (hA : A.PosSemidef) :
    hA.sqrt = (h ▸ hA).sqrt := by
  congr!

@[simp]
theorem sqrt_0 : (Matrix.PosSemidef.zero (n := n) (R := 𝕜)).sqrt = 0 :=
  Eq.symm $ eq_sqrt_of_sq_eq Matrix.PosSemidef.zero _ (by simp)

@[simp]
theorem sqrt_1 : (Matrix.PosSemidef.one (n := n) (R := 𝕜)).sqrt = 1 :=
  Eq.symm $ eq_sqrt_of_sq_eq Matrix.PosSemidef.one _ (by simp)

theorem pos_smul {c : 𝕜} (hA : A.PosSemidef) (hc : 0 ≤ c) : (c • A).PosSemidef := by
  constructor
  · simp only [IsHermitian, conjTranspose_smul, RCLike.star_def]
    congr
    exact RCLike.conj_eq_iff_im.mpr (RCLike.nonneg_iff.mp hc).2
    exact hA.1
  · intro x
    rw [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
    exact Left.mul_nonneg hc (hA.2 x)

theorem nonneg_smul {c : 𝕜} (hA : (c • A).PosSemidef) (hc : 0 < c) : A.PosSemidef := by
  have : 0 < 1/c := by
    rw [RCLike.pos_iff] at hc ⊢
    aesop
  convert hA.pos_smul (c := 1/c) this.le
  rw [smul_smul, one_div, inv_mul_cancel hc.ne', one_smul]

theorem sqrt_nonneg_smul {c : 𝕜} (hA : (c^2 • A).PosSemidef) (hc : 0 < c) :
    hA.sqrt = c • (hA.nonneg_smul (sq_pos_of_pos hc) : A.PosSemidef).sqrt := by
  apply Eq.symm
  apply eq_sqrt_of_sq_eq
  · apply pos_smul ?_ hc.le
    apply posSemidef_sqrt
  rw [pow_two, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, sqrt_mul_self, pow_two, smul_smul]

noncomputable section log

/-- Matrix logarithm (base e) of a positive semidefinite matrix, as given by the elementwise
  real logarithm of the diagonal in a diagonalized form.

  Note that this means that the nullspace of the image includes all of the nullspace of the
  original matrix. This contrasts to the standard definition, which is only defined for positive
  *definite* matrices, and the nullspace of the image is exactly the (λ=1)-eigenspace of the
  original matrix. It coincides with the standard definition if A is positive definite. -/
def log (hA : A.PosSemidef) : Matrix m m 𝕜 :=
  hA.1.eigenvectorMatrix * diagonal ((↑) ∘ Real.log ∘ hA.1.eigenvalues) * hA.1.eigenvectorMatrixInv

--TODO: properties here https://en.wikipedia.org/wiki/Logarithm_of_a_matrix#Properties

end log

end PosSemidef
