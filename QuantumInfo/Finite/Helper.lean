import Mathlib

open BigOperators
open Classical

namespace Finset

variable [CommMonoid β]

/-- Cyclically permute 3 nested instances of `Finset.sum`. -/
@[to_additive]
theorem prod_comm_3 {s : Finset γ} {t : Finset α} {u : Finset δ} {f : γ → α → δ → β} :
    (∏ x in s, ∏ y in t, ∏ z in u, f x y z) = ∏ z in u, ∏ x in s, ∏ y in t, f x y z := by
  nth_rewrite 2 [prod_comm]
  congr 1
  funext
  exact prod_comm

end Finset

namespace Matrix

namespace IsHermitian

section eigenvalues
variable {n 𝕜 : Type*}
variable [Fintype n] [RCLike 𝕜]
variable {A : Matrix n n 𝕜}
variable (hA : A.IsHermitian)

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

variable {m n R : Type*}
variable [Fintype m] [Fintype n]
variable [RCLike R] [DecidableEq n] [DecidableEq m]

variable {A : Matrix m m R} {B : Matrix n n R}

theorem PosSemidef_kronecker (hA : A.PosSemidef) (hB : B.PosSemidef) : (A ⊗ₖ B).PosSemidef := by
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

noncomputable section log

/-- Matrix logarithm (base e) of a positive semidefinite matrix, as given by the elementwise
  real logarithm of the diagonal in a diagonalized form.

  Note that this means that the nullspace of the image includes all of the nullspace of the
  original matrix. This contrasts to the standard definition, which is only defined for positive
  *definite* matrices, and the nullspace of the image is exactly the (λ=1)-eigenspace of the
  original matrix. It coincides with the standard definition if A is positive definite. -/
def log (hA : A.PosSemidef) : Matrix m m R :=
  hA.1.eigenvectorMatrix * diagonal ((↑) ∘ Real.log ∘ hA.1.eigenvalues) * hA.1.eigenvectorMatrixInv

--TODO: properties here https://en.wikipedia.org/wiki/Logarithm_of_a_matrix#Properties

end log

end PosSemidef

noncomputable section traceNorm

open scoped ComplexOrder

variable {m n R : Type*}
variable [Fintype m] [Fintype n]
variable [RCLike R] [DecidableEq n] [DecidableEq m]

/-- The trace norm of a matrix: Tr[√(A† A)]. -/
def traceNorm (A : Matrix m n R) : ℝ :=
  RCLike.re (Matrix.posSemidef_conjTranspose_mul_self A).sqrt.trace

/-- The trace norm of the negative is equal to the trace norm. -/
theorem traceNorm_eq_neg  (A : Matrix m n R) : traceNorm (-A) = traceNorm A := by
  unfold traceNorm
  have : (-A)ᴴ * -A = (A)ᴴ * A := by
    rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg]
    exact neg_neg _
  congr!

end traceNorm

end Matrix
