import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef

import QuantumInfo.Mathlib.Other

open BigOperators
open Classical

variable {n 𝕜 : Type*}
variable [RCLike 𝕜]

namespace Matrix

namespace IsHermitian

variable {A : Matrix n n 𝕜} {B : Matrix n n 𝕜}
variable (hA : A.IsHermitian) (hB : B.IsHermitian)

include hA in
theorem smul {c : 𝕜} (h : RCLike.im c = 0) : (c • A).IsHermitian := by
  rw [IsHermitian, Matrix.conjTranspose_smul, RCLike.star_def, RCLike.conj_eq_iff_im.mpr h, hA]

variable [Fintype n]

include hA in
@[simp]
theorem re_trace_eq_trace : RCLike.re (A.trace) = A.trace := by
  rw [trace, map_sum, RCLike.ofReal_sum, IsHermitian.coe_re_diag hA]

section eigenvalues

/-- The sum of the eigenvalues of a Hermitian matrix is equal to its trace. -/
theorem sum_eigenvalues_eq_trace : ∑ i, hA.eigenvalues i = A.trace := by
  nth_rewrite 2 [hA.spectral_theorem]
  rw [Matrix.trace_mul_comm]
  rw [← mul_assoc]
  simp [Matrix.trace_diagonal]

end eigenvalues

end IsHermitian

section Kronecker

open Kronecker

variable [CommRing R] [StarRing R]
variable (A : Matrix m m R) (B : Matrix n n R)

theorem kroneckerMap_conjTranspose : (A ⊗ₖ B)ᴴ = (Aᴴ ⊗ₖ Bᴴ) := by
  ext; simp

variable {A : Matrix m m R} {B : Matrix n n R}
variable (hA : A.IsHermitian) (hB : B.IsHermitian)

include hA hB in
theorem kroneckerMap_IsHermitian : (A ⊗ₖ B).IsHermitian := by
  exact (hA ▸ hB ▸ kroneckerMap_conjTranspose A B : _ = _)

end Kronecker

namespace PosSemidef

open Classical
open Kronecker
open scoped ComplexOrder

variable {m n 𝕜 : Type*}
variable [Fintype m] [Fintype n]
variable [RCLike 𝕜] [DecidableEq n]

section
variable {A : Matrix m m 𝕜} {B : Matrix m m 𝕜}
variable (hA : A.PosSemidef) (hB : B.PosSemidef)

include hA in
theorem diag_nonneg : ∀i, 0 ≤ A.diag i := by
  intro i
  simpa [Matrix.mulVec, Matrix.dotProduct] using hA.2 (fun j ↦ if i = j then 1 else 0)

include hA in
theorem trace_nonneg : 0 ≤ A.trace := by
  rw [Matrix.trace]
  apply Finset.sum_nonneg
  simp_rw [Finset.mem_univ, forall_true_left]
  exact hA.diag_nonneg

include hA in
theorem smul {c : 𝕜} (h : 0 ≤ c) : (c • A).PosSemidef := by
  constructor
  · apply hA.1.smul (RCLike.nonneg_iff.mp h).2
  · intro x
    rw [Matrix.smul_mulVec_assoc, Matrix.dotProduct_smul]
    exact mul_nonneg h (hA.2 x)

include hA hB in
theorem convex_cone {c₁ c₂ : 𝕜} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) : (c₁ • A + c₂ • B).PosSemidef :=
  (hA.smul hc₁).add (hB.smul hc₂)

end

variable {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
variable (hA : A.PosSemidef) (hB : B.PosSemidef)

include hA hB in
theorem PosSemidef_kronecker : (A ⊗ₖ B).PosSemidef := by
  rw [hA.left.spectral_theorem, hB.left.spectral_theorem]
  rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
  rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]
  rw [← kroneckerMap_conjTranspose]
  rw [Matrix.diagonal_kronecker_diagonal]
  apply mul_mul_conjTranspose_same
  rw [posSemidef_diagonal_iff]
  rintro ⟨i₁, i₂⟩
  convert mul_nonneg (hA.eigenvalues_nonneg i₁) (hB.eigenvalues_nonneg i₂)
  rw [RCLike.nonneg_iff]
  simp

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
  rw [smul_smul, one_div, inv_mul_cancel₀ hc.ne', one_smul]

theorem pos_Real_smul {c : ℝ} (hA : A.PosSemidef) (hc : 0 ≤ c) : (c • A).PosSemidef := by
  rw [(RCLike.real_smul_eq_coe_smul c A : c • A = (c : 𝕜) • A)]
  exact pos_smul hA (RCLike.ofReal_nonneg.mpr hc)

theorem nonneg_Real_smul {c : ℝ} (hA : (c • A).PosSemidef) (hc : 0 < c) : A.PosSemidef := by
  rw [(RCLike.real_smul_eq_coe_smul c A : c • A = (c : 𝕜) • A)] at hA
  exact nonneg_smul hA (RCLike.ofReal_pos.mpr hc)

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
  (hA.1.eigenvectorUnitary : Matrix _ _ _) * diagonal (RCLike.ofReal ∘ Real.log ∘ hA.1.eigenvalues) *
  (star hA.1.eigenvectorUnitary : Matrix _ _ _)

--TODO: properties here https://en.wikipedia.org/wiki/Logarithm_of_a_matrix#Properties

end log

end PosSemidef

section frobenius_inner_product
open scoped ComplexOrder

variable {A : Matrix n n 𝕜} {B : Matrix n n 𝕜} [Fintype n]

/-- Inner product of two square matrices. TODO: Rectangular? -/
def inner (A : Matrix n n 𝕜) (B : Matrix n n 𝕜) : 𝕜 :=
  (Aᴴ * B).trace

/-- The inner product for Hermtian matrices is equal to the trace of
  the product. -/
theorem inner_eq_trace_mul (hA : A.IsHermitian) : A.inner B = (A * B).trace := by
  rw [inner, hA]

variable (hA : A.PosSemidef) (hB : B.PosSemidef)

include hA hB in
/-- The inner product for PSD matrices is nonnegative. -/
theorem PosSemidef.inner_ge_zero : 0 ≤ A.inner B := by
  rw [inner, hA.left, ← hA.sqrt_mul_self, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  nth_rewrite 1 [← hA.posSemidef_sqrt.left]
  convert (hB.conjTranspose_mul_mul_same _).trace_nonneg

include hA hB in
/-- The inner product for PSD matrices is at most the product of their traces. -/
theorem PosSemidef.inner_le_mul_trace : RCLike.re (A.inner B) ≤ RCLike.re A.trace * RCLike.re B.trace :=
  sorry

/-- The InnerProductSpace on Matrix n n 𝕜 defined by the Frobenius inner product, `Matrix.inner`.-/
def MatrixInnerProduct :=
  InnerProductSpace.ofCore (𝕜 := 𝕜) (F := Matrix n n 𝕜) {
    inner := inner
    conj_symm := fun x y ↦ by
      simp [inner, starRingEnd_apply, ← Matrix.trace_conjTranspose,
        conjTranspose_mul, conjTranspose_conjTranspose]
    nonneg_re := fun x ↦ by
      simp only [inner]
      exact (RCLike.nonneg_iff.mp x.posSemidef_conjTranspose_mul_self.trace_nonneg).1
    add_left := by simp [inner, add_mul]
    smul_left := by simp [inner]
    definite := sorry
  }

end frobenius_inner_product
