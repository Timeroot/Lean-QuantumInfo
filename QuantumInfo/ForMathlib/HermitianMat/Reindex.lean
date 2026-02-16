/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.Basic
import QuantumInfo.ForMathlib.ContinuousLinearMap
import QuantumInfo.ForMathlib.LinearEquiv

/-!
Much like `Matrix.reindex` and `Matrix.submatrix`, we can reindex a Hermitian matrix to get another
Hermitian matrix; however, this only makes sense when both permutations are the same, accordingly,
`HermitianMat.reindex` only takes one `Equiv` argument (as opposed to `Matrix.reindex`'s two).

This file then gives relevant lemmas for simplifying this.
-/
namespace HermitianMat

variable {d d₂ d₃ d₄ 𝕜 : Type*} [RCLike 𝕜]

variable (A B : HermitianMat d 𝕜) (e : d ≃ d₂)

def reindex (e : d ≃ d₂) : HermitianMat d₂ 𝕜 :=
  ⟨A.mat.reindex e e, A.H.submatrix e.symm⟩

@[simp]
theorem mat_reindex : (A.reindex e).mat = A.mat.reindex e e := by
  rfl

/-! Our simp-normal form for expressions involving `HermitianMat.reindex` is that we try to push
the reindexing as far out as possible, so that it can be absorbed by `HermitianMat.trace`, or
cancelled our in a `HermitianMat.inner`. In places where it commutes (like `HermitianMat.inner`)
we push it to the right side. One downside is that we're not as likely to hit `reindex_one`. -/

@[simp]
theorem reindex_refl (A : HermitianMat d 𝕜) :
    A.reindex (.refl _) = A := by
  rfl

@[simp]
theorem reindex_reindex (A : HermitianMat d 𝕜) (e : d ≃ d₂) (f : d₂ ≃ d₃) :
    (A.reindex e).reindex f = A.reindex (e.trans f) := by
  ext1; simp; rfl

@[simp]
theorem reindex_zero : (0 : HermitianMat d 𝕜).reindex e = 0 := by
  ext1; simp

@[simp]
theorem reindex_one [DecidableEq d] [DecidableEq d₂] :
    (1 : HermitianMat d 𝕜).reindex e = 1 := by
  ext1
  simp [reindex]

@[simp]
theorem reindex_add : A.reindex e + B.reindex e = (A + B).reindex e := by
  ext1; simp [Matrix.submatrix_add]

@[simp]
theorem reindex_sub  : A.reindex e - B.reindex e = (A - B).reindex e := by
  ext1; simp [Matrix.submatrix_sub]

@[simp]
theorem reindex_neg : (-A).reindex e = -(A.reindex e) := by
  ext1; simp [Matrix.submatrix_neg]

@[simp]
theorem reindex_smul (c : ℝ) : (c • A).reindex e = c • (A.reindex e) := by
  ext1; simp [Matrix.submatrix_smul]

@[simp]
theorem reindex_conj [Fintype d₂] [Fintype d] (B : Matrix d₃ d₂ 𝕜) :
    (A.reindex e).conj B = A.conj (B.submatrix id e) := by
  ext1
  simp only [conj_apply, mat_reindex, Matrix.reindex_apply, mat_mk]
  rw [← Matrix.submatrix_id_mul_right, Matrix.mul_assoc]
  rw [← Matrix.submatrix_id_mul_left, ← Matrix.mul_assoc]
  simp

variable [Fintype d]

theorem conj_submatrix (B : Matrix d₂ d₄ 𝕜) (e : d₃ ≃ d₂) (f : d → d₄) :
    A.conj (B.submatrix e f) = (A.conj (B.submatrix id f)).reindex e.symm := by
  ext1
  simp [conj_apply, ← Matrix.submatrix_mul_equiv (e₂ := .refl d)]

theorem reindex_eq_conj [DecidableEq d] (e : d ≃ d₂) : A.reindex e = A.conj (Matrix.reindex e (.refl d) 1) := by
  ext : 3
  simp [-mat_apply, reindex, conj_apply, Matrix.submatrix,
    Matrix.mul_apply, Matrix.one_apply]

variable [Fintype d₂] [DecidableEq d] [DecidableEq d₂]

theorem ker_reindex :
    (A.reindex e).ker = A.ker.comap (LinearEquiv.euclidean_of_relabel 𝕜 e) := by
  dsimp only [reindex, ker, lin]
  simp only [ContinuousLinearMap.ker_mk, mat_mk]
  rw [Matrix.reindex_toEuclideanLin, LinearEquiv.ker_comp, LinearMap.ker_comp]
  rfl

@[simp]
theorem ker_reindex_le_iff :
    (A.reindex e).ker ≤ (B.reindex e).ker ↔ A.ker ≤ B.ker := by
  rw [ker_reindex, ker_reindex]
  apply Submodule.comap_le_comap_iff_of_surjective
  exact LinearEquiv.surjective (LinearEquiv.euclidean_of_relabel 𝕜 e)

end HermitianMat
