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

@[simps]
def reindex (e : d ≃ d₂) : HermitianMat d₂ 𝕜 :=
  ⟨A.toMat.reindex e e, A.H.submatrix e.symm⟩

/-! Our simp-normal form for expressions involving `HermitianMat.reindex` is that we try to push
the reindexing as far out as possible, so that it can be absorbed by `HermitianMat.trace`, or
cancelled our in a `HermitianMat.inner`. In places where it commutes (like `HermitianMat.inner`)
we push it to the right side. -/

@[simp]
theorem reindex_refl (A : HermitianMat d ℂ) :
    A.reindex (.refl _) = A := by
  rfl

@[simp]
theorem reindex_reindex (A : HermitianMat d ℂ) (e : d ≃ d₂) (f : d₂ ≃ d₃) :
    (A.reindex e).reindex f = A.reindex (e.trans f) := by
  ext1; simp; rfl

@[simp]
theorem reindex_add :
    A.reindex e + B.reindex e = (A + B).reindex e := by
  simp [HermitianMat.ext_iff, Matrix.submatrix_add]

@[simp]
theorem reindex_sub  :
    A.reindex e - B.reindex e = (A - B).reindex e := by
  simp [HermitianMat.ext_iff, Matrix.submatrix_sub]

@[simp]
theorem reindex_conj [Fintype d₂] [Fintype d] (B : Matrix d₃ d₂ 𝕜) :
    (A.reindex e).conj B = A.conj (B.submatrix id e) := by
  ext1
  simp only [conj_apply, reindex_coe, Matrix.reindex_apply, mk_toMat]
  rw [← Matrix.submatrix_id_mul_right, Matrix.mul_assoc]
  rw [← Matrix.submatrix_id_mul_left, ← Matrix.mul_assoc]
  simp

variable [Fintype d]

@[simp]
theorem conj_submatrix (A : HermitianMat d ℂ) (B : Matrix d₂ d₄ ℂ)
  (e : d₃ ≃ d₂) (f : d → d₄) :
    A.conj (B.submatrix e f) = (A.conj (B.submatrix id f)).reindex e.symm := by
  ext1
  simp [conj_apply, ← Matrix.submatrix_mul_equiv (e₂ := .refl d)]

variable [Fintype d₂] [DecidableEq d] [DecidableEq d₂]

theorem ker_reindex :
    (A.reindex e).ker = A.ker.comap (LinearEquiv.euclidean_of_relabel 𝕜 e) := by
  dsimp only [reindex, ker, lin]
  simp only [ContinuousLinearMap.ker_mk, mk_toMat]
  rw [Matrix.reindex_toEuclideanLin, LinearEquiv.ker_comp, LinearMap.ker_comp]
  rfl

@[simp]
theorem ker_reindex_le_iff :
    (A.reindex e).ker ≤ (B.reindex e).ker ↔ A.ker ≤ B.ker := by
  rw [ker_reindex, ker_reindex]
  apply Submodule.comap_le_comap_iff_of_surjective
  exact LinearEquiv.surjective (LinearEquiv.euclidean_of_relabel 𝕜 e)

end HermitianMat
