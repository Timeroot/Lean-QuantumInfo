import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef

/- This file is generically useful / missing lemmas that "could" be in Mathlib, but
aren't. They concern things like, basic facts about positive semidefinite matrices (that
aren't otherwise quantum-related).
-/

namespace MeasureTheory

-- import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
-- /-- A measure on a type T induces a natural (product) measure on finite lists of T's. -/
-- instance instMeasurableList (T : Type*) [MeasurableSpace T] : MeasurableSpace (List T) where
--   MeasurableSet' := sorry
--   measurableSet_empty := sorry
--   measurableSet_compl := sorry
--   measurableSet_iUnion := sorry

end MeasureTheory

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

variable {m n 𝕜 : Type*}
variable [Fintype m] [Fintype n]
variable [RCLike 𝕜] [DecidableEq n] [DecidableEq m]

variable {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}

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

theorem diag_nonneg (hA : A.PosSemidef) : ∀i, 0 ≤ A.diag i := by
  intro i
  simpa [Matrix.mulVec, Matrix.dotProduct] using hA.2 (fun j ↦ if i = j then 1 else 0)

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

end PosSemidef

noncomputable section traceNorm

open scoped ComplexOrder

variable {m n R : Type*}
variable [Fintype m] [Fintype n]
variable [RCLike R] [DecidableEq n] [DecidableEq m]

/-- The trace norm of a matrix: Tr[√(A† A)]. -/
def traceNorm (A : Matrix m n R) : ℝ :=
  RCLike.re A.posSemidef_conjTranspose_mul_self.sqrt.trace

/-- The trace norm of the negative is equal to the trace norm. -/
theorem traceNorm_eq_self_neg (A : Matrix m n R) : traceNorm (-A) = traceNorm A := by
  unfold traceNorm
  congr! 3
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg]
  exact neg_neg _

--More generally sum of abs of singular values.
--Proposition 9.1.1 in Wilde
theorem traceNorm_Hermitian_eq_sum_abs_eigenvalues {A : Matrix n n R} (hA : A.IsHermitian) :
    A.traceNorm = ∑ i, abs (hA.eigenvalues i) :=
  sorry --Diagonalize A

/-- The trace norm is nonnegative. Property 9.1.1 in Wilde -/
theorem traceNorm_nonneg (A : Matrix m n R) : 0 ≤ A.traceNorm := by
  unfold traceNorm
  have : 0 ≤ A.posSemidef_conjTranspose_mul_self.sqrt.trace := by
    rw [Matrix.trace]
    apply Finset.sum_nonneg
    simp_rw [Finset.mem_univ, forall_true_left]
    exact A.posSemidef_conjTranspose_mul_self.posSemidef_sqrt.diag_nonneg
  exact And.left $ RCLike.nonneg_iff.1 this

/-- The trace norm is zero only if the matrix is zero. -/
theorem traceNorm_zero_iff (A : Matrix m n R) : A.traceNorm = 0 ↔ A = 0 := by
  constructor
  · intro h
    have h₂ : ∀ i, A.posSemidef_conjTranspose_mul_self.posSemidef_sqrt.1.eigenvalues i = 0 :=
      sorry --sum of nonnegative values to zero
    have h₃ : A.posSemidef_conjTranspose_mul_self.sqrt = 0 :=
      sorry --all eigenvalues are zero iff matrix is zero
    have h₄ : Aᴴ * A = 0 :=
      sorry --sqrt is zero iff matrix is zero
    have h₅ : A = 0 :=
      sorry --conj_mul_self is zero iff A is zero
    exact h₅
  · intro hA
    subst hA
    have : (0 : Matrix m n R)ᴴ * (0 : Matrix m n R) = 0 := by simp
    rw [traceNorm, PosSemidef.sqrt_eq this _ Matrix.PosSemidef.zero]
    simp

  -- apply Finset.sum_nonneg
  --   simp_rw [Finset.mem_univ, forall_true_left]
  --   exact A.posSemidef_conjTranspose_mul_self.posSemidef_sqrt.diag_nonneg
  -- exact And.left $ RCLike.nonneg_iff.1 this

-- BACKPORT -- REMOVE LATER
@[simp]
lemma _root_.RCLike.ofReal_le_ofReal {K : Type*} [RCLike K] {x y : ℝ} : (x : K) ≤ (y : K) ↔ x ≤ y := by
  rw [RCLike.le_iff_re_im]
  simp

@[simp]
lemma _root_.RCLike.ofReal_nonneg {K : Type*} [RCLike K] {x : ℝ} : 0 ≤ (x : K) ↔ 0 ≤ x := by
  rw [← RCLike.ofReal_zero, RCLike.ofReal_le_ofReal]
-- END BACKPORT

/-- Trace norm is linear under scalar multiplication. Property 9.1.2 in Wilde -/
theorem traceNorm_smul (A : Matrix m n R) (c : R) : (c • A).traceNorm = ‖c‖ * A.traceNorm := by
  have h : (c • A)ᴴ * (c • A) = (‖c‖^2:R) • (Aᴴ * A) := by
    rw [conjTranspose_smul, RCLike.star_def, mul_smul, smul_mul, smul_smul]
    rw [RCLike.mul_conj c]
  rw [traceNorm, PosSemidef.sqrt_eq' h]
  have : RCLike.re (trace (‖c‖ • A.posSemidef_conjTranspose_mul_self.sqrt)) = ‖c‖ * traceNorm A := by
    simp [RCLike.smul_re]
    apply Or.inl
    rfl
  convert this
  rw [RCLike.real_smul_eq_coe_smul (K := R) ‖c‖]
  by_cases h : c = 0
  · nth_rewrite 8 [h]
    simp only [norm_zero, algebraMap.coe_zero, zero_smul]
    rw [← PosSemidef.sqrt_0]
    apply PosSemidef.sqrt_eq
    simp [h]
  · apply PosSemidef.sqrt_nonneg_smul _
    rw [RCLike.pos_iff_exists_ofReal]
    use ‖c‖
    simp [h]

end traceNorm

end Matrix


namespace LinearMap
section unitary

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

open Module.End

@[simp]
theorem unitary_star_apply_eq (U : unitary (E →ₗ[𝕜] E)) (v : E) :
    (star U.val) (U.val v) = v := by
  rw [← mul_apply, (unitary.mem_iff.mp U.prop).left, one_apply]

@[simp]
theorem unitary_apply_star_eq (U : unitary (E →ₗ[𝕜] E)) (v : E) :
    U.val ((star U.val) v) = v := by
  rw [← mul_apply, (unitary.mem_iff.mp U.prop).right, one_apply]

/-- Conjugating a linear map by a unitary operator gives a map whose μ-eigenspace is
  isomorphic (same dimension) as those of the original linear map. -/
noncomputable def conj_unitary_eigenspace_equiv (T : E →ₗ[𝕜] E) (U : unitary (E →ₗ[𝕜] E)) (μ : 𝕜) :
    eigenspace T μ ≃ₗ[𝕜] eigenspace (U.val * T * star (U.val)) μ := by
  constructor
  case toLinearMap =>
    constructor
    case toAddHom =>
      constructor
      case toFun =>
        rintro ⟨v,hv⟩
        use U.val v
        rw [mem_eigenspace_iff] at hv ⊢
        simp [mul_apply, hv]
      case map_add' =>
        intro x y
        simp
    intro m x
    simp
  case invFun =>
    rintro ⟨v,hv⟩
    use (star U.val) v
    rw [mem_eigenspace_iff] at hv ⊢
    simpa using congrArg ((star U.val) ·) hv
  case left_inv =>
    intro v
    simp
  case right_inv =>
    intro v
    simp


end unitary
namespace IsSymmetric

open Module.End

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)

/-- A symmetric operator conjugated by a unitary is symmetric. -/
theorem conj_unitary_IsSymmetric (U : unitary (E →ₗ[𝕜] E)) : (U.val * T * star U.val).IsSymmetric := by
  intro i j
  rw [mul_assoc, mul_apply, ← LinearMap.adjoint_inner_right]
  rw [mul_apply, mul_apply, mul_apply, ← LinearMap.adjoint_inner_left U.val]
  exact hT (star U.val <| i) (star U.val j)

variable {n : ℕ} (hn : FiniteDimensional.finrank 𝕜 E = n)

/-- There is an equivalence between the eigenvalues of a finite dimensional symmetric operator,
and the eigenvalues of that operator conjugated by a unitary. -/
def conj_unitary_eigenvalue_equiv (U : unitary (E →ₗ[𝕜] E)) : { σ : Equiv.Perm (Fin n) //
     (hT.conj_unitary_IsSymmetric U).eigenvalues hn = hT.eigenvalues hn ∘ σ } := by
  sorry --use conj_unitary_eigenspace_equiv

end IsSymmetric
end LinearMap
