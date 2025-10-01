import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Module.LinearMap.Basic
import QuantumInfo.ForMathlib
import QuantumInfo.Finite.Braket
import QuantumInfo.Finite.MState

/-! # Linear maps of matrices

This file works with `MatrixMap`s, that is, linear maps from square matrices to square matrices.
Although this is just a shorthand for `Matrix A A R →ₗ[R] Matrix B B R`, there are several
concepts that specifically make sense in this context.

 * `toMatrix` is the rectangular "transfer matrix", where matrix multiplication commutes with map composition.
 * `choi_matrix` is the square "Choi matrix", see `MatrixMap.choi_PSD_iff_CP_map` for example usage
 * `kron` is the Kronecker product of matrix maps
 * `IsTracePreserving` states the trace of the output is always equal to the trace of the input.

We provide simp lemmas for relating these facts, prove basic facts e.g. composition and identity, and some facts
about `IsTracePreserving` maps.
-/

/-- A `MatrixMap` is a linear map between squares matrices of size A to size B, over R. -/
abbrev MatrixMap (A B R : Type*) [Semiring R] := Matrix A A R →ₗ[R] Matrix B B R

variable {A B C D E F R R₂ : Type*} [Fintype A] [Semiring R] [DecidableEq A] [CommSemiring R₂]

namespace MatrixMap
section matrix

variable (A R) in
/-- Alias of LinearMap.id, but specifically as a MatrixMap. -/
@[reducible]
def id : MatrixMap A A R := LinearMap.id

/-- Choi matrix of a given linear matrix map. Note that this is defined even for things that
  aren't CPTP, it's just rarely talked about in those contexts. This is the inverse of
  `MatrixMap.of_choi_matrix`. Compare with `MatrixMap.toMatrix`, which gives the transfer matrix. -/
def choi_matrix (M : MatrixMap A B R) : Matrix (B × A) (B × A) R :=
  fun (j₁,i₁) (j₂,i₂) ↦ M (Matrix.single i₁ i₂ 1) j₁ j₂

/-- Given the Choi matrix, generate the corresponding R-linear map between matrices as a
MatrixMap. This is the inverse of `MatrixMap.choi_matrix`. -/
def of_choi_matrix (M : Matrix (B × A) (B × A) R) : MatrixMap A B R where
  toFun X := fun b₁ b₂ ↦ ∑ (a₁ : A), ∑ (a₂ : A), X a₁ a₂ * M (b₁, a₁) (b₂, a₂)
  map_add' x y := by funext b₁ b₂; simp [add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    funext b₁ b₂
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

/-- Proves that `MatrixMap.of_choi_matrix` and `MatrixMap.choi_matrix` inverses. -/
@[simp]
theorem map_choi_inv (M : Matrix (B × A) (B × A) R) : choi_matrix (of_choi_matrix M) = M := by
  ext ⟨i₁,i₂⟩ ⟨j₁,j₂⟩
  simp [of_choi_matrix, choi_matrix, Matrix.single, ite_and]

/-- Proves that `MatrixMap.choi_matrix` and `MatrixMap.of_choi_matrix` inverses. -/
@[simp]
theorem choi_map_inv (M : MatrixMap A B R) : of_choi_matrix (choi_matrix M) = M := by
  -- By definition of `MatrixMap.of_choi_matrix`, we know that applying it to the Choi matrix of `M` reconstructs `M`.
  ext X b₁ b₂; simp [MatrixMap.of_choi_matrix, MatrixMap.choi_matrix];
  -- By linearity of $M$, we can distribute $M$ over the sum.
  have h_linear : M X = ∑ x : A, ∑ x_1 : A, X x x_1 • M (Matrix.single x x_1 1) := by
    have h_linear : M X = M (∑ x : A, ∑ x_1 : A, X x x_1 • Matrix.single x x_1 1) := by
      congr with i j ; simp ( config := { decide := Bool.true } ) [ Matrix.sum_apply ];
      simp ( config := { decide := Bool.true } ) [ Matrix.single ];
      rw [ Finset.sum_eq_single i ] <;> aesop;
    simp +decide only [h_linear, map_sum, LinearMap.map_smulₛₗ];
    simp +zetaDelta at *;
  -- By linearity of $M$, we can distribute $M$ over the sum and then apply it to each term.
  simp [h_linear, Matrix.sum_apply]

/-- The linear equivalence between linear maps of matrices,and Choi matrices.-/
@[simps]
def choi_equiv : MatrixMap A B R₂ ≃ₗ[R₂] Matrix (B × A) (B × A) R₂ where
  toFun := choi_matrix
  invFun := of_choi_matrix
  left_inv _ := by simp
  right_inv _ := by simp
  map_add' _ _ := by ext; simp [choi_matrix]
  map_smul' _ _ := by ext; simp [choi_matrix]

/-- The correspondence induced by `MatrixMap.of_choi_matrix` is injective. -/
theorem choi_matrix_inj : Function.Injective (@choi_matrix A B R _ _) := by
  intro _ _ h
  simpa only [choi_map_inv] using congrArg of_choi_matrix h

variable {R : Type*} [CommSemiring R]

/-- The linear equivalence between MatrixMap's and transfer matrices on a larger space.
Compare with `MatrixMap.choi_matrix`, which gives the Choi matrix instead of the transfer matrix. -/
noncomputable def toMatrix [Fintype B] : MatrixMap A B R ≃ₗ[R] Matrix (B × B) (A × A) R :=
  LinearMap.toMatrix (Matrix.stdBasis R A A) (Matrix.stdBasis R B B)

/-- Multiplication of transfer matrices, `MatrixMap.toMatrix`, is equivalent to composition of maps. -/
theorem toMatrix_comp [Fintype B] [Fintype C] [DecidableEq B] (M₁ : MatrixMap A B R) (M₂ : MatrixMap B C R) : toMatrix (M₂ ∘ₗ M₁) = (toMatrix M₂) * (toMatrix M₁) :=
  LinearMap.toMatrix_comp _ _ _ M₂ M₁

end matrix

section kraus

variable [SMulCommClass R R R] [Star R]
variable {κ : Type*} [Fintype κ]

/-- Construct a matrix map out of families of matrices M N : Σ → Matrix B A R
indexed by κ via X ↦ ∑ k : κ, (M k) * X * (N k)ᴴ -/
def of_kraus (M N : κ → Matrix B A R) : MatrixMap A B R :=
  ∑ k : κ, {
    toFun X := M k * X * (N k).conjTranspose
    map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
    map_smul' r x := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]
  }

end kraus

section kron
open Kronecker

variable {A B C D R : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
variable [DecidableEq A] [DecidableEq C]

/-- The Kronecker product of MatrixMaps. Defined here using `TensorProduct.map M₁ M₂`, with appropriate
reindexing operations and `LinearMap.toMatrix`/`Matrix.toLin`. Notation `⊗ₖₘ`. -/
noncomputable def kron [CommSemiring R] (M₁ : MatrixMap A B R) (M₂ : MatrixMap C D R) : MatrixMap (A × C) (B × D) R :=
  let h₁ := (LinearMap.toMatrix (Module.Basis.tensorProduct  (Matrix.stdBasis R A A) (Matrix.stdBasis R C C))
      (Module.Basis.tensorProduct  (Matrix.stdBasis R B B) (Matrix.stdBasis R D D)))
    (TensorProduct.map M₁ M₂);
  let r₁ := Equiv.prodProdProdComm B B D D;
  let r₂ := Equiv.prodProdProdComm A A C C;
  let h₂ := Matrix.reindex r₁ r₂ h₁;
  Matrix.toLin (Matrix.stdBasis R (A × C) (A × C)) (Matrix.stdBasis R (B × D) (B × D)) h₂

scoped[MatrixMap] infixl:100 " ⊗ₖₘ " => MatrixMap.kron

set_option maxHeartbeats 400000 in
/-- The extensional definition of the Kronecker product `MatrixMap.kron`, in terms of the entries of its image. -/
theorem kron_def [CommSemiring R] (M₁ : MatrixMap A B R) (M₂ : MatrixMap C D R) (M : Matrix (A × C) (A × C) R) :
    (M₁ ⊗ₖₘ M₂) M (b₁, d₁) (b₂, d₂) = ∑ a₁, ∑ a₂, ∑ c₁, ∑ c₂,
      (M₁ (Matrix.single a₁ a₂ 1) b₁ b₂) * (M₂ (Matrix.single c₁ c₂ 1) d₁ d₂) * (M (a₁, c₁) (a₂, c₂)) := by
  rw [kron]
  have h_expand : (Matrix.toLin (Matrix.stdBasis R (A × C) (A × C)) (Matrix.stdBasis R (B × D) (B × D))) ((Matrix.reindex (Equiv.prodProdProdComm B B D D) (Equiv.prodProdProdComm A A C C)) ((LinearMap.toMatrix ((Matrix.stdBasis R A A).tensorProduct (Matrix.stdBasis R C C)) ((Matrix.stdBasis R B B).tensorProduct (Matrix.stdBasis R D D))) (TensorProduct.map M₁ M₂))) M = ∑ a₁ : A, ∑ a₂ : A, ∑ c₁ : C, ∑ c₂ : C, M (a₁, c₁) (a₂, c₂) • (Matrix.toLin (Matrix.stdBasis R (A × C) (A × C)) (Matrix.stdBasis R (B × D) (B × D))) ((Matrix.reindex (Equiv.prodProdProdComm B B D D) (Equiv.prodProdProdComm A A C C)) ((LinearMap.toMatrix ((Matrix.stdBasis R A A).tensorProduct (Matrix.stdBasis R C C)) ((Matrix.stdBasis R B B).tensorProduct (Matrix.stdBasis R D D))) (TensorProduct.map M₁ M₂))) (Matrix.single (a₁, c₁) (a₂, c₂) 1) := by
    have h_expand : M = ∑ a₁ : A, ∑ a₂ : A, ∑ c₁ : C, ∑ c₂ : C, M (a₁, c₁) (a₂, c₂) • Matrix.single (a₁, c₁) (a₂, c₂) 1 := by
      ext ⟨a₁, c₁⟩ ⟨a₂, c₂⟩
      simp only [Matrix.single, Matrix.sum_apply]
      rw [Finset.sum_eq_single a₁, Finset.sum_eq_single a₂, Finset.sum_eq_single c₁, Finset.sum_eq_single c₂]
      <;> simp +contextual
    nth_rw 1 [h_expand]
    simp only [map_sum, LinearMap.map_smulₛₗ]
    rfl
  rw [h_expand]
  clear h_expand
  simp only [Matrix.sum_apply]
  congr! 8 with a₁ _ a₂ _ c₁ _ c₂ _
  rw [Matrix.smul_apply, smul_eq_mul, mul_comm]
  congr
  classical
  simp only [Matrix.stdBasis,
    Matrix.reindex_apply, Equiv.prodProdProdComm_symm, Matrix.toLin_apply,
    Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Equiv.prodProdProdComm_apply, LinearMap.toMatrix_apply,
    Module.Basis.tensorProduct_apply, Module.Basis.map_apply, Module.Basis.coe_reindex, Function.comp_apply,
    Equiv.sigmaEquivProd_symm_apply, Pi.basis_apply, Pi.basisFun_apply, Matrix.coe_ofLinearEquiv, TensorProduct.map_tmul,
    Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.map_repr, LinearEquiv.trans_apply, Matrix.coe_ofLinearEquiv_symm,
    Module.Basis.repr_reindex, Finsupp.mapDomain_equiv_apply, Pi.basis_repr, Pi.basisFun_repr, Matrix.of_symm_apply, smul_eq_mul,
    Matrix.of_symm_single, Pi.single_apply, Matrix.smul_of, Matrix.sum_apply, Matrix.of_apply, Pi.smul_apply]
  rw [ Finset.sum_eq_single ( ( b₁, d₁ ), ( b₂, d₂ ) ) ]
  · rw [ Finset.sum_eq_single ( ( a₁, c₁ ), ( a₂, c₂ ) ) ]
    · simp only [↓reduceIte, Pi.single_eq_same, mul_one]
      rw [ mul_comm ]
      congr! 2
      · ext i j
        by_cases hi : i = a₁
        <;> by_cases hj : j = a₂
        <;> simp only [hi, hj, Matrix.of_apply, ne_eq, not_false_eq_true, Pi.single_eq_of_ne,
              Pi.single_eq_same, Pi.zero_apply, Matrix.single]
        <;> grind only
      · ext i j
        by_cases hi : i = c₁
        <;> by_cases hj : j = c₂
        <;> simp only [hi, hj, Matrix.of_apply, ne_eq, not_false_eq_true, Pi.single_eq_of_ne,
              Pi.single_eq_same, Pi.zero_apply, Matrix.single]
        <;> grind only
    · intros
      split
      · grind [Prod.mk.injEq, Pi.single_eq_of_ne, mul_zero]
      · simp
    · simp
  · simp only [Finset.mem_univ, ne_eq, forall_const, Prod.forall, Prod.mk.injEq, not_and, and_imp]
    intro a b c d h
    split_ifs
    · simp_all
    · simp
  · simp

section kron_lemmas
variable [CommSemiring R]

theorem add_kron (ML₁ ML₂ : MatrixMap A B R) (MR : MatrixMap C D R) : (ML₁ + ML₂) ⊗ₖₘ MR = ML₁ ⊗ₖₘ MR + ML₂ ⊗ₖₘ MR := by
  simp [kron, TensorProduct.map_add_left, Matrix.submatrix_add]

theorem kron_add (ML : MatrixMap A B R) (MR₁ MR₂ : MatrixMap C D R) : ML ⊗ₖₘ (MR₁ + MR₂) = ML ⊗ₖₘ MR₁ + ML ⊗ₖₘ  MR₂ := by
  simp [kron, TensorProduct.map_add_right, Matrix.submatrix_add]

theorem smul_kron (r : R) (ML : MatrixMap A B R) (MR : MatrixMap C D R) : (r • ML) ⊗ₖₘ MR = r • (ML ⊗ₖₘ MR) := by
  simp [kron, TensorProduct.map_smul_left, Matrix.submatrix_smul]

theorem kron_smul (r : R) (ML : MatrixMap A B R) (MR : MatrixMap C D R) : ML ⊗ₖₘ (r • MR) = r • (ML ⊗ₖₘ MR) := by
  simp [kron, TensorProduct.map_smul_right, Matrix.submatrix_smul]

@[simp]
theorem zero_kron (MR : MatrixMap C D R) : (0 : MatrixMap A B R) ⊗ₖₘ MR = 0 := by
  simp [kron]

@[simp]
theorem kron_zero (ML : MatrixMap A B R) : ML ⊗ₖₘ (0 : MatrixMap C D R) = 0 := by
  simp [kron]

variable [DecidableEq B] in
theorem kron_id_id : (id A R ⊗ₖₘ id B R) = id (A × B) R := by
  simp [kron]

variable {Dl₁ Dl₂ Dl₃ Dr₁ Dr₂ Dr₃ : Type*}
  [Fintype Dl₁] [Fintype Dl₂] [Fintype Dl₃] [Fintype Dr₁] [Fintype Dr₂] [Fintype Dr₃]
  [DecidableEq Dl₁] [DecidableEq Dl₂] [DecidableEq Dr₁] [DecidableEq Dr₂] in
/-- For maps L₁, L₂, R₁, and R₂, the product (L₂ ∘ₗ L₁) ⊗ₖₘ (R₂ ∘ₗ R₁) = (L₂ ⊗ₖₘ R₂) ∘ₗ (L₁ ⊗ₖₘ R₁) -/
theorem kron_comp_distrib (L₁ : MatrixMap Dl₁ Dl₂ R) (L₂ : MatrixMap Dl₂ Dl₃ R) (R₁ : MatrixMap Dr₁ Dr₂ R)
    (R₂ : MatrixMap Dr₂ Dr₃ R) : (L₂ ∘ₗ L₁) ⊗ₖₘ (R₂ ∘ₗ R₁) = (L₂ ⊗ₖₘ R₂) ∘ₗ (L₁ ⊗ₖₘ R₁) := by
  simp [kron, TensorProduct.map_comp, ← Matrix.toLin_mul, Matrix.submatrix_mul_equiv, ← LinearMap.toMatrix_comp]

end kron_lemmas

end kron
