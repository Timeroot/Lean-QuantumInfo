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

variable {A B C D E F R : Type*} [Fintype A] [Semiring R] [DecidableEq A]

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
  sorry

/-- The correspondence induced by `MatrixMap.of_choi_matrix` is injective. -/
theorem choi_matrix_inj : Function.Injective (@choi_matrix A B R _ _) := by
  intro x y h
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

def exists_kraus (Φ : MatrixMap A B R) : ∃ r : ℕ, ∃ (M N : Fin r → Matrix B A R), Φ = of_kraus M N :=
  sorry

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

-- /-- The canonical tensor product on linear maps between matrices, where a map from
--   M[A,B] to M[C,D] is given by M[A×C,B×D]. This tensor product acts independently on
--   Kronecker products and gives Kronecker products as outputs. -/
-- def matrixMap_kron (M₁ : Matrix (A₁ × B₁) (C₁ × D₁) R) (M₂ : Matrix (A₂ × B₂) (C₂ × D₂) R) : Matrix ((A₁ × A₂) × (B₁ × B₂)) ((C₁ × C₂) × (D₁ × D₂)) R :=
--   Matrix.of fun ((a₁, a₂), (b₁, b₂)) ((c₁, c₂), (d₁, d₂)) ↦
--     (M₁ (a₁, b₁) (c₁, d₁)) * (M₂ (a₂, b₂) (c₂, d₂))

/-- The operational definition of the Kronecker product `MatrixMap.kron`, that it maps a Kronecker product of
inputs to the Kronecker product of outputs. It is the unique bilinear map doing so. -/
theorem kron_map_of_kron_state [CommRing R] (M₁ : MatrixMap A B R) (M₂ : MatrixMap C D R) (MA : Matrix A A R) (MC : Matrix C C R) : (M₁ ⊗ₖₘ M₂) (MA ⊗ₖ MC) = (M₁ MA) ⊗ₖ (M₂ MC) := by
  ext bd₁ bd₂
  let (b₁, d₁) := bd₁
  let (b₂, d₂) := bd₂
  rw [kron_def]
  simp only [Matrix.kroneckerMap_apply]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  simp_rw [mul_comm (M₂ _ _ _), mul_assoc, ← Finset.mul_sum, ← mul_assoc]
  simp_rw [← Finset.sum_mul]
  congr
  -- simp_rw [← Matrix.stdBasis_eq_stdBasisMatrix ]
  -- unfold Matrix.stdBasisMatrix
  -- simp_rw [← LinearMap.sum_apply]
  -- simp
  sorry
  sorry

theorem choi_matrix_state_rep {B : Type*} [Fintype B] [Nonempty A] (M : MatrixMap A B ℂ) :
  M.choi_matrix = (↑(Fintype.card (α := A)) : ℂ) • (M ⊗ₖₘ (LinearMap.id : MatrixMap A A ℂ)) (MState.pure (Ket.MES A)).m := by
  ext i j
  simp [choi_matrix, kron_def M, Ket.MES, Ket.apply, Finset.mul_sum]
  conv =>
    rhs
    conv =>
      enter [2, x, 2, a_1]
      conv =>
        enter [2, a_2]
        simp [apply_ite]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      rw [← mul_inv, ← Complex.ofReal_mul, ← Real.sqrt_mul (Fintype.card A).cast_nonneg',
        Real.sqrt_mul_self (Fintype.card A).cast_nonneg', mul_comm, mul_assoc]
      simp
      conv =>
        right
        rw [Matrix.single, Matrix.of_apply]
        enter [1]
        rw [and_comm]
      simp [apply_ite, ite_and]
    conv =>
      enter [2, x]
      simp [Finset.sum_ite]
    simp [Finset.sum_ite]

end kron

section pi
section basis

--Missing from Mathlib

variable {ι : Type*}
variable {R : Type*} [CommSemiring R]
variable {s : ι → Type*} [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]
variable {L : ι → Type* }

/-- Like `Basis.tensorProduct`, but for `PiTensorProduct` -/
noncomputable def _root_.Module.Basis.piTensorProduct [∀i, Fintype (L i)]
    (b : (i:ι) → Module.Basis (L i) R (s i)) :
      Module.Basis ((i:ι) → L i) R (PiTensorProduct R s) :=
  Finsupp.basisSingleOne.map sorry

end basis

variable {R : Type*} [CommSemiring R]
variable {ι : Type u} [DecidableEq ι] [fι : Fintype ι]
variable {dI : ι → Type v} [∀i, Fintype (dI i)] [∀i, DecidableEq (dI i)]
variable {dO : ι → Type w} [∀i, Fintype (dO i)] [∀i, DecidableEq (dO i)]

/-- Finite Pi-type tensor product of MatrixMaps. Defined as `PiTensorProduct.tprod` of the underlying
Linear maps. Notation `⨂ₜₘ[R] i, f i`, eventually. -/
noncomputable def piKron (Λi : ∀ i, MatrixMap (dI i) (dO i) R) : MatrixMap (∀i, dI i) (∀i, dO i) R :=
  let map₁ := PiTensorProduct.map Λi;
  let map₂ := LinearMap.toMatrix
    (Module.Basis.piTensorProduct (fun i ↦ Matrix.stdBasis R (dI i) (dI i)))
    (Module.Basis.piTensorProduct (fun i ↦ Matrix.stdBasis R (dO i) (dO i))) map₁
  let r₁ : ((i : ι) → dO i × dO i) ≃ ((i : ι) → dO i) × ((i : ι) → dO i) := Equiv.arrowProdEquivProdArrow _ dO dO
  let r₂ : ((i : ι) → dI i × dI i) ≃ ((i : ι) → dI i) × ((i : ι) → dI i) := Equiv.arrowProdEquivProdArrow _ dI dI
  let map₃ := Matrix.reindex r₁ r₂ map₂;
  Matrix.toLin
    (Matrix.stdBasis R ((i:ι) → dI i) ((i:ι) → dI i))
    (Matrix.stdBasis R ((i:ι) → dO i) ((i:ι) → dO i)) map₃

-- notation3:100 "⨂ₜₘ "(...)", "r:(scoped f => tprod R f) => r
-- syntax (name := bigsum) "∑ " bigOpBinders ("with " term)? ", " term:67 : term

end pi
