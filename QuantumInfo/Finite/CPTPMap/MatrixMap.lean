import QuantumInfo.Finite.MState
import QuantumInfo.Finite.Unitary
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Module.LinearMap.Basic

/- This file works with `MatrixMap`s, that is, linear maps from square matrices to square matrices.
They can be represented as a transfer matrix themselves, so that multiplication of the transfer matrix
gives map composition; or as a Choi matrix, which is square and with a spectrum related to its Kraus operators.

We also prove basic facts about `MatrixMap.IsTracePreserving`.
-/

/-- A `MatrixMap` is a linear map between squares matrices of size A to size B, over R. -/
abbrev MatrixMap (A B R : Type*) [Semiring R] := Matrix A A R →ₗ[R] Matrix B B R

variable {A B C D E F R : Type*} [Fintype A] [Semiring R] [DecidableEq A]

namespace MatrixMap
section matrix

variable (A R) in
/-- Alias of LinearMap.id, but specifically as a MatrixMap. -/
def id : MatrixMap A A R := LinearMap.id

/-- Choi matrix of a given linear matrix map. Note that this is defined even for things that
  aren't CPTP, it's just rarely talked about in those contexts. This is the inverse of
  `MatrixMap.of_choi_matrix`. Compare with `MatrixMap.toMatrix`, which gives the transfer matrix. -/
def choi_matrix (M : MatrixMap A B R) : Matrix (A × B) (A × B) R :=
  fun (i₁,j₁) (i₂,j₂) ↦ M (Matrix.stdBasisMatrix i₁ i₂ 1) j₁ j₂

/-- Given the Choi matrix, generate the corresponding R-linear map between matrices as a
MatrixMap. This is the inverse of `MatrixMap.choi_matrix`. -/
def of_choi_matrix (M : Matrix (A × B) (A × B) R) : MatrixMap A B R where
  toFun X := fun b₁ b₂ ↦ ∑ (a₁ : A), ∑ (a₂ : A), X a₁ a₂ * M (a₁, b₁) (a₂, b₂)
  map_add' x y := by funext b₁ b₂; simp [add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    funext b₁ b₂
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

/-- Proves that `MatrixMap.of_choi_matrix` and `MatrixMap.choi_matrix` inverses. -/
@[simp]
theorem map_choi_inv (M : Matrix (A × B) (A × B) R) : choi_matrix (of_choi_matrix M) = M := by
  ext ⟨i₁,i₂⟩ ⟨j₁,j₂⟩
  simp [of_choi_matrix, choi_matrix, Matrix.stdBasisMatrix, ite_and]

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

section kron
open Kronecker

variable {A B C D R : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
variable [DecidableEq A] [DecidableEq C]

/-- The Kronecker product of MatrixMaps. Defined here using `TensorProduct.map M₁ M₂`, with appropriate
reindexing operations and `LinearMap.toMatrix`/`Matrix.toLin`. Notation `⊗ₖₘ`. -/
noncomputable def kron [CommSemiring R] (M₁ : MatrixMap A B R) (M₂ : MatrixMap C D R) : MatrixMap (A × C) (B × D) R :=
  let h₁ := (LinearMap.toMatrix (Basis.tensorProduct (Matrix.stdBasis R A A) (Matrix.stdBasis R C C))
      (Basis.tensorProduct (Matrix.stdBasis R B B) (Matrix.stdBasis R D D)))
    (TensorProduct.map M₁ M₂);
  let r₁ := Equiv.prodProdProdComm B B D D;
  let r₂ := Equiv.prodProdProdComm A A C C;
  let h₂ := Matrix.reindex r₁ r₂ h₁;
  Matrix.toLin (Matrix.stdBasis R (A × C) (A × C)) (Matrix.stdBasis R (B × D) (B × D)) h₂

scoped[MatrixMap] infixl:100 " ⊗ₖₘ " => MatrixMap.kron

/-- The extensional definition of the Kronecker product `MatrixMap.kron`, in terms of the entries of its image. -/
theorem kron_def [CommRing R] (M₁ : MatrixMap A B R) (M₂ : MatrixMap C D R) (M : Matrix (A × C) (A × C) R) : (M₁ ⊗ₖₘ M₂) M (b₁, d₁) (b₂, d₂) =
  ∑ a₁, ∑ a₂, ∑ c₁, ∑ c₂, (M₁ (Matrix.stdBasisMatrix a₁ a₂ 1) b₁ b₂) * (M₂ (Matrix.stdBasisMatrix c₁ c₂ 1) d₁ d₂) * (M (a₁, c₁) (a₂, c₂)) := by
  rw [kron, TensorProduct.toMatrix_map]
  simp
  rw [Matrix.toLin_apply]
  simp [Equiv.prodProdProdComm, Matrix.kroneckerMap, Matrix.submatrix, LinearMap.toMatrix]
  simp [Matrix.stdBasis_eq_stdBasisMatrix]
  sorry

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

variable [CommRing R] {Dl₁ Dl₂ Dl₃ Dr₁ Dr₂ Dr₃ : Type*}
  [Fintype Dl₁] [Fintype Dl₂] [Fintype Dl₃] [Fintype Dr₁] [Fintype Dr₂] [Fintype Dr₃]
  [DecidableEq Dl₁] [DecidableEq Dl₂] [DecidableEq Dr₁] [DecidableEq Dr₂] in
/-- For maps L₁, L₂, R₁, and R₂, the product (L₂ ∘ₗ L₁) ⊗ₖₘ (R₂ ∘ₗ R₁) = (L₂ ⊗ₖₘ R₂) ∘ₗ (L₁ ⊗ₖₘ R₁) -/
theorem kron_comp_distrib (L₁ : MatrixMap Dl₁ Dl₂ R) (L₂ : MatrixMap Dl₂ Dl₃ R) (R₁ : MatrixMap Dr₁ Dr₂ R)
    (R₂ : MatrixMap Dr₂ Dr₃ R) : (L₂ ∘ₗ L₁) ⊗ₖₘ (R₂ ∘ₗ R₁) = (L₂ ⊗ₖₘ R₂) ∘ₗ (L₁ ⊗ₖₘ R₁) := by
  sorry

end kron

section trace_preserving

variable [Fintype B] [Fintype C]

/-- A linear matrix map is *trace preserving* if trace of the output equals trace of the input. -/
def IsTracePreserving (M : MatrixMap A B R) : Prop :=
  ∀ (x : Matrix A A R), (M x).trace = x.trace

/-- A map is trace preserving iff the partial trace of the Choi matrix is the identity. -/
theorem IsTracePreserving_iff_trace_choi (M : MatrixMap A B R) : M.IsTracePreserving
    ↔ M.choi_matrix.trace_right = 1 := by
  constructor
  · intro h
    ext a₁ a₂
    replace h := h (Matrix.stdBasisMatrix a₁ a₂ 1)
    simp_rw [Matrix.trace, Matrix.diag] at h
    simp [choi_matrix, Matrix.trace_right, h, Matrix.stdBasisMatrix, Matrix.one_apply]
    have : (fun x => a₁ = x ∧ a₂ = x) = (fun x => a₁ = a₂ ∧ a₂ = x) := by
      funext x
      rw [eq_iff_iff, and_congr_left_iff]
      rintro rfl
      trivial
    split_ifs with h
    <;> simp [this, h, Finset.filter_eq]
  · intro h X
    replace h := fun (a₁ a₂ : A) ↦ congrFun₂ h a₁ a₂
    simp [Matrix.trace_right, Matrix.trace] at h ⊢
    rw [← M.choi_map_inv, of_choi_matrix]
    dsimp
    rw [Finset.sum_comm_3, Finset.sum_comm_3]
    simp_rw [← Finset.mul_sum, h, Matrix.one_apply]
    simp

namespace IsTracePreserving

variable {A : Type*} [Fintype A] in
/-- Simp lemma: the trace of the image of a IsTracePreserving map is the same as the original trace. -/
@[simp]
theorem apply_trace {M : MatrixMap A B R} (h : M.IsTracePreserving) (ρ : Matrix A A R)
    : (M ρ).trace = ρ.trace :=
  h ρ

/-- The trace of a Choi matrix of a TP map is the cardinality of the input space. -/
theorem trace_choi {M : MatrixMap A B R} (h : M.IsTracePreserving) :
    M.choi_matrix.trace = (Finset.univ (α := A)).card := by
  rw [← Matrix.trace_of_trace_right, (IsTracePreserving_iff_trace_choi M).mp h,
    Matrix.trace_one, Finset.card_univ]

variable {A : Type*} [Fintype A] in
/-- The composotion of IsTracePreserving maps is also trace preserving. -/
theorem comp {M₁ : MatrixMap A B R} {M₂ : MatrixMap B C R} (h₁ : M₁.IsTracePreserving) (h₂ : M₂.IsTracePreserving) :
    IsTracePreserving (M₂ ∘ₗ M₁) := by
  intro x
  simp [h₂ _, h₁ _]

variable {A : Type*} [Fintype A] in
/-- The identity MatrixMap IsTracePreserving. -/
theorem id : (id A R).IsTracePreserving := by
  simp [IsTracePreserving, MatrixMap.id]

variable {A R : Type*} [CommSemiring R] [Fintype A] in
/-- Unit linear combinations of IsTracePreserving maps are IsTracePreserving. -/
theorem unit_linear {M₁ M₂ : MatrixMap A B R} {x y : R}
    (h₁ : M₁.IsTracePreserving) (h₂ : M₂.IsTracePreserving) (hxy : x + y = 1) :
    (x • M₁ + y • M₂).IsTracePreserving := by
  rw [IsTracePreserving] at h₁ h₂ ⊢
  simp [h₁, h₂, ← add_mul, hxy]

variable {D R : Type*} [CommSemiring R] [DecidableEq C] [Fintype D] in
/-- The kronecker product of IsTracePreserving maps is also trace preserving. -/
theorem kron {M₁ : MatrixMap A B R} {M₂ : MatrixMap C D R} (h₁ : M₁.IsTracePreserving) (h₂ : M₂.IsTracePreserving) :
    (M₁ ⊗ₖₘ M₂).IsTracePreserving := by
  sorry

end IsTracePreserving
end trace_preserving