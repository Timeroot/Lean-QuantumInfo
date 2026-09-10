/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazumi Kasaura, Hayata Yamasaki
-/

import QuantumLib.States.Qudit
import QuantumInfo.Channels.Bundled
import QuantumInfo.ForMathlib.PartialTrace
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Superoperators between qudits

A linear map between the operator algebras of two qudits is an `OpMap ℋ₁ ℋ₂`, and a quantum
channel is a `CPTPOp ℋ₁ ℋ₂`. This file collects the qudit-specific tools built on top of those.

* `Qudit` instances for tensor products and for `EuclideanSpace ℂ κ`.
* `outerProduct u v`, the rank-one operator `|v⟩⟨u|`.
* `matEquiv bE bF`, the matrix of an operator `ℋ₁ →L[ℂ] ℋ₂` in orthonormal bases of the source
  and the target. This is the rectangular counterpart of `StdBasis.toMatOf`, and it is what
  transports the Kraus theory of `MatrixMap` to operator maps: `krausTerm V` is conjugation
  `A ↦ V A V†`, `toMatOf_krausTerm` identifies its matrix with `MatrixMap.conj`, and
  `exists_kraus` is the Kraus decomposition of a completely positive `OpMap`.
* `isCompletelyPositive_add` and `isCompletelyPositive_smul`, closure of complete positivity under
  sums and nonnegative scalings, and `CPTPOp.convexComb`, the convex combination of two channels.
* `TrLeft` and `TrRight`, the partial traces, as bundled operator maps over
  `ContinuousLinearMap.traceLeft` and `ContinuousLinearMap.traceRight`.
* `opTensorEquiv : L (ℋ₁ ⊗[ℂ] ℋ₂) ≃ₗ[ℂ] L ℋ₁ ⊗[ℂ] L ℋ₂`, and `conjugateEnd` for transporting
  operators along an isomorphism of the underlying spaces.
* `krausToStinespringOperator`, the Stinespring operator of a Kraus family, and `trRight_kraus`,
  which recovers the channel from it.
-/

namespace QuantumChannel

open QuantumState TensorProduct
open scoped Matrix ComplexOrder

universe u v w

section Instances

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]

/-- A tensor product of qudits is a qudit. -/
noncomputable instance : Qudit (ℋ₁ ⊗[ℂ] ℋ₂) where
  toNormedAddCommGroup := inferInstance
  toInnerProductSpace := inferInstance
  fg_top := Module.Finite.fg_top

/-- `EuclideanSpace ℂ κ` is a qudit for finite `κ`; this is the concrete qudit the Kraus and
Stinespring constructions use for the environment. -/
noncomputable instance {κ : Type u} [Fintype κ] : Qudit (EuclideanSpace ℂ κ) where
  toNormedAddCommGroup := inferInstance
  toInnerProductSpace := inferInstance
  fg_top := Module.Finite.fg_top

end Instances

section OuterProduct

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]

/-- The rank-one operator `|v⟩⟨u| : x ↦ ⟪u, x⟫ • v`. See (1.57) of
<https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf>. -/
noncomputable abbrev outerProduct (u : ℋ₁) (v : ℋ₂) : ℋ₁ →L[ℂ] ℋ₂ :=
  InnerProductSpace.rankOne ℂ v u

/-- `|v⟩⟨u|` sends `x` to `⟪u, x⟫ • v`. -/
@[simp]
theorem outerProduct_apply (u : ℋ₁) (v : ℋ₂) (x : ℋ₁) :
    outerProduct u v x = (inner ℂ u x : ℂ) • v :=
  rfl

/-- The adjoint of `|v⟩⟨u|` is `|u⟩⟨v|`. -/
theorem adjoint_outerProduct (u : ℋ₁) (v : ℋ₂) : (outerProduct u v)† = outerProduct v u :=
  InnerProductSpace.adjoint_rankOne v u

/-- `|u⟩⟨u|` is positive. -/
theorem outerProduct_self_nonneg (u : ℋ₁) : 0 ≤ outerProduct u u :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (InnerProductSpace.isPositive_rankOne_self u)

/-- The outer product is bilinear, so it expands over sums in both arguments. -/
theorem outerProduct_sum {κ : Type*} [Fintype κ] (x y : κ → ℋ₁) :
    outerProduct (∑ a : κ, x a) (∑ a : κ, y a) =
      ∑ a : κ, ∑ b : κ, outerProduct (x a) (y b) := by
  refine ContinuousLinearMap.ext fun z ↦ ?_
  simp

/-- `|v⟩⟨u|` has trace `⟪u, v⟫`. -/
@[simp]
theorem trace_outerProduct {E : Type u} [Qudit E] (u v : E) : Tr (outerProduct u v) = inner ℂ u v :=
  InnerProductSpace.trace_rankOne v u

/-- Every operator is the sum of the rank-one operators `|T bᵢ⟩⟨bᵢ|` over an orthonormal basis. -/
theorem linearMap_eq_sum_outerProduct {E : Type u} [Qudit E] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (T : L E) : T = ∑ i : ι, outerProduct (b i) (T (b i)) := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  rw [sum_apply]
  conv_lhs => rw [← b.sum_repr' x]
  simp

/-- An operator with the same trace pairing as the identity *is* the identity. -/
theorem eq_one_of_Tr_mul {E : Type u} [Qudit E] {S : L E} (h : ∀ X : L E, Tr (S * X) = Tr X) :
    S = 1 := by
  refine ContinuousLinearMap.ext fun v ↦ ext_inner_left ℂ fun w ↦ ?_
  have hmul : S * outerProduct w v = outerProduct w (S v) :=
    ContinuousLinearMap.ext fun x ↦ by simp
  have hv := h (outerProduct w v)
  rw [hmul, trace_outerProduct, trace_outerProduct] at hv
  exact hv

end OuterProduct

section Matrices

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The matrix of an operator in given orthonormal bases of the source and the target. This is the
rectangular counterpart of `StdBasis.toMatOf`. -/
noncomputable def matEquiv (bE : OrthonormalBasis ι ℂ ℋ₁) (bF : OrthonormalBasis κ ℂ ℋ₂) :
    (ℋ₁ →L[ℂ] ℋ₂) ≃ₗ[ℂ] Matrix κ ι ℂ :=
  LinearMap.toContinuousLinearMap.symm ≪≫ₗ LinearMap.toMatrix bE.toBasis bF.toBasis

omit [DecidableEq κ] in
/-- The `(i, j)` entry of the matrix of `V` is `⟪bF i, V (bE j)⟫`. -/
@[simp]
theorem matEquiv_apply (bE : OrthonormalBasis ι ℂ ℋ₁) (bF : OrthonormalBasis κ ℂ ℋ₂)
    (V : ℋ₁ →L[ℂ] ℋ₂) (i : κ) (j : ι) : matEquiv bE bF V i j = inner ℂ (bF i) (V (bE j)) := by
  simp [matEquiv, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]

/-- Taking the adjoint of an operator conjugate-transposes its matrix. -/
theorem matEquiv_conjTranspose (bE : OrthonormalBasis ι ℂ ℋ₁) (bF : OrthonormalBasis κ ℂ ℋ₂)
    (V : ℋ₁ →L[ℂ] ℋ₂) : (matEquiv bE bF V)ᴴ = matEquiv bF bE (V†) := by
  ext i j
  rw [Matrix.conjTranspose_apply, matEquiv_apply, matEquiv_apply, RCLike.star_def, inner_conj_symm,
    ContinuousLinearMap.adjoint_inner_right]

/-- On a single space, read in one basis, `matEquiv` is `StdBasis.toMatOf`. -/
theorem matEquiv_self (b : OrthonormalBasis ι ℂ ℋ₁) (A : L ℋ₁) :
    matEquiv b b A = StdBasis.toMatOf b A := by
  ext i j
  rw [matEquiv_apply, StdBasis.toMatOf_apply]

end Matrices

section Kraus

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Conjugation by a single operator, `A ↦ V A V†`. Every completely positive map is a finite sum
of these; see `QuantumChannel.exists_kraus`. -/
noncomputable def krausTerm (V : ℋ₁ →L[ℂ] ℋ₂) : OpMap ℋ₁ ℋ₂ where
  toFun A := V ∘L A ∘L V†
  map_add' A B := by
    simp [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]
  map_smul' c A := by
    simp [ContinuousLinearMap.smul_comp]

/-- `krausTerm V` acts by `A ↦ V A V†`. -/
@[simp]
theorem krausTerm_apply (V : ℋ₁ →L[ℂ] ℋ₂) (A : L ℋ₁) : krausTerm V A = V ∘L A ∘L V† :=
  rfl

/-- The matrix representation of `krausTerm V` is conjugation by the matrix of `V`. -/
theorem toMatOf_krausTerm (bE : OrthonormalBasis ι ℂ ℋ₁) (bF : OrthonormalBasis κ ℂ ℋ₂)
    (V : ℋ₁ →L[ℂ] ℋ₂) :
    OpMap.toMatOf bE bF (krausTerm V) = MatrixMap.conj (matEquiv bE bF V) := by
  refine LinearMap.ext fun M ↦ ?_
  rw [OpMap.toMatOf_apply, MatrixMap.conj_apply]
  ext i j
  set A : L ℋ₁ := (StdBasis.toMatOf bE).symm M with hA
  have hM (k l : ι) : (inner ℂ (bE k) (A (bE l)) : ℂ) = M k l := by
    rw [hA, ← StdBasis.toMatOf_apply, StarAlgEquiv.apply_symm_apply]
  have hadj (l : ι) : (matEquiv bE bF V)ᴴ l j = inner ℂ (bE l) ((V†) (bF j)) := by
    rw [matEquiv_conjTranspose, matEquiv_apply]
  have hcol (l : ι) : (inner ℂ (bF i) (V (A (bE l))) : ℂ) = ∑ k, matEquiv bE bF V i k * M k l := by
    conv_lhs => rw [← bE.sum_repr' (A (bE l))]
    simp [hM, mul_comm]
  rw [StdBasis.toMatOf_apply, krausTerm_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  conv_lhs => rw [← bE.sum_repr' ((V†) (bF j))]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right, hcol]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  simp only [Matrix.mul_apply, hadj]
  rw [mul_comm]

/-- Passing to matrices commutes with finite sums of operator maps. -/
theorem toMatOf_sum {σ : Type*} (s : Finset σ) (Φ : σ → OpMap ℋ₁ ℋ₂)
    (bE : OrthonormalBasis ι ℂ ℋ₁) (bF : OrthonormalBasis κ ℂ ℋ₂) :
    OpMap.toMatOf bE bF (∑ r ∈ s, Φ r) = ∑ r ∈ s, OpMap.toMatOf bE bF (Φ r) :=
  map_sum (OpMap.matEquivOf bE bF) Φ s

/-- Passing to matrices commutes with addition of operator maps. -/
theorem toMatOf_add (Φ Ψ : OpMap ℋ₁ ℋ₂) (bE : OrthonormalBasis ι ℂ ℋ₁)
    (bF : OrthonormalBasis κ ℂ ℋ₂) :
    OpMap.toMatOf bE bF (Φ + Ψ) = OpMap.toMatOf bE bF Φ + OpMap.toMatOf bE bF Ψ :=
  map_add (OpMap.matEquivOf bE bF) Φ Ψ

/-- Passing to matrices commutes with scaling an operator map. -/
theorem toMatOf_smul (c : ℂ) (Φ : OpMap ℋ₁ ℋ₂) (bE : OrthonormalBasis ι ℂ ℋ₁)
    (bF : OrthonormalBasis κ ℂ ℋ₂) :
    OpMap.toMatOf bE bF (c • Φ) = c • OpMap.toMatOf bE bF Φ :=
  map_smul (OpMap.matEquivOf bE bF) c Φ

/-- A sum of completely positive operator maps is completely positive. -/
theorem isCompletelyPositive_add {Φ Ψ : OpMap ℋ₁ ℋ₂} (hΦ : OpMap.IsCompletelyPositive Φ)
    (hΨ : OpMap.IsCompletelyPositive Ψ) : OpMap.IsCompletelyPositive (Φ + Ψ) := by
  rw [OpMap.isCompletelyPositive_iff_of (stdOrthonormalBasis ℂ ℋ₁) (stdOrthonormalBasis ℂ ℋ₂),
    OpMap.IsCompletelyPositiveOf, toMatOf_add]
  exact MatrixMap.IsCompletelyPositive.add ((OpMap.isCompletelyPositive_iff_of _ _ Φ).mp hΦ)
    ((OpMap.isCompletelyPositive_iff_of _ _ Ψ).mp hΨ)

/-- A nonnegative multiple of a completely positive operator map is completely positive. -/
theorem isCompletelyPositive_smul {Φ : OpMap ℋ₁ ℋ₂} (hΦ : OpMap.IsCompletelyPositive Φ) {c : ℂ}
    (hc : 0 ≤ c) : OpMap.IsCompletelyPositive (c • Φ) := by
  rw [OpMap.isCompletelyPositive_iff_of (stdOrthonormalBasis ℂ ℋ₁) (stdOrthonormalBasis ℂ ℋ₂),
    OpMap.IsCompletelyPositiveOf, toMatOf_smul]
  exact MatrixMap.IsCompletelyPositive.smul ((OpMap.isCompletelyPositive_iff_of _ _ Φ).mp hΦ) hc

/-- Conjugation by a single operator is completely positive. -/
theorem krausTerm_isCompletelyPositive (V : ℋ₁ →L[ℂ] ℋ₂) :
    OpMap.IsCompletelyPositive (krausTerm V) := by
  rw [OpMap.isCompletelyPositive_iff_of (stdOrthonormalBasis ℂ ℋ₁) (stdOrthonormalBasis ℂ ℋ₂),
    OpMap.IsCompletelyPositiveOf, toMatOf_krausTerm]
  exact MatrixMap.congruence_CP _

/-- A finite sum of conjugations is completely positive. -/
theorem sum_krausTerm_isCompletelyPositive {σ : Type*} [Fintype σ] (V : σ → (ℋ₁ →L[ℂ] ℋ₂)) :
    OpMap.IsCompletelyPositive (∑ r, krausTerm (V r)) := by
  rw [OpMap.isCompletelyPositive_iff_of (stdOrthonormalBasis ℂ ℋ₁) (stdOrthonormalBasis ℂ ℋ₂),
    OpMap.IsCompletelyPositiveOf, toMatOf_sum]
  refine MatrixMap.IsCompletelyPositive.finset_sum fun r ↦ ?_
  rw [toMatOf_krausTerm]
  exact MatrixMap.congruence_CP _

/-- **Kraus decomposition.** Every completely positive operator map is a finite sum of
conjugations `A ↦ Vᵣ A Vᵣ†`. -/
theorem exists_kraus {Φ : OpMap ℋ₁ ℋ₂} (hΦ : OpMap.IsCompletelyPositive Φ) :
    ∃ (σ : Type w) (_ : Fintype σ) (_ : DecidableEq σ) (V : σ → (ℋ₁ →L[ℂ] ℋ₂)),
      Φ = ∑ r, krausTerm (V r) := by
  classical
  set bE := stdOrthonormalBasis ℂ ℋ₁
  set bF := stdOrthonormalBasis ℂ ℋ₂
  obtain ⟨M, hM⟩ := MatrixMap.IsCompletelyPositive.exists_kraus _ hΦ
  refine ⟨ULift.{w} _, inferInstance, inferInstance,
    fun r ↦ (matEquiv bE bF).symm (M r.down), ?_⟩
  refine OpMap.toMatOf_injective bE bF ?_
  rw [toMatOf_sum, hM, MatrixMap.of_kraus_eq_sum_conj,
    ← Equiv.ulift.{w}.sum_comp fun k ↦ MatrixMap.conj (M k)]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [toMatOf_krausTerm, LinearEquiv.apply_symm_apply]
  rfl

end Kraus

section PartialTrace

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]

/-- The partial trace over the *first* factor, as an operator map. See (1.121) of
<https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf>. -/
noncomputable def TrLeft : OpMap (ℋ₁ ⊗[ℂ] ℋ₂) ℋ₂ where
  toFun := ContinuousLinearMap.traceLeft
  map_add' := ContinuousLinearMap.traceLeft_add
  map_smul' c A := ContinuousLinearMap.traceLeft_smul A c

/-- `TrLeft` acts by `ContinuousLinearMap.traceLeft`. -/
@[simp]
theorem TrLeft_apply (A : L (ℋ₁ ⊗[ℂ] ℋ₂)) : TrLeft A = A.traceLeft :=
  rfl

/-- The partial trace over the *second* factor, as an operator map. -/
noncomputable def TrRight {ℋ₃ : Type w} [Qudit ℋ₃] : OpMap (ℋ₂ ⊗[ℂ] ℋ₃) ℋ₂ where
  toFun := ContinuousLinearMap.traceRight
  map_add' := ContinuousLinearMap.traceRight_add
  map_smul' c A := ContinuousLinearMap.traceRight_smul A c

/-- `TrRight` acts by `ContinuousLinearMap.traceRight`. -/
@[simp]
theorem TrRight_apply {ℋ₃ : Type w} [Qudit ℋ₃] (A : L (ℋ₂ ⊗[ℂ] ℋ₃)) : TrRight A = A.traceRight :=
  rfl

/-- The partial trace over the first factor is positive. -/
theorem TrLeft_isPositive : OpMap.IsPositive (TrLeft (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)) := fun A hA ↦
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (ContinuousLinearMap.IsPositive.traceLeft A ((ContinuousLinearMap.nonneg_iff_isPositive A).mp hA))

/-- The partial trace over the second factor is positive. -/
theorem TrRight_isPositive {ℋ₃ : Type w} [Qudit ℋ₃] :
    OpMap.IsPositive (TrRight (ℋ₂ := ℋ₂) (ℋ₃ := ℋ₃)) := fun A hA ↦
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (ContinuousLinearMap.IsPositive.traceRight A
      ((ContinuousLinearMap.nonneg_iff_isPositive A).mp hA))

end PartialTrace

section TensorEquiv

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]

/-- Operators on `ℋ₁ ⊗ ℋ₂` are the tensor product of the operators on the two factors. -/
noncomputable def opTensorEquiv : L (ℋ₁ ⊗[ℂ] ℋ₂) ≃ₗ[ℂ] L ℋ₁ ⊗[ℂ] L ℋ₂ :=
  LinearMap.toContinuousLinearMap.symm ≪≫ₗ (homTensorHomEquiv ℂ ℋ₁ ℋ₂ ℋ₁ ℋ₂).symm ≪≫ₗ
    TensorProduct.congr LinearMap.toContinuousLinearMap LinearMap.toContinuousLinearMap

/-- `opTensorEquiv` sends `TensorProduct.mapL B C` back and forth to `B ⊗ₜ C`. -/
@[simp]
theorem opTensorEquiv_symm_tmul (B : L ℋ₁) (C : L ℋ₂) :
    opTensorEquiv.symm (B ⊗ₜ[ℂ] C) = TensorProduct.mapL B C := by
  refine ContinuousLinearMap.coe_injective (TensorProduct.ext' fun x y ↦ ?_)
  simp [opTensorEquiv, homTensorHomEquiv_apply]

/-- The forward direction of `opTensorEquiv_symm_tmul`. -/
theorem opTensorEquiv_mapL (B : L ℋ₁) (C : L ℋ₂) :
    opTensorEquiv (TensorProduct.mapL B C) = B ⊗ₜ[ℂ] C := by
  rw [← opTensorEquiv_symm_tmul, LinearEquiv.apply_symm_apply]

/-- The trace of `X ⊗ Y` is the product of the traces. -/
@[simp]
theorem Tr_mapL (X : L ℋ₁) (Y : L ℋ₂) : Tr (TensorProduct.mapL X Y) = Tr X * Tr Y := by
  simp only [Tr_apply, TensorProduct.toLinearMap_mapL]
  exact LinearMap.trace_tensorProduct' _ _

/-- Tracing out the first factor of `X ⊗ Y` leaves `Tr X • Y`. -/
theorem TrLeft_opTensorEquiv_symm_tmul (X : L ℋ₁) (Y : L ℋ₂) :
    TrLeft (opTensorEquiv.symm (X ⊗ₜ[ℂ] Y)) = Tr X • Y := by
  refine ContinuousLinearMap.ext fun y' ↦ ext_inner_left ℂ fun y ↦ ?_
  rw [TrLeft_apply, ContinuousLinearMap.inner_traceLeft _ (stdOrthonormalBasis ℂ ℋ₁)]
  simp only [opTensorEquiv_symm_tmul, TensorProduct.mapL_tmul, TensorProduct.inner_tmul,
    smul_apply, inner_smul_right, Tr_apply]
  rw [← Finset.sum_mul, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ ℋ₁)]
  rfl

/-- Tracing out the second factor of `X ⊗ Y` leaves `Tr Y • X`. -/
theorem TrRight_opTensorEquiv_symm_tmul (X : L ℋ₁) (Y : L ℋ₂) :
    TrRight (opTensorEquiv.symm (X ⊗ₜ[ℂ] Y)) = Tr Y • X := by
  refine ContinuousLinearMap.ext fun x' ↦ ext_inner_left ℂ fun x ↦ ?_
  rw [TrRight_apply, ContinuousLinearMap.inner_traceRight _ (stdOrthonormalBasis ℂ ℋ₂)]
  simp only [opTensorEquiv_symm_tmul, TensorProduct.mapL_tmul, TensorProduct.inner_tmul,
    smul_apply, inner_smul_right, Tr_apply]
  rw [← Finset.mul_sum, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ ℋ₂), mul_comm]
  rfl

/-- Tracing out the first factor of a product of positive operators leaves a positive operator. -/
theorem TrLeft_opTensorEquiv_symm_tmul_nonneg (X : L ℋ₁) (Y : L ℋ₂) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ TrLeft (opTensorEquiv.symm (X ⊗ₜ[ℂ] Y)) := by
  rw [TrLeft_opTensorEquiv_symm_tmul]
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr <|
    ((ContinuousLinearMap.nonneg_iff_isPositive Y).mp hY).smul_of_nonneg
      ((ContinuousLinearMap.nonneg_iff_isPositive X).mp hX).toLinearMap.trace_nonneg

/-- The same for a sum of products of positive operators, a separable operator. -/
theorem TrLeft_sum_opTensorEquiv_symm_tmul_nonneg {σ : Type*} [Fintype σ]
    (X : σ → L ℋ₁) (Y : σ → L ℋ₂) (hX : ∀ a, 0 ≤ X a) (hY : ∀ a, 0 ≤ Y a) :
    0 ≤ TrLeft (∑ a : σ, opTensorEquiv.symm ((X a) ⊗ₜ[ℂ] (Y a))) := by
  rw [map_sum]
  exact Finset.sum_nonneg fun a _ ↦ TrLeft_opTensorEquiv_symm_tmul_nonneg (X a) (Y a) (hX a) (hY a)

end TensorEquiv

section Conjugate

variable {E : Type u} {F : Type v} [Qudit E] [Qudit F]

/-- Transporting an operator along an isomorphism of the underlying spaces, `X ↦ e X e⁻¹`. -/
noncomputable def conjugateEnd (e : E ≃L[ℂ] F) : OpMap E F where
  toFun X := (e : E →L[ℂ] F) ∘L X ∘L (e.symm : F →L[ℂ] E)
  map_add' X Y := by
    simp [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]
  map_smul' c X := by
    simp [ContinuousLinearMap.smul_comp]

/-- `conjugateEnd e` acts by `X ↦ e X e⁻¹`. -/
@[simp]
theorem conjugateEnd_apply (e : E ≃L[ℂ] F) (X : L E) :
    conjugateEnd e X = (e : E →L[ℂ] F) ∘L X ∘L (e.symm : F →L[ℂ] E) :=
  rfl

end Conjugate

section Stinespring

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable {κ : Type u} [Fintype κ] [DecidableEq κ]

/-- The Stinespring operator `x ↦ ∑ₐ (Aₐ x) ⊗ eₐ` of a Kraus family `A`. -/
noncomputable def krausToStinespringOperator (A : κ → (ℋ₁ →L[ℂ] ℋ₂)) :
    ℋ₁ →L[ℂ] (ℋ₂ ⊗[ℂ] EuclideanSpace ℂ κ) :=
  ∑ a : κ, TensorProduct.tmulRightL ℂ (EuclideanSpace.basisFun κ ℂ a) ∘L A a

/-- The Stinespring operator sends `x` to `∑ₐ (Aₐ x) ⊗ eₐ`. -/
@[simp]
theorem krausToStinespringOperator_apply (A : κ → (ℋ₁ →L[ℂ] ℋ₂)) (x : ℋ₁) :
    krausToStinespringOperator A x = ∑ a : κ, (A a x) ⊗ₜ[ℂ] (EuclideanSpace.basisFun κ ℂ a) := by
  simp [krausToStinespringOperator]

/-- Its adjoint reads off one Kraus operator at a time: `y ⊗ e_b` goes to `A_b† y`. -/
@[simp]
theorem adjoint_krausToStinespringOperator_tmul_single (A : κ → (ℋ₁ →L[ℂ] ℋ₂)) (y : ℋ₂) (b : κ) :
    ((krausToStinespringOperator A)†) (y ⊗ₜ[ℂ] EuclideanSpace.single b 1) = ((A b)†) y := by
  refine ext_inner_right ℂ fun x ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
    krausToStinespringOperator_apply]
  simp [inner_sum, TensorProduct.inner_tmul, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left]

/-- Tracing out the environment of the Stinespring operator recovers the Kraus sum. -/
theorem trRight_kraus (A : κ → (ℋ₁ →L[ℂ] ℋ₂)) (X : L ℋ₁) :
    TrRight (krausToStinespringOperator A ∘L X ∘L (krausToStinespringOperator A)†) =
      ∑ a : κ, A a ∘L X ∘L (A a)† := by
  refine ContinuousLinearMap.ext fun x' ↦ ext_inner_left ℂ fun x ↦ ?_
  rw [TrRight_apply, ContinuousLinearMap.inner_traceRight _ (EuclideanSpace.basisFun κ ℂ)]
  simp only [ContinuousLinearMap.comp_apply, EuclideanSpace.basisFun_apply,
    adjoint_krausToStinespringOperator_tmul_single]
  simp only [krausToStinespringOperator_apply, inner_sum, TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, map_one, one_mul, sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- The Gram operator of the Stinespring operator is the Kraus completeness sum. -/
theorem adjoint_comp_krausToStinespringOperator (A : κ → (ℋ₁ →L[ℂ] ℋ₂)) :
    (krausToStinespringOperator A)† ∘L krausToStinespringOperator A =
      ∑ a : κ, (A a)† ∘L A a := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  rw [ContinuousLinearMap.comp_apply, krausToStinespringOperator_apply, map_sum, sum_apply]
  simp only [EuclideanSpace.basisFun_apply]
  exact Finset.sum_congr rfl fun a _ ↦
    adjoint_krausToStinespringOperator_tmul_single A (A a x) a

end Stinespring

section Channel

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]

/-- A channel built from a Kraus family, given that the family is trace preserving. -/
noncomputable def ofKraus {σ : Type*} [Fintype σ] (V : σ → (ℋ₁ →L[ℂ] ℋ₂))
    (hV : ∑ r, (V r)† ∘L V r = 1) : CPTPOp ℋ₁ ℋ₂ where
  toLinearMap := ∑ r, krausTerm (V r)
  cp := sum_krausTerm_isCompletelyPositive V
  TP A := by
    have h (r : σ) : LinearMap.trace ℂ ℋ₂ ((V r ∘L A ∘L (V r)†) : ℋ₂ →ₗ[ℂ] ℋ₂) =
        LinearMap.trace ℂ ℋ₁ ((A ∘L (V r)† ∘L V r : ℋ₁ →L[ℂ] ℋ₁) : ℋ₁ →ₗ[ℂ] ℋ₁) :=
      (LinearMap.trace_comp_comm' (V r : ℋ₁ →ₗ[ℂ] ℋ₂) ((A ∘L (V r)† : ℋ₂ →L[ℂ] ℋ₁) :
        ℋ₂ →ₗ[ℂ] ℋ₁)).symm
    have key : ∑ r, (A ∘L (V r)† ∘L V r) = A := by
      refine ContinuousLinearMap.ext fun x ↦ ?_
      have happ (r : σ) : (A ∘L (V r)† ∘L V r) x = A (((V r)† ∘L V r) x) := rfl
      rw [sum_apply]
      simp only [happ, ← map_sum, ← sum_apply, hV]
      simp
    rw [LinearMap.sum_apply, ContinuousLinearMap.toLinearMap_sum, map_sum]
    simp only [krausTerm_apply, h, ← map_sum, ← ContinuousLinearMap.toLinearMap_sum, key]

/-- `ofKraus V hV` acts by the Kraus sum it was built from. -/
@[simp]
theorem ofKraus_toLinearMap {σ : Type*} [Fintype σ] (V : σ → (ℋ₁ →L[ℂ] ℋ₂))
    (hV : ∑ r, (V r)† ∘L V r = 1) : (ofKraus V hV).toLinearMap = ∑ r, krausTerm (V r) :=
  rfl

/-- Converse of the trace-preservation computation in `ofKraus`: a Kraus family whose sum is
trace preserving satisfies the completeness relation `∑ᵣ Vᵣ† Vᵣ = 1`. -/
theorem sum_adjoint_comp_self_eq_one {σ : Type*} [Fintype σ] (V : σ → (ℋ₁ →L[ℂ] ℋ₂))
    (hTP : OpMap.IsTracePreserving (∑ r, krausTerm (V r))) :
    ∑ r, (V r)† ∘L V r = 1 := by
  refine eq_one_of_Tr_mul fun X ↦ ?_
  have hcyc (r : σ) : Tr (((V r)† ∘L V r) * X) = Tr (V r ∘L X ∘L (V r)†) :=
    LinearMap.trace_comp_comm' ((V r ∘L X : ℋ₁ →L[ℂ] ℋ₂) : ℋ₁ →ₗ[ℂ] ℋ₂)
      (((V r)† : ℋ₂ →L[ℂ] ℋ₁) : ℋ₂ →ₗ[ℂ] ℋ₁)
  have hT := hTP X
  rw [LinearMap.sum_apply, ContinuousLinearMap.toLinearMap_sum, map_sum] at hT
  rw [Finset.sum_mul, map_sum]
  simp only [hcyc]
  simpa only [krausTerm_apply, Tr_apply] using hT

end Channel

end QuantumChannel

namespace CPTPOp

open QuantumState QuantumChannel

open scoped ComplexOrder

universe u v

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]

/-- Trace preservation, stated with `QuantumState.Tr`. -/
@[simp]
theorem Tr_map (Λ : CPTPOp ℋ₁ ℋ₂) (A : L ℋ₁) : Tr (Λ.toLinearMap A) = Tr A :=
  Λ.TP A

/-- The convex combination `(1 - t) • Λ₁ + t • Λ₂` of two channels, for `t ∈ [0,1]`. -/
noncomputable def convexComb (Λ₁ Λ₂ : CPTPOp ℋ₁ ℋ₂) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    CPTPOp ℋ₁ ℋ₂ where
  toLinearMap := ((1 - t : ℝ) : ℂ) • Λ₁.toLinearMap + ((t : ℝ) : ℂ) • Λ₂.toLinearMap
  cp := isCompletelyPositive_add
    (isCompletelyPositive_smul Λ₁.cp (Complex.zero_le_real.mpr (by linarith)))
    (isCompletelyPositive_smul Λ₂.cp (Complex.zero_le_real.mpr ht₀))
  TP A := by
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
      ContinuousLinearMap.toLinearMap_smul, map_add, map_smul, map_smul, Λ₁.TP A, Λ₂.TP A,
      smul_eq_mul, smul_eq_mul, ← add_mul]
    push_cast
    ring

/-- `convexComb` acts by the convex combination it was built from. -/
@[simp]
theorem convexComb_toLinearMap (Λ₁ Λ₂ : CPTPOp ℋ₁ ℋ₂) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (Λ₁.convexComb Λ₂ ht₀ ht₁).toLinearMap =
      ((1 - t : ℝ) : ℂ) • Λ₁.toLinearMap + ((t : ℝ) : ℂ) • Λ₂.toLinearMap :=
  rfl

end CPTPOp
