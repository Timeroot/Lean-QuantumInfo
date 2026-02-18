/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.CPTPMap.Bundled
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-! # Duals of matrix map

Definitions and theorems about the dual of a matrix map. -/

noncomputable section
open ComplexOrder

variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut]
variable {R : Type*} [CommRing R]
variable {𝕜 : Type*} [RCLike 𝕜]

namespace MatrixMap

variable [DecidableEq dIn] [DecidableEq dOut] {M : MatrixMap dIn dOut 𝕜}

--This should be definable with LinearMap.adjoint, but that requires InnerProductSpace stuff
--that is currently causing issues and pains (tried `open scoped Frobenius`).

/-- The dual of a map between matrices, defined by `Tr[A M(B)] = Tr[(dual M)(A) B]`. Sometimes
 called the adjoint of the map instead. -/
@[irreducible]
def dual (M : MatrixMap dIn dOut R) : MatrixMap dOut dIn R :=
  let iso1 := (Module.Basis.toDualEquiv <| Matrix.stdBasis R dIn dIn).symm
  let iso2 := (Module.Basis.toDualEquiv <| Matrix.stdBasis R dOut dOut)
  iso1 ∘ₗ LinearMap.dualMap M ∘ₗ iso2

end MatrixMap

section hermDual

--PULLOUT to Bundled.lean. Also use this to improve the definitions in POVM.lean.
def HPMap.ofHermitianMat (f : HermitianMat dIn ℂ →ₗ[ℝ] HermitianMat dOut ℂ) : HPMap dIn dOut where
  toFun x := f (realPart x) + Complex.I • f (imaginaryPart x)
  map_add' x y := by
    simp only [map_add, HermitianMat.mat_add, smul_add]
    abel
  map_smul' c m := by
    have h_expand : realPart (c • m) = c.re • realPart m - c.im • imaginaryPart m ∧
      imaginaryPart (c • m) = c.re • imaginaryPart m + c.im • realPart m := by
      simp only [Subtype.ext_iff, AddSubgroupClass.coe_sub, selfAdjoint.val_smul,
        AddSubgroup.coe_add, realPart, selfAdjointPart_apply_coe, invOf_eq_inv, star_smul, RCLike.star_def,
        smul_add, imaginaryPart, LinearMap.coe_comp, Function.comp_apply,
        skewAdjoint.negISMul_apply_coe, skewAdjointPart_apply_coe,
        ← Matrix.ext_iff, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul,
        Complex.ofReal_inv, Complex.ofReal_ofNat, Matrix.star_apply, RCLike.star_def,
        Matrix.sub_apply, Complex.ext_iff, Complex.add_re, Complex.mul_re, Complex.inv_re,
        Complex.normSq_ofNat, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.sub_re, Complex.sub_im, Complex.add_im, Complex.neg_re, Complex.neg_im]
      ring_nf
      simp
    ext
    simp only [h_expand, map_sub, map_smul, map_add, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, RingHom.id_apply, Complex.ext_iff, Complex.add_re, Complex.mul_re,
      Complex.I, Complex.mul_im, Complex.add_im]
    simp only [HermitianMat.mat_sub, HermitianMat.mat_smul, Matrix.sub_apply, Matrix.smul_apply,
      Complex.real_smul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, HermitianMat.mat_add, Matrix.add_apply, Complex.add_re, Complex.add_im,
      Complex.mul_im, add_zero, one_mul, zero_sub, neg_add_rev, zero_add, Complex.sub_im]
    ring_nf
    simp
  HP _ h := by
    apply Matrix.IsHermitian.add
    · apply HermitianMat.H
    · simp [IsSelfAdjoint.imaginaryPart h]

--PULLOUT
omit [Fintype dOut] in
@[simp]
theorem HPMap.linearMap_ofHermitianMat (f : HermitianMat dIn ℂ →ₗ[ℝ] HermitianMat dOut ℂ) :
    LinearMapClass.linearMap (HPMap.ofHermitianMat f) = f := by
  ext1 ⟨x, hx⟩
  ext1
  simp only [ofHermitianMat, LinearMap.coe_coe]
  simp only [HPMap.instFunLike, HPMap.map, HermitianMat.mat_mk,
    LinearMap.coe_mk, AddHom.coe_mk]
  conv => enter [2, 1, 2, 1]; rw [← realPart_add_I_smul_imaginaryPart x]
  suffices imaginaryPart x = 0 by simp [this]
  simp [imaginaryPart, skewAdjoint.negISMul, show star x = x from hx]

--PULLOUT
omit [Fintype dOut] in
@[simp]
theorem HPMap.ofHermitianMat_linearMap (f : HPMap dIn dOut ℂ) :
    ofHermitianMat (LinearMapClass.linearMap f) = f := by
  ext : 3
  simp only [map, ofHermitianMat, instFunLike, LinearMap.coe_coe, HermitianMat.val_eq_coe,
    HermitianMat.mat_mk, LinearMap.coe_mk, AddHom.coe_mk,
    ← map_smul, ← map_add]
  simp only [map_add, map_smul, realPart, imaginaryPart, LinearMap.coe_comp, Function.comp_apply]
  simp only [selfAdjointPart,  LinearMap.coe_mk, AddHom.coe_mk,
    HermitianMat.mat_mk,LinearMap.map_smul_of_tower, skewAdjoint.negISMul]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp
  ring


variable (f : HPMap dIn dOut) (A : HermitianMat dIn ℂ)

--Can define one for HPMap's that has 'easier' definitional properties, uses the inner product structure,
--doesn't go through Module.Basis the same way. Requires the equivalence between ℝ-linear maps of HermitianMats
--and ℂ-linear maps of matrices.
def HPMap.hermDual : HPMap dOut dIn :=
  HPMap.ofHermitianMat (LinearMapClass.linearMap f).adjoint

@[simp]
theorem HPMap.hermDual_hermDual : f.hermDual.hermDual = f := by
  simp [hermDual]

open RealInnerProductSpace

/-- The defining property of a dual map: inner products are preserved on the opposite argument. -/
theorem HPMap.inner_hermDual (B : HermitianMat dOut ℂ) :
    ⟪f A, B⟫ = ⟪A, f.hermDual B⟫ := by
  change ⟪(LinearMapClass.linearMap f) A, B⟫ = ⟪A, (LinearMapClass.linearMap f.hermDual) B⟫
  rw [hermDual, ← LinearMap.adjoint_inner_right, HPMap.linearMap_ofHermitianMat]

/-- Version of `HPMap.inner_hermDual` that uses HermitiaMat.inner directly. TODO cleanup -/
theorem HPMap.inner_hermDual' (B : HermitianMat dOut ℂ) :
    ⟪f A, B⟫ = ⟪A, f.hermDual B⟫ :=
  HPMap.inner_hermDual f A B

/-- The dual of a `IsPositive` map also `IsPositive`. -/
theorem MatrixMap.IsPositive.hermDual (h : MatrixMap.IsPositive f.map) : f.hermDual.map.IsPositive := by
  unfold IsPositive at h ⊢
  intro x hx
  set xH : HermitianMat dOut ℂ := ⟨x, hx.left⟩ with hxH
  have hx' : x = xH := rfl; clear_value xH; subst x; clear hxH
  change Matrix.PosSemidef (f.hermDual xH).mat
  rw [← HermitianMat.zero_le_iff] at hx ⊢
  classical
  rw [HermitianMat.zero_le_iff_inner_pos]
  intro y hy
  rw [HermitianMat.zero_le_iff] at hy
  specialize h hy
  change Matrix.PosSemidef (f y).mat at h
  rw [← HermitianMat.zero_le_iff] at h
  rw [HPMap.inner_hermDual, HPMap.hermDual_hermDual]
  apply HermitianMat.inner_ge_zero hx h

/-- The dual of TracePreserving map is *not* trace-preserving, it's *unital*, that is, M*(I) = I. -/
theorem HPMap.hermDual_Unital [DecidableEq dIn] [DecidableEq dOut] (h : MatrixMap.IsTracePreserving f.map) :
    f.hermDual.map.Unital := by
  suffices f.hermDual 1 = 1 by --todo: make this is an accessible 'constructor' for Unital
    rw [HermitianMat.ext_iff] at this
    exact this
  open RealInnerProductSpace in
  apply ext_inner_left ℝ
  intro v
  rw [← HPMap.inner_hermDual]
  rw [HermitianMat.inner_one, HermitianMat.inner_one] --TODO change to Inner.inner
  exact congr(Complex.re $(h v)) --TODO: HPMap with IsTracePreserving give the HermitianMat.trace version

alias MatrixMap.IsTracePreserving.hermDual := HPMap.hermDual_Unital

namespace PTPMap

variable [DecidableEq dIn] [DecidableEq dOut]

def hermDual (M : PTPMap dIn dOut) : PUMap dOut dIn where
  toHPMap := M.toHPMap.hermDual
  pos := M.pos.hermDual
  unital := M.TP.hermDual

theorem hermDual_pos (M : PTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T) :
    0 ≤ M.hermDual T := by
  exact M.hermDual.pos_Hermitian hT

/-- The dual of a PTP map preserves POVMs. Stated here just for two-element POVMs, that is, an
operator `T` between 0 and 1. -/
theorem hermDual.PTP_POVM (M : PTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T ∧ T ≤ 1) :
    (0 ≤ M.hermDual T ∧ M.hermDual T ≤ 1) := by
  rcases hT with ⟨hT₁, hT₂⟩
  have hT_psd := HermitianMat.zero_le_iff.mp hT₁
  use M.hermDual.pos_Hermitian hT₁
  simpa using ContinuousOrderHomClass.map_monotone M.hermDual hT₂

/-- The defining property of a dual channel, as specialized to `MState.exp_val`. -/
theorem exp_val_hermDual (ℰ : PTPMap dIn dOut) (ρ : MState dIn) (T : HermitianMat dOut ℂ) :
    (ℰ ρ).exp_val T  = ρ.exp_val (ℰ.hermDual T) := by
  simp only [MState.exp_val]
  apply HPMap.inner_hermDual'

end PTPMap

end hermDual
