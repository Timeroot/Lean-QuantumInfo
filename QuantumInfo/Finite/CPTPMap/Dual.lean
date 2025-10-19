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

--PULLOUT
theorem HermitianMat.toMat_add (x y : HermitianMat d ℂ) : (x + y).toMat = x.toMat + y.toMat := by
  rfl

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

/-- The defining property of a dual map: inner products are preserved on the opposite argument. -/
theorem Dual.trace_eq (M : MatrixMap dIn dOut R) (A : Matrix dIn dIn R) (B : Matrix dOut dOut R) :
    (M A * B).trace = (A * M.dual B).trace := by
  unfold dual
  dsimp [Matrix.trace]
  rw [LinearMap.dualMap_apply']
  simp_rw [Matrix.mul_apply]
  sorry

--all properties below should provable just from `inner_eq`, since the definition of `dual` itself
-- is pretty hair (and maybe could be improved...)

/-- The dual of a `IsHermitianPreserving` map also `IsHermitianPreserving`. -/
theorem IsHermitianPreserving.dual (h : M.IsHermitianPreserving) : M.dual.IsHermitianPreserving := by
  sorry

/-- The dual of a `IsPositive` map also `IsPositive`. -/
theorem IsPositive.dual (h : M.IsPositive) : M.dual.IsPositive := by
  intro x hx
  use IsHermitianPreserving.dual h.IsHermitianPreserving hx.1
  sorry

/-- The dual of TracePreserving map is *not* trace-preserving, it's *unital*, that is, M*(I) = I. -/
theorem dual_Unital (h : M.IsTracePreserving) : M.dual.Unital := by
  sorry

alias IsTracePreserving.dual := dual_Unital

--The dual of a CompletelyPositive map is always CP, more generally it's k-positive
-- see Lemma 3.1 of https://www.math.uwaterloo.ca/~krdavids/Preprints/CDPRpositivereal.pdf
theorem IsCompletelyPositive.dual (h : M.IsCompletelyPositive) : M.dual.IsCompletelyPositive := by
  sorry

@[simp]
theorem dual_dual : M.dual.dual = M := by
  rw [dual, dual]
  simp only [← LinearMap.dualMap_comp_dualMap]
  have h₁ : (Matrix.stdBasis 𝕜 dOut dOut).toDualEquiv.symm.toLinearMap ∘ₗ
      ((Matrix.stdBasis 𝕜 dOut dOut).toDualEquiv).toLinearMap.dualMap =
      (Module.evalEquiv 𝕜 (Matrix dOut dOut 𝕜)).symm.toLinearMap := by
    sorry
  have h₂ : (Matrix.stdBasis 𝕜 dIn dIn).toDualEquiv.symm.toLinearMap.dualMap ∘ₗ
      (Matrix.stdBasis 𝕜 dIn dIn).toDualEquiv.toLinearMap =
      (Module.evalEquiv 𝕜 (Matrix dIn dIn 𝕜)).toLinearMap := by
    ext x y
    simp
    generalize Matrix.stdBasis 𝕜 dIn dIn = L
    sorry
  rw [← Module.Dual.eval_comp_comp_evalEquiv_eq]
  rw [← Module.evalEquiv_toLinearMap]
  simp only [← LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
    LinearMap.id_comp, h₁]
  simp only [LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
    LinearMap.comp_id, h₂]

end MatrixMap

namespace CPTPMap

variable [DecidableEq dIn] [DecidableEq dOut]

def dual (M : CPTPMap dIn dOut) : CPUMap dOut dIn where
  toLinearMap := M.map.dual
  unital := M.TP.dual
  cp := .dual M.cp

theorem dual_pos (M : CPTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T) :
    0 ≤ M.dual T := by
  exact M.dual.pos_Hermitian hT

/-- The dual of a CPTP map preserves POVMs. Stated here just for two-element POVMs, that is, an
operator `T` between 0 and 1. -/
theorem dual.PTP_POVM (M : CPTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T ∧ T ≤ 1) :
    (0 ≤ M.dual T ∧ M.dual T ≤ 1) := by
  rcases hT with ⟨hT₁, hT₂⟩
  have hT_psd := HermitianMat.zero_le_iff.mp hT₁
  use M.dual.pos_Hermitian hT₁
  simpa using ContinuousOrderHomClass.map_monotone M.dual hT₂

/-- The defining property of a dual channel, as specialized to `MState.exp_val`. -/
theorem exp_val_Dual (ℰ : CPTPMap dIn dOut) (ρ : MState dIn) (T : HermitianMat dOut ℂ) :
    (ℰ ρ).exp_val T  = ρ.exp_val (ℰ.dual T) := by
  simp only [MState.exp_val, HermitianMat.inner_eq_re_trace,
    HermitianMat.val_eq_coe, RCLike.re_to_complex]
  congr 1
  apply MatrixMap.Dual.trace_eq

end CPTPMap

section hermDual

--PULLOUT to Bundled.lean. Also use this to improve the definitions in POVM.lean.
def HPMap.ofHermitianMat (f : HermitianMat dIn ℂ →ₗ[ℝ] HermitianMat dOut ℂ) : HPMap dIn dOut where
  toFun x := f (realPart x) + Complex.I • f (imaginaryPart x)
  map_add' x y := by
    simp only [map_add, AddSubgroup.coe_add, smul_add]
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
    simp only [h_expand, map_sub, map_smul, AddSubgroupClass.coe_sub,
      selfAdjoint.val_smul, map_add, AddSubgroup.coe_add, smul_add, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul, RingHom.id_apply,
      Complex.ext_iff, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I, Complex.mul_im, Complex.add_im, Complex.sub_im]
    ring_nf
    simp
  HP _ h := by
    apply Matrix.IsHermitian.add
    · apply HermitianMat.H
    · simp [IsSelfAdjoint.imaginaryPart h]

--PULLOUT
@[simp]
theorem HPMap.linearMap_ofHermitianMat (f : HermitianMat dIn ℂ →ₗ[ℝ] HermitianMat dOut ℂ) :
    LinearMapClass.linearMap (HPMap.ofHermitianMat f) = f := by
  ext1 ⟨x, hx⟩
  ext1
  simp only [ofHermitianMat, LinearMap.coe_coe]
  simp only [HPMap.instFunLike, HPMap.map, HermitianMat.val_eq_coe, HermitianMat.mk_toMat,
    LinearMap.coe_mk, AddHom.coe_mk]
  conv => enter [2, 1, 2, 1]; rw [← realPart_add_I_smul_imaginaryPart x]
  suffices imaginaryPart x = 0 by simp [this]
  simp [imaginaryPart, skewAdjoint.negISMul, show star x = x from hx]

--PULLOUT
@[simp]
theorem HPMap.ofHermitianMat_linearMap (f : HPMap dIn dOut ℂ) :
    ofHermitianMat (LinearMapClass.linearMap f) = f := by
  ext : 2
  simp only [map, ofHermitianMat, instFunLike, LinearMap.coe_coe, HermitianMat.val_eq_coe,
    HermitianMat.mk_toMat, LinearMap.coe_mk, AddHom.coe_mk,
    ← map_smul, ← map_add, realPart_add_I_smul_imaginaryPart]

variable (f : HPMap dIn dOut) (A : HermitianMat dIn ℂ)

--Can define one for HPMap's that has 'easier' definitional properties, uses the inner product structure,
--doesn't go through Module.Basis the same way. Requires the equivalence between ℝ-linear maps of HermitianMats
--and ℂ-linear maps of matrices.
def HPMap.hermDual : HPMap dOut dIn :=
  HPMap.ofHermitianMat (LinearMapClass.linearMap f).adjoint

@[simp]
theorem HPMap.hermDual_hermDual : f.hermDual.hermDual = f := by
  simp [hermDual]

open RealInnerProductSpace in
/-- The defining property of a dual map: inner products are preserved on the opposite argument. -/
theorem HPMap.inner_hermDual (B : HermitianMat dOut ℂ) :
    ⟪f A, B⟫ = ⟪A, f.hermDual B⟫ := by
  change ⟪(LinearMapClass.linearMap f) A, B⟫ = ⟪A, (LinearMapClass.linearMap f.hermDual) B⟫
  rw [hermDual, ← LinearMap.adjoint_inner_right, HPMap.linearMap_ofHermitianMat]

/-- Version of `HPMap.inner_hermDual` that uses HermitiaMat.inner directly. TODO cleanup -/
theorem HPMap.inner_hermDual' (B : HermitianMat dOut ℂ) :
    (f A).inner B = A.inner (f.hermDual B) :=
  HPMap.inner_hermDual f A B

open RealInnerProductSpace in
theorem HermitianMat.inner_negPart_nonpos [DecidableEq dIn] : ⟪A, A⁻⟫ ≤ 0 := by
  rw [← neg_le_neg_iff, neg_zero, ← inner_neg_right]
  apply inner_mul_nonneg
  nth_rw 1 [← A.cfc_id]
  rw [negPart_eq_cfc_ite]
  rw [← cfc_neg]
  rw [← coe_cfc_mul]
  change 0 ≤ A.cfc _
  rw [zero_le_cfc]
  intro i
  dsimp
  split_ifs with h
  · rw [neg_neg]
    exact mul_self_nonneg _
  · simp

theorem HermitianMat.cfc_eq_cfc_iff_eqOn [DecidableEq dIn] (A : HermitianMat dIn ℂ) (f g : ℝ → ℝ) :
    cfc A f = cfc A g ↔ Set.EqOn f g (spectrum ℝ A.toMat) := by
  rw [HermitianMat.ext_iff, cfc_toMat, cfc_toMat]
  exact _root_.cfc_eq_cfc_iff_eqOn A.H herm_cont herm_cont

open RealInnerProductSpace in
theorem HermitianMat.inner_negPart_zero_iff [DecidableEq dIn] : ⟪A, A⁻⟫ = 0 ↔ 0 ≤ A := by
  constructor
  · intro h
    have h2 : ⟪A⁺, A⁻⟫ = 0 := by
      --TODO own thm?
      have hi := inner_eq_trace_rc A⁺ A⁻
      rw [posPart_mul_negPart, Matrix.trace_zero] at hi
      exact congr(Complex.re ($hi))
    nth_rw 1 [← posPart_add_negPart A] at h
    rw [inner_sub_left, sub_eq_zero, h2, eq_comm, inner_self_eq_zero] at h
    rw [← zero_smul ℝ 1, ← cfc_const A, negPart_eq_cfc_ite] at h --TODO cfc_zero
    rw [cfc_eq_cfc_iff_eqOn, A.H.spectrum_real_eq_range_eigenvalues] at h
    simp only [Set.eqOn_range] at h
    replace h (i) := congrFun h i
    simp only [Function.comp_apply, ite_eq_right_iff, neg_eq_zero] at h
    rw [zero_le_iff, A.H.posSemidef_iff_eigenvalues_nonneg]
    intro i
    contrapose! h
    use i, h.le, h.ne
  · intro h
    apply le_antisymm
    · exact inner_negPart_nonpos A
    · exact inner_ge_zero' _ _ h (negPart_le_zero A)

open RealInnerProductSpace in
theorem HermitianMat.inner_negPart_neg_iff [DecidableEq dIn] : ⟪A, A⁻⟫ < 0 ↔ ¬0 ≤ A := by
  simp [← inner_negPart_zero_iff, lt_iff_le_and_ne, inner_negPart_nonpos A]

--PULLOUT
open RealInnerProductSpace in
theorem HermitianMat.zero_le_iff_inner_pos (A : HermitianMat dIn ℂ) :
    0 ≤ A ↔ ∀ B, 0 ≤ B → 0 ≤ ⟪A, B⟫ := by
  use fun h _ ↦ inner_ge_zero h
  intro h
  contrapose! h
  classical
  use A⁻, negPart_le_zero A
  rwa [inner_negPart_neg_iff]

/-- The dual of a `IsPositive` map also `IsPositive`. -/
theorem MatrixMap.IsPositive.hermDual (h : MatrixMap.IsPositive f.map) : f.hermDual.map.IsPositive := by
  unfold IsPositive at h ⊢
  intro x hx
  set xH : HermitianMat dOut ℂ := ⟨x, hx.left⟩ with hxH
  have hx' : x = xH := rfl; clear_value xH; subst x; clear hxH
  change Matrix.PosSemidef (f.hermDual xH).toMat
  rw [← HermitianMat.zero_le_iff] at hx ⊢
  rw [HermitianMat.zero_le_iff_inner_pos]
  intro y hy
  rw [HermitianMat.zero_le_iff] at hy
  specialize h hy
  change Matrix.PosSemidef (f y).toMat at h
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
  change HermitianMat.inner _ _ = HermitianMat.inner _ _
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
