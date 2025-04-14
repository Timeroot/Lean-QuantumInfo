import QuantumInfo.Finite.CPTPMap.Bundled
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-! # Duals of matrix map

Definitions and theorems about the dual of a matrix map. -/

noncomputable section
open ComplexOrder

variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut]
variable {R : Type*} [CommRing R]
variable {𝕜 : Type*} [RCLike 𝕜]

namespace MatrixMap

variable {M : MatrixMap dIn dOut 𝕜}

--This should be definable with LinearMap.adjoint, but that requires InnerProductSpace stuff
--that is currently causing issues and pains (tried `open scoped Frobenius`).

/-- The dual of a map between matrices, defined by `Tr[A M(B)] = Tr[(dual M)(A) B]`. Sometimes
 called the adjoint of the map instead. -/
@[irreducible]
def dual (M : MatrixMap dIn dOut R) : MatrixMap dOut dIn R :=
  let iso1 := (Basis.toDualEquiv <| Matrix.stdBasis R dIn dIn).symm
  let iso2 := (Basis.toDualEquiv <| Matrix.stdBasis R dOut dOut)
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

def dual (M : CPTPMap dIn dOut) : CPUMap dOut dIn where
  toLinearMap := M.map.dual
  unital := M.TP.dual
  cp := .dual M.cp

theorem dual_pos (M : CPTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T) :
    0 ≤ M.dual T := by
  exact M.dual.pos_Hermitian hT

-- set_option pp.all true

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
  dsimp [MState.exp_val]
  norm_cast
  simp only [HermitianMat.inner_eq_re_trace, HermitianMat.val_eq_coe, RCLike.re_to_complex]
  congr 1
  apply MatrixMap.Dual.trace_eq

end CPTPMap
