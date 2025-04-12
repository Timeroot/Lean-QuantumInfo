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
def Dual (M : MatrixMap dIn dOut R) : MatrixMap dOut dIn R :=
  let iso1 := (Basis.toDualEquiv <| Matrix.stdBasis R dIn dIn).symm
  let iso2 := (Basis.toDualEquiv <| Matrix.stdBasis R dOut dOut)
  iso1 ∘ₗ LinearMap.dualMap M ∘ₗ iso2

/-- The dual of a `IsHermitianPreserving` map also `IsHermitianPreserving`. -/
theorem Dual.IsHermitianPreserving (h : M.IsHermitianPreserving) : M.Dual.IsHermitianPreserving := by
  sorry

/-- The dual of a `IsPositive` map also `IsPositive`. -/
theorem Dual.IsPositive (h : M.IsPositive) : M.Dual.IsPositive := by
  intro x hx
  use Dual.IsHermitianPreserving h.IsHermitianPreserving hx.1
  sorry

/-- The dual of TracePreserving map is *not* trace-preserving, it's *unital*, that is, M*(I) = I. -/
theorem Dual.Unital (h : M.IsTracePreserving) : M.Dual.Unital := by
  sorry

--The dual of a CompletelyPositive map is always CP, more generally it's k-positive
-- see Lemma 3.1 of https://www.math.uwaterloo.ca/~krdavids/Preprints/CDPRpositivereal.pdf
theorem Dual.IsCompletelyPositive (h : M.IsCompletelyPositive) : M.Dual.IsCompletelyPositive := by
  sorry

/-- The defining property of a dual map: inner products are preserved on the opposite argument. -/
theorem Dual.inner_eq (M : MatrixMap dIn dOut R) (A : Matrix dIn dIn R) (B : Matrix dOut dOut R) :
    (M A * B).trace = (A * M.Dual B).trace := by
  dsimp [Matrix.trace, Dual]
  rw [LinearMap.dualMap_apply']
  simp_rw [Matrix.mul_apply]
  sorry

end MatrixMap

namespace CPTPMap

def Dual (M : CPTPMap dIn dOut) : CPUMap dOut dIn where
  toLinearMap := M.map.Dual
  unital := MatrixMap.Dual.Unital M.TP
  cp := MatrixMap.Dual.IsCompletelyPositive M.cp

theorem Dual_pos (M : CPTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T) :
    0 ≤ M.Dual.toHPMap T := by
  have hDT := M.Dual.pos (HermitianMat.zero_le_iff.mp hT)
  exact HermitianMat.zero_le_iff.mpr hDT

-- set_option pp.all true

/-- The dual of a CPTP map preserves POVMs. Stated here just for two-element POVMs, that is, an
operator `T` between 0 and 1. -/
theorem Dual.PTP_POVM (M : CPTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T ∧ T ≤ 1) :
    (0 ≤ M.Dual.toHPMap T ∧ M.Dual.toHPMap T ≤ 1) := by
  rcases hT with ⟨hT₁, hT₂⟩
  have hT_psd := HermitianMat.zero_le_iff.mp hT₁
  have hDT := M.Dual_pos hT₁
  have h1T : 0 ≤ 1 - T := HermitianMat.zero_le_iff.mpr hT₂
  have hD1T := M.Dual_pos h1T
  use hDT
  clear hT₁ hT₂ hDT h1T hT_psd
  have hu : M.Dual.map.Unital := M.Dual.unital
  unfold CPUMap.map at hu
  generalize M.Dual.toHPMap = mmm at *
  clear M
  replace hD1T : 0 ≤ mmm 1 - mmm T := by
    --Again, NEED better simp lemmas for this. TODO
    convert hD1T
    ext1
    symm
    exact map_sub _ _ _
  replace hD1T : 0 ≤ 1 - mmm T := by
    convert hD1T
    --TODO:
    --Need a lemma to help do this - `.Unital` but for `(1 : HermitianMat)` instead of `(1 : Matrix)`.
    symm
    ext1
    exact hu
  --are we really missing this?
  have i2 : AddRightMono (HermitianMat dIn ℂ) := by sorry--inferInstance
  exact le_of_sub_nonneg hD1T

/-- The defining property of a dual channel, as specialized to `MState.exp_val`. -/
theorem exp_val_Dual (ℰ : CPTPMap dIn dOut) (ρ : MState dIn) (T : HermitianMat dOut ℂ) :
    (ℰ ρ).exp_val T  = ρ.exp_val (ℰ.Dual.toHPMap T) := by
  dsimp [MState.exp_val]
  simp only [HermitianMat.inner_eq_re_trace, HermitianMat.val_eq_coe, RCLike.re_to_complex]
  congr 1
  apply MatrixMap.Dual.inner_eq

end CPTPMap
