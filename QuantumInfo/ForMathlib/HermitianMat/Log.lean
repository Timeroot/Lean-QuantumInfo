import QuantumInfo.ForMathlib.HermitianMat.Basic

/-! # Properties of the matrix logarithm

In particular, the operator convexity -/

namespace HermitianMat

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

@[simp]
theorem log_zero : (0 : HermitianMat n 𝕜).log = 0 := by
  simp [log]

@[simp]
theorem log_one : (1 : HermitianMat n 𝕜).log = 0 := by
  simp [log]

theorem log_smul {a : HermitianMat n 𝕜} {x : ℝ}  : (x • a).log = Real.log x • 1 + a.log := by
  rw [log, log, HermitianMat.ext_iff]
  simp only [selfAdjoint.val_smul, val_eq_coe, AddSubgroup.coe_add, selfAdjoint.val_one]
  --easy when #25194 lands in Mathlib
  convert CFC.log_smul (r := x) (a := a.toMat) sorry sorry sorry
  rw [Algebra.algebraMap_eq_smul_one]
