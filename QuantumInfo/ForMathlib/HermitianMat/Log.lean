import QuantumInfo.ForMathlib.HermitianMat.CFC

/-! # Properties of the matrix logarithm

In particular, operator concavity of the matrix logarithm.
-/

namespace HermitianMat

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

@[simp]
theorem log_zero : (0 : HermitianMat n 𝕜).log = 0 := by
  simp [log, cfc]

@[simp]
theorem log_one : (1 : HermitianMat n 𝕜).log = 0 := by
  simp [log, cfc]

theorem log_smul {a : HermitianMat n 𝕜} {x : ℝ}  : (x • a).log = Real.log x • 1 + a.log := by
  rw [log, log, HermitianMat.ext_iff]
  simp only [selfAdjoint.val_smul, val_eq_coe, AddSubgroup.coe_add, selfAdjoint.val_one]
  --easy when #25194 lands in Mathlib
  --convert CFC.log_smul (r := x) (a := a.toMat) sorry sorry sorry
  --rw [Algebra.algebraMap_eq_smul_one]
  sorry

open ComplexOrder in
/-- The matrix logarithm is operator concave. -/
theorem log_concave {x y : HermitianMat n 𝕜} (hx : x.toMat.PosDef) (hy : y.toMat.PosDef)
    ⦃a b : ℝ⦄ (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • x + b • y).log ≤ a • x.log + b • y.log := by
  sorry
