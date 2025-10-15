/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
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

theorem log_smul (A : HermitianMat n 𝕜) (x : ℝ) : (x • A).log = Real.log x • 1 + A.log := by
  rw [log, log, HermitianMat.ext_iff]
  simp only [selfAdjoint.val_smul, val_eq_coe, AddSubgroup.coe_add, selfAdjoint.val_one]
  --#25194 landed in Mathlib but we still have an extra `NormedRing` hypothesis there that we don't really want
  --also I think this theorem needs a hypothesis about `A` being posdef, otherwise 0 is in its spectrum and
  --this isn't true

  --convert CFC.log_smul (r := x) (a := a.toMat) sorry sorry sorry
  --rw [Algebra.algebraMap_eq_smul_one]
  sorry

open ComplexOrder in
/-- The matrix logarithm is operator concave. -/
theorem log_concave {x y : HermitianMat n 𝕜} (hx : x.toMat.PosDef) (hy : y.toMat.PosDef)
    ⦃a b : ℝ⦄ (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • x + b • y).log ≤ a • x.log + b • y.log := by
  sorry
