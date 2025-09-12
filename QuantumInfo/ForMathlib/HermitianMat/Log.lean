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
