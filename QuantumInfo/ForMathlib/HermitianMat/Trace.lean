/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.Reindex

/-! # Trace of Hermitian Matrices

While the trace of a Hermitian matrix is, in informal math, typically just "the same as" a trace of
a matrix that happens to be Hermitian - it is a real number, not a complex number. Or more generally,
it is a self-adjoint element of the base `StarAddMonoid`.

Working directly with `Matrix.trace` then means that there would be constant casts between rings,
chasing imaginary parts and inequalities and so on. By defining `HermitianMat.trace` as its own
operation, we encapsulate the mess and give a clean interface.

The `IsMaximalSelfAdjoint` class is used so that (for example) for matrices over ℤ or ℝ,
`HermitianMat.trace` works as well and is in fact defeq to `Matrix.trace`. For ℂ or `RCLike`,
it uses the real part.
-/

namespace HermitianMat

variable {R n m α : Type*} [Star R] [TrivialStar R] [Fintype n] [Fintype m]

section star
variable [AddGroup α] [StarAddMonoid α] [CommSemiring R] [Semiring α] [Algebra R α] [IsMaximalSelfAdjoint R α]

/-- The trace of the matrix. This requires a `IsMaximalSelfAdjoint R α` instance, and then maps from
  `HermitianMat n α` to `R`. This means that the trace of (say) a `HermitianMat n ℤ` gives values in ℤ,
  but that the trace of a `HermitianMat n ℂ` gives values in ℝ. The fact that traces are "automatically"
  real reduces coercions down the line. -/
def trace (A : HermitianMat n α) : R :=
  IsMaximalSelfAdjoint.selfadjMap (A.toMat.trace)

/-- `HermitianMat.trace` reduces to `Matrix.trace` in the algebra.-/
theorem trace_eq_trace (A : HermitianMat n α) : algebraMap R α A.trace = Matrix.trace A.toMat := by
  rw [HermitianMat.trace, Matrix.trace, map_sum, map_sum]
  congr! 1
  exact IsMaximalSelfAdjoint.selfadj_algebra (Matrix.IsHermitian.apply A.H _ _)

variable [StarModule R α] in
@[simp]
theorem trace_smul (A : HermitianMat n α) (r : R) : (r • A).trace = r * A.trace := by
  simp [trace, IsMaximalSelfAdjoint.selfadj_smul]

end star
section semiring
variable [CommSemiring R] [Ring α] [StarAddMonoid α] [Algebra R α] [IsMaximalSelfAdjoint R α]

@[simp]
theorem trace_zero : (0 : HermitianMat n α).trace = 0 := by
  simp [trace]

@[simp]
theorem trace_add (A B : HermitianMat n α) : (A + B).trace = A.trace + B.trace := by
  simp [trace]

end semiring
section ring

variable [CommRing R] [Ring α] [StarAddMonoid α] [Algebra R α] [IsMaximalSelfAdjoint R α]
@[simp]
theorem trace_neg (A : HermitianMat n α) : (-A).trace = -A.trace := by
  simp [trace]

@[simp]
theorem trace_sub (A B : HermitianMat n α) : (A - B).trace = A.trace - B.trace := by
  simp [trace]

end ring
section starring

variable [CommRing R] [CommRing α] [StarRing α] [Algebra R α] [IsMaximalSelfAdjoint R α]

--PULLOUT
theorem _root_.Matrix.IsHermitian.isSelfAdjoint_trace {A : Matrix n n α} (hA : A.IsHermitian) :
    IsSelfAdjoint A.trace := by
  simp [Matrix.trace, IsSelfAdjoint, ← Matrix.star_apply, show star A = A from hA]

variable (A : HermitianMat m α) (B : HermitianMat n α)

@[simp]
theorem trace_kronecker [FaithfulSMul R α] : (A ⊗ₖ B).trace = A.trace * B.trace := by
  apply FaithfulSMul.algebraMap_injective R α
  simp only [trace, kronecker_coe]
  rw [Matrix.trace_kronecker A.toMat B.toMat]
  simp only [map_mul]
  have hA := A.H.isSelfAdjoint_trace
  have hB := B.H.isSelfAdjoint_trace
  open IsMaximalSelfAdjoint in
  rw [selfadj_algebra hA, selfadj_algebra hB, selfadj_algebra (hA.mul hB)]

end starring

section trivialstar

variable [Star α] [TrivialStar α] [CommSemiring α]

/-- `HermitianMat.trace` reduces to `Matrix.trace` when the elements are a `TrivialStar`. -/
@[simp]
theorem trace_eq_trace_trivial (A : HermitianMat n ℝ) : A.trace = Matrix.trace A.toMat := by
  rw [← trace_eq_trace]
  rfl

end trivialstar

section RCLike

variable {n m 𝕜 : Type*} [Fintype n] [Fintype m] [RCLike 𝕜]

--strictly speaking this works over any division ring, not just ℝ + RCLike
instance FiniteDimensional : FiniteDimensional ℝ (HermitianMat n 𝕜) :=
  FiniteDimensional.finiteDimensional_submodule (selfAdjoint.submodule ℝ (Matrix n n 𝕜))

theorem trace_eq_re_trace (A : HermitianMat n 𝕜) : A.trace = RCLike.re A.toMat.trace := by
  rfl

/-- `HermitianMat.trace` reduces to `Matrix.trace` when the elements are `RCLike`. -/
@[simp]
theorem trace_eq_trace_rc (A : HermitianMat n 𝕜) : ↑A.trace = A.toMat.trace := by
  rw [trace, Matrix.trace, map_sum, RCLike.ofReal_sum]
  congr 1
  exact Matrix.IsHermitian.coe_re_diag A.H

theorem trace_diagonal {T : Type*} [Fintype T] [DecidableEq T] (f : T → ℝ) :
    (diagonal 𝕜 f).trace = ∑ i, f i := by
  rw [trace_eq_re_trace]
  simp [HermitianMat.diagonal, Matrix.trace]

theorem sum_eigenvalues_eq_trace [DecidableEq n] (A : HermitianMat n 𝕜) :
    ∑ i, A.H.eigenvalues i = A.trace := by
  convert congrArg RCLike.re A.H.sum_eigenvalues_eq_trace
  rw [RCLike.ofReal_re]

--Proving that traces are 0 or 1 is common enough that we have a convenience lemma here for turning
--statements about HermitianMat traces into Matrix traces.
theorem trace_eq_zero_iff (A : HermitianMat n 𝕜) : A.trace = 0 ↔ A.toMat.trace = 0 := by
  rw [← trace_eq_trace_rc]
  use mod_cast id, mod_cast id

theorem trace_eq_one_iff (A : HermitianMat n 𝕜) : A.trace = 1 ↔ A.toMat.trace = 1 := by
  rw [← trace_eq_trace_rc]
  use mod_cast id, mod_cast id

@[simp]
theorem trace_reindex (A : HermitianMat n ℂ) (e : n ≃ m) :
    (A.reindex e).trace = A.trace := by
  simp [reindex, trace_eq_re_trace]

end RCLike
