/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.PosSqrt
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Topology.Instances.Matrix

/-!
# Trace distance

The trace norm (Schatten 1-norm) ‖M‖₁ = Tr √(Mᴴ M), trace distance,
and normalized trace distance API for finite-dimensional matrices and density
states. The source gate is registered under
`m5-trace-norm-definition-and-singular-values` and
`m5-trace-distance-definition-and-bounds`.

This module intentionally records only locally provable facts. Spectral trace
norm formulas, triangle inequalities, state upper bounds, and Fuchs-van de
Graaf remain downstream proof obligations.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open Matrix

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

noncomputable local instance cMatrixCStarAlgebraForDistanceContinuity {ι : Type u}
    [Fintype ι] [DecidableEq ι] :
    CStarAlgebra (Matrix ι ι ℂ) where

/-- The trace norm (Schatten 1-norm) ‖M‖₁ = Tr √(Mᴴ M). -/
def traceNorm (M : CMatrix a) : ℝ :=
  (psdSqrt (Mᴴ * M)).trace.re

/-- The CFC square root of the zero matrix is zero. -/
@[simp]
theorem psdSqrt_zero : psdSqrt (0 : CMatrix a) = 0 := by
  simp [psdSqrt]

/-- The trace norm is nonnegative. -/
theorem traceNorm_nonneg (M : CMatrix a) : 0 ≤ traceNorm M := by
  rw [traceNorm]
  have h : 0 ≤ (psdSqrt (Matrix.conjTranspose M * M)).trace :=
    Matrix.PosSemidef.trace_nonneg (psdSqrt_pos (Matrix.conjTranspose M * M))
  have hre := (Complex.nonneg_iff.mp h).1
  simpa using hre

/-- For a positive semidefinite matrix, the trace norm is the real trace. -/
theorem traceNorm_posSemidef_eq_trace_re
    (A : CMatrix a) (hA : A.PosSemidef) :
    traceNorm A = A.trace.re := by
  rw [traceNorm]
  have hherm : Matrix.conjTranspose A = A := hA.isHermitian.eq
  have hsqrt : psdSqrt (Matrix.conjTranspose A * A) = A := by
    rw [hherm]
    simpa [psdSqrt, sq] using (CFC.sqrt_sq A hA.nonneg)
  rw [hsqrt]

/-- The zero matrix has trace norm zero. -/
@[simp]
theorem traceNorm_zero : traceNorm (0 : CMatrix a) = 0 := by
  simp [traceNorm]

/-- The trace norm is invariant under negation. -/
@[simp]
theorem traceNorm_neg (M : CMatrix a) : traceNorm (-M) = traceNorm M := by
  simp [traceNorm]

/-- Unnormalized trace norm of the difference, `‖M - N‖₁ ∈ [0, 2]`.  The standard
QIT trace distance `½ * ‖M - N‖₁ ∈ [0, 1]` is `normalizedTraceDistance`. -/
def traceNormDistance (M N : CMatrix a) : ℝ :=
  traceNorm (M - N)

/-- Normalized trace distance, using the QIT convention `1 / 2 * ‖M - N‖₁`. -/
def normalizedTraceDistance (M N : CMatrix a) : ℝ :=
  (1 / 2 : ℝ) * traceNormDistance M N

@[simp]
theorem traceNormDistance_eq_traceNorm_sub (M N : CMatrix a) :
    traceNormDistance M N = traceNorm (M - N) :=
  rfl

/-- The unnormalized trace-norm distance is nonnegative. -/
theorem traceNormDistance_nonneg (M N : CMatrix a) : 0 ≤ traceNormDistance M N :=
  traceNorm_nonneg (M - N)

@[simp]
theorem traceNormDistance_self (M : CMatrix a) : traceNormDistance M M = 0 := by
  simp [traceNormDistance]

/-- The unnormalized trace-norm distance is symmetric. -/
theorem traceNormDistance_comm (M N : CMatrix a) :
    traceNormDistance M N = traceNormDistance N M := by
  calc
    traceNormDistance M N = traceNorm (M - N) := rfl
    _ = traceNorm (-(M - N)) := by rw [traceNorm_neg]
    _ = traceNormDistance N M := by simp [traceNormDistance, sub_eq_add_neg]

@[simp]
theorem normalizedTraceDistance_eq (M N : CMatrix a) :
    normalizedTraceDistance M N = (1 / 2 : ℝ) * traceNormDistance M N :=
  rfl

/-- Normalized trace distance is nonnegative. -/
theorem normalizedTraceDistance_nonneg (M N : CMatrix a) :
    0 ≤ normalizedTraceDistance M N :=
  mul_nonneg (by norm_num) (traceNormDistance_nonneg M N)

@[simp]
theorem normalizedTraceDistance_self (M : CMatrix a) :
    normalizedTraceDistance M M = 0 := by
  simp [normalizedTraceDistance]

/-- Normalized trace distance is symmetric. -/
theorem normalizedTraceDistance_comm (M N : CMatrix a) :
    normalizedTraceDistance M N = normalizedTraceDistance N M := by
  rw [normalizedTraceDistance, normalizedTraceDistance, traceNormDistance_comm]

omit [Fintype a] [DecidableEq a] in
private theorem decouplingTraceNorm_continuous [Fintype a] [DecidableEq a] :
    Continuous (traceNorm : CMatrix a → ℝ) := by
  have hgram : Continuous (fun M : CMatrix a => star M * M) := by
    exact (Continuous.star continuous_id).matrix_mul continuous_id
  have hnonneg : ∀ M : CMatrix a, (star M * M) ∈ {A : CMatrix a | 0 ≤ A} := by
    intro M
    exact Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.posSemidef_conjTranspose_mul_self M)
  have hsqrtOn :
      ContinuousOn (CFC.sqrt : CMatrix a → CMatrix a) {A : CMatrix a | 0 ≤ A} := by
    exact CFC.continuousOn_sqrt
  have hsqrt : Continuous (fun M : CMatrix a => CFC.sqrt (star M * M)) := by
    exact hsqrtOn.comp_continuous hgram hnonneg
  have htrace : Continuous (fun M : CMatrix a => (CFC.sqrt (star M * M)).trace) :=
    Continuous.matrix_trace hsqrt
  simpa [traceNorm, psdSqrt] using Complex.continuous_re.comp htrace

omit [Fintype a] [DecidableEq a] in
/-- The trace norm is continuous on finite-dimensional complex matrices. -/
theorem traceNorm_continuous [Fintype a] [DecidableEq a] :
    Continuous (traceNorm : CMatrix a → ℝ) :=
  decouplingTraceNorm_continuous

namespace State

/-- Unnormalized trace norm of the difference of two states' matrices,
`‖ρ.matrix - σ.matrix‖₁ ∈ [0, 2]`.  The standard QIT trace distance
`½ * ‖·‖₁ ∈ [0, 1]` is `State.normalizedTraceDistance`. -/
def traceNormDistance (rho sigma : State a) : ℝ :=
  QIT.traceNormDistance rho.matrix sigma.matrix

/-- Normalized trace distance between density states. -/
def normalizedTraceDistance (rho sigma : State a) : ℝ :=
  QIT.normalizedTraceDistance rho.matrix sigma.matrix

@[simp]
theorem traceNormDistance_eq_matrix (rho sigma : State a) :
    rho.traceNormDistance sigma = QIT.traceNormDistance rho.matrix sigma.matrix :=
  rfl

theorem traceNormDistance_nonneg (rho sigma : State a) :
    0 ≤ rho.traceNormDistance sigma :=
  QIT.traceNormDistance_nonneg rho.matrix sigma.matrix

@[simp]
theorem traceNormDistance_self (rho : State a) : rho.traceNormDistance rho = 0 := by
  simp [State.traceNormDistance]

theorem traceNormDistance_comm (rho sigma : State a) :
    rho.traceNormDistance sigma = sigma.traceNormDistance rho :=
  QIT.traceNormDistance_comm rho.matrix sigma.matrix

@[simp]
theorem normalizedTraceDistance_eq_matrix (rho sigma : State a) :
    rho.normalizedTraceDistance sigma =
      QIT.normalizedTraceDistance rho.matrix sigma.matrix :=
  rfl

theorem normalizedTraceDistance_nonneg (rho sigma : State a) :
    0 ≤ rho.normalizedTraceDistance sigma :=
  QIT.normalizedTraceDistance_nonneg rho.matrix sigma.matrix

@[simp]
theorem normalizedTraceDistance_self (rho : State a) :
    rho.normalizedTraceDistance rho = 0 := by
  simp [State.normalizedTraceDistance]

theorem normalizedTraceDistance_comm (rho sigma : State a) :
    rho.normalizedTraceDistance sigma = sigma.normalizedTraceDistance rho :=
  QIT.normalizedTraceDistance_comm rho.matrix sigma.matrix

end State

end

end QIT
