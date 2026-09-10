/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.States.PosSqrt
public import QuantumLib.QIT.Util.MatrixInstances
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

This module records the definitions and the facts provable directly from them.
The singular-value formula is in `QuantumLib.QIT.States.TraceNorm.Spectral`, the
variational characterization and the triangle inequality are in
`QuantumLib.QIT.States.TraceNorm.Variational`, and Fuchs-van de Graaf is in
`QuantumLib.QIT.States.Geometry.FuchsVdG`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator QIT.MatrixL2

open Matrix

noncomputable section
universe u
variable {a : Type u} [Fintype a] [DecidableEq a]

open QIT

namespace QIT

/-- The trace norm (Schatten 1-norm) ‖M‖₁ = Tr √(Mᴴ M). -/
def traceNorm (M : CMatrix a) : ℝ :=
  (psdSqrt (Mᴴ * M)).trace.re

/-- The CFC square root of the zero matrix is zero. -/
@[simp]
theorem psdSqrt_zero : psdSqrt (0 : CMatrix a) = 0 := by
  simp [psdSqrt]

/-- On a one-point index the square root of the constant matrix `r` is the constant
matrix `√r`. -/
theorem punit_psdSqrt_const (r : ℝ) (hr : 0 ≤ r) :
    psdSqrt (Matrix.of fun _ _ : PUnit => ((r : ℝ) : ℂ) : CMatrix PUnit) =
      (Matrix.of fun _ _ : PUnit => ((Real.sqrt r : ℝ) : ℂ) : CMatrix PUnit) := by
  let A : CMatrix PUnit := Matrix.of fun _ _ => ((r : ℝ) : ℂ)
  let S : CMatrix PUnit := Matrix.of fun _ _ => ((Real.sqrt r : ℝ) : ℂ)
  have hsqrt_sq : ((Real.sqrt r : ℂ) * (Real.sqrt r : ℂ)) = (r : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr]
  have hSsq : S * S = A := by
    ext i j
    cases i
    cases j
    simp [S, A, Matrix.mul_apply, hsqrt_sq]
  have hSpos : S.PosSemidef := by
    have hdiag : S = Matrix.diagonal (fun _ : PUnit => ((Real.sqrt r : ℝ) : ℂ)) := by
      ext i j
      cases i
      cases j
      simp [S, Matrix.diagonal]
    rw [hdiag]
    exact Matrix.PosSemidef.diagonal fun _ =>
      Complex.nonneg_iff.mpr ⟨Real.sqrt_nonneg r, by simp⟩
  change psdSqrt A = S
  simpa [psdSqrt] using (CFC.sqrt_unique (a := A) (b := S) hSsq hSpos.nonneg)

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

/-- On a one-point index the constant matrix `r ≥ 0` has trace norm `r`. -/
theorem traceNorm_punit_const_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    traceNorm (Matrix.of fun _ _ : PUnit => ((r : ℝ) : ℂ) : CMatrix PUnit) = r := by
  let A : CMatrix PUnit := Matrix.of fun _ _ => ((r : ℝ) : ℂ)
  have hgram : Aᴴ * A = (Matrix.of fun _ _ : PUnit => ((r * r : ℝ) : ℂ) : CMatrix PUnit) := by
    ext i j
    cases i
    cases j
    simp [A, Matrix.mul_apply, ← Complex.ofReal_mul]
  have hsqrt : psdSqrt (Aᴴ * A) = A := by
    rw [hgram, punit_psdSqrt_const (r * r) (mul_self_nonneg r)]
    ext i j
    cases i
    cases j
    simp [A, Real.sqrt_mul_self hr]
  rw [traceNorm, hsqrt]
  simp [A, Matrix.trace]

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

theorem normalizedTraceDistance_self (M : CMatrix a) :
    normalizedTraceDistance M M = 0 := by
  simp [normalizedTraceDistance]

/-- Normalized trace distance is symmetric. -/
theorem normalizedTraceDistance_comm (M N : CMatrix a) :
    normalizedTraceDistance M N = normalizedTraceDistance N M := by
  rw [normalizedTraceDistance, normalizedTraceDistance, traceNormDistance_comm]

omit [Fintype a] [DecidableEq a] in
/-- The trace norm is continuous on finite-dimensional complex matrices. -/
theorem traceNorm_continuous [Fintype a] [DecidableEq a] :
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
  have heq : (traceNorm : CMatrix a → ℝ) =
      Complex.re ∘ fun M : CMatrix a => (CFC.sqrt (star M * M)).trace := rfl
  rw [heq]
  exact Complex.continuous_re.comp htrace

end QIT

namespace MState

/-- Unnormalized trace norm of the difference of two states' matrices,
`‖ρ.m - σ.m‖₁ ∈ [0, 2]`.  The standard QIT trace distance
`½ * ‖·‖₁ ∈ [0, 1]` is `MState.normalizedTraceDistance`. -/
def traceNormDistance (rho sigma : MState a) : ℝ :=
  QIT.traceNormDistance rho.m sigma.m

/-- Normalized trace distance between density states. -/
def normalizedTraceDistance (rho sigma : MState a) : ℝ :=
  QIT.normalizedTraceDistance rho.m sigma.m

@[simp]
theorem traceNormDistance_eq_matrix (rho sigma : MState a) :
    rho.traceNormDistance sigma = QIT.traceNormDistance rho.m sigma.m :=
  rfl

theorem traceNormDistance_nonneg (rho sigma : MState a) :
    0 ≤ rho.traceNormDistance sigma :=
  QIT.traceNormDistance_nonneg rho.m sigma.m

theorem traceNormDistance_self (rho : MState a) : rho.traceNormDistance rho = 0 := by
  simp [MState.traceNormDistance]

theorem traceNormDistance_comm (rho sigma : MState a) :
    rho.traceNormDistance sigma = sigma.traceNormDistance rho :=
  QIT.traceNormDistance_comm rho.m sigma.m

@[simp]
theorem normalizedTraceDistance_eq_matrix (rho sigma : MState a) :
    rho.normalizedTraceDistance sigma =
      QIT.normalizedTraceDistance rho.m sigma.m :=
  rfl

theorem normalizedTraceDistance_nonneg (rho sigma : MState a) :
    0 ≤ rho.normalizedTraceDistance sigma :=
  QIT.normalizedTraceDistance_nonneg rho.m sigma.m

theorem normalizedTraceDistance_self (rho : MState a) :
    rho.normalizedTraceDistance rho = 0 := by
  simp [MState.normalizedTraceDistance]

theorem normalizedTraceDistance_comm (rho sigma : MState a) :
    rho.normalizedTraceDistance sigma = sigma.normalizedTraceDistance rho :=
  QIT.normalizedTraceDistance_comm rho.m sigma.m

end MState
