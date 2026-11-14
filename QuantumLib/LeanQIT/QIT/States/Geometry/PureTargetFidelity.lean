/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Geometry.Fidelity
public import QIT.Core.Pure

/-!
# Squared fidelity against pure targets

For an explicit pure target, squared fidelity is the ordinary trace overlap.
Consequently it is affine in a finite weighted decomposition of the other
state, provided at the matrix level.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u v

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

private theorem pure_state_mul_state_mul_pure_state
    (rho : State a) (phi : PureVector a) :
    phi.state.matrix * rho.matrix * phi.state.matrix =
      ((rho.matrix * phi.state.matrix).trace) • phi.state.matrix := by
  let c : ℂ := (star phi.amp ᵥ* rho.matrix) ⬝ᵥ phi.amp
  have hc : c = (rho.matrix * phi.state.matrix).trace := by
    dsimp [c]
    simp only [Matrix.vecMul, dotProduct, rankOneMatrix, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Matrix.vecMulVec_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    ac_rfl
  rw [← hc]
  simp only [PureVector.state_matrix, rankOneMatrix]
  rw [Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
  change c • vecMulVec phi.amp (fun i => star (phi.amp i)) =
    c • vecMulVec phi.amp (fun i => star (phi.amp i))
  rfl

private theorem pure_state_sqrtMatrix (phi : PureVector a) :
    phi.state.sqrtMatrix = phi.state.matrix := by
  change psdSqrt phi.state.matrix = phi.state.matrix
  calc
    psdSqrt phi.state.matrix = psdSqrt (phi.state.matrix * phi.state.matrix) := by
      rw [phi.state_matrix_mul_self]
    _ = phi.state.matrix := by
      simpa [psdSqrt] using
        (CFC.sqrt_unique (b := phi.state.matrix) rfl phi.state.pos.nonneg)

/-- Squared fidelity against an explicit pure target is its trace overlap. -/
theorem State.squaredFidelity_pure_right_eq_trace
    (rho : State a) (phi : PureVector a) :
    rho.squaredFidelity phi.state =
      ((rho.matrix * phi.state.matrix).trace).re := by
  let P : CMatrix a := phi.state.matrix
  let M : CMatrix a := rho.sqrtMatrix * P
  let t : ℝ := ((rho.matrix * P).trace).re
  have hMstar : Matrix.conjTranspose M = P * rho.sqrtMatrix := by
    simp [M, P, Matrix.conjTranspose_mul, rho.sqrtMatrix_isHermitian.eq]
  have hgramC : Matrix.conjTranspose M * M = ((rho.matrix * P).trace) • P := by
    rw [hMstar]
    change P * rho.sqrtMatrix * (rho.sqrtMatrix * P) = ((rho.matrix * P).trace) • P
    rw [show P * rho.sqrtMatrix * (rho.sqrtMatrix * P) =
      P * (rho.sqrtMatrix * rho.sqrtMatrix) * P by noncomm_ring,
      rho.sqrtMatrix_mul_self]
    simpa [P] using pure_state_mul_state_mul_pure_state rho phi
  have hgramPos : (Matrix.conjTranspose M * M).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self M
  have hc : (rho.matrix * P).trace = (t : ℂ) := by
    apply Complex.ext
    · rfl
    · have him : (Matrix.conjTranspose M * M).trace.im = 0 :=
        (Matrix.PosSemidef.trace_nonneg hgramPos).2.symm
      rw [hgramC, Matrix.trace_smul, phi.state.trace_eq_one] at him
      simpa [t] using him
  have hgram : Matrix.conjTranspose M * M = (t : ℂ) • P := by
    rw [hgramC, hc]
  have ht0 : 0 <= t := by
    have htrace := (Matrix.PosSemidef.trace_nonneg hgramPos).1
    change 0 <= (Matrix.conjTranspose M * M).trace.re at htrace
    rw [hgram, Matrix.trace_smul, phi.state.trace_eq_one] at htrace
    simpa [t] using htrace
  have hsqrt : psdSqrt (Matrix.conjTranspose M * M) = (Real.sqrt t : ℂ) • P := by
    rw [hgram]
    apply CFC.sqrt_unique
    · change ((Real.sqrt t : ℂ) • P) * ((Real.sqrt t : ℂ) • P) = (t : ℂ) • P
      simp only [Matrix.smul_mul, Matrix.mul_smul]
      have hP : P * P = P := by simpa [P] using phi.state_matrix_mul_self
      rw [hP]
      have hcoeff : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = (t : ℂ) := by
        norm_cast
        simpa [pow_two] using Real.sq_sqrt ht0
      ext i j
      change (Real.sqrt t : ℂ) * ((Real.sqrt t : ℂ) * P i j) = (t : ℂ) * P i j
      rw [← mul_assoc, hcoeff]
    · apply Matrix.nonneg_iff_posSemidef.mpr
      simpa using phi.state.pos.smul (Real.sqrt_nonneg t)
  rw [State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq,
    pure_state_sqrtMatrix phi]
  change traceNorm M ^ 2 = t
  rw [traceNorm, hsqrt, Matrix.trace_smul, phi.state.trace_eq_one]
  simp [Real.sq_sqrt ht0]

/-- Squared fidelity against an explicit pure target is affine over a finite
weighted pure-state decomposition stated at the matrix level. -/
theorem State.squaredFidelity_sum_smul_pure_right
    {i : Type v} [Fintype i] (q : i -> NNReal) (phi : i -> PureVector a)
    (rho : State a)
    (hsum : (Finset.univ.sum fun j => (q j : ℂ) • (phi j).state.matrix) = rho.matrix)
    (target : PureVector a) :
    Finset.univ.sum (fun j => (q j : ℝ) *
      (phi j).state.squaredFidelity target.state) = rho.squaredFidelity target.state := by
  rw [State.squaredFidelity_pure_right_eq_trace rho target]
  calc
    Finset.univ.sum (fun j => (q j : ℝ) *
        (phi j).state.squaredFidelity target.state) =
        Finset.univ.sum (fun j =>
          (((q j : ℂ) * ((phi j).state.matrix * target.state.matrix).trace).re)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [State.squaredFidelity_pure_right_eq_trace]
          simp [Complex.mul_re]
    _ = ((Finset.univ.sum fun j =>
        ((q j : ℂ) • (phi j).state.matrix)) * target.state.matrix).trace.re := by
          simp [Finset.sum_mul, Matrix.trace_sum, Matrix.trace_smul, Complex.mul_re]
    _ = ((rho.matrix * target.state.matrix).trace).re := by rw [hsum]

end

end QIT
