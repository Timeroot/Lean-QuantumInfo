/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Purification.ReferenceUnitary
public import QIT.Util.SDP.HermitianPSDTraceDuality

/-!
# Pure-state projector geometry

This module packages the small pure-state rank-one projector geometry needed by
the purified-distance triangle route.  The key bridge is the Hilbert--Schmidt
square identity
`Tr((|ψ⟩⟨ψ| - |φ⟩⟨φ|)^2) = 2 * (1 - |⟨ψ|φ⟩|^2)`, plus the Frobenius
triangle inequality for these projectors.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

namespace PureVector

theorem rankOneMatrix_mul_trace_re_eq_overlapSq (ψ φ : PureVector a) :
    (rankOneMatrix ψ.amp * rankOneMatrix φ.amp).trace.re = ψ.overlapSq φ := by
  have htrace : (rankOneMatrix ψ.amp * rankOneMatrix φ.amp).trace =
      ψ.overlap φ * star (ψ.overlap φ) := by
    let C : ℂ := ψ.overlap φ
    change (Matrix.vecMulVec ψ.amp (fun i => star (ψ.amp i)) *
        Matrix.vecMulVec φ.amp (fun i => star (φ.amp i))).trace = _
    rw [Matrix.vecMulVec_mul_vecMulVec]
    simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ x, ψ.amp x * (C * star (φ.amp x))) = C * star C
    calc
      (∑ x, ψ.amp x * (C * star (φ.amp x))) =
          ∑ x, C * (star (φ.amp x) * ψ.amp x) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
      _ = C * (∑ x, star (φ.amp x) * ψ.amp x) := by
            simp [Finset.mul_sum]
      _ = C * star C := by
            congr 1
            simp [C, PureVector.overlap, mul_comm]
  rw [htrace, PureVector.overlapSq_eq_normSq]
  simp [Complex.normSq]

/-- Squared pure-state overlaps are symmetric. -/
theorem overlapSq_comm (ψ φ : PureVector a) :
    φ.overlapSq ψ = ψ.overlapSq φ := by
  have hover : φ.overlap ψ = star (ψ.overlap φ) := by
    simp [PureVector.overlap, mul_comm]
  rw [PureVector.overlapSq_eq_normSq, PureVector.overlapSq_eq_normSq, hover]
  simp

/--
The Hilbert--Schmidt square of the difference of two pure states is determined
by their squared overlap.
-/
theorem state_sub_state_sq_trace_re_eq_two_mul_one_sub_overlapSq (ψ φ : PureVector a) :
    (((ψ.state.matrix - φ.state.matrix) *
        (ψ.state.matrix - φ.state.matrix)).trace).re =
      2 * (1 - ψ.overlapSq φ) := by
  have hψψ : (ψ.state.matrix * ψ.state.matrix).trace.re = 1 := by
    rw [PureVector.state_matrix_mul_self, ψ.state.trace_eq_one]
    norm_num
  have hφφ : (φ.state.matrix * φ.state.matrix).trace.re = 1 := by
    rw [PureVector.state_matrix_mul_self, φ.state.trace_eq_one]
    norm_num
  have hψφ : (ψ.state.matrix * φ.state.matrix).trace.re = ψ.overlapSq φ := by
    simpa [PureVector.state_matrix] using rankOneMatrix_mul_trace_re_eq_overlapSq ψ φ
  have hφψ : (φ.state.matrix * ψ.state.matrix).trace.re = ψ.overlapSq φ := by
    have h := rankOneMatrix_mul_trace_re_eq_overlapSq φ ψ
    simpa [PureVector.state_matrix, overlapSq_comm ψ φ] using h
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub]
  rw [Complex.sub_re, Complex.sub_re, Complex.sub_re]
  rw [hψψ, hφφ, hψφ, hφψ]
  ring

/-- The pure-state overlap deficit is nonnegative. -/
theorem one_sub_overlapSq_nonneg (ψ φ : PureVector a) :
    0 ≤ 1 - ψ.overlapSq φ := by
  let D : CMatrix a := ψ.state.matrix - φ.state.matrix
  have hDherm : D.IsHermitian := ψ.state.pos.isHermitian.sub φ.state.pos.isHermitian
  have hstar : star D = D := hDherm.eq
  have htrace_nonneg : 0 ≤ ((star D * D).trace).re :=
    (Matrix.PosSemidef.trace_nonneg (Matrix.posSemidef_conjTranspose_mul_self D)).1
  have htrace : ((star D * D).trace).re = 2 * (1 - ψ.overlapSq φ) := by
    rw [hstar]
    exact state_sub_state_sq_trace_re_eq_two_mul_one_sub_overlapSq ψ φ
  rw [htrace] at htrace_nonneg
  nlinarith

private def frobeniusNorm (X : CMatrix a) : ℝ :=
  Real.sqrt ((X * Matrix.conjTranspose X).trace).re

private theorem frobeniusNorm_triangle (ψ φ ω : PureVector a) :
    frobeniusNorm (ψ.state.matrix - ω.state.matrix) ≤
      frobeniusNorm (ψ.state.matrix - φ.state.matrix) +
        frobeniusNorm (φ.state.matrix - ω.state.matrix) := by
  letI iSemi : SeminormedAddCommGroup (CMatrix a) :=
    (1 : CMatrix a).toMatrixSeminormedAddCommGroup Matrix.PosSemidef.one
  letI iInner : InnerProductSpace ℂ (CMatrix a) :=
    (1 : CMatrix a).toMatrixInnerProductSpace Matrix.PosSemidef.one
  have hnorm_eq_frob (X : CMatrix a) :
      @norm (CMatrix a) iSemi.toNorm X = frobeniusNorm X := by
    have hnorm_sq_eq :
        @norm (CMatrix a) iSemi.toNorm X ^ 2 =
          ((X * Matrix.conjTranspose X).trace).re := by
      rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ (CMatrix a)
          Complex.instRCLike iSemi iInner X]
      show ((X * (1 : CMatrix a) * Matrix.conjTranspose X).trace).re = _
      rw [Matrix.mul_one]
    have htrace_nonneg : 0 ≤ ((X * Matrix.conjTranspose X).trace).re :=
      (Matrix.PosSemidef.trace_nonneg (Matrix.posSemidef_self_mul_conjTranspose X)).1
    have hsq :
        @norm (CMatrix a) iSemi.toNorm X ^ 2 =
          Real.sqrt ((X * Matrix.conjTranspose X).trace).re ^ 2 := by
      rw [hnorm_sq_eq, Real.sq_sqrt htrace_nonneg]
    exact (sq_eq_sq₀ (norm_nonneg X) (Real.sqrt_nonneg _)).mp hsq
  have htri :
      @norm (CMatrix a) iSemi.toNorm (ψ.state.matrix - ω.state.matrix) ≤
        @norm (CMatrix a) iSemi.toNorm (ψ.state.matrix - φ.state.matrix) +
          @norm (CMatrix a) iSemi.toNorm (φ.state.matrix - ω.state.matrix) := by
    calc
      @norm (CMatrix a) iSemi.toNorm (ψ.state.matrix - ω.state.matrix)
          = @norm (CMatrix a) iSemi.toNorm
              ((ψ.state.matrix - φ.state.matrix) + (φ.state.matrix - ω.state.matrix)) := by
            congr 1
            abel
      _ ≤ @norm (CMatrix a) iSemi.toNorm (ψ.state.matrix - φ.state.matrix) +
            @norm (CMatrix a) iSemi.toNorm (φ.state.matrix - ω.state.matrix) :=
          norm_add_le _ _
  rw [hnorm_eq_frob] at htri
  rw [hnorm_eq_frob] at htri
  rw [hnorm_eq_frob] at htri
  exact htri

private theorem frobeniusNorm_state_sub_state_eq_sqrt_two_mul_one_sub_overlapSq
    (ψ φ : PureVector a) :
    frobeniusNorm (ψ.state.matrix - φ.state.matrix) =
      Real.sqrt (2 * (1 - ψ.overlapSq φ)) := by
  let D : CMatrix a := ψ.state.matrix - φ.state.matrix
  have hDherm : D.IsHermitian := ψ.state.pos.isHermitian.sub φ.state.pos.isHermitian
  have hstar : Matrix.conjTranspose D = D := hDherm.eq
  unfold frobeniusNorm
  rw [hstar]
  exact congrArg Real.sqrt (state_sub_state_sq_trace_re_eq_two_mul_one_sub_overlapSq ψ φ)

private theorem frobeniusNorm_state_sub_state_eq_sqrt_two_mul_sqrt_one_sub_overlapSq
    (ψ φ : PureVector a) :
    frobeniusNorm (ψ.state.matrix - φ.state.matrix) =
      Real.sqrt 2 * Real.sqrt (1 - ψ.overlapSq φ) := by
  rw [frobeniusNorm_state_sub_state_eq_sqrt_two_mul_one_sub_overlapSq]
  rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]

/--
The sine distance between pure rays, expressed as
`sqrt (1 - |⟨ψ|φ⟩|^2)`, satisfies the triangle inequality.
-/
theorem sqrt_one_sub_overlapSq_triangle (Ψ Φ Ω : PureVector a) :
    Real.sqrt (1 - Ψ.overlapSq Ω) ≤
      Real.sqrt (1 - Ψ.overlapSq Φ) +
      Real.sqrt (1 - Φ.overlapSq Ω) := by
  have htri := frobeniusNorm_triangle Ψ Φ Ω
  rw [frobeniusNorm_state_sub_state_eq_sqrt_two_mul_sqrt_one_sub_overlapSq] at htri
  rw [frobeniusNorm_state_sub_state_eq_sqrt_two_mul_sqrt_one_sub_overlapSq] at htri
  rw [frobeniusNorm_state_sub_state_eq_sqrt_two_mul_sqrt_one_sub_overlapSq] at htri
  have hsqrt_two_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  nlinarith

end PureVector

end

end QIT
