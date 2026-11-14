/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.SmoothEndpoint

/-!
# Fidelity comparison under a conditional max-entropy scale bound

This file proves the cross-state fidelity/scale step used in the
min--max smoothing comparison.  The proof uses the fidelity block SDP: a
polar-unitary witness for `F(omega, tau)` remains feasible after enlarging its
lower-right block from `tau` to `t (I_A tensor sigma)` and rescaling.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal Pointwise

open Matrix

namespace QIT

universe u v

noncomputable section

namespace State

private theorem exists_fidelityBlock_trace_re_eq
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (omega tau : State alpha) :
    exists X : CMatrix alpha,
      (Matrix.fromBlocks omega.matrix X (star X) tau.matrix :
        CMatrix (Sum alpha alpha)).PosSemidef /\
      X.trace.re = omega.fidelity tau := by
  let H : CMatrix (Sum alpha alpha) :=
    Matrix.fromBlocks (1 : CMatrix alpha) (0 : CMatrix alpha)
      (0 : CMatrix alpha) 1
  obtain ⟨U, hU⟩ :=
    traceNorm_variational_exists_unitary_abs_trace (tau.sqrtMatrix * omega.sqrtMatrix)
  let X0 : CMatrix alpha :=
    omega.sqrtMatrix * (U : CMatrix alpha) * tau.sqrtMatrix
  have hblock0 :
      (Matrix.fromBlocks omega.matrix X0 (star X0) tau.matrix :
        CMatrix (Sum alpha alpha)).PosSemidef := by
    let G : CMatrix (Sum alpha alpha) :=
      Matrix.fromBlocks (1 : CMatrix alpha) (U : CMatrix alpha)
        (star (U : CMatrix alpha)) 1
    let S : CMatrix (Sum alpha alpha) :=
      Matrix.fromBlocks omega.sqrtMatrix 0 0 tau.sqrtMatrix
    have hG : G.PosSemidef := by
      simpa [G] using cMatrix_fromBlocks_unitary_posSemidef U
    have hconj : (S * G * star S).PosSemidef := by
      simpa [Matrix.mul_assoc] using hG.mul_mul_conjTranspose_same S
    have hEq :
        S * G * star S =
          (Matrix.fromBlocks omega.matrix X0 (star X0) tau.matrix :
            CMatrix (Sum alpha alpha)) := by
      have homegaH : omega.sqrtMatrixᴴ = omega.sqrtMatrix :=
        omega.sqrtMatrix_isHermitian.eq
      have htauH : tau.sqrtMatrixᴴ = tau.sqrtMatrix := tau.sqrtMatrix_isHermitian.eq
      have homegaSq : omega.sqrtMatrix * omega.sqrtMatrix = omega.matrix :=
        omega.sqrtMatrix_mul_self
      have htauSq : tau.sqrtMatrix * tau.sqrtMatrix = tau.matrix :=
        tau.sqrtMatrix_mul_self
      dsimp [S, G]
      change
        Matrix.fromBlocks omega.sqrtMatrix 0 0 tau.sqrtMatrix *
            Matrix.fromBlocks (1 : CMatrix alpha) (U : CMatrix alpha)
              (star (U : CMatrix alpha)) 1 *
              (Matrix.fromBlocks omega.sqrtMatrix 0 0 tau.sqrtMatrix)ᴴ =
          (Matrix.fromBlocks omega.matrix X0 (star X0) tau.matrix :
            CMatrix (Sum alpha alpha))
      rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
        Matrix.fromBlocks_multiply]
      ext i j
      cases i <;> cases j <;>
        simp [X0, homegaH, htauH, homegaSq, htauSq, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simpa [hEq] using hconj
  have htrace0 : Complex.abs X0.trace = omega.fidelity tau := by
    have htrace :
        X0.trace = ((tau.sqrtMatrix * omega.sqrtMatrix) *
          (U : CMatrix alpha)).trace := by
      calc
        X0.trace =
            ((omega.sqrtMatrix * (U : CMatrix alpha)) * tau.sqrtMatrix).trace := by
              simp [X0, Matrix.mul_assoc]
        _ = (tau.sqrtMatrix * (omega.sqrtMatrix *
              (U : CMatrix alpha))).trace := by
              rw [Matrix.trace_mul_comm]
        _ = ((tau.sqrtMatrix * omega.sqrtMatrix) *
              (U : CMatrix alpha)).trace := by
              rw [Matrix.mul_assoc]
    have hconj :
        tau.sqrtMatrix * omega.sqrtMatrix =
          Matrix.conjTranspose (omega.sqrtMatrix * tau.sqrtMatrix) := by
      rw [Matrix.conjTranspose_mul, omega.sqrtMatrix_isHermitian.eq,
        tau.sqrtMatrix_isHermitian.eq]
    calc
      Complex.abs X0.trace =
          Complex.abs (((tau.sqrtMatrix * omega.sqrtMatrix) *
            (U : CMatrix alpha)).trace) := by rw [htrace]
      _ = traceNorm (tau.sqrtMatrix * omega.sqrtMatrix) := hU
      _ = traceNorm (omega.sqrtMatrix * tau.sqrtMatrix) := by
        rw [hconj, traceNorm_conjTranspose]
      _ = omega.fidelity tau := by rfl
  rcases exists_complex_phase_mul_re_eq_abs X0.trace with ⟨c, hc, hcTrace⟩
  let D : CMatrix (Sum alpha alpha) :=
    Matrix.fromBlocks (1 : CMatrix alpha) 0 0
      ((star c) • (1 : CMatrix alpha))
  have hc' : c * (starRingEnd ℂ) c = 1 := by simpa using hc
  have hphase :
      (Matrix.fromBlocks omega.matrix (c • X0) (star (c • X0)) tau.matrix :
        CMatrix (Sum alpha alpha)).PosSemidef := by
    have hconj :
        (D *
            (Matrix.fromBlocks omega.matrix X0 (star X0) tau.matrix :
              CMatrix (Sum alpha alpha)) * star D).PosSemidef :=
      hblock0.mul_mul_conjTranspose_same D
    have hEq :
        D *
            (Matrix.fromBlocks omega.matrix X0 (star X0) tau.matrix :
              CMatrix (Sum alpha alpha)) * star D =
          (Matrix.fromBlocks omega.matrix (c • X0) (star (c • X0)) tau.matrix :
            CMatrix (Sum alpha alpha)) := by
      dsimp [D]
      simp_rw [Matrix.star_eq_conjTranspose]
      rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
        Matrix.fromBlocks_multiply]
      ext i j
      cases i <;> cases j <;> simp [← mul_assoc, hc']
    simpa [hEq] using hconj
  refine ⟨c • X0, hphase, ?_⟩
  have htrace : (c • X0).trace = c * X0.trace := by
    simp [Matrix.trace, Finset.mul_sum]
  rw [htrace, hcTrace, htrace0]

/-- A state domination `tau <= t (I_A tensor sigma)` produces a feasible
conditional-max fidelity block whose exponent is `F(omega,tau)^2 / t`.

This is the unconditional exponent-level form of the cross-state comparison;
it remains meaningful when the two states have zero fidelity. -/
theorem exists_conditionalMaxFidelityBlockFeasible_of_le_scaled_identityTensor
    {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] [Nonempty b]
    (omega tau : State (Prod a b)) (sigma : State b) {t : ℝ}
    (ht : 0 < t)
    (htau : tau.matrix <= ((t : ℂ) • identityTensorStateMatrix (a := a) sigma)) :
    exists X : CMatrix (Prod a b),
      ConditionalMaxFidelityBlockFeasible (a := a) omega sigma X /\
      conditionalMaxFidelityBlockExponentValue (a := a) X =
        (omega.fidelity tau) ^ 2 / t := by
  classical
  let piSigma : State (Prod a b) := (maximallyMixed a).prod sigma
  let d : ℝ := t * Fintype.card a
  have hcard : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hd : 0 < d := mul_pos ht hcard
  have htau' : tau.matrix <= ((d : ℂ) • piSigma.matrix) := by
    rw [identityTensorStateMatrix_eq_card_smul_maximallyMixed_prod (a := a)] at htau
    simpa [d, piSigma, smul_smul, mul_assoc] using htau
  rcases exists_fidelityBlock_trace_re_eq omega tau with ⟨X0, hX0, htrace0⟩
  have hdiff : (((d : ℂ) • piSigma.matrix) - tau.matrix).PosSemidef := by
    simpa [Matrix.le_iff] using htau'
  have hdiag :
      (Matrix.fromBlocks (0 : CMatrix (Prod a b)) 0 0
        (((d : ℂ) • piSigma.matrix) - tau.matrix) :
        CMatrix (Sum (Prod a b) (Prod a b))).PosSemidef :=
    cMatrix_fromBlocks_diagonal_posSemidef Matrix.PosSemidef.zero hdiff
  have henlarged :
      (Matrix.fromBlocks omega.matrix X0 (star X0) ((d : ℂ) • piSigma.matrix) :
        CMatrix (Sum (Prod a b) (Prod a b))).PosSemidef := by
    have hadd := hX0.add hdiag
    convert hadd using 1
    ext i j
    cases i
    · cases j
      · simp [Matrix.fromBlocks, Matrix.of_apply]
      · simp [Matrix.fromBlocks, Matrix.of_apply]
    · cases j
      · simp [Matrix.fromBlocks, Matrix.of_apply]
      · simp [Matrix.fromBlocks, Matrix.of_apply]
  let r : ℝ := (Real.sqrt d)⁻¹
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hr : 0 < r := inv_pos.mpr hsqrt
  have hrdr : r * d * r = 1 := by
    dsimp [r]
    field_simp [hsqrt.ne']
    nlinarith [Real.sq_sqrt hd.le]
  let D : CMatrix (Sum (Prod a b) (Prod a b)) :=
    Matrix.fromBlocks (1 : CMatrix (Prod a b)) 0 0
      (((r : ℝ) : ℂ) • (1 : CMatrix (Prod a b)))
  let X : CMatrix (Prod a b) := (((r : ℝ) : ℂ) • X0)
  have hscaled :
      ConditionalMaxFidelityBlockFeasible (a := a) omega sigma X := by
    have hconj :
        (D *
            (Matrix.fromBlocks omega.matrix X0 (star X0)
              ((d : ℂ) • piSigma.matrix) :
              CMatrix (Sum (Prod a b) (Prod a b))) * star D).PosSemidef :=
      henlarged.mul_mul_conjTranspose_same D
    have hrdrC : ((r : ℂ) * (d : ℂ) * (r : ℂ)) = 1 := by
      exact_mod_cast hrdr
    have hEq :
        D *
            (Matrix.fromBlocks omega.matrix X0 (star X0)
              ((d : ℂ) • piSigma.matrix) :
              CMatrix (Sum (Prod a b) (Prod a b))) * star D =
          (Matrix.fromBlocks omega.matrix X (star X) piSigma.matrix :
            CMatrix (Sum (Prod a b) (Prod a b))) := by
      dsimp [D, X]
      simp_rw [Matrix.star_eq_conjTranspose]
      rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
        Matrix.fromBlocks_multiply]
      ext i j
      cases i <;> cases j <;>
        simp [piSigma, ← mul_assoc, hrdrC]
    have hconj' :
        (Matrix.fromBlocks omega.matrix X (star X) piSigma.matrix :
          CMatrix (Sum (Prod a b) (Prod a b))).PosSemidef := by
      rw [← hEq]
      exact hconj
    simpa [ConditionalMaxFidelityBlockFeasible, piSigma] using hconj'
  refine ⟨X, hscaled, ?_⟩
  have htrace : X.trace.re = r * omega.fidelity tau := by
    dsimp [X]
    rw [Matrix.trace_smul]
    simp [htrace0]
  rw [conditionalMaxFidelityBlockExponentValue_eq, htrace]
  have hrsq : r ^ 2 = d⁻¹ := by
    field_simp [hd.ne']
    nlinarith [hrdr]
  rw [mul_pow, hrsq]
  dsimp [d]
  field_simp [ht.ne', hcard.ne']

/-- Unconditional cross-state fidelity/exponent comparison. -/
theorem fidelity_sq_div_le_conditionalMaxEntropyExponent_of_le_scaled_identityTensor
    {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] [Nonempty b]
    (omega tau : State (Prod a b)) (sigma : State b) {t : ℝ}
    (ht : 0 < t)
    (htau : tau.matrix <= ((t : ℂ) • identityTensorStateMatrix (a := a) sigma)) :
    (omega.fidelity tau) ^ 2 / t <=
      omega.conditionalMaxEntropyExponent (a := a) := by
  rcases exists_conditionalMaxFidelityBlockFeasible_of_le_scaled_identityTensor
      (a := a) omega tau sigma ht htau with ⟨X, hX, hvalue⟩
  rw [← hvalue]
  exact hX.blockExponentValue_le_conditionalMaxEntropyExponent

/-- The logarithmic cross-state comparison when the fidelity is nonzero.

The positivity hypothesis is exactly what is needed by the repository's
finite-real logarithm convention. -/
theorem neg_log2_add_log2_fidelity_sq_le_conditionalMaxEntropy
    {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] [Nonempty b]
    (omega tau : State (Prod a b)) (sigma : State b) {t : ℝ}
    (ht : 0 < t) (hfidelity : 0 < omega.fidelity tau)
    (htau : tau.matrix <= ((t : ℂ) • identityTensorStateMatrix (a := a) sigma)) :
    -log2 t + log2 ((omega.fidelity tau) ^ 2) <=
      omega.conditionalMaxEntropy := by
  have hquot_pos : 0 < (omega.fidelity tau) ^ 2 / t :=
    div_pos (sq_pos_of_pos hfidelity) ht
  have hraw :=
    fidelity_sq_div_le_conditionalMaxEntropyExponent_of_le_scaled_identityTensor
      (a := a) omega tau sigma ht htau
  have hexp_pos := omega.conditionalMaxEntropyExponent_pos (a := a)
  have hlog :
      log2 ((omega.fidelity tau) ^ 2 / t) <=
        log2 (omega.conditionalMaxEntropyExponent (a := a)) := by
    unfold log2
    exact div_le_div_of_nonneg_right (Real.log_le_log hquot_pos hraw)
      (le_of_lt (Real.log_pos one_lt_two))
  rw [omega.conditionalMaxEntropy_eq_positive (a := a),
    omega.conditionalMaxEntropyPositive_eq_log2_exponent_of_nonempty (a := a)]
  have hlog_div :
      log2 ((omega.fidelity tau) ^ 2 / t) =
        log2 ((omega.fidelity tau) ^ 2) - log2 t := by
    unfold log2
    rw [Real.log_div (sq_pos_of_pos hfidelity).ne' ht.ne']
    ring
  rw [hlog_div] at hlog
  linarith

/-- Zero-aware, assumption-free logarithmic form of the comparison. -/
theorem fidelity_eq_zero_or_neg_log2_add_log2_fidelity_sq_le_conditionalMaxEntropy
    {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] [Nonempty b]
    (omega tau : State (Prod a b)) (sigma : State b) {t : ℝ}
    (ht : 0 < t)
    (htau : tau.matrix <= ((t : ℂ) • identityTensorStateMatrix (a := a) sigma)) :
    omega.fidelity tau = 0 \/
      -log2 t + log2 ((omega.fidelity tau) ^ 2) <=
        omega.conditionalMaxEntropy := by
  rcases (State.fidelity_nonneg omega tau).eq_or_lt with hzero | hpos
  · exact Or.inl hzero.symm
  · exact Or.inr
      (neg_log2_add_log2_fidelity_sq_le_conditionalMaxEntropy
        (a := a) omega tau sigma ht hpos htau)

end State

end

end QIT
