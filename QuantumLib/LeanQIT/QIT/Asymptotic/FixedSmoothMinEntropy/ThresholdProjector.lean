/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Asymptotic.FixedSmoothMinEntropy.PetzWitness
public import QIT.States.TraceNorm.BlockMatrix

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker NNReal
open Filter

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
namespace State
/-! ### Fixed-reference threshold projector bridge -/

/-- Hermitian fixed-reference threshold matrix
`ρ_AB - λ (I_A ⊗ σ_B)`.

This is the conditional analogue of the state-vs-state threshold matrix used
in the hypothesis-testing/Petz comparison file. -/
def fixedPetzThresholdMatrix
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) : CMatrix (Prod a b) :=
  ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ

theorem fixedPetzThresholdMatrix_isHermitian
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdMatrix σ lambda).IsHermitian := by
  unfold fixedPetzThresholdMatrix identityTensorStateMatrix
  exact ρ.pos.isHermitian.sub
    ((identityTensorStateMatrix_posSemidef_of_state (a := a) σ).isHermitian.smul
      (IsSelfAdjoint.all lambda))

/-- Positive spectral projector of
`ρ_AB - λ (I_A ⊗ σ_B)` for the fixed-reference threshold construction. -/
def fixedPetzThresholdProjector
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) : CMatrix (Prod a b) :=
  positiveSpectralProjector
    (ρ.fixedPetzThresholdMatrix σ lambda)
    (ρ.fixedPetzThresholdMatrix_isHermitian σ lambda)

theorem fixedPetzThresholdProjector_posSemidef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdProjector σ lambda).PosSemidef := by
  unfold fixedPetzThresholdProjector
  exact positiveSpectralProjector_posSemidef
    (ρ.fixedPetzThresholdMatrix σ lambda)
    (ρ.fixedPetzThresholdMatrix_isHermitian σ lambda)

theorem fixedPetzThresholdProjector_isHermitian
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdProjector σ lambda).IsHermitian :=
  (ρ.fixedPetzThresholdProjector_posSemidef σ lambda).isHermitian

theorem fixedPetzThresholdProjector_idempotent
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ρ.fixedPetzThresholdProjector σ lambda *
        ρ.fixedPetzThresholdProjector σ lambda =
      ρ.fixedPetzThresholdProjector σ lambda := by
  unfold fixedPetzThresholdProjector
  exact positiveSpectralProjector_idempotent
    (ρ.fixedPetzThresholdMatrix σ lambda)
    (ρ.fixedPetzThresholdMatrix_isHermitian σ lambda)

theorem fixedPetzThresholdProjector_le_one
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ρ.fixedPetzThresholdProjector σ lambda ≤ 1 := by
  unfold fixedPetzThresholdProjector
  exact positiveSpectralProjector_le_one
    (ρ.fixedPetzThresholdMatrix σ lambda)
    (ρ.fixedPetzThresholdMatrix_isHermitian σ lambda)

private theorem one_sub_positiveSpectralProjector_mul_neg_self_eq_negPart_fixed
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : CMatrix ι) (hH : H.IsHermitian) :
    (1 - positiveSpectralProjector H hH) * (-H) = H⁻ := by
  let P := positiveSpectralProjector H hH
  have hPH : P * H = H⁺ := positiveSpectralProjector_mul_self_eq_posPart H hH
  have hsub : H⁺ - H⁻ = H := CFC.posPart_sub_negPart H hH.isSelfAdjoint
  have hQH : (1 - P) * H = -H⁻ := by
    calc
      (1 - P) * H = H - P * H := by simp [sub_mul]
      _ = H - H⁺ := by rw [hPH]
      _ = -H⁻ := by
        nth_rewrite 1 [← hsub]
        abel
  calc
    (1 - P) * (-H) = -((1 - P) * H) := by rw [mul_neg]
    _ = -(-H⁻) := by rw [hQH]
    _ = H⁻ := by simp

/-- On the complement of the fixed-reference positive threshold projector,
`λ(I_A ⊗ σ_B) - ρ_AB` is positive semidefinite after left selection.

This is the matrix-order core needed before a postselection/normalization
bridge can turn the threshold effect into a smoothed min-entropy witness. -/
theorem fixedPetzThresholdComplement_mul_gap_posSemidef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ((1 - ρ.fixedPetzThresholdProjector σ lambda) *
        (lambda • identityTensorStateMatrix (a := a) σ - ρ.matrix)).PosSemidef := by
  let H : CMatrix (Prod a b) := ρ.fixedPetzThresholdMatrix σ lambda
  let hH : H.IsHermitian := ρ.fixedPetzThresholdMatrix_isHermitian σ lambda
  have hselect :
      (1 - positiveSpectralProjector H hH) * (-H) = H⁻ :=
    one_sub_positiveSpectralProjector_mul_neg_self_eq_negPart_fixed H hH
  have hneg : (H⁻).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H)
  have hmatrix :
      (1 - ρ.fixedPetzThresholdProjector σ lambda) *
          (lambda • identityTensorStateMatrix (a := a) σ - ρ.matrix) =
        H⁻ := by
    simpa [H, hH, fixedPetzThresholdProjector, fixedPetzThresholdMatrix,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hselect
  rw [hmatrix]
  exact hneg

/-- Complement projection matrix for the fixed-reference Petz threshold. -/
def fixedPetzThresholdComplementProjector
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) : CMatrix (Prod a b) :=
  1 - ρ.fixedPetzThresholdProjector σ lambda

@[simp]
theorem fixedPetzThresholdComplementProjector_eq
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ρ.fixedPetzThresholdComplementProjector σ lambda =
      1 - ρ.fixedPetzThresholdProjector σ lambda :=
  rfl

theorem fixedPetzThresholdComplementProjector_posSemidef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdComplementProjector σ lambda).PosSemidef := by
  have hle := ρ.fixedPetzThresholdProjector_le_one σ lambda
  rw [Matrix.le_iff] at hle
  simpa [fixedPetzThresholdComplementProjector] using hle

theorem fixedPetzThresholdComplementProjector_isHermitian
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdComplementProjector σ lambda).IsHermitian :=
  (ρ.fixedPetzThresholdComplementProjector_posSemidef σ lambda).isHermitian

theorem fixedPetzThresholdComplementProjector_idempotent
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ρ.fixedPetzThresholdComplementProjector σ lambda *
        ρ.fixedPetzThresholdComplementProjector σ lambda =
      ρ.fixedPetzThresholdComplementProjector σ lambda := by
  unfold fixedPetzThresholdComplementProjector
  have hP := ρ.fixedPetzThresholdProjector_idempotent σ lambda
  calc
    (1 - ρ.fixedPetzThresholdProjector σ lambda) *
        (1 - ρ.fixedPetzThresholdProjector σ lambda) =
      1 - ρ.fixedPetzThresholdProjector σ lambda -
        ρ.fixedPetzThresholdProjector σ lambda +
          ρ.fixedPetzThresholdProjector σ lambda *
            ρ.fixedPetzThresholdProjector σ lambda := by
        noncomm_ring
    _ = 1 - ρ.fixedPetzThresholdProjector σ lambda := by
        rw [hP]
        noncomm_ring

/-- The fixed-threshold postselected matrix `(1-P)ρ(1-P)`. -/
def fixedPetzThresholdCompressedMatrix
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) : CMatrix (Prod a b) :=
  ρ.fixedPetzThresholdComplementProjector σ lambda *
    ρ.matrix * ρ.fixedPetzThresholdComplementProjector σ lambda

@[simp]
theorem fixedPetzThresholdCompressedMatrix_eq
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ρ.fixedPetzThresholdCompressedMatrix σ lambda =
      ρ.fixedPetzThresholdComplementProjector σ lambda *
        ρ.matrix * ρ.fixedPetzThresholdComplementProjector σ lambda :=
  rfl

theorem fixedPetzThresholdCompressedMatrix_posSemidef
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdCompressedMatrix σ lambda).PosSemidef := by
  let Q : CMatrix (Prod a b) := ρ.fixedPetzThresholdComplementProjector σ lambda
  have h := ρ.pos.conjTranspose_mul_mul_same Q
  have hQ : Matrix.conjTranspose Q = Q := by
    simpa [Q] using (ρ.fixedPetzThresholdComplementProjector_isHermitian σ lambda).eq
  rw [hQ] at h
  change (Q * ρ.matrix * Q).PosSemidef
  exact h

theorem fixedPetzThresholdCompressedMatrix_trace_re_le_one
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdCompressedMatrix σ lambda).trace.re ≤ 1 := by
  let Q : CMatrix (Prod a b) := ρ.fixedPetzThresholdComplementProjector σ lambda
  have htrace_le' :
      ((ρ.matrix * Q).trace).re ≤ ((ρ.matrix * 1).trace).re :=
    cMatrix_trace_mul_le_of_le_posSemidef_left ρ.pos
      (by
        rw [Matrix.le_iff]
        have hPpos := ρ.fixedPetzThresholdProjector_posSemidef σ lambda
        simpa [Q, fixedPetzThresholdComplementProjector, sub_eq_add_neg,
          add_comm, add_left_comm, add_assoc] using hPpos)
  have htrace_le : ((ρ.matrix * Q).trace).re ≤ ρ.matrix.trace.re := by
    simpa [Q, Matrix.mul_one] using htrace_le'
  have hcyc :
      (ρ.fixedPetzThresholdCompressedMatrix σ lambda).trace =
        (ρ.matrix * Q).trace := by
    calc
      (ρ.fixedPetzThresholdCompressedMatrix σ lambda).trace =
          (Q * ρ.matrix * Q).trace := rfl
      _ = (ρ.matrix * (Q * Q)).trace := by
          calc
            (Q * ρ.matrix * Q).trace = ((Q * ρ.matrix) * Q).trace := by
              rw [Matrix.mul_assoc]
            _ = (Q * (Q * ρ.matrix)).trace := by rw [Matrix.trace_mul_comm]
            _ = ((Q * Q) * ρ.matrix).trace := by rw [← Matrix.mul_assoc]
            _ = (ρ.matrix * (Q * Q)).trace := by rw [Matrix.trace_mul_comm]
      _ = (ρ.matrix * Q).trace := by
          rw [show Q * Q = Q by
            exact ρ.fixedPetzThresholdComplementProjector_idempotent σ lambda]
  rw [hcyc]
  rw [ρ.trace_eq_one] at htrace_le
  norm_num at htrace_le
  exact htrace_le

/-- The fixed-threshold postselected matrix as a subnormalized state. -/
def fixedPetzThresholdCompressedSubstate
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    SubnormalizedState (Prod a b) where
  matrix := ρ.fixedPetzThresholdCompressedMatrix σ lambda
  pos := ρ.fixedPetzThresholdCompressedMatrix_posSemidef σ lambda
  trace_le_one := ρ.fixedPetzThresholdCompressedMatrix_trace_re_le_one σ lambda

@[simp]
theorem fixedPetzThresholdCompressedSubstate_matrix
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdCompressedSubstate σ lambda).matrix =
      ρ.fixedPetzThresholdCompressedMatrix σ lambda :=
  rfl

theorem fixedPetzThresholdComplement_trace_re_eq_one_sub_projector_trace_re
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ((ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace).re =
      1 - ((ρ.fixedPetzThresholdProjector σ lambda * ρ.matrix).trace).re := by
  rw [fixedPetzThresholdComplementProjector_eq]
  have htrace :
      (((1 - ρ.fixedPetzThresholdProjector σ lambda) * ρ.matrix).trace).re =
        ρ.matrix.trace.re -
          ((ρ.fixedPetzThresholdProjector σ lambda * ρ.matrix).trace).re := by
    simp [sub_mul, Matrix.trace_sub]
  rw [htrace, ρ.trace_eq_one]
  norm_num

/-- The complement fail probability is the positive-threshold projector
probability. -/
theorem fixedPetzThresholdComplement_fail_eq_projector_trace_re
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    1 - ((ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace).re =
      ((ρ.fixedPetzThresholdProjector σ lambda * ρ.matrix).trace).re := by
  rw [fixedPetzThresholdComplement_trace_re_eq_one_sub_projector_trace_re]
  ring

theorem fixedPetzThresholdCompressedSubstate_traceNorm_sub_le_of_complement_fail
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfail :
      1 - (((ρ.fixedPetzThresholdComplementProjector σ lambda) * ρ.matrix).trace).re ≤
        ε ^ 2 / 2) :
    traceNorm ((ρ.fixedPetzThresholdCompressedSubstate σ lambda).matrix - ρ.matrix) ≤
      2 * ε := by
  let Q : CMatrix (Prod a b) := ρ.fixedPetzThresholdComplementProjector σ lambda
  have hgentle := gentle_projector Q
    (ρ.fixedPetzThresholdComplementProjector_posSemidef σ lambda)
    (ρ.fixedPetzThresholdComplementProjector_idempotent σ lambda) ρ
  have hsqrt_le : Real.sqrt (1 - ((Q * ρ.matrix).trace).re) ≤ ε := by
    refine (Real.sqrt_le_left hε).mpr ?_
    have hhalf : ε ^ 2 / 2 ≤ ε ^ 2 := by
      nlinarith [sq_nonneg ε]
    exact le_trans hfail hhalf
  calc
    traceNorm ((ρ.fixedPetzThresholdCompressedSubstate σ lambda).matrix - ρ.matrix)
        = traceNorm (Q * ρ.matrix * Q - ρ.matrix) := by
          rfl
    _ ≤ 2 * Real.sqrt (1 - ((Q * ρ.matrix).trace).re) := hgentle
    _ ≤ 2 * ε := by
          exact mul_le_mul_of_nonneg_left hsqrt_le (by norm_num)

theorem fixedPetzThresholdCompressedSubstate_traceNorm_sub_le_of_projector_fail
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfail :
      (((ρ.fixedPetzThresholdProjector σ lambda) * ρ.matrix).trace).re ≤ ε ^ 2 / 2) :
    traceNorm ((ρ.fixedPetzThresholdCompressedSubstate σ lambda).matrix - ρ.matrix) ≤
      2 * ε := by
  refine ρ.fixedPetzThresholdCompressedSubstate_traceNorm_sub_le_of_complement_fail
    σ lambda hε ?_
  rwa [fixedPetzThresholdComplement_fail_eq_projector_trace_re]

/-- If the compressed substate is known to have sufficiently large
generalized fidelity with the original state, it lies in the subnormalized
purified-distance ball. This is the remaining handoff needed after a
compression-specific fidelity lower bound is available. -/
theorem fixedPetzThresholdCompressedSubstate_purifiedBall_of_generalizedFidelity
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfid :
      1 - ρ.toSubnormalized.generalizedFidelity
          (ρ.fixedPetzThresholdCompressedSubstate σ lambda) ≤ ε ^ 2) :
    ρ.toSubnormalized.purifiedBall ε
      (ρ.fixedPetzThresholdCompressedSubstate σ lambda) := by
  rw [SubnormalizedState.purifiedBall_eq, SubnormalizedState.purifiedDistance_eq]
  exact (Real.sqrt_le_left hε).mpr hfid

/-- Purification-overlap handoff for the fixed-Petz compressed substate.

This is the checked intermediate used by the purification/Uhlmann route: once
the concrete post-measurement purification of
`ρ.fixedPetzThresholdCompressedSubstate σ lambda` is constructed with overlap
at least `t` against a purification of `ρ.toSubnormalized`, generalized
fidelity is at least `t`. -/
theorem fixedPetzThresholdCompressedSubstate_le_generalizedFidelity_of_hatExtension_overlap
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    {r : Type*} [Fintype r] [DecidableEq r]
    {Ψ Φ : PureVector (Prod r (Sum PUnit (Prod a b)))}
    (hΨ : Ψ.Purifies ρ.toSubnormalized.hatExtension)
    (hΦ : Φ.Purifies (ρ.fixedPetzThresholdCompressedSubstate σ lambda).hatExtension)
    {t : ℝ} (hoverlap : t ≤ Ψ.overlapSq Φ) :
    t ≤ ρ.toSubnormalized.generalizedFidelity
      (ρ.fixedPetzThresholdCompressedSubstate σ lambda) :=
by
  rw [SubnormalizedState.generalizedFidelity_eq_squaredFidelity_hatExtension]
  exact le_trans hoverlap
    (PureVector.overlapSq_le_squaredFidelity_of_purifies hΨ hΦ)

/-- Exact-overlap handoff for the fixed-Petz compressed substate.

This is the concrete target left by the post-measurement purification
construction: if two hat-extension purifications have overlap exactly
`Tr(Qρ)`, where `Q` is the fixed-Petz complement projector, then generalized
fidelity is at least `(Re Tr(Qρ))²`. -/
theorem fixedPetzThresholdCompressedSubstate_sq_trace_re_le_generalizedFidelity_of_hatExtension_overlap_eq
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    {r : Type*} [Fintype r] [DecidableEq r]
    {Ψ Φ : PureVector (Prod r (Sum PUnit (Prod a b)))}
    (hΨ : Ψ.Purifies ρ.toSubnormalized.hatExtension)
    (hΦ : Φ.Purifies (ρ.fixedPetzThresholdCompressedSubstate σ lambda).hatExtension)
    (hoverlap :
      Ψ.overlap Φ =
        ((ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace)) :
    (((ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace).re) ^ 2 ≤
      ρ.toSubnormalized.generalizedFidelity
        (ρ.fixedPetzThresholdCompressedSubstate σ lambda) :=
by
  refine
    fixedPetzThresholdCompressedSubstate_le_generalizedFidelity_of_hatExtension_overlap
      (ρ := ρ) (σ := σ) (lambda := lambda) (Ψ := Ψ) (Φ := Φ)
      hΨ hΦ ?_
  rw [PureVector.overlapSq_eq_normSq, hoverlap]
  simpa [sq] using
    Complex.re_sq_le_normSq
      ((ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace)

/-- Amplitude-matrix version of the fixed-Petz compressed-substate
purification-overlap handoff.

This isolates the concrete post-measurement construction obligation to three
matrix equations: the two target-side Gram equations matching
`PureVector.Purifies`, and the trace pairing of the two amplitude matrices. -/
theorem fixedPetzThresholdCompressedSubstate_sq_trace_re_le_generalizedFidelity_of_hatExtension_amplitudeMatrix_eq
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    {r : Type*} [Fintype r] [DecidableEq r]
    {Ψ Φ : PureVector (Prod r (Sum PUnit (Prod a b)))}
    (hΨamp :
      Ψ.amplitudeMatrix * Matrix.conjTranspose Ψ.amplitudeMatrix =
        ρ.toSubnormalized.hatExtension.matrix)
    (hΦamp :
      Φ.amplitudeMatrix * Matrix.conjTranspose Φ.amplitudeMatrix =
        (ρ.fixedPetzThresholdCompressedSubstate σ lambda).hatExtension.matrix)
    (hoverlapAmp :
      (Matrix.conjTranspose Ψ.amplitudeMatrix * Φ.amplitudeMatrix).trace =
        ((ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace)) :
    (((ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace).re) ^ 2 ≤
      ρ.toSubnormalized.generalizedFidelity
        (ρ.fixedPetzThresholdCompressedSubstate σ lambda) :=
by
  have hΨ : Ψ.Purifies ρ.toSubnormalized.hatExtension := by
    rw [PureVector.purifies_iff, PureVector.state_matrix]
    rw [PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose]
    exact hΨamp
  have hΦ : Φ.Purifies (ρ.fixedPetzThresholdCompressedSubstate σ lambda).hatExtension := by
    rw [PureVector.purifies_iff, PureVector.state_matrix]
    rw [PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose]
    exact hΦamp
  refine
    fixedPetzThresholdCompressedSubstate_sq_trace_re_le_generalizedFidelity_of_hatExtension_overlap_eq
      (ρ := ρ) (σ := σ) (lambda := lambda) (Ψ := Ψ) (Φ := Φ)
      hΨ hΦ ?_
  rw [PureVector.overlap_eq_trace_conjTranspose_amplitudeMatrix_mul]
  exact hoverlapAmp

/-- Candidate amplitude matrix for the hat extension of the fixed-Petz
compressed substate.

The failure row carries the square root of the compressed state's failure mass.
The success block is the complement threshold projector applied to the
canonical square-root amplitude of `ρ`. -/
def fixedPetzThresholdHatCompressedAmplitudeMatrix
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    CMatrix (Sum PUnit (Prod a b)) :=
  Matrix.fromBlocks
    (fun _ _ : PUnit =>
      ((Real.sqrt
        (ρ.fixedPetzThresholdCompressedSubstate σ lambda).hatFailureMass : ℝ) : ℂ))
    0 0
    (ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.sqrtMatrix)

theorem fixedPetzThresholdHatCompressedAmplitudeMatrix_gram
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ρ.fixedPetzThresholdHatCompressedAmplitudeMatrix σ lambda *
        Matrix.conjTranspose
          (ρ.fixedPetzThresholdHatCompressedAmplitudeMatrix σ lambda) =
      (ρ.fixedPetzThresholdCompressedSubstate σ lambda).hatExtension.matrix := by
  classical
  let τ : SubnormalizedState (Prod a b) :=
    ρ.fixedPetzThresholdCompressedSubstate σ lambda
  let Q : CMatrix (Prod a b) :=
    ρ.fixedPetzThresholdComplementProjector σ lambda
  let S : CMatrix (Prod a b) := ρ.sqrtMatrix
  have hQ : Matrix.conjTranspose Q = Q := by
    simpa [Q] using (ρ.fixedPetzThresholdComplementProjector_isHermitian σ lambda).eq
  have hS : Matrix.conjTranspose S = S := by
    simpa [S] using ρ.sqrtMatrix_isHermitian.eq
  have hsuccess :
      (Q * S) * Matrix.conjTranspose (Q * S) = τ.matrix := by
    rw [Matrix.conjTranspose_mul, hQ, hS]
    calc
      (Q * S) * (S * Q) = Q * (S * S) * Q := by
        simp only [Matrix.mul_assoc]
      _ = Q * ρ.matrix * Q := by rw [ρ.sqrtMatrix_mul_self]
      _ = τ.matrix := by
        simp [τ, Q, fixedPetzThresholdCompressedSubstate_matrix,
          fixedPetzThresholdCompressedMatrix]
  unfold fixedPetzThresholdHatCompressedAmplitudeMatrix
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  ext x y
  cases x with
  | inl xi =>
      cases y with
      | inl yj =>
          cases xi
          cases yj
          simp [τ, Matrix.mul_apply, SubnormalizedState.hatExtension_matrix,
            ← Complex.ofReal_mul, Real.mul_self_sqrt τ.hatFailureMass_nonneg]
      | inr yj =>
          simp [SubnormalizedState.hatExtension_matrix]
  | inr xi =>
      cases y with
      | inl yj =>
          simp [SubnormalizedState.hatExtension_matrix]
      | inr yj =>
          simpa [τ, Q, S] using congrFun (congrFun hsuccess xi) yj

theorem toSubnormalized_hatExtension_sqrtMatrix
    (ρ : State (Prod a b)) :
    ρ.toSubnormalized.hatExtension.sqrtMatrix =
      Matrix.fromBlocks (0 : CMatrix PUnit) 0 0 ρ.sqrtMatrix := by
  classical
  have hfail : ρ.toSubnormalized.hatFailureMass = 0 := by
    simp [SubnormalizedState.hatFailureMass, ρ.trace_eq_one]
  rw [State.sqrtMatrix, SubnormalizedState.hatExtension_matrix,
    SubnormalizedState.hatExtensionMatrix]
  rw [Matrix.fromBlocks_diagonal_psdSqrt ρ.toSubnormalized.hatFailureBlock_pos
    ρ.toSubnormalized.pos]
  have hfailBlock :
      psdSqrt ρ.toSubnormalized.hatFailureBlock = (0 : CMatrix PUnit) := by
    rw [show ρ.toSubnormalized.hatFailureBlock = (0 : CMatrix PUnit) by
      ext i j
      cases i
      cases j
      simp [SubnormalizedState.hatFailureBlock, hfail]]
    simp
  rw [hfailBlock]
  rfl

theorem toSubnormalized_hatExtension_canonicalPurification_amplitudeMatrix
    (ρ : State (Prod a b)) :
    ρ.toSubnormalized.hatExtension.canonicalPurification.amplitudeMatrix =
      Matrix.fromBlocks (0 : CMatrix PUnit) 0 0 ρ.sqrtMatrix := by
  classical
  ext x i
  cases x with
  | inl xi =>
      cases xi
      cases i with
      | inl ij =>
          cases ij
          simp [PureVector.amplitudeMatrix, State.canonicalPurification,
            State.canonicalPurificationAmp,
            toSubnormalized_hatExtension_sqrtMatrix]
      | inr ij =>
          simp [PureVector.amplitudeMatrix, State.canonicalPurification,
            State.canonicalPurificationAmp,
            toSubnormalized_hatExtension_sqrtMatrix]
  | inr xi =>
      cases i with
      | inl ij =>
          cases ij
          simp [PureVector.amplitudeMatrix, State.canonicalPurification,
            State.canonicalPurificationAmp,
            toSubnormalized_hatExtension_sqrtMatrix]
      | inr ij =>
          simp [PureVector.amplitudeMatrix, State.canonicalPurification,
            State.canonicalPurificationAmp,
            toSubnormalized_hatExtension_sqrtMatrix]

/-- Candidate amplitude matrix for the hat extension of the source-shaped
`GρG†` witness.

The failure row carries the square root of the witness failure mass.  The
success block is the source filter `G` applied to the canonical square-root
amplitude of `ρ`. -/
def fixedPetzSmoothMinWitnessHatAmplitudeMatrix
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1) :
    CMatrix (Sum PUnit (Prod a b)) :=
  Matrix.fromBlocks
    (fun _ _ : PUnit =>
      ((Real.sqrt
        (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract).hatFailureMass : ℝ) : ℂ))
    0 0 (ρ.fixedPetzSmoothMinG σ lambda * ρ.sqrtMatrix)

theorem fixedPetzSmoothMinWitnessHatAmplitudeMatrix_gram
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1) :
    ρ.fixedPetzSmoothMinWitnessHatAmplitudeMatrix σ lambda hcontract *
        Matrix.conjTranspose
          (ρ.fixedPetzSmoothMinWitnessHatAmplitudeMatrix σ lambda hcontract) =
      (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract).hatExtension.matrix := by
  classical
  let τ : SubnormalizedState (Prod a b) :=
    ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract
  let G : CMatrix (Prod a b) := ρ.fixedPetzSmoothMinG σ lambda
  let S : CMatrix (Prod a b) := ρ.sqrtMatrix
  have hS : Matrix.conjTranspose S = S := by
    simpa [S] using ρ.sqrtMatrix_isHermitian.eq
  have hsuccess :
      (G * S) * Matrix.conjTranspose (G * S) = τ.matrix := by
    rw [Matrix.conjTranspose_mul, hS]
    calc
      (G * S) * (S * Matrix.conjTranspose G) =
          G * (S * S) * Matrix.conjTranspose G := by
        noncomm_ring
      _ = G * ρ.matrix * Matrix.conjTranspose G := by
        rw [show S * S = ρ.matrix by simp [S]]
      _ = τ.matrix := by
        simp [τ, G, fixedPetzSmoothMinWitnessSubstate_matrix,
          fixedPetzSmoothMinWitnessMatrix]
  unfold fixedPetzSmoothMinWitnessHatAmplitudeMatrix
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  ext x y
  cases x with
  | inl xi =>
      cases y with
      | inl yj =>
          cases xi
          cases yj
          simp [τ, Matrix.mul_apply, SubnormalizedState.hatExtension_matrix,
            ← Complex.ofReal_mul, Real.mul_self_sqrt τ.hatFailureMass_nonneg]
      | inr yj =>
          simp [SubnormalizedState.hatExtension_matrix]
  | inr xi =>
      cases y with
      | inl yj =>
          simp [SubnormalizedState.hatExtension_matrix]
      | inr yj =>
          simpa [τ, G, S] using congrFun (congrFun hsuccess xi) yj

theorem fixedPetzSmoothMinWitnessHatAmplitudeMatrix_overlap_trace
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1) :
    (Matrix.conjTranspose
          ρ.toSubnormalized.hatExtension.canonicalPurification.amplitudeMatrix *
        ρ.fixedPetzSmoothMinWitnessHatAmplitudeMatrix σ lambda hcontract).trace =
      (ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace := by
  classical
  let G : CMatrix (Prod a b) := ρ.fixedPetzSmoothMinG σ lambda
  rw [toSubnormalized_hatExtension_canonicalPurification_amplitudeMatrix]
  unfold fixedPetzSmoothMinWitnessHatAmplitudeMatrix
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp
  rw [Matrix.trace_fromBlocks_diagonal]
  simp
  calc
    (Matrix.conjTranspose ρ.sqrtMatrix * (G * ρ.sqrtMatrix)).trace =
        (ρ.sqrtMatrix * (G * ρ.sqrtMatrix)).trace := by
      rw [ρ.sqrtMatrix_isHermitian.eq]
    _ = ((ρ.sqrtMatrix * G) * ρ.sqrtMatrix).trace := by rw [Matrix.mul_assoc]
    _ = (G * (ρ.sqrtMatrix * ρ.sqrtMatrix)).trace := by
      calc
        ((ρ.sqrtMatrix * G) * ρ.sqrtMatrix).trace =
            (ρ.sqrtMatrix * (ρ.sqrtMatrix * G)).trace := by
              rw [Matrix.trace_mul_comm]
        _ = ((ρ.sqrtMatrix * ρ.sqrtMatrix) * G).trace := by
              rw [← Matrix.mul_assoc]
        _ = (G * (ρ.sqrtMatrix * ρ.sqrtMatrix)).trace := by
              rw [Matrix.trace_mul_comm]
    _ = (G * ρ.matrix).trace := by
      rw [ρ.sqrtMatrix_mul_self]
    _ = (ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace := by
      simp [G]

theorem fixedPetzSmoothMinWitnessSubstate_sq_trace_re_le_generalizedFidelity
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1) :
    (((ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace).re) ^ 2 ≤
      ρ.toSubnormalized.generalizedFidelity
        (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract) := by
  classical
  let τ : SubnormalizedState (Prod a b) :=
    ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract
  let AΦ : CMatrix (Sum PUnit.{max u v + 1} (Prod a b)) :=
    ρ.fixedPetzSmoothMinWitnessHatAmplitudeMatrix σ lambda hcontract
  have htrace : (AΦ * Matrix.conjTranspose AΦ).trace = 1 := by
    rw [show AΦ * Matrix.conjTranspose AΦ = τ.hatExtension.matrix by
      simpa [AΦ, τ] using
        ρ.fixedPetzSmoothMinWitnessHatAmplitudeMatrix_gram σ lambda hcontract]
    exact τ.hatExtension_trace_one
  let Φ := PureVector.ofAmplitudeMatrix AΦ htrace
  have hΨ :
      ρ.toSubnormalized.hatExtension.canonicalPurification.Purifies
        ρ.toSubnormalized.hatExtension :=
    ρ.toSubnormalized.hatExtension.canonicalPurification_purifies
  have hΦ : Φ.Purifies τ.hatExtension := by
    rw [PureVector.purifies_iff, PureVector.state_matrix]
    rw [PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose]
    simpa [Φ, AΦ, PureVector.ofAmplitudeMatrix_amplitudeMatrix] using
      ρ.fixedPetzSmoothMinWitnessHatAmplitudeMatrix_gram σ lambda hcontract
  have hoverlapSq :
      (((ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace).re) ^ 2 ≤
        ρ.toSubnormalized.hatExtension.canonicalPurification.overlapSq Φ := by
    rw [PureVector.overlapSq_eq_normSq]
    have hoverlap :
        ρ.toSubnormalized.hatExtension.canonicalPurification.overlap Φ =
          (ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace := by
      rw [PureVector.overlap_eq_trace_conjTranspose_amplitudeMatrix_mul]
      simpa [Φ, AΦ, PureVector.ofAmplitudeMatrix_amplitudeMatrix] using
        ρ.fixedPetzSmoothMinWitnessHatAmplitudeMatrix_overlap_trace σ lambda hcontract
    rw [hoverlap]
    simpa [sq] using
      Complex.re_sq_le_normSq
        ((ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace)
  rw [SubnormalizedState.generalizedFidelity_eq_squaredFidelity_hatExtension]
  exact le_trans hoverlapSq
    (PureVector.overlapSq_le_squaredFidelity_of_purifies hΨ hΦ)

theorem fixedPetzSmoothMinWitnessSubstate_purifiedBall_of_trace_re
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1)
    (htrace :
      1 - (((ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace).re) ≤ ε ^ 2 / 2) :
    ρ.toSubnormalized.purifiedBall ε
      (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract) := by
  let τ : SubnormalizedState (Prod a b) :=
    ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract
  let q : ℝ := ((ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace).re
  have hgf : q ^ 2 ≤ ρ.toSubnormalized.generalizedFidelity τ := by
    simpa [τ, q] using
      ρ.fixedPetzSmoothMinWitnessSubstate_sq_trace_re_le_generalizedFidelity
        σ lambda hcontract
  have hq_nonneg : 0 ≤ q := by
    have hhalf_lt_one : ε ^ 2 / 2 < 1 := by nlinarith [hε_pos, hε_lt]
    have hq_lt : 1 - q < 1 := lt_of_le_of_lt (by simpa [q] using htrace) hhalf_lt_one
    linarith
  have hone_sub_gf :
      1 - ρ.toSubnormalized.generalizedFidelity τ ≤ ε ^ 2 := by
    have hone_sub_qsq : 1 - q ^ 2 ≤ ε ^ 2 := by
      by_cases hq_le_one : q ≤ 1
      · have hfactor : 1 - q ^ 2 = (1 - q) * (1 + q) := by ring
        have htwo : 1 + q ≤ 2 := by linarith
        have hnon : 0 ≤ 1 - q := by linarith
        calc
          1 - q ^ 2 = (1 - q) * (1 + q) := hfactor
          _ ≤ (1 - q) * 2 := mul_le_mul_of_nonneg_left htwo hnon
          _ ≤ (ε ^ 2 / 2) * 2 := by
            exact mul_le_mul_of_nonneg_right (by simpa [q] using htrace) (by norm_num)
          _ = ε ^ 2 := by ring
      · have hq_ge_one : 1 ≤ q := le_of_not_ge hq_le_one
        have hnonpos : 1 - q ^ 2 ≤ 0 := by nlinarith
        have hεsq_nonneg : 0 ≤ ε ^ 2 := sq_nonneg ε
        exact le_trans hnonpos hεsq_nonneg
    linarith
  rw [SubnormalizedState.purifiedBall_eq, SubnormalizedState.purifiedDistance_eq]
  exact (Real.sqrt_le_left hε_pos.le).mpr hone_sub_gf

theorem fixedPetzSmoothMinWitnessSubstate_purifiedBall_of_positivePart_trace
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1)
    (htrace :
      1 - (((ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace).re) ≤
        (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re)
    (hdelta :
      (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤ ε ^ 2 / 2) :
    ρ.toSubnormalized.purifiedBall ε
      (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract) :=
  ρ.fixedPetzSmoothMinWitnessSubstate_purifiedBall_of_trace_re σ lambda
    hε_pos hε_lt hcontract (le_trans htrace hdelta)

theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_positivePart_trace_scale
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε lambda : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) (hlambda : 0 < lambda)
    (htrace :
      1 - (((ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace).re) ≤
        (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re)
    (hdelta :
      (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤ ε ^ 2 / 2) :
    -log2 lambda ≤
      ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lambda) *
          ρ.fixedPetzSmoothMinG σ lambda ≤ 1 :=
    ρ.fixedPetzSmoothMinG_contract_posDef σ lambda hlambda hσ
  have hball :
      ρ.toSubnormalized.purifiedBall ε
        (ρ.fixedPetzSmoothMinWitnessSubstate σ lambda hcontract) :=
    ρ.fixedPetzSmoothMinWitnessSubstate_purifiedBall_of_positivePart_trace
      σ lambda hε_pos hε_lt hcontract htrace hdelta
  exact
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_ball_scale
      σ hσ ε lambda hε_pos hε_lt hlambda
      (by simpa [hcontract] using hball)

theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_petzTrace_scale
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε lambda α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) (hlambda : 0 < lambda)
    (hpetz :
      (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤
        lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α)
    (hscale :
      lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α ≤ ε ^ 2 / 2) :
    -log2 lambda ≤
      ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  have htrace_lam :
      1 - (((ρ.fixedPetzSmoothMinG σ lambda * ρ.matrix).trace).re) ≤
        (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re :=
    ρ.fixedPetzSmoothMinG_trace_loss_le_positivePart_trace σ lambda hlambda hσ
  have hdelta_lam :
      (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤ ε ^ 2 / 2 :=
    le_trans hpetz hscale
  exact
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_positivePart_trace_scale
      σ hσ ε lambda hε_pos hε_lt hlambda htrace_lam hdelta_lam

theorem fixedPetzThresholdPositivePart_trace_re_le_epsilon_sq_half_of_petzTrace
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    {ε α : ℝ} (hε_pos : 0 < ε) (hα_gt : 1 < α)
    (hpetz :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤
        lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α) :
    let lam : ℝ :=
      ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
    (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤ ε ^ 2 / 2 := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let lam : ℝ := ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
  have hpetz_lam :
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤
        lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
    simpa [lam, hα_pos, hα_ne_one] using hpetz
  have hscale :
      lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α = ε ^ 2 / 2 := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρ.petzSmoothMinThresholdScale_rpow_one_sub_alpha_mul_traceTerm_eq
        hρ σ hσ hε_pos hα_gt
  exact le_trans hpetz_lam (le_of_eq hscale)

/-- Fixed-reference specialization of the Petz effect-variational reduction.

This is the exact remaining one-shot source obligation in matrix form:
prove the Petz effect-variational inequality for
`A = ρ_AB` and `B = I_A ⊗ σ_B`, then the TCR positive-part trace bound follows. -/
theorem fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_effect_variational_posSemidef
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    {lambda α : ℝ} (hlambda : 0 < lambda)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hvar :
      cMatrixPetzTraceEffectVariational ρ.matrix
        (identityTensorStateMatrix (a := a) σ) lambda α) :
    (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤
      lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  simpa [fixedPetzThresholdPositivePart, conditionalPetzRenyiTraceTerm] using
    cMatrix_posPart_trace_re_le_scaled_petzTrace_of_effect_variational
      (A := ρ.matrix) (B := identityTensorStateMatrix (a := a) σ)
      ρ.pos hB hlambda hα_gt hα_le_two hvar

theorem fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_effect_variational
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    {lambda α : ℝ} (hlambda : 0 < lambda)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hvar :
      cMatrixPetzTraceEffectVariational ρ.matrix
        (identityTensorStateMatrix (a := a) σ) lambda α) :
    (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤
      lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  simpa [fixedPetzThresholdPositivePart, conditionalPetzRenyiTraceTerm] using
    cMatrix_posPart_trace_re_le_scaled_petzTrace_of_effect_variational
      (A := ρ.matrix) (B := identityTensorStateMatrix (a := a) σ)
      hρ.posSemidef hB hlambda hα_gt hα_le_two hvar

/-- Fixed-reference positive-part trace bound from the narrow Petz
unitary-dephasing monotonicity predicate in the Petz-threshold eigenbasis. -/
theorem fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_unitaryDephaseMonotone_posSemidef
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    {lambda α : ℝ} (hlambda : 0 < lambda)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hmono :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        ρ.pos.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α) :
    (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤
      lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  simpa [fixedPetzThresholdPositivePart, conditionalPetzRenyiTraceTerm] using
    cMatrix_posPart_trace_re_le_scaled_petzTrace_of_unitaryDephaseMonotone
      (A := ρ.matrix) (B := identityTensorStateMatrix (a := a) σ)
      ρ.pos hB hlambda hα_gt hα_le_two
      (ρ.pos.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian))
      (by simpa [hB] using hmono)

theorem fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_unitaryDephaseMonotone
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    {lambda α : ℝ} (hlambda : 0 < lambda)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hmono :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α) :
    (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤
      lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  simpa [fixedPetzThresholdPositivePart, conditionalPetzRenyiTraceTerm] using
    cMatrix_posPart_trace_re_le_scaled_petzTrace_of_unitaryDephaseMonotone
      (A := ρ.matrix) (B := identityTensorStateMatrix (a := a) σ)
      hρ.posSemidef hB hlambda hα_gt hα_le_two
      (hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian))
      (by simpa [hB] using hmono)

/-- Fixed-reference positive-part trace bound from the Hilbert-Schmidt kernel
form of Petz dephasing monotonicity in the Petz-threshold eigenbasis. -/
theorem fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_kernelDephaseMonotone_posSemidef
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    {lambda α : ℝ} (hlambda : 0 < lambda)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hkernel :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        ρ.pos.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceKernelDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α) :
    (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤
      lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let H : CMatrix (Prod a b) :=
    ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
  have hH : H.IsHermitian := by
    dsimp [H]
    exact ρ.pos.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
  let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
  have hmono :
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α :=
    cMatrixPetzTraceUnitaryDephaseMonotone_of_kernelDephaseMonotone
      ρ.matrix (identityTensorStateMatrix (a := a) σ) U α
      (by simpa [hB, H, hH, U] using hkernel)
  exact ρ.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_unitaryDephaseMonotone_posSemidef
    σ hσ hlambda hα_gt hα_le_two (by
      simpa [hB, H, hH, U] using hmono)

theorem fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_kernelDephaseMonotone
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    {lambda α : ℝ} (hlambda : 0 < lambda)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hkernel :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceKernelDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α) :
    (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤
      lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let H : CMatrix (Prod a b) :=
    ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
  have hH : H.IsHermitian := by
    dsimp [H]
    exact hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
  let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
  have hmono :
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α :=
    cMatrixPetzTraceUnitaryDephaseMonotone_of_kernelDephaseMonotone
      ρ.matrix (identityTensorStateMatrix (a := a) σ) U α
      (by simpa [hB, H, hH, U] using hkernel)
  exact ρ.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_unitaryDephaseMonotone
    hρ σ hσ hlambda hα_gt hα_le_two (by
      simpa [hB, H, hH, U] using hmono)

/-- Fixed-reference positive-part trace bound from finite uniform joint
convexity on the sign orbit of the Petz-threshold eigenbasis. -/
theorem fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_uniformJointConvex_posSemidef
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    {lambda α : ℝ} (hlambda : 0 < lambda)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hconv :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        ρ.pos.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      let A' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) * ρ.matrix * (U : CMatrix (Prod a b))
      let B' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) *
          identityTensorStateMatrix (a := a) σ * (U : CMatrix (Prod a b))
      cMatrixPetzTraceUniformJointConvex
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * A' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * B' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        α) :
    (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤
      lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let H : CMatrix (Prod a b) :=
    ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
  have hH : H.IsHermitian := by
    dsimp [H]
    exact ρ.pos.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
  let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
  have hmono :
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α :=
    cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex
      ρ.matrix (identityTensorStateMatrix (a := a) σ) ρ.pos hB U
      hα_gt hα_le_two (by
        simpa [hB, H, hH, U] using hconv)
  exact ρ.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_unitaryDephaseMonotone_posSemidef
    σ hσ hlambda hα_gt hα_le_two (by
      simpa [hB, H, hH, U] using hmono)

theorem fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_uniformJointConvex
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    {lambda α : ℝ} (hlambda : 0 < lambda)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hconv :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      let A' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) * ρ.matrix * (U : CMatrix (Prod a b))
      let B' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) *
          identityTensorStateMatrix (a := a) σ * (U : CMatrix (Prod a b))
      cMatrixPetzTraceUniformJointConvex
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * A' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * B' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        α) :
    (ρ.fixedPetzThresholdPositivePart σ lambda).trace.re ≤
      lambda ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let H : CMatrix (Prod a b) :=
    ρ.matrix - lambda • identityTensorStateMatrix (a := a) σ
  have hH : H.IsHermitian := by
    dsimp [H]
    exact hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
  let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
  have hmono :
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α :=
      cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex
      ρ.matrix (identityTensorStateMatrix (a := a) σ) hρ.posSemidef hB U
      hα_gt hα_le_two (by
        simpa [hB, H, hH, U] using hconv)
  exact ρ.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_unitaryDephaseMonotone
    hρ σ hσ hlambda hα_gt hα_le_two (by
      simpa [hB, H, hH, U] using hmono)

/-- Fixed-reference source one-shot smooth-min lower bound for arbitrary left
states and a full-rank reference, with Petz dephasing monotonicity supplied via
finite-uniform joint convexity.

This is the `σ_B` full-support branch of TCR 2008 `thm:entropy-ineq`: the left
state is only positive semidefinite, while the reference side is positive
definite. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_fullReference_of_uniformJointConvex
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hconv :
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScaleFullReference σ hσ ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        ρ.pos.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρ.petzSmoothMinThresholdScaleFullReference_pos σ hσ ε α
            hα_pos hα_ne_one)).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      let A' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) * ρ.matrix * (U : CMatrix (Prod a b))
      let B' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) *
          identityTensorStateMatrix (a := a) σ * (U : CMatrix (Prod a b))
      cMatrixPetzTraceUniformJointConvex
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * A' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * B' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        α) :
    ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let lam : ℝ :=
    ρ.petzSmoothMinThresholdScaleFullReference σ hσ ε α hα_pos hα_ne_one
  have hlam : 0 < lam := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρ.petzSmoothMinThresholdScaleFullReference_pos σ hσ ε α hα_pos hα_ne_one
  have hpetz :
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤
        lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α := by
    exact
      ρ.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_uniformJointConvex_posSemidef
        σ hσ hlam hα_gt hα_le_two (by
          simpa [lam, hα_pos, hα_ne_one] using hconv)
  have hscale :
      lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α ≤ ε ^ 2 / 2 := by
    exact le_of_eq (by
      simpa [lam, hα_pos, hα_ne_one] using
        ρ.petzSmoothMinThresholdScaleFullReference_rpow_one_sub_alpha_mul_traceTerm_eq
          σ hσ hε_pos hα_gt)
  have hsmooth :
      -log2 lam ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε :=
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_petzTrace_scale
      σ hσ ε lam α hε_pos hε_lt hlam hpetz hscale
  have hexponent :
      ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α hα_pos hα_ne_one -
          (1 / (α - 1)) * log2 (2 / ε ^ 2) =
        -log2 lam := by
    simpa [lam, hα_pos, hα_ne_one, petzSmoothMinThresholdExponentFullReference] using
      ρ.petzSmoothMinThresholdExponentFullReference_eq_neg_log2_scale
        σ hσ ε α hα_pos hα_ne_one
  simpa [hα_pos, hα_ne_one] using hexponent.le.trans hsmooth

/-- Fixed-reference source one-shot smooth-min lower bound for arbitrary left
states and a full-rank reference, with Petz monotonicity discharged by the
finite-dimensional rpow-perspective theorem. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_fullReference
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2) :
    ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  exact
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_fullReference_of_uniformJointConvex
      σ hσ ε α hε_pos hε_lt hα_gt hα_le_two (by
        exact cMatrixPetzTraceUniformJointConvex_of_rpow_perspective_one_two _ _)

theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_positivePart_trace
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (htrace :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      1 - (((ρ.fixedPetzSmoothMinG σ lam * ρ.matrix).trace).re) ≤
        (ρ.fixedPetzThresholdPositivePart σ lam).trace.re)
    (hdelta :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤ ε ^ 2 / 2) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let lam : ℝ :=
    ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
      (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
  let hlam : 0 < lam :=
    ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α
      (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
  let hcontract :
      Matrix.conjTranspose (ρ.fixedPetzSmoothMinG σ lam) *
          ρ.fixedPetzSmoothMinG σ lam ≤ 1 :=
    ρ.fixedPetzSmoothMinG_contract_posDef σ lam hlam hσ
  have htrace_lam :
      1 - (((ρ.fixedPetzSmoothMinG σ lam * ρ.matrix).trace).re) ≤
        (ρ.fixedPetzThresholdPositivePart σ lam).trace.re := by
    simpa [lam] using htrace
  have hdelta_lam :
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤ ε ^ 2 / 2 := by
    simpa [lam] using hdelta
  have hball :
      ρ.toSubnormalized.purifiedBall ε
        (ρ.fixedPetzSmoothMinWitnessSubstate σ lam hcontract) :=
    ρ.fixedPetzSmoothMinWitnessSubstate_purifiedBall_of_positivePart_trace
      σ lam hε_pos hε_lt hcontract htrace_lam hdelta_lam
  exact
    smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_ball
      (ρ := ρ) hρ (σ := σ) hσ ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [lam, hcontract] using hball)

theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_petzTrace
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hpetz :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤
        lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let lam : ℝ := ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
  have hlam : 0 < lam := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one
  have htrace_lam :
      1 - (((ρ.fixedPetzSmoothMinG σ lam * ρ.matrix).trace).re) ≤
        (ρ.fixedPetzThresholdPositivePart σ lam).trace.re :=
    ρ.fixedPetzSmoothMinG_trace_loss_le_positivePart_trace σ lam hlam hσ
  have hdelta_lam :
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤ ε ^ 2 / 2 := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρ.fixedPetzThresholdPositivePart_trace_re_le_epsilon_sq_half_of_petzTrace
        hρ σ hσ hε_pos hα_gt hpetz
  exact
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_positivePart_trace
      hρ σ hσ ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [lam, hα_pos, hα_ne_one] using htrace_lam)
      (by simpa [lam, hα_pos, hα_ne_one] using hdelta_lam)

/-- Source-shaped `GρG†` smooth-min lower bound from the fixed-reference
Petz effect-variational inequality.

The noncommutative Petz-Hölder/operator-convex step is the explicit `hvar`
hypothesis; everything else in the TCR smooth-min bridge is discharged here. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_effectVariational
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hvar :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational ρ.matrix
        (identityTensorStateMatrix (a := a) σ) lam α) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let lam : ℝ := ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
  have hlam : 0 < lam := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one
  have hvar_lam :
      cMatrixPetzTraceEffectVariational ρ.matrix
        (identityTensorStateMatrix (a := a) σ) lam α := by
    simpa [lam, hα_pos, hα_ne_one] using hvar
  have hpetz :
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤
        lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α :=
    ρ.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_effect_variational
      hρ σ hσ hlam hα_gt hα_le_two hvar_lam
  exact
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_petzTrace
      hρ σ hσ ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [lam, hα_pos, hα_ne_one] using hpetz)

/-- Source-shaped `GρG†` smooth-min lower bound from the narrow Petz
unitary-dephasing monotonicity predicate in the Petz-threshold eigenbasis. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_unitaryDephaseMonotone
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hmono :
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one)
        ).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let lam : ℝ := ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
  have hlam : 0 < lam := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one
  have hmono_lam :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlam).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α := by
    simpa [lam, hα_pos, hα_ne_one, hlam] using hmono
  have hpetz :
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤
        lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α :=
    ρ.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_unitaryDephaseMonotone
      hρ σ hσ hlam hα_gt hα_le_two hmono_lam
  exact
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_petzTrace
      hρ σ hσ ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [lam, hα_pos, hα_ne_one] using hpetz)

/-- Source-shaped `GρG†` smooth-min lower bound from the Hilbert-Schmidt
kernel form of Petz dephasing monotonicity in the Petz-threshold eigenbasis. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_kernelDephaseMonotone
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hkernel :
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one)
        ).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceKernelDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let lam : ℝ := ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
  have hlam : 0 < lam := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let H : CMatrix (Prod a b) :=
    ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
  have hH : H.IsHermitian := by
    dsimp [H]
    exact hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlam).isHermitian)
  let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
  have hmono_lam :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlam).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α := by
    have hkernel_lam :
        cMatrixPetzTraceKernelDephaseMonotone ρ.matrix
          (identityTensorStateMatrix (a := a) σ) U α := by
      simpa [lam, hα_pos, hα_ne_one, hlam, hB, H, hH, U] using hkernel
    have hmono :
        cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
          (identityTensorStateMatrix (a := a) σ) U α :=
      cMatrixPetzTraceUnitaryDephaseMonotone_of_kernelDephaseMonotone
        ρ.matrix (identityTensorStateMatrix (a := a) σ) U α hkernel_lam
    simpa [hB, H, hH, U] using hmono
  exact
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_unitaryDephaseMonotone
      hρ σ hσ ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [lam, hα_pos, hα_ne_one, hlam] using hmono_lam)

/-- Source-shaped `GρG†` smooth-min lower bound from finite uniform joint
convexity on the sign orbit of the Petz-threshold eigenbasis. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_uniformJointConvex
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hconv :
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one)
        ).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      let A' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) * ρ.matrix * (U : CMatrix (Prod a b))
      let B' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) *
          identityTensorStateMatrix (a := a) σ * (U : CMatrix (Prod a b))
      cMatrixPetzTraceUniformJointConvex
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * A' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * B' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        α) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let lam : ℝ := ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
  have hlam : 0 < lam := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one
  have hconv_lam :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlam).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      let A' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) * ρ.matrix * (U : CMatrix (Prod a b))
      let B' : CMatrix (Prod a b) :=
        star (U : CMatrix (Prod a b)) *
          identityTensorStateMatrix (a := a) σ * (U : CMatrix (Prod a b))
      cMatrixPetzTraceUniformJointConvex
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * A' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        (fun s : Prod a b → Bool =>
          star (cMatrixSignUnitary s : CMatrix (Prod a b)) * B' *
            (cMatrixSignUnitary s : CMatrix (Prod a b)))
        α := by
    simpa [lam, hα_pos, hα_ne_one, hlam] using hconv
  have hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let H : CMatrix (Prod a b) :=
    ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
  have hH : H.IsHermitian := by
    dsimp [H]
    exact hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlam).isHermitian)
  let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
  have hmono_lam :
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB hlam).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α := by
    have hmono :
        cMatrixPetzTraceUnitaryDephaseMonotone ρ.matrix
          (identityTensorStateMatrix (a := a) σ) U α :=
      cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex
        ρ.matrix (identityTensorStateMatrix (a := a) σ) hρ.posSemidef hB U
        hα_gt hα_le_two (by
          simpa [hB, H, hH, U] using hconv_lam)
    simpa [hB, H, hH, U] using hmono
  exact
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_unitaryDephaseMonotone
      hρ σ hσ ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [lam, hα_pos, hα_ne_one, hlam] using hmono_lam)

theorem fixedPetzThresholdHatCompressedAmplitudeMatrix_overlap_trace
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
  (Matrix.conjTranspose
          ρ.toSubnormalized.hatExtension.canonicalPurification.amplitudeMatrix *
        ρ.fixedPetzThresholdHatCompressedAmplitudeMatrix σ lambda).trace =
      (ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace := by
  classical
  rw [toSubnormalized_hatExtension_canonicalPurification_amplitudeMatrix]
  unfold fixedPetzThresholdHatCompressedAmplitudeMatrix
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp
  rw [Matrix.trace_fromBlocks_diagonal]
  simp
  calc
    (Matrix.conjTranspose ρ.sqrtMatrix *
        (ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.sqrtMatrix)).trace =
        (ρ.sqrtMatrix *
          (ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.sqrtMatrix)).trace := by
      rw [ρ.sqrtMatrix_isHermitian.eq]
    _ = ((ρ.sqrtMatrix * ρ.fixedPetzThresholdComplementProjector σ lambda) *
          ρ.sqrtMatrix).trace := by rw [Matrix.mul_assoc]
    _ = (ρ.fixedPetzThresholdComplementProjector σ lambda *
          (ρ.sqrtMatrix * ρ.sqrtMatrix)).trace := by
      calc
        ((ρ.sqrtMatrix * ρ.fixedPetzThresholdComplementProjector σ lambda) *
            ρ.sqrtMatrix).trace =
          (ρ.sqrtMatrix *
            (ρ.sqrtMatrix * ρ.fixedPetzThresholdComplementProjector σ lambda)).trace := by
            rw [Matrix.trace_mul_comm]
        _ = ((ρ.sqrtMatrix * ρ.sqrtMatrix) *
              ρ.fixedPetzThresholdComplementProjector σ lambda).trace := by
            rw [← Matrix.mul_assoc]
        _ = (ρ.fixedPetzThresholdComplementProjector σ lambda *
              (ρ.sqrtMatrix * ρ.sqrtMatrix)).trace := by
            rw [Matrix.trace_mul_comm]
    _ = (ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace := by
      rw [ρ.sqrtMatrix_mul_self]
    _ = (ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace := rfl

theorem fixedPetzThresholdCompressedSubstate_sq_trace_re_le_generalizedFidelity
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (((ρ.fixedPetzThresholdComplementProjector σ lambda * ρ.matrix).trace).re) ^ 2 ≤
      ρ.toSubnormalized.generalizedFidelity
        (ρ.fixedPetzThresholdCompressedSubstate σ lambda) := by
  classical
  let AΦ : CMatrix (Sum PUnit.{max u v + 1} (Prod a b)) :=
    ρ.fixedPetzThresholdHatCompressedAmplitudeMatrix σ lambda
  have htrace : (AΦ * Matrix.conjTranspose AΦ).trace = 1 := by
    rw [show AΦ * Matrix.conjTranspose AΦ =
        (ρ.fixedPetzThresholdCompressedSubstate σ lambda).hatExtension.matrix by
      simpa [AΦ] using
        ρ.fixedPetzThresholdHatCompressedAmplitudeMatrix_gram σ lambda]
    exact (ρ.fixedPetzThresholdCompressedSubstate σ lambda).hatExtension_trace_one
  let Φ := PureVector.ofAmplitudeMatrix AΦ htrace
  refine
    fixedPetzThresholdCompressedSubstate_sq_trace_re_le_generalizedFidelity_of_hatExtension_amplitudeMatrix_eq
      (ρ := ρ) (σ := σ) (lambda := lambda)
      (Ψ := ρ.toSubnormalized.hatExtension.canonicalPurification)
      (Φ := Φ) ?_ ?_ ?_
  · exact PureVector.purifies_amplitudeMatrix_mul_conjTranspose_eq
      ρ.toSubnormalized.hatExtension.canonicalPurification_purifies
  · simpa [Φ, AΦ, PureVector.ofAmplitudeMatrix_amplitudeMatrix] using
      ρ.fixedPetzThresholdHatCompressedAmplitudeMatrix_gram σ lambda
  · simpa [Φ, AΦ, PureVector.ofAmplitudeMatrix_amplitudeMatrix] using
      ρ.fixedPetzThresholdHatCompressedAmplitudeMatrix_overlap_trace σ lambda

theorem fixedPetzThresholdCompressedSubstate_purifiedBall_of_complement_fail
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfail :
      1 - (((ρ.fixedPetzThresholdComplementProjector σ lambda) *
        ρ.matrix).trace).re ≤ ε ^ 2 / 2) :
    ρ.toSubnormalized.purifiedBall ε
      (ρ.fixedPetzThresholdCompressedSubstate σ lambda) := by
  let τ : SubnormalizedState (Prod a b) :=
    ρ.fixedPetzThresholdCompressedSubstate σ lambda
  let Q : CMatrix (Prod a b) :=
    ρ.fixedPetzThresholdComplementProjector σ lambda
  let q : ℝ := ((Q * ρ.matrix).trace).re
  have hq_trace : τ.matrix.trace.re = q := by
    have hcyc : τ.matrix.trace = (ρ.matrix * Q).trace := by
      calc
        τ.matrix.trace = (Q * ρ.matrix * Q).trace := by
          simp [τ, Q, fixedPetzThresholdCompressedSubstate_matrix,
            fixedPetzThresholdCompressedMatrix]
        _ = (ρ.matrix * (Q * Q)).trace := by
          calc
            (Q * ρ.matrix * Q).trace = ((Q * ρ.matrix) * Q).trace := by
              rw [Matrix.mul_assoc]
            _ = (Q * (Q * ρ.matrix)).trace := by rw [Matrix.trace_mul_comm]
            _ = ((Q * Q) * ρ.matrix).trace := by rw [← Matrix.mul_assoc]
            _ = (ρ.matrix * (Q * Q)).trace := by rw [Matrix.trace_mul_comm]
        _ = (ρ.matrix * Q).trace := by
          rw [ρ.fixedPetzThresholdComplementProjector_idempotent σ lambda]
    rw [hcyc, Matrix.trace_mul_comm]
  have hgf :
      q ^ 2 ≤ ρ.toSubnormalized.generalizedFidelity τ := by
    simpa [τ, Q, q] using
      ρ.fixedPetzThresholdCompressedSubstate_sq_trace_re_le_generalizedFidelity σ lambda
  have hq_nonneg : 0 ≤ q := by
    simpa [hq_trace] using τ.trace_nonneg
  have hq_le_one : q ≤ 1 := by
    simpa [hq_trace] using τ.trace_le_one
  have hone_sub_gf :
      1 - ρ.toSubnormalized.generalizedFidelity τ ≤ ε ^ 2 := by
    have hone_sub_qsq : 1 - q ^ 2 ≤ ε ^ 2 := by
      have hfactor : 1 - q ^ 2 = (1 - q) * (1 + q) := by ring
      have htwo : 1 + q ≤ 2 := by linarith
      have hnon : 0 ≤ 1 - q := by linarith
      calc
        1 - q ^ 2 = (1 - q) * (1 + q) := hfactor
        _ ≤ (1 - q) * 2 := mul_le_mul_of_nonneg_left htwo hnon
        _ ≤ (ε ^ 2 / 2) * 2 := by
          exact mul_le_mul_of_nonneg_right (by simpa [Q, q] using hfail) (by norm_num)
        _ = ε ^ 2 := by ring
    linarith
  exact fixedPetzThresholdCompressedSubstate_purifiedBall_of_generalizedFidelity
    (ρ := ρ) (σ := σ) (lambda := lambda) hε (by simpa [τ] using hone_sub_gf)

/-- Two-sided compression by the complement of the fixed-reference threshold
projector satisfies the corresponding threshold operator inequality. -/
theorem fixedPetzThresholdComplement_compress_matrix_le
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (1 - ρ.fixedPetzThresholdProjector σ lambda) * ρ.matrix *
        (1 - ρ.fixedPetzThresholdProjector σ lambda) ≤
      (1 - ρ.fixedPetzThresholdProjector σ lambda) *
        (lambda • identityTensorStateMatrix (a := a) σ) *
          (1 - ρ.fixedPetzThresholdProjector σ lambda) := by
  let H : CMatrix (Prod a b) := ρ.fixedPetzThresholdMatrix σ lambda
  let hH : H.IsHermitian := ρ.fixedPetzThresholdMatrix_isHermitian σ lambda
  let P : CMatrix (Prod a b) := positiveSpectralProjector H hH
  let Q : CMatrix (Prod a b) := 1 - P
  let B : CMatrix (Prod a b) := lambda • identityTensorStateMatrix (a := a) σ
  change Q * ρ.matrix * Q ≤ Q * B * Q
  rw [Matrix.le_iff]
  have hselect : Q * (B - ρ.matrix) = H⁻ := by
    have h :=
      one_sub_positiveSpectralProjector_mul_neg_self_eq_negPart_fixed H hH
    simpa [Q, P, B, H, hH, fixedPetzThresholdMatrix,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hnegQ : H⁻ * Q = H⁻ := by
    have hnegP : H⁻ * P = 0 := by
      simpa [P] using negPart_mul_positiveSpectralProjector H hH
    calc
      H⁻ * Q = H⁻ * (1 - P) := rfl
      _ = H⁻ - H⁻ * P := by rw [mul_sub, mul_one]
      _ = H⁻ := by rw [hnegP]; simp
  have hdiff :
      Q * B * Q - Q * ρ.matrix * Q = Q * (B - ρ.matrix) * Q := by
    noncomm_ring
  rw [hdiff, hselect, hnegQ]
  exact Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H)

theorem fixedPetzThresholdCompressedMatrix_le_compressed_threshold
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    ρ.fixedPetzThresholdCompressedMatrix σ lambda ≤
      ρ.fixedPetzThresholdComplementProjector σ lambda *
        (lambda • identityTensorStateMatrix (a := a) σ) *
          ρ.fixedPetzThresholdComplementProjector σ lambda := by
  unfold fixedPetzThresholdCompressedMatrix fixedPetzThresholdComplementProjector
  exact ρ.fixedPetzThresholdComplement_compress_matrix_le σ lambda

theorem fixedPetzThresholdCompressedSubstate_le_compressed_threshold
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ) :
    (ρ.fixedPetzThresholdCompressedSubstate σ lambda).matrix ≤
      ρ.fixedPetzThresholdComplementProjector σ lambda *
        (lambda • identityTensorStateMatrix (a := a) σ) *
          ρ.fixedPetzThresholdComplementProjector σ lambda := by
  simpa using ρ.fixedPetzThresholdCompressedMatrix_le_compressed_threshold σ lambda

theorem fixedPetzThresholdCompressedSubstate_normalize_matrix
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (htr :
      (ρ.fixedPetzThresholdCompressedSubstate σ lambda).matrix.trace.re ≠ 0) :
    ((ρ.fixedPetzThresholdCompressedSubstate σ lambda).normalize htr).matrix =
      ((((ρ.fixedPetzThresholdCompressedSubstate σ lambda).matrix.trace.re)⁻¹ : ℝ) : ℂ) •
        ρ.fixedPetzThresholdCompressedMatrix σ lambda := by
  rw [SubnormalizedState.normalize_matrix]
  rfl

theorem fixedPetzThresholdCompressedSubstate_normalize_le_scaled_compressed_threshold
    (ρ : State (Prod a b)) (σ : State b) (lambda : ℝ)
    (htr :
      (ρ.fixedPetzThresholdCompressedSubstate σ lambda).matrix.trace.re ≠ 0) :
    ((ρ.fixedPetzThresholdCompressedSubstate σ lambda).normalize htr).matrix ≤
      ((((ρ.fixedPetzThresholdCompressedSubstate σ lambda).matrix.trace.re)⁻¹ : ℝ) : ℂ) •
        (ρ.fixedPetzThresholdComplementProjector σ lambda *
          (lambda • identityTensorStateMatrix (a := a) σ) *
            ρ.fixedPetzThresholdComplementProjector σ lambda) := by
  rw [fixedPetzThresholdCompressedSubstate_normalize_matrix]
  exact cMatrix_ofReal_smul_le_smul
    (inv_nonneg.mpr
      (ρ.fixedPetzThresholdCompressedSubstate σ lambda).trace_nonneg)
    (ρ.fixedPetzThresholdCompressedMatrix_le_compressed_threshold σ lambda)

/-- Any feasible fixed-reference exponent lower-bounds the fixed-reference
conditional min-entropy. -/
theorem le_conditionalMinEntropyFixed_of_feasible
    {ρ : State (Prod a b)} {σ : State b} {lam : ℝ}
    (hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    lam ≤ ρ.conditionalMinEntropyFixed σ := by
  rw [conditionalMinEntropyFixed_eq]
  refine le_csSup ?_ hfeas
  refine ⟨log2 (Fintype.card a : ℝ), ?_⟩
  intro mu hmu
  exact ConditionalMinEntropyFeasible_le_log2_card_left (a := a) hmu

/-- A purified-ball state with a feasible fixed-reference min-entropy exponent
gives a lower bound on fixed-reference smooth min-entropy. -/
theorem le_smoothConditionalMinEntropyFixed_of_feasible_witness
    {ρ ρ' : State (Prod a b)} {σ : State b} {ε lam lower : ℝ}
    (hball : ρ.purifiedBall ε ρ')
    (hfeas : ConditionalMinEntropyFeasible (a := a) ρ' σ lam)
    (hlower : lower ≤ lam) :
    lower ≤ ρ.smoothConditionalMinEntropyFixed σ ε := by
  have hmin : lam ≤ ρ'.conditionalMinEntropyFixed σ :=
    le_conditionalMinEntropyFixed_of_feasible (a := a) hfeas
  have hsmooth :
      ρ'.conditionalMinEntropyFixed σ ≤
        ρ.smoothConditionalMinEntropyFixed σ ε := by
    rw [smoothConditionalMinEntropyFixed_eq_sSup_candidates]
    exact le_csSup
      (SmoothConditionalMinEntropyFixedCandidate_bddAbove (a := a) ρ σ ε)
      (show SmoothConditionalMinEntropyFixedCandidate (a := a) ρ σ ε
        (ρ'.conditionalMinEntropyFixed σ) from ⟨ρ', hball, rfl⟩)
  exact le_trans hlower (le_trans hmin hsmooth)

/-- Petz-shaped fixed-reference smooth-min lower bound from a concrete
order-feasible smoothed witness.

This isolates the remaining TCR construction: produce a nearby state `ρ'` whose
fixed-reference min-entropy order constraint is feasible at the displayed Petz
threshold. -/
theorem smoothConditionalMinEntropyFixed_lower_bound_of_petz_feasible_witness
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (_hε_pos : 0 < ε) (_hε_lt : ε < 1)
    (hα_gt : 1 < α) (_hα_le_two : α ≤ 2)
    (ρ' : State (Prod a b))
    (hball : ρ.purifiedBall ε ρ')
    (hfeas :
      ConditionalMinEntropyFeasible (a := a) ρ' σ
        (ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
            (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
          (1 / (α - 1)) * log2 (2 / ε ^ 2))) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixed σ ε := by
  exact le_smoothConditionalMinEntropyFixed_of_feasible_witness
    (a := a) hball hfeas le_rfl

/-- An operator bound at the fixed-reference Petz threshold scale is exactly a
conditional-min-entropy feasible exponent at the Petz threshold. -/
theorem ConditionalMinEntropyFeasible.of_le_petzSmoothMinThresholdScale
    {ρ' : State (Prod a b)}
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1)
    (hbound :
      ρ'.matrix ≤
        ((ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one : ℝ) : ℂ) •
          identityTensorStateMatrix (a := a) σ) :
    ConditionalMinEntropyFeasible (a := a) ρ' σ
      (ρ.petzSmoothMinThresholdExponent hρ σ hσ ε α hα_pos hα_ne_one) := by
  simpa [ConditionalMinEntropyFeasible, petzSmoothMinThresholdScale] using hbound

/-- Petz-shaped fixed-reference smooth-min lower bound from a concrete
operator-order smoothed witness at the Petz threshold scale. -/
theorem smoothConditionalMinEntropyFixed_lower_bound_of_petz_operator_bound
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (ρ' : State (Prod a b))
    (hball : ρ.purifiedBall ε ρ')
    (hbound :
      ρ'.matrix ≤
        ((ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) : ℝ) : ℂ) •
          identityTensorStateMatrix (a := a) σ) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
      (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
        ρ.smoothConditionalMinEntropyFixed σ ε := by
  exact smoothConditionalMinEntropyFixed_lower_bound_of_petz_feasible_witness
    (ρ := ρ) hρ (σ := σ) hσ ε α hε_pos hε_lt hα_gt hα_le_two
    ρ' hball
    (ConditionalMinEntropyFeasible.of_le_petzSmoothMinThresholdScale
      (a := a) (ρ' := ρ') ρ hρ σ hσ ε α
      (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) hbound)

end State

end

end QIT
