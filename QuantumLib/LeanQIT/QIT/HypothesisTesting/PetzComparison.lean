/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.OneShot.Lower.Petz
public import QIT.Coding.EntanglementAssisted.OneShot.Lower.HypothesisTesting
public import QIT.HypothesisTesting.ComparatorTest
public import QIT.States.TraceNorm.Audenaert
public import QIT.States.Schatten

/-!
# Hypothesis-testing to Petz-Renyi comparison infrastructure

This module begins the proof-dependency layer for the Khatri--Wilde
hypothesis-testing/Petz--Renyi comparison
[KhatriWilde2024Principles, Chapters/entropies.tex:7037-7042].

The comparison proof uses a Neyman--Pearson threshold effect built from the
positive spectral projector of `rho - lambda sigma`, then combines its
type-I/type-II bounds with Audenaert's trace inequality.  This file provides
the threshold-effect API; the final comparison theorem is a downstream target.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

private theorem chosenThreshold_budget_eq
    {epsilon T alpha : ℝ} (hε : 0 < epsilon) (hT : 0 < T) (halpha : alpha < 1) :
    ((epsilon / T) ^ (1 / (1 - alpha))) ^ (1 - alpha) * T = epsilon := by
  have hden : 1 - alpha ≠ 0 := ne_of_gt (sub_pos.mpr halpha)
  have hratio_nonneg : 0 ≤ epsilon / T := le_of_lt (div_pos hε hT)
  calc
    ((epsilon / T) ^ (1 / (1 - alpha))) ^ (1 - alpha) * T =
        (epsilon / T) ^ ((1 / (1 - alpha)) * (1 - alpha)) * T := by
          rw [← Real.rpow_mul hratio_nonneg]
    _ = (epsilon / T) * T := by
          have hexp : (1 / (1 - alpha)) * (1 - alpha) = 1 := by
            field_simp [hden]
          rw [hexp, Real.rpow_one]
    _ = epsilon := by
          field_simp [ne_of_gt hT]

private theorem neg_log2_chosenThreshold_budget_div_eq
    {epsilon T alpha : ℝ} (hε : 0 < epsilon) (hT : 0 < T) (halpha : alpha < 1) :
    -log2
        (epsilon /
          ((epsilon / T) ^ (1 / (1 - alpha)))) =
      1 / (alpha - 1) * log2 T +
        alpha / (alpha - 1) * log2 (1 / epsilon) := by
  have hratio : 0 < epsilon / T := div_pos hε hT
  have hden1 : 1 - alpha ≠ 0 := ne_of_gt (sub_pos.mpr halpha)
  have hden2 : alpha - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt halpha)
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hlambda_pos : 0 < (epsilon / T) ^ (1 / (1 - alpha)) :=
    Real.rpow_pos_of_pos hratio _
  unfold log2
  rw [Real.log_div hε.ne' hlambda_pos.ne']
  rw [Real.log_rpow hratio]
  rw [Real.log_div hε.ne' hT.ne']
  rw [Real.log_div one_ne_zero hε.ne']
  simp
  field_simp [hlog2, hden1, hden2]
  ring

/-- Real powers commute with nonnegative real scalar multiplication of a PSD
matrix.  This finite-dimensional CFC lemma is the scalar step needed to turn
the Audenaert budget with `lambda * sigma` into the Petz coefficient. -/
theorem cMatrix_rpow_real_smul_posSemidef
    {A : CMatrix a} (hA : A.PosSemidef) {lambda s : ℝ} (hlambda : 0 ≤ lambda) :
    CFC.rpow (lambda • A : CMatrix a) s =
      (lambda ^ s : ℝ) • CFC.rpow A s := by
  let U : Matrix.unitaryGroup a ℂ := hA.isHermitian.eigenvectorUnitary
  let d : a → ℝ := hA.isHermitian.eigenvalues
  have hd : ∀ i, 0 ≤ d i := fun i => hA.eigenvalues_nonneg i
  have hA_spec :
      A = (U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a) := by
    simpa [U, d, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hA.isHermitian.spectral_theorem
  have hscaled_spec :
      (lambda • A : CMatrix a) =
        (U : CMatrix a) *
          (Matrix.diagonal fun i => ((lambda * d i : ℝ) : ℂ)) *
            star (U : CMatrix a) := by
    rw [hA_spec]
    have hdiag :
        (lambda • (Matrix.diagonal fun i => (d i : ℂ)) : CMatrix a) =
          Matrix.diagonal fun i => ((lambda * d i : ℝ) : ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.smul_apply]
      · simp [Matrix.smul_apply, Matrix.diagonal, hij]
    calc
      (lambda • (((U : CMatrix a) *
          (Matrix.diagonal fun i => (d i : ℂ))) * star (U : CMatrix a)) :
          CMatrix a)
          = (lambda • ((U : CMatrix a) *
              (Matrix.diagonal fun i => (d i : ℂ))) : CMatrix a) *
                star (U : CMatrix a) := by
              rw [Matrix.smul_mul]
      _ = ((U : CMatrix a) *
              (lambda • (Matrix.diagonal fun i => (d i : ℂ)) : CMatrix a)) *
                star (U : CMatrix a) := by
              rw [Matrix.mul_smul]
      _ = (U : CMatrix a) *
          (Matrix.diagonal fun i => ((lambda * d i : ℝ) : ℂ)) *
            star (U : CMatrix a) := by
              rw [hdiag]
  have hscaled_nonneg : ∀ i, 0 ≤ lambda * d i := fun i => mul_nonneg hlambda (hd i)
  rw [hscaled_spec]
  rw [cMatrix_rpow_unitary_conj_diagonal_ofReal U (fun i => lambda * d i)
    hscaled_nonneg s]
  rw [cMatrix_rpow_eq_eigenbasis_diagonal hA s]
  have hdiag_pow :
      Matrix.diagonal (fun i => (((lambda * d i) ^ s : ℝ) : ℂ)) =
        ((lambda ^ s : ℝ) •
          Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) : CMatrix a) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.smul_apply, Real.mul_rpow hlambda (hd _)]
    · simp [Matrix.smul_apply, Matrix.diagonal, hij]
  rw [hdiag_pow]
  calc
    (U : CMatrix a) *
          (((lambda ^ s : ℝ) •
            Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) : CMatrix a)) *
        star (U : CMatrix a)
        = ((lambda ^ s : ℝ) •
            ((U : CMatrix a) *
              Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ))) : CMatrix a) *
            star (U : CMatrix a) := by
          rw [Matrix.mul_smul]
    _ = ((lambda ^ s : ℝ) •
          (((U : CMatrix a) *
            Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ))) *
              star (U : CMatrix a)) : CMatrix a) := by
          rw [Matrix.smul_mul]

namespace State

/-- Hermitian threshold matrix `rho - lambda sigma` used in the
Neyman--Pearson proof of the hypothesis-testing/Petz comparison. -/
def petzThresholdMatrix (rho sigma : State a) (lambda : ℝ) : CMatrix a :=
  rho.matrix - lambda • sigma.matrix

theorem petzThresholdMatrix_isHermitian (rho sigma : State a) (lambda : ℝ) :
    (rho.petzThresholdMatrix sigma lambda).IsHermitian := by
  unfold petzThresholdMatrix
  exact rho.pos.isHermitian.sub (sigma.pos.isHermitian.smul (IsSelfAdjoint.all lambda))

/-- Positive spectral projector of `rho - lambda sigma`. -/
def petzThresholdProjector (rho sigma : State a) (lambda : ℝ) : CMatrix a :=
  positiveSpectralProjector
    (rho.petzThresholdMatrix sigma lambda)
    (rho.petzThresholdMatrix_isHermitian sigma lambda)

theorem petzThresholdProjector_posSemidef (rho sigma : State a) (lambda : ℝ) :
    (rho.petzThresholdProjector sigma lambda).PosSemidef := by
  unfold petzThresholdProjector
  exact positiveSpectralProjector_posSemidef
    (rho.petzThresholdMatrix sigma lambda)
    (rho.petzThresholdMatrix_isHermitian sigma lambda)

theorem petzThresholdProjector_le_one (rho sigma : State a) (lambda : ℝ) :
    rho.petzThresholdProjector sigma lambda ≤ 1 := by
  unfold petzThresholdProjector
  exact positiveSpectralProjector_le_one
    (rho.petzThresholdMatrix sigma lambda)
    (rho.petzThresholdMatrix_isHermitian sigma lambda)

/-- The scaled second hypothesis `lambda sigma` is PSD for nonnegative
threshold parameter `lambda`. -/
theorem petzThreshold_scaledSigma_posSemidef
    (sigma : State a) {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    (lambda • sigma.matrix : CMatrix a).PosSemidef :=
  Matrix.PosSemidef.smul sigma.pos hlambda

/-- Audenaert budget for the threshold proof, with `B = lambda sigma`. -/
def petzThresholdAudenaertBudget
    (rho sigma : State a) (lambda alpha : ℝ) : ℝ :=
  ((CFC.rpow rho.matrix alpha *
      CFC.rpow (lambda • sigma.matrix : CMatrix a) (1 - alpha)).trace).re

/-- Audenaert's threshold budget is the Petz trace objective multiplied by
`lambda^(1-alpha)`. -/
theorem petzThresholdAudenaertBudget_eq_lambda_rpow_mul_petzTrace
    (rho sigma : State a) {lambda alpha : ℝ} (hlambda : 0 ≤ lambda) :
    rho.petzThresholdAudenaertBudget sigma lambda alpha =
      lambda ^ (1 - alpha) *
        ((CFC.rpow rho.matrix alpha *
          CFC.rpow sigma.matrix (1 - alpha)).trace).re := by
  unfold petzThresholdAudenaertBudget
  rw [cMatrix_rpow_real_smul_posSemidef sigma.pos hlambda]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  simp

theorem petzThresholdAudenaertBudget_ge_traceAbsRhs
    (rho sigma : State a) {lambda alpha : ℝ}
    (hlambda : 0 ≤ lambda) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    rho.petzThresholdAudenaertBudget sigma lambda alpha ≥
      ((rho.matrix + lambda • sigma.matrix -
          CFC.abs (rho.matrix - lambda • sigma.matrix)).trace).re / 2 := by
  unfold petzThresholdAudenaertBudget
  exact audenaertTraceInequality halpha0 halpha1 rho.pos
    (petzThreshold_scaledSigma_posSemidef sigma hlambda)

theorem petzThreshold_traceAbsRhs_eq_trace_sub_posPart
    (rho sigma : State a) {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    ((rho.matrix + lambda • sigma.matrix -
        CFC.abs (rho.matrix - lambda • sigma.matrix)).trace).re / 2 =
      rho.matrix.trace.re -
        ((rho.petzThresholdMatrix sigma lambda)⁺).trace.re := by
  simpa [petzThresholdMatrix] using
    audenaertTraceAbsRhs_eq_trace_sub_posPart rho.pos
      (petzThreshold_scaledSigma_posSemidef sigma hlambda)

theorem petzThresholdAudenaertBudget_ge_trace_sub_posPart
    (rho sigma : State a) {lambda alpha : ℝ}
    (hlambda : 0 ≤ lambda) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    rho.petzThresholdAudenaertBudget sigma lambda alpha ≥
      rho.matrix.trace.re - ((rho.petzThresholdMatrix sigma lambda)⁺).trace.re := by
  calc
    rho.petzThresholdAudenaertBudget sigma lambda alpha ≥
        ((rho.matrix + lambda • sigma.matrix -
            CFC.abs (rho.matrix - lambda • sigma.matrix)).trace).re / 2 :=
      rho.petzThresholdAudenaertBudget_ge_traceAbsRhs sigma hlambda halpha0 halpha1
    _ = rho.matrix.trace.re - ((rho.petzThresholdMatrix sigma lambda)⁺).trace.re :=
      rho.petzThreshold_traceAbsRhs_eq_trace_sub_posPart sigma hlambda

theorem petzThresholdProjector_score_eq_posPart_trace
    (rho sigma : State a) (lambda : ℝ) :
    ((rho.petzThresholdMatrix sigma lambda *
        rho.petzThresholdProjector sigma lambda).trace).re =
      ((rho.petzThresholdMatrix sigma lambda)⁺).trace.re := by
  unfold petzThresholdProjector
  exact positiveSpectralProjector_score_eq_posPart_trace
    (rho.petzThresholdMatrix sigma lambda)
    (rho.petzThresholdMatrix_isHermitian sigma lambda)

theorem petzThreshold_trace_sub_posPart_eq_typeBudget
    (rho sigma : State a) (lambda : ℝ) :
    rho.matrix.trace.re - ((rho.petzThresholdMatrix sigma lambda)⁺).trace.re =
      1 - effectAcceptProbability rho (rho.petzThresholdProjector sigma lambda) +
        lambda * effectTypeIIError sigma (rho.petzThresholdProjector sigma lambda) := by
  have hscore := rho.petzThresholdProjector_score_eq_posPart_trace sigma lambda
  unfold petzThresholdMatrix at hscore
  unfold effectAcceptProbability effectTypeIIError
  change rho.matrix.trace.re - ((rho.matrix - lambda • sigma.matrix)⁺).trace.re =
      1 - ((rho.matrix * rho.petzThresholdProjector sigma lambda).trace).re +
        lambda * ((sigma.matrix * rho.petzThresholdProjector sigma lambda).trace).re
  rw [← hscore]
  rw [rho.trace_eq_one]
  simp [Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_smul, Complex.real_smul]
  ring

theorem petzThresholdAudenaertBudget_ge_typeBudget
    (rho sigma : State a) {lambda alpha : ℝ}
    (hlambda : 0 ≤ lambda) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    rho.petzThresholdAudenaertBudget sigma lambda alpha ≥
      1 - effectAcceptProbability rho (rho.petzThresholdProjector sigma lambda) +
        lambda * effectTypeIIError sigma (rho.petzThresholdProjector sigma lambda) := by
  calc
    rho.petzThresholdAudenaertBudget sigma lambda alpha ≥
        rho.matrix.trace.re - ((rho.petzThresholdMatrix sigma lambda)⁺).trace.re :=
      rho.petzThresholdAudenaertBudget_ge_trace_sub_posPart sigma hlambda halpha0 halpha1
    _ = 1 - effectAcceptProbability rho (rho.petzThresholdProjector sigma lambda) +
        lambda * effectTypeIIError sigma (rho.petzThresholdProjector sigma lambda) :=
      rho.petzThreshold_trace_sub_posPart_eq_typeBudget sigma lambda

/-- The threshold effect has nonnegative type-II error. -/
theorem petzThreshold_typeIIError_nonneg
    (rho sigma : State a) (lambda : ℝ) :
    0 ≤ effectTypeIIError sigma (rho.petzThresholdProjector sigma lambda) := by
  unfold effectTypeIIError effectAcceptProbability
  exact cMatrix_trace_mul_posSemidef_re_nonneg sigma.pos
    (rho.petzThresholdProjector_posSemidef sigma lambda)

/-- The threshold effect has accept probability at most one. -/
theorem petzThreshold_accept_le_one
    (rho sigma : State a) (lambda : ℝ) :
    effectAcceptProbability rho (rho.petzThresholdProjector sigma lambda) ≤ 1 := by
  have hcompl :
      (1 - rho.petzThresholdProjector sigma lambda).PosSemidef := by
    simpa [Matrix.le_iff] using rho.petzThresholdProjector_le_one sigma lambda
  have hnonneg :
      0 ≤ ((rho.matrix * (1 - rho.petzThresholdProjector sigma lambda)).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg rho.pos hcompl
  have htrace :
      ((rho.matrix * (1 - rho.petzThresholdProjector sigma lambda)).trace).re =
        1 - effectAcceptProbability rho (rho.petzThresholdProjector sigma lambda) := by
    unfold effectAcceptProbability
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, rho.trace_eq_one]
    simp
  linarith

/-- Audenaert's budget controls the type-I error of the threshold effect. -/
theorem petzThreshold_typeIError_le_budget
    (rho sigma : State a) {lambda alpha : ℝ}
    (hlambda : 0 ≤ lambda) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    1 - effectAcceptProbability rho (rho.petzThresholdProjector sigma lambda) ≤
      rho.petzThresholdAudenaertBudget sigma lambda alpha := by
  have hbudget :=
    rho.petzThresholdAudenaertBudget_ge_typeBudget sigma hlambda halpha0 halpha1
  have herr_nonneg :
      0 ≤ lambda * effectTypeIIError sigma (rho.petzThresholdProjector sigma lambda) :=
    mul_nonneg hlambda (rho.petzThreshold_typeIIError_nonneg sigma lambda)
  linarith

/-- Audenaert's budget controls the type-II error of the threshold effect after
division by the positive threshold parameter. -/
theorem petzThreshold_typeIIError_le_budget_div
    (rho sigma : State a) {lambda alpha : ℝ}
    (hlambda : 0 < lambda) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    effectTypeIIError sigma (rho.petzThresholdProjector sigma lambda) ≤
      rho.petzThresholdAudenaertBudget sigma lambda alpha / lambda := by
  have hbudget :=
    rho.petzThresholdAudenaertBudget_ge_typeBudget sigma (le_of_lt hlambda) halpha0 halpha1
  have haccept_le := rho.petzThreshold_accept_le_one sigma lambda
  have hmul :
      lambda * effectTypeIIError sigma (rho.petzThresholdProjector sigma lambda) ≤
        rho.petzThresholdAudenaertBudget sigma lambda alpha := by
    linarith
  exact (le_div_iff₀ hlambda).mpr (by simpa [mul_comm] using hmul)

/-- If Audenaert's budget is at most `epsilon`, the threshold projector is a
feasible hypothesis-testing effect at type-I level `epsilon`. -/
def petzThresholdHypothesisTestingEffectOfBudget
    (rho sigma : State a) (epsilon : ℝ) {lambda alpha : ℝ}
    (hlambda : 0 ≤ lambda) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hbudget : rho.petzThresholdAudenaertBudget sigma lambda alpha ≤ epsilon) :
    HypothesisTestingEffect rho epsilon :=
  { effect := rho.petzThresholdProjector sigma lambda
    pos := rho.petzThresholdProjector_posSemidef sigma lambda
    le_one := rho.petzThresholdProjector_le_one sigma lambda
    accept_ge := by
      have htypeI :=
        rho.petzThreshold_typeIError_le_budget sigma hlambda halpha0 halpha1
      linarith }

@[simp]
theorem petzThresholdHypothesisTestingEffectOfBudget_effect
    (rho sigma : State a) (epsilon : ℝ) {lambda alpha : ℝ}
    (hlambda : 0 ≤ lambda) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hbudget : rho.petzThresholdAudenaertBudget sigma lambda alpha ≤ epsilon) :
    (rho.petzThresholdHypothesisTestingEffectOfBudget sigma epsilon hlambda
        halpha0 halpha1 hbudget).effect =
      rho.petzThresholdProjector sigma lambda :=
  rfl

@[simp]
theorem petzThresholdHypothesisTestingEffectOfBudget_typeIIError
    (rho sigma : State a) (epsilon : ℝ) {lambda alpha : ℝ}
    (hlambda : 0 ≤ lambda) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hbudget : rho.petzThresholdAudenaertBudget sigma lambda alpha ≤ epsilon) :
    (rho.petzThresholdHypothesisTestingEffectOfBudget sigma epsilon hlambda
        halpha0 halpha1 hbudget).typeIIError sigma =
      effectTypeIIError sigma (rho.petzThresholdProjector sigma lambda) :=
  rfl

/-- Threshold-test upper bound on `beta_epsilon`, parameterized by the
Audenaert budget and a positive threshold. -/
theorem hypothesisTestingBeta_le_petzThreshold_budget_div
    (rho sigma : State a) {epsilon lambda alpha : ℝ}
    (hlambda : 0 < lambda) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hbudget : rho.petzThresholdAudenaertBudget sigma lambda alpha ≤ epsilon) :
    rho.hypothesisTestingBeta sigma epsilon ≤
      rho.petzThresholdAudenaertBudget sigma lambda alpha / lambda := by
  let Λ :=
    rho.petzThresholdHypothesisTestingEffectOfBudget sigma epsilon
      (le_of_lt hlambda) halpha0 halpha1 hbudget
  have hβ := rho.hypothesisTestingBeta_le_of_effect sigma epsilon Λ
  have hΛ :
      Λ.typeIIError sigma =
        effectTypeIIError sigma (rho.petzThresholdProjector sigma lambda) := by
    simp [Λ]
  have htypeII :=
    rho.petzThreshold_typeIIError_le_budget_div sigma hlambda halpha0 halpha1
  linarith

/-- Real-valued hypothesis-testing relative entropy lower bound induced by the
threshold test.  The positive-beta side condition is inherited from the
current real-valued `D_H` API; an extended-real version can remove it later. -/
theorem neg_log2_petzThreshold_budget_div_le_hypothesisTestingRelativeEntropyFinite
    (rho sigma : State a) {epsilon lambda alpha : ℝ}
    (hlambda : 0 < lambda) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hbudget : rho.petzThresholdAudenaertBudget sigma lambda alpha ≤ epsilon)
    (hβpos : 0 < rho.hypothesisTestingBeta sigma epsilon) :
    -log2 (rho.petzThresholdAudenaertBudget sigma lambda alpha / lambda) ≤
      rho.hypothesisTestingRelativeEntropyFinite sigma epsilon := by
  exact rho.neg_log2_le_hypothesisTestingRelativeEntropyFinite_of_beta_le sigma epsilon
    hβpos
    (rho.hypothesisTestingBeta_le_petzThreshold_budget_div sigma hlambda
      halpha0 halpha1 hbudget)

/-- Extended-real version of the threshold lower bound.  The zero-beta branch
of `D_H` is `⊤`, so no beta-positivity hypothesis is needed. -/
theorem neg_log2_petzThreshold_budget_div_le_hypothesisTestingRelativeEntropy
    (rho sigma : State a) {epsilon lambda alpha : ℝ}
    (hε : 0 ≤ epsilon)
    (hlambda : 0 < lambda) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hbudget : rho.petzThresholdAudenaertBudget sigma lambda alpha ≤ epsilon) :
    ((-log2 (rho.petzThresholdAudenaertBudget sigma lambda alpha / lambda) : ℝ) :
        EReal) ≤
      rho.hypothesisTestingRelativeEntropy sigma epsilon := by
  rw [rho.hypothesisTestingRelativeEntropy_eq sigma epsilon]
  by_cases hzero : rho.hypothesisTestingBeta sigma epsilon = 0
  · simp [hzero]
  · have hβ_nonneg := rho.hypothesisTestingBeta_nonneg sigma epsilon hε
    have hβpos : 0 < rho.hypothesisTestingBeta sigma epsilon :=
      lt_of_le_of_ne hβ_nonneg (Ne.symm hzero)
    have hreal :=
      rho.neg_log2_petzThreshold_budget_div_le_hypothesisTestingRelativeEntropyFinite
        sigma hlambda halpha0 halpha1 hbudget hβpos
    simpa [hzero, EReal.coe_neg] using (EReal.coe_le_coe_iff.mpr hreal)

/-- Source-shaped threshold lower bound after rewriting the Audenaert budget
as the scaled Petz trace objective.  The remaining source proof step is the
choice of `lambda` and the associated `log2` optimization. -/
theorem neg_log2_scaledPetzTrace_div_lambda_le_hypothesisTestingRelativeEntropyFinite
    (rho sigma : State a) {epsilon lambda alpha : ℝ}
    (hlambda : 0 < lambda) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hbudget :
      lambda ^ (1 - alpha) *
          ((CFC.rpow rho.matrix alpha *
            CFC.rpow sigma.matrix (1 - alpha)).trace).re ≤ epsilon)
    (hβpos : 0 < rho.hypothesisTestingBeta sigma epsilon) :
    -log2
        ((lambda ^ (1 - alpha) *
            ((CFC.rpow rho.matrix alpha *
              CFC.rpow sigma.matrix (1 - alpha)).trace).re) / lambda) ≤
      rho.hypothesisTestingRelativeEntropyFinite sigma epsilon := by
  have hbudget' :
      rho.petzThresholdAudenaertBudget sigma lambda alpha ≤ epsilon := by
    rwa [rho.petzThresholdAudenaertBudget_eq_lambda_rpow_mul_petzTrace sigma
      (le_of_lt hlambda)]
  have h :=
    rho.neg_log2_petzThreshold_budget_div_le_hypothesisTestingRelativeEntropyFinite
      sigma hlambda halpha0 halpha1 hbudget' hβpos
  rwa [rho.petzThresholdAudenaertBudget_eq_lambda_rpow_mul_petzTrace sigma
      (le_of_lt hlambda)] at h

/-- Extended-real threshold lower bound after rewriting Audenaert's budget as
the scaled Petz trace objective. -/
theorem neg_log2_scaledPetzTrace_div_lambda_le_hypothesisTestingRelativeEntropy
    (rho sigma : State a) {epsilon lambda alpha : ℝ}
    (hε : 0 ≤ epsilon)
    (hlambda : 0 < lambda) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hbudget :
      lambda ^ (1 - alpha) *
          ((CFC.rpow rho.matrix alpha *
            CFC.rpow sigma.matrix (1 - alpha)).trace).re ≤ epsilon) :
    ((-log2
        ((lambda ^ (1 - alpha) *
            ((CFC.rpow rho.matrix alpha *
              CFC.rpow sigma.matrix (1 - alpha)).trace).re) / lambda) : ℝ) :
        EReal) ≤
      rho.hypothesisTestingRelativeEntropy sigma epsilon := by
  have hbudget' :
      rho.petzThresholdAudenaertBudget sigma lambda alpha ≤ epsilon := by
    rwa [rho.petzThresholdAudenaertBudget_eq_lambda_rpow_mul_petzTrace sigma
      (le_of_lt hlambda)]
  have h :=
    rho.neg_log2_petzThreshold_budget_div_le_hypothesisTestingRelativeEntropy
      sigma hε hlambda halpha0 halpha1 hbudget'
  rwa [rho.petzThresholdAudenaertBudget_eq_lambda_rpow_mul_petzTrace sigma
      (le_of_lt hlambda)] at h

/-- Khatri--Wilde hypothesis-testing/Petz--Renyi comparison, in the
positive-definite domain of the current `State.petzRenyi` API.

This proves the source inequality
`D_H^epsilon(rho || sigma) >= D_alpha(rho || sigma)
  + alpha/(alpha-1) log_2(1/epsilon)` for `0 < alpha < 1`, with the explicit
positive-beta side condition required by the real-valued `D_H` encoding. -/
theorem petzRenyi_add_log_inv_epsilon_le_hypothesisTestingRelativeEntropyFinite
    (rho sigma : State a)
    (hρ : rho.matrix.PosDef) (hσ : sigma.matrix.PosDef)
    {epsilon alpha : ℝ} (hε : 0 < epsilon)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hβpos : 0 < rho.hypothesisTestingBeta sigma epsilon) :
    rho.petzRenyi sigma hρ hσ alpha halpha0 (ne_of_lt halpha1) +
        alpha / (alpha - 1) * log2 (1 / epsilon) ≤
      rho.hypothesisTestingRelativeEntropyFinite sigma epsilon := by
  haveI : Nonempty a := rho.nonempty
  let T : ℝ :=
    ((CFC.rpow rho.matrix alpha *
      CFC.rpow sigma.matrix (1 - alpha)).trace).re
  have hTpos : 0 < T := by
    dsimp [T]
    exact trace_mul_posDef_re_pos
      (rho.rpowMatrix_posDef_of_posDef hρ alpha)
      (sigma.rpowMatrix_posDef_of_posDef hσ (1 - alpha))
  let lambda : ℝ := (epsilon / T) ^ (1 / (1 - alpha))
  have hlambda_pos : 0 < lambda := by
    dsimp [lambda]
    exact Real.rpow_pos_of_pos (div_pos hε hTpos) _
  have hbudget :
      lambda ^ (1 - alpha) *
          ((CFC.rpow rho.matrix alpha *
            CFC.rpow sigma.matrix (1 - alpha)).trace).re ≤ epsilon := by
    change lambda ^ (1 - alpha) * T ≤ epsilon
    exact le_of_eq (chosenThreshold_budget_eq hε hTpos halpha1)
  have hlower :=
    rho.neg_log2_scaledPetzTrace_div_lambda_le_hypothesisTestingRelativeEntropyFinite
      sigma hlambda_pos (le_of_lt halpha0) (le_of_lt halpha1) hbudget hβpos
  have hleft :
      -log2
          ((lambda ^ (1 - alpha) *
              ((CFC.rpow rho.matrix alpha *
                CFC.rpow sigma.matrix (1 - alpha)).trace).re) / lambda) =
        rho.petzRenyi sigma hρ hσ alpha halpha0 (ne_of_lt halpha1) +
          alpha / (alpha - 1) * log2 (1 / epsilon) := by
    change -log2 (lambda ^ (1 - alpha) * T / lambda) =
        rho.petzRenyi sigma hρ hσ alpha halpha0 (ne_of_lt halpha1) +
          alpha / (alpha - 1) * log2 (1 / epsilon)
    rw [chosenThreshold_budget_eq hε hTpos halpha1]
    dsimp [lambda]
    rw [neg_log2_chosenThreshold_budget_div_eq hε hTpos halpha1]
    unfold petzRenyi
    dsimp [T]
  rw [← hleft]
  exact hlower

/-- Khatri--Wilde hypothesis-testing/Petz--Renyi comparison in the PSD
`0 < alpha < 1` branch, with the Petz trace positivity supplied explicitly.

The explicit trace-positivity hypothesis is the finite-dimensional support
condition that is automatic in the barred mutual-information specialization
`rho_AB || rho_A tensor rho_B`, but it is not true for arbitrary disjoint PSD
states. -/
theorem petzRenyiPSDFinite_add_log_inv_epsilon_le_hypothesisTestingRelativeEntropy
    (rho sigma : State a)
    {epsilon alpha : ℝ} (hε : 0 < epsilon)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hTpos :
      0 <
        ((CFC.rpow rho.matrix alpha *
          CFC.rpow sigma.matrix (1 - alpha)).trace).re) :
    ((rho.petzRenyiPSDFinite sigma alpha halpha0 (ne_of_lt halpha1) +
        alpha / (alpha - 1) * log2 (1 / epsilon) : ℝ) : EReal) ≤
      rho.hypothesisTestingRelativeEntropy sigma epsilon := by
  let T : ℝ :=
    ((CFC.rpow rho.matrix alpha *
      CFC.rpow sigma.matrix (1 - alpha)).trace).re
  have hTpos' : 0 < T := by
    simpa [T] using hTpos
  let lambda : ℝ := (epsilon / T) ^ (1 / (1 - alpha))
  have hlambda_pos : 0 < lambda := by
    dsimp [lambda]
    exact Real.rpow_pos_of_pos (div_pos hε hTpos') _
  have hbudget :
      lambda ^ (1 - alpha) *
          ((CFC.rpow rho.matrix alpha *
            CFC.rpow sigma.matrix (1 - alpha)).trace).re ≤ epsilon := by
    change lambda ^ (1 - alpha) * T ≤ epsilon
    exact le_of_eq (chosenThreshold_budget_eq hε hTpos' halpha1)
  have hlower :=
    rho.neg_log2_scaledPetzTrace_div_lambda_le_hypothesisTestingRelativeEntropy
      sigma (le_of_lt hε) hlambda_pos (le_of_lt halpha0) (le_of_lt halpha1) hbudget
  have hleft :
      -log2
          ((lambda ^ (1 - alpha) *
              ((CFC.rpow rho.matrix alpha *
                CFC.rpow sigma.matrix (1 - alpha)).trace).re) / lambda) =
        rho.petzRenyiPSDFinite sigma alpha halpha0 (ne_of_lt halpha1) +
          alpha / (alpha - 1) * log2 (1 / epsilon) := by
    change -log2 (lambda ^ (1 - alpha) * T / lambda) =
        rho.petzRenyiPSDFinite sigma alpha halpha0 (ne_of_lt halpha1) +
          alpha / (alpha - 1) * log2 (1 / epsilon)
    rw [chosenThreshold_budget_eq hε hTpos' halpha1]
    dsimp [lambda]
    rw [neg_log2_chosenThreshold_budget_div_eq hε hTpos' halpha1]
    unfold State.petzRenyiPSDFinite
    dsimp [T]
  have hleftE :
      ((rho.petzRenyiPSDFinite sigma alpha halpha0 (ne_of_lt halpha1) +
          alpha / (alpha - 1) * log2 (1 / epsilon) : ℝ) : EReal) =
        ((-log2
          ((lambda ^ (1 - alpha) *
              ((CFC.rpow rho.matrix alpha *
                CFC.rpow sigma.matrix (1 - alpha)).trace).re) / lambda) : ℝ) :
            EReal) := by
    exact congrArg (fun x : ℝ => (x : EReal)) hleft.symm
  rw [hleftE]
  exact hlower

/-- Source-facing extended-real form of the PSD Petz/hypothesis-testing
comparison on the positive trace-coefficient branch. -/
theorem petzRenyiPSD_add_log_inv_epsilon_le_hypothesisTestingRelativeEntropy
    (rho sigma : State a)
    {epsilon alpha : ℝ} (hε : 0 < epsilon)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hTpos : 0 < rho.petzRenyiPSDTraceCoeff sigma alpha) :
    rho.petzRenyiPSD sigma alpha halpha0 halpha1 +
        ((alpha / (alpha - 1) * log2 (1 / epsilon) : ℝ) : EReal) ≤
      rho.hypothesisTestingRelativeEntropy sigma epsilon := by
  rw [rho.petzRenyiPSD_eq_coe_finite_of_traceCoeff_ne_zero
    sigma alpha halpha0 halpha1 (ne_of_gt hTpos)]
  simpa [EReal.coe_add] using
    rho.petzRenyiPSDFinite_add_log_inv_epsilon_le_hypothesisTestingRelativeEntropy
      sigma hε halpha0 halpha1 hTpos

/-- PSD comparison where the Petz trace positivity is discharged by an
explicit powered support-inclusion hypothesis. -/
theorem petzRenyiPSDFinite_add_log_inv_epsilon_le_hypothesisTestingRelativeEntropy_of_support
    (rho sigma : State a)
    {epsilon alpha : ℝ} (hε : 0 < epsilon)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hSupport :
      Matrix.Supports (CFC.rpow rho.matrix alpha) sigma.matrix) :
    ((rho.petzRenyiPSDFinite sigma alpha halpha0 (ne_of_lt halpha1) +
        alpha / (alpha - 1) * log2 (1 / epsilon) : ℝ) : EReal) ≤
      rho.hypothesisTestingRelativeEntropy sigma epsilon := by
  have hTpos := rho.petzRenyiPSDTraceCoeff_pos_of_support
    sigma hSupport
  exact rho.petzRenyiPSDFinite_add_log_inv_epsilon_le_hypothesisTestingRelativeEntropy
    sigma hε halpha0 halpha1 hTpos

/-- Canonical extended-real PSD comparison under powered support inclusion. -/
theorem petzRenyiPSD_add_log_inv_epsilon_le_hypothesisTestingRelativeEntropy_of_support
    (rho sigma : State a)
    {epsilon alpha : ℝ} (hε : 0 < epsilon)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hSupport : Matrix.Supports (CFC.rpow rho.matrix alpha) sigma.matrix) :
    rho.petzRenyiPSD sigma alpha halpha0 halpha1 +
        ((alpha / (alpha - 1) * log2 (1 / epsilon) : ℝ) : EReal) ≤
      rho.hypothesisTestingRelativeEntropy sigma epsilon :=
  rho.petzRenyiPSD_add_log_inv_epsilon_le_hypothesisTestingRelativeEntropy
    sigma hε halpha0 halpha1
      (rho.petzRenyiPSDTraceCoeff_pos_of_support sigma hSupport)

/-- Khatri--Wilde hypothesis-testing/Petz--Renyi comparison with the
real-valued beta positivity branch discharged from positive definiteness of the
second hypothesis and `ε < 1`. -/
theorem petzRenyi_add_log_inv_epsilon_le_hypothesisTestingRelativeEntropyFinite_of_posDef
    (rho sigma : State a)
    (hρ : rho.matrix.PosDef) (hσ : sigma.matrix.PosDef)
    {epsilon alpha : ℝ} (hε : 0 < epsilon) (hε_lt_one : epsilon < 1)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    rho.petzRenyi sigma hρ hσ alpha halpha0 (ne_of_lt halpha1) +
        alpha / (alpha - 1) * log2 (1 / epsilon) ≤
      rho.hypothesisTestingRelativeEntropyFinite sigma epsilon := by
  obtain ⟨c, hc, hlower⟩ :=
    sigma.exists_pos_scalar_smul_one_le_matrix_of_posDef hσ
  have hβpos :
      0 < rho.hypothesisTestingBeta sigma epsilon :=
    rho.hypothesisTestingBeta_pos_of_matrix_lower_bound sigma epsilon
      (le_of_lt hε) hε_lt_one hc hlower
  exact rho.petzRenyi_add_log_inv_epsilon_le_hypothesisTestingRelativeEntropyFinite
    sigma hρ hσ hε halpha0 halpha1 hβpos

/-- A threshold projector becomes a feasible hypothesis-testing effect once
its type-I accept-probability constraint has been proved. -/
def petzThresholdHypothesisTestingEffect
    (rho sigma : State a) (epsilon lambda : ℝ)
    (haccept :
      1 - epsilon ≤ effectAcceptProbability rho (rho.petzThresholdProjector sigma lambda)) :
    HypothesisTestingEffect rho epsilon where
  effect := rho.petzThresholdProjector sigma lambda
  pos := rho.petzThresholdProjector_posSemidef sigma lambda
  le_one := rho.petzThresholdProjector_le_one sigma lambda
  accept_ge := haccept

@[simp]
theorem petzThresholdHypothesisTestingEffect_effect
    (rho sigma : State a) (epsilon lambda : ℝ)
    (haccept :
      1 - epsilon ≤ effectAcceptProbability rho (rho.petzThresholdProjector sigma lambda)) :
    (rho.petzThresholdHypothesisTestingEffect sigma epsilon lambda haccept).effect =
      rho.petzThresholdProjector sigma lambda :=
  rfl

@[simp]
theorem petzThresholdHypothesisTestingEffect_typeIIError
    (rho sigma : State a) (epsilon lambda : ℝ)
    (haccept :
      1 - epsilon ≤ effectAcceptProbability rho (rho.petzThresholdProjector sigma lambda)) :
    (rho.petzThresholdHypothesisTestingEffect sigma epsilon lambda haccept).typeIIError sigma =
      effectTypeIIError sigma (rho.petzThresholdProjector sigma lambda) :=
  rfl

end State

namespace Channel

variable {b : Type v} [Fintype b] [DecidableEq b]

/-- Input-state version of the Khatri--Wilde hypothesis-testing/Petz
comparison for the barred entanglement-assisted information quantities.

This is the state comparison applied to
`(id_R tensor N)(|psi><psi|)` and its product marginal
`rho_R tensor rho_B`. -/
theorem inputBarPetzRenyi_add_log_inv_epsilon_le_inputBarHypothesisTestingFinite
    (N : Channel a b) (ψ : PureVector (Prod a a))
    (hω : (N.hypothesisTestingOutputState ψ).matrix.PosDef)
    (hR : (N.hypothesisTestingOutputState ψ).marginalA.matrix.PosDef)
    (hB : (N.hypothesisTestingOutputState ψ).marginalB.matrix.PosDef)
    {epsilon alpha : ℝ} (hε : 0 < epsilon)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hβpos :
      0 <
        (N.hypothesisTestingOutputState ψ).hypothesisTestingBeta
          ((N.hypothesisTestingOutputState ψ).marginalA.prod
            (N.hypothesisTestingOutputState ψ).marginalB)
          epsilon) :
    N.inputBarPetzRenyiMutualInformation ψ hω hR hB
        alpha halpha0 (ne_of_lt halpha1) +
        alpha / (alpha - 1) * log2 (1 / epsilon) ≤
      N.inputBarHypothesisTestingMutualInformationFinite ψ epsilon := by
  unfold inputBarPetzRenyiMutualInformation State.barPetzRenyiMutualInformation
    inputBarHypothesisTestingMutualInformationFinite State.barHypothesisTestingMutualInformationFinite
  exact (N.hypothesisTestingOutputState ψ).petzRenyi_add_log_inv_epsilon_le_hypothesisTestingRelativeEntropyFinite
    ((N.hypothesisTestingOutputState ψ).marginalA.prod
      (N.hypothesisTestingOutputState ψ).marginalB)
    hω (State.prod_posDef hR hB) hε halpha0 halpha1 hβpos

/-- Input-state barred comparison with beta positivity discharged by positive
definiteness and `ε < 1`. -/
theorem inputBarPetzRenyi_add_log_inv_epsilon_le_inputBarHypothesisTestingFinite_of_posDef
    (N : Channel a b) (ψ : PureVector (Prod a a))
    (hω : (N.hypothesisTestingOutputState ψ).matrix.PosDef)
    (hR : (N.hypothesisTestingOutputState ψ).marginalA.matrix.PosDef)
    (hB : (N.hypothesisTestingOutputState ψ).marginalB.matrix.PosDef)
    {epsilon alpha : ℝ} (hε : 0 < epsilon) (hε_lt_one : epsilon < 1)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    N.inputBarPetzRenyiMutualInformation ψ hω hR hB
        alpha halpha0 (ne_of_lt halpha1) +
        alpha / (alpha - 1) * log2 (1 / epsilon) ≤
      N.inputBarHypothesisTestingMutualInformationFinite ψ epsilon := by
  unfold inputBarPetzRenyiMutualInformation State.barPetzRenyiMutualInformation
    inputBarHypothesisTestingMutualInformationFinite State.barHypothesisTestingMutualInformationFinite
  exact (N.hypothesisTestingOutputState ψ).petzRenyi_add_log_inv_epsilon_le_hypothesisTestingRelativeEntropyFinite_of_posDef
    ((N.hypothesisTestingOutputState ψ).marginalA.prod
      (N.hypothesisTestingOutputState ψ).marginalB)
    hω (State.prod_posDef hR hB) hε hε_lt_one halpha0 halpha1

/-- Input-state barred comparison in the PSD `0 < alpha < 1` branch.  The
trace-positivity hypothesis is the remaining support condition for the
barred state/product-marginal pair. -/
theorem inputBarPetzRenyiPSDFinite_add_log_inv_epsilon_le_inputBarHypothesisTesting_of_trace_pos
    (N : Channel a b) (ψ : PureVector (Prod a a))
    {epsilon alpha : ℝ} (hε : 0 < epsilon)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hTpos :
      0 <
        ((CFC.rpow (N.hypothesisTestingOutputState ψ).matrix alpha *
          CFC.rpow
            ((N.hypothesisTestingOutputState ψ).marginalA.prod
              (N.hypothesisTestingOutputState ψ).marginalB).matrix
            (1 - alpha)).trace).re) :
    ((N.inputBarPetzRenyiMutualInformationPSDFinite ψ
        alpha halpha0 (ne_of_lt halpha1) +
        alpha / (alpha - 1) * log2 (1 / epsilon) : ℝ) : EReal) ≤
      N.inputBarHypothesisTestingMutualInformation ψ epsilon := by
  unfold inputBarPetzRenyiMutualInformationPSDFinite State.barPetzRenyiMutualInformationPSDFinite
    inputBarHypothesisTestingMutualInformation State.barHypothesisTestingMutualInformation
  exact (N.hypothesisTestingOutputState ψ).petzRenyiPSDFinite_add_log_inv_epsilon_le_hypothesisTestingRelativeEntropy
      ((N.hypothesisTestingOutputState ψ).marginalA.prod
        (N.hypothesisTestingOutputState ψ).marginalB)
      hε halpha0 halpha1 hTpos

/-- Input-state PSD barred comparison with trace positivity discharged by a
powered support-inclusion hypothesis. -/
theorem inputBarPetzRenyiPSDFinite_add_log_inv_epsilon_le_inputBarHypothesisTesting_of_support
    (N : Channel a b) (ψ : PureVector (Prod a a))
    {epsilon alpha : ℝ} (hε : 0 < epsilon)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hSupport :
      Matrix.Supports
        (CFC.rpow (N.hypothesisTestingOutputState ψ).matrix alpha)
        ((N.hypothesisTestingOutputState ψ).marginalA.prod
          (N.hypothesisTestingOutputState ψ).marginalB).matrix) :
    ((N.inputBarPetzRenyiMutualInformationPSDFinite ψ
        alpha halpha0 (ne_of_lt halpha1) +
        alpha / (alpha - 1) * log2 (1 / epsilon) : ℝ) : EReal) ≤
      N.inputBarHypothesisTestingMutualInformation ψ epsilon := by
  unfold inputBarPetzRenyiMutualInformationPSDFinite State.barPetzRenyiMutualInformationPSDFinite
    inputBarHypothesisTestingMutualInformation State.barHypothesisTestingMutualInformation
  exact (N.hypothesisTestingOutputState ψ).petzRenyiPSDFinite_add_log_inv_epsilon_le_hypothesisTestingRelativeEntropy_of_support
      ((N.hypothesisTestingOutputState ψ).marginalA.prod
        (N.hypothesisTestingOutputState ψ).marginalB)
      hε halpha0 halpha1 hSupport

/-- Input-state PSD barred comparison for the product-marginal pair.  The
support condition required by the PSD Petz trace argument is automatic for any
bipartite density state: `rho_AB^alpha` is supported on
`rho_A tensor rho_B`. -/
theorem inputBarPetzRenyiPSDFinite_add_log_inv_epsilon_le_inputBarHypothesisTesting
    (N : Channel a b) (ψ : PureVector (Prod a a))
    {epsilon alpha : ℝ} (hε : 0 < epsilon)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    ((N.inputBarPetzRenyiMutualInformationPSDFinite ψ
        alpha halpha0 (ne_of_lt halpha1) +
        alpha / (alpha - 1) * log2 (1 / epsilon) : ℝ) : EReal) ≤
      N.inputBarHypothesisTestingMutualInformation ψ epsilon := by
  exact N.inputBarPetzRenyiPSDFinite_add_log_inv_epsilon_le_inputBarHypothesisTesting_of_support
    ψ hε halpha0 halpha1
    ((N.hypothesisTestingOutputState ψ).rpow_matrix_supports_prod_marginals halpha0)

/-- Canonical extended-real input-state barred Petz comparison. -/
theorem inputBarPetzRenyiPSD_add_log_inv_epsilon_le_inputBarHypothesisTesting
    (N : Channel a b) (ψ : PureVector (Prod a a))
    {epsilon alpha : ℝ} (hε : 0 < epsilon)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    N.inputBarPetzRenyiMutualInformationPSD ψ alpha halpha0 halpha1 +
        ((alpha / (alpha - 1) * log2 (1 / epsilon) : ℝ) : EReal) ≤
      N.inputBarHypothesisTestingMutualInformation ψ epsilon := by
  unfold Channel.inputBarPetzRenyiMutualInformationPSD
    State.barPetzRenyiMutualInformationPSD
    inputBarHypothesisTestingMutualInformation
    State.barHypothesisTestingMutualInformation
  exact State.petzRenyiPSD_add_log_inv_epsilon_le_hypothesisTestingRelativeEntropy_of_support
      (N.hypothesisTestingOutputState ψ)
      ((N.hypothesisTestingOutputState ψ).marginalA.prod
        (N.hypothesisTestingOutputState ψ).marginalB)
      hε halpha0 halpha1
      ((N.hypothesisTestingOutputState ψ).rpow_matrix_supports_prod_marginals halpha0)

/-- Channel-level barred hypothesis-testing/Petz comparison from the
input-state comparison, with the remaining supremum side conditions explicit.

The hypotheses isolate what is not proved by the state comparison itself:
nonemptiness of the current positive-definite Petz value set, boundedness of
the barred hypothesis-testing value set, and positivity of the real-valued
beta quantity for each positive-definite output candidate. -/
theorem barHypothesisTestingFinite_dominates_barPetz_of_input_beta_pos
    (N : Channel a b) {epsilon alpha : ℝ}
    (hε : 0 < epsilon) (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hne :
      (N.barPetzRenyiMutualInformationValueSet alpha halpha0
        (ne_of_lt halpha1)).Nonempty)
    (hbddHT :
      BddAbove (N.barHypothesisTestingMutualInformationFiniteValueSet epsilon))
    (hβpos :
      ∀ (ψ : PureVector (Prod a a))
        (_hω : (N.hypothesisTestingOutputState ψ).matrix.PosDef)
        (_hR : (N.hypothesisTestingOutputState ψ).marginalA.matrix.PosDef)
        (_hB : (N.hypothesisTestingOutputState ψ).marginalB.matrix.PosDef),
        0 <
          (N.hypothesisTestingOutputState ψ).hypothesisTestingBeta
            ((N.hypothesisTestingOutputState ψ).marginalA.prod
              (N.hypothesisTestingOutputState ψ).marginalB)
            epsilon) :
    N.BarHypothesisTestingFiniteDominatesBarPetz epsilon alpha halpha0
      (ne_of_lt halpha1) := by
  unfold BarHypothesisTestingFiniteDominatesBarPetz
  rw [N.barPetzRenyiMutualInformation_eq_sSup,
    N.barHypothesisTestingMutualInformationFinite_eq_sSup]
  have hsSup :
      sSup (N.barPetzRenyiMutualInformationValueSet alpha halpha0
          (ne_of_lt halpha1)) ≤
        sSup (N.barHypothesisTestingMutualInformationFiniteValueSet epsilon) -
          alpha / (alpha - 1) * log2 (1 / epsilon) := by
    refine csSup_le hne ?_
    intro y hy
    rcases hy with ⟨ψ, hω, hR, hB, rfl⟩
    have hinput :=
      N.inputBarPetzRenyi_add_log_inv_epsilon_le_inputBarHypothesisTestingFinite
        ψ hω hR hB hε halpha0 halpha1 (hβpos ψ hω hR hB)
    have hchannel :
        N.inputBarHypothesisTestingMutualInformationFinite ψ epsilon ≤
          sSup (N.barHypothesisTestingMutualInformationFiniteValueSet epsilon) := by
      have hmem :
          N.inputBarHypothesisTestingMutualInformationFinite ψ epsilon ∈
            N.barHypothesisTestingMutualInformationFiniteValueSet epsilon := by
        exact ⟨ψ, rfl⟩
      exact le_csSup hbddHT hmem
    linarith
  linarith

/-- Channel-level barred hypothesis-testing/Petz comparison with beta
positivity discharged from positive-definite output and marginal hypotheses. -/
theorem barHypothesisTestingFinite_dominates_barPetz_of_posDef
    (N : Channel a b) {epsilon alpha : ℝ}
    (hε : 0 < epsilon) (hε_lt_one : epsilon < 1)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hne :
      (N.barPetzRenyiMutualInformationValueSet alpha halpha0
        (ne_of_lt halpha1)).Nonempty)
    (hbddHT :
      BddAbove (N.barHypothesisTestingMutualInformationFiniteValueSet epsilon)) :
    N.BarHypothesisTestingFiniteDominatesBarPetz epsilon alpha halpha0
      (ne_of_lt halpha1) := by
  unfold BarHypothesisTestingFiniteDominatesBarPetz
  rw [N.barPetzRenyiMutualInformation_eq_sSup,
    N.barHypothesisTestingMutualInformationFinite_eq_sSup]
  have hsSup :
      sSup (N.barPetzRenyiMutualInformationValueSet alpha halpha0
          (ne_of_lt halpha1)) ≤
        sSup (N.barHypothesisTestingMutualInformationFiniteValueSet epsilon) -
          alpha / (alpha - 1) * log2 (1 / epsilon) := by
    refine csSup_le hne ?_
    intro y hy
    rcases hy with ⟨ψ, hω, hR, hB, rfl⟩
    have hinput :=
      N.inputBarPetzRenyi_add_log_inv_epsilon_le_inputBarHypothesisTestingFinite_of_posDef
        ψ hω hR hB hε hε_lt_one halpha0 halpha1
    have hchannel :
        N.inputBarHypothesisTestingMutualInformationFinite ψ epsilon ≤
          sSup (N.barHypothesisTestingMutualInformationFiniteValueSet epsilon) := by
      have hmem :
          N.inputBarHypothesisTestingMutualInformationFinite ψ epsilon ∈
            N.barHypothesisTestingMutualInformationFiniteValueSet epsilon := by
        exact ⟨ψ, rfl⟩
      exact le_csSup hbddHT hmem
    linarith
  linarith

/-- Extended-real channel-level barred hypothesis-testing/Petz comparison
with beta positivity discharged from positive-definite output and marginal
hypotheses.

Unlike the real-valued comparison, this version needs no boundedness
hypothesis for the hypothesis-testing value set: the right-hand side is the
source-faithful extended-real barred information. -/
theorem barHypothesisTesting_dominates_barPetz_of_posDef
    (N : Channel a b) {epsilon alpha : ℝ}
    (hε : 0 < epsilon) (hε_lt_one : epsilon < 1)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hne :
      (N.barPetzRenyiMutualInformationValueSet alpha halpha0
        (ne_of_lt halpha1)).Nonempty) :
    N.BarHypothesisTestingDominatesBarPetz epsilon alpha halpha0
      (ne_of_lt halpha1) := by
  unfold BarHypothesisTestingDominatesBarPetz
  rw [N.barPetzRenyiMutualInformation_eq_sSup,
    N.barHypothesisTestingMutualInformation_eq_sSup]
  set c : ℝ := alpha / (alpha - 1) * log2 (1 / epsilon)
  rw [← EReal.ge_of_forall_gt_iff_ge]
  intro z hz
  have hz_real : z < sSup
      (N.barPetzRenyiMutualInformationValueSet alpha halpha0
        (ne_of_lt halpha1)) + c := by
    exact EReal.coe_lt_coe_iff.mp (by simpa [EReal.coe_add, c] using hz)
  have hz_minus :
      z - c <
        sSup (N.barPetzRenyiMutualInformationValueSet alpha halpha0
          (ne_of_lt halpha1)) := by
    linarith
  obtain ⟨y, hy, hygt⟩ := exists_lt_of_lt_csSup hne hz_minus
  rcases hy with ⟨ψ, hω, hR, hB, rfl⟩
  have hinput :=
    N.inputBarPetzRenyi_add_log_inv_epsilon_le_inputBarHypothesisTestingFinite_of_posDef
      ψ hω hR hB hε hε_lt_one halpha0 halpha1
  have hz_le_input :
      z ≤ N.inputBarHypothesisTestingMutualInformationFinite ψ epsilon := by
    dsimp [c] at hz_real hz_minus
    linarith
  exact (EReal.coe_le_coe_iff.mpr hz_le_input).trans
    ((N.inputBarHypothesisTestingMutualInformationFinite_le_E ψ epsilon).trans
      (N.inputBarHypothesisTestingMutualInformation_le_channel epsilon ψ))

/-- Extended-real channel-level barred hypothesis-testing/Petz comparison in
the PSD branch, assuming the Petz trace objective is positive for every input
pure state. -/
theorem barHypothesisTesting_dominates_barPetzPSDFinite_of_trace_pos
    (N : Channel a b) [Nonempty (PureVector (Prod a a))]
    {epsilon alpha : ℝ}
    (hε : 0 < epsilon)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hTpos :
      ∀ ψ : PureVector (Prod a a),
        0 <
          ((CFC.rpow (N.hypothesisTestingOutputState ψ).matrix alpha *
            CFC.rpow
              ((N.hypothesisTestingOutputState ψ).marginalA.prod
                (N.hypothesisTestingOutputState ψ).marginalB).matrix
              (1 - alpha)).trace).re) :
    N.BarHypothesisTestingDominatesBarPetzPSDFinite epsilon alpha halpha0
      (ne_of_lt halpha1) := by
  unfold BarHypothesisTestingDominatesBarPetzPSDFinite
  rw [N.barPetzRenyiMutualInformationPSDFinite_eq_sSup,
    N.barHypothesisTestingMutualInformation_eq_sSup]
  set c : ℝ := alpha / (alpha - 1) * log2 (1 / epsilon)
  rw [← EReal.ge_of_forall_gt_iff_ge]
  intro z hz
  have hne :
      (N.barPetzRenyiMutualInformationPSDFiniteValueSet alpha halpha0
        (ne_of_lt halpha1)).Nonempty := by
    rcases ‹Nonempty (PureVector (Prod a a))› with ⟨ψ⟩
    exact ⟨N.inputBarPetzRenyiMutualInformationPSDFinite ψ alpha halpha0
      (ne_of_lt halpha1), ⟨ψ, rfl⟩⟩
  have hz_real : z < sSup
      (N.barPetzRenyiMutualInformationPSDFiniteValueSet alpha halpha0
        (ne_of_lt halpha1)) + c := by
    exact EReal.coe_lt_coe_iff.mp (by simpa [EReal.coe_add, c] using hz)
  have hz_minus :
      z - c <
        sSup (N.barPetzRenyiMutualInformationPSDFiniteValueSet alpha halpha0
          (ne_of_lt halpha1)) := by
    linarith
  obtain ⟨y, hy, hygt⟩ := exists_lt_of_lt_csSup hne hz_minus
  rcases hy with ⟨ψ, rfl⟩
  have hinput :=
    N.inputBarPetzRenyiPSDFinite_add_log_inv_epsilon_le_inputBarHypothesisTesting_of_trace_pos
      ψ hε halpha0 halpha1 (hTpos ψ)
  have hz_le_input :
      ((z : ℝ) : EReal) ≤
        ((N.inputBarPetzRenyiMutualInformationPSDFinite ψ alpha halpha0
            (ne_of_lt halpha1) + c : ℝ) : EReal) := by
    have hz_real_le :
        z ≤ N.inputBarPetzRenyiMutualInformationPSDFinite ψ alpha halpha0
            (ne_of_lt halpha1) + c := by
      linarith
    exact EReal.coe_le_coe_iff.mpr hz_real_le
  exact hz_le_input.trans (hinput.trans
    (N.inputBarHypothesisTestingMutualInformation_le_channel epsilon ψ))

/-- Canonical extended-real channel-level barred Petz comparison. -/
theorem barHypothesisTesting_dominates_barPetzPSD
    (N : Channel a b) [Nonempty (PureVector (Prod a a))]
    {epsilon alpha : ℝ} (hε : 0 < epsilon)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    N.BarHypothesisTestingDominatesBarPetzPSD
      epsilon alpha halpha0 halpha1 := by
  unfold BarHypothesisTestingDominatesBarPetzPSD
  rw [N.barPetzRenyiMutualInformationPSD_eq_sSup]
  let c : EReal := ((alpha / (alpha - 1) * log2 (1 / epsilon) : ℝ) : EReal)
  rw [← EReal.ge_of_forall_gt_iff_ge]
  intro z hz
  have hz_minus :
      (z : EReal) - c <
        sSup (N.barPetzRenyiMutualInformationPSDValueSet
          alpha halpha0 halpha1) := by
    exact (EReal.sub_lt_iff (by simp [c]) (by simp [c])).2 hz
  obtain ⟨value, hvalue, hgt⟩ := lt_sSup_iff.mp hz_minus
  rcases hvalue with ⟨ψ, rfl⟩
  have hc_ne_bot : c ≠ (⊥ : EReal) := by
    change ((alpha / (alpha - 1) * log2 (1 / epsilon) : ℝ) : EReal) ≠ ⊥
    exact EReal.coe_ne_bot _
  have hc_ne_top : c ≠ (⊤ : EReal) := by
    change ((alpha / (alpha - 1) * log2 (1 / epsilon) : ℝ) : EReal) ≠ ⊤
    exact EReal.coe_ne_top _
  have hz_le :
      (z : EReal) ≤
        N.inputBarPetzRenyiMutualInformationPSD ψ alpha halpha0 halpha1 + c := by
    exact (EReal.sub_le_iff_le_add
      (Or.inl hc_ne_bot) (Or.inl hc_ne_top)).1 hgt.le
  exact hz_le.trans
    ((N.inputBarPetzRenyiPSD_add_log_inv_epsilon_le_inputBarHypothesisTesting
      ψ hε halpha0 halpha1).trans
        (N.inputBarHypothesisTestingMutualInformation_le_channel epsilon ψ))

/-- Extended-real channel-level barred hypothesis-testing/Petz comparison in
the PSD branch, assuming powered support inclusion for every input pure state. -/
theorem barHypothesisTesting_dominates_barPetzPSDFinite_of_support
    (N : Channel a b) [Nonempty (PureVector (Prod a a))]
    {epsilon alpha : ℝ}
    (hε : 0 < epsilon)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hSupport :
      ∀ ψ : PureVector (Prod a a),
        Matrix.Supports
          (CFC.rpow (N.hypothesisTestingOutputState ψ).matrix alpha)
          ((N.hypothesisTestingOutputState ψ).marginalA.prod
            (N.hypothesisTestingOutputState ψ).marginalB).matrix) :
    N.BarHypothesisTestingDominatesBarPetzPSDFinite epsilon alpha halpha0
      (ne_of_lt halpha1) := by
  refine N.barHypothesisTesting_dominates_barPetzPSDFinite_of_trace_pos
    hε halpha0 halpha1 ?_
  intro ψ
  have hMne : CFC.rpow (N.hypothesisTestingOutputState ψ).matrix alpha ≠ 0 := by
    have hρne : (N.hypothesisTestingOutputState ψ).matrix ≠ 0 := by
      intro hzero
      have htrace := (N.hypothesisTestingOutputState ψ).trace_eq_one
      rw [hzero] at htrace
      simp at htrace
    have hpow_pos :=
      psdTracePower_pos_of_ne_zero
        (N.hypothesisTestingOutputState ψ).matrix
        (N.hypothesisTestingOutputState ψ).pos
        (p := alpha) hρne
    intro hzero
    have hpow_zero :
        psdTracePower (N.hypothesisTestingOutputState ψ).matrix
          (N.hypothesisTestingOutputState ψ).pos alpha = 0 := by
      change (CFC.rpow (N.hypothesisTestingOutputState ψ).matrix alpha).trace.re = 0
      rw [hzero]
      simp
    linarith
  exact trace_mul_cMatrix_rpow_pos_of_support
    (M := CFC.rpow (N.hypothesisTestingOutputState ψ).matrix alpha)
    (N := ((N.hypothesisTestingOutputState ψ).marginalA.prod
      (N.hypothesisTestingOutputState ψ).marginalB).matrix)
    (cMatrix_rpow_posSemidef
      (A := (N.hypothesisTestingOutputState ψ).matrix) (s := alpha)
      (N.hypothesisTestingOutputState ψ).pos)
    ((N.hypothesisTestingOutputState ψ).marginalA.prod
      (N.hypothesisTestingOutputState ψ).marginalB).pos
    hMne (hSupport ψ) (1 - alpha)

/-- Petz--Renyi one-shot lower bound obtained by combining the
hypothesis-testing one-shot lower bound with the proved threshold/Audenaert
comparison route.

This removes the explicit `BarHypothesisTestingFiniteDominatesBarPetz` hypothesis
from the public Petz lower-bound bridge.  The remaining side conditions are
exactly those still required by the current real-valued, positive-definite
Petz and hypothesis-testing APIs: nonempty positive-definite Petz candidates,
bounded barred hypothesis-testing values, and positivity of the beta branch
for positive-definite output candidates.
-/
theorem oneShotEntanglementAssistedClassicalCapacityE_petzLowerBound_of_input_beta_pos
    (N : Channel a b) {ε η α : ℝ}
    (hεη : 0 < ε - η) (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hHT :
      ((N.barHypothesisTestingMutualInformationFinite (ε - η) -
          log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
        N.oneShotEntanglementAssistedClassicalCapacityE ε)
    (hne :
      (N.barPetzRenyiMutualInformationValueSet α hα_pos
        (ne_of_lt hα_lt_one)).Nonempty)
    (hbddHT :
      BddAbove (N.barHypothesisTestingMutualInformationFiniteValueSet (ε - η)))
    (hβpos :
      ∀ (ψ : PureVector (Prod a a))
        (_hω : (N.hypothesisTestingOutputState ψ).matrix.PosDef)
        (_hR : (N.hypothesisTestingOutputState ψ).marginalA.matrix.PosDef)
        (_hB : (N.hypothesisTestingOutputState ψ).marginalB.matrix.PosDef),
        0 <
          (N.hypothesisTestingOutputState ψ).hypothesisTestingBeta
            ((N.hypothesisTestingOutputState ψ).marginalA.prod
              (N.hypothesisTestingOutputState ψ).marginalB)
            (ε - η)) :
    ((N.barPetzRenyiMutualInformation α hα_pos (ne_of_lt hα_lt_one) -
        α / (1 - α) * log2 (1 / (ε - η)) -
        log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  exact N.oneShotEntanglementAssistedClassicalCapacityE_petzLowerBound_of_comparison
    hα_pos hα_lt_one hHT
    (N.barHypothesisTestingFinite_dominates_barPetz_of_input_beta_pos
      hεη hα_pos hα_lt_one hne hbddHT hβpos)

/-- Petz--Renyi one-shot lower bound from the hypothesis-testing lower bound
and the proved threshold/Audenaert comparison route, with beta positivity
discharged by positive definiteness and `ε - η < 1`. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_petzLowerBound_of_posDef
    (N : Channel a b) {ε η α : ℝ}
    (hεη : 0 < ε - η) (hεη_lt_one : ε - η < 1)
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hHT :
      ((N.barHypothesisTestingMutualInformationFinite (ε - η) -
          log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
        N.oneShotEntanglementAssistedClassicalCapacityE ε)
    (hne :
      (N.barPetzRenyiMutualInformationValueSet α hα_pos
        (ne_of_lt hα_lt_one)).Nonempty)
    (hbddHT :
      BddAbove (N.barHypothesisTestingMutualInformationFiniteValueSet (ε - η))) :
    ((N.barPetzRenyiMutualInformation α hα_pos (ne_of_lt hα_lt_one) -
        α / (1 - α) * log2 (1 / (ε - η)) -
        log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  exact N.oneShotEntanglementAssistedClassicalCapacityE_petzLowerBound_of_comparison
    hα_pos hα_lt_one hHT
    (N.barHypothesisTestingFinite_dominates_barPetz_of_posDef
      hεη hεη_lt_one hα_pos hα_lt_one hne hbddHT)

/-- Khatri--Wilde one-shot Petz--Renyi lower bound obtained by combining the
source-faithful hypothesis-testing lower bound with the proved
threshold/Audenaert comparison route.

This theorem removes the explicit hypothesis-testing lower-bound and
beta-positivity hypotheses from the Petz bridge.  The remaining side
conditions are exactly the current positive-definite Petz API and the
real-valued channel-supremum boundedness side condition. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_petzLowerBound
    (N : Channel a b) [Nonempty a] {ε η α : ℝ}
    (hε_pos : 0 < ε) (hη_pos : 0 < η) (hη_lt : η < ε)
    (hεη_lt_one : ε - η < 1)
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hne :
      (N.barPetzRenyiMutualInformationValueSet α hα_pos
        (ne_of_lt hα_lt_one)).Nonempty) :
    ((N.barPetzRenyiMutualInformation α hα_pos (ne_of_lt hα_lt_one) -
        α / (1 - α) * log2 (1 / (ε - η)) -
        log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  haveI : Nonempty (PureVector (Prod a a)) :=
    ⟨PureVector.basisPureVector⟩
  have hεη : 0 < ε - η := sub_pos.mpr hη_lt
  exact N.oneShotEntanglementAssistedClassicalCapacityE_petzLowerBound_of_comparison_EReal
    hα_pos hα_lt_one
    (N.oneShotEntanglementAssistedClassicalCapacityE_htLowerBound
      hε_pos hη_pos hη_lt)
    (N.barHypothesisTesting_dominates_barPetz_of_posDef
      hεη hεη_lt_one hα_pos hα_lt_one hne)

/-- PSD-domain Khatri--Wilde one-shot Petz--Renyi lower bound, reduced to the
barred-product-marginal trace-positivity condition. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_petzPSDFiniteLowerBound_of_trace_pos
    (N : Channel a b) [Nonempty a] {ε η α : ℝ}
    (hε_pos : 0 < ε) (hη_pos : 0 < η) (hη_lt : η < ε)
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hTpos :
      ∀ ψ : PureVector (Prod a a),
        0 <
          ((CFC.rpow (N.hypothesisTestingOutputState ψ).matrix α *
            CFC.rpow
              ((N.hypothesisTestingOutputState ψ).marginalA.prod
                (N.hypothesisTestingOutputState ψ).marginalB).matrix
              (1 - α)).trace).re) :
    ((N.barPetzRenyiMutualInformationPSDFinite α hα_pos (ne_of_lt hα_lt_one) -
        α / (1 - α) * log2 (1 / (ε - η)) -
        log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  haveI : Nonempty (PureVector (Prod a a)) :=
    ⟨PureVector.basisPureVector⟩
  have hεη : 0 < ε - η := sub_pos.mpr hη_lt
  exact N.oneShotEntanglementAssistedClassicalCapacityE_petzPSDFiniteLowerBound_of_comparison_EReal
    hα_pos hα_lt_one
    (N.oneShotEntanglementAssistedClassicalCapacityE_htLowerBound
      hε_pos hη_pos hη_lt)
    (N.barHypothesisTesting_dominates_barPetzPSDFinite_of_trace_pos
      hεη hα_pos hα_lt_one hTpos)

/-- PSD-domain Khatri--Wilde one-shot Petz--Renyi lower bound, reduced to the
finite-dimensional support condition `rho_AB^alpha << rho_A tensor rho_B` for
each pure input. This is the support-sensitive form of the source theorem. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_petzPSDFiniteLowerBound_of_support
    (N : Channel a b) [Nonempty a] {ε η α : ℝ}
    (hε_pos : 0 < ε) (hη_pos : 0 < η) (hη_lt : η < ε)
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hSupport :
      ∀ ψ : PureVector (Prod a a),
        Matrix.Supports
          (CFC.rpow (N.hypothesisTestingOutputState ψ).matrix α)
          ((N.hypothesisTestingOutputState ψ).marginalA.prod
            (N.hypothesisTestingOutputState ψ).marginalB).matrix) :
    ((N.barPetzRenyiMutualInformationPSDFinite α hα_pos (ne_of_lt hα_lt_one) -
        α / (1 - α) * log2 (1 / (ε - η)) -
        log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  haveI : Nonempty (PureVector (Prod a a)) :=
    ⟨PureVector.basisPureVector⟩
  have hεη : 0 < ε - η := sub_pos.mpr hη_lt
  exact N.oneShotEntanglementAssistedClassicalCapacityE_petzPSDFiniteLowerBound_of_comparison_EReal
    hα_pos hα_lt_one
    (N.oneShotEntanglementAssistedClassicalCapacityE_htLowerBound
      hε_pos hη_pos hη_lt)
    (N.barHypothesisTesting_dominates_barPetzPSDFinite_of_support
      hεη hα_pos hα_lt_one hSupport)

/-- Khatri--Wilde barred hypothesis-testing/Petz comparison in the PSD
product-marginal domain, with the support condition discharged by the general
bipartite support theorem. -/
theorem barHypothesisTesting_dominates_barPetzPSDFinite
    (N : Channel a b) [Nonempty (PureVector (Prod a a))]
    {epsilon alpha : ℝ}
    (hε : 0 < epsilon)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    N.BarHypothesisTestingDominatesBarPetzPSDFinite epsilon alpha halpha0
      (ne_of_lt halpha1) := by
  unfold BarHypothesisTestingDominatesBarPetzPSDFinite
  rw [N.barPetzRenyiMutualInformationPSDFinite_eq_sSup,
    N.barHypothesisTestingMutualInformation_eq_sSup]
  set c : ℝ := alpha / (alpha - 1) * log2 (1 / epsilon)
  rw [← EReal.ge_of_forall_gt_iff_ge]
  intro z hz
  have hne :
      (N.barPetzRenyiMutualInformationPSDFiniteValueSet alpha halpha0
        (ne_of_lt halpha1)).Nonempty := by
    rcases ‹Nonempty (PureVector (Prod a a))› with ⟨ψ⟩
    exact ⟨N.inputBarPetzRenyiMutualInformationPSDFinite ψ alpha halpha0
      (ne_of_lt halpha1), ⟨ψ, rfl⟩⟩
  have hz_real : z < sSup
      (N.barPetzRenyiMutualInformationPSDFiniteValueSet alpha halpha0
        (ne_of_lt halpha1)) + c := by
    exact EReal.coe_lt_coe_iff.mp (by simpa [EReal.coe_add, c] using hz)
  have hz_minus :
      z - c <
        sSup (N.barPetzRenyiMutualInformationPSDFiniteValueSet alpha halpha0
          (ne_of_lt halpha1)) := by
    linarith
  obtain ⟨y, hy, hygt⟩ := exists_lt_of_lt_csSup hne hz_minus
  rcases hy with ⟨ψ, rfl⟩
  have hinput :=
    N.inputBarPetzRenyiPSDFinite_add_log_inv_epsilon_le_inputBarHypothesisTesting
      ψ hε halpha0 halpha1
  have hz_le_input :
      ((z : ℝ) : EReal) ≤
        ((N.inputBarPetzRenyiMutualInformationPSDFinite ψ alpha halpha0
            (ne_of_lt halpha1) + c : ℝ) : EReal) := by
    have hz_real_le :
        z ≤ N.inputBarPetzRenyiMutualInformationPSDFinite ψ alpha halpha0
            (ne_of_lt halpha1) + c := by
      linarith
    exact EReal.coe_le_coe_iff.mpr hz_real_le
  exact hz_le_input.trans (hinput.trans
    (N.inputBarHypothesisTestingMutualInformation_le_channel epsilon ψ))

/-- Source-shaped strict-rate operational form of the Khatri--Wilde
one-shot Petz--Renyi lower bound in the PSD barred domain.

Any real rate strictly below the Petz--Renyi right-hand side in
`thm-eacc_one_shot_lower_bound` is achieved by an explicit one-shot
entanglement-assisted achievability witness.  The proof follows the source
route: compare the barred Petz quantity to barred hypothesis-testing mutual
information, then invoke the position-based HT construction. -/
theorem exists_oneShotAchievabilityWitness_petzPSDFiniteLowerBound_rate_strict
    (N : Channel a b) [Nonempty a] {ε η α rate : ℝ}
    (hε_pos : 0 < ε) (hη_pos : 0 < η) (hη_lt : η < ε)
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hrate :
      (rate : EReal) <
        ((N.barPetzRenyiMutualInformationPSDFinite α hα_pos (ne_of_lt hα_lt_one) -
          α / (1 - α) * log2 (1 / (ε - η)) -
          log2 (4 * ε / η ^ 2) : ℝ) : EReal)) :
    ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
      ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
        ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
          Nonempty (EntanglementAssistedOneShotAchievabilityWitness N ε rate M EA EB) := by
  haveI : Nonempty (PureVector (Prod a a)) :=
    ⟨PureVector.basisPureVector⟩
  have hεη : 0 < ε - η := sub_pos.mpr hη_lt
  have hcmp :=
    N.barHypothesisTesting_dominates_barPetzPSDFinite
      hεη hα_pos hα_lt_one
  have hα_ne_one : α ≠ 1 := ne_of_lt hα_lt_one
  have hden :
      α / (α - 1) * log2 (1 / (ε - η)) =
        - (α / (1 - α) * log2 (1 / (ε - η))) := by
    have hsub : α - 1 = -(1 - α) := by ring
    rw [hsub]
    field_simp [sub_ne_zero.mpr hα_ne_one.symm]
  have hreal_rate :
      rate + log2 (4 * ε / η ^ 2) <
        N.barPetzRenyiMutualInformationPSDFinite α hα_pos (ne_of_lt hα_lt_one) +
          α / (α - 1) * log2 (1 / (ε - η)) := by
    have hrate_real := EReal.coe_lt_coe_iff.mp hrate
    rw [hden]
    linarith
  have hrate_HT :
      ((rate + log2 (4 * ε / η ^ 2) : ℝ) : EReal) <
        N.barHypothesisTestingMutualInformation (ε - η) := by
    have hrate_E :
        ((rate + log2 (4 * ε / η ^ 2) : ℝ) : EReal) <
          (N.barPetzRenyiMutualInformationPSDFinite α hα_pos (ne_of_lt hα_lt_one) : EReal) +
            ((α / (α - 1) * log2 (1 / (ε - η)) : ℝ) : EReal) := by
      simpa [EReal.coe_add] using EReal.coe_lt_coe_iff.mpr hreal_rate
    exact lt_of_lt_of_le hrate_E hcmp
  exact
    N.exists_oneShotAchievabilityWitness_htLowerBound_rate_strict_E
      hε_pos hη_pos hη_lt hrate_HT

/-- Source-facing strict-rate Petz lower bound using the canonical
extended-real barred PSD quantity. -/
theorem exists_oneShotAchievabilityWitness_petzPSDLowerBound_rate_strict
    (N : Channel a b) [Nonempty a] {ε η α rate : ℝ}
    (hε_pos : 0 < ε) (hη_pos : 0 < η) (hη_lt : η < ε)
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hrate :
      (rate : EReal) <
        N.barPetzRenyiMutualInformationPSD α hα_pos hα_lt_one -
            ((α / (1 - α) * log2 (1 / (ε - η)) : ℝ) : EReal) -
          (log2 (4 * ε / η ^ 2) : EReal)) :
    ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
      ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
        ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
          Nonempty (EntanglementAssistedOneShotAchievabilityWitness N ε rate M EA EB) := by
  haveI : Nonempty (PureVector (Prod a a)) := ⟨PureVector.basisPureVector⟩
  have hεη : 0 < ε - η := sub_pos.mpr hη_lt
  have hcmp := N.barHypothesisTesting_dominates_barPetzPSD
    hεη hα_pos hα_lt_one
  have hα_ne_one : α ≠ 1 := ne_of_lt hα_lt_one
  have hden :
      α / (α - 1) * log2 (1 / (ε - η)) =
        - (α / (1 - α) * log2 (1 / (ε - η))) := by
    have hsub : α - 1 = -(1 - α) := by ring
    rw [hsub]
    field_simp [sub_ne_zero.mpr hα_ne_one.symm]
  have hdenE :
      - (((α / (1 - α) * log2 (1 / (ε - η)) : ℝ) : EReal)) =
        ((α / (α - 1) * log2 (1 / (ε - η)) : ℝ) : EReal) := by
    rw [← EReal.coe_neg, ← hden]
  have hshift :
      (rate : EReal) + (log2 (4 * ε / η ^ 2) : EReal) <
        N.barPetzRenyiMutualInformationPSD α hα_pos hα_lt_one +
          ((α / (α - 1) * log2 (1 / (ε - η)) : ℝ) : EReal) := by
    have h := EReal.add_lt_of_lt_sub hrate
    rw [sub_eq_add_neg, hdenE] at h
    exact h
  have hrate_HT :
      ((rate + log2 (4 * ε / η ^ 2) : ℝ) : EReal) <
        N.barHypothesisTestingMutualInformation (ε - η) := by
    simpa [EReal.coe_add] using lt_of_lt_of_le hshift hcmp
  exact N.exists_oneShotAchievabilityWitness_htLowerBound_rate_strict_E
    hε_pos hη_pos hη_lt hrate_HT

/-- Source-shaped PSD-domain Khatri--Wilde one-shot Petz--Renyi lower bound
with no positive-definite input assumption. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_petzPSDFiniteLowerBound
    (N : Channel a b) [Nonempty a] {ε η α : ℝ}
    (hε_pos : 0 < ε) (hη_pos : 0 < η) (hη_lt : η < ε)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    ((N.barPetzRenyiMutualInformationPSDFinite α hα_pos (ne_of_lt hα_lt_one) -
        α / (1 - α) * log2 (1 / (ε - η)) -
        log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  haveI : Nonempty (PureVector (Prod a a)) :=
    ⟨PureVector.basisPureVector⟩
  have hεη : 0 < ε - η := sub_pos.mpr hη_lt
  exact N.oneShotEntanglementAssistedClassicalCapacityE_petzPSDFiniteLowerBound_of_comparison_EReal
    hα_pos hα_lt_one
    (N.oneShotEntanglementAssistedClassicalCapacityE_htLowerBound
      hε_pos hη_pos hη_lt)
    (N.barHypothesisTesting_dominates_barPetzPSDFinite
      hεη hα_pos hα_lt_one)

/-- Source-facing one-shot lower bound with the canonical extended-real PSD
Petz channel quantity. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_petzPSDLowerBound
    (N : Channel a b) [Nonempty a] {ε η α : ℝ}
    (hε_pos : 0 < ε) (hη_pos : 0 < η) (hη_lt : η < ε)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    N.barPetzRenyiMutualInformationPSD α hα_pos hα_lt_one -
          ((α / (1 - α) * log2 (1 / (ε - η)) : ℝ) : EReal) -
        (log2 (4 * ε / η ^ 2) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  haveI : Nonempty (PureVector (Prod a a)) :=
    ⟨PureVector.basisPureVector⟩
  have hεη : 0 < ε - η := sub_pos.mpr hη_lt
  exact N.oneShotEntanglementAssistedClassicalCapacityE_petzPSDLowerBound_of_comparison_EReal
    hα_pos hα_lt_one
    (N.oneShotEntanglementAssistedClassicalCapacityE_htLowerBound
      hε_pos hη_pos hη_lt)
    (N.barHypothesisTesting_dominates_barPetzPSD
      hεη hα_pos hα_lt_one)

/-- Khatri--Wilde one-shot lower bounds for entanglement-assisted classical
communication.

The first component is the hypothesis-testing lower bound
`C_EA^epsilon(N) >= bar I_H^(epsilon-eta)(N) - log2(4 epsilon / eta^2)`.
The second component is the Petz--Renyi lower bound obtained from the
source comparison, in the PSD-domain `0 < alpha < 1` branch with no
positive-definite input assumption. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_lowerBoundsFinite
    (N : Channel a b) [Nonempty a] {ε η α : ℝ}
    (hε_pos : 0 < ε) (hη_pos : 0 < η) (hη_lt : η < ε)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    (N.barHypothesisTestingMutualInformation (ε - η) -
        (log2 (4 * ε / η ^ 2) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε) ∧
    (((N.barPetzRenyiMutualInformationPSDFinite α hα_pos (ne_of_lt hα_lt_one) -
        α / (1 - α) * log2 (1 / (ε - η)) -
        log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε) :=
  ⟨N.oneShotEntanglementAssistedClassicalCapacityE_htLowerBound
      hε_pos hη_pos hη_lt,
    N.oneShotEntanglementAssistedClassicalCapacityE_petzPSDFiniteLowerBound
      hε_pos hη_pos hη_lt hα_pos hα_lt_one⟩

/-- Canonical extended-real Khatri--Wilde one-shot lower-bound bundle. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_lowerBounds
    (N : Channel a b) [Nonempty a] {ε η α : ℝ}
    (hε_pos : 0 < ε) (hη_pos : 0 < η) (hη_lt : η < ε)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    (N.barHypothesisTestingMutualInformation (ε - η) -
        (log2 (4 * ε / η ^ 2) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε) ∧
    (N.barPetzRenyiMutualInformationPSD α hα_pos hα_lt_one -
          ((α / (1 - α) * log2 (1 / (ε - η)) : ℝ) : EReal) -
        (log2 (4 * ε / η ^ 2) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε) :=
  ⟨N.oneShotEntanglementAssistedClassicalCapacityE_htLowerBound
      hε_pos hη_pos hη_lt,
    N.oneShotEntanglementAssistedClassicalCapacityE_petzPSDLowerBound
      hε_pos hη_pos hη_lt hα_pos hα_lt_one⟩

/-- Operational and endpoint forms of the Khatri--Wilde one-shot lower
bounds for entanglement-assisted classical communication.

The first and third components are the finite-message source-shaped
operational statements: every rate strictly below the HT or Petz right-hand
side is realized by an explicit one-shot achievability witness.  The second
and fourth components are the endpoint extended-real capacity lower bounds
obtained by supremum closure. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_lowerBoundsFinite_operational
    (N : Channel a b) [Nonempty a] {ε η α : ℝ}
    (hε_pos : 0 < ε) (hη_pos : 0 < η) (hη_lt : η < ε)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    (∀ rate : ℝ,
      (rate : EReal) <
        N.barHypothesisTestingMutualInformation (ε - η) -
          (log2 (4 * ε / η ^ 2) : EReal) →
        ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
          ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
            ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
              Nonempty (EntanglementAssistedOneShotAchievabilityWitness N ε rate M EA EB)) ∧
    (N.barHypothesisTestingMutualInformation (ε - η) -
        (log2 (4 * ε / η ^ 2) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε) ∧
    (∀ rate : ℝ,
      (rate : EReal) <
        ((N.barPetzRenyiMutualInformationPSDFinite α hα_pos (ne_of_lt hα_lt_one) -
          α / (1 - α) * log2 (1 / (ε - η)) -
          log2 (4 * ε / η ^ 2) : ℝ) : EReal) →
        ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
          ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
            ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
              Nonempty (EntanglementAssistedOneShotAchievabilityWitness N ε rate M EA EB)) ∧
    (((N.barPetzRenyiMutualInformationPSDFinite α hα_pos (ne_of_lt hα_lt_one) -
        α / (1 - α) * log2 (1 / (ε - η)) -
        log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε) := by
  have hbounds :=
    N.oneShotEntanglementAssistedClassicalCapacityE_lowerBoundsFinite
      hε_pos hη_pos hη_lt hα_pos hα_lt_one
  refine ⟨?_, hbounds.1, ?_, hbounds.2⟩
  · intro rate hrate
    have hrate_HT :
        ((rate + log2 (4 * ε / η ^ 2) : ℝ) : EReal) <
          N.barHypothesisTestingMutualInformation (ε - η) := by
      have hlt :
          (rate : EReal) + (log2 (4 * ε / η ^ 2) : EReal) <
            N.barHypothesisTestingMutualInformation (ε - η) :=
        EReal.add_lt_of_lt_sub hrate
      simpa [EReal.coe_add] using hlt
    exact
      N.exists_oneShotAchievabilityWitness_htLowerBound_rate_strict_E
        hε_pos hη_pos hη_lt hrate_HT
  · intro rate hrate
    exact
      N.exists_oneShotAchievabilityWitness_petzPSDFiniteLowerBound_rate_strict
        hε_pos hη_pos hη_lt hα_pos hα_lt_one hrate

/-- Canonical operational and endpoint Khatri--Wilde one-shot lower-bound
bundle. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_lowerBounds_operational
    (N : Channel a b) [Nonempty a] {ε η α : ℝ}
    (hε_pos : 0 < ε) (hη_pos : 0 < η) (hη_lt : η < ε)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    (∀ rate : ℝ,
      (rate : EReal) <
        N.barHypothesisTestingMutualInformation (ε - η) -
          (log2 (4 * ε / η ^ 2) : EReal) →
        ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
          ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
            ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
              Nonempty (EntanglementAssistedOneShotAchievabilityWitness N ε rate M EA EB)) ∧
    (N.barHypothesisTestingMutualInformation (ε - η) -
        (log2 (4 * ε / η ^ 2) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε) ∧
    (∀ rate : ℝ,
      (rate : EReal) <
        N.barPetzRenyiMutualInformationPSD α hα_pos hα_lt_one -
            ((α / (1 - α) * log2 (1 / (ε - η)) : ℝ) : EReal) -
          (log2 (4 * ε / η ^ 2) : EReal) →
        ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
          ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
            ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
              Nonempty (EntanglementAssistedOneShotAchievabilityWitness N ε rate M EA EB)) ∧
    (N.barPetzRenyiMutualInformationPSD α hα_pos hα_lt_one -
          ((α / (1 - α) * log2 (1 / (ε - η)) : ℝ) : EReal) -
        (log2 (4 * ε / η ^ 2) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε) := by
  have hbounds := N.oneShotEntanglementAssistedClassicalCapacityE_lowerBounds
    hε_pos hη_pos hη_lt hα_pos hα_lt_one
  refine ⟨?_, hbounds.1, ?_, hbounds.2⟩
  · intro rate hrate
    have hrate_HT :
        ((rate + log2 (4 * ε / η ^ 2) : ℝ) : EReal) <
          N.barHypothesisTestingMutualInformation (ε - η) := by
      have hlt := EReal.add_lt_of_lt_sub hrate
      simpa [EReal.coe_add] using hlt
    exact N.exists_oneShotAchievabilityWitness_htLowerBound_rate_strict_E
      hε_pos hη_pos hη_lt hrate_HT
  · intro rate hrate
    exact N.exists_oneShotAchievabilityWitness_petzPSDLowerBound_rate_strict
      hε_pos hη_pos hη_lt hα_pos hα_lt_one hrate

end Channel

end

end QIT
