/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Additivity.KetBridge
public import QuantumLib.QIT.Information.Entropy.Log2Lemmas

/-!
# MState product branch for sandwiched EA additivity

This module is part of the Khatri--Wilde sandwiched-Renyi additivity proof
spine for entanglement-assisted classical communication.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Pointwise

noncomputable section
universe u1 v1 u2 v2

open QIT

namespace MState

/-- Singular side-information references are outside the finite high-`alpha`
branch when the joint state is full rank.

This is the local support-closure step behind the KW reduction of the
`sigma_B` optimization to the full-rank side-reference domain: if
`rho_AB` is positive definite and `rho_AB` is supported by
`rho_A ⊗ sigma_B`, then `rho_A ⊗ sigma_B` is positive definite, hence
`sigma_B` is positive definite after tracing out `A`. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_top_of_not_side_posDef
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hrho : rhoAB.m.PosDef) (hsigma : ¬ sigmaB.m.PosDef)
    {alphaR : ℝ} (halpha : 1 < alphaR) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alphaR = ⊤ := by
  rw [MState.sandwichedRenyiMutualInformationCandidateE_eq]
  rw [MState.sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha]
  refine MState.sandwichedRenyiPSDReferenceHighAlphaE_eq_top_of_not_supports
    rhoAB (rhoAB.traceRight.prod sigmaB).psd alphaR ?_
  intro hSupport
  have hrefPD : (rhoAB.traceRight.prod sigmaB).m.PosDef :=
    Matrix.Supports.posDef_right_of_left_posDef hrho
      (rhoAB.traceRight.prod sigmaB).psd hSupport
  have : Nonempty a := by
    rcases rhoAB.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  exact hsigma
    (MState.prod_right_posDef_of_posDef rhoAB.traceRight sigmaB hrefPD)

theorem sandwichedRenyiReference_reindex {alpha : Type u1} {beta : Type u2}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (rho : MState alpha) (sigma : CMatrix alpha) (e : alpha ≃ beta)
    (hrho : rho.m.PosDef) (hsigma : sigma.PosDef)
    (alphaR : ℝ) (halpha_pos : 0 < alphaR) (halpha_ne_one : alphaR ≠ 1) :
    sandwichedRenyiReference (rho.reindex e) (Matrix.reindex e e sigma)
        (MState.reindex_posDef rho e hrho)
        (hsigma.submatrix e.symm.injective)
        alphaR halpha_pos halpha_ne_one =
      sandwichedRenyiReference rho sigma hrho hsigma
        alphaR halpha_pos halpha_ne_one := by
  unfold sandwichedRenyiReference
  rw [MState.reindex_matrix]
  let s := (1 - alphaR) / (2 * alphaR)
  change (1 / (alphaR - 1)) *
      log2 (((CFC.rpow
        (CFC.rpow (Matrix.reindex e e sigma) s *
          Matrix.reindex e e rho.m *
          CFC.rpow (Matrix.reindex e e sigma) s) alphaR).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow (CFC.rpow sigma s * rho.m * CFC.rpow sigma s)
        alphaR).trace).re)
  rw [cMatrix_rpow_reindex_posDef e sigma hsigma s]
  change (1 / (alphaR - 1)) *
      log2 (((CFC.rpow
        (((Matrix.reindexAlgEquiv ℂ ℂ e) (CFC.rpow sigma s)) *
          ((Matrix.reindexAlgEquiv ℂ ℂ e) rho.m) *
          ((Matrix.reindexAlgEquiv ℂ ℂ e) (CFC.rpow sigma s))) alphaR).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow (CFC.rpow sigma s * rho.m * CFC.rpow sigma s)
        alphaR).trace).re)
  rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ e)
    (CFC.rpow sigma s) rho.m]
  rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ e)
    (CFC.rpow sigma s * rho.m) (CFC.rpow sigma s)]
  change (1 / (alphaR - 1)) *
      log2 (((CFC.rpow
        (Matrix.reindex e e (CFC.rpow sigma s * rho.m * CFC.rpow sigma s))
        alphaR).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow (CFC.rpow sigma s * rho.m * CFC.rpow sigma s)
        alphaR).trace).re)
  rw [cMatrix_rpow_reindex_posDef e
    (CFC.rpow sigma s * rho.m * CFC.rpow sigma s) ?_ alphaR]
  rw [cMatrix_trace_reindex e]
  have hC : (CFC.rpow sigma s).PosDef := by
    exact cMatrix_rpow_posDef_of_posDef hsigma s
  have hChm : (CFC.rpow sigma s).IsHermitian := by
    exact (cMatrix_rpow_posSemidef (A := sigma) (s := s) hsigma.posSemidef).isHermitian
  have hinner := hrho.mul_mul_conjTranspose_same (B := CFC.rpow sigma s) ?_
  · rwa [hChm.eq] at hinner
  · exact Matrix.vecMul_injective_of_isUnit hC.isUnit

/-- The finite high-`alpha` PSD-reference branch is invariant under finite
reindexing.

This is the support-convention replacement for the older full-rank
`sandwichedRenyiReference_reindex`: KW's product-state proof only repartitions
the tensor factors, so the value of the finite PSD-reference expression should
not depend on the chosen product association. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_reindex
    {alpha : Type u1} {beta : Type u2}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (rho : MState alpha) (sigma : CMatrix alpha) (e : alpha ≃ beta)
    (hsigma : sigma.PosSemidef) (alphaR : ℝ) :
    sandwichedRenyiPSDReferenceHighAlphaFinite (rho.reindex e)
        (Matrix.reindex e e sigma) (hsigma.submatrix e.symm) alphaR =
      sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma alphaR := by
  unfold sandwichedRenyiPSDReferenceHighAlphaFinite sandwichedRenyiReferenceInner
  let s : ℝ := (1 - alphaR) / (2 * alphaR)
  have hpow_sigma :
      CFC.rpow (Matrix.reindex e e sigma) s =
        Matrix.reindex e e (CFC.rpow sigma s) :=
    cMatrix_rpow_reindex_posSemidef e hsigma s
  let inner : CMatrix alpha := CFC.rpow sigma s * rho.m * CFC.rpow sigma s
  have hinner_psd : inner.PosSemidef := by
    simpa [inner, s, MState.sandwichedRenyiReferenceInner] using
      sandwichedRenyiReferenceInner_posSemidef rho hsigma alphaR
  have hinner_reindex :
      CFC.rpow (Matrix.reindex e e sigma) s *
            (rho.reindex e).m *
          CFC.rpow (Matrix.reindex e e sigma) s =
        Matrix.reindex e e inner := by
    rw [hpow_sigma, MState.reindex_matrix]
    change
      (Matrix.reindexAlgEquiv ℂ ℂ e) (CFC.rpow sigma s) *
            (Matrix.reindexAlgEquiv ℂ ℂ e) rho.m *
          (Matrix.reindexAlgEquiv ℂ ℂ e) (CFC.rpow sigma s) =
        (Matrix.reindexAlgEquiv ℂ ℂ e) inner
    rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ e)
      (CFC.rpow sigma s) rho.m]
    rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ e)
      (CFC.rpow sigma s * rho.m) (CFC.rpow sigma s)]
  have hpow_inner :
      CFC.rpow
          (CFC.rpow (Matrix.reindex e e sigma) s *
              (rho.reindex e).m *
            CFC.rpow (Matrix.reindex e e sigma) s)
          alphaR =
        Matrix.reindex e e (CFC.rpow inner alphaR) := by
    rw [hinner_reindex]
    exact cMatrix_rpow_reindex_posSemidef e hinner_psd alphaR
  unfold psdTracePower
  apply congrArg (fun x : ℝ => 1 / (alphaR - 1) * log2 x)
  change
    (CFC.rpow
          (CFC.rpow (Matrix.reindex e e sigma) s *
              (rho.reindex e).m *
            CFC.rpow (Matrix.reindex e e sigma) s)
          alphaR).trace.re =
      (CFC.rpow inner alphaR).trace.re
  rw [hpow_inner]
  rw [cMatrix_trace_reindex e]

/-- MState-reference form of
`sandwichedRenyiPSDReferenceHighAlphaFinite_reindex`.

Keeping the reference as a `MState` packages the PSD witness together with the
matrix equality, avoiding dependent proof-object rewrites when a product
reference is merely repartitioned. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_reindex_stateReference
    {alpha : Type u1} {beta : Type u2}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (rho : MState alpha) (sigma : MState alpha) (e : alpha ≃ beta)
    (alphaR : ℝ) :
    sandwichedRenyiPSDReferenceHighAlphaFinite (rho.reindex e)
        (sigma.reindex e).m (sigma.reindex e).psd alphaR =
      sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma.m sigma.psd alphaR := by
  simpa [MState.reindex_matrix] using
    sandwichedRenyiPSDReferenceHighAlphaFinite_reindex
      (rho := rho) (sigma := sigma.m) (e := e) (hsigma := sigma.psd) alphaR

/-- Support-convention product rule for the sandwiched `Q` functional.

This is the PSD/high-`alpha` algebra hidden in KW
`EA_capacity.tex:1183-1186`: even when references are singular, the
repository support convention for `CFC.rpow` makes the tensor-product trace
factorize. -/
theorem sandwichedRenyiQ_kronecker_posSemidef_support
    {x : Type u1} {y : Type v1} [Fintype x] [DecidableEq x]
    [Fintype y] [DecidableEq y]
    {rho1 sigma1 : CMatrix x} {rho2 sigma2 : CMatrix y}
    (hrho1 : rho1.PosSemidef) (hsigma1 : sigma1.PosSemidef)
    (hrho2 : rho2.PosSemidef) (hsigma2 : sigma2.PosSemidef)
    (alpha : ℝ) :
    MState.sandwichedRenyiQ
        (Matrix.kronecker rho1 rho2)
        (Matrix.kronecker sigma1 sigma2)
        (hrho1.kronecker hrho2) (hsigma1.kronecker hsigma2) alpha =
      MState.sandwichedRenyiQ rho1 sigma1 hrho1 hsigma1 alpha *
        MState.sandwichedRenyiQ rho2 sigma2 hrho2 hsigma2 alpha := by
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let C1 : CMatrix x := CFC.rpow sigma1 s
  let C2 : CMatrix y := CFC.rpow sigma2 s
  let inner1 : CMatrix x := C1 * rho1 * C1
  let inner2 : CMatrix y := C2 * rho2 * C2
  have hC :
      CFC.rpow (Matrix.kronecker sigma1 sigma2) s =
        Matrix.kronecker C1 C2 := by
    simpa [C1, C2, s] using
      cMatrix_rpow_kronecker hsigma1 hsigma2 s
  have hinner :
      CFC.rpow (Matrix.kronecker sigma1 sigma2) s *
          Matrix.kronecker rho1 rho2 *
          CFC.rpow (Matrix.kronecker sigma1 sigma2) s =
        Matrix.kronecker inner1 inner2 := by
    rw [hC]
    simp [inner1, inner2, Matrix.mul_kronecker_mul, Matrix.mul_assoc]
  have hC1_hm : C1.IsHermitian :=
    (cMatrix_rpow_posSemidef (A := sigma1) (s := s) hsigma1).isHermitian
  have hC2_hm : C2.IsHermitian :=
    (cMatrix_rpow_posSemidef (A := sigma2) (s := s) hsigma2).isHermitian
  have hinner1_psd : inner1.PosSemidef := by
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hrho1 C1
    rwa [hC1_hm.eq] at h
  have hinner2_psd : inner2.PosSemidef := by
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hrho2 C2
    rwa [hC2_hm.eq] at h
  have htraceC :
      (CFC.rpow
        (CFC.rpow (Matrix.kronecker sigma1 sigma2) s * Matrix.kronecker rho1 rho2 *
          CFC.rpow (Matrix.kronecker sigma1 sigma2) s) alpha).trace =
        (CFC.rpow inner1 alpha).trace * (CFC.rpow inner2 alpha).trace := by
    rw [hinner]
    rw [cMatrix_rpow_kronecker hinner1_psd hinner2_psd]
    change
      (Matrix.kroneckerMap (fun x y => x * y)
        (CFC.rpow inner1 alpha) (CFC.rpow inner2 alpha)).trace =
        (CFC.rpow inner1 alpha).trace * (CFC.rpow inner2 alpha).trace
    rw [Matrix.trace_kronecker]
  have him1 : ((CFC.rpow inner1 alpha).trace).im = 0 := by
    have htrace_nonneg : 0 ≤ (CFC.rpow inner1 alpha).trace :=
      Matrix.PosSemidef.trace_nonneg
        (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := inner1) (y := alpha)))
    exact htrace_nonneg.2.symm
  have him2 : ((CFC.rpow inner2 alpha).trace).im = 0 := by
    have htrace_nonneg : 0 ≤ (CFC.rpow inner2 alpha).trace :=
      Matrix.PosSemidef.trace_nonneg
        (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := inner2) (y := alpha)))
    exact htrace_nonneg.2.symm
  unfold MState.sandwichedRenyiQ
  change
    (CFC.rpow
      (CFC.rpow (Matrix.kronecker sigma1 sigma2) s * Matrix.kronecker rho1 rho2 *
        CFC.rpow (Matrix.kronecker sigma1 sigma2) s) alpha).trace.re =
      (CFC.rpow inner1 alpha).trace.re * (CFC.rpow inner2 alpha).trace.re
  rw [htraceC, Complex.mul_re, him1, him2]
  ring

/-- Product rule for the supported high-`alpha` finite PSD-reference branch.

This is the finite-branch form of the KW step
`EA_capacity.tex:1183-1186`, where the sandwiched Renyi divergence of product
states against product references splits into the sum of the two divergences.
The hypotheses are support-convention hypotheses, not full-rank assumptions. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_prod_of_supports
    {x : Type u1} {y : Type v1} [Fintype x] [DecidableEq x]
    [Fintype y] [DecidableEq y]
    (rho1 : MState x) (rho2 : MState y)
    {sigma1 : CMatrix x} {sigma2 : CMatrix y}
    (hsigma1 : sigma1.PosSemidef) (hsigma2 : sigma2.PosSemidef)
    (hsupport1 : Matrix.Supports rho1.m sigma1)
    (hsupport2 : Matrix.Supports rho2.m sigma2)
    (alpha : ℝ) :
    MState.sandwichedRenyiPSDReferenceHighAlphaFinite (rho1.prod rho2)
        (Matrix.kronecker sigma1 sigma2) (hsigma1.kronecker hsigma2) alpha =
      MState.sandwichedRenyiPSDReferenceHighAlphaFinite rho1 sigma1 hsigma1 alpha +
        MState.sandwichedRenyiPSDReferenceHighAlphaFinite rho2 sigma2 hsigma2 alpha := by
  have hq :=
    sandwichedRenyiQ_kronecker_posSemidef_support
      (rho1 := rho1.m) (sigma1 := sigma1)
      (rho2 := rho2.m) (sigma2 := sigma2)
      rho1.psd hsigma1 rho2.psd hsigma2 alpha
  have htrace :
      psdTracePower
          (MState.sandwichedRenyiReferenceInner (rho1.prod rho2)
            (Matrix.kronecker sigma1 sigma2) alpha)
          (MState.sandwichedRenyiReferenceInner_posSemidef (rho1.prod rho2)
            (hsigma1.kronecker hsigma2) alpha)
          alpha =
        psdTracePower (MState.sandwichedRenyiReferenceInner rho1 sigma1 alpha)
            (MState.sandwichedRenyiReferenceInner_posSemidef rho1 hsigma1 alpha)
            alpha *
          psdTracePower (MState.sandwichedRenyiReferenceInner rho2 sigma2 alpha)
            (MState.sandwichedRenyiReferenceInner_posSemidef rho2 hsigma2 alpha)
            alpha := by
    simpa [MState.sandwichedRenyiQ, MState.sandwichedRenyiReferenceInner,
      MState.prod_m, psdTracePower] using hq
  have hq1_pos :
      0 <
        psdTracePower (MState.sandwichedRenyiReferenceInner rho1 sigma1 alpha)
          (MState.sandwichedRenyiReferenceInner_posSemidef rho1 hsigma1 alpha) alpha := by
    exact MState.sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports rho1 hsigma1
      hsupport1 alpha
  have hq2_pos :
      0 <
        psdTracePower (MState.sandwichedRenyiReferenceInner rho2 sigma2 alpha)
          (MState.sandwichedRenyiReferenceInner_posSemidef rho2 hsigma2 alpha) alpha := by
    exact MState.sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports rho2 hsigma2
      hsupport2 alpha
  have hqprod_pos :
      0 <
        psdTracePower
          (MState.sandwichedRenyiReferenceInner (rho1.prod rho2)
            (Matrix.kronecker sigma1 sigma2) alpha)
          (MState.sandwichedRenyiReferenceInner_posSemidef (rho1.prod rho2)
            (hsigma1.kronecker hsigma2) alpha)
          alpha := by
    rw [htrace]
    exact mul_pos hq1_pos hq2_pos
  unfold MState.sandwichedRenyiPSDReferenceHighAlphaFinite
  rw [htrace]
  have hlog :
      log2
          (psdTracePower (MState.sandwichedRenyiReferenceInner rho1 sigma1 alpha)
              (MState.sandwichedRenyiReferenceInner_posSemidef rho1 hsigma1 alpha) alpha *
            psdTracePower (MState.sandwichedRenyiReferenceInner rho2 sigma2 alpha)
              (MState.sandwichedRenyiReferenceInner_posSemidef rho2 hsigma2 alpha) alpha) =
        log2
            (psdTracePower (MState.sandwichedRenyiReferenceInner rho1 sigma1 alpha)
              (MState.sandwichedRenyiReferenceInner_posSemidef rho1 hsigma1 alpha) alpha) +
          log2
            (psdTracePower (MState.sandwichedRenyiReferenceInner rho2 sigma2 alpha)
              (MState.sandwichedRenyiReferenceInner_posSemidef rho2 hsigma2 alpha) alpha) := by
    exact log2_mul hq1_pos.ne' hq2_pos.ne'
  rw [hlog]
  ring

/-- Real-valued full-rank candidate for sandwiched-Renyi mutual information.

This is the positive-definite branch of
`MState.sandwichedRenyiMutualInformationCandidateE`, kept as a real-valued
quantity so the KW product `inf` split can use real scalar order lemmas before
the singular-reference closure is proved. -/
def sandwichedRenyiMutualInformationCandidateRealPosDef
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hrho : rhoAB.m.PosDef) (hA : rhoAB.traceRight.m.PosDef)
    (hsigma : sigmaB.m.PosDef) (alphaR : ℝ) (halpha : 1 < alphaR) : ℝ :=
  sandwichedRenyiReference rhoAB (rhoAB.traceRight.prod sigmaB).m
    hrho (MState.PosDef.kron hA hsigma)
    alphaR (lt_trans zero_lt_one halpha) (ne_of_gt halpha)

/-- Full-rank sandwiched mutual-information candidates are nonnegative in the
proved high-`alpha` range. -/
theorem sandwichedRenyiMutualInformationCandidateRealPosDef_nonneg
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hrho : rhoAB.m.PosDef) (hA : rhoAB.traceRight.m.PosDef)
    (hsigma : sigmaB.m.PosDef) {alphaR : ℝ} (halpha : 1 < alphaR) :
    0 ≤ sandwichedRenyiMutualInformationCandidateRealPosDef
      rhoAB sigmaB hrho hA hsigma alphaR halpha := by
  unfold sandwichedRenyiMutualInformationCandidateRealPosDef
  rw [sandwichedRenyiReference_state rhoAB (rhoAB.traceRight.prod sigmaB)
    hrho (MState.PosDef.kron hA hsigma)
    alphaR (lt_trans zero_lt_one halpha) (ne_of_gt halpha)]
  exact sandwichedRenyi_nonneg_of_one_lt rhoAB (rhoAB.traceRight.prod sigmaB)
    hrho (MState.PosDef.kron hA hsigma) alphaR halpha

/-- The full-rank side-reference candidate family is bounded below. -/
theorem sandwichedRenyiMutualInformationCandidateRealPosDef_bddBelow
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rhoAB : MState (a × b))
    (hrho : rhoAB.m.PosDef) (hA : rhoAB.traceRight.m.PosDef)
    {alphaR : ℝ} (halpha : 1 < alphaR) :
    BddBelow (Set.range fun sigmaB : {sigma : MState b // sigma.m.PosDef} =>
      sandwichedRenyiMutualInformationCandidateRealPosDef
        rhoAB sigmaB.1 hrho hA sigmaB.2 alphaR halpha) := by
  refine ⟨0, ?_⟩
  rintro y ⟨sigmaB, rfl⟩
  exact sandwichedRenyiMutualInformationCandidateRealPosDef_nonneg
    rhoAB sigmaB.1 hrho hA sigmaB.2 halpha

/-- The extended-real candidate is the coercion of the real full-rank branch. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_candidateRealPosDef
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hrho : rhoAB.m.PosDef) (hA : rhoAB.traceRight.m.PosDef)
    (hsigma : sigmaB.m.PosDef) {alphaR : ℝ} (halpha : 1 < alphaR) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alphaR =
      (sandwichedRenyiMutualInformationCandidateRealPosDef
        rhoAB sigmaB hrho hA hsigma alphaR halpha : EReal) := by
  unfold sandwichedRenyiMutualInformationCandidateRealPosDef
  exact MState.sandwichedRenyiMutualInformationCandidateE_eq_coe_reference_posDef
    rhoAB sigmaB hrho hA hsigma halpha

/-- The high-`alpha` side-information optimization may be restricted to
full-rank side references when the state and its `A` marginal are full rank.

This packages the KW support convention: singular references contribute
`⊤`, while full-rank references are exactly the real-valued finite branch. -/
theorem sandwichedRenyiMutualInformationE_eq_sInf_fullRankCandidateReal
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (rhoAB : MState (a × b))
    (hrho : rhoAB.m.PosDef) (hA : rhoAB.traceRight.m.PosDef)
    {alphaR : ℝ} (halpha : 1 < alphaR) :
    rhoAB.sandwichedRenyiMutualInformationE alphaR =
      sInf (Set.range fun sigmaB : {sigma : MState b // sigma.m.PosDef} =>
        (sandwichedRenyiMutualInformationCandidateRealPosDef
          rhoAB sigmaB.1 hrho hA sigmaB.2 alphaR halpha : EReal)) := by
  have : Nonempty {sigma : MState b // sigma.m.PosDef} :=
    ⟨⟨(MState.uniform : MState b), MState.uniform_posDef⟩⟩
  rw [MState.sandwichedRenyiMutualInformationE_eq_sInf]
  apply le_antisymm
  · refine le_csInf (Set.range_nonempty _) ?_
    intro y hy
    rcases hy with ⟨sigmaB, rfl⟩
    have hle :=
      sInf_le
      (MState.sandwichedRenyiMutualInformationCandidateE_mem_valueSet rhoAB sigmaB.1 alphaR)
    have heq :=
      sandwichedRenyiMutualInformationCandidateE_eq_coe_candidateRealPosDef
        rhoAB sigmaB.1 hrho hA sigmaB.2 halpha
    simpa [heq] using hle
  · refine le_csInf (rhoAB.sandwichedRenyiMutualInformationEValueSet_nonempty alphaR) ?_
    intro y hy
    rcases hy with ⟨sigmaB, rfl⟩
    by_cases hsigma : sigmaB.m.PosDef
    · have hle :
          sInf (Set.range fun sigmaB : {sigma : MState b // sigma.m.PosDef} =>
            (sandwichedRenyiMutualInformationCandidateRealPosDef
              rhoAB sigmaB.1 hrho hA sigmaB.2 alphaR halpha : EReal)) ≤
            (sandwichedRenyiMutualInformationCandidateRealPosDef
              rhoAB sigmaB hrho hA hsigma alphaR halpha : EReal) :=
        sInf_le ⟨⟨sigmaB, hsigma⟩, rfl⟩
      have heq :=
        sandwichedRenyiMutualInformationCandidateE_eq_coe_candidateRealPosDef
          rhoAB sigmaB hrho hA hsigma halpha
      simpa [heq] using hle
    · have heq :=
        sandwichedRenyiMutualInformationCandidateE_eq_top_of_not_side_posDef
          rhoAB sigmaB hrho hsigma halpha
      simp [heq]

variable {a1 : Type u1} {b1 : Type v1} {a2 : Type u2} {b2 : Type v2}
variable [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
variable [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]

/-- Product of bipartite states, repartitioned as a bipartite state
`(A1 x A2) : (B1 x B2)`. -/
def bipartiteProduct (xi : MState (a1 × b1)) (omega : MState (a2 × b2)) :
    MState ((a1 × a2) × (b1 × b2)) :=
  (xi.prod omega).reindex (Equiv.prodProdProdComm a1 b1 a2 b2)

/-- Positive definiteness is preserved by forming and repartitioning a product
of bipartite states. -/
theorem bipartiteProduct_posDef
    {xi : MState (a1 × b1)} {omega : MState (a2 × b2)}
    (hxi : xi.m.PosDef) (homega : omega.m.PosDef) :
    (xi.bipartiteProduct omega).m.PosDef := by
  unfold bipartiteProduct
  exact MState.reindex_posDef (xi.prod omega) (Equiv.prodProdProdComm a1 b1 a2 b2)
    (MState.PosDef.kron hxi homega)

/-- The left marginal of a repartitioned product bipartite state is the product
of the two left marginals. -/
theorem bipartiteProduct_traceRight
    (xi : MState (a1 × b1)) (omega : MState (a2 × b2)) :
    (xi.bipartiteProduct omega).traceRight = xi.traceRight.prod omega.traceRight := by
  apply MState.ext
  ext x y
  rcases x with ⟨x1, x2⟩
  rcases y with ⟨y1, y2⟩
  simp [bipartiteProduct, Equiv.prodProdProdComm,
    Matrix.traceRight, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]

/-- The right marginal of a repartitioned product bipartite state is the product
of the two right marginals. -/
theorem bipartiteProduct_traceLeft
    (xi : MState (a1 × b1)) (omega : MState (a2 × b2)) :
    (xi.bipartiteProduct omega).traceLeft = xi.traceLeft.prod omega.traceLeft := by
  apply MState.ext
  ext x y
  rcases x with ⟨x1, x2⟩
  rcases y with ⟨y1, y2⟩
  simp [bipartiteProduct, Equiv.prodProdProdComm,
    Matrix.traceLeft, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]

/-- Any bipartite state is supported by its left marginal tensored with a
full-rank right-side state.

This is the support-convention form of the side-information branch in KW
`EA_capacity.tex:1983-1986`: the optimized side state can be full-rank even
when the left marginal of the bipartite state is singular. -/
theorem supports_traceRight_prod_of_side_posDef
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hsigmaB : sigmaB.m.PosDef) :
    Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m := by
  have hside :
      Matrix.Supports (rhoAB.traceRight.prod rhoAB.traceLeft).m
        (rhoAB.traceRight.prod sigmaB).m := by
    simpa using
      Matrix.Supports.kronecker_right_of_posDef
        rhoAB.traceRight.m rhoAB.traceLeft.m sigmaB.m hsigmaB
  exact rhoAB.matrix_supports_prod_marginals.trans hside

/-- Product side-information references repartition in the same way as product
bipartite states. -/
theorem bipartiteProduct_candidateReference
    (xi : MState (a1 × b1)) (omega : MState (a2 × b2))
    (sigma1 : MState b1) (sigma2 : MState b2) :
    (xi.bipartiteProduct omega).traceRight.prod (sigma1.prod sigma2) =
      ((xi.traceRight.prod sigma1).prod (omega.traceRight.prod sigma2)).reindex
        (Equiv.prodProdProdComm a1 b1 a2 b2) := by
  rw [bipartiteProduct_traceRight]
  apply MState.ext
  ext x y
  rcases x with ⟨⟨xA1, xA2⟩, ⟨xB1, xB2⟩⟩
  rcases y with ⟨⟨yA1, yA2⟩, ⟨yB1, yB2⟩⟩
  simp [Equiv.prodProdProdComm, Matrix.kroneckerMap_apply, mul_assoc, mul_left_comm]

/-- Factor support hypotheses imply support for the repartitioned product
candidate reference.

This is the support-convention bridge used in the KW state-product proof:
from
`xi_AB << xi_A ⊗ sigma_B` and `omega_AB << omega_A ⊗ tau_B`, the product state
is supported by the product candidate reference after repartitioning
`(A1B1)(A2B2)` as `(A1A2)(B1B2)`. -/
theorem bipartiteProduct_candidateReference_supports_of_supports
    (xi : MState (a1 × b1)) (omega : MState (a2 × b2))
    (sigma1 : MState b1) (sigma2 : MState b2)
    (hsupport1 :
      Matrix.Supports xi.m (xi.traceRight.prod sigma1).m)
    (hsupport2 :
      Matrix.Supports omega.m (omega.traceRight.prod sigma2).m) :
    Matrix.Supports (xi.bipartiteProduct omega).m
      ((xi.bipartiteProduct omega).traceRight.prod (sigma1.prod sigma2)).m := by
  let ref1 : MState (a1 × b1) := xi.traceRight.prod sigma1
  let ref2 : MState (a2 × b2) := omega.traceRight.prod sigma2
  let e := Equiv.prodProdProdComm a1 b1 a2 b2
  have hraw :
      Matrix.Supports (Matrix.kronecker xi.m omega.m)
        (Matrix.kronecker ref1.m ref2.m) := by
    simpa [ref1, ref2, MState.prod_m] using
      Matrix.Supports.kronecker_of_posSemidef xi.psd ref1.psd omega.psd ref2.psd
        hsupport1 hsupport2
  have hreindex := Matrix.Supports.reindex hraw e
  have hrefState :
      (xi.bipartiteProduct omega).traceRight.prod (sigma1.prod sigma2) =
        (ref1.prod ref2).reindex e := by
    simpa [e, ref1, ref2] using
      MState.bipartiteProduct_candidateReference xi omega sigma1 sigma2
  have hleftMatrix :
      (xi.bipartiteProduct omega).m =
        (Matrix.kronecker xi.m omega.m).submatrix e.symm e.symm := by
    simp [e, MState.bipartiteProduct, MState.reindex_matrix]
  have hrightMatrix :
      ((xi.bipartiteProduct omega).traceRight.prod (sigma1.prod sigma2)).m =
        (Matrix.kronecker ref1.m ref2.m).submatrix e.symm e.symm := by
    rw [hrefState]
    simp [e, MState.reindex_matrix]
  rw [hleftMatrix, hrightMatrix]
  exact hreindex

end MState

namespace Ket

/-- The KW product purification reduces on `A1A2B1B2` to the repartitioned
product of the two `AB` marginals.

This is the finite-dimensional matrix form of the source step in
`EA_capacity.tex:1200-1207` where a product purification of
`xi_{A1B1} ⊗ omega_{A2B2}` is chosen before restricting the `tau` optimization
to product states. -/
theorem bipartiteProductPurification_marginalAB
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (psi : Ket ((a1 × b1) × c1))
    (phi : Ket ((a2 × b2) × c2)) :
    (bipartiteProductPurification psi phi).state.marginalAB =
      psi.state.marginalAB.bipartiteProduct phi.state.marginalAB := by
  apply MState.ext
  ext x y
  rcases x with ⟨⟨i1, i2⟩, ⟨j1, j2⟩⟩
  rcases y with ⟨⟨i1', i2'⟩, ⟨j1', j2'⟩⟩
  simp [bipartiteProductPurification, prodTripartiteZipEquiv,
    Ket.reindex_state, MState.bipartiteProduct, MState.marginalAB,
    Equiv.prodProdProdComm, Matrix.traceRight,
    Matrix.kroneckerMap_apply, Ket.state_matrix, rankOneMatrix_apply,
    Fintype.sum_prod_type, mul_assoc]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro k1 _hk1
  apply Finset.sum_congr rfl
  intro k2 _hk2
  ring

/-- The `A1A2` marginal of the KW product purification is the product of the
two `A` marginals. -/
theorem bipartiteProductPurification_traceRight
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (psi : Ket ((a1 × b1) × c1))
    (phi : Ket ((a2 × b2) × c2)) :
    (bipartiteProductPurification psi phi).state.marginalAB.traceRight =
      psi.state.marginalAB.traceRight.prod phi.state.marginalAB.traceRight := by
  rw [bipartiteProductPurification_marginalAB, MState.bipartiteProduct_traceRight]

/-- The KW `AC` weight factorizes over product input and reference states.

This is the pointwise matrix version of the product factorization used in
`EA_capacity.tex:1201-1208`.  Both the `rho_A` and the `tau_C` exponent go
through the `CFC.rpow` support convention, so neither side needs full rank. -/
theorem sandwichedMutualInformationACWeight_prod
    {a1 c1 a2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype c1] [DecidableEq c1]
    [Fintype a2] [DecidableEq a2] [Fintype c2] [DecidableEq c2]
    (rhoA1 : MState a1) (rhoA2 : MState a2)
    (tauC1 : MState c1) (tauC2 : MState c2)
    (alpha : ℝ) (i1 i1' : a1) (i2 i2' : a2)
    (k1 k1' : c1) (k2 k2' : c2) :
    sandwichedMutualInformationACWeight (rhoA1.prod rhoA2) (tauC1.prod tauC2) alpha
        ((i1, i2), (k1, k2)) ((i1', i2'), (k1', k2')) =
      sandwichedMutualInformationACWeight rhoA1 tauC1 alpha (i1, k1) (i1', k1') *
        sandwichedMutualInformationACWeight rhoA2 tauC2 alpha (i2, k2) (i2', k2') := by
  simp only [sandwichedMutualInformationACWeight]
  rw [MState.prod_m rhoA1 rhoA2]
  rw [MState.prod_m tauC1 tauC2]
  rw [← Matrix.kronecker, ← Matrix.kronecker]
  rw [cMatrix_rpow_kronecker rhoA1.psd rhoA2.psd ((1 - alpha) / alpha)]
  rw [cMatrix_rpow_kronecker tauC1.psd tauC2.psd ((alpha - 1) / alpha)]
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_assoc, mul_left_comm]

/-- Finite-sum factorization used after the KW product `AC` trace entries have
been reduced to componentwise products. -/
private theorem sum_three_mul_sum_three
    {x1 y1 z1 x2 y2 z2 : Type*}
    [Fintype x1] [DecidableEq x1] [Fintype y1] [DecidableEq y1]
    [Fintype z1] [DecidableEq z1] [Fintype x2] [DecidableEq x2]
    [Fintype y2] [DecidableEq y2] [Fintype z2] [DecidableEq z2]
    (f : x1 → y1 → z1 → ℂ) (g : x2 → y2 → z2 → ℂ) :
    (∑ a1, ∑ b1, ∑ c1, f a1 b1 c1) *
        (∑ a2, ∑ b2, ∑ c2, g a2 b2 c2) =
      ∑ a1, ∑ a2, ∑ b1, ∑ b2, ∑ c1, ∑ c2,
        f a1 b1 c1 * g a2 b2 c2 := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl ?_
  intro a1 _ha1
  refine Finset.sum_congr rfl ?_
  intro a2 _ha2
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl ?_
  intro b1 _hb1
  refine Finset.sum_congr rfl ?_
  intro b2 _hb2
  rw [Finset.sum_mul_sum]

/-- For product `A`- and `C`-side weights, the KW `AC` trace matrix of the
product purification factors as the Kronecker product of the component `AC`
trace matrices.

This is the matrix factorization behind the middle equality in
`EA_capacity.tex:1201-1208`, before applying Schatten-norm multiplicativity. -/
theorem sandwichedMutualInformationACTraceMatrix_bipartiteProductPurification_prod
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (rhoA1 : MState a1) (rhoA2 : MState a2)
    (psi : Ket ((a1 × b1) × c1))
    (phi : Ket ((a2 × b2) × c2))
    (tauC1 : MState c1) (tauC2 : MState c2)
    (alpha : ℝ) :
    sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
        (bipartiteProductPurification psi phi) (tauC1.prod tauC2) alpha =
      Matrix.kronecker
        (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha)
        (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha) := by
  ext j j'
  rcases j with ⟨j1, j2⟩
  rcases j' with ⟨j1', j2'⟩
  rw [sandwichedMutualInformationACTraceMatrix_apply]
  change _ =
    sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha j1 j1' *
      sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha j2 j2'
  rw [sandwichedMutualInformationACTraceMatrix_apply]
  rw [sandwichedMutualInformationACTraceMatrix_apply]
  simp_rw [Fintype.sum_prod_type]
  simp only [sandwichedMutualInformationACWeight_prod rhoA1 rhoA2 tauC1 tauC2 alpha,
    bipartiteProductPurification_vec, star_mul]
  ring_nf
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i1 _hi1
  apply Finset.sum_congr rfl
  intro k1 _hk1
  rw [sum_three_mul_sum_three
    (f := fun k i' k' =>
      sandwichedMutualInformationACWeight rhoA1 tauC1 alpha (i1, k) (i', k') *
        psi.vec ((i', j1), k') * star (psi.vec ((i1, j1'), k)))
    (g := fun k i' k' =>
      sandwichedMutualInformationACWeight rhoA2 tauC2 alpha (k1, k) (i', k') *
        phi.vec ((i', j2), k') * star (phi.vec ((k1, j2'), k)))]
  apply Finset.sum_congr rfl
  intro x _hx
  apply Finset.sum_congr rfl
  intro x_1 _hx_1
  apply Finset.sum_congr rfl
  intro x_2 _hx_2
  apply Finset.sum_congr rfl
  intro x_3 _hx_3
  apply Finset.sum_congr rfl
  intro x_4 _hx_4
  apply Finset.sum_congr rfl
  intro x_5 _hx_5
  ring

/-- Schatten-norm multiplicativity for the KW product-purification `AC` trace
matrix.

This is the norm step in `EA_capacity.tex:1208` after the product purification
and product side-information restriction have made the `AC` trace matrix a
Kronecker product. -/
theorem psdSchattenPNorm_ACTraceMatrix_bipartiteProductPurification_prod
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (rhoA1 : MState a1) (rhoA2 : MState a2)
    (psi : Ket ((a1 × b1) × c1))
    (phi : Ket ((a2 × b2) × c2))
    (tauC1 : MState c1) (tauC2 : MState c2)
    {alpha : ℝ} (halpha : 1 < alpha) :
    psdSchattenPNorm
        (sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
          (bipartiteProductPurification psi phi) (tauC1.prod tauC2) alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef
          (rhoA1.prod rhoA2) (bipartiteProductPurification psi phi)
          (tauC1.prod tauC2) alpha)
        (sandwichedAlternateSchattenOrder halpha) =
      psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA1 psi tauC1 alpha)
          (sandwichedAlternateSchattenOrder halpha) *
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA2 phi tauC2 alpha)
          (sandwichedAlternateSchattenOrder halpha) := by
  let matrixProd : CMatrix (b1 × b2) :=
    sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
      (bipartiteProductPurification psi phi) (tauC1.prod tauC2) alpha
  let matrixLeft : CMatrix b1 :=
    sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha
  let matrixRight : CMatrix b2 :=
    sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha
  let hmatrixProd : matrixProd.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef
      (rhoA1.prod rhoA2) (bipartiteProductPurification psi phi)
      (tauC1.prod tauC2) alpha
  let hmatrixLeft : matrixLeft.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef rhoA1 psi tauC1 alpha
  let hmatrixRight : matrixRight.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef rhoA2 phi tauC2 alpha
  have hmat : matrixProd = Matrix.kronecker matrixLeft matrixRight := by
    simpa [matrixProd, matrixLeft, matrixRight] using
      sandwichedMutualInformationACTraceMatrix_bipartiteProductPurification_prod
        rhoA1 rhoA2 psi phi tauC1 tauC2 alpha
  calc
    psdSchattenPNorm matrixProd hmatrixProd (sandwichedAlternateSchattenOrder halpha)
        = psdSchattenPNorm (Matrix.kronecker matrixLeft matrixRight)
            (hmatrixLeft.kronecker hmatrixRight)
            (sandwichedAlternateSchattenOrder halpha) := by
          exact psdSchattenPNorm_congr hmat hmatrixProd
            (hmatrixLeft.kronecker hmatrixRight) (sandwichedAlternateSchattenOrder halpha)
    _ = psdSchattenPNorm matrixLeft hmatrixLeft (sandwichedAlternateSchattenOrder halpha) *
        psdSchattenPNorm matrixRight hmatrixRight (sandwichedAlternateSchattenOrder halpha) := by
          exact psdSchattenPNorm_kronecker hmatrixLeft hmatrixRight
            (sandwichedAlternateSchattenOrder halpha)

/-- Log-additivity for the KW product-purification `AC` trace-matrix norm,
with the logarithm side conditions stated explicitly.

The positivity assumptions are discharged later from the full-rank side weights;
this lemma is only the scalar `log xy = log x + log y` step following
`EA_capacity.tex:1208`. -/
theorem sandwichedACTraceMatrixLog_bipartiteProductPurification_prod_of_pos
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (rhoA1 : MState a1) (rhoA2 : MState a2)
    (psi : Ket ((a1 × b1) × c1))
    (phi : Ket ((a2 × b2) × c2))
    (tauC1 : MState c1) (tauC2 : MState c2)
    {alpha : ℝ} (halpha : 1 < alpha)
    (hM1pos :
      0 <
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA1 psi tauC1 alpha)
          (sandwichedAlternateSchattenOrder halpha))
    (hM2pos :
      0 <
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA2 phi tauC2 alpha)
          (sandwichedAlternateSchattenOrder halpha)) :
    alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
              (bipartiteProductPurification psi phi) (tauC1.prod tauC2) alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              (rhoA1.prod rhoA2) (bipartiteProductPurification psi phi)
              (tauC1.prod tauC2) alpha)
            (sandwichedAlternateSchattenOrder halpha)) =
      alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA1 psi tauC1 alpha)
              (sandwichedAlternateSchattenOrder halpha)) +
        alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA2 phi tauC2 alpha)
              (sandwichedAlternateSchattenOrder halpha)) := by
  rw [psdSchattenPNorm_ACTraceMatrix_bipartiteProductPurification_prod
    rhoA1 rhoA2 psi phi tauC1 tauC2 halpha]
  rw [log2_mul (ne_of_gt hM1pos) (ne_of_gt hM2pos)]
  ring

/-- Log-additivity for the KW product-purification `AC` trace-matrix norm on
the full-rank branch.

This discharges the positivity side conditions in
`sandwichedACTraceMatrixLog_bipartiteProductPurification_prod_of_pos`
from the full-rank `A` and `C` side weights. -/
theorem sandwichedACTraceMatrixLog_bipartiteProductPurification_prod_posDef
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (rhoA1 : MState a1) (rhoA2 : MState a2)
    (psi : Ket ((a1 × b1) × c1))
    (phi : Ket ((a2 × b2) × c2))
    (tauC1 : MState c1) (tauC2 : MState c2)
    (hrhoA1 : rhoA1.m.PosDef) (hrhoA2 : rhoA2.m.PosDef)
    (htauC1 : tauC1.m.PosDef) (htauC2 : tauC2.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
              (bipartiteProductPurification psi phi) (tauC1.prod tauC2) alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              (rhoA1.prod rhoA2) (bipartiteProductPurification psi phi)
              (tauC1.prod tauC2) alpha)
            (sandwichedAlternateSchattenOrder halpha)) =
      alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1 alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA1 psi tauC1 alpha)
              (sandwichedAlternateSchattenOrder halpha)) +
        alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2 alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA2 phi tauC2 alpha)
              (sandwichedAlternateSchattenOrder halpha)) := by
  exact
    sandwichedACTraceMatrixLog_bipartiteProductPurification_prod_of_pos
      rhoA1 rhoA2 psi phi tauC1 tauC2 halpha
      (psdSchattenPNorm_ACTraceMatrix_pos_posDef rhoA1 psi tauC1 hrhoA1 htauC1 halpha)
      (psdSchattenPNorm_ACTraceMatrix_pos_posDef rhoA2 phi tauC2 hrhoA2 htauC2 halpha)

/-- Supremum split for the KW product-purification `AC` trace-matrix
alternate expression on full-rank product purifying references.

This is the product-`tau` optimization step in `EA_capacity.tex:1208-1214`,
after the product purification has reduced the norm to a product and before the
remaining source closure removes the full-rank/product-domain restrictions. -/
theorem sandwichedACTraceMatrixLog_fullRankProduct_sSup_eq_add
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Nonempty c1]
    [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    [Fintype c2] [DecidableEq c2] [Nonempty c2]
    (rhoA1 : MState a1) (rhoA2 : MState a2)
    (psi : Ket ((a1 × b1) × c1))
    (phi : Ket ((a2 × b2) × c2))
    (hrhoA1 : rhoA1.m.PosDef) (hrhoA2 : rhoA2.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha)
    (hBdd1 :
      BddAbove (Set.range fun tauC1 : {tau : MState c1 // tau.m.PosDef} =>
        alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1.1 alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef
                rhoA1 psi tauC1.1 alpha)
              (sandwichedAlternateSchattenOrder halpha))))
    (hBdd2 :
      BddAbove (Set.range fun tauC2 : {tau : MState c2 // tau.m.PosDef} =>
        alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2.1 alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef
                rhoA2 phi tauC2.1 alpha)
              (sandwichedAlternateSchattenOrder halpha)))) :
    sSup (Set.range fun
        p : {tau : MState c1 // tau.m.PosDef} ×
            {tau : MState c2 // tau.m.PosDef} =>
      alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
              (bipartiteProductPurification psi phi) (p.1.1.prod p.2.1) alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              (rhoA1.prod rhoA2) (bipartiteProductPurification psi phi)
              (p.1.1.prod p.2.1) alpha)
            (sandwichedAlternateSchattenOrder halpha))) =
      sSup (Set.range fun tauC1 : {tau : MState c1 // tau.m.PosDef} =>
        alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1.1 alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef
                rhoA1 psi tauC1.1 alpha)
              (sandwichedAlternateSchattenOrder halpha))) +
      sSup (Set.range fun tauC2 : {tau : MState c2 // tau.m.PosDef} =>
        alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2.1 alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef
                rhoA2 phi tauC2.1 alpha)
              (sandwichedAlternateSchattenOrder halpha))) := by
  let S1 := {tau : MState c1 // tau.m.PosDef}
  let S2 := {tau : MState c2 // tau.m.PosDef}
  have : Nonempty S1 := ⟨⟨(MState.uniform : MState c1), MState.uniform_posDef⟩⟩
  have : Nonempty S2 := ⟨⟨(MState.uniform : MState c2), MState.uniform_posDef⟩⟩
  let f : S1 → ℝ := fun tauC1 =>
    alpha / (alpha - 1) *
      log2
        (psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA1 psi tauC1.1 alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA1 psi tauC1.1 alpha)
          (sandwichedAlternateSchattenOrder halpha))
  let g : S2 → ℝ := fun tauC2 =>
    alpha / (alpha - 1) *
      log2
        (psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA2 phi tauC2.1 alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA2 phi tauC2.1 alpha)
          (sandwichedAlternateSchattenOrder halpha))
  have hpoint :
      (fun p : S1 × S2 =>
        alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix (rhoA1.prod rhoA2)
                (bipartiteProductPurification psi phi) (p.1.1.prod p.2.1) alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef
                (rhoA1.prod rhoA2) (bipartiteProductPurification psi phi)
                (p.1.1.prod p.2.1) alpha)
              (sandwichedAlternateSchattenOrder halpha))) =
        (fun p : S1 × S2 => f p.1 + g p.2) := by
    funext p
    exact sandwichedACTraceMatrixLog_bipartiteProductPurification_prod_posDef
      rhoA1 rhoA2 psi phi p.1.1 p.2.1 hrhoA1 hrhoA2 p.1.2 p.2.2 halpha
  rw [hpoint]
  exact real_sSup_range_prod_add_eq_add_sSup_range f g hBdd1 hBdd2

end Ket

namespace MState

variable {a : Type u1} {b : Type v1}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Fixed-candidate Schatten-norm form of the sandwiched mutual-information
definition on the supported PSD-reference branch.

This is the singular-reference version needed by KW's support convention: the
product reference `rho_A \otimes sigma_B` may be singular on the `A` side, but
as long as it supports `rho_AB`, the high-`alpha` branch is finite and the same
Schatten-norm logarithmic formula follows from the PSD-reference definition. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_schattenNorm_of_supports
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hSupport :
      Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m)
    {alpha : ℝ} (halpha : 1 < alpha) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
      (alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedRenyiReferenceInner rhoAB
              (rhoAB.traceRight.prod sigmaB).m alpha)
            (sandwichedRenyiReferenceInner_posSemidef rhoAB
              (rhoAB.traceRight.prod sigmaB).psd alpha)
            (SchattenOrder.ofOneLt halpha)) : EReal) := by
  let ref : CMatrix (a × b) := (rhoAB.traceRight.prod sigmaB).m
  let href : ref.PosSemidef := by
    simpa [ref] using (rhoAB.traceRight.prod sigmaB).psd
  let inner : CMatrix (a × b) := sandwichedRenyiReferenceInner rhoAB ref alpha
  let hinner : inner.PosSemidef :=
    sandwichedRenyiReferenceInner_posSemidef rhoAB href alpha
  have htrace_pos :
      0 < psdTracePower inner hinner alpha := by
    simpa [inner, hinner, ref, href] using
      sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports
        rhoAB href hSupport alpha
  have hlog :
      log2 (psdSchattenPNorm inner hinner (SchattenOrder.ofOneLt halpha)) =
        (1 / alpha) * log2 (psdTracePower inner hinner alpha) := by
    simpa [psdSchattenPNorm, Internal.psdSchattenExpression, inner, hinner] using
      log2_rpow_pos (x := psdTracePower inner hinner alpha) (y := 1 / alpha)
        htrace_pos
  rw [MState.sandwichedRenyiMutualInformationCandidateE_eq]
  rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha]
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
    rhoAB href alpha hSupport]
  change (((1 / (alpha - 1)) * log2 (psdTracePower inner hinner alpha) : ℝ) :
      EReal) =
    (((alpha / (alpha - 1)) *
      log2 (psdSchattenPNorm inner hinner (SchattenOrder.ofOneLt halpha)) : ℝ) :
      EReal)
  rw [hlog]
  congr 1
  field_simp [ne_of_gt (lt_trans zero_lt_one halpha), sub_ne_zero.mpr (ne_of_gt halpha)]

/-- Fixed-candidate Schatten-norm form for a full-rank side state, without
assuming the bipartite state or its left marginal is full rank.

This is the KW support-convention replacement for the older positive-definite
branch: a full-rank `sigma_B` makes `rho_A ⊗ sigma_B` support `rho_AB`, so the
high-`alpha` PSD-reference expression is finite and has the same Schatten-norm
form used in `EA_capacity.tex:1983-1986`. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_schattenNorm_of_side_posDef
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hsigmaB : sigmaB.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
      (alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedRenyiReferenceInner rhoAB
              (rhoAB.traceRight.prod sigmaB).m alpha)
            (sandwichedRenyiReferenceInner_posSemidef rhoAB
              (rhoAB.traceRight.prod sigmaB).psd alpha)
            (SchattenOrder.ofOneLt halpha)) : EReal) := by
  exact sandwichedRenyiMutualInformationCandidateE_eq_coe_schattenNorm_of_supports
    rhoAB sigmaB
      (MState.supports_traceRight_prod_of_side_posDef rhoAB sigmaB hsigmaB) halpha

/-- Full-rank side candidates are exactly the finite PSD-reference branch, with
no full-rank assumption on the bipartite state or its left marginal. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_highAlphaFinite_of_side_posDef
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hsigmaB : sigmaB.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
      (sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
        (rhoAB.traceRight.prod sigmaB).m (rhoAB.traceRight.prod sigmaB).psd alpha :
        EReal) := by
  have hsupport :
      Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m :=
    MState.supports_traceRight_prod_of_side_posDef rhoAB sigmaB hsigmaB
  rw [MState.sandwichedRenyiMutualInformationCandidateE_eq]
  rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha]
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
    rhoAB (rhoAB.traceRight.prod sigmaB).psd alpha hsupport]

/-- Supported state-reference high-`alpha` finite candidates are nonnegative.

This is the support-convention version of the usual nonnegativity of
sandwiched Renyi divergence, obtained by applying the already proved supported
PSD-reference DPI to the terminal measurement channel. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_nonneg_of_state_reference_supports
    (rho sigma : MState a) (hSupport : Matrix.Supports rho.m sigma.m)
    {alpha : ℝ} (halpha : 1 < alpha) :
    0 ≤ sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma.m sigma.psd alpha := by
  let Phi : CPTPMap a PUnit.{1} := terminalMeasureChannel a
  have hDPI :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_dataProcessing_channel_supported
      rho sigma.psd Phi alpha halpha hSupport
  have hrhoPhi : Phi rho = MState.unit := by
    simpa [Phi] using terminalMeasureChannel_applyState rho
  have hsigmaPhiState : Phi sigma = MState.unit := by
    simpa [Phi] using terminalMeasureChannel_applyState sigma
  have hsigmaPhi : Phi.map sigma.m = (1 : CMatrix PUnit.{1}) := by
    have h := congrArg DensityOp.m hsigmaPhiState
    simpa [Phi, CPTPOp.mat_coe_eq_apply_mat, MState.unit] using h
  have hzero :
      sandwichedRenyiPSDReferenceHighAlphaFinite
          (Phi rho) (Phi.map sigma.m)
          (Phi.mapsPositive sigma.m sigma.psd) alpha = 0 := by
    simpa [hrhoPhi, hsigmaPhi] using
      sandwichedRenyiPSDReferenceHighAlphaFinite_unit_one_eq_zero alpha halpha
  linarith

/-- Every high-`alpha` side-information candidate is nonnegative.

On the supported branch this is the usual nonnegativity of sandwiched Renyi
divergence; on the unsupported branch the extended-real candidate is `+∞`.
This is the all-side-state nonnegativity needed to split the KW product
infimum without restricting to full-rank side states. -/
theorem sandwichedRenyiMutualInformationCandidateE_nonneg
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    {alpha : ℝ} (halpha : 1 < alpha) :
    0 ≤ rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha := by
  by_cases hSupport :
      Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m
  · have hfinite :
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
          (MState.sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
            (rhoAB.traceRight.prod sigmaB).m
            (rhoAB.traceRight.prod sigmaB).psd alpha : EReal) := by
      rw [MState.sandwichedRenyiMutualInformationCandidateE_eq]
      rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha]
      rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
        rhoAB (rhoAB.traceRight.prod sigmaB).psd alpha hSupport]
    rw [hfinite]
    exact_mod_cast
      MState.sandwichedRenyiPSDReferenceHighAlphaFinite_nonneg_of_state_reference_supports
        rhoAB (rhoAB.traceRight.prod sigmaB) hSupport halpha
  · rw [MState.sandwichedRenyiMutualInformationCandidateE_eq_top_of_not_supports
      rhoAB sigmaB halpha hSupport]
    exact le_top

/-- Fixed product side-information candidates are additive on the supported
high-`alpha` branch.

This is the support-convention version of KW
`EA_capacity.tex:1177-1186`: no full-rank hypothesis is imposed on the
bipartite states, their left marginals, or the side states.  The hypotheses are
exactly the support-convention branch of the extended sandwiched divergence:
the product reference supports the product state and each factor reference
supports its factor state. -/
theorem sandwichedRenyiMutualInformationCandidateE_bipartiteProduct_prod_of_supports
    {a1 : Type u1} {b1 : Type v1} {a2 : Type u2} {b2 : Type v2}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (xi : MState (a1 × b1)) (omega : MState (a2 × b2))
    (sigma1 : MState b1) (sigma2 : MState b2)
    (hsupportProd :
      Matrix.Supports (xi.bipartiteProduct omega).m
        ((xi.bipartiteProduct omega).traceRight.prod (sigma1.prod sigma2)).m)
    (hsupport1 :
      Matrix.Supports xi.m (xi.traceRight.prod sigma1).m)
    (hsupport2 :
      Matrix.Supports omega.m (omega.traceRight.prod sigma2).m)
    {alphaR : ℝ} (halpha : 1 < alphaR) :
    (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationCandidateE
        (sigma1.prod sigma2) alphaR =
      xi.sandwichedRenyiMutualInformationCandidateE sigma1 alphaR +
        omega.sandwichedRenyiMutualInformationCandidateE sigma2 alphaR := by
  let ref1 : MState (a1 × b1) := xi.traceRight.prod sigma1
  let ref2 : MState (a2 × b2) := omega.traceRight.prod sigma2
  have hleft :
      (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationCandidateE
          (sigma1.prod sigma2) alphaR =
        (MState.sandwichedRenyiPSDReferenceHighAlphaFinite (xi.prod omega)
          (ref1.prod ref2).m (ref1.prod ref2).psd alphaR : EReal) := by
    let e := Equiv.prodProdProdComm a1 b1 a2 b2
    rw [MState.sandwichedRenyiMutualInformationCandidateE_eq]
    rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha]
    rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      (xi.bipartiteProduct omega)
      ((xi.bipartiteProduct omega).traceRight.prod (sigma1.prod sigma2)).psd
      alphaR hsupportProd]
    change
      (MState.sandwichedRenyiPSDReferenceHighAlphaFinite
          ((xi.prod omega).reindex e)
          (((xi.prod omega).reindex e).traceRight.prod (sigma1.prod sigma2)).m
          (((xi.prod omega).reindex e).traceRight.prod (sigma1.prod sigma2)).psd alphaR :
        EReal) =
        (MState.sandwichedRenyiPSDReferenceHighAlphaFinite (xi.prod omega)
          (ref1.prod ref2).m (ref1.prod ref2).psd alphaR : EReal)
    have hrefState :
        ((xi.prod omega).reindex e).traceRight.prod (sigma1.prod sigma2) =
          (ref1.prod ref2).reindex e := by
      simpa [e, MState.bipartiteProduct, ref1, ref2] using
        MState.bipartiteProduct_candidateReference xi omega sigma1 sigma2
    have hfiniteRef :
        MState.sandwichedRenyiPSDReferenceHighAlphaFinite
            ((xi.prod omega).reindex e)
            (((xi.prod omega).reindex e).traceRight.prod (sigma1.prod sigma2)).m
            (((xi.prod omega).reindex e).traceRight.prod (sigma1.prod sigma2)).psd alphaR =
          MState.sandwichedRenyiPSDReferenceHighAlphaFinite
            ((xi.prod omega).reindex e)
            ((ref1.prod ref2).reindex e).m
            ((ref1.prod ref2).reindex e).psd alphaR := by
      exact congrArg
        (fun tau : MState ((a1 × a2) × (b1 × b2)) =>
          MState.sandwichedRenyiPSDReferenceHighAlphaFinite
            ((xi.prod omega).reindex e) tau.m tau.psd alphaR)
        hrefState
    rw [hfiniteRef]
    simpa [e, MState.bipartiteProduct, MState.reindex_matrix, ref1, ref2] using
      congrArg (fun x : ℝ => (x : EReal))
        (MState.sandwichedRenyiPSDReferenceHighAlphaFinite_reindex_stateReference
          (rho := xi.prod omega) (sigma := ref1.prod ref2) (e := e) alphaR)
  have hright1 :
      xi.sandwichedRenyiMutualInformationCandidateE sigma1 alphaR =
        (MState.sandwichedRenyiPSDReferenceHighAlphaFinite xi ref1.m ref1.psd alphaR :
          EReal) := by
    rw [MState.sandwichedRenyiMutualInformationCandidateE_eq]
    rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha]
    rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      xi ref1.psd alphaR hsupport1]
  have hright2 :
      omega.sandwichedRenyiMutualInformationCandidateE sigma2 alphaR =
        (MState.sandwichedRenyiPSDReferenceHighAlphaFinite omega ref2.m ref2.psd alphaR :
          EReal) := by
    rw [MState.sandwichedRenyiMutualInformationCandidateE_eq]
    rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha]
    rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      omega ref2.psd alphaR hsupport2]
  rw [hleft, hright1, hright2]
  have hprodFinite :=
    MState.sandwichedRenyiPSDReferenceHighAlphaFinite_prod_of_supports
      xi omega (sigma1 := ref1.m) (sigma2 := ref2.m)
      ref1.psd ref2.psd hsupport1 hsupport2 alphaR
  rw [← EReal.coe_add]
  exact congrArg (fun x : ℝ => (x : EReal)) (by
    simpa [ref1, ref2, MState.prod_m] using hprodFinite)

/-- Fixed product side-information candidates are additive for full-rank side
states.

This is a corollary of
`sandwichedRenyiMutualInformationCandidateE_bipartiteProduct_prod_of_supports`;
the positive-definite side states only discharge the support-convention
premises. -/
theorem sandwichedRenyiMutualInformationCandidateE_bipartiteProduct_prod
    {a1 : Type u1} {b1 : Type v1} {a2 : Type u2} {b2 : Type v2}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (xi : MState (a1 × b1)) (omega : MState (a2 × b2))
    (sigma1 : MState b1) (sigma2 : MState b2)
    (hsigma1 : sigma1.m.PosDef) (hsigma2 : sigma2.m.PosDef)
    {alphaR : ℝ} (halpha : 1 < alphaR) :
    (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationCandidateE
        (sigma1.prod sigma2) alphaR =
      xi.sandwichedRenyiMutualInformationCandidateE sigma1 alphaR +
        omega.sandwichedRenyiMutualInformationCandidateE sigma2 alphaR := by
  have hsigmaProd : (sigma1.prod sigma2).m.PosDef :=
    MState.PosDef.kron hsigma1 hsigma2
  exact
    MState.sandwichedRenyiMutualInformationCandidateE_bipartiteProduct_prod_of_supports
      xi omega sigma1 sigma2
      (MState.supports_traceRight_prod_of_side_posDef
        (xi.bipartiteProduct omega) (sigma1.prod sigma2) hsigmaProd)
      (by
        simpa using
          MState.supports_traceRight_prod_of_side_posDef xi sigma1 hsigma1)
      (by
        simpa using
          MState.supports_traceRight_prod_of_side_posDef omega sigma2 hsigma2)
      halpha

/-- Product side-information candidates are subadditive for all side states.

This is the pointwise KW product-candidate step without full-rank side-state
restriction.  If both factor support conventions hold, the fixed-candidate
equality applies.  If either factor is unsupported, the right-hand side is
`+∞`, so the inequality is automatic. -/
theorem sandwichedRenyiMutualInformationCandidateE_bipartiteProduct_prod_le
    {a1 : Type u1} {b1 : Type v1} {a2 : Type u2} {b2 : Type v2}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (xi : MState (a1 × b1)) (omega : MState (a2 × b2))
    (sigma1 : MState b1) (sigma2 : MState b2)
    {alphaR : ℝ} (halpha : 1 < alphaR) :
    (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationCandidateE
        (sigma1.prod sigma2) alphaR ≤
      xi.sandwichedRenyiMutualInformationCandidateE sigma1 alphaR +
        omega.sandwichedRenyiMutualInformationCandidateE sigma2 alphaR := by
  by_cases hsupport1 :
      Matrix.Supports xi.m (xi.traceRight.prod sigma1).m
  · by_cases hsupport2 :
        Matrix.Supports omega.m (omega.traceRight.prod sigma2).m
    · have hsupportProd :
          Matrix.Supports (xi.bipartiteProduct omega).m
            ((xi.bipartiteProduct omega).traceRight.prod (sigma1.prod sigma2)).m :=
        MState.bipartiteProduct_candidateReference_supports_of_supports
          xi omega sigma1 sigma2 hsupport1 hsupport2
      rw [MState.sandwichedRenyiMutualInformationCandidateE_bipartiteProduct_prod_of_supports
        xi omega sigma1 sigma2 hsupportProd hsupport1 hsupport2 halpha]
    · rw [MState.sandwichedRenyiMutualInformationCandidateE_eq_top_of_not_supports
        omega sigma2 halpha hsupport2]
      have hxi_ne_bot :
          xi.sandwichedRenyiMutualInformationCandidateE sigma1 alphaR ≠ ⊥ :=
        ne_bot_of_gt (EReal.bot_lt_zero.trans_le
          (MState.sandwichedRenyiMutualInformationCandidateE_nonneg xi sigma1 halpha))
      rw [EReal.add_top_of_ne_bot hxi_ne_bot]
      exact le_top
  · rw [MState.sandwichedRenyiMutualInformationCandidateE_eq_top_of_not_supports
      xi sigma1 halpha hsupport1]
    have homega_ne_bot :
        omega.sandwichedRenyiMutualInformationCandidateE sigma2 alphaR ≠ ⊥ :=
      ne_bot_of_gt (EReal.bot_lt_zero.trans_le
        (MState.sandwichedRenyiMutualInformationCandidateE_nonneg omega sigma2 halpha))
    rw [EReal.top_add_of_ne_bot homega_ne_bot]
    exact le_top

/-- Optimized state sandwiched-Renyi mutual information is subadditive on
bipartite product states, without any full-rank hypothesis on the states.

This is the completed `≤` half of KW `EA_capacity.tex:1177-1191`: restrict the
optimization to product side states, split the fixed-candidate value
pointwise, and separate the independent infimum directly in the extended-real
all-side-state objective. -/
theorem sandwichedRenyiMutualInformationE_bipartiteProduct_le_add
    {a1 : Type u1} {b1 : Type v1} {a2 : Type u2} {b2 : Type v2}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    [Nonempty b1] [Nonempty b2]
    (xi : MState (a1 × b1)) (omega : MState (a2 × b2))
    {alpha : ℝ} (halpha : 1 < alpha) :
    (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationE alpha ≤
      xi.sandwichedRenyiMutualInformationE alpha +
        omega.sandwichedRenyiMutualInformationE alpha := by
  let f : MState b1 → EReal := fun sigma1 =>
    xi.sandwichedRenyiMutualInformationCandidateE sigma1 alpha
  let g : MState b2 → EReal := fun sigma2 =>
    omega.sandwichedRenyiMutualInformationCandidateE sigma2 alpha
  let prodF : MState b1 × MState b2 → EReal := fun p =>
    (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationCandidateE
      (p.1.prod p.2) alpha
  have : Nonempty (MState b1) := ⟨(MState.uniform : MState b1)⟩
  have : Nonempty (MState b2) := ⟨(MState.uniform : MState b2)⟩
  have hfNonneg : ∀ sigma1 : MState b1, 0 ≤ f sigma1 := by
    intro sigma1
    exact MState.sandwichedRenyiMutualInformationCandidateE_nonneg xi sigma1 halpha
  have hgNonneg : ∀ sigma2 : MState b2, 0 ≤ g sigma2 := by
    intro sigma2
    exact MState.sandwichedRenyiMutualInformationCandidateE_nonneg omega sigma2 halpha
  have hleft :
      (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationE alpha ≤
        sInf (Set.range prodF) := by
    refine le_csInf (Set.range_nonempty _) ?_
    rintro y ⟨p, rfl⟩
    exact
      (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationE_le_candidate
        (p.1.prod p.2) alpha
  have hprodToSum :
      sInf (Set.range prodF) ≤
        sInf (Set.range fun p : MState b1 × MState b2 => f p.1 + g p.2) := by
    refine le_csInf (Set.range_nonempty _) ?_
    rintro y ⟨p, rfl⟩
    exact le_trans (sInf_le ⟨p, rfl⟩)
      (MState.sandwichedRenyiMutualInformationCandidateE_bipartiteProduct_prod_le
        xi omega p.1 p.2 halpha)
  have hsplit :
      sInf (Set.range fun p : MState b1 × MState b2 => f p.1 + g p.2) =
        sInf (Set.range f) + sInf (Set.range g) :=
    ereal_sInf_range_prod_add_eq_add_sInf_range_nonneg f g hfNonneg hgNonneg
  have hxi :
      xi.sandwichedRenyiMutualInformationE alpha =
        sInf (Set.range f) := by
    rfl
  have homega :
      omega.sandwichedRenyiMutualInformationE alpha =
        sInf (Set.range g) := by
    rfl
  calc
    (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationE alpha ≤
        sInf (Set.range prodF) := hleft
    _ ≤ sInf (Set.range fun p : MState b1 × MState b2 => f p.1 + g p.2) :=
        hprodToSum
    _ = sInf (Set.range f) + sInf (Set.range g) := hsplit
    _ = xi.sandwichedRenyiMutualInformationE alpha +
          omega.sandwichedRenyiMutualInformationE alpha := by
        rw [hxi, homega]

/-- Fixed-candidate Schatten-norm form of the sandwiched mutual-information
definition when the product reference is positive definite.

This is the support-aware version of the positive-definite branch used in
KW `EA_capacity.tex:1983-1986`: the input state `rhoAB` may be singular, because
the full-rank product reference `rho_A \otimes sigma_B` supports it and the
PSD-reference high-`alpha` branch is finite. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_schattenNorm_of_reference_posDef
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hA : rhoAB.traceRight.m.PosDef)
    (hsigma : sigmaB.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
      (alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedRenyiReferenceInner rhoAB
              (rhoAB.traceRight.prod sigmaB).m alpha)
            (sandwichedRenyiReferenceInner_posSemidef rhoAB
              (MState.PosDef.kron hA hsigma).posSemidef alpha)
            (SchattenOrder.ofOneLt halpha)) : EReal) := by
  let ref : CMatrix (a × b) := (rhoAB.traceRight.prod sigmaB).m
  let hRef : ref.PosDef := by
    simpa [ref] using MState.PosDef.kron hA hsigma
  let inner : CMatrix (a × b) := sandwichedRenyiReferenceInner rhoAB ref alpha
  let hinner : inner.PosSemidef :=
    sandwichedRenyiReferenceInner_posSemidef rhoAB hRef.posSemidef alpha
  have htrace_pos :
      0 < psdTracePower inner hinner alpha := by
    simpa [inner, hinner, ref, hRef] using
      sandwichedRenyiReferenceInner_psdTracePower_pos_of_reference_posDef
        rhoAB hRef alpha
  have hlog :
      log2 (psdSchattenPNorm inner hinner (SchattenOrder.ofOneLt halpha)) =
        (1 / alpha) * log2 (psdTracePower inner hinner alpha) := by
    simpa [psdSchattenPNorm, Internal.psdSchattenExpression, inner, hinner] using
      log2_rpow_pos (x := psdTracePower inner hinner alpha) (y := 1 / alpha)
        htrace_pos
  have hSupport : Matrix.Supports rhoAB.m ref :=
    Matrix.Supports.of_right_posDef rhoAB.m ref hRef
  rw [MState.sandwichedRenyiMutualInformationCandidateE_eq]
  rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha]
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
    rhoAB hRef.posSemidef alpha hSupport]
  change (((1 / (alpha - 1)) * log2 (psdTracePower inner hinner alpha) : ℝ) :
      EReal) =
    (((alpha / (alpha - 1)) *
      log2 (psdSchattenPNorm inner hinner (SchattenOrder.ofOneLt halpha)) : ℝ) :
      EReal)
  rw [hlog]
  congr 1
  field_simp [ne_of_gt (lt_trans zero_lt_one halpha), sub_ne_zero.mpr (ne_of_gt halpha)]

/-- Fixed-candidate Schatten-norm form of the sandwiched mutual-information
definition on the positive-definite branch.

This is the Lean fixed-reference version of
`EA_capacity.tex:1983-1986`, before optimizing over the side-information
state. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_schattenNorm_posDef
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hrho : rhoAB.m.PosDef) (hA : rhoAB.traceRight.m.PosDef)
    (hsigma : sigmaB.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
      (alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedRenyiReferenceInner rhoAB
              (rhoAB.traceRight.prod sigmaB).m alpha)
            (sandwichedRenyiReferenceInner_posSemidef rhoAB
              (MState.PosDef.kron hA hsigma).posSemidef alpha)
            (SchattenOrder.ofOneLt halpha)) : EReal) := by
  let ref : CMatrix (a × b) := (rhoAB.traceRight.prod sigmaB).m
  let inner : CMatrix (a × b) := sandwichedRenyiReferenceInner rhoAB ref alpha
  let hinner : inner.PosSemidef :=
    sandwichedRenyiReferenceInner_posSemidef rhoAB
      (MState.PosDef.kron hA hsigma).posSemidef alpha
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have halpha_ne : alpha ≠ 1 := ne_of_gt halpha
  have htrace_pos :
      0 < psdTracePower inner hinner alpha := by
    simpa [inner, hinner, ref] using
      sandwichedRenyiReferenceInner_psdTracePower_pos rhoAB hrho
        (MState.PosDef.kron hA hsigma) alpha
  have hlog :
      log2 (psdSchattenPNorm inner hinner (SchattenOrder.ofOneLt halpha)) =
        (1 / alpha) * log2 (psdTracePower inner hinner alpha) := by
    simpa [psdSchattenPNorm, Internal.psdSchattenExpression, inner, hinner] using
      log2_rpow_pos (x := psdTracePower inner hinner alpha) (y := 1 / alpha)
        htrace_pos
  rw [MState.sandwichedRenyiMutualInformationCandidateE_eq_coe_reference_posDef
    (rhoAB := rhoAB) (sigmaB := sigmaB) hrho hA hsigma halpha]
  rw [sandwichedRenyiReference_eq_log2_psdTracePower_inner
    rhoAB hrho (MState.PosDef.kron hA hsigma) alpha halpha_pos halpha_ne]
  change (((1 / (alpha - 1)) * log2 (psdTracePower inner hinner alpha) : ℝ) :
      EReal) =
    ((alpha / (alpha - 1)) *
      log2 (psdSchattenPNorm inner hinner (SchattenOrder.ofOneLt halpha)) : ℝ)
  rw [hlog]
  congr 1
  field_simp [ne_of_gt halpha_pos, sub_ne_zero.mpr halpha_ne]

/-- Local-channel data processing for sandwiched mutual information on the
left system.

This is the KW data-processing step used by the purification/isometry bridge:
for each side state `sigmaB`, PSD-reference sandwiched-Renyi DPI compares the
candidate after `Phi ⊗ id` with the original candidate; taking the infimum over
`sigmaB` gives the optimized inequality. -/
theorem sandwichedRenyiMutualInformationE_dataProcessing_left
    {c : Type u2} [Fintype c] [DecidableEq c]
    (rhoAB : MState (a × b)) (Phi : CPTPMap a c)
    {alpha : ℝ} (halpha : 1 < alpha) :
    MState.sandwichedRenyiMutualInformationE
        ((Phi.prod (CPTPOp.id (dIn := b))) rhoAB) alpha ≤
      rhoAB.sandwichedRenyiMutualInformationE alpha := by
  classical
  let rhoOut : MState (c × b) := (Phi.prod (CPTPOp.id (dIn := b))) rhoAB
  have : Nonempty b := by
    rcases rhoAB.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  rw [MState.sandwichedRenyiMutualInformationE_eq_sInf]
  refine le_csInf (rhoAB.sandwichedRenyiMutualInformationEValueSet_nonempty alpha) ?_
  intro y hy
  rcases hy with ⟨sigmaB, rfl⟩
  have hOutLe :
      rhoOut.sandwichedRenyiMutualInformationE alpha ≤
        rhoOut.sandwichedRenyiMutualInformationCandidateE sigmaB alpha :=
    rhoOut.sandwichedRenyiMutualInformationE_le_candidate sigmaB alpha
  have hRefState :
      (Phi.prod (CPTPOp.id (dIn := b))) (rhoAB.traceRight.prod sigmaB) =
        rhoOut.traceRight.prod sigmaB := by
    calc
      (Phi.prod (CPTPOp.id (dIn := b))) (rhoAB.traceRight.prod sigmaB) =
          MState.prod (Phi rhoAB.traceRight) sigmaB := by
            exact MState.applyState_prod_id_prod rhoAB.traceRight sigmaB Phi
      _ = rhoOut.traceRight.prod sigmaB := by
            have hmarg :
                rhoOut.traceRight = Phi rhoAB.traceRight := by
              simpa [rhoOut] using MState.traceRight_applyState_prod_id rhoAB Phi
            rw [hmarg]
  have hRefMap :
      (Phi.prod (CPTPOp.id (dIn := b))).map (rhoAB.traceRight.prod sigmaB).m =
        (rhoOut.traceRight.prod sigmaB).m := by
    rw [← CPTPOp.mat_coe_eq_apply_mat]
    exact congrArg DensityOp.m hRefState
  have hDPI :
      rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha ≥
        rhoOut.sandwichedRenyiMutualInformationCandidateE sigmaB alpha := by
    rw [MState.sandwichedRenyiMutualInformationCandidateE_eq,
      MState.sandwichedRenyiMutualInformationCandidateE_eq]
    have hbase :=
      sandwichedRenyiPSDReferenceE_dataProcessing_channel_ge_of_half_le_lt_one_or_one_lt
        rhoAB (rhoAB.traceRight.prod sigmaB).psd (Phi.prod (CPTPOp.id (dIn := b)))
        alpha (Or.inr halpha)
    simp only [hRefMap] at hbase
    simpa [rhoOut] using hbase
  exact hOutLe.trans hDPI

/-- Local-channel data processing for sandwiched mutual information on the
right system.

This is the right-register counterpart of
`sandwichedRenyiMutualInformationE_dataProcessing_left`.  The side-information
candidate is pushed forward by the channel, matching the product-reference
step in KW's purification/isometry reduction. -/
theorem sandwichedRenyiMutualInformationE_dataProcessing_right
    {c : Type u2} [Fintype c] [DecidableEq c]
    (rhoAB : MState (a × b)) (Psi : CPTPMap b c)
    {alpha : ℝ} (halpha : 1 < alpha) :
    MState.sandwichedRenyiMutualInformationE
        (((CPTPOp.id (dIn := a)).prod Psi) rhoAB) alpha ≤
      rhoAB.sandwichedRenyiMutualInformationE alpha := by
  classical
  let rhoOut : MState (a × c) := ((CPTPOp.id (dIn := a)).prod Psi) rhoAB
  have : Nonempty b := by
    rcases rhoAB.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  rw [MState.sandwichedRenyiMutualInformationE_eq_sInf]
  refine le_csInf (rhoAB.sandwichedRenyiMutualInformationEValueSet_nonempty alpha) ?_
  intro y hy
  rcases hy with ⟨sigmaB, rfl⟩
  let sigmaC : MState c := Psi sigmaB
  have hOutLe :
      rhoOut.sandwichedRenyiMutualInformationE alpha ≤
        rhoOut.sandwichedRenyiMutualInformationCandidateE sigmaC alpha :=
    rhoOut.sandwichedRenyiMutualInformationE_le_candidate sigmaC alpha
  have hRefState :
      ((CPTPOp.id (dIn := a)).prod Psi) (rhoAB.traceRight.prod sigmaB) =
        rhoOut.traceRight.prod sigmaC := by
    calc
      ((CPTPOp.id (dIn := a)).prod Psi) (rhoAB.traceRight.prod sigmaB) =
          rhoAB.traceRight.prod (Psi sigmaB) := by
            exact MState.applyState_id_prod_prod rhoAB.traceRight sigmaB Psi
      _ = rhoOut.traceRight.prod sigmaC := by
            have hmarg :
                rhoOut.traceRight = rhoAB.traceRight := by
              simpa [rhoOut] using MState.traceRight_applyState_id_prod rhoAB Psi
            rw [hmarg]
  have hRefMap :
      ((CPTPOp.id (dIn := a)).prod Psi).map (rhoAB.traceRight.prod sigmaB).m =
        (rhoOut.traceRight.prod sigmaC).m := by
    rw [← CPTPOp.mat_coe_eq_apply_mat]
    exact congrArg DensityOp.m hRefState
  have hDPI :
      rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha ≥
        rhoOut.sandwichedRenyiMutualInformationCandidateE sigmaC alpha := by
    rw [MState.sandwichedRenyiMutualInformationCandidateE_eq,
      MState.sandwichedRenyiMutualInformationCandidateE_eq]
    have hbase :=
      sandwichedRenyiPSDReferenceE_dataProcessing_channel_ge_of_half_le_lt_one_or_one_lt
        rhoAB (rhoAB.traceRight.prod sigmaB).psd ((CPTPOp.id (dIn := a)).prod Psi)
        alpha (Or.inr halpha)
    simp only [hRefMap] at hbase
    simpa [rhoOut, sigmaC] using hbase
  exact hOutLe.trans hDPI

end MState

namespace Ket

/-- Support-convention version of
`traceRight_rankOne_weightedPurificationAmp_eq_referenceInner`.

The matrix identity in KW `EA_capacity.tex:1989-1996` only uses the PSD
functional calculus support convention for the source weight
`rho_A^((1-alpha)/(2 alpha)) \otimes sigma_B^((1-alpha)/(2 alpha))`; it does
not require either factor to be full rank. -/
theorem traceRight_rankOne_weightedPurificationAmp_eq_referenceInner_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : MState b) (ψ : Ket ((a × b) × c)) (alpha : ℝ) :
    Matrix.traceRight
        (rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp
            ψ.state.marginalAB.traceRight σB ψ alpha)) =
      MState.sandwichedRenyiReferenceInner ψ.state.marginalAB
        (ψ.state.marginalAB.traceRight.prod σB).m alpha := by
  let W : CMatrix (a × b) :=
    sandwichedMutualInformationABWeight ψ.state.marginalAB.traceRight σB alpha
  have hW :
      Matrix.conjTranspose W = W := by
    unfold W sandwichedMutualInformationABWeight
    exact (kronecker_isHermitian
      (CFC.rpow ψ.state.marginalAB.traceRight.m ((1 - alpha) / (2 * alpha)))
      (CFC.rpow σB.m ((1 - alpha) / (2 * alpha)))
      (cMatrix_rpow_posSemidef
        (A := ψ.state.marginalAB.traceRight.m)
        (s := (1 - alpha) / (2 * alpha))
        ψ.state.marginalAB.traceRight.psd).isHermitian
      (cMatrix_rpow_posSemidef
        (A := σB.m)
        (s := (1 - alpha) / (2 * alpha))
        σB.psd).isHermitian).eq
  rw [traceRight_rankOne_weightedPurificationAmp_eq]
  unfold MState.sandwichedRenyiReferenceInner
  rw [MState.prod_m ψ.state.marginalAB.traceRight σB]
  change sandwichedMutualInformationABWeight ψ.state.marginalAB.traceRight σB alpha *
      Matrix.traceRight (rankOneMatrix ψ.vec) *
        Matrix.conjTranspose
          (sandwichedMutualInformationABWeight ψ.state.marginalAB.traceRight σB alpha) =
    CFC.rpow (Matrix.kronecker ψ.state.marginalAB.traceRight.m σB.m)
        ((1 - alpha) / (2 * alpha)) *
      ψ.state.marginalAB.m *
      CFC.rpow (Matrix.kronecker ψ.state.marginalAB.traceRight.m σB.m)
        ((1 - alpha) / (2 * alpha))
  rw [cMatrix_rpow_kronecker
    ψ.state.marginalAB.traceRight.psd σB.psd ((1 - alpha) / (2 * alpha))]
  change W * Matrix.traceRight (rankOneMatrix ψ.vec) *
      Matrix.conjTranspose W =
    W * ψ.state.marginalAB.m * W
  rw [hW, MState.marginalAB_eq_traceRight, MState.traceRight_m, Ket.state_matrix]

/-- Support-convention Schatten-norm form of the KW weighted-purification
bridge.

This removes the full-rank assumptions from
`psdSchattenPNorm_referenceInner_eq_weightedPurification_traceLeft`; the
matrix identity itself follows from the PSD support convention for real powers
and the complementary partial-trace Schatten-norm equality. -/
theorem psdSchattenPNorm_referenceInner_eq_weightedPurification_traceLeft_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : MState b) (ψ : Ket ((a × b) × c))
    (alpha : ℝ) {p : ℝ} (hp : 0 < p) :
    psdSchattenPNorm
        (MState.sandwichedRenyiReferenceInner ψ.state.marginalAB
          (ψ.state.marginalAB.traceRight.prod σB).m alpha)
        (MState.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
          (ψ.state.marginalAB.traceRight.prod σB).psd alpha)
        (SchattenOrder.ofPositive hp) =
      psdSchattenPNorm
        (Matrix.traceLeft
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp
              ψ.state.marginalAB.traceRight σB ψ alpha)))
        (traceLeft_posSemidef
          (rankOneMatrix_pos
            (sandwichedMutualInformationWeightedPurificationAmp
              ψ.state.marginalAB.traceRight σB ψ alpha)))
        (SchattenOrder.ofPositive hp) := by
  let amp :=
    sandwichedMutualInformationWeightedPurificationAmp
      ψ.state.marginalAB.traceRight σB ψ alpha
  let hB : (Matrix.traceRight
      (rankOneMatrix amp)).PosSemidef :=
    traceRight_posSemidef (rankOneMatrix_pos amp)
  let hRef :
      (MState.sandwichedRenyiReferenceInner ψ.state.marginalAB
        (ψ.state.marginalAB.traceRight.prod σB).m alpha).PosSemidef :=
    MState.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
      (ψ.state.marginalAB.traceRight.prod σB).psd alpha
  have hmatrix :
      Matrix.traceRight (rankOneMatrix amp) =
        MState.sandwichedRenyiReferenceInner ψ.state.marginalAB
          (ψ.state.marginalAB.traceRight.prod σB).m alpha := by
    simpa [amp] using
      traceRight_rankOne_weightedPurificationAmp_eq_referenceInner_support σB ψ alpha
  have hnormB :
      psdSchattenPNorm (Matrix.traceRight
          (rankOneMatrix amp)) hB (SchattenOrder.ofPositive hp) =
        psdSchattenPNorm
          (MState.sandwichedRenyiReferenceInner ψ.state.marginalAB
            (ψ.state.marginalAB.traceRight.prod σB).m alpha)
          hRef (SchattenOrder.ofPositive hp) :=
    psdSchattenPNorm_congr hmatrix hB hRef (SchattenOrder.ofPositive hp)
  have hBA :
      psdSchattenPNorm (Matrix.traceRight
          (rankOneMatrix amp)) hB (SchattenOrder.ofPositive hp) =
        psdSchattenPNorm
          (Matrix.traceLeft (rankOneMatrix amp))
          (traceLeft_posSemidef (rankOneMatrix_pos amp))
            (SchattenOrder.ofPositive hp) := by
    simpa [amp, hB] using
      psdSchattenPNorm_weightedPurification_partialTraceC_eq_traceLeftB
        ψ.state.marginalAB.traceRight σB ψ alpha hp
  exact hnormB.symm.trans hBA

/-- Fixed-candidate sandwiched mutual information as the Schatten norm of the
`C`-side marginal of the KW weighted purification.

This combines the definition-level positive-reference formula with the
same-nonzero-eigenvalues step in KW `EA_capacity.tex:1983-2004`. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_weightedPurification_traceLeft
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : MState b) (ψ : Ket ((a × b) × c))
    (hAB : ψ.state.marginalAB.m.PosDef)
    (hA : ψ.state.marginalAB.traceRight.m.PosDef)
    (hσ : σB.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationCandidateE σB alpha =
      (alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (Matrix.traceLeft
              (rankOneMatrix
                (sandwichedMutualInformationWeightedPurificationAmp
                  ψ.state.marginalAB.traceRight σB ψ alpha)))
            (traceLeft_posSemidef
              (rankOneMatrix_pos
                (sandwichedMutualInformationWeightedPurificationAmp
                  ψ.state.marginalAB.traceRight σB ψ alpha)))
            (SchattenOrder.ofOneLt halpha)) : EReal) := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  rw [MState.sandwichedRenyiMutualInformationCandidateE_eq_coe_schattenNorm_posDef
    (rhoAB := ψ.state.marginalAB) (sigmaB := σB) hAB hA hσ halpha]
  have hnorm :=
    psdSchattenPNorm_referenceInner_eq_weightedPurification_traceLeft
      σB ψ hA hσ alpha halpha_pos
  exact congrArg
    (fun x : ℝ => ((alpha / (alpha - 1) * log2 x : ℝ) : EReal))
    (by simpa only [SchattenOrder.ofPositive, SchattenOrder.ofOneLt] using hnorm)

/-- Support-convention fixed-candidate sandwiched mutual information as the
Schatten norm of the `C`-side marginal of the KW weighted purification.

This is the source-shaped replacement for the older positive-definite branch:
the side state `sigma_B` is full rank because the optimization is restricted to
that dense domain, but the bipartite state and its `A` marginal may be
singular. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_weightedPurification_traceLeft_of_side_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : MState b) (ψ : Ket ((a × b) × c))
    (hσ : σB.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationCandidateE σB alpha =
      (alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (Matrix.traceLeft
              (rankOneMatrix
                (sandwichedMutualInformationWeightedPurificationAmp
                  ψ.state.marginalAB.traceRight σB ψ alpha)))
            (traceLeft_posSemidef
              (rankOneMatrix_pos
                (sandwichedMutualInformationWeightedPurificationAmp
                  ψ.state.marginalAB.traceRight σB ψ alpha)))
            (SchattenOrder.ofOneLt halpha)) : EReal) := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  rw [MState.sandwichedRenyiMutualInformationCandidateE_eq_coe_schattenNorm_of_side_posDef
    (rhoAB := ψ.state.marginalAB) (sigmaB := σB) hσ halpha]
  have hnorm :=
    psdSchattenPNorm_referenceInner_eq_weightedPurification_traceLeft_support
      σB ψ alpha halpha_pos
  exact congrArg
    (fun x : ℝ => ((alpha / (alpha - 1) * log2 x : ℝ) : EReal))
    (by simpa only [SchattenOrder.ofPositive, SchattenOrder.ofOneLt] using hnorm)

/-- Holder variational form of the weighted-purification Schatten expression.

This is the Lean version of the first variational step in KW
`EA_capacity.tex:2006-2018`: after the rank-one purification reduction, the
positive `C`-side marginal's `alpha`-Schatten expression is the supremum over
the PSD Holder dual unit ball. -/
theorem weightedPurification_traceLeft_schattenNorm_eq_holderUnitBall_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : MState b) (ψ : Ket ((a × b) × c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    let M : CMatrix c :=
      Matrix.traceLeft
        (rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp
            ψ.state.marginalAB.traceRight σB ψ alpha))
    let hM : M.PosSemidef :=
      traceLeft_posSemidef
        (rankOneMatrix_pos
          (sandwichedMutualInformationWeightedPurificationAmp
            ψ.state.marginalAB.traceRight σB ψ alpha))
    psdSchattenPNorm M hM (SchattenOrder.ofOneLt halpha) =
      sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) := by
  let M : CMatrix c :=
    Matrix.traceLeft
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.traceRight σB ψ alpha))
  let hM : M.PosSemidef :=
    traceLeft_posSemidef
      (rankOneMatrix_pos
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.traceRight σB ψ alpha))
  exact
    (psdTraceHolderUnitBall_sSup_eq
      (M := M) hM (p := alpha) (q := Real.conjExponent alpha)
      (Real.HolderConjugate.conjExponent halpha)).symm

/-- Fixed-side-information candidate in the Holder unit-ball form used before
the Sion exchange in KW `EA_capacity.tex:2006-2025`. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_holderUnitBall_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : MState b) (ψ : Ket ((a × b) × c))
    (hAB : ψ.state.marginalAB.m.PosDef)
    (hA : ψ.state.marginalAB.traceRight.m.PosDef)
    (hσ : σB.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationCandidateE σB alpha =
      (alpha / (alpha - 1) *
        log2
          (sSup
            (psdTraceHolderUnitBallValueSet
              (Matrix.traceLeft
                (rankOneMatrix
                  (sandwichedMutualInformationWeightedPurificationAmp
                    ψ.state.marginalAB.traceRight σB ψ alpha)))
              (Real.conjExponent alpha))) : EReal) := by
  let M : CMatrix c :=
    Matrix.traceLeft
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.traceRight σB ψ alpha))
  let hM : M.PosSemidef :=
    traceLeft_posSemidef
      (rankOneMatrix_pos
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.traceRight σB ψ alpha))
  rw [sandwichedRenyiMutualInformationCandidateE_eq_coe_weightedPurification_traceLeft
    σB ψ hAB hA hσ halpha]
  have hholder :
      psdSchattenPNorm M hM (SchattenOrder.ofOneLt halpha) =
        sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) := by
    exact weightedPurification_traceLeft_schattenNorm_eq_holderUnitBall_sSup
      σB ψ halpha
  change
    ((alpha / (alpha - 1) *
        log2 (psdSchattenPNorm M hM (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) =
      ((alpha / (alpha - 1) *
        log2 (sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha))) : ℝ) :
          EReal)
  rw [hholder]

/-- Support-convention fixed-side-information candidate in the Holder
unit-ball form used before the Sion exchange in KW
`EA_capacity.tex:2006-2025`. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_holderUnitBall_sSup_of_side_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : MState b) (ψ : Ket ((a × b) × c))
    (hσ : σB.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationCandidateE σB alpha =
      (alpha / (alpha - 1) *
        log2
          (sSup
            (psdTraceHolderUnitBallValueSet
              (Matrix.traceLeft
                (rankOneMatrix
                  (sandwichedMutualInformationWeightedPurificationAmp
                    ψ.state.marginalAB.traceRight σB ψ alpha)))
              (Real.conjExponent alpha))) : EReal) := by
  let M : CMatrix c :=
    Matrix.traceLeft
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.traceRight σB ψ alpha))
  let hM : M.PosSemidef :=
    traceLeft_posSemidef
      (rankOneMatrix_pos
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.traceRight σB ψ alpha))
  rw [sandwichedRenyiMutualInformationCandidateE_eq_coe_weightedPurification_traceLeft_of_side_posDef
    σB ψ hσ halpha]
  have hholder :
      psdSchattenPNorm M hM (SchattenOrder.ofOneLt halpha) =
        sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) := by
    exact weightedPurification_traceLeft_schattenNorm_eq_holderUnitBall_sSup
      σB ψ halpha
  change
    ((alpha / (alpha - 1) *
        log2 (psdSchattenPNorm M hM (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) =
      ((alpha / (alpha - 1) *
        log2 (sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha))) : ℝ) :
          EReal)
  rw [hholder]

/-- Real-valued full-rank candidate in the Holder unit-ball form used before
the Sion exchange in KW `EA_capacity.tex:2006-2025`.

This is the real branch of
`sandwichedRenyiMutualInformationCandidateE_eq_coe_holderUnitBall_sSup`,
extracted so the optimized full-rank `inf` can be rewritten before the Sion
minimax exchange. -/
theorem sandwichedRenyiMutualInformationCandidateRealPosDef_eq_holderUnitBall_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : MState b) (ψ : Ket ((a × b) × c))
    (hAB : ψ.state.marginalAB.m.PosDef)
    (hA : ψ.state.marginalAB.traceRight.m.PosDef)
    (hσ : σB.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    MState.sandwichedRenyiMutualInformationCandidateRealPosDef
        ψ.state.marginalAB σB hAB hA hσ alpha halpha =
      alpha / (alpha - 1) *
        log2
          (sSup
            (psdTraceHolderUnitBallValueSet
              (Matrix.traceLeft
                (rankOneMatrix
                  (sandwichedMutualInformationWeightedPurificationAmp
                    ψ.state.marginalAB.traceRight σB ψ alpha)))
              (Real.conjExponent alpha))) := by
  have hreal :=
    MState.sandwichedRenyiMutualInformationCandidateE_eq_coe_candidateRealPosDef
      (rhoAB := ψ.state.marginalAB) (sigmaB := σB) hAB hA hσ halpha
  have hholder :=
    sandwichedRenyiMutualInformationCandidateE_eq_coe_holderUnitBall_sSup
      σB ψ hAB hA hσ halpha
  exact EReal.coe_eq_coe_iff.mp (hreal.symm.trans hholder)

/-- Optimized state sandwiched-Renyi mutual information as the full-rank
side-reference infimum of the KW Holder unit-ball expression.

This is the source-shaped bridge between the repository definition
`inf_{sigma_B} D_alpha(rho_AB || rho_A ⊗ sigma_B)` and the first variational
form of KW `EA_capacity.tex:2006-2025`.  It is still before the Sion exchange
and before the reverse-Holder reduction to the `AC` trace-matrix norm. -/
theorem sandwichedRenyiMutualInformationE_eq_sInf_fullRank_holderUnitBall_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (ψ : Ket ((a × b) × c))
    (hAB : ψ.state.marginalAB.m.PosDef)
    (hA : ψ.state.marginalAB.traceRight.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      sInf (Set.range fun σB : {σ : MState b // σ.m.PosDef} =>
        ((alpha / (alpha - 1) *
          log2
            (sSup
              (psdTraceHolderUnitBallValueSet
                (Matrix.traceLeft
                  (rankOneMatrix
                    (sandwichedMutualInformationWeightedPurificationAmp
                      ψ.state.marginalAB.traceRight σB.1 ψ alpha)))
                (Real.conjExponent alpha))) : ℝ) : EReal)) := by
  rw [MState.sandwichedRenyiMutualInformationE_eq_sInf_fullRankCandidateReal
    ψ.state.marginalAB hAB hA halpha]
  have hfun :
      (fun σB : {σ : MState b // σ.m.PosDef} =>
        (MState.sandwichedRenyiMutualInformationCandidateRealPosDef
          ψ.state.marginalAB σB.1 hAB hA σB.2 alpha halpha : EReal)) =
      (fun σB : {σ : MState b // σ.m.PosDef} =>
        ((alpha / (alpha - 1) *
          log2
            (sSup
              (psdTraceHolderUnitBallValueSet
                (Matrix.traceLeft
                  (rankOneMatrix
                    (sandwichedMutualInformationWeightedPurificationAmp
                      ψ.state.marginalAB.traceRight σB.1 ψ alpha)))
                (Real.conjExponent alpha))) : ℝ) : EReal)) := by
    funext σB
    rw [sandwichedRenyiMutualInformationCandidateRealPosDef_eq_holderUnitBall_sSup
      σB.1 ψ hAB hA σB.2 halpha]
  rw [hfun]

/-- Support-convention optimized state sandwiched-Renyi mutual information as
the full-rank side-reference infimum of the KW Holder unit-ball expression.

This is the source-shaped variant of
`sandwichedRenyiMutualInformationE_eq_sInf_fullRank_holderUnitBall_sSup`.
The full-rank restriction is only on the optimized side state `sigma_B`; the
input bipartite state and its `A` marginal are allowed to be singular, matching
the support convention in KW `EA_capacity.tex:2006-2025`. -/
theorem sandwichedRenyiMutualInformationE_eq_iInf_fullRank_holderUnitBall_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (ψ : Ket ((a × b) × c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      ⨅ σB : {σ : MState b // σ.m.PosDef},
        ((alpha / (alpha - 1) *
          log2
            (sSup
              (psdTraceHolderUnitBallValueSet
                (Matrix.traceLeft
                  (rankOneMatrix
                    (sandwichedMutualInformationWeightedPurificationAmp
                      ψ.state.marginalAB.traceRight σB.1 ψ alpha)))
                (Real.conjExponent alpha))) : ℝ) : EReal) := by
  rw [MState.sandwichedRenyiMutualInformationE_eq_iInf_posDef_candidates_highAlpha
    ψ.state.marginalAB halpha]
  apply iInf_congr
  intro σB
  exact
    sandwichedRenyiMutualInformationCandidateE_eq_coe_holderUnitBall_sSup_of_side_posDef
      σB.1 ψ σB.2 halpha

/-- For a fixed full-rank `sigma_B`, the Holder unit-ball supremum equals the
source supremum over purifying side states `tau_C`.

This is the exact equality form of KW `EA_capacity.tex:2010-2018`, combining
the two one-sided bridges already proved above. -/
theorem sandwichedMutualInformationSionBracketRe_sSup_eq_holderUnitBall_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (sigmaB : MState b) (hrhoA : rhoA.m.PosDef) (hsigmaB : sigmaB.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sSup (Set.range fun tauC : MState c =>
      sandwichedMutualInformationSionBracketRe rhoA ψ sigmaB tauC alpha) =
      sSup
        (psdTraceHolderUnitBallValueSet
          (Matrix.traceLeft
            (rankOneMatrix
              (sandwichedMutualInformationWeightedPurificationAmp rhoA sigmaB ψ alpha)))
          (Real.conjExponent alpha)) := by
  let M : CMatrix c :=
    Matrix.traceLeft
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA sigmaB ψ alpha))
  let holder : ℝ := sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha))
  have hupper :
      BddAbove (Set.range fun tauC : MState c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ sigmaB tauC alpha) := by
    refine ⟨holder, ?_⟩
    rintro y ⟨tauC, rfl⟩
    simpa [holder, M] using
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup
        rhoA ψ sigmaB tauC hrhoA hsigmaB halpha
  have : Nonempty (MState c) := ⟨(MState.uniform : MState c)⟩
  apply le_antisymm
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro y ⟨tauC, rfl⟩
    simpa [holder, M] using
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup
        rhoA ψ sigmaB tauC hrhoA hsigmaB halpha
  · simpa [holder, M] using
      weightedPurification_holderUnitBall_sSup_le_sandwichedMutualInformationSionBracketRe_sSup
        rhoA ψ sigmaB hrhoA hsigmaB halpha

/-- Support-convention equality between the `tau_C`-optimized KW Sion bracket
and the Holder unit-ball supremum.

This is the source-shaped version of
`sandwichedMutualInformationSionBracketRe_sSup_eq_holderUnitBall_sSup`: the
fixed `rho_A` may be singular, and only the side state `sigma_B` is restricted
to the full-rank branch used for the dense side optimization. -/
theorem sandwichedMutualInformationSionBracketRe_sSup_eq_holderUnitBall_sSup_of_side_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (sigmaB : MState b) (hsigmaB : sigmaB.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sSup (Set.range fun tauC : MState c =>
      sandwichedMutualInformationSionBracketRe rhoA ψ sigmaB tauC alpha) =
      sSup
        (psdTraceHolderUnitBallValueSet
          (Matrix.traceLeft
            (rankOneMatrix
              (sandwichedMutualInformationWeightedPurificationAmp rhoA sigmaB ψ alpha)))
          (Real.conjExponent alpha)) := by
  let M : CMatrix c :=
    Matrix.traceLeft
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA sigmaB ψ alpha))
  let holder : ℝ := sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha))
  have hupper :
      BddAbove (Set.range fun tauC : MState c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ sigmaB tauC alpha) := by
    refine ⟨holder, ?_⟩
    rintro y ⟨tauC, rfl⟩
    simpa [holder, M] using
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup_of_side_posDef
        rhoA ψ sigmaB tauC hsigmaB halpha
  have : Nonempty (MState c) := ⟨(MState.uniform : MState c)⟩
  apply le_antisymm
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro y ⟨tauC, rfl⟩
    simpa [holder, M] using
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup_of_side_posDef
        rhoA ψ sigmaB tauC hsigmaB halpha
  · simpa [holder, M] using
      weightedPurification_holderUnitBall_sSup_le_sandwichedMutualInformationSionBracketRe_sSup_of_side_posDef
        rhoA ψ sigmaB hsigmaB halpha

/-- The KW `tau_C`-optimized Sion bracket is strictly positive on a full-rank
`sigma_B` branch.

This is the positivity side condition for moving `log2` across the
`tau_C` supremum in the state alternate-expression proof. -/
theorem sandwichedMutualInformationSionBracketRe_sSup_pos
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : Ket ((a × b) × c))
    (sigmaB : MState b)
    (hAB : ψ.state.marginalAB.m.PosDef)
    (hA : ψ.state.marginalAB.traceRight.m.PosDef)
    (hsigmaB : sigmaB.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    0 < sSup (Set.range fun tauC : MState c =>
      sandwichedMutualInformationSionBracketRe
        ψ.state.marginalAB.traceRight ψ sigmaB tauC alpha) := by
  let M : CMatrix c :=
    Matrix.traceLeft
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.traceRight sigmaB ψ alpha))
  let hM : M.PosSemidef :=
    traceLeft_posSemidef
      (rankOneMatrix_pos
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.traceRight sigmaB ψ alpha))
  have hholder_eq :
      sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) =
        psdSchattenPNorm M hM (SchattenOrder.ofOneLt halpha) := by
    exact psdTraceHolderUnitBall_sSup_eq
      (M := M) hM (p := alpha) (q := Real.conjExponent alpha)
      (Real.HolderConjugate.conjExponent halpha)
  have href_pos :
      0 <
        psdTracePower
          (MState.sandwichedRenyiReferenceInner ψ.state.marginalAB
            (ψ.state.marginalAB.traceRight.prod sigmaB).m alpha)
          (MState.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
            (MState.PosDef.kron hA hsigmaB).posSemidef alpha)
          alpha :=
    MState.sandwichedRenyiReferenceInner_psdTracePower_pos ψ.state.marginalAB hAB
      (MState.PosDef.kron hA hsigmaB) alpha
  have hnorm_pos :
      0 <
        psdSchattenPNorm
          (MState.sandwichedRenyiReferenceInner ψ.state.marginalAB
            (ψ.state.marginalAB.traceRight.prod sigmaB).m alpha)
          (MState.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
            (MState.PosDef.kron hA hsigmaB).posSemidef alpha)
          (SchattenOrder.ofOneLt halpha) := by
    unfold psdSchattenPNorm
    exact Real.rpow_pos_of_pos href_pos (1 / alpha)
  have hholder_pos :
      0 < sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) := by
    rw [hholder_eq]
    simpa [M, hM] using
      (hnorm_pos.trans_eq
        (psdSchattenPNorm_referenceInner_eq_weightedPurification_traceLeft
          sigmaB ψ hA hsigmaB alpha (lt_trans zero_lt_one halpha)))
  have hsup_eq :=
    sandwichedMutualInformationSionBracketRe_sSup_eq_holderUnitBall_sSup
      ψ.state.marginalAB.traceRight ψ sigmaB hA hsigmaB halpha
  rwa [hsup_eq]

/-- On each full-rank `sigma_B` branch, the KW `tau_C`-optimized raw bracket
is at least one.

This is the scalar consequence of nonnegativity of the corresponding
sandwiched-Renyi candidate, and it supplies the strict lower bound needed for
the `log2`/`sInf` transport in the alternate-expression proof. -/
theorem one_le_sandwichedMutualInformationSionBracketRe_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : Ket ((a × b) × c))
    (sigmaB : MState b)
    (hAB : ψ.state.marginalAB.m.PosDef)
    (hA : ψ.state.marginalAB.traceRight.m.PosDef)
    (hsigmaB : sigmaB.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    1 ≤ sSup (Set.range fun tauC : MState c =>
      sandwichedMutualInformationSionBracketRe
        ψ.state.marginalAB.traceRight ψ sigmaB tauC alpha) := by
  let x : ℝ := sSup (Set.range fun tauC : MState c =>
    sandwichedMutualInformationSionBracketRe
      ψ.state.marginalAB.traceRight ψ sigmaB tauC alpha)
  have hxpos : 0 < x := by
    simpa [x] using
      sandwichedMutualInformationSionBracketRe_sSup_pos
        ψ sigmaB hAB hA hsigmaB halpha
  have hcandidate_nonneg :
      0 ≤ MState.sandwichedRenyiMutualInformationCandidateRealPosDef
        ψ.state.marginalAB sigmaB hAB hA hsigmaB alpha halpha :=
    MState.sandwichedRenyiMutualInformationCandidateRealPosDef_nonneg
      ψ.state.marginalAB sigmaB hAB hA hsigmaB halpha
  have hcandidate_eq :
      MState.sandwichedRenyiMutualInformationCandidateRealPosDef
          ψ.state.marginalAB sigmaB hAB hA hsigmaB alpha halpha =
        alpha / (alpha - 1) * log2 x := by
    rw [sandwichedRenyiMutualInformationCandidateRealPosDef_eq_holderUnitBall_sSup
      sigmaB ψ hAB hA hsigmaB halpha]
    have hsup_eq :=
      sandwichedMutualInformationSionBracketRe_sSup_eq_holderUnitBall_sSup
        ψ.state.marginalAB.traceRight ψ sigmaB hA hsigmaB halpha
    simpa [x] using congrArg (fun y : ℝ => alpha / (alpha - 1) * log2 y) hsup_eq.symm
  have hlog_nonneg : 0 ≤ log2 x := by
    have hmul : 0 ≤ alpha / (alpha - 1) * log2 x := by
      rw [hcandidate_eq] at hcandidate_nonneg
      exact hcandidate_nonneg
    have hmul' : 0 ≤ log2 x * (alpha / (alpha - 1)) := by
      simpa [mul_comm] using hmul
    exact nonneg_of_mul_nonneg_left hmul' (highAlpha_conjExponent_pos halpha)
  unfold log2 at hlog_nonneg
  have hlog_nonneg' : 0 ≤ Real.log x := by
    have hden_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    rcases (div_nonneg_iff.mp hlog_nonneg) with h | h
    · exact h.1
    · exact (not_le_of_gt hden_pos h.2).elim
  exact (Real.log_nonneg_iff hxpos).mp hlog_nonneg'

/-- Support-convention positivity of the KW `tau_C`-optimized Sion bracket on a
full-rank `sigma_B` branch.

The input bipartite state and its left marginal may be singular.  Positivity is
obtained from the supported PSD-reference branch for
`rho_AB || rho_A \otimes sigma_B`, using that a full-rank `sigma_B` supports the
side-information reference. -/
theorem sandwichedMutualInformationSionBracketRe_sSup_pos_of_side_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : Ket ((a × b) × c))
    (sigmaB : MState b) (hsigmaB : sigmaB.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    0 < sSup (Set.range fun tauC : MState c =>
      sandwichedMutualInformationSionBracketRe
        ψ.state.marginalAB.traceRight ψ sigmaB tauC alpha) := by
  let M : CMatrix c :=
    Matrix.traceLeft
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.traceRight sigmaB ψ alpha))
  let hM : M.PosSemidef :=
    traceLeft_posSemidef
      (rankOneMatrix_pos
        (sandwichedMutualInformationWeightedPurificationAmp
          ψ.state.marginalAB.traceRight sigmaB ψ alpha))
  have hholder_eq :
      sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) =
        psdSchattenPNorm M hM (SchattenOrder.ofOneLt halpha) := by
    exact psdTraceHolderUnitBall_sSup_eq
      (M := M) hM (p := alpha) (q := Real.conjExponent alpha)
      (Real.HolderConjugate.conjExponent halpha)
  have hsupport :
      Matrix.Supports ψ.state.marginalAB.m
        (ψ.state.marginalAB.traceRight.prod sigmaB).m :=
    MState.supports_traceRight_prod_of_side_posDef ψ.state.marginalAB sigmaB hsigmaB
  have href_pos :
      0 <
        psdTracePower
          (MState.sandwichedRenyiReferenceInner ψ.state.marginalAB
            (ψ.state.marginalAB.traceRight.prod sigmaB).m alpha)
          (MState.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
            (ψ.state.marginalAB.traceRight.prod sigmaB).psd alpha)
          alpha :=
    MState.sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports
      ψ.state.marginalAB (ψ.state.marginalAB.traceRight.prod sigmaB).psd
      hsupport alpha
  have hnorm_pos :
      0 <
        psdSchattenPNorm
          (MState.sandwichedRenyiReferenceInner ψ.state.marginalAB
            (ψ.state.marginalAB.traceRight.prod sigmaB).m alpha)
          (MState.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
            (ψ.state.marginalAB.traceRight.prod sigmaB).psd alpha)
          (SchattenOrder.ofOneLt halpha) := by
    unfold psdSchattenPNorm
    exact Real.rpow_pos_of_pos href_pos (1 / alpha)
  have hholder_pos :
      0 < sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) := by
    rw [hholder_eq]
    simpa [M, hM] using
      (hnorm_pos.trans_eq
        (psdSchattenPNorm_referenceInner_eq_weightedPurification_traceLeft_support
          sigmaB ψ alpha (lt_trans zero_lt_one halpha)))
  have hsup_eq :=
    sandwichedMutualInformationSionBracketRe_sSup_eq_holderUnitBall_sSup_of_side_posDef
      ψ.state.marginalAB.traceRight ψ sigmaB hsigmaB halpha
  rwa [hsup_eq]

/-- Support-convention scalar lower bound for the KW `tau_C`-optimized Sion
bracket on a full-rank `sigma_B` branch.

This is the no-full-support replacement for
`one_le_sandwichedMutualInformationSionBracketRe_sSup`; it is the scalar fact
needed to move `log2` through the full-rank side-reference infimum. -/
theorem one_le_sandwichedMutualInformationSionBracketRe_sSup_of_side_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : Ket ((a × b) × c))
    (sigmaB : MState b) (hsigmaB : sigmaB.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    1 ≤ sSup (Set.range fun tauC : MState c =>
      sandwichedMutualInformationSionBracketRe
        ψ.state.marginalAB.traceRight ψ sigmaB tauC alpha) := by
  let x : ℝ := sSup (Set.range fun tauC : MState c =>
    sandwichedMutualInformationSionBracketRe
      ψ.state.marginalAB.traceRight ψ sigmaB tauC alpha)
  have hxpos : 0 < x := by
    simpa [x] using
      sandwichedMutualInformationSionBracketRe_sSup_pos_of_side_posDef
        ψ sigmaB hsigmaB halpha
  let finite : ℝ :=
    MState.sandwichedRenyiPSDReferenceHighAlphaFinite ψ.state.marginalAB
      (ψ.state.marginalAB.traceRight.prod sigmaB).m
      (ψ.state.marginalAB.traceRight.prod sigmaB).psd alpha
  have hsupport :
      Matrix.Supports ψ.state.marginalAB.m
        (ψ.state.marginalAB.traceRight.prod sigmaB).m :=
    MState.supports_traceRight_prod_of_side_posDef ψ.state.marginalAB sigmaB hsigmaB
  have hfinite_nonneg : 0 ≤ finite := by
    simpa [finite] using
      MState.sandwichedRenyiPSDReferenceHighAlphaFinite_nonneg_of_state_reference_supports
        ψ.state.marginalAB (ψ.state.marginalAB.traceRight.prod sigmaB) hsupport halpha
  have hcandidate_finite :
      ψ.state.marginalAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
        (finite : EReal) := by
    simpa [finite] using
      MState.sandwichedRenyiMutualInformationCandidateE_eq_coe_highAlphaFinite_of_side_posDef
        ψ.state.marginalAB sigmaB hsigmaB halpha
  have hcandidate_holder :
      ψ.state.marginalAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
        ((alpha / (alpha - 1) * log2 x : ℝ) : EReal) := by
    rw [sandwichedRenyiMutualInformationCandidateE_eq_coe_holderUnitBall_sSup_of_side_posDef
      sigmaB ψ hsigmaB halpha]
    have hsup_eq :=
      sandwichedMutualInformationSionBracketRe_sSup_eq_holderUnitBall_sSup_of_side_posDef
        ψ.state.marginalAB.traceRight ψ sigmaB hsigmaB halpha
    simpa [x, EReal.coe_div] using congrArg
      (fun y : ℝ => ((alpha / (alpha - 1) * log2 y : ℝ) : EReal))
      hsup_eq.symm
  have hreal_eq : finite = alpha / (alpha - 1) * log2 x :=
    EReal.coe_eq_coe_iff.mp (hcandidate_finite.symm.trans hcandidate_holder)
  have hlog_nonneg : 0 ≤ log2 x := by
    have hmul : 0 ≤ alpha / (alpha - 1) * log2 x := by
      rwa [← hreal_eq]
    have hmul' : 0 ≤ log2 x * (alpha / (alpha - 1)) := by
      simpa [mul_comm] using hmul
    exact nonneg_of_mul_nonneg_left hmul' (highAlpha_conjExponent_pos halpha)
  unfold log2 at hlog_nonneg
  have hlog_nonneg' : 0 ≤ Real.log x := by
    have hden_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    rcases (div_nonneg_iff.mp hlog_nonneg) with h | h
    · exact h.1
    · exact (not_le_of_gt hden_pos h.2).elim
  exact (Real.log_nonneg_iff hxpos).mp hlog_nonneg'

/-- Equality version of the KW bridge from the optimized state quantity to the
full-rank `sigma_B` infimum of the `tau_C`-optimized Sion bracket. -/
theorem sandwichedRenyiMutualInformationE_eq_sInf_fullRank_sSup_sionBracketLog
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : Ket ((a × b) × c))
    (hAB : ψ.state.marginalAB.m.PosDef)
    (hA : ψ.state.marginalAB.traceRight.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      sInf (Set.range fun σB : {σ : MState b // σ.m.PosDef} =>
        ((alpha / (alpha - 1) *
          log2
            (sSup (Set.range fun τC : MState c =>
              sandwichedMutualInformationSionBracketRe
                ψ.state.marginalAB.traceRight ψ σB.1 τC alpha)) : ℝ) : EReal)) := by
  rw [sandwichedRenyiMutualInformationE_eq_sInf_fullRank_holderUnitBall_sSup
    ψ hAB hA halpha]
  have hfun :
      (fun σB : {σ : MState b // σ.m.PosDef} =>
        ((alpha / (alpha - 1) *
          log2
            (sSup
              (psdTraceHolderUnitBallValueSet
                (Matrix.traceLeft
                  (rankOneMatrix
                    (sandwichedMutualInformationWeightedPurificationAmp
                      ψ.state.marginalAB.traceRight σB.1 ψ alpha)))
                (Real.conjExponent alpha))) : ℝ) : EReal)) =
        (fun σB : {σ : MState b // σ.m.PosDef} =>
          ((alpha / (alpha - 1) *
            log2
              (sSup (Set.range fun τC : MState c =>
                sandwichedMutualInformationSionBracketRe
                  ψ.state.marginalAB.traceRight ψ σB.1 τC alpha)) : ℝ) : EReal)) := by
    funext σB
    rw [sandwichedMutualInformationSionBracketRe_sSup_eq_holderUnitBall_sSup
      ψ.state.marginalAB.traceRight ψ σB.1 hA σB.2 halpha]
  rw [hfun]

/-- Support-convention pointwise logarithmic bridge from the optimized state
quantity to the full-rank `sigma_B` infimum of the `tau_C`-optimized Sion
bracket.

Unlike the subsequent scalar transport theorem, this statement does not move
`log2` through the outer infimum.  It is therefore the exact safe API supplied
by the KW Holder/Sion variational step before proving the extra positivity and
boundedness needed for `log inf = inf log`. -/
theorem sandwichedRenyiMutualInformationE_eq_iInf_fullRank_sSup_sionBracketLog
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : Ket ((a × b) × c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      ⨅ σB : {σ : MState b // σ.m.PosDef},
        ((alpha / (alpha - 1) *
          log2
            (sSup (Set.range fun τC : MState c =>
              sandwichedMutualInformationSionBracketRe
                ψ.state.marginalAB.traceRight ψ σB.1 τC alpha)) : ℝ) : EReal) := by
  rw [sandwichedRenyiMutualInformationE_eq_iInf_fullRank_holderUnitBall_sSup
    ψ halpha]
  apply iInf_congr
  intro σB
  rw [sandwichedMutualInformationSionBracketRe_sSup_eq_holderUnitBall_sSup_of_side_posDef
    ψ.state.marginalAB.traceRight ψ σB.1 σB.2 halpha]

/-- Logarithmic scalar transport for the pre-Sion side of the KW state
alternate expression.

After the Holder variational equality, the optimized state quantity is the
positive coefficient times the logarithm of the raw `inf_sigma sup_tau`
Sion bracket. -/
theorem sandwichedRenyiMutualInformationE_eq_coeff_log2_sInf_sSup_sionBracketRe
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : Ket ((a × b) × c))
    (hAB : ψ.state.marginalAB.m.PosDef)
    (hA : ψ.state.marginalAB.traceRight.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      ((alpha / (alpha - 1) *
        log2
          (sInf (Set.range fun σB : {σ : MState b // σ.m.PosDef} =>
            sSup (Set.range fun τC : MState c =>
              sandwichedMutualInformationSionBracketRe
                ψ.state.marginalAB.traceRight ψ σB.1 τC alpha))) : ℝ) : EReal) := by
  let S := {σ : MState b // σ.m.PosDef}
  let raw : S → MState c → ℝ := fun σB τC =>
    sandwichedMutualInformationSionBracketRe
      ψ.state.marginalAB.traceRight ψ σB.1 τC alpha
  let supRaw : S → ℝ := fun σB => sSup (Set.range fun τC : MState c => raw σB τC)
  let coeff : ℝ := alpha / (alpha - 1)
  let logs : S → ℝ := fun σB => log2 (supRaw σB)
  let scaled : S → ℝ := fun σB => coeff * logs σB
  have : Nonempty S := ⟨⟨(MState.uniform : MState b), MState.uniform_posDef⟩⟩
  have hsup_one (σB : S) : 1 ≤ supRaw σB := by
    simpa [supRaw, raw] using
      one_le_sandwichedMutualInformationSionBracketRe_sSup
        ψ σB.1 hAB hA σB.2 halpha
  have hsup_bddBelow : BddBelow (Set.range supRaw) := by
    refine ⟨1, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact hsup_one σB
  have hsup_inf_pos : 0 < sInf (Set.range supRaw) := by
    exact zero_lt_one.trans_le (le_csInf (Set.range_nonempty supRaw) (by
      rintro y ⟨σB, rfl⟩
      exact hsup_one σB))
  have hlogs_sInf :
      sInf (Set.range logs) = log2 (sInf (Set.range supRaw)) := by
    have himage : Set.range logs = log2 '' Set.range supRaw := by
      ext x
      constructor
      · rintro ⟨σB, rfl⟩
        exact ⟨supRaw σB, ⟨σB, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨σB, rfl⟩, rfl⟩
        exact ⟨σB, rfl⟩
    rw [himage, real_log2_sInf_image_eq (Set.range_nonempty supRaw)
      hsup_bddBelow hsup_inf_pos]
  have hlogs_nonneg (σB : S) : 0 ≤ logs σB := by
    unfold logs log2
    have hxpos : 0 < supRaw σB := zero_lt_one.trans_le (hsup_one σB)
    have hxlog : 0 ≤ Real.log (supRaw σB) :=
      (Real.log_nonneg_iff hxpos).mpr (hsup_one σB)
    exact div_nonneg hxlog (le_of_lt (Real.log_pos one_lt_two))
  have hscaled_bddBelow : BddBelow (Set.range scaled) := by
    refine ⟨0, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact mul_nonneg (le_of_lt (highAlpha_conjExponent_pos halpha)) (hlogs_nonneg σB)
  have hscaled_sInf :
      sInf (Set.range scaled) =
        coeff * log2 (sInf (Set.range supRaw)) := by
    have hcoeff_nonneg : 0 ≤ coeff := le_of_lt (by
      simpa [coeff] using highAlpha_conjExponent_pos halpha)
    have himage :
        Set.range scaled = (fun x : ℝ => coeff * x) '' Set.range logs := by
      ext x
      constructor
      · rintro ⟨σB, rfl⟩
        exact ⟨logs σB, ⟨σB, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨σB, rfl⟩, rfl⟩
        exact ⟨σB, rfl⟩
    have hsmul : (fun x : ℝ => coeff * x) '' Set.range logs =
        coeff • Set.range logs := by
      ext x
      constructor
      · rintro ⟨_, hy, rfl⟩
        exact Set.mem_smul_set.mpr ⟨_, hy, by rw [smul_eq_mul]⟩
      · intro hx
        rcases Set.mem_smul_set.mp hx with ⟨_, hy, hxy⟩
        exact ⟨_, hy, by simpa [smul_eq_mul] using hxy⟩
    calc
      sInf (Set.range scaled) =
          sInf ((fun x : ℝ => coeff * x) '' Set.range logs) := by
            rw [himage]
      _ = sInf (coeff • Set.range logs) := by
            rw [hsmul]
      _ = coeff * sInf (Set.range logs) := by
            rw [Real.sInf_smul_of_nonneg hcoeff_nonneg]
            simp [smul_eq_mul]
      _ = coeff * log2 (sInf (Set.range supRaw)) := by
            rw [hlogs_sInf]
  rw [sandwichedRenyiMutualInformationE_eq_sInf_fullRank_sSup_sionBracketLog
    ψ hAB hA halpha]
  change sInf (Set.range fun σB : S => (scaled σB : EReal)) =
    ((coeff * log2 (sInf (Set.range supRaw)) : ℝ) : EReal)
  rw [ereal_sInf_range_coe_eq_coe_real_sInf scaled hscaled_bddBelow]
  rw [hscaled_sInf]

/-- Support-convention logarithmic scalar transport for the pre-Sion side of the
KW state alternate expression.

This is the no-full-support version of
`sandwichedRenyiMutualInformationE_eq_coeff_log2_sInf_sSup_sionBracketRe`.
It uses the supported full-rank side-candidate branch, so neither the input
bipartite state nor its left marginal is assumed positive definite. -/
theorem sandwichedRenyiMutualInformationE_eq_coeff_log2_sInf_sSup_sionBracketRe_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : Ket ((a × b) × c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      ((alpha / (alpha - 1) *
        log2
          (sInf (Set.range fun σB : {σ : MState b // σ.m.PosDef} =>
            sSup (Set.range fun τC : MState c =>
              sandwichedMutualInformationSionBracketRe
                ψ.state.marginalAB.traceRight ψ σB.1 τC alpha))) : ℝ) : EReal) := by
  let S := {σ : MState b // σ.m.PosDef}
  let raw : S → MState c → ℝ := fun σB τC =>
    sandwichedMutualInformationSionBracketRe
      ψ.state.marginalAB.traceRight ψ σB.1 τC alpha
  let supRaw : S → ℝ := fun σB => sSup (Set.range fun τC : MState c => raw σB τC)
  let coeff : ℝ := alpha / (alpha - 1)
  let logs : S → ℝ := fun σB => log2 (supRaw σB)
  let scaled : S → ℝ := fun σB => coeff * logs σB
  have : Nonempty S := ⟨⟨(MState.uniform : MState b), MState.uniform_posDef⟩⟩
  have hsup_one (σB : S) : 1 ≤ supRaw σB := by
    simpa [supRaw, raw] using
      one_le_sandwichedMutualInformationSionBracketRe_sSup_of_side_posDef
        ψ σB.1 σB.2 halpha
  have hsup_bddBelow : BddBelow (Set.range supRaw) := by
    refine ⟨1, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact hsup_one σB
  have hsup_inf_pos : 0 < sInf (Set.range supRaw) := by
    exact zero_lt_one.trans_le (le_csInf (Set.range_nonempty supRaw) (by
      rintro y ⟨σB, rfl⟩
      exact hsup_one σB))
  have hlogs_sInf :
      sInf (Set.range logs) = log2 (sInf (Set.range supRaw)) := by
    have himage : Set.range logs = log2 '' Set.range supRaw := by
      ext x
      constructor
      · rintro ⟨σB, rfl⟩
        exact ⟨supRaw σB, ⟨σB, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨σB, rfl⟩, rfl⟩
        exact ⟨σB, rfl⟩
    rw [himage, real_log2_sInf_image_eq (Set.range_nonempty supRaw)
      hsup_bddBelow hsup_inf_pos]
  have hlogs_nonneg (σB : S) : 0 ≤ logs σB := by
    unfold logs log2
    have hxpos : 0 < supRaw σB := zero_lt_one.trans_le (hsup_one σB)
    have hxlog : 0 ≤ Real.log (supRaw σB) :=
      (Real.log_nonneg_iff hxpos).mpr (hsup_one σB)
    exact div_nonneg hxlog (le_of_lt (Real.log_pos one_lt_two))
  have hscaled_bddBelow : BddBelow (Set.range scaled) := by
    refine ⟨0, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact mul_nonneg (le_of_lt (highAlpha_conjExponent_pos halpha)) (hlogs_nonneg σB)
  have hscaled_sInf :
      sInf (Set.range scaled) =
        coeff * log2 (sInf (Set.range supRaw)) := by
    have hcoeff_nonneg : 0 ≤ coeff := le_of_lt (by
      simpa [coeff] using highAlpha_conjExponent_pos halpha)
    have himage :
        Set.range scaled = (fun x : ℝ => coeff * x) '' Set.range logs := by
      ext x
      constructor
      · rintro ⟨σB, rfl⟩
        exact ⟨logs σB, ⟨σB, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨σB, rfl⟩, rfl⟩
        exact ⟨σB, rfl⟩
    have hsmul : (fun x : ℝ => coeff * x) '' Set.range logs =
        coeff • Set.range logs := by
      ext x
      constructor
      · rintro ⟨_, hy, rfl⟩
        exact Set.mem_smul_set.mpr ⟨_, hy, by rw [smul_eq_mul]⟩
      · intro hx
        rcases Set.mem_smul_set.mp hx with ⟨_, hy, hxy⟩
        exact ⟨_, hy, by simpa [smul_eq_mul] using hxy⟩
    calc
      sInf (Set.range scaled) =
          sInf ((fun x : ℝ => coeff * x) '' Set.range logs) := by
            rw [himage]
      _ = sInf (coeff • Set.range logs) := by
            rw [hsmul]
      _ = coeff * sInf (Set.range logs) := by
            rw [Real.sInf_smul_of_nonneg hcoeff_nonneg]
            simp [smul_eq_mul]
      _ = coeff * log2 (sInf (Set.range supRaw)) := by
            rw [hlogs_sInf]
  rw [sandwichedRenyiMutualInformationE_eq_iInf_fullRank_sSup_sionBracketLog
    ψ halpha]
  change sInf (Set.range fun σB : S => (scaled σB : EReal)) =
    ((coeff * log2 (sInf (Set.range supRaw)) : ℝ) : EReal)
  rw [ereal_sInf_range_coe_eq_coe_real_sInf scaled hscaled_bddBelow]
  rw [hscaled_sInf]

/-- Real-valued form of the full-rank Sion exchange for the KW sandwiched
mutual-information bracket. -/
theorem sandwichedMutualInformationSionBracketRe_real_sInf_sSup_eq_sSup_sInf
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (hrhoA : rhoA.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    sInf (Set.range fun σB : {σ : MState b // σ.m.PosDef} =>
      sSup (Set.range fun τC : MState c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha)) =
      sSup (Set.range fun τC : MState c =>
        sInf (Set.range fun σB : {σ : MState b // σ.m.PosDef} =>
          sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha)) := by
  let S := {σ : MState b // σ.m.PosDef}
  let raw : S → MState c → ℝ := fun σB τC =>
    sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha
  let supRaw : S → ℝ := fun σB => sSup (Set.range fun τC : MState c => raw σB τC)
  let infRaw : MState c → ℝ := fun τC => sInf (Set.range fun σB : S => raw σB τC)
  have : Nonempty S := ⟨⟨(MState.uniform : MState b), MState.uniform_posDef⟩⟩
  have : Nonempty (MState c) := ⟨(MState.uniform : MState c)⟩
  have hrawBddAbove (σB : S) :
      BddAbove (Set.range fun τC : MState c => raw σB τC) := by
    refine ⟨sSup
      (psdTraceHolderUnitBallValueSet
        (Matrix.traceLeft
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB.1 ψ alpha)))
        (Real.conjExponent alpha)), ?_⟩
    rintro y ⟨τC, rfl⟩
    simpa [raw] using
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup
        rhoA ψ σB.1 τC hrhoA σB.2 halpha
  have hrawBddBelowSigma (τC : MState c) :
      BddBelow (Set.range fun σB : S => raw σB τC) := by
    refine ⟨0, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact sandwichedMutualInformationSionBracketRe_nonneg rhoA ψ σB.1 τC alpha
  have hsupRaw_nonneg (σB : S) : 0 ≤ supRaw σB := by
    exact (sandwichedMutualInformationSionBracketRe_nonneg
      rhoA ψ σB.1 (MState.uniform : MState c) alpha).trans
        (le_csSup (hrawBddAbove σB)
          ⟨(MState.uniform : MState c), by simp [raw]⟩)
  have hsupRawBddBelow : BddBelow (Set.range supRaw) := by
    refine ⟨0, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact hsupRaw_nonneg σB
  have hinfRawBddAbove : BddAbove (Set.range infRaw) := by
    let σ0 : S := ⟨(MState.uniform : MState b), MState.uniform_posDef⟩
    refine ⟨supRaw σ0, ?_⟩
    rintro y ⟨τC, rfl⟩
    have hle_inf : infRaw τC ≤ raw σ0 τC := by
      exact csInf_le (hrawBddBelowSigma τC) ⟨σ0, rfl⟩
    have hle_sup : raw σ0 τC ≤ supRaw σ0 := by
      exact le_csSup (hrawBddAbove σ0) ⟨τC, rfl⟩
    exact hle_inf.trans hle_sup
  have hleftE :
      (⨅ σB : S, ⨆ τC : MState c, (raw σB τC : EReal)) =
        ((sInf (Set.range supRaw) : ℝ) : EReal) := by
    calc
      (⨅ σB : S, ⨆ τC : MState c, (raw σB τC : EReal))
          = ⨅ σB : S, (supRaw σB : EReal) := by
            apply iInf_congr
            intro σB
            exact ereal_sSup_range_coe_eq_coe_real_sSup
              (fun τC : MState c => raw σB τC) (hrawBddAbove σB)
      _ = ((sInf (Set.range supRaw) : ℝ) : EReal) := by
            exact ereal_sInf_range_coe_eq_coe_real_sInf supRaw hsupRawBddBelow
  have hrightE :
      (⨆ τC : MState c, ⨅ σB : S, (raw σB τC : EReal)) =
        ((sSup (Set.range infRaw) : ℝ) : EReal) := by
    calc
      (⨆ τC : MState c, ⨅ σB : S, (raw σB τC : EReal))
          = ⨆ τC : MState c, (infRaw τC : EReal) := by
            apply iSup_congr
            intro τC
            exact ereal_sInf_range_coe_eq_coe_real_sInf
              (fun σB : S => raw σB τC) (hrawBddBelowSigma τC)
      _ = ((sSup (Set.range infRaw) : ℝ) : EReal) := by
            exact ereal_sSup_range_coe_eq_coe_real_sSup infRaw hinfRawBddAbove
  have hSion := sandwichedAlpha_fullRank_sion_mutualInformationBracket_EReal
    rhoA ψ halpha
  have hE :
      ((sInf (Set.range supRaw) : ℝ) : EReal) =
        ((sSup (Set.range infRaw) : ℝ) : EReal) := by
    rw [← hleftE, ← hrightE]
    simpa [S, raw] using hSion
  exact EReal.coe_eq_coe_iff.mp hE

/-- Support-convention real-valued form of the full-rank Sion exchange for the
KW sandwiched mutual-information bracket.

This removes the old full-rank assumption on the fixed source marginal
`rho_A`.  The proof is the same EReal Sion wrapper as
`sandwichedMutualInformationSionBracketRe_real_sInf_sSup_eq_sSup_sInf`, with
the raw upper bound supplied by the support-convention Holder bridge. -/
theorem sandwichedMutualInformationSionBracketRe_real_sInf_sSup_eq_sSup_sInf_of_side_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    sInf (Set.range fun σB : {σ : MState b // σ.m.PosDef} =>
      sSup (Set.range fun τC : MState c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha)) =
      sSup (Set.range fun τC : MState c =>
        sInf (Set.range fun σB : {σ : MState b // σ.m.PosDef} =>
          sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha)) := by
  let S := {σ : MState b // σ.m.PosDef}
  let raw : S → MState c → ℝ := fun σB τC =>
    sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha
  let supRaw : S → ℝ := fun σB => sSup (Set.range fun τC : MState c => raw σB τC)
  let infRaw : MState c → ℝ := fun τC => sInf (Set.range fun σB : S => raw σB τC)
  have : Nonempty S := ⟨⟨(MState.uniform : MState b), MState.uniform_posDef⟩⟩
  have : Nonempty (MState c) := ⟨(MState.uniform : MState c)⟩
  have hrawBddAbove (σB : S) :
      BddAbove (Set.range fun τC : MState c => raw σB τC) := by
    refine ⟨sSup
      (psdTraceHolderUnitBallValueSet
        (Matrix.traceLeft
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB.1 ψ alpha)))
        (Real.conjExponent alpha)), ?_⟩
    rintro y ⟨τC, rfl⟩
    simpa [raw] using
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup_of_side_posDef
        rhoA ψ σB.1 τC σB.2 halpha
  have hrawBddBelowSigma (τC : MState c) :
      BddBelow (Set.range fun σB : S => raw σB τC) := by
    refine ⟨0, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact sandwichedMutualInformationSionBracketRe_nonneg rhoA ψ σB.1 τC alpha
  have hsupRaw_nonneg (σB : S) : 0 ≤ supRaw σB := by
    exact (sandwichedMutualInformationSionBracketRe_nonneg
      rhoA ψ σB.1 (MState.uniform : MState c) alpha).trans
        (le_csSup (hrawBddAbove σB)
          ⟨(MState.uniform : MState c), by simp [raw]⟩)
  have hsupRawBddBelow : BddBelow (Set.range supRaw) := by
    refine ⟨0, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact hsupRaw_nonneg σB
  have hinfRawBddAbove : BddAbove (Set.range infRaw) := by
    let σ0 : S := ⟨(MState.uniform : MState b), MState.uniform_posDef⟩
    refine ⟨supRaw σ0, ?_⟩
    rintro y ⟨τC, rfl⟩
    have hle_inf : infRaw τC ≤ raw σ0 τC := by
      exact csInf_le (hrawBddBelowSigma τC) ⟨σ0, rfl⟩
    have hle_sup : raw σ0 τC ≤ supRaw σ0 := by
      exact le_csSup (hrawBddAbove σ0) ⟨τC, rfl⟩
    exact hle_inf.trans hle_sup
  have hleftE :
      (⨅ σB : S, ⨆ τC : MState c, (raw σB τC : EReal)) =
        ((sInf (Set.range supRaw) : ℝ) : EReal) := by
    calc
      (⨅ σB : S, ⨆ τC : MState c, (raw σB τC : EReal))
          = ⨅ σB : S, (supRaw σB : EReal) := by
            apply iInf_congr
            intro σB
            exact ereal_sSup_range_coe_eq_coe_real_sSup
              (fun τC : MState c => raw σB τC) (hrawBddAbove σB)
      _ = ((sInf (Set.range supRaw) : ℝ) : EReal) := by
            exact ereal_sInf_range_coe_eq_coe_real_sInf supRaw hsupRawBddBelow
  have hrightE :
      (⨆ τC : MState c, ⨅ σB : S, (raw σB τC : EReal)) =
        ((sSup (Set.range infRaw) : ℝ) : EReal) := by
    calc
      (⨆ τC : MState c, ⨅ σB : S, (raw σB τC : EReal))
          = ⨆ τC : MState c, (infRaw τC : EReal) := by
            apply iSup_congr
            intro τC
            exact ereal_sInf_range_coe_eq_coe_real_sInf
              (fun σB : S => raw σB τC) (hrawBddBelowSigma τC)
      _ = ((sSup (Set.range infRaw) : ℝ) : EReal) := by
            exact ereal_sSup_range_coe_eq_coe_real_sSup infRaw hinfRawBddAbove
  have hSion := sandwichedAlpha_fullRank_sion_mutualInformationBracket_EReal
    rhoA ψ halpha
  have hE :
      ((sInf (Set.range supRaw) : ℝ) : EReal) =
        ((sSup (Set.range infRaw) : ℝ) : EReal) := by
    rw [← hleftE, ← hrightE]
    simpa [S, raw] using hSion
  exact EReal.coe_eq_coe_iff.mp hE

/-- Post-Sion logarithmic form of the KW state alternate expression.

This combines the pre-Sion logarithmic transport with the source Sion exchange,
leaving only the fixed-`tau_C` reverse-Holder replacement of the inner
`sigma_B` infimum. -/
theorem sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_sInf_sionBracketRe
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : Ket ((a × b) × c))
    (hAB : ψ.state.marginalAB.m.PosDef)
    (hA : ψ.state.marginalAB.traceRight.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      ((alpha / (alpha - 1) *
        log2
          (sSup (Set.range fun τC : MState c =>
            sInf (Set.range fun σB : {σ : MState b // σ.m.PosDef} =>
              sandwichedMutualInformationSionBracketRe
                ψ.state.marginalAB.traceRight ψ σB.1 τC alpha))) : ℝ) : EReal) := by
  rw [sandwichedRenyiMutualInformationE_eq_coeff_log2_sInf_sSup_sionBracketRe
    ψ hAB hA halpha]
  rw [sandwichedMutualInformationSionBracketRe_real_sInf_sSup_eq_sSup_sInf
    ψ.state.marginalAB.traceRight ψ hA halpha]

/-- Support-convention post-Sion logarithmic form of the KW state alternate
expression. -/
theorem sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_sInf_sionBracketRe_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : Ket ((a × b) × c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      ((alpha / (alpha - 1) *
        log2
          (sSup (Set.range fun τC : MState c =>
            sInf (Set.range fun σB : {σ : MState b // σ.m.PosDef} =>
              sandwichedMutualInformationSionBracketRe
                ψ.state.marginalAB.traceRight ψ σB.1 τC alpha))) : ℝ) : EReal) := by
  rw [sandwichedRenyiMutualInformationE_eq_coeff_log2_sInf_sSup_sionBracketRe_support
    ψ halpha]
  rw [sandwichedMutualInformationSionBracketRe_real_sInf_sSup_eq_sSup_sInf_of_side_posDef
    ψ.state.marginalAB.traceRight ψ halpha]

/-- Reverse-Holder replacement of the post-Sion inner infimum in the KW state
alternate expression.

This is the source formula after `EA_capacity.tex:2030-2035`, before deciding
whether to state the final `tau_C` optimization over all side states or the
full-rank dense subdomain used for logarithmic product splitting. -/
theorem sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_ACTraceMatrixNorm
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : Ket ((a × b) × c))
    (hAB : ψ.state.marginalAB.m.PosDef)
    (hA : ψ.state.marginalAB.traceRight.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      ((alpha / (alpha - 1) *
        log2
          (sSup (Set.range fun τC : MState c =>
            psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix
                ψ.state.marginalAB.traceRight ψ τC alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef
                ψ.state.marginalAB.traceRight ψ τC alpha)
              (sandwichedAlternateSchattenOrder halpha))) : ℝ) : EReal) := by
  rw [sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_sInf_sionBracketRe
    ψ hAB hA halpha]
  have hsets :
      Set.range (fun τC : MState c =>
        sInf (Set.range fun σB : {σ : MState b // σ.m.PosDef} =>
          sandwichedMutualInformationSionBracketRe
            ψ.state.marginalAB.traceRight ψ σB.1 τC alpha)) =
        Set.range (fun τC : MState c =>
          psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix
              ψ.state.marginalAB.traceRight ψ τC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              ψ.state.marginalAB.traceRight ψ τC alpha)
            (sandwichedAlternateSchattenOrder halpha)) := by
    ext x
    constructor
    · rintro ⟨τC, rfl⟩
      exact ⟨τC, by
        exact (sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
          ψ.state.marginalAB.traceRight ψ τC halpha).symm⟩
    · rintro ⟨τC, rfl⟩
      exact ⟨τC, by
        exact sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
          ψ.state.marginalAB.traceRight ψ τC halpha⟩
  rw [hsets]

/-- Support-convention reverse-Holder replacement of the post-Sion inner
infimum in the KW state alternate expression.

This is the singular-state version of
`sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_ACTraceMatrixNorm`, matching
KW `EA_capacity.tex:1193-1214` and `2030-2035`. -/
theorem sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_ACTraceMatrixNorm_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : Ket ((a × b) × c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
      ((alpha / (alpha - 1) *
        log2
          (sSup (Set.range fun τC : MState c =>
            psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix
                ψ.state.marginalAB.traceRight ψ τC alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef
                ψ.state.marginalAB.traceRight ψ τC alpha)
              (sandwichedAlternateSchattenOrder halpha))) : ℝ) : EReal) := by
  rw [sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_sInf_sionBracketRe_support
    ψ halpha]
  have hsets :
      Set.range (fun τC : MState c =>
        sInf (Set.range fun σB : {σ : MState b // σ.m.PosDef} =>
          sandwichedMutualInformationSionBracketRe
            ψ.state.marginalAB.traceRight ψ σB.1 τC alpha)) =
        Set.range (fun τC : MState c =>
          psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix
              ψ.state.marginalAB.traceRight ψ τC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              ψ.state.marginalAB.traceRight ψ τC alpha)
            (sandwichedAlternateSchattenOrder halpha)) := by
    ext x
    constructor
    · rintro ⟨τC, rfl⟩
      exact ⟨τC, by
        exact (sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
          ψ.state.marginalAB.traceRight ψ τC halpha).symm⟩
    · rintro ⟨τC, rfl⟩
      exact ⟨τC, by
        exact sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
          ψ.state.marginalAB.traceRight ψ τC halpha⟩
  rw [hsets]

/-- The all-state `tau_C` norm branch in the KW alternate expression is
bounded above.

For a fixed full-rank `sigma_B`, reverse Holder identifies the norm with an
infimum over `sigma_B`, and the pointwise Sion bracket is bounded by the
Holder unit-ball supremum. -/
theorem psdSchattenPNorm_ACTraceMatrix_bddAbove
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (hrhoA : rhoA.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    BddAbove (Set.range fun τC : MState c =>
      psdSchattenPNorm
        (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
        (sandwichedAlternateSchattenOrder halpha)) := by
  let σ0 : {σ : MState b // σ.m.PosDef} :=
    ⟨(MState.uniform : MState b), MState.uniform_posDef⟩
  let M : CMatrix c :=
    Matrix.traceLeft
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σ0.1 ψ alpha))
  let holder : ℝ :=
    sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha))
  refine ⟨holder, ?_⟩
  rintro y ⟨τC, rfl⟩
  let raw : {σ : MState b // σ.m.PosDef} → ℝ := fun σB =>
    sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha
  have hrawBelow : BddBelow (Set.range raw) := by
    refine ⟨0, ?_⟩
    rintro z ⟨σB, rfl⟩
    exact sandwichedMutualInformationSionBracketRe_nonneg rhoA ψ σB.1 τC alpha
  have hnorm_eq :
      psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
          (sandwichedAlternateSchattenOrder halpha) =
        sInf (Set.range raw) := by
    simpa [raw] using
      (sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
        rhoA ψ τC halpha).symm
  have hinf_le : sInf (Set.range raw) ≤ raw σ0 :=
    csInf_le hrawBelow ⟨σ0, rfl⟩
  have hraw_le_holder : raw σ0 ≤ holder := by
    simpa [raw, M, holder] using
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup
        rhoA ψ σ0.1 τC hrhoA σ0.2 halpha
  change
    psdSchattenPNorm
        (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
        (sandwichedAlternateSchattenOrder halpha) ≤ holder
  rw [hnorm_eq]
  exact hinf_le.trans hraw_le_holder

/-- Support-convention boundedness of the all-state `tau_C` norm branch in the
KW alternate expression.

This is the same boundedness argument as
`psdSchattenPNorm_ACTraceMatrix_bddAbove`, but with the Holder upper bound
supplied by the support-convention branch.  It is the boundedness side
condition needed for the singular-state product lower bound in
`EA_capacity.tex:1193-1214`. -/
theorem psdSchattenPNorm_ACTraceMatrix_bddAbove_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    BddAbove (Set.range fun τC : MState c =>
      psdSchattenPNorm
        (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
        (sandwichedAlternateSchattenOrder halpha)) := by
  let σ0 : {σ : MState b // σ.m.PosDef} :=
    ⟨(MState.uniform : MState b), MState.uniform_posDef⟩
  let M : CMatrix c :=
    Matrix.traceLeft
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σ0.1 ψ alpha))
  let holder : ℝ :=
    sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha))
  refine ⟨holder, ?_⟩
  rintro y ⟨τC, rfl⟩
  let raw : {σ : MState b // σ.m.PosDef} → ℝ := fun σB =>
    sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha
  have hrawBelow : BddBelow (Set.range raw) := by
    refine ⟨0, ?_⟩
    rintro z ⟨σB, rfl⟩
    exact sandwichedMutualInformationSionBracketRe_nonneg rhoA ψ σB.1 τC alpha
  have hnorm_eq :
      psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
          (sandwichedAlternateSchattenOrder halpha) =
        sInf (Set.range raw) := by
    simpa [raw] using
      (sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
        rhoA ψ τC halpha).symm
  have hinf_le : sInf (Set.range raw) ≤ raw σ0 :=
    csInf_le hrawBelow ⟨σ0, rfl⟩
  have hraw_le_holder : raw σ0 ≤ holder := by
    simpa [raw, M, holder] using
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup_of_side_posDef
        rhoA ψ σ0.1 τC σ0.2 halpha
  change
    psdSchattenPNorm
        (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
        (sandwichedAlternateSchattenOrder halpha) ≤ holder
  rw [hnorm_eq]
  exact hinf_le.trans hraw_le_holder

/-- The support-convention `AC` trace-matrix norm branch has supremum at least
one.

This is the scalar positivity needed for the logarithmic product split in
KW `EA_capacity.tex:1208-1214`.  It follows from the full-rank side-state
support branch (`sup_tau ≥ 1`), the Sion exchange, and the reverse-Holder
identification of the post-Sion inner infimum with the `AC` Schatten norm. -/
theorem one_le_sSup_ACTraceMatrixNorm_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : Ket ((a × b) × c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    1 ≤ sSup (Set.range fun τC : MState c =>
      psdSchattenPNorm
        (sandwichedMutualInformationACTraceMatrix
          ψ.state.marginalAB.traceRight ψ τC alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef
          ψ.state.marginalAB.traceRight ψ τC alpha)
        (sandwichedAlternateSchattenOrder halpha)) := by
  let S := {σ : MState b // σ.m.PosDef}
  let raw : S → MState c → ℝ := fun σB τC =>
    sandwichedMutualInformationSionBracketRe
      ψ.state.marginalAB.traceRight ψ σB.1 τC alpha
  let supRaw : S → ℝ := fun σB => sSup (Set.range fun τC : MState c => raw σB τC)
  let infRaw : MState c → ℝ := fun τC => sInf (Set.range fun σB : S => raw σB τC)
  let F : MState c → ℝ := fun τC =>
    psdSchattenPNorm
      (sandwichedMutualInformationACTraceMatrix
        ψ.state.marginalAB.traceRight ψ τC alpha)
      (sandwichedMutualInformationACTraceMatrix_posSemidef
        ψ.state.marginalAB.traceRight ψ τC alpha)
      (sandwichedAlternateSchattenOrder halpha)
  have : Nonempty S := ⟨⟨(MState.uniform : MState b), MState.uniform_posDef⟩⟩
  have hsup_one (σB : S) : 1 ≤ supRaw σB := by
    simpa [supRaw, raw] using
      one_le_sandwichedMutualInformationSionBracketRe_sSup_of_side_posDef
        ψ σB.1 σB.2 halpha
  have hsion :
      sInf (Set.range supRaw) = sSup (Set.range infRaw) := by
    simpa [supRaw, infRaw, raw, S] using
      sandwichedMutualInformationSionBracketRe_real_sInf_sSup_eq_sSup_sInf_of_side_posDef
        ψ.state.marginalAB.traceRight ψ halpha
  have hleft : 1 ≤ sInf (Set.range supRaw) := by
    refine le_csInf (Set.range_nonempty supRaw) ?_
    rintro y ⟨σB, rfl⟩
    exact hsup_one σB
  have hsets : Set.range infRaw = Set.range F := by
    ext x
    constructor
    · rintro ⟨τC, rfl⟩
      exact ⟨τC, by
        exact (sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
          ψ.state.marginalAB.traceRight ψ τC halpha).symm⟩
    · rintro ⟨τC, rfl⟩
      exact ⟨τC, by
        exact sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
          ψ.state.marginalAB.traceRight ψ τC halpha⟩
  rw [hsion, hsets] at hleft
  simpa [F] using hleft

/-- Product-purification lower bound from the KW all-state alternate
expression.

This is the missing reverse half of the state product argument on the
source-shaped purification branch: restrict the product-side `tau_C`
optimization to product states, use the `AC` trace-matrix product identity and
Schatten-norm multiplicativity, then split the logarithm of the product
supremum. -/
theorem sandwichedRenyiMutualInformationE_bipartiteProductPurification_ge_add
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1] [Nonempty b1]
    [Fintype c1] [DecidableEq c1] [Nonempty c1]
    [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2] [Nonempty b2]
    [Fintype c2] [DecidableEq c2] [Nonempty c2]
    (ψ : Ket ((a1 × b1) × c1))
    (φ : Ket ((a2 × b2) × c2))
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha +
        φ.state.marginalAB.sandwichedRenyiMutualInformationE alpha ≤
      (bipartiteProductPurification ψ φ).state.marginalAB.sandwichedRenyiMutualInformationE
        alpha := by
  let Fψ : MState c1 → ℝ := fun τC =>
    psdSchattenPNorm
      (sandwichedMutualInformationACTraceMatrix
        ψ.state.marginalAB.traceRight ψ τC alpha)
      (sandwichedMutualInformationACTraceMatrix_posSemidef
        ψ.state.marginalAB.traceRight ψ τC alpha)
      (sandwichedAlternateSchattenOrder halpha)
  let Fφ : MState c2 → ℝ := fun τC =>
    psdSchattenPNorm
      (sandwichedMutualInformationACTraceMatrix
        φ.state.marginalAB.traceRight φ τC alpha)
      (sandwichedMutualInformationACTraceMatrix_posSemidef
        φ.state.marginalAB.traceRight φ τC alpha)
      (sandwichedAlternateSchattenOrder halpha)
  let ψφ := bipartiteProductPurification ψ φ
  let rhoProdA : MState (a1 × a2) :=
    ψ.state.marginalAB.traceRight.prod φ.state.marginalAB.traceRight
  let Fprod : MState (c1 × c2) → ℝ := fun τC =>
    psdSchattenPNorm
      (sandwichedMutualInformationACTraceMatrix
        rhoProdA ψφ τC alpha)
      (sandwichedMutualInformationACTraceMatrix_posSemidef
        rhoProdA ψφ τC alpha)
      (sandwichedAlternateSchattenOrder halpha)
  have hψφA :
      ψφ.state.marginalAB.traceRight =
        ψ.state.marginalAB.traceRight.prod φ.state.marginalAB.traceRight := by
    dsimp [ψφ]
    exact bipartiteProductPurification_traceRight ψ φ
  have hψφA_unfolded :
      ψφ.state.traceRight.traceRight =
        ψ.state.traceRight.traceRight.prod φ.state.traceRight.traceRight := by
    simpa using hψφA
  have hFψBdd : BddAbove (Set.range Fψ) := by
    simpa [Fψ] using
      psdSchattenPNorm_ACTraceMatrix_bddAbove_support
        ψ.state.marginalAB.traceRight ψ halpha
  have hFφBdd : BddAbove (Set.range Fφ) := by
    simpa [Fφ] using
      psdSchattenPNorm_ACTraceMatrix_bddAbove_support
        φ.state.marginalAB.traceRight φ halpha
  have hFprodBdd : BddAbove (Set.range Fprod) := by
    simpa [Fprod, ψφ] using
      psdSchattenPNorm_ACTraceMatrix_bddAbove_support
        rhoProdA ψφ halpha
  have hFψ_nonneg : ∀ τC : MState c1, 0 ≤ Fψ τC := by
    intro τC
    exact psdSchattenPNorm_nonneg _ _ _
  have hFφ_nonneg : ∀ τC : MState c2, 0 ≤ Fφ τC := by
    intro τC
    exact psdSchattenPNorm_nonneg _ _ _
  have hFψ_sup_pos : 0 < sSup (Set.range Fψ) := by
    exact zero_lt_one.trans_le (by
      simpa [Fψ] using one_le_sSup_ACTraceMatrixNorm_support ψ halpha)
  have hFφ_sup_pos : 0 < sSup (Set.range Fφ) := by
    exact zero_lt_one.trans_le (by
      simpa [Fφ] using one_le_sSup_ACTraceMatrixNorm_support φ halpha)
  have : Nonempty (MState c1) := ⟨(MState.uniform : MState c1)⟩
  have : Nonempty (MState c2) := ⟨(MState.uniform : MState c2)⟩
  let Fpair : MState c1 × MState c2 → ℝ := fun p => Fψ p.1 * Fφ p.2
  have hFpairBdd : BddAbove (Set.range Fpair) := by
    refine ⟨sSup (Set.range Fprod), ?_⟩
    rintro y ⟨p, rfl⟩
    have hpoint : Fprod (p.1.prod p.2) = Fpair p := by
      dsimp [Fprod, Fpair, Fψ, Fφ, rhoProdA]
      exact
        psdSchattenPNorm_ACTraceMatrix_bipartiteProductPurification_prod
          ψ.state.marginalAB.traceRight φ.state.marginalAB.traceRight
          ψ φ p.1 p.2 halpha
    exact le_csSup hFprodBdd ⟨p.1.prod p.2, by simp [hpoint]⟩
  have hFpair_log :
      log2 (sSup (Set.range Fpair)) =
        log2 (sSup (Set.range Fψ)) + log2 (sSup (Set.range Fφ)) := by
    simpa [Fpair] using
      real_log2_sSup_range_prod_mul_eq_add_of_nonneg
        Fψ Fφ hFψ_nonneg hFφ_nonneg hFpairBdd hFψ_sup_pos hFφ_sup_pos
  have hFpair_le_prod : sSup (Set.range Fpair) ≤ sSup (Set.range Fprod) := by
    refine csSup_le (Set.range_nonempty _) ?_
    rintro y ⟨p, rfl⟩
    have hpoint : Fprod (p.1.prod p.2) = Fpair p := by
      dsimp [Fprod, Fpair, Fψ, Fφ, rhoProdA]
      exact
        psdSchattenPNorm_ACTraceMatrix_bipartiteProductPurification_prod
          ψ.state.marginalAB.traceRight φ.state.marginalAB.traceRight
          ψ φ p.1 p.2 halpha
    exact le_csSup hFprodBdd ⟨p.1.prod p.2, by simp [hpoint]⟩
  have hFpair_pos : 0 < sSup (Set.range Fpair) := by
    rw [real_sSup_range_prod_mul_eq_mul_sSup_range_of_nonneg
      Fψ Fφ hFψ_nonneg hFφ_nonneg hFpairBdd]
    exact mul_pos hFψ_sup_pos hFφ_sup_pos
  have hlog_le :
      log2 (sSup (Set.range Fψ)) + log2 (sSup (Set.range Fφ)) ≤
        log2 (sSup (Set.range Fprod)) := by
    rw [← hFpair_log]
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hFpair_pos hFpair_le_prod)
      (le_of_lt (Real.log_pos one_lt_two))
  have hψ :
      ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
        ((alpha / (alpha - 1) * log2 (sSup (Set.range Fψ)) : ℝ) : EReal) := by
    simpa [Fψ] using
      sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_ACTraceMatrixNorm_support
        ψ halpha
  have hφ :
      φ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
        ((alpha / (alpha - 1) * log2 (sSup (Set.range Fφ)) : ℝ) : EReal) := by
    simpa [Fφ] using
      sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_ACTraceMatrixNorm_support
        φ halpha
  have hprod :
      ψφ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
        ((alpha / (alpha - 1) * log2 (sSup (Set.range Fprod)) : ℝ) : EReal) := by
    simpa [Fprod, rhoProdA, hψφA_unfolded] using
      sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_ACTraceMatrixNorm_support
        ψφ halpha
  rw [hψ, hφ, hprod]
  rw [← EReal.coe_add]
  exact EReal.coe_le_coe_iff.mpr
    (by
      have hcoeff_nonneg : 0 ≤ alpha / (alpha - 1) :=
        le_of_lt (highAlpha_conjExponent_pos halpha)
      nlinarith [mul_le_mul_of_nonneg_left hlog_le hcoeff_nonneg])

/-- KW `EA_capacity.tex:2010-2018`: after the Holder unit-ball variational
formula, each full-rank `sigma_B` branch is bounded by optimizing the source
Sion bracket over purifying states `tau_C`.

This is the source-shaped bridge from `inf_sigma sup_B` to
`inf_sigma sup_tau`.  It deliberately stops before the Sion exchange/removal of
the compact full-support regularization. -/
theorem sandwichedRenyiMutualInformationE_le_sInf_fullRank_sSup_sionBracketLog
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : Ket ((a × b) × c))
    (hAB : ψ.state.marginalAB.m.PosDef)
    (hA : ψ.state.marginalAB.traceRight.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha ≤
      sInf (Set.range fun σB : {σ : MState b // σ.m.PosDef} =>
        ((alpha / (alpha - 1) *
          log2
            (sSup (Set.range fun τC : MState c =>
              sandwichedMutualInformationSionBracketRe
                ψ.state.marginalAB.traceRight ψ σB.1 τC alpha)) : ℝ) : EReal)) := by
  let S := {σ : MState b // σ.m.PosDef}
  have : Nonempty S := ⟨⟨(MState.uniform : MState b), MState.uniform_posDef⟩⟩
  let holder : S → ℝ := fun σB =>
    alpha / (alpha - 1) *
      log2
        (sSup
          (psdTraceHolderUnitBallValueSet
            (Matrix.traceLeft
              (rankOneMatrix
                (sandwichedMutualInformationWeightedPurificationAmp
                  ψ.state.marginalAB.traceRight σB.1 ψ alpha)))
            (Real.conjExponent alpha)))
  let bracket : S → ℝ := fun σB =>
    alpha / (alpha - 1) *
      log2
        (sSup (Set.range fun τC : MState c =>
          sandwichedMutualInformationSionBracketRe
            ψ.state.marginalAB.traceRight ψ σB.1 τC alpha))
  have hpoint : ∀ σB : S, holder σB ≤ bracket σB := by
    intro σB
    let M : CMatrix c :=
      Matrix.traceLeft
        (rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp
            ψ.state.marginalAB.traceRight σB.1 ψ alpha))
    let hM : M.PosSemidef :=
      traceLeft_posSemidef
        (rankOneMatrix_pos
          (sandwichedMutualInformationWeightedPurificationAmp
            ψ.state.marginalAB.traceRight σB.1 ψ alpha))
    have hholder_eq :
        sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) =
          psdSchattenPNorm M hM (SchattenOrder.ofOneLt halpha) := by
      exact psdTraceHolderUnitBall_sSup_eq
        (M := M) hM (p := alpha) (q := Real.conjExponent alpha)
        (Real.HolderConjugate.conjExponent halpha)
    have hholder_pos :
        0 < sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) := by
      rw [hholder_eq]
      have href_pos :
          0 <
            psdTracePower
              (MState.sandwichedRenyiReferenceInner ψ.state.marginalAB
                (ψ.state.marginalAB.traceRight.prod σB.1).m alpha)
              (MState.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
                (MState.PosDef.kron hA σB.2).posSemidef alpha)
              alpha :=
        MState.sandwichedRenyiReferenceInner_psdTracePower_pos ψ.state.marginalAB hAB
          (MState.PosDef.kron hA σB.2) alpha
      have hnorm_pos :
          0 <
            psdSchattenPNorm
              (MState.sandwichedRenyiReferenceInner ψ.state.marginalAB
                (ψ.state.marginalAB.traceRight.prod σB.1).m alpha)
              (MState.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
                (MState.PosDef.kron hA σB.2).posSemidef alpha)
              (SchattenOrder.ofOneLt halpha) := by
        unfold psdSchattenPNorm
        exact Real.rpow_pos_of_pos href_pos (1 / alpha)
      simpa [M, hM] using
        (hnorm_pos.trans_eq
          (psdSchattenPNorm_referenceInner_eq_weightedPurification_traceLeft
            σB.1 ψ hA σB.2 alpha (lt_trans zero_lt_one halpha)))
    have hle :
        sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha)) ≤
          sSup (Set.range fun τC : MState c =>
            sandwichedMutualInformationSionBracketRe
              ψ.state.marginalAB.traceRight ψ σB.1 τC alpha) := by
      simpa [M] using
        weightedPurification_holderUnitBall_sSup_le_sandwichedMutualInformationSionBracketRe_sSup
          ψ.state.marginalAB.traceRight ψ σB.1 hA σB.2 halpha
    have hlog :
        log2 (sSup (psdTraceHolderUnitBallValueSet M (Real.conjExponent alpha))) ≤
          log2 (sSup (Set.range fun τC : MState c =>
            sandwichedMutualInformationSionBracketRe
              ψ.state.marginalAB.traceRight ψ σB.1 τC alpha)) := by
      unfold log2
      exact div_le_div_of_nonneg_right
        (Real.log_le_log hholder_pos hle)
        (le_of_lt (Real.log_pos one_lt_two))
    exact mul_le_mul_of_nonneg_left hlog (le_of_lt (highAlpha_conjExponent_pos halpha))
  have hfBelow : BddBelow (Set.range holder) := by
    have hfCandidate :
        BddBelow (Set.range fun σB : S =>
          MState.sandwichedRenyiMutualInformationCandidateRealPosDef
            ψ.state.marginalAB σB.1 hAB hA σB.2 alpha halpha) := by
      simpa [S] using
        MState.sandwichedRenyiMutualInformationCandidateRealPosDef_bddBelow
          ψ.state.marginalAB hAB hA halpha
    have hholder_eq_candidate :
        holder =
          (fun σB : S =>
            MState.sandwichedRenyiMutualInformationCandidateRealPosDef
              ψ.state.marginalAB σB.1 hAB hA σB.2 alpha halpha) := by
      funext σB
      simpa [holder] using
        (sandwichedRenyiMutualInformationCandidateRealPosDef_eq_holderUnitBall_sSup
          σB.1 ψ hAB hA σB.2 halpha).symm
    simpa [hholder_eq_candidate] using hfCandidate
  have hgBelow : BddBelow (Set.range bracket) := by
    rcases hfBelow with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact (hC ⟨σB, rfl⟩).trans (hpoint σB)
  have hinf_le : sInf (Set.range holder) ≤ sInf (Set.range bracket) := by
    refine le_csInf (Set.range_nonempty _) ?_
    rintro y ⟨σB, rfl⟩
    exact (csInf_le hfBelow ⟨σB, rfl⟩).trans (hpoint σB)
  have hstate :
      ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range holder) : ℝ) : EReal) := by
    rw [sandwichedRenyiMutualInformationE_eq_sInf_fullRank_holderUnitBall_sSup
      ψ hAB hA halpha]
    change sInf (Set.range fun σB : S => (holder σB : EReal)) =
      ((sInf (Set.range holder) : ℝ) : EReal)
    exact ereal_sInf_range_coe_eq_coe_real_sInf holder hfBelow
  rw [hstate]
  change ((sInf (Set.range holder) : ℝ) : EReal) ≤
    sInf (Set.range fun σB : S => (bracket σB : EReal))
  rw [ereal_sInf_range_coe_eq_coe_real_sInf bracket hgBelow]
  exact EReal.coe_le_coe_iff.mpr hinf_le

/-- A fixed full-rank `tau_C` value in the KW `AC` trace-matrix alternate
expression is bounded above by the optimized state sandwiched-Renyi mutual
information.

This is the one-sided closure obtained by following
KW `EA_capacity.tex:2006-2035`: Holder variational form, Sion bracket, and
reverse Holder.  It does not replace the remaining equality/approximation
direction of the full alternate-expression lemma. -/
theorem sandwichedACTraceMatrixLog_le_sandwichedRenyiMutualInformationE_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (ψ : Ket ((a × b) × c))
    (τC : MState c)
    (hAB : ψ.state.marginalAB.m.PosDef)
    (hA : ψ.state.marginalAB.traceRight.m.PosDef)
    (hτC : τC.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    ((alpha / (alpha - 1) *
      log2
        (psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix
            ψ.state.marginalAB.traceRight ψ τC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef
            ψ.state.marginalAB.traceRight ψ τC alpha)
          (sandwichedAlternateSchattenOrder halpha)) : ℝ) : EReal) ≤
      ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha := by
  let S := {σ : MState b // σ.m.PosDef}
  let acLog : ℝ :=
    alpha / (alpha - 1) *
      log2
        (psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix
            ψ.state.marginalAB.traceRight ψ τC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef
            ψ.state.marginalAB.traceRight ψ τC alpha)
          (sandwichedAlternateSchattenOrder halpha))
  let f : S → ℝ := fun σB =>
    alpha / (alpha - 1) *
      log2 (sandwichedMutualInformationSionBracketRe
        ψ.state.marginalAB.traceRight ψ σB.1 τC alpha)
  let g : S → ℝ := fun σB =>
    alpha / (alpha - 1) *
      log2
        (sSup
          (psdTraceHolderUnitBallValueSet
            (Matrix.traceLeft
              (rankOneMatrix
                (sandwichedMutualInformationWeightedPurificationAmp
                  ψ.state.marginalAB.traceRight σB.1 ψ alpha)))
            (Real.conjExponent alpha)))
  have : Nonempty S := ⟨⟨(MState.uniform : MState b), MState.uniform_posDef⟩⟩
  have hAC_le_f (σB : S) : acLog ≤ f σB := by
    simpa [acLog, f, S] using
      sandwichedACTraceMatrixLog_le_SionBracketLog_posDef
        ψ.state.marginalAB.traceRight ψ σB.1 τC hA σB.2 hτC halpha
  have hf_le_g (σB : S) : f σB ≤ g σB := by
    let bracket :=
      sandwichedMutualInformationSionBracketRe
        ψ.state.marginalAB.traceRight ψ σB.1 τC alpha
    let holder :=
      sSup
        (psdTraceHolderUnitBallValueSet
          (Matrix.traceLeft
            (rankOneMatrix
              (sandwichedMutualInformationWeightedPurificationAmp
                ψ.state.marginalAB.traceRight σB.1 ψ alpha)))
          (Real.conjExponent alpha))
    have hnorm_pos :
        0 <
          psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix
              ψ.state.marginalAB.traceRight ψ τC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              ψ.state.marginalAB.traceRight ψ τC alpha)
            (sandwichedAlternateSchattenOrder halpha) := by
      simpa using
        psdSchattenPNorm_ACTraceMatrix_pos_posDef
          ψ.state.marginalAB.traceRight ψ τC hA hτC halpha
    have hnorm_le_bracket :
        psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix
              ψ.state.marginalAB.traceRight ψ τC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              ψ.state.marginalAB.traceRight ψ τC alpha)
            (sandwichedAlternateSchattenOrder halpha) ≤ bracket := by
      simpa [bracket] using
        psdSchattenPNorm_ACTraceMatrix_le_SionBracketRe_of_support
          ψ.state.marginalAB.traceRight ψ σB.1 τC halpha
          (Matrix.Supports.of_right_posDef
            (sandwichedMutualInformationACTraceMatrix
              ψ.state.marginalAB.traceRight ψ τC alpha)
            σB.1.m σB.2)
    have hbracket_pos : 0 < bracket := lt_of_lt_of_le hnorm_pos hnorm_le_bracket
    have hbracket_le_holder : bracket ≤ holder := by
      simpa [bracket, holder] using
        sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup
          ψ.state.marginalAB.traceRight ψ σB.1 τC hA σB.2 halpha
    have hlog_le : log2 bracket ≤ log2 holder := by
      unfold log2
      exact div_le_div_of_nonneg_right
        (Real.log_le_log hbracket_pos hbracket_le_holder)
        (le_of_lt (Real.log_pos one_lt_two))
    exact mul_le_mul_of_nonneg_left hlog_le (le_of_lt (highAlpha_conjExponent_pos halpha))
  have hfBelow : BddBelow (Set.range f) := by
    refine ⟨acLog, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact hAC_le_f σB
  have hgBelow : BddBelow (Set.range g) := by
    refine ⟨acLog, ?_⟩
    rintro y ⟨σB, rfl⟩
    exact (hAC_le_f σB).trans (hf_le_g σB)
  have hAC_le_inf_f : acLog ≤ sInf (Set.range f) := by
    exact le_csInf (Set.range_nonempty _) (by
      rintro y ⟨σB, rfl⟩
      exact hAC_le_f σB)
  have hinf_f_le_inf_g : sInf (Set.range f) ≤ sInf (Set.range g) := by
    refine le_csInf (Set.range_nonempty _) ?_
    rintro y ⟨σB, rfl⟩
    exact (csInf_le hfBelow ⟨σB, rfl⟩).trans (hf_le_g σB)
  have hAC_le_inf_g : acLog ≤ sInf (Set.range g) :=
    hAC_le_inf_f.trans hinf_f_le_inf_g
  have hstate :
      ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range g) : ℝ) : EReal) := by
    rw [sandwichedRenyiMutualInformationE_eq_sInf_fullRank_holderUnitBall_sSup
      ψ hAB hA halpha]
    have hgfun :
        (fun σB : S => (g σB : EReal)) =
          (fun σB : {σ : MState b // σ.m.PosDef} =>
            ((alpha / (alpha - 1) *
              log2
                (sSup
                  (psdTraceHolderUnitBallValueSet
                    (Matrix.traceLeft
                      (rankOneMatrix
                        (sandwichedMutualInformationWeightedPurificationAmp
                          ψ.state.marginalAB.traceRight σB.1 ψ alpha)))
                    (Real.conjExponent alpha))) : ℝ) : EReal)) := by
      funext σB
      rfl
    change sInf (Set.range fun σB : S => (g σB : EReal)) =
      ((sInf (Set.range g) : ℝ) : EReal)
    exact ereal_sInf_range_coe_eq_coe_real_sInf g hgBelow
  rw [hstate]
  exact EReal.coe_le_coe_iff.mpr hAC_le_inf_g

/-- The KW `AC` trace-matrix logarithmic objective over full-rank purifying
side states is bounded above by a real number.

The bound is obtained from the already source-shaped direction
`ACLog tau_C ≤ I~_alpha(A;B)` and the full-rank real branch of the
state sandwiched-Renyi mutual information. -/
theorem sandwichedACTraceMatrixLog_fullRank_bddAbove
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : Ket ((a × b) × c))
    (hAB : ψ.state.marginalAB.m.PosDef)
    (hA : ψ.state.marginalAB.traceRight.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    BddAbove (Set.range fun τC : {τ : MState c // τ.m.PosDef} =>
      alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix
              ψ.state.marginalAB.traceRight ψ τC.1 alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              ψ.state.marginalAB.traceRight ψ τC.1 alpha)
            (sandwichedAlternateSchattenOrder halpha))) := by
  let S := {σ : MState b // σ.m.PosDef}
  have : Nonempty S := ⟨(MState.uniform : MState b), MState.uniform_posDef⟩
  let f : S → ℝ := fun σB =>
    MState.sandwichedRenyiMutualInformationCandidateRealPosDef
      ψ.state.marginalAB σB.1 hAB hA σB.2 alpha halpha
  have hfBelow : BddBelow (Set.range f) := by
    simpa [S, f] using
      MState.sandwichedRenyiMutualInformationCandidateRealPosDef_bddBelow
        ψ.state.marginalAB hAB hA halpha
  have hstate :
      ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range f) : ℝ) : EReal) := by
    rw [MState.sandwichedRenyiMutualInformationE_eq_sInf_fullRankCandidateReal
      ψ.state.marginalAB hAB hA halpha]
    exact ereal_sInf_range_coe_eq_coe_real_sInf f hfBelow
  refine ⟨sInf (Set.range f), ?_⟩
  rintro y ⟨τC, rfl⟩
  have hleE :=
    sandwichedACTraceMatrixLog_le_sandwichedRenyiMutualInformationE_posDef
      ψ τC.1 hAB hA τC.2 halpha
  rw [hstate] at hleE
  exact EReal.coe_le_coe_iff.mp hleE

/-- The full-rank `tau_C` AC-log supremum can be moved through the real-to-`EReal`
coercion once the source-shaped upper bound above is available. -/
theorem sandwichedACTraceMatrixLog_fullRank_ereal_sSup_eq
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : Ket ((a × b) × c))
    (hAB : ψ.state.marginalAB.m.PosDef)
    (hA : ψ.state.marginalAB.traceRight.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sSup (Set.range fun τC : {τ : MState c // τ.m.PosDef} =>
      ((alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix
              ψ.state.marginalAB.traceRight ψ τC.1 alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              ψ.state.marginalAB.traceRight ψ τC.1 alpha)
            (sandwichedAlternateSchattenOrder halpha)) : ℝ) : EReal)) =
      ((sSup (Set.range fun τC : {τ : MState c // τ.m.PosDef} =>
        alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (sandwichedMutualInformationACTraceMatrix
                ψ.state.marginalAB.traceRight ψ τC.1 alpha)
              (sandwichedMutualInformationACTraceMatrix_posSemidef
                ψ.state.marginalAB.traceRight ψ τC.1 alpha)
              (sandwichedAlternateSchattenOrder halpha))) : ℝ) : EReal) := by
  have : Nonempty {τ : MState c // τ.m.PosDef} :=
    ⟨⟨(MState.uniform : MState c), MState.uniform_posDef⟩⟩
  exact ereal_sSup_range_coe_eq_coe_real_sSup _
    (sandwichedACTraceMatrixLog_fullRank_bddAbove ψ hAB hA halpha)

/-- The already-proved KW direction after optimizing the full-rank `tau_C`
side of the alternate expression.  This is one half of the pending state
alternate-expression equality. -/
theorem sandwichedACTraceMatrixLog_fullRank_sSup_le_sandwichedRenyiMutualInformationE
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : Ket ((a × b) × c))
    (hAB : ψ.state.marginalAB.m.PosDef)
    (hA : ψ.state.marginalAB.traceRight.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sSup (Set.range fun τC : {τ : MState c // τ.m.PosDef} =>
      ((alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix
              ψ.state.marginalAB.traceRight ψ τC.1 alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef
              ψ.state.marginalAB.traceRight ψ τC.1 alpha)
            (sandwichedAlternateSchattenOrder halpha)) : ℝ) : EReal)) ≤
      ψ.state.marginalAB.sandwichedRenyiMutualInformationE alpha := by
  have : Nonempty {τ : MState c // τ.m.PosDef} :=
    ⟨⟨(MState.uniform : MState c), MState.uniform_posDef⟩⟩
  refine csSup_le (Set.range_nonempty _) ?_
  rintro y ⟨τC, rfl⟩
  exact sandwichedACTraceMatrixLog_le_sandwichedRenyiMutualInformationE_posDef
    ψ τC.1 hAB hA τC.2 halpha

end Ket

namespace MState

/-- Swapping the canonical purification of a bipartite state puts the purified
`AB` system in the left factor, so the `marginalAB` used by the KW
alternate-expression lemmas is the original state. -/
theorem canonicalPurification_swap_marginalAB
    {a : Type u1} {b : Type v1}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rhoAB : MState (a × b)) :
    ((rhoAB.canonicalPurification.reindex
        (Equiv.prodComm (a × b) (a × b))).state.marginalAB) = rhoAB := by
  apply MState.ext
  ext x y
  have hpur := rhoAB.canonicalPurification_purifies
  simpa [MState.marginalAB_eq_traceRight, Ket.reindex_state,
    Matrix.traceLeft, Matrix.traceRight] using
      congrFun (congrFun hpur x) y

/-- The reference marginal of the unswapped canonical purification is the
transpose of the purified state.

This is the matrix bookkeeping behind the KW polar-decomposition route: a
full-rank input marginal also gives a full-rank reference marginal for the
canonical purification, up to transpose. -/
theorem canonicalPurification_traceRight_matrix
    {a : Type u1} [Fintype a] [DecidableEq a] (rho : MState a) :
    rho.canonicalPurification.state.traceRight.m = rho.m.transpose := by
  rw [MState.traceRight_m, Ket.state_matrix]
  ext i j
  change (∑ k : a, rho.sqrtMatrix k i * star (rho.sqrtMatrix k j)) =
    rho.m.transpose i j
  rw [Matrix.transpose_apply]
  rw [← rho.sqrtMatrix_mul_self, Matrix.mul_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [rho.sqrtMatrix_isHermitian.apply j k]
  ring

/-- Full-rank states have full-rank reference marginals in their unswapped
canonical purifications. -/
theorem canonicalPurification_traceRight_posDef
    {a : Type u1} [Fintype a] [DecidableEq a] (rho : MState a)
    (hrho : rho.m.PosDef) :
    rho.canonicalPurification.state.traceRight.m.PosDef := by
  rw [canonicalPurification_traceRight_matrix rho]
  exact hrho.transpose

/-- Canonical purifications vary continuously with the purified state.

This is the local topological bridge needed in the KW full-rank approximation
step: after regularizing the input marginal, its canonical purification
converges back to the original canonical purification. -/
theorem canonicalPurification_tendsto_of_tendsto
    {a : Type u1} [Fintype a] [DecidableEq a]
    {X : Type*} {l : Filter X} {rhoF : X → MState a} {rho : MState a}
    (hrhoF : Filter.Tendsto rhoF l (nhds rho)) :
    Filter.Tendsto (fun x : X => (rhoF x).canonicalPurification) l
      (nhds rho.canonicalPurification) := by
  rw [Filter.tendsto_iff_comap]
  rw [nhds_induced]
  rw [Filter.comap_comap]
  rw [← Filter.tendsto_iff_comap]
  change
    Filter.Tendsto
      (fun x : X => fun p : a × a => (rhoF x).sqrtMatrix p.2 p.1)
      l
      (nhds (fun p : a × a => rho.sqrtMatrix p.2 p.1))
  refine tendsto_pi_nhds.mpr ?_
  intro p
  exact ((continuous_id.matrix_elem p.2 p.1).tendsto rho.sqrtMatrix).comp
    (sqrtMatrix_tendsto_of_tendsto hrhoF)

/-- KW support-convention power algebra for a possibly singular input state.

For `alpha > 1` and `s = (1 - alpha) / (2 * alpha)`, the source expression
`rho^s rho rho^s` is interpreted on the positive spectral support of `rho`;
after embedding back it is exactly `rho^(1 / alpha)`. -/
theorem rpow_sandwich_self_eq_rpow_one_div
    {a : Type u1} [Fintype a] [DecidableEq a] (rho : MState a)
    {alpha : ℝ} (halpha : 1 < alpha) :
    let s : ℝ := (1 - alpha) / (2 * alpha)
    CFC.rpow rho.m s * rho.m * CFC.rpow rho.m s =
      CFC.rpow rho.m (1 / alpha) := by
  classical
  intro s
  let V : Matrix a (psdSupportIndex rho.m rho.psd) ℂ :=
    psdSupportIsometry rho.m rho.psd
  let rhoc : CMatrix (psdSupportIndex rho.m rho.psd) :=
    psdSupportCompress rho.m rho.psd rho.m
  let P : CMatrix (psdSupportIndex rho.m rho.psd) := CFC.rpow rhoc s
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hs_ne : s ≠ 0 := by
    dsimp [s]
    field_simp [ne_of_gt halpha_pos]
    linarith
  have hone_div_ne : (1 / alpha : ℝ) ≠ 0 := by
    exact one_div_ne_zero (ne_of_gt halpha_pos)
  have hV : Matrix.conjTranspose V * V =
      (1 : CMatrix (psdSupportIndex rho.m rho.psd)) := by
    simpa [V] using psdSupportIsometry_isometry rho.m rho.psd
  have hrec : V * rhoc * Matrix.conjTranspose V = rho.m := by
    simpa [V, rhoc] using psdSupportCompress_reconstruct_self rho.m rho.psd
  have hpow_s : V * P * Matrix.conjTranspose V = CFC.rpow rho.m s := by
    simpa [V, P, rhoc] using
      cMatrix_rpow_psdSupportCompress_reconstruct_self rho.m rho.psd hs_ne
  have hpow_one_div :
      V * CFC.rpow rhoc (1 / alpha) * Matrix.conjTranspose V =
        CFC.rpow rho.m (1 / alpha) := by
    simpa [V, rhoc] using
      cMatrix_rpow_psdSupportCompress_reconstruct_self
        rho.m rho.psd hone_div_ne
  have hRhoc : rhoc.PosDef := by
    simpa [rhoc] using psdSupportCompress_self_posDef rho.m rho.psd
  have hnonneg : 0 ≤ rhoc :=
    Matrix.nonneg_iff_posSemidef.mpr hRhoc.posSemidef
  have hpow_one : CFC.rpow rhoc (1 : ℝ) = rhoc :=
    CFC.rpow_one rhoc (ha := hnonneg)
  have hs_left :
      CFC.rpow rhoc s * rhoc = CFC.rpow rhoc (s + 1) := by
    calc
      CFC.rpow rhoc s * rhoc =
          CFC.rpow rhoc s * CFC.rpow rhoc (1 : ℝ) := by
            rw [hpow_one]
      _ = CFC.rpow rhoc (s + 1) := by
            exact (CFC.rpow_add (a := rhoc) (x := s) (y := 1) hRhoc.isUnit).symm
  have hs_total :
      CFC.rpow rhoc (s + 1) * CFC.rpow rhoc s =
        CFC.rpow rhoc ((s + 1) + s) := by
    exact (CFC.rpow_add (a := rhoc) (x := s + 1) (y := s) hRhoc.isUnit).symm
  have hexp : (s + 1) + s = 1 / alpha := by
    dsimp [s]
    field_simp [ne_of_gt halpha_pos]
    ring
  have hcompressed :
      P * rhoc * P = CFC.rpow rhoc (1 / alpha) := by
    calc
      P * rhoc * P =
          CFC.rpow rhoc s * rhoc * CFC.rpow rhoc s := by
            rfl
      _ = (CFC.rpow rhoc s * rhoc) * CFC.rpow rhoc s := by
            rw [Matrix.mul_assoc]
      _ = CFC.rpow rhoc (s + 1) * CFC.rpow rhoc s := by
            rw [hs_left]
      _ = CFC.rpow rhoc ((s + 1) + s) := hs_total
      _ = CFC.rpow rhoc (1 / alpha) := by rw [hexp]
  have houter :
      CFC.rpow rho.m s * rho.m * CFC.rpow rho.m s =
        (V * P * Matrix.conjTranspose V) * rho.m *
          (V * P * Matrix.conjTranspose V) := by
    exact congrArg (fun M : CMatrix a => M * rho.m * M) hpow_s.symm
  have hmiddle :
      (V * P * Matrix.conjTranspose V) * rho.m *
          (V * P * Matrix.conjTranspose V) =
        (V * P * Matrix.conjTranspose V) *
            (V * rhoc * Matrix.conjTranspose V) *
          (V * P * Matrix.conjTranspose V) := by
    exact congrArg
      (fun M : CMatrix a =>
        (V * P * Matrix.conjTranspose V) * M * (V * P * Matrix.conjTranspose V))
      hrec.symm
  calc
    CFC.rpow rho.m s * rho.m * CFC.rpow rho.m s =
        (V * P * Matrix.conjTranspose V) * rho.m *
          (V * P * Matrix.conjTranspose V) := houter
    _ =
        (V * P * Matrix.conjTranspose V) *
            (V * rhoc * Matrix.conjTranspose V) *
          (V * P * Matrix.conjTranspose V) := hmiddle
    _ = V * (P * rhoc * P) * Matrix.conjTranspose V := by
          calc
            (V * P * Matrix.conjTranspose V) *
                (V * rhoc * Matrix.conjTranspose V) *
              (V * P * Matrix.conjTranspose V) =
                V * P * (Matrix.conjTranspose V * V) * rhoc *
                  (Matrix.conjTranspose V * V) * P * Matrix.conjTranspose V := by
              simp [Matrix.mul_assoc]
            _ = V * P * (1 : CMatrix (psdSupportIndex rho.m rho.psd)) * rhoc *
                  (1 : CMatrix (psdSupportIndex rho.m rho.psd)) *
                P * Matrix.conjTranspose V := by
              rw [hV]
            _ = V * (P * rhoc * P) * Matrix.conjTranspose V := by
              simp [Matrix.mul_assoc]
    _ = V * CFC.rpow rhoc (1 / alpha) * Matrix.conjTranspose V := by
          rw [hcompressed]
    _ = CFC.rpow rho.m (1 / alpha) := hpow_one_div

/-- PSD version of the normalized interpolation endpoint
`Tr((rho^(1 / alpha))^alpha) = 1`.

Unlike the older full-rank endpoint lemma, this only uses the source
support-convention functional calculus for PSD states. -/
theorem state_rpow_one_div_psdTracePower_eq_one_psd
    {a : Type u1} [Fintype a] [DecidableEq a] (rho : MState a)
    {alpha : ℝ} (halpha_pos : 0 < alpha) :
    psdTracePower (CFC.rpow rho.m (1 / alpha))
        (rho.rpowMatrix_posSemidef (1 / alpha))
        alpha = 1 := by
  have hrho_nonneg : 0 ≤ rho.m :=
    Matrix.nonneg_iff_posSemidef.mpr rho.psd
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have hone_div_nonneg : 0 ≤ 1 / alpha := by positivity
  have halpha_ne_zero : alpha ≠ 0 := ne_of_gt halpha_pos
  have hpow :
      CFC.rpow (CFC.rpow rho.m (1 / alpha)) alpha =
        CFC.rpow rho.m (1 : ℝ) := by
    calc
      CFC.rpow (CFC.rpow rho.m (1 / alpha)) alpha =
          CFC.rpow rho.m ((1 / alpha) * alpha) := by
            exact CFC.rpow_rpow_of_exponent_nonneg rho.m
              (1 / alpha) alpha hone_div_nonneg halpha_nonneg hrho_nonneg
      _ = CFC.rpow rho.m (1 : ℝ) := by
            congr 1
            field_simp [halpha_ne_zero]
  have hone : CFC.rpow rho.m (1 : ℝ) = rho.m :=
    CFC.rpow_one rho.m (ha := hrho_nonneg)
  rw [psdTracePower, hpow, hone, rho.tr']
  norm_num

/-- PSD version of the normalized interpolation endpoint in Schatten-norm
form. -/
theorem state_rpow_one_div_psdSchattenPNorm_eq_one_psd
    {a : Type u1} [Fintype a] [DecidableEq a] (rho : MState a)
    {alpha : ℝ} (halpha_pos : 0 < alpha) :
    psdSchattenPNorm (CFC.rpow rho.m (1 / alpha))
        (rho.rpowMatrix_posSemidef (1 / alpha))
        (SchattenOrder.ofPositive halpha_pos) = 1 := by
  change Real.rpow
    (psdTracePower (CFC.rpow rho.m (1 / alpha))
      (rho.rpowMatrix_posSemidef (1 / alpha)) alpha) (1 / alpha) = 1
  rw [state_rpow_one_div_psdTracePower_eq_one_psd rho halpha_pos]
  exact Real.one_rpow (1 / alpha)

/-- MState-level lower-bound half of KW `EA_capacity.tex:1193-1217`.

This is the support-convention version of the product-state argument: purify
both states canonically, restrict the post-Sion `tau_C` optimization to product
states, and use the `AC` trace-matrix product factorization.  No full-rank
hypothesis is imposed on the bipartite states or their marginals. -/
theorem sandwichedRenyiMutualInformationE_bipartiteProduct_ge_add
    {a1 b1 a2 b2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (xi : MState (a1 × b1)) (omega : MState (a2 × b2))
    {alpha : ℝ} (halpha : 1 < alpha) :
    xi.sandwichedRenyiMutualInformationE alpha +
        omega.sandwichedRenyiMutualInformationE alpha ≤
      (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationE alpha := by
  have : Nonempty (a1 × b1) := xi.nonempty
  have : Nonempty a1 := ⟨(Classical.choice (xi.nonempty)).1⟩
  have : Nonempty b1 := ⟨(Classical.choice (xi.nonempty)).2⟩
  have : Nonempty (a2 × b2) := omega.nonempty
  have : Nonempty a2 := ⟨(Classical.choice (omega.nonempty)).1⟩
  have : Nonempty b2 := ⟨(Classical.choice (omega.nonempty)).2⟩
  let psi : Ket ((a1 × b1) × (a1 × b1)) :=
    xi.canonicalPurification.reindex (Equiv.prodComm (a1 × b1) (a1 × b1))
  let phi : Ket ((a2 × b2) × (a2 × b2)) :=
    omega.canonicalPurification.reindex (Equiv.prodComm (a2 × b2) (a2 × b2))
  have hpsiAB : psi.state.marginalAB = xi := by
    simpa [psi] using MState.canonicalPurification_swap_marginalAB xi
  have hphiAB : phi.state.marginalAB = omega := by
    simpa [phi] using MState.canonicalPurification_swap_marginalAB omega
  have h :=
    Ket.sandwichedRenyiMutualInformationE_bipartiteProductPurification_ge_add
      psi phi halpha
  have htarget :
      psi.state.marginalAB.sandwichedRenyiMutualInformationE alpha +
          phi.state.marginalAB.sandwichedRenyiMutualInformationE alpha ≤
        (psi.state.marginalAB.bipartiteProduct phi.state.marginalAB).sandwichedRenyiMutualInformationE
          alpha := by
    have hprodAB := Ket.bipartiteProductPurification_marginalAB psi phi
    rw [← hprodAB]
    simpa [MState.marginalAB_eq_traceRight] using h
  rw [hpsiAB, hphiAB] at htarget
  exact htarget

/-- MState-level product additivity for sandwiched-Renyi mutual information.

This is the completed support-convention form of KW `EA_capacity.tex:1169-1217`,
combining the definition-side upper bound with the source-shaped lower branch
above. -/
theorem sandwichedRenyiMutualInformationE_bipartiteProduct_eq_add
    {a1 b1 a2 b2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]
    (xi : MState (a1 × b1)) (omega : MState (a2 × b2))
    {alpha : ℝ} (halpha : 1 < alpha) :
    (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationE alpha =
      xi.sandwichedRenyiMutualInformationE alpha +
        omega.sandwichedRenyiMutualInformationE alpha := by
  have : Nonempty (a1 × b1) := xi.nonempty
  have : Nonempty b1 := ⟨(Classical.choice (xi.nonempty)).2⟩
  have : Nonempty (a2 × b2) := omega.nonempty
  have : Nonempty b2 := ⟨(Classical.choice (omega.nonempty)).2⟩
  exact le_antisymm
    (MState.sandwichedRenyiMutualInformationE_bipartiteProduct_le_add
      xi omega halpha)
    (MState.sandwichedRenyiMutualInformationE_bipartiteProduct_ge_add
      xi omega halpha)

end MState
