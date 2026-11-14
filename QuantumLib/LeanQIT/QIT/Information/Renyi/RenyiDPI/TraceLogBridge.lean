/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy.RelativeEntropyTraceLog
public import QIT.Information.Renyi.FrankLieb.DPI
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Log.RpowTendsto
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Sandwiched Renyi alpha-to-one trace-log bridge

High-alpha curve, source-limit PSD-reference relative entropy, and trace-log
endpoint bridge declarations for sandwiched Renyi.
-/

@[expose] public section

open Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator UniformConvergence

namespace QIT

universe u v

noncomputable section

noncomputable local instance cMatrixCStarAlgebraForRelativeEntropyDPI
    {n : Type*} [Fintype n] [DecidableEq n] : CStarAlgebra (CMatrix n) := {}

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]

private theorem terminalMeasureChannel_map_state_matrix (σ : State a) :
    (terminalMeasureChannel a).map σ.matrix = (1 : CMatrix PUnit.{1}) := by
  ext i j
  cases i
  cases j
  simp [terminalMeasureChannel, terminalPOVM, Channel.measure, Channel.measureMap,
    σ.trace_eq_one]

private theorem sandwichedRenyiPSDReferenceHighAlphaFinite_unit_one_eq_zero
    (α : ℝ) (_hα : 1 < α) :
    sandwichedRenyiPSDReferenceHighAlphaFinite (State.unit : State PUnit.{1})
      (1 : CMatrix PUnit.{1}) Matrix.PosSemidef.one α = 0 := by
  have htrace :
      ((Matrix.trace ((State.unit.matrix : CMatrix PUnit.{1}) ^ α)).re) = 1 := by
    rw [show (State.unit.matrix : CMatrix PUnit.{1}) = 1 by rfl]
    rw [CFC.one_rpow]
    simp
  simp [sandwichedRenyiPSDReferenceHighAlphaFinite, sandwichedRenyiReferenceInner,
    psdTracePower, log2, CFC.one_rpow, htrace]

theorem sandwichedRenyiPSDReferenceHighAlphaFinite_nonneg_of_posDef_reference
    (ρ σ : State a) (hσ : σ.matrix.PosDef)
    (alpha : {alpha : ℝ // 1 < alpha}) :
    0 ≤ sandwichedRenyiPSDReferenceHighAlphaFinite
      ρ σ.matrix hσ.posSemidef alpha.1 := by
  let Φ : Channel a PUnit.{1} := terminalMeasureChannel a
  have hDPIE :=
    sandwichedRenyiPSDReferenceE_dataProcessing_channel_ge_of_half_le_lt_one_or_one_lt
      ρ hσ.posSemidef Φ alpha.1 (Or.inr alpha.2)
  rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ alpha.2,
    sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ alpha.2] at hDPIE
  have hinSupport : Matrix.Supports ρ.matrix σ.matrix :=
    Matrix.Supports.of_right_posDef ρ.matrix σ.matrix hσ
  have hmap : Φ.map σ.matrix = (1 : CMatrix PUnit.{1}) := by
    simpa [Φ] using terminalMeasureChannel_map_state_matrix σ
  have houtState : Φ.applyState ρ = State.unit := by
    simpa [Φ] using terminalMeasureChannel_applyState ρ
  have houtSupport : Matrix.Supports (Φ.applyState ρ).matrix (Φ.map σ.matrix) := by
    rw [hmap]
    exact Matrix.Supports.of_right_posDef (Φ.applyState ρ).matrix
      (1 : CMatrix PUnit.{1}) Matrix.PosDef.one
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      ρ hσ.posSemidef alpha.1 hinSupport,
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      (Φ.applyState ρ) (Φ.mapsPositive σ.matrix hσ.posSemidef) alpha.1
      houtSupport] at hDPIE
  have hreal :
      sandwichedRenyiPSDReferenceHighAlphaFinite
          (Φ.applyState ρ) (Φ.map σ.matrix)
          (Φ.mapsPositive σ.matrix hσ.posSemidef) alpha.1 ≤
        sandwichedRenyiPSDReferenceHighAlphaFinite
          ρ σ.matrix hσ.posSemidef alpha.1 := by
    exact EReal.coe_le_coe_iff.mp hDPIE
  have houtZero :
      sandwichedRenyiPSDReferenceHighAlphaFinite
          (Φ.applyState ρ) (Φ.map σ.matrix)
          (Φ.mapsPositive σ.matrix hσ.posSemidef) alpha.1 = 0 := by
    simpa [houtState, hmap] using
      sandwichedRenyiPSDReferenceHighAlphaFinite_unit_one_eq_zero
        alpha.1 alpha.2
  linarith

/-- Positive-definite matrix logarithms are the right endpoint of the
positive-power CFC difference quotient.

This is the fixed-reference CFC ingredient for the `alpha -> 1+` trace-log
endpoint: for a strictly positive matrix `sigma`,
`p^{-1}(sigma^p - I) -> log sigma` as `p -> 0+`. -/
theorem cMatrix_cfc_rpow_sub_one_tendsto_psdLog_posDef
    {sigma : CMatrix a} (hSigma : sigma.PosDef) :
    Filter.Tendsto
      (fun p : Real => cfc (fun x : Real => p⁻¹ * (x ^ p - 1)) sigma)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (psdLog sigma hSigma)) := by
  simpa [psdLog, CFC.log] using
    (CFC.tendsto_cfc_rpow_sub_one_log
      (a := sigma) (ha := Matrix.PosDef.isStrictlyPositive hSigma))

/-- Trace pairing form of
`cMatrix_cfc_rpow_sub_one_tendsto_psdLog_posDef`.

For fixed state `rho` and positive-definite reference `sigma`, the scalar
pairing against `rho` converges to the `Tr rho log sigma` contribution in the
trace-log endpoint. -/
theorem trace_mul_cfc_rpow_sub_one_tendsto_trace_mul_psdLog_posDef
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef) :
    Filter.Tendsto
      (fun p : Real =>
        ((rho.matrix * cfc (fun x : Real => p⁻¹ * (x ^ p - 1)) sigma).trace).re)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds ((rho.matrix * psdLog sigma hSigma).trace.re)) := by
  have hmatrix := cMatrix_cfc_rpow_sub_one_tendsto_psdLog_posDef hSigma
  have hcont :
      Continuous fun X : CMatrix a => ((rho.matrix * X).trace).re := by
    have hmul : Continuous fun X : CMatrix a => rho.matrix * X := by
      fun_prop
    exact Complex.continuous_re.comp (Continuous.matrix_trace hmul)
  exact (hcont.tendsto (psdLog sigma hSigma)).comp hmatrix

/-- The logarithm of a positive-definite matrix inverse is the negative
logarithm of the matrix.

This is the fixed-reference CFC identity needed to turn the derivative of the
negative reference power into the `- Tr rho log sigma` contribution in the
trace-log endpoint. -/
theorem psdLog_inv_eq_neg_psdLog_posDef
    {sigma : CMatrix a} (hSigma : sigma.PosDef) :
    psdLog sigma⁻¹ hSigma.inv = - psdLog sigma hSigma := by
  rw [psdLog, psdLog]
  let u : (CMatrix a)ˣ := hSigma.isUnit.unit
  have hu : (u : CMatrix a) = sigma := hSigma.isUnit.unit_spec
  have hInv : (u⁻¹ : CMatrix a) = sigma⁻¹ := by
    rw [hu]
  rw [← hInv, ← hu]
  have huStrict : IsStrictlyPositive (u : CMatrix a) := by
    simpa [hu] using Matrix.PosDef.isStrictlyPositive hSigma
  have hLogCont :
      ContinuousOn Real.log ((fun x : Real => x⁻¹) '' spectrum Real (u : CMatrix a)) := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact (Real.continuousAt_log
      (ne_of_gt (inv_pos.mpr (huStrict.spectrum_pos hx)))).continuousWithinAt
  have hcomp :
      cfc (fun x : Real => Real.log x⁻¹) (u : CMatrix a) =
        cfc Real.log (u⁻¹ : CMatrix a) := by
    simpa using (cfc_comp_inv (A := CMatrix a) (p := IsSelfAdjoint)
      (f := Real.log) (a := u) (hf := hLogCont))
  rw [← hcomp]
  have hneg :
      cfc (fun x : Real => - Real.log x) (u : CMatrix a) =
        - cfc Real.log (u : CMatrix a) := by
    simpa using (cfc_neg (A := CMatrix a) (p := IsSelfAdjoint)
      (f := Real.log) (a := (u : CMatrix a)))
  rw [← hneg]
  apply cfc_congr
  intro x _hx
  simp [Real.log_inv]

/-- Positive-definite inverse powers tend to the identity at exponent `0+`.

This is the zero-order moving-reference ingredient for the high-`alpha`
endpoint: if `sigma` is full rank, then `sigma^{-p} -> I` as `p -> 0+`. -/
theorem cMatrix_rpow_inv_tendsto_one_right_posDef
    {sigma : CMatrix a} (hSigma : sigma.PosDef) :
    Filter.Tendsto
      (fun p : Real => CFC.rpow sigma⁻¹ p)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (1 : CMatrix a)) := by
  let l : Filter Real := nhdsWithin (0 : Real) (Set.Ioi 0)
  have hquot :=
    cMatrix_cfc_rpow_sub_one_tendsto_psdLog_posDef
      (sigma := sigma⁻¹) hSigma.inv
  have hp : Filter.Tendsto (fun p : Real => p) l (nhds (0 : Real)) := by
    exact
      (tendsto_nhdsWithin_iff.mp
        (tendsto_id : Filter.Tendsto (fun p : Real => p) l l)).1
  have hprod :
      Filter.Tendsto
        (fun p : Real =>
          p • cfc (fun x : Real => p⁻¹ * (x ^ p - 1)) (sigma⁻¹))
        l
        (nhds ((0 : Real) • psdLog (sigma⁻¹) hSigma.inv)) := by
    exact hp.smul hquot
  have hzero :
      ((0 : Real) • psdLog (sigma⁻¹) hSigma.inv : CMatrix a) = 0 := by
    simp
  rw [hzero] at hprod
  have hdiff :
      Filter.Tendsto
        (fun p : Real => CFC.rpow (sigma⁻¹) p - (1 : CMatrix a))
        l (nhds 0) := by
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with p hp0
    have hpne : p ≠ 0 := ne_of_gt hp0
    have hcfc :
        cfc (fun x : Real => p⁻¹ * (x ^ p - 1)) (sigma⁻¹) =
          (p⁻¹ : Real) • (CFC.rpow (sigma⁻¹) p - (1 : CMatrix a)) := by
      change cfc (fun x : Real => p⁻¹ • (x ^ p - 1)) (sigma⁻¹) =
        (p⁻¹ : Real) • (CFC.rpow (sigma⁻¹) p - (1 : CMatrix a))
      have hpowCont :
          ContinuousOn (fun x : Real => x ^ p) (spectrum Real (sigma⁻¹)) :=
        (Real.continuous_rpow_const (le_of_lt hp0)).continuousOn
      have hsubCont :
          ContinuousOn (fun x : Real => x ^ p - 1) (spectrum Real (sigma⁻¹)) :=
        hpowCont.sub continuousOn_const
      rw [cfc_smul _ (hf := hsubCont),
        cfc_sub _ _ (hf := hpowCont),
        cfc_const_one Real (sigma⁻¹)
          (ha := Matrix.IsHermitian.isSelfAdjoint hSigma.inv.isHermitian)]
      have hrpowReal :
          CFC.rpow (sigma⁻¹) p = cfc (fun x : Real => x ^ p) (sigma⁻¹) := by
        simpa [CFC.rpow_eq_pow] using
          (CFC.rpow_eq_cfc_real (a := sigma⁻¹) (y := p)
            (ha := Matrix.nonneg_iff_posSemidef.mpr hSigma.inv.posSemidef))
      rw [← hrpowReal]
    rw [hcfc]
    simp [smul_smul, hpne]
  have hone :
      Filter.Tendsto
        (fun p : Real => (CFC.rpow (sigma⁻¹) p - (1 : CMatrix a)) + 1)
        l (nhds (0 + (1 : CMatrix a))) :=
    hdiff.add tendsto_const_nhds
  simpa [sub_add_cancel] using hone

/-- The reference-weighted inner operator itself converges to the input state
matrix as `alpha = 1 + p -> 1+`.

This is the zero-order moving-base endpoint behind the source trace-log bridge.
The remaining first-order endpoint is the derivative of the trace power around
this convergent moving base. -/
theorem sandwichedRenyiReferenceInner_one_add_tendsto_state_matrix_posDef
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef) :
    Filter.Tendsto
      (fun p : Real => sandwichedRenyiReferenceInner rho sigma (1 + p))
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds rho.matrix) := by
  let l : Filter Real := nhdsWithin (0 : Real) (Set.Ioi 0)
  let q : Real -> Real := fun p => p / (2 * (1 + p))
  have hidWithin : Filter.Tendsto (fun p : Real => p) l l := tendsto_id
  have hid : Filter.Tendsto (fun p : Real => p) l (nhds 0) := by
    exact (tendsto_nhdsWithin_iff.mp hidWithin).1
  have hq_nhds : Filter.Tendsto q l (nhds 0) := by
    have hcont : ContinuousAt (fun p : Real => p / (2 * (1 + p))) 0 := by
      exact continuousAt_id.div
        (continuousAt_const.mul (continuousAt_const.add continuousAt_id))
        (by norm_num)
    simpa [q] using hcont.tendsto.comp hid
  have hq_pos : ∀ᶠ p in l, q p ∈ Set.Ioi (0 : Real) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    have hp0 : 0 < p := by simpa using hp
    have hden : 0 < 2 * (1 + p) := by
      exact mul_pos (by norm_num) (by linarith)
    dsimp [q]
    exact div_pos hp0 hden
  have hq_tendsto :
      Filter.Tendsto q l (nhdsWithin (0 : Real) (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hq_nhds, hq_pos⟩
  have hpowInv :
      Filter.Tendsto (fun p : Real => CFC.rpow (sigma⁻¹) (q p))
        l (nhds (1 : CMatrix a)) :=
    (cMatrix_rpow_inv_tendsto_one_right_posDef hSigma).comp hq_tendsto
  have hpow :
      Filter.Tendsto
        (fun p : Real => CFC.rpow sigma ((1 - (1 + p)) / (2 * (1 + p))))
        l (nhds (1 : CMatrix a)) := by
    refine hpowInv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with p hp
    have hp0 : 0 < p := by simpa using hp
    have halpha_ne : 1 + p ≠ 0 := by linarith
    have hs : (1 - (1 + p)) / (2 * (1 + p)) = -q p := by
      dsimp [q]
      field_simp [halpha_ne]
      ring
    rw [hs, ← cMatrix_rpow_nonsing_inv_eq_rpow_neg hSigma (q p)]
  have hleft :
      Filter.Tendsto
        (fun p : Real =>
          CFC.rpow sigma ((1 - (1 + p)) / (2 * (1 + p))) * rho.matrix)
        l (nhds ((1 : CMatrix a) * rho.matrix)) :=
    hpow.mul (tendsto_const_nhds (x := rho.matrix))
  have hinner :
      Filter.Tendsto
        (fun p : Real =>
          (CFC.rpow sigma ((1 - (1 + p)) / (2 * (1 + p))) * rho.matrix) *
            CFC.rpow sigma ((1 - (1 + p)) / (2 * (1 + p))))
        l (nhds (((1 : CMatrix a) * rho.matrix) * (1 : CMatrix a))) :=
    hleft.mul hpow
  simpa [sandwichedRenyiReferenceInner, Matrix.one_mul, Matrix.mul_one] using hinner

/-- Trace pairing version of the positive-power quotient endpoint on the
inverse reference.

Equivalently, the right derivative of the inverse-reference power contributes
`- Tr rho log sigma`. -/
theorem trace_mul_cfc_rpow_sub_one_inv_tendsto_neg_trace_mul_psdLog_posDef
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef) :
    Filter.Tendsto
      (fun p : Real =>
        ((rho.matrix * cfc (fun x : Real => p⁻¹ * (x ^ p - 1)) sigma⁻¹).trace).re)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (-((rho.matrix * psdLog sigma hSigma).trace.re))) := by
  have h :=
    trace_mul_cfc_rpow_sub_one_tendsto_trace_mul_psdLog_posDef
      (rho := rho) (sigma := sigma⁻¹) hSigma.inv
  simpa [psdLog_inv_eq_neg_psdLog_posDef hSigma] using h

/-- Trace pairing form of the inverse-reference endpoint, with the scalar
difference quotient outside the CFC expression. -/
theorem trace_mul_cfc_rpow_sub_one_inv_div_tendsto_neg_trace_mul_psdLog_posDef
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef) :
    Filter.Tendsto
      (fun p : Real =>
        ((rho.matrix *
          (CFC.rpow sigma⁻¹ p - (1 : CMatrix a))).trace).re / p)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (-((rho.matrix * psdLog sigma hSigma).trace.re))) := by
  have h :=
    trace_mul_cfc_rpow_sub_one_inv_tendsto_neg_trace_mul_psdLog_posDef
      (rho := rho) (sigma := sigma) hSigma
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p hp
  have hpne : p ≠ 0 := ne_of_gt hp
  have hcfc :
      cfc (fun x : Real => p⁻¹ * (x ^ p - 1)) sigma⁻¹ =
        (p⁻¹ : Real) • (CFC.rpow sigma⁻¹ p - (1 : CMatrix a)) := by
    change cfc (fun x : Real => p⁻¹ • (x ^ p - 1)) sigma⁻¹ =
      (p⁻¹ : Real) • (CFC.rpow sigma⁻¹ p - (1 : CMatrix a))
    have hpowCont :
        ContinuousOn (fun x : Real => x ^ p) (spectrum Real sigma⁻¹) :=
      (Real.continuous_rpow_const (le_of_lt hp)).continuousOn
    have hsubCont :
        ContinuousOn (fun x : Real => x ^ p - 1) (spectrum Real sigma⁻¹) :=
      hpowCont.sub continuousOn_const
    rw [cfc_smul _ (hf := hsubCont),
      cfc_sub _ _ (hf := hpowCont),
      cfc_const_one Real (sigma⁻¹)
        (ha := Matrix.IsHermitian.isSelfAdjoint hSigma.inv.isHermitian)]
    have hrpowReal :
        CFC.rpow sigma⁻¹ p = cfc (fun x : Real => x ^ p) sigma⁻¹ := by
      simpa [CFC.rpow_eq_pow] using
        (CFC.rpow_eq_cfc_real (a := sigma⁻¹) (y := p)
          (ha := Matrix.nonneg_iff_posSemidef.mpr hSigma.inv.posSemidef))
    rw [← hrpowReal]
  calc
    ((rho.matrix *
        cfc (fun x : Real => p⁻¹ * (x ^ p - 1)) sigma⁻¹).trace).re =
        ((rho.matrix *
          ((p⁻¹ : Real) • (CFC.rpow sigma⁻¹ p - (1 : CMatrix a)))).trace).re := by
          rw [hcfc]
    _ = ((rho.matrix *
          (CFC.rpow sigma⁻¹ p - (1 : CMatrix a))).trace).re / p := by
          simp [Matrix.trace_smul, div_eq_mul_inv,
            mul_comm, mul_assoc]
          field_simp [hpne]

/-- The trace of the high-`alpha` reference-weighted inner operator is the
trace pairing against the doubled reference power. -/
theorem sandwichedRenyiReferenceInner_trace_re_eq_trace_mul_reference_rpow_posDef
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    {alpha : Real} (hAlpha : alpha ≠ 0) :
    (sandwichedRenyiReferenceInner rho sigma alpha).trace.re =
      (rho.matrix * CFC.rpow sigma ((1 - alpha) / alpha)).trace.re := by
  let s : Real := (1 - alpha) / (2 * alpha)
  let C : CMatrix a := CFC.rpow sigma s
  have hcycle :
      (C * rho.matrix * C).trace = (rho.matrix * (C * C)).trace := by
    have h1 : (C * rho.matrix * C).trace = (C * C * rho.matrix).trace :=
      Matrix.trace_mul_cycle C rho.matrix C
    have h2 : (C * C * rho.matrix).trace = (rho.matrix * (C * C)).trace := by
      simpa [Matrix.mul_assoc] using Matrix.trace_mul_comm (C * C) rho.matrix
    exact h1.trans h2
  have hpow :
      C * C = CFC.rpow sigma (s + s) := by
    simpa [C] using
      (CFC.rpow_add (a := sigma) (x := s) (y := s) hSigma.isUnit).symm
  have hs : s + s = (1 - alpha) / alpha := by
    dsimp [s]
    field_simp [hAlpha]
    ring_nf
  calc
    (sandwichedRenyiReferenceInner rho sigma alpha).trace.re =
        (rho.matrix * (C * C)).trace.re := by
          simpa [sandwichedRenyiReferenceInner, C, s] using congrArg Complex.re hcycle
    _ = (rho.matrix * CFC.rpow sigma (s + s)).trace.re := by rw [hpow]
    _ = (rho.matrix * CFC.rpow sigma ((1 - alpha) / alpha)).trace.re := by rw [hs]

/-- The reference-weighted inner trace contributes the `- Tr rho log sigma`
term in the high-`alpha`, `alpha -> 1+` endpoint. -/
theorem sandwichedRenyiReferenceInner_trace_re_one_add_slope_tendsto_neg_trace_mul_psdLog_posDef
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef) :
    Filter.Tendsto
      (fun p : Real =>
        ((sandwichedRenyiReferenceInner rho sigma (1 + p)).trace.re - 1) / p)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (-((rho.matrix * psdLog sigma hSigma).trace.re))) := by
  let l : Filter Real := nhdsWithin (0 : Real) (Set.Ioi 0)
  let q : Real -> Real := fun p => p / (1 + p)
  have hidWithin : Filter.Tendsto (fun p : Real => p) l l := tendsto_id
  have hid : Filter.Tendsto (fun p : Real => p) l (nhds 0) := by
    exact (tendsto_nhdsWithin_iff.mp hidWithin).1
  have hq_nhds : Filter.Tendsto q l (nhds 0) := by
    have hcont : ContinuousAt (fun p : Real => p / (1 + p)) 0 := by
      exact continuousAt_id.div (continuousAt_const.add continuousAt_id) (by norm_num)
    simpa [q] using hcont.tendsto.comp hid
  have hq_pos : ∀ᶠ p in l, q p ∈ Set.Ioi (0 : Real) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    have hp0 : 0 < p := by simpa using hp
    dsimp [q]
    exact div_pos hp0 (by linarith)
  have hq_tendsto :
      Filter.Tendsto q l (nhdsWithin (0 : Real) (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hq_nhds, hq_pos⟩
  have hbase :=
    (trace_mul_cfc_rpow_sub_one_inv_div_tendsto_neg_trace_mul_psdLog_posDef
      (rho := rho) (sigma := sigma) hSigma).comp hq_tendsto
  have hfactor : Filter.Tendsto (fun p : Real => q p / p) l (nhds 1) := by
    have hcont : ContinuousAt (fun p : Real => (1 : Real) / (1 + p)) 0 := by
      exact continuousAt_const.div (continuousAt_const.add continuousAt_id) (by norm_num)
    have hlim : Filter.Tendsto (fun p : Real => (1 : Real) / (1 + p)) l (nhds 1) := by
      simpa using hcont.tendsto.comp hid
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with p hp
    have hp0 : 0 < p := by simpa using hp
    have hpne : p ≠ 0 := ne_of_gt hp0
    have hone : 1 + p ≠ 0 := by linarith
    dsimp [q]
    field_simp [hpne, hone]
  have hprod := hbase.mul hfactor
  have htarget :
      Filter.Tendsto
        (fun p : Real =>
          (((rho.matrix *
            (CFC.rpow sigma⁻¹ (q p) - (1 : CMatrix a))).trace).re / q p) *
              (q p / p))
        l
        (nhds (-((rho.matrix * psdLog sigma hSigma).trace.re))) := by
    simpa using hprod
  refine htarget.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p hp
  have hp0 : 0 < p := by simpa using hp
  have hpne : p ≠ 0 := ne_of_gt hp
  have halpha_ne : 1 + p ≠ 0 := by linarith
  have hqpos : 0 < q p := by
    dsimp [q]
    exact div_pos hp0 (by linarith)
  have hqne : q p ≠ 0 := ne_of_gt hqpos
  have htrace :=
    sandwichedRenyiReferenceInner_trace_re_eq_trace_mul_reference_rpow_posDef
      (rho := rho) (sigma := sigma) hSigma (alpha := 1 + p) halpha_ne
  have hexp : (1 - (1 + p)) / (1 + p) = -q p := by
    dsimp [q]
    field_simp [halpha_ne]
    ring
  rw [hexp, ← cMatrix_rpow_nonsing_inv_eq_rpow_neg hSigma (q p)] at htrace
  have hdiff :
      (rho.matrix * CFC.rpow sigma⁻¹ (q p)).trace.re - 1 =
        (rho.matrix * (CFC.rpow sigma⁻¹ (q p) - (1 : CMatrix a))).trace.re := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_one]
    simp [rho.trace_eq_one]
  symm
  calc
    ((sandwichedRenyiReferenceInner rho sigma (1 + p)).trace.re - 1) / p =
        ((rho.matrix * CFC.rpow sigma⁻¹ (q p)).trace.re - 1) / p := by
          rw [htrace]
    _ = ((rho.matrix * (CFC.rpow sigma⁻¹ (q p) - (1 : CMatrix a))).trace.re) / p := by
          rw [hdiff]
    _ = (((rho.matrix *
            (CFC.rpow sigma⁻¹ (q p) - (1 : CMatrix a))).trace).re / q p) *
          (q p / p) := by
          field_simp [hpne, hqne]

/-- Once the moving-matrix self power term has its `alpha -> 1+` slope, the
raw sandwiched trace-power slope follows from the proved reference-trace
endpoint. -/
theorem sandwichedRenyiReferenceInner_tracePower_slope_tendsto_of_power_minus_trace_slope_posDef
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    (hPowerMinusTrace :
      Filter.Tendsto
        (fun p : Real =>
          (psdTracePower (sandwichedRenyiReferenceInner rho sigma (1 + p))
              (sandwichedRenyiReferenceInner_posSemidef
                rho hSigma.posSemidef (1 + p))
              (1 + p) -
            (sandwichedRenyiReferenceInner rho sigma (1 + p)).trace.re) / p)
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds (-rho.vonNeumann * Real.log 2))) :
    Filter.Tendsto
      (fun p : Real =>
        (psdTracePower (sandwichedRenyiReferenceInner rho sigma (1 + p))
            (sandwichedRenyiReferenceInner_posSemidef
              rho hSigma.posSemidef (1 + p))
            (1 + p) - 1) / p)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds
        (-rho.vonNeumann * Real.log 2 -
          (rho.matrix * psdLog sigma hSigma).trace.re)) := by
  have hTrace :=
    sandwichedRenyiReferenceInner_trace_re_one_add_slope_tendsto_neg_trace_mul_psdLog_posDef
      rho hSigma
  have hsum := hPowerMinusTrace.add hTrace
  have hsum' :
      Filter.Tendsto
        (fun p : Real =>
          (psdTracePower (sandwichedRenyiReferenceInner rho sigma (1 + p))
              (sandwichedRenyiReferenceInner_posSemidef
                rho hSigma.posSemidef (1 + p))
              (1 + p) - 1) / p)
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds
          ((-rho.vonNeumann * Real.log 2) +
            -((rho.matrix * psdLog sigma hSigma).trace.re))) := by
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with p hp
    have hp0 : 0 < p := by simpa using hp
    have hpne : p ≠ 0 := ne_of_gt hp0
    field_simp [hpne]
    ring
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum'

/-- Nonnegative scalar endpoint for the trace-power self term.

For `x = 0` the right-neighborhood branch is identically zero; for `x > 0`
this is the ordinary derivative of `p ↦ x^(1+p)` at `p = 0`. -/
theorem real_rpow_one_add_sub_self_div_tendsto_mul_log_of_nonneg
    {x : Real} (hx : 0 ≤ x) :
    Filter.Tendsto
      (fun p : Real => (x ^ (1 + p) - x) / p)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (x * Real.log x)) := by
  rcases lt_or_eq_of_le hx with hxpos | rfl
  · have hderiv :
        HasDerivAt (fun p : Real => x ^ (1 + p)) (x * Real.log x) 0 := by
      have hpow0 :
          HasDerivAt (fun p : Real => x ^ p)
            (x ^ (0 : Real) * Real.log x) 0 :=
        (Real.hasStrictDerivAt_const_rpow hxpos 0).hasDerivAt
      have hpow : HasDerivAt (fun p : Real => x ^ p) (Real.log x) 0 := by
        simpa using hpow0
      have hmul : HasDerivAt (fun p : Real => x * x ^ p) (x * Real.log x) 0 :=
        hpow.const_mul x
      refine hmul.congr_of_eventuallyEq ?_
      filter_upwards with p
      calc
        x ^ (1 + p) = x ^ (1 : Real) * x ^ p := by
          exact Real.rpow_add hxpos 1 p
        _ = x * x ^ p := by rw [Real.rpow_one]
    have hslope := hderiv.tendsto_slope_zero_right
    refine hslope.congr' ?_
    filter_upwards with p
    simp [div_eq_mul_inv, mul_comm]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with p hp
    have hp_ne : (1 : Real) + p ≠ 0 := by
      have hp_pos : 0 < p := hp
      linarith
    simp [Real.zero_rpow hp_ne]

/-- Finite nonnegative spectral-sum version of
`real_rpow_one_add_sub_self_div_tendsto_mul_log_of_nonneg`. -/
theorem finite_sum_rpow_one_add_sub_self_div_tendsto_sum_mul_log
    {ι : Type*} [Fintype ι] (d : ι -> Real) (hd : ∀ i, 0 ≤ d i) :
    Filter.Tendsto
      (fun p : Real => ((∑ i, d i ^ (1 + p)) - (∑ i, d i)) / p)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (∑ i, d i * Real.log (d i))) := by
  have hsum :
      Filter.Tendsto
        (fun p : Real => ∑ i, (d i ^ (1 + p) - d i) / p)
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds (∑ i, d i * Real.log (d i))) := by
    simpa using
      tendsto_finsetSum (Finset.univ : Finset ι)
        (fun i _ => real_rpow_one_add_sub_self_div_tendsto_mul_log_of_nonneg
          (hd i))
  refine hsum.congr' ?_
  filter_upwards with p
  rw [← Finset.sum_sub_distrib, Finset.sum_div]

/-- The `x log_2 x` convention agrees with `x log x` after multiplying by
`log 2`, including at `x = 0`. -/
theorem xlog2_mul_log2_self_of_nonneg {x : Real} (hx : 0 ≤ x) :
    xlog2 x * Real.log 2 = x * Real.log x := by
  by_cases hzx : x = 0
  · simp [xlog2, hzx, Real.log_zero]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hzx)
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    simp only [xlog2, if_neg hzx, log2]
    field_simp [hlog2]

/-- CFC trace form of the von Neumann entropy endpoint.

This rewrites the eigenvalue definition of `State.vonNeumann` as the natural-log
trace expression `Tr rho log rho`, with the `0 log 0 = 0` convention carried by
the continuous scalar function `x * log x`. -/
theorem trace_cfc_mul_log_state_eq_neg_vonNeumann_mul_log2
    (rho : State a) :
    ((cfc (fun x : Real => x * Real.log x) rho.matrix).trace).re =
      -rho.vonNeumann * Real.log 2 := by
  have hcfc :
      cfc (fun x : Real => x * Real.log x) rho.matrix =
        rho.pos.isHermitian.cfc (fun x : Real => x * Real.log x) :=
    Matrix.IsHermitian.cfc_eq (𝕜 := Complex) rho.pos.isHermitian
      (fun x : Real => x * Real.log x)
  rw [hcfc]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  have hsum :
      (∑ i, rho.pos.isHermitian.eigenvalues i *
          Real.log (rho.pos.isHermitian.eigenvalues i)) =
        (∑ i, xlog2 (rho.pos.isHermitian.eigenvalues i)) * Real.log 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    exact (xlog2_mul_log2_self_of_nonneg (rho.pos.eigenvalues_nonneg i)).symm
  rw [State.vonNeumann]
  simp [hsum]

/-- Near zero, the positive right difference quotient
`(x^(1+p)-x)/p` is controlled by the continuous `0 log 0` envelope. -/
theorem abs_rpow_one_add_sub_self_div_le_neg_mul_log_of_Icc
    {x p : Real} (hp : 0 < p) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |(x ^ (1 + p) - x) / p| ≤ -(x * Real.log x) := by
  rcases lt_or_eq_of_le hx0 with hxpos | rfl
  · have hpne : p ≠ 0 := ne_of_gt hp
    have hpow_add : x ^ (1 + p) = x * x ^ p := by
      rw [Real.rpow_add hxpos 1 p, Real.rpow_one]
    have hxp_le_one : x ^ p ≤ 1 := Real.rpow_le_one hx0 hx1 hp.le
    have hdiff_nonpos : x ^ (1 + p) - x ≤ 0 := by
      rw [hpow_add]
      have hmul : x * x ^ p ≤ x * 1 :=
        mul_le_mul_of_nonneg_left hxp_le_one hx0
      linarith
    have hquot_nonpos : (x ^ (1 + p) - x) / p ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hdiff_nonpos hp.le
    rw [abs_of_nonpos hquot_nonpos]
    have hlog_le : p * Real.log x ≤ x ^ p - 1 := by
      have h :=
        Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hxpos p)
      simpa [Real.log_rpow hxpos p] using h
    have hmain : 1 - x ^ p ≤ -p * Real.log x := by
      linarith
    have hscaled :
        x * (1 - x ^ p) / p ≤ x * (-p * Real.log x) / p := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmain hx0) hp.le
    have hleft :
        -((x ^ (1 + p) - x) / p) = x * (1 - x ^ p) / p := by
      rw [hpow_add]
      field_simp [hpne]
      ring
    have hright :
        x * (-p * Real.log x) / p = -(x * Real.log x) := by
      field_simp [hpne]
    calc
      -((x ^ (1 + p) - x) / p)
          = x * (1 - x ^ p) / p := hleft
      _ ≤ x * (-p * Real.log x) / p := hscaled
      _ = -(x * Real.log x) := hright
  · have hp1 : (1 : Real) + p ≠ 0 := by linarith
    simp [Real.zero_rpow hp1]

/-- The scalar self-entropy difference quotient converges uniformly on compact
nonnegative intervals, including the singular endpoint `x = 0`. -/
theorem tendstoUniformlyOn_rpow_one_add_sub_self_div_mul_log_Icc
    {M : Real} (hM : 0 ≤ M) :
    TendstoUniformlyOn
      (fun p : Real => fun x : Real => (x ^ (1 + p) - x) / p)
      (fun x : Real => x * Real.log x)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (Set.Icc (0 : Real) M) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hmul_tendsto :
      Filter.Tendsto (fun x : Real => x * Real.log x)
        (nhds (0 : Real)) (nhds (0 : Real)) := by
    simpa [Real.log_zero] using (Real.continuous_mul_log.tendsto (0 : Real))
  have hsmall_eventually :
      ∀ᶠ x : Real in nhds (0 : Real),
        dist (x * Real.log x) (0 : Real) < ε / 3 := by
    exact hmul_tendsto (Metric.ball_mem_nhds _ hε3)
  rw [Metric.eventually_nhds_iff] at hsmall_eventually
  rcases hsmall_eventually with ⟨δ0, hδ0pos, hδ0small⟩
  let δ : Real := min (δ0 / 2) 1
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (half_pos hδ0pos) zero_lt_one
  have hδle1 : δ ≤ 1 := by
    dsimp [δ]
    exact min_le_right _ _
  have hδltδ0 : δ < δ0 := by
    calc
      δ ≤ δ0 / 2 := by
        dsimp [δ]
        exact min_le_left _ _
      _ < δ0 := by linarith
  have hawayBase :
      TendstoUniformlyOn
        (fun p : Real => fun x : Real => p⁻¹ * (x ^ p - 1))
        Real.log
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (Set.Icc δ M) := by
    have hloc := Real.tendstoLocallyUniformlyOn_rpow_sub_one_log
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi] at hloc
    exact hloc (Set.Icc δ M)
      (by
        intro x hx
        exact lt_of_lt_of_le hδpos hx.1)
      isCompact_Icc
  rw [Metric.tendstoUniformlyOn_iff] at hawayBase
  have hMplus_pos : 0 < M + 1 := by linarith
  have hηpos : 0 < ε / (M + 1) := div_pos hε hMplus_pos
  have hawayε := hawayBase (ε / (M + 1)) hηpos
  filter_upwards [self_mem_nhdsWithin, hawayε] with p hp hpaway x hx
  by_cases hxsmall : x < δ
  · have hx0 : 0 ≤ x := hx.1
    have hxleδ : x ≤ δ := le_of_lt hxsmall
    have hxle1 : x ≤ 1 := hxleδ.trans hδle1
    have hxball : dist x (0 : Real) < δ0 := by
      rw [Real.dist_eq]
      have habs : |x - 0| = x := by
        simp [abs_of_nonneg hx0]
      rw [habs]
      exact lt_of_le_of_lt hxleδ hδltδ0
    have hxlog_small : |x * Real.log x| < ε / 3 := by
      have := hδ0small hxball
      simpa [Real.dist_eq, sub_zero, abs_of_nonneg] using this
    have hg_bound :
        |(x ^ (1 + p) - x) / p| ≤ -(x * Real.log x) :=
      abs_rpow_one_add_sub_self_div_le_neg_mul_log_of_Icc hp hx0 hxle1
    have hxlog_abs : |x * Real.log x| = -(x * Real.log x) :=
      abs_of_nonpos (Real.mul_log_nonpos hx0 hxle1)
    rw [Real.dist_eq]
    have htri :
        |x * Real.log x - (x ^ (1 + p) - x) / p| ≤
          |x * Real.log x| + |(x ^ (1 + p) - x) / p| := by
      calc
        |x * Real.log x - (x ^ (1 + p) - x) / p|
            = |x * Real.log x + -((x ^ (1 + p) - x) / p)| := by
                rw [sub_eq_add_neg]
        _ ≤ |x * Real.log x| + |-((x ^ (1 + p) - x) / p)| :=
            abs_add_le _ _
        _ = |x * Real.log x| + |(x ^ (1 + p) - x) / p| := by
            rw [abs_neg]
    have hsum_bound :
        |x * Real.log x| + |(x ^ (1 + p) - x) / p| <
          ε / 3 + ε / 3 := by
      rw [hxlog_abs] at hxlog_small ⊢
      exact add_lt_add hxlog_small (lt_of_le_of_lt hg_bound hxlog_small)
    have htwo : ε / 3 + ε / 3 < ε := by linarith
    exact lt_of_le_of_lt htri (hsum_bound.trans htwo)
  · have hxaway : x ∈ Set.Icc δ M := ⟨le_of_not_gt hxsmall, hx.2⟩
    have hpne : p ≠ 0 := ne_of_gt hp
    have hxpos : 0 < x := lt_of_lt_of_le hδpos hxaway.1
    have hx0 : 0 ≤ x := le_of_lt hxpos
    have hquot :
        (x ^ (1 + p) - x) / p = x * (p⁻¹ * (x ^ p - 1)) := by
      rw [Real.rpow_add hxpos 1 p, Real.rpow_one]
      field_simp [hpne]
    rw [hquot, Real.dist_eq]
    have hpaway_x := hpaway x hxaway
    rw [Real.dist_eq] at hpaway_x
    have hxabs_lt : |x| < M + 1 := by
      rw [abs_of_nonneg hx0]
      linarith [hxaway.2]
    have hfactor :
        |x * Real.log x - x * (p⁻¹ * (x ^ p - 1))| =
          |x| * |Real.log x - p⁻¹ * (x ^ p - 1)| := by
      rw [← mul_sub, abs_mul]
    rw [hfactor]
    have hle :
        |x| * |Real.log x - p⁻¹ * (x ^ p - 1)| ≤
          |x| * (ε / (M + 1)) :=
      mul_le_mul_of_nonneg_left hpaway_x.le (abs_nonneg x)
    have hlt :
        |x| * (ε / (M + 1)) < (M + 1) * (ε / (M + 1)) :=
      mul_lt_mul_of_pos_right hxabs_lt hηpos
    have hscale : (M + 1) * (ε / (M + 1)) = ε := by
      field_simp [(ne_of_gt hMplus_pos)]
    exact lt_of_le_of_lt hle (hlt.trans_eq hscale)

/-- Joint CFC trace endpoint for the moving scalar functions
`x ↦ (x^(1+p)-x)/p` along PSD matrices converging to a state. -/
theorem cfc_trace_rpow_one_add_sub_self_div_tendsto_of_tendsto_posSemidef
    {F : Real -> CMatrix a} (rho : State a)
    (hF :
      Filter.Tendsto F (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds rho.matrix))
    (hFpsd :
      ∀ᶠ p : Real in nhdsWithin (0 : Real) (Set.Ioi 0), (F p).PosSemidef) :
    Filter.Tendsto
      (fun p : Real =>
        ((cfc (fun x : Real => (x ^ (1 + p) - x) / p) (F p)).trace).re)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds ((cfc (fun x : Real => x * Real.log x) rho.matrix).trace).re) := by
  haveI : Nonempty a := rho.nonempty
  let M : Real := ‖rho.matrix‖ + 2
  let S : Set Real := Set.Icc (0 : Real) M
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hMnonneg : 0 ≤ M := le_of_lt hMpos
  let G : Real -> (Real →ᵤ[{S}] Real) := fun p =>
    UniformOnFun.ofFun {S} (fun x : Real => (x ^ (1 + p) - x) / p)
  let G0 : Real →ᵤ[{S}] Real :=
    UniformOnFun.ofFun {S} (fun x : Real => x * Real.log x)
  have hGunif :
      TendstoUniformlyOn
        (fun p : Real => fun x : Real => (x ^ (1 + p) - x) / p)
        (fun x : Real => x * Real.log x)
        (nhdsWithin (0 : Real) (Set.Ioi 0)) S := by
    simpa [S] using
      (tendstoUniformlyOn_rpow_one_add_sub_self_div_mul_log_Icc
        (M := M) hMnonneg)
  have hG : Filter.Tendsto G (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds G0) := by
    rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn]
    intro s hs
    simp only [Set.mem_singleton_iff] at hs
    subst hs
    simpa [G, G0, UniformOnFun.toFun_ofFun] using hGunif
  let pair : Real -> (Real →ᵤ[{S}] Real) × CMatrix a := fun p => (G p, F p)
  let pair0 : (Real →ᵤ[{S}] Real) × CMatrix a := (G0, rho.matrix)
  have hpair : Filter.Tendsto pair (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds pair0) := by
    simpa [pair, pair0, nhds_prod_eq] using hG.prodMk hF
  let domain : Set ((Real →ᵤ[{S}] Real) × CMatrix a) :=
    {f : Real →ᵤ[{S}] Real | ContinuousOn (UniformOnFun.toFun {S} f) S} ×ˢ
      {A : CMatrix a | IsSelfAdjoint A ∧ spectrum Real A ⊆ S}
  have hG0cont : ContinuousOn (UniformOnFun.toFun {S} G0) S := by
    simpa [G0, UniformOnFun.toFun_ofFun] using
      Real.continuous_mul_log.continuousOn
  have hspec_rho : spectrum Real rho.matrix ⊆ S := by
    intro x hx
    constructor
    · exact spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr rho.pos) hx
    · have hxabs : |x| ≤ ‖rho.matrix‖ := by
        simpa [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem hx
      have hxle : x ≤ ‖rho.matrix‖ := le_trans (le_abs_self x) hxabs
      dsimp [S, M]
      linarith
  have hpair0_mem : pair0 ∈ domain := by
    constructor
    · exact hG0cont
    · constructor
      · exact Matrix.IsHermitian.isSelfAdjoint rho.pos.isHermitian
      · exact hspec_rho
  have hevent_domain : ∀ᶠ p : Real in nhdsWithin (0 : Real) (Set.Ioi 0),
      pair p ∈ domain := by
    have hclose : ∀ᶠ p : Real in nhdsWithin (0 : Real) (Set.Ioi 0),
        dist (F p) rho.matrix < 1 := by
      exact hF (Metric.ball_mem_nhds _ zero_lt_one)
    filter_upwards [self_mem_nhdsWithin, hFpsd, hclose] with p hp_pos hp_psd hp_close
    constructor
    · dsimp [pair, G, domain]
      have hpowCont :
          ContinuousOn (fun x : Real => x ^ (1 + p)) S :=
        (Real.continuous_rpow_const (by
          have hp_gt : 0 < p := hp_pos
          linarith)).continuousOn
      exact hpowCont.sub continuousOn_id |>.div_const p
    · constructor
      · exact Matrix.IsHermitian.isSelfAdjoint hp_psd.isHermitian
      · intro x hx
        constructor
        · exact spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hp_psd) hx
        · have hxabs : |x| ≤ ‖F p‖ := by
            simpa [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem hx
          have hnorm_le : ‖F p‖ < ‖rho.matrix‖ + 1 := by
            have hdist_norm : ‖F p - rho.matrix‖ < 1 := by
              simpa [dist_eq_norm] using hp_close
            have := norm_le_norm_add_norm_sub' (F p) rho.matrix
            nlinarith
          have hxle : x < ‖rho.matrix‖ + 1 :=
            lt_of_le_of_lt (le_trans (le_abs_self x) hxabs) hnorm_le
          dsimp [S, M]
          linarith
  have hwithin : Filter.Tendsto pair
      (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhdsWithin pair0 domain) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hpair, hevent_domain⟩
  have hcont :=
    (continuousOn_cfc_setProd (A := CMatrix a) (s := S) isCompact_Icc).continuousWithinAt
      hpair0_mem
  have hcfc : Filter.Tendsto
      (fun p : Real => cfc (UniformOnFun.toFun {S} (G p)) (F p))
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (cfc (UniformOnFun.toFun {S} G0) rho.matrix)) := by
    simpa [pair, pair0] using hcont.tendsto.comp hwithin
  have htraceCont : Continuous fun M : CMatrix a => M.trace :=
    Continuous.matrix_trace continuous_id
  have htrace :=
    (Complex.continuous_re.tendsto _).comp (htraceCont.tendsto _ |>.comp hcfc)
  simpa [G, G0, UniformOnFun.toFun_ofFun] using htrace

/-- CFC self endpoint for the sandwiched inner operator with positive-definite
reference. -/
theorem sandwichedRenyiReferenceInner_cfc_self_endpoint_posDef
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef) :
    Filter.Tendsto
      (fun p : Real =>
        ((cfc (fun x : Real => (x ^ (1 + p) - x) / p)
          (sandwichedRenyiReferenceInner rho sigma (1 + p))).trace).re)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (-rho.vonNeumann * Real.log 2)) := by
  have hEndpoint :=
    cfc_trace_rpow_one_add_sub_self_div_tendsto_of_tendsto_posSemidef
      (F := fun p : Real => sandwichedRenyiReferenceInner rho sigma (1 + p))
      rho
      (sandwichedRenyiReferenceInner_one_add_tendsto_state_matrix_posDef rho hSigma)
      (Filter.Eventually.of_forall fun p =>
        sandwichedRenyiReferenceInner_posSemidef rho hSigma.posSemidef (1 + p))
  simpa [trace_cfc_mul_log_state_eq_neg_vonNeumann_mul_log2 rho] using hEndpoint

/-- PSD trace-power self difference quotients are CFC trace difference
quotients.

This algebraic bridge turns
`(Tr A^(1+p) - Tr A) / p` into the trace of the continuous scalar function
`x ↦ (x^(1+p) - x) / p` applied by CFC. -/
theorem psdTracePower_one_add_sub_trace_div_eq_trace_cfc_rpow_sub_self_div
    {A : CMatrix a} (hA : A.PosSemidef) {p : Real} (hp : 0 < p) :
    (psdTracePower A hA (1 + p) - A.trace.re) / p =
      ((cfc (fun x : Real => (x ^ (1 + p) - x) / p) A).trace).re := by
  have hpne : p ≠ 0 := ne_of_gt hp
  have hpowCont :
      ContinuousOn (fun x : Real => x ^ (1 + p)) (spectrum Real A) :=
    (Real.continuous_rpow_const (by linarith : 0 ≤ 1 + p)).continuousOn
  have hsubCont :
      ContinuousOn (fun x : Real => x ^ (1 + p) - x) (spectrum Real A) :=
    hpowCont.sub continuousOn_id
  have hcfc :
      cfc (fun x : Real => (x ^ (1 + p) - x) / p) A =
        (p⁻¹ : Real) • (CFC.rpow A (1 + p) - A) := by
    have hfun :
        (fun x : Real => (x ^ (1 + p) - x) / p) =
          (fun x : Real => p⁻¹ • (x ^ (1 + p) - x)) := by
      funext x
      simp [div_eq_mul_inv, mul_comm]
    rw [hfun]
    rw [cfc_smul _ (hf := hsubCont)]
    rw [show cfc (fun x : Real => x ^ (1 + p) - x) A =
        cfc (fun x : Real => x ^ (1 + p)) A - cfc (fun x : Real => x) A from
      cfc_sub (fun x : Real => x ^ (1 + p)) (fun x : Real => x) A
        (hf := hpowCont) (hg := continuousOn_id)]
    rw [cfc_id' Real A (ha := Matrix.IsHermitian.isSelfAdjoint hA.isHermitian)]
    have hrpowReal :
        CFC.rpow A (1 + p) = cfc (fun x : Real => x ^ (1 + p)) A := by
      simpa [CFC.rpow_eq_pow] using
        (CFC.rpow_eq_cfc_real (a := A) (y := 1 + p)
          (ha := Matrix.nonneg_iff_posSemidef.mpr hA))
    rw [← hrpowReal]
  rw [psdTracePower_eq, hcfc, Matrix.trace_smul, Matrix.trace_sub]
  simp [div_eq_mul_inv, hpne, mul_comm]

/-- A CFC self-endpoint for the moving sandwiched inner operator implies the
raw self trace-power endpoint used by the high-`alpha` bridge. -/
theorem sandwichedRenyiReferenceInner_power_minus_trace_slope_tendsto_of_cfc_self_endpoint
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    {L : Real}
    (hEndpoint :
      Filter.Tendsto
        (fun p : Real =>
          ((cfc (fun x : Real => (x ^ (1 + p) - x) / p)
            (sandwichedRenyiReferenceInner rho sigma (1 + p))).trace).re)
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds L)) :
    Filter.Tendsto
      (fun p : Real =>
        (psdTracePower (sandwichedRenyiReferenceInner rho sigma (1 + p))
            (sandwichedRenyiReferenceInner_posSemidef rho hSigma (1 + p))
            (1 + p) -
          (sandwichedRenyiReferenceInner rho sigma (1 + p)).trace.re) / p)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds L) := by
  refine hEndpoint.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact
    (psdTracePower_one_add_sub_trace_div_eq_trace_cfc_rpow_sub_self_div
      (sandwichedRenyiReferenceInner_posSemidef rho hSigma (1 + p)) hp).symm

/-- CFC self-endpoint form of the positive-definite reference raw
trace-power endpoint.

The reference trace derivative is supplied by
`sandwichedRenyiReferenceInner_trace_re_one_add_slope_tendsto_neg_trace_mul_psdLog_posDef`;
the only remaining input is the CFC endpoint for
`x ↦ (x^(1+p)-x)/p` along the moving inner operator. -/
theorem sandwichedRenyiReferenceInner_tracePower_slope_tendsto_of_cfc_self_endpoint_posDef
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    (hEndpoint :
      Filter.Tendsto
        (fun p : Real =>
          ((cfc (fun x : Real => (x ^ (1 + p) - x) / p)
            (sandwichedRenyiReferenceInner rho sigma (1 + p))).trace).re)
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds (-rho.vonNeumann * Real.log 2))) :
    Filter.Tendsto
      (fun p : Real =>
        (psdTracePower (sandwichedRenyiReferenceInner rho sigma (1 + p))
            (sandwichedRenyiReferenceInner_posSemidef
              rho hSigma.posSemidef (1 + p))
            (1 + p) - 1) / p)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds
        (-rho.vonNeumann * Real.log 2 -
          (rho.matrix * psdLog sigma hSigma).trace.re)) := by
  exact
    sandwichedRenyiReferenceInner_tracePower_slope_tendsto_of_power_minus_trace_slope_posDef
      rho hSigma
      (sandwichedRenyiReferenceInner_power_minus_trace_slope_tendsto_of_cfc_self_endpoint
        rho hSigma.posSemidef hEndpoint)

/-- Positive-definite reference raw trace-power endpoint at `alpha = 1+`.

This closes the endpoint input previously supplied as a hypothesis: the moving
CFC self term is handled by the zero-inclusive uniform scalar endpoint above. -/
theorem sandwichedRenyiReferenceInner_tracePower_slope_tendsto_posDef
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef) :
    Filter.Tendsto
      (fun p : Real =>
        (psdTracePower (sandwichedRenyiReferenceInner rho sigma (1 + p))
            (sandwichedRenyiReferenceInner_posSemidef
              rho hSigma.posSemidef (1 + p))
            (1 + p) - 1) / p)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds
        (-rho.vonNeumann * Real.log 2 -
          (rho.matrix * psdLog sigma hSigma).trace.re)) := by
  exact
    sandwichedRenyiReferenceInner_tracePower_slope_tendsto_of_cfc_self_endpoint_posDef
      rho hSigma
      (sandwichedRenyiReferenceInner_cfc_self_endpoint_posDef rho hSigma)

/-- Spectral trace-power self endpoint for a density state.

This identifies the right derivative of `Tr rho^(1+p)` at `p = 0` with the
natural-log version of the von Neumann entropy contribution. -/
theorem state_psdTracePower_one_add_sub_one_div_tendsto_neg_vonNeumann_mul_log2
    (rho : State a) :
    Filter.Tendsto
      (fun p : Real => (psdTracePower rho.matrix rho.pos (1 + p) - 1) / p)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (-rho.vonNeumann * Real.log 2)) := by
  let d : a -> Real := fun i => rho.pos.isHermitian.eigenvalues i
  have hd : ∀ i, 0 ≤ d i := fun i => rho.pos.eigenvalues_nonneg i
  have hsumOne : (∑ i, d i) = 1 := by
    have htrace := congrArg Complex.re rho.pos.isHermitian.trace_eq_sum_eigenvalues
    simpa [d] using htrace.symm.trans (congrArg Complex.re rho.trace_eq_one)
  have htarget :
      (∑ i, d i * Real.log (d i)) = -rho.vonNeumann * Real.log 2 := by
    calc
      (∑ i, d i * Real.log (d i))
          = ∑ i, xlog2 (d i) * Real.log 2 := by
              refine Finset.sum_congr rfl ?_
              intro i _
              exact (xlog2_mul_log2_self_of_nonneg (hd i)).symm
      _ = (∑ i, xlog2 (d i)) * Real.log 2 := by
              rw [Finset.sum_mul]
      _ = -rho.vonNeumann * Real.log 2 := by
              simp [State.vonNeumann, d]
  have hsum :=
    finite_sum_rpow_one_add_sub_self_div_tendsto_sum_mul_log d hd
  have hsum' :
      Filter.Tendsto
        (fun p : Real => (psdTracePower rho.matrix rho.pos (1 + p) - 1) / p)
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds (∑ i, d i * Real.log (d i))) := by
    refine hsum.congr' ?_
    filter_upwards with p
    rw [← psdTracePower_eq_sum_eigenvalues_rpow rho.matrix rho.pos (1 + p)]
    simp [psdTracePower, d, hsumOne]
  simpa [htarget] using hsum'

/-- Turning a value-slope endpoint at `1` into a natural-log slope endpoint.

This isolates the elementary real-analysis step used after proving a raw
trace-power derivative: if `T -> 1` and `(T - 1) / denom -> L`, then
`log T / denom -> L`.  The `dslope` formulation handles points where `T = 1`
without requiring an eventual `T ≠ 1` side condition. -/
theorem real_log_slope_tendsto_of_value_slope_tendsto
    {β : Type*} {l : Filter β} {T denom : β -> Real} {L : Real}
    (hT : Filter.Tendsto T l (nhds 1))
    (hslope : Filter.Tendsto (fun b => (T b - 1) / denom b) l (nhds L))
    (hdenom : ∀ᶠ b in l, denom b ≠ 0) :
    Filter.Tendsto (fun b => Real.log (T b) / denom b) l (nhds L) := by
  have hlogSlope :
      Filter.Tendsto (dslope Real.log 1) (nhds 1) (nhds (1 : Real)) := by
    have hcont : ContinuousAt (dslope Real.log 1) (1 : Real) :=
      continuousAt_dslope_same.2
        (Real.hasDerivAt_log one_ne_zero).differentiableAt
    simpa [dslope_same, Real.deriv_log] using hcont.tendsto
  have hprod :
      Filter.Tendsto
        (fun b => dslope Real.log 1 (T b) * ((T b - 1) / denom b))
        l (nhds (1 * L)) :=
    (hlogSlope.comp hT).mul hslope
  have hprod' :
      Filter.Tendsto
        (fun b => dslope Real.log 1 (T b) * ((T b - 1) / denom b))
        l (nhds L) := by
    simpa using hprod
  refine hprod'.congr' ?_
  filter_upwards [hdenom] with b hb
  by_cases hTb : T b = 1
  · simp [hTb, Real.log_one]
  · have hsub : T b - 1 ≠ 0 := sub_ne_zero.mpr hTb
    rw [dslope_of_ne Real.log hTb]
    simp [slope, Real.log_one, hb, div_eq_mul_inv, mul_comm, mul_assoc]
    calc
      (T b - 1) * ((T b - 1)⁻¹ * Real.log (T b))
          = ((T b - 1) * (T b - 1)⁻¹) * Real.log (T b) := by ring
      _ = Real.log (T b) := by rw [mul_inv_cancel₀ hsub, one_mul]

/-- Base-2 version of `real_log_slope_tendsto_of_value_slope_tendsto`. -/
theorem real_log2_slope_tendsto_of_value_slope_tendsto
    {β : Type*} {l : Filter β} {T denom : β -> Real} {L : Real}
    (hT : Filter.Tendsto T l (nhds 1))
    (hslope : Filter.Tendsto (fun b => (T b - 1) / denom b) l (nhds L))
    (hdenom : ∀ᶠ b in l, denom b ≠ 0) :
    Filter.Tendsto (fun b => log2 (T b) / denom b) l
      (nhds (L / Real.log 2)) := by
  have hlog :=
    real_log_slope_tendsto_of_value_slope_tendsto hT hslope hdenom
  have hdiv := hlog.div_const (Real.log 2)
  refine hdiv.congr' ?_
  filter_upwards with b
  ring_nf
  simp [log2, div_eq_mul_inv, mul_comm, mul_assoc]

/-- A finite difference-quotient endpoint forces the underlying value to
converge to the base point when the denominator tends to zero. -/
theorem real_value_tendsto_one_of_sub_div_tendsto
    {β : Type*} {l : Filter β} {T denom : β -> Real} {L : Real}
    (hdenom0 : Filter.Tendsto denom l (nhds 0))
    (hslope : Filter.Tendsto (fun b => (T b - 1) / denom b) l (nhds L))
    (hdenom : ∀ᶠ b in l, denom b ≠ 0) :
    Filter.Tendsto T l (nhds 1) := by
  have hprod :
      Filter.Tendsto
        (fun b => ((T b - 1) / denom b) * denom b)
        l (nhds (L * 0)) :=
    hslope.mul hdenom0
  have hsub :
      Filter.Tendsto (fun b => T b - 1) l (nhds 0) := by
    have hprod0 :
        Filter.Tendsto
          (fun b => ((T b - 1) / denom b) * denom b)
          l (nhds 0) := by
      simpa using hprod
    refine hprod0.congr' ?_
    filter_upwards [hdenom] with b hb
    field_simp [hb]
  have hadd :
      Filter.Tendsto (fun b => (T b - 1) + 1) l (nhds (0 + 1)) :=
    hsub.add tendsto_const_nhds
  simpa using hadd

/-- The right-neighborhood filter `alpha -> 1+` on orders satisfying
`1 < alpha`. -/
def relativeEntropyHighAlphaRightToOne : Filter {alpha : Real // 1 < alpha} :=
  Filter.comap (fun alpha : {alpha : Real // 1 < alpha} => alpha.1)
    (nhdsWithin (1 : Real) (Set.Ioi 1))

/-- The right-neighborhood filter `alpha -> 1+` is nontrivial on the subtype
`1 < alpha`. -/
theorem relativeEntropyHighAlphaRightToOne_neBot :
    Filter.NeBot relativeEntropyHighAlphaRightToOne := by
  unfold relativeEntropyHighAlphaRightToOne
  refine Filter.comap_neBot ?_
  intro t ht
  have hflt :
      t ∩ Set.Ioi (1 : Real) ∈ nhdsWithin (1 : Real) (Set.Ioi 1) := by
    exact Filter.inter_mem ht self_mem_nhdsWithin
  haveI : Filter.NeBot (nhdsWithin (1 : Real) (Set.Ioi 1)) :=
    nhdsWithin_Ioi_neBot (α := Real) (a := 1) (b := 1) le_rfl
  rcases Filter.nonempty_of_mem hflt with ⟨x, hx⟩
  exact ⟨⟨x, hx.2⟩, hx.1⟩

/-- Along the high-`alpha` right-neighborhood filter, `alpha - 1` tends to
zero. -/
theorem relativeEntropyHighAlphaRightToOne_sub_tendsto_zero :
    Filter.Tendsto
      (fun alpha : {alpha : Real // 1 < alpha} => alpha.1 - 1)
      relativeEntropyHighAlphaRightToOne
      (nhds 0) := by
  unfold relativeEntropyHighAlphaRightToOne
  have hsub :
      Filter.Tendsto (fun x : Real => x - 1)
        (nhdsWithin (1 : Real) (Set.Ioi 1)) (nhds 0) := by
    have hxWithin :
        Filter.Tendsto (fun x : Real => x)
          (nhdsWithin (1 : Real) (Set.Ioi 1))
          (nhdsWithin (1 : Real) (Set.Ioi 1)) :=
      tendsto_id
    have hx : Filter.Tendsto (fun x : Real => x)
        (nhdsWithin (1 : Real) (Set.Ioi 1)) (nhds 1) :=
      (tendsto_nhdsWithin_iff.mp hxWithin).1
    have hconst : Filter.Tendsto (fun _ : Real => (1 : Real))
        (nhdsWithin (1 : Real) (Set.Ioi 1)) (nhds 1) :=
      tendsto_const_nhds
    simpa using hx.sub hconst
  exact hsub.comp Filter.tendsto_comap

/-- Along the high-`alpha` right-neighborhood filter, `alpha - 1` tends to zero
from the right. -/
theorem relativeEntropyHighAlphaRightToOne_sub_tendsto_zero_within :
    Filter.Tendsto
      (fun alpha : {alpha : Real // 1 < alpha} => alpha.1 - 1)
      relativeEntropyHighAlphaRightToOne
      (nhdsWithin (0 : Real) (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  exact
    ⟨relativeEntropyHighAlphaRightToOne_sub_tendsto_zero,
      Filter.Eventually.of_forall fun alpha => sub_pos.mpr alpha.2⟩

/-- Positive-definite reference raw trace-power endpoint along the high-`alpha`
subtype filter. -/
theorem sandwichedRenyiReferenceInner_tracePower_slope_tendsto_posDef_highAlpha
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef) :
    Filter.Tendsto
      (fun alpha : {alpha : Real // 1 < alpha} =>
        (psdTracePower (sandwichedRenyiReferenceInner rho sigma alpha.1)
            (sandwichedRenyiReferenceInner_posSemidef
              rho hSigma.posSemidef alpha.1)
            alpha.1 - 1) / (alpha.1 - 1))
      relativeEntropyHighAlphaRightToOne
      (nhds
        (-rho.vonNeumann * Real.log 2 -
          (rho.matrix * psdLog sigma hSigma).trace.re)) := by
  have hp := sandwichedRenyiReferenceInner_tracePower_slope_tendsto_posDef rho hSigma
  have hsub := relativeEntropyHighAlphaRightToOne_sub_tendsto_zero_within
  have hcomp := hp.comp hsub
  refine hcomp.congr' ?_
  filter_upwards with alpha
  have hadd : (1 : Real) + (alpha.1 - 1) = alpha.1 := by ring
  simp [hadd, psdTracePower]

/-- The high-`alpha` sandwiched Renyi curve used to define the source-limit
relative entropy quantity. -/
def sandwichedRenyiPSDReferenceHighAlphaCurve
    (rho : State a) (sigma : CMatrix a) (hSigma : sigma.PosSemidef) :
    {alpha : Real // 1 < alpha} -> EReal :=
  fun alpha => sandwichedRenyiPSDReferenceE rho sigma hSigma alpha.1

/-- Source-limit extended-real PSD-reference relative entropy.

For supported inputs this is the `limsup` of the high-`alpha` sandwiched Renyi
relative entropy along `alpha -> 1+`; unsupported inputs use the standard
extended-real top branch. -/
noncomputable def relativeEntropyPSDReferenceE
    (rho : State a) (sigma : CMatrix a) (hSigma : sigma.PosSemidef) : EReal := by
  classical
  exact
    if Matrix.Supports rho.matrix sigma then
      Filter.limsup
        (sandwichedRenyiPSDReferenceHighAlphaCurve rho sigma hSigma)
        relativeEntropyHighAlphaRightToOne
    else
      (⊤ : EReal)

@[simp]
theorem relativeEntropyPSDReferenceE_eq_top_of_not_supports
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : ¬ Matrix.Supports rho.matrix sigma) :
    relativeEntropyPSDReferenceE rho sigma hSigma = (⊤ : EReal) := by
  simp [relativeEntropyPSDReferenceE, hSupport]

@[simp]
theorem relativeEntropyPSDReferenceE_eq_limsup_of_supports
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma) :
    relativeEntropyPSDReferenceE rho sigma hSigma =
      Filter.limsup
        (sandwichedRenyiPSDReferenceHighAlphaCurve rho sigma hSigma)
        relativeEntropyHighAlphaRightToOne := by
  simp [relativeEntropyPSDReferenceE, hSupport]

/-- Raw trace-power slope endpoint implies the high-`alpha` finite branch has
the trace-log endpoint.

This is the outer real-analysis bridge for the sandwiched `alpha -> 1+`
endpoint.  It leaves only the noncommutative raw trace-power derivative
`Tr[(sigma^s rho sigma^s)^alpha]` as the remaining mathematical input. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_tendsto_traceLogFinite_of_tracePower_slope
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma)
    (hTracePower :
      Filter.Tendsto
        (fun alpha : {alpha : Real // 1 < alpha} =>
          psdTracePower (sandwichedRenyiReferenceInner rho sigma alpha.1)
            (sandwichedRenyiReferenceInner_posSemidef rho hSigma alpha.1)
            alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds 1))
    (hTracePowerSlope :
      Filter.Tendsto
        (fun alpha : {alpha : Real // 1 < alpha} =>
          (psdTracePower (sandwichedRenyiReferenceInner rho sigma alpha.1)
              (sandwichedRenyiReferenceInner_posSemidef rho hSigma alpha.1)
              alpha.1 - 1) / (alpha.1 - 1))
        relativeEntropyHighAlphaRightToOne
        (nhds
          (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport *
            Real.log 2))) :
    Filter.Tendsto
      (fun alpha : {alpha : Real // 1 < alpha} =>
        sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hSigma alpha.1)
      relativeEntropyHighAlphaRightToOne
      (nhds (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport)) := by
  let T : {alpha : Real // 1 < alpha} -> Real := fun alpha =>
    psdTracePower (sandwichedRenyiReferenceInner rho sigma alpha.1)
      (sandwichedRenyiReferenceInner_posSemidef rho hSigma alpha.1)
      alpha.1
  let denom : {alpha : Real // 1 < alpha} -> Real := fun alpha => alpha.1 - 1
  change Filter.Tendsto T relativeEntropyHighAlphaRightToOne (nhds 1) at hTracePower
  change
    Filter.Tendsto (fun alpha : {alpha : Real // 1 < alpha} =>
      (T alpha - 1) / denom alpha) relativeEntropyHighAlphaRightToOne
      (nhds
        (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport *
          Real.log 2)) at hTracePowerSlope
  have hdenom : ∀ᶠ alpha in relativeEntropyHighAlphaRightToOne, denom alpha ≠ 0 :=
    Filter.Eventually.of_forall fun alpha => by
      dsimp [denom]
      exact ne_of_gt (sub_pos.mpr alpha.2)
  have hlog2 :=
    real_log2_slope_tendsto_of_value_slope_tendsto
      (T := T) (denom := denom) hTracePower hTracePowerSlope hdenom
  have hscale :
      (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport *
          Real.log 2) / Real.log 2 =
        relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport := by
    field_simp [(Real.log_pos one_lt_two).ne']
  have hscale' :
      Real.log 2 * ((Real.log 2)⁻¹ *
          relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport) =
        relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.log_pos one_lt_two)), one_mul]
  simpa [T, denom, sandwichedRenyiPSDReferenceHighAlphaFinite, one_div,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hscale, hscale'] using hlog2

/-- A raw trace-power slope endpoint already implies the value endpoint needed
by the high-`alpha` finite-branch bridge.

This form is closer to the remaining noncommutative endpoint obligation: the
only supplied input is the first-order trace-power expansion at `alpha = 1`. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_tendsto_traceLogFinite_of_tracePower_slope_only
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma)
    (hTracePowerSlope :
      Filter.Tendsto
        (fun alpha : {alpha : Real // 1 < alpha} =>
          (psdTracePower (sandwichedRenyiReferenceInner rho sigma alpha.1)
              (sandwichedRenyiReferenceInner_posSemidef rho hSigma alpha.1)
              alpha.1 - 1) / (alpha.1 - 1))
        relativeEntropyHighAlphaRightToOne
        (nhds
          (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport *
            Real.log 2))) :
    Filter.Tendsto
      (fun alpha : {alpha : Real // 1 < alpha} =>
        sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hSigma alpha.1)
      relativeEntropyHighAlphaRightToOne
      (nhds (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport)) := by
  let T : {alpha : Real // 1 < alpha} -> Real := fun alpha =>
    psdTracePower (sandwichedRenyiReferenceInner rho sigma alpha.1)
      (sandwichedRenyiReferenceInner_posSemidef rho hSigma alpha.1)
      alpha.1
  let denom : {alpha : Real // 1 < alpha} -> Real := fun alpha => alpha.1 - 1
  change
    Filter.Tendsto (fun alpha : {alpha : Real // 1 < alpha} =>
      (T alpha - 1) / denom alpha) relativeEntropyHighAlphaRightToOne
      (nhds
        (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport *
          Real.log 2)) at hTracePowerSlope
  have hdenom0 : Filter.Tendsto denom relativeEntropyHighAlphaRightToOne (nhds 0) := by
    simpa [denom] using relativeEntropyHighAlphaRightToOne_sub_tendsto_zero
  have hdenom : ∀ᶠ alpha in relativeEntropyHighAlphaRightToOne, denom alpha ≠ 0 :=
    Filter.Eventually.of_forall fun alpha => by
      dsimp [denom]
      exact ne_of_gt (sub_pos.mpr alpha.2)
  have hTracePower : Filter.Tendsto T relativeEntropyHighAlphaRightToOne (nhds 1) :=
    real_value_tendsto_one_of_sub_div_tendsto hdenom0 hTracePowerSlope hdenom
  exact
    sandwichedRenyiPSDReferenceHighAlphaFinite_tendsto_traceLogFinite_of_tracePower_slope
      rho hSigma hSupport hTracePower hTracePowerSlope

/-- A raw trace-power slope endpoint implies convergence of the high-`alpha`
finite branch to any declared real endpoint whose natural-log scaling is the
slope. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_tendsto_of_tracePower_slope_only
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (D : Real)
    (hTracePowerSlope :
      Filter.Tendsto
        (fun alpha : {alpha : Real // 1 < alpha} =>
          (psdTracePower (sandwichedRenyiReferenceInner rho sigma alpha.1)
              (sandwichedRenyiReferenceInner_posSemidef rho hSigma alpha.1)
              alpha.1 - 1) / (alpha.1 - 1))
        relativeEntropyHighAlphaRightToOne
        (nhds (D * Real.log 2))) :
    Filter.Tendsto
      (fun alpha : {alpha : Real // 1 < alpha} =>
        sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hSigma alpha.1)
      relativeEntropyHighAlphaRightToOne
      (nhds D) := by
  let T : {alpha : Real // 1 < alpha} -> Real := fun alpha =>
    psdTracePower (sandwichedRenyiReferenceInner rho sigma alpha.1)
      (sandwichedRenyiReferenceInner_posSemidef rho hSigma alpha.1)
      alpha.1
  let denom : {alpha : Real // 1 < alpha} -> Real := fun alpha => alpha.1 - 1
  change
    Filter.Tendsto (fun alpha : {alpha : Real // 1 < alpha} =>
      (T alpha - 1) / denom alpha) relativeEntropyHighAlphaRightToOne
      (nhds (D * Real.log 2)) at hTracePowerSlope
  have hdenom0 : Filter.Tendsto denom relativeEntropyHighAlphaRightToOne (nhds 0) := by
    simpa [denom] using relativeEntropyHighAlphaRightToOne_sub_tendsto_zero
  have hdenom : ∀ᶠ alpha in relativeEntropyHighAlphaRightToOne, denom alpha ≠ 0 :=
    Filter.Eventually.of_forall fun alpha => by
      dsimp [denom]
      exact ne_of_gt (sub_pos.mpr alpha.2)
  have hTracePower : Filter.Tendsto T relativeEntropyHighAlphaRightToOne (nhds 1) :=
    real_value_tendsto_one_of_sub_div_tendsto hdenom0 hTracePowerSlope hdenom
  have hlog2 :=
    real_log2_slope_tendsto_of_value_slope_tendsto
      (T := T) (denom := denom) hTracePower hTracePowerSlope hdenom
  have hscale : (D * Real.log 2) / Real.log 2 = D := by
    field_simp [(Real.log_pos one_lt_two).ne']
  have hscale' : Real.log 2 * ((Real.log 2)⁻¹ * D) = D := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.log_pos one_lt_two)), one_mul]
  have hscale'' : D * (Real.log 2 * (Real.log 2)⁻¹) = D := by
    rw [mul_inv_cancel₀ (ne_of_gt (Real.log_pos one_lt_two)), mul_one]
  simpa [T, denom, sandwichedRenyiPSDReferenceHighAlphaFinite, one_div,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hscale, hscale', hscale''] using hlog2

/-- Positive-definite reference high-`alpha` finite branch endpoint, in the
trace-log convention. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_tendsto_posDef_traceLog
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef) :
    Filter.Tendsto
      (fun alpha : {alpha : Real // 1 < alpha} =>
        sandwichedRenyiPSDReferenceHighAlphaFinite
          rho sigma hSigma.posSemidef alpha.1)
      relativeEntropyHighAlphaRightToOne
      (nhds
        (-rho.vonNeumann -
          ((rho.matrix * psdLog sigma hSigma).trace.re / Real.log 2))) := by
  refine
    sandwichedRenyiPSDReferenceHighAlphaFinite_tendsto_of_tracePower_slope_only
      rho hSigma.posSemidef
      (-rho.vonNeumann -
        ((rho.matrix * psdLog sigma hSigma).trace.re / Real.log 2)) ?_
  have hSlope :=
    sandwichedRenyiReferenceInner_tracePower_slope_tendsto_posDef_highAlpha
      rho hSigma
  have hscale :
      (-rho.vonNeumann -
          ((rho.matrix * psdLog sigma hSigma).trace.re / Real.log 2)) *
          Real.log 2 =
        -rho.vonNeumann * Real.log 2 -
          (rho.matrix * psdLog sigma hSigma).trace.re := by
    field_simp [(Real.log_pos one_lt_two).ne']
  simpa [hscale] using hSlope

/-- Quantum relative entropy against a positive-definite matrix reference is
nonnegative in the source trace-log convention, with no full-rank assumption on
the left state.

This is the `α -> 1+` endpoint of high-`α` PSD-reference Renyi
nonnegativity, itself obtained from DPI to the terminal one-outcome channel. -/
theorem relativeEntropy_posDefReferenceTraceLog_nonneg
    (ρ σ : State a) (hσ : σ.matrix.PosDef) :
    0 ≤ -ρ.vonNeumann -
      ((ρ.matrix * psdLog σ.matrix hσ).trace.re / Real.log 2) := by
  have hlim :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_tendsto_posDef_traceLog
      ρ hσ
  haveI : Filter.NeBot relativeEntropyHighAlphaRightToOne :=
    relativeEntropyHighAlphaRightToOne_neBot
  exact ge_of_tendsto hlim
    (Filter.Eventually.of_forall fun alpha =>
      sandwichedRenyiPSDReferenceHighAlphaFinite_nonneg_of_posDef_reference
        ρ σ hσ alpha)

/-- The finite trace-power endpoint lifts to the source-facing `EReal`
high-`alpha` PSD-reference curve on supported inputs. -/
theorem sandwichedRenyiPSDReferenceHighAlphaCurve_tendsto_traceLogFinite_of_tracePower_slope
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma)
    (hTracePower :
      Filter.Tendsto
        (fun alpha : {alpha : Real // 1 < alpha} =>
          psdTracePower (sandwichedRenyiReferenceInner rho sigma alpha.1)
            (sandwichedRenyiReferenceInner_posSemidef rho hSigma alpha.1)
            alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds 1))
    (hTracePowerSlope :
      Filter.Tendsto
        (fun alpha : {alpha : Real // 1 < alpha} =>
          (psdTracePower (sandwichedRenyiReferenceInner rho sigma alpha.1)
              (sandwichedRenyiReferenceInner_posSemidef rho hSigma alpha.1)
              alpha.1 - 1) / (alpha.1 - 1))
        relativeEntropyHighAlphaRightToOne
        (nhds
          (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport *
            Real.log 2))) :
    Filter.Tendsto
      (sandwichedRenyiPSDReferenceHighAlphaCurve rho sigma hSigma)
      relativeEntropyHighAlphaRightToOne
      (nhds (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport : EReal)) := by
  have hFinite :
      Filter.Tendsto
        (fun alpha : {alpha : Real // 1 < alpha} =>
          sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hSigma alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport)) :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_tendsto_traceLogFinite_of_tracePower_slope
      rho hSigma hSupport hTracePower hTracePowerSlope
  refine (EReal.tendsto_coe.mpr hFinite).congr' ?_
  filter_upwards with alpha
  unfold sandwichedRenyiPSDReferenceHighAlphaCurve
  rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt rho hSigma alpha.2]
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports rho hSigma alpha.1 hSupport]

/-- The raw trace-power slope endpoint alone lifts to the source-facing
`EReal` high-`alpha` PSD-reference curve on supported inputs. -/
theorem sandwichedRenyiPSDReferenceHighAlphaCurve_tendsto_traceLogFinite_of_tracePower_slope_only
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma)
    (hTracePowerSlope :
      Filter.Tendsto
        (fun alpha : {alpha : Real // 1 < alpha} =>
          (psdTracePower (sandwichedRenyiReferenceInner rho sigma alpha.1)
              (sandwichedRenyiReferenceInner_posSemidef rho hSigma alpha.1)
              alpha.1 - 1) / (alpha.1 - 1))
        relativeEntropyHighAlphaRightToOne
        (nhds
          (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport *
            Real.log 2))) :
    Filter.Tendsto
      (sandwichedRenyiPSDReferenceHighAlphaCurve rho sigma hSigma)
      relativeEntropyHighAlphaRightToOne
      (nhds (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport : EReal)) := by
  have hFinite :
      Filter.Tendsto
        (fun alpha : {alpha : Real // 1 < alpha} =>
          sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hSigma alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport)) :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_tendsto_traceLogFinite_of_tracePower_slope_only
      rho hSigma hSupport hTracePowerSlope
  refine (EReal.tendsto_coe.mpr hFinite).congr' ?_
  filter_upwards with alpha
  unfold sandwichedRenyiPSDReferenceHighAlphaCurve
  rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt rho hSigma alpha.2]
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports rho hSigma alpha.1 hSupport]

/-- Supported PSD references have the source trace-log endpoint after
compression to the positive spectral support. -/
theorem sandwichedRenyiPSDReferenceHighAlphaCurve_tendsto_traceLogFinite_of_supports
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma) :
    Filter.Tendsto
      (sandwichedRenyiPSDReferenceHighAlphaCurve rho sigma hSigma)
      relativeEntropyHighAlphaRightToOne
      (nhds (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport : EReal)) := by
  classical
  letI : Nonempty (psdSupportIndex sigma hSigma) :=
    psdSupportCompressedState_support_nonempty rho hSigma hSupport
  let rhoC : State (psdSupportIndex sigma hSigma) :=
    psdSupportCompressedState rho hSigma hSupport
  let sigmaC : CMatrix (psdSupportIndex sigma hSigma) :=
    psdSupportCompress sigma hSigma sigma
  have hSigmaC : sigmaC.PosDef := by
    simpa [sigmaC] using psdSupportCompressedState_reference_posDef hSigma
  have hFiniteC :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_tendsto_posDef_traceLog
      rhoC hSigmaC
  have hFiniteC' :
      Filter.Tendsto
        (fun alpha : {alpha : Real // 1 < alpha} =>
          sandwichedRenyiPSDReferenceHighAlphaFinite
            rhoC sigmaC hSigmaC.posSemidef alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport)) := by
    simpa [relativeEntropyPSDReferenceTraceLogFinite, rhoC, sigmaC, hSigmaC]
      using hFiniteC
  have hFinite :
      Filter.Tendsto
        (fun alpha : {alpha : Real // 1 < alpha} =>
          sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hSigma alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport)) := by
    refine hFiniteC'.congr' ?_
    filter_upwards with alpha
    exact
      (sandwichedRenyiPSDReferenceHighAlphaFinite_supportCompress_eq
        rho hSigma hSupport alpha.1 alpha.2).symm
  refine (EReal.tendsto_coe.mpr hFinite).congr' ?_
  filter_upwards with alpha
  unfold sandwichedRenyiPSDReferenceHighAlphaCurve
  rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt rho hSigma alpha.2]
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports rho hSigma alpha.1 hSupport]

/-- On the unsupported branch, the source-limit and trace-log conventions both
return `+infty`. -/
theorem relativeEntropyPSDReferenceE_eq_traceLogE_of_not_supports
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : ¬ Matrix.Supports rho.matrix sigma) :
    relativeEntropyPSDReferenceE rho sigma hSigma =
      relativeEntropyPSDReferenceTraceLogE rho sigma hSigma := by
  rw [relativeEntropyPSDReferenceE_eq_top_of_not_supports rho hSigma hSupport,
    relativeEntropyPSDReferenceTraceLogE_eq_top_of_not_supports rho hSigma hSupport]

/-- If the high-`alpha` sandwiched Renyi curve has the source trace-log endpoint
on the supported branch, then the source-limit convention agrees with the
trace-log convention there. -/
theorem relativeEntropyPSDReferenceE_eq_traceLogE_of_supports_of_tendsto
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma)
    (hEndpoint :
      Filter.Tendsto
        (sandwichedRenyiPSDReferenceHighAlphaCurve rho sigma hSigma)
        relativeEntropyHighAlphaRightToOne
        (nhds (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport : EReal))) :
    relativeEntropyPSDReferenceE rho sigma hSigma =
      relativeEntropyPSDReferenceTraceLogE rho sigma hSigma := by
  haveI : Filter.NeBot relativeEntropyHighAlphaRightToOne :=
    relativeEntropyHighAlphaRightToOne_neBot
  rw [relativeEntropyPSDReferenceE_eq_limsup_of_supports rho hSigma hSupport,
    relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports rho hSigma hSupport]
  exact Filter.Tendsto.limsup_eq hEndpoint

/-- A raw trace-power endpoint on the supported branch identifies the
source-limit and trace-log conventions. -/
theorem relativeEntropyPSDReferenceE_eq_traceLogE_of_supports_of_tracePower_slope
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma)
    (hTracePower :
      Filter.Tendsto
        (fun alpha : {alpha : Real // 1 < alpha} =>
          psdTracePower (sandwichedRenyiReferenceInner rho sigma alpha.1)
            (sandwichedRenyiReferenceInner_posSemidef rho hSigma alpha.1)
            alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds 1))
    (hTracePowerSlope :
      Filter.Tendsto
        (fun alpha : {alpha : Real // 1 < alpha} =>
          (psdTracePower (sandwichedRenyiReferenceInner rho sigma alpha.1)
              (sandwichedRenyiReferenceInner_posSemidef rho hSigma alpha.1)
              alpha.1 - 1) / (alpha.1 - 1))
        relativeEntropyHighAlphaRightToOne
        (nhds
          (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport *
            Real.log 2))) :
    relativeEntropyPSDReferenceE rho sigma hSigma =
      relativeEntropyPSDReferenceTraceLogE rho sigma hSigma := by
  exact
    relativeEntropyPSDReferenceE_eq_traceLogE_of_supports_of_tendsto
      rho hSigma hSupport
      (sandwichedRenyiPSDReferenceHighAlphaCurve_tendsto_traceLogFinite_of_tracePower_slope
        rho hSigma hSupport hTracePower hTracePowerSlope)

/-- A raw trace-power slope endpoint on the supported branch identifies the
source-limit and trace-log conventions; the value endpoint is derived from the
same first-order expansion. -/
theorem relativeEntropyPSDReferenceE_eq_traceLogE_of_supports_of_tracePower_slope_only
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma)
    (hTracePowerSlope :
      Filter.Tendsto
        (fun alpha : {alpha : Real // 1 < alpha} =>
          (psdTracePower (sandwichedRenyiReferenceInner rho sigma alpha.1)
              (sandwichedRenyiReferenceInner_posSemidef rho hSigma alpha.1)
              alpha.1 - 1) / (alpha.1 - 1))
        relativeEntropyHighAlphaRightToOne
        (nhds
          (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport *
            Real.log 2))) :
    relativeEntropyPSDReferenceE rho sigma hSigma =
      relativeEntropyPSDReferenceTraceLogE rho sigma hSigma := by
  exact
    relativeEntropyPSDReferenceE_eq_traceLogE_of_supports_of_tendsto
      rho hSigma hSupport
      (sandwichedRenyiPSDReferenceHighAlphaCurve_tendsto_traceLogFinite_of_tracePower_slope_only
        rho hSigma hSupport hTracePowerSlope)

/-- A pointwise endpoint theorem on the supported branch is enough to identify
the source-limit and trace-log conventions for all support cases. -/
theorem relativeEntropyPSDReferenceE_eq_traceLogE_of_supported_endpoint
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hEndpoint :
      ∀ hSupport : Matrix.Supports rho.matrix sigma,
        Filter.Tendsto
          (sandwichedRenyiPSDReferenceHighAlphaCurve rho sigma hSigma)
          relativeEntropyHighAlphaRightToOne
          (nhds (relativeEntropyPSDReferenceTraceLogFinite
            rho sigma hSigma hSupport : EReal))) :
    relativeEntropyPSDReferenceE rho sigma hSigma =
      relativeEntropyPSDReferenceTraceLogE rho sigma hSigma := by
  classical
  by_cases hSupport : Matrix.Supports rho.matrix sigma
  · exact relativeEntropyPSDReferenceE_eq_traceLogE_of_supports_of_tendsto
      rho hSigma hSupport (hEndpoint hSupport)
  · exact relativeEntropyPSDReferenceE_eq_traceLogE_of_not_supports
      rho hSigma hSupport

/-- The source-limit PSD-reference relative entropy agrees with the
source-facing trace-log support convention. -/
theorem relativeEntropyPSDReferenceE_eq_traceLogE
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef) :
    relativeEntropyPSDReferenceE rho sigma hSigma =
      relativeEntropyPSDReferenceTraceLogE rho sigma hSigma := by
  exact
    relativeEntropyPSDReferenceE_eq_traceLogE_of_supported_endpoint
      rho hSigma
      (fun hSupport =>
        sandwichedRenyiPSDReferenceHighAlphaCurve_tendsto_traceLogFinite_of_supports
          rho hSigma hSupport)

end State

end

end QIT
