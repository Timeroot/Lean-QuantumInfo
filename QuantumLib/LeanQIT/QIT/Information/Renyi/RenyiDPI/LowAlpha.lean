/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.RenyiDPI.HighAlpha
public import QIT.Information.Entropy.Log2Lemmas

/-!
# Low-alpha sandwiched Renyi DPI support

Low-alpha data-processing reductions, reverse-Holder and pinching support, and
channel composition helpers.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

namespace State

open RenyiDPI.Statement

/-- For `1 / 2 ≤ α < 1`, the negative logarithmic prefactor reverses the
trace-power order: a core trace-power expansion for the sandwiched inner
operator implies the full-rank channel DPI inequality.

This packages the precise operator inequality needed for the subunit Renyi
range without assuming DPI as a hypothesis. -/
theorem sandwichedRenyi_dataProcessing_le_of_inner_tracePower_ge_of_lt_one
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (hpower :
      psdTracePower (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α ≤
        psdTracePower (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α) α) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (by linarith) (ne_of_lt hα_lt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (by linarith) (ne_of_lt hα_lt_one) := by
  have hα_pos : 0 < α := by linarith
  have hα_ne_one : α ≠ 1 := ne_of_lt hα_lt_one
  rw [sandwichedRenyi_eq_log2_psdTracePower_inner
      (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ α hα_pos hα_ne_one,
    sandwichedRenyi_eq_log2_psdTracePower_inner
      ρ σ hρ hσ α hα_pos hα_ne_one]
  have hin_pos :
      0 <
        psdTracePower (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α :=
    sandwichedRenyiInner_psdTracePower_pos ρ σ hρ hσ α
  have hlog := log2_mono_of_pos hin_pos hpower
  have hcoef_nonpos : 1 / (α - 1) ≤ 0 := by
    have hcoef_neg : 1 / (α - 1) < 0 := by
      simpa [one_div] using (inv_lt_zero.2 (sub_neg.mpr hα_lt_one))
    exact le_of_lt hcoef_neg
  exact mul_le_mul_of_nonpos_left hlog hcoef_nonpos

/-- Low-`α` `Q`-functional form of the full-rank DPI reduction.

For `α < 1`, the logarithmic prefactor in `D̃_α` is negative, so the data
processing inequality is obtained from the reverse `Q`-functional inequality
`Q_α(ρ, σ) ≤ Q_α(Φρ, Φσ)`.  This is the bridge from the PSD-friendly
matrix-level route back to the current `State + PosDef` public theorem
surface. -/
theorem sandwichedRenyi_dataProcessing_le_of_lowAlphaQ_ge
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (hQ :
      sandwichedRenyiQ ρ.matrix σ.matrix ρ.pos σ.pos α ≤
        sandwichedRenyiQ (Φ.applyState ρ).matrix (Φ.applyState σ).matrix
          (Φ.applyState ρ).pos (Φ.applyState σ).pos α) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (by linarith) (ne_of_lt hα_lt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (by linarith) (ne_of_lt hα_lt_one) := by
  exact
    sandwichedRenyi_dataProcessing_le_of_inner_tracePower_ge_of_lt_one
      ρ σ Φ hρ hσ hρΦ hσΦ α hα_half hα_lt_one
      (by
        simpa [sandwichedRenyiQ_eq_psdTracePower_inner] using hQ)

/-- The reference-spectral pinching channel satisfies the full-rank sandwiched
Renyi DPI in the `1 / 2 ≤ α < 1` range. -/
theorem sandwichedRenyi_dataProcessing_referenceSpectralPinching_channel_statement_lt_one
    (ρ σ : State a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρP :
      (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
        ).pinchingChannel).applyState ρ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ
      ((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
        ).pinchingChannel)
      hρ hσ hρP
      (by
        rw [ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_self]
        exact hσ)
      α hα_half (ne_of_lt hα_lt_one) := by
  classical
  let P : ProjectiveMeasurement a a :=
    ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
  have hσP_eq : P.pinchingChannel.applyState σ = σ := by
    simpa [P] using
      ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_self σ
  have hσP : (P.pinchingChannel.applyState σ).matrix.PosDef := by
    rw [hσP_eq]
    exact hσ
  have hpower :
      psdTracePower (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α ≤
        psdTracePower
          (sandwichedRenyiInner (P.pinchingChannel.applyState ρ)
            (P.pinchingChannel.applyState σ) α)
          (sandwichedRenyiInner_posSemidef
            (P.pinchingChannel.applyState ρ) (P.pinchingChannel.applyState σ) α)
          α := by
    simpa [hσP_eq, P] using
      sandwichedRenyiInner_referenceSpectralPinching_tracePower_ge_of_le_one
        ρ σ α (by linarith) (le_of_lt hα_lt_one)
  have hDPI :=
    sandwichedRenyi_dataProcessing_le_of_inner_tracePower_ge_of_lt_one
      ρ σ P.pinchingChannel hρ hσ hρP hσP α hα_half hα_lt_one hpower
  simpa [sandwichedRenyi_dataProcessing_channel_statement, P, hσP_eq] using hDPI

/-- The reference-spectral pinching channel satisfies the local full-rank
sandwiched Renyi DPI statement throughout the source range
`1 / 2 ≤ α < 1` or `1 < α`. -/
theorem sandwichedRenyi_dataProcessing_referenceSpectralPinching_channel_statement
    (ρ σ : State a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρP :
      (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
        ).pinchingChannel).applyState ρ).matrix.PosDef)
    (α : ℝ) (hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ
      ((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
        ).pinchingChannel)
      hρ hσ hρP
      (by
        rw [ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_self]
        exact hσ)
      α
      (by
        rcases hα_range with hlt | hgt
        · exact hlt.1
        · linarith)
      (by
        rcases hα_range with hlt | hgt
        · exact ne_of_lt hlt.2
        · exact ne_of_gt hgt) := by
  rcases hα_range with hlt | hgt
  · exact sandwichedRenyi_dataProcessing_referenceSpectralPinching_channel_statement_lt_one
      ρ σ hρ hσ hρP α hlt.1 hlt.2
  · exact sandwichedRenyi_dataProcessing_referenceSpectralPinching_channel_statement_one_lt
      ρ σ hρ hσ hρP α hgt

/-- For `1 / 2 ≤ α < 1`, a Schatten-norm expansion for the sandwiched inner
operator implies the full-rank channel DPI inequality.

This is the matching reverse-Holder handoff for the subunit Renyi range: once
the proof route establishes that the input inner operator's PSD Schatten
expression is bounded by the output inner operator's expression, the negative
Renyi prefactor converts it to DPI. -/
theorem sandwichedRenyi_dataProcessing_le_of_inner_schattenPNorm_ge_of_lt_one
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (hnorm :
      psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) ⟨α, by linarith⟩ ≤
        psdSchattenPNorm
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
          ⟨α, by linarith⟩) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (by linarith) (ne_of_lt hα_lt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (by linarith) (ne_of_lt hα_lt_one) := by
  have hα_pos : 0 < α := by linarith
  have hpower :
      psdTracePower (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α ≤
        psdTracePower (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α) α :=
    psdTracePower_le_of_psdSchattenPNorm_le
      (sandwichedRenyiInner_posSemidef ρ σ α)
      (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
      hα_pos
      (sandwichedRenyiInner_psdTracePower_pos ρ σ hρ hσ α)
      (sandwichedRenyiInner_psdTracePower_pos
        (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ α)
      hnorm
  exact sandwichedRenyi_dataProcessing_le_of_inner_tracePower_ge_of_lt_one
    ρ σ Φ hρ hσ hρΦ hσΦ α hα_half hα_lt_one hpower

/-- Reverse-Holder witness handoff for the `1 / 2 ≤ α < 1` channel DPI route.

The remaining channel-specific task in this range is to construct a normalized
PSD side-state `N` supporting the input sandwiched inner operator and prove the
displayed trace objective is controlled by the output PSD Schatten expression.
This theorem then converts that source-shaped reverse-Holder bound into the
full-rank logarithmic DPI inequality. -/
theorem sandwichedRenyi_dataProcessing_le_of_reverseHolder_trace_le_of_lt_one
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    {N : CMatrix a} (hN : N.PosSemidef) (hNtr : N.trace.re = 1)
    (hSupport : Matrix.Supports (sandwichedRenyiInner ρ σ α) N)
    (htrace_le :
      ((sandwichedRenyiInner ρ σ α * CFC.rpow N (1 - 1 / α)).trace).re ≤
        psdSchattenPNorm
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
          ⟨α, by linarith⟩) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (by linarith) (ne_of_lt hα_lt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (by linarith) (ne_of_lt hα_lt_one) := by
  have hα_pos : 0 < α := by linarith
  have hnorm :
      psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) ⟨α, hα_pos⟩ ≤
        psdSchattenPNorm
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
          ⟨α, hα_pos⟩ :=
    psdSchattenPNorm_le_of_reverseHolder_trace_le
      (sandwichedRenyiInner_posSemidef ρ σ α) hN hNtr hSupport
      hα_pos hα_lt_one htrace_le
  exact
    sandwichedRenyi_dataProcessing_le_of_inner_schattenPNorm_ge_of_lt_one
      ρ σ Φ hρ hσ hρΦ hσΦ α hα_half hα_lt_one hnorm

/-- All-side-state reverse-Holder handoff for the `1 / 2 ≤ α < 1` channel
DPI route.

Because the full-rank input sandwiched inner operator has positive
`α`-power trace, the reverse-Holder optimizer supplies a normalized supporting
side-state. Thus it is enough to prove the displayed trace bound for every
normalized PSD side-state supporting the input inner operator. -/
theorem sandwichedRenyi_dataProcessing_le_of_all_reverseHolder_sideStates_trace_le_of_lt_one
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (htrace_all :
      ∀ {N : CMatrix a}, N.PosSemidef → N.trace.re = 1 →
        Matrix.Supports (sandwichedRenyiInner ρ σ α) N →
          ((sandwichedRenyiInner ρ σ α *
              CFC.rpow N (1 - 1 / α)).trace).re ≤
            psdSchattenPNorm
              (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
              (sandwichedRenyiInner_posSemidef
                (Φ.applyState ρ) (Φ.applyState σ) α)
              ⟨α, by linarith⟩) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (by linarith) (ne_of_lt hα_lt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (by linarith) (ne_of_lt hα_lt_one) := by
  have hα_pos : 0 < α := by linarith
  obtain ⟨N, hN, hNtr, hSupport, _hattain⟩ :=
    exists_psdTraceReverseHolder_sideState_attaining
      (sandwichedRenyiInner_posSemidef ρ σ α) hα_pos
      (sandwichedRenyiInner_psdTracePower_pos ρ σ hρ hσ α)
  exact
    sandwichedRenyi_dataProcessing_le_of_reverseHolder_trace_le_of_lt_one
      ρ σ Φ hρ hσ hρΦ hσΦ α hα_half hα_lt_one
      hN hNtr hSupport (htrace_all hN hNtr hSupport)

/-- Full-rank side-state handoff for the `1 / 2 ≤ α < 1` channel DPI route.

The input sandwiched inner operator is full-rank in the local `State + PosDef`
domain. Its explicit reverse-Holder optimizer is therefore also full-rank, so
the remaining channel-specific low-`α` task can be stated using only
normalized positive-definite side-states. This is the form needed before using
negative powers of the side-state in a source-faithful duality argument. -/
theorem sandwichedRenyi_dataProcessing_le_of_all_reverseHolder_fullRank_sideStates_trace_le_of_lt_one
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (htrace_all :
      ∀ {N : CMatrix a}, N.PosDef → N.trace.re = 1 →
          ((sandwichedRenyiInner ρ σ α *
              CFC.rpow N (1 - 1 / α)).trace).re ≤
            psdSchattenPNorm
              (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
              (sandwichedRenyiInner_posSemidef
                (Φ.applyState ρ) (Φ.applyState σ) α)
              ⟨α, by linarith⟩) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (by linarith) (ne_of_lt hα_lt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (by linarith) (ne_of_lt hα_lt_one) := by
  have hα_pos : 0 < α := by linarith
  let M : CMatrix a := sandwichedRenyiInner ρ σ α
  let hM : M.PosSemidef := by
    simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
  have hMdef : M.PosDef := by
    simpa [M] using sandwichedRenyiInner_posDef ρ σ hρ hσ α
  have hSpos : 0 < psdTracePower M hM α := by
    simpa [M, hM] using sandwichedRenyiInner_psdTracePower_pos ρ σ hρ hσ α
  have hNdef :
      (psdTraceReverseHolderOptimizer M hM α).PosDef :=
    _root_.QIT.psdTraceReverseHolderOptimizer_posDef_of_posDef hM hMdef hSpos
  rcases _root_.QIT.psdTraceReverseHolderOptimizer_props hM hα_pos hSpos with
    ⟨hN, hNtr, _hSupport, _hattain⟩
  exact
    sandwichedRenyi_dataProcessing_le_of_reverseHolder_trace_le_of_lt_one
      ρ σ Φ hρ hσ hρΦ hσΦ α hα_half hα_lt_one
      (by simpa [M, hM] using hN)
      (by simpa [M, hM] using hNtr)
      (by
        simpa [M, hM] using
          Matrix.Supports.of_right_posDef M
            (psdTraceReverseHolderOptimizer M hM α) hNdef)
      (by simpa [M, hM] using htrace_all hNdef hNtr)

/-- The reverse-Holder trace objective is strictly positive for full-rank
inputs and full-rank side-states.

This isolates the finite-dimensional positivity fact needed by the low-`α`
route before applying negative side-state powers or logarithmic conversions. -/
theorem sandwichedRenyi_reverseHolder_fullRank_sideState_trace_pos
    (ρ σ : State a) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α : ℝ) {N : CMatrix a} (hN : N.PosDef) :
    0 <
      ((sandwichedRenyiInner ρ σ α *
        CFC.rpow N (1 - 1 / α)).trace).re := by
  haveI : Nonempty a := ρ.nonempty
  exact _root_.QIT.trace_mul_posDef_re_pos
    (sandwichedRenyiInner_posDef ρ σ hρ hσ α)
    (_root_.QIT.cMatrix_rpow_posDef_of_posDef hN (1 - 1 / α))

/-- The explicit reverse-Holder optimizer has exactly the input PSD Schatten
value as its trace objective.

This is the concrete equality behind the low-`α` optimizer handoff: after this
point, the only missing channel-specific inequality is to compare this exact
input-side optimizer value with the output-side PSD Schatten expression. -/
theorem sandwichedRenyi_reverseHolder_optimizer_trace_eq_schatten
    (ρ σ : State a) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) :
    let M : CMatrix a := sandwichedRenyiInner ρ σ α
    let hM : M.PosSemidef := by
      simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
    ((M * CFC.rpow (psdTraceReverseHolderOptimizer M hM α)
        (1 - 1 / α)).trace).re =
      psdSchattenPNorm M hM ⟨α, hα_pos⟩ := by
  let M : CMatrix a := sandwichedRenyiInner ρ σ α
  let hM : M.PosSemidef := by
    simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
  have hSpos : 0 < psdTracePower M hM α := by
    simpa [M, hM] using sandwichedRenyiInner_psdTracePower_pos ρ σ hρ hσ α
  rcases _root_.QIT.psdTraceReverseHolderOptimizer_props hM hα_pos hSpos with
    ⟨_hN, _hNtr, _hSupport, hattain⟩
  simpa [M, hM] using hattain.symm

/-- Source-shaped form of the explicit low-`α` reverse-Holder optimizer for a
sandwiched Renyi inner operator: it is the normalized positive `α`-power of the
inner operator.

This is the concrete power-state form needed by the conditional-duality/minimax
route for the strict subunit interval. -/
theorem sandwichedRenyi_reverseHolder_optimizer_eq_normalized_inner_power
    (ρ σ : State a) (α : ℝ) :
    let M : CMatrix a := sandwichedRenyiInner ρ σ α
    let hM : M.PosSemidef := by
      simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
    psdTraceReverseHolderOptimizer M hM α =
      (((psdTracePower M hM α)⁻¹ : ℝ) : ℂ) • CFC.rpow M α := by
  let M : CMatrix a := sandwichedRenyiInner ρ σ α
  let hM : M.PosSemidef := by
    simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
  simpa [M, hM] using
    (_root_.QIT.psdTraceReverseHolderOptimizer_eq_inv_tracePower_smul_rpow
      (M := M) hM (p := α))

/-- The low-`α` reverse-Holder optimizer trace bound is fully proved for the
reference spectral pinching channel.

This is the first nontrivial closed instance of the strict-subunit optimizer
obligation: it combines the already-proved pinching trace-power expansion with
the explicit reverse-Holder optimizer equality. The general-channel case still
requires the conditional-duality/minimax route. -/
theorem sandwichedRenyi_referenceSpectralPinching_reverseHolder_optimizer_trace_le_of_lt_one
    (ρ σ : State a) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1) :
    let P : ProjectiveMeasurement a a :=
      ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
    let M : CMatrix a := sandwichedRenyiInner ρ σ α
    let hM : M.PosSemidef := by
      simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
    ((M * CFC.rpow (psdTraceReverseHolderOptimizer M hM α)
        (1 - 1 / α)).trace).re ≤
      psdSchattenPNorm
        (sandwichedRenyiInner (P.pinchingChannel.applyState ρ)
          (P.pinchingChannel.applyState σ) α)
        (sandwichedRenyiInner_posSemidef
          (P.pinchingChannel.applyState ρ) (P.pinchingChannel.applyState σ) α)
        ⟨α, by linarith⟩ := by
  classical
  let P : ProjectiveMeasurement a a :=
    ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
  let M : CMatrix a := sandwichedRenyiInner ρ σ α
  let hM : M.PosSemidef := by
    simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
  have hα_pos : 0 < α := by linarith
  have hσP_eq : P.pinchingChannel.applyState σ = σ := by
    simpa [P] using
      ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_self σ
  have htrace_eq :
      ((M * CFC.rpow (psdTraceReverseHolderOptimizer M hM α)
          (1 - 1 / α)).trace).re =
        psdSchattenPNorm M hM ⟨α, hα_pos⟩ := by
    simpa [M, hM] using
      sandwichedRenyi_reverseHolder_optimizer_trace_eq_schatten
        ρ σ hρ hσ α hα_pos
  have hpower :
      psdTracePower M hM α ≤
        psdTracePower
          (sandwichedRenyiInner (P.pinchingChannel.applyState ρ) σ α)
          (sandwichedRenyiInner_posSemidef
            (P.pinchingChannel.applyState ρ) σ α)
          α := by
    simpa [M, hM, P] using
      sandwichedRenyiInner_referenceSpectralPinching_tracePower_ge_of_le_one
        ρ σ α (by linarith) (le_of_lt hα_lt_one)
  have hnorm :
      psdSchattenPNorm M hM ⟨α, hα_pos⟩ ≤
        psdSchattenPNorm
          (sandwichedRenyiInner (P.pinchingChannel.applyState ρ) σ α)
          (sandwichedRenyiInner_posSemidef
            (P.pinchingChannel.applyState ρ) σ α)
          ⟨α, hα_pos⟩ :=
    _root_.QIT.psdSchattenPNorm_le_of_psdTracePower_le
      hM
      (sandwichedRenyiInner_posSemidef
        (P.pinchingChannel.applyState ρ) σ α)
      hα_pos hpower
  calc
    ((M * CFC.rpow (psdTraceReverseHolderOptimizer M hM α)
        (1 - 1 / α)).trace).re =
        psdSchattenPNorm M hM ⟨α, hα_pos⟩ := htrace_eq
    _ ≤ psdSchattenPNorm
          (sandwichedRenyiInner (P.pinchingChannel.applyState ρ) σ α)
          (sandwichedRenyiInner_posSemidef
            (P.pinchingChannel.applyState ρ) σ α)
          ⟨α, hα_pos⟩ := hnorm
    _ = psdSchattenPNorm
          (sandwichedRenyiInner (P.pinchingChannel.applyState ρ)
            (P.pinchingChannel.applyState σ) α)
          (sandwichedRenyiInner_posSemidef
            (P.pinchingChannel.applyState ρ) (P.pinchingChannel.applyState σ) α)
          ⟨α, hα_pos⟩ := by
          rw [hσP_eq]

/-- Single-obligation optimizer handoff for the `1 / 2 ≤ α < 1` channel DPI
route.

The previous all-side-state form is equivalent to a source-shaped variational
argument, but the actual remaining proof obligation can be concentrated on the
explicit full-rank reverse-Holder optimizer for the input sandwiched inner
operator. Proving the displayed trace bound for that optimizer is now enough
to obtain the full-rank logarithmic DPI inequality in the subunit range. -/
theorem sandwichedRenyi_dataProcessing_le_of_reverseHolder_optimizer_trace_le_of_lt_one
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (htrace_le :
      let M : CMatrix a := sandwichedRenyiInner ρ σ α
      let hM : M.PosSemidef := by
        simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
      ((M * CFC.rpow (psdTraceReverseHolderOptimizer M hM α)
          (1 - 1 / α)).trace).re ≤
        psdSchattenPNorm
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef
            (Φ.applyState ρ) (Φ.applyState σ) α)
          ⟨α, by linarith⟩) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (by linarith) (ne_of_lt hα_lt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (by linarith) (ne_of_lt hα_lt_one) := by
  have hα_pos : 0 < α := by linarith
  let M : CMatrix a := sandwichedRenyiInner ρ σ α
  let hM : M.PosSemidef := by
    simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
  have hSpos : 0 < psdTracePower M hM α := by
    simpa [M, hM] using sandwichedRenyiInner_psdTracePower_pos ρ σ hρ hσ α
  rcases _root_.QIT.psdTraceReverseHolderOptimizer_props hM hα_pos hSpos with
    ⟨hN, hNtr, hSupport, _hattain⟩
  exact
    sandwichedRenyi_dataProcessing_le_of_reverseHolder_trace_le_of_lt_one
      ρ σ Φ hρ hσ hρΦ hσΦ α hα_half hα_lt_one
      (by simpa [M, hM] using hN)
      (by simpa [M, hM] using hNtr)
      (by simpa [M, hM] using hSupport)
      (by simpa [M, hM] using htrace_le)

/-- Statement-form strict-subunit handoff for the remaining low-`α` proof
obligation.

This theorem does not prove the missing reverse-Holder optimizer inequality.
It records the exact final shape needed to turn that future inequality into the
general-channel full-rank DPI statement for `1 / 2 ≤ α < 1`. -/
theorem sandwichedRenyi_dataProcessing_channel_statement_of_reverseHolder_optimizer_trace_le_of_lt_one
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (htrace_le :
      let M : CMatrix a := sandwichedRenyiInner ρ σ α
      let hM : M.PosSemidef := by
        simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
      ((M * CFC.rpow (psdTraceReverseHolderOptimizer M hM α)
          (1 - 1 / α)).trace).re ≤
        psdSchattenPNorm
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef
            (Φ.applyState ρ) (Φ.applyState σ) α)
          ⟨α, by linarith⟩) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ hρ hσ hρΦ hσΦ
      α hα_half (ne_of_lt hα_lt_one) := by
  unfold sandwichedRenyi_dataProcessing_channel_statement
  exact
    sandwichedRenyi_dataProcessing_le_of_reverseHolder_optimizer_trace_le_of_lt_one
      ρ σ Φ hρ hσ hρΦ hσΦ α hα_half hα_lt_one htrace_le

/-- The reference-spectral pinching channel satisfies the strict-subunit
full-rank DPI through the reverse-Holder optimizer route.

This is a proof-route check rather than a new public endpoint: it shows that
the optimizer trace bound above is strong enough to feed the general
`reverseHolder_optimizer_trace_le` handoff. -/
theorem sandwichedRenyi_dataProcessing_referenceSpectralPinching_channel_statement_lt_one_via_optimizer
    (ρ σ : State a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρP :
      (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
        ).pinchingChannel).applyState ρ).matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ
      ((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
        ).pinchingChannel)
      hρ hσ hρP
      (by
        rw [ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_self]
        exact hσ)
      α hα_half (ne_of_lt hα_lt_one) := by
  classical
  let P : ProjectiveMeasurement a a :=
    ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
  have hσP_eq : P.pinchingChannel.applyState σ = σ := by
    simpa [P] using
      ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_self σ
  have hσP : (P.pinchingChannel.applyState σ).matrix.PosDef := by
    rw [hσP_eq]
    exact hσ
  have htrace_le :
      let M : CMatrix a := sandwichedRenyiInner ρ σ α
      let hM : M.PosSemidef := by
        simpa [M] using sandwichedRenyiInner_posSemidef ρ σ α
      ((M * CFC.rpow (psdTraceReverseHolderOptimizer M hM α)
          (1 - 1 / α)).trace).re ≤
        psdSchattenPNorm
          (sandwichedRenyiInner (P.pinchingChannel.applyState ρ)
            (P.pinchingChannel.applyState σ) α)
          (sandwichedRenyiInner_posSemidef
            (P.pinchingChannel.applyState ρ) (P.pinchingChannel.applyState σ) α)
          ⟨α, by linarith⟩ := by
    simpa [P] using
      sandwichedRenyi_referenceSpectralPinching_reverseHolder_optimizer_trace_le_of_lt_one
        ρ σ hρ hσ α hα_half hα_lt_one
  have hDPI :=
    sandwichedRenyi_dataProcessing_channel_statement_of_reverseHolder_optimizer_trace_le_of_lt_one
      ρ σ P.pinchingChannel hρ hσ hρP hσP α hα_half hα_lt_one htrace_le
  simpa [sandwichedRenyi_dataProcessing_channel_statement, P, hσP_eq] using hDPI

/-- Applying the identity channel does not change the sandwiched Renyi
divergence. This small API lemma keeps later DPI sanity checks independent from
the concrete Kraus implementation of `Channel.idChannel`. -/
@[simp]
theorem sandwichedRenyi_idChannel_applyState
    (ρ σ : State a) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρid : ((Channel.idChannel a).applyState ρ).matrix.PosDef)
    (hσid : ((Channel.idChannel a).applyState σ).matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyi ((Channel.idChannel a).applyState ρ)
        ((Channel.idChannel a).applyState σ) hρid hσid α hα_pos hα_ne_one =
      sandwichedRenyi ρ σ hρ hσ α hα_pos hα_ne_one := by
  unfold sandwichedRenyi
  simp [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus]

/-- Identity-channel sanity check for the generalized statement surface.

This is a genuine proved specialization and an API check for the `Channel a b`
statement shape; it is not the sandwiched Renyi DPI proof required to close
`sandwiched-renyi-dpi`. -/
theorem sandwichedRenyi_dataProcessing_channel_statement_idChannel
    (ρ σ : State a) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ (Channel.idChannel a) hρ hσ
      (by simpa [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus] using hρ)
      (by simpa [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus] using hσ)
      α hα hα_ne_one := by
  unfold sandwichedRenyi_dataProcessing_channel_statement
  exact le_of_eq (sandwichedRenyi_idChannel_applyState ρ σ hρ hσ _ _ α (by linarith) hα_ne_one)

/-- A proved state-level DPI instance remains true after tensoring both inputs
with the same untouched full-rank side-information pair.

This is a reusable lifting step for later tensor-power/asymptotic DPI work: it
uses the already-proved product additivity of `sandwichedRenyi`, not the deep DPI
theorem itself. -/
theorem sandwichedRenyi_dataProcessing_channel_statement_prod_idChannel
    (ρ₁ σ₁ : State a) (ρ₂ σ₂ : State c) (Φ : Channel a b)
    (hρ₁ : ρ₁.matrix.PosDef) (hσ₁ : σ₁.matrix.PosDef)
    (hρ₂ : ρ₂.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ₁).matrix.PosDef) (hσΦ : (Φ.applyState σ₁).matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1)
    (hΦ : sandwichedRenyi_dataProcessing_channel_statement ρ₁ σ₁ Φ
      hρ₁ hσ₁ hρΦ hσΦ α hα hα_ne_one) :
    sandwichedRenyi_dataProcessing_channel_statement (ρ₁.prod ρ₂) (σ₁.prod σ₂)
      (Φ.prod (Channel.idChannel c))
      (State.prod_posDef hρ₁ hρ₂) (State.prod_posDef hσ₁ hσ₂)
      (by
        rw [Channel.applyState_prod]
        exact State.prod_posDef hρΦ
          (by simpa [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus] using hρ₂))
      (by
        rw [Channel.applyState_prod]
        exact State.prod_posDef hσΦ
          (by simpa [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus] using hσ₂))
      α hα hα_ne_one := by
  have hα_pos : 0 < α := by linarith
  unfold sandwichedRenyi_dataProcessing_channel_statement at hΦ ⊢
  calc
    sandwichedRenyi ((Φ.prod (Channel.idChannel c)).applyState (ρ₁.prod ρ₂))
        ((Φ.prod (Channel.idChannel c)).applyState (σ₁.prod σ₂)) _ _
        α _ hα_ne_one =
      sandwichedRenyi ((Φ.applyState ρ₁).prod ((Channel.idChannel c).applyState ρ₂))
        ((Φ.applyState σ₁).prod ((Channel.idChannel c).applyState σ₂)) _ _
        α hα_pos hα_ne_one := by
          unfold sandwichedRenyi
          simp [Channel.applyState_prod]
    _ =
      sandwichedRenyi (Φ.applyState ρ₁) (Φ.applyState σ₁) hρΦ hσΦ
          α hα_pos hα_ne_one +
        sandwichedRenyi ((Channel.idChannel c).applyState ρ₂)
          ((Channel.idChannel c).applyState σ₂)
          (by simpa [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus] using hρ₂)
          (by simpa [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus] using hσ₂)
          α hα_pos hα_ne_one := by
          rw [State.sandwichedRenyi_prod (Φ.applyState ρ₁) (Φ.applyState σ₁)
            ((Channel.idChannel c).applyState ρ₂) ((Channel.idChannel c).applyState σ₂)
            hρΦ hσΦ
            (by simpa [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus] using hρ₂)
            (by simpa [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus] using hσ₂)
            α hα_pos hα_ne_one]
    _ =
      sandwichedRenyi (Φ.applyState ρ₁) (Φ.applyState σ₁) hρΦ hσΦ
          α hα_pos hα_ne_one +
        sandwichedRenyi ρ₂ σ₂ hρ₂ hσ₂ α hα_pos hα_ne_one := by
          rw [sandwichedRenyi_idChannel_applyState ρ₂ σ₂ hρ₂ hσ₂ _ _
            α hα_pos hα_ne_one]
    _ ≤ sandwichedRenyi ρ₁ σ₁ hρ₁ hσ₁ α hα_pos hα_ne_one +
        sandwichedRenyi ρ₂ σ₂ hρ₂ hσ₂ α hα_pos hα_ne_one := by
          exact add_le_add hΦ (le_refl _)
    _ = sandwichedRenyi (ρ₁.prod ρ₂) (σ₁.prod σ₂)
        (State.prod_posDef hρ₁ hρ₂) (State.prod_posDef hσ₁ hσ₂)
        α hα_pos hα_ne_one := by
          rw [State.sandwichedRenyi_prod ρ₁ σ₁ ρ₂ σ₂
            hρ₁ hσ₁ hρ₂ hσ₂ α hα_pos hα_ne_one]

/-- The class of channels satisfying the local full-rank sandwiched Renyi DPI
statement is closed under channel composition.

This does not prove DPI for every channel by itself. It is the composition step
needed by reduction routes that prove DPI for primitive maps and then assemble
larger channels from them. -/
theorem sandwichedRenyi_dataProcessing_channel_statement_comp
    (ρ σ : State a) (Φ : Channel a b) (Ψ : Channel b c)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (hρΨΦ : (Ψ.applyState (Φ.applyState ρ)).matrix.PosDef)
    (hσΨΦ : (Ψ.applyState (Φ.applyState σ)).matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1)
    (hΦ : sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ
      hρ hσ hρΦ hσΦ α hα hα_ne_one)
    (hΨ : sandwichedRenyi_dataProcessing_channel_statement (Φ.applyState ρ)
      (Φ.applyState σ) Ψ hρΦ hσΦ hρΨΦ hσΨΦ α hα hα_ne_one) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ (Ψ.comp Φ) hρ hσ
      (by rw [Channel.applyState_comp]; exact hρΨΦ)
      (by rw [Channel.applyState_comp]; exact hσΨΦ)
      α hα hα_ne_one := by
  have hα_pos : 0 < α := by linarith
  unfold sandwichedRenyi_dataProcessing_channel_statement at hΦ hΨ ⊢
  calc
    sandwichedRenyi ((Ψ.comp Φ).applyState ρ) ((Ψ.comp Φ).applyState σ) _ _
        α _ hα_ne_one =
      sandwichedRenyi (Ψ.applyState (Φ.applyState ρ))
        (Ψ.applyState (Φ.applyState σ)) hρΨΦ hσΨΦ α hα_pos hα_ne_one := by
          unfold sandwichedRenyi
          simp [Channel.applyState_comp]
    _ ≤ sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ)
        hρΦ hσΦ α hα_pos hα_ne_one := hΨ
    _ ≤ sandwichedRenyi ρ σ hρ hσ α hα_pos hα_ne_one := hΦ

/-- Reference-spectral pinching reduces the sandwiched Renyi expression to a
finite classical power sum in the reference eigenbasis.

This is a non-circular endpoint for the Tomamichel pinching route: once the
pinched state is known to be full-rank in the reference eigenbasis, its
sandwiched Renyi divergence against the reference state is exactly the
classical Renyi power-sum expression for the two eigenbasis distributions. -/
theorem sandwichedRenyi_referenceSpectralPinching_eq_classicalPowerSum
    (ρ σ : State a)
    (hρP :
      (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
        ).applyState ρ).matrix.PosDef)
    (hσ : σ.matrix.PosDef)
    (hp_pos : ∀ i, 0 < (ProjectiveMeasurement.eigenbasisDiagonalProb ρ σ i : ℝ))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyi
        (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
          ).applyState ρ)
        σ hρP hσ α hα_pos hα_ne_one =
      (1 / (α - 1)) *
        log2
          (∑ i,
            ((ProjectiveMeasurement.eigenbasisDiagonalProb ρ σ i : ℝ) ^ α) *
              ((ProjectiveMeasurement.stateEigenvalueProb σ i : ℝ) ^ (1 - α))) := by
  let U : Matrix.unitaryGroup a ℂ := σ.pos.isHermitian.eigenvectorUnitary
  let Pρ : State a :=
    ((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
      ).applyState ρ
  let p : a → ℝ≥0 := ProjectiveMeasurement.eigenbasisDiagonalProb ρ σ
  let q : a → ℝ≥0 := ProjectiveMeasurement.stateEigenvalueProb σ
  let hp_sum : ∑ i, p i = 1 := ProjectiveMeasurement.eigenbasisDiagonalProb_sum ρ σ
  let hq_sum : ∑ i, q i = 1 := ProjectiveMeasurement.stateEigenvalueProb_sum σ
  let ρdiag : State a := Classical.diagonalState p hp_sum
  let σdiag : State a := Classical.diagonalState q hq_sum
  have hρdiag_pos : ρdiag.matrix.PosDef :=
    Classical.diagonalState_posDef p hp_sum hp_pos
  have hσdiag_pos : σdiag.matrix.PosDef :=
    Classical.diagonalState_posDef q hq_sum
      (ProjectiveMeasurement.stateEigenvalueProb_pos_of_posDef σ hσ)
  have hPρ_eq : Pρ = ρdiag.unitaryConj U := by
    apply State.ext
    calc
      Pρ.matrix =
          (U : CMatrix a) *
            Matrix.diagonal (fun i => ((p i : ℝ≥0) : ℂ)) *
            star (U : CMatrix a) := by
            simpa [Pρ, p, U] using
              ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_matrix_eq_unitary_diagonalProb
                ρ σ
      _ = (ρdiag.unitaryConj U).matrix := by
            simp [ρdiag, State.unitaryConj, Classical.diagonalState_matrix]
  have hσ_eq : σ = σdiag.unitaryConj U := by
    apply State.ext
    calc
      σ.matrix =
          (U : CMatrix a) *
            Matrix.diagonal (fun i => ((q i : ℝ≥0) : ℂ)) *
            star (U : CMatrix a) := by
            simpa [q, U] using
              ProjectiveMeasurement.state_matrix_eq_unitary_diagonalEigenvalueProb σ
      _ = (σdiag.unitaryConj U).matrix := by
            simp [σdiag, State.unitaryConj, Classical.diagonalState_matrix]
  calc
    sandwichedRenyi Pρ σ hρP hσ α hα_pos hα_ne_one =
        sandwichedRenyi (ρdiag.unitaryConj U) (σdiag.unitaryConj U)
          (ρdiag.unitaryConj_posDef U hρdiag_pos)
          (σdiag.unitaryConj_posDef U hσdiag_pos)
          α hα_pos hα_ne_one := by
          unfold sandwichedRenyi
          simp [hPρ_eq, hσ_eq]
    _ = sandwichedRenyi ρdiag σdiag hρdiag_pos hσdiag_pos α hα_pos hα_ne_one := by
          exact sandwichedRenyi_unitaryConj ρdiag σdiag U hρdiag_pos hσdiag_pos
            α hα_pos hα_ne_one
    _ = (1 / (α - 1)) *
        log2
          (∑ i,
            ((ProjectiveMeasurement.eigenbasisDiagonalProb ρ σ i : ℝ) ^ α) *
              ((ProjectiveMeasurement.stateEigenvalueProb σ i : ℝ) ^ (1 - α))) := by
          simpa [ρdiag, σdiag, p, q, hp_sum, hq_sum] using
            sandwichedRenyi_diagonalState_eq_classicalPowerSum p q hp_sum hq_sum
              hp_pos (ProjectiveMeasurement.stateEigenvalueProb_pos_of_posDef σ hσ)
              α hα_pos hα_ne_one

/-- Reference-spectral pinching reduces the Petz Renyi expression to the same
finite classical power sum in the reference eigenbasis. -/
theorem petzRenyi_referenceSpectralPinching_eq_classicalPowerSum
    (ρ σ : State a)
    (hρP :
      (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
        ).applyState ρ).matrix.PosDef)
    (hσ : σ.matrix.PosDef)
    (hp_pos : ∀ i, 0 < (ProjectiveMeasurement.eigenbasisDiagonalProb ρ σ i : ℝ))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    petzRenyi
        (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
          ).applyState ρ)
        σ hρP hσ α hα_pos hα_ne_one =
      (1 / (α - 1)) *
        log2
          (∑ i,
            ((ProjectiveMeasurement.eigenbasisDiagonalProb ρ σ i : ℝ) ^ α) *
              ((ProjectiveMeasurement.stateEigenvalueProb σ i : ℝ) ^ (1 - α))) := by
  let U : Matrix.unitaryGroup a ℂ := σ.pos.isHermitian.eigenvectorUnitary
  let Pρ : State a :=
    ((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
      ).applyState ρ
  let p : a → ℝ≥0 := ProjectiveMeasurement.eigenbasisDiagonalProb ρ σ
  let q : a → ℝ≥0 := ProjectiveMeasurement.stateEigenvalueProb σ
  let hp_sum : ∑ i, p i = 1 := ProjectiveMeasurement.eigenbasisDiagonalProb_sum ρ σ
  let hq_sum : ∑ i, q i = 1 := ProjectiveMeasurement.stateEigenvalueProb_sum σ
  let ρdiag : State a := Classical.diagonalState p hp_sum
  let σdiag : State a := Classical.diagonalState q hq_sum
  have hρdiag_pos : ρdiag.matrix.PosDef :=
    Classical.diagonalState_posDef p hp_sum hp_pos
  have hσdiag_pos : σdiag.matrix.PosDef :=
    Classical.diagonalState_posDef q hq_sum
      (ProjectiveMeasurement.stateEigenvalueProb_pos_of_posDef σ hσ)
  have hPρ_eq : Pρ = ρdiag.unitaryConj U := by
    apply State.ext
    calc
      Pρ.matrix =
          (U : CMatrix a) *
            Matrix.diagonal (fun i => ((p i : ℝ≥0) : ℂ)) *
            star (U : CMatrix a) := by
            simpa [Pρ, p, U] using
              ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_matrix_eq_unitary_diagonalProb
                ρ σ
      _ = (ρdiag.unitaryConj U).matrix := by
            simp [ρdiag, State.unitaryConj, Classical.diagonalState_matrix]
  have hσ_eq : σ = σdiag.unitaryConj U := by
    apply State.ext
    calc
      σ.matrix =
          (U : CMatrix a) *
            Matrix.diagonal (fun i => ((q i : ℝ≥0) : ℂ)) *
            star (U : CMatrix a) := by
            simpa [q, U] using
              ProjectiveMeasurement.state_matrix_eq_unitary_diagonalEigenvalueProb σ
      _ = (σdiag.unitaryConj U).matrix := by
            simp [σdiag, State.unitaryConj, Classical.diagonalState_matrix]
  calc
    petzRenyi Pρ σ hρP hσ α hα_pos hα_ne_one =
        petzRenyi (ρdiag.unitaryConj U) (σdiag.unitaryConj U)
          (ρdiag.unitaryConj_posDef U hρdiag_pos)
          (σdiag.unitaryConj_posDef U hσdiag_pos)
          α hα_pos hα_ne_one := by
          unfold petzRenyi
          simp [hPρ_eq, hσ_eq]
    _ = petzRenyi ρdiag σdiag hρdiag_pos hσdiag_pos α hα_pos hα_ne_one := by
          exact petzRenyi_unitaryConj ρdiag σdiag U hρdiag_pos hσdiag_pos
            α hα_pos hα_ne_one
    _ = (1 / (α - 1)) *
        log2
          (∑ i,
            ((ProjectiveMeasurement.eigenbasisDiagonalProb ρ σ i : ℝ) ^ α) *
              ((ProjectiveMeasurement.stateEigenvalueProb σ i : ℝ) ^ (1 - α))) := by
          simpa [ρdiag, σdiag, p, q, hp_sum, hq_sum] using
            petzRenyi_diagonalState_eq_classicalPowerSum p q hp_sum hq_sum
              hp_pos (ProjectiveMeasurement.stateEigenvalueProb_pos_of_posDef σ hσ)
              α hα_pos hα_ne_one

/-- After pinching the first argument in the spectral basis of the full-rank
reference state, sandwiched Renyi and Petz Renyi coincide. This is the
commuting-state bridge used by the pinching proof route. -/
theorem sandwichedRenyi_referenceSpectralPinching_eq_petzRenyi
    (ρ σ : State a)
    (hρP :
      (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
        ).applyState ρ).matrix.PosDef)
    (hσ : σ.matrix.PosDef)
    (hp_pos : ∀ i, 0 < (ProjectiveMeasurement.eigenbasisDiagonalProb ρ σ i : ℝ))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyi
        (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
          ).applyState ρ)
        σ hρP hσ α hα_pos hα_ne_one =
      petzRenyi
        (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
          ).applyState ρ)
        σ hρP hσ α hα_pos hα_ne_one := by
  rw [sandwichedRenyi_referenceSpectralPinching_eq_classicalPowerSum ρ σ hρP hσ
      hp_pos α hα_pos hα_ne_one,
    petzRenyi_referenceSpectralPinching_eq_classicalPowerSum ρ σ hρP hσ
      hp_pos α hα_pos hα_ne_one]

/-- A product measurement-channel DPI instance yields the corresponding
measured-subsystem sandwiched Renyi inequality.

This bridges the source route's measurement-map language with the local channel
statement surface: proving DPI for `Channel.measure M ⊗ id` is enough to obtain
the inequality phrased using `measureSubsystemState`. -/
theorem sandwichedRenyi_measureSubsystem_le_of_dataProcessing_channel_statement
    (ρ σ : State (Prod a b)) (M : POVM c a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (hσM : (measureSubsystemState M σ).matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1)
    (hDPI : sandwichedRenyi_dataProcessing_channel_statement ρ σ
      ((Channel.measure M).prod (Channel.idChannel b)) hρ hσ
      (by simpa [measureSubsystemState] using hρM)
      (by simpa [measureSubsystemState] using hσM)
      α hα hα_ne_one) :
    sandwichedRenyi (measureSubsystemState M ρ) (measureSubsystemState M σ)
        hρM hσM α (by linarith) hα_ne_one ≤
      sandwichedRenyi ρ σ hρ hσ α (by linarith) hα_ne_one := by
  simpa [sandwichedRenyi_dataProcessing_channel_statement, measureSubsystemState] using hDPI

end State

end

end QIT
