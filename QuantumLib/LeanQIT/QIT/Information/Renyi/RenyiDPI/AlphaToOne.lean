/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.RenyiDPI.TraceLogBridge

/-!
# Sandwiched Renyi alpha-to-one data-processing bridge

Source-limit data processing obtained by taking the right-limit of the
PSD-reference sandwiched Renyi data-processing theorem.
-/

@[expose] public section

open Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator UniformConvergence

namespace QIT

universe u v

noncomputable section

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Data processing for the source-limit PSD-reference relative entropy bridge.

This is obtained by taking `limsup` along `alpha -> 1+` in the proved
PSD-reference sandwiched Renyi data-processing theorem. -/
theorem relativeEntropyPSDReferenceE_dataProcessing_channel_ge
    {b : Type v} [Fintype b] [DecidableEq b]
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (Phi : Channel a b) :
    relativeEntropyPSDReferenceE rho sigma hSigma >=
      relativeEntropyPSDReferenceE
        (Phi.applyState rho) (Phi.map sigma) (Phi.mapsPositive sigma hSigma) := by
  classical
  by_cases hSupport : Matrix.Supports rho.matrix sigma
  · have hOutSupport :
        Matrix.Supports (Phi.applyState rho).matrix (Phi.map sigma) :=
      channel_applyState_supports_of_supports rho hSigma Phi hSupport
    rw [relativeEntropyPSDReferenceE_eq_limsup_of_supports rho hSigma hSupport,
      relativeEntropyPSDReferenceE_eq_limsup_of_supports
        (Phi.applyState rho) (Phi.mapsPositive sigma hSigma) hOutSupport]
    exact
      Filter.limsup_le_limsup
        (Filter.Eventually.of_forall fun alpha =>
          sandwichedRenyiPSDReferenceE_dataProcessing_channel_of_half_le_lt_one_or_one_lt
            rho hSigma Phi alpha.1 (Or.inr alpha.2))
        (β := EReal)
  · rw [relativeEntropyPSDReferenceE_eq_top_of_not_supports rho hSigma hSupport]
    exact le_top

end State

end

end QIT
