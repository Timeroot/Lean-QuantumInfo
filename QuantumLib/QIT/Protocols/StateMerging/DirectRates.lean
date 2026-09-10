/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Protocols.FQSW.IIDTypical

/-!
# Direct state-merging rate helpers

Source-level entropy and finite-register rate identities used by the ADHW
FQSW-plus-teleportation route to state merging.
-/

@[expose] public section

namespace QIT

universe u v w

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

end QIT

namespace Ket

open QIT
universe u v w
variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

/-- The net quantum communication rate of FQSW followed by teleportation is
the source conditional entropy, as in ADHW `fqsw.tex:402-420`. -/
theorem fqswCommunicationRate_sub_ebitYieldRate_eq_conditionalEntropy
    (psi : Ket ((a × b) × r)) :
    psi.fqswCommunicationRate - psi.fqswEbitYieldRate =
      psi.state.traceRight.conditionalEntropy := by
  unfold fqswCommunicationRate fqswEbitYieldRate
  rw [adhwFQSWMutualInformationAR_eq_entropyA_add_entropyR_sub_entropyB,
    adhwFQSWMutualInformationAB_eq_entropyA_add_entropyB_sub_entropyR]
  rw [MState.conditionalEntropy_eq,
    adhwFQSWSourceAB_vonNeumann_eq_entropyR]
  unfold adhwFQSWEntropyB adhwFQSWSystemBState
  ring

/-- The FQSW ebit-yield exponent is nonnegative. -/
theorem fqswEbitYieldRate_nonneg
    (psi : Ket ((a × b) × r)) :
    0 ≤ psi.fqswEbitYieldRate := by
  unfold fqswEbitYieldRate
  exact mul_nonneg (by norm_num)
    (MState.mutualInformation_nonneg psi.state.traceRight)

end Ket

namespace QIT

universe u v w
variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

/-- A finite nonempty register bounded by a base-two exponential has the
corresponding base-two logarithmic size bound. The `Nonempty` assumption is
essential: it supplies positivity of the cardinality before taking logs. -/
theorem log2_card_le_exponent_mul_of_card_le_two_rpow
    (e : Type u) [Fintype e] [Nonempty e]
    (n : ℕ) (exponent : ℝ)
    (hcard : (Fintype.card e : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) * exponent)) :
    log2 (Fintype.card e : ℝ) ≤ exponent * (n : ℝ) := by
  have hcard_pos : 0 < (Fintype.card e : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hlog := Real.log_le_log hcard_pos hcard
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
  unfold log2
  have hlog_two_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [div_le_iff₀ hlog_two_pos]
  calc
    Real.log (Fintype.card e : ℝ) ≤
        ((n : ℝ) * exponent) * Real.log 2 := hlog
    _ = (exponent * (n : ℝ)) * Real.log 2 := by ring

end QIT
