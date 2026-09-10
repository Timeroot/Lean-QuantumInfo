/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

module

public import QuantumLib.QIT.Information.Entropy.Entropy
public import QuantumInfo.Entropy.VonNeumann

/-!
# Lean-QIT entropies and physlib entropies

Lean-QIT measures entropy in bits and physlib in nats, so the two von Neumann entropies differ by
the factor `Real.log 2`; apart from that they are the same quantity, both being the sum of
`x ↦ -x log x` over the eigenvalues of the density matrix. That identification is
`MState.vonNeumann_eq_Sᵥₙ_div_log_two`, proved where `MState.vonNeumann` is defined because
the entropy bounds there are transferred across it. The conditional entropy and the mutual
information inherit the same relation, and that is what this file records.

## Main statements

* `MState.conditionalEntropy_eq_qConditionalEnt_div_log_two` and
  `QIT.mutualInformation_eq_qMutualInfo_div_log_two` — the change of log base for the derived
  quantities.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem _root_.MState.conditionalEntropy_eq_qConditionalEnt_div_log_two (rho : MState (a × b)) :
    rho.conditionalEntropy = qConditionalEnt rho / Real.log 2 := by
  rw [MState.conditionalEntropy_eq, MState.vonNeumann_eq_Sᵥₙ_div_log_two,
    MState.vonNeumann_eq_Sᵥₙ_div_log_two, qConditionalEnt]
  ring

theorem mutualInformation_eq_qMutualInfo_div_log_two (rho : MState (a × b)) :
    mutualInformation rho = qMutualInfo rho / Real.log 2 := by
  rw [mutualInformation, MState.vonNeumann_eq_Sᵥₙ_div_log_two,
    MState.vonNeumann_eq_Sᵥₙ_div_log_two, MState.vonNeumann_eq_Sᵥₙ_div_log_two, qMutualInfo]
  ring

end QIT

end
