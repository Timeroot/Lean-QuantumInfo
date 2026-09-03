/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QIT.Information.Entropy.Entropy
import QuantumLib.QIT.Bridge.State
import QuantumInfo.Entropy.VonNeumann

/-!
# Lean-QIT entropies and physlib entropies

Lean-QIT measures entropy in bits and physlib in nats, so the two von Neumann entropies differ by
the factor `Real.log 2`; apart from that they are the same quantity, both being the sum of
`x ↦ -x log x` over the eigenvalues of the density matrix. The conditional entropy and the mutual
information inherit the same relation.

## Main statements

* `QIT.State.vonNeumann_eq_Sᵥₙ_div_log_two` — the two von Neumann entropies agree up to log base.
* `QIT.State.conditionalEntropy_eq_qConditionalEnt_div_log_two` and
  `QIT.mutualInformation_eq_qMutualInfo_div_log_two` — the same for the derived quantities.
-/

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

omit [Fintype a] [DecidableEq a] in
/-- Lean-QIT's `xlog2` is physlib's `Real.negMulLog`, negated and rescaled to base two. -/
theorem neg_xlog2_eq_negMulLog_div (t : ℝ) : -xlog2 t = Real.negMulLog t / Real.log 2 := by
  rw [xlog2]
  by_cases ht : t = 0
  · simp [ht]
  · rw [if_neg ht, log2, Real.negMulLog]
    ring

namespace State

private theorem eigenvalues_congr {M N : CMatrix a} (hM : M.IsHermitian) (hN : N.IsHermitian)
    (h : M = N) : hM.eigenvalues = hN.eigenvalues := by
  subst h
  rfl

/-- The two libraries take the eigenvalues of the same matrix. -/
theorem eigenvalues_toMState (rho : State a) :
    rho.toMState.M.H.eigenvalues = rho.pos.isHermitian.eigenvalues :=
  eigenvalues_congr _ _ ((DensityOp.mat_M _).trans (m_toMState rho))

@[simp]
theorem coe_spectrum_toMState (rho : State a) (i : a) :
    (rho.toMState.spectrum i : ℝ) = rho.pos.isHermitian.eigenvalues i :=
  congrFun (eigenvalues_toMState rho) i

/-- physlib's von Neumann entropy, as the eigenvalue sum that Lean-QIT starts from. -/
theorem Sᵥₙ_toMState (rho : State a) :
    Sᵥₙ rho.toMState = ∑ i, Real.negMulLog (rho.pos.isHermitian.eigenvalues i) := by
  rw [Sᵥₙ_eq_Hₛ_spectrum, Hₛ]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg Real.negMulLog (coe_spectrum_toMState rho i)

/-- Lean-QIT's von Neumann entropy is measured in bits and physlib's in nats. -/
theorem vonNeumann_eq_Sᵥₙ_div_log_two (rho : State a) :
    rho.vonNeumann = Sᵥₙ rho.toMState / Real.log 2 := by
  rw [vonNeumann, Sᵥₙ_toMState, Finset.sum_div, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => neg_xlog2_eq_negMulLog_div _

theorem conditionalEntropy_eq_qConditionalEnt_div_log_two (rho : State (a × b)) :
    rho.conditionalEntropy = qConditionalEnt rho.toMState / Real.log 2 := by
  rw [conditionalEntropy_eq, vonNeumann_eq_Sᵥₙ_div_log_two, vonNeumann_eq_Sᵥₙ_div_log_two,
    qConditionalEnt, toMState_marginalB]
  ring

end State

theorem mutualInformation_eq_qMutualInfo_div_log_two (rho : State (a × b)) :
    mutualInformation rho = qMutualInfo rho.toMState / Real.log 2 := by
  rw [mutualInformation, State.vonNeumann_eq_Sᵥₙ_div_log_two,
    State.vonNeumann_eq_Sᵥₙ_div_log_two, State.vonNeumann_eq_Sᵥₙ_div_log_two, qMutualInfo,
    State.toMState_marginalA, State.toMState_marginalB]
  ring

end QIT
