/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Core.Pure
public import QuantumLib.QIT.Information.Entropy.Entropy

/-!
# Entanglement entropy of bipartite pure states

The entropy of entanglement of a finite-dimensional bipartite pure state,
defined as the von Neumann entropy of either marginal, together with
invariance under swapping the two tensor factors.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

end
end QIT

namespace Ket

noncomputable section

open QIT
universe u v

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

/-- Entanglement entropy of a finite bipartite pure state. -/
def entanglementEntropy (psi : Ket (a × b)) : ℝ :=
  psi.state.traceLeft.vonNeumann

/-- Either marginal computes the entanglement entropy of a bipartite pure state. -/
theorem entanglementEntropy_eq_traceRight (psi : Ket (a × b)) :
    psi.entanglementEntropy = psi.state.traceRight.vonNeumann := by
  rw [entanglementEntropy]
  exact (MState.ket_traceRight_vonNeumann_eq_traceLeft psi).symm

/-- Swapping the two tensor factors does not change pure-state entanglement. -/
theorem entanglementEntropy_reindex_prodComm (psi : Ket (a × b)) :
    (psi.reindex (Equiv.prodComm a b)).entanglementEntropy = psi.entanglementEntropy := by
  have hswap :
      (psi.reindex (Equiv.prodComm a b)).state.traceLeft = psi.state.traceRight := by
    apply MState.ext
    rw [MState.traceLeft_m, MState.traceRight_m, Ket.state_matrix,
      Ket.state_matrix]
    ext i j
    rfl
  rw [entanglementEntropy, entanglementEntropy, hswap]
  exact MState.ket_traceRight_vonNeumann_eq_traceLeft psi

end

end Ket

namespace QIT
noncomputable section

universe u v

end

end QIT
