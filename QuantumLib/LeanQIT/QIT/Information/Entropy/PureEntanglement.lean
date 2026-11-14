/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Pure
public import QIT.Information.Entropy.Entropy

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

namespace PureVector

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

/-- Entanglement entropy of a finite bipartite pure state. -/
def entanglementEntropy (psi : PureVector (Prod a b)) : Real :=
  psi.state.marginalB.vonNeumann

/-- Either marginal computes the entanglement entropy of a bipartite pure state. -/
theorem entanglementEntropy_eq_marginalA (psi : PureVector (Prod a b)) :
    psi.entanglementEntropy = psi.state.marginalA.vonNeumann := by
  rw [entanglementEntropy]
  exact (State.pureVector_marginalA_vonNeumann_eq_marginalB psi).symm

/-- Swapping the two tensor factors does not change pure-state entanglement. -/
theorem entanglementEntropy_reindex_prodComm (psi : PureVector (Prod a b)) :
    (psi.reindex (Equiv.prodComm a b)).entanglementEntropy = psi.entanglementEntropy := by
  have hswap :
      (psi.reindex (Equiv.prodComm a b)).state.marginalB = psi.state.marginalA := by
    apply State.ext
    ext i j
    rfl
  rw [entanglementEntropy, entanglementEntropy, hswap]
  exact State.pureVector_marginalA_vonNeumann_eq_marginalB psi

end PureVector

end

end QIT
