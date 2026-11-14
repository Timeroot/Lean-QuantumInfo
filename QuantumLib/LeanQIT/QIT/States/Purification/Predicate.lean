/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Pure

/-!
# Purification predicates

This module fixes the local reference-system convention for purification work.
For a pure vector on `Prod r a`, the first factor `r` is the reference register
and the second factor `a` is the target system. A purification of a target state
is therefore stated by tracing out the first factor with `partialTraceA`, matching
the source route registered from [Wilde2011Qst, qit-notes.tex:10238-10290] and
[Gour2024Resources, BookQRT.tex:2051-2069]. With this product orientation,
`partialTraceB` traces out the target system and leaves the reference system.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

namespace PureVector

variable {r : Type u} {a : Type v}
variable [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]

/-- A bipartite pure vector on `Prod r a` purifies a target state on `a`.

The first product factor `r` is the reference register. The predicate traces out
that first factor with `partialTraceA`, leaving the target system `a`. -/
def Purifies (Ψ : PureVector (Prod r a)) (ρ : State a) : Prop :=
  partialTraceA (a := r) (b := a) Ψ.state.matrix = ρ.matrix

/-- Unfold the purification predicate to the reference-trace convention. -/
@[simp]
theorem purifies_iff (Ψ : PureVector (Prod r a)) (ρ : State a) :
    Ψ.Purifies ρ ↔
      partialTraceA (a := r) (b := a) Ψ.state.matrix = ρ.matrix :=
  Iff.rfl

/-- A purification predicate directly gives the target reduced state. -/
theorem partialTraceA_state_matrix_eq_of_purifies
    {Ψ : PureVector (Prod r a)} {ρ : State a} (h : Ψ.Purifies ρ) :
    partialTraceA (a := r) (b := a) Ψ.state.matrix = ρ.matrix :=
  h

/-- Swapping the two registers of a pure state makes it a purification of the
original first marginal.  This adapter converts the channel-input-first
convention used by finite diamond-distance statements into the local
purification convention where the purified target is the second product
factor. -/
theorem reindex_prodComm_purifies_marginalA (Ψ : PureVector (Prod r a)) :
    (Ψ.reindex (Equiv.prodComm r a)).Purifies Ψ.state.marginalA := by
  rw [purifies_iff]
  ext i j
  simp [PureVector.reindex_state, State.reindex, State.marginalA, partialTraceA,
    partialTraceB, PureVector.state_matrix, rankOneMatrix_apply]

end PureVector

end

end QIT
