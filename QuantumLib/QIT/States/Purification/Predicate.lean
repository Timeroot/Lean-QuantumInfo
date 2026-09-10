/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Core.Pure

/-!
# Purification predicates

This module fixes the local reference-system convention for purification work.
For a ket on `(r × a`), the first factor `r` is the reference register
and the second factor `a` is the target system. A purification of a target state
is therefore stated by tracing out the first factor with `Matrix.traceLeft`, matching
the source route registered from [Wilde2011Qst, qit-notes.tex:10238-10290] and
[Gour2024Resources, BookQRT.tex:2051-2069]. With this product orientation,
`Matrix.traceRight` traces out the target system and leaves the reference system.
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

variable {r : Type u} {a : Type v}
variable [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]

/-- A bipartite ket on `(r × a`) purifies a target state on `a`.

The first product factor `r` is the reference register. The predicate traces out
that first factor with `Matrix.traceLeft`, leaving the target system `a`. -/
def Purifies (Ψ : Ket (r × a)) (ρ : MState a) : Prop :=
  Matrix.traceLeft Ψ.state.m = ρ.m

/-- Unfold the purification predicate to the reference-trace convention. -/
@[simp]
theorem purifies_iff (Ψ : Ket (r × a)) (ρ : MState a) :
    Ψ.Purifies ρ ↔
      Matrix.traceLeft Ψ.state.m = ρ.m :=
  Iff.rfl

/-- A purification predicate directly gives the target reduced state. -/
theorem traceLeft_state_matrix_eq_of_purifies
    {Ψ : Ket (r × a)} {ρ : MState a} (h : Ψ.Purifies ρ) :
    Matrix.traceLeft Ψ.state.m = ρ.m :=
  h

/-- Swapping the two registers of a pure state makes it a purification of the
original first marginal.  This adapter converts the channel-input-first
convention used by finite diamond-distance statements into the local
purification convention where the purified target is the second product
factor. -/
theorem reindex_prodComm_purifies_traceRight (Ψ : Ket (r × a)) :
    (Ψ.reindex (Equiv.prodComm r a)).Purifies Ψ.state.traceRight := by
  rw [purifies_iff]
  ext i j
  simp [Ket.reindex_state, Matrix.traceLeft, Matrix.traceRight, Ket.state_matrix,
    rankOneMatrix_apply]

end

end Ket

namespace QIT
noncomputable section

universe u v

end

end QIT
