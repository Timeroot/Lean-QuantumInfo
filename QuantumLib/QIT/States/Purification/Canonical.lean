/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Core.Pure
public import QuantumLib.QIT.States.MaximallyEntangled
public import QuantumLib.QIT.States.MaximallyMixed
public import QuantumLib.QIT.States.Purification.Equivalence
public import QuantumLib.QIT.States.Purification.Predicate
public import QuantumLib.QIT.States.PosSqrt

/-!
# Canonical purification

The canonical purification of a density state built from its positive
semidefinite square root and a maximally entangled vector, following the
canonical square-root construction registered from [Wilde2011Qst,
qit-notes.tex:10238-10290] and [Gour2024Resources, BookQRT.tex:2051-2069].
The reference system is the first factor of `(a × a`), traced out by
`Matrix.traceLeft`, matching the convention in `QIT.States.Purification.Predicate`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

noncomputable section
universe u
variable {a : Type u} [Fintype a] [DecidableEq a]

open QIT

namespace MState

/-- The canonical purification amplitude: the maximally-entangled reshape
`ψ(i,j) = (√ρ)_{j i}`, with reference index `i` and target index `j`. -/
def canonicalPurificationAmp (ρ : MState a) : a × a → ℂ :=
  fun (i, j) => ρ.sqrtMatrix j i

/-- The rank-one kernel of the canonical amplitude traces back to the state:
`Matrix.traceLeft (rankOneMatrix ψ) = ρ.m`. -/
theorem canonicalPurification_matrix (ρ : MState a) :
    Matrix.traceLeft (rankOneMatrix ρ.canonicalPurificationAmp) = ρ.m := by
  ext j j'
  simp only [Matrix.traceLeft, Matrix.of_apply, rankOneMatrix_apply, MState.canonicalPurificationAmp]
  rw [← ρ.sqrtMatrix_mul_self, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ρ.sqrtMatrix_isHermitian.apply i j']

/-- The canonical purification of `ρ`, as a ket on `(a × a`). -/
def canonicalPurification (ρ : MState a) : Ket (a × a) :=
  Ket.ofRankOne ρ.canonicalPurificationAmp <| by
    rw [← Matrix.traceLeft_trace (rankOneMatrix ρ.canonicalPurificationAmp),
        canonicalPurification_matrix]
    exact ρ.tr'

/-- The canonical purification purifies `ρ`. -/
theorem canonicalPurification_purifies (ρ : MState a) :
    ρ.canonicalPurification.Purifies ρ := by
  rw [Ket.purifies_iff, Ket.state_matrix]
  exact canonicalPurification_matrix ρ

/-- Swapping the canonical purification of a state puts the purified system in
the left factor, so tracing out the right factor returns the original state. -/
theorem canonicalPurification_reindex_prodComm_traceRight (ρ : MState a) :
    (ρ.canonicalPurification.reindex (Equiv.prodComm a a)).state.traceRight = ρ := by
  apply MState.ext
  ext i j
  have hp : Matrix.traceLeft ρ.canonicalPurification.state.m = ρ.m :=
    Ket.traceLeft_state_matrix_eq_of_purifies ρ.canonicalPurification_purifies
  have hpij := congrFun (congrFun hp i) j
  simpa [Matrix.traceRight, Matrix.traceLeft, Ket.reindex_state] using hpij

/-- The canonical purification of the maximally mixed state is the canonical
maximally entangled ket on the same register order. -/
theorem canonicalPurification_uniform [Nonempty a] :
    canonicalPurification (MState.uniform : MState a) =
      Ket.maximallyEntangled (Equiv.refl a) := by
  apply Ket.ext_vec
  funext x
  rcases x with ⟨i, j⟩
  by_cases h : i = j
  · subst j
    simp [canonicalPurification, canonicalPurificationAmp,
      MState.uniform_sqrtMatrix, Ket.maximallyEntangled_vec]
  · have h' : ¬ j = i := by
      intro hji
      exact h hji.symm
    simp [canonicalPurification, canonicalPurificationAmp,
      MState.uniform_sqrtMatrix, Ket.maximallyEntangled_vec, h, h']

end MState
