/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Pure
public import QIT.States.MaximallyEntangled
public import QIT.States.MaximallyMixed
public import QIT.States.Purification.Equivalence
public import QIT.States.Purification.Predicate
public import QIT.States.PosSqrt

/-!
# Canonical purification

The canonical purification of a density state built from its positive
semidefinite square root and a maximally entangled vector, following the
canonical square-root construction registered from [Wilde2011Qst,
qit-notes.tex:10238-10290] and [Gour2024Resources, BookQRT.tex:2051-2069].
The reference system is the first factor of `Prod a a`, traced out by
`partialTraceA`, matching the convention in `QIT.States.Purification.Predicate`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

namespace State

/-- The canonical purification amplitude: the maximally-entangled reshape
`ψ(i,j) = (√ρ)_{j i}`, with reference index `i` and target index `j`. -/
def canonicalPurificationAmp (ρ : State a) : Prod a a → ℂ :=
  fun (i, j) => ρ.sqrtMatrix j i

/-- The rank-one kernel of the canonical amplitude traces back to the state:
`partialTraceA (rankOneMatrix ψ) = ρ.matrix`. -/
theorem canonicalPurification_matrix (ρ : State a) :
    partialTraceA (rankOneMatrix ρ.canonicalPurificationAmp) = ρ.matrix := by
  ext j j'
  simp only [partialTraceA, rankOneMatrix_apply, State.canonicalPurificationAmp]
  rw [← ρ.sqrtMatrix_mul_self, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ρ.sqrtMatrix_isHermitian.apply i j']

/-- The canonical purification of `ρ`, as a pure vector on `Prod a a`. -/
def canonicalPurification (ρ : State a) : PureVector (Prod a a) where
  amp := ρ.canonicalPurificationAmp
  trace_rankOne_eq_one := by
    rw [← partialTraceA_trace (rankOneMatrix ρ.canonicalPurificationAmp),
        canonicalPurification_matrix]
    exact ρ.trace_eq_one

/-- The canonical purification purifies `ρ`. -/
theorem canonicalPurification_purifies (ρ : State a) :
    ρ.canonicalPurification.Purifies ρ := by
  rw [PureVector.purifies_iff, PureVector.state_matrix]
  exact canonicalPurification_matrix ρ

/-- The canonical purification of the maximally mixed state is the canonical
maximally entangled pure vector on the same register order. -/
theorem canonicalPurification_maximallyMixed [Nonempty a] :
    canonicalPurification (maximallyMixed a) =
      PureVector.maximallyEntangled (Equiv.refl a) := by
  apply PureVector.ext_amp
  funext x
  rcases x with ⟨i, j⟩
  by_cases h : i = j
  · subst j
    simp [canonicalPurification, canonicalPurificationAmp,
      State.maximallyMixed_sqrtMatrix, PureVector.maximallyEntangled_amp]
  · have h' : ¬ j = i := by
      intro hji
      exact h hji.symm
    simp [canonicalPurification, canonicalPurificationAmp,
      State.maximallyMixed_sqrtMatrix, PureVector.maximallyEntangled_amp, h, h']

end State

end

end QIT
