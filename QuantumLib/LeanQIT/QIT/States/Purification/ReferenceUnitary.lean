/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Purification.ReferenceIsometry
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Reference-system unitaries and pure-vector overlaps

This module supplies the local reference-unitary and overlap API needed for the
Uhlmann route registered from [Wilde2011Qst, qit-notes.tex:15060-15093] and the
trace-norm variational source claim [Wilde2011Qst, qit-notes.tex:14119-14127].
It only packages the unitary action and overlap convention; it does not state
the trace-norm variational theorem or Uhlmann's theorem.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

/-- A unitary acting on a finite purifying reference register. -/
structure ReferenceUnitary (r : Type u) [Fintype r] [DecidableEq r] where
  matrix : Matrix.unitaryGroup r Complex

namespace ReferenceUnitary

variable {r : Type u} {a : Type v}
variable [Fintype r] [DecidableEq r]

variable (U : ReferenceUnitary r)

/-- The underlying matrix of a reference unitary. -/
def matrixCoe : Matrix r r Complex :=
  U.matrix

/-- A reference unitary is, in particular, a reference isometry on the same register. -/
def toReferenceIsometry : ReferenceIsometry r r where
  matrix := U.matrix
  isometry := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U.matrix

variable [Fintype a] [DecidableEq a]

/-- Apply a reference unitary to the reference side of a bipartite pure vector. -/
def applyPureVector (Ψ : PureVector (Prod r a)) : PureVector (Prod r a) :=
  U.toReferenceIsometry.applyPureVector Ψ

/-- The unitary pure-vector action unfolds to the underlying reference-isometry action. -/
theorem applyPureVector_eq_referenceIsometry (Ψ : PureVector (Prod r a)) :
    U.applyPureVector Ψ = U.toReferenceIsometry.applyPureVector Ψ :=
  rfl

/-- The amplitude formula for applying a reference unitary. -/
theorem applyPureVector_amp (Ψ : PureVector (Prod r a)) :
    (U.applyPureVector Ψ).amp = U.toReferenceIsometry.applyAmp Ψ.amp :=
  rfl

end ReferenceUnitary

namespace PureVector

variable {a : Type u}
variable [Fintype a] [DecidableEq a]

/-- Bra-ket overlap of two pure vectors, using the convention `⟨Ψ|Φ⟩`. -/
def overlap (Ψ Φ : PureVector a) : ℂ :=
  ∑ i, star (Ψ.amp i) * Φ.amp i

/-- Squared magnitude of the pure-vector overlap. -/
def overlapSq (Ψ Φ : PureVector a) : ℝ :=
  Complex.normSq (Ψ.overlap Φ)

/-- The overlap definition as a finite coordinate sum. -/
theorem overlap_eq_sum (Ψ Φ : PureVector a) :
    Ψ.overlap Φ = ∑ i, star (Ψ.amp i) * Φ.amp i :=
  rfl

/-- The squared overlap definition unfolds to `Complex.normSq`. -/
theorem overlapSq_eq_normSq (Ψ Φ : PureVector a) :
    Ψ.overlapSq Φ = Complex.normSq (Ψ.overlap Φ) :=
  rfl

/-- Squared overlaps are nonnegative. -/
theorem overlapSq_nonneg (Ψ Φ : PureVector a) :
    0 ≤ Ψ.overlapSq Φ :=
  Complex.normSq_nonneg _

end PureVector

end

end QIT
