/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.States.Purification.ReferenceIsometry
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Reference-system unitaries and ket overlaps

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
  /-- The underlying element of the unitary group. -/
  matrix : Matrix.unitaryGroup r ℂ

namespace ReferenceUnitary

variable {r : Type u} {a : Type v}
variable [Fintype r] [DecidableEq r]

variable (U : ReferenceUnitary r)

/-- The underlying matrix of a reference unitary. -/
def matrixCoe : Matrix r r ℂ :=
  U.matrix

/-- A reference unitary is, in particular, a reference isometry on the same register. -/
def toReferenceIsometry : ReferenceIsometry r r where
  matrix := U.matrix
  isometry := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U.matrix

variable [Fintype a] [DecidableEq a]

/-- Apply a reference unitary to the reference side of a bipartite ket. -/
def applyKet (Ψ : Ket (r × a)) : Ket (r × a) :=
  U.toReferenceIsometry.applyKet Ψ

/-- The unitary ket action unfolds to the underlying reference-isometry action. -/
theorem applyKet_eq_referenceIsometry (Ψ : Ket (r × a)) :
    U.applyKet Ψ = U.toReferenceIsometry.applyKet Ψ :=
  rfl

/-- The amplitude formula for applying a reference unitary. -/
theorem applyKet_vec (Ψ : Ket (r × a)) :
    (U.applyKet Ψ).vec = U.toReferenceIsometry.applyAmp Ψ.vec :=
  rfl

end ReferenceUnitary

end
end QIT

namespace Ket

noncomputable section

open QIT
universe u v

variable {a : Type u}
variable [Fintype a] [DecidableEq a]

/-- Bra-ket overlap of two kets, using the convention `⟨Ψ|Φ⟩`. -/
def overlap (Ψ Φ : Ket a) : ℂ :=
  ∑ i, star (Ψ.vec i) * Φ.vec i

/-- Squared magnitude of the ket overlap. -/
def overlapSq (Ψ Φ : Ket a) : ℝ :=
  Complex.normSq (Ψ.overlap Φ)

omit [DecidableEq a] in
/-- The overlap definition as a finite coordinate sum. -/
theorem overlap_eq_sum (Ψ Φ : Ket a) :
    Ψ.overlap Φ = ∑ i, star (Ψ.vec i) * Φ.vec i :=
  rfl

omit [DecidableEq a] in
/-- The squared overlap definition unfolds to `Complex.normSq`. -/
theorem overlapSq_eq_normSq (Ψ Φ : Ket a) :
    Ψ.overlapSq Φ = Complex.normSq (Ψ.overlap Φ) :=
  rfl

omit [DecidableEq a] in
/-- Squared overlaps are nonnegative. -/
theorem overlapSq_nonneg (Ψ Φ : Ket a) :
    0 ≤ Ψ.overlapSq Φ :=
  Complex.normSq_nonneg _

end

end Ket

namespace QIT
noncomputable section

universe u v

end

end QIT
