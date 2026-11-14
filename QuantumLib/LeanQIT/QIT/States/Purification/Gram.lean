/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Purification.Predicate

/-!
# Amplitude Gram matrices for purifications

This module exposes the target-side matrix view used by the purification
equivalence route registered from [Wilde2011Qst, qit-notes.tex:10320-10338]
and [Gour2024Resources, BookQRT.tex:2051-2069].  For a pure vector on
`Prod r a`, the reference system is the first factor.  The amplitude matrix
therefore has target rows and reference columns, so tracing out the reference
factor yields `A * Aᴴ`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
open Matrix

namespace QIT

universe u v w

noncomputable section

namespace PureVector

variable {r : Type u} {a : Type v}
variable [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]

/-- View a bipartite pure vector as a target-by-reference amplitude matrix.

The entry `Ψ.amplitudeMatrix x i` is the amplitude of reference basis vector
`i` and target basis vector `x`.  With the local `rankOneMatrix` convention,
the target marginal is `Ψ.amplitudeMatrix * Ψ.amplitudeMatrixᴴ`. -/
def amplitudeMatrix (Ψ : PureVector (Prod r a)) : Matrix a r Complex :=
  fun x i => Ψ.amp (i, x)

@[simp]
theorem amplitudeMatrix_apply (Ψ : PureVector (Prod r a)) (x : a) (i : r) :
    Ψ.amplitudeMatrix x i = Ψ.amp (i, x) :=
  rfl

/-- Tracing out the reference factor of a rank-one pure state gives the
target-side amplitude Gram matrix. -/
theorem partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose
    (Ψ : PureVector (Prod r a)) :
    partialTraceA (a := r) (b := a) (rankOneMatrix Ψ.amp) =
      Ψ.amplitudeMatrix * Matrix.conjTranspose Ψ.amplitudeMatrix := by
  ext x y
  simp [partialTraceA, rankOneMatrix_apply, amplitudeMatrix, Matrix.mul_apply]

/-- A purification predicate identifies the target-side amplitude Gram matrix
with the purified state's density matrix. -/
theorem purifies_amplitudeMatrix_mul_conjTranspose_eq
    {Ψ : PureVector (Prod r a)} {ρ : State a} (h : Ψ.Purifies ρ) :
    Ψ.amplitudeMatrix * Matrix.conjTranspose Ψ.amplitudeMatrix = ρ.matrix := by
  rw [← h]
  rw [PureVector.state_matrix]
  rw [partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose]

/-- Two purifications of the same state have equal target-side amplitude Gram
matrices. -/
theorem amplitudeMatrix_mul_conjTranspose_eq_of_purifies_same_state
    {r₁ : Type u} {r₂ : Type v} {a : Type w}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    [Fintype a] [DecidableEq a]
    {Ψ : PureVector (Prod r₁ a)} {Φ : PureVector (Prod r₂ a)} {ρ : State a}
    (hΨ : Ψ.Purifies ρ) (hΦ : Φ.Purifies ρ) :
    Ψ.amplitudeMatrix * Matrix.conjTranspose Ψ.amplitudeMatrix =
      Φ.amplitudeMatrix * Matrix.conjTranspose Φ.amplitudeMatrix := by
  rw [purifies_amplitudeMatrix_mul_conjTranspose_eq hΨ]
  rw [purifies_amplitudeMatrix_mul_conjTranspose_eq hΦ]

end PureVector

end

end QIT
