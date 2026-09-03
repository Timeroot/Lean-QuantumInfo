/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Purification.Gram
public import QIT.States.Purification.GramFactorization

/-!
# Purification equivalence by reference isometry

This module closes the finite-dimensional purification-equivalence route
registered from [Wilde2011Qst, qit-notes.tex:10320-10338] and
[Gour2024Resources, BookQRT.tex:2051-2069].

The proof composes the target-side amplitude Gram identity for purifications
with the corrected matrix Gram-factorization bridge.  It does not state
Uhlmann's theorem or any fidelity maximization result.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w

noncomputable section

namespace PureVector

variable {a : Type u}
variable [Fintype a] [DecidableEq a]

/-- Pure vectors are extensional in their amplitude functions. -/
theorem ext_amp {Ψ Φ : PureVector a} (h : Ψ.amp = Φ.amp) : Ψ = Φ := by
  cases Ψ
  cases Φ
  simp only at h
  subst h
  simp

variable {r₁ : Type u} {r₂ : Type v} {a : Type w}
variable [Fintype r₁] [DecidableEq r₁]
variable [Fintype r₂] [DecidableEq r₂]
variable [Fintype a] [DecidableEq a]

/-- Two purifications of the same state are related by a reference-side
isometry, provided the first reference system embeds into the second. -/
theorem exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state
    {Ψ : PureVector (Prod r₁ a)} {Φ : PureVector (Prod r₂ a)} {ρ : State a}
    (hΨ : Ψ.Purifies ρ) (hΦ : Φ.Purifies ρ)
    (hcard : Fintype.card r₁ ≤ Fintype.card r₂) :
    ∃ V : ReferenceIsometry r₁ r₂, Φ = V.applyPureVector Ψ := by
  have hGram :=
    amplitudeMatrix_mul_conjTranspose_eq_of_purifies_same_state hΨ hΦ
  obtain ⟨V, hV⟩ :=
    ReferenceIsometry.exists_eq_mul_transpose_of_mul_conjTranspose_eq
      Ψ.amplitudeMatrix Φ.amplitudeMatrix hGram hcard
  refine ⟨V, ?_⟩
  apply ext_amp
  funext p
  have hp := congrFun (congrFun hV p.2) p.1
  simpa [amplitudeMatrix, ReferenceIsometry.applyPureVector_amp,
    ReferenceIsometry.applyAmp, Matrix.mul_apply, Matrix.transpose,
    Matrix.mulVec, dotProduct, mul_comm] using hp

end PureVector

end

end QIT
