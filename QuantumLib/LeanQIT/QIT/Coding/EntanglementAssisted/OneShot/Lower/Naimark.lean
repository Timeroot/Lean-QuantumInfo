/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.SequentialDecoding
public import QIT.Measurements.Naimark

/-!
# One-shot entanglement-assisted lower-bound bridge

This module collects the proof bridges for the Khatri--Wilde one-shot
entanglement-assisted classical communication lower bound
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:530-665].

The source route starts from a hypothesis-testing effect, converts it to a
projective test through Naimark dilation, inserts the corresponding projectors
into the position-based sequential decoder, and finally converts the reliable
one-shot protocol into a lower bound on `C_EA^ε(N)`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

open SequentialDecoding

namespace HypothesisTestingEffect

variable {ρ σ : State a} {ε : ℝ}

/-- The Naimark accept projector associated to a feasible hypothesis-testing
effect.  It is the projective measurement outcome corresponding to accepting
the first hypothesis. -/
def acceptNaimarkProjection (Λ : HypothesisTestingEffect ρ ε) :
    ProjectionMatrix Λ.toBinaryHypothesisTest.FixedNaimarkSpace where
  matrix := Λ.toBinaryHypothesisTest.fixedNaimarkProjector true
  isHermitian := Λ.toBinaryHypothesisTest.fixedNaimarkProjector_isHermitian true
  idempotent := Λ.toBinaryHypothesisTest.fixedNaimarkProjector_idempotent true

@[simp]
theorem acceptNaimarkProjection_matrix (Λ : HypothesisTestingEffect ρ ε) :
    Λ.acceptNaimarkProjection.matrix =
      Λ.toBinaryHypothesisTest.fixedNaimarkProjector true :=
  rfl

/-- Naimark dilation preserves the accept probability of any tested state. -/
theorem effectTrace_fixedNaimark_accept
    (Λ : HypothesisTestingEffect ρ ε) (τ : State a) :
    effectTrace
        (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState τ)
        Λ.acceptNaimarkProjection.matrix =
      effectAcceptProbability τ Λ.effect := by
  unfold effectTrace effectAcceptProbability
  rw [acceptNaimarkProjection_matrix]
  exact congrArg Complex.re
    (Λ.toBinaryHypothesisTest.fixedNaimark_trace_projector_eq τ true)

/-- Naimark dilation preserves the accept probability of the source state. -/
theorem effectTrace_fixedNaimark_accept_source
    (Λ : HypothesisTestingEffect ρ ε) :
    effectTrace
        (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState ρ)
        Λ.acceptNaimarkProjection.matrix =
      effectAcceptProbability ρ Λ.effect :=
  Λ.effectTrace_fixedNaimark_accept ρ

/-- Naimark dilation preserves the type-II error of the comparison state. -/
theorem effectTrace_fixedNaimark_accept_comparison
    (Λ : HypothesisTestingEffect ρ ε) (σ : State a) :
    effectTrace
        (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState σ)
        Λ.acceptNaimarkProjection.matrix =
      Λ.typeIIError σ := by
  unfold HypothesisTestingEffect.typeIIError effectTypeIIError
  exact Λ.effectTrace_fixedNaimark_accept σ

/-- The Naimark accept projector inherits the hypothesis-testing type-I
acceptance constraint. -/
theorem fixedNaimark_accept_ge
    (Λ : HypothesisTestingEffect ρ ε) :
    1 - ε ≤
      effectTrace
        (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState ρ)
        Λ.acceptNaimarkProjection.matrix := by
  rw [Λ.effectTrace_fixedNaimark_accept_source]
  exact Λ.accept_ge

/-- The Naimark reject projector has missed-detection trace at most the
hypothesis-testing type-I error budget. -/
theorem fixedNaimark_reject_le
    (Λ : HypothesisTestingEffect ρ ε) :
    effectTrace
        (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState ρ)
        Λ.acceptNaimarkProjection.compl.matrix ≤ ε := by
  have hsum :
      effectTrace
          (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState ρ)
          Λ.acceptNaimarkProjection.matrix +
        effectTrace
          (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState ρ)
          Λ.acceptNaimarkProjection.compl.matrix = 1 :=
    effectTrace_add_compl
      (Λ.toBinaryHypothesisTest.fixedNaimarkLiftState ρ)
      Λ.acceptNaimarkProjection
  have haccept := Λ.fixedNaimark_accept_ge
  linarith

end HypothesisTestingEffect

end

end QIT
