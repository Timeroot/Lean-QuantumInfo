/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.ConditionalRenyi
public import QIT.Core.Pure
public import QIT.States.Subnormalized

/-!
# Pure-state trace bridge for upward sandwiched Renyi duality

This module isolates the pure-state marginal and bracket trace handoff used in
Tomamichel's proof of upward sandwiched conditional Renyi duality.

Source: Tomamichel2015FiniteResources, `cond.tex`, Proposition `pr:dual-new`,
proof lines 366-400.  The final Sion minimax step and the final conditional
Renyi duality theorem remain downstream work.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

namespace State

/-- Lift an `AB` operator to the left-associated tripartite system `ABC`. -/
def liftABToABC (MAB : CMatrix (Prod a b)) : CMatrix (Prod (Prod a b) c) :=
  fun x y => if x.2 = y.2 then MAB x.1 y.1 else 0

/-- Lift an `AC` operator to the left-associated tripartite system `ABC`,
acting as the identity on the middle `B` register. -/
def liftACToABC (MAC : CMatrix (Prod a c)) : CMatrix (Prod (Prod a b) c) :=
  fun x y =>
    if x.1.2 = y.1.2 then MAC (x.1.1, x.2) (y.1.1, y.2) else 0

/-- The source-shaped `I_A ⊗ σ_B^{-α'} ⊗ τ_C^{α'}` matrix appearing in the
common bracket expression in `cond.tex`, Proposition `pr:dual-new`. -/
def abcSideStatePowerMatrix (σB : State b) (τC : State c) (alphaPrime : ℝ) :
    CMatrix (Prod (Prod a b) c) :=
  Matrix.kronecker
    (Matrix.kronecker (1 : CMatrix a) (CFC.rpow σB.matrix (-alphaPrime)))
    (CFC.rpow τC.matrix alphaPrime)

end State

namespace PureVector

/-- Tripartite bracket `⟨ψ|M|ψ⟩`, represented as a trace against the rank-one
state matrix. -/
def tripartiteBracket (ψ : PureVector (Prod (Prod a b) c))
    (M : CMatrix (Prod (Prod a b) c)) : ℂ :=
  (M * ψ.state.matrix).trace

/-- Lifting an `AB` operator to `ABC` and evaluating it on a pure tripartite
state is the same as tracing that operator against the `AB` marginal. -/
theorem tripartiteBracket_liftABToABC_eq_trace_marginalAB
    (ψ : PureVector (Prod (Prod a b) c)) (MAB : CMatrix (Prod a b)) :
    ψ.tripartiteBracket (State.liftABToABC (c := c) MAB) =
      (MAB * ψ.state.marginalAB.matrix).trace := by
  simp [tripartiteBracket, State.liftABToABC, State.marginalAB, State.marginalA,
    partialTraceB, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x' _
  conv_lhs => rw [Finset.sum_comm]

/-- Lifting an `AC` operator to `ABC` and evaluating it on a pure tripartite
state is the same as tracing that operator against the `AC` marginal. -/
theorem tripartiteBracket_liftACToABC_eq_trace_marginalAC
    (ψ : PureVector (Prod (Prod a b) c)) (MAC : CMatrix (Prod a c)) :
    ψ.tripartiteBracket (State.liftACToABC (b := b) MAC) =
      (MAC * ψ.state.marginalAC.matrix).trace := by
  simp [tripartiteBracket, State.liftACToABC, State.marginalAC, Matrix.trace,
    Matrix.mul_apply, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  let f : a → b → c → a → c → ℂ := fun x y z x' z' =>
    MAC (x, z) (x', z') *
      (ψ.amp ((x', y), z') * star (ψ.amp ((x, y), z)))
  change (∑ x : a, ∑ y : b, ∑ z : c, ∑ x' : a, ∑ z' : c,
      f x y z x' z') =
    ∑ x : a, ∑ z : c, ∑ x' : a, ∑ z' : c, ∑ y : b,
      f x y z x' z'
  calc
    (∑ x : a, ∑ y : b, ∑ z : c, ∑ x' : a, ∑ z' : c,
        f x y z x' z') =
        ∑ x : a, ∑ z : c, ∑ y : b, ∑ x' : a, ∑ z' : c,
          f x y z x' z' := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ x : a, ∑ z : c, ∑ x' : a, ∑ y : b, ∑ z' : c,
          f x y z x' z' := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_comm]
    _ = ∑ x : a, ∑ z : c, ∑ x' : a, ∑ z' : c, ∑ y : b,
          f x y z x' z' := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x' _
      rw [Finset.sum_comm]

/-- The common bracket expression reached by the pure-state trace bridge in
Tomamichel's upward sandwiched conditional Renyi duality proof. -/
def upwardRenyiDualityCommonBracket (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c) (alphaPrime : ℝ) : ℂ :=
  ψ.tripartiteBracket (State.abcSideStatePowerMatrix (a := a) σB τC alphaPrime)

/-- Scale a normalized pure vector state into a subnormalized state.

This is only the scale-compatible trace bridge; the final subnormalized
conditional Renyi duality theorem remains downstream. -/
def toSubnormalizedScaled {α : Type u} [Fintype α] [DecidableEq α]
    (ψ : PureVector α) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SubnormalizedState α where
  matrix := t • ψ.state.matrix
  pos := Matrix.PosSemidef.smul ψ.state.pos ht0
  trace_le_one := by
    rw [Matrix.trace_smul, ψ.state.trace_eq_one]
    simpa [Complex.real_smul] using ht1

/-- Evaluating an observable on a scaled pure subnormalized state pulls out the
real scaling factor. -/
theorem trace_mul_toSubnormalizedScaled_eq (ψ : PureVector (Prod (Prod a b) c))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (M : CMatrix (Prod (Prod a b) c)) :
    (M * (ψ.toSubnormalizedScaled t ht0 ht1).matrix).trace =
      (t : ℂ) * ψ.tripartiteBracket M := by
  simp [toSubnormalizedScaled, tripartiteBracket, Matrix.trace_smul]

end PureVector

end

end QIT
