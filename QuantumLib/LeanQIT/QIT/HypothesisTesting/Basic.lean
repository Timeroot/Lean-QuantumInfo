/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.POVMProbability
public import QIT.States.TraceNorm.PositivePart

/-!
# Binary hypothesis tests

Finite-dimensional binary hypothesis tests are represented by two-outcome
POVMs.  The `true` outcome accepts the first state, so the type-I error is the
probability of `false` on that state and the type-II error is the probability
of `true` on the second state.  This is the convention behind the equal-prior
binary testing expression [Tomamichel2015FiniteResources, apps.tex:46-50].

The same two-outcome effect convention is compatible with the Helstrom
discrimination setup [Audenaert2006QuantumChernoff,
audenaert-2006-quantum-chernoff.tex:258-263], but the trace-norm optimality
formula is not part of this definition-level API.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u

noncomputable section

/-- A finite-dimensional binary hypothesis test, with `true` accepting the
first state and `false` accepting the second state. -/
abbrev BinaryHypothesisTest (a : Type u) [Fintype a] [DecidableEq a] :=
  POVM Bool a

/-- A binary test on `n` IID copies of a finite system. -/
abbrev TensorPowerHypothesisTest (a : Type u) [Fintype a] [DecidableEq a] (n : Nat) :=
  BinaryHypothesisTest (TensorPower a n)

namespace BinaryHypothesisTest

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- The effect for accepting the first state. -/
def acceptRhoEffect (T : BinaryHypothesisTest a) : CMatrix a :=
  T.effects true

/-- The complementary effect for rejecting the first state. -/
def rejectRhoEffect (T : BinaryHypothesisTest a) : CMatrix a :=
  T.effects false

/-- The accept effect is positive semidefinite. -/
theorem acceptRhoEffect_pos (T : BinaryHypothesisTest a) :
    T.acceptRhoEffect.PosSemidef :=
  T.pos true

/-- The reject effect is positive semidefinite. -/
theorem rejectRhoEffect_pos (T : BinaryHypothesisTest a) :
    T.rejectRhoEffect.PosSemidef :=
  T.pos false

/-- The accept effect is nonnegative in the matrix order. -/
theorem acceptRhoEffect_nonneg (T : BinaryHypothesisTest a) :
    0 ≤ T.acceptRhoEffect :=
  T.acceptRhoEffect_pos.nonneg

/-- The reject effect is nonnegative in the matrix order. -/
theorem rejectRhoEffect_nonneg (T : BinaryHypothesisTest a) :
    0 ≤ T.rejectRhoEffect :=
  T.rejectRhoEffect_pos.nonneg

/-- The two effects of a binary test sum to the identity. -/
theorem acceptRhoEffect_add_rejectRhoEffect (T : BinaryHypothesisTest a) :
    T.acceptRhoEffect + T.rejectRhoEffect = 1 := by
  simpa [rejectRhoEffect, acceptRhoEffect] using T.sum_eq_one

/-- The two effects of a binary test sum to the identity, in the opposite order. -/
theorem rejectRhoEffect_add_acceptRhoEffect (T : BinaryHypothesisTest a) :
    T.rejectRhoEffect + T.acceptRhoEffect = 1 := by
  simpa [add_comm] using T.acceptRhoEffect_add_rejectRhoEffect

/-- The accept effect is bounded above by the identity. -/
theorem acceptRhoEffect_le_one (T : BinaryHypothesisTest a) :
    T.acceptRhoEffect ≤ 1 := by
  rw [Matrix.le_iff]
  have hsum := T.rejectRhoEffect_add_acceptRhoEffect
  have hcomp : 1 - T.acceptRhoEffect = T.rejectRhoEffect := by
    calc
      1 - T.acceptRhoEffect =
          (T.rejectRhoEffect + T.acceptRhoEffect) - T.acceptRhoEffect := by rw [hsum]
      _ = T.rejectRhoEffect := by simp
  simpa [hcomp] using T.rejectRhoEffect_pos

/-- The reject effect is bounded above by the identity. -/
theorem rejectRhoEffect_le_one (T : BinaryHypothesisTest a) :
    T.rejectRhoEffect ≤ 1 := by
  rw [Matrix.le_iff]
  have hsum := T.rejectRhoEffect_add_acceptRhoEffect
  have hcomp : 1 - T.rejectRhoEffect = T.acceptRhoEffect := by
    calc
      1 - T.rejectRhoEffect =
          (T.rejectRhoEffect + T.acceptRhoEffect) - T.rejectRhoEffect := by rw [hsum]
      _ = T.acceptRhoEffect := by simp [add_comm]
  simpa [hcomp] using T.acceptRhoEffect_pos

/-- Probability that the test accepts the first state. -/
def acceptProb (T : BinaryHypothesisTest a) (rho : State a) : ℝ≥0 :=
  T.prob rho true

/-- Probability that the test rejects the first state. -/
def rejectProb (T : BinaryHypothesisTest a) (rho : State a) : ℝ≥0 :=
  T.prob rho false

/-- Accept probability as a real Born-rule trace expression. -/
theorem acceptProb_eq_trace_re (T : BinaryHypothesisTest a) (rho : State a) :
    (T.acceptProb rho : ℝ) =
      Complex.re ((rho.matrix * T.acceptRhoEffect).trace) := by
  simpa [acceptProb, acceptRhoEffect] using T.prob_eq_trace_re rho true

/-- Reject probability as a real Born-rule trace expression. -/
theorem rejectProb_eq_trace_re (T : BinaryHypothesisTest a) (rho : State a) :
    (T.rejectProb rho : ℝ) =
      Complex.re ((rho.matrix * T.rejectRhoEffect).trace) := by
  simpa [rejectProb, rejectRhoEffect] using T.prob_eq_trace_re rho false

/-- Type-I error: reject the first state when it is true. -/
def typeIError (T : BinaryHypothesisTest a) (rho : State a) : ℝ≥0 :=
  T.rejectProb rho

/-- Type-II error: accept the first state when the second state is true. -/
def typeIIError (T : BinaryHypothesisTest a) (sigma : State a) : ℝ≥0 :=
  T.acceptProb sigma

/-- Equal-prior average of type-I and type-II errors. -/
def equalPriorError (T : BinaryHypothesisTest a) (rho sigma : State a) : ℝ≥0 :=
  (T.typeIError rho + T.typeIIError sigma) / 2

/-- Type-I error is nonnegative as a real number. -/
theorem typeIError_nonneg (T : BinaryHypothesisTest a) (rho : State a) :
    0 ≤ (T.typeIError rho : ℝ) :=
  NNReal.coe_nonneg _

/-- Type-II error is nonnegative as a real number. -/
theorem typeIIError_nonneg (T : BinaryHypothesisTest a) (sigma : State a) :
    0 ≤ (T.typeIIError sigma : ℝ) :=
  NNReal.coe_nonneg _

/-- Equal-prior error is nonnegative as a real number. -/
theorem equalPriorError_nonneg (T : BinaryHypothesisTest a) (rho sigma : State a) :
    0 ≤ (T.equalPriorError rho sigma : ℝ) :=
  NNReal.coe_nonneg _

/-- Type-I error is bounded above by one. -/
theorem typeIError_le_one (T : BinaryHypothesisTest a) (rho : State a) :
  T.typeIError rho ≤ 1 := by
  have hle : T.prob rho false ≤ ∑ outcome : Bool, T.prob rho outcome :=
    Finset.single_le_sum (fun _ _ => by exact bot_le) (Finset.mem_univ false)
  rw [T.sum_prob rho] at hle
  simpa [typeIError, rejectProb] using hle

/-- Type-II error is bounded above by one. -/
theorem typeIIError_le_one (T : BinaryHypothesisTest a) (sigma : State a) :
  T.typeIIError sigma ≤ 1 := by
  have hle : T.prob sigma true ≤ ∑ outcome : Bool, T.prob sigma outcome :=
    Finset.single_le_sum (fun _ _ => by exact bot_le) (Finset.mem_univ true)
  rw [T.sum_prob sigma] at hle
  simpa [typeIIError, acceptProb] using hle

/-- Equal-prior error is bounded above by one. -/
theorem equalPriorError_le_one (T : BinaryHypothesisTest a) (rho sigma : State a) :
    T.equalPriorError rho sigma ≤ 1 := by
  apply NNReal.coe_le_coe.mp
  have hI : (T.typeIError rho : ℝ) ≤ 1 := by
    exact_mod_cast T.typeIError_le_one rho
  have hII : (T.typeIIError sigma : ℝ) ≤ 1 := by
    exact_mod_cast T.typeIIError_le_one sigma
  change ((T.typeIError rho + T.typeIIError sigma) / 2 : ℝ≥0) ≤ (1 : ℝ)
  simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_ofNat]
  nlinarith

/-- The reject effect is the complement of the accept effect. -/
theorem rejectRhoEffect_eq_one_sub_acceptRhoEffect (T : BinaryHypothesisTest a) :
    T.rejectRhoEffect = 1 - T.acceptRhoEffect := by
  have hsum := T.acceptRhoEffect_add_rejectRhoEffect
  calc
    T.rejectRhoEffect = (T.acceptRhoEffect + T.rejectRhoEffect) - T.acceptRhoEffect := by
      simp
    _ = 1 - T.acceptRhoEffect := by rw [hsum]

/-- Equal-prior error as `1/2 * (1 - Tr((rho-sigma)T))`. -/
theorem equalPriorError_eq_half_one_sub_score
    (T : BinaryHypothesisTest a) (rho sigma : State a) :
    (T.equalPriorError rho sigma : ℝ) =
      (1 / 2 : ℝ) *
        (1 - (((rho.matrix - sigma.matrix) * T.acceptRhoEffect).trace).re) := by
  have hreject := T.rejectProb_eq_trace_re rho
  have haccept := T.acceptProb_eq_trace_re sigma
  have hreject_trace :
      Complex.re ((rho.matrix * T.rejectRhoEffect).trace) =
        1 - Complex.re ((rho.matrix * T.acceptRhoEffect).trace) := by
    rw [rejectRhoEffect_eq_one_sub_acceptRhoEffect T]
    calc
      Complex.re ((rho.matrix * (1 - T.acceptRhoEffect)).trace) =
          Complex.re ((rho.matrix - rho.matrix * T.acceptRhoEffect).trace) := by
            rw [Matrix.mul_sub, Matrix.mul_one]
      _ = Complex.re (rho.matrix.trace - (rho.matrix * T.acceptRhoEffect).trace) := by
            rw [Matrix.trace_sub]
      _ = 1 - Complex.re ((rho.matrix * T.acceptRhoEffect).trace) := by
            rw [rho.trace_eq_one]
            simp
  have hscore :
      (((rho.matrix - sigma.matrix) * T.acceptRhoEffect).trace).re =
        Complex.re ((rho.matrix * T.acceptRhoEffect).trace) -
          Complex.re ((sigma.matrix * T.acceptRhoEffect).trace) := by
    rw [Matrix.sub_mul, Matrix.trace_sub]
    simp
  unfold BinaryHypothesisTest.equalPriorError BinaryHypothesisTest.typeIError
    BinaryHypothesisTest.typeIIError
  change ((T.rejectProb rho + T.acceptProb sigma) / 2 : ℝ≥0) =
    (1 / 2 : ℝ) *
      (1 - (((rho.matrix - sigma.matrix) * T.acceptRhoEffect).trace).re)
  simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_ofNat]
  rw [hreject, haccept, hreject_trace, hscore]
  ring

/-- Helstrom lower bound for every binary test. -/
theorem helstrom_equalPriorError_lower_bound
    (T : BinaryHypothesisTest a) (rho sigma : State a) :
    (1 / 2 : ℝ) * (1 - rho.normalizedTraceDistance sigma) ≤
      (T.equalPriorError rho sigma : ℝ) := by
  let H : CMatrix a := rho.matrix - sigma.matrix
  let hH : H.IsHermitian := rho.pos.isHermitian.sub sigma.pos.isHermitian
  have hscore_le :
      (((H * T.acceptRhoEffect).trace).re) ≤ (H⁺).trace.re :=
    hermitian_trace_mul_effect_le_posPart_trace H T.acceptRhoEffect hH
      T.acceptRhoEffect_pos T.acceptRhoEffect_le_one
  have hdist := normalizedTraceDistance_eq_posPart_trace rho sigma
  rw [equalPriorError_eq_half_one_sub_score]
  change (1 / 2 : ℝ) * (1 - rho.normalizedTraceDistance sigma) ≤
    (1 / 2 : ℝ) * (1 - (((H * T.acceptRhoEffect).trace).re))
  rw [hdist]
  nlinarith

/-- Type-I error on IID tensor powers. -/
def typeIErrorTensorPower {n : Nat} (T : TensorPowerHypothesisTest a n) (rho : State a) : ℝ≥0 :=
  T.typeIError (State.tensorPower rho n)

/-- Type-II error on IID tensor powers. -/
def typeIIErrorTensorPower {n : Nat} (T : TensorPowerHypothesisTest a n) (sigma : State a) : ℝ≥0 :=
  T.typeIIError (State.tensorPower sigma n)

/-- Equal-prior error on IID tensor powers. -/
def equalPriorTensorPowerError {n : Nat} (T : TensorPowerHypothesisTest a n)
    (rho sigma : State a) : ℝ≥0 :=
  T.equalPriorError (State.tensorPower rho n) (State.tensorPower sigma n)

end BinaryHypothesisTest

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Helstrom test: accept the first state on the positive spectral subspace of `rho - sigma`. -/
def helstromTest (rho sigma : State a) : BinaryHypothesisTest a :=
  let H : CMatrix a := rho.matrix - sigma.matrix
  let hH : H.IsHermitian := rho.pos.isHermitian.sub sigma.pos.isHermitian
  let P : CMatrix a := positiveSpectralProjector H hH
  let hPpos : P.PosSemidef := positiveSpectralProjector_posSemidef H hH
  let hPle : P ≤ 1 := positiveSpectralProjector_le_one H hH
  { effects := fun b => if b then P else 1 - P
    pos := by
      intro b
      by_cases hb : b
      · simp [hb, hPpos]
      · have hcomp : (1 - P).PosSemidef := by
          rwa [← Matrix.le_iff]
        simp [hb, hcomp]
    sum_eq_one := by
      rw [Fintype.sum_bool]
      simp }

/-- The Helstrom test attains the equal-prior trace-distance formula. -/
theorem helstromTest_equalPriorError_eq (rho sigma : State a) :
    ((rho.helstromTest sigma).equalPriorError rho sigma : ℝ) =
      (1 / 2 : ℝ) * (1 - rho.normalizedTraceDistance sigma) := by
  let H : CMatrix a := rho.matrix - sigma.matrix
  let hH : H.IsHermitian := rho.pos.isHermitian.sub sigma.pos.isHermitian
  rw [BinaryHypothesisTest.equalPriorError_eq_half_one_sub_score]
  have hscore := positiveSpectralProjector_score_eq_posPart_trace H hH
  have hdist := normalizedTraceDistance_eq_posPart_trace rho sigma
  change (1 / 2 : ℝ) *
      (1 - (((H * positiveSpectralProjector H hH).trace).re)) =
    (1 / 2 : ℝ) * (1 - rho.normalizedTraceDistance sigma)
  rw [hscore, hdist]

/-- Helstrom optimality in the repository normalized trace-distance convention. -/
theorem helstrom_equalPriorError_optimal (rho sigma : State a) :
    (∃ T : BinaryHypothesisTest a,
      (T.equalPriorError rho sigma : ℝ) =
        (1 / 2 : ℝ) * (1 - rho.normalizedTraceDistance sigma)) ∧
    ∀ T : BinaryHypothesisTest a,
      (1 / 2 : ℝ) * (1 - rho.normalizedTraceDistance sigma) ≤
        (T.equalPriorError rho sigma : ℝ) := by
  constructor
  · exact ⟨rho.helstromTest sigma, State.helstromTest_equalPriorError_eq rho sigma⟩
  · intro T
    exact BinaryHypothesisTest.helstrom_equalPriorError_lower_bound T rho sigma

end State

end

end QIT
