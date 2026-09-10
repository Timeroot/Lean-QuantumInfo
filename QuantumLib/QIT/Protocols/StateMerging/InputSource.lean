/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Protocols.StateMerging.Converse
public import QuantumLib.QIT.OneShot.SmoothEndpoint.SourceDiscard

/-!
# The input source state for the smooth-min-entropy state-merging converse

This module identifies the `K_A A^n | R^n` marginal of a physical
state-merging input.  The identification is the algebraic input to the
one-shot converse of Berta: the input ebit contributes a maximally mixed
`K_A` factor, and discarding that factor leaves precisely the IID `A^n R^n`
source state.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y z p q

noncomputable section

/-- A double sum whose summand factors as `f a * g k` splits into a product of
sums. -/
private theorem sum_sum_mul_eq_mul_sum
    {A K : Type*} [Fintype A] [Fintype K]
    (f : A → ℂ) (g : K → ℂ) :
    (Finset.univ.sum fun a => Finset.univ.sum fun k => f a * g k) =
      (Finset.univ.sum g) * Finset.univ.sum f := by
  rw [← Fintype.sum_mul_sum, mul_comm]

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable {psi : Ket ((a × b) × r)} {n : ℕ}
variable {kA : Type x} {kB : Type y} {lA : Type z} {lB : Type p}
variable {outcome : Type q}
variable [Fintype kA] [DecidableEq kA] [Nonempty kA]
variable [Fintype kB] [DecidableEq kB]
variable [Fintype lA] [DecidableEq lA] [Nonempty lA]
variable [Fintype lB] [DecidableEq lB]
variable [Fintype outcome] [DecidableEq outcome] [Nonempty outcome]

namespace StateMergingBlockProtocol

variable (C : StateMergingBlockProtocol psi n kA kB lA lB outcome)

/-- The physical converse input marginal on `K_A A^n | R^n`, with the input
ebit register placed first so that `SubnormalizedState.sourceDiscard` removes
exactly `K_A`. -/
def converseInputARSource :
    SubnormalizedState
      ((kA × TensorPower a n) × TensorPower r n) :=
  (C.converseInputKet.state.traceRight.reindex
      (Equiv.prodCongr
        (Equiv.prodComm (TensorPower a n) kA)
        (Equiv.refl (TensorPower r n)))).toSubnormalized

/-- The input source reordering is exactly the source-register reference
isometry induced by swapping `A^n` and `K_A`. -/
theorem converseInputARSource_eq_sourceIsometryApply :
    C.converseInputARSource =
      C.converseInputKet.state.traceRight.toSubnormalized.sourceIsometryApply
        (ReferenceIsometry.ofEquiv
          (Equiv.prodComm (TensorPower a n) kA)) := by
  apply SubnormalizedState.ext
  ext i j
  simp [converseInputARSource, SubnormalizedState.sourceIsometryApply_matrix,
    ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
    ReferenceIsometry.ofEquiv, Matrix.mul_apply]
  rw [Finset.sum_eq_single j.1.swap]
  · rw [Finset.sum_eq_single i.1.swap]
    · simp [Prod.map]
    · intro x _ hx
      have hne : i.1 ≠ x.swap := by
        intro hix
        apply hx
        simpa using (congrArg Prod.swap hix).symm
      simp [hne]
    · simp
  · intro x _ hx
    have hne : j.1 ≠ x.swap := by
      intro hjx
      apply hx
      simpa using (congrArg Prod.swap hjx).symm
    simp [hne]
  · simp

/-- The input `K_A A^n R^n` marginal is the grouped product of the maximally
mixed Alice half of the input ebit and the IID source `A^n R^n` marginal. -/
theorem converseInputARSource_eq_groupedProduct :
    C.converseInputARSource =
      (((Ket.maximallyEntangled C.inputEbitPairing).state.traceRight.prod
          (stateMergingBlockSource psi n).state.marginalAC).reindex
        (Equiv.prodAssoc kA (TensorPower a n) (TensorPower r n)).symm).toSubnormalized := by
  apply SubnormalizedState.ext
  ext i j
  simp [converseInputARSource, converseInputKet, initialKet,
    prodABCToACBEquiv, stateMergingInputEquiv,
    Ket.reindex_state, Ket.prod_state,
    MState.marginalAC, Matrix.traceRight,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  exact sum_sum_mul_eq_mul_sum
    (fun x =>
      (stateMergingBlockSource psi n).vec ((i.1.2, x), i.2) *
        star ((stateMergingBlockSource psi n).vec ((j.1.2, x), j.2)))
    (fun x =>
      (Ket.maximallyEntangled C.inputEbitPairing).vec (i.1.1, x) *
        star ((Ket.maximallyEntangled C.inputEbitPairing).vec (j.1.1, x)))

/-- Discarding the input-ebit source register leaves exactly the IID `A^n R^n`
marginal used in Berta's one-shot converse. -/
theorem converseInputARSource_sourceDiscard :
    C.converseInputARSource.sourceDiscard =
      (stateMergingBlockSource psi n).state.marginalAC.toSubnormalized := by
  rw [C.converseInputARSource_eq_groupedProduct]
  apply SubnormalizedState.ext
  ext i j
  have htrace :
      (Finset.univ.sum fun x : kA =>
        Matrix.traceRight
          (rankOneMatrix (Ket.maximallyEntangled C.inputEbitPairing).vec) x x) = 1 := by
    simpa [Matrix.trace] using
      (Ket.maximallyEntangled C.inputEbitPairing).state.traceRight.tr'
  simp [SubnormalizedState.sourceDiscard_matrix, MState.toSubnormalized_matrix,
    Matrix.traceLeft,
    Matrix.kroneckerMap_apply]
  rw [← Finset.sum_mul, htrace, one_mul]

/-- Tensor-power form of `converseInputARSource_sourceDiscard`. -/
theorem converseInputARSource_sourceDiscard_eq_tensorPower :
    C.converseInputARSource.sourceDiscard =
      (psi.state.marginalAC.tensorPowerBipartite n).toSubnormalized := by
  rw [C.converseInputARSource_sourceDiscard,
    stateMergingBlockSource_marginalAC_eq_tensorPower]

@[simp]
theorem converseInputARSource_trace_re :
    C.converseInputARSource.matrix.trace.re = 1 := by
  change
    ((C.converseInputKet.state.traceRight.reindex
      (Equiv.prodCongr
        (Equiv.prodComm (TensorPower a n) kA)
        (Equiv.refl (TensorPower r n)))).toSubnormalized.matrix.trace).re = 1
  rw [MState.toSubnormalized_trace]
  norm_num

theorem converseInputARSource_trace_pos :
    0 < C.converseInputARSource.matrix.trace.re := by
  simp

/-- Berta's input-ebit chain rule, specialized to the physical state-merging
input and the IID `A^n | R^n` source obtained after discarding `K_A`. -/
theorem converseInputARSource_smoothConditionalMinEntropyRaw_le_log2_card_add_tensorPower
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon < 1) :
    C.converseInputARSource.smoothConditionalMinEntropyRaw epsilon ≤
      log2 (Fintype.card kA : ℝ) +
        SubnormalizedState.smoothConditionalMinEntropyRaw
          (psi.state.marginalAC.tensorPowerBipartite n).toSubnormalized epsilon := by
  let : Nonempty a := ⟨(Classical.choice psi.state.nonempty).1.1⟩
  let : Nonempty r := ⟨(Classical.choice psi.state.nonempty).2⟩
  have hepsilonTrace :
      epsilon < Real.sqrt C.converseInputARSource.matrix.trace.re := by
    rw [C.converseInputARSource_trace_re, Real.sqrt_one]
    exact hepsilon1
  have hchain :=
    C.converseInputARSource.smoothConditionalMinEntropyRaw_le_log2_card_add_sourceDiscard
      (k := kA) (a := TensorPower a n) (b := TensorPower r n)
      hepsilon0 hepsilonTrace
  rwa [C.converseInputARSource_sourceDiscard_eq_tensorPower] at hchain

/-- Canonical finite-domain form of the state-merging input-ebit chain rule. -/
theorem converseInputARSource_smoothConditionalMinEntropy_le_log2_card_add_tensorPower
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon < 1) :
    C.converseInputARSource.smoothConditionalMinEntropy epsilon hepsilon0
        (by rw [C.converseInputARSource_trace_re, Real.sqrt_one]; exact hepsilon1) ≤
      log2 (Fintype.card kA : ℝ) +
        SubnormalizedState.smoothConditionalMinEntropy
          (psi.state.marginalAC.tensorPowerBipartite n).toSubnormalized epsilon hepsilon0
            (by
              rw [MState.toSubnormalized_trace]
              simpa using hepsilon1) := by
  simpa only [SubnormalizedState.smoothConditionalMinEntropy_eq_raw] using
    C.converseInputARSource_smoothConditionalMinEntropyRaw_le_log2_card_add_tensorPower
      hepsilon0 hepsilon1

end StateMergingBlockProtocol

end

end QIT
