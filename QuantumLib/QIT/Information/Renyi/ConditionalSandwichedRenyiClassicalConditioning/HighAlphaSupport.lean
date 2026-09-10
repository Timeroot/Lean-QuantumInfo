/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

import Mathlib.Algebra.Order.CompleteField
public import QuantumLib.QIT.Information.Renyi.ConditionalRenyiClassical
public import QuantumLib.QIT.Information.Renyi.SandwichedRenyiOptimizedUSC
public import QuantumLib.QIT.Information.Renyi.ConditionalSandwichedRenyiDuality
public import QuantumLib.QIT.Information.Renyi.ConditionalSandwichedRenyiAdditivity
public import QuantumLib.QIT.Measurements.Projective
public import QuantumLib.QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.BlockAlgebra
public import QuantumLib.QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.LowAlphaQDecomposition

/-!
# High-alpha support route

The `alpha > 1` source formula for the downward sandwiched conditional Renyi
entropy under classical conditioning, obtained from the low-alpha decomposition
on the support of the reference.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Pointwise
open Matrix

noncomputable section
universe u v w
variable {A : Type u} {B : Type v} {Y : Type w}
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable [Fintype Y] [DecidableEq Y]

open QIT

namespace MState

/-! ### High-alpha support branch

For `α > 1`, the reference is singular in general, so the source convention
first asks for support.  A cq state is supported by the identity tensored with
its right marginal; this closes the EReal-to-finite high-alpha branch without
introducing a zero block into a negative matrix power. -/

theorem conditionalSandwichedRenyiDown_classicalConditioning_source_formula_of_one_lt
    (E : MEnsemble (A × B) Y) (α : ℝ) (hα : 1 / 2 ≤ α)
    (hα_ne_one : α ≠ 1) (hα_gt_one : 1 < α) :
    conditionalSandwichedRenyiDownE E α hα hα_ne_one =
      -(sandwichedRenyiPSDReferenceHighAlphaFinite
        (MState.cqConditioningState E)
        (identityTensorStateMatrix (a := A)
          (MState.cqConditioningState E).traceLeft)
        (identityTensorStateMatrix_posSemidef
          (a := A) (MState.cqConditioningState E).traceLeft) α : EReal) := by
  have hSupport :
      Matrix.Supports (MState.cqConditioningState E).m
        (identityTensorStateMatrix (a := A)
          (MState.cqConditioningState E).traceLeft) := by
    simpa [identityTensorStateMatrix] using
      (matrix_supports_identityTensor_traceLeft
        (MState.cqConditioningState E))
  unfold conditionalSandwichedRenyiDownE
  rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ hα_gt_one,
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      _ _ _ hSupport]

end MState
