/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

import Mathlib.Algebra.Order.CompleteField
public import QIT.Information.Renyi.ConditionalRenyiClassical
public import QIT.Information.Renyi.SandwichedRenyiOptimizedUSC
public import QIT.Information.Renyi.ConditionalSandwichedRenyiDuality
public import QIT.Information.Renyi.ConditionalSandwichedRenyiAdditivity
public import QIT.Measurements.Projective
public import QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.BlockAlgebra
public import QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.LowAlphaQDecomposition

/-!
# high-alpha support route

Responsibility layer of the sandwiched conditional Renyi classical-conditioning
source route.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Pointwise
open Matrix

namespace QIT

universe u v w

noncomputable section

variable {A : Type u} {B : Type v} {Y : Type w}
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable [Fintype Y] [DecidableEq Y]

namespace State

/-! ### High-alpha support branch

For `α > 1`, the reference is singular in general, so the source convention
first asks for support.  A cq state is supported by the identity tensored with
its right marginal; this closes the EReal-to-finite high-alpha branch without
introducing a zero block into a negative matrix power. -/

theorem conditionalSandwichedRenyiDown_classicalConditioning_source_formula_of_one_lt
    (E : Ensemble Y (A × B)) (α : ℝ) (hα : 1 / 2 ≤ α)
    (hα_ne_one : α ≠ 1) (hα_gt_one : 1 < α) :
    conditionalSandwichedRenyiDownE E α hα hα_ne_one =
      -(sandwichedRenyiPSDReferenceHighAlphaFinite
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A)
          (State.cqConditioningState E).marginalB)
        (identityTensorStateMatrix_posSemidef_of_state
          (a := A) (State.cqConditioningState E).marginalB) α : EReal) := by
  have hSupport :
      Matrix.Supports (State.cqConditioningState E).matrix
        (identityTensorStateMatrix (a := A)
          (State.cqConditioningState E).marginalB) := by
    simpa [identityTensorStateMatrix] using
      (matrix_supports_identityTensor_marginalB
        (State.cqConditioningState E))
  unfold conditionalSandwichedRenyiDownE
  rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ hα_gt_one,
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      _ _ _ hSupport]


end State

end

end QIT
