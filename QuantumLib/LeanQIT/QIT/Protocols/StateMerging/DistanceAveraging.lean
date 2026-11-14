/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Protocols.LOCC.PureEntanglement
public import QIT.States.Geometry.FuchsVdG
public import QIT.States.Geometry.PureTargetFidelity
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

@[expose] public section

namespace QIT

universe u v

noncomputable section

open scoped ComplexOrder MatrixOrder NNReal

namespace State

/-- Discarding the first register cannot increase normalized trace distance. -/
theorem normalizedTraceDistance_marginalB_le
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rho sigma : State (Prod a b)) :
    rho.marginalB.normalizedTraceDistance sigma.marginalB <=
      rho.normalizedTraceDistance sigma := by
  let D : CMatrix (Prod a b) := rho.matrix - sigma.matrix
  calc
    rho.marginalB.normalizedTraceDistance sigma.marginalB =
        (1 / 2 : Real) * traceNorm (partialTraceA (a := a) (b := b) D) := by
          simp [State.normalizedTraceDistance, QIT.normalizedTraceDistance,
            QIT.traceNormDistance, State.marginalB_matrix, D, partialTraceA_sub]
    _ <= (1 / 2 : Real) * traceNorm D := by
          exact mul_le_mul_of_nonneg_left (traceNorm_partialTraceA_le D) (by norm_num)
    _ = rho.normalizedTraceDistance sigma := by
          simp [State.normalizedTraceDistance, QIT.normalizedTraceDistance,
            QIT.traceNormDistance, D]

/-- Discarding the first register cannot increase unnormalized trace distance. -/
theorem traceNormDistance_marginalB_le
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rho sigma : State (Prod a b)) :
    rho.marginalB.traceNormDistance sigma.marginalB <= rho.traceNormDistance sigma := by
  have h := normalizedTraceDistance_marginalB_le rho sigma
  simpa [State.normalizedTraceDistance, QIT.normalizedTraceDistance] using
    mul_le_mul_of_nonneg_left h (show (0 : Real) <= 2 by norm_num)

end State

namespace Finset

/-- Jensen's square-root bound for the finite branch average in the HOW converse. -/
theorem sum_mul_sqrt_one_sub_squaredFidelity_le_sqrt_of_average
    {i : Type v} [Fintype i] {a : Type u} [Fintype a] [DecidableEq a]
    (q : i -> NNReal) (phi : i -> PureVector a) (target : PureVector a)
    (hsum : Finset.sum Finset.univ q = 1) :
    Finset.sum Finset.univ (fun j => (q j : Real) *
      Real.sqrt (1 - (phi j).state.squaredFidelity target.state)) <=
      Real.sqrt (1 - Finset.sum Finset.univ (fun j => (q j : Real) *
        (phi j).state.squaredFidelity target.state)) := by
  classical
  let deficit : i -> Real := fun j => 1 - (phi j).state.squaredFidelity target.state
  have hdeficit : forall j, deficit j ∈ Set.Ici (0 : Real) := by
    intro j
    exact sub_nonneg.mpr (State.squaredFidelity_le_one _ _)
  have hsum' : Finset.sum Finset.univ (fun j => (q j : Real)) = 1 := by
    simpa only [NNReal.coe_sum, NNReal.coe_one] using
      congrArg (fun x : NNReal => (x : Real)) hsum
  have hjensen := Real.strictConcaveOn_sqrt.concaveOn.le_map_sum
    (t := Finset.univ) (w := fun j => (q j : Real)) (p := deficit)
    (fun j _ => NNReal.coe_nonneg (q j)) hsum'
    (fun j _ => hdeficit j)
  have havg : Finset.sum Finset.univ (fun j => (q j : Real) * deficit j) =
      1 - Finset.sum Finset.univ
        (fun j => (q j : Real) * (phi j).state.squaredFidelity target.state) := by
    calc
      Finset.sum Finset.univ (fun j => (q j : Real) * deficit j) =
          Finset.sum Finset.univ (fun j => (q j : Real) -
            (q j : Real) * (phi j).state.squaredFidelity target.state) := by
              apply Finset.sum_congr rfl
              intro j _
              dsimp [deficit]
              ring
      _ = Finset.sum Finset.univ (fun j => (q j : Real)) -
          Finset.sum Finset.univ
            (fun j => (q j : Real) * (phi j).state.squaredFidelity target.state) :=
            by rw [Finset.sum_sub_distrib]
      _ = 1 - Finset.sum Finset.univ
          (fun j => (q j : Real) * (phi j).state.squaredFidelity target.state) := by
            rw [hsum']
  have hjensen' :
      Finset.sum Finset.univ (fun j => (q j : Real) * Real.sqrt (deficit j)) <=
        Real.sqrt (Finset.sum Finset.univ (fun j => (q j : Real) * deficit j)) := by
    simpa only [Function.comp_apply, smul_eq_mul] using hjensen
  rw [havg] at hjensen'
  simpa only [deficit] using hjensen'

end Finset

namespace OneWayLOCC

variable {A : Type u} {A' : Type v} {B : Type*} {B' : Type*} {X : Type*}
variable [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
variable [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
variable [Fintype X]

/-- Squared fidelity with a pure target is affine over the physical positive
branches of a finite one-way LOCC protocol. -/
theorem sum_jointPositiveBranchProbability_mul_squaredFidelity_eq_output
    (L : OneWayLOCC A A' B B' X) (psi : PureVector (Prod A B))
    (target : PureVector (Prod A' B')) :
    (Finset.univ.sum fun j : L.jointPositiveSupport psi =>
      (L.jointPositiveBranchProbability psi j : Real) *
        (L.finalNormalizedBranch psi j).state.squaredFidelity target.state) =
      (L.toChannel.applyState psi.state).squaredFidelity target.state := by
  apply State.squaredFidelity_sum_smul_pure_right
  simpa using L.sum_jointPositiveBranchProbability_smul_finalNormalizedBranch_state_matrix psi

/-- The HOW branch average of full trace distances is controlled by the
fidelity error of the realized one-way LOCC output. -/
theorem sum_jointPositiveBranchProbability_mul_traceNormDistance_le
    (L : OneWayLOCC A A' B B' X) (psi : PureVector (Prod A B))
    (target : PureVector (Prod A' B')) :
    (Finset.univ.sum fun j : L.jointPositiveSupport psi =>
      (L.jointPositiveBranchProbability psi j : Real) *
        (L.finalNormalizedBranch psi j).state.traceNormDistance target.state) <=
      2 * Real.sqrt
        (1 - (L.toChannel.applyState psi.state).squaredFidelity target.state) := by
  have hsum := L.sum_jointPositiveBranchProbability_eq_one psi
  have hfdg (j : L.jointPositiveSupport psi) :
      (L.finalNormalizedBranch psi j).state.traceNormDistance target.state <=
        2 * Real.sqrt
          (1 - (L.finalNormalizedBranch psi j).state.squaredFidelity target.state) := by
    have h := State.fuchs_van_de_graaf_upper
      (L.finalNormalizedBranch psi j).state target.state
    simpa [State.normalizedTraceDistance, QIT.normalizedTraceDistance] using
      mul_le_mul_of_nonneg_left h (show (0 : Real) <= 2 by norm_num)
  calc
    (Finset.univ.sum fun j : L.jointPositiveSupport psi =>
        (L.jointPositiveBranchProbability psi j : Real) *
          (L.finalNormalizedBranch psi j).state.traceNormDistance target.state) <=
        Finset.univ.sum (fun j : L.jointPositiveSupport psi =>
          (L.jointPositiveBranchProbability psi j : Real) *
            (2 * Real.sqrt
              (1 - (L.finalNormalizedBranch psi j).state.squaredFidelity target.state))) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hfdg j) (NNReal.coe_nonneg _)
    _ = 2 * Finset.univ.sum (fun j : L.jointPositiveSupport psi =>
          (L.jointPositiveBranchProbability psi j : Real) *
            Real.sqrt
              (1 - (L.finalNormalizedBranch psi j).state.squaredFidelity target.state)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ <= 2 * Real.sqrt
        (1 - Finset.univ.sum (fun j : L.jointPositiveSupport psi =>
          (L.jointPositiveBranchProbability psi j : Real) *
            (L.finalNormalizedBranch psi j).state.squaredFidelity target.state)) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_mul_sqrt_one_sub_squaredFidelity_le_sqrt_of_average
          (fun j => L.jointPositiveBranchProbability psi j)
          (fun j => L.finalNormalizedBranch psi j) target hsum)
        (by norm_num)
    _ = 2 * Real.sqrt
        (1 - (L.toChannel.applyState psi.state).squaredFidelity target.state) := by
      rw [L.sum_jointPositiveBranchProbability_mul_squaredFidelity_eq_output psi target]

/-- The HOW branch average remains bounded after tracing out Alice. -/
theorem sum_jointPositiveBranchProbability_mul_marginalB_traceNormDistance_le
    (L : OneWayLOCC A A' B B' X) (psi : PureVector (Prod A B))
    (target : PureVector (Prod A' B')) :
    (Finset.univ.sum fun j : L.jointPositiveSupport psi =>
      (L.jointPositiveBranchProbability psi j : Real) *
        (L.finalNormalizedBranch psi j).state.marginalB.traceNormDistance
          target.state.marginalB) <=
      2 * Real.sqrt
        (1 - (L.toChannel.applyState psi.state).squaredFidelity target.state) := by
  calc
    (Finset.univ.sum fun j : L.jointPositiveSupport psi =>
        (L.jointPositiveBranchProbability psi j : Real) *
          (L.finalNormalizedBranch psi j).state.marginalB.traceNormDistance
            target.state.marginalB) <=
        Finset.univ.sum (fun j : L.jointPositiveSupport psi =>
          (L.jointPositiveBranchProbability psi j : Real) *
            (L.finalNormalizedBranch psi j).state.traceNormDistance target.state) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (State.traceNormDistance_marginalB_le _ _) (NNReal.coe_nonneg _)
    _ <= 2 * Real.sqrt
        (1 - (L.toChannel.applyState psi.state).squaredFidelity target.state) :=
      L.sum_jointPositiveBranchProbability_mul_traceNormDistance_le psi target

end OneWayLOCC

end

end QIT
