/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Protocols.LOCC.PureEntanglement
public import QuantumLib.QIT.States.Geometry.FuchsVdG
public import QuantumLib.QIT.States.Geometry.PureTargetFidelity
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Averaging trace distance over the branches of a one-way LOCC protocol

The Horodecki--Oppenheim--Winter converse bounds the error of a state merging protocol branch by
branch and then averages, and this module supplies what that averaging needs: monotonicity of the
trace distance under discarding a register, Jensen's inequality for the concave `x ↦ √(1 - x)`
against a finite probability vector, and the fact that squared fidelity with a *pure* target is
affine over the positive-probability branches of a `OneWayLOCC`, so the branch average of the
squared fidelities is the squared fidelity of the realized output.

Together they give `sum_jointPositiveBranchProbability_mul_traceNormDistance_le`: the branch
average of the trace distances to a pure target is at most `2 √(1 - F²)` for the squared fidelity
`F²` of the realized channel output.  This is Fuchs--van de Graaf applied once to the average
rather than once per branch, which is what keeps the converse from paying a branch-count factor.
Tracing out Alice afterwards leaves the bound intact.
-/

@[expose] public section

noncomputable section
universe u v
open scoped ComplexOrder MatrixOrder NNReal

open QIT

namespace MState

/-- Discarding the first register cannot increase normalized trace distance. -/
theorem normalizedTraceDistance_traceLeft_le
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rho sigma : MState (a × b)) :
    rho.traceLeft.normalizedTraceDistance sigma.traceLeft ≤
      rho.normalizedTraceDistance sigma := by
  let D : CMatrix (a × b) := rho.m - sigma.m
  calc
    rho.traceLeft.normalizedTraceDistance sigma.traceLeft =
        (1 / 2 : ℝ) * traceNorm (Matrix.traceLeft D) := by
          simp [MState.normalizedTraceDistance, QIT.normalizedTraceDistance,
            QIT.traceNormDistance, D, Matrix.traceLeft_sub]
    _ ≤ (1 / 2 : ℝ) * traceNorm D := by
          exact mul_le_mul_of_nonneg_left (traceNorm_traceLeft_le_matrix D) (by norm_num)
    _ = rho.normalizedTraceDistance sigma := by
          simp [MState.normalizedTraceDistance, QIT.normalizedTraceDistance,
            QIT.traceNormDistance, D]

/-- Discarding the first register cannot increase unnormalized trace distance. -/
theorem traceNormDistance_traceLeft_le
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rho sigma : MState (a × b)) :
    rho.traceLeft.traceNormDistance sigma.traceLeft ≤ rho.traceNormDistance sigma := by
  have h := normalizedTraceDistance_traceLeft_le rho sigma
  simpa [MState.normalizedTraceDistance, QIT.normalizedTraceDistance] using
    mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 2 by norm_num)

end MState

namespace QIT

namespace Finset

/-- Jensen's square-root bound for the finite branch average in the HOW converse. -/
theorem sum_mul_sqrt_one_sub_squaredFidelity_le_sqrt_of_average
    {i : Type v} [Fintype i] {a : Type u} [Fintype a] [DecidableEq a]
    (q : i → NNReal) (phi : i → Ket a) (target : Ket a)
    (hsum : Finset.sum Finset.univ q = 1) :
    Finset.sum Finset.univ (fun j => (q j : ℝ) *
      Real.sqrt (1 - (phi j).state.squaredFidelity target.state)) ≤
      Real.sqrt (1 - Finset.sum Finset.univ (fun j => (q j : ℝ) *
        (phi j).state.squaredFidelity target.state)) := by
  classical
  let deficit : i → ℝ := fun j => 1 - (phi j).state.squaredFidelity target.state
  have hdeficit : ∀ j, deficit j ∈ Set.Ici (0 : ℝ) := by
    intro j
    exact sub_nonneg.mpr (MState.squaredFidelity_le_one _ _)
  have hsum' : Finset.sum Finset.univ (fun j => (q j : ℝ)) = 1 := by
    simpa only [NNReal.coe_sum, NNReal.coe_one] using
      congrArg (fun x : NNReal => (x : ℝ)) hsum
  have hjensen := Real.strictConcaveOn_sqrt.concaveOn.le_map_sum
    (t := Finset.univ) (w := fun j => (q j : ℝ)) (p := deficit)
    (fun j _ => NNReal.coe_nonneg (q j)) hsum'
    (fun j _ => hdeficit j)
  have havg : Finset.sum Finset.univ (fun j => (q j : ℝ) * deficit j) =
      1 - Finset.sum Finset.univ
        (fun j => (q j : ℝ) * (phi j).state.squaredFidelity target.state) := by
    calc
      Finset.sum Finset.univ (fun j => (q j : ℝ) * deficit j) =
          Finset.sum Finset.univ (fun j => (q j : ℝ) -
            (q j : ℝ) * (phi j).state.squaredFidelity target.state) := by
              apply Finset.sum_congr rfl
              intro j _
              dsimp [deficit]
              ring
      _ = Finset.sum Finset.univ (fun j => (q j : ℝ)) -
          Finset.sum Finset.univ
            (fun j => (q j : ℝ) * (phi j).state.squaredFidelity target.state) :=
            by rw [Finset.sum_sub_distrib]
      _ = 1 - Finset.sum Finset.univ
          (fun j => (q j : ℝ) * (phi j).state.squaredFidelity target.state) := by
            rw [hsum']
  have hjensen' :
      Finset.sum Finset.univ (fun j => (q j : ℝ) * Real.sqrt (deficit j)) ≤
        Real.sqrt (Finset.sum Finset.univ (fun j => (q j : ℝ) * deficit j)) := by
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
    (L : OneWayLOCC A A' B B' X) (psi : Ket (A × B))
    (target : Ket (A' × B')) :
    (Finset.univ.sum fun j : L.jointPositiveSupport psi =>
      (L.jointPositiveBranchProbability psi j : ℝ) *
        (L.finalNormalizedBranch psi j).state.squaredFidelity target.state) =
      MState.squaredFidelity (L.toChannel psi.state) target.state := by
  apply MState.squaredFidelity_sum_smul_pure_right
  have h := L.sum_jointPositiveBranchProbability_smul_finalNormalizedBranch_state_matrix psi
  rw [CPTPOp.mat_coe_eq_apply_mat]
  show (Finset.univ.sum fun j : L.jointPositiveSupport psi =>
      ((L.jointPositiveBranchProbability psi j : ℂ) •
        (L.finalNormalizedBranch psi j).state.m)) = L.toChannel.map psi.state.m
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext p q
  simp [NNReal.smul_def, Complex.real_smul]

/-- The HOW branch average of full trace distances is controlled by the
fidelity error of the realized one-way LOCC output. -/
theorem sum_jointPositiveBranchProbability_mul_traceNormDistance_le
    (L : OneWayLOCC A A' B B' X) (psi : Ket (A × B))
    (target : Ket (A' × B')) :
    (Finset.univ.sum fun j : L.jointPositiveSupport psi =>
      (L.jointPositiveBranchProbability psi j : ℝ) *
        (L.finalNormalizedBranch psi j).state.traceNormDistance target.state) ≤
      2 * Real.sqrt
        (1 - MState.squaredFidelity (L.toChannel psi.state) target.state) := by
  have hsum := L.sum_jointPositiveBranchProbability_eq_one psi
  have hfdg (j : L.jointPositiveSupport psi) :
      (L.finalNormalizedBranch psi j).state.traceNormDistance target.state ≤
        2 * Real.sqrt
          (1 - (L.finalNormalizedBranch psi j).state.squaredFidelity target.state) := by
    have h := MState.fuchs_van_de_graaf_upper
      (L.finalNormalizedBranch psi j).state target.state
    simpa [MState.normalizedTraceDistance, QIT.normalizedTraceDistance] using
      mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 2 by norm_num)
  calc
    (Finset.univ.sum fun j : L.jointPositiveSupport psi =>
        (L.jointPositiveBranchProbability psi j : ℝ) *
          (L.finalNormalizedBranch psi j).state.traceNormDistance target.state) ≤
        Finset.univ.sum (fun j : L.jointPositiveSupport psi =>
          (L.jointPositiveBranchProbability psi j : ℝ) *
            (2 * Real.sqrt
              (1 - (L.finalNormalizedBranch psi j).state.squaredFidelity target.state))) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hfdg j) (NNReal.coe_nonneg _)
    _ = 2 * Finset.univ.sum (fun j : L.jointPositiveSupport psi =>
          (L.jointPositiveBranchProbability psi j : ℝ) *
            Real.sqrt
              (1 - (L.finalNormalizedBranch psi j).state.squaredFidelity target.state)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ 2 * Real.sqrt
        (1 - Finset.univ.sum (fun j : L.jointPositiveSupport psi =>
          (L.jointPositiveBranchProbability psi j : ℝ) *
            (L.finalNormalizedBranch psi j).state.squaredFidelity target.state)) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_mul_sqrt_one_sub_squaredFidelity_le_sqrt_of_average
          (fun j => L.jointPositiveBranchProbability psi j)
          (fun j => L.finalNormalizedBranch psi j) target hsum)
        (by norm_num)
    _ = 2 * Real.sqrt
        (1 - MState.squaredFidelity (L.toChannel psi.state) target.state) := by
      rw [L.sum_jointPositiveBranchProbability_mul_squaredFidelity_eq_output psi target]

/-- The HOW branch average remains bounded after tracing out Alice. -/
theorem sum_jointPositiveBranchProbability_mul_traceLeft_traceNormDistance_le
    (L : OneWayLOCC A A' B B' X) (psi : Ket (A × B))
    (target : Ket (A' × B')) :
    (Finset.univ.sum fun j : L.jointPositiveSupport psi =>
      (L.jointPositiveBranchProbability psi j : ℝ) *
        (L.finalNormalizedBranch psi j).state.traceLeft.traceNormDistance
          target.state.traceLeft) ≤
      2 * Real.sqrt
        (1 - MState.squaredFidelity (L.toChannel psi.state) target.state) := by
  calc
    (Finset.univ.sum fun j : L.jointPositiveSupport psi =>
        (L.jointPositiveBranchProbability psi j : ℝ) *
          (L.finalNormalizedBranch psi j).state.traceLeft.traceNormDistance
            target.state.traceLeft) ≤
        Finset.univ.sum (fun j : L.jointPositiveSupport psi =>
          (L.jointPositiveBranchProbability psi j : ℝ) *
            (L.finalNormalizedBranch psi j).state.traceNormDistance target.state) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (MState.traceNormDistance_traceLeft_le _ _) (NNReal.coe_nonneg _)
    _ ≤ 2 * Real.sqrt
        (1 - MState.squaredFidelity (L.toChannel psi.state) target.state) :=
      L.sum_jointPositiveBranchProbability_mul_traceNormDistance_le psi target

end OneWayLOCC

end QIT
