/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Nonlocality.YangNavascues.LocalIsometry

/-!
# Rank-one coherence bridge for Yang-Navascues density calculations

The density-form Yang-Navascues conditions record squared coefficient ratios.
The CGS Fourier density calculation also needs off-diagonal coherence terms.
This module makes that extra source-level vector phase alignment explicit,
instead of deriving it from density information alone.

Source: ColadangeloGohScarani2016SelfTesting, `all_pure_v2.tex` lines
168-171 and 735-738.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

namespace QIT

universe u v w

noncomputable section

namespace YangNavascues

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

namespace YNData

variable (data : YNData ι HA HB)

/-- Rank-one cross/coherence matrix `|φ⟩⟨χ|`. -/
def rankOneCoherence {α : Type*} (φ χ : α → ℂ) : CMatrix α :=
  Matrix.vecMulVec φ (fun x => star (χ x))

@[simp]
theorem rankOneCoherence_apply {α : Type*} (φ χ : α → ℂ) (i j : α) :
    rankOneCoherence φ χ i j = φ i * star (χ j) := by
  simp [rankOneCoherence, Matrix.vecMulVec_apply]

/-- The CGS base branch vector `P_A^(0) ψ`. -/
def baseBranchVector (ψ : PureVector (HA × HB)) : HA × HB → ℂ :=
  (data.aliceProjectionOp data.target.base).mulVec ψ.amp

@[simp]
theorem baseBranchVector_eq (ψ : PureVector (HA × HB)) :
    data.baseBranchVector ψ =
      (data.aliceProjectionOp data.target.base).mulVec ψ.amp :=
  rfl

/-- The pure-state base projection density is the rank-one matrix of the base branch vector. -/
theorem baseProjectionMatrix_pure_eq_rankOneMatrix_baseBranchVector
    (ψ : PureVector (HA × HB)) :
    data.baseProjectionMatrix ψ.state =
      rankOneMatrix (data.baseBranchVector ψ) := by
  exact data.postMatrix_pure_eq_rankOneMatrix_mulVec ψ
    (data.aliceProjectionOp data.target.base)

end YNData

/--
Phase-aligned Yang-Navascues conditions for a pure state.

The first field is the existing density-level YN condition.  The second field
is the source vector equality with the unsquared coefficient ratio, needed for
off-diagonal target coherence terms in the CGS Fourier calculation.
-/
def YNPhaseAlignedConditions (data : YNData ι HA HB) (ψ : PureVector (HA × HB)) : Prop :=
  YNConditions data ψ.state ∧
    (∀ k : ι,
      (data.aliceProjectionOp k).mulVec ψ.amp =
        (data.bobProjectionOp k).mulVec ψ.amp) ∧
    (∀ k : ι,
      (data.transformedBobProjectionOp k).mulVec ψ.amp =
        (((data.target.coeff k / data.target.coeff data.target.base : ℝ) : ℂ)) •
          data.baseBranchVector ψ)

namespace YNPhaseAlignedConditions

variable {data : YNData ι HA HB} {ψ : PureVector (HA × HB)}

/-- Forget the explicit phase alignment to the density-level YN conditions. -/
theorem ynConditions (h : YNPhaseAlignedConditions data ψ) :
    YNConditions data ψ.state :=
  h.1

/-- The base branch vector has squared norm `c_0^2`. -/
theorem baseBranchVector_trace_rankOne
    (h : YNPhaseAlignedConditions data ψ) :
    (rankOneMatrix (data.baseBranchVector ψ)).trace =
      (((data.target.coeff data.target.base) ^ 2 : ℝ) : ℂ) := by
  rw [← data.baseProjectionMatrix_pure_eq_rankOneMatrix_baseBranchVector ψ]
  exact h.ynConditions.baseProjectionMatrix_trace_eq_coeff_base_sq

/-- Extract the source vector-level coefficient-ratio condition. -/
theorem phaseAligned (h : YNPhaseAlignedConditions data ψ) (k : ι) :
    (data.transformedBobProjectionOp k).mulVec ψ.amp =
      (((data.target.coeff k / data.target.coeff data.target.base : ℝ) : ℂ)) •
        data.baseBranchVector ψ :=
  h.2.2 k

/-- Extract the source vector-level projection-agreement condition. -/
theorem projectionAligned (h : YNPhaseAlignedConditions data ψ) (k : ι) :
    (data.aliceProjectionOp k).mulVec ψ.amp =
      (data.bobProjectionOp k).mulVec ψ.amp :=
  h.2.1 k

private theorem rankOneCoherence_smul_smul {α : Type*} (a b : ℝ) (φ χ : α → ℂ) :
    YNData.rankOneCoherence ((a : ℂ) • φ) ((b : ℂ) • χ) =
      ((a * b : ℝ) : ℂ) • YNData.rankOneCoherence φ χ := by
  ext i j
  simp [YNData.rankOneCoherence_apply, mul_assoc, mul_left_comm, mul_comm]

/--
The explicit phase alignment supplies the rank-one cross/coherence block used
by the CGS Fourier sum.
-/
theorem transformedBobProjection_rankOneCoherence
    (h : YNPhaseAlignedConditions data ψ) (i j : ι) :
    YNData.rankOneCoherence
        ((data.transformedBobProjectionOp i).mulVec ψ.amp)
        ((data.transformedBobProjectionOp j).mulVec ψ.amp) =
      (((data.target.coeff i / data.target.coeff data.target.base) *
          (data.target.coeff j / data.target.coeff data.target.base) : ℝ) : ℂ) •
        YNData.rankOneCoherence (data.baseBranchVector ψ) (data.baseBranchVector ψ) := by
  rw [h.phaseAligned i, h.phaseAligned j]
  exact rankOneCoherence_smul_smul
    (data.target.coeff i / data.target.coeff data.target.base)
    (data.target.coeff j / data.target.coeff data.target.base)
    (data.baseBranchVector ψ) (data.baseBranchVector ψ)

/--
The phase-aligned condition still consumes the existing Bob-local replacement
machinery through its density-level YN component.
-/
def toBobLocalOrthogonalization (h : YNPhaseAlignedConditions data ψ) :
    BobLocalOrthogonalization data ψ.state :=
  h.ynConditions.bobReducedSupportOrthogonalization

/--
The Bob-local orthogonalization carried by a phase-aligned YN witness has the
same vector-level action on the pure witness as Bob's original projection.

This wrapper is the branch-vector-facing form: later CGS calculations can
consume it without unfolding the reduced-support construction.
-/
theorem bobLocalOrthogonalization_mulVec_eq_bobProjectionOp
    (h : YNPhaseAlignedConditions data ψ) (k : ι) :
    (bobLocalOp HA (h.toBobLocalOrthogonalization.bobLocal) k).mulVec ψ.amp =
      (data.bobProjectionOp k).mulVec ψ.amp :=
  YNConditions.bobReducedSupportOrthogonalization_mulVec_eq_bobProjectionOp h.ynConditions k

end YNPhaseAlignedConditions

end YangNavascues

end

end QIT
