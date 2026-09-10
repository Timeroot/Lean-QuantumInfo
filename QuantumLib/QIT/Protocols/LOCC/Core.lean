/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Channels.Diamond

/-!
# Finite one-way LOCC operations

This module contains the protocol-independent finite instrument and one-way
LOCC data used by state merging. A one-way LOCC realization is fixed by
Alice's finite instrument and Bob's outcome-conditioned channels; it is not a
freely supplied replacement channel.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y

noncomputable section

namespace MatrixMap

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

/-- A trace-preserving map on the left tensor factor leaves the right marginal unchanged. -/
theorem traceLeft_kron_idChannel_of_tracePreserving
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsTracePreserving Phi)
    (X : CMatrix (a × r)) :
    Matrix.traceLeft
        (MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map X) =
      Matrix.traceLeft X := by
  ext i j
  have htrace := hPhi (Matrix.of fun x x' => X (x, i) (x', j))
  simpa [-CPTPOp.id_map, Matrix.traceLeft, Matrix.trace, Matrix.of_apply,
    MatrixMap.kron_idChannel_apply_slice] using htrace

/-- A trace-preserving map on the right tensor factor leaves the left marginal unchanged. -/
theorem traceRight_kron_idChannel_of_tracePreserving
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsTracePreserving Phi)
    (X : CMatrix (r × a)) :
    Matrix.traceRight
        (MatrixMap.kron (CPTPOp.id (dIn := r)).map Phi X) =
      Matrix.traceRight X := by
  ext i j
  have htrace := hPhi (Matrix.of fun x x' => X (i, x) (j, x'))
  simpa [-CPTPOp.id_map, Matrix.traceRight, Matrix.trace, Matrix.of_apply,
    MatrixMap.kron_idChannel_left_apply_slice] using htrace

end MatrixMap

/-- A finite quantum instrument. Each outcome branch is completely positive
and trace-nonincreasing, and the sum of all branches is a channel. -/
structure FiniteInstrument
    (input : Type u) (output : Type v) (outcome : Type w)
    [Fintype input] [DecidableEq input]
    [Fintype output] [DecidableEq output]
    [Fintype outcome] where
  /-- The map applied on each outcome branch. -/
  branch : outcome → MatrixMap input output
  /-- Each branch is completely positive and trace-nonincreasing. -/
  branchTraceNonincreasingCP :
    ∀ result, MatrixMap.TraceNonincreasingCP (branch result)
  /-- The channel obtained by forgetting the outcome. -/
  total : CPTPMap input output
  /-- The branches sum to the total channel. -/
  sum_branch_eq_total : (∑ result, branch result) = total.map

namespace FiniteInstrument

variable {input : Type u} {output : Type v} {outcome : Type w}
variable [Fintype input] [DecidableEq input]
variable [Fintype output] [DecidableEq output]
variable [Fintype outcome]

/-- The channel obtained by forgetting the classical outcome. -/
def totalChannel (M : FiniteInstrument input output outcome) : CPTPMap input output :=
  M.total

theorem branch_completelyPositive
    (M : FiniteInstrument input output outcome) (result : outcome) :
    MatrixMap.IsCompletelyPositive (M.branch result) :=
  (M.branchTraceNonincreasingCP result).completelyPositive

end FiniteInstrument

/-- A finite one-way LOCC operation. Alice applies an instrument, sends its
classical result, and Bob applies the channel indexed by that result. -/
structure OneWayLOCC
    (aliceInput : Type u) (aliceOutput : Type v)
    (bobInput : Type w) (bobOutput : Type x) (outcome : Type y)
    [Fintype aliceInput] [DecidableEq aliceInput]
    [Fintype aliceOutput] [DecidableEq aliceOutput]
    [Fintype bobInput] [DecidableEq bobInput]
    [Fintype bobOutput] [DecidableEq bobOutput]
    [Fintype outcome] where
  /-- Alice's instrument, whose outcome she communicates to Bob. -/
  aliceInstrument : FiniteInstrument aliceInput aliceOutput outcome
  /-- Bob's channel, chosen according to Alice's outcome. -/
  bobChannel : outcome → CPTPMap bobInput bobOutput
  /-- The joint channel realizing the protocol. -/
  realization : CPTPMap (aliceInput × bobInput) (aliceOutput × bobOutput)
  /-- The joint channel is the outcome-averaged product of the two local maps. -/
  realization_map :
    realization.map =
      ∑ result,
        MatrixMap.kron (aliceInstrument.branch result) (bobChannel result).map

namespace OneWayLOCC

variable {aliceInput : Type u} {aliceOutput : Type v}
variable {bobInput : Type w} {bobOutput : Type x} {outcome : Type y}
variable [Fintype aliceInput] [DecidableEq aliceInput]
variable [Fintype aliceOutput] [DecidableEq aliceOutput]
variable [Fintype bobInput] [DecidableEq bobInput]
variable [Fintype bobOutput] [DecidableEq bobOutput]
variable [Fintype outcome]

/-- The CPTP map computed by the one-way LOCC realization. -/
def toChannel
    (L : OneWayLOCC aliceInput aliceOutput bobInput bobOutput outcome) :
    CPTPMap (aliceInput × bobInput) (aliceOutput × bobOutput) :=
  L.realization

theorem toChannel_map
    (L : OneWayLOCC aliceInput aliceOutput bobInput bobOutput outcome) :
    L.toChannel.map =
      ∑ result,
        MatrixMap.kron (L.aliceInstrument.branch result) (L.bobChannel result).map :=
  L.realization_map

end OneWayLOCC

end

end QIT
