/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Channels.Diamond

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
theorem partialTraceA_kron_idChannel_of_tracePreserving
    (Phi : MatrixMap a b) (hPhi : IsTracePreserving Phi)
    (X : CMatrix (Prod a r)) :
    QIT.partialTraceA (a := b) (b := r)
        (MatrixMap.kron Phi (Channel.idChannel r).map X) =
      QIT.partialTraceA (a := a) (b := r) X := by
  ext i j
  have htrace := hPhi (fun x x' => X (x, i) (x', j))
  simpa [QIT.partialTraceA, Matrix.trace,
    MatrixMap.kron_idChannel_apply_slice] using htrace

/-- A trace-preserving map on the right tensor factor leaves the left marginal unchanged. -/
theorem partialTraceB_kron_idChannel_of_tracePreserving
    (Phi : MatrixMap a b) (hPhi : IsTracePreserving Phi)
    (X : CMatrix (Prod r a)) :
    QIT.partialTraceB (a := r) (b := b)
        (MatrixMap.kron (Channel.idChannel r).map Phi X) =
      QIT.partialTraceB (a := r) (b := a) X := by
  ext i j
  have htrace := hPhi (fun x x' => X (i, x) (j, x'))
  simpa [QIT.partialTraceB, Matrix.trace,
    MatrixMap.kron_idChannel_left_apply_slice] using htrace

end MatrixMap

/-- A finite quantum instrument. Each outcome branch is completely positive
and trace-nonincreasing, and the sum of all branches is a channel. -/
structure FiniteInstrument
    (input : Type u) (output : Type v) (outcome : Type w)
    [Fintype input] [DecidableEq input]
    [Fintype output] [DecidableEq output]
    [Fintype outcome] where
  branch : outcome → MatrixMap input output
  branchTraceNonincreasingCP :
    ∀ result, MatrixMap.TraceNonincreasingCP (branch result)
  total : Channel input output
  sum_branch_eq_total : (∑ result, branch result) = total.map

namespace FiniteInstrument

variable {input : Type u} {output : Type v} {outcome : Type w}
variable [Fintype input] [DecidableEq input]
variable [Fintype output] [DecidableEq output]
variable [Fintype outcome]

/-- The channel obtained by forgetting the classical outcome. -/
def totalChannel (M : FiniteInstrument input output outcome) : Channel input output :=
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
  aliceInstrument : FiniteInstrument aliceInput aliceOutput outcome
  bobChannel : outcome → Channel bobInput bobOutput
  realization : Channel (Prod aliceInput bobInput) (Prod aliceOutput bobOutput)
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
    Channel (Prod aliceInput bobInput) (Prod aliceOutput bobOutput) :=
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
