/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Protocols.LOCC.Core

/-!
# Constructions for finite one-way LOCC operations

This module provides reusable composition operations on finite instruments and
constructs the physical channel of a finite one-way LOCC protocol directly
from Alice's instrument and Bob's outcome-conditioned channels.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y z

noncomputable section

namespace FiniteInstrument

variable {input : Type u} {output : Type v} {outcome : Type w}
variable [Fintype input] [DecidableEq input]
variable [Fintype output] [DecidableEq output]
variable [Fintype outcome]

/-- Precompose every branch of an instrument with the same input channel. -/
def precompChannel
    {newInput : Type x} [Fintype newInput] [DecidableEq newInput]
    (M : FiniteInstrument input output outcome)
    (pre : CPTPMap newInput input) :
    FiniteInstrument newInput output outcome where
  branch result := (M.branch result).comp pre.map
  branchTraceNonincreasingCP result := by
    refine
      { completelyPositive := MatrixMap.isCompletelyPositive_comp
          (M.branch result) pre.map
          (M.branchTraceNonincreasingCP result).completelyPositive
          pre.map_cp
        traceNonincreasing := ?_ }
    intro X hX
    calc
      ((M.branch result).comp pre.map X).trace.re ≤ (pre.map X).trace.re :=
        (M.branchTraceNonincreasingCP result).traceNonincreasing
          (pre.map X) (pre.mapsPositive X hX)
      _ = X.trace.re := congrArg Complex.re (pre.map_TP X)
  total := M.total ∘ₘ pre
  sum_branch_eq_total := by
    calc
      (∑ result, (M.branch result).comp pre.map) =
          (∑ result, M.branch result).comp pre.map := by
        apply LinearMap.ext
        intro X
        simp
      _ = (M.total ∘ₘ pre).map := by rw [CPTPOp.compose_map, M.sum_branch_eq_total]

@[simp]
theorem precompChannel_branch
    {newInput : Type x} [Fintype newInput] [DecidableEq newInput]
    (M : FiniteInstrument input output outcome)
    (pre : CPTPMap newInput input) (result : outcome) :
    (M.precompChannel pre).branch result = (M.branch result).comp pre.map :=
  rfl

theorem precompChannel_totalChannel
    {newInput : Type x} [Fintype newInput] [DecidableEq newInput]
    (M : FiniteInstrument input output outcome)
    (pre : CPTPMap newInput input) :
    (M.precompChannel pre).totalChannel = M.totalChannel ∘ₘ pre :=
  rfl

/-- Postcompose every branch of an instrument with the same output channel. -/
def postcompChannel
    {newOutput : Type x} [Fintype newOutput] [DecidableEq newOutput]
    (M : FiniteInstrument input output outcome)
    (post : CPTPMap output newOutput) :
    FiniteInstrument input newOutput outcome where
  branch result := post.map.comp (M.branch result)
  branchTraceNonincreasingCP result := by
    refine
      { completelyPositive := MatrixMap.isCompletelyPositive_comp
          post.map (M.branch result) post.map_cp
          (M.branchTraceNonincreasingCP result).completelyPositive
        traceNonincreasing := ?_ }
    intro X hX
    change (post.map (M.branch result X)).trace.re ≤ X.trace.re
    rw [post.map_TP]
    exact (M.branchTraceNonincreasingCP result).traceNonincreasing X hX
  total := post ∘ₘ M.total
  sum_branch_eq_total := by
    calc
      (∑ result, post.map.comp (M.branch result)) =
          post.map.comp (∑ result, M.branch result) := by
        apply LinearMap.ext
        intro X
        simp
      _ = (post ∘ₘ M.total).map := by rw [CPTPOp.compose_map, M.sum_branch_eq_total]

@[simp]
theorem postcompChannel_branch
    {newOutput : Type x} [Fintype newOutput] [DecidableEq newOutput]
    (M : FiniteInstrument input output outcome)
    (post : CPTPMap output newOutput) (result : outcome) :
    (M.postcompChannel post).branch result = post.map.comp (M.branch result) :=
  rfl

theorem postcompChannel_totalChannel
    {newOutput : Type x} [Fintype newOutput] [DecidableEq newOutput]
    (M : FiniteInstrument input output outcome)
    (post : CPTPMap output newOutput) :
    (M.postcompChannel post).totalChannel = post ∘ₘ M.totalChannel :=
  rfl

private theorem trace_kron_eq_trace_kron_id_of_right_tracePreserving
    {aliceInput : Type u} {aliceOutput : Type v}
    {bobInput : Type w} {bobOutput : Type x}
    [Fintype aliceInput] [DecidableEq aliceInput]
    [Fintype aliceOutput] [DecidableEq aliceOutput]
    [Fintype bobInput] [DecidableEq bobInput]
    [Fintype bobOutput] [DecidableEq bobOutput]
    (left : MatrixMap aliceInput aliceOutput)
    (right : MatrixMap bobInput bobOutput)
    (hRight : MatrixMap.IsTracePreserving right)
    (X : CMatrix (aliceInput × bobInput)) :
    (MatrixMap.kron left right X).trace =
      (MatrixMap.kron left (CPTPOp.id (dIn := bobInput)).map X).trace := by
  rw [MatrixMap.trace_map_eq_sum_single, MatrixMap.trace_map_eq_sum_single]
  refine Finset.sum_congr rfl fun inputIndex _ => ?_
  refine Finset.sum_congr rfl fun inputIndex' _ => ?_
  rcases inputIndex with ⟨i, j⟩
  rcases inputIndex' with ⟨i', j'⟩
  rw [MatrixMap.trace_kron_single, MatrixMap.trace_kron_single,
    hRight, (CPTPOp.id (dIn := bobInput)).map_TP]

/-- The matrix map physically implemented by Alice's instrument followed by
Bob's outcome-conditioned channels. -/
def oneWayLOCCMap
    {bobInput : Type x} {bobOutput : Type y}
    [Fintype bobInput] [DecidableEq bobInput]
    [Fintype bobOutput] [DecidableEq bobOutput]
    (M : FiniteInstrument input output outcome)
    (bobChannel : outcome → CPTPMap bobInput bobOutput) :
    MatrixMap (input × bobInput) (output × bobOutput) :=
  ∑ result, MatrixMap.kron (M.branch result) (bobChannel result).map

/-- The physical one-way LOCC map is completely positive. -/
theorem oneWayLOCCMap_completelyPositive
    {bobInput : Type x} {bobOutput : Type y}
    [Fintype bobInput] [DecidableEq bobInput]
    [Fintype bobOutput] [DecidableEq bobOutput]
    (M : FiniteInstrument input output outcome)
    (bobChannel : outcome → CPTPMap bobInput bobOutput) :
    MatrixMap.IsCompletelyPositive (M.oneWayLOCCMap bobChannel) := by
  rw [MatrixMap.isCompletelyPositive_iff_choi]
  have hchoi :
      MatrixMap.choi (M.oneWayLOCCMap bobChannel) =
        ∑ result, MatrixMap.choi
          (MatrixMap.kron (M.branch result) (bobChannel result).map) := by
    ext i j
    simp only [oneWayLOCCMap, MatrixMap.choi, LinearMap.coe_sum,
      Finset.sum_apply, Matrix.sum_apply]
  rw [hchoi]
  exact Matrix.posSemidef_sum Finset.univ fun result _ =>
    (MatrixMap.isCompletelyPositive_iff_choi _).mp <|
      MatrixMap.IsCompletelyPositive.kron (M.branch_completelyPositive result) (bobChannel result).map_cp

/-- The physical one-way LOCC map is trace preserving. -/
theorem oneWayLOCCMap_tracePreserving
    {bobInput : Type x} {bobOutput : Type y}
    [Fintype bobInput] [DecidableEq bobInput]
    [Fintype bobOutput] [DecidableEq bobOutput]
    (M : FiniteInstrument input output outcome)
    (bobChannel : outcome → CPTPMap bobInput bobOutput) :
    MatrixMap.IsTracePreserving (M.oneWayLOCCMap bobChannel) := by
  intro X
  calc
    (M.oneWayLOCCMap bobChannel X).trace =
        ∑ result,
          (MatrixMap.kron (M.branch result) (bobChannel result).map X).trace := by
      simp [oneWayLOCCMap, Matrix.trace_sum]
    _ = ∑ result,
          (MatrixMap.kron (M.branch result)
            (CPTPOp.id (dIn := bobInput)).map X).trace := by
      refine Finset.sum_congr rfl fun result _ => ?_
      exact trace_kron_eq_trace_kron_id_of_right_tracePreserving
        (M.branch result) (bobChannel result).map
        (bobChannel result).map_TP X
    _ = ((∑ result, MatrixMap.kron (M.branch result)
          (CPTPOp.id (dIn := bobInput)).map) X).trace := by
      simp [Matrix.trace_sum]
    _ = (MatrixMap.kron (∑ result, M.branch result)
          (CPTPOp.id (dIn := bobInput)).map X).trace := by
      rw [MatrixMap.kron_sum_left]
    _ = X.trace := by
      rw [M.sum_branch_eq_total]
      exact MatrixMap.IsTracePreserving.kron M.total.map_TP (CPTPOp.id (dIn := bobInput)).map_TP X

/-- The physical channel implemented by a finite one-way LOCC protocol. -/
def oneWayLOCCChannel
    {bobInput : Type x} {bobOutput : Type y}
    [Fintype bobInput] [DecidableEq bobInput]
    [Fintype bobOutput] [DecidableEq bobOutput]
    (M : FiniteInstrument input output outcome)
    (bobChannel : outcome → CPTPMap bobInput bobOutput) :
    CPTPMap (input × bobInput) (output × bobOutput) :=
  CPTPOp.ofMat
    (M.oneWayLOCCMap bobChannel)
    (M.oneWayLOCCMap_completelyPositive bobChannel)
    (M.oneWayLOCCMap_tracePreserving bobChannel)

@[simp]
theorem oneWayLOCCChannel_map
    {bobInput : Type x} {bobOutput : Type y}
    [Fintype bobInput] [DecidableEq bobInput]
    [Fintype bobOutput] [DecidableEq bobOutput]
    (M : FiniteInstrument input output outcome)
    (bobChannel : outcome → CPTPMap bobInput bobOutput) :
    (M.oneWayLOCCChannel bobChannel).map =
      ∑ result, MatrixMap.kron (M.branch result) (bobChannel result).map :=
  CPTPOp.map_ofMat _ _ _

end FiniteInstrument

namespace OneWayLOCC

variable {aliceInput : Type u} {aliceOutput : Type v}
variable {bobInput : Type w} {bobOutput : Type x} {outcome : Type y}
variable [Fintype aliceInput] [DecidableEq aliceInput]
variable [Fintype aliceOutput] [DecidableEq aliceOutput]
variable [Fintype bobInput] [DecidableEq bobInput]
variable [Fintype bobOutput] [DecidableEq bobOutput]
variable [Fintype outcome]

/-- Construct a finite one-way LOCC operation from Alice's instrument and
Bob's outcome-conditioned channels. Its realization is fixed by construction. -/
def ofFiniteInstrument
    (aliceInstrument : FiniteInstrument aliceInput aliceOutput outcome)
    (bobChannel : outcome → CPTPMap bobInput bobOutput) :
    OneWayLOCC aliceInput aliceOutput bobInput bobOutput outcome where
  aliceInstrument := aliceInstrument
  bobChannel := bobChannel
  realization := aliceInstrument.oneWayLOCCChannel bobChannel
  realization_map := aliceInstrument.oneWayLOCCChannel_map bobChannel

/-- Smoke theorem: the constructor's realized map is the protocol map, so no
independent realization channel can be chosen. -/
@[simp]
theorem ofFiniteInstrument_toChannel_map
    (aliceInstrument : FiniteInstrument aliceInput aliceOutput outcome)
    (bobChannel : outcome → CPTPMap bobInput bobOutput) :
    (ofFiniteInstrument aliceInstrument bobChannel).toChannel.map =
      ∑ result, MatrixMap.kron (aliceInstrument.branch result)
        (bobChannel result).map :=
  aliceInstrument.oneWayLOCCChannel_map bobChannel

end OneWayLOCC

end

end QIT
