/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Protocols.LOCC.Core

/-!
# Measurement instruments for finite one-way LOCC

This module turns a finite POVM into the physical quantum instrument that
records its classical outcome and discards the measured quantum system.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

namespace POVM

variable {outcome : Type u} {input : Type v}
variable [Fintype outcome]
variable [Fintype input] [DecidableEq input]

/-- Every effect of a finite POVM is bounded above by the identity. -/
theorem effect_le_one (M : POVM outcome input) (result : outcome) :
    M.effects result ≤ 1 := by
  classical
  rw [Matrix.le_iff]
  have hsum :
      1 - M.effects result =
        ∑ other ∈ Finset.univ.erase result, M.effects other := by
    rw [← M.sum_eq_one, ← Finset.sum_erase_add _ _ (Finset.mem_univ result)]
    abel
  rw [hsum]
  exact Matrix.posSemidef_sum (Finset.univ.erase result) fun other _ => M.pos other

/-- The finite instrument that performs `M`, records the outcome, and discards
the measured quantum system. -/
def discardInstrument (M : POVM outcome input) :
    FiniteInstrument input PUnit outcome where
  branch result := MatrixMap.traceEffectToUnit (M.effects result)
  branchTraceNonincreasingCP result :=
    MatrixMap.traceEffectToUnit_traceNonincreasingCP
      (M.pos result) (M.effect_le_one result)
  total := Channel.traceToUnit input
  sum_branch_eq_total := by
    change (∑ result, MatrixMap.traceEffectToUnit (M.effects result)) =
      MatrixMap.traceEffectToUnit (1 : CMatrix input)
    apply LinearMap.ext
    intro X
    rw [LinearMap.sum_apply]
    ext i j
    cases i
    cases j
    simp only [Matrix.sum_apply]
    simp_rw [MatrixMap.traceEffectToUnit_apply_of_posSemidef (M.pos _)]
    rw [MatrixMap.traceEffectToUnit_apply_of_posSemidef Matrix.PosSemidef.one]
    change (∑ result, (X * M.effects result).trace) = (X * (1 : CMatrix input)).trace
    rw [← Matrix.trace_sum, ← Matrix.mul_sum, M.sum_eq_one, Matrix.mul_one]

@[simp]
theorem discardInstrument_branch (M : POVM outcome input) (result : outcome) :
    (M.discardInstrument.branch result) =
      MatrixMap.traceEffectToUnit (M.effects result) :=
  rfl

theorem discardInstrument_totalChannel (M : POVM outcome input) :
    M.discardInstrument.totalChannel = Channel.traceToUnit input :=
  rfl

end POVM

end


end QIT
