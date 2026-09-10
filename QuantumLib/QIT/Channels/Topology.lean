/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Core.Channel
public import QuantumLib.QIT.States.Topology

/-!
# Topology for channel actions on states

This module records the basic continuity fact for applying a fixed finite-
dimensional channel to a state.  It is kept on the channel-facing surface while
reusing the canonical state topology from `QIT.States.Topology`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

universe u v

noncomputable section

namespace CPTPOp

open QIT

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable (N : CPTPMap a b)

/-- Applying a fixed channel is continuous on the state space. -/
theorem applyState_continuous : Continuous (fun ρ : MState a => N ρ) := by
  refine MState.continuous_of_continuous_m ?_
  simp only [CPTPOp.mat_coe_eq_apply_mat]
  exact (LinearMap.continuous_of_finiteDimensional N.map).comp MState.continuous_matrix

end CPTPOp

end
