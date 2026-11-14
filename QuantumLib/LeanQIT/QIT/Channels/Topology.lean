/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Channel
public import QIT.States.Topology

/-!
# Topology for channel actions on states

This module records the basic continuity fact for applying a fixed finite-
dimensional channel to a state.  It is kept on the channel-facing surface while
reusing the canonical state topology from `QIT.States.Topology`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

namespace Channel

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable (N : Channel a b)

/-- Applying a fixed channel is continuous on the state space. -/
theorem applyState_continuous : Continuous (fun ρ : State a => N.applyState ρ) := by
  rw [continuous_induced_rng]
  change Continuous fun ρ : State a => N.map ρ.matrix
  exact (LinearMap.continuous_of_finiteDimensional N.map).comp State.continuous_matrix

end Channel

end

end QIT
