/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.LeanQIT.Core.System
public import QuantumLib.LeanQIT.Core.State
public import QuantumLib.LeanQIT.Core.Pure
public import QuantumLib.LeanQIT.Core.Map
public import QuantumLib.LeanQIT.Core.Map.ChoiCharacterization
public import QuantumLib.LeanQIT.Core.Channel
public import QuantumLib.LeanQIT.Core.Measurement
public import QuantumLib.LeanQIT.Core.POVMProbability

/-!
# QIT core

Finite-dimensional cross-domain proof-kernel objects for the rest of Lean-QIT.

Topic-heavy theorem surfaces are available through public facades such as
`QIT.States`, `QIT.Information`, `QIT.Entanglement`, and `QIT.Nonlocality`.
-/

@[expose] public section
