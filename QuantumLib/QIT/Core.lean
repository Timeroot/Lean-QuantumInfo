/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Core.System
public import QuantumLib.QIT.Core.State
public import QuantumLib.QIT.Core.Pure
public import QuantumLib.QIT.Core.Map
public import QuantumLib.QIT.Core.Map.ChoiCharacterization
public import QuantumLib.QIT.Core.Channel
public import QuantumLib.QIT.Core.Measurement
public import QuantumLib.QIT.Core.POVMProbability

/-!
# QIT core

Finite-dimensional cross-domain proof-kernel objects for the rest of Lean-QIT.

Topic-heavy theorem surfaces are available through public facades such as
`QIT.States`, `QIT.Information`, `QIT.Entanglement`, and `QIT.Nonlocality`.
-/

@[expose] public section
