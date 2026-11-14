/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.System
public import QIT.Core.State
public import QIT.Core.Pure
public import QIT.Core.Map
public import QIT.Core.Map.ChoiCharacterization
public import QIT.Core.Channel
public import QIT.Core.Measurement
public import QIT.Core.POVMProbability
public import QIT.Core.Components

/-!
# QIT core

Finite-dimensional cross-domain proof-kernel objects for local QIT development.

Topic-heavy theorem surfaces are available through public facades such as
`QIT.States`, `QIT.Information`, `QIT.Entanglement`, and `QIT.Nonlocality`.
-/

@[expose] public section
