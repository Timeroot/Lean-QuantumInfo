/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy.Entropy
public import QIT.States.TraceNorm.Distance
public import QIT.States.TraceNorm.Spectral
public import QIT.States.TraceNorm.PositivePart
public import QIT.States.TraceNorm.PositivePartBlock
public import QIT.States.TraceNorm.Variational
public import QIT.States.Geometry.Fidelity
public import QIT.States.Geometry.FuchsVdG
public import QIT.Information.Renyi
public import QIT.HypothesisTesting.MutualInformation
public import QIT.OneShot.Smooth
public import QIT.OneShot.CQGuessing

/-!
# Basic information quantities

Compatibility import surface for entropy, divergences, trace distance,
fidelity, smooth quantities, and cq guessing APIs.
-/

@[expose] public section

namespace QIT
namespace Information
namespace Basic

end Basic
end Information
end QIT
