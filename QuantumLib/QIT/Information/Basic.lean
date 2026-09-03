/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Entropy.Entropy
public import QuantumLib.QIT.States.TraceNorm.Distance
public import QuantumLib.QIT.States.TraceNorm.Spectral
public import QuantumLib.QIT.States.TraceNorm.PositivePart
public import QuantumLib.QIT.States.TraceNorm.PositivePartBlock
public import QuantumLib.QIT.States.TraceNorm.Variational
public import QuantumLib.QIT.States.Geometry.Fidelity
public import QuantumLib.QIT.States.Geometry.FuchsVdG
public import QuantumLib.QIT.Information.Renyi
public import QuantumLib.QIT.HypothesisTesting.MutualInformation
public import QuantumLib.QIT.OneShot.Smooth
public import QuantumLib.QIT.OneShot.CQGuessing

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
