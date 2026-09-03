/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Entropy.Entropy
public import QuantumLib.QIT.Information.Entropy.EntropyTensorPower
public import QuantumLib.QIT.States.Geometry.Fidelity
public import QuantumLib.QIT.States.Geometry.FuchsVdG
public import QuantumLib.QIT.Information.Renyi
public import QuantumLib.QIT.OneShot.CQGuessing
public import QuantumLib.QIT.OneShot.Smooth
public import QuantumLib.QIT.OneShot.SmoothEndpoint

/-!
# Information foundations

Low-conflict facade for entropy, fidelity, Rényi, and smooth entropy
infrastructure.
-/

@[expose] public section

namespace QIT
namespace Information
namespace Foundations

end Foundations
end Information
end QIT
