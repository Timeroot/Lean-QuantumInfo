/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Coding.EntanglementAssisted.Basic
public import QuantumLib.QIT.Coding.EntanglementAssisted.PositionBasedCoding
public import QuantumLib.QIT.Coding.EntanglementAssisted.PositionNaimarkTrace
public import QuantumLib.QIT.Coding.EntanglementAssisted.SequentialDecoding
public import QuantumLib.QIT.Coding.EntanglementAssisted.OneShot
public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Petz.Additivity
public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Petz.Limit
public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Basic
public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Additivity.ChannelProduct
public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Limit
public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.CBNorm
public import QuantumLib.QIT.Coding.EntanglementAssisted.Asymptotic
public import QuantumLib.QIT.Coding.EntanglementAssisted.Asymptotic.Upper
public import QuantumLib.QIT.Coding.EntanglementAssisted.Asymptotic.Lower
public import QuantumLib.QIT.Coding.EntanglementAssisted.Asymptotic.Final

/-!
# Entanglement-assisted classical communication

Import surface for one-shot, asymptotic, Petz-Renyi, sandwiched-Renyi, and
completely bounded norm infrastructure for entanglement-assisted classical
communication.
-/

@[expose] public section

namespace QIT
namespace Coding
namespace EntanglementAssisted

end EntanglementAssisted
end Coding
end QIT
