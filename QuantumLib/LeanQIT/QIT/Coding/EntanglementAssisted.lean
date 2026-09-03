/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Basic
public import QIT.Coding.EntanglementAssisted.PositionBasedCoding
public import QIT.Coding.EntanglementAssisted.PositionNaimarkTrace
public import QIT.Coding.EntanglementAssisted.SequentialDecoding
public import QIT.Coding.EntanglementAssisted.OneShot
public import QIT.Coding.EntanglementAssisted.Renyi.Petz.Additivity
public import QIT.Coding.EntanglementAssisted.Renyi.Petz.Limit
public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Basic
public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Additivity.ChannelProduct
public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Limit
public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.CBNorm
public import QIT.Coding.EntanglementAssisted.Asymptotic
public import QIT.Coding.EntanglementAssisted.Asymptotic.Upper
public import QIT.Coding.EntanglementAssisted.Asymptotic.Lower
public import QIT.Coding.EntanglementAssisted.Asymptotic.Final

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
