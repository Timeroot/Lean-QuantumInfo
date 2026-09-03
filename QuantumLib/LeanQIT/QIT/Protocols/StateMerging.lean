/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Protocols.StateMerging.Converse
public import QIT.Protocols.StateMerging.InputSource
public import QIT.Protocols.StateMerging.RecordedOutcome
public import QIT.Protocols.StateMerging.OneShotConverse
public import QIT.Protocols.StateMerging.SmoothMinConverse
public import QIT.Protocols.StateMerging.DirectRates
public import QIT.Protocols.StateMerging.DirectProtocol
public import QIT.Protocols.StateMerging.DirectOperational
public import QIT.Protocols.StateMerging.Direct
public import QIT.Protocols.StateMerging.Optimality

/-!
# State merging

Facade for the source-shaped one-way-LOCC operational semantics of standard
quantum state merging.
-/

@[expose] public section

namespace QIT
namespace Protocols
namespace StateMerging

end StateMerging
end Protocols
end QIT
