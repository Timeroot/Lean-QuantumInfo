/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Asymptotic.Basic
public import QIT.Coding.EntanglementAssisted.Asymptotic.ProtocolLifting
public import QIT.Coding.EntanglementAssisted.Asymptotic.MutualInformationAdditivity
public import QIT.Coding.EntanglementAssisted.Asymptotic.SandwichedTensorPower
public import QIT.Coding.EntanglementAssisted.Asymptotic.LowerBound
public import QIT.Coding.EntanglementAssisted.Asymptotic.ConverseWitness

/-!
# Entanglement-assisted asymptotic support facade

This module is part of the entanglement-assisted classical communication
asymptotic proof spine.  It was split out mechanically from the historical
`EntanglementAssistedAsymptotic` files; theorem statements and proof routes are
unchanged.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Topology
open Filter

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]


end

end QIT
