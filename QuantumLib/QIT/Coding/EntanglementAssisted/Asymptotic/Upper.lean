/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Coding.EntanglementAssisted.Asymptotic.Upper.Input
public import QuantumLib.QIT.Coding.EntanglementAssisted.Asymptotic.Upper.Witness
public import QuantumLib.QIT.Coding.EntanglementAssisted.Asymptotic.Upper.Assembly

/-!
# Asymptotic upper-bound facade

This module is part of the entanglement-assisted classical communication
asymptotic proof spine.
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
