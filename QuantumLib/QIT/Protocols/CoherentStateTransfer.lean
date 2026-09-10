/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Protocols.FQSW.Core

/-!
# Coherent state transfer

The fully quantum Slepian--Wolf protocol transfers Alice's share coherently at
quantum communication rate `(1/2) I(A;R)` while generating entanglement.  This
is distinct from standard LOCC state merging, whose net entanglement cost is
`H(A|B)`.  The operational protocol below is exactly the concrete FQSW block
protocol; no second output/target skeleton is introduced.

Source: ADHW `fqsw.tex:352-372,467-515` and Wilde's coherent state-transfer
presentation `qit-notes.tex:37311-37435`.
-/

@[expose] public section

namespace QIT

universe u v w x y z

noncomputable section

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

/-- A coherent state-transfer block protocol is the concrete FQSW block
protocol, including Alice/Bob isometries, computed output, and canonical
transferred-source target. -/
abbrev CoherentStateTransferBlockProtocol
    (psi : Ket ((a × b) × r)) (n : ℕ)
    (communication : Type x) (ebitAlice : Type y) (ebitBob : Type z)
    [Fintype communication] [DecidableEq communication]
    [Fintype ebitAlice] [DecidableEq ebitAlice] [Nonempty ebitAlice]
    [Fintype ebitBob] [DecidableEq ebitBob] :=
  FQSWBlockProtocol psi n communication ebitAlice ebitBob

end
end QIT

namespace Ket

noncomputable section

open QIT
universe u v w x y z
variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

/-- Achievability of coherent state transfer, reusing the canonical concrete
FQSW protocol contract. -/
def IsAchievableCoherentStateTransfer
    (psi : Ket ((a × b) × r)) : Prop :=
  Ket.IsAchievableFQSW.{u, v, w, x, y, z} psi

theorem isAchievableCoherentStateTransfer_iff_isAchievableFQSW
    (psi : Ket ((a × b) × r)) :
    Ket.IsAchievableCoherentStateTransfer.{u, v, w, x, y, z} psi ↔
      Ket.IsAchievableFQSW.{u, v, w, x, y, z} psi :=
  by
    unfold IsAchievableCoherentStateTransfer
    rfl

theorem fqswCommunicationRate_eq_coherentTransferRate
    (psi : Ket ((a × b) × r)) :
    psi.fqswCommunicationRate = psi.state.coherentTransferRate :=
  rfl

end

end Ket

namespace QIT
noncomputable section

universe u v w x y z
variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

end

end QIT
