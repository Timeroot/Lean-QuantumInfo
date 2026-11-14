/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Protocols.FQSW.IIDDirect
public import QIT.Protocols.LOCC.Construction
public import QIT.Protocols.LOCC.ReferenceLift
public import QIT.Protocols.StateMerging.Core
public import QIT.Protocols.TeleportationLOCC

/-!
# Finite-block state merging from FQSW and teleportation

This module turns a physical FQSW block protocol into a physical one-way-LOCC
state-merging block protocol. Alice first runs the FQSW encoder and teleports
its `q` register with the generalized Bell instrument. Bob applies the
outcome-conditioned Weyl correction before running the FQSW decoder.

Source: ADHW `fqsw.tex:352-515,402-420`. This is the explicit
FQSW-plus-teleportation child route, not the distinct HOW random-measurement
direct proof.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y p u₁ v₁

noncomputable section

/-- Regroup the FQSW encoder output and Alice's teleportation half so the two
`q` registers are the input of the Bell instrument and `e` is a spectator. -/
def fqswStateMergingAliceRegroupEquiv (q : Type x) (e : Type y) :
    Prod (Prod q e) q ≃ Prod (Prod q q) e where
  toFun t := ((t.1.1, t.2), t.1.2)
  invFun t := ((t.1.1, t.2), t.1.2)
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

/-- Remove the unit output of the Bell measurement while retaining Alice's
FQSW ebit half. The `q` argument fixes the universe of the discarded unit. -/
def fqswStateMergingAliceOutputEquiv (q : Type x) (e : Type y) :
    Prod PUnit.{x + 1} e ≃ e :=
  let _qUniverseWitness := q
  {
    toFun := fun t => t.2
    invFun := fun t => (PUnit.unit, t)
    left_inv := by intro t; cases t.1; rfl
    right_inv := by intro t; rfl
  }

/-- The Bell instrument with Alice's FQSW ebit half carried through as an
untouched local spectator. -/
def fqswStateMergingTeleportationAliceInstrument
    (q : Type x) (e : Type y)
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] :
    FiniteInstrument
      (Prod (Prod q q) e) e (TeleportationOutcome q) :=
  ((teleportationBellInstrument q).prodIdRight (R := e)).postcompChannel
    (Channel.reindex (fqswStateMergingAliceOutputEquiv q e))

/-- Bob's physical teleportation branch with an arbitrary left spectator. -/
def fqswStateMergingTeleportationBobChannel
    (q : Type x) (s : Type v)
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype s] [DecidableEq s]
    (result : TeleportationOutcome q) :
    Channel (Prod s q) (Prod q s) :=
  (Channel.reindex (Equiv.prodComm s q)).comp <|
    (Channel.idChannel s).prod (teleportationCorrection q result)

/-- Physical teleportation with Alice's output-ebit spectator and Bob's
source spectator exposed as a finite one-way LOCC. -/
def fqswStateMergingTeleportationLOCC
    (q : Type x) (e : Type y) (s : Type v)
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e]
    [Fintype s] [DecidableEq s] :
    OneWayLOCC
      (Prod (Prod q q) e) e
      (Prod s q) (Prod q s)
      (TeleportationOutcome q) :=
  OneWayLOCC.ofFiniteInstrument
    (fqswStateMergingTeleportationAliceInstrument q e)
    (fqswStateMergingTeleportationBobChannel q s)

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

namespace FQSWBlockProtocol

variable {psi : PureVector (Prod (Prod a b) r)} {n : ℕ}
variable {q : Type x} {e : Type y}
variable [Fintype q] [DecidableEq q] [Nonempty q]
variable [Fintype e] [DecidableEq e] [Nonempty e]

variable (C : FQSWBlockProtocol psi n q e e)

/-- Alice's FQSW encoder followed by the register permutation that exposes
the message and her half of the teleportation resource to the Bell
instrument. -/
def stateMergingAlicePreparation :
    Channel (Prod (TensorPower a n) q) (Prod (Prod q q) e) :=
  (Channel.reindex (fqswStateMergingAliceRegroupEquiv q e)).comp
    (C.aliceOperation.prod (Channel.idChannel q))

/-- Alice's physical state-merging instrument: run the FQSW encoder, perform
the Bell instrument on the message and input ebit half, and retain the FQSW
ebit half. -/
def stateMergingAliceInstrument :
    FiniteInstrument
      (Prod (TensorPower a n) q) e (TeleportationOutcome q) :=
  (fqswStateMergingTeleportationAliceInstrument q e).precompChannel
    C.stateMergingAlicePreparation

/-- Bob's branch channel: correct his teleportation half, move the recovered
message before the source `B` register, and run the FQSW decoder. -/
def stateMergingBobChannel (result : TeleportationOutcome q) :
    Channel
      (Prod (TensorPower b n) q)
      (Prod (Prod (TensorPower a n) (TensorPower b n)) e) :=
  C.bobOperation.comp
    (fqswStateMergingTeleportationBobChannel q (TensorPower b n) result)

/-- The finite one-way LOCC obtained by replacing the FQSW quantum message
with physical teleportation. -/
def stateMergingLOCC :
    OneWayLOCC
      (Prod (TensorPower a n) q)
      e
      (Prod (TensorPower b n) q)
      (Prod (Prod (TensorPower a n) (TensorPower b n)) e)
      (TeleportationOutcome q) :=
  OneWayLOCC.ofFiniteInstrument C.stateMergingAliceInstrument
    C.stateMergingBobChannel

/-- A physical finite-block state-merging protocol obtained from an arbitrary
physical FQSW block protocol with communication register `q` and ebit
register `e`. -/
def toStateMergingProtocol :
    StateMergingBlockProtocol
      psi n q q e e (TeleportationOutcome q) where
  inputEbitPairing := Equiv.refl q
  outputEbitPairing := C.ebitPairing
  locc := C.stateMergingLOCC

@[simp]
theorem stateMergingAliceInstrument_branch
    (result : TeleportationOutcome q) :
    (C.stateMergingAliceInstrument.branch result) =
      ((Channel.reindex (fqswStateMergingAliceOutputEquiv q e)).map.comp
        (MatrixMap.kron
          ((teleportationBellInstrument q).branch result)
          (Channel.idChannel e).map)).comp
        C.stateMergingAlicePreparation.map :=
  rfl

@[simp]
theorem stateMergingBobChannel_map
    (result : TeleportationOutcome q) :
    (C.stateMergingBobChannel result).map =
      C.bobOperation.map.comp
        (fqswStateMergingTeleportationBobChannel
          q (TensorPower b n) result).map :=
  rfl

@[simp]
theorem stateMergingLOCC_toChannel_map :
    C.stateMergingLOCC.toChannel.map =
      ∑ result : TeleportationOutcome q,
        MatrixMap.kron
          (C.stateMergingAliceInstrument.branch result)
          (C.stateMergingBobChannel result).map :=
  rfl

/-- The full one-way LOCC channel factors as Alice's FQSW encoder, the
physical teleportation core, and Bob's FQSW decoder. -/
theorem stateMergingLOCC_toChannel_eq_encoder_teleportation_decoder :
    C.stateMergingLOCC.toChannel =
      ((Channel.idChannel e).prod C.bobOperation).comp
        ((fqswStateMergingTeleportationLOCC
            q e (TensorPower b n)).toChannel.comp
          (C.stateMergingAlicePreparation.prod
            (Channel.idChannel (Prod (TensorPower b n) q)))) := by
  rw [Channel.mk.injEq]
  apply LinearMap.ext
  intro X
  change
    (((∑ result : TeleportationOutcome q,
        MatrixMap.kron
          (((fqswStateMergingTeleportationAliceInstrument q e).branch result).comp
            C.stateMergingAlicePreparation.map)
          (C.bobOperation.map.comp
            (fqswStateMergingTeleportationBobChannel
              q (TensorPower b n) result).map)) :
        MatrixMap
          (Prod (Prod (TensorPower a n) q) (Prod (TensorPower b n) q))
          (Prod e (Prod (Prod (TensorPower a n) (TensorPower b n)) e))) X) =
      MatrixMap.kron (Channel.idChannel e).map C.bobOperation.map
        (((∑ result : TeleportationOutcome q,
            MatrixMap.kron
              ((fqswStateMergingTeleportationAliceInstrument q e).branch result)
              (fqswStateMergingTeleportationBobChannel
                q (TensorPower b n) result).map) :
            MatrixMap
              (Prod (Prod (Prod q q) e) (Prod (TensorPower b n) q))
              (Prod e (Prod q (TensorPower b n))))
          (MatrixMap.kron C.stateMergingAlicePreparation.map
            (Channel.idChannel (Prod (TensorPower b n) q)).map X))
  simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun result _ => ?_
  rw [MatrixMap.kron_comp_apply_general]
  rw [MatrixMap.kron_comp_apply_general]
  rw [Channel.idChannel_map_eq_linearMap_id,
    Channel.idChannel_map_eq_linearMap_id]
  simp only [LinearMap.id_comp, LinearMap.comp_id]

/-- The ideal state-merging target is exactly the FQSW target relabelled into
the state-merging output register order. -/
theorem toStateMergingProtocol_targetState_eq_reindex :
    C.toStateMergingProtocol.targetState =
      C.targetState.reindex
        (stateMergingTargetEquiv
          (TensorPower a n) (TensorPower b n) (TensorPower r n) e e) := by
  unfold StateMergingBlockProtocol.targetState FQSWBlockProtocol.targetState
  unfold toStateMergingProtocol stateMergingBlockSource
  rfl

end FQSWBlockProtocol

namespace ADHWFQSWIidMixedBlockConstruction

variable {psi : PureVector (Prod (Prod a b) r)} {n : ℕ}
variable {deltaTypical deltaRate epsilon : ℝ}
variable {atyp : Type p} {btyp : Type u₁} {rtyp : Type v₁}
variable {q : Type x} {e : Type y}
variable [Fintype atyp] [DecidableEq atyp]
variable [Fintype btyp] [DecidableEq btyp]
variable [Fintype rtyp] [DecidableEq rtyp]
variable [Fintype q] [DecidableEq q] [Nonempty q]
variable [Fintype e] [DecidableEq e] [Nonempty e]

variable (C : ADHWFQSWIidMixedBlockConstruction
  psi n deltaTypical deltaRate epsilon atyp btyp rtyp q e)

/-- The concrete finite-block state-merging protocol obtained by teleporting
the quantum message of the mixed-slack ADHW FQSW construction. -/
def stateMergingProtocol :
    StateMergingBlockProtocol
      psi n q q e e (TeleportationOutcome q) :=
  C.physicalProtocol.toStateMergingProtocol

/-- The state-merging target is the concrete FQSW target in the declared
state-merging output order. -/
theorem stateMergingProtocol_targetState_eq_reindex :
    C.stateMergingProtocol.targetState =
      C.physicalProtocol.targetState.reindex
        (stateMergingTargetEquiv
          (TensorPower a n) (TensorPower b n) (TensorPower r n) e e) :=
  C.physicalProtocol.toStateMergingProtocol_targetState_eq_reindex

/-- Exact finite-block net entanglement accounting: teleportation consumes
the FQSW communication rank and the FQSW protocol returns its ebit rank. -/
theorem stateMergingProtocol_netEntanglementRate_eq :
    C.stateMergingProtocol.netEntanglementRate =
      C.physicalProtocol.communicationRate -
        C.physicalProtocol.ebitYieldRate := by
  by_cases hn : n = 0
  · simp [StateMergingBlockProtocol.netEntanglementRate,
      FQSWBlockProtocol.communicationRate, FQSWBlockProtocol.ebitYieldRate, hn]
  · simp only [StateMergingBlockProtocol.netEntanglementRate,
      FQSWBlockProtocol.communicationRate, FQSWBlockProtocol.ebitYieldRate,
      if_neg hn]
    ring

/-- The generalized Bell instrument communicates exactly twice the FQSW
quantum communication rate in classical bits. -/
theorem stateMergingProtocol_classicalCommunicationRate_eq :
    C.stateMergingProtocol.classicalCommunicationRate =
      2 * C.physicalProtocol.communicationRate := by
  by_cases hn : n = 0
  · simp [StateMergingBlockProtocol.classicalCommunicationRate,
      FQSWBlockProtocol.communicationRate, hn]
  · simp only [StateMergingBlockProtocol.classicalCommunicationRate,
      FQSWBlockProtocol.communicationRate, if_neg hn]
    have houtcome :
        log2 (Fintype.card (TeleportationOutcome q) : ℝ) =
          2 * log2 (Fintype.card q : ℝ) := by
      simpa [teleportationClassicalCommunication] using
        teleportationClassicalCommunication_eq_two_log2 q
    rw [houtcome]
    ring

end ADHWFQSWIidMixedBlockConstruction

end

end QIT
