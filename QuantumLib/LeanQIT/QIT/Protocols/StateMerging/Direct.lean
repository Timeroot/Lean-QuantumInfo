/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Protocols.StateMerging.DirectOperational
public import QIT.Protocols.StateMerging.DirectRates

/-!
# Direct state merging from FQSW and teleportation

This module completes the ADHW child-protocol route: run the concrete IID FQSW
block, teleport its quantum communication register, and account for the input
and output entanglement ranks. The resulting net rate converges to the source
conditional entropy.

Source: ADHW `fqsw.tex:352-515,402-420,1093-1180`; HOW
`swlong.6.2.tex:545-625` supplies the operational state-merging rate target.
-/

@[expose] public section

namespace QIT

universe u v w x y z p q

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

namespace PureVector

/-- Achievability is monotone in the allowed net entanglement rate. -/
theorem IsAchievableStateMergingRate.mono
    {psi : PureVector (Prod (Prod a b) r)} {R S : Real}
    (hRS : R ≤ S)
    (hR : IsAchievableStateMergingRate.{u, v, w, x, y, z, p, q} psi R) :
    IsAchievableStateMergingRate.{u, v, w, x, y, z, p, q} psi S := by
  intro delta hdelta epsilon hepsilon
  obtain ⟨N, hblocks⟩ := hR delta hdelta epsilon hepsilon
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨kA, hkAF, hkAD, hkAN, kB, hkBF, hkBD,
      lA, hlAF, hlAD, hlAN, lB, hlBF, hlBD,
      outcome, houtcomeF, houtcomeD, houtcomeN,
      C, hrate, herror⟩ := hblocks n hn
  refine ⟨kA, hkAF, hkAD, hkAN, kB, hkBF, hkBD,
    lA, hlAF, hlAD, hlAN, lB, hlBF, hlBD,
    outcome, houtcomeF, houtcomeD, houtcomeN,
    C, ?_, herror⟩
  exact hrate.trans (by simpa [add_comm] using add_le_add_right hRS delta)

/-- The concrete ADHW FQSW-plus-teleportation construction obeys the stronger
uniform output-ebit exponent bound used by the original HOW/Fannes converse. -/
theorem stateMerging_direct_achievable_at_conditionalEntropy_withOutputEbitExponent
    (psi : PureVector (Prod (Prod a b) r)) :
    PureVector.IsAchievableStateMergingRateWithOutputEbitExponent.{u, v, w, x, x, y, y, x}
      psi psi.state.marginalA.conditionalEntropy := by
  refine ⟨psi.fqswEbitYieldRate, psi.fqswEbitYieldRate_nonneg, ?_⟩
  intro delta hdelta epsilon hepsilon
  let rateSlack : Real := delta / 6
  let typicalSlack : Real := rateSlack / 8
  let targetFQSWError : Real := epsilon / 2
  let internalFQSWError : Real := targetFQSWError / 4
  have hrateSlack : 0 < rateSlack := by
    dsimp [rateSlack]
    positivity
  have htypicalSlack : 0 < typicalSlack := by
    dsimp [typicalSlack]
    positivity
  have htargetFQSWError : 0 < targetFQSWError := by
    dsimp [targetFQSWError]
    positivity
  have hinternalFQSWError : 0 < internalFQSWError := by
    dsimp [internalFQSWError]
    positivity
  obtain ⟨Nblocks, hblocks⟩ :=
    exists_adhwFQSWIidMixedBlockConstruction_eventually
      psi htypicalSlack hrateSlack hinternalFQSWError (by
        dsimp [typicalSlack]
        exact le_rfl)
  obtain ⟨Nerror, herror⟩ :=
    eventually_half_adhwFQSWIidPostCompressionTraceErrorBound_le
      hrateSlack htargetFQSWError
  refine ⟨max (max Nblocks Nerror) 1, Nat.le_max_right _ _, ?_⟩
  intro n hn
  have hnblocks : Nblocks ≤ n :=
    le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_left _ _) hn)
  have hnerror : Nerror ≤ n :=
    le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_left _ _) hn)
  have hnpos : 0 < n :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one (le_trans (Nat.le_max_right _ _) hn)
  obtain ⟨atyp, hatypF, hatypD, btyp, hbtypF, hbtypD, rtyp, hrtypF, hrtypD,
      q, hqF, hqD, hqN, e, heF, heD, heN, hB⟩ := hblocks n hnblocks
  let _ : Fintype atyp := hatypF
  let _ : DecidableEq atyp := hatypD
  let _ : Fintype btyp := hbtypF
  let _ : DecidableEq btyp := hbtypD
  let _ : Fintype rtyp := hrtypF
  let _ : DecidableEq rtyp := hrtypD
  let _ : Fintype q := hqF
  let _ : DecidableEq q := hqD
  let _ : Nonempty q := hqN
  let _ : Fintype e := heF
  let _ : DecidableEq e := heD
  let _ : Nonempty e := heN
  obtain ⟨B⟩ := hB
  refine ⟨q, hqF, hqD, hqN, q, hqF, hqD,
    e, heF, heD, heN, e, heF, heD,
    TeleportationOutcome q, inferInstance, inferInstance, inferInstance,
    B.stateMergingProtocol, ?_, ?_, ?_⟩
  · rw [B.stateMergingProtocol_netEntanglementRate_eq]
    have hcomm := B.physicalProtocol_communicationRate_le hnpos
    have hyield := B.physicalProtocol_ebitYieldRate_ge hnpos
    calc
      B.physicalProtocol.communicationRate - B.physicalProtocol.ebitYieldRate ≤
          (psi.fqswCommunicationRate + (9 / 4 : Real) * rateSlack) -
            (psi.fqswEbitYieldRate - 3 * rateSlack) := sub_le_sub hcomm hyield
      _ ≤ psi.state.marginalA.conditionalEntropy + delta := by
        rw [← psi.fqswCommunicationRate_sub_ebitYieldRate_eq_conditionalEntropy]
        dsimp [rateSlack]
        linarith
  · calc
      B.stateMergingProtocol.fidelityError ≤
          2 * B.physicalProtocol.normalizedError :=
        B.stateMergingProtocol_fidelityError_le
      _ ≤ 2 * targetFQSWError := by
        gcongr
        exact B.physicalProtocol_normalizedError_le.trans (herror n hnerror)
      _ = epsilon := by
        dsimp [targetFQSWError]
        ring
  · exact log2_card_le_exponent_mul_of_card_le_two_rpow
      e n psi.fqswEbitYieldRate
      B.balancedRateChoice.ebit_card_upper_for_target

/-- The ADHW FQSW-plus-teleportation construction achieves the conditional
entropy endpoint for the canonical HOW rate predicate. In particular, this
includes negative conditional entropy, where the protocol generates net
entanglement. -/
theorem stateMerging_direct_achievable_at_conditionalEntropy
    (psi : PureVector (Prod (Prod a b) r)) :
    PureVector.IsAchievableStateMergingRate.{u, v, w, x, x, y, y, x}
      psi psi.state.marginalA.conditionalEntropy :=
  (stateMerging_direct_achievable_at_conditionalEntropy_withOutputEbitExponent psi)
    |>.toIsAchievableStateMergingRate

/-- Every net entanglement rate strictly above the conditional entropy is
achievable by the concrete FQSW-plus-teleportation route. -/
theorem stateMerging_direct_achievable
    (psi : PureVector (Prod (Prod a b) r)) (R : Real)
    (hR : psi.state.marginalA.conditionalEntropy < R) :
    PureVector.IsAchievableStateMergingRate.{u, v, w, x, x, y, y, x} psi R :=
  IsAchievableStateMergingRate.mono hR.le
    (stateMerging_direct_achievable_at_conditionalEntropy psi)

end PureVector

end QIT
