/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Asymptotic.LowerBound
public import QIT.Coding.EntanglementAssisted.Asymptotic.ConverseWitness

/-!
# Asymptotic entanglement-assisted classical communication facade

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

namespace Channel

variable (N : Channel a b)

/-- Khatri--Wilde asymptotic lower bound: the channel mutual information
`I(N)` is an operationally achievable entanglement-assisted classical rate.

This theorem is the source-shaped independent lower-bound route: it combines
the one-shot PSD Petz--Renyi lower bound, tensor-power superadditivity of the
barred PSD Petz channel quantity, the `alpha -> 1^-` limit to `I(N)`, and the
block-channel lifting lemma above.  It does not use the sandwiched-Renyi DPI
or strong-converse route. -/
theorem entanglementAssistedInformation_isAchievable_of_oneShotPetzLowerBound
    [Nonempty a] :
    N.IsAchievableEntanglementAssistedClassicalRate
      N.entanglementAssistedInformation := by
  refine N.entanglementAssisted_achievable_of_nUseLowerBoundWitness
    N.entanglementAssistedInformation ?_
  intro δ hδ ε hε
  let η : ℝ := ε / 2
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  have hη_lt : η < ε := by
    dsimp [η]
    linarith
  have hhalfδ : 0 < δ / 2 := by positivity
  have hlim :=
    N.barPetzRenyiMutualInformationPSDFinite_tendsto_entanglementAssistedInformation_left
  have hα_eventually :
      ∀ᶠ alpha in PetzRenyiAlpha.leftToOne,
        N.entanglementAssistedInformation - δ / 2 <
          N.barPetzRenyiMutualInformationPSDFinite
            alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) := by
    exact (tendsto_order.mp hlim).1
      (N.entanglementAssistedInformation - δ / 2) (by linarith)
  haveI : Filter.NeBot PetzRenyiAlpha.leftToOne := PetzRenyiAlpha.leftToOne_neBot
  obtain ⟨alpha, hα_lower⟩ := hα_eventually.exists
  let penalty : ℝ :=
    alpha.1 / (1 - alpha.1) * log2 (1 / (ε - η)) +
      log2 (4 * ε / η ^ 2)
  have hpenalty_tendsto :
      Tendsto (fun n : ℕ => penalty / (n : ℝ)) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpenalty_eventually :
      ∀ᶠ n : ℕ in atTop, penalty / (n : ℝ) < δ / 2 := by
    exact hpenalty_tendsto.eventually (eventually_lt_nhds hhalfδ)
  obtain ⟨Npen, hNpen⟩ := Filter.eventually_atTop.mp hpenalty_eventually
  refine ⟨max 1 Npen, ?_⟩
  intro n hn
  have hn_pos : 0 < n :=
    lt_of_lt_of_le (by norm_num : 0 < 1) (le_trans (Nat.le_max_left 1 Npen) hn)
  have hn_pen : n ≥ Npen :=
    le_trans (Nat.le_max_right 1 Npen) hn
  have hnR_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  have hpen_div : penalty / (n : ℝ) < δ / 2 := hNpen n hn_pen
  have hpen_lt : penalty < (n : ℝ) * (δ / 2) := by
    have := (div_lt_iff₀ hnR_pos).mp hpen_div
    simpa [mul_comm, mul_left_comm] using this
  let blockN : Channel (QIT.TensorPower a n) (QIT.TensorPower b n) := N.tensorPower n
  let blockPetz : ℝ :=
    blockN.barPetzRenyiMutualInformationPSDFinite
      alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)
  have hsingle_scaled :
      (n : ℝ) * (N.entanglementAssistedInformation - δ / 2) <
        (n : ℝ) *
          N.barPetzRenyiMutualInformationPSDFinite
            alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) :=
    mul_lt_mul_of_pos_left hα_lower hnR_pos
  have htensor :
      (n : ℝ) *
          N.barPetzRenyiMutualInformationPSDFinite
            alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) ≤
        blockPetz := by
    dsimp [blockPetz, blockN]
    exact N.barPetzRenyiMutualInformationPSDFinite_tensorPower_lower_bound
      hn_pos alpha
  have hblock_gt :
      (n : ℝ) * (N.entanglementAssistedInformation - δ / 2) <
        blockPetz :=
    lt_of_lt_of_le hsingle_scaled htensor
  let lowerReal : ℝ := (n : ℝ) * (N.entanglementAssistedInformation - δ)
  let oneShotLower : ℝ :=
    blockPetz -
      alpha.1 / (1 - alpha.1) * log2 (1 / (ε - η)) -
      log2 (4 * ε / η ^ 2)
  have honeShotLower_gt : lowerReal < oneShotLower := by
    dsimp [lowerReal, oneShotLower, penalty]
    linarith
  have honeShotLower_le_capacity :
      (oneShotLower : EReal) ≤
        blockN.oneShotEntanglementAssistedClassicalCapacityE ε := by
    change
      ((blockN.barPetzRenyiMutualInformationPSDFinite
            alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) -
          alpha.1 / (1 - alpha.1) * log2 (1 / (ε - η)) -
          log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
        blockN.oneShotEntanglementAssistedClassicalCapacityE ε
    exact @Channel.oneShotEntanglementAssistedClassicalCapacityE_petzPSDFiniteLowerBound
      (QIT.TensorPower a n)
      (QIT.tensorPowerFintype (a := a) n)
      (QIT.tensorPowerDecidableEq (a := a) n)
      (QIT.TensorPower b n)
      (QIT.tensorPowerFintype (a := b) n)
      (QIT.tensorPowerDecidableEq (a := b) n)
      blockN (TensorPower.nonempty (a := a) n)
      ε η alpha.1 hε hη_pos hη_lt alpha.2.1 alpha.2.2
  have hlower_lt_capacity :
      (lowerReal : EReal) <
        blockN.oneShotEntanglementAssistedClassicalCapacityE ε :=
    (EReal.coe_lt_coe_iff.mpr honeShotLower_gt).trans_le honeShotLower_le_capacity
  obtain ⟨M, hMfin, hMdec, hMnonempty,
    EA, hEAfin, hEAdec, EB, hEBfin, hEBdec, C, hCerr, hCrate_gt⟩ :=
    blockN.exists_oneShotCode_rate_gt_of_lt_oneShotCapacityE
      (le_of_lt hε) hlower_lt_capacity
  letI : Fintype M := hMfin
  letI : DecidableEq M := hMdec
  letI : Nonempty M := hMnonempty
  letI : Fintype EA := hEAfin
  letI : DecidableEq EA := hEAdec
  letI : Fintype EB := hEBfin
  letI : DecidableEq EB := hEBdec
  refine ⟨M, inferInstance, inferInstance, inferInstance,
    EA, inferInstance, inferInstance, EB, inferInstance, inferInstance, ?_⟩
  let C' : EntanglementAssistedClassicalCode (N.tensorPower n) 1 M EA EB := by
    simpa [blockN] using C
  have hCerr' : C'.maxErrorAtMost ε := by
    dsimp [C']
    simpa [blockN] using hCerr
  have hCrate_gt' : lowerReal < C'.rate := by
    dsimp [C']
    simpa [blockN] using hCrate_gt
  exact N.nUseLowerBoundWitness_of_blockOneShotCode
    hn_pos C' hCerr' (le_of_lt (by simpa [lowerReal] using hCrate_gt'))

set_option maxHeartbeats 200000

end Channel

end

end QIT
