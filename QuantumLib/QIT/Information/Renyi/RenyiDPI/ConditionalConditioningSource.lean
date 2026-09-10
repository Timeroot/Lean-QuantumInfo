/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Entropy.MutualInformationDPI
public import QuantumLib.QIT.Information.Renyi.RenyiDPI.ReferenceOrder
public import QuantumLib.QIT.Information.Renyi.RenyiOrderParameter
public import QuantumLib.QIT.Channels.Diamond
public import QuantumLib.QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.RegularizedSourceWrappers

/-!
# Conditional sandwiched Renyi data processing on the conditioning system

This module proves the conditioning-system data-processing inequality from
Tomamichel2015FiniteResources, `cond.tex:268-284`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal
open Matrix

noncomputable section
universe u v w
variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

open QIT

namespace MState

private theorem idChannel_applyState_eq (rho : MState a) :
    (CPTPOp.id (dIn := a)) rho = rho := by
  apply MState.ext
  simp

private theorem sandwichedRenyiPSDReferenceE_real_smul_reference_of_lt_one
    (rho : MState a) {tau : CMatrix a} (htau : tau.PosSemidef)
    {scale : ℝ} (hscale : 0 < scale) (alpha : ℝ)
    (halpha_pos : 0 < alpha) (halpha_lt_one : alpha < 1)
    (hQ : 0 < sandwichedRenyiQ rho.m tau rho.psd htau alpha) :
    sandwichedRenyiPSDReferenceE rho (scale • tau)
        (Matrix.PosSemidef.smul htau hscale.le) alpha =
      sandwichedRenyiPSDReferenceE rho tau htau alpha - log2 scale := by
  have hQscale := sandwichedRenyiQ_real_smul_reference_of_pos
    rho htau hscale alpha halpha_pos
  have hQscale_pos :
      0 < sandwichedRenyiQ rho.m (scale • tau) rho.psd
        (Matrix.PosSemidef.smul htau hscale.le) alpha := by
    rw [hQscale]
    exact mul_pos (Real.rpow_pos_of_pos hscale _) hQ
  rw [sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one _ _ halpha_lt_one,
    sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one _ _ halpha_lt_one,
    sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
      _ _ _ hQscale_pos.ne',
    sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero _ _ _ hQ.ne']
  apply EReal.coe_eq_coe_iff.mpr
  unfold sandwichedRenyiPSDReferenceLowAlpha
  rw [hQscale, log2_mul
    (Real.rpow_pos_of_pos hscale (1 - alpha)).ne' hQ.ne']
  have hlogpow : log2 (scale ^ (1 - alpha)) =
      (1 - alpha) * log2 scale := by
    unfold log2
    rw [Real.log_rpow hscale]
    ring
  rw [hlogpow]
  have halpha_sub_ne : alpha - 1 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_lt halpha_lt_one)
  field_simp [halpha_sub_ne]
  ring

private theorem sandwichedRenyiPSDReferenceE_real_smul_reference_of_one_lt
    (rho : MState a) {tau : CMatrix a} (htau : tau.PosSemidef)
    (hSupport : Matrix.Supports rho.m tau)
    {scale : ℝ} (hscale : 0 < scale) (alpha : ℝ) (halpha : 1 < alpha) :
    sandwichedRenyiPSDReferenceE rho (scale • tau)
        (Matrix.PosSemidef.smul htau hscale.le) alpha =
      sandwichedRenyiPSDReferenceE rho tau htau alpha - log2 scale := by
  have hscaleSupport : Matrix.Supports rho.m (scale • tau) := by
    intro v hv
    apply hSupport v
    have hscaled : scale • tau.mulVec v = 0 := by
      simpa [Matrix.smul_mulVec] using hv
    exact (smul_eq_zero.mp hscaled).resolve_left hscale.ne'
  rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha,
    sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha,
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      rho (Matrix.PosSemidef.smul htau hscale.le) alpha hscaleSupport,
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      rho htau alpha hSupport]
  apply EReal.coe_eq_coe_iff.mpr
  exact sandwichedRenyiPSDReferenceHighAlphaFinite_real_smul_reference_of_supports
    rho htau hSupport hscale alpha halpha

private theorem smul_identityTensorStateMatrix_le_fullRankApprox
    (sigma : MState b) {delta : ℝ} (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1) :
    ((1 - delta : ℝ) • identityTensorStateMatrix (a := a) sigma) ≤
      identityTensorStateMatrix (a := a)
        (fullRankApproxMaximallyMixedStatePath sigma delta) := by
  let : Nonempty b := sigma.nonempty
  have hside := smul_left_le_fullRankApproxStatePath_matrix_of_mem
    sigma (MState.uniform : MState b) hdelta
  rw [Matrix.le_iff] at hside ⊢
  have hone : (1 : CMatrix a).PosSemidef := Matrix.PosSemidef.one
  have hkron := hone.kronecker hside
  have heq :
      Matrix.kronecker (1 : CMatrix a)
          ((fullRankApproxStatePath sigma (MState.uniform : MState b) delta).m -
            (1 - delta) • sigma.m) =
        identityTensorStateMatrix (a := a)
            (fullRankApproxMaximallyMixedStatePath sigma delta) -
          (1 - delta) • identityTensorStateMatrix (a := a) sigma := by
    ext i j
    simp [identityTensorStateMatrix, fullRankApproxMaximallyMixedStatePath,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply]
    ring
  rw [← heq]
  exact hkron

/-- A channel on the conditioning system maps `I_A tensor sigma_B` exactly to
`I_A tensor N(sigma_B)`. -/
theorem conditioningChannel_map_identityTensorStateMatrix
    (N : CPTPMap b c) (sigma : MState b) :
    ((CPTPOp.id (dIn := a)).prod N).map
        (identityTensorStateMatrix (a := a) sigma) =
      identityTensorStateMatrix (a := a) (N sigma) := by
  rw [identityTensorStateMatrix, identityTensorStateMatrix,
    CPTPOp.prod_map_kronecker]
  simp [CPTPOp.mat_coe_eq_apply_mat, CPTPOp.id_map]

set_option maxRecDepth 4000 in
/-- Every strict finite-order source candidate is bounded by the optimized
output entropy after a channel on the conditioning system. The output side
reference is allowed to be singular. -/
theorem conditionalSandwichedRenyiUpSourceCandidate_le_conditioning
    (rho : MState (a × b)) (N : CPTPMap b c)
    (alpha : ℝ) (halpha_half : 1 / 2 < alpha) (halpha_one : alpha ≠ 1)
    (sigma : MState b) (hsigma : sigma.m.PosDef) :
      rho.conditionalSandwichedRenyiUpSourceCandidate sigma hsigma alpha
        (lt_trans (by norm_num) halpha_half) halpha_one ≤
      MState.conditionalSandwichedRenyiUpSource (((CPTPOp.id (dIn := a)).prod N) rho)
        alpha (lt_trans (by norm_num) halpha_half) halpha_one := by
  let Phi : CPTPMap (a × b) (a × c) := (CPTPOp.id (dIn := a)).prod N
  let omega : MState (a × c) := Phi rho
  let tau : MState c := N sigma
  let rin : CMatrix (a × b) := identityTensorStateMatrix (a := a) sigma
  let rout : CMatrix (a × c) := identityTensorStateMatrix (a := a) tau
  let hrin : rin.PosSemidef :=
    identityTensorStateMatrix_posSemidef (a := a) sigma
  let hrout : rout.PosSemidef :=
    identityTensorStateMatrix_posSemidef (a := a) tau
  let candidate : ℝ :=
    rho.conditionalSandwichedRenyiUpSourceCandidate sigma hsigma alpha
      (lt_trans (by norm_num) halpha_half) halpha_one
  have hrin_pd : rin.PosDef := by
    exact identityTensorStateMatrix_posDef_of_posDef (a := a) sigma hsigma
  have hmap : Phi.map rin = rout := by
    simpa [Phi, rin, rout, tau] using
      conditioningChannel_map_identityTensorStateMatrix (a := a) N sigma
  have hrange : (1 / 2 ≤ alpha ∧ alpha < 1) ∨ 1 < alpha := by
    rcases lt_or_gt_of_ne halpha_one with halpha_lt | halpha_gt
    · exact Or.inl ⟨halpha_half.le, halpha_lt⟩
    · exact Or.inr halpha_gt
  have hDPI :=
    sandwichedRenyiPSDReferenceE_dataProcessing_channel_of_half_le_lt_one_or_one_lt
      rho hrin Phi alpha hrange
  have hDPI' :
      sandwichedRenyiPSDReferenceE omega rout hrout alpha ≤
        sandwichedRenyiPSDReferenceE rho rin hrin alpha := by
    simpa [omega, hmap] using hDPI
  have hbridgeIn :=
    conditionalSandwichedRenyiUpSourceCandidate_eq_neg_referenceE
      rho sigma hsigma alpha (lt_trans (by norm_num) halpha_half) halpha_one
  have hinput : sandwichedRenyiPSDReferenceE rho rin hrin alpha =
      -(candidate : EReal) := by
    rw [show (candidate : EReal) =
      -sandwichedRenyiPSDReferenceE rho rin hrin alpha by
        simpa [candidate, rin] using hbridgeIn]
    simp
  have hdiv : sandwichedRenyiPSDReferenceE omega rout hrout alpha ≤
      -(candidate : EReal) := hDPI'.trans_eq hinput
  let : Nonempty c := tau.nonempty
  have hbdd := omega.conditionalSandwichedRenyiUpSourceValueSet_bddAbove
    halpha_half halpha_one
  have htend : Filter.Tendsto (fun delta : ℝ =>
      candidate + log2 (1 - delta))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds candidate) := by
    simpa using tendsto_const_nhds.add log2_one_sub_tendsto_zero
  let : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) :=
    left_nhdsWithin_Ioo_neBot zero_lt_one
  refine le_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  have hscale : 0 < 1 - delta := sub_pos.mpr hdelta.2
  let path : MState c := fullRankApproxMaximallyMixedStatePath tau delta
  have hpath_pd : path.m.PosDef := by
    simpa [path, fullRankApproxMaximallyMixedStatePath, fullRankApproxStatePath,
      hdelta] using fullRankApproxState_posDef_of_noise tau
        (MState.uniform : MState c) MState.uniform_posDef
        hdelta.1.le hdelta.2.le hdelta.1
  let rpath : CMatrix (a × c) := identityTensorStateMatrix (a := a) path
  let hrpath : rpath.PosSemidef :=
    identityTensorStateMatrix_posSemidef (a := a) path
  have hscaled : ((1 - delta : ℝ) • rout).PosSemidef :=
    Matrix.PosSemidef.smul hrout hscale.le
  have horder : ((1 - delta : ℝ) • rout) ≤ rpath := by
    simpa [rout, rpath, path] using
      smul_identityTensorStateMatrix_le_fullRankApprox
        (a := a) tau hdelta
  have hanti : sandwichedRenyiPSDReferenceE omega rpath hrpath alpha ≤
      sandwichedRenyiPSDReferenceE omega ((1 - delta : ℝ) • rout)
        hscaled alpha :=
    sandwichedRenyiPSDReferenceE_antitone_reference omega
      hscaled hrpath horder halpha_half.le
  have hscaleDiv :
      sandwichedRenyiPSDReferenceE omega ((1 - delta : ℝ) • rout)
          hscaled alpha =
        sandwichedRenyiPSDReferenceE omega rout hrout alpha -
          log2 (1 - delta) := by
    rcases lt_or_gt_of_ne halpha_one with halpha_lt | halpha_gt
    · have hQin : 0 < sandwichedRenyiQ rho.m rin rho.psd hrin alpha :=
        sandwichedRenyiQ_pos_of_state_posDef_reference rho hrin_pd alpha
      have hQmap :=
        sandwichedRenyiQ_dataProcessing_channel_reference_of_half_lt_lt_one
          rho hrin Phi alpha halpha_half halpha_lt
      have hQoutMap : 0 < sandwichedRenyiQ (Phi rho).m
          (Phi.map rin) (Phi rho).psd (Phi.mapsPositive rin hrin) alpha :=
        lt_of_lt_of_le hQin hQmap
      have hQout : 0 < sandwichedRenyiQ omega.m rout omega.psd hrout alpha := by
        simpa [omega, hmap] using hQoutMap
      exact sandwichedRenyiPSDReferenceE_real_smul_reference_of_lt_one
        omega hrout hscale alpha (lt_trans (by norm_num) halpha_half)
        halpha_lt hQout
    · have hinSupport : Matrix.Supports rho.m rin :=
        Matrix.Supports.of_right_posDef rho.m rin hrin_pd
      have houtSupportMap :=
        channel_applyState_supports_of_supports rho hrin Phi hinSupport
      have houtSupport : Matrix.Supports omega.m rout := by
        simpa [omega, hmap] using houtSupportMap
      exact sandwichedRenyiPSDReferenceE_real_smul_reference_of_one_lt
        omega hrout houtSupport hscale alpha halpha_gt
  have hchain : sandwichedRenyiPSDReferenceE omega rpath hrpath alpha ≤
      ((-(candidate + log2 (1 - delta)) : ℝ) : EReal) := by
    calc
      sandwichedRenyiPSDReferenceE omega rpath hrpath alpha ≤
          sandwichedRenyiPSDReferenceE omega ((1 - delta : ℝ) • rout)
            hscaled alpha := hanti
      _ = sandwichedRenyiPSDReferenceE omega rout hrout alpha -
          log2 (1 - delta) := hscaleDiv
      _ ≤ -(candidate : EReal) - log2 (1 - delta) :=
        by
          have hadd := add_le_add_right hdiv
            (-(log2 (1 - delta) : EReal))
          simpa [sub_eq_add_neg, add_comm] using hadd
      _ = ((-(candidate + log2 (1 - delta)) : ℝ) : EReal) := by
        have hreal : -candidate - log2 (1 - delta) =
            -(candidate + log2 (1 - delta)) := by ring
        simpa [EReal.coe_neg] using
          congrArg (fun x : ℝ => (x : EReal)) hreal
  have hbridgePath :=
    conditionalSandwichedRenyiUpSourceCandidate_eq_neg_referenceE
      omega path hpath_pd alpha (lt_trans (by norm_num) halpha_half) halpha_one
  have hcandidateE : ((candidate + log2 (1 - delta) : ℝ) : EReal) ≤
      (omega.conditionalSandwichedRenyiUpSourceCandidate path hpath_pd alpha
        (lt_trans (by norm_num) halpha_half) halpha_one : EReal) := by
    rw [hbridgePath]
    have hcoeNeg : ((candidate + log2 (1 - delta) : ℝ) : EReal) =
        -(((-(candidate + log2 (1 - delta)) : ℝ) : EReal)) := by
      rw [← EReal.coe_neg]
      congr 1
      ring
    rw [hcoeNeg]
    exact EReal.neg_le_neg_iff.mpr hchain
  have hcandidate : candidate + log2 (1 - delta) ≤
      omega.conditionalSandwichedRenyiUpSourceCandidate path hpath_pd alpha
        (lt_trans (by norm_num) halpha_half) halpha_one :=
    EReal.coe_le_coe_iff.mp hcandidateE
  exact hcandidate.trans <| le_csSup hbdd ⟨path, hpath_pd, rfl⟩

/-- The strict finite-order upward conditional sandwiched Renyi entropy cannot
decrease under a channel on the conditioning system. -/
theorem conditionalSandwichedRenyiUpSource_dataProcessing_conditioning
    (rho : MState (a × b)) (N : CPTPMap b c)
    (alpha : ℝ) (halpha_half : 1 / 2 < alpha) (halpha_one : alpha ≠ 1) :
    rho.conditionalSandwichedRenyiUpSource alpha
        (lt_trans (by norm_num) halpha_half) halpha_one ≤
      MState.conditionalSandwichedRenyiUpSource (((CPTPOp.id (dIn := a)).prod N) rho)
        alpha (lt_trans (by norm_num) halpha_half) halpha_one := by
  let : Nonempty b := by
    rcases rho.nonempty with ⟨z⟩
    exact ⟨z.2⟩
  unfold conditionalSandwichedRenyiUpSource
  refine csSup_le
    (rho.conditionalSandwichedRenyiUpSourceValueSet_nonempty
      alpha (lt_trans (by norm_num) halpha_half) halpha_one) ?_
  intro x hx
  rcases hx with ⟨sigma, hsigma, rfl⟩
  exact conditionalSandwichedRenyiUpSourceCandidate_le_conditioning
    rho N alpha halpha_half halpha_one sigma hsigma

/-- Conditional-min feasibility is preserved by a channel on the conditioning
system. -/
theorem ConditionalMinEntropyFeasible.conditioningChannel
    (rho : MState (a × b)) (sigma : MState b) (lam : ℝ)
    (N : CPTPMap b c)
    (h : ConditionalMinEntropyFeasible (a := a) rho sigma lam) :
    ConditionalMinEntropyFeasible (a := a)
      (((CPTPOp.id (dIn := a)).prod N) rho) (N sigma) lam := by
  let Phi : CPTPMap (a × b) (a × c) := (CPTPOp.id (dIn := a)).prod N
  let rin : CMatrix (a × b) := identityTensorStateMatrix (a := a) sigma
  let rout : CMatrix (a × c) :=
    identityTensorStateMatrix (a := a) (N sigma)
  let t : ℝ := Real.rpow 2 (-lam)
  have hmapFeas : Phi.map rho.m ≤ Phi.map ((t : ℂ) • rin) := by
    apply Matrix.le_iff.mpr
    have hpos : (((t : ℂ) • rin) - rho.m).PosSemidef := by
      simpa [t, rin, ConditionalMinEntropyFeasible, Matrix.le_iff] using h
    simpa [map_sub, map_smul] using Phi.mapsPositive _ hpos
  rw [ConditionalMinEntropyFeasible]
  have hmapRef : Phi.map rin = rout := by
    simpa [Phi, rin, rout] using
      conditioningChannel_map_identityTensorStateMatrix (a := a) N sigma
  have hfinal : Phi.map rho.m ≤ (t : ℂ) • rout := by
    simpa [map_smul, hmapRef] using hmapFeas
  simpa [Phi, rin, rout, t, CPTPOp.mat_coe_eq_apply_mat] using hfinal

/-- Conditional min-entropy cannot decrease under a channel on the
conditioning system. -/
theorem conditionalMinEntropy_dataProcessing_conditioning
    (rho : MState (a × b)) (N : CPTPMap b c) :
    rho.conditionalMinEntropy ≤
      MState.conditionalMinEntropy (((CPTPOp.id (dIn := a)).prod N) rho) := by
  let : Nonempty b := by
    rcases rho.nonempty with ⟨z⟩
    exact ⟨z.2⟩
  rw [conditionalMinEntropy_eq, conditionalMinEntropy_eq]
  change sSup (rho.conditionalMinEntropyFeasibleExponentValueSet (a := a)) ≤
    sSup (MState.conditionalMinEntropyFeasibleExponentValueSet
      (((CPTPOp.id (dIn := a)).prod N) rho) (a := a))
  refine csSup_le
    (rho.conditionalMinEntropyFeasibleExponentValueSet_nonempty (a := a)) ?_
  intro lam hlam
  rcases hlam with ⟨sigma, hfeas⟩
  exact le_csSup
    (MState.conditionalMinEntropyFeasibleExponentValueSet_bddAbove
      (((CPTPOp.id (dIn := a)).prod N) rho) (a := a))
    ⟨N sigma,
      ConditionalMinEntropyFeasible.conditioningChannel rho sigma lam N hfeas⟩

/-! ## Boundary order `alpha = 1 / 2` -/

/-- Conditional max-entropy cannot decrease under a channel on the
conditioning system. -/
theorem conditionalMaxEntropy_dataProcessing_conditioning
    (rho : MState (a × b)) (N : CPTPMap b c) :
    rho.conditionalMaxEntropy ≤
      MState.conditionalMaxEntropy (((CPTPOp.id (dIn := a)).prod N) rho) := by
  let Phi : CPTPMap (a × b) (a × c) := (CPTPOp.id (dIn := a)).prod N
  let omega : MState (a × c) := Phi rho
  let : Nonempty a := by
    rcases rho.nonempty with ⟨z⟩
    exact ⟨z.1⟩
  let : Nonempty b := by
    rcases rho.nonempty with ⟨z⟩
    exact ⟨z.2⟩
  let : Nonempty c := by
    exact MState.nonempty (N (MState.uniform : MState b))
  rw [conditionalMaxEntropy_eq_sSup_valueSet,
    conditionalMaxEntropy_eq_sSup_valueSet]
  refine csSup_le (rho.conditionalMaxEntropyValueSet_nonempty (a := a)) ?_
  intro x hx
  rcases hx with ⟨sigma, hsigma_pos, rfl⟩
  have hrefmap :
      Phi ((MState.uniform : MState a).prod sigma) =
        (MState.uniform : MState a).prod (N sigma) := by
    rw [show Phi = (CPTPOp.id (dIn := a)).prod N by rfl,
      CPTPOp.prod_apply_prod, idChannel_applyState_eq]
  have hfid :
      rho.squaredFidelity ((MState.uniform : MState a).prod sigma) ≤
        omega.squaredFidelity
          ((MState.uniform : MState a).prod (N sigma)) := by
    simpa [omega, hrefmap] using
      MState.squaredFidelity_le_applyState_squaredFidelity
        Phi rho ((MState.uniform : MState a).prod sigma)
  have hexponent :
      rho.conditionalMaxEntropyExponentCandidate (a := a) sigma ≤
        omega.conditionalMaxEntropyExponentCandidate (a := a) (N sigma) := by
    rw [conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity,
      conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity]
    exact mul_le_mul_of_nonneg_left hfid (Nat.cast_nonneg _)
  have hout_pos :
      0 < omega.conditionalMaxEntropyExponentCandidate (a := a) (N sigma) :=
    lt_of_lt_of_le hsigma_pos hexponent
  have hcandidate :
      rho.conditionalMaxEntropyCandidate (a := a) sigma ≤
        omega.conditionalMaxEntropyCandidate (a := a) (N sigma) := by
    rw [conditionalMaxEntropyCandidate_eq_log2_exponentCandidate,
      conditionalMaxEntropyCandidate_eq_log2_exponentCandidate]
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hsigma_pos hexponent) (Real.log_nonneg (by norm_num))
  exact hcandidate.trans <| le_csSup
    (omega.conditionalMaxEntropyValueSet_bddAbove (a := a))
    ⟨N sigma, hout_pos, rfl⟩

/-! ## Boundary order `alpha = 1` -/

/-- Conditional von Neumann entropy cannot decrease under a channel on the
conditioning system. The proof is the trace-log relative-entropy DPI packaged
as mutual-information DPI. -/
theorem conditionalEntropy_dataProcessing_conditioning
    (rho : MState (a × b)) (N : CPTPMap b c) :
    rho.conditionalEntropy ≤
      MState.conditionalEntropy (((CPTPOp.id (dIn := a)).prod N) rho) := by
  let omega : MState (a × c) := ((CPTPOp.id (dIn := a)).prod N) rho
  have hmi := mutualInformation_dataProcessing_local_channels_ge
    rho (CPTPOp.id (dIn := a)) N
  have hmarginal : omega.traceRight = rho.traceRight := by
    change MState.traceRight (((CPTPOp.id (dIn := a)).prod N) rho) =
      rho.traceRight
    rw [MState.traceRight_applyState_prod, idChannel_applyState_eq]
  unfold QIT.mutualInformation at hmi
  rw [show ((CPTPOp.id (dIn := a)).prod N) rho = omega by rfl,
    hmarginal] at hmi
  unfold conditionalEntropy
  linarith

/-! ## Full closed Renyi-order theorem -/

/-- A channel on the conditioning system cannot decrease the upward
sandwiched conditional Renyi entropy at any order in `[1/2, infinity]`.

This is Tomamichel2015FiniteResources, `cond.tex:268-284`. -/
theorem conditionalSandwichedRenyiUpExtendedOrder_dataProcessing_conditioning
    (rho : MState (a × b)) (N : CPTPMap b c) (alpha : RenyiOrder) :
    rho.conditionalSandwichedRenyiUpExtendedOrder alpha ≤
      conditionalSandwichedRenyiUpExtendedOrder
        (((CPTPOp.id (dIn := a)).prod N) rho) alpha := by
  obtain ⟨val, hval⟩ := alpha
  cases val with
  | top =>
      change rho.conditionalMinEntropy ≤
        MState.conditionalMinEntropy (((CPTPOp.id (dIn := a)).prod N) rho)
      exact conditionalMinEntropy_dataProcessing_conditioning rho N
  | coe r =>
      have hr : 1 / 2 ≤ r := by exact_mod_cast hval
      change rho.conditionalSandwichedRenyiUpFiniteOrder r ≤
        conditionalSandwichedRenyiUpFiniteOrder
          (((CPTPOp.id (dIn := a)).prod N) rho) r
      by_cases hone : r = 1
      · subst r
        rw [conditionalSandwichedRenyiUpFiniteOrder_one,
          conditionalSandwichedRenyiUpFiniteOrder_one]
        exact conditionalEntropy_dataProcessing_conditioning rho N
      by_cases hhalf : r = (2 : ℝ)⁻¹
      · subst r
        rw [conditionalSandwichedRenyiUpFiniteOrder_half,
          conditionalSandwichedRenyiUpFiniteOrder_half]
        exact conditionalMaxEntropy_dataProcessing_conditioning rho N
      · have hpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
        have hhalf' : r ≠ 1 / 2 := by
          simpa using hhalf
        have hstrict : 1 / 2 < r :=
          lt_of_le_of_ne hr hhalf'.symm
        rw [conditionalSandwichedRenyiUpFiniteOrder_of_pos_ne_one_ne_half
            rho hpos hone hhalf,
          conditionalSandwichedRenyiUpFiniteOrder_of_pos_ne_one_ne_half
            (((CPTPOp.id (dIn := a)).prod N) rho) hpos hone hhalf]
        exact conditionalSandwichedRenyiUpSource_dataProcessing_conditioning
          rho N r hstrict hone

/-- Discarding the right part of the conditioning register gives
`H(A|BC) ≤ H(A|B)` at every sandwiched Renyi order. -/
theorem conditionalSandwichedRenyiUpExtendedOrder_dataProcessing_discardRight
    (rho : MState (a × (b × c))) (alpha : RenyiOrder) :
    rho.conditionalSandwichedRenyiUpExtendedOrder alpha ≤
      conditionalSandwichedRenyiUpExtendedOrder
        (((CPTPOp.id (dIn := a)).prod (CPTPOp.traceOutRight b c)) rho)
        alpha := by
  exact conditionalSandwichedRenyiUpExtendedOrder_dataProcessing_conditioning
    rho (CPTPOp.traceOutRight b c) alpha

end MState
