/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy.MutualInformationDPI
public import QIT.Information.Renyi.RenyiDPI.ReferenceOrder
public import QIT.Information.Renyi.RenyiOrderParameter
public import QIT.Channels.Diamond

/-!
# Conditional sandwiched Renyi data processing on the conditioning system

This module proves the conditioning-system data-processing inequality from
Tomamichel2015FiniteResources, `cond.tex:268-284`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal
open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

namespace State

private theorem idChannel_applyState_eq (rho : State a) :
    (Channel.idChannel a).applyState rho = rho := by
  apply State.ext
  simp [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus]

private theorem sandwichedRenyiQ_real_smul_reference
    (rho : State a) {tau : CMatrix a} (htau : tau.PosSemidef)
    {scale : Real} (hscale : 0 < scale) (alpha : Real) (halpha : 0 < alpha) :
    sandwichedRenyiQ rho.matrix (scale • tau) rho.pos
        (Matrix.PosSemidef.smul htau hscale.le) alpha =
      scale ^ (1 - alpha) *
        sandwichedRenyiQ rho.matrix tau rho.pos htau alpha := by
  have hinner := sandwichedRenyiReferenceInner_psdTracePower_real_smul_reference
    rho htau hscale.le alpha
  have hfactor :
      (scale ^ ((1 - alpha) / (2 * alpha)) *
          scale ^ ((1 - alpha) / (2 * alpha))) ^ alpha =
        scale ^ (1 - alpha) := by
    rw [← Real.rpow_add hscale, ← Real.rpow_mul hscale.le]
    congr 1
    field_simp [halpha.ne']
    ring
  rw [sandwichedRenyiQ_eq_psdTracePower_referenceInner,
    sandwichedRenyiQ_eq_psdTracePower_referenceInner, hinner, hfactor]

private theorem sandwichedRenyiPSDReferenceE_real_smul_reference_of_lt_one
    (rho : State a) {tau : CMatrix a} (htau : tau.PosSemidef)
    {scale : Real} (hscale : 0 < scale) (alpha : Real)
    (halpha_pos : 0 < alpha) (halpha_lt_one : alpha < 1)
    (hQ : 0 < sandwichedRenyiQ rho.matrix tau rho.pos htau alpha) :
    sandwichedRenyiPSDReferenceE rho (scale • tau)
        (Matrix.PosSemidef.smul htau hscale.le) alpha =
      sandwichedRenyiPSDReferenceE rho tau htau alpha - log2 scale := by
  have hQscale := sandwichedRenyiQ_real_smul_reference
    rho htau hscale alpha halpha_pos
  have hQscale_pos :
      0 < sandwichedRenyiQ rho.matrix (scale • tau) rho.pos
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
    (rho : State a) {tau : CMatrix a} (htau : tau.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix tau)
    {scale : Real} (hscale : 0 < scale) (alpha : Real) (halpha : 1 < alpha) :
    sandwichedRenyiPSDReferenceE rho (scale • tau)
        (Matrix.PosSemidef.smul htau hscale.le) alpha =
      sandwichedRenyiPSDReferenceE rho tau htau alpha - log2 scale := by
  have hscaleSupport : Matrix.Supports rho.matrix (scale • tau) := by
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
    (sigma : State b) {delta : Real} (hdelta : delta ∈ Set.Ioo (0 : Real) 1) :
    ((1 - delta : Real) • identityTensorStateMatrix (a := a) sigma) <=
      identityTensorStateMatrix (a := a)
        (fullRankApproxMaximallyMixedStatePath sigma delta) := by
  letI : Nonempty b := sigma.nonempty
  have hside := smul_left_le_fullRankApproxStatePath_matrix_of_mem
    sigma (State.maximallyMixed b) hdelta
  rw [Matrix.le_iff] at hside ⊢
  have hone : (1 : CMatrix a).PosSemidef := Matrix.PosSemidef.one
  have hkron := hone.kronecker hside
  have heq :
      Matrix.kronecker (1 : CMatrix a)
          ((fullRankApproxStatePath sigma (State.maximallyMixed b) delta).matrix -
            (1 - delta) • sigma.matrix) =
        identityTensorStateMatrix (a := a)
            (fullRankApproxMaximallyMixedStatePath sigma delta) -
          (1 - delta) • identityTensorStateMatrix (a := a) sigma := by
    ext i j
    simp [identityTensorStateMatrix, fullRankApproxMaximallyMixedStatePath,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply]
    ring
  rw [← heq]
  exact hkron

/-- A full-rank side-reference source candidate is the negative
support-aware PSD-reference divergence. -/
theorem conditionalSandwichedRenyiUpSourceCandidate_eq_neg_referenceE
    (rho : State (Prod a b)) (sigma : State b) (hsigma : sigma.matrix.PosDef)
    (alpha : Real) (halpha_pos : 0 < alpha) (halpha_one : alpha ≠ 1) :
    rho.conditionalSandwichedRenyiUpSourceCandidate
        sigma hsigma alpha halpha_pos halpha_one =
      -sandwichedRenyiPSDReferenceE rho
        (identityTensorStateMatrix (a := a) sigma)
        (identityTensorStateMatrix_posSemidef_of_state (a := a) sigma) alpha := by
  by_cases halpha_lt_one : alpha < 1
  · rw [sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one _ _ halpha_lt_one]
    have hQpos : 0 < sandwichedRenyiQ rho.matrix
        (identityTensorStateMatrix (a := a) sigma) rho.pos
        (identityTensorStateMatrix_posSemidef_of_state (a := a) sigma) alpha :=
      sandwichedRenyiQ_pos_of_state_posDef_reference rho
        (identityTensorStateMatrix_posDef_of_posDef (a := a) sigma hsigma) alpha
    rw [sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
      rho (identityTensorStateMatrix_posSemidef_of_state (a := a) sigma)
      alpha hQpos.ne']
    unfold conditionalSandwichedRenyiUpSourceCandidate
      sandwichedRenyiPSDReferenceLowAlpha
    simp only [sandwichedRenyiQ_eq_psdTracePower_referenceInner]
    simp [psdTracePower, sandwichedRenyiReferenceInner, EReal.coe_neg]
  · have halpha_gt_one : 1 < alpha :=
      lt_of_le_of_ne (not_lt.mp halpha_lt_one) halpha_one.symm
    have href : (identityTensorStateMatrix (a := a) sigma).PosDef :=
      identityTensorStateMatrix_posDef_of_posDef (a := a) sigma hsigma
    have hsupport : Matrix.Supports rho.matrix
        (identityTensorStateMatrix (a := a) sigma) :=
      Matrix.Supports.of_right_posDef _ _ href
    rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha_gt_one,
      sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
        rho href.posSemidef alpha hsupport]
    unfold conditionalSandwichedRenyiUpSourceCandidate
      sandwichedRenyiPSDReferenceHighAlphaFinite
    simp [sandwichedRenyiReferenceInner]

/-- A channel on the conditioning system maps `I_A tensor sigma_B` exactly to
`I_A tensor N(sigma_B)`. -/
theorem conditioningChannel_map_identityTensorStateMatrix
    (N : Channel b c) (sigma : State b) :
    ((Channel.idChannel a).prod N).map
        (identityTensorStateMatrix (a := a) sigma) =
      identityTensorStateMatrix (a := a) (N.applyState sigma) := by
  rw [identityTensorStateMatrix, identityTensorStateMatrix,
    Channel.prod_map_kronecker]
  simp [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus]

/-- Every strict finite-order source candidate is bounded by the optimized
output entropy after a channel on the conditioning system. The output side
reference is allowed to be singular. -/
theorem conditionalSandwichedRenyiUpSourceCandidate_le_conditioning
    (rho : State (Prod a b)) (N : Channel b c)
    (alpha : Real) (halpha_half : 1 / 2 < alpha) (halpha_one : alpha ≠ 1)
    (sigma : State b) (hsigma : sigma.matrix.PosDef) :
      rho.conditionalSandwichedRenyiUpSourceCandidate sigma hsigma alpha
        (lt_trans (by norm_num) halpha_half) halpha_one <=
      (((Channel.idChannel a).prod N).applyState rho).conditionalSandwichedRenyiUpSource
        alpha (lt_trans (by norm_num) halpha_half) halpha_one := by
  let Phi : Channel (Prod a b) (Prod a c) := (Channel.idChannel a).prod N
  let omega : State (Prod a c) := Phi.applyState rho
  let tau : State c := N.applyState sigma
  let rin : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) sigma
  let rout : CMatrix (Prod a c) := identityTensorStateMatrix (a := a) tau
  let hrin : rin.PosSemidef :=
    identityTensorStateMatrix_posSemidef_of_state (a := a) sigma
  let hrout : rout.PosSemidef :=
    identityTensorStateMatrix_posSemidef_of_state (a := a) tau
  let candidate : Real :=
    rho.conditionalSandwichedRenyiUpSourceCandidate sigma hsigma alpha
      (lt_trans (by norm_num) halpha_half) halpha_one
  have hrin_pd : rin.PosDef := by
    exact identityTensorStateMatrix_posDef_of_posDef (a := a) sigma hsigma
  have hmap : Phi.map rin = rout := by
    simpa [Phi, rin, rout, tau] using
      conditioningChannel_map_identityTensorStateMatrix (a := a) N sigma
  have hrange : (1 / 2 <= alpha ∧ alpha < 1) ∨ 1 < alpha := by
    rcases lt_or_gt_of_ne halpha_one with halpha_lt | halpha_gt
    · exact Or.inl ⟨halpha_half.le, halpha_lt⟩
    · exact Or.inr halpha_gt
  have hDPI :=
    sandwichedRenyiPSDReferenceE_dataProcessing_channel_of_half_le_lt_one_or_one_lt
      rho hrin Phi alpha hrange
  have hDPI' :
      sandwichedRenyiPSDReferenceE omega rout hrout alpha <=
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
  have hdiv : sandwichedRenyiPSDReferenceE omega rout hrout alpha <=
      -(candidate : EReal) := hDPI'.trans_eq hinput
  letI : Nonempty c := tau.nonempty
  have hbdd := omega.conditionalSandwichedRenyiUpSourceValueSet_bddAbove
    halpha_half halpha_one
  have htend : Filter.Tendsto (fun delta : Real =>
      candidate + log2 (1 - delta))
      (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds candidate) := by
    simpa using tendsto_const_nhds.add log2_one_sub_tendsto_zero
  letI : Filter.NeBot (nhdsWithin (0 : Real) (Set.Ioo 0 1)) :=
    left_nhdsWithin_Ioo_neBot zero_lt_one
  refine le_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  have hscale : 0 < 1 - delta := sub_pos.mpr hdelta.2
  let path : State c := fullRankApproxMaximallyMixedStatePath tau delta
  have hpath_pd : path.matrix.PosDef := by
    simpa [path, fullRankApproxMaximallyMixedStatePath, fullRankApproxStatePath,
      hdelta] using fullRankApproxState_posDef_of_noise tau
        (State.maximallyMixed c) State.maximallyMixed_posDef
        hdelta.1.le hdelta.2.le hdelta.1
  let rpath : CMatrix (Prod a c) := identityTensorStateMatrix (a := a) path
  let hrpath : rpath.PosSemidef :=
    identityTensorStateMatrix_posSemidef_of_state (a := a) path
  have hscaled : ((1 - delta : Real) • rout).PosSemidef :=
    Matrix.PosSemidef.smul hrout hscale.le
  have horder : ((1 - delta : Real) • rout) <= rpath := by
    simpa [rout, rpath, path] using
      smul_identityTensorStateMatrix_le_fullRankApprox
        (a := a) tau hdelta
  have hanti : sandwichedRenyiPSDReferenceE omega rpath hrpath alpha <=
      sandwichedRenyiPSDReferenceE omega ((1 - delta : Real) • rout)
        hscaled alpha :=
    sandwichedRenyiPSDReferenceE_antitone_reference omega
      hscaled hrpath horder halpha_half.le
  have hscaleDiv :
      sandwichedRenyiPSDReferenceE omega ((1 - delta : Real) • rout)
          hscaled alpha =
        sandwichedRenyiPSDReferenceE omega rout hrout alpha -
          log2 (1 - delta) := by
    rcases lt_or_gt_of_ne halpha_one with halpha_lt | halpha_gt
    · have hQin : 0 < sandwichedRenyiQ rho.matrix rin rho.pos hrin alpha :=
        sandwichedRenyiQ_pos_of_state_posDef_reference rho hrin_pd alpha
      have hQmap :=
        sandwichedRenyiQ_dataProcessing_channel_reference_of_half_lt_lt_one
          rho hrin Phi alpha halpha_half halpha_lt
      have hQoutMap : 0 < sandwichedRenyiQ (Phi.applyState rho).matrix
          (Phi.map rin) (Phi.applyState rho).pos (Phi.mapsPositive rin hrin) alpha :=
        lt_of_lt_of_le hQin hQmap
      have hQout : 0 < sandwichedRenyiQ omega.matrix rout omega.pos hrout alpha := by
        simpa [omega, hmap] using hQoutMap
      exact sandwichedRenyiPSDReferenceE_real_smul_reference_of_lt_one
        omega hrout hscale alpha (lt_trans (by norm_num) halpha_half)
        halpha_lt hQout
    · have hinSupport : Matrix.Supports rho.matrix rin :=
        Matrix.Supports.of_right_posDef rho.matrix rin hrin_pd
      have houtSupportMap :=
        channel_applyState_supports_of_supports rho hrin Phi hinSupport
      have houtSupport : Matrix.Supports omega.matrix rout := by
        simpa [omega, hmap] using houtSupportMap
      exact sandwichedRenyiPSDReferenceE_real_smul_reference_of_one_lt
        omega hrout houtSupport hscale alpha halpha_gt
  have hchain : sandwichedRenyiPSDReferenceE omega rpath hrpath alpha <=
      ((-(candidate + log2 (1 - delta)) : Real) : EReal) := by
    calc
      sandwichedRenyiPSDReferenceE omega rpath hrpath alpha <=
          sandwichedRenyiPSDReferenceE omega ((1 - delta : Real) • rout)
            hscaled alpha := hanti
      _ = sandwichedRenyiPSDReferenceE omega rout hrout alpha -
          log2 (1 - delta) := hscaleDiv
      _ <= -(candidate : EReal) - log2 (1 - delta) :=
        by
          have hadd := add_le_add_right hdiv
            (-(log2 (1 - delta) : EReal))
          simpa [sub_eq_add_neg, add_comm] using hadd
      _ = ((-(candidate + log2 (1 - delta)) : Real) : EReal) := by
        have hreal : -candidate - log2 (1 - delta) =
            -(candidate + log2 (1 - delta)) := by ring
        simpa [EReal.coe_neg] using
          congrArg (fun x : Real => (x : EReal)) hreal
  have hbridgePath :=
    conditionalSandwichedRenyiUpSourceCandidate_eq_neg_referenceE
      omega path hpath_pd alpha (lt_trans (by norm_num) halpha_half) halpha_one
  have hcandidateE : ((candidate + log2 (1 - delta) : Real) : EReal) <=
      (omega.conditionalSandwichedRenyiUpSourceCandidate path hpath_pd alpha
        (lt_trans (by norm_num) halpha_half) halpha_one : EReal) := by
    rw [hbridgePath]
    have hcoeNeg : ((candidate + log2 (1 - delta) : Real) : EReal) =
        -(((-(candidate + log2 (1 - delta)) : Real) : EReal)) := by
      rw [← EReal.coe_neg]
      congr 1
      ring
    rw [hcoeNeg]
    exact EReal.neg_le_neg_iff.mpr hchain
  have hcandidate : candidate + log2 (1 - delta) <=
      omega.conditionalSandwichedRenyiUpSourceCandidate path hpath_pd alpha
        (lt_trans (by norm_num) halpha_half) halpha_one :=
    EReal.coe_le_coe_iff.mp hcandidateE
  exact hcandidate.trans <| le_csSup hbdd ⟨path, hpath_pd, rfl⟩

/-- The strict finite-order upward conditional sandwiched Renyi entropy cannot
decrease under a channel on the conditioning system. -/
theorem conditionalSandwichedRenyiUpSource_dataProcessing_conditioning
    (rho : State (Prod a b)) (N : Channel b c)
    (alpha : Real) (halpha_half : 1 / 2 < alpha) (halpha_one : alpha ≠ 1) :
    rho.conditionalSandwichedRenyiUpSource alpha
        (lt_trans (by norm_num) halpha_half) halpha_one <=
      (((Channel.idChannel a).prod N).applyState rho).conditionalSandwichedRenyiUpSource
        alpha (lt_trans (by norm_num) halpha_half) halpha_one := by
  letI : Nonempty b := by
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
    (rho : State (Prod a b)) (sigma : State b) (lam : Real)
    (N : Channel b c)
    (h : ConditionalMinEntropyFeasible (a := a) rho sigma lam) :
    ConditionalMinEntropyFeasible (a := a)
      (((Channel.idChannel a).prod N).applyState rho) (N.applyState sigma) lam := by
  let Phi : Channel (Prod a b) (Prod a c) := (Channel.idChannel a).prod N
  let rin : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) sigma
  let rout : CMatrix (Prod a c) :=
    identityTensorStateMatrix (a := a) (N.applyState sigma)
  let t : Real := Real.rpow 2 (-lam)
  have hmapFeas : Phi.map rho.matrix <= Phi.map ((t : Complex) • rin) := by
    apply Matrix.le_iff.mpr
    have hpos : (((t : Complex) • rin) - rho.matrix).PosSemidef := by
      simpa [t, rin, ConditionalMinEntropyFeasible, Matrix.le_iff] using h
    simpa [map_sub, map_smul] using Phi.mapsPositive _ hpos
  rw [ConditionalMinEntropyFeasible]
  have hmapRef : Phi.map rin = rout := by
    simpa [Phi, rin, rout] using
      conditioningChannel_map_identityTensorStateMatrix (a := a) N sigma
  have hfinal : Phi.map rho.matrix <= (t : Complex) • rout := by
    simpa [map_smul, hmapRef] using hmapFeas
  simpa [Phi, rin, rout, t] using hfinal

/-- Conditional min-entropy cannot decrease under a channel on the
conditioning system. -/
theorem conditionalMinEntropy_dataProcessing_conditioning
    (rho : State (Prod a b)) (N : Channel b c) :
    rho.conditionalMinEntropy <=
      (((Channel.idChannel a).prod N).applyState rho).conditionalMinEntropy := by
  letI : Nonempty b := by
    rcases rho.nonempty with ⟨z⟩
    exact ⟨z.2⟩
  rw [conditionalMinEntropy_eq, conditionalMinEntropy_eq]
  change sSup (rho.conditionalMinEntropyFeasibleExponentValueSet (a := a)) <=
    sSup ((((Channel.idChannel a).prod N).applyState rho)
      |>.conditionalMinEntropyFeasibleExponentValueSet (a := a))
  refine csSup_le
    (rho.conditionalMinEntropyFeasibleExponentValueSet_nonempty (a := a)) ?_
  intro lam hlam
  rcases hlam with ⟨sigma, hfeas⟩
  exact le_csSup
    ((((Channel.idChannel a).prod N).applyState rho)
      |>.conditionalMinEntropyFeasibleExponentValueSet_bddAbove (a := a))
    ⟨N.applyState sigma,
      ConditionalMinEntropyFeasible.conditioningChannel rho sigma lam N hfeas⟩

/-! ## Boundary order `alpha = 1 / 2` -/

/-- Conditional max-entropy cannot decrease under a channel on the
conditioning system. -/
theorem conditionalMaxEntropy_dataProcessing_conditioning
    (rho : State (Prod a b)) (N : Channel b c) :
    rho.conditionalMaxEntropy <=
      (((Channel.idChannel a).prod N).applyState rho).conditionalMaxEntropy := by
  let Phi : Channel (Prod a b) (Prod a c) := (Channel.idChannel a).prod N
  let omega : State (Prod a c) := Phi.applyState rho
  letI : Nonempty a := by
    rcases rho.nonempty with ⟨z⟩
    exact ⟨z.1⟩
  letI : Nonempty b := by
    rcases rho.nonempty with ⟨z⟩
    exact ⟨z.2⟩
  letI : Nonempty c := by
    exact (N.applyState (State.maximallyMixed b)).nonempty
  rw [conditionalMaxEntropy_eq_sSup_valueSet,
    conditionalMaxEntropy_eq_sSup_valueSet]
  refine csSup_le (rho.conditionalMaxEntropyValueSet_nonempty (a := a)) ?_
  intro x hx
  rcases hx with ⟨sigma, hsigma_pos, rfl⟩
  have hrefmap :
      Phi.applyState ((State.maximallyMixed a).prod sigma) =
        (State.maximallyMixed a).prod (N.applyState sigma) := by
    rw [show Phi = (Channel.idChannel a).prod N by rfl,
      Channel.applyState_prod, idChannel_applyState_eq]
  have hfid :
      rho.squaredFidelity ((State.maximallyMixed a).prod sigma) <=
        omega.squaredFidelity
          ((State.maximallyMixed a).prod (N.applyState sigma)) := by
    simpa [omega, hrefmap] using
      State.squaredFidelity_le_applyState_squaredFidelity
        Phi rho ((State.maximallyMixed a).prod sigma)
  have hexponent :
      rho.conditionalMaxEntropyExponentCandidate (a := a) sigma <=
        omega.conditionalMaxEntropyExponentCandidate (a := a) (N.applyState sigma) := by
    rw [conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity,
      conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity]
    exact mul_le_mul_of_nonneg_left hfid (Nat.cast_nonneg _)
  have hout_pos :
      0 < omega.conditionalMaxEntropyExponentCandidate (a := a) (N.applyState sigma) :=
    lt_of_lt_of_le hsigma_pos hexponent
  have hcandidate :
      rho.conditionalMaxEntropyCandidate (a := a) sigma <=
        omega.conditionalMaxEntropyCandidate (a := a) (N.applyState sigma) := by
    rw [conditionalMaxEntropyCandidate_eq_log2_exponentCandidate,
      conditionalMaxEntropyCandidate_eq_log2_exponentCandidate]
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hsigma_pos hexponent) (Real.log_nonneg (by norm_num))
  exact hcandidate.trans <| le_csSup
    (omega.conditionalMaxEntropyValueSet_bddAbove (a := a))
    ⟨N.applyState sigma, hout_pos, rfl⟩

/-! ## Boundary order `alpha = 1` -/

/-- Conditional von Neumann entropy cannot decrease under a channel on the
conditioning system. The proof is the trace-log relative-entropy DPI packaged
as mutual-information DPI. -/
theorem conditionalEntropy_dataProcessing_conditioning
    (rho : State (Prod a b)) (N : Channel b c) :
    rho.conditionalEntropy <=
      (((Channel.idChannel a).prod N).applyState rho).conditionalEntropy := by
  let omega : State (Prod a c) := ((Channel.idChannel a).prod N).applyState rho
  have hmi := mutualInformation_dataProcessing_local_channels_ge
    rho (Channel.idChannel a) N
  have hmarginal : omega.marginalA = rho.marginalA := by
    change (((Channel.idChannel a).prod N).applyState rho).marginalA =
      rho.marginalA
    rw [State.marginalA_applyState_prod, idChannel_applyState_eq]
  unfold QIT.mutualInformation at hmi
  rw [show ((Channel.idChannel a).prod N).applyState rho = omega by rfl,
    hmarginal] at hmi
  unfold conditionalEntropy
  linarith

/-! ## Full closed Renyi-order theorem -/

/-- A channel on the conditioning system cannot decrease the upward
sandwiched conditional Renyi entropy at any order in `[1/2, infinity]`.

This is Tomamichel2015FiniteResources, `cond.tex:268-284`. -/
theorem conditionalSandwichedRenyiUpExtendedOrder_dataProcessing_conditioning
    (rho : State (Prod a b)) (N : Channel b c) (alpha : RenyiOrder) :
    rho.conditionalSandwichedRenyiUpExtendedOrder alpha <=
      conditionalSandwichedRenyiUpExtendedOrder
        (((Channel.idChannel a).prod N).applyState rho) alpha := by
  obtain ⟨val, hval⟩ := alpha
  cases val with
  | top =>
      change rho.conditionalMinEntropy <=
        (((Channel.idChannel a).prod N).applyState rho).conditionalMinEntropy
      exact conditionalMinEntropy_dataProcessing_conditioning rho N
  | coe r =>
      have hr : 1 / 2 <= r := by exact_mod_cast hval
      change rho.conditionalSandwichedRenyiUpFiniteOrder r <=
        conditionalSandwichedRenyiUpFiniteOrder
          (((Channel.idChannel a).prod N).applyState rho) r
      by_cases hone : r = 1
      · subst r
        rw [conditionalSandwichedRenyiUpFiniteOrder_one,
          conditionalSandwichedRenyiUpFiniteOrder_one]
        exact conditionalEntropy_dataProcessing_conditioning rho N
      by_cases hhalf : r = (2 : Real)⁻¹
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
            (((Channel.idChannel a).prod N).applyState rho) hpos hone hhalf]
        exact conditionalSandwichedRenyiUpSource_dataProcessing_conditioning
          rho N r hstrict hone

/-- Discarding the right part of the conditioning register gives
`H(A|BC) <= H(A|B)` at every sandwiched Renyi order. -/
theorem conditionalSandwichedRenyiUpExtendedOrder_dataProcessing_discardRight
    (rho : State (Prod a (Prod b c))) (alpha : RenyiOrder) :
    rho.conditionalSandwichedRenyiUpExtendedOrder alpha <=
      conditionalSandwichedRenyiUpExtendedOrder
        (((Channel.idChannel a).prod (Channel.traceOutRight b c)).applyState rho)
        alpha := by
  exact conditionalSandwichedRenyiUpExtendedOrder_dataProcessing_conditioning
    rho (Channel.traceOutRight b c) alpha

end State

end

end QIT
