/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy.RelativeEntropyTraceLog
public import QIT.Information.Renyi.FrankLieb.DPI
public import QIT.Information.Renyi.IsometryImageMean
public import QIT.Information.Renyi.RenyiDPI.ConditionalConditioningSource
public import QIT.Information.Renyi.RenyiDPI.ConditionalMeasurementSource
public import QIT.Measurements.Coherent
public import QIT.Measurements.OverlapDomination

/-!
# Coherent-measurement entropic uncertainty comparison

This module follows the proof of Tomamichel's `eq:ucr-dual` comparison in
`apps.tex:202-214`.  The first group of lemmas records the positive-scalar
reference shift used in the final overlap-domination step.  The coherent
measurement comparison then uses the source Stinespring bridge from
`QIT.Measurements.Coherent`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal
open Matrix

namespace QIT

universe u v w z

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

namespace State

/-- Scaling a PSD reference by a positive real multiplies the sandwiched
`Q_alpha` functional by `scale^(1-alpha)`.

This is the scalar-reference identity used in Tomamichel's uncertainty proof
before taking logarithms. -/
theorem sandwichedRenyiQ_real_smul_reference_of_pos
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    {scale : Real} (hScale : 0 < scale) (alpha : Real) (hAlpha : 0 < alpha) :
    sandwichedRenyiQ rho.matrix (scale • sigma) rho.pos
        (Matrix.PosSemidef.smul hSigma hScale.le) alpha =
      scale ^ (1 - alpha) *
        sandwichedRenyiQ rho.matrix sigma rho.pos hSigma alpha := by
  have hPower :=
    sandwichedRenyiReferenceInner_psdTracePower_real_smul_reference
      rho hSigma hScale.le alpha
  have hFactor :
      (scale ^ ((1 - alpha) / (2 * alpha)) *
          scale ^ ((1 - alpha) / (2 * alpha))) ^ alpha =
        scale ^ (1 - alpha) := by
    have hMul :
        scale ^ ((1 - alpha) / (2 * alpha)) *
            scale ^ ((1 - alpha) / (2 * alpha)) =
          scale ^ (((1 - alpha) / (2 * alpha)) +
            ((1 - alpha) / (2 * alpha))) := by
      rw [Real.rpow_add hScale]
    rw [hMul, ← Real.rpow_mul hScale.le]
    congr 1
    field_simp [ne_of_gt hAlpha]
    ring
  rw [sandwichedRenyiQ_eq_psdTracePower_referenceInner,
    sandwichedRenyiQ_eq_psdTracePower_referenceInner]
  rw [hPower, hFactor]

/-- Finite low-order sandwiched Renyi divergence shifts by `-log2 scale`
when a positive-definite reference is multiplied by `scale`. -/
theorem sandwichedRenyiPSDReferenceLowAlpha_real_smul_reference
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    {scale : Real} (hScale : 0 < scale)
    (alpha : Real) (hAlpha : 0 < alpha) (hAlphaOne : alpha ≠ 1) :
    sandwichedRenyiPSDReferenceLowAlpha rho (scale • sigma)
        (Matrix.PosDef.smul hSigma hScale).posSemidef alpha =
      sandwichedRenyiPSDReferenceLowAlpha rho sigma hSigma.posSemidef alpha -
        log2 scale := by
  have hQ :
      0 < sandwichedRenyiQ rho.matrix sigma rho.pos hSigma.posSemidef alpha :=
    sandwichedRenyiQ_pos_of_state_posDef_reference rho hSigma alpha
  have hScalePower : 0 < scale ^ (1 - alpha) :=
    Real.rpow_pos_of_pos hScale _
  have hLogPower :
      log2 (scale ^ (1 - alpha)) = (1 - alpha) * log2 scale := by
    unfold log2
    rw [Real.log_rpow hScale]
    ring
  unfold sandwichedRenyiPSDReferenceLowAlpha
  rw [sandwichedRenyiQ_real_smul_reference_of_pos rho hSigma.posSemidef
    hScale alpha hAlpha]
  rw [log2_mul (ne_of_gt hScalePower) (ne_of_gt hQ), hLogPower]
  field_simp [hAlphaOne]
  ring

/-- Extended-real low-order branch version of positive scalar reference
scaling, requiring only that the reference is positive definite. -/
theorem sandwichedRenyiPSDReferenceLowAlphaE_real_smul_reference
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    {scale : Real} (hScale : 0 < scale)
    (alpha : Real) (hAlpha : 0 < alpha) (hAlphaOne : alpha ≠ 1) :
    sandwichedRenyiPSDReferenceLowAlphaE rho (scale • sigma)
        (Matrix.PosDef.smul hSigma hScale).posSemidef alpha =
      sandwichedRenyiPSDReferenceLowAlphaE rho sigma hSigma.posSemidef alpha -
        (log2 scale : EReal) := by
  have hQ :
      0 < sandwichedRenyiQ rho.matrix sigma rho.pos hSigma.posSemidef alpha :=
    sandwichedRenyiQ_pos_of_state_posDef_reference rho hSigma alpha
  have hQScaled :
      0 < sandwichedRenyiQ rho.matrix (scale • sigma) rho.pos
        (Matrix.PosDef.smul hSigma hScale).posSemidef alpha := by
    rw [sandwichedRenyiQ_real_smul_reference_of_pos rho hSigma.posSemidef
      hScale alpha hAlpha]
    positivity
  rw [sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
      rho (Matrix.PosDef.smul hSigma hScale).posSemidef alpha hQScaled.ne',
    sandwichedRenyiPSDReferenceLowAlphaE_eq_coe_of_Q_ne_zero
      rho hSigma.posSemidef alpha hQ.ne',
    sandwichedRenyiPSDReferenceLowAlpha_real_smul_reference
      rho hSigma hScale alpha hAlpha hAlphaOne]
  norm_cast

/-- High-order extended-real sandwiched Renyi divergence shifts by
`-log2 scale` for a positive-definite reference. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_real_smul_reference
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    {scale : Real} (hScale : 0 < scale)
    (alpha : Real) (hAlpha : 1 < alpha) :
    sandwichedRenyiPSDReferenceHighAlphaE rho (scale • sigma)
        (Matrix.PosDef.smul hSigma hScale).posSemidef alpha =
      sandwichedRenyiPSDReferenceHighAlphaE rho sigma hSigma.posSemidef alpha -
        (log2 scale : EReal) := by
  have hSupport : Matrix.Supports rho.matrix sigma :=
    Matrix.Supports.of_right_posDef rho.matrix sigma hSigma
  have hSupportScaled : Matrix.Supports rho.matrix (scale • sigma) :=
    Matrix.Supports.of_right_posDef rho.matrix (scale • sigma)
      (Matrix.PosDef.smul hSigma hScale)
  simp only [sandwichedRenyiPSDReferenceHighAlphaE, hSupport, hSupportScaled]
  rw [sandwichedRenyiPSDReferenceHighAlphaFinite_real_smul_reference
    rho hSigma hScale alpha hAlpha]
  norm_cast

/-- Unified finite-order scalar-reference shift for the source-facing
sandwiched Renyi divergence, including the Umegaki order `alpha = 1`. -/
theorem sandwichedRenyiPSDReferenceE_real_smul_reference
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    {scale : Real} (hScale : 0 < scale)
    (alpha : Real) (hHalf : 1 / 2 ≤ alpha) :
    sandwichedRenyiPSDReferenceE rho (scale • sigma)
        (Matrix.PosDef.smul hSigma hScale).posSemidef alpha =
      sandwichedRenyiPSDReferenceE rho sigma hSigma.posSemidef alpha -
        (log2 scale : EReal) := by
  by_cases hOne : alpha = 1
  · subst alpha
    rw [sandwichedRenyiPSDReferenceE_eq_traceLogE_of_eq_one
        rho (Matrix.PosDef.smul hSigma hScale).posSemidef rfl,
      sandwichedRenyiPSDReferenceE_eq_traceLogE_of_eq_one
        rho hSigma.posSemidef rfl]
    exact relativeEntropyPSDReferenceTraceLogE_real_smul_reference
      rho hSigma hScale
  · rcases lt_or_gt_of_ne hOne with hLow | hHigh
    · have hPos : 0 < alpha := lt_of_lt_of_le (by norm_num) hHalf
      rw [sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one
          rho (Matrix.PosDef.smul hSigma hScale).posSemidef hLow,
        sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one
          rho hSigma.posSemidef hLow]
      exact sandwichedRenyiPSDReferenceLowAlphaE_real_smul_reference
        rho hSigma hScale alpha hPos hOne
    · rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt
          rho (Matrix.PosDef.smul hSigma hScale).posSemidef hHigh,
        sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt
          rho hSigma.posSemidef hHigh]
      exact sandwichedRenyiPSDReferenceHighAlphaE_real_smul_reference
        rho hSigma hScale alpha hHigh

end State

namespace ProjectiveMeasurement.IsRankOne

variable {x : Type u} {y : Type v} {a : Type w} {b : Type z}
variable [Fintype x] [DecidableEq x]
variable [Fintype y] [DecidableEq y]
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable {X : ProjectiveMeasurement x a} {Y : ProjectiveMeasurement y a}

private theorem ofEquiv_compression_eq_reindex_symm
    {p q : Type*} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q] (e : p ≃ q) (M : CMatrix q) :
    Matrix.conjTranspose (ReferenceIsometry.ofEquiv e).matrix * M *
        (ReferenceIsometry.ofEquiv e).matrix =
      Matrix.reindex e.symm e.symm M := by
  classical
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (e j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (e i)]
    · simp [ReferenceIsometry.ofEquiv, Matrix.reindex_apply]
    · intro k _ hk
      have hki : k ≠ e i := by simpa [eq_comm] using hk
      simp [ReferenceIsometry.ofEquiv, Matrix.conjTranspose_apply, hki]
    · simp
  · intro k _ hk
    simp [ReferenceIsometry.ofEquiv, hk]
  · simp

/-- The coherent measurement isometry, with the copied outcome and side
information grouped as the conditioning register `Y'B`.

This is the register association used in `apps.tex:202-214`. -/
def coherentGroupedSideIsometry (hY : Y.IsRankOne) :
    ReferenceIsometry (Prod a b) (Prod y (Prod y b)) :=
  (ReferenceIsometry.ofEquiv (Equiv.prodAssoc y y b)).comp
    hY.coherentSideIsometry

@[simp]
theorem coherentGroupedSideIsometry_matrix
    (hY : Y.IsRankOne) (out : Prod y (Prod y b)) (input : Prod a b) :
    hY.coherentGroupedSideIsometry.matrix out input =
      hY.coherentSideIsometry.matrix ((out.1, out.2.1), out.2.2) input := by
  classical
  let e : Prod (Prod y y) b ≃ Prod y (Prod y b) := Equiv.prodAssoc y y b
  let mid : Prod (Prod y y) b := e.symm out
  change
    (∑ q, (ReferenceIsometry.ofEquiv e).matrix out q *
      hY.coherentSideIsometry.matrix q input) = _
  rw [Finset.sum_eq_single mid]
  · simp [e, mid, ReferenceIsometry.ofEquiv]
  · intro q _ hq
    have hout : out ≠ e q := by
      intro heq
      apply hq
      apply e.injective
      simpa [mid] using heq.symm
    simp [ReferenceIsometry.ofEquiv, hout]
  · simp

/-- The coherent `Y | Y'B` state from `apps.tex:200-203`. -/
def coherentMeasurementState (hY : Y.IsRankOne) (rho : State (Prod a b)) :
    State (Prod y (Prod y b)) :=
  (Channel.ofReferenceIsometry hY.coherentGroupedSideIsometry).applyState rho

/-- The grouped coherent state is the coherent measurement channel on the
first register, tensored with the identity on side information, followed by
the source register association `Y x (Y' x B)`. -/
theorem coherentMeasurementState_eq_reindex_prod
    (hY : Y.IsRankOne) (rho : State (Prod a b)) :
    hY.coherentMeasurementState rho =
      ((hY.coherentChannel.prod (Channel.idChannel b)).applyState rho).reindex
        (Equiv.prodAssoc y y b) := by
  classical
  apply State.ext
  ext out out'
  rw [State.reindex_matrix]
  change MatrixMap.ofReferenceIsometry hY.coherentGroupedSideIsometry rho.matrix
      out out' =
    MatrixMap.kron hY.coherentChannel.map (Channel.idChannel b).map rho.matrix
      ((out.1, out.2.1), out.2.2) ((out'.1, out'.2.1), out'.2.2)
  rw [MatrixMap.kron_idChannel_apply_slice]
  rcases out with ⟨i, j, k⟩
  rcases out' with ⟨i', j', k'⟩
  by_cases hij : i = j <;> by_cases hi'j' : i' = j'
  · subst j
    subst j'
    simp [MatrixMap.ofReferenceIsometry_apply, Matrix.mul_apply,
      coherentGroupedSideIsometry_matrix, coherentSideIsometry_matrix,
      coherentChannel_map_apply, coherentBracket, Fintype.sum_prod_type,
      Finset.sum_mul, Finset.sum_ite_eq, eq_comm, mul_assoc]
    simp [apply_ite, map_zero, Finset.sum_ite_eq, eq_comm]
    rw [Finset.sum_comm]
  · simp [MatrixMap.ofReferenceIsometry_apply, Matrix.mul_apply,
      coherentGroupedSideIsometry_matrix, coherentSideIsometry_matrix,
      coherentChannel_map_apply, hij, hi'j']
  · simp [MatrixMap.ofReferenceIsometry_apply, Matrix.mul_apply,
      coherentGroupedSideIsometry_matrix, coherentSideIsometry_matrix,
      coherentChannel_map_apply, hij, hi'j']
  · simp [MatrixMap.ofReferenceIsometry_apply, Matrix.mul_apply,
      coherentGroupedSideIsometry_matrix, coherentSideIsometry_matrix,
      coherentChannel_map_apply, hij, hi'j']

/-- Tracing both coherent outcome registers leaves the original side
information marginal. -/
theorem coherentMeasurementState_marginalB_marginalB
    (hY : Y.IsRankOne) (rho : State (Prod a b)) :
    (hY.coherentMeasurementState rho).marginalB.marginalB = rho.marginalB := by
  let out := (hY.coherentChannel.prod (Channel.idChannel b)).applyState rho
  have hassoc :
      (out.reindex (Equiv.prodAssoc y y b)).marginalB.marginalB =
        out.marginalB := by
    apply State.ext
    ext k k'
    simp [State.reindex, State.marginalB, partialTraceA,
      Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  calc
    (hY.coherentMeasurementState rho).marginalB.marginalB =
        (out.reindex (Equiv.prodAssoc y y b)).marginalB.marginalB := by
      rw [hY.coherentMeasurementState_eq_reindex_prod]
    _ = out.marginalB := hassoc
    _ = rho.marginalB := by
      exact State.marginalB_applyState_prod_id rho hY.coherentChannel

/-- Measuring the first register leaves the side-information marginal
unchanged. -/
theorem measureSubsystemState_marginalB
    (X : ProjectiveMeasurement x a) (rho : State (Prod a b)) :
    (measureSubsystemState X.toPOVM rho).marginalB = rho.marginalB := by
  simpa [measureSubsystemState] using
    State.marginalB_applyState_prod_id rho (Channel.measure X.toPOVM)

/-- Compressing `I_Y tensor sigma_{Y'B}` through the grouped coherent
isometry gives the source pullback `U_Y^*(I_Y tensor sigma)U_Y`. -/
theorem coherentGroupedSideIsometry_compression_identityTensor
    (hY : Y.IsRankOne) (sigma : State (Prod y b)) :
    Matrix.conjTranspose hY.coherentGroupedSideIsometry.matrix *
          State.identityTensorStateMatrix (a := y) sigma *
          hY.coherentGroupedSideIsometry.matrix =
      hY.coherentPullback sigma.matrix := by
  let e : Prod (Prod y y) b ≃ Prod y (Prod y b) := Equiv.prodAssoc y y b
  let P := (ReferenceIsometry.ofEquiv e).matrix
  let V : Matrix (Prod (Prod y y) b) (Prod a b) Complex :=
    (hY.coherentSideIsometry (b := b)).matrix
  let T := State.identityTensorStateMatrix (a := y) sigma
  have hreindex : Matrix.conjTranspose P * T * P =
      copiedIdentityTensor (y := y) sigma.matrix := by
    simpa [P, T, e, ProjectiveMeasurement.IsRankOne.copiedIdentityTensor] using
      ofEquiv_compression_eq_reindex_symm e T
  change Matrix.conjTranspose (P * V) * T * (P * V) =
    Matrix.conjTranspose V * copiedIdentityTensor (y := y) sigma.matrix * V
  rw [Matrix.conjTranspose_mul]
  calc
    (Matrix.conjTranspose V * Matrix.conjTranspose P) * T * (P * V) =
        Matrix.conjTranspose V * (Matrix.conjTranspose P * T * P) * V := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.conjTranspose V * copiedIdentityTensor (y := y) sigma.matrix * V := by
      rw [hreindex]

private theorem referenceIsometry_compression_mono
    {p q : Type*} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q] (V : ReferenceIsometry p q)
    {M N : CMatrix q} (hMN : M <= N) :
    Matrix.conjTranspose V.matrix * M * V.matrix <=
      Matrix.conjTranspose V.matrix * N * V.matrix := by
  rw [Matrix.le_iff] at hMN ⊢
  have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hMN V.matrix
  simpa [Matrix.mul_sub, Matrix.sub_mul] using h

private theorem referenceIsometry_compression_ofReferenceIsometry_applyState
    {p q : Type*} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q] (V : ReferenceIsometry p q)
    (rho : State p) :
    Matrix.conjTranspose V.matrix *
        ((Channel.ofReferenceIsometry V).applyState rho).matrix * V.matrix =
      rho.matrix := by
  simp only [Channel.applyState, Channel.ofReferenceIsometry_map,
    MatrixMap.ofReferenceIsometry_apply]
  calc
    Matrix.conjTranspose V.matrix *
          (V.matrix * rho.matrix * Matrix.conjTranspose V.matrix) * V.matrix =
        (Matrix.conjTranspose V.matrix * V.matrix) * rho.matrix *
          (Matrix.conjTranspose V.matrix * V.matrix) := by
            simp only [Matrix.mul_assoc]
    _ = rho.matrix := by rw [V.isometry, Matrix.one_mul, Matrix.mul_one]

/-- The diagonal copied-outcome blocks of a `Y'B` state sum to its `B`
marginal. This is the final equality in `apps.tex:212`. -/
theorem sum_copiedOutcomeBlock_eq_marginalB
    (sigma : State (Prod y b)) :
    (Finset.univ.sum fun outcome => copiedOutcomeBlock sigma.matrix outcome) =
      sigma.marginalB.matrix := by
  apply Matrix.ext
  intro i j
  simp [Matrix.sum_apply, copiedOutcomeBlock, State.marginalB_matrix, partialTraceA]

/-- The measured coherent pullback is dominated by the overlap-scaled
conditional reference, exactly as in `apps.tex:210-213`.

The right-hand side uses the actual `B` marginal of the supplied `Y'B`
reference. Positivity of every copied block follows by principal compression,
so no independent block-positivity certificate is exposed. -/
theorem measureCoherentPullback_le_overlap_identityTensorMarginal
    (hX : X.IsRankOne) (hY : Y.IsRankOne) (sigma : State (Prod y b)) :
    MatrixMap.kron (Channel.measure X.toPOVM).map (Channel.idChannel b).map
        (hY.coherentPullback sigma.matrix) <=
      (X.rankOneTraceOverlap Y : Real) •
        State.identityTensorStateMatrix (a := x) sigma.marginalB := by
  have hblock : forall outcome,
      (copiedOutcomeBlock sigma.matrix outcome).PosSemidef := by
    intro outcome
    simpa [copiedOutcomeBlock] using
      sigma.pos.submatrix (fun side : b => (outcome, side))
  rw [hY.measureCoherentPullback_rankOne hX]
  calc
    (Finset.univ.sum fun measured => Finset.univ.sum fun outcome =>
        (hX.vector measured).overlapSq (hY.vector outcome) •
          Matrix.kronecker (Matrix.single measured measured (1 : Complex))
            (copiedOutcomeBlock sigma.matrix outcome)) <=
        (X.rankOneTraceOverlap Y : Real) •
          Matrix.kronecker (1 : CMatrix x)
            (Finset.univ.sum fun outcome =>
              copiedOutcomeBlock sigma.matrix outcome) :=
      X.overlap_domination_le_rankOne Y hX hY _ hblock
    _ = (X.rankOneTraceOverlap Y : Real) •
        State.identityTensorStateMatrix (a := x) sigma.marginalB := by
      rw [sum_copiedOutcomeBlock_eq_marginalB sigma]
      rfl

/-- Every full-rank `Y'B` reference candidate in the coherent state is
bounded by the corresponding `B`-marginal candidate after measuring `X`,
with the overlap loss from `apps.tex:208-214`. -/
theorem conditionalSandwichedRenyiUpSourceCandidate_coherentMeasurement_sub_log2_le
    (hX : X.IsRankOne) (hY : Y.IsRankOne) (rho : State (Prod a b))
    (sigma : State (Prod y b)) (hsigma : sigma.matrix.PosDef)
    (alpha : Real) (halpha_pos : 0 < alpha) (halpha_one : alpha ≠ 1)
    (halpha_half : 1 / 2 <= alpha) :
    (hY.coherentMeasurementState rho).conditionalSandwichedRenyiUpSourceCandidate
          sigma hsigma alpha halpha_pos halpha_one -
        log2 (X.rankOneTraceOverlap Y) <=
      (measureSubsystemState X.toPOVM rho).conditionalSandwichedRenyiUpSourceCandidate
        sigma.marginalB (sigma.marginalB_posDef_of_posDef hsigma)
        alpha halpha_pos halpha_one := by
  letI : Nonempty a := by
    rcases rho.nonempty with ⟨i, _⟩
    exact ⟨i⟩
  let coherent := hY.coherentMeasurementState rho
  let measured := measureSubsystemState X.toPOVM rho
  let Phi : Channel (Prod a b) (Prod x b) :=
    (Channel.measure X.toPOVM).prod (Channel.idChannel b)
  let rin : CMatrix (Prod a b) := hY.coherentPullback sigma.matrix
  let rout : CMatrix (Prod x b) :=
    State.identityTensorStateMatrix (a := x) sigma.marginalB
  let c : Real := X.rankOneTraceOverlap Y
  have hc : 0 < c := by
    exact hX.rankOneTraceOverlap_pos Y
  have hsigmaB : sigma.marginalB.matrix.PosDef :=
    sigma.marginalB_posDef_of_posDef hsigma
  have hrin : rin.PosDef := by
    exact hY.coherentPullback_posDef hsigma
  have hrout : rout.PosDef := by
    exact State.identityTensorStateMatrix_posDef_of_posDef
      (a := x) sigma.marginalB hsigmaB
  have hambient :
      (State.identityTensorStateMatrix (a := y) sigma).PosDef :=
    State.identityTensorStateMatrix_posDef_of_posDef (a := y) sigma hsigma
  have himage :
      coherent.sandwichedRenyiPSDReferenceE
          (State.identityTensorStateMatrix (a := y) sigma)
          hambient.posSemidef alpha >=
        rho.sandwichedRenyiPSDReferenceE rin hrin.posSemidef alpha := by
    have h := State.sandwichedRenyiPSDReferenceE_isometryImage_ge_compression
      rho hY.coherentGroupedSideIsometry hambient alpha halpha_half
    simpa [coherent, coherentMeasurementState, rin,
      hY.coherentGroupedSideIsometry_compression_identityTensor sigma] using h
  have hrange : (1 / 2 <= alpha ∧ alpha < 1) ∨ 1 < alpha := by
    rcases lt_or_gt_of_ne halpha_one with hlt | hgt
    · exact Or.inl ⟨halpha_half, hlt⟩
    · exact Or.inr hgt
  have hdpi :
      measured.sandwichedRenyiPSDReferenceE
          (Phi.map rin) (Phi.mapsPositive rin hrin.posSemidef) alpha <=
        rho.sandwichedRenyiPSDReferenceE rin hrin.posSemidef alpha := by
    have h :=
      State.sandwichedRenyiPSDReferenceE_dataProcessing_channel_ge_of_half_le_lt_one_or_one_lt
        rho hrin.posSemidef Phi alpha hrange
    simpa [measured, Phi, measureSubsystemState] using h
  have hdom : Phi.map rin <= c • rout := by
    simpa [Phi, rin, rout, c] using
      hX.measureCoherentPullback_le_overlap_identityTensorMarginal hY sigma
  have hscaled : (c • rout).PosDef :=
    Matrix.PosDef.smul hrout hc
  have hreference :
      measured.sandwichedRenyiPSDReferenceE (c • rout)
          hscaled.posSemidef alpha <=
        measured.sandwichedRenyiPSDReferenceE
          (Phi.map rin) (Phi.mapsPositive rin hrin.posSemidef) alpha :=
    State.sandwichedRenyiPSDReferenceE_antitone_reference measured
      (Phi.mapsPositive rin hrin.posSemidef) hscaled.posSemidef hdom halpha_half
  have hchain :
      measured.sandwichedRenyiPSDReferenceE (c • rout)
          hscaled.posSemidef alpha <=
        coherent.sandwichedRenyiPSDReferenceE
          (State.identityTensorStateMatrix (a := y) sigma)
          hambient.posSemidef alpha :=
    hreference.trans (hdpi.trans himage)
  have hscale :
      measured.sandwichedRenyiPSDReferenceE (c • rout)
          hscaled.posSemidef alpha =
        measured.sandwichedRenyiPSDReferenceE rout hrout.posSemidef alpha -
          (log2 c : EReal) := by
    exact State.sandwichedRenyiPSDReferenceE_real_smul_reference
      measured hrout hc alpha halpha_half
  have hcoherent :=
    State.conditionalSandwichedRenyiUpSourceCandidate_eq_neg_referenceE
      coherent sigma hsigma alpha halpha_pos halpha_one
  have hmeasured :=
    State.conditionalSandwichedRenyiUpSourceCandidate_eq_neg_referenceE
      measured sigma.marginalB hsigmaB alpha halpha_pos halpha_one
  have hcoherentDiv :
      coherent.sandwichedRenyiPSDReferenceE
          (State.identityTensorStateMatrix (a := y) sigma)
          hambient.posSemidef alpha =
        -(coherent.conditionalSandwichedRenyiUpSourceCandidate
          sigma hsigma alpha halpha_pos halpha_one : EReal) := by
    rw [hcoherent]
    simp
  have hmeasuredDiv :
      measured.sandwichedRenyiPSDReferenceE rout hrout.posSemidef alpha =
        -(measured.conditionalSandwichedRenyiUpSourceCandidate
          sigma.marginalB hsigmaB alpha halpha_pos halpha_one : EReal) := by
    rw [hmeasured]
    simp [rout]
  rw [hscale, hmeasuredDiv, hcoherentDiv] at hchain
  have hreal :
      -(measured.conditionalSandwichedRenyiUpSourceCandidate
          sigma.marginalB hsigmaB alpha halpha_pos halpha_one) - log2 c <=
        -(coherent.conditionalSandwichedRenyiUpSourceCandidate
          sigma hsigma alpha halpha_pos halpha_one) := by
    exact_mod_cast hchain
  dsimp [coherent, measured, c] at hreal ⊢
  linarith

/-- Tomamichel's `eq:ucr-dual` comparison on the strict finite-order
interior, obtained by taking the supremum of the candidate inequality above. -/
theorem conditionalSandwichedRenyiUpSource_coherentMeasurement_sub_log2_le
    (hX : X.IsRankOne) (hY : Y.IsRankOne) (rho : State (Prod a b))
    (alpha : Real) (halpha_half : 1 / 2 < alpha) (halpha_one : alpha ≠ 1) :
    (hY.coherentMeasurementState rho).conditionalSandwichedRenyiUpSource
          alpha (lt_trans (by norm_num) halpha_half) halpha_one -
        log2 (X.rankOneTraceOverlap Y) <=
      (measureSubsystemState X.toPOVM rho).conditionalSandwichedRenyiUpSource
        alpha (lt_trans (by norm_num) halpha_half) halpha_one := by
  let coherent := hY.coherentMeasurementState rho
  let measured := measureSubsystemState X.toPOVM rho
  let hpos : 0 < alpha := lt_trans (by norm_num) halpha_half
  let S := coherent.conditionalSandwichedRenyiUpSourceValueSet
    alpha hpos halpha_one
  let T := measured.conditionalSandwichedRenyiUpSourceValueSet
    alpha hpos halpha_one
  letI : Nonempty (Prod y b) := by
    rcases coherent.nonempty with ⟨_, side⟩
    exact ⟨side⟩
  letI : Nonempty b := by
    rcases rho.nonempty with ⟨_, side⟩
    exact ⟨side⟩
  have hS : S.Nonempty := by
    exact coherent.conditionalSandwichedRenyiUpSourceValueSet_nonempty
      alpha hpos halpha_one
  have hTbdd : BddAbove T := by
    exact measured.conditionalSandwichedRenyiUpSourceValueSet_bddAbove
      halpha_half halpha_one
  have hpoint : ∀ z, z ∈ S →
      z - log2 (X.rankOneTraceOverlap Y) <= sSup T := by
    intro z hz
    rcases hz with ⟨sigma, hsigma, rfl⟩
    have hcand :=
      hX.conditionalSandwichedRenyiUpSourceCandidate_coherentMeasurement_sub_log2_le
        hY rho sigma hsigma alpha hpos halpha_one halpha_half.le
    have hmember :
        measured.conditionalSandwichedRenyiUpSourceCandidate
            sigma.marginalB (sigma.marginalB_posDef_of_posDef hsigma)
            alpha hpos halpha_one ∈ T := by
      exact ⟨sigma.marginalB, sigma.marginalB_posDef_of_posDef hsigma, rfl⟩
    exact hcand.trans (le_csSup hTbdd hmember)
  change sSup S - log2 (X.rankOneTraceOverlap Y) <= sSup T
  rw [sub_le_iff_le_add]
  apply csSup_le hS
  intro z hz
  have hz' := hpoint z hz
  linarith

/-- The Umegaki (`alpha = 1`) endpoint of Tomamichel's coherent-measurement
comparison.  The proof follows `apps.tex:202-214`: isometry compression,
measurement DPI, overlap domination, reference antitonicity, and the
support-aware canonical trace-log identity. -/
theorem conditionalEntropy_coherentMeasurement_sub_log2_le
    (hX : X.IsRankOne) (hY : Y.IsRankOne) (rho : State (Prod a b)) :
    (hY.coherentMeasurementState rho).conditionalEntropy -
        log2 (X.rankOneTraceOverlap Y) <=
      (measureSubsystemState X.toPOVM rho).conditionalEntropy := by
  letI : Nonempty a := by
    rcases rho.nonempty with ⟨input, _side⟩
    exact ⟨input⟩
  let coherent := hY.coherentMeasurementState rho
  let measured := measureSubsystemState X.toPOVM rho
  let sigma := coherent.marginalB
  let V := hY.coherentGroupedSideIsometry (b := b)
  let Phi : Channel (Prod a b) (Prod x b) :=
    (Channel.measure X.toPOVM).prod (Channel.idChannel b)
  let ambient : CMatrix (Prod y (Prod y b)) :=
    State.identityTensorStateMatrix (a := y) sigma
  let rin : CMatrix (Prod a b) := hY.coherentPullback sigma.matrix
  let rout : CMatrix (Prod x b) :=
    State.identityTensorStateMatrix (a := x) sigma.marginalB
  let c : Real := X.rankOneTraceOverlap Y
  have hc : 0 < c := hX.rankOneTraceOverlap_pos Y
  have hambient : ambient.PosSemidef :=
    State.identityTensorStateMatrix_posSemidef_of_state (a := y) sigma
  have hsupport : Matrix.Supports coherent.matrix ambient := by
    simpa [coherent, sigma, ambient, State.identityTensorStateMatrix] using
      State.matrix_supports_identityTensor_marginalB coherent
  have hrin : rin.PosSemidef := hY.coherentPullback_posSemidef sigma.pos
  have hrout : rout.PosSemidef :=
    State.identityTensorStateMatrix_posSemidef_of_state (a := x) sigma.marginalB
  have himage :
      State.relativeEntropyPSDReferenceTraceLogE coherent ambient hambient >=
        State.relativeEntropyPSDReferenceTraceLogE rho rin hrin := by
    have h :=
      State.relativeEntropyPSDReferenceTraceLogE_isometryImage_ge_compression
        rho V hambient hsupport
    simpa [V, coherent, coherentMeasurementState, ambient, rin,
      hY.coherentGroupedSideIsometry_compression_identityTensor sigma] using h
  have hdpi :
      State.relativeEntropyPSDReferenceTraceLogE measured
          (Phi.map rin) (Phi.mapsPositive rin hrin) <=
        State.relativeEntropyPSDReferenceTraceLogE rho rin hrin := by
    have h :=
      State.relativeEntropyPSDReferenceTraceLogE_dataProcessing_channel_ge
        rho hrin Phi
    simpa [measured, Phi, measureSubsystemState] using h
  have hdom : Phi.map rin <= c • rout := by
    simpa [Phi, rin, rout, c] using
      hX.measureCoherentPullback_le_overlap_identityTensorMarginal hY sigma
  have hscaled : (c • rout).PosSemidef :=
    Matrix.PosSemidef.smul hrout hc.le
  have hreference :
      State.relativeEntropyPSDReferenceTraceLogE measured (c • rout) hscaled <=
        State.relativeEntropyPSDReferenceTraceLogE measured
          (Phi.map rin) (Phi.mapsPositive rin hrin) :=
    State.relativeEntropyPSDReferenceTraceLogE_antitone_reference measured
      (Phi.mapsPositive rin hrin) hscaled hdom
  have hchain :
      State.relativeEntropyPSDReferenceTraceLogE measured (c • rout) hscaled <=
        State.relativeEntropyPSDReferenceTraceLogE coherent ambient hambient :=
    hreference.trans (hdpi.trans himage)
  have hsigmaB : sigma.marginalB = rho.marginalB := by
    simpa [sigma, coherent] using
      hY.coherentMeasurementState_marginalB_marginalB rho
  have hmeasuredB : measured.marginalB = rho.marginalB := by
    simpa [measured] using measureSubsystemState_marginalB X rho
  have hsides : sigma.marginalB = measured.marginalB :=
    hsigmaB.trans hmeasuredB.symm
  have hmeasuredDiv :
      State.relativeEntropyPSDReferenceTraceLogE measured (c • rout) hscaled =
        (-measured.conditionalEntropy - log2 c : EReal) := by
    simpa [rout, hsides] using
      State.relativeEntropyPSDReferenceTraceLogE_real_smul_identityTensor_marginalB_eq
        measured hc
  have hcoherentDiv :
      State.relativeEntropyPSDReferenceTraceLogE coherent ambient hambient =
        (-coherent.conditionalEntropy : EReal) := by
    have h :=
      State.relativeEntropyPSDReferenceTraceLogE_real_smul_identityTensor_marginalB_eq
        coherent (scale := 1) (by norm_num)
    simpa [ambient, sigma, log2] using h
  rw [hmeasuredDiv, hcoherentDiv] at hchain
  have hreal :
      -measured.conditionalEntropy - log2 c <= -coherent.conditionalEntropy := by
    exact_mod_cast hchain
  dsimp [coherent, measured, c] at hreal ⊢
  linarith

/-- The closed finite endpoint `alpha = 1/2` of the coherent-measurement
comparison.  The source entropy is the conditional max-entropy here. -/
theorem conditionalMaxEntropy_coherentMeasurement_sub_log2_le
    (hX : X.IsRankOne) (hY : Y.IsRankOne) (rho : State (Prod a b)) :
    (hY.coherentMeasurementState rho).conditionalMaxEntropy -
        log2 (X.rankOneTraceOverlap Y) <=
      (measureSubsystemState X.toPOVM rho).conditionalMaxEntropy := by
  let coherent := hY.coherentMeasurementState rho
  let measured := measureSubsystemState X.toPOVM rho
  let S := coherent.conditionalSandwichedRenyiUpSourceValueSet
    (1 / 2 : Real) (by norm_num) (by norm_num)
  letI : Nonempty (Prod y b) := by
    rcases coherent.nonempty with ⟨_, side⟩
    exact ⟨side⟩
  have hS : S.Nonempty := by
    exact coherent.conditionalSandwichedRenyiUpSourceValueSet_nonempty
      (1 / 2 : Real) (by norm_num) (by norm_num)
  rw [← State.conditionalSandwichedRenyiUpSource_half_eq_conditionalMaxEntropy
    coherent]
  change sSup S - log2 (X.rankOneTraceOverlap Y) <=
    measured.conditionalMaxEntropy
  rw [sub_le_iff_le_add]
  apply csSup_le hS
  intro z hz
  rcases hz with ⟨sigma, hsigma, rfl⟩
  have hcand :=
    hX.conditionalSandwichedRenyiUpSourceCandidate_coherentMeasurement_sub_log2_le
      hY rho sigma hsigma (1 / 2 : Real) (by norm_num) (by norm_num) (by norm_num)
  have htarget := State.sandwichedUpSourceCandidate_half_le_conditionalMaxEntropy
    measured sigma.marginalB (sigma.marginalB_posDef_of_posDef hsigma)
  have hcand' :
      coherent.conditionalSandwichedRenyiUpSourceCandidate
            sigma hsigma (1 / 2 : Real) (by norm_num) (by norm_num) -
          log2 (X.rankOneTraceOverlap Y) <=
        measured.conditionalSandwichedRenyiUpSourceCandidate
          sigma.marginalB (sigma.marginalB_posDef_of_posDef hsigma)
          (1 / 2 : Real) (by norm_num) (by norm_num) := by
    simpa [coherent, measured] using hcand
  linarith

/-- A coherent-measurement conditional-min witness gives a measured witness
with the overlap penalty subtracted from its exponent.  This is the
`alpha = infinity` instance of the matrix chain in `apps.tex:202-214`. -/
theorem conditionalMinEntropyFeasible_coherentMeasurement_sub_log2
    (hX : X.IsRankOne) (hY : Y.IsRankOne) (rho : State (Prod a b))
    (sigma : State (Prod y b)) (lam : Real)
    (hfeas : State.ConditionalMinEntropyFeasible (a := y)
      (hY.coherentMeasurementState rho) sigma lam) :
    State.ConditionalMinEntropyFeasible (a := x)
      (measureSubsystemState X.toPOVM rho) sigma.marginalB
      (lam - log2 (X.rankOneTraceOverlap Y)) := by
  letI : Nonempty a := by
    rcases rho.nonempty with ⟨i, _⟩
    exact ⟨i⟩
  let coherent := hY.coherentMeasurementState rho
  let measured := measureSubsystemState X.toPOVM rho
  let V := hY.coherentGroupedSideIsometry (b := b)
  let Phi : Channel (Prod a b) (Prod x b) :=
    (Channel.measure X.toPOVM).prod (Channel.idChannel b)
  let rin : CMatrix (Prod a b) := hY.coherentPullback sigma.matrix
  let rout : CMatrix (Prod x b) :=
    State.identityTensorStateMatrix (a := x) sigma.marginalB
  let c : Real := X.rankOneTraceOverlap Y
  let t : Real := Real.rpow 2 (-lam)
  have hc : 0 < c := hX.rankOneTraceOverlap_pos Y
  have ht : 0 <= t := Real.rpow_nonneg (by norm_num) _
  have hsource :
      coherent.matrix <= (t : Complex) •
        State.identityTensorStateMatrix (a := y) sigma := by
    simpa [coherent, t, State.ConditionalMinEntropyFeasible] using hfeas
  have hcompressed : rho.matrix <= (t : Complex) • rin := by
    have h := referenceIsometry_compression_mono V hsource
    have himage :
        Matrix.conjTranspose V.matrix * coherent.matrix * V.matrix =
          rho.matrix := by
      simpa [V, coherent, coherentMeasurementState] using
        referenceIsometry_compression_ofReferenceIsometry_applyState V rho
    have href :
        Matrix.conjTranspose V.matrix *
            State.identityTensorStateMatrix (a := y) sigma * V.matrix = rin := by
      simpa [V, rin] using
        hY.coherentGroupedSideIsometry_compression_identityTensor sigma
    calc
      rho.matrix = Matrix.conjTranspose V.matrix * coherent.matrix * V.matrix :=
        himage.symm
      _ <= Matrix.conjTranspose V.matrix *
          ((t : Complex) • State.identityTensorStateMatrix (a := y) sigma) *
            V.matrix := h
      _ = (t : Complex) • rin := by
        simp [Matrix.mul_smul, Matrix.smul_mul, href]
  have hmapFeas : Phi.map rho.matrix <= Phi.map ((t : Complex) • rin) := by
    apply Matrix.le_iff.mpr
    have hpos : (((t : Complex) • rin) - rho.matrix).PosSemidef := by
      simpa [Matrix.le_iff] using hcompressed
    simpa [map_sub, map_smul] using Phi.mapsPositive _ hpos
  have hdom : Phi.map rin <= (c : Complex) • rout := by
    simpa [Phi, rin, rout, c] using
      hX.measureCoherentPullback_le_overlap_identityTensorMarginal hY sigma
  have hscaled :
      (t : Complex) • Phi.map rin <=
        (t : Complex) • ((c : Complex) • rout) :=
    cMatrix_ofReal_smul_le_smul ht hdom
  have htc : t * c = Real.rpow 2 (-(lam - log2 c)) := by
    dsimp [t]
    rw [show -(lam - log2 c) = -lam + log2 c by ring,
      Real.rpow_add (by norm_num : (0 : Real) < 2)]
    exact congrArg (fun z : Real => Real.rpow 2 (-lam) * z)
      (QIT.rpow_two_log2_pos hc).symm
  rw [State.ConditionalMinEntropyFeasible]
  have hfinal : Phi.map rho.matrix <=
      (Real.rpow 2 (-(lam - log2 c)) : Complex) • rout := by
    calc
      Phi.map rho.matrix <= Phi.map ((t : Complex) • rin) := hmapFeas
      _ = (t : Complex) • Phi.map rin := by rw [map_smul]
      _ <= (t : Complex) • ((c : Complex) • rout) := hscaled
      _ = (Real.rpow 2 (-(lam - log2 c)) : Complex) • rout := by
        simp only [smul_smul]
        norm_cast
        rw [htc]
  simpa [Phi, measured, rout, c, measureSubsystemState] using hfinal

/-- The `alpha = infinity` endpoint of Tomamichel's coherent-measurement
comparison. -/
theorem conditionalMinEntropy_coherentMeasurement_sub_log2_le
    (hX : X.IsRankOne) (hY : Y.IsRankOne) (rho : State (Prod a b)) :
    (hY.coherentMeasurementState rho).conditionalMinEntropy -
        log2 (X.rankOneTraceOverlap Y) <=
      (measureSubsystemState X.toPOVM rho).conditionalMinEntropy := by
  let coherent := hY.coherentMeasurementState rho
  let measured := measureSubsystemState X.toPOVM rho
  let S := coherent.conditionalMinEntropyFeasibleExponentValueSet (a := y)
  let T := measured.conditionalMinEntropyFeasibleExponentValueSet (a := x)
  letI : Nonempty (Prod y b) := by
    rcases coherent.nonempty with ⟨_, side⟩
    exact ⟨side⟩
  have hS : S.Nonempty :=
    coherent.conditionalMinEntropyFeasibleExponentValueSet_nonempty (a := y)
  have hTbdd : BddAbove T :=
    measured.conditionalMinEntropyFeasibleExponentValueSet_bddAbove (a := x)
  rw [State.conditionalMinEntropy_eq, State.conditionalMinEntropy_eq]
  change sSup S - log2 (X.rankOneTraceOverlap Y) <= sSup T
  rw [sub_le_iff_le_add]
  apply csSup_le hS
  intro lam hlam
  rcases hlam with ⟨sigma, hfeas⟩
  have hmember : lam - log2 (X.rankOneTraceOverlap Y) ∈ T := by
    exact ⟨sigma.marginalB,
      hX.conditionalMinEntropyFeasible_coherentMeasurement_sub_log2
        hY rho sigma lam hfeas⟩
  have hle := le_csSup hTbdd hmember
  linarith

end ProjectiveMeasurement.IsRankOne

namespace State

variable {x : Type u} {y : Type v} {a : Type w} {b : Type z}
variable [Fintype x] [DecidableEq x]
variable [Fintype y] [DecidableEq y]
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable {X : ProjectiveMeasurement x a} {Y : ProjectiveMeasurement y a}

/-- Tomamichel's `eq:ucr-dual` coherent-measurement comparison for every
closed sandwiched-Renyi order `alpha in [1/2, infinity]`.

The finite interior, Umegaki, max-entropy, and min-entropy branches are the
four source routes proved above.  In particular, the endpoint statement does
not require a full-rank marginal or a separate positivity assumption on the
rank-one overlap. -/
theorem conditionalSandwichedRenyiUpExtendedOrder_coherentMeasurementComparison
    (hX : X.IsRankOne) (hY : Y.IsRankOne) (rho : State (Prod a b))
    (alpha : RenyiOrder) :
    (hY.coherentMeasurementState rho).conditionalSandwichedRenyiUpExtendedOrder alpha -
        log2 (X.rankOneTraceOverlap Y) <=
      (measureSubsystemState X.toPOVM rho).conditionalSandwichedRenyiUpExtendedOrder alpha := by
  obtain ⟨val, hval⟩ := alpha
  cases val with
  | top =>
      change (hY.coherentMeasurementState rho).conditionalMinEntropy -
          log2 (X.rankOneTraceOverlap Y) <=
        (measureSubsystemState X.toPOVM rho).conditionalMinEntropy
      exact hX.conditionalMinEntropy_coherentMeasurement_sub_log2_le hY rho
  | coe r =>
      have hr : 1 / 2 <= r := by exact_mod_cast hval
      change
        (hY.coherentMeasurementState rho).conditionalSandwichedRenyiUpFiniteOrder r -
            log2 (X.rankOneTraceOverlap Y) <=
          (measureSubsystemState X.toPOVM rho).conditionalSandwichedRenyiUpFiniteOrder r
      by_cases hone : r = 1
      · subst r
        rw [conditionalSandwichedRenyiUpFiniteOrder_one,
          conditionalSandwichedRenyiUpFiniteOrder_one]
        exact hX.conditionalEntropy_coherentMeasurement_sub_log2_le hY rho
      by_cases hhalf : r = (2 : Real)⁻¹
      · subst r
        rw [conditionalSandwichedRenyiUpFiniteOrder_half,
          conditionalSandwichedRenyiUpFiniteOrder_half]
        exact hX.conditionalMaxEntropy_coherentMeasurement_sub_log2_le hY rho
      · have hhalf' : r ≠ 1 / 2 := by
          simpa [div_eq_mul_inv] using hhalf
        have hhalfStrict : 1 / 2 < r := lt_of_le_of_ne hr (Ne.symm hhalf')
        have hpos : 0 < r := lt_trans (by norm_num) hhalfStrict
        rw [conditionalSandwichedRenyiUpFiniteOrder_of_pos_ne_one_ne_half
            (hY.coherentMeasurementState rho) hpos hone hhalf,
          conditionalSandwichedRenyiUpFiniteOrder_of_pos_ne_one_ne_half
            (measureSubsystemState X.toPOVM rho) hpos hone hhalf]
        exact hX.conditionalSandwichedRenyiUpSource_coherentMeasurement_sub_log2_le
          hY rho r hhalfStrict hone

end State

end

end QIT
