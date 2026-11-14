/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.ConditionalRenyiMinimaxBoundary
public import QIT.Information.Renyi.ConditionalRenyiSource
public import QIT.Information.Renyi.RenyiDPIStatement
public import QIT.States.Purification.Schatten
public import QIT.Util.Order.EReal

/-!
# Upward sandwiched conditional Renyi duality

Tomamichel's pure-state duality theorem for the upward sandwiched conditional
Renyi entropy.  The proof follows `cond.tex`, Proposition `pr:dual-new`, lines
361--397: Holder and reverse-Holder extrema are identified through the pure
`AB`/`AC` trace bridge, and the resulting common bracket is exchanged by the
support-aware Sion theorem.

Unlike the historical compatibility API, the source-shaped quantity below
does not require the input state to be positive definite.  The optimizing side
states are normalized; singular support is handled by the extended bracket in
`ConditionalRenyiMinimaxBoundary`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal ENNReal Pointwise

open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

private theorem ereal_sInf_range_coe_eq_coe_real_sInf_source
    {i : Type*} [Nonempty i] (f : i -> Real)
    (hf : BddBelow (Set.range f)) :
    sInf (Set.range fun x : i => (f x : EReal)) =
      ((sInf (Set.range f) : Real) : EReal) := by
  let S : Set (WithTop Real) := Set.range fun x : i => ((f x : Real) : WithTop Real)
  have hS_bdd : BddBelow S := by
    rcases hf with ⟨lower, hlower⟩
    refine ⟨(lower : WithTop Real), ?_⟩
    rintro y ⟨x, rfl⟩
    exact WithTop.coe_le_coe.mpr (hlower ⟨x, rfl⟩)
  have htop : sInf S = ((sInf (Set.range f) : Real) : WithTop Real) := by
    have h := WithTop.coe_sInf' (s := Set.range f) (Set.range_nonempty f) hf
    have himage : ((fun x : Real => (x : WithTop Real)) '' Set.range f) = S := by
      ext y
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨f i, ⟨i, rfl⟩, rfl⟩
    rw [himage] at h
    exact h.symm
  have hbot := WithBot.coe_sInf' (s := S) hS_bdd
  have hrange : (Set.range fun x : i => (f x : EReal)) =
      ((fun x : WithTop Real => (x : WithBot (WithTop Real))) '' S) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(f i : WithTop Real), ⟨i, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [hrange]
  calc
    sInf ((fun x : WithTop Real => (x : WithBot (WithTop Real))) '' S) =
        ((sInf S : WithTop Real) : WithBot (WithTop Real)) := hbot.symm
    _ = (((sInf (Set.range f) : Real) : WithTop Real) :
        WithBot (WithTop Real)) := by rw [htop]

private theorem state_iInf_matrix_eq_densityMatrixSet_iInf_source
    {d : Type*} [Fintype d] [DecidableEq d] (f : CMatrix d -> EReal) :
    (⨅ rho : State d, f rho.matrix) =
      ⨅ M : CMatrix d, ⨅ _hM : M ∈ State.densityMatrixSet d, f M := by
  apply le_antisymm
  · refine le_iInf fun M => ?_
    refine le_iInf fun hM => ?_
    calc
      (⨅ rho : State d, f rho.matrix) <=
          f (State.densityMatrixSetState M hM).matrix := iInf_le _ _
      _ = f M := by rw [State.densityMatrixSetState_matrix]
  · refine le_iInf fun rho => ?_
    exact (iInf_le_of_le rho.matrix
      (iInf_le_of_le (State.state_matrix_mem_densityMatrixSet rho) le_rfl))

private theorem state_iSup_matrix_eq_densityMatrixSet_iSup_source
    {d : Type*} [Fintype d] [DecidableEq d] (f : CMatrix d -> EReal) :
    (⨆ rho : State d, f rho.matrix) =
      ⨆ M : CMatrix d, ⨆ _hM : M ∈ State.densityMatrixSet d, f M := by
  apply le_antisymm
  · refine iSup_le fun rho => ?_
    exact (le_iSup_of_le rho.matrix
      (le_iSup_of_le (State.state_matrix_mem_densityMatrixSet rho) le_rfl))
  · refine iSup_le fun M => ?_
    refine iSup_le fun hM => ?_
    calc
      f M = f (State.densityMatrixSetState M hM).matrix := by
        rw [State.densityMatrixSetState_matrix]
      _ <= (⨆ rho : State d, f rho.matrix) :=
        le_iSup (fun rho : State d => f rho.matrix)
          (State.densityMatrixSetState M hM)

private theorem fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf_source
    {d : Type*} [Fintype d] [DecidableEq d] (f : CMatrix d -> EReal) :
    (⨅ sigma : {sigma : State d // sigma.matrix.PosDef}, f sigma.1.matrix) =
      ⨅ M : CMatrix d,
        ⨅ _hM : M ∈ State.fullRankDensityMatrixSet d, f M := by
  apply le_antisymm
  · refine le_iInf fun M => ?_
    refine le_iInf fun hM => ?_
    let sigma : {sigma : State d // sigma.matrix.PosDef} :=
      ⟨{ matrix := M, pos := hM.1.posSemidef, trace_eq_one := hM.2 }, hM.1⟩
    exact iInf_le_of_le sigma le_rfl
  · refine le_iInf fun sigma => ?_
    exact iInf_le_of_le sigma.1.matrix
      (iInf_le_of_le ⟨sigma.2, sigma.1.trace_eq_one⟩ le_rfl)

private theorem log2_rpow_pos_source {x y : Real} (hx : 0 < x) :
    log2 (Real.rpow x y) = y * log2 x := by
  unfold log2
  change Real.log (x ^ y) / Real.log 2 = y * (Real.log x / Real.log 2)
  rw [Real.log_rpow hx]
  ring

private theorem psdSchattenPNorm_rpow_eq_psdTracePower_source
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : CMatrix d) (hA : A.PosSemidef) {p : Real} (hp : 0 < p) :
    Real.rpow (psdSchattenPNorm A hA ⟨p, hp⟩) p = psdTracePower A hA p := by
  rw [psdSchattenPNorm, Internal.psdSchattenExpression]
  have htrace_nonneg : 0 <= psdTracePower A hA p :=
    psdTracePower_nonneg A hA p
  have hp_ne : p ≠ 0 := ne_of_gt hp
  calc
    Real.rpow (Real.rpow (psdTracePower A hA p) (1 / p)) p =
        Real.rpow (psdTracePower A hA p) ((1 / p) * p) := by
          simpa using (Real.rpow_mul htrace_nonneg (1 / p) p).symm
    _ = psdTracePower A hA p := by
      rw [show (1 / p) * p = 1 by field_simp [hp_ne]]
      exact Real.rpow_one _

private theorem continuous_kronecker_right_one_source
    {d : Type*} {e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e] :
    Continuous (fun X : CMatrix d => Matrix.kronecker X (1 : CMatrix e)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
  exact (continuous_apply_apply i.1 j.1).mul continuous_const

private theorem continuous_identity_kronecker_source
    {d : Type*} {e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e] :
    Continuous (fun X : CMatrix e => Matrix.kronecker (1 : CMatrix d) X) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
  exact continuous_const.mul (continuous_apply_apply i.2 j.2)

private theorem continuous_partialTraceA_source
    {d : Type*} {e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e] :
    Continuous (fun X : CMatrix (Prod d e) =>
      partialTraceA (a := d) (b := e) X) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp [partialTraceA]
  fun_prop

private theorem densityIdentityRegularization_matrix_tendsto_source
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (rho : State d) :
    Filter.Tendsto
      (fun epsilon : Real => (State.densityIdentityRegularization rho epsilon).matrix)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds rho.matrix) := by
  have hraw : Filter.Tendsto
      (fun epsilon : Real => rho.matrix + epsilon • (1 : CMatrix d))
      (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds rho.matrix) := by
    have hcont : Continuous (fun epsilon : Real =>
        rho.matrix + epsilon • (1 : CMatrix d)) := by fun_prop
    have hnhds : Filter.Tendsto
        (fun epsilon : Real => rho.matrix + epsilon • (1 : CMatrix d))
        (nhds (0 : Real)) (nhds rho.matrix) := by
      simpa using hcont.tendsto (0 : Real)
    exact hnhds.mono_left inf_le_left
  have hscale := State.densityIdentityRegularization_scale_tendsto rho
  have hscaled := hscale.smul hraw
  have hscaled' : Filter.Tendsto
      (fun epsilon : Real =>
        ((rho.matrix + epsilon • (1 : CMatrix d)).trace.re)⁻¹ •
          (rho.matrix + epsilon • (1 : CMatrix d)))
      (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds rho.matrix) := by
    simpa using hscaled
  apply hscaled'.congr'
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  have hpos : 0 < epsilon := hepsilon
  rw [State.densityIdentityRegularization_eq_of_pos rho hpos,
    State.stateOfPosDefReference_matrix]

private theorem sSup_range_mul_eq_mul_sSup_range_source
    {i : Type*} [Nonempty i] (f : i -> Real) {c : Real} (hc : 0 <= c) :
    sSup (Set.range fun x : i => c * f x) = c * sSup (Set.range f) := by
  have himage : Set.range (fun x : i => c * f x) =
      ((c : Real) • (Set.range f : Set Real) : Set Real) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Set.mem_smul_set.mpr ⟨f x, ⟨x, rfl⟩, by simp [smul_eq_mul]⟩
    · intro hy
      rcases Set.mem_smul_set.mp hy with ⟨z, ⟨x, rfl⟩, hy⟩
      exact ⟨x, by simpa [smul_eq_mul] using hy⟩
  rw [himage, Real.sSup_smul_of_nonneg hc]
  simp [smul_eq_mul]

namespace State

/-- The source-shaped full-rank-side candidate for
`H_tilde^up_alpha(A|B)_rho`, without a positive-definiteness assumption on
`rho`.

The matrix expression is exactly the one used by the historical
`conditionalSandwichedRenyiCandidate`; only its unused input-state
positive-definiteness witness has been removed.  The explicit order guards
prevent the raw logarithmic formula from being exposed as an entropy at
`alpha = 1`. -/
def conditionalSandwichedRenyiUpSourceCandidate
    (rho : State (Prod a b)) (sigma : State b) (_hsigma : sigma.matrix.PosDef)
    (alpha : Real) (_hAlphaPos : 0 < alpha) (_hAlphaNeOne : alpha ≠ 1) : Real :=
  let r := -(1 / (alpha - 1))
  let s := (1 - alpha) / (2 * alpha)
  let tau : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) sigma
  let M := CFC.rpow (CFC.rpow tau s * rho.matrix * CFC.rpow tau s) alpha
  r * log2 M.trace.re

/-- Candidate values for the source-shaped upward sandwiched conditional
Renyi entropy. -/
def conditionalSandwichedRenyiUpSourceValueSet
    (rho : State (Prod a b)) (alpha : Real)
    (hAlphaPos : 0 < alpha) (hAlphaNeOne : alpha ≠ 1) : Set Real :=
  {x | exists sigma : State b, exists hsigma : sigma.matrix.PosDef,
    x = rho.conditionalSandwichedRenyiUpSourceCandidate
      sigma hsigma alpha hAlphaPos hAlphaNeOne}

/-- Source-shaped upward sandwiched conditional Renyi entropy.

The optimization over normalized full-rank side states is the proved dense
implementation of Tomamichel's normalized side-state domain.  Singular side
states and support failures are supplied by the support-aware boundary theorem
and identity-regularization closure below.  No full-rank condition is imposed
on the input state. -/
def conditionalSandwichedRenyiUpSource
    (rho : State (Prod a b)) (alpha : Real)
    (hAlphaPos : 0 < alpha) (hAlphaNeOne : alpha ≠ 1) : Real :=
  sSup (rho.conditionalSandwichedRenyiUpSourceValueSet
    alpha hAlphaPos hAlphaNeOne)

@[simp]
theorem conditionalSandwichedRenyiUpSource_eq
    (rho : State (Prod a b)) (alpha : Real)
    (hAlphaPos : 0 < alpha) (hAlphaNeOne : alpha ≠ 1) :
    rho.conditionalSandwichedRenyiUpSource alpha hAlphaPos hAlphaNeOne =
      sSup (rho.conditionalSandwichedRenyiUpSourceValueSet
        alpha hAlphaPos hAlphaNeOne) :=
  rfl

/-- On the historical positive-definite domain, the source-shaped candidate
is definitionally the old candidate. -/
theorem conditionalSandwichedRenyiUpSourceCandidate_eq_old
    (rho : State (Prod a b)) (hrho : rho.matrix.PosDef)
    (sigma : State b) (hsigma : sigma.matrix.PosDef)
    (alpha : Real) (halpha : 0 < alpha) (halpha_one : alpha ≠ 1) :
    rho.conditionalSandwichedRenyiUpSourceCandidate
        sigma hsigma alpha halpha halpha_one =
      rho.conditionalSandwichedRenyiCandidate hrho sigma hsigma alpha
        halpha halpha_one :=
  rfl

/-- Compatibility with the historical positive-definite upward conditional
sandwiched Renyi API. -/
theorem conditionalSandwichedRenyiUpSource_eq_conditionalSandwichedRenyiUp
    (rho : State (Prod a b)) (hrho : rho.matrix.PosDef)
    (alpha : Real) (halpha : 1 / 2 <= alpha) (halpha_one : alpha ≠ 1) :
    rho.conditionalSandwichedRenyiUpSource alpha (by linarith) halpha_one =
      rho.conditionalSandwichedRenyiUp hrho alpha halpha halpha_one := by
  rfl

/-- A source candidate is the negative sandwiched Schatten logarithm.  Only
the side-reference is assumed full-rank; the input state may be singular. -/
theorem conditionalSandwichedRenyiUpSourceCandidate_eq_schattenLog
    (rho : State (Prod a b)) (sigma : State b) (hsigma : sigma.matrix.PosDef)
    {alpha : Real} (halpha_pos : 0 < alpha) (_halpha_one : alpha ≠ 1) :
    rho.conditionalSandwichedRenyiUpSourceCandidate
        sigma hsigma alpha halpha_pos _halpha_one =
      -(alpha / (alpha - 1)) *
        log2 (psdSchattenPNorm
          (sandwichedRenyiReferenceInner rho
            (identityTensorStateMatrix (a := a) sigma) alpha)
          (sandwichedRenyiReferenceInner_posSemidef rho
            (identityTensorStateMatrix_posSemidef (a := a) sigma) alpha)
          ⟨alpha, halpha_pos⟩) := by
  let reference : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) sigma
  let inner : CMatrix (Prod a b) :=
    sandwichedRenyiReferenceInner rho reference alpha
  let hinner : inner.PosSemidef :=
    sandwichedRenyiReferenceInner_posSemidef rho
      (identityTensorStateMatrix_posSemidef (a := a) sigma) alpha
  let norm : Real := psdSchattenPNorm inner hinner ⟨alpha, halpha_pos⟩
  have href : reference.PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) sigma hsigma
  have hinner_ne : inner ≠ 0 := by
    simpa [inner, reference] using
      sandwichedRenyiReferenceInner_ne_zero_of_reference_posDef rho href alpha
  have hnorm_pos : 0 < norm := by
    exact psdSchattenPNorm_pos_of_ne_zero inner hinner hinner_ne
  have hpow : Real.rpow norm alpha = psdTracePower inner hinner alpha := by
    exact psdSchattenPNorm_rpow_eq_psdTracePower_source
      inner hinner halpha_pos
  unfold conditionalSandwichedRenyiUpSourceCandidate
  change -(1 / (alpha - 1)) * log2 (psdTracePower inner hinner alpha) =
    -(alpha / (alpha - 1)) * log2 norm
  rw [← hpow, log2_rpow_pos_source hnorm_pos]
  ring

/-- The source value set is the range over normalized full-rank side states. -/
theorem conditionalSandwichedRenyiUpSourceValueSet_eq_range
    [Nonempty b] (rho : State (Prod a b)) (alpha : Real)
    (hAlphaPos : 0 < alpha) (hAlphaNeOne : alpha ≠ 1) :
    rho.conditionalSandwichedRenyiUpSourceValueSet alpha hAlphaPos hAlphaNeOne =
      Set.range (fun sigma : {sigma : State b // sigma.matrix.PosDef} =>
        rho.conditionalSandwichedRenyiUpSourceCandidate
          sigma.1 sigma.2 alpha hAlphaPos hAlphaNeOne) := by
  ext x
  constructor
  · rintro ⟨sigma, hsigma, rfl⟩
    exact ⟨⟨sigma, hsigma⟩, rfl⟩
  · rintro ⟨sigma, rfl⟩
    exact ⟨sigma.1, sigma.2, rfl⟩

end State

namespace PureVector

/-- Conjugate-order parameter used in Tomamichel's proof. -/
def upwardRenyiDualityParameter (alpha : Real) : Real :=
  (alpha - 1) / alpha

theorem upwardRenyiDualityParameter_pos
    {alpha : Real} (halpha : 1 < alpha) :
    0 < upwardRenyiDualityParameter alpha := by
  unfold upwardRenyiDualityParameter
  positivity

theorem upwardRenyiDualityParameter_lt_one
    {alpha : Real} (halpha : 1 < alpha) :
    upwardRenyiDualityParameter alpha < 1 := by
  unfold upwardRenyiDualityParameter
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  rw [div_lt_one halpha_pos]
  linarith

theorem upwardRenyiDualityParameter_eq_beta
    {alpha beta : Real} (halpha : 1 < alpha)
    (hconj : 1 / alpha + 1 / beta = 2) :
    upwardRenyiDualityParameter alpha = (1 - beta) / beta := by
  have halpha_ne : alpha ≠ 0 := ne_of_gt (lt_trans zero_lt_one halpha)
  have hbeta_ne : beta ≠ 0 := by
    intro hbeta
    simp [hbeta] at hconj
    have hinv_lt : 1 / alpha < 1 := by
      rw [div_lt_one (lt_trans zero_lt_one halpha)]
      linarith
    rw [one_div] at hinv_lt
    linarith
  unfold upwardRenyiDualityParameter
  field_simp [halpha_ne, hbeta_ne] at hconj ⊢
  nlinarith

/-- Apply the source high-order side weight
`I_A tensor sigma_B^(-p/2)` to the `AB` leg of a purification. -/
def upwardRenyiDualityABWeightedAmplitude
    (psi : PureVector (Prod (Prod a b) c)) (sigma : CMatrix b) (p : Real) :
    Prod (Prod a b) c -> Complex :=
  Matrix.mulVec
    (Matrix.kronecker
      (Matrix.kronecker (1 : CMatrix a) (CFC.rpow sigma (-p / 2)))
      (1 : CMatrix c))
    psi.amp

/-- The complementary `C` marginal of the high-order weighted
purification. -/
def upwardRenyiDualityHighCMatrix
    (psi : PureVector (Prod (Prod a b) c)) (sigma : CMatrix b) (p : Real) :
    CMatrix c :=
  partialTraceA (a := Prod a b) (b := c)
    (rankOneMatrix (psi.upwardRenyiDualityABWeightedAmplitude sigma p))

theorem upwardRenyiDualityHighCMatrix_posSemidef
    (psi : PureVector (Prod (Prod a b) c)) (sigma : CMatrix b) (p : Real) :
    (psi.upwardRenyiDualityHighCMatrix sigma p).PosSemidef :=
  partialTraceA_posSemidef
    (rankOneMatrix_pos (psi.upwardRenyiDualityABWeightedAmplitude sigma p))

/-- High-order Schatten value attached to a full-rank `B` side state. -/
def upwardRenyiDualityHighNorm
    (psi : PureVector (Prod (Prod a b) c))
    (sigma : State b) (alpha : SchattenOrder) : Real :=
  psdSchattenPNorm
    (psi.upwardRenyiDualityHighCMatrix sigma.matrix
      (upwardRenyiDualityParameter alpha))
    (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.matrix
      (upwardRenyiDualityParameter alpha)) alpha

/-- Low-order Schatten value attached to a normalized `C` side state. -/
def upwardRenyiDualityLowNorm
    (psi : PureVector (Prod (Prod a b) c))
    (tau : State c) (alpha : Real) (beta : SchattenOrder) : Real :=
  psdSchattenPNorm
    (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix
      (upwardRenyiDualityParameter alpha))
    (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.matrix
      (upwardRenyiDualityParameter alpha)) beta

private theorem rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose_source
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : CMatrix d) (v : d -> Complex) :
    rankOneMatrix (M.mulVec v) =
      M * rankOneMatrix v * Matrix.conjTranspose M := by
  rw [rankOneMatrix, rankOneMatrix]
  rw [Matrix.mul_vecMulVec]
  rw [Matrix.vecMulVec_mul]
  congr
  ext i
  simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.conjTranspose, mul_comm]

private theorem partialTraceA_mul_trace_eq_trace_mul_rightKroneckerOne_source
    {d : Type*} {e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (X : CMatrix (Prod d e)) (T : CMatrix e) :
    ((partialTraceA (a := d) (b := e) X) * T).trace =
      (X * Matrix.kronecker (1 : CMatrix d) T).trace := by
  rw [← partialTraceA_mul_rightKroneckerOne X T]
  exact partialTraceA_trace (a := d) (b := e)
    (X * Matrix.kronecker (1 : CMatrix d) T)

private theorem kronecker_left_one_mulVec_apply_source
    {d : Type*} {e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (W : CMatrix d) (v : Prod d e -> Complex) (i : d) (k : e) :
    (Matrix.kronecker W (1 : CMatrix e)).mulVec v (i, k) =
      W.mulVec (fun j => v (j, k)) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Matrix.one_apply]

/-- Partial trace of a rank-one vector after a left Kronecker weight.

This is the finite-dimensional rank-one identity behind source arguments that
write a weighted pure projector as `(W ⊗ I)|ψ⟩⟨ψ|(W† ⊗ I)` and then trace out
the purifying register. -/
theorem partialTraceB_rankOne_kron_left_mulVec_eq_source
    {d : Type*} {e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (W : CMatrix d) (v : Prod d e -> Complex) :
    partialTraceB (a := d) (b := e)
        (rankOneMatrix
          (Matrix.mulVec (Matrix.kronecker W (1 : CMatrix e)) v)) =
      W * partialTraceB (a := d) (b := e) (rankOneMatrix v) *
        Matrix.conjTranspose W := by
  ext x y
  have hmulVec :
      Matrix.mulVec (Matrix.kronecker W (1 : CMatrix e)) v =
        fun z : Prod d e => W.mulVec (fun i => v (i, z.2)) z.1 := by
    ext z
    exact kronecker_left_one_mulVec_apply_source W v z.1 z.2
  rw [hmulVec]
  let F : e -> d -> d -> Complex := fun k i j =>
    W x i * (v (i, k) * (star (W y j) * star (v (j, k))))
  calc
    partialTraceB (a := d) (b := e)
        (rankOneMatrix
          (fun z : Prod d e => W.mulVec (fun i => v (i, z.2)) z.1)) x y =
        ∑ k : e, ∑ j : d, ∑ i : d, F k i j := by
          simp [F, partialTraceB, rankOneMatrix_apply, Matrix.mulVec, dotProduct,
            Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ = ∑ j : d, ∑ k : e, ∑ i : d, F k i j := by
          rw [Finset.sum_comm]
    _ = ∑ j : d, ∑ i : d, ∑ k : e, F k i j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
    _ = ∑ j : d, star (W y j) *
          ∑ i : d, W x i * ∑ k : e, v (i, k) * star (v (j, k)) := by
          simp [F, Finset.mul_sum, mul_left_comm]
    _ = (W * partialTraceB (a := d) (b := e) (rankOneMatrix v) *
          Matrix.conjTranspose W) x y := by
          simp [partialTraceB, rankOneMatrix_apply, Matrix.mul_apply,
            Matrix.conjTranspose_apply, mul_comm]

/-- The `AB` marginal of the high-order weighted purification is exactly the
sandwiched-Renyi inner operator for `I_A tensor sigma_B`. -/
theorem partialTraceB_rankOne_upwardRenyiDualityABWeightedAmplitude_eq_referenceInner
    (psi : PureVector (Prod (Prod a b) c))
    (sigma : State b) (hsigma : sigma.matrix.PosDef)
    {alpha : Real} (_halpha : 1 < alpha) :
    partialTraceB (a := Prod a b) (b := c)
        (rankOneMatrix
          (psi.upwardRenyiDualityABWeightedAmplitude sigma.matrix
            (upwardRenyiDualityParameter alpha))) =
      State.sandwichedRenyiReferenceInner psi.state.marginalAB
        (State.identityTensorStateMatrix (a := a) sigma) alpha := by
  let p := upwardRenyiDualityParameter alpha
  let s : Real := (1 - alpha) / (2 * alpha)
  let Wab : CMatrix (Prod a b) :=
    Matrix.kronecker (1 : CMatrix a) (CFC.rpow sigma.matrix (-p / 2))
  have hp : p = (alpha - 1) / alpha := rfl
  have hsp : -p / 2 = s := by
    simp [p, upwardRenyiDualityParameter, s]
    ring
  have hWab :
      Wab = CFC.rpow (State.identityTensorStateMatrix (a := a) sigma) s := by
    unfold Wab State.identityTensorStateMatrix
    rw [cMatrix_rpow_kronecker_posDef Matrix.PosDef.one hsigma s]
    simp [hsp]
  rw [show upwardRenyiDualityParameter alpha = p by rfl]
  change partialTraceB (a := Prod a b) (b := c)
      (rankOneMatrix
        (Matrix.mulVec (Matrix.kronecker Wab (1 : CMatrix c)) psi.amp)) = _
  rw [partialTraceB_rankOne_kron_left_mulVec_eq_source]
  have hWabHerm : Matrix.conjTranspose Wab = Wab := by
    rw [hWab]
    exact (cMatrix_rpow_posSemidef
      (A := State.identityTensorStateMatrix (a := a) sigma) (s := s)
      (State.identityTensorStateMatrix_posSemidef (a := a) sigma)).isHermitian.eq
  rw [hWabHerm, hWab]
  change CFC.rpow (State.identityTensorStateMatrix (a := a) sigma) s *
      psi.state.marginalAB.matrix *
        CFC.rpow (State.identityTensorStateMatrix (a := a) sigma) s = _
  rfl

/-- The common Tomamichel bracket is the trace pairing of the high-order
weighted purification's complementary marginal with `tau_C^p`. -/
theorem abcSidePowerTraceRe_eq_highCMatrix_pairing
    (psi : PureVector (Prod (Prod a b) c))
    (sigma : CMatrix b) (tau : CMatrix c) (p : Real)
    (hsigma : sigma.PosDef) :
    State.abcSidePowerTraceRe (a := a) psi.state.matrix sigma tau p =
      ((psi.upwardRenyiDualityHighCMatrix sigma p *
        CFC.rpow tau p).trace).re := by
  let S : CMatrix b := CFC.rpow sigma (-p / 2)
  let Wab : CMatrix (Prod a b) := Matrix.kronecker (1 : CMatrix a) S
  let W : CMatrix (Prod (Prod a b) c) :=
    Matrix.kronecker Wab (1 : CMatrix c)
  let T : CMatrix c := CFC.rpow tau p
  let K : CMatrix (Prod (Prod a b) c) :=
    Matrix.kronecker (1 : CMatrix (Prod a b)) T
  have hSpow : S * S = CFC.rpow sigma (-p) := by
    calc
      S * S = CFC.rpow sigma ((-p / 2) + (-p / 2)) := by
        exact (CFC.rpow_add (a := sigma) (x := -p / 2) (y := -p / 2)
          hsigma.isUnit).symm
      _ = CFC.rpow sigma (-p) := by
        congr 1
        ring
  have hWstar : Matrix.conjTranspose W = W := by
    have hS : S.PosSemidef :=
      cMatrix_rpow_posSemidef (A := sigma) (s := -p / 2) hsigma.posSemidef
    have hWab : Wab.PosSemidef := Matrix.PosSemidef.one.kronecker hS
    have hW : W.PosSemidef := hWab.kronecker Matrix.PosSemidef.one
    exact hW.isHermitian.eq
  have hWKW :
      W * K * W =
        Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a) (CFC.rpow sigma (-p))) T := by
    have hWK : W * K = Matrix.kronecker Wab T := by
      unfold W K
      simpa using
        (Matrix.mul_kronecker_mul Wab (1 : CMatrix (Prod a b))
          (1 : CMatrix c) T).symm
    have hWab2 :
        Wab * Wab =
          Matrix.kronecker (1 : CMatrix a) (CFC.rpow sigma (-p)) := by
      unfold Wab
      calc
        Matrix.kronecker (1 : CMatrix a) S *
            Matrix.kronecker (1 : CMatrix a) S =
            Matrix.kronecker ((1 : CMatrix a) * 1) (S * S) := by
              exact (Matrix.mul_kronecker_mul
                (1 : CMatrix a) (1 : CMatrix a) S S).symm
        _ = Matrix.kronecker (1 : CMatrix a) (CFC.rpow sigma (-p)) := by
              rw [hSpow]
              simp
    calc
      W * K * W = Matrix.kronecker Wab T * W := by rw [hWK]
      _ = Matrix.kronecker Wab T *
          Matrix.kronecker Wab (1 : CMatrix c) := by rfl
      _ = Matrix.kronecker (Wab * Wab) (T * (1 : CMatrix c)) := by
            exact (Matrix.mul_kronecker_mul Wab Wab T (1 : CMatrix c)).symm
      _ = Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a) (CFC.rpow sigma (-p))) T := by
            rw [hWab2]
            simp
  have hrank :
      rankOneMatrix (psi.upwardRenyiDualityABWeightedAmplitude sigma p) =
        W * rankOneMatrix psi.amp * W := by
    unfold upwardRenyiDualityABWeightedAmplitude W Wab S
    rw [rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose_source]
    rw [hWstar]
  unfold State.abcSidePowerTraceRe
  change
    ((Matrix.kronecker
        (Matrix.kronecker (1 : CMatrix a) (CFC.rpow sigma (-p)))
        (CFC.rpow tau p) * rankOneMatrix psi.amp).trace).re =
      ((partialTraceA (a := Prod a b) (b := c)
          (rankOneMatrix (psi.upwardRenyiDualityABWeightedAmplitude sigma p)) *
        CFC.rpow tau p).trace).re
  rw [partialTraceA_mul_trace_eq_trace_mul_rightKroneckerOne_source]
  change
    ((Matrix.kronecker
        (Matrix.kronecker (1 : CMatrix a) (CFC.rpow sigma (-p))) T *
      rankOneMatrix psi.amp).trace).re =
      ((rankOneMatrix (psi.upwardRenyiDualityABWeightedAmplitude sigma p) *
        K).trace).re
  rw [hrank]
  calc
    ((Matrix.kronecker
        (Matrix.kronecker (1 : CMatrix a) (CFC.rpow sigma (-p))) T *
      rankOneMatrix psi.amp).trace).re =
        ((W * K * W * rankOneMatrix psi.amp).trace).re := by rw [hWKW]
    _ = (((W * rankOneMatrix psi.amp * W) * K).trace).re := by
      congr 1
      simpa [Matrix.mul_assoc] using
        Matrix.trace_mul_cycle W K (W * rankOneMatrix psi.amp)

/-- For fixed full-rank `sigma_B`, Holder's variational formula identifies
the supremum of the common bracket with the Schatten `alpha` norm of the
weighted purification's `C` marginal. -/
theorem upwardRenyiDualityHighBracket_isGreatest
    [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c))
    (sigma : State b) (hsigma : sigma.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    IsGreatest
      (Set.range fun tau : State c =>
        State.abcSidePowerTraceRe (a := a) psi.state.matrix
          sigma.matrix tau.matrix (upwardRenyiDualityParameter alpha))
      (psdSchattenPNorm
        (psi.upwardRenyiDualityHighCMatrix sigma.matrix
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.matrix
          (upwardRenyiDualityParameter alpha))
        ⟨alpha, lt_trans zero_lt_one halpha⟩) := by
  let p := upwardRenyiDualityParameter alpha
  let M := psi.upwardRenyiDualityHighCMatrix sigma.matrix p
  let hM : M.PosSemidef :=
    psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.matrix p
  have hp : p = 1 - 1 / alpha := by
    simp [p, upwardRenyiDualityParameter]
    field_simp [ne_of_gt (lt_trans zero_lt_one halpha)]
  have hset :
      (Set.range fun tau : State c =>
        State.abcSidePowerTraceRe (a := a) psi.state.matrix
          sigma.matrix tau.matrix p) =
        psdTraceHolderStateValueSet M alpha := by
    ext x
    constructor
    · rintro ⟨tau, rfl⟩
      refine ⟨tau, ?_⟩
      change State.abcSidePowerTraceRe (a := a) psi.state.matrix
          sigma.matrix tau.matrix p =
        ((M * CFC.rpow tau.matrix (1 - 1 / alpha)).trace).re
      rw [psi.abcSidePowerTraceRe_eq_highCMatrix_pairing
        sigma.matrix tau.matrix p hsigma]
      rw [← hp]
    · rintro ⟨tau, rfl⟩
      refine ⟨tau, ?_⟩
      change State.abcSidePowerTraceRe (a := a) psi.state.matrix
          sigma.matrix tau.matrix p =
        ((M * CFC.rpow tau.matrix (1 - 1 / alpha)).trace).re
      rw [psi.abcSidePowerTraceRe_eq_highCMatrix_pairing
        sigma.matrix tau.matrix p hsigma]
      rw [← hp]
  rw [show upwardRenyiDualityParameter alpha = p by rfl, hset]
  exact psdTraceHolderStateValueSet_isGreatest_of_one_lt hM halpha

/-- Reverse-Holder candidate values for the fixed `tau_C` branch of the
source common bracket. -/
def upwardRenyiDualityLowBracketValueSet
    (psi : PureVector (Prod (Prod a b) c))
    (tau : State c) (p : Real) : Set Real :=
  {x | exists sigma : State b,
    Matrix.Supports
      (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix p) sigma.matrix ∧
    x = State.abcSidePowerTraceRe (a := a) psi.state.matrix
      sigma.matrix tau.matrix p}

/-- For fixed `tau_C`, reverse Holder identifies the minimum of the
support-aware common bracket with the Schatten `beta` norm of the effective
`B` matrix. -/
theorem upwardRenyiDualityLowBracket_isLeast
    [Nonempty b]
    (psi : PureVector (Prod (Prod a b) c)) (tau : State c)
    {alpha beta : Real} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    IsLeast
      (psi.upwardRenyiDualityLowBracketValueSet tau
        (upwardRenyiDualityParameter alpha))
      (psdSchattenPNorm
        (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.matrix
          (upwardRenyiDualityParameter alpha))
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩) := by
  let p := upwardRenyiDualityParameter alpha
  let M := psi.upwardRenyiDualityEffectiveBMatrix tau.matrix p
  let hM : M.PosSemidef :=
    psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.matrix p
  have hbeta_pos : 0 < beta := lt_trans (by norm_num) hbeta_half
  have hexp : 1 - 1 / beta = -p := by
    change 1 - 1 / beta = -upwardRenyiDualityParameter alpha
    rw [upwardRenyiDualityParameter_eq_beta halpha hconj]
    field_simp [ne_of_gt hbeta_pos]
    ring
  have hset :
      psi.upwardRenyiDualityLowBracketValueSet tau p =
        psdTraceReverseHolderNormalizedStateValueSet M beta := by
    ext x
    constructor
    · rintro ⟨sigma, hsupp, rfl⟩
      refine ⟨sigma, ?_, ?_⟩
      · simpa [M] using hsupp
      · rw [psi.abcSidePowerTraceRe_eq_effectiveBMatrix_pairing
          sigma.matrix tau.matrix p tau.pos]
        rw [hexp, Matrix.trace_mul_comm]
    · rintro ⟨sigma, hsupp, rfl⟩
      refine ⟨sigma, ?_, ?_⟩
      · simpa [M] using hsupp
      · rw [psi.abcSidePowerTraceRe_eq_effectiveBMatrix_pairing
          sigma.matrix tau.matrix p tau.pos]
        rw [hexp, Matrix.trace_mul_comm]
  rw [show upwardRenyiDualityParameter alpha = p by rfl, hset]
  exact psdTraceReverseHolderNormalizedStateValueSet_isLeast_of_lt_one
    hM hbeta_pos hbeta_one

/-- The `AC` marginal of the low-order weighted purification is exactly the
sandwiched-Renyi inner operator for `I_A tensor tau_C`. -/
theorem partialTraceB_rankOne_upwardRenyiDualityACWeightedAmplitude_eq_referenceInner
    (psi : PureVector (Prod (Prod a b) c)) (tau : State c)
    {alpha beta : Real} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    partialTraceB (a := Prod a c) (b := b)
        (rankOneMatrix
          (psi.upwardRenyiDualityACWeightedAmplitude tau.matrix
            (upwardRenyiDualityParameter alpha))) =
      State.sandwichedRenyiReferenceInner psi.state.marginalAC
        (State.identityTensorStateMatrix (a := a) tau) beta := by
  let p := upwardRenyiDualityParameter alpha
  let X : CMatrix (Prod a c) := State.identityTensorStateMatrix (a := a) tau
  let W : CMatrix (Prod a c) := upwardRenyiDualityACWeight (a := a) tau.matrix p
  let S : CMatrix (Prod a c) := CFC.sqrt W
  have hp0 : 0 < p := upwardRenyiDualityParameter_pos halpha
  have hp_nonneg : 0 <= p := hp0.le
  have hp_beta : p = (1 - beta) / beta :=
    upwardRenyiDualityParameter_eq_beta halpha hconj
  have hbeta_pos : 0 < beta := by linarith
  have hs : p / 2 = (1 - beta) / (2 * beta) := by
    rw [hp_beta]
    field_simp [ne_of_gt hbeta_pos]
  have hX : X.PosSemidef :=
    State.identityTensorStateMatrix_posSemidef (a := a) tau
  have hW : W = CFC.rpow X p := by
    unfold W PureVector.upwardRenyiDualityACWeight X
    simpa using
      (cMatrix_rpow_kronecker_nonneg
        (A := (1 : CMatrix a)) (B := tau.matrix)
        Matrix.PosSemidef.one tau.pos hp_nonneg).symm
  have hS : S = CFC.rpow X (p / 2) := by
    change CFC.sqrt W = CFC.rpow X (p / 2)
    rw [hW]
    let pnn : NNReal := ⟨p, hp_nonneg⟩
    simpa [S, pnn] using
      (CFC.sqrt_rpow_nnreal (a := X) (x := pnn))
  have hmarg :
      partialTraceB (a := Prod a c) (b := b)
          (rankOneMatrix psi.upwardRenyiDualityACBAmplitude) =
        psi.state.marginalAC.matrix := by
    ext x y
    simp [PureVector.upwardRenyiDualityACBAmplitude, State.marginalAC,
      partialTraceB, rankOneMatrix_apply]
  unfold upwardRenyiDualityACWeightedAmplitude
  change partialTraceB (a := Prod a c) (b := b)
      (rankOneMatrix
        (Matrix.mulVec (Matrix.kronecker S (1 : CMatrix b))
          psi.upwardRenyiDualityACBAmplitude)) = _
  rw [partialTraceB_rankOne_kron_left_mulVec_eq_source]
  rw [hmarg]
  have hSherm : Matrix.conjTranspose S = S := by
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg W)).isHermitian.eq
  rw [hSherm, hS, hs]
  rfl

/-- The low-order reference inner and the effective `B` matrix have the same
Schatten `beta` norm because they are complementary marginals of one weighted
pure vector. -/
theorem psdSchattenPNorm_lowReferenceInner_eq_effectiveBMatrix
    (psi : PureVector (Prod (Prod a b) c)) (tau : State c)
    {alpha beta : Real} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    psdSchattenPNorm
        (State.sandwichedRenyiReferenceInner psi.state.marginalAC
          (State.identityTensorStateMatrix (a := a) tau) beta)
        (State.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAC
          (State.identityTensorStateMatrix_posSemidef (a := a) tau) beta)
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩ =
      psdSchattenPNorm
        (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.matrix
          (upwardRenyiDualityParameter alpha))
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩ := by
  have hbeta_pos : 0 < beta := lt_trans (by norm_num) hbeta_half
  let v := psi.upwardRenyiDualityACWeightedAmplitude tau.matrix
    (upwardRenyiDualityParameter alpha)
  have hcomp :=
    psdSchattenPNorm_partialTraceB_rankOneMatrix_eq_partialTraceA_rankOneMatrix
      v ⟨beta, hbeta_pos⟩
  have hleft :=
    psi.partialTraceB_rankOne_upwardRenyiDualityACWeightedAmplitude_eq_referenceInner
      tau halpha hbeta_half hbeta_one hconj
  calc
    psdSchattenPNorm
        (State.sandwichedRenyiReferenceInner psi.state.marginalAC
          (State.identityTensorStateMatrix (a := a) tau) beta)
        (State.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAC
          (State.identityTensorStateMatrix_posSemidef (a := a) tau) beta)
        ⟨beta, hbeta_pos⟩ =
      psdSchattenPNorm
        (partialTraceB (a := Prod a c) (b := b) (rankOneMatrix v))
        (partialTraceB_posSemidef (rankOneMatrix_pos v)) ⟨beta, hbeta_pos⟩ :=
          psdSchattenPNorm_congr hleft.symm _ _ ⟨beta, hbeta_pos⟩
    _ = psdSchattenPNorm
        (partialTraceA (a := Prod a c) (b := b) (rankOneMatrix v))
        (partialTraceA_posSemidef (rankOneMatrix_pos v)) ⟨beta, hbeta_pos⟩ := hcomp
    _ = psdSchattenPNorm
        (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.matrix
          (upwardRenyiDualityParameter alpha)) ⟨beta, hbeta_pos⟩ := by rfl

/-- The high-order reference inner and the complementary `C` matrix have the
same Schatten `alpha` norm. -/
theorem psdSchattenPNorm_highReferenceInner_eq_highCMatrix
    (psi : PureVector (Prod (Prod a b) c))
    (sigma : State b) (hsigma : sigma.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    psdSchattenPNorm
        (State.sandwichedRenyiReferenceInner psi.state.marginalAB
          (State.identityTensorStateMatrix (a := a) sigma) alpha)
        (State.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAB
          (State.identityTensorStateMatrix_posSemidef (a := a) sigma) alpha)
        ⟨alpha, lt_trans zero_lt_one halpha⟩ =
      psdSchattenPNorm
        (psi.upwardRenyiDualityHighCMatrix sigma.matrix
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.matrix
          (upwardRenyiDualityParameter alpha))
        ⟨alpha, lt_trans zero_lt_one halpha⟩ := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  let v := psi.upwardRenyiDualityABWeightedAmplitude sigma.matrix
    (upwardRenyiDualityParameter alpha)
  have hcomp :=
    psdSchattenPNorm_partialTraceB_rankOneMatrix_eq_partialTraceA_rankOneMatrix
      v ⟨alpha, halpha_pos⟩
  have hleft :=
    psi.partialTraceB_rankOne_upwardRenyiDualityABWeightedAmplitude_eq_referenceInner
      sigma hsigma halpha
  calc
    psdSchattenPNorm
        (State.sandwichedRenyiReferenceInner psi.state.marginalAB
          (State.identityTensorStateMatrix (a := a) sigma) alpha)
        (State.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAB
          (State.identityTensorStateMatrix_posSemidef (a := a) sigma) alpha)
        ⟨alpha, halpha_pos⟩ =
      psdSchattenPNorm
        (partialTraceB (a := Prod a b) (b := c) (rankOneMatrix v))
        (partialTraceB_posSemidef (rankOneMatrix_pos v)) ⟨alpha, halpha_pos⟩ :=
          psdSchattenPNorm_congr hleft.symm _ _ ⟨alpha, halpha_pos⟩
    _ = psdSchattenPNorm
        (partialTraceA (a := Prod a b) (b := c) (rankOneMatrix v))
        (partialTraceA_posSemidef (rankOneMatrix_pos v)) ⟨alpha, halpha_pos⟩ := hcomp
    _ = psdSchattenPNorm
        (psi.upwardRenyiDualityHighCMatrix sigma.matrix
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.matrix
          (upwardRenyiDualityParameter alpha)) ⟨alpha, halpha_pos⟩ := by rfl

/-- State-language form of the full-rank Sion exchange proved at the matrix
boundary in `ConditionalRenyiMinimaxBoundary`. -/
theorem upwardRenyiDualitySource_fullRank_sion
    [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c))
    {p : Real} (hp0 : 0 < p) (hp1 : p < 1) :
    (⨅ sigma : {sigma : State b // sigma.matrix.PosDef},
      ⨆ tau : State c,
        (State.abcSidePowerTraceRe (a := a) psi.state.matrix
          sigma.1.matrix tau.matrix p : EReal)) =
      ⨆ tau : State c,
        ⨅ sigma : {sigma : State b // sigma.matrix.PosDef},
          (State.abcSidePowerTraceRe (a := a) psi.state.matrix
            sigma.1.matrix tau.matrix p : EReal) := by
  let F : CMatrix b -> CMatrix c -> EReal := fun sigma tau =>
    (State.abcSidePowerTraceRe (a := a) psi.state.matrix sigma tau p : EReal)
  calc
    (⨅ sigma : {sigma : State b // sigma.matrix.PosDef},
      ⨆ tau : State c,
        (State.abcSidePowerTraceRe (a := a) psi.state.matrix
          sigma.1.matrix tau.matrix p : EReal)) =
        ⨅ sigma : CMatrix b,
          ⨅ _hSigma : sigma ∈ State.fullRankDensityMatrixSet b,
            ⨆ tau : State c, F sigma tau.matrix := by
              exact fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf_source
                (fun sigma => ⨆ tau : State c, F sigma tau.matrix)
    _ = ⨅ sigma : CMatrix b,
          ⨅ _hSigma : sigma ∈ State.fullRankDensityMatrixSet b,
            ⨆ tau : CMatrix c,
              ⨆ _hTau : tau ∈ State.densityMatrixSet c, F sigma tau := by
              simp_rw [state_iSup_matrix_eq_densityMatrixSet_iSup_source]
    _ = ⨆ tau : CMatrix c,
          ⨆ _hTau : tau ∈ State.densityMatrixSet c,
            ⨅ sigma : CMatrix b,
              ⨅ _hSigma : sigma ∈ State.fullRankDensityMatrixSet b,
                F sigma tau := by
              exact State.fullRankDensityMatrixSet_sion_abcSidePowerTraceRe_EReal_boundary
                (a := a) (b := b) (c := c) psi.state.pos hp0 hp1.le
    _ = ⨆ tau : State c,
          ⨅ sigma : CMatrix b,
            ⨅ _hSigma : sigma ∈ State.fullRankDensityMatrixSet b,
              F sigma tau.matrix := by
              exact (state_iSup_matrix_eq_densityMatrixSet_iSup_source
                (fun tau => ⨅ sigma : CMatrix b,
                  ⨅ _hSigma : sigma ∈ State.fullRankDensityMatrixSet b,
                    F sigma tau)).symm
    _ = ⨆ tau : State c,
          ⨅ sigma : {sigma : State b // sigma.matrix.PosDef},
            (State.abcSidePowerTraceRe (a := a) psi.state.matrix
              sigma.1.matrix tau.matrix p : EReal) := by
              apply iSup_congr
              intro tau
              exact (fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf_source
                (fun sigma => F sigma tau.matrix)).symm

/-- The fixed-full-rank-`sigma_B` extended-real supremum of the source bracket
is the embedded Schatten `alpha` norm. -/
theorem upwardRenyiDualityHighBracket_iSup_EReal_eq
    [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c))
    (sigma : State b) (hsigma : sigma.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    (⨆ tau : State c,
      (State.abcSidePowerTraceRe (a := a) psi.state.matrix
        sigma.matrix tau.matrix (upwardRenyiDualityParameter alpha) : EReal)) =
      (psdSchattenPNorm
        (psi.upwardRenyiDualityHighCMatrix sigma.matrix
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.matrix
          (upwardRenyiDualityParameter alpha))
        ⟨alpha, lt_trans zero_lt_one halpha⟩ : EReal) := by
  letI : Nonempty (State c) := ⟨State.maximallyMixed c⟩
  let f : State c -> Real := fun tau =>
    State.abcSidePowerTraceRe (a := a) psi.state.matrix
      sigma.matrix tau.matrix (upwardRenyiDualityParameter alpha)
  let target : Real := psdSchattenPNorm
    (psi.upwardRenyiDualityHighCMatrix sigma.matrix
      (upwardRenyiDualityParameter alpha))
    (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.matrix
      (upwardRenyiDualityParameter alpha)) ⟨alpha, lt_trans zero_lt_one halpha⟩
  have hgreatest : IsGreatest (Set.range f) target := by
    simpa [f, target] using
      psi.upwardRenyiDualityHighBracket_isGreatest sigma hsigma halpha
  have hbdd : BddAbove (Set.range f) := ⟨target, hgreatest.2⟩
  change sSup (Set.range fun tau : State c => (f tau : EReal)) = (target : EReal)
  rw [ereal_sSup_range_coe_eq_coe_real_sSup f hbdd, hgreatest.csSup_eq]

/-- On the complete density domain, the support-aware bracket has exactly the
reverse-Holder Schatten `beta` norm as its infimum. -/
theorem upwardRenyiDualityLowBracket_density_iInf_EReal_eq
    [Nonempty b]
    (psi : PureVector (Prod (Prod a b) c)) (tau : State c)
    {alpha beta : Real} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    (⨅ sigma : State b,
      psi.upwardRenyiDualitySourceBracketEReal sigma.matrix tau.matrix
        (upwardRenyiDualityParameter alpha)) =
      (psdSchattenPNorm
        (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.matrix
          (upwardRenyiDualityParameter alpha))
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩ : EReal) := by
  let p := upwardRenyiDualityParameter alpha
  let target : Real := psdSchattenPNorm
    (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix p)
    (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.matrix p)
    ⟨beta, lt_trans (by norm_num) hbeta_half⟩
  have hleast : IsLeast (psi.upwardRenyiDualityLowBracketValueSet tau p) target := by
    simpa [p, target] using
      psi.upwardRenyiDualityLowBracket_isLeast tau
        halpha hbeta_half hbeta_one hconj
  apply le_antisymm
  · rcases hleast.1 with ⟨sigma, hsupport, hvalue⟩
    refine iInf_le_of_le sigma ?_
    rw [psi.upwardRenyiDualitySourceBracketEReal_of_supports
      sigma.matrix tau.matrix p hsupport]
    exact EReal.coe_le_coe_iff.mpr hvalue.symm.le
  · refine le_iInf fun sigma => ?_
    by_cases hsupport : Matrix.Supports
        (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix p) sigma.matrix
    · rw [psi.upwardRenyiDualitySourceBracketEReal_of_supports
        sigma.matrix tau.matrix p hsupport]
      exact EReal.coe_le_coe_iff.mpr (hleast.2 ⟨sigma, hsupport, rfl⟩)
    · rw [psi.upwardRenyiDualitySourceBracketEReal_of_not_supports
        sigma.matrix tau.matrix p hsupport]
      exact le_top

/-- The fixed-`tau_C` full-rank `sigma_B` infimum of the real source bracket
is the embedded reverse-Holder Schatten norm.  The equality uses the
support-aware identity-regularization closure, not an extra support
hypothesis. -/
theorem upwardRenyiDualityLowBracket_fullRank_iInf_EReal_eq
    [Nonempty b]
    (psi : PureVector (Prod (Prod a b) c)) (tau : State c)
    {alpha beta : Real} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    (⨅ sigma : {sigma : State b // sigma.matrix.PosDef},
      (State.abcSidePowerTraceRe (a := a) psi.state.matrix
        sigma.1.matrix tau.matrix (upwardRenyiDualityParameter alpha) : EReal)) =
      (psdSchattenPNorm
        (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.matrix
          (upwardRenyiDualityParameter alpha))
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩ : EReal) := by
  let p := upwardRenyiDualityParameter alpha
  calc
    (⨅ sigma : {sigma : State b // sigma.matrix.PosDef},
      (State.abcSidePowerTraceRe (a := a) psi.state.matrix
        sigma.1.matrix tau.matrix p : EReal)) =
        ⨅ sigma : CMatrix b,
          ⨅ _hSigma : sigma ∈ State.fullRankDensityMatrixSet b,
            (State.abcSidePowerTraceRe (a := a) psi.state.matrix
              sigma tau.matrix p : EReal) := by
                exact fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf_source
                  (d := b) (fun sigma : CMatrix b =>
                    (State.abcSidePowerTraceRe (a := a) psi.state.matrix
                      sigma tau.matrix p : EReal))
    _ = ⨅ sigma : CMatrix b,
          ⨅ _hSigma : sigma ∈ State.densityMatrixSet b,
            psi.upwardRenyiDualitySourceBracketEReal sigma tau.matrix p := by
              exact psi.upwardRenyiDualitySourceBracketEReal_fullRank_iInf_eq_density_iInf
                tau.matrix (State.state_matrix_mem_densityMatrixSet tau) p
    _ = ⨅ sigma : State b,
          psi.upwardRenyiDualitySourceBracketEReal sigma.matrix tau.matrix p := by
              exact (state_iInf_matrix_eq_densityMatrixSet_iInf_source _).symm
    _ = (psdSchattenPNorm
        (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix p)
        (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.matrix p)
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩ :
          EReal) := by
            simpa [p] using psi.upwardRenyiDualityLowBracket_density_iInf_EReal_eq
              tau halpha hbeta_half hbeta_one hconj

/-- Tomamichel's common Holder bracket identifies the infimum of the
high-order Schatten expression with the supremum of the complementary
low-order Schatten expression. -/
theorem upwardRenyiDuality_commonSchattenExtrema_eq
    [Nonempty b] [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c))
    {alpha beta : Real} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    sInf (Set.range fun sigma : {sigma : State b // sigma.matrix.PosDef} =>
      psdSchattenPNorm
        (psi.upwardRenyiDualityHighCMatrix sigma.1.matrix
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.1.matrix
          (upwardRenyiDualityParameter alpha))
        ⟨alpha, lt_trans zero_lt_one halpha⟩) =
      sSup (Set.range fun tau : State c =>
        psdSchattenPNorm
          (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix
            (upwardRenyiDualityParameter alpha))
          (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.matrix
            (upwardRenyiDualityParameter alpha))
          ⟨beta, lt_trans (by norm_num) hbeta_half⟩) := by
  let S := {sigma : State b // sigma.matrix.PosDef}
  let high : S -> Real := fun sigma =>
    psdSchattenPNorm
      (psi.upwardRenyiDualityHighCMatrix sigma.1.matrix
        (upwardRenyiDualityParameter alpha))
      (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.1.matrix
        (upwardRenyiDualityParameter alpha))
      ⟨alpha, lt_trans zero_lt_one halpha⟩
  let low : State c -> Real := fun tau =>
    psdSchattenPNorm
      (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix
        (upwardRenyiDualityParameter alpha))
      (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.matrix
        (upwardRenyiDualityParameter alpha))
      ⟨beta, lt_trans (by norm_num) hbeta_half⟩
  let sigma0 : S :=
    ⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩
  letI : Nonempty S := ⟨sigma0⟩
  letI : Nonempty (State c) := ⟨State.maximallyMixed c⟩
  have hhigh_bdd : BddBelow (Set.range high) := by
    refine ⟨0, ?_⟩
    rintro x ⟨sigma, rfl⟩
    exact psdSchattenPNorm_nonneg _ _ _
  have hlow_bdd : BddAbove (Set.range low) := by
    refine ⟨high sigma0, ?_⟩
    rintro x ⟨tau, rfl⟩
    have hleast := psi.upwardRenyiDualityLowBracket_isLeast tau
      halpha hbeta_half hbeta_one hconj
    have hsupport : Matrix.Supports
        (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix
          (upwardRenyiDualityParameter alpha)) sigma0.1.matrix :=
      Matrix.Supports.of_right_posDef _ _ sigma0.2
    have hlow_le : low tau <=
        State.abcSidePowerTraceRe (a := a) psi.state.matrix
          sigma0.1.matrix tau.matrix (upwardRenyiDualityParameter alpha) := by
      exact hleast.2 ⟨sigma0.1, hsupport, rfl⟩
    have hgreatest := psi.upwardRenyiDualityHighBracket_isGreatest
      sigma0.1 sigma0.2 halpha
    have hbracket_le :
        State.abcSidePowerTraceRe (a := a) psi.state.matrix
          sigma0.1.matrix tau.matrix (upwardRenyiDualityParameter alpha) <=
        high sigma0 := by
      exact hgreatest.2 ⟨tau, rfl⟩
    exact hlow_le.trans hbracket_le
  have hsion := psi.upwardRenyiDualitySource_fullRank_sion
    (upwardRenyiDualityParameter_pos halpha)
    (upwardRenyiDualityParameter_lt_one halpha)
  have hhigh (sigma : S) :=
    psi.upwardRenyiDualityHighBracket_iSup_EReal_eq
      sigma.1 sigma.2 (alpha := alpha) halpha
  have hlow (tau : State c) :=
    psi.upwardRenyiDualityLowBracket_fullRank_iInf_EReal_eq
      tau (alpha := alpha) (beta := beta)
        halpha hbeta_half hbeta_one hconj
  simp_rw [hhigh] at hsion
  simp_rw [hlow] at hsion
  change sInf (Set.range fun sigma : S => (high sigma : EReal)) =
    sSup (Set.range fun tau : State c => (low tau : EReal)) at hsion
  rw [ereal_sInf_range_coe_eq_coe_real_sInf_source high hhigh_bdd,
    ereal_sSup_range_coe_eq_coe_real_sSup low hlow_bdd] at hsion
  exact EReal.coe_eq_coe_iff.mp hsion

/-- The high-order `AB` entropy candidate is `-1/p` times the logarithm of
the Holder-side common Schatten value. -/
theorem upwardRenyiDualityABSourceCandidate_eq_highNormLog
    (psi : PureVector (Prod (Prod a b) c))
    (sigma : State b) (hsigma : sigma.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    psi.state.marginalAB.conditionalSandwichedRenyiUpSourceCandidate
        sigma hsigma alpha (lt_trans zero_lt_one halpha) (ne_of_gt halpha) =
      -(1 / upwardRenyiDualityParameter alpha) *
        log2 (psdSchattenPNorm
          (psi.upwardRenyiDualityHighCMatrix sigma.matrix
            (upwardRenyiDualityParameter alpha))
          (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.matrix
            (upwardRenyiDualityParameter alpha))
          ⟨alpha, lt_trans zero_lt_one halpha⟩) := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have halpha_one : alpha ≠ 1 := ne_of_gt halpha
  rw [State.conditionalSandwichedRenyiUpSourceCandidate_eq_schattenLog
    psi.state.marginalAB sigma hsigma halpha_pos halpha_one]
  rw [psi.psdSchattenPNorm_highReferenceInner_eq_highCMatrix
    sigma hsigma halpha]
  congr 1
  unfold upwardRenyiDualityParameter
  field_simp [ne_of_gt halpha_pos, halpha_one]

/-- The low-order `AC` entropy candidate is `1/p` times the logarithm of the
reverse-Holder-side common Schatten value. -/
theorem upwardRenyiDualityACSourceCandidate_eq_lowNormLog
    (psi : PureVector (Prod (Prod a b) c))
    (tau : State c) (htau : tau.matrix.PosDef)
    {alpha beta : Real} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    psi.state.marginalAC.conditionalSandwichedRenyiUpSourceCandidate
        tau htau beta (lt_trans (by norm_num) hbeta_half) (ne_of_lt hbeta_one) =
      (1 / upwardRenyiDualityParameter alpha) *
        log2 (psdSchattenPNorm
          (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix
            (upwardRenyiDualityParameter alpha))
          (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.matrix
            (upwardRenyiDualityParameter alpha))
          ⟨beta, lt_trans (by norm_num) hbeta_half⟩) := by
  have hbeta_pos : 0 < beta := lt_trans (by norm_num) hbeta_half
  have hbeta_one_ne : beta ≠ 1 := ne_of_lt hbeta_one
  rw [State.conditionalSandwichedRenyiUpSourceCandidate_eq_schattenLog
    psi.state.marginalAC tau htau hbeta_pos hbeta_one_ne]
  rw [psi.psdSchattenPNorm_lowReferenceInner_eq_effectiveBMatrix
    tau halpha hbeta_half hbeta_one hconj]
  congr 1
  rw [upwardRenyiDualityParameter_eq_beta halpha hconj]
  field_simp [ne_of_gt hbeta_pos, hbeta_one_ne]
  ring

/-- The effective reverse-Holder matrix is continuous along normalized
identity regularization of the `C` side state. -/
theorem upwardRenyiDualityEffectiveBMatrix_densityIdentityRegularization_tendsto
    [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c)) (tau : State c)
    {p : Real} (hp : 0 < p) :
    Filter.Tendsto
      (fun epsilon : Real =>
        psi.upwardRenyiDualityEffectiveBMatrix
          (State.densityIdentityRegularization tau epsilon).matrix p)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix p)) := by
  let K : CMatrix (Prod (Prod a c) b) :=
    rankOneMatrix psi.upwardRenyiDualityACBAmplitude
  let G : CMatrix c -> CMatrix b := fun T =>
    partialTraceA (a := Prod a c) (b := b)
      (Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) T)
        (1 : CMatrix b) * K)
  have hG : Continuous G := by
    have hinner : Continuous (fun T : CMatrix c =>
        Matrix.kronecker (1 : CMatrix a) T) :=
      continuous_identity_kronecker_source
    have houter : Continuous (fun T : CMatrix c =>
        Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) T)
          (1 : CMatrix b)) :=
      continuous_kronecker_right_one_source.comp hinner
    have harg : Continuous (fun T : CMatrix c =>
        Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) T)
          (1 : CMatrix b) * K) :=
      Continuous.matrix_mul houter continuous_const
    simpa [G, Function.comp_def] using continuous_partialTraceA_source.comp harg
  have htau := densityIdentityRegularization_matrix_tendsto_source tau
  have hpow : Filter.Tendsto
      (fun epsilon : Real => CFC.rpow
        (State.densityIdentityRegularization tau epsilon).matrix p)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (CFC.rpow tau.matrix p)) :=
    cMatrix_rpow_tendsto_of_tendsto_posSemidef hp htau
      (Filter.Eventually.of_forall fun epsilon =>
        (State.densityIdentityRegularization tau epsilon).pos) tau.pos
  have hcomp : Filter.Tendsto
      (fun epsilon : Real => G (CFC.rpow
        (State.densityIdentityRegularization tau epsilon).matrix p))
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (G (CFC.rpow tau.matrix p))) := hG.continuousAt.tendsto.comp hpow
  have heq (rho : State c) :
      psi.upwardRenyiDualityEffectiveBMatrix rho.matrix p =
        G (CFC.rpow rho.matrix p) := by
    rw [psi.upwardRenyiDualityEffectiveBMatrix_eq_partialTrace_weight_mul
      rho.matrix p rho.pos]
    rfl
  have hcomp' : Filter.Tendsto
      (fun epsilon : Real =>
        psi.upwardRenyiDualityEffectiveBMatrix
          (State.densityIdentityRegularization tau epsilon).matrix p)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (G (CFC.rpow tau.matrix p))) := by
    apply hcomp.congr'
    exact Filter.Eventually.of_forall fun epsilon => (heq _).symm
  simpa [heq tau] using hcomp'

/-- The complementary low-order Schatten value is continuous along normalized
identity regularization. -/
theorem upwardRenyiDualityLowNorm_densityIdentityRegularization_tendsto
    [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c)) (tau : State c)
    {p beta : Real} (hp : 0 < p) (hbeta : 0 < beta) :
    Filter.Tendsto
      (fun epsilon : Real =>
        psdSchattenPNorm
          (psi.upwardRenyiDualityEffectiveBMatrix
            (State.densityIdentityRegularization tau epsilon).matrix p)
          (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef
            (State.densityIdentityRegularization tau epsilon).matrix p)
          ⟨beta, hbeta⟩)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (psdSchattenPNorm
        (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix p)
        (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.matrix p)
        ⟨beta, hbeta⟩)) := by
  exact psdSchattenPNorm_tendsto_of_tendsto_posSemidef ⟨beta, hbeta⟩
    (psi.upwardRenyiDualityEffectiveBMatrix_densityIdentityRegularization_tendsto
      tau hp)
    (fun epsilon =>
      psi.upwardRenyiDualityEffectiveBMatrix_posSemidef
        (State.densityIdentityRegularization tau epsilon).matrix p)
    (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.matrix p)

/-- For the low-order branch, optimizing over full-rank normalized `C` states
has the same supremum as optimizing over the closed density-state domain.
This is the explicit dense-domain closure used by
`State.conditionalSandwichedRenyiUpSource`, and is the source
identity-regularization step for the compact variable. -/
theorem upwardRenyiDualityLowNorm_fullRank_sSup_eq_all
    [Nonempty b] [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c))
    {alpha beta : Real} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    sSup (Set.range fun tau : {tau : State c // tau.matrix.PosDef} =>
      psdSchattenPNorm
        (psi.upwardRenyiDualityEffectiveBMatrix tau.1.matrix
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.1.matrix
          (upwardRenyiDualityParameter alpha))
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩) =
      sSup (Set.range fun tau : State c =>
        psdSchattenPNorm
          (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix
            (upwardRenyiDualityParameter alpha))
          (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.matrix
            (upwardRenyiDualityParameter alpha))
          ⟨beta, lt_trans (by norm_num) hbeta_half⟩) := by
  let T := {tau : State c // tau.matrix.PosDef}
  let full : T -> Real := fun tau =>
    psdSchattenPNorm
      (psi.upwardRenyiDualityEffectiveBMatrix tau.1.matrix
        (upwardRenyiDualityParameter alpha))
      (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.1.matrix
        (upwardRenyiDualityParameter alpha))
      ⟨beta, lt_trans (by norm_num) hbeta_half⟩
  let all : State c -> Real := fun tau =>
    psdSchattenPNorm
      (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix
        (upwardRenyiDualityParameter alpha))
      (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.matrix
        (upwardRenyiDualityParameter alpha))
      ⟨beta, lt_trans (by norm_num) hbeta_half⟩
  let sigma0 : {sigma : State b // sigma.matrix.PosDef} :=
    ⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩
  let tau0 : T :=
    ⟨State.maximallyMixed c, State.maximallyMixed_posDef⟩
  letI : Nonempty T := ⟨tau0⟩
  letI : Nonempty (State c) := ⟨tau0.1⟩
  have hall_bdd : BddAbove (Set.range all) := by
    let high0 : Real := psdSchattenPNorm
      (psi.upwardRenyiDualityHighCMatrix sigma0.1.matrix
        (upwardRenyiDualityParameter alpha))
      (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma0.1.matrix
        (upwardRenyiDualityParameter alpha))
      ⟨alpha, lt_trans zero_lt_one halpha⟩
    refine ⟨high0, ?_⟩
    rintro x ⟨tau, rfl⟩
    have hleast := psi.upwardRenyiDualityLowBracket_isLeast tau
      halpha hbeta_half hbeta_one hconj
    have hsupport : Matrix.Supports
        (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix
          (upwardRenyiDualityParameter alpha)) sigma0.1.matrix :=
      Matrix.Supports.of_right_posDef _ _ sigma0.2
    have hlow : all tau <=
        State.abcSidePowerTraceRe (a := a) psi.state.matrix
          sigma0.1.matrix tau.matrix (upwardRenyiDualityParameter alpha) :=
      hleast.2 ⟨sigma0.1, hsupport, rfl⟩
    have hhigh := psi.upwardRenyiDualityHighBracket_isGreatest
      sigma0.1 sigma0.2 halpha
    exact hlow.trans (hhigh.2 ⟨tau, rfl⟩)
  have hfull_bdd : BddAbove (Set.range full) := by
    rcases hall_bdd with ⟨upper, hupper⟩
    refine ⟨upper, ?_⟩
    rintro x ⟨tau, rfl⟩
    exact hupper ⟨tau.1, rfl⟩
  apply le_antisymm
  · refine csSup_le (Set.range_nonempty full) ?_
    rintro x ⟨tau, rfl⟩
    exact le_csSup hall_bdd ⟨tau.1, rfl⟩
  · refine csSup_le (Set.range_nonempty all) ?_
    rintro x ⟨tau, rfl⟩
    have htend := psi.upwardRenyiDualityLowNorm_densityIdentityRegularization_tendsto
      tau (upwardRenyiDualityParameter_pos halpha)
        (lt_trans (by norm_num) hbeta_half)
    refine le_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    let tauE : T :=
      ⟨State.densityIdentityRegularization tau epsilon,
        State.densityIdentityRegularization_posDef_of_pos tau hepsilon⟩
    exact le_csSup hfull_bdd ⟨tauE, rfl⟩

theorem upwardRenyiDualityHighNorm_pos
    (psi : PureVector (Prod (Prod a b) c))
    (sigma : State b) (hsigma : sigma.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    0 < psi.upwardRenyiDualityHighNorm sigma
      ⟨alpha, lt_trans zero_lt_one halpha⟩ := by
  have href : (State.identityTensorStateMatrix (a := a) sigma).PosDef :=
    State.identityTensorStateMatrix_posDef_of_posDef (a := a) sigma hsigma
  have hne := State.sandwichedRenyiReferenceInner_ne_zero_of_reference_posDef
    psi.state.marginalAB href alpha
  have hpos := psdSchattenPNorm_pos_of_ne_zero
    (State.sandwichedRenyiReferenceInner psi.state.marginalAB
      (State.identityTensorStateMatrix (a := a) sigma) alpha)
    (State.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAB
      (State.identityTensorStateMatrix_posSemidef (a := a) sigma) alpha)
    (p := ⟨alpha, lt_trans zero_lt_one halpha⟩) hne
  rw [psi.psdSchattenPNorm_highReferenceInner_eq_highCMatrix
    sigma hsigma halpha] at hpos
  exact hpos

theorem upwardRenyiDualityLowNorm_pos_of_posDef
    (psi : PureVector (Prod (Prod a b) c))
    (tau : State c) (htau : tau.matrix.PosDef)
    {alpha beta : Real} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    0 < psi.upwardRenyiDualityLowNorm tau alpha
      ⟨beta, lt_trans (by norm_num) hbeta_half⟩ := by
  have href : (State.identityTensorStateMatrix (a := a) tau).PosDef :=
    State.identityTensorStateMatrix_posDef_of_posDef (a := a) tau htau
  have hne := State.sandwichedRenyiReferenceInner_ne_zero_of_reference_posDef
    psi.state.marginalAC href beta
  have hpos := psdSchattenPNorm_pos_of_ne_zero
    (State.sandwichedRenyiReferenceInner psi.state.marginalAC
      (State.identityTensorStateMatrix (a := a) tau) beta)
    (State.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAC
      (State.identityTensorStateMatrix_posSemidef (a := a) tau) beta)
    (p := ⟨beta, lt_trans (by norm_num) hbeta_half⟩) hne
  rw [psi.psdSchattenPNorm_lowReferenceInner_eq_effectiveBMatrix
    tau halpha hbeta_half hbeta_one hconj] at hpos
  exact hpos

theorem upwardRenyiDualityLowNorm_range_bddAbove
    [Nonempty b] [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c))
    {alpha beta : Real} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    BddAbove (Set.range fun tau : State c =>
      psi.upwardRenyiDualityLowNorm tau alpha
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩) := by
  let sigma0 : {sigma : State b // sigma.matrix.PosDef} :=
    ⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩
  refine ⟨psi.upwardRenyiDualityHighNorm sigma0.1
    ⟨alpha, lt_trans zero_lt_one halpha⟩, ?_⟩
  rintro x ⟨tau, rfl⟩
  have hleast := psi.upwardRenyiDualityLowBracket_isLeast tau
    halpha hbeta_half hbeta_one hconj
  have hsupport : Matrix.Supports
      (psi.upwardRenyiDualityEffectiveBMatrix tau.matrix
        (upwardRenyiDualityParameter alpha)) sigma0.1.matrix :=
    Matrix.Supports.of_right_posDef _ _ sigma0.2
  have hlow : psi.upwardRenyiDualityLowNorm tau alpha
      ⟨beta, lt_trans (by norm_num) hbeta_half⟩ <=
      State.abcSidePowerTraceRe (a := a) psi.state.matrix
        sigma0.1.matrix tau.matrix (upwardRenyiDualityParameter alpha) := by
    exact hleast.2 ⟨sigma0.1, hsupport, rfl⟩
  have hhigh := psi.upwardRenyiDualityHighBracket_isGreatest
    sigma0.1 sigma0.2 halpha
  exact hlow.trans (hhigh.2 ⟨tau, rfl⟩)

private theorem upwardRenyiDuality_commonSchattenExtrema_eq_named
    [Nonempty b] [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c))
    {alpha beta : Real} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    sInf (Set.range fun sigma : {sigma : State b // sigma.matrix.PosDef} =>
      psi.upwardRenyiDualityHighNorm sigma.1
        ⟨alpha, lt_trans zero_lt_one halpha⟩) =
      sSup (Set.range fun tau : State c =>
        psi.upwardRenyiDualityLowNorm tau alpha
          ⟨beta, lt_trans (by norm_num) hbeta_half⟩) := by
  simpa [upwardRenyiDualityHighNorm, upwardRenyiDualityLowNorm] using
    psi.upwardRenyiDuality_commonSchattenExtrema_eq
      halpha hbeta_half hbeta_one hconj

private theorem upwardRenyiDualityLowNorm_fullRank_sSup_eq_all_named
    [Nonempty b] [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c))
    {alpha beta : Real} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    sSup (Set.range fun tau : {tau : State c // tau.matrix.PosDef} =>
      psi.upwardRenyiDualityLowNorm tau.1 alpha
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩) =
      sSup (Set.range fun tau : State c =>
      psi.upwardRenyiDualityLowNorm tau alpha
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩) := by
  simpa [upwardRenyiDualityLowNorm] using
    psi.upwardRenyiDualityLowNorm_fullRank_sSup_eq_all
      halpha hbeta_half hbeta_one hconj

theorem upwardRenyiDuality_commonSchattenExtremum_pos
    [Nonempty b] [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c))
    {alpha beta : Real} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    0 < sInf (Set.range fun sigma : {sigma : State b // sigma.matrix.PosDef} =>
      psi.upwardRenyiDualityHighNorm sigma.1
        ⟨alpha, lt_trans zero_lt_one halpha⟩) := by
  rw [psi.upwardRenyiDuality_commonSchattenExtrema_eq_named
    halpha hbeta_half hbeta_one hconj]
  rw [← psi.upwardRenyiDualityLowNorm_fullRank_sSup_eq_all_named
    halpha hbeta_half hbeta_one hconj]
  let tau0 : {tau : State c // tau.matrix.PosDef} :=
    ⟨State.maximallyMixed c, State.maximallyMixed_posDef⟩
  have hall_bdd := psi.upwardRenyiDualityLowNorm_range_bddAbove
    halpha hbeta_half hbeta_one hconj
  have hfull_bdd : BddAbove (Set.range fun tau :
      {tau : State c // tau.matrix.PosDef} =>
        psi.upwardRenyiDualityLowNorm tau.1 alpha
          ⟨beta, lt_trans (by norm_num) hbeta_half⟩) := by
    rcases hall_bdd with ⟨upper, hupper⟩
    refine ⟨upper, ?_⟩
    rintro x ⟨tau, rfl⟩
    exact hupper ⟨tau.1, rfl⟩
  exact (psi.upwardRenyiDualityLowNorm_pos_of_posDef tau0.1 tau0.2
    halpha hbeta_half hbeta_one hconj).trans_le
      (le_csSup hfull_bdd ⟨tau0, rfl⟩)

/-- High-order source entropy as the negative logarithm of the common
Schatten extremum. -/
theorem conditionalSandwichedRenyiUpSource_marginalAB_eq_commonLog
    [Nonempty b] [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c))
    {alpha beta : Real} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    psi.state.marginalAB.conditionalSandwichedRenyiUpSource alpha
        (lt_trans zero_lt_one halpha) (ne_of_gt halpha) =
      -(1 / upwardRenyiDualityParameter alpha) *
        log2 (sInf (Set.range fun sigma :
          {sigma : State b // sigma.matrix.PosDef} =>
            psi.upwardRenyiDualityHighNorm sigma.1
              ⟨alpha, lt_trans zero_lt_one halpha⟩)) := by
  let S := {sigma : State b // sigma.matrix.PosDef}
  let high : S -> Real := fun sigma =>
    psi.upwardRenyiDualityHighNorm sigma.1
      ⟨alpha, lt_trans zero_lt_one halpha⟩
  let coeff : Real := 1 / upwardRenyiDualityParameter alpha
  let candidate : S -> Real := fun sigma =>
    psi.state.marginalAB.conditionalSandwichedRenyiUpSourceCandidate
      sigma.1 sigma.2 alpha (lt_trans zero_lt_one halpha) (ne_of_gt halpha)
  letI : Nonempty S :=
    ⟨⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩⟩
  have hp : 0 < upwardRenyiDualityParameter alpha :=
    upwardRenyiDualityParameter_pos halpha
  have hcoeff : 0 <= coeff := (one_div_pos.mpr hp).le
  have hcandidate (sigma : S) :
      candidate sigma = coeff * (-log2 (high sigma)) := by
    rw [show candidate sigma =
      -(1 / upwardRenyiDualityParameter alpha) * log2 (high sigma) by
        simpa [candidate, high, upwardRenyiDualityHighNorm] using
          psi.upwardRenyiDualityABSourceCandidate_eq_highNormLog
            sigma.1 sigma.2 halpha]
    simp [coeff]
  have hhigh_bdd : BddBelow (Set.range high) := by
    refine ⟨0, ?_⟩
    rintro x ⟨sigma, rfl⟩
    exact psdSchattenPNorm_nonneg _ _ _
  have hinf_pos : 0 < sInf (Set.range high) := by
    simpa [high, upwardRenyiDualityHighNorm] using
      psi.upwardRenyiDuality_commonSchattenExtremum_pos
        halpha hbeta_half hbeta_one hconj
  have himage : Set.range (fun sigma : S => -log2 (high sigma)) =
      (fun x : Real => -log2 x) '' Set.range high := by
    ext x
    constructor
    · rintro ⟨sigma, rfl⟩
      exact ⟨high sigma, ⟨sigma, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨sigma, rfl⟩, rfl⟩
      exact ⟨sigma, rfl⟩
  unfold State.conditionalSandwichedRenyiUpSource
  rw [State.conditionalSandwichedRenyiUpSourceValueSet_eq_range]
  change sSup (Set.range candidate) = _
  calc
    sSup (Set.range candidate) =
        sSup (Set.range fun sigma : S => coeff * (-log2 (high sigma))) := by
          congr 1
          ext x
          constructor <;> rintro ⟨sigma, rfl⟩
          · exact ⟨sigma, (hcandidate sigma).symm⟩
          · exact ⟨sigma, hcandidate sigma⟩
    _ = coeff * sSup (Set.range fun sigma : S => -log2 (high sigma)) :=
      sSup_range_mul_eq_mul_sSup_range_source _ hcoeff
    _ = coeff * (-log2 (sInf (Set.range high))) := by
      rw [himage, neg_log2_sInf_image_eq
        (Set.range_nonempty high) hhigh_bdd hinf_pos]
    _ = -(1 / upwardRenyiDualityParameter alpha) *
        log2 (sInf (Set.range high)) := by simp [coeff]

/-- Low-order source entropy as the positive logarithm of the same common
Schatten extremum, with the full-rank optimization retained. -/
theorem conditionalSandwichedRenyiUpSource_marginalAC_eq_commonLog
    [Nonempty b] [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c))
    {alpha beta : Real} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    psi.state.marginalAC.conditionalSandwichedRenyiUpSource beta
        (lt_trans (by norm_num) hbeta_half) (ne_of_lt hbeta_one) =
      (1 / upwardRenyiDualityParameter alpha) *
        log2 (sSup (Set.range fun tau :
          {tau : State c // tau.matrix.PosDef} =>
            psi.upwardRenyiDualityLowNorm tau.1 alpha
              ⟨beta, lt_trans (by norm_num) hbeta_half⟩)) := by
  let T := {tau : State c // tau.matrix.PosDef}
  let low : T -> Real := fun tau =>
    psi.upwardRenyiDualityLowNorm tau.1 alpha
      ⟨beta, lt_trans (by norm_num) hbeta_half⟩
  let coeff : Real := 1 / upwardRenyiDualityParameter alpha
  let candidate : T -> Real := fun tau =>
    psi.state.marginalAC.conditionalSandwichedRenyiUpSourceCandidate
      tau.1 tau.2 beta (lt_trans (by norm_num) hbeta_half) (ne_of_lt hbeta_one)
  letI : Nonempty T :=
    ⟨⟨State.maximallyMixed c, State.maximallyMixed_posDef⟩⟩
  have hp : 0 < upwardRenyiDualityParameter alpha :=
    upwardRenyiDualityParameter_pos halpha
  have hcoeff : 0 <= coeff := (one_div_pos.mpr hp).le
  have hcandidate (tau : T) : candidate tau = coeff * log2 (low tau) := by
    simpa [candidate, low, coeff, upwardRenyiDualityLowNorm] using
      psi.upwardRenyiDualityACSourceCandidate_eq_lowNormLog
        tau.1 tau.2 halpha hbeta_half hbeta_one hconj
  have hall_bdd := psi.upwardRenyiDualityLowNorm_range_bddAbove
    halpha hbeta_half hbeta_one hconj
  have hlow_bdd : BddAbove (Set.range low) := by
    rcases hall_bdd with ⟨upper, hupper⟩
    refine ⟨upper, ?_⟩
    rintro x ⟨tau, rfl⟩
    exact hupper ⟨tau.1, rfl⟩
  have hlow_pos : ∀ x ∈ Set.range low, 0 < x := by
    rintro x ⟨tau, rfl⟩
    exact psi.upwardRenyiDualityLowNorm_pos_of_posDef tau.1 tau.2
      halpha hbeta_half hbeta_one hconj
  have himage : Set.range (fun tau : T => log2 (low tau)) =
      log2 '' Set.range low := by
    ext x
    constructor
    · rintro ⟨tau, rfl⟩
      exact ⟨low tau, ⟨tau, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨tau, rfl⟩, rfl⟩
      exact ⟨tau, rfl⟩
  unfold State.conditionalSandwichedRenyiUpSource
  rw [State.conditionalSandwichedRenyiUpSourceValueSet_eq_range]
  change sSup (Set.range candidate) = _
  calc
    sSup (Set.range candidate) =
        sSup (Set.range fun tau : T => coeff * log2 (low tau)) := by
          congr 1
          ext x
          constructor <;> rintro ⟨tau, rfl⟩
          · exact ⟨tau, (hcandidate tau).symm⟩
          · exact ⟨tau, hcandidate tau⟩
    _ = coeff * sSup (Set.range fun tau : T => log2 (low tau)) :=
      sSup_range_mul_eq_mul_sSup_range_source _ hcoeff
    _ = coeff * log2 (sSup (Set.range low)) := by
      rw [himage, log2_sSup_image_eq
        (Set.range_nonempty low) hlow_bdd hlow_pos]

/-- Tomamichel's normalized pure-state upward sandwiched conditional Renyi
duality (`cond.tex`, Proposition `pr:dual-new`).  Singular marginals are
allowed: support failures are accounted for by the support-aware extended
bracket before the Sion exchange. -/
theorem conditionalSandwichedRenyiUpSource_duality
    [Nonempty b] [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c))
    {alpha beta : Real} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    psi.state.marginalAB.conditionalSandwichedRenyiUpSource alpha
        (lt_trans zero_lt_one halpha) (ne_of_gt halpha) +
      psi.state.marginalAC.conditionalSandwichedRenyiUpSource beta
        (lt_trans (by norm_num) hbeta_half) (ne_of_lt hbeta_one) = 0 := by
  rw [psi.conditionalSandwichedRenyiUpSource_marginalAB_eq_commonLog
      halpha hbeta_half hbeta_one hconj,
    psi.conditionalSandwichedRenyiUpSource_marginalAC_eq_commonLog
      halpha hbeta_half hbeta_one hconj]
  have hextrema := psi.upwardRenyiDuality_commonSchattenExtrema_eq_named
    halpha hbeta_half hbeta_one hconj
  have hfullRank := psi.upwardRenyiDualityLowNorm_fullRank_sSup_eq_all_named
    halpha hbeta_half hbeta_one hconj
  rw [hextrema, ← hfullRank]
  ring

end PureVector

namespace SubnormalizedState

/-- The positive-trace extension of the source-shaped upward sandwiched
conditional Renyi entropy.  It uses Tomamichel's convention
`H_tilde^up_alpha(t rho) = H_tilde^up_alpha(rho) - log2 t`. -/
noncomputable def conditionalSandwichedRenyiUpSource
    (rho : SubnormalizedState (Prod a b)) (alpha : Real)
    (hAlphaPos : 0 < alpha) (hAlphaNeOne : alpha ≠ 1)
    (htrace : 0 < rho.matrix.trace.re) : Real :=
  (rho.normalize htrace.ne').conditionalSandwichedRenyiUpSource
      alpha hAlphaPos hAlphaNeOne -
    log2 rho.matrix.trace.re

theorem normalize_ofStateScale
    (rho : State (Prod a b)) {t : Real} (ht : 0 < t) (ht1 : t <= 1) :
    (ofStateScale rho t ht.le ht1).normalize
        (by rw [ofStateScale_trace_re]; exact ht.ne') = rho := by
  apply State.ext
  rw [normalize_matrix, ofStateScale_trace_re, ofStateScale_matrix]
  ext i j
  simp [ht.ne']

/-- Scaling a normalized bipartite state shifts the source entropy by
`-log2 t`. -/
theorem conditionalSandwichedRenyiUpSource_ofStateScale
    (rho : State (Prod a b)) {t alpha : Real}
    (hAlphaPos : 0 < alpha) (hAlphaNeOne : alpha ≠ 1)
    (ht : 0 < t) (ht1 : t <= 1) :
    (ofStateScale rho t ht.le ht1).conditionalSandwichedRenyiUpSource alpha
        hAlphaPos hAlphaNeOne
        (by rw [ofStateScale_trace_re]; exact ht) =
      rho.conditionalSandwichedRenyiUpSource alpha hAlphaPos hAlphaNeOne - log2 t := by
  unfold conditionalSandwichedRenyiUpSource
  rw [normalize_ofStateScale rho ht ht1, ofStateScale_trace_re]

/-- Lean-derived positive-trace scaled-pure extension of Tomamichel's
normalized upward sandwiched conditional Renyi duality.  Each complementary
marginal contributes the same `-log2 t` normalization shift under the accepted
subnormalized scaling convention. -/
theorem conditionalSandwichedRenyiUpSource_duality_of_scaled_pure
    [Nonempty b] [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c))
    {alpha beta t : Real} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2)
    (ht : 0 < t) (ht1 : t <= 1) :
    (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
      psi t ht.le ht1).conditionalSandwichedRenyiUpSource alpha
        (lt_trans zero_lt_one halpha) (ne_of_gt halpha)
        (by rw [abMarginalFromScaledTripartitePure, ofStateScale_trace_re]; exact ht) +
      (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        psi t ht.le ht1).conditionalSandwichedRenyiUpSource beta
          (lt_trans (by norm_num) hbeta_half) (ne_of_lt hbeta_one)
          (by rw [acMarginalFromScaledTripartitePure, ofStateScale_trace_re]; exact ht) =
        -2 * log2 t := by
  unfold abMarginalFromScaledTripartitePure acMarginalFromScaledTripartitePure
  rw [conditionalSandwichedRenyiUpSource_ofStateScale psi.state.marginalAB
      (lt_trans zero_lt_one halpha) (ne_of_gt halpha) ht ht1,
    conditionalSandwichedRenyiUpSource_ofStateScale psi.state.marginalAC
      (lt_trans (by norm_num) hbeta_half) (ne_of_lt hbeta_one) ht ht1]
  have hdual := psi.conditionalSandwichedRenyiUpSource_duality
    halpha hbeta_half hbeta_one hconj
  linarith

end SubnormalizedState

end


end QIT
