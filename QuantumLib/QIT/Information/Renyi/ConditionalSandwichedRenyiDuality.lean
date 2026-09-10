/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Renyi.ConditionalRenyiMinimaxBoundary
public import QuantumLib.QIT.Information.Renyi.ConditionalRenyiSource
public import QuantumLib.QIT.Information.Renyi.RenyiDPIStatement
public import QuantumLib.QIT.States.Purification.Schatten
public import QuantumLib.QIT.Util.Order.EReal

/-!
# Upward sandwiched conditional Renyi duality

Tomamichel's pure-state duality theorem for the upward sandwiched conditional
Renyi entropy.  The proof follows `cond.tex`, Proposition `pr:dual-new`, lines
361--397: Holder and reverse-Holder extrema are identified through the pure
`AB`/`AC` trace bridge, and the resulting common bracket is exchanged by the
support-aware Sion theorem.

Unlike `conditionalSandwichedRenyiUp`, the source-shaped quantity below
does not require the input state to be positive definite.  The optimizing side
states are normalized; singular support is handled by the extended bracket in
`ConditionalRenyiMinimaxBoundary`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker NNReal ENNReal Pointwise

open Matrix

noncomputable section
universe u v w
variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

open QIT

namespace QIT

private theorem continuous_kronecker_right_one
    {d : Type*} {e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e] :
    Continuous (fun X : CMatrix d => X ⊗ₖ (1 : CMatrix e)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp [Matrix.kroneckerMap_apply]
  exact (continuous_apply_apply i.1 j.1).mul continuous_const

private theorem continuous_traceLeft
    {d : Type*} {e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e] :
    Continuous (fun X : CMatrix (d × e) =>
      Matrix.traceLeft X) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp [Matrix.traceLeft]
  fun_prop

private theorem sSup_range_mul_eq_mul_sSup_range
    {i : Type*} [Nonempty i] (f : i → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    sSup (Set.range fun x : i => c * f x) = c * sSup (Set.range f) := by
  have himage : Set.range (fun x : i => c * f x) =
      ((c : ℝ) • (Set.range f : Set ℝ) : Set ℝ) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Set.mem_smul_set.mpr ⟨f x, ⟨x, rfl⟩, by simp [smul_eq_mul]⟩
    · intro hy
      rcases Set.mem_smul_set.mp hy with ⟨z, ⟨x, rfl⟩, hy⟩
      exact ⟨x, by simpa [smul_eq_mul] using hy⟩
  rw [himage, Real.sSup_smul_of_nonneg hc]
  simp [smul_eq_mul]

end QIT

namespace MState

/-- The source-shaped full-rank-side candidate for
`H_tilde^up_alpha(A|B)_rho`, without a positive-definiteness assumption on
`rho`.

The matrix expression is exactly the one used by
`conditionalSandwichedRenyiCandidate`, minus its unused input-state
positive-definiteness witness.  The explicit order guards prevent the raw
logarithmic formula from being exposed as an entropy at `alpha = 1`. -/
def conditionalSandwichedRenyiUpSourceCandidate
    (rho : MState (a × b)) (sigma : MState b) (_hsigma : sigma.m.PosDef)
    (alpha : ℝ) (_hAlphaPos : 0 < alpha) (_hAlphaNeOne : alpha ≠ 1) : ℝ :=
  let r := -(1 / (alpha - 1))
  let s := (1 - alpha) / (2 * alpha)
  let tau : CMatrix (a × b) := identityTensorStateMatrix (a := a) sigma
  let M := CFC.rpow (CFC.rpow tau s * rho.m * CFC.rpow tau s) alpha
  r * log2 M.trace.re

/-- Candidate values for the source-shaped upward sandwiched conditional
Renyi entropy. -/
def conditionalSandwichedRenyiUpSourceValueSet
    (rho : MState (a × b)) (alpha : ℝ)
    (hAlphaPos : 0 < alpha) (hAlphaNeOne : alpha ≠ 1) : Set ℝ :=
  {x | ∃ sigma : MState b, ∃ hsigma : sigma.m.PosDef,
    x = rho.conditionalSandwichedRenyiUpSourceCandidate
      sigma hsigma alpha hAlphaPos hAlphaNeOne}

/-- Source-shaped upward sandwiched conditional Renyi entropy.

The optimization over normalized full-rank side states is the proved dense
implementation of Tomamichel's normalized side-state domain.  Singular side
states and support failures are supplied by the support-aware boundary theorem
and identity-regularization closure below.  No full-rank condition is imposed
on the input state. -/
def conditionalSandwichedRenyiUpSource
    (rho : MState (a × b)) (alpha : ℝ)
    (hAlphaPos : 0 < alpha) (hAlphaNeOne : alpha ≠ 1) : ℝ :=
  sSup (rho.conditionalSandwichedRenyiUpSourceValueSet
    alpha hAlphaPos hAlphaNeOne)

@[simp]
theorem conditionalSandwichedRenyiUpSource_eq
    (rho : MState (a × b)) (alpha : ℝ)
    (hAlphaPos : 0 < alpha) (hAlphaNeOne : alpha ≠ 1) :
    rho.conditionalSandwichedRenyiUpSource alpha hAlphaPos hAlphaNeOne =
      sSup (rho.conditionalSandwichedRenyiUpSourceValueSet
        alpha hAlphaPos hAlphaNeOne) :=
  rfl

/-- On the positive-definite domain, the source-shaped candidate is
definitionally `conditionalSandwichedRenyiCandidate`. -/
theorem conditionalSandwichedRenyiUpSourceCandidate_eq_conditionalSandwichedRenyiCandidate
    (rho : MState (a × b)) (hrho : rho.m.PosDef)
    (sigma : MState b) (hsigma : sigma.m.PosDef)
    (alpha : ℝ) (halpha : 0 < alpha) (halpha_one : alpha ≠ 1) :
    rho.conditionalSandwichedRenyiUpSourceCandidate
        sigma hsigma alpha halpha halpha_one =
      rho.conditionalSandwichedRenyiCandidate hrho sigma hsigma alpha
        halpha halpha_one :=
  rfl

/-- Agreement with the positive-definite upward conditional sandwiched Renyi
entropy. -/
theorem conditionalSandwichedRenyiUpSource_eq_conditionalSandwichedRenyiUp
    (rho : MState (a × b)) (hrho : rho.m.PosDef)
    (alpha : ℝ) (halpha : 1 / 2 ≤ alpha) (halpha_one : alpha ≠ 1) :
    rho.conditionalSandwichedRenyiUpSource alpha (by linarith) halpha_one =
      rho.conditionalSandwichedRenyiUp hrho alpha halpha halpha_one := by
  rfl

/-- A source candidate is the negative sandwiched Schatten logarithm.  Only
the side-reference is assumed full-rank; the input state may be singular. -/
theorem conditionalSandwichedRenyiUpSourceCandidate_eq_schattenLog
    (rho : MState (a × b)) (sigma : MState b) (hsigma : sigma.m.PosDef)
    {alpha : ℝ} (halpha_pos : 0 < alpha) (_halpha_one : alpha ≠ 1) :
    rho.conditionalSandwichedRenyiUpSourceCandidate
        sigma hsigma alpha halpha_pos _halpha_one =
      -(alpha / (alpha - 1)) *
        log2 (psdSchattenPNorm
          (sandwichedRenyiReferenceInner rho
            (identityTensorStateMatrix (a := a) sigma) alpha)
          (sandwichedRenyiReferenceInner_posSemidef rho
            (identityTensorStateMatrix_posSemidef (a := a) sigma) alpha)
          ⟨alpha, halpha_pos⟩) := by
  let reference : CMatrix (a × b) := identityTensorStateMatrix (a := a) sigma
  let inner : CMatrix (a × b) :=
    sandwichedRenyiReferenceInner rho reference alpha
  let hinner : inner.PosSemidef :=
    sandwichedRenyiReferenceInner_posSemidef rho
      (identityTensorStateMatrix_posSemidef (a := a) sigma) alpha
  let norm : ℝ := psdSchattenPNorm inner hinner ⟨alpha, halpha_pos⟩
  have href : reference.PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) sigma hsigma
  have hinner_ne : inner ≠ 0 := by
    simpa [inner, reference] using
      sandwichedRenyiReferenceInner_ne_zero_of_reference_posDef rho href alpha
  have hnorm_pos : 0 < norm := by
    exact psdSchattenPNorm_pos_of_ne_zero inner hinner hinner_ne
  have hpow : norm ^ alpha = psdTracePower inner hinner alpha := by
    exact psdSchattenPNorm_rpow_eq_psdTracePower
      inner hinner halpha_pos
  unfold conditionalSandwichedRenyiUpSourceCandidate
  change -(1 / (alpha - 1)) * log2 (psdTracePower inner hinner alpha) =
    -(alpha / (alpha - 1)) * log2 norm
  rw [← hpow, log2_rpow_pos hnorm_pos _]
  ring

/-- The source value set is the range over normalized full-rank side states. -/
theorem conditionalSandwichedRenyiUpSourceValueSet_eq_range
    [Nonempty b] (rho : MState (a × b)) (alpha : ℝ)
    (hAlphaPos : 0 < alpha) (hAlphaNeOne : alpha ≠ 1) :
    rho.conditionalSandwichedRenyiUpSourceValueSet alpha hAlphaPos hAlphaNeOne =
      Set.range (fun sigma : {sigma : MState b // sigma.m.PosDef} =>
        rho.conditionalSandwichedRenyiUpSourceCandidate
          sigma.1 sigma.2 alpha hAlphaPos hAlphaNeOne) := by
  ext x
  constructor
  · rintro ⟨sigma, hsigma, rfl⟩
    exact ⟨⟨sigma, hsigma⟩, rfl⟩
  · rintro ⟨sigma, rfl⟩
    exact ⟨sigma.1, sigma.2, rfl⟩

end MState

namespace Ket

/-- Conjugate-order parameter used in Tomamichel's proof. -/
def upwardRenyiDualityParameter (alpha : ℝ) : ℝ :=
  (alpha - 1) / alpha

theorem upwardRenyiDualityParameter_pos
    {alpha : ℝ} (halpha : 1 < alpha) :
    0 < upwardRenyiDualityParameter alpha := by
  unfold upwardRenyiDualityParameter
  positivity

theorem upwardRenyiDualityParameter_lt_one
    {alpha : ℝ} (halpha : 1 < alpha) :
    upwardRenyiDualityParameter alpha < 1 := by
  unfold upwardRenyiDualityParameter
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  rw [div_lt_one halpha_pos]
  linarith

theorem upwardRenyiDualityParameter_eq_beta
    {alpha beta : ℝ} (halpha : 1 < alpha)
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
    (psi : Ket ((a × b) × c)) (sigma : CMatrix b) (p : ℝ) :
    (a × b) × c → ℂ :=
  Matrix.mulVec
    (((1 : CMatrix a) ⊗ₖ (CFC.rpow sigma (-p / 2))) ⊗ₖ
      (1 : CMatrix c))
    psi.vec

/-- The complementary `C` marginal of the high-order weighted
purification. -/
def upwardRenyiDualityHighCMatrix
    (psi : Ket ((a × b) × c)) (sigma : CMatrix b) (p : ℝ) :
    CMatrix c :=
  Matrix.traceLeft
    (rankOneMatrix (psi.upwardRenyiDualityABWeightedAmplitude sigma p))

theorem upwardRenyiDualityHighCMatrix_posSemidef
    (psi : Ket ((a × b) × c)) (sigma : CMatrix b) (p : ℝ) :
    (psi.upwardRenyiDualityHighCMatrix sigma p).PosSemidef :=
  traceLeft_posSemidef
    (rankOneMatrix_pos (psi.upwardRenyiDualityABWeightedAmplitude sigma p))

/-- High-order Schatten value attached to a full-rank `B` side state. -/
def upwardRenyiDualityHighNorm
    (psi : Ket ((a × b) × c))
    (sigma : MState b) (alpha : SchattenOrder) : ℝ :=
  psdSchattenPNorm
    (psi.upwardRenyiDualityHighCMatrix sigma.m
      (upwardRenyiDualityParameter alpha))
    (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.m
      (upwardRenyiDualityParameter alpha)) alpha

/-- Low-order Schatten value attached to a normalized `C` side state. -/
def upwardRenyiDualityLowNorm
    (psi : Ket ((a × b) × c))
    (tau : MState c) (alpha : ℝ) (beta : SchattenOrder) : ℝ :=
  psdSchattenPNorm
    (psi.upwardRenyiDualityEffectiveBMatrix tau.m
      (upwardRenyiDualityParameter alpha))
    (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.m
      (upwardRenyiDualityParameter alpha)) beta

/-- The `AB` marginal of the high-order weighted purification is exactly the
sandwiched-Renyi inner operator for `I_A tensor sigma_B`. -/
theorem traceRight_rankOne_upwardRenyiDualityABWeightedAmplitude_eq_referenceInner
    (psi : Ket ((a × b) × c))
    (sigma : MState b) (hsigma : sigma.m.PosDef)
    {alpha : ℝ} (_halpha : 1 < alpha) :
    Matrix.traceRight
        (rankOneMatrix
          (psi.upwardRenyiDualityABWeightedAmplitude sigma.m
            (upwardRenyiDualityParameter alpha))) =
      MState.sandwichedRenyiReferenceInner psi.state.marginalAB
        (MState.identityTensorStateMatrix (a := a) sigma) alpha := by
  let p := upwardRenyiDualityParameter alpha
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let Wab : CMatrix (a × b) :=
    (1 : CMatrix a) ⊗ₖ (CFC.rpow sigma.m (-p / 2))
  have hp : p = (alpha - 1) / alpha := rfl
  have hsp : -p / 2 = s := by
    simp [p, upwardRenyiDualityParameter, s]
    ring
  have hWab :
      Wab = CFC.rpow (MState.identityTensorStateMatrix (a := a) sigma) s := by
    unfold Wab MState.identityTensorStateMatrix
    rw [cMatrix_rpow_kronecker Matrix.PosSemidef.one hsigma.posSemidef s]
    simp [hsp]
  rw [show upwardRenyiDualityParameter alpha = p by rfl]
  change Matrix.traceRight
      (rankOneMatrix
        (Matrix.mulVec (Wab ⊗ₖ (1 : CMatrix c)) psi.vec)) = _
  rw [traceRight_rankOne_kron_left_mulVec_eq]
  have hWabHerm : Matrix.conjTranspose Wab = Wab := by
    rw [hWab]
    exact (cMatrix_rpow_posSemidef
      (A := MState.identityTensorStateMatrix (a := a) sigma) (s := s)
      (MState.identityTensorStateMatrix_posSemidef (a := a) sigma)).isHermitian.eq
  rw [hWabHerm, hWab]
  simp only [MState.sandwichedRenyiReferenceInner, MState.marginalAB, MState.traceRight_m,
    Ket.state_matrix]
  rfl

/-- The common Tomamichel bracket is the trace pairing of the high-order
weighted purification's complementary marginal with `tau_C^p`. -/
theorem abcSidePowerTraceRe_eq_highCMatrix_pairing
    (psi : Ket ((a × b) × c))
    (sigma : CMatrix b) (tau : CMatrix c) (p : ℝ)
    (hsigma : sigma.PosDef) :
    MState.abcSidePowerTraceRe (a := a) psi.state.m sigma tau p =
      ((psi.upwardRenyiDualityHighCMatrix sigma p *
        CFC.rpow tau p).trace).re := by
  let S : CMatrix b := CFC.rpow sigma (-p / 2)
  let Wab : CMatrix (a × b) := (1 : CMatrix a) ⊗ₖ S
  let W : CMatrix ((a × b) × c) :=
    Wab ⊗ₖ (1 : CMatrix c)
  let T : CMatrix c := CFC.rpow tau p
  let K : CMatrix ((a × b) × c) :=
    (1 : CMatrix (a × b)) ⊗ₖ T
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
        ((1 : CMatrix a) ⊗ₖ (CFC.rpow sigma (-p))) ⊗ₖ T := by
    have hWK : W * K = Wab ⊗ₖ T := by
      unfold W K
      simpa using
        (Matrix.mul_kronecker_mul Wab (1 : CMatrix (a × b))
          (1 : CMatrix c) T).symm
    have hWab2 :
        Wab * Wab =
          (1 : CMatrix a) ⊗ₖ (CFC.rpow sigma (-p)) := by
      unfold Wab
      calc
        ((1 : CMatrix a) ⊗ₖ S) *
            ((1 : CMatrix a) ⊗ₖ S) =
            ((1 : CMatrix a) * 1) ⊗ₖ (S * S) := by
              exact (Matrix.mul_kronecker_mul
                (1 : CMatrix a) (1 : CMatrix a) S S).symm
        _ = (1 : CMatrix a) ⊗ₖ (CFC.rpow sigma (-p)) := by
              rw [hSpow]
              simp
    calc
      W * K * W = (Wab ⊗ₖ T) * W := by rw [hWK]
      _ = (Wab ⊗ₖ T) *
          (Wab ⊗ₖ (1 : CMatrix c)) := by rfl
      _ = (Wab * Wab) ⊗ₖ (T * (1 : CMatrix c)) := by
            exact (Matrix.mul_kronecker_mul Wab Wab T (1 : CMatrix c)).symm
      _ = ((1 : CMatrix a) ⊗ₖ (CFC.rpow sigma (-p))) ⊗ₖ T := by
            rw [hWab2]
            simp
  have hrank :
      rankOneMatrix (psi.upwardRenyiDualityABWeightedAmplitude sigma p) =
        W * rankOneMatrix psi.vec * W := by
    unfold upwardRenyiDualityABWeightedAmplitude W Wab S
    rw [rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
    rw [hWstar]
  unfold MState.abcSidePowerTraceRe upwardRenyiDualityHighCMatrix
  rw [Ket.state_matrix]
  rw [traceLeft_mul_trace_eq_trace_mul_kronecker_one_right]
  change
    (((((1 : CMatrix a) ⊗ₖ (CFC.rpow sigma (-p))) ⊗ₖ T) *
      rankOneMatrix psi.vec).trace).re =
      ((rankOneMatrix (psi.upwardRenyiDualityABWeightedAmplitude sigma p) *
        K).trace).re
  rw [hrank]
  calc
    (((((1 : CMatrix a) ⊗ₖ (CFC.rpow sigma (-p))) ⊗ₖ T) *
      rankOneMatrix psi.vec).trace).re =
        ((W * K * W * rankOneMatrix psi.vec).trace).re := by rw [hWKW]
    _ = (((W * rankOneMatrix psi.vec * W) * K).trace).re := by
      congr 1
      simpa [Matrix.mul_assoc] using
        Matrix.trace_mul_cycle W K (W * rankOneMatrix psi.vec)

/-- For fixed full-rank `sigma_B`, Holder's variational formula identifies
the supremum of the common bracket with the Schatten `alpha` norm of the
weighted purification's `C` marginal. -/
theorem upwardRenyiDualityHighBracket_isGreatest
    [Nonempty c]
    (psi : Ket ((a × b) × c))
    (sigma : MState b) (hsigma : sigma.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    IsGreatest
      (Set.range fun tau : MState c =>
        MState.abcSidePowerTraceRe (a := a) psi.state.m
          sigma.m tau.m (upwardRenyiDualityParameter alpha))
      (psdSchattenPNorm
        (psi.upwardRenyiDualityHighCMatrix sigma.m
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.m
          (upwardRenyiDualityParameter alpha))
        ⟨alpha, lt_trans zero_lt_one halpha⟩) := by
  let p := upwardRenyiDualityParameter alpha
  let M := psi.upwardRenyiDualityHighCMatrix sigma.m p
  let hM : M.PosSemidef :=
    psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.m p
  have hp : p = 1 - 1 / alpha := by
    simp [p, upwardRenyiDualityParameter]
    field_simp [ne_of_gt (lt_trans zero_lt_one halpha)]
  have hset :
      (Set.range fun tau : MState c =>
        MState.abcSidePowerTraceRe (a := a) psi.state.m
          sigma.m tau.m p) =
        psdTraceHolderStateValueSet M alpha := by
    ext x
    constructor
    · rintro ⟨tau, rfl⟩
      refine ⟨tau, ?_⟩
      change MState.abcSidePowerTraceRe (a := a) psi.state.m
          sigma.m tau.m p =
        ((M * CFC.rpow tau.m (1 - 1 / alpha)).trace).re
      rw [psi.abcSidePowerTraceRe_eq_highCMatrix_pairing
        sigma.m tau.m p hsigma]
      rw [← hp]
    · rintro ⟨tau, rfl⟩
      refine ⟨tau, ?_⟩
      change MState.abcSidePowerTraceRe (a := a) psi.state.m
          sigma.m tau.m p =
        ((M * CFC.rpow tau.m (1 - 1 / alpha)).trace).re
      rw [psi.abcSidePowerTraceRe_eq_highCMatrix_pairing
        sigma.m tau.m p hsigma]
      rw [← hp]
  rw [show upwardRenyiDualityParameter alpha = p by rfl, hset]
  exact psdTraceHolderStateValueSet_isGreatest_of_one_lt hM halpha

/-- Reverse-Holder candidate values for the fixed `tau_C` branch of the
source common bracket. -/
def upwardRenyiDualityLowBracketValueSet
    (psi : Ket ((a × b) × c))
    (tau : MState c) (p : ℝ) : Set ℝ :=
  {x | ∃ sigma : MState b,
    Matrix.Supports
      (psi.upwardRenyiDualityEffectiveBMatrix tau.m p) sigma.m ∧
    x = MState.abcSidePowerTraceRe (a := a) psi.state.m
      sigma.m tau.m p}

/-- For fixed `tau_C`, reverse Holder identifies the minimum of the
support-aware common bracket with the Schatten `beta` norm of the effective
`B` matrix. -/
theorem upwardRenyiDualityLowBracket_isLeast
    [Nonempty b]
    (psi : Ket ((a × b) × c)) (tau : MState c)
    {alpha beta : ℝ} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    IsLeast
      (psi.upwardRenyiDualityLowBracketValueSet tau
        (upwardRenyiDualityParameter alpha))
      (psdSchattenPNorm
        (psi.upwardRenyiDualityEffectiveBMatrix tau.m
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.m
          (upwardRenyiDualityParameter alpha))
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩) := by
  let p := upwardRenyiDualityParameter alpha
  let M := psi.upwardRenyiDualityEffectiveBMatrix tau.m p
  let hM : M.PosSemidef :=
    psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.m p
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
          sigma.m tau.m p tau.psd]
        rw [hexp, Matrix.trace_mul_comm]
    · rintro ⟨sigma, hsupp, rfl⟩
      refine ⟨sigma, ?_, ?_⟩
      · simpa [M] using hsupp
      · rw [psi.abcSidePowerTraceRe_eq_effectiveBMatrix_pairing
          sigma.m tau.m p tau.psd]
        rw [hexp, Matrix.trace_mul_comm]
  rw [show upwardRenyiDualityParameter alpha = p by rfl, hset]
  exact psdTraceReverseHolderNormalizedStateValueSet_isLeast_of_lt_one
    hM hbeta_pos hbeta_one

/-- The `AC` marginal of the low-order weighted purification is exactly the
sandwiched-Renyi inner operator for `I_A tensor tau_C`. -/
theorem traceRight_rankOne_upwardRenyiDualityACWeightedAmplitude_eq_referenceInner
    (psi : Ket ((a × b) × c)) (tau : MState c)
    {alpha beta : ℝ} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    Matrix.traceRight
        (rankOneMatrix
          (psi.upwardRenyiDualityACWeightedAmplitude tau.m
            (upwardRenyiDualityParameter alpha))) =
      MState.sandwichedRenyiReferenceInner psi.state.marginalAC
        (MState.identityTensorStateMatrix (a := a) tau) beta := by
  let p := upwardRenyiDualityParameter alpha
  let X : CMatrix (a × c) := MState.identityTensorStateMatrix (a := a) tau
  let W : CMatrix (a × c) := upwardRenyiDualityACWeight (a := a) tau.m p
  let S : CMatrix (a × c) := CFC.sqrt W
  have hp0 : 0 < p := upwardRenyiDualityParameter_pos halpha
  have hp_nonneg : 0 ≤ p := hp0.le
  have hp_beta : p = (1 - beta) / beta :=
    upwardRenyiDualityParameter_eq_beta halpha hconj
  have hbeta_pos : 0 < beta := by linarith
  have hs : p / 2 = (1 - beta) / (2 * beta) := by
    rw [hp_beta]
    field_simp [ne_of_gt hbeta_pos]
  have hX : X.PosSemidef :=
    MState.identityTensorStateMatrix_posSemidef (a := a) tau
  have hW : W = CFC.rpow X p := by
    unfold W Ket.upwardRenyiDualityACWeight X MState.identityTensorStateMatrix
    simpa using
      (cMatrix_rpow_kronecker
        (A := (1 : CMatrix a)) (B := tau.m)
        Matrix.PosSemidef.one tau.psd p).symm
  have hS : S = CFC.rpow X (p / 2) := by
    change CFC.sqrt W = CFC.rpow X (p / 2)
    rw [hW]
    exact CFC.sqrt_rpow_nnreal (a := X) (x := ⟨p, hp_nonneg⟩)
  have hmarg :
      Matrix.traceRight
          (rankOneMatrix psi.upwardRenyiDualityACBAmplitude) =
        psi.state.marginalAC.m := by
    ext x y
    simp [Ket.upwardRenyiDualityACBAmplitude, MState.marginalAC,
      Matrix.traceRight, rankOneMatrix_apply]
  unfold upwardRenyiDualityACWeightedAmplitude
  change Matrix.traceRight
      (rankOneMatrix
        (Matrix.mulVec (S ⊗ₖ (1 : CMatrix b))
          psi.upwardRenyiDualityACBAmplitude)) = _
  rw [traceRight_rankOne_kron_left_mulVec_eq]
  rw [hmarg]
  have hSherm : Matrix.conjTranspose S = S := by
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg W)).isHermitian.eq
  rw [hSherm, hS, hs]
  rfl

/-- The low-order reference inner and the effective `B` matrix have the same
Schatten `beta` norm because they are complementary marginals of one weighted
ket. -/
theorem psdSchattenPNorm_lowReferenceInner_eq_effectiveBMatrix
    (psi : Ket ((a × b) × c)) (tau : MState c)
    {alpha beta : ℝ} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    psdSchattenPNorm
        (MState.sandwichedRenyiReferenceInner psi.state.marginalAC
          (MState.identityTensorStateMatrix (a := a) tau) beta)
        (MState.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAC
          (MState.identityTensorStateMatrix_posSemidef (a := a) tau) beta)
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩ =
      psdSchattenPNorm
        (psi.upwardRenyiDualityEffectiveBMatrix tau.m
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.m
          (upwardRenyiDualityParameter alpha))
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩ := by
  have hbeta_pos : 0 < beta := lt_trans (by norm_num) hbeta_half
  let v := psi.upwardRenyiDualityACWeightedAmplitude tau.m
    (upwardRenyiDualityParameter alpha)
  have hcomp :=
    psdSchattenPNorm_traceRight_rankOneMatrix_eq_traceLeft_rankOneMatrix
      v ⟨beta, hbeta_pos⟩
  have hleft :=
    psi.traceRight_rankOne_upwardRenyiDualityACWeightedAmplitude_eq_referenceInner
      tau halpha hbeta_half hbeta_one hconj
  calc
    psdSchattenPNorm
        (MState.sandwichedRenyiReferenceInner psi.state.marginalAC
          (MState.identityTensorStateMatrix (a := a) tau) beta)
        (MState.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAC
          (MState.identityTensorStateMatrix_posSemidef (a := a) tau) beta)
        ⟨beta, hbeta_pos⟩ =
      psdSchattenPNorm
        (Matrix.traceRight (rankOneMatrix v))
        (traceRight_posSemidef (rankOneMatrix_pos v)) ⟨beta, hbeta_pos⟩ :=
          psdSchattenPNorm_congr hleft.symm _ _ ⟨beta, hbeta_pos⟩
    _ = psdSchattenPNorm
        (Matrix.traceLeft (rankOneMatrix v))
        (traceLeft_posSemidef (rankOneMatrix_pos v)) ⟨beta, hbeta_pos⟩ := hcomp
    _ = psdSchattenPNorm
        (psi.upwardRenyiDualityEffectiveBMatrix tau.m
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.m
          (upwardRenyiDualityParameter alpha)) ⟨beta, hbeta_pos⟩ := by rfl

/-- The high-order reference inner and the complementary `C` matrix have the
same Schatten `alpha` norm. -/
theorem psdSchattenPNorm_highReferenceInner_eq_highCMatrix
    (psi : Ket ((a × b) × c))
    (sigma : MState b) (hsigma : sigma.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    psdSchattenPNorm
        (MState.sandwichedRenyiReferenceInner psi.state.marginalAB
          (MState.identityTensorStateMatrix (a := a) sigma) alpha)
        (MState.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAB
          (MState.identityTensorStateMatrix_posSemidef (a := a) sigma) alpha)
        ⟨alpha, lt_trans zero_lt_one halpha⟩ =
      psdSchattenPNorm
        (psi.upwardRenyiDualityHighCMatrix sigma.m
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.m
          (upwardRenyiDualityParameter alpha))
        ⟨alpha, lt_trans zero_lt_one halpha⟩ := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  let v := psi.upwardRenyiDualityABWeightedAmplitude sigma.m
    (upwardRenyiDualityParameter alpha)
  have hcomp :=
    psdSchattenPNorm_traceRight_rankOneMatrix_eq_traceLeft_rankOneMatrix
      v ⟨alpha, halpha_pos⟩
  have hleft :=
    psi.traceRight_rankOne_upwardRenyiDualityABWeightedAmplitude_eq_referenceInner
      sigma hsigma halpha
  calc
    psdSchattenPNorm
        (MState.sandwichedRenyiReferenceInner psi.state.marginalAB
          (MState.identityTensorStateMatrix (a := a) sigma) alpha)
        (MState.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAB
          (MState.identityTensorStateMatrix_posSemidef (a := a) sigma) alpha)
        ⟨alpha, halpha_pos⟩ =
      psdSchattenPNorm
        (Matrix.traceRight (rankOneMatrix v))
        (traceRight_posSemidef (rankOneMatrix_pos v)) ⟨alpha, halpha_pos⟩ :=
          psdSchattenPNorm_congr hleft.symm _ _ ⟨alpha, halpha_pos⟩
    _ = psdSchattenPNorm
        (Matrix.traceLeft (rankOneMatrix v))
        (traceLeft_posSemidef (rankOneMatrix_pos v)) ⟨alpha, halpha_pos⟩ := hcomp
    _ = psdSchattenPNorm
        (psi.upwardRenyiDualityHighCMatrix sigma.m
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.m
          (upwardRenyiDualityParameter alpha)) ⟨alpha, halpha_pos⟩ := by rfl

/-- MState-language form of the full-rank Sion exchange proved at the matrix
boundary in `ConditionalRenyiMinimaxBoundary`. -/
theorem upwardRenyiDualitySource_fullRank_sion
    [Nonempty c]
    (psi : Ket ((a × b) × c))
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (⨅ sigma : {sigma : MState b // sigma.m.PosDef},
      ⨆ tau : MState c,
        (MState.abcSidePowerTraceRe (a := a) psi.state.m
          sigma.1.m tau.m p : EReal)) =
      ⨆ tau : MState c,
        ⨅ sigma : {sigma : MState b // sigma.m.PosDef},
          (MState.abcSidePowerTraceRe (a := a) psi.state.m
            sigma.1.m tau.m p : EReal) := by
  let F : CMatrix b → CMatrix c → EReal := fun sigma tau =>
    (MState.abcSidePowerTraceRe (a := a) psi.state.m sigma tau p : EReal)
  calc
    (⨅ sigma : {sigma : MState b // sigma.m.PosDef},
      ⨆ tau : MState c,
        (MState.abcSidePowerTraceRe (a := a) psi.state.m
          sigma.1.m tau.m p : EReal)) =
        ⨅ sigma : CMatrix b,
          ⨅ _hSigma : sigma ∈ MState.fullRankDensityMatrixSet b,
            ⨆ tau : MState c, F sigma tau.m := by
              exact fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf
                (fun sigma => ⨆ tau : MState c, F sigma tau.m)
    _ = ⨅ sigma : CMatrix b,
          ⨅ _hSigma : sigma ∈ MState.fullRankDensityMatrixSet b,
            ⨆ tau : CMatrix c,
              ⨆ _hTau : tau ∈ MState.densityMatrixSet c, F sigma tau := by
              simp_rw [state_iSup_matrix_eq_densityMatrixSet_iSup]
    _ = ⨆ tau : CMatrix c,
          ⨆ _hTau : tau ∈ MState.densityMatrixSet c,
            ⨅ sigma : CMatrix b,
              ⨅ _hSigma : sigma ∈ MState.fullRankDensityMatrixSet b,
                F sigma tau := by
              exact MState.fullRankDensityMatrixSet_sion_abcSidePowerTraceRe_EReal
                (a := a) (b := b) (c := c) psi.state.psd hp0 hp1.le
    _ = ⨆ tau : MState c,
          ⨅ sigma : CMatrix b,
            ⨅ _hSigma : sigma ∈ MState.fullRankDensityMatrixSet b,
              F sigma tau.m := by
              exact (state_iSup_matrix_eq_densityMatrixSet_iSup
                (fun tau => ⨅ sigma : CMatrix b,
                  ⨅ _hSigma : sigma ∈ MState.fullRankDensityMatrixSet b,
                    F sigma tau)).symm
    _ = ⨆ tau : MState c,
          ⨅ sigma : {sigma : MState b // sigma.m.PosDef},
            (MState.abcSidePowerTraceRe (a := a) psi.state.m
              sigma.1.m tau.m p : EReal) := by
              apply iSup_congr
              intro tau
              exact (fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf
                (fun sigma => F sigma tau.m)).symm

/-- The fixed-full-rank-`sigma_B` extended-real supremum of the source bracket
is the embedded Schatten `alpha` norm. -/
theorem upwardRenyiDualityHighBracket_iSup_EReal_eq
    [Nonempty c]
    (psi : Ket ((a × b) × c))
    (sigma : MState b) (hsigma : sigma.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    (⨆ tau : MState c,
      (MState.abcSidePowerTraceRe (a := a) psi.state.m
        sigma.m tau.m (upwardRenyiDualityParameter alpha) : EReal)) =
      (psdSchattenPNorm
        (psi.upwardRenyiDualityHighCMatrix sigma.m
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.m
          (upwardRenyiDualityParameter alpha))
        ⟨alpha, lt_trans zero_lt_one halpha⟩ : EReal) := by
  let : Nonempty (MState c) := ⟨(MState.uniform : MState c)⟩
  let f : MState c → ℝ := fun tau =>
    MState.abcSidePowerTraceRe (a := a) psi.state.m
      sigma.m tau.m (upwardRenyiDualityParameter alpha)
  let target : ℝ := psdSchattenPNorm
    (psi.upwardRenyiDualityHighCMatrix sigma.m
      (upwardRenyiDualityParameter alpha))
    (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.m
      (upwardRenyiDualityParameter alpha)) ⟨alpha, lt_trans zero_lt_one halpha⟩
  have hgreatest : IsGreatest (Set.range f) target := by
    simpa [f, target] using
      psi.upwardRenyiDualityHighBracket_isGreatest sigma hsigma halpha
  have hbdd : BddAbove (Set.range f) := ⟨target, hgreatest.2⟩
  change sSup (Set.range fun tau : MState c => (f tau : EReal)) = (target : EReal)
  rw [ereal_sSup_range_coe_eq_coe_real_sSup f hbdd, hgreatest.csSup_eq]

/-- On the complete density domain, the support-aware bracket has exactly the
reverse-Holder Schatten `beta` norm as its infimum. -/
theorem upwardRenyiDualityLowBracket_density_iInf_EReal_eq
    [Nonempty b]
    (psi : Ket ((a × b) × c)) (tau : MState c)
    {alpha beta : ℝ} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    (⨅ sigma : MState b,
      psi.upwardRenyiDualitySourceBracketEReal sigma.m tau.m
        (upwardRenyiDualityParameter alpha)) =
      (psdSchattenPNorm
        (psi.upwardRenyiDualityEffectiveBMatrix tau.m
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.m
          (upwardRenyiDualityParameter alpha))
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩ : EReal) := by
  let p := upwardRenyiDualityParameter alpha
  let target : ℝ := psdSchattenPNorm
    (psi.upwardRenyiDualityEffectiveBMatrix tau.m p)
    (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.m p)
    ⟨beta, lt_trans (by norm_num) hbeta_half⟩
  have hleast : IsLeast (psi.upwardRenyiDualityLowBracketValueSet tau p) target := by
    simpa [p, target] using
      psi.upwardRenyiDualityLowBracket_isLeast tau
        halpha hbeta_half hbeta_one hconj
  apply le_antisymm
  · rcases hleast.1 with ⟨sigma, hsupport, hvalue⟩
    refine iInf_le_of_le sigma ?_
    rw [psi.upwardRenyiDualitySourceBracketEReal_of_supports
      sigma.m tau.m p hsupport]
    exact EReal.coe_le_coe_iff.mpr hvalue.symm.le
  · refine le_iInf fun sigma => ?_
    by_cases hsupport : Matrix.Supports
        (psi.upwardRenyiDualityEffectiveBMatrix tau.m p) sigma.m
    · rw [psi.upwardRenyiDualitySourceBracketEReal_of_supports
        sigma.m tau.m p hsupport]
      exact EReal.coe_le_coe_iff.mpr (hleast.2 ⟨sigma, hsupport, rfl⟩)
    · rw [psi.upwardRenyiDualitySourceBracketEReal_of_not_supports
        sigma.m tau.m p hsupport]
      exact le_top

/-- The fixed-`tau_C` full-rank `sigma_B` infimum of the real source bracket
is the embedded reverse-Holder Schatten norm.  The equality uses the
support-aware identity-regularization closure, not an extra support
hypothesis. -/
theorem upwardRenyiDualityLowBracket_fullRank_iInf_EReal_eq
    [Nonempty b]
    (psi : Ket ((a × b) × c)) (tau : MState c)
    {alpha beta : ℝ} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    (⨅ sigma : {sigma : MState b // sigma.m.PosDef},
      (MState.abcSidePowerTraceRe (a := a) psi.state.m
        sigma.1.m tau.m (upwardRenyiDualityParameter alpha) : EReal)) =
      (psdSchattenPNorm
        (psi.upwardRenyiDualityEffectiveBMatrix tau.m
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.m
          (upwardRenyiDualityParameter alpha))
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩ : EReal) := by
  let p := upwardRenyiDualityParameter alpha
  calc
    (⨅ sigma : {sigma : MState b // sigma.m.PosDef},
      (MState.abcSidePowerTraceRe (a := a) psi.state.m
        sigma.1.m tau.m p : EReal)) =
        ⨅ sigma : CMatrix b,
          ⨅ _hSigma : sigma ∈ MState.fullRankDensityMatrixSet b,
            (MState.abcSidePowerTraceRe (a := a) psi.state.m
              sigma tau.m p : EReal) := by
                exact fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf
                  (b := b) (fun sigma : CMatrix b =>
                    (MState.abcSidePowerTraceRe (a := a) psi.state.m
                      sigma tau.m p : EReal))
    _ = ⨅ sigma : CMatrix b,
          ⨅ _hSigma : sigma ∈ MState.densityMatrixSet b,
            psi.upwardRenyiDualitySourceBracketEReal sigma tau.m p := by
              exact psi.upwardRenyiDualitySourceBracketEReal_fullRank_iInf_eq_density_iInf
                tau.m (MState.state_matrix_mem_densityMatrixSet tau) p
    _ = ⨅ sigma : MState b,
          psi.upwardRenyiDualitySourceBracketEReal sigma.m tau.m p := by
              exact (state_iInf_matrix_eq_densityMatrixSet_iInf _).symm
    _ = (psdSchattenPNorm
        (psi.upwardRenyiDualityEffectiveBMatrix tau.m p)
        (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.m p)
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩ :
          EReal) := by
            simpa [p] using psi.upwardRenyiDualityLowBracket_density_iInf_EReal_eq
              tau halpha hbeta_half hbeta_one hconj

/-- Tomamichel's common Holder bracket identifies the infimum of the
high-order Schatten expression with the supremum of the complementary
low-order Schatten expression. -/
theorem upwardRenyiDuality_commonSchattenExtrema_eq
    [Nonempty b] [Nonempty c]
    (psi : Ket ((a × b) × c))
    {alpha beta : ℝ} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    sInf (Set.range fun sigma : {sigma : MState b // sigma.m.PosDef} =>
      psdSchattenPNorm
        (psi.upwardRenyiDualityHighCMatrix sigma.1.m
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.1.m
          (upwardRenyiDualityParameter alpha))
        ⟨alpha, lt_trans zero_lt_one halpha⟩) =
      sSup (Set.range fun tau : MState c =>
        psdSchattenPNorm
          (psi.upwardRenyiDualityEffectiveBMatrix tau.m
            (upwardRenyiDualityParameter alpha))
          (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.m
            (upwardRenyiDualityParameter alpha))
          ⟨beta, lt_trans (by norm_num) hbeta_half⟩) := by
  let S := {sigma : MState b // sigma.m.PosDef}
  let high : S → ℝ := fun sigma =>
    psdSchattenPNorm
      (psi.upwardRenyiDualityHighCMatrix sigma.1.m
        (upwardRenyiDualityParameter alpha))
      (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.1.m
        (upwardRenyiDualityParameter alpha))
      ⟨alpha, lt_trans zero_lt_one halpha⟩
  let low : MState c → ℝ := fun tau =>
    psdSchattenPNorm
      (psi.upwardRenyiDualityEffectiveBMatrix tau.m
        (upwardRenyiDualityParameter alpha))
      (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.m
        (upwardRenyiDualityParameter alpha))
      ⟨beta, lt_trans (by norm_num) hbeta_half⟩
  let sigma0 : S :=
    ⟨(MState.uniform : MState b), MState.uniform_posDef⟩
  let : Nonempty S := ⟨sigma0⟩
  let : Nonempty (MState c) := ⟨(MState.uniform : MState c)⟩
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
        (psi.upwardRenyiDualityEffectiveBMatrix tau.m
          (upwardRenyiDualityParameter alpha)) sigma0.1.m :=
      Matrix.Supports.of_right_posDef _ _ sigma0.2
    have hlow_le : low tau ≤
        MState.abcSidePowerTraceRe (a := a) psi.state.m
          sigma0.1.m tau.m (upwardRenyiDualityParameter alpha) := by
      exact hleast.2 ⟨sigma0.1, hsupport, rfl⟩
    have hgreatest := psi.upwardRenyiDualityHighBracket_isGreatest
      sigma0.1 sigma0.2 halpha
    have hbracket_le :
        MState.abcSidePowerTraceRe (a := a) psi.state.m
          sigma0.1.m tau.m (upwardRenyiDualityParameter alpha) ≤
        high sigma0 := by
      exact hgreatest.2 ⟨tau, rfl⟩
    exact hlow_le.trans hbracket_le
  have hsion := psi.upwardRenyiDualitySource_fullRank_sion
    (upwardRenyiDualityParameter_pos halpha)
    (upwardRenyiDualityParameter_lt_one halpha)
  have hhigh (sigma : S) :=
    psi.upwardRenyiDualityHighBracket_iSup_EReal_eq
      sigma.1 sigma.2 (alpha := alpha) halpha
  have hlow (tau : MState c) :=
    psi.upwardRenyiDualityLowBracket_fullRank_iInf_EReal_eq
      tau (alpha := alpha) (beta := beta)
        halpha hbeta_half hbeta_one hconj
  simp_rw [hhigh] at hsion
  simp_rw [hlow] at hsion
  change sInf (Set.range fun sigma : S => (high sigma : EReal)) =
    sSup (Set.range fun tau : MState c => (low tau : EReal)) at hsion
  rw [ereal_sInf_range_coe_eq_coe_real_sInf high hhigh_bdd,
    ereal_sSup_range_coe_eq_coe_real_sSup low hlow_bdd] at hsion
  exact EReal.coe_eq_coe_iff.mp hsion

/-- The high-order `AB` entropy candidate is `-1/p` times the logarithm of
the Holder-side common Schatten value. -/
theorem upwardRenyiDualityABSourceCandidate_eq_highNormLog
    (psi : Ket ((a × b) × c))
    (sigma : MState b) (hsigma : sigma.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    psi.state.marginalAB.conditionalSandwichedRenyiUpSourceCandidate
        sigma hsigma alpha (lt_trans zero_lt_one halpha) (ne_of_gt halpha) =
      -(1 / upwardRenyiDualityParameter alpha) *
        log2 (psdSchattenPNorm
          (psi.upwardRenyiDualityHighCMatrix sigma.m
            (upwardRenyiDualityParameter alpha))
          (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma.m
            (upwardRenyiDualityParameter alpha))
          ⟨alpha, lt_trans zero_lt_one halpha⟩) := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have halpha_one : alpha ≠ 1 := ne_of_gt halpha
  rw [MState.conditionalSandwichedRenyiUpSourceCandidate_eq_schattenLog
    psi.state.marginalAB sigma hsigma halpha_pos halpha_one]
  rw [psi.psdSchattenPNorm_highReferenceInner_eq_highCMatrix
    sigma hsigma halpha]
  congr 1
  unfold upwardRenyiDualityParameter
  field_simp [ne_of_gt halpha_pos, halpha_one]

/-- The low-order `AC` entropy candidate is `1/p` times the logarithm of the
reverse-Holder-side common Schatten value. -/
theorem upwardRenyiDualityACSourceCandidate_eq_lowNormLog
    (psi : Ket ((a × b) × c))
    (tau : MState c) (htau : tau.m.PosDef)
    {alpha beta : ℝ} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    psi.state.marginalAC.conditionalSandwichedRenyiUpSourceCandidate
        tau htau beta (lt_trans (by norm_num) hbeta_half) (ne_of_lt hbeta_one) =
      (1 / upwardRenyiDualityParameter alpha) *
        log2 (psdSchattenPNorm
          (psi.upwardRenyiDualityEffectiveBMatrix tau.m
            (upwardRenyiDualityParameter alpha))
          (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.m
            (upwardRenyiDualityParameter alpha))
          ⟨beta, lt_trans (by norm_num) hbeta_half⟩) := by
  have hbeta_pos : 0 < beta := lt_trans (by norm_num) hbeta_half
  have hbeta_one_ne : beta ≠ 1 := ne_of_lt hbeta_one
  rw [MState.conditionalSandwichedRenyiUpSourceCandidate_eq_schattenLog
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
    (psi : Ket ((a × b) × c)) (tau : MState c)
    {p : ℝ} (hp : 0 < p) :
    Filter.Tendsto
      (fun epsilon : ℝ =>
        psi.upwardRenyiDualityEffectiveBMatrix
          (MState.densityIdentityRegularization tau epsilon).m p)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (psi.upwardRenyiDualityEffectiveBMatrix tau.m p)) := by
  let K : CMatrix ((a × c) × b) :=
    rankOneMatrix psi.upwardRenyiDualityACBAmplitude
  let G : CMatrix c → CMatrix b := fun T =>
    Matrix.traceLeft
      ((((1 : CMatrix a) ⊗ₖ T) ⊗ₖ
        (1 : CMatrix b)) * K)
  have hG : Continuous G := by
    have hinner : Continuous (fun T : CMatrix c =>
        (1 : CMatrix a) ⊗ₖ T) :=
      SubnormalizedState.continuous_kronecker_one_matrix
    have houter : Continuous (fun T : CMatrix c =>
        ((1 : CMatrix a) ⊗ₖ T) ⊗ₖ
          (1 : CMatrix b)) :=
      continuous_kronecker_right_one.comp hinner
    have harg : Continuous (fun T : CMatrix c =>
        (((1 : CMatrix a) ⊗ₖ T) ⊗ₖ
          (1 : CMatrix b)) * K) :=
      Continuous.matrix_mul houter continuous_const
    simpa [G, Function.comp_def] using continuous_traceLeft.comp harg
  have htau := MState.densityIdentityRegularization_matrix_tendsto tau
  have hpow : Filter.Tendsto
      (fun epsilon : ℝ => CFC.rpow
        (MState.densityIdentityRegularization tau epsilon).m p)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (CFC.rpow tau.m p)) :=
    cMatrix_rpow_tendsto_of_tendsto_posSemidef hp htau
      (Filter.Eventually.of_forall fun epsilon =>
        (MState.densityIdentityRegularization tau epsilon).psd) tau.psd
  have hcomp : Filter.Tendsto
      (fun epsilon : ℝ => G (CFC.rpow
        (MState.densityIdentityRegularization tau epsilon).m p))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (G (CFC.rpow tau.m p))) := hG.continuousAt.tendsto.comp hpow
  have heq (rho : MState c) :
      psi.upwardRenyiDualityEffectiveBMatrix rho.m p =
        G (CFC.rpow rho.m p) := by
    rw [psi.upwardRenyiDualityEffectiveBMatrix_eq_partialTrace_weight_mul
      rho.m p rho.psd]
    rfl
  have hcomp' : Filter.Tendsto
      (fun epsilon : ℝ =>
        psi.upwardRenyiDualityEffectiveBMatrix
          (MState.densityIdentityRegularization tau epsilon).m p)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (G (CFC.rpow tau.m p))) := by
    apply hcomp.congr'
    exact Filter.Eventually.of_forall fun epsilon => (heq _).symm
  simpa [heq tau] using hcomp'

/-- The complementary low-order Schatten value is continuous along normalized
identity regularization. -/
theorem upwardRenyiDualityLowNorm_densityIdentityRegularization_tendsto
    [Nonempty c]
    (psi : Ket ((a × b) × c)) (tau : MState c)
    {p beta : ℝ} (hp : 0 < p) (hbeta : 0 < beta) :
    Filter.Tendsto
      (fun epsilon : ℝ =>
        psdSchattenPNorm
          (psi.upwardRenyiDualityEffectiveBMatrix
            (MState.densityIdentityRegularization tau epsilon).m p)
          (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef
            (MState.densityIdentityRegularization tau epsilon).m p)
          ⟨beta, hbeta⟩)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (psdSchattenPNorm
        (psi.upwardRenyiDualityEffectiveBMatrix tau.m p)
        (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.m p)
        ⟨beta, hbeta⟩)) := by
  exact psdSchattenPNorm_tendsto_of_tendsto_posSemidef ⟨beta, hbeta⟩
    (psi.upwardRenyiDualityEffectiveBMatrix_densityIdentityRegularization_tendsto
      tau hp)
    (fun epsilon =>
      psi.upwardRenyiDualityEffectiveBMatrix_posSemidef
        (MState.densityIdentityRegularization tau epsilon).m p)
    (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.m p)

/-- For the low-order branch, optimizing over full-rank normalized `C` states
has the same supremum as optimizing over the closed density-state domain.
This is the explicit dense-domain closure used by
`MState.conditionalSandwichedRenyiUpSource`, and is the source
identity-regularization step for the compact variable. -/
theorem upwardRenyiDualityLowNorm_fullRank_sSup_eq_all
    [Nonempty b] [Nonempty c]
    (psi : Ket ((a × b) × c))
    {alpha beta : ℝ} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    sSup (Set.range fun tau : {tau : MState c // tau.m.PosDef} =>
      psdSchattenPNorm
        (psi.upwardRenyiDualityEffectiveBMatrix tau.1.m
          (upwardRenyiDualityParameter alpha))
        (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.1.m
          (upwardRenyiDualityParameter alpha))
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩) =
      sSup (Set.range fun tau : MState c =>
        psdSchattenPNorm
          (psi.upwardRenyiDualityEffectiveBMatrix tau.m
            (upwardRenyiDualityParameter alpha))
          (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.m
            (upwardRenyiDualityParameter alpha))
          ⟨beta, lt_trans (by norm_num) hbeta_half⟩) := by
  let T := {tau : MState c // tau.m.PosDef}
  let full : T → ℝ := fun tau =>
    psdSchattenPNorm
      (psi.upwardRenyiDualityEffectiveBMatrix tau.1.m
        (upwardRenyiDualityParameter alpha))
      (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.1.m
        (upwardRenyiDualityParameter alpha))
      ⟨beta, lt_trans (by norm_num) hbeta_half⟩
  let all : MState c → ℝ := fun tau =>
    psdSchattenPNorm
      (psi.upwardRenyiDualityEffectiveBMatrix tau.m
        (upwardRenyiDualityParameter alpha))
      (psi.upwardRenyiDualityEffectiveBMatrix_posSemidef tau.m
        (upwardRenyiDualityParameter alpha))
      ⟨beta, lt_trans (by norm_num) hbeta_half⟩
  let sigma0 : {sigma : MState b // sigma.m.PosDef} :=
    ⟨(MState.uniform : MState b), MState.uniform_posDef⟩
  let tau0 : T :=
    ⟨(MState.uniform : MState c), MState.uniform_posDef⟩
  let : Nonempty T := ⟨tau0⟩
  let : Nonempty (MState c) := ⟨tau0.1⟩
  have hall_bdd : BddAbove (Set.range all) := by
    let high0 : ℝ := psdSchattenPNorm
      (psi.upwardRenyiDualityHighCMatrix sigma0.1.m
        (upwardRenyiDualityParameter alpha))
      (psi.upwardRenyiDualityHighCMatrix_posSemidef sigma0.1.m
        (upwardRenyiDualityParameter alpha))
      ⟨alpha, lt_trans zero_lt_one halpha⟩
    refine ⟨high0, ?_⟩
    rintro x ⟨tau, rfl⟩
    have hleast := psi.upwardRenyiDualityLowBracket_isLeast tau
      halpha hbeta_half hbeta_one hconj
    have hsupport : Matrix.Supports
        (psi.upwardRenyiDualityEffectiveBMatrix tau.m
          (upwardRenyiDualityParameter alpha)) sigma0.1.m :=
      Matrix.Supports.of_right_posDef _ _ sigma0.2
    have hlow : all tau ≤
        MState.abcSidePowerTraceRe (a := a) psi.state.m
          sigma0.1.m tau.m (upwardRenyiDualityParameter alpha) :=
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
      ⟨MState.densityIdentityRegularization tau epsilon,
        MState.densityIdentityRegularization_posDef_of_pos tau hepsilon⟩
    exact le_csSup hfull_bdd ⟨tauE, rfl⟩

theorem upwardRenyiDualityHighNorm_pos
    (psi : Ket ((a × b) × c))
    (sigma : MState b) (hsigma : sigma.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    0 < psi.upwardRenyiDualityHighNorm sigma
      ⟨alpha, lt_trans zero_lt_one halpha⟩ := by
  have href : (MState.identityTensorStateMatrix (a := a) sigma).PosDef :=
    MState.identityTensorStateMatrix_posDef_of_posDef (a := a) sigma hsigma
  have hne := MState.sandwichedRenyiReferenceInner_ne_zero_of_reference_posDef
    psi.state.marginalAB href alpha
  have hpos := psdSchattenPNorm_pos_of_ne_zero
    (MState.sandwichedRenyiReferenceInner psi.state.marginalAB
      (MState.identityTensorStateMatrix (a := a) sigma) alpha)
    (MState.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAB
      (MState.identityTensorStateMatrix_posSemidef (a := a) sigma) alpha)
    (p := ⟨alpha, lt_trans zero_lt_one halpha⟩) hne
  rw [psi.psdSchattenPNorm_highReferenceInner_eq_highCMatrix
    sigma hsigma halpha] at hpos
  exact hpos

theorem upwardRenyiDualityLowNorm_pos_of_posDef
    (psi : Ket ((a × b) × c))
    (tau : MState c) (htau : tau.m.PosDef)
    {alpha beta : ℝ} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    0 < psi.upwardRenyiDualityLowNorm tau alpha
      ⟨beta, lt_trans (by norm_num) hbeta_half⟩ := by
  have href : (MState.identityTensorStateMatrix (a := a) tau).PosDef :=
    MState.identityTensorStateMatrix_posDef_of_posDef (a := a) tau htau
  have hne := MState.sandwichedRenyiReferenceInner_ne_zero_of_reference_posDef
    psi.state.marginalAC href beta
  have hpos := psdSchattenPNorm_pos_of_ne_zero
    (MState.sandwichedRenyiReferenceInner psi.state.marginalAC
      (MState.identityTensorStateMatrix (a := a) tau) beta)
    (MState.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAC
      (MState.identityTensorStateMatrix_posSemidef (a := a) tau) beta)
    (p := ⟨beta, lt_trans (by norm_num) hbeta_half⟩) hne
  rw [psi.psdSchattenPNorm_lowReferenceInner_eq_effectiveBMatrix
    tau halpha hbeta_half hbeta_one hconj] at hpos
  exact hpos

theorem upwardRenyiDualityLowNorm_range_bddAbove
    [Nonempty b] [Nonempty c]
    (psi : Ket ((a × b) × c))
    {alpha beta : ℝ} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    BddAbove (Set.range fun tau : MState c =>
      psi.upwardRenyiDualityLowNorm tau alpha
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩) := by
  let sigma0 : {sigma : MState b // sigma.m.PosDef} :=
    ⟨(MState.uniform : MState b), MState.uniform_posDef⟩
  refine ⟨psi.upwardRenyiDualityHighNorm sigma0.1
    ⟨alpha, lt_trans zero_lt_one halpha⟩, ?_⟩
  rintro x ⟨tau, rfl⟩
  have hleast := psi.upwardRenyiDualityLowBracket_isLeast tau
    halpha hbeta_half hbeta_one hconj
  have hsupport : Matrix.Supports
      (psi.upwardRenyiDualityEffectiveBMatrix tau.m
        (upwardRenyiDualityParameter alpha)) sigma0.1.m :=
    Matrix.Supports.of_right_posDef _ _ sigma0.2
  have hlow : psi.upwardRenyiDualityLowNorm tau alpha
      ⟨beta, lt_trans (by norm_num) hbeta_half⟩ ≤
      MState.abcSidePowerTraceRe (a := a) psi.state.m
        sigma0.1.m tau.m (upwardRenyiDualityParameter alpha) := by
    exact hleast.2 ⟨sigma0.1, hsupport, rfl⟩
  have hhigh := psi.upwardRenyiDualityHighBracket_isGreatest
    sigma0.1 sigma0.2 halpha
  exact hlow.trans (hhigh.2 ⟨tau, rfl⟩)

private theorem upwardRenyiDuality_commonSchattenExtrema_eq_named
    [Nonempty b] [Nonempty c]
    (psi : Ket ((a × b) × c))
    {alpha beta : ℝ} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    sInf (Set.range fun sigma : {sigma : MState b // sigma.m.PosDef} =>
      psi.upwardRenyiDualityHighNorm sigma.1
        ⟨alpha, lt_trans zero_lt_one halpha⟩) =
      sSup (Set.range fun tau : MState c =>
        psi.upwardRenyiDualityLowNorm tau alpha
          ⟨beta, lt_trans (by norm_num) hbeta_half⟩) := by
  simpa [upwardRenyiDualityHighNorm, upwardRenyiDualityLowNorm] using
    psi.upwardRenyiDuality_commonSchattenExtrema_eq
      halpha hbeta_half hbeta_one hconj

private theorem upwardRenyiDualityLowNorm_fullRank_sSup_eq_all_named
    [Nonempty b] [Nonempty c]
    (psi : Ket ((a × b) × c))
    {alpha beta : ℝ} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    sSup (Set.range fun tau : {tau : MState c // tau.m.PosDef} =>
      psi.upwardRenyiDualityLowNorm tau.1 alpha
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩) =
      sSup (Set.range fun tau : MState c =>
      psi.upwardRenyiDualityLowNorm tau alpha
        ⟨beta, lt_trans (by norm_num) hbeta_half⟩) := by
  simpa [upwardRenyiDualityLowNorm] using
    psi.upwardRenyiDualityLowNorm_fullRank_sSup_eq_all
      halpha hbeta_half hbeta_one hconj

theorem upwardRenyiDuality_commonSchattenExtremum_pos
    [Nonempty b] [Nonempty c]
    (psi : Ket ((a × b) × c))
    {alpha beta : ℝ} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    0 < sInf (Set.range fun sigma : {sigma : MState b // sigma.m.PosDef} =>
      psi.upwardRenyiDualityHighNorm sigma.1
        ⟨alpha, lt_trans zero_lt_one halpha⟩) := by
  rw [psi.upwardRenyiDuality_commonSchattenExtrema_eq_named
    halpha hbeta_half hbeta_one hconj]
  rw [← psi.upwardRenyiDualityLowNorm_fullRank_sSup_eq_all_named
    halpha hbeta_half hbeta_one hconj]
  let tau0 : {tau : MState c // tau.m.PosDef} :=
    ⟨(MState.uniform : MState c), MState.uniform_posDef⟩
  have hall_bdd := psi.upwardRenyiDualityLowNorm_range_bddAbove
    halpha hbeta_half hbeta_one hconj
  have hfull_bdd : BddAbove (Set.range fun tau :
      {tau : MState c // tau.m.PosDef} =>
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
    (psi : Ket ((a × b) × c))
    {alpha beta : ℝ} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    psi.state.marginalAB.conditionalSandwichedRenyiUpSource alpha
        (lt_trans zero_lt_one halpha) (ne_of_gt halpha) =
      -(1 / upwardRenyiDualityParameter alpha) *
        log2 (sInf (Set.range fun sigma :
          {sigma : MState b // sigma.m.PosDef} =>
            psi.upwardRenyiDualityHighNorm sigma.1
              ⟨alpha, lt_trans zero_lt_one halpha⟩)) := by
  let S := {sigma : MState b // sigma.m.PosDef}
  let high : S → ℝ := fun sigma =>
    psi.upwardRenyiDualityHighNorm sigma.1
      ⟨alpha, lt_trans zero_lt_one halpha⟩
  let coeff : ℝ := 1 / upwardRenyiDualityParameter alpha
  let candidate : S → ℝ := fun sigma =>
    psi.state.marginalAB.conditionalSandwichedRenyiUpSourceCandidate
      sigma.1 sigma.2 alpha (lt_trans zero_lt_one halpha) (ne_of_gt halpha)
  let : Nonempty S :=
    ⟨⟨(MState.uniform : MState b), MState.uniform_posDef⟩⟩
  have hp : 0 < upwardRenyiDualityParameter alpha :=
    upwardRenyiDualityParameter_pos halpha
  have hcoeff : 0 ≤ coeff := (one_div_pos.mpr hp).le
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
      (fun x : ℝ => -log2 x) '' Set.range high := by
    ext x
    constructor
    · rintro ⟨sigma, rfl⟩
      exact ⟨high sigma, ⟨sigma, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨sigma, rfl⟩, rfl⟩
      exact ⟨sigma, rfl⟩
  unfold MState.conditionalSandwichedRenyiUpSource
  rw [MState.conditionalSandwichedRenyiUpSourceValueSet_eq_range]
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
      sSup_range_mul_eq_mul_sSup_range _ hcoeff
    _ = coeff * (-log2 (sInf (Set.range high))) := by
      rw [himage, neg_log2_sInf_image_eq
        (Set.range_nonempty high) hhigh_bdd hinf_pos]
    _ = -(1 / upwardRenyiDualityParameter alpha) *
        log2 (sInf (Set.range high)) := by simp [coeff]

/-- Low-order source entropy as the positive logarithm of the same common
Schatten extremum, with the full-rank optimization retained. -/
theorem conditionalSandwichedRenyiUpSource_marginalAC_eq_commonLog
    [Nonempty b] [Nonempty c]
    (psi : Ket ((a × b) × c))
    {alpha beta : ℝ} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2) :
    psi.state.marginalAC.conditionalSandwichedRenyiUpSource beta
        (lt_trans (by norm_num) hbeta_half) (ne_of_lt hbeta_one) =
      (1 / upwardRenyiDualityParameter alpha) *
        log2 (sSup (Set.range fun tau :
          {tau : MState c // tau.m.PosDef} =>
            psi.upwardRenyiDualityLowNorm tau.1 alpha
              ⟨beta, lt_trans (by norm_num) hbeta_half⟩)) := by
  let T := {tau : MState c // tau.m.PosDef}
  let low : T → ℝ := fun tau =>
    psi.upwardRenyiDualityLowNorm tau.1 alpha
      ⟨beta, lt_trans (by norm_num) hbeta_half⟩
  let coeff : ℝ := 1 / upwardRenyiDualityParameter alpha
  let candidate : T → ℝ := fun tau =>
    psi.state.marginalAC.conditionalSandwichedRenyiUpSourceCandidate
      tau.1 tau.2 beta (lt_trans (by norm_num) hbeta_half) (ne_of_lt hbeta_one)
  let : Nonempty T :=
    ⟨⟨(MState.uniform : MState c), MState.uniform_posDef⟩⟩
  have hp : 0 < upwardRenyiDualityParameter alpha :=
    upwardRenyiDualityParameter_pos halpha
  have hcoeff : 0 ≤ coeff := (one_div_pos.mpr hp).le
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
  unfold MState.conditionalSandwichedRenyiUpSource
  rw [MState.conditionalSandwichedRenyiUpSourceValueSet_eq_range]
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
      sSup_range_mul_eq_mul_sSup_range _ hcoeff
    _ = coeff * log2 (sSup (Set.range low)) := by
      rw [himage, log2_sSup_image_eq
        (Set.range_nonempty low) hlow_bdd hlow_pos]

/-- Tomamichel's normalized pure-state upward sandwiched conditional Renyi
duality (`cond.tex`, Proposition `pr:dual-new`).  Singular marginals are
allowed: support failures are accounted for by the support-aware extended
bracket before the Sion exchange. -/
theorem conditionalSandwichedRenyiUpSource_duality
    [Nonempty b] [Nonempty c]
    (psi : Ket ((a × b) × c))
    {alpha beta : ℝ} (halpha : 1 < alpha)
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

end Ket

namespace QIT

namespace SubnormalizedState

/-- The positive-trace extension of the source-shaped upward sandwiched
conditional Renyi entropy.  It uses Tomamichel's convention
`H_tilde^up_alpha(t rho) = H_tilde^up_alpha(rho) - log2 t`. -/
noncomputable def conditionalSandwichedRenyiUpSource
    (rho : SubnormalizedState (a × b)) (alpha : ℝ)
    (hAlphaPos : 0 < alpha) (hAlphaNeOne : alpha ≠ 1)
    (htrace : 0 < rho.matrix.trace.re) : ℝ :=
  (rho.normalize htrace.ne').conditionalSandwichedRenyiUpSource
      alpha hAlphaPos hAlphaNeOne -
    log2 rho.matrix.trace.re

theorem normalize_ofStateScale
    (rho : MState (a × b)) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (ofStateScale rho t ht.le ht1).normalize
        (by rw [ofStateScale_trace_re]; exact ht.ne') = rho := by
  apply MState.ext
  rw [normalize_matrix, ofStateScale_trace_re, ofStateScale_matrix]
  ext i j
  simp [ht.ne']

/-- Scaling a normalized bipartite state shifts the source entropy by
`-log2 t`. -/
theorem conditionalSandwichedRenyiUpSource_ofStateScale
    (rho : MState (a × b)) {t alpha : ℝ}
    (hAlphaPos : 0 < alpha) (hAlphaNeOne : alpha ≠ 1)
    (ht : 0 < t) (ht1 : t ≤ 1) :
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
    (psi : Ket ((a × b) × c))
    {alpha beta t : ℝ} (halpha : 1 < alpha)
    (hbeta_half : 1 / 2 < beta) (hbeta_one : beta < 1)
    (hconj : 1 / alpha + 1 / beta = 2)
    (ht : 0 < t) (ht1 : t ≤ 1) :
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

end QIT
