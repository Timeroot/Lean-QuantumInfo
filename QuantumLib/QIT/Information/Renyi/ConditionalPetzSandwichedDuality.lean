/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Renyi.ConditionalPetzRenyiAlternative
public import QuantumLib.QIT.Information.Renyi.ConditionalPetzRenyiDuality
public import QuantumLib.QIT.Information.Renyi.ConditionalSandwichedRenyiDuality

/-!
# Mixed Petz/sandwiched conditional Renyi duality

Source-shaped lemmas for Tomamichel2015FiniteResources, `cond.tex`,
Proposition `pr:dual-both` and Eq. `eq:marginals`, lines 408--440.

The proof follows the source route:

* use Lemma `lm:dau-new` for the upward Petz side;
* identify the Petz closed trace with the sandwiched-down trace power by a
  common weighted rank-one operator;
* close the entropy identity by the parameter relation `alpha * beta = 1`.

The theorem realized here is the normalized non-endpoint statement available
through the current finite-dimensional APIs.  It does not claim endpoint
conventions at `0`, `1`, or `∞`, and the sandwiched-down side keeps the current
positive-definite API hypotheses.
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

/-- Parameter algebra for Tomamichel2015FiniteResources, `cond.tex:420`:
from `alpha * beta = 1`, the finite nonzero parameter `beta` is `alpha⁻¹`. -/
theorem mixedPetzSandwiched_beta_eq_inv {alpha beta : ℝ}
    (halpha_ne_zero : alpha ≠ 0) (hdual : alpha * beta = 1) :
    beta = alpha⁻¹ := by
  calc
    beta = (alpha⁻¹ * alpha) * beta := by
      rw [inv_mul_cancel₀ halpha_ne_zero]
      simp
    _ = alpha⁻¹ * (alpha * beta) := by ring
    _ = alpha⁻¹ := by
      rw [hdual]
      simp

/-- The sandwiched reference exponent under the mixed duality relation:
`(1 - beta)/(2 beta) = (alpha - 1)/2`. -/
theorem mixedPetzSandwiched_sandwichedExponent_eq
    {alpha beta : ℝ} (halpha_ne_zero : alpha ≠ 0)
    (hdual : alpha * beta = 1) :
    (1 - beta) / (2 * beta) = (alpha - 1) / 2 := by
  have hbeta : beta = alpha⁻¹ :=
    mixedPetzSandwiched_beta_eq_inv halpha_ne_zero hdual
  subst beta
  field_simp [halpha_ne_zero]

/-- Coefficient cancellation for the final mixed duality scalar identity. -/
theorem mixedPetzSandwiched_coeff_cancel
    {alpha beta : ℝ} (halpha_ne_zero : alpha ≠ 0)
    (halpha_ne_one : alpha ≠ 1) (hdual : alpha * beta = 1) :
    alpha / (1 - alpha) + 1 / (1 - beta) = 0 := by
  have hbeta : beta = alpha⁻¹ :=
    mixedPetzSandwiched_beta_eq_inv halpha_ne_zero hdual
  subst beta
  field_simp [halpha_ne_zero, halpha_ne_one]
  ring

/-- Source rewrite `rho^s rho rho^s = rho^alpha` with
`s = (alpha - 1)/2`, used in `cond.tex:436`. -/
theorem cMatrix_rpow_half_sub_one_sandwich_eq_rpow
    {d : Type*} [Fintype d] [DecidableEq d] {A : CMatrix d}
    (hA : A.PosSemidef) {alpha : ℝ} (halpha_pos : 0 < alpha) :
    CFC.rpow A ((alpha - 1) / 2) * A * CFC.rpow A ((alpha - 1) / 2) =
      CFC.rpow A alpha := by
  let p : ℝ := (alpha - 1) / 2
  have hA_one : CFC.rpow A (1 : ℝ) = A :=
    CFC.rpow_one A (ha := Matrix.nonneg_iff_posSemidef.mpr hA)
  have hp_one_ne : p + 1 ≠ 0 := by
    dsimp [p]
    nlinarith
  have hp_alpha_ne : (p + 1) + p ≠ 0 := by
    dsimp [p]
    nlinarith
  calc
    CFC.rpow A ((alpha - 1) / 2) * A * CFC.rpow A ((alpha - 1) / 2) =
        CFC.rpow A p * CFC.rpow A (1 : ℝ) * CFC.rpow A p := by
          dsimp [p]
          exact congrArg
            (fun X => CFC.rpow A ((alpha - 1) / 2) * X *
              CFC.rpow A ((alpha - 1) / 2))
            hA_one.symm
    _ = CFC.rpow A (p + 1) * CFC.rpow A p := by
          rw [cMatrix_rpow_add_psd hA hp_one_ne]
    _ = CFC.rpow A ((p + 1) + p) := by
          rw [cMatrix_rpow_add_psd hA hp_alpha_ne]
    _ = CFC.rpow A alpha := by
          congr 1
          dsimp [p]
          ring

end MState

namespace Ket

/-- The purifying vector reindexed to the `(a × c) × b` grouping and weighted by
`ρ_C^((α-1)/2)` on the `c` register.  Its Gram matrix carries the `A|C` side of the duality. -/
def mixedPetzSandwichedACBWeightedAmplitude
    (psi : Ket ((a × b) × c)) (alpha : ℝ) :
    (a × c) × b → ℂ :=
  let phi := psi.reindex (QIT.prodABCToACBEquiv (a := a) (b := b) (c := c))
  let W : CMatrix (a × c) :=
    Matrix.kronecker (1 : CMatrix a)
      (CFC.rpow psi.state.marginalAC.traceLeft.m ((alpha - 1) / 2))
  Matrix.mulVec (Matrix.kronecker W (1 : CMatrix b)) phi.vec

/-- The purifying vector weighted by `ρ_AB^((α-1)/2)` on the `a × b` registers, carrying the
`A|B` side of the duality. -/
def mixedPetzSandwichedABWeightedAmplitude
    (psi : Ket ((a × b) × c)) (alpha : ℝ) :
    (a × b) × c → ℂ :=
  Matrix.mulVec
    (Matrix.kronecker
      (CFC.rpow psi.state.marginalAB.m ((alpha - 1) / 2))
      (1 : CMatrix c))
    psi.vec

omit [DecidableEq a] [Fintype b] [DecidableEq b] [DecidableEq c] in
private theorem traceLeft_rankOne_ACB_reindex_eq_traceLeft_traceRight_ABC
    (v : (a × b) × c → ℂ) :
    Matrix.traceLeft
        (rankOneMatrix
          (fun x : (a × c) × b => v ((x.1.1, x.2), x.1.2))) =
      Matrix.traceLeft
        (Matrix.traceRight (rankOneMatrix v)) := by
  ext j j'
  simp [Matrix.traceLeft, Matrix.traceRight, rankOneMatrix_apply, Fintype.sum_prod_type]

theorem mixedPetzSandwichedACBWeightedAmplitude_eq_reindex_ABWeightedAmplitude
    (psi : Ket ((a × b) × c)) (alpha : ℝ) :
    psi.mixedPetzSandwichedACBWeightedAmplitude alpha =
      fun x : (a × c) × b =>
        psi.mixedPetzSandwichedABWeightedAmplitude alpha ((x.1.1, x.2), x.1.2) := by
  let p : ℝ := (alpha - 1) / 2
  let e := QIT.prodABCToACBEquiv (a := a) (b := b) (c := c)
  have hmove :=
    ket_rpow_traceRight_tensor_one_mulVec_eq_one_tensor_traceLeft_rpow_mulVec
      (r := a × b) (s := c) psi p
  have hC : psi.state.marginalAC.traceLeft = psi.state.traceLeft :=
    MState.marginalAC_traceLeft_eq_traceLeft psi.state
  have hCmat : psi.state.marginalAC.traceLeft.m = psi.state.traceLeft.m :=
    congrArg DensityOp.m hC
  let T : CMatrix c := CFC.rpow psi.state.traceLeft.m p
  let KC : CMatrix ((a × b) × c) :=
    Matrix.kronecker (1 : CMatrix (a × b)) T
  let KACB : CMatrix ((a × c) × b) :=
    Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) T) (1 : CMatrix b)
  let phi : Ket ((a × c) × b) := psi.reindex e
  have hACB_matrix :
      Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalAC.traceLeft.m p))
          (1 : CMatrix b) = KACB := by
    dsimp [KACB, T]
    rw [hCmat]
  have hACB_def :
      psi.mixedPetzSandwichedACBWeightedAmplitude alpha =
        Matrix.mulVec KACB phi.vec := by
    ext y
    change
      (Matrix.mulVec
        (Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalAC.traceLeft.m p))
          (1 : CMatrix b))
        (psi.reindex e).vec) y =
      (Matrix.mulVec KACB phi.vec) y
    rw [hACB_matrix]
  have hKC_submatrix :
      KC.submatrix e.symm e.symm = KACB := by
    simpa [KC, KACB, T, e] using
      prodABCToACB_submatrix_refC
        (a := a) (b := b) (c := c) T
  ext x
  rcases x with ⟨⟨i, k⟩, j⟩
  have hx := congrFun hmove ((i, j), k)
  have hleft :
      psi.mixedPetzSandwichedACBWeightedAmplitude alpha ((i, k), j) =
        (Matrix.kronecker (1 : CMatrix (a × b))
            (CFC.rpow psi.state.traceLeft.m p)).mulVec psi.vec ((i, j), k) := by
    rw [hACB_def]
    change Matrix.mulVec KACB phi.vec ((i, k), j) =
      Matrix.mulVec KC psi.vec ((i, j), k)
    rw [← hKC_submatrix]
    simp [KC, T, phi, e, Ket.reindex_vec,
      QIT.prodABCToACBEquiv, Matrix.mulVec, dotProduct, Matrix.kronecker,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro _ _
    rw [Finset.sum_comm]
  have hab :
      psi.mixedPetzSandwichedABWeightedAmplitude alpha ((i, j), k) =
        (Matrix.kronecker
          (CFC.rpow psi.state.marginalAB.m p) (1 : CMatrix c)).mulVec
          psi.vec ((i, j), k) := by
    rfl
  rw [hleft, hab]
  exact hx.symm

/-- AC-side half of Tomamichel's Eq. `eq:marginals`: the common weighted
rank-one operator has AC marginal equal to the sandwiched-down reference inner. -/
theorem traceRight_rankOne_mixedPetzSandwichedACBWeightedAmplitude_eq_referenceInner
    (psi : Ket ((a × b) × c))
    (hC : psi.state.marginalAC.traceLeft.m.PosDef)
    {alpha beta : ℝ} (halpha_ne_zero : alpha ≠ 0)
    (hdual : alpha * beta = 1) :
    Matrix.traceRight
        (rankOneMatrix (psi.mixedPetzSandwichedACBWeightedAmplitude alpha)) =
      MState.sandwichedRenyiReferenceInner psi.state.marginalAC
        (MState.identityTensorStateMatrix (a := a) psi.state.marginalAC.traceLeft)
        beta := by
  let phi := psi.reindex (QIT.prodABCToACBEquiv (a := a) (b := b) (c := c))
  let tau := psi.state.marginalAC.traceLeft
  let p : ℝ := (alpha - 1) / 2
  let W : CMatrix (a × c) :=
    Matrix.kronecker (1 : CMatrix a) (CFC.rpow tau.m p)
  have hp :
      (1 - beta) / (2 * beta) = p := by
    simpa [p] using
      MState.mixedPetzSandwiched_sandwichedExponent_eq halpha_ne_zero hdual
  have hmarg :
      Matrix.traceRight (rankOneMatrix phi.vec) =
        psi.state.marginalAC.m := by
    ext x y
    rcases x with ⟨i, k⟩
    rcases y with ⟨i', k'⟩
    simp [phi, MState.marginalAC_matrix, Matrix.traceRight,
      QIT.prodABCToACBEquiv]
  have hWherm : Matrix.conjTranspose W = W := by
    have hWpsd : W.PosSemidef := by
      dsimp [W, tau, p]
      exact Matrix.PosSemidef.one.kronecker
        (cMatrix_rpow_posSemidef
          (A := psi.state.marginalAC.traceLeft.m)
          (s := (alpha - 1) / 2) psi.state.marginalAC.traceLeft.psd)
    exact hWpsd.isHermitian.eq
  change Matrix.traceRight
      (rankOneMatrix (Matrix.mulVec (Matrix.kronecker W (1 : CMatrix b)) phi.vec)) =
    MState.sandwichedRenyiReferenceInner psi.state.marginalAC
      (MState.identityTensorStateMatrix (a := a) tau) beta
  rw [traceRight_rankOne_kron_left_mulVec_eq, hmarg, hWherm]
  unfold MState.sandwichedRenyiReferenceInner
  change W * psi.state.marginalAC.m * W =
    CFC.rpow (MState.identityTensorStateMatrix (a := a) tau)
        ((1 - beta) / (2 * beta)) *
      psi.state.marginalAC.m *
      CFC.rpow (MState.identityTensorStateMatrix (a := a) tau)
        ((1 - beta) / (2 * beta))
  rw [hp]
  have href :
      CFC.rpow (MState.identityTensorStateMatrix (a := a) tau) p = W := by
    simpa [W, tau, MState.identityTensorStateMatrix] using
      cMatrix_rpow_kronecker
        (A := (1 : CMatrix a)) (B := tau.m) Matrix.PosSemidef.one hC.posSemidef p
  rw [href]

/-- B-side half of Tomamichel's Eq. `eq:marginals`: the same weighted rank-one
operator has B marginal equal to `Tr_A(rho_AB^alpha)`. -/
theorem traceLeft_rankOne_mixedPetzSandwichedACBWeightedAmplitude_eq_petzTraceMatrix
    (psi : Ket ((a × b) × c))
    {alpha : ℝ} (halpha_pos : 0 < alpha) :
    Matrix.traceLeft
        (rankOneMatrix (psi.mixedPetzSandwichedACBWeightedAmplitude alpha)) =
      psi.state.marginalAB.conditionalPetzRenyiUpTraceMatrix alpha := by
  let p : ℝ := (alpha - 1) / 2
  let Wab : CMatrix (a × b) := CFC.rpow psi.state.marginalAB.m p
  have hamp :=
    psi.mixedPetzSandwichedACBWeightedAmplitude_eq_reindex_ABWeightedAmplitude alpha
  rw [hamp]
  rw [traceLeft_rankOne_ACB_reindex_eq_traceLeft_traceRight_ABC]
  change Matrix.traceLeft
      (Matrix.traceRight
        (rankOneMatrix
          (Matrix.mulVec (Matrix.kronecker Wab (1 : CMatrix c)) psi.vec))) =
    psi.state.marginalAB.conditionalPetzRenyiUpTraceMatrix alpha
  rw [traceRight_rankOne_kron_left_mulVec_eq]
  have hmargAB :
      Matrix.traceRight (rankOneMatrix psi.vec) =
        psi.state.marginalAB.m := by
    ext x y
    rcases x with ⟨i, j⟩
    rcases y with ⟨i', j'⟩
    simp [MState.marginalAB, Matrix.traceRight]
  have hWherm : Matrix.conjTranspose Wab = Wab := by
    have hWpsd : Wab.PosSemidef := by
      dsimp [Wab, p]
      exact cMatrix_rpow_posSemidef
        (A := psi.state.marginalAB.m) (s := (alpha - 1) / 2)
        psi.state.marginalAB.psd
    exact hWpsd.isHermitian.eq
  rw [hmargAB, hWherm]
  dsimp [Wab, p, MState.conditionalPetzRenyiUpTraceMatrix]
  exact congrArg (Matrix.traceLeft)
    (MState.cMatrix_rpow_half_sub_one_sandwich_eq_rpow
      psi.state.marginalAB.psd halpha_pos)

/-- Trace-power form of the source marginal equivalence Eq. `eq:marginals`. -/
theorem mixedPetzSandwiched_closedTrace_eq_sandwichedDownTracePower
    (psi : Ket ((a × b) × c))
    (hC : psi.state.marginalAC.traceLeft.m.PosDef)
    {alpha beta : ℝ} (halpha_pos : 0 < alpha)
    (hbeta_pos : 0 < beta) (hdual : alpha * beta = 1) :
    psi.state.marginalAB.conditionalPetzRenyiUpClosedTrace alpha =
      psdTracePower
        (MState.sandwichedRenyiReferenceInner psi.state.marginalAC
          (MState.identityTensorStateMatrix (a := a) psi.state.marginalAC.traceLeft)
          beta)
        (MState.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAC
          (MState.identityTensorStateMatrix_posSemidef
            (a := a) psi.state.marginalAC.traceLeft)
          beta)
        beta := by
  have hB :=
    traceLeft_rankOne_mixedPetzSandwichedACBWeightedAmplitude_eq_petzTraceMatrix
      (a := a) (b := b) (c := c) psi halpha_pos
  have hAC :=
    traceRight_rankOne_mixedPetzSandwichedACBWeightedAmplitude_eq_referenceInner
      (a := a) (b := b) (c := c) psi hC (ne_of_gt halpha_pos) hdual
  have hcomp :=
    psdTracePower_traceRight_rankOneMatrix_eq_traceLeft_rankOneMatrix
      (r := a × c) (a := b)
      (psi.mixedPetzSandwichedACBWeightedAmplitude alpha) hbeta_pos
  have hbeta_eq : beta = alpha⁻¹ :=
    MState.mixedPetzSandwiched_beta_eq_inv (ne_of_gt halpha_pos) hdual
  have hinv_eq : (1 / alpha : ℝ) = beta := by
    simpa [one_div] using hbeta_eq.symm
  rw [MState.conditionalPetzRenyiUpClosedTrace_eq_psdTracePower]
  rw [hinv_eq]
  simpa [hB, hAC] using hcomp.symm

/-- Normalized non-endpoint mixed Petz/sandwiched conditional Renyi duality.

This is the current Lean realization of Tomamichel2015FiniteResources,
`cond.tex`, Proposition `pr:dual-both`, lines 408--440, under the local API's
finite non-endpoint and positive-definite sandwiched-reference hypotheses. -/
theorem conditionalPetzSandwichedRenyi_duality_source
    [Nonempty b]
    (psi : Ket ((a × b) × c))
    (hAC : psi.state.marginalAC.m.PosDef)
    (hC : psi.state.marginalAC.traceLeft.m.PosDef)
    {alpha beta : ℝ}
    (halpha_pos : 0 < alpha) (hbeta_pos : 0 < beta)
    (halpha_ne_one : alpha ≠ 1) (hbeta_ne_one : beta ≠ 1)
    (hdual : alpha * beta = 1) :
    psi.state.marginalAB.conditionalPetzRenyiUp
        alpha halpha_pos halpha_ne_one +
      psi.state.marginalAC.conditionalSandwichedRenyiDown
        hAC hC beta hbeta_pos hbeta_ne_one =
      0 := by
  have htrace :=
    mixedPetzSandwiched_closedTrace_eq_sandwichedDownTracePower
      (a := a) (b := b) (c := c) psi hC halpha_pos hbeta_pos hdual
  have hpetz :
      psi.state.marginalAB.conditionalPetzRenyiUp
          alpha halpha_pos halpha_ne_one =
        (alpha / (1 - alpha)) *
          log2 (psi.state.marginalAB.conditionalPetzRenyiUpClosedTrace alpha) := by
    rw [MState.conditionalPetzRenyiUp_eq_alternative]
    rfl
  have hdown :
      psi.state.marginalAC.conditionalSandwichedRenyiDown
          hAC hC beta hbeta_pos hbeta_ne_one =
        (1 / (1 - beta)) *
          log2 (psdTracePower
            (MState.sandwichedRenyiReferenceInner psi.state.marginalAC
              (MState.identityTensorStateMatrix
                (a := a) psi.state.marginalAC.traceLeft)
              beta)
            (MState.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAC
              (MState.identityTensorStateMatrix_posSemidef
                (a := a) psi.state.marginalAC.traceLeft)
              beta)
            beta) := by
    rw [MState.conditionalSandwichedRenyiDown_eq]
    rw [MState.sandwichedRenyiReference_eq_log2_psdTracePower_inner]
    set L : ℝ :=
      log2 (psdTracePower
        (MState.sandwichedRenyiReferenceInner psi.state.marginalAC
          (MState.identityTensorStateMatrix
            (a := a) psi.state.marginalAC.traceLeft)
          beta)
        (MState.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAC
          (MState.identityTensorStateMatrix_posSemidef
            (a := a) psi.state.marginalAC.traceLeft)
          beta)
        beta)
    have hden : 1 - beta = -(beta - 1) := by ring
    rw [hden]
    have hone : 1 / -(beta - 1) = (-(beta - 1))⁻¹ := by
      exact one_div (-(beta - 1))
    rw [hone, inv_neg]
    ring
  rw [hpetz, hdown, htrace]
  let L : ℝ :=
    log2 (psdTracePower
      (MState.sandwichedRenyiReferenceInner psi.state.marginalAC
        (MState.identityTensorStateMatrix (a := a) psi.state.marginalAC.traceLeft)
        beta)
      (MState.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAC
        (MState.identityTensorStateMatrix_posSemidef
          (a := a) psi.state.marginalAC.traceLeft)
        beta)
      beta)
  change alpha / (1 - alpha) * L + 1 / (1 - beta) * L = 0
  have hcoeff :
      alpha / (1 - alpha) + 1 / (1 - beta) = 0 :=
    MState.mixedPetzSandwiched_coeff_cancel
      (ne_of_gt halpha_pos) halpha_ne_one hdual
  calc
    alpha / (1 - alpha) * L + 1 / (1 - beta) * L =
        (alpha / (1 - alpha) + 1 / (1 - beta)) * L := by ring
    _ = 0 := by
      rw [hcoeff]
      ring

end Ket
