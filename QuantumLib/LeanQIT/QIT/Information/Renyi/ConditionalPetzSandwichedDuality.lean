/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.ConditionalPetzRenyiAlternative
public import QIT.Information.Renyi.ConditionalPetzRenyiDuality
public import QIT.Information.Renyi.ConditionalSandwichedRenyiDuality

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

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

namespace State

/-- Parameter algebra for Tomamichel2015FiniteResources, `cond.tex:420`:
from `alpha * beta = 1`, the finite nonzero parameter `beta` is `alpha⁻¹`. -/
theorem mixedPetzSandwiched_beta_eq_inv {alpha beta : Real}
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
    {alpha beta : Real} (halpha_ne_zero : alpha ≠ 0)
    (hdual : alpha * beta = 1) :
    (1 - beta) / (2 * beta) = (alpha - 1) / 2 := by
  have hbeta : beta = alpha⁻¹ :=
    mixedPetzSandwiched_beta_eq_inv halpha_ne_zero hdual
  subst beta
  field_simp [halpha_ne_zero]

/-- Coefficient cancellation for the final mixed duality scalar identity. -/
theorem mixedPetzSandwiched_coeff_cancel
    {alpha beta : Real} (halpha_ne_zero : alpha ≠ 0)
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
    (hA : A.PosSemidef) {alpha : Real} (halpha_pos : 0 < alpha) :
    CFC.rpow A ((alpha - 1) / 2) * A * CFC.rpow A ((alpha - 1) / 2) =
      CFC.rpow A alpha := by
  let p : Real := (alpha - 1) / 2
  have hA_one : CFC.rpow A (1 : Real) = A :=
    CFC.rpow_one A (ha := Matrix.nonneg_iff_posSemidef.mpr hA)
  have hp_one_ne : p + 1 ≠ 0 := by
    dsimp [p]
    nlinarith
  have hp_alpha_ne : (p + 1) + p ≠ 0 := by
    dsimp [p]
    nlinarith
  calc
    CFC.rpow A ((alpha - 1) / 2) * A * CFC.rpow A ((alpha - 1) / 2) =
        CFC.rpow A p * CFC.rpow A (1 : Real) * CFC.rpow A p := by
          dsimp [p]
          exact congrArg
            (fun X => CFC.rpow A ((alpha - 1) / 2) * X *
              CFC.rpow A ((alpha - 1) / 2))
            hA_one.symm
    _ = CFC.rpow A (p + 1) * CFC.rpow A p := by
          rw [cMatrix_rpow_add_psd_forPetz hA hp_one_ne]
    _ = CFC.rpow A ((p + 1) + p) := by
          rw [cMatrix_rpow_add_psd_forPetz hA hp_alpha_ne]
    _ = CFC.rpow A alpha := by
          congr 1
          dsimp [p]
          ring

end State

namespace PureVector

def mixedPetzSandwichedACBWeightedAmplitude
    (psi : PureVector (Prod (Prod a b) c)) (alpha : Real) :
    Prod (Prod a c) b → Complex :=
  let phi := psi.reindex (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))
  let W : CMatrix (Prod a c) :=
    Matrix.kronecker (1 : CMatrix a)
      (CFC.rpow psi.state.marginalAC.marginalB.matrix ((alpha - 1) / 2))
  Matrix.mulVec (Matrix.kronecker W (1 : CMatrix b)) phi.amp

def mixedPetzSandwichedABWeightedAmplitude
    (psi : PureVector (Prod (Prod a b) c)) (alpha : Real) :
    Prod (Prod a b) c → Complex :=
  Matrix.mulVec
    (Matrix.kronecker
      (CFC.rpow psi.state.marginalAB.matrix ((alpha - 1) / 2))
      (1 : CMatrix c))
    psi.amp

private theorem mixedPetzSandwiched_marginalAC_marginalB_eq_marginalB
    (psi : PureVector (Prod (Prod a b) c)) :
    psi.state.marginalAC.marginalB = psi.state.marginalB := by
  apply State.ext
  ext k k'
  simp [State.marginalAC, State.marginalB, partialTraceA, Fintype.sum_prod_type]

omit [DecidableEq a] [Fintype b] [DecidableEq b] [DecidableEq c] in
private theorem partialTraceA_rankOne_ACB_reindex_eq_partialTraceA_partialTraceB_ABC
    (v : Prod (Prod a b) c → Complex) :
    partialTraceA (a := Prod a c) (b := b)
        (rankOneMatrix
          (fun x : Prod (Prod a c) b => v ((x.1.1, x.2), x.1.2))) =
      partialTraceA (a := a) (b := b)
        (partialTraceB (a := Prod a b) (b := c) (rankOneMatrix v)) := by
  ext j j'
  simp [partialTraceA, partialTraceB, rankOneMatrix_apply, Fintype.sum_prod_type]

theorem mixedPetzSandwichedACBWeightedAmplitude_eq_reindex_ABWeightedAmplitude
    (psi : PureVector (Prod (Prod a b) c)) (alpha : Real) :
    psi.mixedPetzSandwichedACBWeightedAmplitude alpha =
      fun x : Prod (Prod a c) b =>
        psi.mixedPetzSandwichedABWeightedAmplitude alpha ((x.1.1, x.2), x.1.2) := by
  let p : Real := (alpha - 1) / 2
  let e := conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c)
  have hmove :=
    pureVector_rpow_marginalA_tensor_one_mulVec_eq_one_tensor_marginalB_rpow_mulVec
      (r := Prod a b) (s := c) psi p
  have hC : psi.state.marginalAC.marginalB = psi.state.marginalB :=
    mixedPetzSandwiched_marginalAC_marginalB_eq_marginalB psi
  have hCmat : psi.state.marginalAC.marginalB.matrix = psi.state.marginalB.matrix :=
    congrArg State.matrix hC
  let T : CMatrix c := CFC.rpow psi.state.marginalB.matrix p
  let KC : CMatrix (Prod (Prod a b) c) :=
    Matrix.kronecker (1 : CMatrix (Prod a b)) T
  let KACB : CMatrix (Prod (Prod a c) b) :=
    Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) T) (1 : CMatrix b)
  let phi : PureVector (Prod (Prod a c) b) := psi.reindex e
  have hCmat_unfold :
      partialTraceA (a := a) (b := c)
          (fun ac ac' =>
            ∑ j : b,
              rankOneMatrix psi.amp ((ac.1, j), ac.2) ((ac'.1, j), ac'.2)) =
        partialTraceA (a := Prod a b) (b := c) (rankOneMatrix psi.amp) := by
    simpa [State.marginalAC, State.marginalB, State.marginalAC_matrix,
      State.marginalB_matrix] using hCmat
  have hACB_matrix :
      Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalAC.marginalB.matrix p))
          (1 : CMatrix b) = KACB := by
    dsimp [KACB, T]
    rw [hCmat_unfold]
  have hACB_def :
      psi.mixedPetzSandwichedACBWeightedAmplitude alpha =
        Matrix.mulVec KACB phi.amp := by
    ext y
    change
      (Matrix.mulVec
        (Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalAC.marginalB.matrix p))
          (1 : CMatrix b))
        (psi.reindex e).amp) y =
      (Matrix.mulVec KACB phi.amp) y
    rw [hACB_matrix]
  have hKC_submatrix :
      KC.submatrix e.symm e.symm = KACB := by
    simpa [KC, KACB, T, e] using
      conditionalPetzRenyiABCToACB_submatrix_refC
        (a := a) (b := b) (c := c) T
  ext x
  rcases x with ⟨⟨i, k⟩, j⟩
  have hx := congrFun hmove ((i, j), k)
  have hleft :
      psi.mixedPetzSandwichedACBWeightedAmplitude alpha ((i, k), j) =
        (Matrix.kronecker (1 : CMatrix (Prod a b))
            (CFC.rpow psi.state.marginalB.matrix p)).mulVec psi.amp ((i, j), k) := by
    rw [hACB_def]
    change Matrix.mulVec KACB phi.amp ((i, k), j) =
      Matrix.mulVec KC psi.amp ((i, j), k)
    rw [← hKC_submatrix]
    simp [KC, T, phi, e, PureVector.reindex_amp,
      conditionalPetzRenyiABCToACBEquiv, Matrix.mulVec, dotProduct, Matrix.kronecker,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro _ _
    rw [Finset.sum_comm]
  have hab :
      psi.mixedPetzSandwichedABWeightedAmplitude alpha ((i, j), k) =
        (Matrix.kronecker
          (CFC.rpow psi.state.marginalAB.matrix p) (1 : CMatrix c)).mulVec
          psi.amp ((i, j), k) := by
    rfl
  rw [hleft, hab]
  exact hx.symm

/-- AC-side half of Tomamichel's Eq. `eq:marginals`: the common weighted
rank-one operator has AC marginal equal to the sandwiched-down reference inner. -/
theorem partialTraceB_rankOne_mixedPetzSandwichedACBWeightedAmplitude_eq_referenceInner
    (psi : PureVector (Prod (Prod a b) c))
    (hC : psi.state.marginalAC.marginalB.matrix.PosDef)
    {alpha beta : Real} (halpha_ne_zero : alpha ≠ 0)
    (hdual : alpha * beta = 1) :
    partialTraceB (a := Prod a c) (b := b)
        (rankOneMatrix (psi.mixedPetzSandwichedACBWeightedAmplitude alpha)) =
      State.sandwichedRenyiReferenceInner psi.state.marginalAC
        (State.identityTensorStateMatrix (a := a) psi.state.marginalAC.marginalB)
        beta := by
  let phi := psi.reindex (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))
  let tau := psi.state.marginalAC.marginalB
  let p : Real := (alpha - 1) / 2
  let W : CMatrix (Prod a c) :=
    Matrix.kronecker (1 : CMatrix a) (CFC.rpow tau.matrix p)
  have hp :
      (1 - beta) / (2 * beta) = p := by
    simpa [p] using
      State.mixedPetzSandwiched_sandwichedExponent_eq halpha_ne_zero hdual
  have hmarg :
      partialTraceB (a := Prod a c) (b := b) (rankOneMatrix phi.amp) =
        psi.state.marginalAC.matrix := by
    ext x y
    rcases x with ⟨i, k⟩
    rcases y with ⟨i', k'⟩
    simp [phi, State.marginalAC_matrix, partialTraceB,
      conditionalPetzRenyiABCToACBEquiv]
  have hWherm : Matrix.conjTranspose W = W := by
    have hWpsd : W.PosSemidef := by
      dsimp [W, tau, p]
      exact Matrix.PosSemidef.one.kronecker
        (cMatrix_rpow_posSemidef
          (A := psi.state.marginalAC.marginalB.matrix)
          (s := (alpha - 1) / 2) psi.state.marginalAC.marginalB.pos)
    exact hWpsd.isHermitian.eq
  change partialTraceB (a := Prod a c) (b := b)
      (rankOneMatrix (Matrix.mulVec (Matrix.kronecker W (1 : CMatrix b)) phi.amp)) =
    State.sandwichedRenyiReferenceInner psi.state.marginalAC
      (State.identityTensorStateMatrix (a := a) tau) beta
  rw [partialTraceB_rankOne_kron_left_mulVec_eq_source, hmarg, hWherm]
  unfold State.sandwichedRenyiReferenceInner
  change W * psi.state.marginalAC.matrix * W =
    CFC.rpow (State.identityTensorStateMatrix (a := a) tau)
        ((1 - beta) / (2 * beta)) *
      psi.state.marginalAC.matrix *
      CFC.rpow (State.identityTensorStateMatrix (a := a) tau)
        ((1 - beta) / (2 * beta))
  rw [hp]
  have href :
      CFC.rpow (State.identityTensorStateMatrix (a := a) tau) p = W := by
    simpa [W, tau, State.identityTensorStateMatrix] using
      cMatrix_rpow_kronecker_posDef
        (A := (1 : CMatrix a)) (B := tau.matrix) Matrix.PosDef.one hC p
  rw [href]

/-- B-side half of Tomamichel's Eq. `eq:marginals`: the same weighted rank-one
operator has B marginal equal to `Tr_A(rho_AB^alpha)`. -/
theorem partialTraceA_rankOne_mixedPetzSandwichedACBWeightedAmplitude_eq_petzTraceMatrix
    (psi : PureVector (Prod (Prod a b) c))
    {alpha : Real} (halpha_pos : 0 < alpha) :
    partialTraceA (a := Prod a c) (b := b)
        (rankOneMatrix (psi.mixedPetzSandwichedACBWeightedAmplitude alpha)) =
      psi.state.marginalAB.conditionalPetzRenyiUpTraceMatrix alpha := by
  let p : Real := (alpha - 1) / 2
  let Wab : CMatrix (Prod a b) := CFC.rpow psi.state.marginalAB.matrix p
  have hamp :=
    psi.mixedPetzSandwichedACBWeightedAmplitude_eq_reindex_ABWeightedAmplitude alpha
  rw [hamp]
  rw [partialTraceA_rankOne_ACB_reindex_eq_partialTraceA_partialTraceB_ABC]
  change partialTraceA (a := a) (b := b)
      (partialTraceB (a := Prod a b) (b := c)
        (rankOneMatrix
          (Matrix.mulVec (Matrix.kronecker Wab (1 : CMatrix c)) psi.amp))) =
    psi.state.marginalAB.conditionalPetzRenyiUpTraceMatrix alpha
  rw [partialTraceB_rankOne_kron_left_mulVec_eq_source]
  have hmargAB :
      partialTraceB (a := Prod a b) (b := c) (rankOneMatrix psi.amp) =
        psi.state.marginalAB.matrix := by
    ext x y
    rcases x with ⟨i, j⟩
    rcases y with ⟨i', j'⟩
    simp [State.marginalAB, State.marginalA, PureVector.state_matrix, partialTraceB]
  have hWherm : Matrix.conjTranspose Wab = Wab := by
    have hWpsd : Wab.PosSemidef := by
      dsimp [Wab, p]
      exact cMatrix_rpow_posSemidef
        (A := psi.state.marginalAB.matrix) (s := (alpha - 1) / 2)
        psi.state.marginalAB.pos
    exact hWpsd.isHermitian.eq
  rw [hmargAB, hWherm]
  dsimp [Wab, p, State.conditionalPetzRenyiUpTraceMatrix]
  exact congrArg (partialTraceA (a := a) (b := b))
    (State.cMatrix_rpow_half_sub_one_sandwich_eq_rpow
      (partialTraceB_posSemidef (rankOneMatrix_pos psi.amp)) halpha_pos)

/-- Trace-power form of the source marginal equivalence Eq. `eq:marginals`. -/
theorem mixedPetzSandwiched_closedTrace_eq_sandwichedDownTracePower
    (psi : PureVector (Prod (Prod a b) c))
    (hC : psi.state.marginalAC.marginalB.matrix.PosDef)
    {alpha beta : Real} (halpha_pos : 0 < alpha)
    (hbeta_pos : 0 < beta) (hdual : alpha * beta = 1) :
    psi.state.marginalAB.conditionalPetzRenyiUpClosedTrace alpha =
      psdTracePower
        (State.sandwichedRenyiReferenceInner psi.state.marginalAC
          (State.identityTensorStateMatrix (a := a) psi.state.marginalAC.marginalB)
          beta)
        (State.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAC
          (State.identityTensorStateMatrix_posSemidef
            (a := a) psi.state.marginalAC.marginalB)
          beta)
        beta := by
  have hB :=
    partialTraceA_rankOne_mixedPetzSandwichedACBWeightedAmplitude_eq_petzTraceMatrix
      (a := a) (b := b) (c := c) psi halpha_pos
  have hAC :=
    partialTraceB_rankOne_mixedPetzSandwichedACBWeightedAmplitude_eq_referenceInner
      (a := a) (b := b) (c := c) psi hC (ne_of_gt halpha_pos) hdual
  have hcomp :=
    psdTracePower_partialTraceB_rankOneMatrix_eq_partialTraceA_rankOneMatrix
      (r := Prod a c) (a := b)
      (psi.mixedPetzSandwichedACBWeightedAmplitude alpha) hbeta_pos
  have hbeta_eq : beta = alpha⁻¹ :=
    State.mixedPetzSandwiched_beta_eq_inv (ne_of_gt halpha_pos) hdual
  have hinv_eq : (1 / alpha : Real) = beta := by
    simpa [one_div] using hbeta_eq.symm
  rw [State.conditionalPetzRenyiUpClosedTrace_eq_psdTracePower]
  rw [hinv_eq]
  simpa [hB, hAC] using hcomp.symm

/-- Normalized non-endpoint mixed Petz/sandwiched conditional Renyi duality.

This is the current Lean realization of Tomamichel2015FiniteResources,
`cond.tex`, Proposition `pr:dual-both`, lines 408--440, under the local API's
finite non-endpoint and positive-definite sandwiched-reference hypotheses. -/
theorem conditionalPetzSandwichedRenyi_duality_source
    [Nonempty b]
    (psi : PureVector (Prod (Prod a b) c))
    (hAC : psi.state.marginalAC.matrix.PosDef)
    (hC : psi.state.marginalAC.marginalB.matrix.PosDef)
    {alpha beta : Real}
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
    rw [State.conditionalPetzRenyiUp_eq_alternative]
    rfl
  have hdown :
      psi.state.marginalAC.conditionalSandwichedRenyiDown
          hAC hC beta hbeta_pos hbeta_ne_one =
        (1 / (1 - beta)) *
          log2 (psdTracePower
            (State.sandwichedRenyiReferenceInner psi.state.marginalAC
              (State.identityTensorStateMatrix
                (a := a) psi.state.marginalAC.marginalB)
              beta)
            (State.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAC
              (State.identityTensorStateMatrix_posSemidef
                (a := a) psi.state.marginalAC.marginalB)
              beta)
            beta) := by
    rw [State.conditionalSandwichedRenyiDown_eq]
    rw [State.sandwichedRenyiReference_eq_log2_psdTracePower_inner]
    set L : Real :=
      log2 (psdTracePower
        (State.sandwichedRenyiReferenceInner psi.state.marginalAC
          (State.identityTensorStateMatrix
            (a := a) psi.state.marginalAC.marginalB)
          beta)
        (State.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAC
          (State.identityTensorStateMatrix_posSemidef
            (a := a) psi.state.marginalAC.marginalB)
          beta)
        beta)
    have hden : 1 - beta = -(beta - 1) := by ring
    rw [hden]
    have hone : 1 / -(beta - 1) = (-(beta - 1))⁻¹ := by
      exact one_div (-(beta - 1))
    rw [hone, inv_neg]
    ring
  rw [hpetz, hdown, htrace]
  let L : Real :=
    log2 (psdTracePower
      (State.sandwichedRenyiReferenceInner psi.state.marginalAC
        (State.identityTensorStateMatrix (a := a) psi.state.marginalAC.marginalB)
        beta)
      (State.sandwichedRenyiReferenceInner_posSemidef psi.state.marginalAC
        (State.identityTensorStateMatrix_posSemidef
          (a := a) psi.state.marginalAC.marginalB)
        beta)
      beta)
  change alpha / (1 - alpha) * L + 1 / (1 - beta) * L = 0
  have hcoeff :
      alpha / (1 - alpha) + 1 / (1 - beta) = 0 :=
    State.mixedPetzSandwiched_coeff_cancel
      (ne_of_gt halpha_pos) halpha_ne_one hdual
  calc
    alpha / (1 - alpha) * L + 1 / (1 - beta) * L =
        (alpha / (1 - alpha) + 1 / (1 - beta)) * L := by ring
    _ = 0 := by
      rw [hcoeff]
      ring

end PureVector

end

end QIT
