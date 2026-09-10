/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Renyi.ConditionalSandwichedRenyiDuality
public import QuantumLib.QIT.Information.Renyi.ConditionalPetzRenyi
public import QuantumLib.QIT.Information.Entropy.EntropyTensorPower
public import QuantumLib.QIT.OneShot.SmoothEndpoint

/-!
# Additivity of upward sandwiched conditional Renyi entropy

This module formalizes the tensor-product additivity corollary following
[Tomamichel2015FiniteResources, cond.tex:448-487].  The proof first restricts
the side-state optimization to product candidates.  The reverse inequality is
then obtained from pure-state conditional Renyi duality at conjugate orders.
The finite-order endpoint cases are handled separately at `alpha = 1/2` and
`alpha = 1`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

open Matrix

noncomputable section
universe u v w x
variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

open QIT

namespace QIT

/-- The finite conjugate order used in the source additivity proof. -/
def conditionalRenyiConjugateOrder (alpha : ℝ) : ℝ :=
  alpha / (2 * alpha - 1)

theorem conditionalRenyiConjugateOrder_conjugate
    {alpha : ℝ} (hhalf : 1 / 2 < alpha) :
    1 / conditionalRenyiConjugateOrder alpha + 1 / alpha = 2 := by
  have halpha : alpha ≠ 0 := by linarith
  have hdenom : 2 * alpha - 1 ≠ 0 := by linarith
  unfold conditionalRenyiConjugateOrder
  field_simp [halpha, hdenom]
  ring

theorem conditionalRenyiConjugateOrder_gt_one_of_lt_one
    {alpha : ℝ} (hhalf : 1 / 2 < alpha) (hone : alpha < 1) :
    1 < conditionalRenyiConjugateOrder alpha := by
  have hdenom : 0 < 2 * alpha - 1 := by linarith
  unfold conditionalRenyiConjugateOrder
  rw [lt_div_iff₀ hdenom]
  linarith

theorem conditionalRenyiConjugateOrder_half_lt_of_one_lt
    {alpha : ℝ} (hone : 1 < alpha) :
    1 / 2 < conditionalRenyiConjugateOrder alpha := by
  have hdenom : 0 < 2 * alpha - 1 := by linarith
  unfold conditionalRenyiConjugateOrder
  rw [lt_div_iff₀ hdenom]
  linarith

theorem conditionalRenyiConjugateOrder_lt_one_of_one_lt
    {alpha : ℝ} (hone : 1 < alpha) :
    conditionalRenyiConjugateOrder alpha < 1 := by
  have hdenom : 0 < 2 * alpha - 1 := by linarith
  unfold conditionalRenyiConjugateOrder
  rw [div_lt_one hdenom]
  linarith

private def conditionalRenyiTargetFirstCanonicalPurification
    (rho : MState (a × b)) :
    Ket ((a × b) × (a × b)) :=
  rho.canonicalPurification.reindex (Equiv.prodComm (a × b) (a × b))

private theorem conditionalRenyiTargetFirstCanonicalPurification_marginalAB
    (rho : MState (a × b)) :
    (conditionalRenyiTargetFirstCanonicalPurification rho).state.marginalAB = rho := by
  apply MState.ext
  ext x y
  have hpur := rho.canonicalPurification_purifies
  simpa [conditionalRenyiTargetFirstCanonicalPurification,
    MState.marginalAB_eq_traceRight, Ket.reindex_state,
    Matrix.traceLeft, Matrix.traceRight] using
      congrFun (congrFun hpur x) y

end QIT

namespace MState

/-- Regroup the product of states on `A x B` and `C x D` as a state on
`(A x C) x (B x D)`. -/
def conditionalRenyiGroupedProduct
    (rho : MState (a × b)) (tau : MState (c × d)) :
    MState ((a × c) × (b × d)) :=
  (rho.prod tau).reindex (Equiv.prodProdProdComm a b c d)

@[simp]
theorem conditionalRenyiGroupedProduct_matrix
    (rho : MState (a × b)) (tau : MState (c × d)) :
    (rho.conditionalRenyiGroupedProduct tau).m =
      (rho.m ⊗ₖ tau.m).submatrix
        (Equiv.prodProdProdComm a b c d).symm
        (Equiv.prodProdProdComm a b c d).symm := by
  rw [conditionalRenyiGroupedProduct, MState.reindex_matrix, MState.prod_m]

/-- The conditioning marginal of a grouped product is the product of the two
conditioning marginals. -/
theorem conditionalRenyiGroupedProduct_traceLeft
    (rho : MState (a × b)) (tau : MState (c × d)) :
    (rho.conditionalRenyiGroupedProduct tau).traceLeft =
      rho.traceLeft.prod tau.traceLeft := by
  apply MState.ext
  simp only [MState.traceLeft_m, conditionalRenyiGroupedProduct_matrix,
    MState.prod_m]
  ext x y
  rcases x with ⟨j, l⟩
  rcases y with ⟨j', l'⟩
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.kroneckerMap_apply,
    Equiv.prodProdProdComm, Fintype.sum_prod_type,
    Matrix.submatrix_apply]
  change (∑ i : a, ∑ k : c,
      rho.m (i, j) (i, j') * tau.m (k, l) (k, l')) =
    (∑ i : a, rho.m (i, j) (i, j')) *
      (∑ k : c, tau.m (k, l) (k, l'))
  calc
    _ = ∑ i : a, rho.m (i, j) (i, j') *
        (∑ k : c, tau.m (k, l) (k, l')) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = _ := by rw [Finset.sum_mul]

/-- Conditional von Neumann entropy is additive on grouped product states. -/
theorem conditionalEntropy_conditionalRenyiGroupedProduct
    (rho : MState (a × b)) (tau : MState (c × d)) :
    (rho.conditionalRenyiGroupedProduct tau).conditionalEntropy =
      rho.conditionalEntropy + tau.conditionalEntropy := by
  rw [conditionalEntropy_eq, conditionalRenyiGroupedProduct_traceLeft]
  change ((rho.prod tau).reindex
      (Equiv.prodProdProdComm a b c d)).vonNeumann -
    (rho.traceLeft.prod tau.traceLeft).vonNeumann = _
  rw [vonNeumann_reindex, vonNeumann_prod, vonNeumann_prod]
  rw [conditionalEntropy_eq, conditionalEntropy_eq]
  ring

/-- Unified finite-order upward sandwiched conditional Renyi entropy.

At order one this is conditional von Neumann entropy.  At order one half it
uses the conditional max-entropy endpoint, while all other positive orders use
the support-aware source quantity proved in the conditional-duality module. -/
def conditionalSandwichedRenyiUpFiniteOrder
    (rho : MState (a × b)) (alpha : ℝ) : ℝ :=
  if hOne : alpha = 1 then
    rho.conditionalEntropy
  else if _hHalf : alpha = (2 : ℝ)⁻¹ then
    rho.conditionalMaxEntropy
  else if hpos : 0 < alpha then
    rho.conditionalSandwichedRenyiUpSource alpha hpos hOne
  else
    0

@[simp]
theorem conditionalSandwichedRenyiUpFiniteOrder_one
    (rho : MState (a × b)) :
    rho.conditionalSandwichedRenyiUpFiniteOrder 1 = rho.conditionalEntropy := by
  simp [conditionalSandwichedRenyiUpFiniteOrder]

@[simp]
theorem conditionalSandwichedRenyiUpFiniteOrder_half
    (rho : MState (a × b)) :
    rho.conditionalSandwichedRenyiUpFiniteOrder (2 : ℝ)⁻¹ =
      rho.conditionalMaxEntropy := by
  norm_num [conditionalSandwichedRenyiUpFiniteOrder]

theorem conditionalSandwichedRenyiUpFiniteOrder_of_pos_ne_one_ne_half
    (rho : MState (a × b)) {alpha : ℝ}
    (hpos : 0 < alpha) (hone : alpha ≠ 1) (hhalf : alpha ≠ (2 : ℝ)⁻¹) :
    rho.conditionalSandwichedRenyiUpFiniteOrder alpha =
      rho.conditionalSandwichedRenyiUpSource alpha hpos hone := by
  rw [conditionalSandwichedRenyiUpFiniteOrder, dif_neg hone, dif_neg hhalf,
    dif_pos hpos]

theorem conditionalSandwichedRenyiUpFiniteOrder_prod_grouped_one
    (rho : MState (a × b)) (tau : MState (c × d)) :
    (rho.conditionalRenyiGroupedProduct tau).conditionalSandwichedRenyiUpFiniteOrder 1 =
      rho.conditionalSandwichedRenyiUpFiniteOrder 1 +
        tau.conditionalSandwichedRenyiUpFiniteOrder 1 := by
  rw [conditionalSandwichedRenyiUpFiniteOrder_one,
    conditionalSandwichedRenyiUpFiniteOrder_one,
    conditionalSandwichedRenyiUpFiniteOrder_one]
  exact conditionalEntropy_conditionalRenyiGroupedProduct rho tau

/-- The positive trace-power kernel underneath a source-shaped upward
sandwiched conditional Renyi candidate. -/
def conditionalSandwichedRenyiUpSourceTraceTerm
    (rho : MState (a × b)) (sigma : MState b) (alpha : ℝ) : ℝ :=
  psdTracePower
    (sandwichedRenyiReferenceInner rho
      (identityTensorStateMatrix (a := a) sigma) alpha)
    (sandwichedRenyiReferenceInner_posSemidef rho
      (identityTensorStateMatrix_posSemidef (a := a) sigma) alpha)
    alpha

theorem conditionalSandwichedRenyiUpSourceTraceTerm_pos_of_posDef
    (rho : MState (a × b)) (sigma : MState b) (hsigma : sigma.m.PosDef)
    (alpha : ℝ) :
    0 < rho.conditionalSandwichedRenyiUpSourceTraceTerm sigma alpha := by
  exact sandwichedRenyiReferenceInner_psdTracePower_pos_of_reference_posDef
    rho (identityTensorStateMatrix_posDef_of_posDef (a := a) sigma hsigma) alpha

/-- The source candidate is the logarithm of its positive trace-power
kernel. -/
theorem conditionalSandwichedRenyiUpSourceCandidate_eq_traceTerm
    (rho : MState (a × b)) (sigma : MState b) (hsigma : sigma.m.PosDef)
    (alpha : ℝ) (hpos : 0 < alpha) (hone : alpha ≠ 1) :
    rho.conditionalSandwichedRenyiUpSourceCandidate sigma hsigma alpha hpos hone =
      -(1 / (alpha - 1)) *
        log2 (rho.conditionalSandwichedRenyiUpSourceTraceTerm sigma alpha) := by
  rfl

/-- The sandwiched inner operator for a grouped product and a product side
state is the grouped Kronecker product of the two inner operators. -/
theorem sandwichedRenyiReferenceInner_conditionalRenyiGroupedProduct
    (rho : MState (a × b)) (sigma : MState b)
    (tau : MState (c × d)) (omega : MState d)
    (hsigma : sigma.m.PosDef) (homega : omega.m.PosDef)
    (alpha : ℝ) :
    sandwichedRenyiReferenceInner
        (rho.conditionalRenyiGroupedProduct tau)
        (identityTensorStateMatrix (a := a × c) (sigma.prod omega)) alpha =
      ((sandwichedRenyiReferenceInner rho
          (identityTensorStateMatrix (a := a) sigma) alpha) ⊗ₖ
        (sandwichedRenyiReferenceInner tau
          (identityTensorStateMatrix (a := c) omega) alpha)).submatrix
        (Equiv.prodProdProdComm a b c d).symm
        (Equiv.prodProdProdComm a b c d).symm := by
  let e := Equiv.prodProdProdComm a b c d
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let R1 : CMatrix (a × b) := identityTensorStateMatrix (a := a) sigma
  let R2 : CMatrix (c × d) := identityTensorStateMatrix (a := c) omega
  let C1 : CMatrix (a × b) := CFC.rpow R1 s
  let C2 : CMatrix (c × d) := CFC.rpow R2 s
  have hR1 : R1.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) sigma hsigma
  have hR2 : R2.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := c) omega homega
  have hpow :
      CFC.rpow (identityTensorStateMatrix (a := a × c) (sigma.prod omega)) s =
        (C1 ⊗ₖ C2).submatrix e.symm e.symm := by
    rw [identityTensorStateMatrix_prod_grouping]
    rw [cMatrix_rpow_submatrix_equiv_posDef
      (R1 ⊗ₖ R2) (hR1.kronecker hR2) e.symm s]
    rw [cMatrix_rpow_kronecker hR1.posSemidef hR2.posSemidef s]
  unfold sandwichedRenyiReferenceInner
  simp only [conditionalRenyiGroupedProduct_matrix]
  change
    CFC.rpow (identityTensorStateMatrix (a := a × c) (sigma.prod omega)) s *
          (rho.m ⊗ₖ tau.m).submatrix e.symm e.symm *
          CFC.rpow (identityTensorStateMatrix (a := a × c) (sigma.prod omega)) s =
      ((C1 * rho.m * C1) ⊗ₖ (C2 * tau.m * C2)).submatrix
        e.symm e.symm
  rw [hpow]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  apply congrArg (fun M : CMatrix ((a × b) × (c × d)) =>
    M.submatrix e.symm e.symm)
  calc
    (C1 ⊗ₖ C2) * (rho.m ⊗ₖ tau.m) *
          (C1 ⊗ₖ C2) =
        ((C1 * rho.m) ⊗ₖ (C2 * tau.m)) *
          (C1 ⊗ₖ C2) := by
      exact congrArg (fun M : CMatrix ((a × b) × (c × d)) =>
        M * (C1 ⊗ₖ C2))
        (Matrix.mul_kronecker_mul C1 rho.m C2 tau.m).symm
    _ = (C1 * rho.m * C1) ⊗ₖ (C2 * tau.m * C2) :=
      (Matrix.mul_kronecker_mul (C1 * rho.m) C1
        (C2 * tau.m) C2).symm

/-- The fixed-side source trace kernel is multiplicative on grouped product
states. -/
theorem conditionalSandwichedRenyiUpSourceTraceTerm_prod_grouped
    (rho : MState (a × b)) (sigma : MState b)
    (tau : MState (c × d)) (omega : MState d)
    (hsigma : sigma.m.PosDef) (homega : omega.m.PosDef)
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    (rho.conditionalRenyiGroupedProduct tau).conditionalSandwichedRenyiUpSourceTraceTerm
        (sigma.prod omega) alpha =
      rho.conditionalSandwichedRenyiUpSourceTraceTerm sigma alpha *
        tau.conditionalSandwichedRenyiUpSourceTraceTerm omega alpha := by
  let e := Equiv.prodProdProdComm a b c d
  let inner1 : CMatrix (a × b) :=
    sandwichedRenyiReferenceInner rho
      (identityTensorStateMatrix (a := a) sigma) alpha
  let inner2 : CMatrix (c × d) :=
    sandwichedRenyiReferenceInner tau
      (identityTensorStateMatrix (a := c) omega) alpha
  have hinner1 : inner1.PosSemidef :=
    sandwichedRenyiReferenceInner_posSemidef rho
      (identityTensorStateMatrix_posSemidef (a := a) sigma) alpha
  have hinner2 : inner2.PosSemidef :=
    sandwichedRenyiReferenceInner_posSemidef tau
      (identityTensorStateMatrix_posSemidef (a := c) omega) alpha
  have hinner :
      sandwichedRenyiReferenceInner
          (rho.conditionalRenyiGroupedProduct tau)
          (identityTensorStateMatrix (a := a × c) (sigma.prod omega)) alpha =
        (inner1 ⊗ₖ inner2).submatrix e.symm e.symm := by
    simpa [e, inner1, inner2] using
      sandwichedRenyiReferenceInner_conditionalRenyiGroupedProduct
        rho sigma tau omega hsigma homega alpha
  unfold conditionalSandwichedRenyiUpSourceTraceTerm psdTracePower
  rw [hinner]
  rw [cMatrix_rpow_submatrix_equiv_nonneg
    (inner1 ⊗ₖ inner2) (hinner1.kronecker hinner2) e.symm halpha]
  rw [Matrix.trace_submatrix _ e.symm]
  exact psdTracePower_kronecker hinner1 hinner2

/-- Fixed full-rank product side states make the source entropy candidate
additive. -/
theorem conditionalSandwichedRenyiUpSourceCandidate_prod_grouped
    (rho : MState (a × b)) (sigma : MState b)
    (tau : MState (c × d)) (omega : MState d)
    (hsigma : sigma.m.PosDef) (homega : omega.m.PosDef)
    {alpha : ℝ} (halpha : 0 < alpha) (hone : alpha ≠ 1) :
    (rho.conditionalRenyiGroupedProduct tau).conditionalSandwichedRenyiUpSourceCandidate
        (sigma.prod omega) (MState.PosDef.kron hsigma homega) alpha halpha hone =
      rho.conditionalSandwichedRenyiUpSourceCandidate sigma hsigma alpha halpha hone +
        tau.conditionalSandwichedRenyiUpSourceCandidate omega homega alpha halpha hone := by
  rw [conditionalSandwichedRenyiUpSourceCandidate_eq_traceTerm,
    conditionalSandwichedRenyiUpSourceCandidate_eq_traceTerm,
    conditionalSandwichedRenyiUpSourceCandidate_eq_traceTerm]
  rw [conditionalSandwichedRenyiUpSourceTraceTerm_prod_grouped
    rho sigma tau omega hsigma homega halpha.le]
  rw [log2_mul
    (ne_of_gt (rho.conditionalSandwichedRenyiUpSourceTraceTerm_pos_of_posDef
      sigma hsigma alpha))
    (ne_of_gt (tau.conditionalSandwichedRenyiUpSourceTraceTerm_pos_of_posDef
      omega homega alpha))]
  ring

/-- In the high-order range, the source candidate family is bounded above.

The proof uses a target-first canonical purification and the positive common
Schatten extremum from pure-state duality; no positive-definiteness condition
is placed on the input state. -/
theorem conditionalSandwichedRenyiUpSourceValueSet_bddAbove_of_one_lt
    (rho : MState (a × b)) {alpha : ℝ} (halpha : 1 < alpha) :
    BddAbove (rho.conditionalSandwichedRenyiUpSourceValueSet alpha
      (lt_trans zero_lt_one halpha) (ne_of_gt halpha)) := by
  let : Nonempty a := by
    rcases rho.nonempty with ⟨i, _⟩
    exact ⟨i⟩
  let : Nonempty b := by
    rcases rho.nonempty with ⟨_, j⟩
    exact ⟨j⟩
  let psi : Ket ((a × b) × (a × b)) :=
    conditionalRenyiTargetFirstCanonicalPurification rho
  let beta : ℝ := conditionalRenyiConjugateOrder alpha
  have hbeta_half : 1 / 2 < beta :=
    conditionalRenyiConjugateOrder_half_lt_of_one_lt halpha
  have hbeta_one : beta < 1 :=
    conditionalRenyiConjugateOrder_lt_one_of_one_lt halpha
  have hconj : 1 / alpha + 1 / beta = 2 := by
    simpa [beta, add_comm] using conditionalRenyiConjugateOrder_conjugate
      (lt_trans (by norm_num) halpha)
  let p : ℝ := Ket.upwardRenyiDualityParameter alpha
  let high : {sigma : MState b // sigma.m.PosDef} → ℝ := fun sigma =>
    psi.upwardRenyiDualityHighNorm sigma.1 (SchattenOrder.ofOneLt halpha)
  have hp : 0 < p := Ket.upwardRenyiDualityParameter_pos halpha
  have hhigh_bdd : BddBelow (Set.range high) := by
    refine ⟨0, ?_⟩
    rintro x ⟨sigma, rfl⟩
    exact (psi.upwardRenyiDualityHighNorm_pos sigma.1 sigma.2 halpha).le
  have hinf_pos : 0 < sInf (Set.range high) :=
    psi.upwardRenyiDuality_commonSchattenExtremum_pos halpha hbeta_half hbeta_one hconj
  refine ⟨-(1 / p) * log2 (sInf (Set.range high)), ?_⟩
  intro x hx
  rcases hx with ⟨sigma, hsigma, rfl⟩
  have hcandidate :=
    psi.upwardRenyiDualityABSourceCandidate_eq_highNormLog
      sigma hsigma halpha
  have hpsi : psi.state.marginalAB = rho := by
    simpa [psi] using conditionalRenyiTargetFirstCanonicalPurification_marginalAB rho
  rw [hpsi] at hcandidate
  rw [hcandidate]
  have hinf_le : sInf (Set.range high) ≤ high ⟨sigma, hsigma⟩ :=
    csInf_le hhigh_bdd ⟨⟨sigma, hsigma⟩, rfl⟩
  have hlog : log2 (sInf (Set.range high)) ≤ log2 (high ⟨sigma, hsigma⟩) :=
    log2_mono_of_pos hinf_pos hinf_le
  have hlog' : log2 (sInf (Set.range high)) ≤
      log2 (psi.upwardRenyiDualityHighNorm sigma
        (SchattenOrder.ofOneLt halpha)) := by
    simpa only [high] using hlog
  have hcoeff : -(1 / p) ≤ 0 :=
    neg_nonpos.mpr (one_div_nonneg.mpr hp.le)
  exact mul_le_mul_of_nonpos_left hlog' hcoeff

/-- In the low-order range above one half, the source candidate family is
bounded above by the reverse-Holder common Schatten bracket of a canonical
purification. -/
theorem conditionalSandwichedRenyiUpSourceValueSet_bddAbove_of_half_lt_lt_one
    (rho : MState (a × b)) {alpha : ℝ}
    (hhalf : 1 / 2 < alpha) (hone : alpha < 1) :
    BddAbove (rho.conditionalSandwichedRenyiUpSourceValueSet alpha
      (lt_trans (by norm_num) hhalf) (ne_of_lt hone)) := by
  let : Nonempty a := by
    rcases rho.nonempty with ⟨i, _⟩
    exact ⟨i⟩
  let : Nonempty b := by
    rcases rho.nonempty with ⟨_, j⟩
    exact ⟨j⟩
  let r := (a × b)
  let psi0 : Ket ((a × b) × r) :=
    conditionalRenyiTargetFirstCanonicalPurification rho
  let psi : Ket ((a × r) × b) :=
    psi0.reindex (prodABCToACBEquiv a b r)
  let gamma : ℝ := conditionalRenyiConjugateOrder alpha
  have hgamma : 1 < gamma :=
    conditionalRenyiConjugateOrder_gt_one_of_lt_one hhalf hone
  have hconj : 1 / gamma + 1 / alpha = 2 := by
    simpa [gamma] using conditionalRenyiConjugateOrder_conjugate hhalf
  let p : ℝ := Ket.upwardRenyiDualityParameter gamma
  let low : MState b → ℝ := fun omega =>
    psi.upwardRenyiDualityLowNorm omega gamma
      ⟨alpha, lt_trans (by norm_num) hhalf⟩
  have hp : 0 < p := Ket.upwardRenyiDualityParameter_pos hgamma
  have hlow_bdd : BddAbove (Set.range low) := by
    simpa [low] using psi.upwardRenyiDualityLowNorm_range_bddAbove
      hgamma hhalf hone hconj
  rcases hlow_bdd with ⟨upper, hupper⟩
  let omega0 : MState b := (MState.uniform : MState b)
  have homega0 : omega0.m.PosDef :=
    MState.uniform_posDef
  have hlow0 : 0 < low omega0 := by
    simpa [low] using psi.upwardRenyiDualityLowNorm_pos_of_posDef
      omega0 homega0 hgamma hhalf hone hconj
  have hupper_pos : 0 < upper :=
    hlow0.trans_le (hupper ⟨omega0, rfl⟩)
  refine ⟨(1 / p) * log2 upper, ?_⟩
  intro x hx
  rcases hx with ⟨omega, homega, rfl⟩
  have hcandidate :=
    psi.upwardRenyiDualityACSourceCandidate_eq_lowNormLog
      omega homega hgamma hhalf hone hconj
  have hpsiAC : psi.state.marginalAC = rho := by
    calc
      psi.state.marginalAC = psi0.state.marginalAB := by
        simpa [psi] using Ket.prodABCToACB_marginalAC psi0
      _ = rho := by
        simpa [psi0] using conditionalRenyiTargetFirstCanonicalPurification_marginalAB rho
  rw [hpsiAC] at hcandidate
  rw [hcandidate]
  have hlow_pos : 0 < low omega := by
    simpa [low] using psi.upwardRenyiDualityLowNorm_pos_of_posDef
      omega homega hgamma hhalf hone hconj
  have hlow_le : low omega ≤ upper := hupper ⟨omega, rfl⟩
  have hlog : log2 (low omega) ≤ log2 upper :=
    log2_mono_of_pos hlow_pos hlow_le
  have hlog' :
      log2 (psi.upwardRenyiDualityLowNorm omega gamma
        ⟨alpha, lt_trans (by norm_num) hhalf⟩) ≤ log2 upper := by
    simpa only [low] using hlog
  have hcoeff : 0 ≤ 1 / p := by positivity
  exact mul_le_mul_of_nonneg_left hlog' hcoeff

theorem conditionalSandwichedRenyiUpSourceValueSet_nonempty
    [Nonempty b] (rho : MState (a × b)) (alpha : ℝ)
    (hpos : 0 < alpha) (hone : alpha ≠ 1) :
    (rho.conditionalSandwichedRenyiUpSourceValueSet alpha hpos hone).Nonempty := by
  let sigma : MState b := (MState.uniform : MState b)
  have hsigma : sigma.m.PosDef := MState.uniform_posDef
  exact ⟨rho.conditionalSandwichedRenyiUpSourceCandidate sigma hsigma alpha hpos hone,
    sigma, hsigma, rfl⟩

theorem conditionalSandwichedRenyiUpSourceValueSet_bddAbove
    (rho : MState (a × b)) {alpha : ℝ}
    (hhalf : 1 / 2 < alpha) (hone : alpha ≠ 1) :
    BddAbove (rho.conditionalSandwichedRenyiUpSourceValueSet alpha
      (lt_trans (by norm_num) hhalf) hone) := by
  rcases lt_or_gt_of_ne hone with halpha | halpha
  · exact rho.conditionalSandwichedRenyiUpSourceValueSet_bddAbove_of_half_lt_lt_one
      hhalf halpha
  · exact rho.conditionalSandwichedRenyiUpSourceValueSet_bddAbove_of_one_lt halpha

/-- Product side-state candidates give the direct inequality in Tomamichel's
conditional Renyi additivity proof. -/
theorem conditionalSandwichedRenyiUpSource_prod_grouped_ge_add
    (rho : MState (a × b)) (tau : MState (c × d))
    {alpha : ℝ} (hhalf : 1 / 2 < alpha) (hone : alpha ≠ 1) :
    rho.conditionalSandwichedRenyiUpSource alpha
          (lt_trans (by norm_num) hhalf) hone +
        tau.conditionalSandwichedRenyiUpSource alpha
          (lt_trans (by norm_num) hhalf) hone ≤
      (rho.conditionalRenyiGroupedProduct tau).conditionalSandwichedRenyiUpSource
        alpha (lt_trans (by norm_num) hhalf) hone := by
  let : Nonempty a := by
    rcases rho.nonempty with ⟨i, _⟩
    exact ⟨i⟩
  let : Nonempty b := by
    rcases rho.nonempty with ⟨_, j⟩
    exact ⟨j⟩
  let : Nonempty c := by
    rcases tau.nonempty with ⟨i, _⟩
    exact ⟨i⟩
  let : Nonempty d := by
    rcases tau.nonempty with ⟨_, j⟩
    exact ⟨j⟩
  let hpos : 0 < alpha := lt_trans (by norm_num) hhalf
  let S1 := rho.conditionalSandwichedRenyiUpSourceValueSet alpha hpos hone
  let S2 := tau.conditionalSandwichedRenyiUpSourceValueSet alpha hpos hone
  let SP := (rho.conditionalRenyiGroupedProduct tau)
    |>.conditionalSandwichedRenyiUpSourceValueSet alpha hpos hone
  have hS1_nonempty : S1.Nonempty :=
    rho.conditionalSandwichedRenyiUpSourceValueSet_nonempty alpha hpos hone
  have hS2_nonempty : S2.Nonempty :=
    tau.conditionalSandwichedRenyiUpSourceValueSet_nonempty alpha hpos hone
  have hSP_bdd : BddAbove SP := by
    simpa [SP, hpos] using
      (rho.conditionalRenyiGroupedProduct tau)
        |>.conditionalSandwichedRenyiUpSourceValueSet_bddAbove hhalf hone
  have hcandidate_le : ∀ x ∈ S1, ∀ y ∈ S2, x + y ≤ sSup SP := by
    intro x hx y hy
    rcases hx with ⟨sigma, hsigma, rfl⟩
    rcases hy with ⟨omega, homega, rfl⟩
    refine le_csSup hSP_bdd ?_
    exact ⟨sigma.prod omega, MState.PosDef.kron hsigma homega,
      (conditionalSandwichedRenyiUpSourceCandidate_prod_grouped
        rho sigma tau omega hsigma homega hpos hone).symm⟩
  unfold conditionalSandwichedRenyiUpSource
  change sSup S1 + sSup S2 ≤ sSup SP
  have houter : sSup S1 ≤ sSup SP - sSup S2 := by
    refine csSup_le hS1_nonempty ?_
    intro x hx
    have hinner : sSup S2 ≤ sSup SP - x := by
      refine csSup_le hS2_nonempty ?_
      intro y hy
      have hxy := hcandidate_le x hx y hy
      linarith
    linarith
  linarith

end MState

namespace Ket

private def conditionalRenyiGroupedProductPurification
    {r : Type*} {s : Type*} [Fintype r] [DecidableEq r]
    [Fintype s] [DecidableEq s]
    (psi : Ket ((a × b) × r))
    (phi : Ket ((c × d) × s)) :
    Ket (((a × c) × (b × d)) × (r × s)) :=
  (psi.prod phi).reindex prodTripartiteZipEquiv

private theorem conditionalRenyiGroupedProductPurification_marginalAB
    {r : Type*} {s : Type*} [Fintype r] [DecidableEq r]
    [Fintype s] [DecidableEq s]
    (psi : Ket ((a × b) × r))
    (phi : Ket ((c × d) × s)) :
    (conditionalRenyiGroupedProductPurification psi phi).state.marginalAB =
      psi.state.marginalAB.conditionalRenyiGroupedProduct phi.state.marginalAB := by
  apply MState.ext
  ext x y
  rcases x with ⟨⟨i, k⟩, ⟨j, l⟩⟩
  rcases y with ⟨⟨i', k'⟩, ⟨j', l'⟩⟩
  simp [conditionalRenyiGroupedProductPurification,
    prodTripartiteZipEquiv,
    Ket.reindex_state, MState.conditionalRenyiGroupedProduct,
    Equiv.prodProdProdComm, MState.marginalAB,
    Matrix.traceRight, Matrix.kroneckerMap_apply,
    Ket.state_matrix, rankOneMatrix_apply, Fintype.sum_prod_type, mul_assoc]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

private theorem conditionalRenyiGroupedProductPurification_marginalAC
    {r : Type*} {s : Type*} [Fintype r] [DecidableEq r]
    [Fintype s] [DecidableEq s]
    (psi : Ket ((a × b) × r))
    (phi : Ket ((c × d) × s)) :
    (conditionalRenyiGroupedProductPurification psi phi).state.marginalAC =
      psi.state.marginalAC.conditionalRenyiGroupedProduct phi.state.marginalAC := by
  apply MState.ext
  ext x y
  rcases x with ⟨⟨i, k⟩, ⟨r1, s1⟩⟩
  rcases y with ⟨⟨i', k'⟩, ⟨r1', s1'⟩⟩
  simp [conditionalRenyiGroupedProductPurification,
    prodTripartiteZipEquiv,
    Ket.reindex_state, MState.conditionalRenyiGroupedProduct,
    Equiv.prodProdProdComm, MState.marginalAC_matrix,
    Matrix.kroneckerMap_apply,
    Ket.state_matrix, rankOneMatrix_apply, Fintype.sum_prod_type, mul_assoc]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

end Ket

namespace MState

/-- The reverse product inequality in the high-order range, obtained exactly
as in Tomamichel's source proof: apply the direct product inequality at the
conjugate low order to complementary marginals, then use pure-state duality. -/
theorem conditionalSandwichedRenyiUpSource_prod_grouped_le_add_of_one_lt
    (rho : MState (a × b)) (tau : MState (c × d))
    {alpha : ℝ} (halpha : 1 < alpha) :
    (rho.conditionalRenyiGroupedProduct tau).conditionalSandwichedRenyiUpSource alpha
        (lt_trans zero_lt_one halpha) (ne_of_gt halpha) ≤
      rho.conditionalSandwichedRenyiUpSource alpha
          (lt_trans zero_lt_one halpha) (ne_of_gt halpha) +
        tau.conditionalSandwichedRenyiUpSource alpha
          (lt_trans zero_lt_one halpha) (ne_of_gt halpha) := by
  let : Nonempty a := by
    rcases rho.nonempty with ⟨i, _⟩
    exact ⟨i⟩
  let : Nonempty b := by
    rcases rho.nonempty with ⟨_, j⟩
    exact ⟨j⟩
  let : Nonempty c := by
    rcases tau.nonempty with ⟨k, _⟩
    exact ⟨k⟩
  let : Nonempty d := by
    rcases tau.nonempty with ⟨_, l⟩
    exact ⟨l⟩
  let psi := conditionalRenyiTargetFirstCanonicalPurification rho
  let phi := conditionalRenyiTargetFirstCanonicalPurification tau
  let Psi := Ket.conditionalRenyiGroupedProductPurification psi phi
  let beta := conditionalRenyiConjugateOrder alpha
  have hbeta_half : 1 / 2 < beta :=
    conditionalRenyiConjugateOrder_half_lt_of_one_lt halpha
  have hbeta_one : beta < 1 :=
    conditionalRenyiConjugateOrder_lt_one_of_one_lt halpha
  have hbeta_pos : 0 < beta := lt_trans (by norm_num) hbeta_half
  have hbeta_ne_one : beta ≠ 1 := ne_of_lt hbeta_one
  have hconj : 1 / alpha + 1 / beta = 2 := by
    simpa [beta, add_comm] using conditionalRenyiConjugateOrder_conjugate
      (lt_trans (by norm_num) halpha)
  have hPsiAB : Psi.state.marginalAB = rho.conditionalRenyiGroupedProduct tau := by
    rw [Ket.conditionalRenyiGroupedProductPurification_marginalAB]
    rw [conditionalRenyiTargetFirstCanonicalPurification_marginalAB,
      conditionalRenyiTargetFirstCanonicalPurification_marginalAB]
  have hPsiAC : Psi.state.marginalAC =
      psi.state.marginalAC.conditionalRenyiGroupedProduct phi.state.marginalAC :=
    Ket.conditionalRenyiGroupedProductPurification_marginalAC psi phi
  have hdirect := conditionalSandwichedRenyiUpSource_prod_grouped_ge_add
    psi.state.marginalAC phi.state.marginalAC hbeta_half hbeta_ne_one
  have hdualPsi := Psi.conditionalSandwichedRenyiUpSource_duality
    halpha hbeta_half hbeta_one hconj
  have hdualPsiLeft := psi.conditionalSandwichedRenyiUpSource_duality
    halpha hbeta_half hbeta_one hconj
  have hdualPsiRight := phi.conditionalSandwichedRenyiUpSource_duality
    halpha hbeta_half hbeta_one hconj
  rw [hPsiAB, hPsiAC] at hdualPsi
  rw [conditionalRenyiTargetFirstCanonicalPurification_marginalAB] at hdualPsiLeft
  rw [conditionalRenyiTargetFirstCanonicalPurification_marginalAB] at hdualPsiRight
  linarith

/-- The reverse product inequality in the low-order range.  The conditioning
and purifying systems are exchanged, so that duality pairs the requested low
order with a high conjugate order on the complementary marginals. -/
theorem conditionalSandwichedRenyiUpSource_prod_grouped_le_add_of_half_lt_lt_one
    (rho : MState (a × b)) (tau : MState (c × d))
    {alpha : ℝ} (hhalf : 1 / 2 < alpha) (hone : alpha < 1) :
    (rho.conditionalRenyiGroupedProduct tau).conditionalSandwichedRenyiUpSource alpha
        (lt_trans (by norm_num) hhalf) (ne_of_lt hone) ≤
      rho.conditionalSandwichedRenyiUpSource alpha
          (lt_trans (by norm_num) hhalf) (ne_of_lt hone) +
        tau.conditionalSandwichedRenyiUpSource alpha
          (lt_trans (by norm_num) hhalf) (ne_of_lt hone) := by
  let : Nonempty a := by
    rcases rho.nonempty with ⟨i, _⟩
    exact ⟨i⟩
  let : Nonempty b := by
    rcases rho.nonempty with ⟨_, j⟩
    exact ⟨j⟩
  let : Nonempty c := by
    rcases tau.nonempty with ⟨k, _⟩
    exact ⟨k⟩
  let : Nonempty d := by
    rcases tau.nonempty with ⟨_, l⟩
    exact ⟨l⟩
  let psi := conditionalRenyiTargetFirstCanonicalPurification rho
  let phi := conditionalRenyiTargetFirstCanonicalPurification tau
  let Psi := Ket.conditionalRenyiGroupedProductPurification psi phi
  let psiSwap := psi.reindex
    (prodABCToACBEquiv a b (a × b))
  let phiSwap := phi.reindex
    (prodABCToACBEquiv c d (c × d))
  let PsiSwap := Psi.reindex
    (prodABCToACBEquiv
      (a × c) (b × d) ((a × b) × (c × d)))
  let gamma := conditionalRenyiConjugateOrder alpha
  have hgamma : 1 < gamma :=
    conditionalRenyiConjugateOrder_gt_one_of_lt_one hhalf hone
  have hconj : 1 / gamma + 1 / alpha = 2 := by
    simpa [gamma] using conditionalRenyiConjugateOrder_conjugate hhalf
  have hPsiAB : Psi.state.marginalAB = rho.conditionalRenyiGroupedProduct tau := by
    rw [Ket.conditionalRenyiGroupedProductPurification_marginalAB]
    rw [conditionalRenyiTargetFirstCanonicalPurification_marginalAB,
      conditionalRenyiTargetFirstCanonicalPurification_marginalAB]
  have hPsiAC : Psi.state.marginalAC =
      psi.state.marginalAC.conditionalRenyiGroupedProduct phi.state.marginalAC :=
    Ket.conditionalRenyiGroupedProductPurification_marginalAC psi phi
  have hdirect := conditionalSandwichedRenyiUpSource_prod_grouped_ge_add
    psi.state.marginalAC phi.state.marginalAC (lt_trans (by norm_num) hgamma)
      (ne_of_gt hgamma)
  have hdualPsi := PsiSwap.conditionalSandwichedRenyiUpSource_duality
    hgamma hhalf hone hconj
  have hdualPsiLeft := psiSwap.conditionalSandwichedRenyiUpSource_duality
    hgamma hhalf hone hconj
  have hdualPsiRight := phiSwap.conditionalSandwichedRenyiUpSource_duality
    hgamma hhalf hone hconj
  rw [Ket.prodABCToACB_marginalAB,
    Ket.prodABCToACB_marginalAC, hPsiAC, hPsiAB] at hdualPsi
  rw [Ket.prodABCToACB_marginalAB,
    Ket.prodABCToACB_marginalAC,
    conditionalRenyiTargetFirstCanonicalPurification_marginalAB] at hdualPsiLeft
  rw [Ket.prodABCToACB_marginalAB,
    Ket.prodABCToACB_marginalAC,
    conditionalRenyiTargetFirstCanonicalPurification_marginalAB] at hdualPsiRight
  linarith

/-- Upward sandwiched conditional Renyi entropy is additive at every interior
finite order above one half other than one. -/
theorem conditionalSandwichedRenyiUpSource_prod_grouped
    (rho : MState (a × b)) (tau : MState (c × d))
    {alpha : ℝ} (hhalf : 1 / 2 < alpha) (hone : alpha ≠ 1) :
    (rho.conditionalRenyiGroupedProduct tau).conditionalSandwichedRenyiUpSource alpha
        (lt_trans (by norm_num) hhalf) hone =
      rho.conditionalSandwichedRenyiUpSource alpha
          (lt_trans (by norm_num) hhalf) hone +
        tau.conditionalSandwichedRenyiUpSource alpha
          (lt_trans (by norm_num) hhalf) hone := by
  apply le_antisymm
  · rcases lt_or_gt_of_ne hone with halpha | halpha
    · exact conditionalSandwichedRenyiUpSource_prod_grouped_le_add_of_half_lt_lt_one
        rho tau hhalf halpha
    · exact conditionalSandwichedRenyiUpSource_prod_grouped_le_add_of_one_lt
        rho tau halpha
  · exact conditionalSandwichedRenyiUpSource_prod_grouped_ge_add rho tau hhalf hone

/-- The unified finite-order quantity is additive at every interior order
above one half other than one. -/
theorem conditionalSandwichedRenyiUpFiniteOrder_prod_grouped_of_half_lt_ne_one
    (rho : MState (a × b)) (tau : MState (c × d))
    {alpha : ℝ} (hhalf : 1 / 2 < alpha) (hone : alpha ≠ 1) :
    (rho.conditionalRenyiGroupedProduct tau).conditionalSandwichedRenyiUpFiniteOrder alpha =
      rho.conditionalSandwichedRenyiUpFiniteOrder alpha +
        tau.conditionalSandwichedRenyiUpFiniteOrder alpha := by
  have hpos : 0 < alpha := lt_trans (by norm_num) hhalf
  have hneHalf : alpha ≠ (2 : ℝ)⁻¹ := by
    intro h
    norm_num at h
    linarith
  rw [conditionalSandwichedRenyiUpFiniteOrder_of_pos_ne_one_ne_half _ hpos hone hneHalf,
    conditionalSandwichedRenyiUpFiniteOrder_of_pos_ne_one_ne_half _ hpos hone hneHalf,
    conditionalSandwichedRenyiUpFiniteOrder_of_pos_ne_one_ne_half _ hpos hone hneHalf]
  exact conditionalSandwichedRenyiUpSource_prod_grouped rho tau hhalf hone

/-- Product side operators remain feasible for the grouped product
conditional-min SDP. -/
theorem ConditionalMinEntropyScaleFeasible.prod_grouped
    {rho : MState (a × b)} {tau : MState (c × d)}
    {T : CMatrix b} {U : CMatrix d}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) rho T)
    (hU : ConditionalMinEntropyScaleFeasible (a := c) tau U) :
    ConditionalMinEntropyScaleFeasible (a := a × c)
      (rho.conditionalRenyiGroupedProduct tau) (T ⊗ₖ U) := by
  constructor
  · exact hT.1.kronecker hU.1
  · let e := Equiv.prodProdProdComm a b c d
    let A : CMatrix (a × b) := (1 : CMatrix a) ⊗ₖ T
    let B : CMatrix (c × d) := (1 : CMatrix c) ⊗ₖ U
    have hA : A.PosSemidef := Matrix.PosSemidef.one.kronecker hT.1
    have hB : B.PosSemidef := Matrix.PosSemidef.one.kronecker hU.1
    have hdiffA : (A - rho.m).PosSemidef := hT.2
    have hdiffB : (B - tau.m).PosSemidef := hU.2
    have hraw :
        (A ⊗ₖ B - rho.m ⊗ₖ tau.m).PosSemidef := by
      have hsum := (hdiffA.kronecker hB).add (rho.psd.kronecker hdiffB)
      have heq : A ⊗ₖ B - rho.m ⊗ₖ tau.m =
          (A - rho.m) ⊗ₖ B +
            rho.m ⊗ₖ (B - tau.m) := by
        ext x y
        simp [A, B, Matrix.kroneckerMap_apply]
        ring
      rw [heq]
      exact hsum
    change ((1 : CMatrix (a × c)) ⊗ₖ (T ⊗ₖ U) -
      (rho.conditionalRenyiGroupedProduct tau).m).PosSemidef
    convert hraw.submatrix e.symm using 1
    ext x y
    rcases x with ⟨⟨i, k⟩, ⟨j, l⟩⟩
    rcases y with ⟨⟨i', k'⟩, ⟨j', l'⟩⟩
    simp [e, A, B, Equiv.prodProdProdComm,
      conditionalRenyiGroupedProduct_matrix, Matrix.kroneckerMap_apply]
    by_cases hi : i = i' <;> by_cases hk : k = k' <;>
      simp [Matrix.one_apply, hi, hk]

omit [DecidableEq b] [DecidableEq d] in
private theorem trace_kronecker_re_of_posSemidef
    {T : CMatrix b} {U : CMatrix d} (hT : T.PosSemidef) (hU : U.PosSemidef) :
    (T ⊗ₖ U).trace.re = T.trace.re * U.trace.re := by
  have htrace := congrArg Complex.re (Matrix.trace_kronecker T U)
  have hTim : T.trace.im = 0 := (Matrix.PosSemidef.trace_nonneg hT).2.symm
  have hUim : U.trace.im = 0 := (Matrix.PosSemidef.trace_nonneg hU).2.symm
  rw [Complex.mul_re, hTim, hUim] at htrace
  norm_num at htrace
  exact htrace

private theorem conditionalMinEntropyScale_eq_iInf_feasible
    [Nonempty b] (rho : MState (a × b)) :
    rho.conditionalMinEntropyScale (a := a) =
      ⨅ T : {T : CMatrix b // ConditionalMinEntropyScaleFeasible (a := a) rho T},
        T.1.trace.re := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet, ← sInf_range]
  congr 1
  ext x
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact ⟨⟨T, hT⟩, rfl⟩
  · rintro ⟨T, rfl⟩
    exact ⟨T.1, T.2, rfl⟩

/-- Regroup the Kronecker product of two endpoint dual effects. -/
def conditionalMinEntropyDualEffectGroupedProduct
    (M : CMatrix (a × b)) (N : CMatrix (c × d)) :
    CMatrix ((a × c) × (b × d)) :=
  (M ⊗ₖ N).submatrix
    (Equiv.prodProdProdComm a b c d).symm
    (Equiv.prodProdProdComm a b c d).symm

omit [DecidableEq a] [Fintype b] [DecidableEq b] [DecidableEq c]
    [Fintype d] [DecidableEq d] in
private theorem traceLeft_conditionalMinEntropyDualEffectGroupedProduct
    (M : CMatrix (a × b)) (N : CMatrix (c × d)) :
    Matrix.traceLeft
        (conditionalMinEntropyDualEffectGroupedProduct M N) =
      (Matrix.traceLeft M) ⊗ₖ
        (Matrix.traceLeft N) := by
  ext x y
  rcases x with ⟨j, l⟩
  rcases y with ⟨j', l'⟩
  simp [conditionalMinEntropyDualEffectGroupedProduct, Matrix.traceLeft,
    Equiv.prodProdProdComm, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]

omit [DecidableEq a] [DecidableEq c] in
/-- Product dual effects remain feasible for the grouped product
conditional-min SDP. -/
theorem ConditionalMinEntropyDualEffectFeasible.prod_grouped
    {M : CMatrix (a × b)} {N : CMatrix (c × d)}
    (hM : ConditionalMinEntropyDualEffectFeasible (a := a) M)
    (hN : ConditionalMinEntropyDualEffectFeasible (a := c) N) :
    ConditionalMinEntropyDualEffectFeasible (a := a × c)
      (conditionalMinEntropyDualEffectGroupedProduct M N) := by
  constructor
  · exact (hM.1.kronecker hN.1).submatrix
      (Equiv.prodProdProdComm a b c d).symm
  · rw [traceLeft_conditionalMinEntropyDualEffectGroupedProduct]
    let P : CMatrix b := Matrix.traceLeft M
    let Q : CMatrix d := Matrix.traceLeft N
    have hP : P.PosSemidef := traceLeft_posSemidef hM.1
    have hQ : Q.PosSemidef := traceLeft_posSemidef hN.1
    have hdiffP : ((1 : CMatrix b) - P).PosSemidef := hM.2
    have hdiffQ : ((1 : CMatrix d) - Q).PosSemidef := hN.2
    change (P ⊗ₖ Q ≤ (1 : CMatrix (b × d)))
    rw [Matrix.le_iff]
    have hsum := (hdiffP.kronecker Matrix.PosSemidef.one).add (hP.kronecker hdiffQ)
    convert hsum using 1
    ext x y
    rcases x with ⟨j, l⟩
    rcases y with ⟨j', l'⟩
    by_cases hj : j = j' <;> by_cases hl : l = l' <;>
      simp [P, Q, Matrix.kroneckerMap_apply, hj, hl] <;> ring

private theorem conditionalMinEntropyDualEffectGroupedProduct_value
    (rho : MState (a × b)) (tau : MState (c × d))
    (M : CMatrix (a × b)) (N : CMatrix (c × d))
    (hM : M.PosSemidef) (hN : N.PosSemidef) :
    (((rho.conditionalRenyiGroupedProduct tau).m *
        conditionalMinEntropyDualEffectGroupedProduct M N).trace).re =
      ((rho.m * M).trace).re * ((tau.m * N).trace).re := by
  let e := Equiv.prodProdProdComm a b c d
  have htrace :
      ((rho.conditionalRenyiGroupedProduct tau).m *
          conditionalMinEntropyDualEffectGroupedProduct M N).trace =
        (rho.m * M).trace * (tau.m * N).trace := by
    rw [conditionalRenyiGroupedProduct_matrix]
    unfold conditionalMinEntropyDualEffectGroupedProduct
    rw [Matrix.submatrix_mul_equiv]
    rw [Matrix.trace_submatrix _ e.symm]
    calc
      ((rho.m ⊗ₖ tau.m) * (M ⊗ₖ N)).trace =
          ((rho.m * M) ⊗ₖ (tau.m * N)).trace :=
        congrArg Matrix.trace
          (Matrix.mul_kronecker_mul rho.m M tau.m N).symm
      _ = (rho.m * M).trace * (tau.m * N).trace :=
        Matrix.trace_kronecker (rho.m * M) (tau.m * N)
  have hleftIm : ((rho.m * M).trace).im = 0 :=
    trace_mul_posSemidef_im_eq_zero rho.psd hM
  have hrightIm : ((tau.m * N).trace).im = 0 :=
    trace_mul_posSemidef_im_eq_zero tau.psd hN
  rw [htrace, Complex.mul_re, hleftIm, hrightIm]
  ring

private theorem conditionalMinEntropyScale_eq_iSup_dualEffect
    [Nonempty b] (rho : MState (a × b)) :
    rho.conditionalMinEntropyScale (a := a) =
      ⨆ M : {M : CMatrix (a × b) //
        ConditionalMinEntropyDualEffectFeasible (a := a) M},
        ((rho.m * M.1).trace).re := by
  rw [rho.conditionalMinEntropyScale_eq_sSup_dualEffectValueSet (a := a),
    ← sSup_range]
  congr 1
  ext x
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact ⟨⟨M, hM⟩, rfl⟩
  · rintro ⟨M, rfl⟩
    exact ⟨M.1, M.2, rfl⟩

/-- The endpoint conditional-min SDP scale is multiplicative on grouped
product states.  The upper bound tensors primal side operators; the lower
bound tensors dual effects and uses the already-proved finite-dimensional
strong duality theorem. -/
theorem conditionalMinEntropyScale_prod_grouped
    (rho : MState (a × b)) (tau : MState (c × d)) :
    (rho.conditionalRenyiGroupedProduct tau).conditionalMinEntropyScale
        (a := a × c) =
      rho.conditionalMinEntropyScale (a := a) *
        tau.conditionalMinEntropyScale (a := c) := by
  let : Nonempty a := by
    rcases rho.nonempty with ⟨i, _⟩
    exact ⟨i⟩
  let : Nonempty b := by
    rcases rho.nonempty with ⟨_, j⟩
    exact ⟨j⟩
  let : Nonempty c := by
    rcases tau.nonempty with ⟨k, _⟩
    exact ⟨k⟩
  let : Nonempty d := by
    rcases tau.nonempty with ⟨_, l⟩
    exact ⟨l⟩
  let rhoTau := rho.conditionalRenyiGroupedProduct tau
  let Prho := {T : CMatrix b // ConditionalMinEntropyScaleFeasible (a := a) rho T}
  let Ptau := {U : CMatrix d // ConditionalMinEntropyScaleFeasible (a := c) tau U}
  let Pprod := {V : CMatrix (b × d) //
    ConditionalMinEntropyScaleFeasible (a := a × c) rhoTau V}
  let Drho := {M : CMatrix (a × b) //
    ConditionalMinEntropyDualEffectFeasible (a := a) M}
  let Dtau := {N : CMatrix (c × d) //
    ConditionalMinEntropyDualEffectFeasible (a := c) N}
  let Dprod := {K : CMatrix ((a × c) × (b × d)) //
    ConditionalMinEntropyDualEffectFeasible (a := a × c) K}
  let : Nonempty Prho := by
    rcases rho.conditionalMinEntropyScaleValueSet_nonempty (a := a) with
      ⟨_, T, hT, rfl⟩
    exact ⟨⟨T, hT⟩⟩
  let : Nonempty Ptau := by
    rcases tau.conditionalMinEntropyScaleValueSet_nonempty (a := c) with
      ⟨_, U, hU, rfl⟩
    exact ⟨⟨U, hU⟩⟩
  let : Nonempty Pprod := by
    rcases rhoTau.conditionalMinEntropyScaleValueSet_nonempty (a := a × c) with
      ⟨_, V, hV, rfl⟩
    exact ⟨⟨V, hV⟩⟩
  let : Nonempty Drho :=
    ⟨⟨0, by
      constructor
      · exact Matrix.PosSemidef.zero
      · rw [Matrix.le_iff]
        have hzero : Matrix.traceLeft (0 : CMatrix (a × b)) = 0 := by
          ext i j
          simp [Matrix.traceLeft]
        rw [hzero]
        simpa using
          (Matrix.PosSemidef.one : (1 : CMatrix b).PosSemidef)⟩⟩
  let : Nonempty Dtau :=
    ⟨⟨0, by
      constructor
      · exact Matrix.PosSemidef.zero
      · rw [Matrix.le_iff]
        have hzero : Matrix.traceLeft (0 : CMatrix (c × d)) = 0 := by
          ext i j
          simp [Matrix.traceLeft]
        rw [hzero]
        simpa using
          (Matrix.PosSemidef.one : (1 : CMatrix d).PosSemidef)⟩⟩
  let : Nonempty Dprod :=
    ⟨⟨0, by
      constructor
      · exact Matrix.PosSemidef.zero
      · rw [Matrix.le_iff]
        have hzero : Matrix.traceLeft
            (0 : CMatrix ((a × c) × (b × d))) = 0 := by
          ext i j
          simp [Matrix.traceLeft]
        rw [hzero]
        simpa using
          (Matrix.PosSemidef.one : (1 : CMatrix (b × d)).PosSemidef)⟩⟩
  have hScaleTauPos : 0 < tau.conditionalMinEntropyScale (a := c) := by
    rw [tau.conditionalMinEntropyScale_eq_normalizedScale (a := c)]
    exact tau.conditionalMinEntropyNormalizedScale_inf_pos (a := c)
  have hPtauInfNonneg :
      0 ≤ ⨅ U : Ptau, U.1.trace.re := by
    change 0 ≤ ⨅ U : {U : CMatrix d //
      ConditionalMinEntropyScaleFeasible (a := c) tau U}, U.1.trace.re
    rw [← conditionalMinEntropyScale_eq_iInf_feasible tau]
    exact hScaleTauPos.le
  have hDtauSupNonneg :
      0 ≤ ⨆ N : Dtau, ((tau.m * N.1).trace).re := by
    change 0 ≤ ⨆ N : {N : CMatrix (c × d) //
      ConditionalMinEntropyDualEffectFeasible (a := c) N},
        ((tau.m * N.1).trace).re
    rw [← conditionalMinEntropyScale_eq_iSup_dualEffect tau]
    exact hScaleTauPos.le
  have hPrhoBdd : BddBelow (Set.range fun T : Prho => T.1.trace.re) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨T, rfl⟩
    exact (Matrix.PosSemidef.trace_nonneg T.2.1).1
  have hPtauBdd : BddBelow (Set.range fun U : Ptau => U.1.trace.re) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨U, rfl⟩
    exact (Matrix.PosSemidef.trace_nonneg U.2.1).1
  have hPprodBdd : BddBelow (Set.range fun V : Pprod => V.1.trace.re) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨V, rfl⟩
    exact (Matrix.PosSemidef.trace_nonneg V.2.1).1
  apply le_antisymm
  · rw [conditionalMinEntropyScale_eq_iInf_feasible rhoTau,
      conditionalMinEntropyScale_eq_iInf_feasible rho,
      conditionalMinEntropyScale_eq_iInf_feasible tau]
    rw [Real.iInf_mul_of_nonneg hPtauInfNonneg]
    refine le_ciInf fun T : Prho => ?_
    have hTnonneg : 0 ≤ T.1.trace.re :=
      (Matrix.PosSemidef.trace_nonneg T.2.1).1
    rw [Real.mul_iInf_of_nonneg hTnonneg]
    refine le_ciInf fun U : Ptau => ?_
    have hle := ciInf_le hPprodBdd
      (⟨T.1 ⊗ₖ U.1, T.2.prod_grouped U.2⟩ : Pprod)
    rw [trace_kronecker_re_of_posSemidef T.2.1 U.2.1] at hle
    exact hle
  · rw [conditionalMinEntropyScale_eq_iSup_dualEffect rhoTau,
      conditionalMinEntropyScale_eq_iSup_dualEffect rho,
      conditionalMinEntropyScale_eq_iSup_dualEffect tau]
    have hDprodBdd : BddAbove (Set.range fun K : Dprod =>
        ((rhoTau.m * K.1).trace).re) := by
      rcases rhoTau.conditionalMinEntropyDualEffectValueSet_bddAbove
          (a := a × c) with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      rintro _ ⟨K, rfl⟩
      exact hz ⟨K.1, K.2, rfl⟩
    rw [Real.iSup_mul_of_nonneg hDtauSupNonneg]
    refine ciSup_le fun M : Drho => ?_
    have hMnonneg : 0 ≤ ((rho.m * M.1).trace).re :=
      cMatrix_trace_mul_posSemidef_re_nonneg rho.psd M.2.1
    rw [Real.mul_iSup_of_nonneg hMnonneg]
    refine ciSup_le fun N : Dtau => ?_
    let K : Dprod := ⟨conditionalMinEntropyDualEffectGroupedProduct M.1 N.1,
      M.2.prod_grouped N.2⟩
    have hle := le_ciSup hDprodBdd K
    rw [conditionalMinEntropyDualEffectGroupedProduct_value
      rho tau M.1 N.1 M.2.1 N.2.1] at hle
    exact hle

/-- Conditional min-entropy is additive on grouped product states. -/
theorem conditionalMinEntropy_prod_grouped
    (rho : MState (a × b)) (tau : MState (c × d)) :
    (rho.conditionalRenyiGroupedProduct tau).conditionalMinEntropy =
      rho.conditionalMinEntropy + tau.conditionalMinEntropy := by
  let : Nonempty a := by
    rcases rho.nonempty with ⟨i, _⟩
    exact ⟨i⟩
  let : Nonempty b := by
    rcases rho.nonempty with ⟨_, j⟩
    exact ⟨j⟩
  let : Nonempty c := by
    rcases tau.nonempty with ⟨k, _⟩
    exact ⟨k⟩
  let : Nonempty d := by
    rcases tau.nonempty with ⟨_, l⟩
    exact ⟨l⟩
  have hRhoScale : 0 < rho.conditionalMinEntropyScale (a := a) := by
    rw [rho.conditionalMinEntropyScale_eq_normalizedScale (a := a)]
    exact rho.conditionalMinEntropyNormalizedScale_inf_pos (a := a)
  have hTauScale : 0 < tau.conditionalMinEntropyScale (a := c) := by
    rw [tau.conditionalMinEntropyScale_eq_normalizedScale (a := c)]
    exact tau.conditionalMinEntropyNormalizedScale_inf_pos (a := c)
  rw [(rho.conditionalRenyiGroupedProduct tau)
      |>.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a × c),
    rho.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a),
    tau.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := c),
    conditionalMinEntropyScale_prod_grouped rho tau,
    log2_mul hRhoScale.ne' hTauScale.ne']
  ring

/-- The conditional max-entropy endpoint is additive.  The proof uses product
purifications, min-entropy SDP additivity on the complementary marginals, and
the normalized pure-state min/max endpoint duality. -/
theorem conditionalMaxEntropy_prod_grouped
    (rho : MState (a × b)) (tau : MState (c × d)) :
    (rho.conditionalRenyiGroupedProduct tau).conditionalMaxEntropy =
      rho.conditionalMaxEntropy + tau.conditionalMaxEntropy := by
  let : Nonempty a := by
    rcases rho.nonempty with ⟨i, _⟩
    exact ⟨i⟩
  let : Nonempty b := by
    rcases rho.nonempty with ⟨_, j⟩
    exact ⟨j⟩
  let : Nonempty c := by
    rcases tau.nonempty with ⟨k, _⟩
    exact ⟨k⟩
  let : Nonempty d := by
    rcases tau.nonempty with ⟨_, l⟩
    exact ⟨l⟩
  let psi := conditionalRenyiTargetFirstCanonicalPurification rho
  let phi := conditionalRenyiTargetFirstCanonicalPurification tau
  let Psi := Ket.conditionalRenyiGroupedProductPurification psi phi
  have hPsiAB : Psi.state.marginalAB = rho.conditionalRenyiGroupedProduct tau := by
    rw [Ket.conditionalRenyiGroupedProductPurification_marginalAB]
    rw [conditionalRenyiTargetFirstCanonicalPurification_marginalAB,
      conditionalRenyiTargetFirstCanonicalPurification_marginalAB]
  have hPsiAC : Psi.state.marginalAC =
      psi.state.marginalAC.conditionalRenyiGroupedProduct phi.state.marginalAC :=
    Ket.conditionalRenyiGroupedProductPurification_marginalAC psi phi
  have hdualPsi :=
    Psi.conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC
  have hdualLeft :=
    psi.conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC
  have hdualRight :=
    phi.conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC
  have hmin := conditionalMinEntropy_prod_grouped
    psi.state.marginalAC phi.state.marginalAC
  rw [hPsiAB, hPsiAC] at hdualPsi
  rw [conditionalRenyiTargetFirstCanonicalPurification_marginalAB] at hdualLeft
  rw [conditionalRenyiTargetFirstCanonicalPurification_marginalAB] at hdualRight
  linarith

/-- The unified finite-order quantity is additive at the order-one-half
conditional max-entropy endpoint. -/
theorem conditionalSandwichedRenyiUpFiniteOrder_prod_grouped_half
    (rho : MState (a × b)) (tau : MState (c × d)) :
    (rho.conditionalRenyiGroupedProduct tau).conditionalSandwichedRenyiUpFiniteOrder
        (2 : ℝ)⁻¹ =
      rho.conditionalSandwichedRenyiUpFiniteOrder (2 : ℝ)⁻¹ +
        tau.conditionalSandwichedRenyiUpFiniteOrder (2 : ℝ)⁻¹ := by
  rw [conditionalSandwichedRenyiUpFiniteOrder_half,
    conditionalSandwichedRenyiUpFiniteOrder_half,
    conditionalSandwichedRenyiUpFiniteOrder_half]
  exact conditionalMaxEntropy_prod_grouped rho tau

/-- Tomamichel's finite-order tensor-product additivity theorem for upward
sandwiched conditional Renyi entropy. -/
theorem conditionalSandwichedRenyiUpFiniteOrder_prod_grouped
    (rho : MState (a × b)) (tau : MState (c × d))
    {alpha : ℝ} (halpha : (2 : ℝ)⁻¹ ≤ alpha) :
    (rho.conditionalRenyiGroupedProduct tau).conditionalSandwichedRenyiUpFiniteOrder alpha =
      rho.conditionalSandwichedRenyiUpFiniteOrder alpha +
        tau.conditionalSandwichedRenyiUpFiniteOrder alpha := by
  by_cases hhalf : alpha = (2 : ℝ)⁻¹
  · subst alpha
    exact conditionalSandwichedRenyiUpFiniteOrder_prod_grouped_half rho tau
  by_cases hone : alpha = 1
  · subst alpha
    exact conditionalSandwichedRenyiUpFiniteOrder_prod_grouped_one rho tau
  have hhalfStrict : 1 / 2 < alpha := by
    norm_num at halpha hhalf ⊢
    exact lt_of_le_of_ne halpha (Ne.symm hhalf)
  exact conditionalSandwichedRenyiUpFiniteOrder_prod_grouped_of_half_lt_ne_one
    rho tau hhalfStrict hone

end MState
