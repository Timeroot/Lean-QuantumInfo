/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.RenyiOrderParameter
public import QIT.Information.AlickiFannesWinter

/-!
# Extended-order upward sandwiched conditional Renyi duality

This module closes Tomamichel's pure-state upward sandwiched conditional
Renyi duality over the full order interval `[1/2, infinity]`.

Source: Tomamichel2015FiniteResources, `cond.tex:347-356`. The strict-interior
case reuses `PureVector.conditionalSandwichedRenyiUpSource_duality`, proved
from `cond.tex:366-400`; the boundary cases use conditional von Neumann
entropy duality and conditional max/min entropy duality.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w

noncomputable section

namespace RenyiOrder

private theorem recip_ne_top (alpha : RenyiOrder) : alpha.recip ≠ ⊤ := by
  rcases alpha with ⟨val, hval⟩
  cases val <;> simp [recip]

private theorem recip_injective : Function.Injective recip := by
  intro alpha beta h
  rcases alpha with ⟨alpha, halpha⟩
  rcases beta with ⟨beta, hbeta⟩
  cases alpha with
  | top =>
      cases beta with
      | top => rfl
      | coe beta =>
          have hbeta_half : (1 / 2 : Real) <= beta := by exact_mod_cast hbeta
          have hbeta_pos : 0 < beta := lt_of_lt_of_le (by norm_num) hbeta_half
          simp only [recip] at h
          change (0 : WithTop Real) = ((1 / beta : Real) : WithTop Real) at h
          have hreal : (0 : Real) = 1 / beta := by
            exact WithTop.coe_injective h
          exfalso
          exact (one_div_pos.mpr hbeta_pos).ne hreal
  | coe alpha =>
      cases beta with
      | top =>
          have halpha_half : (1 / 2 : Real) <= alpha := by exact_mod_cast halpha
          have halpha_pos : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha_half
          simp only [recip] at h
          change ((1 / alpha : Real) : WithTop Real) = 0 at h
          have hreal : (1 / alpha : Real) = 0 := by
            exact WithTop.coe_injective h
          exfalso
          exact (one_div_pos.mpr halpha_pos).ne' hreal
      | coe beta =>
          have halpha_half : (1 / 2 : Real) <= alpha := by exact_mod_cast halpha
          have hbeta_half : (1 / 2 : Real) <= beta := by exact_mod_cast hbeta
          have halpha_ne : alpha ≠ 0 :=
            (lt_of_lt_of_le (by norm_num) halpha_half).ne'
          have hbeta_ne : beta ≠ 0 :=
            (lt_of_lt_of_le (by norm_num) hbeta_half).ne'
          simp only [recip] at h
          change ((1 / alpha : Real) : WithTop Real) =
            ((1 / beta : Real) : WithTop Real) at h
          have hreal : (1 / alpha : Real) = 1 / beta := by
            exact WithTop.coe_injective h
          have hab : alpha = beta := by
            field_simp [halpha_ne, hbeta_ne] at hreal
            exact hreal.symm
          subst beta
          rfl

/-- The reciprocal relation determines the conjugate Renyi order uniquely. -/
theorem eq_conjugateOrder_of_recip_add_recip_eq_two
    {alpha beta : RenyiOrder} (h : alpha.recip + beta.recip = 2) :
    beta = alpha.conjugateOrder := by
  apply recip_injective
  exact WithTop.add_left_cancel (recip_ne_top alpha)
    (h.trans (recip_add_recip_conjugateOrder alpha).symm)

/-- Conjugating an extended Renyi order twice returns the original order. -/
theorem conjugateOrder_involutive (alpha : RenyiOrder) :
    alpha.conjugateOrder.conjugateOrder = alpha := by
  exact (eq_conjugateOrder_of_recip_add_recip_eq_two
    (alpha := alpha.conjugateOrder) (beta := alpha)
    (by simpa [add_comm] using recip_add_recip_conjugateOrder alpha)).symm

end RenyiOrder

namespace PureVector

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

private def swapConditioningReferenceEquiv :
    Prod (Prod a b) c ≃ Prod (Prod a c) b where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv x := by rcases x with ⟨⟨_, _⟩, _⟩; rfl
  right_inv x := by rcases x with ⟨⟨_, _⟩, _⟩; rfl

private theorem swapConditioningReference_marginalAB
    (psi : PureVector (Prod (Prod a b) c)) :
    (psi.reindex swapConditioningReferenceEquiv).state.marginalAB =
      psi.state.marginalAC := by
  apply State.ext
  ext x y
  rcases x with ⟨i, k⟩
  rcases y with ⟨i', k'⟩
  simp [State.marginalAC_matrix, State.marginalAB, State.marginalA,
    partialTraceB, PureVector.reindex_state, State.reindex,
    swapConditioningReferenceEquiv]

private theorem swapConditioningReference_marginalAC
    (psi : PureVector (Prod (Prod a b) c)) :
    (psi.reindex swapConditioningReferenceEquiv).state.marginalAC =
      psi.state.marginalAB := by
  apply State.ext
  ext x y
  rcases x with ⟨i, j⟩
  rcases y with ⟨i', j'⟩
  simp [State.marginalAC_matrix, State.marginalAB, State.marginalA,
    partialTraceB, PureVector.reindex_state, State.reindex,
    swapConditioningReferenceEquiv]

private theorem conditionalSandwichedRenyiUpSource_duality_of_ltOne
    [Nonempty b] [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c))
    {alpha beta : Real} (halpha_half : 1 / 2 < alpha)
    (halpha_one : alpha < 1) (hbeta_one : 1 < beta)
    (hconj : 1 / alpha + 1 / beta = 2) :
    psi.state.marginalAB.conditionalSandwichedRenyiUpSource alpha
        (lt_trans (by norm_num) halpha_half) (ne_of_lt halpha_one) +
      psi.state.marginalAC.conditionalSandwichedRenyiUpSource beta
        (lt_trans zero_lt_one hbeta_one) (ne_of_gt hbeta_one) = 0 := by
  let phi : PureVector (Prod (Prod a c) b) :=
    psi.reindex swapConditioningReferenceEquiv
  have hdual := phi.conditionalSandwichedRenyiUpSource_duality
    hbeta_one halpha_half halpha_one (by simpa [add_comm] using hconj)
  rw [swapConditioningReference_marginalAB,
    swapConditioningReference_marginalAC] at hdual
  linarith

private theorem conditionalMinEntropy_marginalAB_eq_neg_conditionalMaxEntropy_marginalAC
    [Nonempty a] [Nonempty b] [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c)) :
    psi.state.marginalAB.conditionalMinEntropy =
      -psi.state.marginalAC.conditionalMaxEntropy := by
  let phi : PureVector (Prod (Prod a c) b) :=
    psi.reindex swapConditioningReferenceEquiv
  have hdual :=
    phi.conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC
  rw [swapConditioningReference_marginalAB,
    swapConditioningReference_marginalAC] at hdual
  linarith

/-- Pure-state upward sandwiched conditional Renyi duality on the full closed
order interval `[1/2, infinity]`.

The two orders are independent inputs constrained only by
`1 / alpha + 1 / beta = 2`. Strict-interior orders use
`conditionalSandwichedRenyiUpSource_duality`, with complementary systems
swapped when `alpha < 1`; order one uses conditional von Neumann entropy
duality; the half/infinity pairs use conditional max/min entropy duality.

Source: Tomamichel2015FiniteResources, `cond.tex:347-356`, Proposition
`pr:dual-new`. -/
theorem conditionalSandwichedRenyiUpExtendedOrder_duality
    [Nonempty b] [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c))
    (alpha beta : RenyiOrder)
    (hconj : alpha.recip + beta.recip = 2) :
    psi.state.marginalAB.conditionalSandwichedRenyiUpExtendedOrder alpha +
      psi.state.marginalAC.conditionalSandwichedRenyiUpExtendedOrder beta = 0 := by
  classical
  have hbeta :=
    RenyiOrder.eq_conjugateOrder_of_recip_add_recip_eq_two hconj
  subst beta
  letI : Nonempty a :=
    ⟨(Classical.choice psi.state.marginalAB.nonempty).1⟩
  cases hval : alpha.val with
  | top =>
      have halpha : alpha = RenyiOrder.infinity := Subtype.ext hval
      rw [halpha]
      simp only [RenyiOrder.conjugateOrder_infinity,
        State.conditionalSandwichedRenyiUpExtendedOrder_infinity]
      rw [show
        psi.state.marginalAC.conditionalSandwichedRenyiUpExtendedOrder
            (RenyiOrder.ofReal (1 / 2 : Real) (by norm_num)) =
          psi.state.marginalAC.conditionalMaxEntropy by
        simp [one_div]]
      have hdual :=
        conditionalMinEntropy_marginalAB_eq_neg_conditionalMaxEntropy_marginalAC psi
      linarith
  | coe r =>
      have hrhalf : 1 / 2 <= r := alpha.le_of_coe hval
      have halpha : alpha = RenyiOrder.ofReal r (by exact_mod_cast hrhalf) :=
        Subtype.ext hval
      rw [halpha]
      by_cases hhalf : r = (2 : Real)⁻¹
      · subst r
        have horder :
            (RenyiOrder.ofReal (2 : Real)⁻¹ (by norm_num)).conjugateOrder =
              RenyiOrder.infinity := by
          simp [RenyiOrder.conjugateOrder]
        rw [horder,
          State.conditionalSandwichedRenyiUpExtendedOrder_half,
          State.conditionalSandwichedRenyiUpExtendedOrder_infinity]
        have hdual :=
          psi.conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC
        linarith
      · by_cases hone : r = 1
        · subst r
          have horder :
              (RenyiOrder.ofReal 1 (by norm_num)).conjugateOrder =
                RenyiOrder.ofReal 1 (by norm_num) := by
            simp [RenyiOrder.conjugateOrder]
          rw [horder,
            State.conditionalSandwichedRenyiUpExtendedOrder_one,
            State.conditionalSandwichedRenyiUpExtendedOrder_one]
          have hdual :=
            State.PureVector.conditionalEntropy_marginalAB_eq_neg_marginalAC psi
          linarith
        · have hhalf_div : r ≠ 1 / 2 := by
            simpa [one_div] using hhalf
          have hhalf_lt : 1 / 2 < r :=
            lt_of_le_of_ne hrhalf (Ne.symm hhalf_div)
          let gamma := conditionalRenyiConjugateOrder r
          by_cases hr : r < 1
          · have hgamma : 1 < gamma :=
              conditionalRenyiConjugateOrder_gt_one_of_lt_one hhalf_lt hr
            have horder :
                (RenyiOrder.ofReal r (by exact_mod_cast hrhalf)).conjugateOrder =
                  RenyiOrder.ofReal gamma
                    (by
                      exact_mod_cast (le_of_lt (lt_trans (by norm_num) hgamma))) := by
              simp [RenyiOrder.conjugateOrder, hhalf, hone, gamma]
            rw [horder,
              State.conditionalSandwichedRenyiUpExtendedOrder_ltOne
                psi.state.marginalAB hhalf_lt hr,
              State.conditionalSandwichedRenyiUpExtendedOrder_gtOne
                psi.state.marginalAC hgamma]
            exact psi.conditionalSandwichedRenyiUpSource_duality_of_ltOne
              hhalf_lt hr hgamma
                (by
                  simpa [gamma, add_comm] using
                    conditionalRenyiConjugateOrder_conjugate hhalf_lt)
          · have hrone : 1 < r :=
              lt_of_le_of_ne (le_of_not_gt hr) (Ne.symm hone)
            have hgamma_half : 1 / 2 < gamma :=
              conditionalRenyiConjugateOrder_half_lt_of_one_lt hrone
            have hgamma_one : gamma < 1 :=
              conditionalRenyiConjugateOrder_lt_one_of_one_lt hrone
            have horder :
                (RenyiOrder.ofReal r (by exact_mod_cast hrhalf)).conjugateOrder =
                  RenyiOrder.ofReal gamma
                    (by exact_mod_cast (le_of_lt hgamma_half)) := by
              simp [RenyiOrder.conjugateOrder, hhalf, hone, gamma]
            rw [horder,
              State.conditionalSandwichedRenyiUpExtendedOrder_gtOne
                psi.state.marginalAB hrone,
              State.conditionalSandwichedRenyiUpExtendedOrder_ltOne
                psi.state.marginalAC hgamma_half hgamma_one]
            exact psi.conditionalSandwichedRenyiUpSource_duality
              hrone hgamma_half hgamma_one
                (by
                  simpa [gamma, add_comm] using
                    conditionalRenyiConjugateOrder_conjugate hhalf_lt)

section RegionSmoke

variable [Nonempty b] [Nonempty c]

example (psi : PureVector (Prod (Prod a b) c)) :
    psi.state.marginalAB.conditionalSandwichedRenyiUpExtendedOrder
        (RenyiOrder.ofReal (1 / 2 : Real) (by norm_num)) +
      psi.state.marginalAC.conditionalSandwichedRenyiUpExtendedOrder
        RenyiOrder.infinity = 0 := by
  apply psi.conditionalSandwichedRenyiUpExtendedOrder_duality
  rw [RenyiOrder.recip_ofReal, RenyiOrder.recip_infinity]
  norm_num

example (psi : PureVector (Prod (Prod a b) c)) :
    psi.state.marginalAB.conditionalSandwichedRenyiUpExtendedOrder
        (RenyiOrder.ofReal (3 / 4 : Real) (by norm_num)) +
      psi.state.marginalAC.conditionalSandwichedRenyiUpExtendedOrder
        (RenyiOrder.ofReal (3 / 2 : Real) (by norm_num)) = 0 := by
  apply psi.conditionalSandwichedRenyiUpExtendedOrder_duality
  rw [RenyiOrder.recip_ofReal, RenyiOrder.recip_ofReal]
  rw [← WithTop.coe_add]
  norm_num

example (psi : PureVector (Prod (Prod a b) c)) :
    psi.state.marginalAB.conditionalSandwichedRenyiUpExtendedOrder
        (RenyiOrder.ofReal 1 (by norm_num)) +
      psi.state.marginalAC.conditionalSandwichedRenyiUpExtendedOrder
        (RenyiOrder.ofReal 1 (by norm_num)) = 0 := by
  apply psi.conditionalSandwichedRenyiUpExtendedOrder_duality
  norm_num [RenyiOrder.recip]

example (psi : PureVector (Prod (Prod a b) c)) :
    psi.state.marginalAB.conditionalSandwichedRenyiUpExtendedOrder
        (RenyiOrder.ofReal 2
          (by exact_mod_cast (show (1 / 2 : Real) <= 2 by norm_num))) +
      psi.state.marginalAC.conditionalSandwichedRenyiUpExtendedOrder
        (RenyiOrder.ofReal (2 / 3 : Real) (by norm_num)) = 0 := by
  apply psi.conditionalSandwichedRenyiUpExtendedOrder_duality
  rw [RenyiOrder.recip_ofReal, RenyiOrder.recip_ofReal]
  rw [← WithTop.coe_add]
  norm_num

example (psi : PureVector (Prod (Prod a b) c)) :
    psi.state.marginalAB.conditionalSandwichedRenyiUpExtendedOrder
        RenyiOrder.infinity +
      psi.state.marginalAC.conditionalSandwichedRenyiUpExtendedOrder
        (RenyiOrder.ofReal (1 / 2 : Real) (by norm_num)) = 0 := by
  apply psi.conditionalSandwichedRenyiUpExtendedOrder_duality
  norm_num [RenyiOrder.recip]

end RegionSmoke

end PureVector

end

end QIT
