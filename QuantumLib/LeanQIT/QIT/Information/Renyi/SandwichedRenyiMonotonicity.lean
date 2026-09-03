/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.SandwichedMutualInformation
public import QIT.Information.Renyi.FrankLieb.DPI
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Sandwiched Renyi monotonicity support

This module isolates reusable high-parameter monotonicity ingredients for the
sandwiched Renyi divergence and mutual information.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Topology
open Filter

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The Holder conjugate exponent associated with a high Renyi parameter. -/
theorem highAlpha_holderConjugate {alpha : Real} (halpha : 1 < alpha) :
    alpha.HolderConjugate (alpha / (alpha - 1)) := by
  simpa [Real.conjExponent] using Real.HolderConjugate.conjExponent halpha

/-- Reciprocal of the high-parameter Holder conjugate. -/
theorem one_div_highAlpha_conjExponent {alpha : Real} (halpha : 1 < alpha) :
    1 / (alpha / (alpha - 1)) = (alpha - 1) / alpha := by
  have halpha_pos : alpha ≠ 0 := ne_of_gt (lt_trans zero_lt_one halpha)
  have hden : alpha - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt halpha)
  field_simp [halpha_pos, hden]

/-- The high-parameter Holder conjugate exponent is positive. -/
theorem highAlpha_conjExponent_pos {alpha : Real} (halpha : 1 < alpha) :
    0 < alpha / (alpha - 1) := by
  exact div_pos (lt_trans zero_lt_one halpha) (sub_pos.mpr halpha)

/-- The high-parameter Holder conjugate exponent is strictly above one. -/
theorem one_lt_highAlpha_conjExponent {alpha : Real} (halpha : 1 < alpha) :
    1 < alpha / (alpha - 1) := by
  have hden : 0 < alpha - 1 := sub_pos.mpr halpha
  rw [lt_div_iff₀ hden]
  linarith

/-- The reciprocal high-parameter Holder conjugate lies in `(0, 1)`. -/
theorem highAlpha_conjExponent_inv_mem_Ioo {alpha : Real} (halpha : 1 < alpha) :
    (alpha - 1) / alpha ∈ Set.Ioo (0 : Real) 1 := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  constructor
  · exact div_pos (sub_pos.mpr halpha) halpha_pos
  · rw [div_lt_one halpha_pos]
    linarith

/-- The high-parameter sandwiched reference exponent is negative. -/
theorem highAlpha_sandwichExponent_neg {alpha : Real} (halpha : 1 < alpha) :
    (1 - alpha) / (2 * alpha) < 0 := by
  have hnum : 1 - alpha < 0 := sub_neg.mpr halpha
  have hden : 0 < 2 * alpha := mul_pos (by norm_num) (lt_trans zero_lt_one halpha)
  exact div_neg_of_neg_of_pos hnum hden

/-- A derivative-sign criterion for monotonicity on an open right ray. -/
theorem monotoneOn_Ioi_of_deriv_nonneg {f : Real → Real} {c : Real}
    (hcont : ContinuousOn f (Set.Ioi c))
    (hdiff : DifferentiableOn Real f (Set.Ioi c))
    (hderiv : ∀ x, c < x → 0 ≤ deriv f x) :
    MonotoneOn f (Set.Ioi c) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi c) hcont ?_ ?_
  · simpa [interior_Ioi] using hdiff
  · intro x hx
    exact hderiv x (by simpa [interior_Ioi] using hx)

/-- Convert monotonicity on the open high-parameter ray into the subtype form
used by right-limit and minimax handoffs. -/
theorem highAlphaSubtype_mono_of_monotoneOn_Ioi {β : Type*} [Preorder β]
    {f : Real → β} (hmono : MonotoneOn f (Set.Ioi (1 : Real))) :
    ∀ alpha beta : {alpha : Real // 1 < alpha},
      alpha.1 ≤ beta.1 → f alpha.1 ≤ f beta.1 := by
  intro alpha beta hab
  exact hmono alpha.2 beta.2 hab

/-- The PSD Schatten `p` expression is normalized so that its `p`-th real
power recovers the underlying PSD trace power. -/
theorem psdSchattenPNorm_rpow_eq_psdTracePower
    (A : CMatrix a) (hA : A.PosSemidef) {p : Real} (hp : 0 < p) :
    Real.rpow (psdSchattenPNorm A hA ⟨p, hp⟩) p = psdTracePower A hA p := by
  rw [psdSchattenPNorm, Internal.psdSchattenExpression]
  have htrace_nonneg : 0 ≤ psdTracePower A hA p := psdTracePower_nonneg A hA p
  have hp_ne : p ≠ 0 := ne_of_gt hp
  have hmul : (1 / p) * p = 1 := by
    field_simp [hp_ne]
  calc
    Real.rpow (Real.rpow (psdTracePower A hA p) (1 / p)) p =
        Real.rpow (psdTracePower A hA p) ((1 / p) * p) := by
      simpa using (Real.rpow_mul htrace_nonneg (1 / p) p).symm
    _ = psdTracePower A hA p := by
      rw [hmul]
      simp

/-- Finite weighted Jensen inequality for the scalar function `x log x`.

This is the finite-dimensional scalar core of the Khatri--Wilde Jensen step in
`Chapters/entropies.tex:2364-2371`. -/
theorem kw_weighted_sum_mul_log_le_sum_weighted_mul_log
    {idx : Type*} [Fintype idx] (w x : idx → Real)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hx_nonneg : ∀ i, 0 ≤ x i) :
    (∑ i, w i * x i) * Real.log (∑ i, w i * x i) ≤
      ∑ i, w i * (x i * Real.log (x i)) := by
  classical
  have hw_nonneg' : ∀ i ∈ (Finset.univ : Finset idx), 0 ≤ w i :=
    fun i _ => hw_nonneg i
  have hx_mem : ∀ i ∈ (Finset.univ : Finset idx), x i ∈ Set.Ici (0 : Real) :=
    fun i _ => hx_nonneg i
  have hjensen :=
    Real.convexOn_mul_log.map_sum_le
      (t := (Finset.univ : Finset idx)) (w := w) (p := x)
      hw_nonneg' (by simpa using hw_sum) hx_mem
  simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hjensen

/-- Base-two version of `kw_weighted_sum_mul_log_le_sum_weighted_mul_log`. -/
theorem kw_weighted_sum_mul_log2_le_sum_weighted_mul_log2
    {idx : Type*} [Fintype idx] (w x : idx → Real)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hx_nonneg : ∀ i, 0 ≤ x i) :
    (∑ i, w i * x i) * log2 (∑ i, w i * x i) ≤
      ∑ i, w i * (x i * log2 (x i)) := by
  classical
  have hnat :=
    kw_weighted_sum_mul_log_le_sum_weighted_mul_log w x hw_nonneg hw_sum hx_nonneg
  have hscale : 0 ≤ (Real.log 2)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (Real.log_pos one_lt_two))
  have hscaled := mul_le_mul_of_nonneg_right hnat hscale
  simpa [log2, div_eq_mul_inv, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm,
    mul_assoc] using hscaled

/-- Derivative formula for the scalar log-moment term in the
Khatri--Wilde proof of sandwiched-Renyi monotonicity in `alpha`
(`Chapters/entropies.tex:2359-2363`). -/
theorem kw_weighted_logMoment_hasDerivAt
    {idx : Type*} [Fintype idx] (w x : idx → Real)
    (hx_pos : ∀ i, 0 < x i) {gamma : Real}
    (hSgamma : (∑ i, w i * x i ^ gamma) ≠ 0) (hgamma : gamma ≠ 0) :
    HasDerivAt
      (fun t : Real => Real.log (∑ i, w i * x i ^ t) / t)
      ((((∑ i, w i * (Real.log (x i) * x i ^ gamma)) /
            (∑ i, w i * x i ^ gamma)) *
          gamma -
        Real.log (∑ i, w i * x i ^ gamma)) / gamma ^ 2)
      gamma := by
  classical
  let S : Real → Real := fun t => ∑ i, w i * x i ^ t
  have hpow :
      ∀ i, HasDerivAt (fun t : Real => x i ^ t)
        (Real.log (x i) * x i ^ gamma) gamma := by
    intro i
    simpa using (hasDerivAt_id gamma).const_rpow (hx_pos i)
  have hterm :
      ∀ i ∈ (Finset.univ : Finset idx),
        HasDerivAt (fun t : Real => w i * x i ^ t)
          (w i * (Real.log (x i) * x i ^ gamma)) gamma := by
    intro i _
    simpa [mul_comm, mul_left_comm, mul_assoc] using (hpow i).const_mul (w i)
  have hS :
      HasDerivAt S (∑ i, w i * (Real.log (x i) * x i ^ gamma)) gamma := by
    simpa [S] using HasDerivAt.fun_sum hterm
  have hlog :
      HasDerivAt (fun t : Real => Real.log (S t))
        ((∑ i, w i * (Real.log (x i) * x i ^ gamma)) / S gamma) gamma :=
    hS.log (by simpa [S] using hSgamma)
  have hdiv := hlog.div (hasDerivAt_id gamma) hgamma
  convert hdiv using 1
  simp [S, div_eq_mul_inv, mul_comm]

/-- Positivity of the weighted power sum appearing in the scalar log-moment
argument. -/
theorem kw_weighted_rpow_sum_pos
    {idx : Type*} [Fintype idx] (w x : idx → Real)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hx_pos : ∀ i, 0 < x i) (gamma : Real) :
    0 < ∑ i, w i * x i ^ gamma := by
  classical
  have hxpow_pos : ∀ i, 0 < x i ^ gamma :=
    fun i => Real.rpow_pos_of_pos (hx_pos i) gamma
  have hterm_nonneg :
      ∀ i ∈ (Finset.univ : Finset idx), 0 ≤ w i * x i ^ gamma := by
    intro i _
    exact mul_nonneg (hw_nonneg i) (le_of_lt (hxpow_pos i))
  have hw_exists : ∃ i ∈ (Finset.univ : Finset idx), 0 < w i := by
    have hsum_pos : 0 < ∑ i, w i := by
      rw [hw_sum]
      norm_num
    exact (Finset.sum_pos_iff_of_nonneg (fun i _ => hw_nonneg i)).mp hsum_pos
  rcases hw_exists with ⟨i, hi, hwi⟩
  exact Finset.sum_pos' hterm_nonneg ⟨i, hi, mul_pos hwi (hxpow_pos i)⟩

/-- Nonnegativity of the scalar derivative in the Khatri--Wilde proof of
sandwiched-Renyi monotonicity in `alpha`
(`Chapters/entropies.tex:2364-2372`).

For positive spectral values `x i` and probability weights `w i`, Jensen gives
`S log S ≤ ∑ᵢ wᵢ xᵢ^γ log(xᵢ^γ) = γ S'`, which is exactly the numerator of the
derivative of `γ ↦ log(S γ) / γ`. -/
theorem kw_weighted_logMoment_deriv_nonneg
    {idx : Type*} [Fintype idx] (w x : idx → Real)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hx_pos : ∀ i, 0 < x i) {gamma : Real} (hgamma : gamma ≠ 0) :
    0 ≤ deriv (fun t : Real => Real.log (∑ i, w i * x i ^ t) / t) gamma := by
  classical
  let S : Real := ∑ i, w i * x i ^ gamma
  let A : Real := ∑ i, w i * (Real.log (x i) * x i ^ gamma)
  have hxpow_pos : ∀ i, 0 < x i ^ gamma :=
    fun i => Real.rpow_pos_of_pos (hx_pos i) gamma
  have hxpow_nonneg : ∀ i, 0 ≤ x i ^ gamma := fun i => le_of_lt (hxpow_pos i)
  have hSpos : 0 < S := by
    simpa [S] using kw_weighted_rpow_sum_pos w x hw_nonneg hw_sum hx_pos gamma
  have hderiv :=
    kw_weighted_logMoment_hasDerivAt w x hx_pos
      (by simpa [S] using ne_of_gt hSpos) hgamma
  rw [hderiv.deriv]
  have hjensen :
      S * Real.log S ≤ ∑ i, w i * (x i ^ gamma * Real.log (x i ^ gamma)) := by
    simpa [S] using
      kw_weighted_sum_mul_log_le_sum_weighted_mul_log w (fun i => x i ^ gamma)
        hw_nonneg hw_sum hxpow_nonneg
  have hright :
      (∑ i, w i * (x i ^ gamma * Real.log (x i ^ gamma))) = gamma * A := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.log_rpow (hx_pos i)]
    ring
  have hSA : S * Real.log S ≤ gamma * A := by
    simpa [hright] using hjensen
  have hlog_le : Real.log S ≤ (gamma * A) / S := by
    rw [le_div_iff₀ hSpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hSA
  have hnum_nonneg :
      0 ≤ (A / S) * gamma - Real.log S := by
    rw [sub_nonneg]
    calc
      Real.log S ≤ (gamma * A) / S := hlog_le
      _ = (A / S) * gamma := by
        field_simp [ne_of_gt hSpos]
  exact div_nonneg hnum_nonneg (sq_nonneg gamma)

/-- Alpha-parameter version of the scalar Khatri--Wilde derivative sign.

With `γ(α) = (1 - α) / α`, the sandwiched variational scalar objective is
`-log(S(γ(α))) / (γ(α) log 2)`.  Since `γ'(α) = -1 / α²` and the log-moment
derivative in `γ` is nonnegative, the derivative in `α` is nonnegative for
`α > 1`. -/
theorem kw_weighted_alphaObjective_deriv_nonneg
    {idx : Type*} [Fintype idx] (w x : idx → Real)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hx_pos : ∀ i, 0 < x i) {alpha : Real} (halpha : 1 < alpha) :
    0 ≤ deriv
      (fun alpha : Real =>
        -((Real.log (∑ i, w i * x i ^ ((1 - alpha) / alpha)) /
            ((1 - alpha) / alpha)) / Real.log 2))
      alpha := by
  classical
  let gamma : Real := (1 - alpha) / alpha
  let F : Real → Real := fun gamma => Real.log (∑ i, w i * x i ^ gamma) / gamma
  let F' : Real :=
    (((∑ i, w i * (Real.log (x i) * x i ^ gamma)) /
          (∑ i, w i * x i ^ gamma)) *
        gamma -
      Real.log (∑ i, w i * x i ^ gamma)) / gamma ^ 2
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hgamma_ne : gamma ≠ 0 := by
    dsimp [gamma]
    exact div_ne_zero (by linarith) (ne_of_gt halpha_pos)
  have hSpos : 0 < ∑ i, w i * x i ^ gamma :=
    kw_weighted_rpow_sum_pos w x hw_nonneg hw_sum hx_pos gamma
  have hF : HasDerivAt F F' gamma := by
    simpa [F, F'] using
      kw_weighted_logMoment_hasDerivAt w x hx_pos (ne_of_gt hSpos) hgamma_ne
  have hF_nonneg : 0 ≤ F' := by
    have hnonneg :=
      kw_weighted_logMoment_deriv_nonneg w x hw_nonneg hw_sum hx_pos hgamma_ne
    rw [hF.deriv] at hnonneg
    exact hnonneg
  have hgammaDeriv : HasDerivAt (fun alpha : Real => (1 - alpha) / alpha)
      (-1 / alpha ^ 2) alpha := by
    have hnum : HasDerivAt (fun alpha : Real => 1 - alpha) (-1) alpha := by
      simpa using
        (hasDerivAt_const (x := alpha) (c := (1 : Real))).sub (hasDerivAt_id alpha)
    have hdiv := hnum.div (hasDerivAt_id alpha) (ne_of_gt halpha_pos)
    convert hdiv using 1
    field_simp [ne_of_gt halpha_pos]
    simp
    ring_nf
  have hcomp : HasDerivAt (fun alpha : Real => F ((1 - alpha) / alpha))
      (F' * (-1 / alpha ^ 2)) alpha := by
    simpa [gamma] using hF.comp alpha hgammaDeriv
  have hD :
      HasDerivAt
        (fun alpha : Real => -(F ((1 - alpha) / alpha) / Real.log 2))
        (-(F' * (-1 / alpha ^ 2) / Real.log 2)) alpha :=
    (hcomp.div_const (Real.log 2)).neg
  rw [hD.deriv]
  have hgammaDeriv_nonpos : -1 / alpha ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg alpha)
  have hprod_nonpos : F' * (-1 / alpha ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hF_nonneg hgammaDeriv_nonpos
  have hlog2_nonneg : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos one_lt_two)
  exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hprod_nonpos hlog2_nonneg)

/-- Differentiability of the scalar Khatri--Wilde `alpha` objective on the
high-parameter ray. -/
theorem kw_weighted_alphaObjective_differentiableAt
    {idx : Type*} [Fintype idx] (w x : idx → Real)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hx_pos : ∀ i, 0 < x i) {alpha : Real} (halpha : 1 < alpha) :
    DifferentiableAt Real
      (fun alpha : Real =>
        -((Real.log (∑ i, w i * x i ^ ((1 - alpha) / alpha)) /
            ((1 - alpha) / alpha)) / Real.log 2))
      alpha := by
  classical
  let gamma : Real := (1 - alpha) / alpha
  let F : Real → Real := fun gamma => Real.log (∑ i, w i * x i ^ gamma) / gamma
  let F' : Real :=
    (((∑ i, w i * (Real.log (x i) * x i ^ gamma)) /
          (∑ i, w i * x i ^ gamma)) *
        gamma -
      Real.log (∑ i, w i * x i ^ gamma)) / gamma ^ 2
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hgamma_ne : gamma ≠ 0 := by
    dsimp [gamma]
    exact div_ne_zero (by linarith) (ne_of_gt halpha_pos)
  have hS_ne : (∑ i, w i * x i ^ gamma) ≠ 0 := by
    exact ne_of_gt (kw_weighted_rpow_sum_pos w x hw_nonneg hw_sum hx_pos gamma)
  have hF : HasDerivAt F F' gamma := by
    simpa [F, F'] using
      kw_weighted_logMoment_hasDerivAt w x hx_pos hS_ne hgamma_ne
  have hgammaDeriv : HasDerivAt (fun alpha : Real => (1 - alpha) / alpha)
      (-1 / alpha ^ 2) alpha := by
    have hnum : HasDerivAt (fun alpha : Real => 1 - alpha) (-1) alpha := by
      simpa using
        (hasDerivAt_const (x := alpha) (c := (1 : Real))).sub (hasDerivAt_id alpha)
    have hdiv := hnum.div (hasDerivAt_id alpha) (ne_of_gt halpha_pos)
    convert hdiv using 1
    field_simp [ne_of_gt halpha_pos]
    simp
    ring_nf
  have hcomp : HasDerivAt (fun alpha : Real => F ((1 - alpha) / alpha))
      (F' * (-1 / alpha ^ 2)) alpha := by
    simpa [gamma] using hF.comp alpha hgammaDeriv
  have hD :
      HasDerivAt
        (fun alpha : Real => -(F ((1 - alpha) / alpha) / Real.log 2))
        (-(F' * (-1 / alpha ^ 2) / Real.log 2)) alpha :=
    (hcomp.div_const (Real.log 2)).neg
  exact hD.differentiableAt

/-- Monotonicity of the scalar Khatri--Wilde `alpha` objective on the
high-parameter ray. -/
theorem kw_weighted_alphaObjective_monotoneOn_Ioi
    {idx : Type*} [Fintype idx] (w x : idx → Real)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hx_pos : ∀ i, 0 < x i) :
    MonotoneOn
      (fun alpha : Real =>
        -((Real.log (∑ i, w i * x i ^ ((1 - alpha) / alpha)) /
            ((1 - alpha) / alpha)) / Real.log 2))
      (Set.Ioi (1 : Real)) := by
  let f : Real → Real := fun alpha =>
    -((Real.log (∑ i, w i * x i ^ ((1 - alpha) / alpha)) /
        ((1 - alpha) / alpha)) / Real.log 2)
  have hdiff : DifferentiableOn Real f (Set.Ioi (1 : Real)) := by
    intro alpha halpha
    have hdiffAt :=
      kw_weighted_alphaObjective_differentiableAt w x hw_nonneg hw_sum hx_pos halpha
    exact hdiffAt.differentiableWithinAt
  have hcont : ContinuousOn f (Set.Ioi (1 : Real)) := hdiff.continuousOn
  exact monotoneOn_Ioi_of_deriv_nonneg hcont hdiff
    (fun alpha halpha =>
      kw_weighted_alphaObjective_deriv_nonneg w x hw_nonneg hw_sum hx_pos halpha)

/-- Subtype form of `kw_weighted_alphaObjective_monotoneOn_Ioi`, matching the
high-parameter order handoffs used later in the sandwiched limit proof. -/
theorem kw_weighted_alphaObjective_mono
    {idx : Type*} [Fintype idx] (w x : idx → Real)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hx_pos : ∀ i, 0 < x i) :
    ∀ alpha beta : {alpha : Real // 1 < alpha},
      alpha.1 ≤ beta.1 →
        -((Real.log (∑ i, w i * x i ^ ((1 - alpha.1) / alpha.1)) /
            ((1 - alpha.1) / alpha.1)) / Real.log 2) ≤
          -((Real.log (∑ i, w i * x i ^ ((1 - beta.1) / beta.1)) /
            ((1 - beta.1) / beta.1)) / Real.log 2) := by
  exact
    highAlphaSubtype_mono_of_monotoneOn_Ioi
      (kw_weighted_alphaObjective_monotoneOn_Ioi w x hw_nonneg hw_sum hx_pos)

/-- Matrix-state form of the Khatri--Wilde scalar derivative step.

For a fixed positive-definite observable `X`, the vector-state log moment
`-log Tr[ρ X^γ] / γ`, with `γ = (1 - α) / α`, is monotone increasing in the
high parameter `α`.  The proof diagonalizes `X`, uses the diagonal of the
conjugated state as probability weights, and applies the finite scalar
Khatri--Wilde Jensen lemma. -/
theorem kw_state_rpowTrace_alphaObjective_mono
    (rho : State a) {X : CMatrix a} (hX : X.PosDef) :
    ∀ alpha beta : {alpha : Real // 1 < alpha},
      alpha.1 ≤ beta.1 →
        -((Real.log
              ((rho.matrix *
                CFC.rpow X ((1 - alpha.1) / alpha.1)).trace).re /
            ((1 - alpha.1) / alpha.1)) / Real.log 2) ≤
          -((Real.log
              ((rho.matrix *
                CFC.rpow X ((1 - beta.1) / beta.1)).trace).re /
            ((1 - beta.1) / beta.1)) / Real.log 2) := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hX.posSemidef.isHermitian.eigenvectorUnitary
  let w : a → Real := fun i =>
    ((star (U : CMatrix a) * rho.matrix * (U : CMatrix a)) i i).re
  let x : a → Real := fun i => hX.posSemidef.isHermitian.eigenvalues i
  have hconj :
      (star (U : CMatrix a) * rho.matrix * (U : CMatrix a)).PosSemidef := by
    simpa [U] using posSemidef_unitary_conj rho.pos U
  have hw_nonneg : ∀ i, 0 ≤ w i := by
    intro i
    simpa [w] using posSemidef_diagonal_re_nonneg hconj i
  have htrace_conj :
      ((star (U : CMatrix a) * rho.matrix * (U : CMatrix a)).trace).re = 1 := by
    have htrace :
        (star (U : CMatrix a) * rho.matrix * (U : CMatrix a)).trace =
          rho.matrix.trace := by
      calc
        (star (U : CMatrix a) * rho.matrix * (U : CMatrix a)).trace =
            (rho.matrix * (U : CMatrix a) * star (U : CMatrix a)).trace := by
              rw [← Matrix.trace_mul_cycle]
        _ = (rho.matrix * ((U : CMatrix a) * star (U : CMatrix a))).trace := by
              rw [Matrix.mul_assoc]
        _ = (rho.matrix * (1 : CMatrix a)).trace := by
              have hUU : (U : CMatrix a) * star (U : CMatrix a) = (1 : CMatrix a) := by
                simp
              rw [hUU]
        _ = rho.matrix.trace := by
              rw [Matrix.mul_one]
    simpa [htrace] using congrArg Complex.re rho.trace_eq_one
  have hw_sum : ∑ i, w i = 1 := by
    calc
      ∑ i, w i =
          ((star (U : CMatrix a) * rho.matrix * (U : CMatrix a)).trace).re := by
            simp [w, Matrix.trace]
      _ = 1 := htrace_conj
  have hx_pos : ∀ i, 0 < x i := by
    intro i
    simpa [x] using hX.eigenvalues_pos i
  have htrace (gamma : Real) :
      ((rho.matrix * CFC.rpow X gamma).trace).re =
        ∑ i, w i * x i ^ gamma := by
    simpa [U, w, x, mul_comm] using
      trace_mul_cMatrix_rpow_eq_conjugate_diag_sum
        (M := rho.matrix) (N := X) hX.posSemidef gamma
  intro alpha beta hab
  have hscalar :=
    kw_weighted_alphaObjective_mono w x hw_nonneg hw_sum hx_pos alpha beta hab
  rw [htrace ((1 - alpha.1) / alpha.1), htrace ((1 - beta.1) / beta.1)]
  exact hscalar

/-- Finite-dimensional vector-state Jensen input for the Khatri--Wilde
`alpha`-monotonicity proof.

For a PSD matrix, each diagonal entry in a Hermitian eigenbasis is a convex
combination of the eigenvalues.  Applying scalar Jensen to `g(x) = x log x`
gives the vector-state inequality used in
`Chapters/entropies.tex:2364-2371`. -/
theorem kw_posSemidef_diagonal_re_mul_log_le_eigenvalue_weighted_mul_log
    {B : CMatrix a} (hB : B.PosSemidef) (i : a) :
    (B i i).re * Real.log (B i i).re ≤
      ∑ j, Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
        (hB.isHermitian.eigenvalues j * Real.log (hB.isHermitian.eigenvalues j)) := by
  classical
  let w : a → Real := fun j =>
    Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j)
  let evals : a → Real := fun j => hB.isHermitian.eigenvalues j
  have hw_nonneg : ∀ j, 0 ≤ w j := fun j => Complex.normSq_nonneg _
  have hw_sum : ∑ j, w j = 1 := by
    simpa [w] using unitary_row_normSq_sum hB.isHermitian.eigenvectorUnitary i
  have hevals_nonneg : ∀ j, 0 ≤ evals j := fun j => hB.eigenvalues_nonneg j
  have hjensen :=
    kw_weighted_sum_mul_log_le_sum_weighted_mul_log w evals hw_nonneg hw_sum hevals_nonneg
  have hdiag :
      (B i i).re = ∑ j, w j * evals j := by
    simpa [w, evals, mul_comm] using
      posSemidef_diagonal_re_eq_eigenvalue_weighted_sum hB i
  rw [hdiag]
  simpa [w, evals, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hjensen

/-- Base-two form of the finite-dimensional vector-state Jensen input used in
Khatri--Wilde's derivative numerator.

This is just
`kw_posSemidef_diagonal_re_mul_log_le_eigenvalue_weighted_mul_log` rescaled by
the positive constant `1 / log 2`. -/
theorem kw_posSemidef_diagonal_re_mul_log2_le_eigenvalue_weighted_mul_log2
    {B : CMatrix a} (hB : B.PosSemidef) (i : a) :
    (B i i).re * log2 (B i i).re ≤
      ∑ j, Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
        (hB.isHermitian.eigenvalues j * log2 (hB.isHermitian.eigenvalues j)) := by
  classical
  have hnat :=
    kw_posSemidef_diagonal_re_mul_log_le_eigenvalue_weighted_mul_log (B := B) hB i
  have hscale : 0 ≤ (Real.log 2)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (Real.log_pos one_lt_two))
  have hscaled := mul_le_mul_of_nonneg_right hnat hscale
  simpa [log2, div_eq_mul_inv, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using
    hscaled

/-- If a high-parameter curve is the supremum of fixed candidates and every
fixed candidate is monotone in the high parameter, then the optimized curve is
monotone.

This is the order-theoretic handoff used after the Khatri--Wilde variational
formula `eq-sand_rel_ent_var`: the analytic work proves fixed-candidate
monotonicity, while the variational formula identifies the divergence as the
supremum over those candidates. -/
theorem highAlpha_iSup_mono_of_eq_iSup {ι : Sort*}
    {f : {alpha : Real // 1 < alpha} → EReal}
    {g : ι → {alpha : Real // 1 < alpha} → EReal}
    (hvar : ∀ alpha, f alpha = ⨆ i, g i alpha)
    (hmono :
      ∀ i, ∀ alpha beta : {alpha : Real // 1 < alpha},
        alpha.1 ≤ beta.1 → g i alpha ≤ g i beta) :
    ∀ alpha beta : {alpha : Real // 1 < alpha},
      alpha.1 ≤ beta.1 → f alpha ≤ f beta := by
  intro alpha beta hab
  rw [hvar alpha, hvar beta]
  refine iSup_le ?_
  intro i
  exact (hmono i alpha beta hab).trans (le_iSup (fun j => g j beta) i)

/-- If a high-parameter curve is the infimum of fixed candidates and every
fixed candidate is monotone in the high parameter, then the optimized curve is
monotone.

This companion order bridge is useful for optimized mutual-information
quantities once the side-state optimization has been restricted to a fixed
candidate domain. -/
theorem highAlpha_iInf_mono_of_eq_iInf {ι : Sort*}
    {f : {alpha : Real // 1 < alpha} → EReal}
    {g : ι → {alpha : Real // 1 < alpha} → EReal}
    (hvar : ∀ alpha, f alpha = ⨅ i, g i alpha)
    (hmono :
      ∀ i, ∀ alpha beta : {alpha : Real // 1 < alpha},
        alpha.1 ≤ beta.1 → g i alpha ≤ g i beta) :
    ∀ alpha beta : {alpha : Real // 1 < alpha},
      alpha.1 ≤ beta.1 → f alpha ≤ f beta := by
  intro alpha beta hab
  rw [hvar alpha, hvar beta]
  refine le_iInf ?_
  intro i
  exact (iInf_le (fun j => g j alpha) i).trans (hmono i alpha beta hab)

namespace State

/-- Khatri--Wilde variational-formula bridge for high-parameter PSD-reference
sandwiched Renyi monotonicity.

Once the source variational formula identifies `D~_alpha(rho || sigma)` with a
supremum over fixed auxiliary states, monotonicity of every fixed auxiliary
objective implies monotonicity of the PSD-reference divergence itself. -/
theorem sandwichedRenyiPSDReferenceE_mono_of_variational_formula
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosSemidef)
    {ι : Sort*} {candidate : ι → {alpha : Real // 1 < alpha} → EReal}
    (hvar :
      ∀ gamma : {gamma : Real // 1 < gamma},
        sandwichedRenyiPSDReferenceE rho sigma hsigma gamma.1 =
          ⨆ i, candidate i gamma)
    (hmono :
      ∀ i, ∀ alpha beta : {alpha : Real // 1 < alpha},
        alpha.1 ≤ beta.1 → candidate i alpha ≤ candidate i beta) :
    ∀ alpha beta : {alpha : Real // 1 < alpha},
      alpha.1 ≤ beta.1 →
        sandwichedRenyiPSDReferenceE rho sigma hsigma alpha.1 ≤
          sandwichedRenyiPSDReferenceE rho sigma hsigma beta.1 :=
  highAlpha_iSup_mono_of_eq_iSup hvar hmono

/-- Khatri--Wilde variational-formula bridge for monotonicity of a fixed
side-information mutual-information candidate.

This is the candidate-level form needed before taking the `inf` over side
states in the optimized mutual information. -/
theorem sandwichedRenyiMutualInformationCandidateE_mono_of_variational_formula
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    {ι : Sort*} {candidate : ι → {alpha : Real // 1 < alpha} → EReal}
    (hvar :
      ∀ gamma : {gamma : Real // 1 < gamma},
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB gamma.1 =
          ⨆ i, candidate i gamma)
    (hmono :
      ∀ i, ∀ alpha beta : {alpha : Real // 1 < alpha},
        alpha.1 ≤ beta.1 → candidate i alpha ≤ candidate i beta) :
    ∀ alpha beta : {alpha : Real // 1 < alpha},
      alpha.1 ≤ beta.1 →
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1 ≤
          rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB beta.1 :=
  highAlpha_iSup_mono_of_eq_iSup hvar hmono

/-- The optimized state sandwiched-Renyi mutual information is an indexed
infimum over side-information states. -/
theorem sandwichedRenyiMutualInformationE_eq_iInf
    (rhoAB : State (Prod a b)) (alpha : Real) :
    rhoAB.sandwichedRenyiMutualInformationE alpha =
      ⨅ sigmaB : State b,
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha := by
  rw [State.sandwichedRenyiMutualInformationE_eq_sInf,
    State.sandwichedRenyiMutualInformationEValueSet, sInf_range]

/-- Khatri--Wilde monotonicity lift for the state optimized
`inf_sigmaB` expression.

Once every fixed side-information candidate is monotone in `alpha`, the
optimized state sandwiched-Renyi mutual information is monotone as well. -/
theorem sandwichedRenyiMutualInformationE_mono_of_candidate_mono
    [Nonempty b]
    (rhoAB : State (Prod a b))
    (hmono :
      ∀ sigmaB : State b, ∀ alpha beta : {alpha : Real // 1 < alpha},
        alpha.1 ≤ beta.1 →
          rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1 ≤
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB beta.1) :
    ∀ alpha beta : {alpha : Real // 1 < alpha},
      alpha.1 ≤ beta.1 →
        rhoAB.sandwichedRenyiMutualInformationE alpha.1 ≤
          rhoAB.sandwichedRenyiMutualInformationE beta.1 := by
  exact
    highAlpha_iInf_mono_of_eq_iInf
      (f := fun gamma : {gamma : Real // 1 < gamma} =>
        rhoAB.sandwichedRenyiMutualInformationE gamma.1)
      (g := fun sigmaB gamma =>
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB gamma.1)
      (fun gamma => rhoAB.sandwichedRenyiMutualInformationE_eq_iInf gamma.1)
      hmono

/-- Variational-formula bridge for optimized state sandwiched-Renyi
monotonicity.

This packages the KW route: a variational formula for every fixed side state,
plus monotonicity of every fixed variational objective, yields monotonicity of
the side-state optimized mutual information. -/
theorem sandwichedRenyiMutualInformationE_mono_of_candidate_variational_formula
    [Nonempty b]
    (rhoAB : State (Prod a b))
    {ι : State b → Sort*}
    {candidate :
      (sigmaB : State b) → ι sigmaB → {alpha : Real // 1 < alpha} → EReal}
    (hvar :
      ∀ sigmaB : State b, ∀ gamma : {gamma : Real // 1 < gamma},
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB gamma.1 =
          ⨆ i, candidate sigmaB i gamma)
    (hmono :
      ∀ sigmaB : State b, ∀ i, ∀ alpha beta : {alpha : Real // 1 < alpha},
        alpha.1 ≤ beta.1 →
          candidate sigmaB i alpha ≤ candidate sigmaB i beta) :
    ∀ alpha beta : {alpha : Real // 1 < alpha},
      alpha.1 ≤ beta.1 →
        rhoAB.sandwichedRenyiMutualInformationE alpha.1 ≤
          rhoAB.sandwichedRenyiMutualInformationE beta.1 := by
  refine rhoAB.sandwichedRenyiMutualInformationE_mono_of_candidate_mono ?_
  intro sigmaB
  exact
    sandwichedRenyiMutualInformationCandidateE_mono_of_variational_formula
      rhoAB sigmaB (hvar sigmaB) (hmono sigmaB)

/-- The finite high-parameter PSD-reference branch can be written as the
logarithm of the `alpha`-th real power of the PSD Schatten `alpha` expression. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_eq_log2_psdSchattenPNorm_rpow
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosSemidef)
    {alpha : Real} (halpha_pos : 0 < alpha) :
    sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma alpha =
      (1 / (alpha - 1)) *
        log2
          (Real.rpow
            (psdSchattenPNorm
              (sandwichedRenyiReferenceInner rho sigma alpha)
              (sandwichedRenyiReferenceInner_posSemidef rho hsigma alpha)
              ⟨alpha, halpha_pos⟩)
            alpha) := by
  rw [sandwichedRenyiPSDReferenceHighAlphaFinite]
  rw [psdSchattenPNorm_rpow_eq_psdTracePower
    (sandwichedRenyiReferenceInner rho sigma alpha)
    (sandwichedRenyiReferenceInner_posSemidef rho hsigma alpha)
    halpha_pos]

/-- On the supported high-parameter branch, the PSD-reference divergence is the
usual Schatten-norm expression used before applying the Holder variational
formula. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_eq_schatten_log_of_supports
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma)
    {alpha : Real} (halpha : 1 < alpha) :
    sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma alpha =
      (alpha / (alpha - 1)) *
        log2
          (psdSchattenPNorm
            (sandwichedRenyiReferenceInner rho sigma alpha)
            (sandwichedRenyiReferenceInner_posSemidef rho hsigma alpha)
            ⟨alpha, lt_trans zero_lt_one halpha⟩) := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have htrace_pos :
      0 <
        psdTracePower
          (sandwichedRenyiReferenceInner rho sigma alpha)
          (sandwichedRenyiReferenceInner_posSemidef rho hsigma alpha)
          alpha :=
    sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports
      rho hsigma hSupport alpha
  have hnorm_pos :
      0 <
        psdSchattenPNorm
          (sandwichedRenyiReferenceInner rho sigma alpha)
          (sandwichedRenyiReferenceInner_posSemidef rho hsigma alpha)
          ⟨alpha, halpha_pos⟩ := by
    rw [psdSchattenPNorm, Internal.psdSchattenExpression]
    exact Real.rpow_pos_of_pos htrace_pos (1 / alpha)
  rw [sandwichedRenyiPSDReferenceHighAlphaFinite_eq_log2_psdSchattenPNorm_rpow
    rho hsigma halpha_pos]
  unfold log2
  have hlog :
      Real.log
          (Real.rpow
            (psdSchattenPNorm
              (sandwichedRenyiReferenceInner rho sigma alpha)
              (sandwichedRenyiReferenceInner_posSemidef rho hsigma alpha)
              ⟨alpha, halpha_pos⟩)
            alpha) =
        alpha *
          Real.log
            (psdSchattenPNorm
              (sandwichedRenyiReferenceInner rho sigma alpha)
              (sandwichedRenyiReferenceInner_posSemidef rho hsigma alpha)
              ⟨alpha, halpha_pos⟩) := by
    simpa using
      (Real.log_rpow hnorm_pos alpha)
  rw [hlog]
  ring

/-- A derivative-sign criterion specialized to the finite high-parameter
PSD-reference branch. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_mono_of_deriv_nonneg
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosSemidef)
    (hcont :
      ContinuousOn
        (fun alpha : Real =>
          sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma alpha)
        (Set.Ioi (1 : Real)))
    (hdiff :
      DifferentiableOn Real
        (fun alpha : Real =>
          sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma alpha)
        (Set.Ioi (1 : Real)))
    (hderiv :
      ∀ alpha : Real, 1 < alpha →
        0 ≤ deriv
          (fun beta : Real =>
            sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma beta)
          alpha)
    {alpha beta : {alpha : Real // 1 < alpha}} (hab : alpha.1 ≤ beta.1) :
    sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma alpha.1 ≤
      sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma beta.1 := by
  have hmono :
      MonotoneOn
        (fun alpha : Real =>
          sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma alpha)
        (Set.Ioi (1 : Real)) :=
    monotoneOn_Ioi_of_deriv_nonneg hcont hdiff hderiv
  exact hmono alpha.2 beta.2 hab

/-- On a positive-definite reference, finite-branch monotonicity lifts to the
support-aware high-parameter extended-real branch. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_mono_posDef_reference_of_finite_mono
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosDef)
    {alpha beta : {alpha : Real // 1 < alpha}}
    (hfinite :
      sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma.posSemidef alpha.1 ≤
        sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma.posSemidef beta.1) :
    sandwichedRenyiPSDReferenceHighAlphaE rho sigma hsigma.posSemidef alpha.1 ≤
      sandwichedRenyiPSDReferenceHighAlphaE rho sigma hsigma.posSemidef beta.1 := by
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      rho hsigma.posSemidef alpha.1
      (Matrix.Supports.of_right_posDef rho.matrix sigma hsigma),
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      rho hsigma.posSemidef beta.1
      (Matrix.Supports.of_right_posDef rho.matrix sigma hsigma)]
  exact EReal.coe_le_coe_iff.mpr hfinite

/-- On a positive-definite reference, derivative nonnegativity of the finite
branch gives monotonicity of the PSD-reference extended-real divergence. -/
theorem sandwichedRenyiPSDReferenceE_mono_posDef_reference_of_deriv_nonneg
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosDef)
    (hcont :
      ContinuousOn
        (fun alpha : Real =>
          sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma.posSemidef alpha)
        (Set.Ioi (1 : Real)))
    (hdiff :
      DifferentiableOn Real
        (fun alpha : Real =>
          sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma.posSemidef alpha)
        (Set.Ioi (1 : Real)))
    (hderiv :
      ∀ alpha : Real, 1 < alpha →
        0 ≤ deriv
          (fun beta : Real =>
            sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma.posSemidef beta)
          alpha)
    {alpha beta : {alpha : Real // 1 < alpha}} (hab : alpha.1 ≤ beta.1) :
    sandwichedRenyiPSDReferenceE rho sigma hsigma.posSemidef alpha.1 ≤
      sandwichedRenyiPSDReferenceE rho sigma hsigma.posSemidef beta.1 := by
  rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ alpha.2,
    sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ beta.2]
  exact
    sandwichedRenyiPSDReferenceHighAlphaE_mono_posDef_reference_of_finite_mono
      rho hsigma
      (sandwichedRenyiPSDReferenceHighAlphaFinite_mono_of_deriv_nonneg
        rho hsigma.posSemidef hcont hdiff hderiv hab)

/-- The support convention for the high-`alpha` EReal branch reduces
monotonicity to the finite supported branch. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_mono_of_finite_mono
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosSemidef)
    {alpha beta : {alpha : Real // 1 < alpha}}
    (hfinite :
      ∀ _hSupport : Matrix.Supports rho.matrix sigma,
        sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma alpha.1 ≤
          sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma beta.1) :
    sandwichedRenyiPSDReferenceHighAlphaE rho sigma hsigma alpha.1 ≤
      sandwichedRenyiPSDReferenceHighAlphaE rho sigma hsigma beta.1 := by
  by_cases hSupport : Matrix.Supports rho.matrix sigma
  · rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports rho hsigma alpha.1 hSupport,
      sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports rho hsigma beta.1 hSupport]
    exact EReal.coe_le_coe_iff.mpr (hfinite hSupport)
  · rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_top_of_not_supports rho hsigma alpha.1 hSupport,
      sandwichedRenyiPSDReferenceHighAlphaE_eq_top_of_not_supports rho hsigma beta.1 hSupport]

/-- High-`alpha` PSD-reference sandwiched-Renyi monotonicity in EReal follows
from the finite supported branch. -/
theorem sandwichedRenyiPSDReferenceE_mono_of_highAlphaFinite_mono
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosSemidef)
    {alpha beta : {alpha : Real // 1 < alpha}} (_hab : alpha.1 ≤ beta.1)
    (hfinite :
      ∀ _hSupport : Matrix.Supports rho.matrix sigma,
        sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma alpha.1 ≤
          sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma beta.1) :
    sandwichedRenyiPSDReferenceE rho sigma hsigma alpha.1 ≤
      sandwichedRenyiPSDReferenceE rho sigma hsigma beta.1 := by
  rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ alpha.2,
    sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ beta.2]
  exact sandwichedRenyiPSDReferenceHighAlphaE_mono_of_finite_mono
    rho hsigma hfinite

/-- The finite supported high-`alpha` branch is monotone once the same statement
is proved after compressing to the positive spectral support of the reference. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_mono_of_supportCompress_mono
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosSemidef)
    {alpha beta : {alpha : Real // 1 < alpha}}
    (hSupport : Matrix.Supports rho.matrix sigma)
    (hcompressed :
      sandwichedRenyiPSDReferenceHighAlphaFinite
          (psdSupportCompressedState rho hsigma hSupport)
          (psdSupportCompress sigma hsigma sigma)
          (psdSupportCompressedState_reference_posDef hsigma).posSemidef
          alpha.1 ≤
        sandwichedRenyiPSDReferenceHighAlphaFinite
          (psdSupportCompressedState rho hsigma hSupport)
          (psdSupportCompress sigma hsigma sigma)
          (psdSupportCompressedState_reference_posDef hsigma).posSemidef
          beta.1) :
    sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma alpha.1 ≤
      sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma beta.1 := by
  rw [sandwichedRenyiPSDReferenceHighAlphaFinite_supportCompress_eq
      rho hsigma hSupport alpha.1 alpha.2,
    sandwichedRenyiPSDReferenceHighAlphaFinite_supportCompress_eq
      rho hsigma hSupport beta.1 beta.2]
  exact hcompressed

/-- A side-information candidate inherits high-`alpha` monotonicity once the
finite supported branch of the underlying PSD-reference divergence is
monotone. -/
theorem sandwichedRenyiMutualInformationCandidateE_mono_of_highAlphaFinite_mono
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    {alpha beta : {alpha : Real // 1 < alpha}} (hab : alpha.1 ≤ beta.1)
    (hfinite :
      ∀ _hSupport : Matrix.Supports rhoAB.matrix (rhoAB.marginalA.prod sigmaB).matrix,
        sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
            (rhoAB.marginalA.prod sigmaB).matrix
            (rhoAB.marginalA.prod sigmaB).pos alpha.1 ≤
          sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
            (rhoAB.marginalA.prod sigmaB).matrix
            (rhoAB.marginalA.prod sigmaB).pos beta.1) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1 ≤
      rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB beta.1 := by
  simpa [State.sandwichedRenyiMutualInformationCandidateE_eq] using
    sandwichedRenyiPSDReferenceE_mono_of_highAlphaFinite_mono
      rhoAB (rhoAB.marginalA.prod sigmaB).pos hab hfinite

/-- A side-information candidate inherits high-`alpha` monotonicity from the
support-compressed finite branch. -/
theorem sandwichedRenyiMutualInformationCandidateE_mono_of_supportCompress_mono
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    {alpha beta : {alpha : Real // 1 < alpha}} (hab : alpha.1 ≤ beta.1)
    (hcompressed :
      ∀ hSupport : Matrix.Supports rhoAB.matrix (rhoAB.marginalA.prod sigmaB).matrix,
        sandwichedRenyiPSDReferenceHighAlphaFinite
            (psdSupportCompressedState rhoAB (rhoAB.marginalA.prod sigmaB).pos hSupport)
            (psdSupportCompress
              (rhoAB.marginalA.prod sigmaB).matrix
              (rhoAB.marginalA.prod sigmaB).pos
              (rhoAB.marginalA.prod sigmaB).matrix)
            (psdSupportCompressedState_reference_posDef
              (rhoAB.marginalA.prod sigmaB).pos).posSemidef
            alpha.1 ≤
          sandwichedRenyiPSDReferenceHighAlphaFinite
            (psdSupportCompressedState rhoAB (rhoAB.marginalA.prod sigmaB).pos hSupport)
            (psdSupportCompress
              (rhoAB.marginalA.prod sigmaB).matrix
              (rhoAB.marginalA.prod sigmaB).pos
              (rhoAB.marginalA.prod sigmaB).matrix)
            (psdSupportCompressedState_reference_posDef
              (rhoAB.marginalA.prod sigmaB).pos).posSemidef
            beta.1) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1 ≤
      rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB beta.1 := by
  refine
    rhoAB.sandwichedRenyiMutualInformationCandidateE_mono_of_highAlphaFinite_mono
      sigmaB hab ?_
  intro hSupport
  exact
    sandwichedRenyiPSDReferenceHighAlphaFinite_mono_of_supportCompress_mono
      rhoAB (rhoAB.marginalA.prod sigmaB).pos hSupport (hcompressed hSupport)

/-- State optimized high-`alpha` monotonicity from the support-compressed
finite branch of sandwiched-Renyi monotonicity. -/
theorem sandwichedRenyiMutualInformationE_mono_of_supportCompress_mono
    (rhoAB : State (Prod a b))
    (hcompressed :
      ∀ sigmaB : State b, ∀ alpha beta : {alpha : Real // 1 < alpha},
        alpha.1 ≤ beta.1 →
          ∀ hSupport : Matrix.Supports rhoAB.matrix (rhoAB.marginalA.prod sigmaB).matrix,
            sandwichedRenyiPSDReferenceHighAlphaFinite
                (psdSupportCompressedState
                  rhoAB (rhoAB.marginalA.prod sigmaB).pos hSupport)
                (psdSupportCompress
                  (rhoAB.marginalA.prod sigmaB).matrix
                  (rhoAB.marginalA.prod sigmaB).pos
                  (rhoAB.marginalA.prod sigmaB).matrix)
                (psdSupportCompressedState_reference_posDef
                  (rhoAB.marginalA.prod sigmaB).pos).posSemidef
                alpha.1 ≤
              sandwichedRenyiPSDReferenceHighAlphaFinite
                (psdSupportCompressedState
                  rhoAB (rhoAB.marginalA.prod sigmaB).pos hSupport)
                (psdSupportCompress
                  (rhoAB.marginalA.prod sigmaB).matrix
                  (rhoAB.marginalA.prod sigmaB).pos
                  (rhoAB.marginalA.prod sigmaB).matrix)
                (psdSupportCompressedState_reference_posDef
                  (rhoAB.marginalA.prod sigmaB).pos).posSemidef
                beta.1) :
    ∀ alpha beta : {alpha : Real // 1 < alpha},
      alpha.1 ≤ beta.1 →
        rhoAB.sandwichedRenyiMutualInformationE alpha.1 ≤
          rhoAB.sandwichedRenyiMutualInformationE beta.1 := by
  haveI : Nonempty b := by
    rcases rhoAB.nonempty with ⟨h⟩
    exact ⟨h.2⟩
  refine rhoAB.sandwichedRenyiMutualInformationE_mono_of_candidate_mono ?_
  intro sigmaB alpha beta hab
  exact
    rhoAB.sandwichedRenyiMutualInformationCandidateE_mono_of_supportCompress_mono
      sigmaB hab (hcompressed sigmaB alpha beta hab)

/-- For a full-rank product reference `rho_A ⊗ sigma_B`, derivative
nonnegativity of the finite branch gives monotonicity of the fixed
side-information candidate. -/
theorem sandwichedRenyiMutualInformationCandidateE_mono_posDef_reference_of_deriv_nonneg
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    (hrhoA : rhoAB.marginalA.matrix.PosDef) (hsigmaB : sigmaB.matrix.PosDef)
    (hcont :
      ContinuousOn
        (fun alpha : Real =>
          sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
            (rhoAB.marginalA.prod sigmaB).matrix
            (rhoAB.marginalA.prod sigmaB).pos alpha)
        (Set.Ioi (1 : Real)))
    (hdiff :
      DifferentiableOn Real
        (fun alpha : Real =>
          sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
            (rhoAB.marginalA.prod sigmaB).matrix
            (rhoAB.marginalA.prod sigmaB).pos alpha)
        (Set.Ioi (1 : Real)))
    (hderiv :
      ∀ alpha : Real, 1 < alpha →
        0 ≤ deriv
          (fun beta : Real =>
            sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
              (rhoAB.marginalA.prod sigmaB).matrix
              (rhoAB.marginalA.prod sigmaB).pos beta)
          alpha)
    {alpha beta : {alpha : Real // 1 < alpha}} (hab : alpha.1 ≤ beta.1) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1 ≤
      rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB beta.1 := by
  have href : (rhoAB.marginalA.prod sigmaB).matrix.PosDef :=
    State.prod_posDef hrhoA hsigmaB
  simpa [sandwichedRenyiMutualInformationCandidateE_eq] using
    sandwichedRenyiPSDReferenceE_mono_posDef_reference_of_deriv_nonneg
      rhoAB href hcont hdiff hderiv hab

/-- If the optimized side-state infimum has been restricted to full-rank side
states, monotonicity of every full-rank fixed candidate gives monotonicity of
the optimized state quantity. -/
theorem sandwichedRenyiMutualInformationE_mono_of_iInf_posDef_candidates_and_candidate_mono
    (rhoAB : State (Prod a b))
    (hfullRankInf :
      ∀ gamma : {gamma : Real // 1 < gamma},
        rhoAB.sandwichedRenyiMutualInformationE gamma.1 =
          ⨅ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB.1 gamma.1)
    (hmono :
      ∀ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        ∀ alpha beta : {alpha : Real // 1 < alpha},
          alpha.1 ≤ beta.1 →
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha.1 ≤
              rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB.1 beta.1) :
    ∀ alpha beta : {alpha : Real // 1 < alpha},
      alpha.1 ≤ beta.1 →
        rhoAB.sandwichedRenyiMutualInformationE alpha.1 ≤
          rhoAB.sandwichedRenyiMutualInformationE beta.1 := by
  intro alpha beta hab
  rw [hfullRankInf alpha, hfullRankInf beta]
  refine le_iInf fun sigmaB => ?_
  exact (iInf_le
    (fun tauB : {tauB : State b // tauB.matrix.PosDef} =>
      rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha.1)
    sigmaB).trans (hmono sigmaB alpha beta hab)

/-- Full-rank optimized monotonicity from derivative nonnegativity of each
full-rank fixed-candidate finite branch. -/
theorem sandwichedRenyiMutualInformationE_mono_of_iInf_posDef_candidates_and_deriv_nonneg
    (rhoAB : State (Prod a b)) (hrhoA : rhoAB.marginalA.matrix.PosDef)
    (hfullRankInf :
      ∀ gamma : {gamma : Real // 1 < gamma},
        rhoAB.sandwichedRenyiMutualInformationE gamma.1 =
          ⨅ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB.1 gamma.1)
    (hcont :
      ∀ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        ContinuousOn
          (fun alpha : Real =>
            sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
              (rhoAB.marginalA.prod sigmaB.1).matrix
              (rhoAB.marginalA.prod sigmaB.1).pos alpha)
          (Set.Ioi (1 : Real)))
    (hdiff :
      ∀ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        DifferentiableOn Real
          (fun alpha : Real =>
            sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
              (rhoAB.marginalA.prod sigmaB.1).matrix
              (rhoAB.marginalA.prod sigmaB.1).pos alpha)
          (Set.Ioi (1 : Real)))
    (hderiv :
      ∀ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        ∀ alpha : Real, 1 < alpha →
          0 ≤ deriv
            (fun beta : Real =>
              sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
                (rhoAB.marginalA.prod sigmaB.1).matrix
                (rhoAB.marginalA.prod sigmaB.1).pos beta)
            alpha) :
    ∀ alpha beta : {alpha : Real // 1 < alpha},
      alpha.1 ≤ beta.1 →
        rhoAB.sandwichedRenyiMutualInformationE alpha.1 ≤
          rhoAB.sandwichedRenyiMutualInformationE beta.1 := by
  refine
    sandwichedRenyiMutualInformationE_mono_of_iInf_posDef_candidates_and_candidate_mono
      rhoAB hfullRankInf ?_
  intro sigmaB alpha beta hab
  exact
    sandwichedRenyiMutualInformationCandidateE_mono_posDef_reference_of_deriv_nonneg
      rhoAB sigmaB.1 hrhoA sigmaB.2 (hcont sigmaB) (hdiff sigmaB)
      (hderiv sigmaB) hab

/-! ## A1.1: KW variational-formula bridge — smooth (PosDef) reference case

This section implements the Khatri--Wilde variational-formula route to
`α`-monotonicity of `sandwichedRenyiPSDReferenceHighAlphaFinite` for `1 < α` on
positive-definite references. The route is `entropies.tex:2059–2072` (variational
formula over the α-independent fixed-trace set) combined with `2347–2351`
(Choi--Jamiołkowski vectorization of the per-`τ` trace objective).

The α-dependence lives entirely in the objective exponent `γ = (1 - α) / α` on
`X_τ = τ⁻¹ ⊗ σᵀ`; the constraint set `{τ : CMatrix a // τ.PosDef ∧ τ.trace.re = 1}`
is α-independent, as required by the source spec (no α-dependent unit-ball shortcut). -/


/-- Entrywise conjugation commutes with real powers on positive-definite
matrices for arbitrary real exponents.

This is the `PosDef` analog of `cMatrix_rpow_map_star_nonneg` and is needed
because the per-`τ` objective exponent `γ = (1 - α) / α` is negative for
`α > 1`. -/
private theorem cMatrix_rpow_map_star_posDef_a1
    {A : CMatrix a} (hA : A.PosDef) (s : ℝ) :
    CFC.rpow (A.map star) s = (CFC.rpow A s).map star := by
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
  have hmap_eq : A.map star = A.transpose :=
    cMatrix_map_star_eq_transpose_of_posSemidef hA.posSemidef
  have hmap_nonneg : 0 ≤ A.map star := by
    rw [hmap_eq]
    exact Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef.transpose
  change (A.map star) ^ s = (A ^ s).map star
  rw [CFC.rpow_eq_cfc_real (a := A.map star) (y := s) hmap_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s) hA_nonneg]
  simpa [cMatrixConjStarAlgEquiv] using
    (StarAlgHomClass.map_cfc
      (cMatrixConjStarAlgEquiv (a := a))
      (fun x : ℝ => x ^ s) A
      (hf := by
        intro x hx
        exact (Real.continuousAt_rpow_const x s
          (.inl (ne_of_gt
            ((Matrix.PosDef.isStrictlyPositive hA).spectrum_pos hx)))).continuousWithinAt)
      (hφ := by
        change Continuous fun A : CMatrix a => A.map star
        fun_prop)
      (hφa := by
        change IsSelfAdjoint (A.map star)
        rw [hmap_eq]
        exact hA.posSemidef.transpose.isHermitian)).symm

/-- Real powers commute with transpose on positive-definite matrices for any
real exponent. This is the `PosDef` analog of `cMatrix_rpow_transpose_nonneg`. -/
private theorem cMatrix_rpow_transpose_posDef_a1
    {A : CMatrix a} (hA : A.PosDef) (s : ℝ) :
    CFC.rpow A.transpose s = (CFC.rpow A s).transpose := by
  have hmapA : A.map star = A.transpose :=
    cMatrix_map_star_eq_transpose_of_posSemidef hA.posSemidef
  have hpowmap : CFC.rpow (A.map star) s = (CFC.rpow A s).map star :=
    cMatrix_rpow_map_star_posDef_a1 hA s
  have hpowPD : (CFC.rpow A s).PosDef := cMatrix_rpow_posDef_of_posDef hA s
  have hpowmapTranspose :
      (CFC.rpow A s).map star = (CFC.rpow A s).transpose :=
    cMatrix_map_star_eq_transpose_of_posSemidef hpowPD.posSemidef
  rw [← hmapA, hpowmap, hpowmapTranspose]

/-- The rank-one purification projector `|φ^ρ⟩⟨φ^ρ|` on the doubled system,
the vector-matrix form of `ρ.sqrtMatrix`.

This is the Khatri--Wilde vectorization `|φ^ρ⟩ = (ρ^{1/2} ⊗ I)|Γ⟩` of
`entropies.tex:2350`, packaged as a matrix on `a × a`. -/
def kwPurificationStateMatrix (ρ : State a) : CMatrix (a × a) :=
  cMatrixVecWeight ρ.sqrtMatrix

theorem kwPurificationStateMatrix_posSemidef (ρ : State a) :
    (kwPurificationStateMatrix ρ).PosSemidef :=
  cMatrixVecWeight_posSemidef ρ.sqrtMatrix

/-- The purification projector has trace one because
`Tr[|φ^ρ⟩⟨φ^ρ|] = ⟨φ^ρ|φ^ρ⟩ = Tr[(ρ^{1/2})† ρ^{1/2}] = Tr ρ = 1`.

The calculation uses the Epstein identity
`Tr[star K · A · K · B] = Tr[cMatrixVecWeight K · (A ⊗ Bᵀ)]` with `A = B = 1`,
which reduces `Tr[cMatrixVecWeight K]` to `Tr[star K · K]`. -/
theorem kwPurificationStateMatrix_trace_eq_one (ρ : State a) :
    (kwPurificationStateMatrix ρ).trace = 1 := by
  have hK_herm : ρ.sqrtMatrix.IsHermitian := ρ.sqrtMatrix_isHermitian
  have hstarK : star ρ.sqrtMatrix = ρ.sqrtMatrix := hK_herm.eq
  have hK_sq : ρ.sqrtMatrix * ρ.sqrtMatrix = ρ.matrix := ρ.sqrtMatrix_mul_self
  -- Epstein with `A = B = 1` gives
  -- `(star K * 1 * K * 1).trace = (cMatrixVecWeight K * kronecker 1 1ᵀ).trace`.
  -- We then simplify `kronecker 1 1ᵀ = kronecker 1 1 = 1` and read off the trace.
  have hep := epstein_traceTerm_tensor_trace_transpose ρ.sqrtMatrix
    (1 : CMatrix a) (1 : CMatrix a)
  simp only [Matrix.mul_one,
    show (1 : CMatrix a).transpose = 1 from Matrix.transpose_one] at hep
  have hK1K1 : Matrix.kronecker (1 : CMatrix a) (1 : CMatrix a) =
      (1 : CMatrix (a × a)) := by
    simp [Matrix.kronecker]
  rw [hK1K1, Matrix.mul_one, hstarK, hK_sq, ρ.trace_eq_one] at hep
  exact hep.symm

/-- The rank-one purification state `|φ^ρ⟩⟨φ^ρ|` on `a × a`, packaged as a
`State` for direct application of `kw_state_rpowTrace_alphaObjective_mono`. -/
def kwPurificationState (ρ : State a) : State (a × a) where
  matrix := kwPurificationStateMatrix ρ
  pos := kwPurificationStateMatrix_posSemidef ρ
  trace_eq_one := kwPurificationStateMatrix_trace_eq_one ρ

@[simp]
theorem kwPurificationState_matrix (ρ : State a) :
    (kwPurificationState ρ).matrix = kwPurificationStateMatrix ρ :=
  rfl

/-- Khatri--Wilde vectorization identity (`entropies.tex:2347–2351`).

For positive-definite `σ, τ` and any real `γ`, the per-`τ` Rényi trace
objective `Tr[ρ^{1/2} σ^γ ρ^{1/2} τ^{-γ}]` is rewritten via Choi--Jamiołkowski
vectorization as the vector-state expectation
`Tr[|φ^ρ⟩⟨φ^ρ| (τ⁻¹ ⊗ σᵀ)^γ]`. This is the per-`τ` rewrite that lets
`kw_state_rpowTrace_alphaObjective_mono` (the operator-Jensen step) apply
directly. -/
theorem kw_vectorization_eq
    (ρ : State a) {σ τ : CMatrix a} (hσ : σ.PosDef) (hτ : τ.PosDef)
    {γ : ℝ} :
    ((ρ.sqrtMatrix * CFC.rpow σ γ * ρ.sqrtMatrix *
        CFC.rpow τ (-γ)).trace).re =
      ((kwPurificationStateMatrix ρ *
        CFC.rpow (Matrix.kronecker τ⁻¹ σ.transpose) γ).trace).re := by
  have hτ_inv : (τ⁻¹ : CMatrix a).PosDef := hτ.inv
  have hσT : σ.transpose.PosDef := hσ.transpose
  -- Expand `(τ⁻¹ ⊗ σᵀ)^γ = τ^{-γ} ⊗ (σ^γ)ᵀ` via PosDef Kronecker + transpose.
  have hKron_rpow :
      CFC.rpow (Matrix.kronecker τ⁻¹ σ.transpose) γ =
        Matrix.kronecker (CFC.rpow τ (-γ)) (CFC.rpow σ γ).transpose := by
    rw [cMatrix_rpow_kronecker_posDef hτ_inv hσT γ]
    rw [cMatrix_rpow_nonsing_inv_eq_rpow_neg hτ γ]
    rw [cMatrix_rpow_transpose_posDef_a1 hσ γ]
  unfold kwPurificationStateMatrix
  rw [hKron_rpow]
  -- Apply the Epstein identity in reverse.
  rw [← epstein_traceTerm_tensor_trace_transpose_re ρ.sqrtMatrix
    (CFC.rpow τ (-γ)) (CFC.rpow σ γ)]
  -- After Epstein, the RHS becomes
  -- `Tr[star(ρ^{1/2}) · τ^{-γ} · ρ^{1/2} · σ^γ]`; using Hermiticity and two
  -- cyclic permutations, this matches the LHS `Tr[ρ^{1/2} · σ^γ · ρ^{1/2} · τ^{-γ}]`.
  rw [show star ρ.sqrtMatrix = ρ.sqrtMatrix from ρ.sqrtMatrix_isHermitian.eq]
  -- Two cyclic permutations carry `(ρ^{1/2} τ^{-γ} ρ^{1/2} σ^γ).trace` to
  -- `(ρ^{1/2} σ^γ ρ^{1/2} τ^{-γ}).trace`.
  apply congrArg Complex.re
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]

/-- The `1 < α` slice of `kw_vectorization_eq`, expressed in the
`(1 - α) / α` exponent convention used by `sandwichedRenyiPSDReferenceHighAlphaFinite`. -/
theorem kw_vectorization_eq_highAlpha
    (ρ : State a) {σ τ : CMatrix a} (hσ : σ.PosDef) (hτ : τ.PosDef)
    {α : ℝ} :
    ((ρ.sqrtMatrix * CFC.rpow σ ((1 - α) / α) * ρ.sqrtMatrix *
        CFC.rpow τ ((α - 1) / α)).trace).re =
      ((kwPurificationStateMatrix ρ *
        CFC.rpow (Matrix.kronecker τ⁻¹ σ.transpose) ((1 - α) / α)).trace).re := by
  have hγ : -((1 - α) / α) = (α - 1) / α := by ring
  rw [← hγ]
  exact kw_vectorization_eq ρ hσ hτ (γ := (1 - α) / α)

/-- Reparametrized PSD Schatten variational formula over the fixed-trace plane.

For `p > 1` with Hölder conjugate `q` and **positive-definite** `M`, the PSD
Schatten `p`-expression of `M` is the supremum of `Tr[M · τ^{1/q}]` over
positive-definite `τ` with `Tr τ = 1`. This is the KW source form
`entropies.tex:2059` (with `τ > 0` read as positive-definite, the source's
strict-positivity convention), obtained from the existing
`psdTraceReverseHolderOptimizer` for the lower bound — the optimizer
`M^p / Tr M^p` is positive-definite whenever `M` is. The PSD-but-singular `M`
extension is the A1.2 deliverable. -/
theorem psdSchattenPNorm_eq_iSup_posDef_fixedTrace_of_posDef
    {M : CMatrix a} (hM : M.PosSemidef) (hMPD : M.PosDef)
    {p q : ℝ} (hpq : p.HolderConjugate q) (hp1 : 1 < p) [Nonempty a] :
    psdSchattenPNorm M hM ⟨p, lt_trans zero_lt_one hp1⟩ =
      ⨆ τ : {τ : CMatrix a // τ.PosDef ∧ τ.trace.re = 1},
        ((M * CFC.rpow τ.1 (1 / q)).trace).re := by
  classical
  have hp_pos : 0 < p := lt_trans zero_lt_one hp1
  -- Upper bound: every PD fixed-trace candidate value is ≤ Schatten norm.
  have hupper :
      ∀ τ : {τ : CMatrix a // τ.PosDef ∧ τ.trace.re = 1},
        ((M * CFC.rpow τ.1 (1 / q)).trace).re ≤
          psdSchattenPNorm M hM ⟨p, hp_pos⟩ := by
    intro τ
    exact psd_trace_rpow_holder_variational_upper hM τ.2.1.posSemidef τ.2.2 hpq rfl
  -- Lower bound: τ* = M^p / Tr M^p is positive-definite and attains the supremum.
  have hMne : M ≠ 0 := by
    intro hMzero
    have htr_pos : 0 < M.trace := hMPD.trace_pos
    rw [hMzero] at htr_pos
    simp [Matrix.trace_zero] at htr_pos
  have hSpos : 0 < psdTracePower M hM p :=
    psdTracePower_pos_of_ne_zero M hM hMne
  have hτstar_PD : (psdTraceReverseHolderOptimizer M hM p).PosDef :=
    psdTraceReverseHolderOptimizer_posDef_of_posDef hM hMPD hSpos
  rcases psdTraceReverseHolderOptimizer_props hM hp_pos hSpos with
    ⟨_, hτstar_tr, _, hτstar_val⟩
  -- Rewrite `1/q = 1 - 1/p` via the high-α Holder conjugacy identity.
  have h_one_div_q : 1 / q = 1 - 1 / p := by
    have hq_eq : q = p / (p - 1) :=
      (Real.holderConjugate_iff_eq_conjExponent hp1).mp hpq
    rw [hq_eq]
    field_simp
  let τstar : {τ : CMatrix a // τ.PosDef ∧ τ.trace.re = 1} :=
    ⟨psdTraceReverseHolderOptimizer M hM p, hτstar_PD, hτstar_tr⟩
  haveI : Nonempty {τ : CMatrix a // τ.PosDef ∧ τ.trace.re = 1} := ⟨τstar⟩
  refine le_antisymm ?_ ?_
  · -- psdSchattenPNorm ≤ ⨆ τ, (M * CFC.rpow τ.1 (1 / q)).trace.re
    have hbdd : BddAbove (Set.range fun τ :
        {τ : CMatrix a // τ.PosDef ∧ τ.trace.re = 1} =>
          ((M * CFC.rpow τ.1 (1 / q)).trace).re) :=
      ⟨psdSchattenPNorm M hM ⟨p, hp_pos⟩, by
        rintro _ ⟨τ, rfl⟩
        exact hupper τ⟩
    rw [hτstar_val, ← h_one_div_q]
    exact le_ciSup hbdd τstar
  · -- ⨆ τ, (M * CFC.rpow τ.1 (1 / q)).trace.re ≤ psdSchattenPNorm
    exact ciSup_le hupper

/-- Sup/log/scale commutation when the supremum is achieved.

For `c > 0`, `0 < v i`, and `v τstar` the greatest value of `v`, the identity
`c * log2 (iSup v) = iSup (fun i => c * log2 (v i))` holds because `log2` is
monotone increasing on `(0, ∞)` and the greatest element is preserved by
composition with `log2` and by multiplication by a positive scalar. This is
the helper that closes the A1.1-assembly sup/log/scale step when the
variational-formula optimizer `τ*` achieves the supremum. -/
theorem real_mul_log2_iSup_eq_iSup_mul_log2_of_isGreatest
    {ι : Sort*} [Nonempty ι] {c : ℝ} (hc : 0 < c)
    {v : ι → ℝ} (hpos : ∀ i, 0 < v i)
    {τstar : ι} (h_greatest : IsGreatest (Set.range v) (v τstar)) :
    c * log2 (iSup v) = iSup (fun i => c * log2 (v i)) := by
  -- `log2` monotonicity on `(0, ∞)` is a local special-case of `Real.log_le_log`.
  have hlog2_mono : ∀ {x y : ℝ}, 0 < x → x ≤ y → log2 x ≤ log2 y := by
    intros x y hx hxy
    unfold log2
    exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
      (le_of_lt (Real.log_pos one_lt_two))
  rcases h_greatest with ⟨h_mem, h_le⟩
  have h_ub : ∀ i, v i ≤ v τstar := by
    have hle := mem_upperBounds.mp h_le
    intro i
    exact hle (v i) ⟨i, rfl⟩
  -- `iSup v = v τstar` because the supremum is achieved at τstar.
  have h_iSup_eq : iSup v = v τstar := IsGreatest.csSup_eq ⟨h_mem, h_le⟩
  rw [h_iSup_eq]
  -- Pull `IsGreatest` through `log2` (monotone on positive reals).
  have h_log_greatest :
      IsGreatest (Set.range (fun i => log2 (v i))) (log2 (v τstar)) := by
    refine ⟨⟨τstar, rfl⟩, ?_⟩
    rw [mem_upperBounds]
    rintro y ⟨i, rfl⟩
    exact hlog2_mono (hpos i) (h_ub i)
  have h_log_iSup_eq : iSup (fun i => log2 (v i)) = log2 (v τstar) :=
    h_log_greatest.csSup_eq
  rcases h_log_greatest with ⟨hlog_mem, hlog_le⟩
  have hlog_ub : ∀ i, log2 (v i) ≤ log2 (v τstar) := by
    have hle := mem_upperBounds.mp hlog_le
    intro i
    exact hle _ ⟨i, rfl⟩
  -- Pull `IsGreatest` through multiplication by `c > 0`.
  have h_clog_greatest :
      IsGreatest (Set.range (fun i => c * log2 (v i))) (c * log2 (v τstar)) := by
    refine ⟨⟨τstar, rfl⟩, mem_upperBounds.mpr ?_⟩
    rintro y ⟨i, rfl⟩
    exact mul_le_mul_of_nonneg_left (hlog_ub i) (le_of_lt hc)
  -- Convert `iSup` (which is `sSup (range _)`) to the `sSup` form so the
  -- `csSup_eq` rewrite can fire.
  show c * log2 (v τstar) = sSup (Set.range fun i => c * log2 (v i))
  rw [h_clog_greatest.csSup_eq]

/-- Smooth-case α-monotonicity of `sandwichedRenyiPSDReferenceHighAlphaFinite`
(positive-definite `σ` and `ρ.matrix`).

Combines iso-spectrality (`psdTracePower_mul_comm`), the fixed-trace
variational formula, CJ vectorization, the sup-log commutation, and per-τ
monotonicity from `kw_state_rpowTrace_alphaObjective_mono`. All intermediate
steps are inlined as tactic-mode `have` bindings to avoid statement-level
elaboration timeouts. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_mono_posDef_reference_posDef_state
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosDef) (hρ : ρ.matrix.PosDef)
    {α β : ℝ} (hα : 1 < α) (hβ : 1 < β) (hab : α ≤ β) :
    sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef α ≤
      sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef β := by
  haveI : Nonempty a := ρ.nonempty
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hβ_pos : 0 < β := lt_trans zero_lt_one hβ
  let ι := {τ : CMatrix a // τ.PosDef ∧ τ.trace.re = 1}
  have hSupport : Matrix.Supports ρ.matrix σ :=
    Matrix.Supports.of_right_posDef ρ.matrix σ hσ
  have hM'pd : ∀ γ : ℝ, (ρ.sqrtMatrix * CFC.rpow σ ((1 - γ) / γ) * ρ.sqrtMatrix).PosDef := by
    intro γ
    have hσpowPD : (CFC.rpow σ ((1 - γ) / γ)).PosDef :=
      cMatrix_rpow_posDef_of_posDef hσ ((1 - γ) / γ)
    have hSqrtPD : ρ.sqrtMatrix.PosDef := by
      have hS : ρ.sqrtMatrix = CFC.rpow ρ.matrix (1 / 2 : ℝ) := by
        simp [State.sqrtMatrix, psdSqrt, CFC.sqrt_eq_rpow]
      rw [hS]
      exact cMatrix_rpow_posDef_of_posDef hρ (1 / 2 : ℝ)
    have hSinj : Function.Injective ρ.sqrtMatrix.vecMul :=
      Matrix.vecMul_injective_of_isUnit hSqrtPD.isUnit
    simpa only [ρ.sqrtMatrix_isHermitian.eq] using
      hσpowPD.mul_mul_conjTranspose_same (B := ρ.sqrtMatrix) hSinj
  have hiso : ∀ γ : ℝ, 1 < γ →
      psdTracePower (sandwichedRenyiReferenceInner ρ σ γ)
        (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef γ) γ =
      psdTracePower (ρ.sqrtMatrix * CFC.rpow σ ((1 - γ) / γ) * ρ.sqrtMatrix)
        (by
          have hσpowPD : (CFC.rpow σ ((1 - γ) / γ)).PosSemidef :=
            cMatrix_rpow_posSemidef (A := σ) (s := (1 - γ) / γ) hσ.posSemidef
          simpa only [ρ.sqrtMatrix_isHermitian.eq] using
            hσpowPD.mul_mul_conjTranspose_same ρ.sqrtMatrix) γ := by
    intro γ hγ
    have hp_pos : 0 < γ := lt_trans zero_lt_one hγ
    let s : ℝ := (1 - γ) / (2 * γ)
    have h2s_eq : 2 * s = (1 - γ) / γ := by dsimp [s]; ring
    have hσss : CFC.rpow σ s * CFC.rpow σ s = CFC.rpow σ (2 * s) := by
      have hss : s + s = 2 * s := by ring
      have hrpow : CFC.rpow σ (s + s) = CFC.rpow σ s * CFC.rpow σ s :=
        CFC.rpow_add (a := σ) (x := s) (y := s) hσ.isUnit
      rw [hss] at hrpow
      exact hrpow.symm
    have hρ_sq : ρ.sqrtMatrix * ρ.sqrtMatrix = ρ.matrix := ρ.sqrtMatrix_mul_self
    have hAB :
        (CFC.rpow σ s * ρ.sqrtMatrix) * (ρ.sqrtMatrix * CFC.rpow σ s) =
          sandwichedRenyiReferenceInner ρ σ γ := by
      have key : ρ.sqrtMatrix * (ρ.sqrtMatrix * CFC.rpow σ s) =
          (ρ.sqrtMatrix * ρ.sqrtMatrix) * CFC.rpow σ s := by
        rw [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc, key, hρ_sq, ← Matrix.mul_assoc]
      rfl
    have h_inner :
        CFC.rpow σ s * (CFC.rpow σ s * ρ.sqrtMatrix) =
          CFC.rpow σ (2 * s) * ρ.sqrtMatrix := by
      rw [← Matrix.mul_assoc, hσss]
    have hBA :
        (ρ.sqrtMatrix * CFC.rpow σ s) * (CFC.rpow σ s * ρ.sqrtMatrix) =
          ρ.sqrtMatrix * CFC.rpow σ ((1 - γ) / γ) * ρ.sqrtMatrix := by
      rw [Matrix.mul_assoc, h_inner, ← Matrix.mul_assoc, h2s_eq]
    have hAB_psd :
        ((CFC.rpow σ s * ρ.sqrtMatrix) * (ρ.sqrtMatrix * CFC.rpow σ s)).PosSemidef := by
      rw [hAB]; exact sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef γ
    have hBA_psd :
        ((ρ.sqrtMatrix * CFC.rpow σ s) * (CFC.rpow σ s * ρ.sqrtMatrix)).PosSemidef := by
      rw [hBA]
      have hσpowPD : (CFC.rpow σ ((1 - γ) / γ)).PosSemidef :=
        cMatrix_rpow_posSemidef (A := σ) (s := (1 - γ) / γ) hσ.posSemidef
      simpa only [ρ.sqrtMatrix_isHermitian.eq] using
        hσpowPD.mul_mul_conjTranspose_same ρ.sqrtMatrix
    have hcomm := psdTracePower_mul_comm hAB_psd hBA_psd hp_pos
    convert hcomm using 2
    · exact hAB.symm
    · exact hBA.symm
  have hhc : ∀ γ : ℝ, 1 < γ → γ.HolderConjugate (γ / (γ - 1)) :=
    fun γ hγ => highAlpha_holderConjugate hγ
  have h_one_div_q : ∀ γ : ℝ, 1 < γ → 1 / (γ / (γ - 1)) = (γ - 1) / γ := by
    intro γ hγ
    field_simp
  have hSpos : ∀ γ : ℝ, 1 < γ →
      0 < psdTracePower (ρ.sqrtMatrix * CFC.rpow σ ((1 - γ) / γ) * ρ.sqrtMatrix)
        (hM'pd γ).posSemidef γ := by
    intro γ hγ
    exact psdTracePower_pos_of_ne_zero _ (hM'pd γ).posSemidef
      (by intro h; have := (hM'pd γ).trace_pos; rw [h] at this; simp [Matrix.trace_zero] at this)
  have hτstar_pd : ∀ γ : ℝ, 1 < γ →
      (psdTraceReverseHolderOptimizer
        (ρ.sqrtMatrix * CFC.rpow σ ((1 - γ) / γ) * ρ.sqrtMatrix)
        (hM'pd γ).posSemidef γ).PosDef := by
    intro γ hγ
    exact psdTraceReverseHolderOptimizer_posDef_of_posDef _ (hM'pd γ) (hSpos γ hγ)
  have hτstar_props : ∀ γ : ℝ, (hγ : 1 < γ) →
      ∃ _hN : (psdTraceReverseHolderOptimizer
        (ρ.sqrtMatrix * CFC.rpow σ ((1 - γ) / γ) * ρ.sqrtMatrix)
        (hM'pd γ).posSemidef γ).PosSemidef,
        (psdTraceReverseHolderOptimizer
          (ρ.sqrtMatrix * CFC.rpow σ ((1 - γ) / γ) * ρ.sqrtMatrix)
          (hM'pd γ).posSemidef γ).trace.re = 1 ∧
          Matrix.Supports
            (ρ.sqrtMatrix * CFC.rpow σ ((1 - γ) / γ) * ρ.sqrtMatrix)
            (psdTraceReverseHolderOptimizer
              (ρ.sqrtMatrix * CFC.rpow σ ((1 - γ) / γ) * ρ.sqrtMatrix)
              (hM'pd γ).posSemidef γ) ∧
            psdSchattenPNorm (ρ.sqrtMatrix * CFC.rpow σ ((1 - γ) / γ) * ρ.sqrtMatrix)
              (hM'pd γ).posSemidef ⟨γ, lt_trans zero_lt_one hγ⟩ =
              ((ρ.sqrtMatrix * CFC.rpow σ ((1 - γ) / γ) * ρ.sqrtMatrix *
                CFC.rpow (psdTraceReverseHolderOptimizer
                  (ρ.sqrtMatrix * CFC.rpow σ ((1 - γ) / γ) * ρ.sqrtMatrix)
                  (hM'pd γ).posSemidef γ) (1 - 1 / γ)).trace).re := by
    intro γ hγ
    exact psdTraceReverseHolderOptimizer_props (hM'pd γ).posSemidef
      (lt_trans zero_lt_one hγ) (hSpos γ hγ)
  have hD_eq : ∀ γ : {γ : ℝ // 1 < γ},
      sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef γ.1 =
        ⨆ τ : ι, (γ.1 / (γ.1 - 1)) *
          log2 ((kwPurificationStateMatrix ρ *
            CFC.rpow (Matrix.kronecker τ.1⁻¹ σ.transpose) ((1 - γ.1) / γ.1)).trace).re := by
    intro γ
    have hγ : 1 < γ.1 := γ.2
    have hγ_pos : 0 < γ.1 := lt_trans zero_lt_one hγ
    rw [sandwichedRenyiPSDReferenceHighAlphaFinite_eq_schatten_log_of_supports
        ρ hσ.posSemidef hSupport hγ]
    have hM'psd : (ρ.sqrtMatrix * CFC.rpow σ ((1 - γ.1) / γ.1) * ρ.sqrtMatrix).PosSemidef :=
      (hM'pd γ.1).posSemidef
    have htrace_eq := hiso γ.1 hγ
    have hnorm_eq :
        psdSchattenPNorm (sandwichedRenyiReferenceInner ρ σ γ.1)
          (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef γ.1)
          ⟨γ.1, hγ_pos⟩ =
        psdSchattenPNorm (ρ.sqrtMatrix * CFC.rpow σ ((1 - γ.1) / γ.1) * ρ.sqrtMatrix)
          hM'psd ⟨γ.1, hγ_pos⟩ := by
      unfold psdSchattenPNorm Internal.psdSchattenExpression
      rw [htrace_eq]
    rw [hnorm_eq]
    rw [psdSchattenPNorm_eq_iSup_posDef_fixedTrace_of_posDef
        hM'psd (hM'pd γ.1) (hhc γ.1 hγ) hγ]
    rw [show (1 / (γ.1 / (γ.1 - 1))) = (γ.1 - 1) / γ.1 from h_one_div_q γ.1 hγ]
    let w : ι → ℝ := fun τ =>
      ((ρ.sqrtMatrix * CFC.rpow σ ((1 - γ.1) / γ.1) * ρ.sqrtMatrix *
          CFC.rpow τ.1 ((γ.1 - 1) / γ.1)).trace).re
    have hw_pos : ∀ τ, 0 < w τ := by
      intro τ
      have hτpd : (CFC.rpow τ.1 ((γ.1 - 1) / γ.1)).PosDef :=
        cMatrix_rpow_posDef_of_posDef τ.2.1 ((γ.1 - 1) / γ.1)
      exact trace_mul_posDef_re_pos (hM'pd γ.1) hτpd
    let τstar : ι :=
      ⟨psdTraceReverseHolderOptimizer
        (ρ.sqrtMatrix * CFC.rpow σ ((1 - γ.1) / γ.1) * ρ.sqrtMatrix)
        (hM'pd γ.1).posSemidef γ.1,
        hτstar_pd γ.1 hγ, (hτstar_props γ.1 hγ).choose_spec.1⟩
    have hw_greatest : IsGreatest (Set.range w) (w τstar) := by
      refine ⟨⟨τstar, rfl⟩, ?_⟩
      rw [mem_upperBounds]
      rintro y ⟨τ, rfl⟩
      have hupper := psd_trace_rpow_holder_variational_upper
        hM'psd τ.2.1.posSemidef τ.2.2 (hhc γ.1 hγ) rfl
      rw [h_one_div_q γ.1 hγ] at hupper
      have hstar_val : w τstar =
          psdSchattenPNorm
            (ρ.sqrtMatrix * CFC.rpow σ ((1 - γ.1) / γ.1) * ρ.sqrtMatrix)
            hM'psd ⟨γ.1, hγ_pos⟩ := by
        simp only [w]
        have hval := (hτstar_props γ.1 hγ).choose_spec.2.2
        have hq : 1 - 1 / γ.1 = (γ.1 - 1) / γ.1 := by field_simp
        rw [hval, hq]
      rw [hstar_val]; exact hupper
    have hc_pos : 0 < γ.1 / (γ.1 - 1) := highAlpha_conjExponent_pos hγ
    haveI : Nonempty ι := ⟨τstar⟩
    have hstar := real_mul_log2_iSup_eq_iSup_mul_log2_of_isGreatest
      hc_pos hw_pos hw_greatest
    rw [hstar]
    apply iSup_congr
    intro τ
    show (γ.1 / (γ.1 - 1)) *
        log2 ((ρ.sqrtMatrix * CFC.rpow σ ((1 - γ.1) / γ.1) * ρ.sqrtMatrix *
          CFC.rpow τ.1 ((γ.1 - 1) / γ.1)).trace).re =
      (γ.1 / (γ.1 - 1)) *
        log2 ((kwPurificationStateMatrix ρ *
          CFC.rpow (Matrix.kronecker τ.1⁻¹ σ.transpose) ((1 - γ.1) / γ.1)).trace).re
    rw [kw_vectorization_eq_highAlpha (α := γ.1) ρ hσ τ.2.1]
  have hper_tau : ∀ τ : ι,
      (α / (α - 1)) *
        log2 ((kwPurificationStateMatrix ρ *
          CFC.rpow (Matrix.kronecker τ.1⁻¹ σ.transpose) ((1 - α) / α)).trace).re ≤
      (β / (β - 1)) *
        log2 ((kwPurificationStateMatrix ρ *
          CFC.rpow (Matrix.kronecker τ.1⁻¹ σ.transpose) ((1 - β) / β)).trace).re := by
    intro τ
    have hXpd : (Matrix.kronecker τ.1⁻¹ σ.transpose).PosDef :=
      (τ.2.1.inv).kronecker hσ.transpose
    have hkw := kw_state_rpowTrace_alphaObjective_mono
      (kwPurificationState ρ) hXpd ⟨α, hα⟩ ⟨β, hβ⟩ hab
    rw [kwPurificationState_matrix] at hkw
    have halg : ∀ γ : {γ : ℝ // 1 < γ},
        (γ.1 / (γ.1 - 1)) *
            log2 ((kwPurificationStateMatrix ρ *
                CFC.rpow (Matrix.kronecker τ.1⁻¹ σ.transpose)
                  ((1 - γ.1) / γ.1)).trace).re =
          -((Real.log
                ((kwPurificationStateMatrix ρ *
                    CFC.rpow (Matrix.kronecker τ.1⁻¹ σ.transpose)
                      ((1 - γ.1) / γ.1)).trace).re /
              ((1 - γ.1) / γ.1)) / Real.log 2) := by
      intro γ
      rw [log2]
      field_simp
      rw [show (γ.1 - 1 : ℝ) = -(1 - γ.1) from by ring, div_neg]
    rw [halg ⟨α, hα⟩, halg ⟨β, hβ⟩]
    exact hkw
  have hI : Nonempty ι := by
    let τstar : ι :=
      ⟨psdTraceReverseHolderOptimizer
        (ρ.sqrtMatrix * CFC.rpow σ ((1 - α) / α) * ρ.sqrtMatrix)
        (hM'pd α).posSemidef α,
        hτstar_pd α hα, (hτstar_props α hα).choose_spec.1⟩
    exact ⟨τstar⟩
  rw [hD_eq ⟨α, hα⟩, hD_eq ⟨β, hβ⟩]
  refine ciSup_mono ?_ hper_tau
  refine ⟨(β / (β - 1)) * log2
      (psdSchattenPNorm (ρ.sqrtMatrix * CFC.rpow σ ((1 - β) / β) * ρ.sqrtMatrix)
        (hM'pd β).posSemidef ⟨β, lt_trans zero_lt_one hβ⟩), ?_⟩
  rintro _ ⟨τ, rfl⟩
  have hpos : 0 < ((kwPurificationStateMatrix ρ *
      CFC.rpow (Matrix.kronecker τ.1⁻¹ σ.transpose) ((1 - β) / β)).trace).re := by
    rw [← kw_vectorization_eq_highAlpha (α := β) ρ hσ τ.2.1]
    have hτpd : (CFC.rpow τ.1 ((β - 1) / β)).PosDef :=
      cMatrix_rpow_posDef_of_posDef τ.2.1 ((β - 1) / β)
    exact trace_mul_posDef_re_pos (hM'pd β) hτpd
  have hupper := psd_trace_rpow_holder_variational_upper
    (hM'pd β).posSemidef τ.2.1.posSemidef τ.2.2 (hhc β hβ) rfl
  have hCJ : ((kwPurificationStateMatrix ρ *
      CFC.rpow (Matrix.kronecker τ.1⁻¹ σ.transpose) ((1 - β) / β)).trace).re =
      ((ρ.sqrtMatrix * CFC.rpow σ ((1 - β) / β) * ρ.sqrtMatrix *
        CFC.rpow τ.1 (1 / (β / (β - 1)))).trace).re := by
    rw [← kw_vectorization_eq_highAlpha (α := β) ρ hσ τ.2.1,
      h_one_div_q β hβ]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right
      (Real.log_le_log hpos (hCJ ▸ hupper))
      (le_of_lt (Real.log_pos one_lt_two)))
    (le_of_lt (highAlpha_conjExponent_pos hβ))

/-- PSD power traces are continuous along PSD-constrained convergent filters.

This is the missing primitive for the A1.2 PSD-`ρ` extension: it lifts
`cMatrix_rpow_trace_re_tendsto_of_tendsto_posSemidef` from raw matrix powers to
the `psdTracePower` API.  Proof-irrelevance of the `PosSemidef` argument is
handled by `psdTracePower_eq` (which is `rfl`). -/
theorem psdTracePower_tendsto_of_tendsto_posSemidef
    {X : Type*} {l : Filter X} {M : X → CMatrix a} {Mlim : CMatrix a}
    {p : ℝ} (hp : 0 < p)
    (hM : Filter.Tendsto M l (nhds Mlim))
    (hMpsd : ∀ x, (M x).PosSemidef)
    (hMlim : Mlim.PosSemidef) :
    Filter.Tendsto (fun x => psdTracePower (M x) (hMpsd x) p) l
      (nhds (psdTracePower Mlim hMlim p)) := by
  simp only [psdTracePower_eq]
  exact cMatrix_rpow_trace_re_tendsto_of_tendsto_posSemidef hp hM
    (Eventually.of_forall hMpsd) hMlim

/-- The high-`α` finite PSD-reference branch is continuous in the input state
matrix along PSD-constrained convergent filters, for fixed positive-definite
reference `σ`.

Mathematically: `D̃_α(ρ∥σ)` is `(1/(α-1)) · log2 Tr[(σ^{(1-α)/(2α)} ρ σ^{(1-α)/(2α)})^α]`,
which is a composition of (i) a linear map `ρ.matrix ↦ σ^s ρ.matrix σ^s`,
(ii) the PSD-power trace (continuous by `psdTracePower_tendsto_of_tendsto_posSemidef`),
(iii) `log2` (continuous on `(0, ∞)`), and (iv) scalar multiplication.  Positivity
of the limit trace comes from `sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports`
(`Matrix.Supports ρ.matrix σ` is free because `σ` is PD).  This is the
faithful KW route (`entropies.tex:2347–2372` treats `ρ` as arbitrary PSD). -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_tendsto_of_posSemidefState
    {X : Type*} {l : Filter X} {ρF : X → State a} {ρ : State a} {σ : CMatrix a}
    (hσ : σ.PosDef) {α : ℝ} (hα : 1 < α)
    (hρF_matrix : Filter.Tendsto (fun x => (ρF x).matrix) l (nhds ρ.matrix))
    (_hρF_psd : ∀ x, (ρF x).matrix.PosSemidef)
    (_hρ_psd : ρ.matrix.PosSemidef) :
    Filter.Tendsto
      (fun x => sandwichedRenyiPSDReferenceHighAlphaFinite (ρF x) σ hσ.posSemidef α)
      l (nhds (sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef α)) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  -- Step 1: `sandwichedRenyiReferenceInner (ρF x) σ α` tends to the limit inner.
  -- The inner operator is `σ^s · ρ.matrix · σ^s` with `s = (1-α)/(2α)` fixed;
  -- it is linear (hence continuous) in `ρ.matrix`.
  have hinnerF_tendsto :
      Filter.Tendsto (fun x => sandwichedRenyiReferenceInner (ρF x) σ α) l
        (nhds (sandwichedRenyiReferenceInner ρ σ α)) := by
    have hcont : Continuous fun M : CMatrix a =>
      CFC.rpow σ ((1 - α) / (2 * α)) * M * CFC.rpow σ ((1 - α) / (2 * α)) := by fun_prop
    have htendsto := (hcont.tendsto ρ.matrix).comp hρF_matrix
    exact htendsto
  -- Step 2: `psdTracePower` of the inner tends to the limit power trace
  -- (using the primitive `psdTracePower_tendsto_of_tendsto_posSemidef`).
  have hpowF_tendsto :
      Filter.Tendsto
        (fun x =>
          psdTracePower (sandwichedRenyiReferenceInner (ρF x) σ α)
            (sandwichedRenyiReferenceInner_posSemidef (ρF x) hσ.posSemidef α) α)
        l
        (nhds
          (psdTracePower (sandwichedRenyiReferenceInner ρ σ α)
            (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef α) α)) := by
    refine psdTracePower_tendsto_of_tendsto_posSemidef hα_pos hinnerF_tendsto
      (fun x => sandwichedRenyiReferenceInner_posSemidef (ρF x) hσ.posSemidef α)
      (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef α)
  -- Step 3: positivity of the limit trace (so `log2` is continuous at it).
  have hSupport : Matrix.Supports ρ.matrix σ :=
    Matrix.Supports.of_right_posDef ρ.matrix σ hσ
  have hpow_pos :
      0 < psdTracePower (sandwichedRenyiReferenceInner ρ σ α)
        (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef α) α :=
    sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports ρ hσ.posSemidef hSupport α
  -- Step 4: compose with `log2` (continuous at the strictly-positive limit).
  have hlog2_cont :
      ContinuousAt (fun y : ℝ => log2 y)
        (psdTracePower (sandwichedRenyiReferenceInner ρ σ α)
          (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef α) α) := by
    unfold log2
    refine ContinuousAt.div ?_ continuousAt_const ?_
    · exact Real.continuousAt_log hpow_pos.ne'
    · exact (Real.log_pos one_lt_two).ne'
  have hlog2F_tendsto :
      Filter.Tendsto
        (fun x =>
          log2
            (psdTracePower (sandwichedRenyiReferenceInner (ρF x) σ α)
              (sandwichedRenyiReferenceInner_posSemidef (ρF x) hσ.posSemidef α) α))
        l
        (nhds
          (log2
            (psdTracePower (sandwichedRenyiReferenceInner ρ σ α)
              (sandwichedRenyiReferenceInner_posSemidef ρ hσ.posSemidef α) α))) :=
    hlog2_cont.tendsto.comp hpowF_tendsto
  -- Step 5: scalar multiplication by `(1/(α-1))` is continuous.
  have hconst_cont : Continuous (fun y : ℝ => (1 / (α - 1)) * y) := continuous_const_mul _
  exact (hconst_cont.tendsto _).comp hlog2F_tendsto

/-- Smooth-case α-monotonicity of `sandwichedRenyiPSDReferenceHighAlphaFinite`
extended to positive-semidefinite `ρ.matrix` (positive-definite `σ`).

This is the A1.2 deliverable: the faithful KW route via full-rank approximation
of `ρ` (no α-dependent Hölder unit ball).  Approximate `ρ` by
`regularizedWithState ρ (maximallyMixed a) ε`, which is positive-definite for
`ε > 0` and tends to `ρ` as `ε → 0+`.  Apply the A1.1 PD-`ρ` theorem at each
`ε`, then lift via `le_of_tendsto` using the continuity of
`sandwichedRenyiPSDReferenceHighAlphaFinite` in `ρ` along PSD paths. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_mono_posSemidef_state_posDef_reference
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosDef)
    {α β : ℝ} (hα : 1 < α) (hβ : 1 < β) (hab : α ≤ β) :
    sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef α ≤
      sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef β := by
  classical
  haveI : Nonempty a := ρ.nonempty
  let ω : State a := maximallyMixed a
  have hω_pd : ω.matrix.PosDef := maximallyMixed_posDef (a := a)
  -- The PD approximation sequence: ε_n = 1 / (n + 2) ∈ (0, 1), ε_n → 0.
  let f : ℕ → ℝ := fun n => 1 / (n + 2 : ℝ)
  have hf_in_Ioo : ∀ n, f n ∈ Set.Ioo (0 : ℝ) 1 := by
    intro n
    have hnpos : (0 : ℝ) < (n : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    refine ⟨?_, ?_⟩
    · exact one_div_pos.mpr hnpos
    · rw [div_lt_iff₀ hnpos]
      have : (1 : ℝ) ≤ (n : ℝ) + 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        linarith
      linarith
  have hf_tendsto : Tendsto f atTop (nhds (0 : ℝ)) := by
    have hadd : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ (2 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ))
    exact tendsto_const_nhds.div_atTop hadd
  have hf_tendsto_within : Tendsto f atTop (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hf_tendsto, Eventually.of_forall hf_in_Ioo⟩
  -- State-valued path: ρ_n = regularizedWithState ρ ω (ε_n).
  let ρF : ℕ → State a := fun n =>
    regularizedWithState ρ ω (f n) (hf_in_Ioo n).1.le (hf_in_Ioo n).2.le
  have hρF_matrix_eq : ∀ n,
      (ρF n).matrix = regularizedStateMatrix ρ ω (f n) := fun n => rfl
  have hρF_matrix_tendsto :
      Tendsto (fun n => (ρF n).matrix) atTop (nhds ρ.matrix) := by
    rw [funext hρF_matrix_eq]
    exact (regularizedStateMatrix_tendsto_zero ρ ω).comp hf_tendsto_within
  have hρF_pd : ∀ n, (ρF n).matrix.PosDef := fun n =>
    regularizedWithState_posDef_of_noise ρ ω hω_pd
      (hf_in_Ioo n).1.le (hf_in_Ioo n).2.le (hf_in_Ioo n).1
  have hρF_psd : ∀ n, (ρF n).matrix.PosSemidef := fun n => (hρF_pd n).posSemidef
  -- Apply A1.1 at each n.
  have hineq : ∀ n,
      sandwichedRenyiPSDReferenceHighAlphaFinite (ρF n) σ hσ.posSemidef α ≤
        sandwichedRenyiPSDReferenceHighAlphaFinite (ρF n) σ hσ.posSemidef β := fun n =>
    sandwichedRenyiPSDReferenceHighAlphaFinite_mono_posDef_reference_posDef_state
      (ρF n) hσ (hρF_pd n) hα hβ hab
  -- Take the limit via the continuity lemma (A1.2 setup).
  have hα_lim :
      Tendsto (fun n => sandwichedRenyiPSDReferenceHighAlphaFinite (ρF n) σ hσ.posSemidef α)
        atTop (nhds (sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef α)) :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_tendsto_of_posSemidefState hσ hα
      hρF_matrix_tendsto hρF_psd ρ.pos
  have hβ_lim :
      Tendsto (fun n => sandwichedRenyiPSDReferenceHighAlphaFinite (ρF n) σ hσ.posSemidef β)
        atTop (nhds (sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef β)) :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_tendsto_of_posSemidefState hσ hβ
      hρF_matrix_tendsto hρF_psd ρ.pos
  -- Combine: β - α ≥ 0 at every n, hence in the limit.
  have hdiff_nonneg :
      ∀ᶠ n in atTop,
        0 ≤ sandwichedRenyiPSDReferenceHighAlphaFinite (ρF n) σ hσ.posSemidef β -
            sandwichedRenyiPSDReferenceHighAlphaFinite (ρF n) σ hσ.posSemidef α :=
    Eventually.of_forall (fun n => sub_nonneg.mpr (hineq n))
  have hdiff_lim :
      Tendsto
        (fun n =>
          sandwichedRenyiPSDReferenceHighAlphaFinite (ρF n) σ hσ.posSemidef β -
          sandwichedRenyiPSDReferenceHighAlphaFinite (ρF n) σ hσ.posSemidef α)
        atTop
        (nhds
          (sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef β -
           sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef α)) :=
    hβ_lim.sub hα_lim
  have hlim_nonneg :
      0 ≤ sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef β -
          sandwichedRenyiPSDReferenceHighAlphaFinite ρ σ hσ.posSemidef α :=
    ge_of_tendsto hdiff_lim hdiff_nonneg
  linarith

/-- Unconditional state-level sandwiched-Rényi mutual-information α-monotonicity.

For every bipartite state `ρ_AB` and high-α parameters `α ≤ β`,
`Ĩ_α(ρ_AB) ≤ Ĩ_β(ρ_AB)` — no hypotheses beyond the (Subtype-encoded) bounds
`1 < α, β`. This is the A1.3 deliverable: the A1.2 PSD-`ρ` extension
discharges the `hcompressed` hypothesis of the supportCompress chain
(`sandwichedRenyiMutualInformationE_mono_of_supportCompress_mono`), since on
the compressed space the reference is positive-definite
(`psdSupportCompressedState_reference_posDef`) and the state is PSD
(`psdSupportCompressedState.pos`).

Faithful to KW `entropies.tex:2347–2372`. -/
theorem sandwichedRenyiMutualInformationE_mono
    (rhoAB : State (Prod a b))
    (alpha beta : {alpha : Real // 1 < alpha})
    (hab : alpha.1 ≤ beta.1) :
    rhoAB.sandwichedRenyiMutualInformationE alpha.1 ≤
      rhoAB.sandwichedRenyiMutualInformationE beta.1 := by
  refine
    rhoAB.sandwichedRenyiMutualInformationE_mono_of_supportCompress_mono
      (fun sigmaB α β hαβ hSupport =>
        sandwichedRenyiPSDReferenceHighAlphaFinite_mono_posSemidef_state_posDef_reference
          (psdSupportCompressedState rhoAB (rhoAB.marginalA.prod sigmaB).pos hSupport)
          (psdSupportCompressedState_reference_posDef (rhoAB.marginalA.prod sigmaB).pos)
          α.2 β.2 hαβ)
      alpha beta hab

end State

end

end QIT
