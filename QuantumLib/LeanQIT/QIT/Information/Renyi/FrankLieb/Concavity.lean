/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.FrankLieb.Variational
public import QIT.Information.Renyi.RenyiDPI.Domain
public import QIT.Information.Renyi.RenyiDPIStatement

/-!
# Frank--Lieb concavity support

Frank--Lieb concavity and low-alpha sandwiched Renyi `Q` concavity tools.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Topology Matrix.Norms.L2Operator

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

/-- Unrestricted finite-dimensional Epstein trace concavity.

For `0 < c < 1`, the map
`σ ↦ Tr[(K† σ^c K)^(1/c)]` is concave on PSD matrices.  This is the
minimum Epstein/Frank--Lieb theorem needed before converting the low-alpha
sandwiched `Q` functional to partial-trace monotonicity. -/
theorem epsteinTraceTerm_concave
    (K : CMatrix a) {σ₁ σ₂ : CMatrix a}
    (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    {c t : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * epsteinTraceTerm K σ₁ c +
        (1 - t) * epsteinTraceTerm K σ₂ c ≤
      epsteinTraceTerm K (cMatrixConvexCombination t σ₁ σ₂) c := by
  let X₁ : CMatrix a := CFC.rpow (star K * CFC.rpow σ₁ c * K) (1 / c)
  let X₂ : CMatrix a := CFC.rpow (star K * CFC.rpow σ₂ c * K) (1 / c)
  let Xt : CMatrix a := cMatrixConvexCombination t X₁ X₂
  have hM₁ : (star K * CFC.rpow σ₁ c * K).PosSemidef :=
    epsteinTraceTerm_inner_posSemidef K hσ₁ c
  have hM₂ : (star K * CFC.rpow σ₂ c * K).PosSemidef :=
    epsteinTraceTerm_inner_posSemidef K hσ₂ c
  have hX₁ : X₁.PosSemidef := by
    simpa [X₁] using
      cMatrix_rpow_posSemidef
        (A := star K * CFC.rpow σ₁ c * K) (s := 1 / c) hM₁
  have hX₂ : X₂.PosSemidef := by
    simpa [X₂] using
      cMatrix_rpow_posSemidef
        (A := star K * CFC.rpow σ₂ c * K) (s := 1 / c) hM₂
  have hσt : (cMatrixConvexCombination t σ₁ σ₂).PosSemidef :=
    cMatrixConvexCombination_posSemidef hσ₁ hσ₂ ht0 ht1
  have hXt : Xt.PosSemidef := by
    simpa [Xt] using cMatrixConvexCombination_posSemidef hX₁ hX₂ ht0 ht1
  have hconc :
      t * epsteinDualObjective K σ₁ X₁ c +
          (1 - t) * epsteinDualObjective K σ₂ X₂ c ≤
        epsteinDualObjective K (cMatrixConvexCombination t σ₁ σ₂) Xt c := by
    simpa [Xt] using
      epsteinDualObjective_concave K σ₁ σ₂ X₁ X₂
        hc_pos hc_lt_one hσ₁ hσ₂ hX₁ hX₂ ht0 ht1
  have heq₁ :
      epsteinDualObjective K σ₁ X₁ c = epsteinTraceTerm K σ₁ c := by
    simpa [X₁] using
      epsteinDualObjective_eq_epsteinTraceTerm_at_optimizer
        K hσ₁ hc_pos hc_lt_one
  have heq₂ :
      epsteinDualObjective K σ₂ X₂ c = epsteinTraceTerm K σ₂ c := by
    simpa [X₂] using
      epsteinDualObjective_eq_epsteinTraceTerm_at_optimizer
        K hσ₂ hc_pos hc_lt_one
  have hupper :
      epsteinDualObjective K (cMatrixConvexCombination t σ₁ σ₂) Xt c ≤
        epsteinTraceTerm K (cMatrixConvexCombination t σ₁ σ₂) c :=
    epsteinDualObjective_le_epsteinTraceTerm K hσt hXt hc_pos hc_lt_one
  rw [heq₁, heq₂] at hconc
  exact hconc.trans hupper

namespace State

open RenyiDPI.Statement

/-- In the low-`alpha` Frank--Lieb range, the sandwiched reference exponent
`(1 - alpha) / (2 * alpha)` is nonnegative. -/
theorem sandwichedRenyiQ_sandwichExponent_nonneg
    {α : ℝ} (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1) :
    0 ≤ (1 - α) / (2 * α) := by
  have hα_pos : 0 < α := by
    linarith
  exact div_nonneg
    (sub_nonneg.mpr (le_of_lt hα_lt_one))
    (mul_nonneg (by norm_num) (le_of_lt hα_pos))

/-- In the low-`alpha` Frank--Lieb range, the trace-power exponent itself is
nonnegative. -/
theorem sandwichedRenyiQ_alpha_nonneg_of_lowAlpha
    {α : ℝ} (hα_half : 1 / 2 ≤ α) :
    0 ≤ α := by
  linarith

/-- In the strict low-`alpha` Frank--Lieb range, the Epstein exponent
`c = (1 - alpha) / alpha` is positive. -/
theorem sandwichedRenyiQ_frankLiebExponent_pos
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    0 < (1 - α) / α := by
  have hα_pos : 0 < α := by linarith
  exact div_pos (sub_pos.mpr hα_lt_one) hα_pos

/-- In the strict low-`alpha` Frank--Lieb range, the Epstein exponent
`c = (1 - alpha) / alpha` is less than one. -/
theorem sandwichedRenyiQ_frankLiebExponent_lt_one
    {α : ℝ} (hα_half : 1 / 2 < α) (_hα_lt_one : α < 1) :
    (1 - α) / α < 1 := by
  have hα_pos : 0 < α := by linarith
  rw [div_lt_one hα_pos]
  linarith

/-- Matrix-level sandwiched Renyi inner operator
`σ^((1 - α) / (2 * α)) ρ σ^((1 - α) / (2 * α))`.

This is the PSD input used in the Frank--Lieb low-`α` reverse-Holder
variational step before applying Lieb concavity. -/
def sandwichedRenyiQInner (ρ σ : CMatrix a) (α : ℝ) : CMatrix a :=
  let s := (1 - α) / (2 * α)
  let C := CFC.rpow σ s
  C * ρ * C

/-- The matrix-level sandwiched Renyi `Q` inner operator is PSD for PSD inputs. -/
theorem sandwichedRenyiQInner_posSemidef
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (α : ℝ) :
    (sandwichedRenyiQInner ρ σ α).PosSemidef := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ s
  have hC : C.PosSemidef := by
    simpa [C] using cMatrix_rpow_posSemidef (A := σ) (s := s) hσ
  have hCstar : star C = C := hC.isHermitian.eq
  have hinner : (star C * ρ * C).PosSemidef :=
    Matrix.PosSemidef.conjTranspose_mul_mul_same hρ C
  rw [hCstar] at hinner
  simpa [sandwichedRenyiQInner, s, C] using hinner

/-- The matrix-level sandwiched Renyi `Q` inner operator is positive definite
for positive-definite inputs. -/
theorem sandwichedRenyiQInner_posDef
    {ρ σ : CMatrix a} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (α : ℝ) :
    (sandwichedRenyiQInner ρ σ α).PosDef := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ s
  have hC : C.PosDef := by
    simpa [C] using cMatrix_rpow_posDef_of_posDef hσ s
  have hCstar : star C = C := hC.isHermitian.eq
  have hinner : (star C * ρ * C).PosDef := by
    rw [Matrix.IsUnit.posDef_star_left_conjugate_iff hC.isUnit]
    exact hρ
  rw [hCstar] at hinner
  simpa [sandwichedRenyiQInner, s, C] using hinner

/-- With a positive-definite reference, the sandwiched `Q` inner operator
vanishes exactly when the left input vanishes. -/
theorem sandwichedRenyiQInner_eq_zero_iff_left_eq_zero_of_sigma_posDef
    {ρ σ : CMatrix a} (hσ : σ.PosDef) (α : ℝ) :
    sandwichedRenyiQInner ρ σ α = 0 ↔ ρ = 0 := by
  constructor
  · intro hinner
    let s : ℝ := (1 - α) / (2 * α)
    let C : CMatrix a := CFC.rpow σ s
    have hC : C.PosDef := by
      simpa [C] using cMatrix_rpow_posDef_of_posDef hσ s
    have hdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit
    have hleft : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul C hdet
    have hright : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hdet
    have hinnerC : C * ρ * C = 0 := by
      simpa [sandwichedRenyiQInner, s, C] using hinner
    have hrho :
        ρ = C⁻¹ * (C * ρ * C) * C⁻¹ := by
      calc
        ρ = (1 : CMatrix a) * ρ * (1 : CMatrix a) := by simp
        _ = (C⁻¹ * C) * ρ * (C * C⁻¹) := by rw [hleft, hright]
        _ = C⁻¹ * (C * ρ * C) * C⁻¹ := by simp [Matrix.mul_assoc]
    rw [hinnerC] at hrho
    simpa using hrho
  · intro hρ
    simp [sandwichedRenyiQInner, hρ]

/-- Definition bridge from matrix-level `sandwichedRenyiQ` to the PSD trace
power used by the Schatten variational API. -/
theorem sandwichedRenyiQ_eq_psdTracePower_QInner
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (α : ℝ) :
    sandwichedRenyiQ ρ σ hρ hσ α =
      psdTracePower (sandwichedRenyiQInner ρ σ α)
        (sandwichedRenyiQInner_posSemidef hρ hσ α) α := by
  unfold sandwichedRenyiQ sandwichedRenyiQInner psdTracePower
  rfl

/-- The PSD-friendly low-`α` `Q` functional is continuous along
PSD-constrained matrix paths when the reference sandwich exponent is
positive. -/
theorem sandwichedRenyiQ_tendsto_of_tendsto_posSemidef
    {X : Type*} {l : Filter X}
    {ρF σF : X → CMatrix a} {ρ σ : CMatrix a}
    {α : ℝ} (hα_pos : 0 < α)
    (hs_pos : 0 < (1 - α) / (2 * α))
    (hρF : Filter.Tendsto ρF l (nhds ρ))
    (hσF : Filter.Tendsto σF l (nhds σ))
    (hρFpsd : ∀ x, (ρF x).PosSemidef)
    (hσFpsd : ∀ x, (σF x).PosSemidef)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    Filter.Tendsto
      (fun x => sandwichedRenyiQ (ρF x) (σF x)
        (hρFpsd x) (hσFpsd x) α)
      l
      (nhds (sandwichedRenyiQ ρ σ hρ hσ α)) := by
  let s : ℝ := (1 - α) / (2 * α)
  have hσpow :
      Filter.Tendsto (fun x => CFC.rpow (σF x) s) l
        (nhds (CFC.rpow σ s)) := by
    exact cMatrix_rpow_tendsto_of_tendsto_posSemidef
      (a := a) (p := s) (by simpa [s] using hs_pos)
      hσF (Filter.Eventually.of_forall hσFpsd) hσ
  have hinner :
      Filter.Tendsto
        (fun x => sandwichedRenyiQInner (ρF x) (σF x) α)
        l
        (nhds (sandwichedRenyiQInner ρ σ α)) := by
    have hmul :
        Filter.Tendsto
          (fun x => CFC.rpow (σF x) s * ρF x * CFC.rpow (σF x) s)
          l
          (nhds (CFC.rpow σ s * ρ * CFC.rpow σ s)) :=
      (hσpow.mul hρF).mul hσpow
    simpa [sandwichedRenyiQInner, s] using hmul
  have hinner_psd :
      ∀ x, (sandwichedRenyiQInner (ρF x) (σF x) α).PosSemidef :=
    fun x => sandwichedRenyiQInner_posSemidef (hρFpsd x) (hσFpsd x) α
  have htrace :=
    cMatrix_rpow_trace_re_tendsto_of_tendsto_posSemidef
      (a := a) (p := α) hα_pos hinner
      (Filter.Eventually.of_forall hinner_psd)
      (sandwichedRenyiQInner_posSemidef hρ hσ α)
  simpa [sandwichedRenyiQ, sandwichedRenyiQInner, s] using htrace

/-- The PSD-friendly low-`α` `Q` functional vanishes when the left input is
zero. -/
theorem sandwichedRenyiQ_zero_left
    (σ : CMatrix a) (hσ : σ.PosSemidef) {α : ℝ} (hα_pos : 0 < α) :
    sandwichedRenyiQ (0 : CMatrix a) σ Matrix.PosSemidef.zero hσ α = 0 := by
  let s : ℝ := (1 - α) / (2 * α)
  have hpow :
      CFC.rpow (0 : CMatrix a) α = 0 := by
    simpa using (CFC.zero_rpow (A := CMatrix a) (x := α) (ne_of_gt hα_pos))
  unfold sandwichedRenyiQ
  change (CFC.rpow (CFC.rpow σ s * (0 : CMatrix a) * CFC.rpow σ s) α).trace.re = 0
  simp only [mul_zero, zero_mul]
  rw [hpow]
  simp

/-- The PSD-friendly low-`α` `Q` functional is nonnegative on PSD inputs. -/
theorem sandwichedRenyiQ_nonneg
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (α : ℝ) :
    0 ≤ sandwichedRenyiQ ρ σ hρ hσ α := by
  rw [sandwichedRenyiQ_eq_psdTracePower_QInner hρ hσ α]
  exact psdTracePower_nonneg
    (sandwichedRenyiQInner ρ σ α)
    (sandwichedRenyiQInner_posSemidef hρ hσ α) α

/-- A normalized state has strictly positive low-`α` `Q` value against a
positive-definite matrix reference.

This is the positivity side condition needed when the source regularizes a PSD
reference to `σ + εI`: the regularized reference is positive definite, so the
finite real logarithmic branch is available without an additional support
hypothesis. -/
theorem sandwichedRenyiQ_pos_of_state_posDef_reference
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosDef)
    (α : ℝ) :
    0 < sandwichedRenyiQ ρ.matrix σ ρ.pos hσ.posSemidef α := by
  have hρ_ne : ρ.matrix ≠ 0 := by
    intro hρ_zero
    have htrace_zero : ρ.matrix.trace = 0 := by
      rw [hρ_zero]
      simp
    have hone_zero : (1 : ℂ) = 0 := by
      rw [ρ.trace_eq_one] at htrace_zero
      exact htrace_zero
    exact one_ne_zero hone_zero
  have hinner_ne : sandwichedRenyiQInner ρ.matrix σ α ≠ 0 := by
    intro hinner_zero
    have hρ_zero :
        ρ.matrix = 0 :=
      (sandwichedRenyiQInner_eq_zero_iff_left_eq_zero_of_sigma_posDef
        (ρ := ρ.matrix) (σ := σ) hσ α).mp hinner_zero
    exact hρ_ne hρ_zero
  rw [sandwichedRenyiQ_eq_psdTracePower_QInner ρ.pos hσ.posSemidef α]
  exact psdTracePower_pos_of_ne_zero
    (sandwichedRenyiQInner ρ.matrix σ α)
    (sandwichedRenyiQInner_posSemidef ρ.pos hσ.posSemidef α) hinner_ne

/-- Reverse-Holder side-state objective values for the sandwiched Renyi `Q`
inner operator.

This is the matrix-level version of the Tomamichel 2015
`renyi.tex:817-824` variational step: for `0 < α < 1`, normalized PSD
side-states `N` supporting the sandwiched inner operator give the
reverse-Holder trace objective with exponent `1 - 1 / α`. -/
def sandwichedRenyiQReverseHolderValueSet
    (ρ σ : CMatrix a) (α : ℝ) : Set ℝ :=
  psdTraceReverseHolderStateValueSet (sandwichedRenyiQInner ρ σ α) α

/-- Reverse-Holder variational lower bound for the low-`α` sandwiched Renyi
`Q` primitive.

This is a non-circular Frank--Lieb-route primitive: it only unfolds
`Q_α(ρ, σ)` to the sandwiched inner PSD trace power and applies the
reverse-Holder variational inequality. It does not assume joint concavity. -/
theorem sandwichedRenyiQ_reverseHolder_norm_le_trace
    {ρ σ N : CMatrix a}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hN : N.PosSemidef) (hNtr : N.trace.re = 1)
    {α : ℝ} (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (hSupport : Matrix.Supports (sandwichedRenyiQInner ρ σ α) N) :
    (sandwichedRenyiQ ρ σ hρ hσ α) ^ (1 / α) ≤
      ((sandwichedRenyiQInner ρ σ α *
        CFC.rpow N (1 - 1 / α)).trace).re := by
  have hα_pos : 0 < α := by linarith
  let M : CMatrix a := sandwichedRenyiQInner ρ σ α
  let hM : M.PosSemidef := by
    simpa [M] using sandwichedRenyiQInner_posSemidef hρ hσ α
  have hvar :
      psdSchattenPNorm M hM ⟨α, hα_pos⟩ ≤
        ((M * CFC.rpow N (1 - 1 / α)).trace).re :=
    psd_trace_rpow_reverse_holder_variational
      hM hN hNtr (by simpa [M] using hSupport) hα_pos hα_lt_one rfl
  simpa [M, psdSchattenPNorm, Internal.psdSchattenExpression, psdTracePower,
    sandwichedRenyiQ, sandwichedRenyiQInner] using hvar

/-- Exact reverse-Holder minimizer statement for the sandwiched Renyi `Q`
inner operator when the inner operator is nonzero.

This formalizes the source-shaped minimization primitive before the Lieb
concavity step: the minimum normalized reverse-Holder side-state value is
`Q_α(ρ, σ)^(1 / α)`. -/
theorem sandwichedRenyiQ_reverseHolder_isLeast_of_inner_ne_zero
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (hinner_ne_zero : sandwichedRenyiQInner ρ σ α ≠ 0) :
    IsLeast (sandwichedRenyiQReverseHolderValueSet ρ σ α)
      ((sandwichedRenyiQ ρ σ hρ hσ α) ^ (1 / α)) := by
  have hα_pos : 0 < α := by linarith
  let M : CMatrix a := sandwichedRenyiQInner ρ σ α
  let hM : M.PosSemidef := by
    simpa [M] using sandwichedRenyiQInner_posSemidef hρ hσ α
  have hleast :
      IsLeast (psdTraceReverseHolderStateValueSet M α)
        (psdSchattenPNorm M hM ⟨α, hα_pos⟩) :=
    psdTraceReverseHolderStateValueSet_isLeast_of_ne_zero
      hM hα_pos hα_lt_one (by simpa [M] using hinner_ne_zero)
  simpa [sandwichedRenyiQReverseHolderValueSet, M, psdSchattenPNorm,
    Internal.psdSchattenExpression,
    psdTracePower, sandwichedRenyiQ, sandwichedRenyiQInner] using hleast

/-- Exact `sInf` form of the reverse-Holder variational formula for the
sandwiched Renyi `Q` inner operator, in the nonzero case. -/
theorem sandwichedRenyiQ_reverseHolder_sInf_eq_of_inner_ne_zero
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1)
    (hinner_ne_zero : sandwichedRenyiQInner ρ σ α ≠ 0) :
    sInf (sandwichedRenyiQReverseHolderValueSet ρ σ α) =
      (sandwichedRenyiQ ρ σ hρ hσ α) ^ (1 / α) :=
  (sandwichedRenyiQ_reverseHolder_isLeast_of_inner_ne_zero
    hρ hσ hα_half hα_lt_one hinner_ne_zero).csInf_eq

omit [Fintype a] [DecidableEq a] in
/-- The mixed `rho` input in the binary joint-concavity statement is PSD. -/
theorem sandwichedRenyiQ_rho_mix_posSemidef
    {ρ₁ ρ₂ : CMatrix a} (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (cMatrixConvexCombination t ρ₁ ρ₂).PosSemidef :=
  cMatrixConvexCombination_posSemidef hρ₁ hρ₂ ht0 ht1

omit [Fintype a] [DecidableEq a] in
/-- The mixed `sigma` input in the binary joint-concavity statement is PSD. -/
theorem sandwichedRenyiQ_sigma_mix_posSemidef
    {σ₁ σ₂ : CMatrix a} (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (cMatrixConvexCombination t σ₁ σ₂).PosSemidef :=
  cMatrixConvexCombination_posSemidef hσ₁ hσ₂ ht0 ht1

/-- The fixed Frank--Lieb weight `H^(-1/2)` is Hermitian. -/
theorem frankLieb_weight_isHermitian
    {H : CMatrix a} (hH : H.PosDef) :
    (CFC.rpow H (-(1 / 2 : ℝ))).IsHermitian :=
  (cMatrix_rpow_posSemidef
    (A := H) (s := -(1 / 2 : ℝ)) hH.posSemidef).isHermitian

/-- The fixed-weight Frank--Lieb inner term
`H^(-1/2) σ^c H^(-1/2)` is PSD. -/
theorem frankLieb_sigmaTerm_inner_posSemidef
    {H σ : CMatrix a} (hH : H.PosDef) (hσ : σ.PosSemidef) (c : ℝ) :
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    (K * CFC.rpow σ c * K).PosSemidef := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  have hKstar : star K = K := by
    simpa [K] using (frankLieb_weight_isHermitian (a := a) hH).eq
  have hinner : (star K * CFC.rpow σ c * K).PosSemidef :=
    epsteinTraceTerm_inner_posSemidef K hσ c
  rw [hKstar] at hinner
  simpa [K] using hinner

/-- The fixed-weight Frank--Lieb trace term is nonnegative. -/
theorem frankLieb_sigmaTerm_nonneg
    {H σ : CMatrix a} (hH : H.PosDef) (hσ : σ.PosSemidef) (c : ℝ) :
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    0 ≤ ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  have hinner : (K * CFC.rpow σ c * K).PosSemidef := by
    simpa [K] using frankLieb_sigmaTerm_inner_posSemidef
      (a := a) (H := H) (σ := σ) hH hσ c
  have hpow : (CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).PosSemidef :=
    cMatrix_rpow_posSemidef
      (A := K * CFC.rpow σ c * K) (s := 1 / c) hinner
  simpa [K] using (Matrix.PosSemidef.trace_nonneg hpow).1

/-- Scaling the positive-definite Frank--Lieb weight rescales the fixed
`sigma` term with the source-predicted homogeneity. -/
theorem frankLieb_sigmaTerm_real_smul_weight
    {H σ : CMatrix a} (hH : H.PosDef) (hσ : σ.PosSemidef)
    {lambda c : ℝ} (hlambda_pos : 0 < lambda) (_hc_pos : 0 < c) :
    let Klam : CMatrix a := CFC.rpow (lambda • H : CMatrix a) (-(1 / 2 : ℝ))
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    ((CFC.rpow (Klam * CFC.rpow σ c * Klam) (1 / c)).trace).re =
      lambda ^ (-(1 / c)) *
        ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re := by
  let Klam : CMatrix a := CFC.rpow (lambda • H : CMatrix a) (-(1 / 2 : ℝ))
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let S : CMatrix a := CFC.rpow σ c
  let mu : ℝ := lambda ^ (-(1 / 2 : ℝ))
  have hKlam : Klam = mu • K := by
    simpa [Klam, K, mu] using
      cMatrix_rpow_real_smul_posSemidef_schatten
        (A := H) (s := -(1 / 2 : ℝ)) hH.posSemidef (le_of_lt hlambda_pos)
  have hmu_mul : mu * mu = lambda ^ (-1 : ℝ) := by
    dsimp [mu]
    rw [← Real.rpow_add hlambda_pos]
    ring_nf
  have hinner :
      Klam * S * Klam = (lambda ^ (-1 : ℝ)) • (K * S * K) := by
    rw [hKlam]
    calc
      (mu • K) * S * (mu • K) =
          (mu * mu) • (K * S * K) := by
            simp [smul_smul, mul_assoc]
      _ = (lambda ^ (-1 : ℝ)) • (K * S * K) := by
            rw [hmu_mul]
  have hbase : (K * S * K).PosSemidef := by
    simpa [K, S] using
      frankLieb_sigmaTerm_inner_posSemidef
        (a := a) (H := H) (σ := σ) hH hσ c
  have hscale_nonneg : 0 ≤ lambda ^ (-1 : ℝ) :=
    Real.rpow_nonneg (le_of_lt hlambda_pos) (-1 : ℝ)
  have hpow :
      CFC.rpow (Klam * S * Klam) (1 / c) =
        (((lambda ^ (-1 : ℝ)) ^ (1 / c) : ℝ) •
          CFC.rpow (K * S * K) (1 / c)) := by
    rw [hinner]
    simpa using cMatrix_rpow_real_smul_posSemidef_schatten
      (A := K * S * K) (s := 1 / c) hbase hscale_nonneg
  have hscale :
      (lambda ^ (-1 : ℝ)) ^ (1 / c) = lambda ^ (-(1 / c)) := by
    calc
      (lambda ^ (-1 : ℝ)) ^ (1 / c) =
          lambda ^ ((-1 : ℝ) * (1 / c)) := by
            rw [← Real.rpow_mul (le_of_lt hlambda_pos)]
      _ = lambda ^ (-(1 / c)) := by
            ring_nf
  dsimp only
  change
    ((CFC.rpow (Klam * S * Klam) (1 / c)).trace).re =
      lambda ^ (-(1 / c)) *
        ((CFC.rpow (K * S * K) (1 / c)).trace).re
  calc
    ((CFC.rpow (Klam * S * Klam) (1 / c)).trace).re =
        ((((lambda ^ (-1 : ℝ)) ^ (1 / c) : ℝ) •
          CFC.rpow (K * S * K) (1 / c)).trace).re := by
          rw [hpow]
    _ = (lambda ^ (-1 : ℝ)) ^ (1 / c) *
          ((CFC.rpow (K * S * K) (1 / c)).trace).re := by
          simp [Matrix.trace_smul, Complex.mul_re]
    _ = lambda ^ (-(1 / c)) *
          ((CFC.rpow (K * S * K) (1 / c)).trace).re := by
          rw [hscale]

theorem frankLieb_sigmaTerm_inner_posDef
    {H σ : CMatrix a} (hH : H.PosDef) (hσ : σ.PosDef) (c : ℝ) :
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    (K * CFC.rpow σ c * K).PosDef := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  have hK : K.PosDef := by
    simpa [K] using cMatrix_rpow_posDef_of_posDef hH (-(1 / 2 : ℝ))
  have hKstar : star K = K := hK.isHermitian.eq
  have hσc : (CFC.rpow σ c).PosDef := cMatrix_rpow_posDef_of_posDef hσ c
  have hconj : (K * CFC.rpow σ c * star K).PosDef := by
    rw [Matrix.IsUnit.posDef_star_right_conjugate_iff hK.isUnit]
    exact hσc
  rwa [hKstar] at hconj

theorem frankLieb_sigmaTerm_pos
    [Nonempty a] {H σ : CMatrix a} (hH : H.PosDef) (hσ : σ.PosDef) (c : ℝ) :
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    0 < ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  have hinner : (K * CFC.rpow σ c * K).PosDef := by
    simpa [K] using frankLieb_sigmaTerm_inner_posDef
      (a := a) (H := H) (σ := σ) hH hσ c
  have hpow :
      (CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).PosDef :=
    cMatrix_rpow_posDef_of_posDef hinner (1 / c)
  exact (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hpow)).1

/-- Gour's source-shaped low-`α` sigma term.

For `c = (1 - α) / α`, this is the second trace term in the
Young variational formula from `BookQRT.tex`, lines 12066--12070:
`Tr[(σ^(-c/2) H σ^(-c/2))^(-1/c)]`. -/
def frankLiebSourceSigmaTerm (σ H : CMatrix a) (c : ℝ) : ℝ :=
  let D : CMatrix a := CFC.rpow σ (-(c / 2))
  ((CFC.rpow (D * H * D) (-(1 / c))).trace).re

/-- Gour's source-shaped fixed-weight low-`α` objective before rewriting the
second term by the `LL*`/`L*L` spectral identity. -/
def frankLiebSourceFixedWeightObjective
    (ρ σ H : CMatrix a) (α c : ℝ) : ℝ :=
  (((ρ * H).trace).re ^ α) *
    (frankLiebSourceSigmaTerm σ H c ^ (1 - α))

/-- The inner matrix in Gour's source-shaped sigma term is positive
definite for positive-definite `σ` and `H`. -/
theorem frankLiebSourceSigmaTerm_inner_posDef
    {σ H : CMatrix a} (hσ : σ.PosDef) (hH : H.PosDef) (c : ℝ) :
    let D : CMatrix a := CFC.rpow σ (-(c / 2))
    (D * H * D).PosDef := by
  let D : CMatrix a := CFC.rpow σ (-(c / 2))
  have hD : D.PosDef := by
    simpa [D] using cMatrix_rpow_posDef_of_posDef hσ (-(c / 2))
  have hDstar : star D = D := hD.isHermitian.eq
  have hconj : (D * H * star D).PosDef := by
    rw [Matrix.IsUnit.posDef_star_right_conjugate_iff hD.isUnit]
    exact hH
  rwa [hDstar] at hconj

/-- Gour's source-shaped sigma term is positive on positive-definite inputs. -/
theorem frankLiebSourceSigmaTerm_pos
    [Nonempty a] {σ H : CMatrix a} (hσ : σ.PosDef) (hH : H.PosDef) (c : ℝ) :
    0 < frankLiebSourceSigmaTerm σ H c := by
  let D : CMatrix a := CFC.rpow σ (-(c / 2))
  have hinner : (D * H * D).PosDef := by
    simpa [D] using frankLiebSourceSigmaTerm_inner_posDef
      (a := a) (σ := σ) (H := H) hσ hH c
  have hpow : (CFC.rpow (D * H * D) (-(1 / c))).PosDef :=
    cMatrix_rpow_posDef_of_posDef hinner (-(1 / c))
  exact (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hpow)).1

/-- The source-shaped weight cancels the two reference powers in the
sandwiched low-`α` inner matrix under the trace.

This is the algebraic part of Gour's Young lower bound before applying
reverse Holder: the test weight `σ^(-c/2) H σ^(-c/2)` pairs with
`σ^(c/2) ρ σ^(c/2)` as `Tr[ρH]`. -/
theorem sandwichedRenyiQInner_mul_sourceWeight_trace_re_eq
    {ρ σ H : CMatrix a} (hσ : σ.PosDef) {α c : ℝ}
    (hc : c = (1 - α) / α) :
    let D : CMatrix a := CFC.rpow σ (-(c / 2))
    (((sandwichedRenyiQInner ρ σ α) * (D * H * D)).trace).re =
      ((ρ * H).trace).re := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ s
  let D : CMatrix a := CFC.rpow σ (-s)
  have hc_half : c / 2 = s := by
    rw [hc]
    ring
  have hD_def : CFC.rpow σ (-(c / 2)) = D := by
    simp [D, s, hc_half]
  have hCD : C * D = 1 := by
    simpa [C, D] using
      (CFC.rpow_mul_rpow_neg (a := σ) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  have hDC : D * C = 1 := by
    simpa [C, D] using
      (CFC.rpow_neg_mul_rpow (a := σ) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  dsimp only
  rw [hD_def]
  change ((((C * ρ * C) * (D * H * D)).trace).re = ((ρ * H).trace).re)
  calc
    (((C * ρ * C) * (D * H * D)).trace).re =
        (((D * H * D) * (C * ρ * C)).trace).re := by
          exact congrArg Complex.re (Matrix.trace_mul_comm (C * ρ * C) (D * H * D))
    _ = (((D * H * ρ) * C).trace).re := by
          have hmat :
              (D * H * D) * (C * ρ * C) = (D * H * ρ) * C := by
            calc
            (D * H * D) * (C * ρ * C) =
                (D * H) * (D * (C * (ρ * C))) := by
                  simp [Matrix.mul_assoc]
            _ = (D * H) * ((D * C) * (ρ * C)) := by
                  rw [← Matrix.mul_assoc D C (ρ * C)]
            _ = (D * H) * (ρ * C) := by
                  rw [hDC, Matrix.one_mul]
            _ = (D * H * ρ) * C := by
                  simp [Matrix.mul_assoc]
          exact congrArg (fun X : CMatrix a => X.trace.re) hmat
    _ = ((C * (D * H * ρ)).trace).re := by
          exact congrArg Complex.re (Matrix.trace_mul_comm (D * H * ρ) C)
    _ = ((H * ρ).trace).re := by
          have hmat : C * (D * H * ρ) = H * ρ := by
            calc
            C * (D * H * ρ) = C * (D * (H * ρ)) := by
              simp [Matrix.mul_assoc]
            _ = (C * D) * (H * ρ) := by
              rw [Matrix.mul_assoc C D (H * ρ)]
            _ = H * ρ := by
              rw [hCD, Matrix.one_mul]
          exact congrArg (fun X : CMatrix a => X.trace.re) hmat
    _ = ((ρ * H).trace).re := by
          exact congrArg Complex.re (Matrix.trace_mul_comm H ρ)

omit [Fintype a] [DecidableEq a] in
private theorem lowAlpha_rpow_bound_to_fixedWeight
    {Q x y α c : ℝ} (hQ : 0 ≤ Q) (hx : 0 ≤ x) (hy : 0 < y)
    (hα_pos : 0 < α) (hc : c = (1 - α) / α)
    (hbound : Q ^ (1 / α) ≤ x * y ^ c) :
    Q ≤ x ^ α * y ^ (1 - α) := by
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  have hQ_pow : (Q ^ (1 / α)) ^ α = Q := by
    simpa [one_div] using Real.rpow_inv_rpow hQ hα_ne
  have hleft_nonneg : 0 ≤ Q ^ (1 / α) :=
    Real.rpow_nonneg hQ (1 / α)
  have hraise :
      (Q ^ (1 / α)) ^ α ≤ (x * y ^ c) ^ α :=
    Real.rpow_le_rpow hleft_nonneg hbound hα_pos.le
  have hyc_nonneg : 0 ≤ y ^ c := Real.rpow_nonneg hy.le c
  have hmul_pow :
      (x * y ^ c) ^ α = x ^ α * (y ^ c) ^ α := by
    rw [Real.mul_rpow hx hyc_nonneg]
  have hy_pow :
      (y ^ c) ^ α = y ^ (1 - α) := by
    calc
      (y ^ c) ^ α = y ^ (c * α) := by
        rw [← Real.rpow_mul hy.le c α]
      _ = y ^ (1 - α) := by
        rw [hc]
        field_simp [hα_ne]
  calc
    Q = (Q ^ (1 / α)) ^ α := hQ_pow.symm
    _ ≤ (x * y ^ c) ^ α := hraise
    _ = x ^ α * y ^ (1 - α) := by
      rw [hmul_pow, hy_pow]

/-- The normalized Gour source witness has the expected reverse-Holder
power.

This is the matrix-power core of the low-`α` Young lower bound.  For
`c = (1 - α) / α` and
`W = σ^(-c/2) H σ^(-c/2)`, the normalized witness
`N = Tr[W^(-1/c)]⁻¹ W^(-1/c)` satisfies
`N^(1 - 1/α) = Tr[W^(-1/c)]^c W`. -/
theorem frankLiebSourceWitness_rpow_eq
    [Nonempty a] {σ H : CMatrix a} (hσ : σ.PosDef) (hH : H.PosDef)
    {α c : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hc : c = (1 - α) / α) :
    let D : CMatrix a := CFC.rpow σ (-(c / 2))
    let W : CMatrix a := D * H * D
    let y : ℝ := frankLiebSourceSigmaTerm σ H c
    let Y : CMatrix a := CFC.rpow W (-(1 / c))
    CFC.rpow ((y⁻¹ : ℝ) • Y : CMatrix a) (1 - 1 / α) =
      (y ^ c : ℝ) • W := by
  let D : CMatrix a := CFC.rpow σ (-(c / 2))
  let W : CMatrix a := D * H * D
  let y : ℝ := frankLiebSourceSigmaTerm σ H c
  let Y : CMatrix a := CFC.rpow W (-(1 / c))
  have hα_pos : 0 < α := by linarith
  have hc_pos : 0 < c := by
    rw [hc]
    exact sandwichedRenyiQ_frankLiebExponent_pos hα_half hα_lt_one
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hy_pos : 0 < y := by
    simpa [y] using frankLiebSourceSigmaTerm_pos
      (a := a) (σ := σ) (H := H) hσ hH c
  have hW : W.PosDef := by
    simpa [W, D] using frankLiebSourceSigmaTerm_inner_posDef
      (a := a) (σ := σ) (H := H) hσ hH c
  have hY : Y.PosSemidef := by
    simpa [Y] using cMatrix_rpow_posSemidef (A := W) (s := -(1 / c)) hW.posSemidef
  have hscale_nonneg : 0 ≤ y⁻¹ := inv_nonneg.mpr hy_pos.le
  have hexp : 1 - 1 / α = -c := by
    rw [hc]
    field_simp [ne_of_gt hα_pos]
    ring
  have hYpow : CFC.rpow Y (1 - 1 / α) = W := by
    have hr_ne : (-(1 / c) : ℝ) ≠ 0 := by
      exact neg_ne_zero.mpr (one_div_ne_zero hc_ne)
    have hrt : (-(1 / c) : ℝ) * (1 - 1 / α) = (1 : ℝ) := by
      rw [hexp]
      field_simp [hc_ne]
    calc
      CFC.rpow Y (1 - 1 / α) =
          CFC.rpow W (1 : ℝ) := by
            simpa [Y] using
              cMatrix_rpow_rpow_of_posDef (A := W) hW hr_ne hrt
      _ = W := by
            exact CFC.rpow_one W
              (ha := Matrix.nonneg_iff_posSemidef.mpr hW.posSemidef)
  have hscale :
      y⁻¹ ^ (1 - 1 / α) = y ^ c := by
    rw [hexp]
    rw [Real.inv_rpow hy_pos.le]
    rw [Real.rpow_neg hy_pos.le]
    simp
  calc
    CFC.rpow ((y⁻¹ : ℝ) • Y : CMatrix a) (1 - 1 / α) =
        (y⁻¹ ^ (1 - 1 / α) : ℝ) • CFC.rpow Y (1 - 1 / α) := by
          exact cMatrix_rpow_real_smul_posSemidef_schatten hY hscale_nonneg
    _ = (y ^ c : ℝ) • W := by
          rw [hscale, hYpow]

/-- Gour source-shaped reverse-Holder/Young lower bound for positive
definite inputs.

This proves the noncommutative analogue of the scalar Young lower bound in
`BookQRT.tex`, lines 12066--12070, but still in the source sigma-term form
`Tr[(σ^(-c/2) H σ^(-c/2))^(-1/c)]`.  The remaining source-alignment step is
the `LL*`/`L*L` spectral identity rewriting this sigma term to the existing
Frank--Lieb/Epstein term. -/
theorem sandwichedRenyiQ_le_frankLiebSourceFixedWeightObjective_posDef
    [Nonempty a] {ρ σ H : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hH : H.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ≤
      frankLiebSourceFixedWeightObjective ρ σ H α ((1 - α) / α) := by
  let c : ℝ := (1 - α) / α
  let D : CMatrix a := CFC.rpow σ (-(c / 2))
  let W : CMatrix a := D * H * D
  let y : ℝ := frankLiebSourceSigmaTerm σ H c
  let Y : CMatrix a := CFC.rpow W (-(1 / c))
  let N : CMatrix a := (y⁻¹ : ℝ) • Y
  let Q : ℝ := sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α
  let x : ℝ := ((ρ * H).trace).re
  let M : CMatrix a := sandwichedRenyiQInner ρ σ α
  have hα_pos : 0 < α := by linarith
  have hα_half_le : 1 / 2 ≤ α := le_of_lt hα_half
  have hQ_nonneg : 0 ≤ Q := by
    have hM : M.PosSemidef := by
      simpa [M] using sandwichedRenyiQInner_posSemidef hρ.posSemidef hσ.posSemidef α
    have hpow_nonneg : 0 ≤ psdTracePower M hM α :=
      psdTracePower_nonneg M hM α
    simpa [Q, M, sandwichedRenyiQ_eq_psdTracePower_QInner] using hpow_nonneg
  have hx_nonneg : 0 ≤ x := by
    exact le_of_lt (by
      simpa [x] using _root_.QIT.trace_mul_posDef_re_pos hρ hH)
  have hW : W.PosDef := by
    simpa [W, D] using frankLiebSourceSigmaTerm_inner_posDef
      (a := a) (σ := σ) (H := H) hσ hH c
  have hy_pos : 0 < y := by
    simpa [y] using frankLiebSourceSigmaTerm_pos
      (a := a) (σ := σ) (H := H) hσ hH c
  have hY : Y.PosDef := by
    simpa [Y] using cMatrix_rpow_posDef_of_posDef hW (-(1 / c))
  have hNdef : N.PosDef := by
    simpa [N] using Matrix.PosDef.smul hY (inv_pos.mpr hy_pos)
  have hN : N.PosSemidef := hNdef.posSemidef
  have hNtr : N.trace.re = 1 := by
    have hy_ne : y ≠ 0 := ne_of_gt hy_pos
    have hYtr : Y.trace.re = y := by
      simp [Y, y, frankLiebSourceSigmaTerm, W, D]
    calc
      N.trace.re = (((y⁻¹ : ℝ) • Y : CMatrix a).trace).re := by
        rfl
      _ = y⁻¹ * Y.trace.re := by
        simp [Matrix.trace_smul, Complex.mul_re]
      _ = y⁻¹ * y := by rw [hYtr]
      _ = 1 := inv_mul_cancel₀ hy_ne
  have hSupport : Matrix.Supports M N :=
    Matrix.Supports.of_right_posDef M N hNdef
  have hvar :
      Q ^ (1 / α) ≤ ((M * CFC.rpow N (1 - 1 / α)).trace).re := by
    simpa [Q, M] using
      sandwichedRenyiQ_reverseHolder_norm_le_trace
        (ρ := ρ) (σ := σ) (N := N)
        hρ.posSemidef hσ.posSemidef hN hNtr hα_half_le hα_lt_one hSupport
  have hNrpow :
      CFC.rpow N (1 - 1 / α) = (y ^ c : ℝ) • W := by
    simpa [N, Y, W, D, y, c] using
      frankLiebSourceWitness_rpow_eq
        (a := a) (σ := σ) (H := H) hσ hH hα_half hα_lt_one (rfl : c = (1 - α) / α)
  have htraceW : ((M * W).trace).re = x := by
    simpa [M, W, D, x, c] using
      sandwichedRenyiQInner_mul_sourceWeight_trace_re_eq
        (a := a) (ρ := ρ) (σ := σ) (H := H) hσ
        (α := α) (c := c) (rfl : c = (1 - α) / α)
  have htrace :
      ((M * CFC.rpow N (1 - 1 / α)).trace).re = x * y ^ c := by
    rw [hNrpow]
    calc
      ((M * ((y ^ c : ℝ) • W : CMatrix a)).trace).re =
          y ^ c * ((M * W).trace).re := by
            simp [Matrix.trace_smul, Complex.mul_re]
      _ = x * y ^ c := by
            rw [htraceW]
            ring
  have hbound : Q ^ (1 / α) ≤ x * y ^ c := by
    rw [htrace] at hvar
    exact hvar
  have hscalar :
      Q ≤ x ^ α * y ^ (1 - α) :=
    lowAlpha_rpow_bound_to_fixedWeight
      (Q := Q) (x := x) (y := y) (α := α) (c := c)
      hQ_nonneg hx_nonneg hy_pos hα_pos (rfl : c = (1 - α) / α) hbound
  simpa [frankLiebSourceFixedWeightObjective, Q, x, y, c] using hscalar

/-- Positive-definite matrices with the same characteristic polynomial have
the same real trace of every real power.

This packages the finite-dimensional spectral bookkeeping needed for Gour's
`LL*`/`L*L` step. -/
theorem psdTracePower_eq_of_posDef_charpoly_eq
    {A B : CMatrix a} (hA : A.PosDef) (hB : B.PosDef) (p : ℝ)
    (hchar : A.charpoly = B.charpoly) :
    psdTracePower A hA.posSemidef p =
      psdTracePower B hB.posSemidef p := by
  have heigs :
      hA.posSemidef.isHermitian.eigenvalues =
        hB.posSemidef.isHermitian.eigenvalues := by
    exact
      ((hA.posSemidef.isHermitian).eigenvalues_eq_eigenvalues_iff
        hB.posSemidef.isHermitian).mpr hchar
  rw [psdTracePower_eq_sum_eigenvalues_rpow,
    psdTracePower_eq_sum_eigenvalues_rpow]
  rw [heigs]

/-- Gour's source sigma term equals the Frank--Lieb/Epstein sigma term.

This is the finite-dimensional `LL*`/`L*L` spectral identity cited in
`BookQRT.tex`, line 12058.  It rewrites
`Tr[(σ^(-c/2) H σ^(-c/2))^(-1/c)]` as
`Tr[(H^(-1/2) σ^c H^(-1/2))^(1/c)]`. -/
theorem frankLiebSourceSigmaTerm_eq_frankLieb_sigmaTerm
    {σ H : CMatrix a} (hσ : σ.PosDef) (hH : H.PosDef) {c : ℝ} :
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    frankLiebSourceSigmaTerm σ H c =
      ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re := by
  let s : ℝ := c / 2
  let D : CMatrix a := CFC.rpow σ (-s)
  let S : CMatrix a := CFC.rpow σ s
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let L : CMatrix a := D * H * D
  let R : CMatrix a := K * CFC.rpow σ c * K
  let X : CMatrix a := S * K
  have hL : L.PosDef := by
    simpa [L, D, s] using frankLiebSourceSigmaTerm_inner_posDef
      (a := a) (σ := σ) (H := H) hσ hH c
  have hR : R.PosDef := by
    simpa [R, K] using frankLieb_sigmaTerm_inner_posDef
      (a := a) (H := H) (σ := σ) hH hσ c
  have hSstar : star S = S := by
    exact (cMatrix_rpow_posDef_of_posDef hσ s).isHermitian.eq
  have hKstar : star K = K := by
    exact (cMatrix_rpow_posDef_of_posDef hH (-(1 / 2 : ℝ))).isHermitian.eq
  have hDS : D * S = 1 := by
    simpa [D, S, s] using
      (CFC.rpow_neg_mul_rpow (a := σ) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  have hSD : S * D = 1 := by
    simpa [D, S, s] using
      (CFC.rpow_mul_rpow_neg (a := σ) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  have hK2 : K * K = H⁻¹ := by
    have hpow : K * K = CFC.rpow H (-1 : ℝ) := by
      calc
        K * K = CFC.rpow H (-(1 / 2 : ℝ) + -(1 / 2 : ℝ)) := by
          simpa [K] using
            (CFC.rpow_add (a := H) (x := -(1 / 2 : ℝ))
              (y := -(1 / 2 : ℝ)) hH.isUnit).symm
        _ = CFC.rpow H (-1 : ℝ) := by ring_nf
    have hinv : CFC.rpow H (-1 : ℝ) = H⁻¹ := by
      calc
        CFC.rpow H (-1 : ℝ) = CFC.rpow H⁻¹ (1 : ℝ) :=
          (cMatrix_rpow_nonsing_inv_eq_rpow_neg
            (a := a) (B := H) hH (1 : ℝ)).symm
        _ = H⁻¹ := by
          exact CFC.rpow_one H⁻¹
            (ha := Matrix.nonneg_iff_posSemidef.mpr hH.inv.posSemidef)
    rw [hpow, hinv]
  have hS2 : S * S = CFC.rpow σ c := by
    calc
      S * S = CFC.rpow σ (s + s) := by
        simpa [S] using
          (CFC.rpow_add (a := σ) (x := s) (y := s) hσ.isUnit).symm
      _ = CFC.rpow σ c := by
        congr 1
        simp [s]
  let V : CMatrix a := S * H⁻¹ * S
  have hLV : L * V = 1 := by
    calc
      L * V = (D * H * D) * (S * H⁻¹ * S) := rfl
      _ = (D * H) * ((D * S) * (H⁻¹ * S)) := by
        simp [Matrix.mul_assoc]
      _ = (D * H) * (H⁻¹ * S) := by
        rw [hDS, Matrix.one_mul]
      _ = D * (H * H⁻¹) * S := by
        simp [Matrix.mul_assoc]
      _ = D * (1 : CMatrix a) * S := by
        rw [Matrix.mul_nonsing_inv H ((Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit)]
      _ = 1 := by
        simpa [Matrix.mul_assoc] using hDS
  have hLinv : L⁻¹ = V := by
    have hdet : IsUnit L.det := (Matrix.isUnit_iff_isUnit_det L).mp hL.isUnit
    calc
      L⁻¹ = L⁻¹ * 1 := by simp
      _ = L⁻¹ * (L * V) := by rw [hLV]
      _ = (L⁻¹ * L) * V := by simp [Matrix.mul_assoc]
      _ = V := by
        rw [Matrix.nonsing_inv_mul L hdet, Matrix.one_mul]
  have hXstar : star X = K * S := by
    simp [X, hSstar, hKstar]
  have hX_left : X * star X = L⁻¹ := by
    calc
      X * star X = (S * K) * (K * S) := by
        rw [hXstar]
      _ = S * (K * K) * S := by
        simp [Matrix.mul_assoc]
      _ = S * H⁻¹ * S := by
        rw [hK2]
      _ = L⁻¹ := hLinv.symm
  have hX_right : star X * X = R := by
    calc
      star X * X = (K * S) * (S * K) := by
        rw [hXstar]
      _ = K * (S * S) * K := by
        simp [Matrix.mul_assoc]
      _ = K * CFC.rpow σ c * K := by
        rw [hS2]
      _ = R := rfl
  have hchar : (L⁻¹).charpoly = R.charpoly := by
    calc
      (L⁻¹).charpoly = (X * star X).charpoly := by rw [hX_left]
      _ = (star X * X).charpoly := Matrix.charpoly_mul_comm X (star X)
      _ = R.charpoly := by rw [hX_right]
  have htrace :
      psdTracePower L⁻¹ hL.inv.posSemidef (1 / c) =
        psdTracePower R hR.posSemidef (1 / c) :=
    psdTracePower_eq_of_posDef_charpoly_eq hL.inv hR (1 / c) hchar
  calc
    frankLiebSourceSigmaTerm σ H c =
        psdTracePower L⁻¹ hL.inv.posSemidef (1 / c) := by
          change ((CFC.rpow L (-(1 / c))).trace).re =
            ((CFC.rpow L⁻¹ (1 / c)).trace).re
          rw [← cMatrix_rpow_nonsing_inv_eq_rpow_neg
            (a := a) (B := L) hL (1 / c)]
    _ = psdTracePower R hR.posSemidef (1 / c) := htrace
    _ = ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re := by
          rfl

/-- The fixed-weight Frank--Lieb trace term is the Epstein trace primitive
with `K = H^(-1/2)`.

This is the source-notation alignment from
`Tr[(H^(-1/2) σ^c H^(-1/2))^(1/c)]` to the reusable Epstein expression
`Tr[(K† σ^c K)^(1/c)]`. -/
theorem frankLieb_sigmaTerm_eq_epsteinTraceTerm
    {H σ : CMatrix a} (hH : H.PosDef) (c : ℝ) :
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re =
      epsteinTraceTerm K σ c := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  have hKstar : star K = K := by
    simpa [K] using (frankLieb_weight_isHermitian (a := a) hH).eq
  have hKstar' : star (CFC.rpow H (-(1 / 2 : ℝ))) =
      CFC.rpow H (-(1 / 2 : ℝ)) := by
    simpa [K] using hKstar
  dsimp only [epsteinTraceTerm]
  rw [hKstar']

/-- Unrestricted fixed-weight Frank--Lieb sigma-term concavity.

For a fixed positive-definite weight `H` and `0 < c < 1`, the map
`σ ↦ Tr[(H^{-1/2} σ^c H^{-1/2})^{1/c}]` is concave on PSD matrices. -/
theorem frankLieb_sigmaTerm_concave
    {H σ₁ σ₂ : CMatrix a} (hH : H.PosDef)
    (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    {c t : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
    t * ((CFC.rpow (K * CFC.rpow σ₁ c * K) (1 / c)).trace).re +
        (1 - t) * ((CFC.rpow (K * CFC.rpow σ₂ c * K) (1 / c)).trace).re ≤
      ((CFC.rpow (K * CFC.rpow σt c * K) (1 / c)).trace).re := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  have hEpstein :
      t * epsteinTraceTerm K σ₁ c + (1 - t) * epsteinTraceTerm K σ₂ c ≤
        epsteinTraceTerm K σt c := by
    simpa [σt] using
      epsteinTraceTerm_concave (a := a) K hσ₁ hσ₂ hc_pos hc_lt_one ht0 ht1
  have h₁ :
      ((CFC.rpow (K * CFC.rpow σ₁ c * K) (1 / c)).trace).re =
        epsteinTraceTerm K σ₁ c := by
    simpa [K] using
      frankLieb_sigmaTerm_eq_epsteinTraceTerm
        (a := a) (H := H) (σ := σ₁) hH c
  have h₂ :
      ((CFC.rpow (K * CFC.rpow σ₂ c * K) (1 / c)).trace).re =
        epsteinTraceTerm K σ₂ c := by
    simpa [K] using
      frankLieb_sigmaTerm_eq_epsteinTraceTerm
        (a := a) (H := H) (σ := σ₂) hH c
  have ht :
      ((CFC.rpow (K * CFC.rpow σt c * K) (1 / c)).trace).re =
        epsteinTraceTerm K σt c := by
    simpa [K] using
      frankLieb_sigmaTerm_eq_epsteinTraceTerm
        (a := a) (H := H) (σ := σt) hH c
  dsimp only
  rw [h₁, h₂, ht]
  exact hEpstein

/-- Fixed-weight Frank--Lieb variational objective.

For a fixed positive-definite weight `H`, this is the source-shaped term
`(Tr ρH)^α * Tr[(H^{-1/2} σ^c H^{-1/2})^{1/c}]^{1-α}` appearing in the
low-`α` reverse-Holder bridge after setting `c = (1 - α) / α`. -/
def frankLiebFixedWeightObjective
    (ρ σ H : CMatrix a) (α c : ℝ) : ℝ :=
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  (((ρ * H).trace).re ^ α) *
    (((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re ^ (1 - α))

/-- Gour/Frank--Lieb fixed-weight lower bound in the local
Frank--Lieb/Epstein notation.

This is the source-shaped Young lower bound after applying the `LL*`/`L*L`
spectral rewrite, so it is directly compatible with
`sandwichedRenyiQFixedWeightValueSet`. -/
theorem sandwichedRenyiQ_le_frankLiebFixedWeightObjective_posDef
    [Nonempty a] {ρ σ H : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hH : H.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ≤
      frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) := by
  let c : ℝ := (1 - α) / α
  have hsource :
      sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ≤
        frankLiebSourceFixedWeightObjective ρ σ H α c := by
    simpa [c] using
      sandwichedRenyiQ_le_frankLiebSourceFixedWeightObjective_posDef
        (a := a) (ρ := ρ) (σ := σ) (H := H)
        hρ hσ hH hα_half hα_lt_one
  have hsigma :
      frankLiebSourceSigmaTerm σ H c =
        (let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
        ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re) := by
    simpa [c] using frankLiebSourceSigmaTerm_eq_frankLieb_sigmaTerm
      (a := a) (σ := σ) (H := H) hσ hH (c := c)
  have hobj :
      frankLiebSourceFixedWeightObjective ρ σ H α c =
        frankLiebFixedWeightObjective ρ σ H α c := by
    unfold frankLiebSourceFixedWeightObjective frankLiebFixedWeightObjective
    rw [hsigma]
  exact hsource.trans_eq hobj

/-- Source-shaped additive Frank--Lieb/Young variational objective.

This is the finite-dimensional low-`α` objective in Gour's presentation
(`BookQRT.tex`, lines 12066--12070) after writing
`c = (1 - α) / α` and the positive weight as `H`.

The existing `frankLiebFixedWeightObjective` is the weighted geometric mean of
the two nonnegative summands in this additive objective. -/
def frankLiebAdditiveObjective
    (ρ σ H : CMatrix a) (α c : ℝ) : ℝ :=
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  α * ((ρ * H).trace).re +
    (1 - α) *
      ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re

/-- The fixed-weight multiplicative objective is bounded by the source-shaped
additive Frank--Lieb/Young objective.

This is exactly the scalar weighted AM--GM/Young step in Gour's low-`α`
variational spine; the two matrix inputs are only used to establish
nonnegativity of the scalar trace terms. -/
theorem frankLiebFixedWeightObjective_le_additiveObjective
    {ρ σ H : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hH : H.PosDef) {α c : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    frankLiebFixedWeightObjective ρ σ H α c ≤
      frankLiebAdditiveObjective ρ σ H α c := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let x : ℝ := ((ρ * H).trace).re
  let y : ℝ := ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re
  have hx : 0 ≤ x := by
    simpa [x] using cMatrix_trace_mul_posSemidef_re_nonneg hρ hH.posSemidef
  have hy : 0 ≤ y := by
    simpa [y, K] using frankLieb_sigmaTerm_nonneg
      (a := a) (H := H) (σ := σ) hH hσ c
  have h1α : 0 ≤ 1 - α := sub_nonneg.mpr hα1
  have hweights : α + (1 - α) = (1 : ℝ) := by ring
  have hyoung : x ^ α * y ^ (1 - α) ≤ α * x + (1 - α) * y :=
    Real.geom_mean_le_arith_mean2_weighted hα0 h1α hx hy hweights
  simpa [frankLiebFixedWeightObjective, frankLiebAdditiveObjective, K, x, y]
    using hyoung

/-- Positive scalar rescaling of the Frank--Lieb weight in the additive
Gour/Young objective.

This is the unrestricted-weight bookkeeping needed before optimizing the
source additive objective over the scale of `H`. -/
theorem frankLiebAdditiveObjective_real_smul_weight
    {ρ σ H : CMatrix a} (hH : H.PosDef) (hσ : σ.PosSemidef)
    {lambda α c : ℝ} (hlambda_pos : 0 < lambda) (hc_pos : 0 < c) :
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    frankLiebAdditiveObjective ρ σ (lambda • H : CMatrix a) α c =
      α * (lambda * ((ρ * H).trace).re) +
        (1 - α) *
          (lambda ^ (-(1 / c)) *
            ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re) := by
  let Klam : CMatrix a := CFC.rpow (lambda • H : CMatrix a) (-(1 / 2 : ℝ))
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  have hleft_trace :
      (((ρ * (lambda • H : CMatrix a)).trace).re) =
        lambda * ((ρ * H).trace).re := by
    calc
      ((ρ * (lambda • H : CMatrix a)).trace).re =
          (((lambda : ℂ) • (ρ * H : CMatrix a)).trace).re := by
            simp
      _ = lambda * ((ρ * H).trace).re := by
            simp [Matrix.trace_smul, Complex.mul_re]
  have hsigma :
      ((CFC.rpow (Klam * CFC.rpow σ c * Klam) (1 / c)).trace).re =
        lambda ^ (-(1 / c)) *
          ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re := by
    simpa [Klam, K] using
      frankLieb_sigmaTerm_real_smul_weight
        (a := a) (H := H) (σ := σ) hH hσ hlambda_pos hc_pos
  dsimp only
  unfold frankLiebAdditiveObjective
  change
    α * (((ρ * (lambda • H : CMatrix a)).trace).re) +
        (1 - α) *
          ((CFC.rpow (Klam * CFC.rpow σ c * Klam) (1 / c)).trace).re =
      α * (lambda * ((ρ * H).trace).re) +
        (1 - α) *
          (lambda ^ (-(1 / c)) *
            ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re)
  rw [hleft_trace, hsigma]

/-- Concavity of the source-shaped additive Gour/Frank--Lieb objective for a
fixed positive weight.

This is the direct formal counterpart of the fixed-`H` part of Gour's
low-`α` variational proof: the `ρ` contribution is affine and the `σ`
contribution is Epstein/Frank--Lieb concave. -/
theorem frankLiebAdditiveObjective_concave
    {H ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hH : H.PosDef)
    (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    {α c t : ℝ} (hα1 : α ≤ 1)
    (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * frankLiebAdditiveObjective ρ₁ σ₁ H α c +
        (1 - t) * frankLiebAdditiveObjective ρ₂ σ₂ H α c ≤
      frankLiebAdditiveObjective
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂) H α c := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let ρt : CMatrix a := cMatrixConvexCombination t ρ₁ ρ₂
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  let x₁ : ℝ := ((ρ₁ * H).trace).re
  let x₂ : ℝ := ((ρ₂ * H).trace).re
  let xt : ℝ := ((ρt * H).trace).re
  let y₁ : ℝ := ((CFC.rpow (K * CFC.rpow σ₁ c * K) (1 / c)).trace).re
  let y₂ : ℝ := ((CFC.rpow (K * CFC.rpow σ₂ c * K) (1 / c)).trace).re
  let yt : ℝ := ((CFC.rpow (K * CFC.rpow σt c * K) (1 / c)).trace).re
  have hxt : xt = t * x₁ + (1 - t) * x₂ := by
    have hmul :
        ρt * H = cMatrixConvexCombination t (ρ₁ * H) (ρ₂ * H) := by
      dsimp [ρt]
      rw [cMatrixConvexCombination_eq_real_smul]
      rw [cMatrixConvexCombination_eq_real_smul]
      simp [Matrix.add_mul]
    change ((ρt * H).trace).re = t * x₁ + (1 - t) * x₂
    rw [hmul]
    simpa [x₁, x₂] using cMatrixConvexCombination_trace_re t (ρ₁ * H) (ρ₂ * H)
  have hy_conc : t * y₁ + (1 - t) * y₂ ≤ yt := by
    simpa [y₁, y₂, yt, K, σt] using
      frankLieb_sigmaTerm_concave
        (a := a) (H := H) (σ₁ := σ₁) (σ₂ := σ₂)
        hH hσ₁ hσ₂ hc_pos hc_lt_one ht0 ht1
  have h1α : 0 ≤ 1 - α := sub_nonneg.mpr hα1
  have hscaled_y :
      (1 - α) * (t * y₁ + (1 - t) * y₂) ≤ (1 - α) * yt :=
    mul_le_mul_of_nonneg_left hy_conc h1α
  calc
    t * frankLiebAdditiveObjective ρ₁ σ₁ H α c +
        (1 - t) * frankLiebAdditiveObjective ρ₂ σ₂ H α c =
        α * (t * x₁ + (1 - t) * x₂) +
          (1 - α) * (t * y₁ + (1 - t) * y₂) := by
          simp [frankLiebAdditiveObjective, x₁, x₂, y₁, y₂, K]
          ring
    _ ≤ α * (t * x₁ + (1 - t) * x₂) + (1 - α) * yt :=
          by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hscaled_y (α * (t * x₁ + (1 - t) * x₂))
    _ = frankLiebAdditiveObjective ρt σt H α c := by
          simp [frankLiebAdditiveObjective, xt, yt, K, hxt]

private theorem frankLieb_additive_optimalScale_eq_weightedGeom
    {x y α : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    let lambda : ℝ := (y / x) ^ (1 - α)
    α * (lambda * x) +
        (1 - α) * (lambda ^ (-(α / (1 - α))) * y) =
      x ^ α * y ^ (1 - α) := by
  let lambda : ℝ := (y / x) ^ (1 - α)
  have hratio_pos : 0 < y / x := div_pos hy hx
  have hden_pos : 0 < 1 - α := sub_pos.mpr hα_lt_one
  have hlambda_x : lambda * x = x ^ α * y ^ (1 - α) := by
    calc
      lambda * x = (y / x) ^ (1 - α) * x := rfl
      _ = (y ^ (1 - α) / x ^ (1 - α)) * x := by
            rw [Real.div_rpow hy.le hx.le]
      _ = y ^ (1 - α) * (x / x ^ (1 - α)) := by
            field_simp [Real.rpow_pos_of_pos hx (1 - α)]
      _ = y ^ (1 - α) * x ^ α := by
            have hxpow : x / x ^ (1 - α) = x ^ α := by
              calc
                x / x ^ (1 - α) = x ^ (1 : ℝ) / x ^ (1 - α) := by
                  rw [Real.rpow_one]
                _ = x ^ (1 - (1 - α)) := by
                  rw [← Real.rpow_sub hx 1 (1 - α)]
                _ = x ^ α := by ring_nf
            rw [hxpow]
      _ = x ^ α * y ^ (1 - α) := by ring
  have hlambda_y :
      lambda ^ (-(α / (1 - α))) * y =
        x ^ α * y ^ (1 - α) := by
    have hexp : (1 - α) * (-(α / (1 - α))) = -α := by
      field_simp [ne_of_gt hden_pos]
    calc
      lambda ^ (-(α / (1 - α))) * y =
          ((y / x) ^ (1 - α)) ^ (-(α / (1 - α))) * y := rfl
      _ = (y / x) ^ ((1 - α) * (-(α / (1 - α)))) * y := by
            rw [Real.rpow_mul hratio_pos.le]
      _ = (y / x) ^ (-α) * y := by rw [hexp]
      _ = ((y / x) ^ α)⁻¹ * y := by
            rw [Real.rpow_neg hratio_pos.le]
      _ = (y ^ α / x ^ α)⁻¹ * y := by
            rw [Real.div_rpow hy.le hx.le]
      _ = (x ^ α / y ^ α) * y := by
            field_simp [Real.rpow_pos_of_pos hx α, Real.rpow_pos_of_pos hy α]
      _ = x ^ α * (y / y ^ α) := by
            field_simp [Real.rpow_pos_of_pos hy α]
      _ = x ^ α * y ^ (1 - α) := by
            have hypow : y / y ^ α = y ^ (1 - α) := by
              calc
                y / y ^ α = y ^ (1 : ℝ) / y ^ α := by
                  rw [Real.rpow_one]
                _ = y ^ (1 - α) := by
                  rw [← Real.rpow_sub hy 1 α]
            rw [hypow]
  dsimp only
  rw [hlambda_x, hlambda_y]
  ring

/-- At the source Young-optimizer scale, the additive Gour/Frank--Lieb
objective agrees with the fixed-weight multiplicative objective.

This is the source-faithful bridge from Gour's additive variational formula to
the fixed-weight objective used by the existing concavity/sInf handoff.  The
statement is intentionally full-rank on both matrix inputs; singular PSD
closure is a later step. -/
theorem frankLiebAdditiveObjective_optimalScale_eq_fixedWeight_posDef
    [Nonempty a] {ρ σ H : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hH : H.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    let c : ℝ := (1 - α) / α
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    let x : ℝ := ((ρ * H).trace).re
    let y : ℝ := ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re
    let lambda : ℝ := (y / x) ^ (1 - α)
    frankLiebAdditiveObjective ρ σ (lambda • H : CMatrix a) α c =
      frankLiebFixedWeightObjective ρ σ H α c := by
  let c : ℝ := (1 - α) / α
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let x : ℝ := ((ρ * H).trace).re
  let y : ℝ := ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re
  let lambda : ℝ := (y / x) ^ (1 - α)
  have hα_pos : 0 < α := by linarith
  have hc_pos : 0 < c := by
    simpa [c] using sandwichedRenyiQ_frankLiebExponent_pos hα_half hα_lt_one
  have hx : 0 < x := by
    simpa [x] using _root_.QIT.trace_mul_posDef_re_pos hρ hH
  have hy : 0 < y := by
    simpa [y, K, c] using frankLieb_sigmaTerm_pos
      (a := a) (H := H) (σ := σ) hH hσ c
  have hlambda_pos : 0 < lambda := by
    dsimp [lambda]
    exact Real.rpow_pos_of_pos (div_pos hy hx) (1 - α)
  have hc_inv : 1 / c = α / (1 - α) := by
    dsimp [c]
    field_simp [ne_of_gt hα_pos, ne_of_gt (sub_pos.mpr hα_lt_one)]
  have hscale :
      frankLiebAdditiveObjective ρ σ (lambda • H : CMatrix a) α c =
        α * (lambda * x) +
          (1 - α) * (lambda ^ (-(1 / c)) * y) := by
    simpa [K, x, y, c, lambda] using
      frankLiebAdditiveObjective_real_smul_weight
        (a := a) (ρ := ρ) (σ := σ) (H := H)
        hH hσ.posSemidef hlambda_pos hc_pos
  have hopt :
      α * (lambda * x) +
          (1 - α) * (lambda ^ (-(α / (1 - α))) * y) =
        x ^ α * y ^ (1 - α) := by
    simpa [lambda] using
      frankLieb_additive_optimalScale_eq_weightedGeom
        (x := x) (y := y) (α := α) hx hy hα_pos hα_lt_one
  calc
    frankLiebAdditiveObjective ρ σ (lambda • H : CMatrix a) α c =
        α * (lambda * x) + (1 - α) * (lambda ^ (-(1 / c)) * y) := hscale
    _ = α * (lambda * x) + (1 - α) * (lambda ^ (-(α / (1 - α))) * y) := by
          rw [hc_inv]
    _ = x ^ α * y ^ (1 - α) := hopt
    _ = frankLiebFixedWeightObjective ρ σ H α c := by
          simp [frankLiebFixedWeightObjective, K, x, y, c]

/-- The fixed-weight Frank--Lieb objective vanishes when the left input is
zero. -/
theorem frankLiebFixedWeightObjective_zero_left
    (σ H : CMatrix a) {α c : ℝ} (hα_pos : 0 < α) :
    frankLiebFixedWeightObjective (0 : CMatrix a) σ H α c = 0 := by
  unfold frankLiebFixedWeightObjective
  simp [Real.zero_rpow (ne_of_gt hα_pos)]

/-- The fixed-weight Frank--Lieb objective is invariant under positive real
rescaling of the weight at the low-alpha source exponent
`c = (1 - alpha) / alpha`.

This is the homogeneity needed to move between normalized reverse-Holder
side-states and unrestricted positive Frank--Lieb weights. -/
theorem frankLiebFixedWeightObjective_real_smul_weight_strictLowAlpha
    {ρ σ H : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hH : H.PosDef) {lambda α : ℝ}
    (hlambda_pos : 0 < lambda)
    (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    frankLiebFixedWeightObjective ρ σ (lambda • H : CMatrix a) α ((1 - α) / α) =
      frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) := by
  let c : ℝ := (1 - α) / α
  let Klam : CMatrix a := CFC.rpow (lambda • H : CMatrix a) (-(1 / 2 : ℝ))
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let x : ℝ := ((ρ * H).trace).re
  let y : ℝ := ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re
  have hlambda_nonneg : 0 ≤ lambda := le_of_lt hlambda_pos
  have hx_nonneg : 0 ≤ x := by
    simpa [x] using cMatrix_trace_mul_posSemidef_re_nonneg hρ hH.posSemidef
  have hy_nonneg : 0 ≤ y := by
    simpa [y, K, c] using frankLieb_sigmaTerm_nonneg
      (a := a) (H := H) (σ := σ) hH hσ c
  have hleft_trace :
      (((ρ * (lambda • H : CMatrix a)).trace).re) = lambda * x := by
    calc
      ((ρ * (lambda • H : CMatrix a)).trace).re =
          (((lambda : ℂ) • (ρ * H : CMatrix a)).trace).re := by
            simp
      _ = lambda * x := by
            simp [x, Matrix.trace_smul, Complex.mul_re]
  have hsigma :
      ((CFC.rpow (Klam * CFC.rpow σ c * Klam) (1 / c)).trace).re =
        lambda ^ (-(1 / c)) * y := by
    simpa [Klam, K, c, y] using
      frankLieb_sigmaTerm_real_smul_weight
        (a := a) (H := H) (σ := σ) hH hσ hlambda_pos
        (sandwichedRenyiQ_frankLiebExponent_pos hα_half hα_lt_one)
  have hpow_x :
      (lambda * x) ^ α = lambda ^ α * x ^ α :=
    Real.mul_rpow hlambda_nonneg hx_nonneg
  have hpow_y :
      (lambda ^ (-(1 / c)) * y) ^ (1 - α) =
        (lambda ^ (-(1 / c))) ^ (1 - α) * y ^ (1 - α) :=
    Real.mul_rpow (Real.rpow_nonneg hlambda_nonneg (-(1 / c))) hy_nonneg
  have hscale :
      lambda ^ α * (lambda ^ (-(1 / c))) ^ (1 - α) = 1 := by
    have hc_pos : 0 < c := by
      simpa [c] using sandwichedRenyiQ_frankLiebExponent_pos hα_half hα_lt_one
    have hα_pos : 0 < α := by linarith
    have hexp :
        α + (-(1 / c)) * (1 - α) = 0 := by
      dsimp [c]
      have hden : 1 - α ≠ 0 := ne_of_gt (sub_pos.mpr hα_lt_one)
      field_simp [ne_of_gt hα_pos, ne_of_gt hc_pos, hden]
      ring_nf
    calc
      lambda ^ α * (lambda ^ (-(1 / c))) ^ (1 - α) =
          lambda ^ α * lambda ^ ((-(1 / c)) * (1 - α)) := by
            rw [← Real.rpow_mul hlambda_nonneg]
      _ = lambda ^ (α + (-(1 / c)) * (1 - α)) := by
            rw [← Real.rpow_add hlambda_pos]
      _ = 1 := by
            rw [hexp, Real.rpow_zero]
  unfold frankLiebFixedWeightObjective
  change
    (((ρ * (lambda • H : CMatrix a)).trace).re ^ α) *
        (((CFC.rpow (Klam * CFC.rpow σ c * Klam) (1 / c)).trace).re ^
          (1 - α)) =
      x ^ α * y ^ (1 - α)
  rw [hleft_trace, hsigma, hpow_x, hpow_y]
  calc
    lambda ^ α * x ^ α *
        ((lambda ^ (-(1 / c))) ^ (1 - α) * y ^ (1 - α)) =
        (lambda ^ α * (lambda ^ (-(1 / c))) ^ (1 - α)) *
          (x ^ α * y ^ (1 - α)) := by ring
    _ = x ^ α * y ^ (1 - α) := by rw [hscale, one_mul]

/-- Identity-`H` special case of the Frank--Lieb `sigma` term concavity.

With `H = I`, the source term reduces by the PSD power-of-power law to
`Tr(σ)`, so the claimed concavity is trace linearity of the matrix convex
combination. -/
theorem frankLieb_sigmaTerm_concave_identity
    {σ₁ σ₂ : CMatrix a} (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    {c t : ℝ} (hc_pos : 0 < c) (_hc_lt_one : c < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
    t * ((CFC.rpow (CFC.rpow σ₁ c) (1 / c)).trace).re +
        (1 - t) * ((CFC.rpow (CFC.rpow σ₂ c) (1 / c)).trace).re ≤
      ((CFC.rpow (CFC.rpow σt c) (1 / c)).trace).re := by
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  have hσt : σt.PosSemidef := by
    simpa [σt] using cMatrixConvexCombination_posSemidef hσ₁ hσ₂ ht0 ht1
  have hpow₁ : CFC.rpow (CFC.rpow σ₁ c) (1 / c) = σ₁ :=
    cMatrix_rpow_rpow_inv_of_pos hσ₁ hc_pos
  have hpow₂ : CFC.rpow (CFC.rpow σ₂ c) (1 / c) = σ₂ :=
    cMatrix_rpow_rpow_inv_of_pos hσ₂ hc_pos
  have hpowt : CFC.rpow (CFC.rpow σt c) (1 / c) = σt :=
    cMatrix_rpow_rpow_inv_of_pos hσt hc_pos
  have htrace :
      σt.trace.re = t * σ₁.trace.re + (1 - t) * σ₂.trace.re := by
    simpa [σt] using cMatrixConvexCombination_trace_re t σ₁ σ₂
  dsimp only
  rw [hpow₁, hpow₂, hpowt, htrace]

/-- Positive-scalar weighted special case of the Frank--Lieb `sigma` term
concavity.

This is the source `H = λ⁻¹ I` sanity case: the weighted source term
`Tr[(λ σ^c)^(1/c)]` reduces to the fixed scalar `λ^(1/c)` times `Tr σ`,
so the binary concavity claim is again trace linearity.  It is still a
non-circular Frank--Lieb-route check because it verifies the weighted exponent
placement used by the general `H` theorem without assuming joint concavity. -/
theorem frankLieb_sigmaTerm_concave_real_smul
    {σ₁ σ₂ : CMatrix a} (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    {lambda c t : ℝ} (hlambda : 0 ≤ lambda)
    (hc_pos : 0 < c) (_hc_lt_one : c < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
    t * ((CFC.rpow (lambda • CFC.rpow σ₁ c : CMatrix a) (1 / c)).trace).re +
        (1 - t) *
          ((CFC.rpow (lambda • CFC.rpow σ₂ c : CMatrix a) (1 / c)).trace).re ≤
      ((CFC.rpow (lambda • CFC.rpow σt c : CMatrix a) (1 / c)).trace).re := by
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  let w : ℝ := lambda ^ (1 / c)
  have hσt : σt.PosSemidef := by
    simpa [σt] using cMatrixConvexCombination_posSemidef hσ₁ hσ₂ ht0 ht1
  have hpow₁ :
      CFC.rpow (lambda • CFC.rpow σ₁ c : CMatrix a) (1 / c) =
        w • σ₁ := by
    rw [cMatrix_rpow_real_smul_posSemidef_schatten
      (cMatrix_rpow_posSemidef (A := σ₁) (s := c) hσ₁) hlambda]
    rw [cMatrix_rpow_rpow_inv_of_pos hσ₁ hc_pos]
  have hpow₂ :
      CFC.rpow (lambda • CFC.rpow σ₂ c : CMatrix a) (1 / c) =
        w • σ₂ := by
    rw [cMatrix_rpow_real_smul_posSemidef_schatten
      (cMatrix_rpow_posSemidef (A := σ₂) (s := c) hσ₂) hlambda]
    rw [cMatrix_rpow_rpow_inv_of_pos hσ₂ hc_pos]
  have hpowt :
      CFC.rpow (lambda • CFC.rpow σt c : CMatrix a) (1 / c) =
        w • σt := by
    rw [cMatrix_rpow_real_smul_posSemidef_schatten
      (cMatrix_rpow_posSemidef (A := σt) (s := c) hσt) hlambda]
    rw [cMatrix_rpow_rpow_inv_of_pos hσt hc_pos]
  have htrace :
      σt.trace.re = t * σ₁.trace.re + (1 - t) * σ₂.trace.re := by
    simpa [σt] using cMatrixConvexCombination_trace_re t σ₁ σ₂
  have htrace₁ :
      ((w • σ₁ : CMatrix a).trace).re = w * σ₁.trace.re := by
    simp [Matrix.trace_smul, Complex.mul_re]
  have htrace₂ :
      ((w • σ₂ : CMatrix a).trace).re = w * σ₂.trace.re := by
    simp [Matrix.trace_smul, Complex.mul_re]
  have htracet :
      ((w • σt : CMatrix a).trace).re = w * σt.trace.re := by
    simp [Matrix.trace_smul, Complex.mul_re]
  dsimp only
  rw [hpow₁, hpow₂, hpowt, htrace₁, htrace₂, htracet, htrace]
  ring_nf
  exact le_rfl

/-- Diagonal fixed-weight special case of the Frank--Lieb `sigma` term
concavity.

This is the common-eigenbasis sanity case for the source term
`Tr[(H^{-1/2} σ^c H^{-1/2})^(1/c)]`: a fixed nonnegative diagonal weight
`w` plays the role of the diagonal entries of `H^{-1}`, and the theorem
reduces the matrix statement to the scalar identity
`(wᵢ dᵢ^c)^(1/c) = wᵢ^(1/c) dᵢ`.  It is still not the full Frank--Lieb
theorem, but it verifies the nonconstant weighted exponent placement used by
that theorem. -/
theorem frankLieb_sigmaTerm_concave_diagonalWeight
    (w d₁ d₂ : a → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hd₁ : ∀ i, 0 ≤ d₁ i) (hd₂ : ∀ i, 0 ≤ d₂ i)
    {c t : ℝ} (hc_pos : 0 < c) (_hc_lt_one : c < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * ((CFC.rpow
          (Matrix.diagonal (fun i => ((w i * d₁ i ^ c : ℝ) : ℂ)) : CMatrix a)
          (1 / c)).trace).re +
        (1 - t) * ((CFC.rpow
          (Matrix.diagonal (fun i => ((w i * d₂ i ^ c : ℝ) : ℂ)) : CMatrix a)
          (1 / c)).trace).re ≤
      ((CFC.rpow
        (Matrix.diagonal
          (fun i => ((w i * (t * d₁ i + (1 - t) * d₂ i) ^ c : ℝ) : ℂ)) :
          CMatrix a)
        (1 / c)).trace).re := by
  let dt : a → ℝ := fun i => t * d₁ i + (1 - t) * d₂ i
  have hdt : ∀ i, 0 ≤ dt i := by
    intro i
    exact add_nonneg (mul_nonneg ht0 (hd₁ i))
      (mul_nonneg (sub_nonneg.mpr ht1) (hd₂ i))
  have hD₁ : ∀ i, 0 ≤ w i * d₁ i ^ c := fun i =>
    mul_nonneg (hw i) (Real.rpow_nonneg (hd₁ i) c)
  have hD₂ : ∀ i, 0 ≤ w i * d₂ i ^ c := fun i =>
    mul_nonneg (hw i) (Real.rpow_nonneg (hd₂ i) c)
  have hDt : ∀ i, 0 ≤ w i * dt i ^ c := fun i =>
    mul_nonneg (hw i) (Real.rpow_nonneg (hdt i) c)
  have hpow₁ :
      CFC.rpow
          (Matrix.diagonal (fun i => ((w i * d₁ i ^ c : ℝ) : ℂ)) : CMatrix a)
          (1 / c) =
        Matrix.diagonal
          (fun i => (((w i) ^ (1 / c) * d₁ i : ℝ) : ℂ)) := by
    rw [cMatrix_rpow_diagonal_ofReal (fun i => w i * d₁ i ^ c) hD₁ (1 / c)]
    ext i j
    by_cases hij : i = j
    · subst j
      have hmul :
          (w i * d₁ i ^ c) ^ (1 / c) = w i ^ (1 / c) * d₁ i := by
        rw [Real.mul_rpow (hw i) (Real.rpow_nonneg (hd₁ i) c)]
        rw [← Real.rpow_mul (hd₁ i)]
        have hc_mul : c * (1 / c) = (1 : ℝ) := by
          field_simp [hc_pos.ne']
        rw [hc_mul, Real.rpow_one]
      simp only [Matrix.diagonal_apply, ↓reduceIte]
      exact congrArg (fun x : ℝ => (x : ℂ)) (by simpa [one_div] using hmul)
    · simp [Matrix.diagonal, hij]
  have hpow₂ :
      CFC.rpow
          (Matrix.diagonal (fun i => ((w i * d₂ i ^ c : ℝ) : ℂ)) : CMatrix a)
          (1 / c) =
        Matrix.diagonal
          (fun i => (((w i) ^ (1 / c) * d₂ i : ℝ) : ℂ)) := by
    rw [cMatrix_rpow_diagonal_ofReal (fun i => w i * d₂ i ^ c) hD₂ (1 / c)]
    ext i j
    by_cases hij : i = j
    · subst j
      have hmul :
          (w i * d₂ i ^ c) ^ (1 / c) = w i ^ (1 / c) * d₂ i := by
        rw [Real.mul_rpow (hw i) (Real.rpow_nonneg (hd₂ i) c)]
        rw [← Real.rpow_mul (hd₂ i)]
        have hc_mul : c * (1 / c) = (1 : ℝ) := by
          field_simp [hc_pos.ne']
        rw [hc_mul, Real.rpow_one]
      simp only [Matrix.diagonal_apply, ↓reduceIte]
      exact congrArg (fun x : ℝ => (x : ℂ)) (by simpa [one_div] using hmul)
    · simp [Matrix.diagonal, hij]
  have hpowt :
      CFC.rpow
          (Matrix.diagonal (fun i => ((w i * dt i ^ c : ℝ) : ℂ)) : CMatrix a)
          (1 / c) =
        Matrix.diagonal
          (fun i => (((w i) ^ (1 / c) * dt i : ℝ) : ℂ)) := by
    rw [cMatrix_rpow_diagonal_ofReal (fun i => w i * dt i ^ c) hDt (1 / c)]
    ext i j
    by_cases hij : i = j
    · subst j
      have hmul :
          (w i * dt i ^ c) ^ (1 / c) = w i ^ (1 / c) * dt i := by
        rw [Real.mul_rpow (hw i) (Real.rpow_nonneg (hdt i) c)]
        rw [← Real.rpow_mul (hdt i)]
        have hc_mul : c * (1 / c) = (1 : ℝ) := by
          field_simp [hc_pos.ne']
        rw [hc_mul, Real.rpow_one]
      simp only [Matrix.diagonal_apply, ↓reduceIte]
      exact congrArg (fun x : ℝ => (x : ℂ)) (by simpa [one_div] using hmul)
    · simp [Matrix.diagonal, hij]
  rw [hpow₁, hpow₂]
  simp only [Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re]
  have hpowt' :
      CFC.rpow
          (Matrix.diagonal
            (fun i => ((w i * (t * d₁ i + (1 - t) * d₂ i) ^ c : ℝ) : ℂ)) :
              CMatrix a)
          (1 / c) =
        Matrix.diagonal
          (fun i => (((w i) ^ (1 / c) * (t * d₁ i + (1 - t) * d₂ i) : ℝ) : ℂ)) := by
    simpa [dt] using hpowt
  rw [hpowt']
  simp only [Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype a] in
omit [Fintype a] in
/-- Convex combinations of real diagonal complex matrices stay diagonal, with
the pointwise real convex-combination entries. -/
theorem cMatrixConvexCombination_diagonal_ofReal
    (t : ℝ) (s₁ s₂ : a → ℝ) :
    cMatrixConvexCombination t
        (Matrix.diagonal fun i => (s₁ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (s₂ i : ℂ) : CMatrix a) =
      Matrix.diagonal
        (fun i => ((t * s₁ i + (1 - t) * s₂ i : ℝ) : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [cMatrixConvexCombination, Matrix.diagonal]
  · simp [cMatrixConvexCombination, Matrix.diagonal, hij]

omit [Fintype a] in
/-- A real diagonal complex matrix is PSD when its diagonal entries are
nonnegative. -/
theorem cMatrix_diagonal_ofReal_posSemidef
    (d : a → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a).PosSemidef :=
  Matrix.PosSemidef.diagonal (d := fun i => (d i : ℂ)) (by
    intro i
    change (0 : ℂ) ≤ (d i : ℂ)
    exact_mod_cast hd i)

/-- Scalar power simplification for one diagonal entry of the Frank--Lieb
`sigma` term. -/
theorem frankLieb_sigmaTerm_diagonal_entry
    {h s c : ℝ} (hh : 0 < h) (hs : 0 ≤ s) (hc_pos : 0 < c) :
    (h ^ (-(1 / 2 : ℝ)) * s ^ c * h ^ (-(1 / 2 : ℝ))) ^ (1 / c) =
      h ^ (-(1 / c)) * s := by
  have hhalf :
      h ^ (-(1 / 2 : ℝ)) * h ^ (-(1 / 2 : ℝ)) =
        h ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hh]
    ring_nf
  have hbase_nonneg : 0 ≤ h ^ (-1 : ℝ) :=
    Real.rpow_nonneg hh.le (-1 : ℝ)
  have hspow_nonneg : 0 ≤ s ^ c :=
    Real.rpow_nonneg hs c
  have hhpow :
      (h ^ (-1 : ℝ)) ^ (1 / c) = h ^ (-(1 / c)) := by
    rw [← Real.rpow_mul hh.le]
    ring_nf
  have hspow : (s ^ c) ^ (1 / c) = s := by
    simpa [one_div] using Real.rpow_rpow_inv hs hc_pos.ne'
  calc
    (h ^ (-(1 / 2 : ℝ)) * s ^ c * h ^ (-(1 / 2 : ℝ))) ^ (1 / c)
        = ((h ^ (-(1 / 2 : ℝ)) * h ^ (-(1 / 2 : ℝ))) * s ^ c) ^ (1 / c) := by
            ring_nf
    _ = (h ^ (-1 : ℝ) * s ^ c) ^ (1 / c) := by
            rw [hhalf]
    _ = (h ^ (-1 : ℝ)) ^ (1 / c) * (s ^ c) ^ (1 / c) := by
            rw [Real.mul_rpow hbase_nonneg hspow_nonneg]
    _ = h ^ (-(1 / c)) * s := by
            rw [hhpow, hspow]

/-- Evaluation of the Frank--Lieb `sigma` term on a common real diagonal
basis.  The weighted term collapses to a fixed weighted trace. -/
theorem frankLieb_sigmaTerm_diagonal_eval
    (h s : a → ℝ) (hh : ∀ i, 0 < h i) (hs : ∀ i, 0 ≤ s i)
    {c : ℝ} (hc_pos : 0 < c) :
    let H : CMatrix a := Matrix.diagonal fun i => (h i : ℂ)
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    let σ : CMatrix a := Matrix.diagonal fun i => (s i : ℂ)
    ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re =
      ∑ i, h i ^ (-(1 / c)) * s i := by
  let H : CMatrix a := Matrix.diagonal fun i => (h i : ℂ)
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let σ : CMatrix a := Matrix.diagonal fun i => (s i : ℂ)
  have hh_nonneg : ∀ i, 0 ≤ h i := fun i => (hh i).le
  have hK :
      K =
        Matrix.diagonal (fun i => ((h i ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
    simpa [K, H] using
      cMatrix_rpow_diagonal_ofReal (a := a) h hh_nonneg (-(1 / 2 : ℝ))
  have hσpow :
      CFC.rpow σ c =
        Matrix.diagonal (fun i => ((s i ^ c : ℝ) : ℂ)) := by
    simpa [σ] using cMatrix_rpow_diagonal_ofReal (a := a) s hs c
  have hinner_nonneg :
      ∀ i, 0 ≤ h i ^ (-(1 / 2 : ℝ)) * s i ^ c * h i ^ (-(1 / 2 : ℝ)) := by
    intro i
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (hh i).le (-(1 / 2 : ℝ)))
        (Real.rpow_nonneg (hs i) c))
      (Real.rpow_nonneg (hh i).le (-(1 / 2 : ℝ)))
  have hinner :
      K * CFC.rpow σ c * K =
        Matrix.diagonal
          (fun i =>
            ((h i ^ (-(1 / 2 : ℝ)) * s i ^ c *
                h i ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
    rw [hK, hσpow, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij]
  dsimp only
  rw [hinner]
  rw [cMatrix_rpow_diagonal_ofReal (a := a)
    (fun i => h i ^ (-(1 / 2 : ℝ)) * s i ^ c *
      h i ^ (-(1 / 2 : ℝ))) hinner_nonneg (1 / c)]
  rw [Matrix.trace_diagonal]
  rw [Complex.re_sum]
  simp only [Complex.ofReal_re]
  apply Finset.sum_congr rfl
  intro i _
  exact frankLieb_sigmaTerm_diagonal_entry (hh i) (hs i) hc_pos

/-- Evaluation of the full fixed-weight Frank--Lieb objective on a common
real diagonal basis.  This is the commuting/classical form of the
fixed-weight variational family:
`(∑ᵢ rhoᵢ hᵢ)^α * (∑ᵢ hᵢ^(-1/c) sigmaᵢ)^(1-α)`. -/
theorem frankLiebFixedWeightObjective_diagonal_eval
    (rho sigma h : a → ℝ) (_hrho : ∀ i, 0 ≤ rho i)
    (hsigma : ∀ i, 0 ≤ sigma i) (hh : ∀ i, 0 < h i)
    (α : ℝ) {c : ℝ} (hc_pos : 0 < c) :
    let ρD : CMatrix a := Matrix.diagonal fun i => (rho i : ℂ)
    let σD : CMatrix a := Matrix.diagonal fun i => (sigma i : ℂ)
    let H : CMatrix a := Matrix.diagonal fun i => (h i : ℂ)
    frankLiebFixedWeightObjective ρD σD H α c =
      (∑ i, rho i * h i) ^ α *
        (∑ i, h i ^ (-(1 / c)) * sigma i) ^ (1 - α) := by
  let ρD : CMatrix a := Matrix.diagonal fun i => (rho i : ℂ)
  let σD : CMatrix a := Matrix.diagonal fun i => (sigma i : ℂ)
  let H : CMatrix a := Matrix.diagonal fun i => (h i : ℂ)
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  have htrace :
      ((ρD * H).trace).re = ∑ i, rho i * h i := by
    rw [Matrix.diagonal_mul_diagonal]
    rw [Matrix.trace_diagonal, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp
  have hsigmaTerm :
      ((CFC.rpow (K * CFC.rpow σD c * K) (1 / c)).trace).re =
        ∑ i, h i ^ (-(1 / c)) * sigma i := by
    simpa [H, K, σD] using
      frankLieb_sigmaTerm_diagonal_eval (a := a) h sigma hh hsigma hc_pos
  unfold frankLiebFixedWeightObjective
  change
    ((ρD * H).trace).re ^ α *
        ((CFC.rpow (K * CFC.rpow σD c * K) (1 / c)).trace).re ^ (1 - α) =
      (∑ i, rho i * h i) ^ α *
        (∑ i, h i ^ (-(1 / c)) * sigma i) ^ (1 - α)
  rw [htrace, hsigmaTerm]

/-- Common-diagonal-basis special case of the Frank--Lieb `sigma` term
concavity.

When `H`, `σ₁`, and `σ₂` are diagonal in the same basis, the source term is
the linear functional `σ ↦ ∑ i hᵢ^(-1/c) σᵢ`.  This is a genuine
non-circular special case of the general theorem: it proves the full weighted
`H` expression for a shared eigenbasis, without assuming Frank--Lieb
concavity. -/
theorem frankLieb_sigmaTerm_concave_diagonal
    (h s₁ s₂ : a → ℝ) (hh : ∀ i, 0 < h i)
    (hs₁ : ∀ i, 0 ≤ s₁ i) (hs₂ : ∀ i, 0 ≤ s₂ i)
    {c t : ℝ} (hc_pos : 0 < c) (_hc_lt_one : c < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let H : CMatrix a := Matrix.diagonal fun i => (h i : ℂ)
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    let σ₁ : CMatrix a := Matrix.diagonal fun i => (s₁ i : ℂ)
    let σ₂ : CMatrix a := Matrix.diagonal fun i => (s₂ i : ℂ)
    let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
    t * ((CFC.rpow (K * CFC.rpow σ₁ c * K) (1 / c)).trace).re +
        (1 - t) * ((CFC.rpow (K * CFC.rpow σ₂ c * K) (1 / c)).trace).re ≤
      ((CFC.rpow (K * CFC.rpow σt c * K) (1 / c)).trace).re := by
  let H : CMatrix a := Matrix.diagonal fun i => (h i : ℂ)
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let σ₁ : CMatrix a := Matrix.diagonal fun i => (s₁ i : ℂ)
  let σ₂ : CMatrix a := Matrix.diagonal fun i => (s₂ i : ℂ)
  let st : a → ℝ := fun i => t * s₁ i + (1 - t) * s₂ i
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  have hst : ∀ i, 0 ≤ st i := by
    intro i
    exact add_nonneg (mul_nonneg ht0 (hs₁ i))
      (mul_nonneg (sub_nonneg.mpr ht1) (hs₂ i))
  have hσt_diag :
      σt = Matrix.diagonal fun i => (st i : ℂ) := by
    simpa [σt, σ₁, σ₂, st] using
      cMatrixConvexCombination_diagonal_ofReal (a := a) t s₁ s₂
  have heval₁ :
      ((CFC.rpow (K * CFC.rpow σ₁ c * K) (1 / c)).trace).re =
        ∑ i, h i ^ (-(1 / c)) * s₁ i := by
    simpa [H, K, σ₁] using
      frankLieb_sigmaTerm_diagonal_eval (a := a) h s₁ hh hs₁ hc_pos
  have heval₂ :
      ((CFC.rpow (K * CFC.rpow σ₂ c * K) (1 / c)).trace).re =
        ∑ i, h i ^ (-(1 / c)) * s₂ i := by
    simpa [H, K, σ₂] using
      frankLieb_sigmaTerm_diagonal_eval (a := a) h s₂ hh hs₂ hc_pos
  have hevalt :
      ((CFC.rpow (K * CFC.rpow σt c * K) (1 / c)).trace).re =
        ∑ i, h i ^ (-(1 / c)) * st i := by
    rw [hσt_diag]
    simpa [H, K, st] using
      frankLieb_sigmaTerm_diagonal_eval (a := a) h st hh hst hc_pos
  have hsum :
      t * (∑ i, h i ^ (-(1 / c)) * s₁ i) +
          (1 - t) * (∑ i, h i ^ (-(1 / c)) * s₂ i) =
        ∑ i, h i ^ (-(1 / c)) * st i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp [st]
    ring
  dsimp only
  rw [heval₁, heval₂, hevalt]
  exact le_of_eq hsum

/-- Entrywise simplification of the common-diagonal sandwiched `Q` power
term.  This is the matrix-level analogue of the scalar identity behind the
classical sandwiched Renyi power sum. -/
theorem sandwichedRenyiQ_diagonal_entry
    {p q α : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hα : 0 < α) :
    (q ^ ((1 - α) / (2 * α)) * p * q ^ ((1 - α) / (2 * α))) ^ α =
      p ^ α * q ^ (1 - α) := by
  let s : ℝ := (1 - α) / (2 * α)
  have hq_nonneg : 0 ≤ q := le_of_lt hq
  have hqs_nonneg : 0 ≤ q ^ s := Real.rpow_nonneg hq_nonneg s
  have hsα : (s + s) * α = 1 - α := by
    dsimp [s]
    field_simp [ne_of_gt hα]
    ring
  calc
    (q ^ ((1 - α) / (2 * α)) * p * q ^ ((1 - α) / (2 * α))) ^ α =
        (p * (q ^ s * q ^ s)) ^ α := by
          dsimp [s]
          ring_nf
    _ = p ^ α * (q ^ s * q ^ s) ^ α := by
          rw [Real.mul_rpow hp (mul_nonneg hqs_nonneg hqs_nonneg)]
    _ = p ^ α * (q ^ (s + s)) ^ α := by
          rw [Real.rpow_add hq s s]
    _ = p ^ α * q ^ ((s + s) * α) := by
          rw [← Real.rpow_mul hq_nonneg (s + s) α]
    _ = p ^ α * q ^ (1 - α) := by
          rw [hsα]

/-- Matrix-level sandwiched `Q` on a common positive real diagonal reference
is the classical power sum `∑ᵢ ρᵢ^α σᵢ^(1-α)`.

The reference diagonal is assumed entrywise positive so the low-alpha
sandwich exponent never has to interpret a negative power at zero. -/
theorem sandwichedRenyiQ_diagonal_eval
    (ρ σ : a → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_pos : 0 < α) :
    sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ hρ)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α =
      ∑ i, ρ i ^ α * σ i ^ (1 - α) := by
  let s : ℝ := (1 - α) / (2 * α)
  let ρD : CMatrix a := Matrix.diagonal fun i => (ρ i : ℂ)
  let σD : CMatrix a := Matrix.diagonal fun i => (σ i : ℂ)
  have hσ_nonneg : ∀ i, 0 ≤ σ i := fun i => (hσ i).le
  have hC :
      CFC.rpow σD s =
        Matrix.diagonal (fun i => ((σ i ^ s : ℝ) : ℂ)) := by
    simpa [σD] using cMatrix_rpow_diagonal_ofReal (a := a) σ hσ_nonneg s
  have hinner_nonneg :
      ∀ i, 0 ≤ σ i ^ s * ρ i * σ i ^ s := by
    intro i
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (hσ_nonneg i) s) (hρ i))
      (Real.rpow_nonneg (hσ_nonneg i) s)
  have hinner :
      CFC.rpow σD s * ρD * CFC.rpow σD s =
        Matrix.diagonal
          (fun i => ((σ i ^ s * ρ i * σ i ^ s : ℝ) : ℂ)) := by
    rw [hC, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij]
  have hM :
      CFC.rpow (CFC.rpow σD s * ρD * CFC.rpow σD s) α =
        Matrix.diagonal
          (fun i => (((σ i ^ s * ρ i * σ i ^ s) ^ α : ℝ) : ℂ)) := by
    rw [hinner]
    exact cMatrix_rpow_diagonal_ofReal
      (a := a) (fun i => σ i ^ s * ρ i * σ i ^ s) hinner_nonneg α
  unfold sandwichedRenyiQ
  change
    (CFC.rpow (CFC.rpow σD s * ρD * CFC.rpow σD s) α).trace.re =
      ∑ i, ρ i ^ α * σ i ^ (1 - α)
  rw [hM, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Complex.ofReal_re]
  apply Finset.sum_congr rfl
  intro i _
  simpa [s, mul_assoc] using
    sandwichedRenyiQ_diagonal_entry (p := ρ i) (q := σ i) (α := α)
      (hρ i) (hσ i) hα_pos

/-- Classical/commuting lower-bound direction of the fixed-weight
Frank--Lieb variational formula.

For every positive diagonal weight `h`, the fixed-weight objective dominates
the diagonal sandwiched `Q` value. This is the scalar core behind the
noncommutative fixed-weight `sInf` bridge. -/
theorem sandwichedRenyiQ_diagonal_le_frankLiebFixedWeightObjective
    [Nonempty a] (ρ σ h : a → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hh : ∀ i, 0 < h i)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ hρ)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α ≤
      frankLiebFixedWeightObjective
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (h i : ℂ) : CMatrix a)
        α ((1 - α) / α) := by
  classical
  let c : ℝ := (1 - α) / α
  let p : a → ℝ := fun i => ρ i * h i
  let q : a → ℝ := fun i => σ i * h i ^ (-(1 / c))
  let w : a → ℝ := fun _ => 1
  have hc_pos : 0 < c := by
    dsimp [c]
    exact div_pos (sub_pos.mpr hα_lt_one) hα_pos
  have hp_nonneg : ∀ i, 0 ≤ p i := by
    intro i
    exact mul_nonneg (hρ i) (le_of_lt (hh i))
  have hq_pos : ∀ i, 0 < q i := by
    intro i
    exact mul_pos (hσ i) (Real.rpow_pos_of_pos (hh i) (-(1 / c)))
  have hw_nonneg : ∀ i, 0 ≤ w i := by
    intro i
    simp [w]
  have hQ_pos : 0 < ∑ i, q i * w i := by
    have hterm : ∀ i ∈ (Finset.univ : Finset a), 0 < q i * w i := by
      intro i _
      simpa [w] using hq_pos i
    exact Finset.sum_pos hterm Finset.univ_nonempty
  have hweighted :=
    real_classical_renyi_weighted_power_term_ge
      (ι := a) (p := p) (q := q) (t := w)
      (le_of_lt hα_pos) (le_of_lt hα_lt_one)
      hp_nonneg hq_pos hw_nonneg hQ_pos
  have hleft :
      ∑ i, w i * p i ^ α * q i ^ (1 - α) =
        ∑ i, ρ i ^ α * σ i ^ (1 - α) := by
    apply Finset.sum_congr rfl
    intro i _
    have hh_nonneg : 0 ≤ h i := le_of_lt (hh i)
    have hsigma_nonneg : 0 ≤ σ i := le_of_lt (hσ i)
    have hpowa : (ρ i * h i) ^ α = ρ i ^ α * h i ^ α :=
      Real.mul_rpow (hρ i) hh_nonneg
    have hpowq :
        (σ i * h i ^ (-(1 / c))) ^ (1 - α) =
          σ i ^ (1 - α) * (h i ^ (-(1 / c))) ^ (1 - α) :=
      Real.mul_rpow hsigma_nonneg
        (Real.rpow_nonneg hh_nonneg (-(1 / c)))
    have hscale :
        h i ^ α * (h i ^ (-(1 / c))) ^ (1 - α) = 1 := by
      have hexp : α + (-(1 / c)) * (1 - α) = 0 := by
        dsimp [c]
        have hden : 1 - α ≠ 0 := ne_of_gt (sub_pos.mpr hα_lt_one)
        field_simp [ne_of_gt hα_pos, ne_of_gt hc_pos, hden]
        ring_nf
      calc
        h i ^ α * (h i ^ (-(1 / c))) ^ (1 - α) =
            h i ^ α * h i ^ ((-(1 / c)) * (1 - α)) := by
              rw [← Real.rpow_mul (le_of_lt (hh i))]
        _ = h i ^ (α + (-(1 / c)) * (1 - α)) := by
              rw [← Real.rpow_add (hh i)]
        _ = 1 := by
              rw [hexp, Real.rpow_zero]
    calc
      w i * p i ^ α * q i ^ (1 - α)
          = (ρ i * h i) ^ α *
              (σ i * h i ^ (-(1 / c))) ^ (1 - α) := by
              simp [p, q, w]
      _ = (ρ i ^ α * h i ^ α) *
            (σ i ^ (1 - α) * (h i ^ (-(1 / c))) ^ (1 - α)) := by
              rw [hpowa, hpowq]
      _ = ρ i ^ α * σ i ^ (1 - α) *
            (h i ^ α * (h i ^ (-(1 / c))) ^ (1 - α)) := by
              ring
      _ = ρ i ^ α * σ i ^ (1 - α) := by
              rw [hscale, mul_one]
  have hright :
      (∑ i, p i * w i) ^ α * (∑ i, q i * w i) ^ (1 - α) =
        (∑ i, ρ i * h i) ^ α *
          (∑ i, h i ^ (-(1 / c)) * σ i) ^ (1 - α) := by
    simp [p, q, w, mul_comm, mul_left_comm]
  have hdiagQ :
      sandwichedRenyiQ
          (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
          (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
          (cMatrix_diagonal_ofReal_posSemidef ρ hρ)
          (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
          α =
        ∑ i, ρ i ^ α * σ i ^ (1 - α) :=
    sandwichedRenyiQ_diagonal_eval ρ σ hρ hσ hα_pos
  have hobj :
      frankLiebFixedWeightObjective
          (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
          (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
          (Matrix.diagonal fun i => (h i : ℂ) : CMatrix a)
          α c =
        (∑ i, ρ i * h i) ^ α *
          (∑ i, h i ^ (-(1 / c)) * σ i) ^ (1 - α) :=
    frankLiebFixedWeightObjective_diagonal_eval ρ σ h hρ
      (fun i => (hσ i).le) hh α hc_pos
  calc
    sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ hρ)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α =
        ∑ i, ρ i ^ α * σ i ^ (1 - α) := hdiagQ
    _ = ∑ i, w i * p i ^ α * q i ^ (1 - α) := hleft.symm
    _ ≤ (∑ i, p i * w i) ^ α *
        (∑ i, q i * w i) ^ (1 - α) := hweighted
    _ = (∑ i, ρ i * h i) ^ α *
          (∑ i, h i ^ (-(1 / c)) * σ i) ^ (1 - α) := hright
    _ = frankLiebFixedWeightObjective
          (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
          (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
          (Matrix.diagonal fun i => (h i : ℂ) : CMatrix a)
          α ((1 - α) / α) := by
            simpa [c] using hobj.symm

/-- Positive diagonal optimizer for the fixed-weight Frank--Lieb objective.

In the common diagonal full-rank case, the weight
`hᵢ = ρᵢ^(α-1) σᵢ^(1-α)` attains the scalar sandwiched `Q` value. Together
with `sandwichedRenyiQ_diagonal_le_frankLiebFixedWeightObjective`, this gives
the classical fixed-weight variational equality before the noncommutative
Frank--Lieb `sInf` bridge. -/
theorem frankLiebFixedWeightObjective_diagonal_optimizer_eq_sandwichedRenyiQ
    [Nonempty a] (ρ σ : a → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    let h : a → ℝ := fun i => ρ i ^ (α - 1) * σ i ^ (1 - α)
    frankLiebFixedWeightObjective
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (h i : ℂ) : CMatrix a)
        α ((1 - α) / α) =
      sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α := by
  classical
  let c : ℝ := (1 - α) / α
  let h : a → ℝ := fun i => ρ i ^ (α - 1) * σ i ^ (1 - α)
  let S : ℝ := ∑ i, ρ i ^ α * σ i ^ (1 - α)
  have hc_pos : 0 < c := by
    dsimp [c]
    exact div_pos (sub_pos.mpr hα_lt_one) hα_pos
  have hh : ∀ i, 0 < h i := by
    intro i
    exact mul_pos (Real.rpow_pos_of_pos (hρ i) (α - 1))
      (Real.rpow_pos_of_pos (hσ i) (1 - α))
  have hS_pos : 0 < S := by
    have hterm : ∀ i ∈ (Finset.univ : Finset a), 0 < ρ i ^ α * σ i ^ (1 - α) := by
      intro i _
      exact mul_pos (Real.rpow_pos_of_pos (hρ i) α)
        (Real.rpow_pos_of_pos (hσ i) (1 - α))
    exact Finset.sum_pos hterm Finset.univ_nonempty
  have hsumρ :
      ∑ i, ρ i * h i = S := by
    apply Finset.sum_congr rfl
    intro i _
    have hρpow : ρ i * ρ i ^ (α - 1) = ρ i ^ α := by
      calc
        ρ i * ρ i ^ (α - 1) = ρ i ^ (1 : ℝ) * ρ i ^ (α - 1) := by
          rw [Real.rpow_one]
        _ = ρ i ^ ((1 : ℝ) + (α - 1)) := by
          rw [← Real.rpow_add (hρ i)]
        _ = ρ i ^ α := by
          ring_nf
    calc
      ρ i * h i = (ρ i * ρ i ^ (α - 1)) * σ i ^ (1 - α) := by
        simp [h, mul_assoc]
      _ = ρ i ^ α * σ i ^ (1 - α) := by
        rw [hρpow]
  have hsumσ :
      ∑ i, h i ^ (-(1 / c)) * σ i = S := by
    apply Finset.sum_congr rfl
    intro i _
    have hbase :
        h i ^ (-(1 / c)) =
          ρ i ^ α * σ i ^ (-α) := by
      have hρ_nonneg : 0 ≤ ρ i ^ (α - 1) := le_of_lt
        (Real.rpow_pos_of_pos (hρ i) (α - 1))
      have hσ_nonneg : 0 ≤ σ i ^ (1 - α) := le_of_lt
        (Real.rpow_pos_of_pos (hσ i) (1 - α))
      have hρexp : (α - 1) * (-(1 / c)) = α := by
        dsimp [c]
        have hden : 1 - α ≠ 0 := ne_of_gt (sub_pos.mpr hα_lt_one)
        field_simp [ne_of_gt hα_pos, ne_of_gt hc_pos, hden]
        ring_nf
      have hσexp : (1 - α) * (-(1 / c)) = -α := by
        dsimp [c]
        have hden : 1 - α ≠ 0 := ne_of_gt (sub_pos.mpr hα_lt_one)
        field_simp [ne_of_gt hα_pos, ne_of_gt hc_pos, hden]
      calc
        h i ^ (-(1 / c)) =
            (ρ i ^ (α - 1) * σ i ^ (1 - α)) ^ (-(1 / c)) := by
              rfl
        _ = (ρ i ^ (α - 1)) ^ (-(1 / c)) *
            (σ i ^ (1 - α)) ^ (-(1 / c)) := by
              rw [Real.mul_rpow hρ_nonneg hσ_nonneg]
        _ = ρ i ^ ((α - 1) * (-(1 / c))) *
            σ i ^ ((1 - α) * (-(1 / c))) := by
              rw [← Real.rpow_mul (hρ i).le, ← Real.rpow_mul (hσ i).le]
        _ = ρ i ^ α * σ i ^ (-α) := by
              rw [hρexp, hσexp]
    have hσpow : σ i ^ (-α) * σ i = σ i ^ (1 - α) := by
      calc
        σ i ^ (-α) * σ i = σ i ^ (-α) * σ i ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = σ i ^ ((-α) + (1 : ℝ)) := by
          rw [← Real.rpow_add (hσ i)]
        _ = σ i ^ (1 - α) := by
          ring_nf
    calc
      h i ^ (-(1 / c)) * σ i =
          (ρ i ^ α * σ i ^ (-α)) * σ i := by
            rw [hbase]
      _ = ρ i ^ α * (σ i ^ (-α) * σ i) := by
            ring
      _ = ρ i ^ α * σ i ^ (1 - α) := by
            rw [hσpow]
  have hobj :
      frankLiebFixedWeightObjective
          (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
          (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
          (Matrix.diagonal fun i => (h i : ℂ) : CMatrix a)
          α c =
        (∑ i, ρ i * h i) ^ α *
          (∑ i, h i ^ (-(1 / c)) * σ i) ^ (1 - α) :=
    frankLiebFixedWeightObjective_diagonal_eval ρ σ h
      (fun i => (hρ i).le) (fun i => (hσ i).le) hh α hc_pos
  have hdiagQ :
      sandwichedRenyiQ
          (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
          (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
          (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
          (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
          α = S := by
    simpa [S] using
      sandwichedRenyiQ_diagonal_eval ρ σ
        (fun i => (hρ i).le) hσ hα_pos
  have hpowS : S ^ α * S ^ (1 - α) = S := by
    calc
      S ^ α * S ^ (1 - α) = S ^ (α + (1 - α)) := by
        rw [← Real.rpow_add hS_pos]
      _ = S := by
        rw [show α + (1 - α) = (1 : ℝ) by ring, Real.rpow_one]
  dsimp only
  calc
    frankLiebFixedWeightObjective
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (h i : ℂ) : CMatrix a)
        α ((1 - α) / α) =
        (∑ i, ρ i * h i) ^ α *
          (∑ i, h i ^ (-(1 / c)) * σ i) ^ (1 - α) := by
          simpa [c] using hobj
    _ = S ^ α * S ^ (1 - α) := by
          rw [hsumρ, hsumσ]
    _ = S := hpowS
    _ = sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α := hdiagQ.symm

omit [Fintype a] [DecidableEq a] in
/-- Binary scalar low-alpha concavity of the classical sandwiched Renyi power
term `p^α q^(1-α)`. -/
theorem sandwichedRenyiQ_scalarTerm_concave_lowAlpha
    {p₁ p₂ q₁ q₂ α t : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (p₁ ^ α * q₁ ^ (1 - α)) +
        (1 - t) * (p₂ ^ α * q₂ ^ (1 - α)) ≤
      (t * p₁ + (1 - t) * p₂) ^ α *
        (t * q₁ + (1 - t) * q₂) ^ (1 - α) := by
  let p : Bool → ℝ := fun b => cond b p₁ p₂
  let q : Bool → ℝ := fun b => cond b q₁ q₂
  let w : Bool → ℝ := fun b => cond b t (1 - t)
  have hp : ∀ b, 0 ≤ p b := by
    intro b
    cases b <;> simp [p, hp₁, hp₂]
  have hq : ∀ b, 0 < q b := by
    intro b
    cases b <;> simp [q, hq₁, hq₂]
  have hw : ∀ b, 0 ≤ w b := by
    intro b
    cases b
    · simpa [w] using sub_nonneg.mpr ht1
    · simpa [w] using ht0
  have hQ_pos : 0 < ∑ b, q b * w b := by
    have hterm_true : 0 < q true * w true + q false * w false := by
      have hsumw : w true + w false = 1 := by simp [w]
      have hqmin : 0 < min q₁ q₂ := lt_min hq₁ hq₂
      have hge :
          min q₁ q₂ * (w true + w false) ≤ q true * w true + q false * w false := by
        have hle_true : min q₁ q₂ * w true ≤ q true * w true :=
          mul_le_mul_of_nonneg_right (min_le_left q₁ q₂) (hw true)
        have hle_false : min q₁ q₂ * w false ≤ q false * w false :=
          mul_le_mul_of_nonneg_right (min_le_right q₁ q₂) (hw false)
        calc
          min q₁ q₂ * (w true + w false) =
              min q₁ q₂ * w true + min q₁ q₂ * w false := by ring
          _ ≤ q true * w true + q false * w false := add_le_add hle_true hle_false
      have hpos : 0 < min q₁ q₂ * (w true + w false) := by
        rw [hsumw, mul_one]
        exact hqmin
      exact lt_of_lt_of_le hpos hge
    simpa [Fintype.sum_bool, q, w, add_comm, add_left_comm, add_assoc] using hterm_true
  have hraw :=
    real_classical_renyi_weighted_power_term_ge
      (ι := Bool) (p := p) (q := q) (t := w)
      hα_nonneg hα_le_one hp hq hw hQ_pos
  simpa [p, q, w, Fintype.sum_bool, mul_comm, mul_left_comm, mul_assoc,
    add_comm, add_left_comm, add_assoc] using hraw

/-- Fixed-weight Frank--Lieb objective is concave in the positive reference
case.

This combines the linearity of `ρ ↦ Tr(ρH)`, unrestricted Frank--Lieb
concavity of the fixed `σ` term, and scalar weighted-product concavity.  It is
the non-circular source-aligned step immediately before the reverse-Holder
fixed-weight variational bridge for `sandwichedRenyiQ`. -/
theorem frankLiebFixedWeightObjective_concave_posDef
    [Nonempty a] {H ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hH : H.PosDef)
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef)
    {α c t : ℝ} (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * frankLiebFixedWeightObjective ρ₁ σ₁ H α c +
        (1 - t) * frankLiebFixedWeightObjective ρ₂ σ₂ H α c ≤
      frankLiebFixedWeightObjective
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂) H α c := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let ρt : CMatrix a := cMatrixConvexCombination t ρ₁ ρ₂
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  let x₁ : ℝ := ((ρ₁ * H).trace).re
  let x₂ : ℝ := ((ρ₂ * H).trace).re
  let xt : ℝ := ((ρt * H).trace).re
  let y₁ : ℝ := ((CFC.rpow (K * CFC.rpow σ₁ c * K) (1 / c)).trace).re
  let y₂ : ℝ := ((CFC.rpow (K * CFC.rpow σ₂ c * K) (1 / c)).trace).re
  let yt : ℝ := ((CFC.rpow (K * CFC.rpow σt c * K) (1 / c)).trace).re
  have hx₁ : 0 ≤ x₁ := by
    simpa [x₁] using cMatrix_trace_mul_posSemidef_re_nonneg hρ₁ hH.posSemidef
  have hx₂ : 0 ≤ x₂ := by
    simpa [x₂] using cMatrix_trace_mul_posSemidef_re_nonneg hρ₂ hH.posSemidef
  have hy₁ : 0 < y₁ := by
    simpa [y₁, K] using frankLieb_sigmaTerm_pos
      (a := a) (H := H) (σ := σ₁) hH hσ₁ c
  have hy₂ : 0 < y₂ := by
    simpa [y₂, K] using frankLieb_sigmaTerm_pos
      (a := a) (H := H) (σ := σ₂) hH hσ₂ c
  have hσt_pos : σt.PosDef := by
    have hconv : (t • σ₁ + (1 - t) • σ₂).PosDef :=
      Matrix.PosDef.convexCombination hσ₁ hσ₂ ht0 ht1
    simpa [σt, cMatrixConvexCombination_eq_real_smul] using hconv
  have hyt_pos : 0 < yt := by
    simpa [yt, K, σt] using frankLieb_sigmaTerm_pos
      (a := a) (H := H) (σ := σt) hH hσt_pos c
  have hxt :
      xt = t * x₁ + (1 - t) * x₂ := by
    have hmul :
        ρt * H = cMatrixConvexCombination t (ρ₁ * H) (ρ₂ * H) := by
      calc
        ρt * H = (cMatrixConvexCombination t ρ₁ ρ₂) * H := rfl
        _ = (t • ρ₁ + (1 - t) • ρ₂) * H := by
          rw [cMatrixConvexCombination_eq_real_smul]
        _ = t • (ρ₁ * H) + (1 - t) • (ρ₂ * H) := by
          simp [Matrix.add_mul]
        _ = cMatrixConvexCombination t (ρ₁ * H) (ρ₂ * H) := by
          rw [cMatrixConvexCombination_eq_real_smul]
    change ((ρt * H).trace).re = t * x₁ + (1 - t) * x₂
    rw [hmul]
    simpa [x₁, x₂] using cMatrixConvexCombination_trace_re t (ρ₁ * H) (ρ₂ * H)
  have hy_conc :
      t * y₁ + (1 - t) * y₂ ≤ yt := by
    simpa [y₁, y₂, yt, K, σt] using
      frankLieb_sigmaTerm_concave
        (a := a) (H := H) (σ₁ := σ₁) (σ₂ := σ₂)
        hH hσ₁.posSemidef hσ₂.posSemidef hc_pos hc_lt_one ht0 ht1
  have hybar_pos : 0 < t * y₁ + (1 - t) * y₂ := by
    have hymin : 0 < min y₁ y₂ := lt_min hy₁ hy₂
    have hle :
        min y₁ y₂ * (t + (1 - t)) ≤ t * y₁ + (1 - t) * y₂ := by
      have hle₁ :
          min y₁ y₂ * t ≤ t * y₁ := by
        calc
          min y₁ y₂ * t = t * min y₁ y₂ := by ring
          _ ≤ t * y₁ := mul_le_mul_of_nonneg_left (min_le_left y₁ y₂) ht0
      have hle₂ :
          min y₁ y₂ * (1 - t) ≤ (1 - t) * y₂ := by
        calc
          min y₁ y₂ * (1 - t) = (1 - t) * min y₁ y₂ := by ring
          _ ≤ (1 - t) * y₂ :=
              mul_le_mul_of_nonneg_left (min_le_right y₁ y₂) (sub_nonneg.mpr ht1)
      calc
        min y₁ y₂ * (t + (1 - t)) =
            min y₁ y₂ * t + min y₁ y₂ * (1 - t) := by ring
        _ ≤ t * y₁ + (1 - t) * y₂ := add_le_add hle₁ hle₂
    have hpos : 0 < min y₁ y₂ * (t + (1 - t)) := by
      rw [show t + (1 - t) = (1 : ℝ) by ring, mul_one]
      exact hymin
    exact lt_of_lt_of_le hpos hle
  have hscalar :
      t * (x₁ ^ α * y₁ ^ (1 - α)) +
          (1 - t) * (x₂ ^ α * y₂ ^ (1 - α)) ≤
        (t * x₁ + (1 - t) * x₂) ^ α *
          (t * y₁ + (1 - t) * y₂) ^ (1 - α) :=
    sandwichedRenyiQ_scalarTerm_concave_lowAlpha
      hx₁ hx₂ hy₁ hy₂ hα_nonneg hα_le_one ht0 ht1
  have hxbar_nonneg : 0 ≤ t * x₁ + (1 - t) * x₂ :=
    add_nonneg (mul_nonneg ht0 hx₁) (mul_nonneg (sub_nonneg.mpr ht1) hx₂)
  have hyleft_nonneg : 0 ≤ t * y₁ + (1 - t) * y₂ := le_of_lt hybar_pos
  have hpow_y :
      (t * y₁ + (1 - t) * y₂) ^ (1 - α) ≤ yt ^ (1 - α) :=
    Real.rpow_le_rpow hyleft_nonneg hy_conc (sub_nonneg.mpr hα_le_one)
  have hxpow_nonneg : 0 ≤ (t * x₁ + (1 - t) * x₂) ^ α :=
    Real.rpow_nonneg hxbar_nonneg α
  have hmono :
      (t * x₁ + (1 - t) * x₂) ^ α *
          (t * y₁ + (1 - t) * y₂) ^ (1 - α) ≤
        (t * x₁ + (1 - t) * x₂) ^ α * yt ^ (1 - α) :=
    mul_le_mul_of_nonneg_left hpow_y hxpow_nonneg
  calc
    t * frankLiebFixedWeightObjective ρ₁ σ₁ H α c +
        (1 - t) * frankLiebFixedWeightObjective ρ₂ σ₂ H α c =
        t * (x₁ ^ α * y₁ ^ (1 - α)) +
          (1 - t) * (x₂ ^ α * y₂ ^ (1 - α)) := by
          simp [frankLiebFixedWeightObjective, x₁, x₂, y₁, y₂, K]
    _ ≤ (t * x₁ + (1 - t) * x₂) ^ α *
          (t * y₁ + (1 - t) * y₂) ^ (1 - α) := hscalar
    _ ≤ (t * x₁ + (1 - t) * x₂) ^ α * yt ^ (1 - α) := hmono
    _ = xt ^ α * yt ^ (1 - α) := by
          rw [hxt]
    _ = frankLiebFixedWeightObjective ρt σt H α c := by
          simp [frankLiebFixedWeightObjective, xt, yt, K]

/-- Strict low-`alpha` specialization of the fixed-weight Frank--Lieb
objective concavity with `c = (1 - alpha) / alpha`. -/
theorem frankLiebFixedWeightObjective_concave_strictLowAlpha
    [Nonempty a] {H ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hH : H.PosDef)
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef)
    {α t : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * frankLiebFixedWeightObjective ρ₁ σ₁ H α ((1 - α) / α) +
        (1 - t) * frankLiebFixedWeightObjective ρ₂ σ₂ H α ((1 - α) / α) ≤
      frankLiebFixedWeightObjective
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂) H α ((1 - α) / α) := by
  exact frankLiebFixedWeightObjective_concave_posDef
    (a := a) (H := H) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (σ₁ := σ₁) (σ₂ := σ₂)
    hH hρ₁ hρ₂ hσ₁ hσ₂
    (by linarith) (le_of_lt hα_lt_one)
    (sandwichedRenyiQ_frankLiebExponent_pos hα_half hα_lt_one)
    (sandwichedRenyiQ_frankLiebExponent_lt_one hα_half hα_lt_one)
    ht0 ht1

/-- Fixed-weight Frank--Lieb variational values for the low-`alpha`
sandwiched `Q` functional.

The intended bridge is that `sandwichedRenyiQ` is the infimum over these
positive-definite weights.  Keeping this value set explicit lets the
Frank--Lieb concavity theorem feed the later `sInf` step without assuming
joint concavity of `Q` itself. -/
def sandwichedRenyiQFixedWeightValueSet
    (ρ σ : CMatrix a) (α : ℝ) : Set ℝ :=
  {y | ∃ H : CMatrix a, H.PosDef ∧
    y = frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α)}

/-- Trace-one positive-definite fixed-weight values.  This normalized variant
matches the normalized reverse-Holder side-state domain; the strict low-alpha
homogeneity theorem identifies it with the unrestricted fixed-weight set. -/
def sandwichedRenyiQFixedWeightStateValueSet
    (ρ σ : CMatrix a) (α : ℝ) : Set ℝ :=
  {y | ∃ H : CMatrix a, H.PosDef ∧ H.trace.re = 1 ∧
    y = frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α)}

/-- Additive Gour/Frank--Lieb Young objective values for the low-`alpha`
sandwiched `Q` functional.

This source-shaped family is equivalent, after optimizing over positive scalar
rescalings of the weight, to the multiplicative fixed-weight family above. -/
def sandwichedRenyiQAdditiveValueSet
    (ρ σ : CMatrix a) (α : ℝ) : Set ℝ :=
  {y | ∃ H : CMatrix a, H.PosDef ∧
    y = frankLiebAdditiveObjective ρ σ H α ((1 - α) / α)}

theorem sandwichedRenyiQFixedWeightValueSet_mem
    {ρ σ H : CMatrix a} (hH : H.PosDef) (α : ℝ) :
    frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) ∈
      sandwichedRenyiQFixedWeightValueSet ρ σ α :=
  ⟨H, hH, rfl⟩

theorem sandwichedRenyiQFixedWeightStateValueSet_mem
    {ρ σ H : CMatrix a} (hH : H.PosDef) (hHtr : H.trace.re = 1) (α : ℝ) :
    frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) ∈
      sandwichedRenyiQFixedWeightStateValueSet ρ σ α :=
  ⟨H, hH, hHtr, rfl⟩

theorem sandwichedRenyiQAdditiveValueSet_mem
    {ρ σ H : CMatrix a} (hH : H.PosDef) (α : ℝ) :
    frankLiebAdditiveObjective ρ σ H α ((1 - α) / α) ∈
      sandwichedRenyiQAdditiveValueSet ρ σ α :=
  ⟨H, hH, rfl⟩

/-- Fixed-weight Frank--Lieb objective values are nonnegative on PSD inputs. -/
theorem frankLiebFixedWeightObjective_nonneg
    {ρ σ H : CMatrix a}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hH : H.PosDef)
    (α c : ℝ) :
    0 ≤ frankLiebFixedWeightObjective ρ σ H α c := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  have hx : 0 ≤ ((ρ * H).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg hρ hH.posSemidef
  have hy :
      0 ≤ ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re := by
    simpa [K] using frankLieb_sigmaTerm_nonneg
      (a := a) (H := H) (σ := σ) hH hσ c
  exact mul_nonneg (Real.rpow_nonneg hx α) (Real.rpow_nonneg hy (1 - α))

/-- Additive Gour/Frank--Lieb objective values are nonnegative in the
low-`alpha` weight range. -/
theorem frankLiebAdditiveObjective_nonneg
    {ρ σ H : CMatrix a}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hH : H.PosDef)
    {α c : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    0 ≤ frankLiebAdditiveObjective ρ σ H α c := by
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  have hx : 0 ≤ ((ρ * H).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg hρ hH.posSemidef
  have hy :
      0 ≤ ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re := by
    simpa [K] using frankLieb_sigmaTerm_nonneg
      (a := a) (H := H) (σ := σ) hH hσ c
  have h1α : 0 ≤ 1 - α := sub_nonneg.mpr hα1
  unfold frankLiebAdditiveObjective
  exact add_nonneg (mul_nonneg hα0 hx) (mul_nonneg h1α hy)

/-- Zero is a lower bound for the fixed-weight value set on PSD inputs. -/
theorem sandwichedRenyiQFixedWeightValueSet_lowerBound_zero
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (α : ℝ) :
    0 ∈ lowerBounds (sandwichedRenyiQFixedWeightValueSet ρ σ α) := by
  intro y hy
  rcases hy with ⟨H, hH, rfl⟩
  exact frankLiebFixedWeightObjective_nonneg hρ hσ hH α ((1 - α) / α)

/-- Gour/Frank--Lieb lower-bound direction: for positive-definite inputs,
`Q_α(ρ, σ)` is a lower bound for every positive-definite fixed-weight
objective.

This is the noncommutative source-shaped Young lower bound after the
`LL*`/`L*L` rewrite, and replaces the earlier diagonal-only lower-bound
sanity check. -/
theorem sandwichedRenyiQFixedWeightValueSet_lowerBound_sandwichedRenyiQ_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ∈
      lowerBounds (sandwichedRenyiQFixedWeightValueSet ρ σ α) := by
  intro y hy
  rcases hy with ⟨H, hH, rfl⟩
  exact sandwichedRenyiQ_le_frankLiebFixedWeightObjective_posDef
    hρ hσ hH hα_half hα_lt_one

/-- Infimum lower-bound direction of Gour's fixed-weight variational formula:
the fixed-weight infimum is at least the sandwiched `Q` value. -/
theorem sandwichedRenyiQFixedWeightValueSet_sInf_ge_sandwichedRenyiQ_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ≤
      sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) := by
  have hnonempty : (sandwichedRenyiQFixedWeightValueSet ρ σ α).Nonempty := by
    refine ⟨frankLiebFixedWeightObjective ρ σ (1 : CMatrix a) α ((1 - α) / α), ?_⟩
    exact sandwichedRenyiQFixedWeightValueSet_mem
      (ρ := ρ) (σ := σ) (H := (1 : CMatrix a)) Matrix.PosDef.one α
  exact le_csInf
    hnonempty
    (sandwichedRenyiQFixedWeightValueSet_lowerBound_sandwichedRenyiQ_posDef
      hρ hσ hα_half hα_lt_one)

/-- The positive-definite reverse-Holder optimizer induces an actual
fixed-weight Frank--Lieb value equal to `Q_α(ρ, σ)`.

This is the optimizer half of Gour's Young variational formula. It constructs
`H = σ^(c/2) N^(-c) σ^(c/2)` from the normalized reverse-Holder optimizer
`N` of the sandwiched inner operator. -/
theorem sandwichedRenyiQ_mem_fixedWeightValueSet_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ∈
      sandwichedRenyiQFixedWeightValueSet ρ σ α := by
  let c : ℝ := (1 - α) / α
  let s : ℝ := c / 2
  let M : CMatrix a := sandwichedRenyiQInner ρ σ α
  let hM : M.PosSemidef := by
    simpa [M] using sandwichedRenyiQInner_posSemidef hρ.posSemidef hσ.posSemidef α
  let Q : ℝ := sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α
  let N : CMatrix a := psdTraceReverseHolderOptimizer M hM α
  let S : CMatrix a := CFC.rpow σ s
  let D : CMatrix a := CFC.rpow σ (-s)
  let W : CMatrix a := CFC.rpow N (-c)
  let H : CMatrix a := S * W * S
  have hα_pos : 0 < α := by linarith
  have hc_pos : 0 < c := by
    simpa [c] using sandwichedRenyiQ_frankLiebExponent_pos hα_half hα_lt_one
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hMdef : M.PosDef := by
    simpa [M] using sandwichedRenyiQInner_posDef hρ hσ α
  have hMne : M ≠ 0 := by
    intro hzero
    have htr : (0 : ℂ) < M.trace := Matrix.PosDef.trace_pos hMdef
    rw [hzero] at htr
    simp at htr
  have hQ_power_pos : 0 < psdTracePower M hM α :=
    psdTracePower_pos_of_ne_zero M hM hMne
  have hNdef : N.PosDef :=
    psdTraceReverseHolderOptimizer_posDef_of_posDef hM hMdef hQ_power_pos
  have hNpsd : N.PosSemidef := hNdef.posSemidef
  rcases psdTraceReverseHolderOptimizer_props hM hα_pos hQ_power_pos with
    ⟨_hN, hNtr, _hSupport, hattain⟩
  have hQ_eq_power : Q = psdTracePower M hM α := by
    simpa [Q, M] using
      sandwichedRenyiQ_eq_psdTracePower_QInner hρ.posSemidef hσ.posSemidef α
  have hQ_pos : 0 < Q := by
    simpa [hQ_eq_power] using hQ_power_pos
  have hschatten :
      ((M * CFC.rpow N (1 - 1 / α)).trace).re =
        Real.rpow Q (1 / α) := by
    have hnorm :
        psdSchattenPNorm M hM ⟨α, hα_pos⟩ = Real.rpow Q (1 / α) := by
      rw [psdSchattenPNorm, Internal.psdSchattenExpression, ← hQ_eq_power]
    exact hattain.symm.trans hnorm
  have hexp : -c = 1 - 1 / α := by
    dsimp [c]
    field_simp [ne_of_gt hα_pos]
    ring
  have hW_eq : W = CFC.rpow N (1 - 1 / α) := by
    simp [W, hexp]
  have hSdef : S.PosDef := by
    simpa [S] using cMatrix_rpow_posDef_of_posDef hσ s
  have hSstar : star S = S := hSdef.isHermitian.eq
  have hWdef : W.PosDef := by
    simpa [W] using cMatrix_rpow_posDef_of_posDef hNdef (-c)
  have hH : H.PosDef := by
    have hconj : (star S * W * S).PosDef := by
      rw [Matrix.IsUnit.posDef_star_left_conjugate_iff hSdef.isUnit]
      exact hWdef
    rwa [hSstar] at hconj
  have hDS : D * S = 1 := by
    simpa [D, S, s] using
      (CFC.rpow_neg_mul_rpow (a := σ) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  have hSD : S * D = 1 := by
    simpa [D, S, s] using
      (CFC.rpow_mul_rpow_neg (a := σ) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  have hDHD : D * H * D = W := by
    calc
      D * H * D = D * (S * W * S) * D := rfl
      _ = (D * S) * W * (S * D) := by
        simp [Matrix.mul_assoc]
      _ = W := by
        rw [hDS, hSD]
        simp
  have hx :
      ((ρ * H).trace).re = Real.rpow Q (1 / α) := by
    have htrace :=
      sandwichedRenyiQInner_mul_sourceWeight_trace_re_eq
        (a := a) (ρ := ρ) (σ := σ) (H := H) hσ
        (α := α) (c := c) (rfl : c = (1 - α) / α)
    have htraceD : ((M * (D * H * D)).trace).re = ((ρ * H).trace).re := by
      simpa [M, D, c] using htrace
    calc
      ((ρ * H).trace).re = ((M * (D * H * D)).trace).re := htraceD.symm
      _ = ((M * W).trace).re := by rw [hDHD]
      _ = ((M * CFC.rpow N (1 - 1 / α)).trace).re := by
        rw [hW_eq]
      _ = Real.rpow Q (1 / α) := hschatten
  have hy :
      frankLiebSourceSigmaTerm σ H c = 1 := by
    have hinner : (CFC.rpow σ (-(c / 2)) * H *
        CFC.rpow σ (-(c / 2))) = W := by
      simpa [D, s] using hDHD
    have hpowW : CFC.rpow W (-(1 / c)) = N := by
      have hr_ne : (-c : ℝ) ≠ 0 := neg_ne_zero.mpr hc_ne
      have hrt : (-c : ℝ) * (-(1 / c)) = (1 : ℝ) := by
        field_simp [hc_ne]
      calc
        CFC.rpow W (-(1 / c)) =
            CFC.rpow N (1 : ℝ) := by
              simpa [W] using
                cMatrix_rpow_rpow_of_posDef (A := N) hNdef hr_ne hrt
        _ = N := by
              exact CFC.rpow_one N
                (ha := Matrix.nonneg_iff_posSemidef.mpr hNdef.posSemidef)
    calc
      frankLiebSourceSigmaTerm σ H c =
          ((CFC.rpow (CFC.rpow σ (-(c / 2)) * H *
            CFC.rpow σ (-(c / 2))) (-(1 / c))).trace).re := rfl
      _ = ((CFC.rpow W (-(1 / c))).trace).re := by rw [hinner]
      _ = N.trace.re := by rw [hpowW]
      _ = 1 := hNtr
  have hfixed :
      frankLiebFixedWeightObjective ρ σ H α c = Q := by
    have hsource :
        frankLiebSourceFixedWeightObjective ρ σ H α c = Q := by
      unfold frankLiebSourceFixedWeightObjective
      calc
        ((ρ * H).trace).re ^ α * frankLiebSourceSigmaTerm σ H c ^ (1 - α) =
            (Real.rpow Q (1 / α)) ^ α * (1 : ℝ) ^ (1 - α) := by
              rw [hx, hy]
        _ = Q := by
              rw [show (Real.rpow Q (1 / α)) ^ α = Q by
                simpa [one_div] using
                  (Real.rpow_inv_rpow (le_of_lt hQ_pos) (ne_of_gt hα_pos))]
              simp
    have hsigma :
        frankLiebSourceSigmaTerm σ H c =
          (let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
          ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re) :=
      frankLiebSourceSigmaTerm_eq_frankLieb_sigmaTerm
        (a := a) (σ := σ) (H := H) hσ hH (c := c)
    have hobj :
        frankLiebSourceFixedWeightObjective ρ σ H α c =
          frankLiebFixedWeightObjective ρ σ H α c := by
      unfold frankLiebSourceFixedWeightObjective frankLiebFixedWeightObjective
      rw [hsigma]
    exact hobj.symm.trans hsource
  refine ⟨H, hH, ?_⟩
  simpa [c] using hfixed.symm

/-- Infimum upper-bound direction of Gour's fixed-weight variational formula:
the fixed-weight infimum is at most the sandwiched `Q` value. -/
theorem sandwichedRenyiQFixedWeightValueSet_sInf_le_sandwichedRenyiQ_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) ≤
      sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α := by
  have hbdd : BddBelow (sandwichedRenyiQFixedWeightValueSet ρ σ α) :=
    ⟨0, sandwichedRenyiQFixedWeightValueSet_lowerBound_zero
      hρ.posSemidef hσ.posSemidef α⟩
  exact csInf_le hbdd
    (sandwichedRenyiQ_mem_fixedWeightValueSet_posDef
      hρ hσ hα_half hα_lt_one)

/-- Positive-definite fixed-weight Frank--Lieb variational formula for the
PSD-friendly low-`α` `Q` functional. -/
theorem sandwichedRenyiQFixedWeightValueSet_sInf_eq_sandwichedRenyiQ_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) =
      sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α :=
  le_antisymm
    (sandwichedRenyiQFixedWeightValueSet_sInf_le_sandwichedRenyiQ_posDef
      hρ hσ hα_half hα_lt_one)
    (sandwichedRenyiQFixedWeightValueSet_sInf_ge_sandwichedRenyiQ_posDef
      hρ hσ hα_half hα_lt_one)

/-- Zero is a lower bound for the additive Gour/Frank--Lieb value set on PSD
inputs in the low-`alpha` weight range. -/
theorem sandwichedRenyiQAdditiveValueSet_lowerBound_zero
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    0 ∈ lowerBounds (sandwichedRenyiQAdditiveValueSet ρ σ α) := by
  intro y hy
  rcases hy with ⟨H, hH, rfl⟩
  exact frankLiebAdditiveObjective_nonneg hρ hσ hH hα0 hα1

/-- Gour additive value-set lower-bound direction: for positive-definite
inputs, `Q_α(ρ, σ)` is a lower bound for every additive Young objective. -/
theorem sandwichedRenyiQAdditiveValueSet_lowerBound_sandwichedRenyiQ_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ∈
      lowerBounds (sandwichedRenyiQAdditiveValueSet ρ σ α) := by
  have hα_nonneg : 0 ≤ α := by linarith
  have hα_le_one : α ≤ 1 := le_of_lt hα_lt_one
  intro y hy
  rcases hy with ⟨H, hH, rfl⟩
  have hQ_le_fixed :
      sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ≤
        frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) :=
    sandwichedRenyiQ_le_frankLiebFixedWeightObjective_posDef
      hρ hσ hH hα_half hα_lt_one
  have hfixed_le_add :
      frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) ≤
        frankLiebAdditiveObjective ρ σ H α ((1 - α) / α) :=
    frankLiebFixedWeightObjective_le_additiveObjective
      hρ.posSemidef hσ.posSemidef hH hα_nonneg hα_le_one
  exact hQ_le_fixed.trans hfixed_le_add

/-- Infimum lower-bound direction of Gour's additive variational formula. -/
theorem sandwichedRenyiQAdditiveValueSet_sInf_ge_sandwichedRenyiQ_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ≤
      sInf (sandwichedRenyiQAdditiveValueSet ρ σ α) := by
  have hnonempty : (sandwichedRenyiQAdditiveValueSet ρ σ α).Nonempty := by
    refine ⟨frankLiebAdditiveObjective ρ σ (1 : CMatrix a) α ((1 - α) / α), ?_⟩
    exact sandwichedRenyiQAdditiveValueSet_mem
      (ρ := ρ) (σ := σ) (H := (1 : CMatrix a)) Matrix.PosDef.one α
  exact le_csInf
    hnonempty
    (sandwichedRenyiQAdditiveValueSet_lowerBound_sandwichedRenyiQ_posDef
      hρ hσ hα_half hα_lt_one)

/-- For zero left input, zero is the least fixed-weight Frank--Lieb value. -/
theorem sandwichedRenyiQFixedWeightValueSet_zero_left_isLeast
    (σ : CMatrix a) (hσ : σ.PosSemidef) {α : ℝ} (hα_pos : 0 < α) :
    IsLeast (sandwichedRenyiQFixedWeightValueSet (0 : CMatrix a) σ α) 0 := by
  constructor
  · refine ⟨(1 : CMatrix a), Matrix.PosDef.one, ?_⟩
    simpa using
      (frankLiebFixedWeightObjective_zero_left
        (a := a) σ (1 : CMatrix a) (α := α) (c := (1 - α) / α) hα_pos).symm
  · exact sandwichedRenyiQFixedWeightValueSet_lowerBound_zero
      (ρ := (0 : CMatrix a)) (σ := σ) Matrix.PosSemidef.zero hσ α

/-- For zero left input, the fixed-weight Frank--Lieb infimum equals the
PSD-friendly `Q` value. -/
theorem sandwichedRenyiQFixedWeightValueSet_sInf_eq_zero_left
    (σ : CMatrix a) (hσ : σ.PosSemidef) {α : ℝ} (hα_pos : 0 < α) :
    sInf (sandwichedRenyiQFixedWeightValueSet (0 : CMatrix a) σ α) =
      sandwichedRenyiQ (0 : CMatrix a) σ Matrix.PosSemidef.zero hσ α := by
  calc
    sInf (sandwichedRenyiQFixedWeightValueSet (0 : CMatrix a) σ α) = 0 :=
      (sandwichedRenyiQFixedWeightValueSet_zero_left_isLeast
        (a := a) σ hσ hα_pos).csInf_eq
    _ = sandwichedRenyiQ (0 : CMatrix a) σ Matrix.PosSemidef.zero hσ α :=
      (sandwichedRenyiQ_zero_left σ hσ hα_pos).symm

/-- Positive-definite-reference zero-inner branch of the fixed-weight
Frank--Lieb variational formula. -/
theorem sandwichedRenyiQFixedWeightValueSet_sInf_eq_of_inner_zero
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosDef)
    {α : ℝ} (hα_pos : 0 < α)
    (hinner : sandwichedRenyiQInner ρ σ α = 0) :
    sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) =
      sandwichedRenyiQ ρ σ hρ hσ.posSemidef α := by
  have hρzero :
      ρ = 0 :=
    (sandwichedRenyiQInner_eq_zero_iff_left_eq_zero_of_sigma_posDef
      (a := a) (ρ := ρ) (σ := σ) hσ α).mp hinner
  subst hρzero
  exact sandwichedRenyiQFixedWeightValueSet_sInf_eq_zero_left
    (a := a) σ hσ.posSemidef hα_pos

/-- The fixed-weight value set is bounded below on PSD inputs. -/
theorem sandwichedRenyiQFixedWeightValueSet_bddBelow
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (α : ℝ) :
    BddBelow (sandwichedRenyiQFixedWeightValueSet ρ σ α) :=
  ⟨0, sandwichedRenyiQFixedWeightValueSet_lowerBound_zero hρ hσ α⟩

theorem sandwichedRenyiQAdditiveValueSet_bddBelow
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    BddBelow (sandwichedRenyiQAdditiveValueSet ρ σ α) :=
  ⟨0, sandwichedRenyiQAdditiveValueSet_lowerBound_zero hρ hσ hα0 hα1⟩

/-- Any fixed-weight value bounds the infimum of the fixed-weight family from
above. -/
theorem sandwichedRenyiQFixedWeightValueSet_sInf_le_fixedWeight
    {ρ σ H : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hH : H.PosDef) (α : ℝ) :
    sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) ≤
      frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) :=
  csInf_le (sandwichedRenyiQFixedWeightValueSet_bddBelow hρ hσ α)
    (sandwichedRenyiQFixedWeightValueSet_mem hH α)

/-- In the positive diagonal case, the sandwiched `Q` value is attained by an
explicit member of the fixed-weight Frank--Lieb value family. -/
theorem sandwichedRenyiQ_diagonal_mem_fixedWeightValueSet_posDef
    [Nonempty a] (ρ σ : a → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α ∈
      sandwichedRenyiQFixedWeightValueSet
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        α := by
  classical
  let h : a → ℝ := fun i => ρ i ^ (α - 1) * σ i ^ (1 - α)
  let H : CMatrix a := Matrix.diagonal fun i => (h i : ℂ)
  have hh : ∀ i, 0 < h i := by
    intro i
    exact mul_pos (Real.rpow_pos_of_pos (hρ i) (α - 1))
      (Real.rpow_pos_of_pos (hσ i) (1 - α))
  have hH : H.PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    change 0 < ((h i : ℝ) : ℂ)
    exact_mod_cast hh i
  refine ⟨H, hH, ?_⟩
  exact (frankLiebFixedWeightObjective_diagonal_optimizer_eq_sandwichedRenyiQ
    (a := a) ρ σ hρ hσ hα_pos hα_lt_one).symm

/-- Infimum upper bound supplied by the explicit positive diagonal
Frank--Lieb optimizer. -/
theorem sandwichedRenyiQFixedWeightValueSet_sInf_le_diagonal_sandwichedRenyiQ_posDef
    [Nonempty a] (ρ σ : a → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    sInf (sandwichedRenyiQFixedWeightValueSet
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        α) ≤
      sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α := by
  exact csInf_le
    (sandwichedRenyiQFixedWeightValueSet_bddBelow
      (ρ := (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a))
      (σ := (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a))
      (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
      (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
      α)
    (sandwichedRenyiQ_diagonal_mem_fixedWeightValueSet_posDef
      (a := a) ρ σ hρ hσ hα_pos hα_lt_one)

/-- Diagonal-only fixed-weight Frank--Lieb values.

This auxiliary family isolates the commuting/classical fixed-weight
variational formula from the still-missing noncommutative minimization over
all positive-definite weights. -/
def sandwichedRenyiQDiagonalFixedWeightValueSet
    (ρ σ : a → ℝ) (α : ℝ) : Set ℝ :=
  {y | ∃ h : a → ℝ, (∀ i, 0 < h i) ∧
    y = frankLiebFixedWeightObjective
      (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
      (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
      (Matrix.diagonal fun i => (h i : ℂ) : CMatrix a)
      α ((1 - α) / α)}

theorem sandwichedRenyiQDiagonalFixedWeightValueSet_mem
    (ρ σ h : a → ℝ) (hh : ∀ i, 0 < h i) (α : ℝ) :
    frankLiebFixedWeightObjective
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (h i : ℂ) : CMatrix a)
        α ((1 - α) / α) ∈
      sandwichedRenyiQDiagonalFixedWeightValueSet ρ σ α :=
  ⟨h, hh, rfl⟩

/-- The diagonal sandwiched `Q` value is a lower bound for every positive
diagonal fixed-weight objective. -/
theorem sandwichedRenyiQDiagonalFixedWeightValueSet_lowerBound_sandwichedRenyiQ
    [Nonempty a] (ρ σ : a → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ hρ)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α ∈
      lowerBounds (sandwichedRenyiQDiagonalFixedWeightValueSet ρ σ α) := by
  intro y hy
  rcases hy with ⟨h, hh, rfl⟩
  exact sandwichedRenyiQ_diagonal_le_frankLiebFixedWeightObjective
    (a := a) ρ σ h hρ hσ hh hα_pos hα_lt_one

/-- In the positive diagonal case, the diagonal fixed-weight family attains
the sandwiched `Q` value. -/
theorem sandwichedRenyiQ_diagonal_mem_diagonalFixedWeightValueSet_posDef
    [Nonempty a] (ρ σ : a → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α ∈
      sandwichedRenyiQDiagonalFixedWeightValueSet ρ σ α := by
  classical
  let h : a → ℝ := fun i => ρ i ^ (α - 1) * σ i ^ (1 - α)
  have hh : ∀ i, 0 < h i := by
    intro i
    exact mul_pos (Real.rpow_pos_of_pos (hρ i) (α - 1))
      (Real.rpow_pos_of_pos (hσ i) (1 - α))
  refine ⟨h, hh, ?_⟩
  exact (frankLiebFixedWeightObjective_diagonal_optimizer_eq_sandwichedRenyiQ
    (a := a) ρ σ hρ hσ hα_pos hα_lt_one).symm

/-- Positive diagonal fixed-weight variational formula for the sandwiched
`Q` functional as an `IsLeast` statement. -/
theorem sandwichedRenyiQDiagonalFixedWeightValueSet_isLeast_posDef
    [Nonempty a] (ρ σ : a → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    IsLeast (sandwichedRenyiQDiagonalFixedWeightValueSet ρ σ α)
      (sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α) := by
  constructor
  · exact sandwichedRenyiQ_diagonal_mem_diagonalFixedWeightValueSet_posDef
      (a := a) ρ σ hρ hσ hα_pos hα_lt_one
  · exact sandwichedRenyiQDiagonalFixedWeightValueSet_lowerBound_sandwichedRenyiQ
      (a := a) ρ σ (fun i => (hρ i).le) hσ hα_pos hα_lt_one

/-- Positive diagonal fixed-weight variational formula in `sInf` form. -/
theorem sandwichedRenyiQDiagonalFixedWeightValueSet_sInf_eq_posDef
    [Nonempty a] (ρ σ : a → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    sInf (sandwichedRenyiQDiagonalFixedWeightValueSet ρ σ α) =
      sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α :=
  (sandwichedRenyiQDiagonalFixedWeightValueSet_isLeast_posDef
    (a := a) ρ σ hρ hσ hα_pos hα_lt_one).csInf_eq

/-- Zero is a lower bound for the trace-one fixed-weight value set on PSD
inputs. -/
theorem sandwichedRenyiQFixedWeightStateValueSet_lowerBound_zero
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (α : ℝ) :
    0 ∈ lowerBounds (sandwichedRenyiQFixedWeightStateValueSet ρ σ α) := by
  intro y hy
  rcases hy with ⟨H, hH, _hHtr, rfl⟩
  exact frankLiebFixedWeightObjective_nonneg hρ hσ hH α ((1 - α) / α)

/-- The trace-one fixed-weight value set is bounded below on PSD inputs. -/
theorem sandwichedRenyiQFixedWeightStateValueSet_bddBelow
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (α : ℝ) :
    BddBelow (sandwichedRenyiQFixedWeightStateValueSet ρ σ α) :=
  ⟨0, sandwichedRenyiQFixedWeightStateValueSet_lowerBound_zero hρ hσ α⟩

/-- Any trace-one fixed-weight value bounds the infimum of the trace-one
family from above. -/
theorem sandwichedRenyiQFixedWeightStateValueSet_sInf_le_fixedWeight
    {ρ σ H : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hH : H.PosDef) (hHtr : H.trace.re = 1) (α : ℝ) :
    sInf (sandwichedRenyiQFixedWeightStateValueSet ρ σ α) ≤
      frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) :=
  csInf_le (sandwichedRenyiQFixedWeightStateValueSet_bddBelow hρ hσ α)
    (sandwichedRenyiQFixedWeightStateValueSet_mem hH hHtr α)

/-- The fixed-weight value family is nonempty, using the identity weight. -/
theorem sandwichedRenyiQFixedWeightValueSet_nonempty
    [Nonempty a] (ρ σ : CMatrix a) (α : ℝ) :
    (sandwichedRenyiQFixedWeightValueSet ρ σ α).Nonempty := by
  refine ⟨frankLiebFixedWeightObjective ρ σ (1 : CMatrix a) α ((1 - α) / α), ?_⟩
  exact sandwichedRenyiQFixedWeightValueSet_mem (ρ := ρ) (σ := σ)
    (H := (1 : CMatrix a)) Matrix.PosDef.one α

/-- The additive Gour/Frank--Lieb value family is nonempty, using the
identity weight. -/
theorem sandwichedRenyiQAdditiveValueSet_nonempty
    [Nonempty a] (ρ σ : CMatrix a) (α : ℝ) :
    (sandwichedRenyiQAdditiveValueSet ρ σ α).Nonempty := by
  refine ⟨frankLiebAdditiveObjective ρ σ (1 : CMatrix a) α ((1 - α) / α), ?_⟩
  exact sandwichedRenyiQAdditiveValueSet_mem (ρ := ρ) (σ := σ)
    (H := (1 : CMatrix a)) Matrix.PosDef.one α

/-- On full-rank inputs, optimizing Gour's additive Young objective over
unrestricted positive weights gives the same infimum as the multiplicative
fixed-weight objective family.

The two inequalities are the source AM--GM bound and the reverse optimized
rescaling supplied by
`frankLiebAdditiveObjective_optimalScale_eq_fixedWeight_posDef`. -/
theorem sandwichedRenyiQAdditiveValueSet_sInf_eq_fixedWeightValueSet_sInf_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sInf (sandwichedRenyiQAdditiveValueSet ρ σ α) =
      sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) := by
  let c : ℝ := (1 - α) / α
  have hα_nonneg : 0 ≤ α := by linarith
  have hα_le_one : α ≤ 1 := le_of_lt hα_lt_one
  have hc_pos : 0 < c := by
    simpa [c] using sandwichedRenyiQ_frankLiebExponent_pos hα_half hα_lt_one
  have hA_bdd :
      BddBelow (sandwichedRenyiQAdditiveValueSet ρ σ α) :=
    sandwichedRenyiQAdditiveValueSet_bddBelow
      hρ.posSemidef hσ.posSemidef hα_nonneg hα_le_one
  have hF_bdd :
      BddBelow (sandwichedRenyiQFixedWeightValueSet ρ σ α) :=
    sandwichedRenyiQFixedWeightValueSet_bddBelow
      hρ.posSemidef hσ.posSemidef α
  have hA_nonempty :
      (sandwichedRenyiQAdditiveValueSet ρ σ α).Nonempty :=
    sandwichedRenyiQAdditiveValueSet_nonempty ρ σ α
  have hF_nonempty :
      (sandwichedRenyiQFixedWeightValueSet ρ σ α).Nonempty :=
    sandwichedRenyiQFixedWeightValueSet_nonempty ρ σ α
  have hA_le_F :
      sInf (sandwichedRenyiQAdditiveValueSet ρ σ α) ≤
        sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) := by
    refine le_csInf hF_nonempty ?_
    intro z hz
    rcases hz with ⟨H, hH, rfl⟩
    let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
    let x : ℝ := ((ρ * H).trace).re
    let y : ℝ := ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re
    let lambda : ℝ := (y / x) ^ (1 - α)
    have hx : 0 < x := by
      simpa [x] using _root_.QIT.trace_mul_posDef_re_pos hρ hH
    have hy : 0 < y := by
      simpa [y, K, c] using frankLieb_sigmaTerm_pos
        (a := a) (H := H) (σ := σ) hH hσ c
    have hlambda_pos : 0 < lambda := by
      dsimp [lambda]
      exact Real.rpow_pos_of_pos (div_pos hy hx) (1 - α)
    have hHscaled : (lambda • H : CMatrix a).PosDef := by
      simpa using Matrix.PosDef.smul hH hlambda_pos
    have hscaled :
        frankLiebAdditiveObjective ρ σ (lambda • H : CMatrix a) α c =
          frankLiebFixedWeightObjective ρ σ H α c := by
      simpa [c, K, x, y, lambda] using
        frankLiebAdditiveObjective_optimalScale_eq_fixedWeight_posDef
          (a := a) (ρ := ρ) (σ := σ) (H := H)
          hρ hσ hH hα_half hα_lt_one
    have hmem :
        frankLiebFixedWeightObjective ρ σ H α c ∈
          sandwichedRenyiQAdditiveValueSet ρ σ α := by
      refine ⟨lambda • H, hHscaled, ?_⟩
      simpa [c] using hscaled.symm
    simpa [c] using csInf_le hA_bdd hmem
  have hF_le_A :
      sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) ≤
        sInf (sandwichedRenyiQAdditiveValueSet ρ σ α) := by
    refine le_csInf hA_nonempty ?_
    intro z hz
    rcases hz with ⟨H, hH, rfl⟩
    have hfixed_le_add :
        frankLiebFixedWeightObjective ρ σ H α c ≤
          frankLiebAdditiveObjective ρ σ H α c :=
      frankLiebFixedWeightObjective_le_additiveObjective
        hρ.posSemidef hσ.posSemidef hH hα_nonneg hα_le_one
    have hsInf_le_fixed :
        sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) ≤
          frankLiebFixedWeightObjective ρ σ H α c := by
      simpa [c] using sandwichedRenyiQFixedWeightValueSet_sInf_le_fixedWeight
        hρ.posSemidef hσ.posSemidef hH α
    exact hsInf_le_fixed.trans hfixed_le_add
  exact le_antisymm hA_le_F hF_le_A

/-- A fixed-weight optimizer for the multiplicative Frank--Lieb family gives
an actual member of Gour's additive Young value family.

This is the source-shaped optimizer direction in Gour's variational formula:
the additive objective may first optimize over positive scalar rescalings of a
weight, and at the Young-optimal scale it agrees with the multiplicative
fixed-weight objective. -/
theorem sandwichedRenyiQ_mem_additiveValueSet_of_fixedWeight_eq_posDef
    [Nonempty a] {ρ σ H : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hH : H.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hfixed :
      frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) =
        sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α) :
    sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α ∈
      sandwichedRenyiQAdditiveValueSet ρ σ α := by
  let c : ℝ := (1 - α) / α
  let K : CMatrix a := CFC.rpow H (-(1 / 2 : ℝ))
  let x : ℝ := ((ρ * H).trace).re
  let y : ℝ := ((CFC.rpow (K * CFC.rpow σ c * K) (1 / c)).trace).re
  let lambda : ℝ := (y / x) ^ (1 - α)
  have hx : 0 < x := by
    simpa [x] using _root_.QIT.trace_mul_posDef_re_pos hρ hH
  have hy : 0 < y := by
    simpa [y, K, c] using frankLieb_sigmaTerm_pos
      (a := a) (H := H) (σ := σ) hH hσ c
  have hlambda_pos : 0 < lambda := by
    dsimp [lambda]
    exact Real.rpow_pos_of_pos (div_pos hy hx) (1 - α)
  have hHscaled : (lambda • H : CMatrix a).PosDef := by
    simpa using Matrix.PosDef.smul hH hlambda_pos
  have hscaled :
      frankLiebAdditiveObjective ρ σ (lambda • H : CMatrix a) α c =
        frankLiebFixedWeightObjective ρ σ H α c := by
    simpa [c, K, x, y, lambda] using
      frankLiebAdditiveObjective_optimalScale_eq_fixedWeight_posDef
        (a := a) (ρ := ρ) (σ := σ) (H := H)
        hρ hσ hH hα_half hα_lt_one
  refine ⟨lambda • H, hHscaled, ?_⟩
  calc
    sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α =
        frankLiebFixedWeightObjective ρ σ H α c := by
          simpa [c] using hfixed.symm
    _ = frankLiebAdditiveObjective ρ σ (lambda • H : CMatrix a) α c :=
          hscaled.symm

/-- In the positive diagonal case, Gour's additive Young value family contains
the sandwiched `Q` value.

This is the commuting source sanity check for the additive variational route:
the diagonal fixed-weight optimizer is transported to the additive family by
the Young-optimal scalar rescaling. -/
theorem sandwichedRenyiQ_diagonal_mem_additiveValueSet_posDef
    [Nonempty a] (ρ σ : a → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hα_half : 1 / 2 < α) :
    sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α ∈
      sandwichedRenyiQAdditiveValueSet
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        α := by
  classical
  let ρD : CMatrix a := Matrix.diagonal fun i => (ρ i : ℂ)
  let σD : CMatrix a := Matrix.diagonal fun i => (σ i : ℂ)
  let h : a → ℝ := fun i => ρ i ^ (α - 1) * σ i ^ (1 - α)
  let H : CMatrix a := Matrix.diagonal fun i => (h i : ℂ)
  have hρD : ρD.PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    change 0 < ((ρ i : ℝ) : ℂ)
    exact_mod_cast hρ i
  have hσD : σD.PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    change 0 < ((σ i : ℝ) : ℂ)
    exact_mod_cast hσ i
  have hh : ∀ i, 0 < h i := by
    intro i
    exact mul_pos (Real.rpow_pos_of_pos (hρ i) (α - 1))
      (Real.rpow_pos_of_pos (hσ i) (1 - α))
  have hH : H.PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    change 0 < ((h i : ℝ) : ℂ)
    exact_mod_cast hh i
  have hfixed :
      frankLiebFixedWeightObjective ρD σD H α ((1 - α) / α) =
        sandwichedRenyiQ ρD σD hρD.posSemidef hσD.posSemidef α := by
    simpa [ρD, σD, H, h] using
      frankLiebFixedWeightObjective_diagonal_optimizer_eq_sandwichedRenyiQ
        (a := a) ρ σ hρ hσ hα_pos hα_lt_one
  have hmem :
      sandwichedRenyiQ ρD σD hρD.posSemidef hσD.posSemidef α ∈
        sandwichedRenyiQAdditiveValueSet ρD σD α :=
    sandwichedRenyiQ_mem_additiveValueSet_of_fixedWeight_eq_posDef
      (a := a) hρD hσD hH hα_half hα_lt_one hfixed
  simpa [ρD, σD] using hmem

/-- Infimum upper-bound direction of Gour's additive variational formula in
the positive diagonal case. -/
theorem sandwichedRenyiQAdditiveValueSet_sInf_le_diagonal_sandwichedRenyiQ_posDef
    [Nonempty a] (ρ σ : a → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sInf (sandwichedRenyiQAdditiveValueSet
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        α) ≤
      sandwichedRenyiQ
        (Matrix.diagonal fun i => (ρ i : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => (σ i : ℂ) : CMatrix a)
        (cMatrix_diagonal_ofReal_posSemidef ρ fun i => (hρ i).le)
        (cMatrix_diagonal_ofReal_posSemidef σ fun i => (hσ i).le)
        α := by
  let ρD : CMatrix a := Matrix.diagonal fun i => (ρ i : ℂ)
  let σD : CMatrix a := Matrix.diagonal fun i => (σ i : ℂ)
  have hρD : ρD.PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    change 0 < ((ρ i : ℝ) : ℂ)
    exact_mod_cast hρ i
  have hσD : σD.PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    change 0 < ((σ i : ℝ) : ℂ)
    exact_mod_cast hσ i
  have hα_nonneg : 0 ≤ α := by linarith
  have hα_le_one : α ≤ 1 := le_of_lt hα_lt_one
  have hmem :
      sandwichedRenyiQ ρD σD hρD.posSemidef hσD.posSemidef α ∈
        sandwichedRenyiQAdditiveValueSet ρD σD α := by
    simpa [ρD, σD] using
      sandwichedRenyiQ_diagonal_mem_additiveValueSet_posDef
        (a := a) ρ σ hρ hσ (by linarith) hα_lt_one hα_half
  have hbdd :
      BddBelow (sandwichedRenyiQAdditiveValueSet ρD σD α) :=
    sandwichedRenyiQAdditiveValueSet_bddBelow
      hρD.posSemidef hσD.posSemidef hα_nonneg hα_le_one
  simpa [ρD, σD] using csInf_le hbdd hmem

/-- Transport a completed fixed-weight variational formula to the
source-shaped additive Gour/Frank--Lieb value family. -/
theorem sandwichedRenyiQAdditiveValueSet_sInf_eq_of_fixedWeight_sInf_eq_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hfixed :
      sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) =
        sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α) :
    sInf (sandwichedRenyiQAdditiveValueSet ρ σ α) =
      sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α := by
  rw [sandwichedRenyiQAdditiveValueSet_sInf_eq_fixedWeightValueSet_sInf_posDef
    hρ hσ hα_half hα_lt_one, hfixed]

/-- Positive-definite additive Gour/Frank--Lieb variational formula for the
PSD-friendly low-`α` `Q` functional. -/
theorem sandwichedRenyiQAdditiveValueSet_sInf_eq_sandwichedRenyiQ_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sInf (sandwichedRenyiQAdditiveValueSet ρ σ α) =
      sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α :=
  sandwichedRenyiQAdditiveValueSet_sInf_eq_of_fixedWeight_sInf_eq_posDef
    hρ hσ hα_half hα_lt_one
    (sandwichedRenyiQFixedWeightValueSet_sInf_eq_sandwichedRenyiQ_posDef
      hρ hσ hα_half hα_lt_one)

/-- Transport a completed additive Gour/Frank--Lieb variational formula back
to the multiplicative fixed-weight family used by existing concavity
infrastructure. -/
theorem sandwichedRenyiQFixedWeightValueSet_sInf_eq_of_additive_sInf_eq_posDef
    [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hadd :
      sInf (sandwichedRenyiQAdditiveValueSet ρ σ α) =
        sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α) :
    sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) =
      sandwichedRenyiQ ρ σ hρ.posSemidef hσ.posSemidef α := by
  have heq :=
    sandwichedRenyiQAdditiveValueSet_sInf_eq_fixedWeightValueSet_sInf_posDef
      hρ hσ hα_half hα_lt_one
  rw [← heq, hadd]

/-- Trace-one fixed-weight values are nonempty, using the identity normalized
by the dimension trace. -/
theorem sandwichedRenyiQFixedWeightStateValueSet_nonempty
    [Nonempty a] (ρ σ : CMatrix a) (α : ℝ) :
    (sandwichedRenyiQFixedWeightStateValueSet ρ σ α).Nonempty := by
  let trI : ℝ := ((1 : CMatrix a).trace).re
  have htrI_pos : 0 < trI := by
    exact (Complex.pos_iff.mp (Matrix.PosDef.trace_pos
      (Matrix.PosDef.one : (1 : CMatrix a).PosDef))).1
  let H : CMatrix a := (trI⁻¹ : ℝ) • (1 : CMatrix a)
  have hH : H.PosDef := by
    simpa [H] using Matrix.PosDef.smul
      (Matrix.PosDef.one : (1 : CMatrix a).PosDef) (inv_pos.mpr htrI_pos)
  have htrI_im : ((1 : CMatrix a).trace).im = 0 :=
    (Complex.pos_iff.mp (Matrix.PosDef.trace_pos
      (Matrix.PosDef.one : (1 : CMatrix a).PosDef))).2.symm
  have hHtr : H.trace.re = 1 := by
    simp [H, trI, Matrix.trace_smul]
  refine ⟨frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α), ?_⟩
  exact sandwichedRenyiQFixedWeightStateValueSet_mem hH hHtr α

/-- In the strict low-alpha range, the unrestricted fixed-weight values equal
the trace-one fixed-weight values.  This removes the normalization mismatch
between Frank--Lieb weights and reverse-Holder side-states. -/
theorem sandwichedRenyiQFixedWeightValueSet_eq_stateValueSet_strictLowAlpha
    [Nonempty a] {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQFixedWeightValueSet ρ σ α =
      sandwichedRenyiQFixedWeightStateValueSet ρ σ α := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨H, hH, rfl⟩
    let trH : ℝ := H.trace.re
    have htrH_pos : 0 < trH :=
      (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hH)).1
    let Hn : CMatrix a := (trH⁻¹ : ℝ) • H
    have hHn : Hn.PosDef := by
      simpa [Hn] using Matrix.PosDef.smul hH (inv_pos.mpr htrH_pos)
    have htrH_im : H.trace.im = 0 :=
      (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hH)).2.symm
    have hHntr : Hn.trace.re = 1 := by
      simp [Hn, trH, Matrix.trace_smul, Complex.mul_re, htrH_im,
        inv_mul_cancel₀ (ne_of_gt htrH_pos)]
    have hinv_pos : 0 < trH⁻¹ := inv_pos.mpr htrH_pos
    have hobj :
        frankLiebFixedWeightObjective ρ σ Hn α ((1 - α) / α) =
          frankLiebFixedWeightObjective ρ σ H α ((1 - α) / α) := by
      simpa [Hn, trH] using
        frankLiebFixedWeightObjective_real_smul_weight_strictLowAlpha
          (a := a) (ρ := ρ) (σ := σ) (H := H)
          hρ hσ hH hinv_pos hα_half hα_lt_one
    exact ⟨Hn, hHn, hHntr, hobj.symm⟩
  · intro hy
    rcases hy with ⟨H, hH, _hHtr, rfl⟩
    exact sandwichedRenyiQFixedWeightValueSet_mem hH α

/-- `sInf` form of the normalization bridge for fixed Frank--Lieb weights. -/
theorem sandwichedRenyiQFixedWeightValueSet_sInf_eq_stateValueSet_strictLowAlpha
    [Nonempty a] {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sInf (sandwichedRenyiQFixedWeightValueSet ρ σ α) =
      sInf (sandwichedRenyiQFixedWeightStateValueSet ρ σ α) := by
  rw [sandwichedRenyiQFixedWeightValueSet_eq_stateValueSet_strictLowAlpha
    hρ hσ hα_half hα_lt_one]

/-- Common normalized-weight convex upper value for the fixed-weight
Frank--Lieb variational family. -/
theorem sandwichedRenyiQFixedWeightStateValueSet_commonWeight_convexUpper_strictLowAlpha
    [Nonempty a] {H ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hH : H.PosDef) (hHtr : H.trace.re = 1)
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef)
    {α t : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ y ∈ sandwichedRenyiQFixedWeightStateValueSet
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂) α,
      t * frankLiebFixedWeightObjective ρ₁ σ₁ H α ((1 - α) / α) +
          (1 - t) * frankLiebFixedWeightObjective ρ₂ σ₂ H α ((1 - α) / α) ≤ y := by
  refine ⟨frankLiebFixedWeightObjective
      (cMatrixConvexCombination t ρ₁ ρ₂)
      (cMatrixConvexCombination t σ₁ σ₂) H α ((1 - α) / α), ?_, ?_⟩
  · exact sandwichedRenyiQFixedWeightStateValueSet_mem
      (ρ := cMatrixConvexCombination t ρ₁ ρ₂)
      (σ := cMatrixConvexCombination t σ₁ σ₂)
      (H := H) hH hHtr α
  · exact frankLiebFixedWeightObjective_concave_strictLowAlpha
      (a := a) (H := H) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (σ₁ := σ₁) (σ₂ := σ₂)
      hH hρ₁ hρ₂ hσ₁ hσ₂ hα_half hα_lt_one ht0 ht1

/-- Common-weight convex upper value for the fixed-weight Frank--Lieb
variational family.

For the same positive-definite weight `H`, the convex combination of the two
fixed-weight objective values is bounded by an actual member of the mixed
input value set.  This is the exact local form needed before passing from
fixed weights to the `sInf` variational formula for `sandwichedRenyiQ`. -/
theorem sandwichedRenyiQFixedWeightValueSet_commonWeight_convexUpper_strictLowAlpha
    [Nonempty a] {H ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hH : H.PosDef)
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef)
    {α t : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ y ∈ sandwichedRenyiQFixedWeightValueSet
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂) α,
      t * frankLiebFixedWeightObjective ρ₁ σ₁ H α ((1 - α) / α) +
          (1 - t) * frankLiebFixedWeightObjective ρ₂ σ₂ H α ((1 - α) / α) ≤ y := by
  refine ⟨frankLiebFixedWeightObjective
      (cMatrixConvexCombination t ρ₁ ρ₂)
      (cMatrixConvexCombination t σ₁ σ₂) H α ((1 - α) / α), ?_, ?_⟩
  · exact sandwichedRenyiQFixedWeightValueSet_mem
      (ρ := cMatrixConvexCombination t ρ₁ ρ₂)
      (σ := cMatrixConvexCombination t σ₁ σ₂)
      (H := H) hH α
  · exact frankLiebFixedWeightObjective_concave_strictLowAlpha
      (a := a) (H := H) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (σ₁ := σ₁) (σ₂ := σ₂)
      hH hρ₁ hρ₂ hσ₁ hσ₂ hα_half hα_lt_one ht0 ht1

/-- Common-weight convex upper value for the source-shaped additive
Gour/Frank--Lieb variational family.

This is the direct Gour-route analogue of
`sandwichedRenyiQFixedWeightValueSet_commonWeight_convexUpper_strictLowAlpha`.
It uses the additive objective concavity rather than passing through the
multiplicative fixed-weight objective. -/
theorem sandwichedRenyiQAdditiveValueSet_commonWeight_convexUpper_strictLowAlpha
    [Nonempty a] {H ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hH : H.PosDef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef)
    {α t : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ y ∈ sandwichedRenyiQAdditiveValueSet
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂) α,
      t * frankLiebAdditiveObjective ρ₁ σ₁ H α ((1 - α) / α) +
          (1 - t) * frankLiebAdditiveObjective ρ₂ σ₂ H α ((1 - α) / α) ≤ y := by
  refine ⟨frankLiebAdditiveObjective
      (cMatrixConvexCombination t ρ₁ ρ₂)
      (cMatrixConvexCombination t σ₁ σ₂) H α ((1 - α) / α), ?_, ?_⟩
  · exact sandwichedRenyiQAdditiveValueSet_mem
      (ρ := cMatrixConvexCombination t ρ₁ ρ₂)
      (σ := cMatrixConvexCombination t σ₁ σ₂)
      (H := H) hH α
  · exact frankLiebAdditiveObjective_concave
      (a := a) (H := H) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (σ₁ := σ₁) (σ₂ := σ₂)
      hH hσ₁.posSemidef hσ₂.posSemidef
      (le_of_lt hα_lt_one)
      (sandwichedRenyiQ_frankLiebExponent_pos hα_half hα_lt_one)
      (sandwichedRenyiQ_frankLiebExponent_lt_one hα_half hα_lt_one)
      ht0 ht1

/-- Handoff from Gour's additive `sInf` variational formula to joint
concavity of the sandwiched `Q` functional.

This is the source-shaped version of the Frank--Lieb gap isolation: once the
additive Gour variational family is identified with `Q`, the already proved
additive fixed-weight concavity gives joint concavity of `Q`. -/
theorem sandwichedRenyiQ_jointConcave_lowAlpha_of_additive_sInf_eq
    [Nonempty a] {ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef)
    {α t : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hQ₁ :
      sInf (sandwichedRenyiQAdditiveValueSet ρ₁ σ₁ α) =
        sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁.posSemidef α)
    (hQ₂ :
      sInf (sandwichedRenyiQAdditiveValueSet ρ₂ σ₂ α) =
        sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂.posSemidef α)
    (hQt :
      sInf (sandwichedRenyiQAdditiveValueSet
          (cMatrixConvexCombination t ρ₁ ρ₂)
          (cMatrixConvexCombination t σ₁ σ₂) α) =
        sandwichedRenyiQ
          (cMatrixConvexCombination t ρ₁ ρ₂)
          (cMatrixConvexCombination t σ₁ σ₂)
          (sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1)
          (sandwichedRenyiQ_sigma_mix_posSemidef hσ₁.posSemidef hσ₂.posSemidef
            ht0 ht1)
          α) :
    t * sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁.posSemidef α +
        (1 - t) * sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂.posSemidef α ≤
      sandwichedRenyiQ
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂)
        (sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1)
        (sandwichedRenyiQ_sigma_mix_posSemidef hσ₁.posSemidef hσ₂.posSemidef
          ht0 ht1)
        α := by
  let ρt : CMatrix a := cMatrixConvexCombination t ρ₁ ρ₂
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  let Q₁ : ℝ := sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁.posSemidef α
  let Q₂ : ℝ := sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂.posSemidef α
  have hρt : ρt.PosSemidef := by
    simpa [ρt] using sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1
  have hσt_psd : σt.PosSemidef := by
    simpa [σt] using
      sandwichedRenyiQ_sigma_mix_posSemidef hσ₁.posSemidef hσ₂.posSemidef
        ht0 ht1
  have hα_nonneg : 0 ≤ α := by linarith
  have hα_le_one : α ≤ 1 := le_of_lt hα_lt_one
  have hlower :
      t * Q₁ + (1 - t) * Q₂ ∈
        lowerBounds (sandwichedRenyiQAdditiveValueSet ρt σt α) := by
    intro y hy
    rcases hy with ⟨H, hH, rfl⟩
    have hQ₁_le :
        Q₁ ≤ frankLiebAdditiveObjective ρ₁ σ₁ H α ((1 - α) / α) := by
      have hsInf_le :
          sInf (sandwichedRenyiQAdditiveValueSet ρ₁ σ₁ α) ≤
            frankLiebAdditiveObjective ρ₁ σ₁ H α ((1 - α) / α) :=
        csInf_le
          (sandwichedRenyiQAdditiveValueSet_bddBelow
            hρ₁ hσ₁.posSemidef hα_nonneg hα_le_one)
          (sandwichedRenyiQAdditiveValueSet_mem hH α)
      simpa [Q₁, hQ₁] using hsInf_le
    have hQ₂_le :
        Q₂ ≤ frankLiebAdditiveObjective ρ₂ σ₂ H α ((1 - α) / α) := by
      have hsInf_le :
          sInf (sandwichedRenyiQAdditiveValueSet ρ₂ σ₂ α) ≤
            frankLiebAdditiveObjective ρ₂ σ₂ H α ((1 - α) / α) :=
        csInf_le
          (sandwichedRenyiQAdditiveValueSet_bddBelow
            hρ₂ hσ₂.posSemidef hα_nonneg hα_le_one)
          (sandwichedRenyiQAdditiveValueSet_mem hH α)
      simpa [Q₂, hQ₂] using hsInf_le
    have hlinear :
        t * Q₁ + (1 - t) * Q₂ ≤
          t * frankLiebAdditiveObjective ρ₁ σ₁ H α ((1 - α) / α) +
            (1 - t) * frankLiebAdditiveObjective ρ₂ σ₂ H α ((1 - α) / α) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hQ₁_le ht0)
        (mul_le_mul_of_nonneg_left hQ₂_le (sub_nonneg.mpr ht1))
    have hconc :
        t * frankLiebAdditiveObjective ρ₁ σ₁ H α ((1 - α) / α) +
            (1 - t) * frankLiebAdditiveObjective ρ₂ σ₂ H α ((1 - α) / α) ≤
          frankLiebAdditiveObjective ρt σt H α ((1 - α) / α) := by
      simpa [ρt, σt] using
        frankLiebAdditiveObjective_concave
          (a := a) (H := H) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (σ₁ := σ₁) (σ₂ := σ₂)
          hH hσ₁.posSemidef hσ₂.posSemidef
          (le_of_lt hα_lt_one)
          (sandwichedRenyiQ_frankLiebExponent_pos hα_half hα_lt_one)
          (sandwichedRenyiQ_frankLiebExponent_lt_one hα_half hα_lt_one)
          ht0 ht1
    exact hlinear.trans hconc
  have hle_sInf :
      t * Q₁ + (1 - t) * Q₂ ≤
        sInf (sandwichedRenyiQAdditiveValueSet ρt σt α) :=
    le_csInf (sandwichedRenyiQAdditiveValueSet_nonempty ρt σt α) hlower
  have hQt' :
      sInf (sandwichedRenyiQAdditiveValueSet ρt σt α) =
        sandwichedRenyiQ ρt σt hρt hσt_psd α := by
    simpa [ρt, σt, hρt, hσt_psd] using hQt
  calc
    t * sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁.posSemidef α +
        (1 - t) * sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂.posSemidef α =
        t * Q₁ + (1 - t) * Q₂ := rfl
    _ ≤ sInf (sandwichedRenyiQAdditiveValueSet ρt σt α) := hle_sInf
    _ = sandwichedRenyiQ ρt σt hρt hσt_psd α := hQt'
    _ = sandwichedRenyiQ
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂)
        (sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1)
        (sandwichedRenyiQ_sigma_mix_posSemidef hσ₁.posSemidef hσ₂.posSemidef
          ht0 ht1)
        α := by
          simp [ρt, σt]

/-- Handoff from the fixed-weight `sInf` variational formula to joint
concavity of the sandwiched `Q` functional.

This theorem isolates the remaining noncommutative Frank--Lieb variational
gap: once each `sandwichedRenyiQ` value is identified with the infimum over
fixed positive-definite weights, the already proved fixed-weight objective
concavity gives joint concavity of `Q`. -/
theorem sandwichedRenyiQ_jointConcave_lowAlpha_of_fixedWeight_sInf_eq
    [Nonempty a] {ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef)
    {α t : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hQ₁ :
      sInf (sandwichedRenyiQFixedWeightValueSet ρ₁ σ₁ α) =
        sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁.posSemidef α)
    (hQ₂ :
      sInf (sandwichedRenyiQFixedWeightValueSet ρ₂ σ₂ α) =
        sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂.posSemidef α)
    (hQt :
      sInf (sandwichedRenyiQFixedWeightValueSet
          (cMatrixConvexCombination t ρ₁ ρ₂)
          (cMatrixConvexCombination t σ₁ σ₂) α) =
        sandwichedRenyiQ
          (cMatrixConvexCombination t ρ₁ ρ₂)
          (cMatrixConvexCombination t σ₁ σ₂)
          (sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1)
          (sandwichedRenyiQ_sigma_mix_posSemidef hσ₁.posSemidef hσ₂.posSemidef
            ht0 ht1)
          α) :
    t * sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁.posSemidef α +
        (1 - t) * sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂.posSemidef α ≤
      sandwichedRenyiQ
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂)
        (sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1)
        (sandwichedRenyiQ_sigma_mix_posSemidef hσ₁.posSemidef hσ₂.posSemidef
          ht0 ht1)
        α := by
  let ρt : CMatrix a := cMatrixConvexCombination t ρ₁ ρ₂
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  let Q₁ : ℝ := sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁.posSemidef α
  let Q₂ : ℝ := sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂.posSemidef α
  have hρt : ρt.PosSemidef := by
    simpa [ρt] using sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1
  have hσt_psd : σt.PosSemidef := by
    simpa [σt] using
      sandwichedRenyiQ_sigma_mix_posSemidef hσ₁.posSemidef hσ₂.posSemidef
        ht0 ht1
  have hlower :
      t * Q₁ + (1 - t) * Q₂ ∈
        lowerBounds (sandwichedRenyiQFixedWeightValueSet ρt σt α) := by
    intro y hy
    rcases hy with ⟨H, hH, rfl⟩
    have hQ₁_le :
        Q₁ ≤ frankLiebFixedWeightObjective ρ₁ σ₁ H α ((1 - α) / α) := by
      simpa [Q₁, hQ₁] using
        sandwichedRenyiQFixedWeightValueSet_sInf_le_fixedWeight
          hρ₁ hσ₁.posSemidef hH α
    have hQ₂_le :
        Q₂ ≤ frankLiebFixedWeightObjective ρ₂ σ₂ H α ((1 - α) / α) := by
      simpa [Q₂, hQ₂] using
        sandwichedRenyiQFixedWeightValueSet_sInf_le_fixedWeight
          hρ₂ hσ₂.posSemidef hH α
    have hlinear :
        t * Q₁ + (1 - t) * Q₂ ≤
          t * frankLiebFixedWeightObjective ρ₁ σ₁ H α ((1 - α) / α) +
            (1 - t) * frankLiebFixedWeightObjective ρ₂ σ₂ H α ((1 - α) / α) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hQ₁_le ht0)
        (mul_le_mul_of_nonneg_left hQ₂_le (sub_nonneg.mpr ht1))
    have hconc :
        t * frankLiebFixedWeightObjective ρ₁ σ₁ H α ((1 - α) / α) +
            (1 - t) * frankLiebFixedWeightObjective ρ₂ σ₂ H α ((1 - α) / α) ≤
          frankLiebFixedWeightObjective ρt σt H α ((1 - α) / α) := by
      simpa [ρt, σt] using
        frankLiebFixedWeightObjective_concave_strictLowAlpha
          (a := a) (H := H) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (σ₁ := σ₁) (σ₂ := σ₂)
          hH hρ₁ hρ₂ hσ₁ hσ₂ hα_half hα_lt_one ht0 ht1
    exact hlinear.trans hconc
  have hle_sInf :
      t * Q₁ + (1 - t) * Q₂ ≤
        sInf (sandwichedRenyiQFixedWeightValueSet ρt σt α) :=
    le_csInf (sandwichedRenyiQFixedWeightValueSet_nonempty ρt σt α) hlower
  have hQt' :
      sInf (sandwichedRenyiQFixedWeightValueSet ρt σt α) =
        sandwichedRenyiQ ρt σt hρt hσt_psd α := by
    simpa [ρt, σt, hρt, hσt_psd] using hQt
  calc
    t * sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁.posSemidef α +
        (1 - t) * sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂.posSemidef α =
        t * Q₁ + (1 - t) * Q₂ := rfl
    _ ≤ sInf (sandwichedRenyiQFixedWeightValueSet ρt σt α) := hle_sInf
    _ = sandwichedRenyiQ ρt σt hρt hσt_psd α := hQt'
    _ = sandwichedRenyiQ
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂)
        (sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1)
        (sandwichedRenyiQ_sigma_mix_posSemidef hσ₁.posSemidef hσ₂.posSemidef
          ht0 ht1)
        α := by
          simp [ρt, σt]

/-- Positive-definite Frank--Lieb low-`α` joint concavity for the
PSD-friendly sandwiched Rényi `Q` functional.

This is the full-rank specialization of Frank--Lieb Proposition 3 needed for
the `α < 1` branch: it combines the Gour/Young variational formula with the
already proved fixed-weight Frank--Lieb objective concavity. -/
theorem sandwichedRenyiQ_jointConcave_lowAlpha_posDef
    [Nonempty a] {ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hρ₁ : ρ₁.PosDef) (hρ₂ : ρ₂.PosDef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef)
    {α t : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * sandwichedRenyiQ ρ₁ σ₁ hρ₁.posSemidef hσ₁.posSemidef α +
        (1 - t) * sandwichedRenyiQ ρ₂ σ₂ hρ₂.posSemidef hσ₂.posSemidef α ≤
      sandwichedRenyiQ
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂)
        (sandwichedRenyiQ_rho_mix_posSemidef hρ₁.posSemidef hρ₂.posSemidef
          ht0 ht1)
        (sandwichedRenyiQ_sigma_mix_posSemidef hσ₁.posSemidef hσ₂.posSemidef
          ht0 ht1)
        α := by
  let ρt : CMatrix a := cMatrixConvexCombination t ρ₁ ρ₂
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  have hρt : ρt.PosDef := by
    simpa [ρt] using cMatrixConvexCombination_posDef hρ₁ hρ₂ ht0 ht1
  have hσt : σt.PosDef := by
    simpa [σt] using cMatrixConvexCombination_posDef hσ₁ hσ₂ ht0 ht1
  have hQ₁ :
      sInf (sandwichedRenyiQFixedWeightValueSet ρ₁ σ₁ α) =
        sandwichedRenyiQ ρ₁ σ₁ hρ₁.posSemidef hσ₁.posSemidef α :=
    sandwichedRenyiQFixedWeightValueSet_sInf_eq_sandwichedRenyiQ_posDef
      hρ₁ hσ₁ hα_half hα_lt_one
  have hQ₂ :
      sInf (sandwichedRenyiQFixedWeightValueSet ρ₂ σ₂ α) =
        sandwichedRenyiQ ρ₂ σ₂ hρ₂.posSemidef hσ₂.posSemidef α :=
    sandwichedRenyiQFixedWeightValueSet_sInf_eq_sandwichedRenyiQ_posDef
      hρ₂ hσ₂ hα_half hα_lt_one
  have hQt :
      sInf (sandwichedRenyiQFixedWeightValueSet ρt σt α) =
        sandwichedRenyiQ ρt σt hρt.posSemidef hσt.posSemidef α :=
    sandwichedRenyiQFixedWeightValueSet_sInf_eq_sandwichedRenyiQ_posDef
      hρt hσt hα_half hα_lt_one
  simpa [ρt, σt] using
    sandwichedRenyiQ_jointConcave_lowAlpha_of_fixedWeight_sInf_eq
      (a := a) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (σ₁ := σ₁) (σ₂ := σ₂)
      hρ₁.posSemidef hρ₂.posSemidef hσ₁ hσ₂
      hα_half hα_lt_one ht0 ht1 hQ₁ hQ₂ hQt

/-- Frank--Lieb low-`α` joint concavity for the PSD-friendly sandwiched Rényi
`Q` functional on unrestricted PSD inputs.

This is the PSD closure of `sandwichedRenyiQ_jointConcave_lowAlpha_posDef`,
obtained by identity regularization and continuity of the positive matrix
powers appearing in Gour's `Q_α` expression. -/
theorem sandwichedRenyiQ_jointConcave_lowAlpha
    [Nonempty a] {ρ₁ ρ₂ σ₁ σ₂ : CMatrix a}
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef)
    (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    {α t : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁ α +
        (1 - t) * sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂ α ≤
      sandwichedRenyiQ
        (cMatrixConvexCombination t ρ₁ ρ₂)
        (cMatrixConvexCombination t σ₁ σ₂)
        (sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1)
        (sandwichedRenyiQ_sigma_mix_posSemidef hσ₁ hσ₂ ht0 ht1)
        α := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let ρ₁ε : ℝ → CMatrix a := fun ε => cMatrixPSDRegularization ρ₁ ε
  let ρ₂ε : ℝ → CMatrix a := fun ε => cMatrixPSDRegularization ρ₂ ε
  let σ₁ε : ℝ → CMatrix a := fun ε => cMatrixPSDRegularization σ₁ ε
  let σ₂ε : ℝ → CMatrix a := fun ε => cMatrixPSDRegularization σ₂ ε
  let ρt : CMatrix a := cMatrixConvexCombination t ρ₁ ρ₂
  let σt : CMatrix a := cMatrixConvexCombination t σ₁ σ₂
  let ρtε : ℝ → CMatrix a :=
    fun ε => cMatrixConvexCombination t (ρ₁ε ε) (ρ₂ε ε)
  let σtε : ℝ → CMatrix a :=
    fun ε => cMatrixConvexCombination t (σ₁ε ε) (σ₂ε ε)
  have hα_pos : 0 < α := by linarith
  have hs_pos : 0 < (1 - α) / (2 * α) := by
    exact div_pos (sub_pos.mpr hα_lt_one) (mul_pos (by norm_num) hα_pos)
  have hρ₁ε_psd : ∀ ε, (ρ₁ε ε).PosSemidef := by
    intro ε
    exact cMatrixPSDRegularization_posSemidef hρ₁ ε
  have hρ₂ε_psd : ∀ ε, (ρ₂ε ε).PosSemidef := by
    intro ε
    exact cMatrixPSDRegularization_posSemidef hρ₂ ε
  have hσ₁ε_psd : ∀ ε, (σ₁ε ε).PosSemidef := by
    intro ε
    exact cMatrixPSDRegularization_posSemidef hσ₁ ε
  have hσ₂ε_psd : ∀ ε, (σ₂ε ε).PosSemidef := by
    intro ε
    exact cMatrixPSDRegularization_posSemidef hσ₂ ε
  have hρt_psd : ρt.PosSemidef := by
    simpa [ρt] using sandwichedRenyiQ_rho_mix_posSemidef hρ₁ hρ₂ ht0 ht1
  have hσt_psd : σt.PosSemidef := by
    simpa [σt] using sandwichedRenyiQ_sigma_mix_posSemidef hσ₁ hσ₂ ht0 ht1
  have hρtε_psd : ∀ ε, (ρtε ε).PosSemidef := by
    intro ε
    exact cMatrixConvexCombination_posSemidef
      (hρ₁ε_psd ε) (hρ₂ε_psd ε) ht0 ht1
  have hσtε_psd : ∀ ε, (σtε ε).PosSemidef := by
    intro ε
    exact cMatrixConvexCombination_posSemidef
      (hσ₁ε_psd ε) (hσ₂ε_psd ε) ht0 ht1
  have hρ₁ε_tend : Filter.Tendsto ρ₁ε l (nhds ρ₁) := by
    simpa [ρ₁ε, l] using cMatrixPSDRegularization_tendsto_zero ρ₁
  have hρ₂ε_tend : Filter.Tendsto ρ₂ε l (nhds ρ₂) := by
    simpa [ρ₂ε, l] using cMatrixPSDRegularization_tendsto_zero ρ₂
  have hσ₁ε_tend : Filter.Tendsto σ₁ε l (nhds σ₁) := by
    simpa [σ₁ε, l] using cMatrixPSDRegularization_tendsto_zero σ₁
  have hσ₂ε_tend : Filter.Tendsto σ₂ε l (nhds σ₂) := by
    simpa [σ₂ε, l] using cMatrixPSDRegularization_tendsto_zero σ₂
  have hρtε_tend : Filter.Tendsto ρtε l (nhds ρt) := by
    have htend :
        Filter.Tendsto
          (fun ε => ((t : ℂ) • ρ₁ε ε) +
            (((1 - t : ℝ) : ℂ) • ρ₂ε ε))
          l
          (nhds (((t : ℂ) • ρ₁) + (((1 - t : ℝ) : ℂ) • ρ₂))) :=
      (hρ₁ε_tend.const_smul (t : ℂ)).add
        (hρ₂ε_tend.const_smul (((1 - t : ℝ) : ℂ)))
    simpa [ρtε, ρt, cMatrixConvexCombination] using htend
  have hσtε_tend : Filter.Tendsto σtε l (nhds σt) := by
    have htend :
        Filter.Tendsto
          (fun ε => ((t : ℂ) • σ₁ε ε) +
            (((1 - t : ℝ) : ℂ) • σ₂ε ε))
          l
          (nhds (((t : ℂ) • σ₁) + (((1 - t : ℝ) : ℂ) • σ₂))) :=
      (hσ₁ε_tend.const_smul (t : ℂ)).add
        (hσ₂ε_tend.const_smul (((1 - t : ℝ) : ℂ)))
    simpa [σtε, σt, cMatrixConvexCombination] using htend
  have hQ₁_tend :
      Filter.Tendsto
        (fun ε => sandwichedRenyiQ (ρ₁ε ε) (σ₁ε ε)
          (hρ₁ε_psd ε) (hσ₁ε_psd ε) α)
        l (nhds (sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁ α)) :=
    sandwichedRenyiQ_tendsto_of_tendsto_posSemidef
      hα_pos hs_pos hρ₁ε_tend hσ₁ε_tend
      hρ₁ε_psd hσ₁ε_psd hρ₁ hσ₁
  have hQ₂_tend :
      Filter.Tendsto
        (fun ε => sandwichedRenyiQ (ρ₂ε ε) (σ₂ε ε)
          (hρ₂ε_psd ε) (hσ₂ε_psd ε) α)
        l (nhds (sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂ α)) :=
    sandwichedRenyiQ_tendsto_of_tendsto_posSemidef
      hα_pos hs_pos hρ₂ε_tend hσ₂ε_tend
      hρ₂ε_psd hσ₂ε_psd hρ₂ hσ₂
  have hQt_tend :
      Filter.Tendsto
        (fun ε => sandwichedRenyiQ (ρtε ε) (σtε ε)
          (hρtε_psd ε) (hσtε_psd ε) α)
        l (nhds (sandwichedRenyiQ ρt σt hρt_psd hσt_psd α)) :=
    sandwichedRenyiQ_tendsto_of_tendsto_posSemidef
      hα_pos hs_pos hρtε_tend hσtε_tend
      hρtε_psd hσtε_psd hρt_psd hσt_psd
  have hleft :
      Filter.Tendsto
        (fun ε =>
          t * sandwichedRenyiQ (ρ₁ε ε) (σ₁ε ε)
              (hρ₁ε_psd ε) (hσ₁ε_psd ε) α +
            (1 - t) * sandwichedRenyiQ (ρ₂ε ε) (σ₂ε ε)
              (hρ₂ε_psd ε) (hσ₂ε_psd ε) α)
        l
        (nhds
          (t * sandwichedRenyiQ ρ₁ σ₁ hρ₁ hσ₁ α +
            (1 - t) * sandwichedRenyiQ ρ₂ σ₂ hρ₂ hσ₂ α)) :=
    (hQ₁_tend.const_mul t).add (hQ₂_tend.const_mul (1 - t))
  have hineq_eventual :
      (fun ε =>
          t * sandwichedRenyiQ (ρ₁ε ε) (σ₁ε ε)
              (hρ₁ε_psd ε) (hσ₁ε_psd ε) α +
            (1 - t) * sandwichedRenyiQ (ρ₂ε ε) (σ₂ε ε)
              (hρ₂ε_psd ε) (hσ₂ε_psd ε) α)
        ≤ᶠ[l]
      (fun ε => sandwichedRenyiQ (ρtε ε) (σtε ε)
          (hρtε_psd ε) (hσtε_psd ε) α) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hρ₁ε_pd : (ρ₁ε ε).PosDef := by
      simpa [ρ₁ε] using cMatrixPSDRegularization_posDef_of_pos hρ₁ hε
    have hρ₂ε_pd : (ρ₂ε ε).PosDef := by
      simpa [ρ₂ε] using cMatrixPSDRegularization_posDef_of_pos hρ₂ hε
    have hσ₁ε_pd : (σ₁ε ε).PosDef := by
      simpa [σ₁ε] using cMatrixPSDRegularization_posDef_of_pos hσ₁ hε
    have hσ₂ε_pd : (σ₂ε ε).PosDef := by
      simpa [σ₂ε] using cMatrixPSDRegularization_posDef_of_pos hσ₂ hε
    simpa [ρtε, σtε] using
      sandwichedRenyiQ_jointConcave_lowAlpha_posDef
        (a := a) (ρ₁ := ρ₁ε ε) (ρ₂ := ρ₂ε ε)
        (σ₁ := σ₁ε ε) (σ₂ := σ₂ε ε)
        hρ₁ε_pd hρ₂ε_pd hσ₁ε_pd hσ₂ε_pd
        hα_half hα_lt_one ht0 ht1
  have hlimit := le_of_tendsto_of_tendsto hleft hQt_tend hineq_eventual
  simpa [ρt, σt] using hlimit

/-- Package the PSD witnesses for `sandwichedRenyiQ` into a pair-valued
function.  The `if` keeps the function total on the ambient matrix product
space so that Mathlib's `ConcaveOn.le_map_sum` can be reused for finite
twirling averages. -/
noncomputable def sandwichedRenyiQPair (α : ℝ)
    (p : CMatrix a × CMatrix a) : ℝ := by
  classical
  exact
    if hp : p.1.PosSemidef ∧ p.2.PosSemidef then
      sandwichedRenyiQ p.1 p.2 hp.1 hp.2 α
    else
      0

theorem sandwichedRenyiQPair_eq {ρ σ : CMatrix a}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (α : ℝ) :
    sandwichedRenyiQPair (a := a) α (ρ, σ) =
      sandwichedRenyiQ ρ σ hρ hσ α := by
  classical
  simp [sandwichedRenyiQPair, hρ, hσ]

/-- Congruence for the PSD-friendly `Q` functional under equality of its two
matrix arguments.  This small helper keeps dependent PSD witnesses out of
larger rewrites such as finite twirling identities. -/
theorem sandwichedRenyiQ_congr
    {ρ ρ' σ σ' : CMatrix a}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hρ' : ρ'.PosSemidef) (hσ' : σ'.PosSemidef)
    (hρeq : ρ = ρ') (hσeq : σ = σ') (α : ℝ) :
    sandwichedRenyiQ ρ σ hρ hσ α =
      sandwichedRenyiQ ρ' σ' hρ' hσ' α := by
  subst ρ'
  subst σ'
  rfl

/-- The PSD domain for the pair-valued `Q` functional. -/
def sandwichedRenyiQPSDDomain : Set (CMatrix a × CMatrix a) :=
  {p | p.1.PosSemidef ∧ p.2.PosSemidef}

omit [Fintype a] [DecidableEq a] in
theorem sandwichedRenyiQPSDDomain_convex :
    Convex ℝ (sandwichedRenyiQPSDDomain (a := a)) := by
  intro x hx y hy s t hs ht hst
  constructor
  · have hρ :
        (s • x.1 + t • y.1 : CMatrix a).PosSemidef :=
      Matrix.PosSemidef.add
        (Matrix.PosSemidef.smul hx.1 hs)
        (Matrix.PosSemidef.smul hy.1 ht)
    simpa [sandwichedRenyiQPSDDomain] using hρ
  · have hσ :
        (s • x.2 + t • y.2 : CMatrix a).PosSemidef :=
      Matrix.PosSemidef.add
        (Matrix.PosSemidef.smul hx.2 hs)
        (Matrix.PosSemidef.smul hy.2 ht)
    simpa [sandwichedRenyiQPSDDomain] using hσ

/-- Frank--Lieb joint concavity as a `ConcaveOn` theorem on the PSD pair cone.

This is a Mathlib-facing wrapper around the source-shaped binary theorem
`sandwichedRenyiQ_jointConcave_lowAlpha`; it is used only to derive finite
average Jensen inequalities for local-unitary twirling. -/
theorem sandwichedRenyiQPair_concaveOn_lowAlpha
    [Nonempty a] {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    ConcaveOn ℝ (sandwichedRenyiQPSDDomain (a := a))
      (sandwichedRenyiQPair (a := a) α) := by
  refine ⟨sandwichedRenyiQPSDDomain_convex (a := a), ?_⟩
  intro x hx y hy s t hs ht hst
  have ht_eq : t = 1 - s := by linarith
  subst t
  have hs_le : s ≤ 1 := by linarith
  have hmixρ :
      (s • x.1 + (1 - s) • y.1 : CMatrix a).PosSemidef :=
    Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hx.1 hs)
      (Matrix.PosSemidef.smul hy.1 (sub_nonneg.mpr hs_le))
  have hmixσ :
      (s • x.2 + (1 - s) • y.2 : CMatrix a).PosSemidef :=
    Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hx.2 hs)
      (Matrix.PosSemidef.smul hy.2 (sub_nonneg.mpr hs_le))
  have hconc :=
    sandwichedRenyiQ_jointConcave_lowAlpha
      (a := a) (ρ₁ := x.1) (ρ₂ := y.1) (σ₁ := x.2) (σ₂ := y.2)
      hx.1 hy.1 hx.2 hy.2 hα_half hα_lt_one hs hs_le
  simpa [sandwichedRenyiQPair, sandwichedRenyiQPSDDomain, hx.1, hx.2,
    hy.1, hy.2, hmixρ, hmixσ, cMatrixConvexCombination_eq_real_smul,
    smul_eq_mul, Complex.real_smul, add_comm, add_left_comm, add_assoc] using hconc

omit [Fintype a] [DecidableEq a] in
theorem cMatrix_finset_weightedSum_posSemidef
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (A : ι → CMatrix a)
    (hA : ∀ i ∈ s, (A i).PosSemidef)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, (w i : ℂ) • A i).PosSemidef := by
  classical
  revert hA hw_nonneg
  refine Finset.induction_on s ?_ ?_
  · simpa using (Matrix.PosSemidef.zero : (0 : CMatrix a).PosSemidef)
  · intro i s his hsind hA hw_nonneg
    rw [Finset.sum_insert his]
    have hwi : (0 : ℂ) ≤ (w i : ℂ) := by
      exact_mod_cast hw_nonneg i (Finset.mem_insert_self i s)
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul (hA i (Finset.mem_insert_self i s))
        hwi)
      (hsind
        (fun j hj => hA j (Finset.mem_insert_of_mem hj))
        (fun j hj => hw_nonneg j (Finset.mem_insert_of_mem hj)))

omit [Fintype a] [DecidableEq a] in
theorem finset_weightedPair_sum_fst
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (ρ σ : ι → CMatrix a) :
    (∑ i ∈ s, w i • ((ρ i, σ i) : CMatrix a × CMatrix a)).1 =
      ∑ i ∈ s, (w i : ℂ) • ρ i := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp
  | insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his]
      rw [Prod.fst_add, Prod.smul_fst, ih]
      change w i • ρ i + (∑ x ∈ s, (w x : ℂ) • ρ x) =
        (w i : ℂ) • ρ i + ∑ x ∈ s, (w x : ℂ) • ρ x
      simp

omit [Fintype a] [DecidableEq a] in
theorem finset_weightedPair_sum_snd
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (ρ σ : ι → CMatrix a) :
    (∑ i ∈ s, w i • ((ρ i, σ i) : CMatrix a × CMatrix a)).2 =
      ∑ i ∈ s, (w i : ℂ) • σ i := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp
  | insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his]
      rw [Prod.snd_add, Prod.smul_snd, ih]
      change w i • σ i + (∑ x ∈ s, (w x : ℂ) • σ x) =
        (w i : ℂ) • σ i + ∑ x ∈ s, (w x : ℂ) • σ x
      simp

/-- Finite Jensen inequality for the low-`α` `Q` functional on PSD matrix
pairs.  This is the exact finite-average bridge needed before applying local
unitary twirling; the proof is just `ConcaveOn.le_map_sum` applied to the
Gour/Frank--Lieb joint concavity theorem. -/
theorem sandwichedRenyiQ_finset_weightedAverage_ge_average_lowAlpha
    [Nonempty a] {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (ρ σ : ι → CMatrix a)
    (hρ : ∀ i ∈ s, (ρ i).PosSemidef)
    (hσ : ∀ i ∈ s, (σ i).PosSemidef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1) :
    ∑ i ∈ s, w i *
        sandwichedRenyiQPair (a := a) α (ρ i, σ i) ≤
      sandwichedRenyiQ
        (∑ i ∈ s, (w i : ℂ) • ρ i)
        (∑ i ∈ s, (w i : ℂ) • σ i)
        (cMatrix_finset_weightedSum_posSemidef s w ρ hρ hw_nonneg)
        (cMatrix_finset_weightedSum_posSemidef s w σ hσ hw_nonneg)
        α := by
  classical
  let p : ι → CMatrix a × CMatrix a := fun i => (ρ i, σ i)
  have hmem : ∀ i ∈ s, p i ∈ sandwichedRenyiQPSDDomain (a := a) := by
    intro i hi
    exact ⟨hρ i hi, hσ i hi⟩
  have hjensen :=
    (sandwichedRenyiQPair_concaveOn_lowAlpha
      (a := a) hα_half hα_lt_one).le_map_sum
      (t := s) (w := w) (p := p) hw_nonneg hw_sum hmem
  have hsum_fst :
      (∑ i ∈ s, w i • p i).1 = ∑ i ∈ s, (w i : ℂ) • ρ i := by
    simpa [p] using finset_weightedPair_sum_fst (a := a) s w ρ σ
  have hsum_snd :
      (∑ i ∈ s, w i • p i).2 = ∑ i ∈ s, (w i : ℂ) • σ i := by
    simpa [p] using finset_weightedPair_sum_snd (a := a) s w ρ σ
  have hsum_mem :
      (∑ i ∈ s, w i • p i) ∈ sandwichedRenyiQPSDDomain (a := a) := by
    constructor
    · rw [hsum_fst]
      exact
        cMatrix_finset_weightedSum_posSemidef s w ρ hρ hw_nonneg
    · rw [hsum_snd]
      exact
        cMatrix_finset_weightedSum_posSemidef s w σ hσ hw_nonneg
  have hright :
      sandwichedRenyiQPair (a := a) α (∑ i ∈ s, w i • p i) =
        sandwichedRenyiQ
          (∑ i ∈ s, (w i : ℂ) • ρ i)
          (∑ i ∈ s, (w i : ℂ) • σ i)
          (cMatrix_finset_weightedSum_posSemidef s w ρ hρ hw_nonneg)
          (cMatrix_finset_weightedSum_posSemidef s w σ hσ hw_nonneg)
          α := by
    rw [sandwichedRenyiQPair_eq hsum_mem.1 hsum_mem.2]
    unfold sandwichedRenyiQ
    rw [hsum_fst, hsum_snd]
  simpa [p, hright, smul_eq_mul]
    using (by simpa [hright, smul_eq_mul] using hjensen)

/-- Finite local-right-unitary averaging lower bound for the low-`α`
`Q` functional.

This is the Frank--Lieb/Jensen part of the local twirling route.  It does not
use partial trace monotonicity: after applying finite Jensen, every summand is
identified with the original `Q(ρ,σ)` by local-right-unitary invariance. -/
theorem sandwichedRenyiQ_localRightUnitary_weightedAverage_ge
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a] [Nonempty b]
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (U : ι → Matrix.unitaryGroup b ℂ)
    {ρ σ : CMatrix (Prod a b)}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1) :
    sandwichedRenyiQ ρ σ hρ hσ α ≤
      sandwichedRenyiQ
        (∑ i ∈ s, (w i : ℂ) •
          ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
            star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b))))
        (∑ i ∈ s, (w i : ℂ) •
          ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
            star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b))))
        (cMatrix_finset_weightedSum_posSemidef s w
          (fun i =>
            (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
              star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))
          (by
            intro i _
            simpa using
              posSemidef_unitary_conj hρ (localRightUnitary (a := a) (U i))⁻¹)
          hw_nonneg)
        (cMatrix_finset_weightedSum_posSemidef s w
          (fun i =>
            (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
              star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))
          (by
            intro i _
            simpa using
              posSemidef_unitary_conj hσ (localRightUnitary (a := a) (U i))⁻¹)
          hw_nonneg)
        α := by
  classical
  let ρU : ι → CMatrix (Prod a b) := fun i =>
    (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
      star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b))
  let σU : ι → CMatrix (Prod a b) := fun i =>
    (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
      star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b))
  have hρU : ∀ i ∈ s, (ρU i).PosSemidef := by
    intro i hi
    simpa [ρU] using
      posSemidef_unitary_conj hρ (localRightUnitary (a := a) (U i))⁻¹
  have hσU : ∀ i ∈ s, (σU i).PosSemidef := by
    intro i hi
    simpa [σU] using
      posSemidef_unitary_conj hσ (localRightUnitary (a := a) (U i))⁻¹
  have hα_pos : 0 < α := by linarith
  have hα_nonneg : 0 ≤ α := le_of_lt hα_pos
  have hs_nonneg : 0 ≤ (1 - α) / (2 * α) := by
    have hnum : 0 ≤ 1 - α := le_of_lt (sub_pos.mpr hα_lt_one)
    have hden : 0 ≤ 2 * α := by positivity
    exact div_nonneg hnum hden
  have hterm :
      ∀ i ∈ s,
        sandwichedRenyiQPair (a := Prod a b) α (ρU i, σU i) =
          sandwichedRenyiQ ρ σ hρ hσ α := by
    intro i hi
    calc
      sandwichedRenyiQPair (a := Prod a b) α (ρU i, σU i) =
          sandwichedRenyiQ (ρU i) (σU i) (hρU i hi) (hσU i hi) α := by
            rw [sandwichedRenyiQPair_eq]
      _ = sandwichedRenyiQ ρ σ hρ hσ α := by
            simpa [ρU, σU] using
              sandwichedRenyiQ_localRightUnitary_conj hρ hσ (U i) α
                hs_nonneg hα_nonneg
  have havg :
      ∑ i ∈ s, w i * sandwichedRenyiQPair (a := Prod a b) α (ρU i, σU i) =
        sandwichedRenyiQ ρ σ hρ hσ α := by
    calc
      ∑ i ∈ s, w i * sandwichedRenyiQPair (a := Prod a b) α (ρU i, σU i) =
          (∑ i ∈ s, w i) * sandwichedRenyiQ ρ σ hρ hσ α := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl (by
              intro i hi
              rw [hterm i hi])
      _ = sandwichedRenyiQ ρ σ hρ hσ α := by
            rw [hw_sum, one_mul]
  have hjensen :=
    sandwichedRenyiQ_finset_weightedAverage_ge_average_lowAlpha
      (a := Prod a b) s w ρU σU hρU hσU hα_half hα_lt_one
      hw_nonneg hw_sum
  calc
    sandwichedRenyiQ ρ σ hρ hσ α =
        ∑ i ∈ s, w i * sandwichedRenyiQPair (a := Prod a b) α (ρU i, σU i) := havg.symm
    _ ≤ sandwichedRenyiQ
        (∑ i ∈ s, (w i : ℂ) • ρU i)
        (∑ i ∈ s, (w i : ℂ) • σU i)
        (cMatrix_finset_weightedSum_posSemidef s w ρU hρU hw_nonneg)
        (cMatrix_finset_weightedSum_posSemidef s w σU hσU hw_nonneg)
        α := hjensen
    _ = sandwichedRenyiQ
        (∑ i ∈ s, (w i : ℂ) •
          ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
            star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b))))
        (∑ i ∈ s, (w i : ℂ) •
          ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
            star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b))))
        (cMatrix_finset_weightedSum_posSemidef s w
          (fun i =>
            (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
              star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))
          (by
            intro i hi
            simpa using
              posSemidef_unitary_conj hρ (localRightUnitary (a := a) (U i))⁻¹)
          hw_nonneg)
        (cMatrix_finset_weightedSum_posSemidef s w
          (fun i =>
            (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
              star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))
          (by
            intro i hi
            simpa using
              posSemidef_unitary_conj hσ (localRightUnitary (a := a) (U i))⁻¹)
          hw_nonneg)
        α := by
          simp [ρU, σU]

/-- If a finite local-right-unitary ensemble realizes the partial-trace
depolarizing twirl, then Frank--Lieb joint concavity gives the low-`α`
partial-trace monotonicity for the PSD-friendly `Q` functional.

This theorem isolates the remaining finite-design input in the Gour/Frank--Lieb
route.  The hypotheses `hTwirlρ` and `hTwirlσ` are exactly the local twirling
identity
`Twirl_B(X) = Tr_B(X) ⊗ π_B`; no DPI or partial-trace monotonicity is assumed. -/
theorem sandwichedRenyiQ_marginalA_ge_of_localRightUnitary_twirling
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty a] [Nonempty b]
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (U : ι → Matrix.unitaryGroup b ℂ)
    {ρ σ : CMatrix (Prod a b)}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (hTwirlρ :
      (∑ i ∈ s, (w i : ℂ) •
        ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
          star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))) =
        Matrix.kronecker (partialTraceB ρ) (maximallyMixed b).matrix)
    (hTwirlσ :
      (∑ i ∈ s, (w i : ℂ) •
        ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
          star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))) =
        Matrix.kronecker (partialTraceB σ) (maximallyMixed b).matrix) :
    sandwichedRenyiQ ρ σ hρ hσ α ≤
      sandwichedRenyiQ
        (partialTraceB ρ) (partialTraceB σ)
        (partialTraceB_posSemidef hρ)
        (partialTraceB_posSemidef hσ)
        α := by
  classical
  have htwirl :=
    sandwichedRenyiQ_localRightUnitary_weightedAverage_ge
      (a := a) (b := b) s w U hρ hσ hα_half hα_lt_one
      hw_nonneg hw_sum
  have hsum_tensor :
      sandwichedRenyiQ
        (∑ i ∈ s, (w i : ℂ) •
          ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
            star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b))))
        (∑ i ∈ s, (w i : ℂ) •
          ((localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
            star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b))))
        (cMatrix_finset_weightedSum_posSemidef s w
          (fun i =>
            (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
              star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))
          (by
            intro i hi
            simpa using
              posSemidef_unitary_conj hρ (localRightUnitary (a := a) (U i))⁻¹)
          hw_nonneg)
        (cMatrix_finset_weightedSum_posSemidef s w
          (fun i =>
            (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
              star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))
          (by
            intro i hi
            simpa using
              posSemidef_unitary_conj hσ (localRightUnitary (a := a) (U i))⁻¹)
          hw_nonneg)
        α =
      sandwichedRenyiQ
        (Matrix.kronecker (partialTraceB ρ) (maximallyMixed b).matrix)
        (Matrix.kronecker (partialTraceB σ) (maximallyMixed b).matrix)
        ((partialTraceB_posSemidef hρ).kronecker (maximallyMixed b).pos)
        ((partialTraceB_posSemidef hσ).kronecker (maximallyMixed b).pos)
        α :=
    sandwichedRenyiQ_congr
      (cMatrix_finset_weightedSum_posSemidef s w
        (fun i =>
          (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * ρ *
            star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))
        (by
          intro i hi
          simpa using
            posSemidef_unitary_conj hρ (localRightUnitary (a := a) (U i))⁻¹)
        hw_nonneg)
      (cMatrix_finset_weightedSum_posSemidef s w
        (fun i =>
          (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)) * σ *
            star (localRightUnitary (a := a) (U i) : CMatrix (Prod a b)))
        (by
          intro i hi
          simpa using
            posSemidef_unitary_conj hσ (localRightUnitary (a := a) (U i))⁻¹)
        hw_nonneg)
      ((partialTraceB_posSemidef hρ).kronecker (maximallyMixed b).pos)
      ((partialTraceB_posSemidef hσ).kronecker (maximallyMixed b).pos)
      hTwirlρ hTwirlσ α
  have htensor :
      sandwichedRenyiQ
        (Matrix.kronecker (partialTraceB ρ) (maximallyMixed b).matrix)
        (Matrix.kronecker (partialTraceB σ) (maximallyMixed b).matrix)
        ((partialTraceB_posSemidef hρ).kronecker (maximallyMixed b).pos)
        ((partialTraceB_posSemidef hσ).kronecker (maximallyMixed b).pos)
        α =
      sandwichedRenyiQ
        (partialTraceB ρ) (partialTraceB σ)
        (partialTraceB_posSemidef hρ)
        (partialTraceB_posSemidef hσ)
        α :=
    sandwichedRenyiQ_kronecker_maximallyMixed_right
      (partialTraceB_posSemidef hρ) (partialTraceB_posSemidef hσ)
      α hα_half hα_lt_one
  exact htwirl.trans_eq (hsum_tensor.trans htensor)

/-- The real signs used for the finite diagonal-sign twirl. -/
def boolSignComplex (x : Bool) : ℂ :=
  if x then -1 else 1

@[simp] theorem boolSignComplex_false : boolSignComplex false = 1 := rfl

@[simp] theorem boolSignComplex_true : boolSignComplex true = -1 := rfl

@[simp] theorem boolSignComplex_not (x : Bool) :
    boolSignComplex (!x) = - boolSignComplex x := by
  cases x <;> simp [boolSignComplex]

@[simp] theorem boolSignComplex_star (x : Bool) :
    star (boolSignComplex x) = boolSignComplex x := by
  cases x <;> simp [boolSignComplex]

@[simp] theorem boolSignComplex_sq (x : Bool) :
    boolSignComplex x * boolSignComplex x = 1 := by
  cases x <;> simp [boolSignComplex]

/-- Diagonal `±1` unitary used to dephase the right tensor factor. -/
def diagonalSignUnitary {b : Type v} [Fintype b] [DecidableEq b]
    (ε : b → Bool) : Matrix.unitaryGroup b ℂ :=
  ⟨Matrix.diagonal fun j => boolSignComplex (ε j), by
    constructor
    · rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal]
      ext j j'
      by_cases h : j = j'
      · subst j'
        simp
      · simp [h]
    · rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal]
      ext j j'
      by_cases h : j = j'
      · subst j'
        simp
      · simp [h]⟩

@[simp] theorem diagonalSignUnitary_coe {b : Type v} [Fintype b] [DecidableEq b]
    (ε : b → Bool) :
    (diagonalSignUnitary ε : CMatrix b) =
      Matrix.diagonal fun j => boolSignComplex (ε j) := rfl

theorem diagonalSignUnitary_conj_apply
    {b : Type v} [Fintype b] [DecidableEq b]
    (ε : b → Bool) (X : CMatrix (Prod a b)) (i i' : a) (j j' : b) :
    (((localRightUnitary (a := a) (diagonalSignUnitary ε) : CMatrix (Prod a b)) *
        X * star (localRightUnitary (a := a) (diagonalSignUnitary ε) :
          CMatrix (Prod a b))) (i, j) (i', j')) =
      boolSignComplex (ε j) * X (i, j) (i', j') * boolSignComplex (ε j') := by
  simp only [localRightUnitary_coe, diagonalSignUnitary_coe, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.diagonal,
    Matrix.of_apply, Matrix.conjTranspose_apply]
  have hinner : ∀ x : Prod a b,
      (∑ y : Prod a b,
        (((if i = y.1 then 1 else 0) *
            if j = y.2 then boolSignComplex (ε j) else 0) * X y x)) =
        boolSignComplex (ε j) * X (i, j) x := by
    intro x
    refine (Finset.sum_eq_single (i, j) ?_ ?_).trans ?_
    · intro y _ hy
      rcases y with ⟨y₁, y₂⟩
      by_cases hjy : j = y₂
      · by_cases hiy : i = y₁
        · exfalso
          apply hy
          exact Prod.ext hiy.symm hjy.symm
        · simp [hjy, hiy]
      · simp [hjy]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
    · simp
  simp_rw [hinner]
  refine (Finset.sum_eq_single (i', j') ?_ ?_).trans ?_
  · intro x _ hx
    rcases x with ⟨x₁, x₂⟩
    by_cases hjx : j' = x₂
    · by_cases hix : i' = x₁
      · exfalso
        apply hx
        exact Prod.ext hix.symm hjx.symm
      · have hix' : x₁ ≠ i' := fun h => hix h.symm
        simp [hjx, hix']
    · simp [hjx]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))
  · simp [mul_assoc]

/-- Flipping one Boolean coordinate negates the corresponding sign. -/
def flipBoolCoordinate {b : Type v} [DecidableEq b] (j : b) :
    (b → Bool) ≃ (b → Bool) where
  toFun ε := Function.update ε j (!(ε j))
  invFun ε := Function.update ε j (!(ε j))
  left_inv ε := by
    funext k
    by_cases hk : k = j
    · subst k
      simp
    · simp [Function.update, hk]
  right_inv ε := by
    funext k
    by_cases hk : k = j
    · subst k
      simp
    · simp [Function.update, hk]

@[simp] theorem flipBoolCoordinate_self {b : Type v} [DecidableEq b]
    (j : b) (ε : b → Bool) :
    flipBoolCoordinate j ε j = !(ε j) := by
  simp [flipBoolCoordinate]

@[simp] theorem flipBoolCoordinate_ne {b : Type v} [DecidableEq b]
    {j k : b} (hjk : k ≠ j) (ε : b → Bool) :
    flipBoolCoordinate j ε k = ε k := by
  simp [flipBoolCoordinate, Function.update, hjk]

theorem boolSignComplex_sum_mul_eq_zero_of_ne
    {b : Type v} [Fintype b] [DecidableEq b] {j j' : b} (hjj' : j ≠ j') :
    (∑ ε : b → Bool, boolSignComplex (ε j) * boolSignComplex (ε j')) = 0 := by
  classical
  let S : ℂ := ∑ ε : b → Bool, boolSignComplex (ε j) * boolSignComplex (ε j')
  have hsum :
      S = -S := by
    calc
      S = ∑ ε : b → Bool,
          boolSignComplex ((flipBoolCoordinate j) ε j) *
            boolSignComplex ((flipBoolCoordinate j) ε j') := by
        dsimp [S]
        exact (Equiv.sum_comp (flipBoolCoordinate j)
          (fun ε : b → Bool => boolSignComplex (ε j) * boolSignComplex (ε j'))).symm
      _ = ∑ ε : b → Bool,
          -(boolSignComplex (ε j) * boolSignComplex (ε j')) := by
        refine Finset.sum_congr rfl ?_
        intro ε _
        have hj' : j' ≠ j := fun h => hjj' h.symm
        simp [hj']
      _ = -S := by
        simp [S, Finset.sum_neg_distrib]
  have htwo : (2 : ℂ) * S = 0 := by
    have hSS : S + S = 0 := by
      exact add_eq_zero_iff_eq_neg.mpr hsum
    calc
      (2 : ℂ) * S = S + S := by ring
      _ = 0 := hSS
  have htwo_ne : (2 : ℂ) ≠ 0 := by norm_num
  exact mul_eq_zero.mp htwo |>.resolve_left htwo_ne

theorem boolSignComplex_sum_mul_eq_card
    {b : Type v} [Fintype b] [DecidableEq b] (j : b) :
    (∑ ε : b → Bool, boolSignComplex (ε j) * boolSignComplex (ε j)) =
      (Fintype.card (b → Bool) : ℂ) := by
  simp

/-- The finite diagonal-sign twirl on the right tensor factor.  It removes the
off-diagonal blocks in the right subsystem. -/
def localRightSignTwirl {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) : CMatrix (Prod a b) :=
  ((Fintype.card (b → Bool) : ℂ)⁻¹) •
    ∑ ε : b → Bool,
      (localRightUnitary (a := a) (diagonalSignUnitary ε) : CMatrix (Prod a b)) *
        X * star (localRightUnitary (a := a) (diagonalSignUnitary ε) :
          CMatrix (Prod a b))

theorem localRightSignTwirl_apply {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (i i' : a) (j j' : b) :
    localRightSignTwirl X (i, j) (i', j') =
      if j = j' then X (i, j) (i', j') else 0 := by
  classical
  have hcard : ((Fintype.card (b → Bool) : ℂ)) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (b → Bool) ≠ 0)
  by_cases hjj' : j = j'
  · subst j'
    unfold localRightSignTwirl
    simp only [Matrix.smul_apply, Matrix.sum_apply]
    simp_rw [diagonalSignUnitary_conj_apply]
    have hsumdiag :
        (∑ ε : b → Bool,
          boolSignComplex (ε j) * X (i, j) (i', j) * boolSignComplex (ε j)) =
            (Fintype.card (b → Bool) : ℂ) * X (i, j) (i', j) := by
      calc
        (∑ ε : b → Bool,
          boolSignComplex (ε j) * X (i, j) (i', j) * boolSignComplex (ε j)) =
            (∑ ε : b → Bool, boolSignComplex (ε j) * boolSignComplex (ε j)) *
              X (i, j) (i', j) := by
          simp [mul_left_comm, mul_comm]
        _ = (Fintype.card (b → Bool) : ℂ) * X (i, j) (i', j) := by
          rw [boolSignComplex_sum_mul_eq_card]
    rw [hsumdiag]
    change ((Fintype.card (b → Bool) : ℂ)⁻¹ *
        ((Fintype.card (b → Bool) : ℂ) * X (i, j) (i', j))) =
      X (i, j) (i', j)
    rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
  · have hzero :
        (∑ ε : b → Bool,
          boolSignComplex (ε j) * X (i, j) (i', j') * boolSignComplex (ε j')) = 0 := by
      calc
        (∑ ε : b → Bool,
          boolSignComplex (ε j) * X (i, j) (i', j') * boolSignComplex (ε j')) =
            X (i, j) (i', j') *
              (∑ ε : b → Bool, boolSignComplex (ε j) * boolSignComplex (ε j')) := by
          simp [Finset.mul_sum, mul_assoc, mul_comm]
        _ = 0 := by
          rw [boolSignComplex_sum_mul_eq_zero_of_ne hjj', mul_zero]
    unfold localRightSignTwirl
    simp only [Matrix.smul_apply, Matrix.sum_apply]
    simp_rw [diagonalSignUnitary_conj_apply]
    simp [hjj', hzero]

/-- Permutation unitary for a finite basis permutation.  The convention is
`U e_k = e_{π k}`. -/
def permutationUnitary {b : Type v} [Fintype b] [DecidableEq b]
    (π : Equiv.Perm b) : Matrix.unitaryGroup b ℂ :=
  ⟨fun j k => if π j = k then 1 else 0, by
    constructor
    · ext j j'
      simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply]
      by_cases hjj' : j = j'
      · subst j'
        refine (Finset.sum_eq_single (π.symm j) ?_ ?_).trans ?_
        · intro k _ hk
          by_cases hkj : k = π.symm j
          · exact False.elim (hk hkj)
          · have hne : π k ≠ j := by
              intro h
              apply hkj
              simpa using congrArg π.symm h
            simp [hne]
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ _))
        · simp
      · rw [if_neg hjj']
        refine Finset.sum_eq_zero ?_
        intro k _
        by_cases hkj : k = π.symm j
        · subst k
          simp [hjj']
        · have hne : π k ≠ j := by
            intro h
            apply hkj
            simpa using congrArg π.symm h
          simp [hne]
    · ext j j'
      simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply]
      by_cases hjj' : j = j'
      · subst j'
        refine (Finset.sum_eq_single (π j) ?_ ?_).trans ?_
        · intro k _ hk
          by_cases hkj : k = π j
          · exact False.elim (hk hkj)
          · have hne : π j ≠ k := fun h => hkj h.symm
            simp [hne]
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ _))
        · simp
      · rw [if_neg hjj']
        refine Finset.sum_eq_zero ?_
        intro k _
        by_cases hkj : k = π j
        · subst k
          have hne : ¬π j' = π j := fun h => hjj' (π.injective h.symm)
          simp [hne]
        · have hne : π j ≠ k := fun h => hkj h.symm
          simp [hne]⟩

@[simp] theorem permutationUnitary_coe {b : Type v} [Fintype b] [DecidableEq b]
    (π : Equiv.Perm b) :
    (permutationUnitary π : CMatrix b) = fun j k => if π j = k then 1 else 0 := rfl

theorem permutationUnitary_conj_apply
    {b : Type v} [Fintype b] [DecidableEq b]
    (π : Equiv.Perm b) (X : CMatrix (Prod a b)) (i i' : a) (j j' : b) :
    (((localRightUnitary (a := a) (permutationUnitary π) : CMatrix (Prod a b)) *
        X * star (localRightUnitary (a := a) (permutationUnitary π) :
          CMatrix (Prod a b))) (i, j) (i', j')) =
      X (i, π j) (i', π j') := by
  simp only [localRightUnitary_coe, permutationUnitary_coe, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.conjTranspose_apply]
  have hinner : ∀ x : Prod a b,
      (∑ y : Prod a b,
        (((if i = y.1 then 1 else 0) * if π j = y.2 then 1 else 0) * X y x)) =
        X (i, π j) x := by
    intro x
    refine (Finset.sum_eq_single (i, π j) ?_ ?_).trans ?_
    · intro y _ hy
      rcases y with ⟨y₁, y₂⟩
      by_cases hiy : i = y₁
      · by_cases hjy : π j = y₂
        · exfalso
          apply hy
          exact Prod.ext hiy.symm hjy.symm
        · simp [hiy, hjy]
      · simp [hiy]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
    · simp
  simp_rw [hinner]
  refine (Finset.sum_eq_single (i', π j') ?_ ?_).trans ?_
  · intro x _ hx
    rcases x with ⟨x₁, x₂⟩
    by_cases hix : i' = x₁
    · by_cases hjx : π j' = x₂
      · exfalso
        apply hx
        exact Prod.ext hix.symm hjx.symm
      · simp [hix, hjx]
    · have hix' : x₁ ≠ i' := fun h => hix h.symm
      simp [hix']
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))
  · simp

/-- The permutation group acts transitively on finite-basis labels, so the
orbit sum of a scalar function is independent of the starting label. -/
theorem perm_orbit_sum_eq {b : Type v} [Fintype b] [DecidableEq b]
    (f : b → ℂ) (j k : b) :
    (∑ π : Equiv.Perm b, f (π j)) =
      ∑ π : Equiv.Perm b, f (π k) := by
  classical
  let τ : Equiv.Perm b := Equiv.swap j k
  have h :
      (∑ π : Equiv.Perm b, f ((π * τ) j)) =
        ∑ π : Equiv.Perm b, f (π j) := by
    exact Fintype.sum_equiv
      { toFun := fun π : Equiv.Perm b => π * τ
        invFun := fun π => π * τ⁻¹
        left_inv := by intro π; simp
        right_inv := by intro π; simp }
      (fun π : Equiv.Perm b => f ((π * τ) j))
      (fun π : Equiv.Perm b => f (π j))
      (by intro π; rfl)
  calc
    (∑ π : Equiv.Perm b, f (π j)) =
        ∑ π : Equiv.Perm b, f ((π * τ) j) := h.symm
    _ = ∑ π : Equiv.Perm b, f (π k) := by
      simp [τ]

theorem perm_orbit_sum_card_mul {b : Type v} [Fintype b] [DecidableEq b]
    (f : b → ℂ) (j : b) :
    (Fintype.card b : ℂ) * (∑ π : Equiv.Perm b, f (π j)) =
      (Fintype.card (Equiv.Perm b) : ℂ) * ∑ k : b, f k := by
  classical
  have hconst : ∀ k : b,
      (∑ π : Equiv.Perm b, f (π k)) =
        ∑ π : Equiv.Perm b, f (π j) := by
    intro k
    exact perm_orbit_sum_eq f k j
  calc
    (Fintype.card b : ℂ) * (∑ π : Equiv.Perm b, f (π j)) =
        ∑ k : b, (∑ π : Equiv.Perm b, f (π j)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ k : b, ∑ π : Equiv.Perm b, f (π k) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [hconst k]
    _ = ∑ π : Equiv.Perm b, ∑ k : b, f (π k) := by
      rw [Finset.sum_comm]
    _ = ∑ π : Equiv.Perm b, ∑ k : b, f k := by
      refine Finset.sum_congr rfl ?_
      intro π _
      exact (Equiv.sum_comp π f)
    _ = (Fintype.card (Equiv.Perm b) : ℂ) * ∑ k : b, f k := by
      simp [Finset.sum_const, nsmul_eq_mul]

theorem perm_orbit_average_eq_uniform {b : Type v} [Fintype b] [DecidableEq b]
    (f : b → ℂ) (j : b) :
    (Fintype.card (Equiv.Perm b) : ℂ)⁻¹ *
        (∑ π : Equiv.Perm b, f (π j)) =
      (Fintype.card b : ℂ)⁻¹ * ∑ k : b, f k := by
  classical
  haveI : Nonempty b := ⟨j⟩
  let cB : ℂ := Fintype.card b
  let cP : ℂ := Fintype.card (Equiv.Perm b)
  let A : ℂ := ∑ π : Equiv.Perm b, f (π j)
  let S : ℂ := ∑ k : b, f k
  have hB : cB ≠ 0 := by
    dsimp [cB]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card b ≠ 0)
  have hP : cP ≠ 0 := by
    dsimp [cP]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm b) ≠ 0)
  have hmain : cB * A = cP * S := by
    dsimp [cB, cP, A, S]
    exact perm_orbit_sum_card_mul f j
  have hA : A = cB⁻¹ * (cP * S) := by
    calc
      A = (cB⁻¹ * cB) * A := by rw [inv_mul_cancel₀ hB, one_mul]
      _ = cB⁻¹ * (cB * A) := by rw [mul_assoc]
      _ = cB⁻¹ * (cP * S) := by rw [hmain]
  calc
    cP⁻¹ * A = cP⁻¹ * (cB⁻¹ * (cP * S)) := by rw [hA]
    _ = cB⁻¹ * S := by
      field_simp [hP]

/-- Average over right-subsystem basis permutations. -/
def localRightPermutationTwirl {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) : CMatrix (Prod a b) :=
  ((Fintype.card (Equiv.Perm b) : ℂ)⁻¹) •
    ∑ π : Equiv.Perm b,
      (localRightUnitary (a := a) (permutationUnitary π) : CMatrix (Prod a b)) *
        X * star (localRightUnitary (a := a) (permutationUnitary π) :
          CMatrix (Prod a b))

theorem localRightPermutationTwirl_apply {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (i i' : a) (j j' : b) :
    localRightPermutationTwirl X (i, j) (i', j') =
      (Fintype.card (Equiv.Perm b) : ℂ)⁻¹ *
        ∑ π : Equiv.Perm b, X (i, π j) (i', π j') := by
  unfold localRightPermutationTwirl
  simp only [Matrix.smul_apply, Matrix.sum_apply]
  simp_rw [permutationUnitary_conj_apply]
  rfl

theorem localRightPermutationTwirl_signTwirl_apply
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (i i' : a) (j j' : b) :
    localRightPermutationTwirl (localRightSignTwirl X) (i, j) (i', j') =
      if j = j' then
        (Fintype.card b : ℂ)⁻¹ * ∑ k : b, X (i, k) (i', k)
      else 0 := by
  classical
  rw [localRightPermutationTwirl_apply]
  by_cases hjj' : j = j'
  · subst j'
    have hsum :
        (∑ π : Equiv.Perm b,
          localRightSignTwirl X (i, π j) (i', π j)) =
          ∑ π : Equiv.Perm b, X (i, π j) (i', π j) := by
      refine Finset.sum_congr rfl ?_
      intro π _
      simp [localRightSignTwirl_apply]
    rw [hsum]
    rw [perm_orbit_average_eq_uniform (fun k : b => X (i, k) (i', k)) j]
    simp
  · have hsum :
        (∑ π : Equiv.Perm b,
          localRightSignTwirl X (i, π j) (i', π j')) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro π _
      have hne : π j ≠ π j' := fun h => hjj' (π.injective h)
      simp [localRightSignTwirl_apply, hne]
    rw [hsum, mul_zero]
    simp [hjj']

theorem localRightPermutationTwirl_signTwirl_eq_marginalA_kronecker_maximallyMixed
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty b]
    (X : CMatrix (Prod a b)) :
    localRightPermutationTwirl (localRightSignTwirl X) =
      Matrix.kronecker (partialTraceB X) (maximallyMixed b).matrix := by
  classical
  ext x y
  rcases x with ⟨i, j⟩
  rcases y with ⟨i', j'⟩
  rw [localRightPermutationTwirl_signTwirl_apply]
  have hcast :
      ((((Fintype.card b : ℝ)⁻¹ : ℝ) : ℂ)) =
        (Fintype.card b : ℂ)⁻¹ := by
    have hcardR : (Fintype.card b : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card b ≠ 0)
    norm_num [hcardR]
  by_cases hjj' : j = j'
  · subst j'
    simp [partialTraceB, maximallyMixed_matrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
      hcast, mul_comm]
  · simp [partialTraceB, maximallyMixed_matrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
      hjj']

/-- Local-right unitaries respect multiplication. -/
theorem localRightUnitary_mul {b : Type v} [Fintype b] [DecidableEq b]
    (U V : Matrix.unitaryGroup b ℂ) :
    (localRightUnitary (a := a) (U * V) : CMatrix (Prod a b)) =
      (localRightUnitary (a := a) U : CMatrix (Prod a b)) *
        (localRightUnitary (a := a) V : CMatrix (Prod a b)) := by
  rw [localRightUnitary_coe, localRightUnitary_coe, localRightUnitary_coe]
  change Matrix.kronecker (1 : CMatrix a) ((U * V : Matrix.unitaryGroup b ℂ) : CMatrix b) =
    Matrix.kronecker (1 : CMatrix a) (U : CMatrix b) *
      Matrix.kronecker (1 : CMatrix a) (V : CMatrix b)
  simpa using
    (Matrix.mul_kronecker_mul (1 : CMatrix a) (1 : CMatrix a)
      (U : CMatrix b) (V : CMatrix b))

/-- Entrywise formula for the finite right-unitary family obtained by first
dephasing with a diagonal sign and then permuting the right tensor factor. -/
theorem localRightSignPermutationUnitary_conj_apply
    {b : Type v} [Fintype b] [DecidableEq b]
    (ε : b → Bool) (π : Equiv.Perm b) (X : CMatrix (Prod a b))
    (i i' : a) (j j' : b) :
    (((localRightUnitary (a := a) (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod a b)) *
        X *
        star (localRightUnitary (a := a) (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod a b))) (i, j) (i', j')) =
      boolSignComplex (ε (π j)) * X (i, π j) (i', π j') *
        boolSignComplex (ε (π j')) := by
  classical
  let P : CMatrix (Prod a b) := localRightUnitary (a := a) (permutationUnitary π)
  let D : CMatrix (Prod a b) := localRightUnitary (a := a) (diagonalSignUnitary ε)
  have hmul :
      (localRightUnitary (a := a) (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod a b)) = P * D := by
    simpa [P, D] using
      localRightUnitary_mul (a := a) (U := permutationUnitary π)
        (V := diagonalSignUnitary ε)
  calc
    (((localRightUnitary (a := a) (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod a b)) *
        X *
        star (localRightUnitary (a := a) (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod a b))) (i, j) (i', j')) =
        (P * (D * X * star D) * star P) (i, j) (i', j') := by
          rw [hmul, star_mul]
          simp [P, D, mul_assoc]
    _ = (D * X * star D) (i, π j) (i', π j') := by
          simpa [P] using
            permutationUnitary_conj_apply (a := a) π (D * X * star D) i i' j j'
    _ = boolSignComplex (ε (π j)) * X (i, π j) (i', π j') *
          boolSignComplex (ε (π j')) := by
          simpa [D] using
            diagonalSignUnitary_conj_apply (a := a) ε X i i' (π j) (π j')

/-- The concrete finite local-right-unitary ensemble used in the low-`α`
Gour/Frank--Lieb route realizes the right-subsystem depolarizing twirl.  The
ensemble first applies all diagonal sign flips and then all basis
permutations; its average is `Tr_B(X) ⊗ π_B`. -/
theorem localRightSignPermutationTwirl_eq_marginalA_kronecker_maximallyMixed
    {b : Type v} [Fintype b] [DecidableEq b] [Nonempty b]
    (X : CMatrix (Prod a b)) :
    (∑ idx : (b → Bool) × Equiv.Perm b,
      ((Fintype.card ((b → Bool) × Equiv.Perm b) : ℂ)⁻¹) •
        ((localRightUnitary (a := a)
            (permutationUnitary idx.2 * diagonalSignUnitary idx.1) :
              CMatrix (Prod a b)) *
          X *
          star (localRightUnitary (a := a)
            (permutationUnitary idx.2 * diagonalSignUnitary idx.1) :
              CMatrix (Prod a b)))) =
      Matrix.kronecker (partialTraceB X) (maximallyMixed b).matrix := by
  classical
  ext x y
  rcases x with ⟨i, j⟩
  rcases y with ⟨i', j'⟩
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  simp_rw [localRightSignPermutationUnitary_conj_apply]
  simp only [smul_eq_mul]
  rw [← Finset.mul_sum]
  have hS : (Fintype.card (b → Bool) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (b → Bool) ≠ 0)
  have hP : (Fintype.card (Equiv.Perm b) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm b) ≠ 0)
  have hcard :
      ((Fintype.card ((b → Bool) × Equiv.Perm b) : ℂ)⁻¹) =
        (Fintype.card (b → Bool) : ℂ)⁻¹ *
          (Fintype.card (Equiv.Perm b) : ℂ)⁻¹ := by
    rw [Fintype.card_prod]
    rw [Nat.cast_mul]
    field_simp [hS, hP]
  have hcastB :
      ((((Fintype.card b : ℝ)⁻¹ : ℝ) : ℂ)) =
        (Fintype.card b : ℂ)⁻¹ := by
    have hcardR : (Fintype.card b : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card b ≠ 0)
    norm_num [hcardR]
  by_cases hjj' : j = j'
  · subst j'
    have hsum :
        (∑ idx : (b → Bool) × Equiv.Perm b,
          boolSignComplex (idx.1 (idx.2 j)) *
              X (i, idx.2 j) (i', idx.2 j) *
            boolSignComplex (idx.1 (idx.2 j))) =
          (Fintype.card (b → Bool) : ℂ) *
            ∑ π : Equiv.Perm b, X (i, π j) (i', π j) := by
      rw [Fintype.sum_prod_type]
      simp [Finset.mul_sum, mul_left_comm, mul_comm]
    rw [hsum, hcard]
    calc
      ((Fintype.card (b → Bool) : ℂ)⁻¹ *
          (Fintype.card (Equiv.Perm b) : ℂ)⁻¹) *
          ((Fintype.card (b → Bool) : ℂ) *
            ∑ π : Equiv.Perm b, X (i, π j) (i', π j)) =
          (Fintype.card (Equiv.Perm b) : ℂ)⁻¹ *
            ∑ π : Equiv.Perm b, X (i, π j) (i', π j) := by
        field_simp [hS, hP]
      _ = (Fintype.card b : ℂ)⁻¹ * ∑ k : b, X (i, k) (i', k) := by
        exact perm_orbit_average_eq_uniform (fun k : b => X (i, k) (i', k)) j
      _ = (Matrix.kronecker (partialTraceB X) (maximallyMixed b).matrix)
          (i, j) (i', j) := by
        simp [partialTraceB, maximallyMixed_matrix, Matrix.kronecker,
          Matrix.kroneckerMap_apply, hcastB, mul_comm]
  · have hsum :
        (∑ idx : (b → Bool) × Equiv.Perm b,
          boolSignComplex (idx.1 (idx.2 j)) *
              X (i, idx.2 j) (i', idx.2 j') *
            boolSignComplex (idx.1 (idx.2 j'))) = 0 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_eq_zero ?_
      intro π _
      have hne : π j ≠ π j' := fun h => hjj' (π.injective h)
      calc
        (∑ ε : b → Bool,
          boolSignComplex (ε (π j)) *
              X (i, π j) (i', π j') *
            boolSignComplex (ε (π j'))) =
            X (i, π j) (i', π j') *
              (∑ ε : b → Bool,
                boolSignComplex (ε (π j)) * boolSignComplex (ε (π j'))) := by
          simp [Finset.mul_sum, mul_assoc, mul_comm]
        _ = 0 := by
          rw [boolSignComplex_sum_mul_eq_zero_of_ne hne, mul_zero]
    rw [hsum, mul_zero]
    simp [partialTraceB, maximallyMixed_matrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
      hjj']

end State

end

end QIT
