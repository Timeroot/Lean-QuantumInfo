/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Renyi.ConditionalRenyiMinimax
public import QuantumLib.QIT.Util.Order.EReal

/-!
# Singular-boundary completion of the conditional Renyi minimax step

This module removes the compact full-support cutoff from the Sion minimax
step in Tomamichel's proof of upward sandwiched conditional Renyi duality.

Source: [Tomamichel2015FiniteResources, cond.tex:361-397], the proof of
Proposition `pr:dual-new`. The support restriction and compact
positive-eigenvalue cutoff are described in `cond.tex`, lines 100-103.

The formal boundary argument keeps the source's common Holder bracket, support
restriction, positive spectral cutoff, Sion exchange, and identity
regularization. Since Sion only needs one optimization domain to be compact,
the final exchange uses the compact `tau` density domain and the convex
full-rank `sigma` domain; the proved cutoff theorem records the source's
compact restriction explicitly. Pointwise identity regularization then removes
the full-rank boundary inside each fixed-`tau` infimum.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

open Matrix

noncomputable section
universe u v w

open QIT

namespace MState

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

/-- Sion exchange on the full-rank `sigma` domain. The compact variable is
the `tau` density domain; applying Sion to the negative bracket gives the
source `inf_sigma sup_tau` orientation without assuming compactness of the
open full-rank set. -/
theorem fullRankDensityMatrixSet_sion_abcSidePowerTraceRe_EReal
    [Nonempty c] {p : ℝ}
    {R : CMatrix ((a × b) × c)} (hR : R.PosSemidef)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (⨅ sigma : CMatrix b,
      ⨅ _hSigma : fullRankDensityMatrixSet b sigma,
        ⨆ tau : CMatrix c,
          ⨆ _hTau : densityMatrixSet c tau,
            (abcSidePowerTraceRe (a := a) R sigma tau p : EReal)) =
      ⨆ tau : CMatrix c,
        ⨆ _hTau : densityMatrixSet c tau,
          ⨅ sigma : CMatrix b,
            ⨅ _hSigma : fullRankDensityMatrixSet b sigma,
              (abcSidePowerTraceRe (a := a) R sigma tau p : EReal) := by
  let F : {sigma : CMatrix b // fullRankDensityMatrixSet b sigma} →
      {tau : CMatrix c // densityMatrixSet c tau} → EReal :=
    fun sigma tau => (abcSidePowerTraceRe (a := a) R sigma.1 tau.1 p : EReal)
  have hnegMem :
      (⨅ tau : CMatrix c,
        ⨅ _hTau : densityMatrixSet c tau,
          ⨆ sigma : CMatrix b,
            ⨆ _hSigma : fullRankDensityMatrixSet b sigma,
              -((abcSidePowerTraceRe (a := a) R sigma tau p : EReal))) =
        ⨆ sigma : CMatrix b,
          ⨆ _hSigma : fullRankDensityMatrixSet b sigma,
            ⨅ tau : CMatrix c,
              ⨅ _hTau : densityMatrixSet c tau,
                -((abcSidePowerTraceRe (a := a) R sigma tau p : EReal)) := by
    exact sion_iInf_iSup_eq_iSup_iInf
      (densityMatrixSet_nonempty (a := c))
      (densityMatrixSet_convex (a := c))
      (densityMatrixSet_isCompact (a := c))
      (fun sigma hSigma => by
        have hcontReal : ContinuousOn
            (fun tau : CMatrix c => abcSidePowerTraceRe (a := a) R sigma tau p)
            (densityMatrixSet c) :=
          (abcSidePowerTraceRe_continuousOn_tau_posSemidef
            (a := a) R sigma hp0).mono (fun tau hTau => hTau.1)
        have hcontE : ContinuousOn
            (fun tau : CMatrix c =>
              (abcSidePowerTraceRe (a := a) R sigma tau p : EReal))
            (densityMatrixSet c) :=
          continuous_coe_real_ereal.comp_continuousOn hcontReal
        exact ContinuousOn.lowerSemicontinuousOn
          (continuous_neg.comp_continuousOn hcontE))
      (fun sigma hSigma => by
        have h : QuasiconvexOn ℝ (densityMatrixSet c)
            ((fun x : ℝ => -((x : EReal))) ∘
              fun tau : CMatrix c => abcSidePowerTraceRe (a := a) R sigma tau p) :=
          (Convex.quasiconcaveOn_restrict
            (abcSidePowerTraceRe_quasiconcaveOn_tau
              (a := a) hR hSigma.1.posSemidef hp0 hp1)
            (fun tau hTau => hTau.1)
            (densityMatrixSet_convex (a := c))).antitone_comp
              antitone_ereal_neg_coe
        exact h)
      (fullRankDensityMatrixSet_convex (a := b))
      (fun tau hTau => by
        have hcontReal : ContinuousOn
            (fun sigma : CMatrix b => abcSidePowerTraceRe (a := a) R sigma tau p)
            (fullRankDensityMatrixSet b) :=
          (abcSidePowerTraceRe_continuousOn_sigma_posDef
            (a := a) R tau p).mono (fun sigma hSigma => hSigma.1)
        have hcontE : ContinuousOn
            (fun sigma : CMatrix b =>
              (abcSidePowerTraceRe (a := a) R sigma tau p : EReal))
            (fullRankDensityMatrixSet b) :=
          continuous_coe_real_ereal.comp_continuousOn hcontReal
        exact ContinuousOn.upperSemicontinuousOn
          (continuous_neg.comp_continuousOn hcontE))
      (fun tau hTau => by
        have h : QuasiconcaveOn ℝ (fullRankDensityMatrixSet b)
            ((fun x : ℝ => -((x : EReal))) ∘
              fun sigma : CMatrix b => abcSidePowerTraceRe (a := a) R sigma tau p) :=
          (Convex.quasiconvexOn_restrict
            (abcSidePowerTraceRe_quasiconvexOn_sigma_posDef
              (a := a) hR hTau.1 hp0 hp1)
            (fun sigma hSigma => hSigma.1)
            (fullRankDensityMatrixSet_convex (a := b))).antitone_comp
              antitone_ereal_neg_coe
        exact h)
  have hnegSub :
      (⨅ tau : {tau : CMatrix c // densityMatrixSet c tau},
        ⨆ sigma : {sigma : CMatrix b // fullRankDensityMatrixSet b sigma},
          -F sigma tau) =
        ⨆ sigma : {sigma : CMatrix b // fullRankDensityMatrixSet b sigma},
          ⨅ tau : {tau : CMatrix c // densityMatrixSet c tau},
            -F sigma tau := by
    simpa [F, iInf_subtype' (p := fun tau : CMatrix c => densityMatrixSet c tau),
      iSup_subtype' (p := fun sigma : CMatrix b => fullRankDensityMatrixSet b sigma)]
      using hnegMem
  have hsub := ereal_sion_from_neg F hnegSub
  simpa [F, iInf_subtype' (p := fun sigma : CMatrix b => fullRankDensityMatrixSet b sigma),
    iSup_subtype' (p := fun tau : CMatrix c => densityMatrixSet c tau)]
    using hsub

/-- Normalized identity regularization of a density state.

For `epsilon > 0`, this is `(sigma + epsilon I) / Tr(sigma + epsilon I)`.
The fallback branch only makes the path total away from the source filter. -/
def densityIdentityRegularization [Nonempty b]
    (sigma : MState b) (epsilon : ℝ) : MState b :=
  if hepsilon : 0 < epsilon then
    stateOfPosDefReference
      (sigma.m + epsilon • (1 : CMatrix b))
      (cMatrix_posSemidef_add_pos_smul_one_posDef sigma.psd hepsilon)
  else
    sigma

@[simp]
theorem densityIdentityRegularization_eq_of_pos [Nonempty b]
    (sigma : MState b) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    densityIdentityRegularization sigma epsilon =
      stateOfPosDefReference
        (sigma.m + epsilon • (1 : CMatrix b))
        (cMatrix_posSemidef_add_pos_smul_one_posDef sigma.psd hepsilon) := by
  simp [densityIdentityRegularization, hepsilon]

/-- The normalized identity regularization is full rank for positive
regularization parameter. -/
theorem densityIdentityRegularization_posDef_of_pos [Nonempty b]
    (sigma : MState b) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (densityIdentityRegularization sigma epsilon).m.PosDef := by
  rw [densityIdentityRegularization_eq_of_pos sigma hepsilon]
  exact stateOfPosDefReference_posDef
    (sigma.m + epsilon • (1 : CMatrix b))
    (cMatrix_posSemidef_add_pos_smul_one_posDef sigma.psd hepsilon)

/-- Trace of the unnormalized identity regularization. -/
theorem add_smul_one_trace_re (sigma : MState b) (epsilon : ℝ) :
    ((sigma.m + epsilon • (1 : CMatrix b)).trace).re =
      1 + epsilon * (Fintype.card b : ℝ) := by
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
  simp [Complex.add_re, Complex.real_smul, sigma.tr']

/-- The normalizing scalar of identity regularization tends to one as the
positive regularization parameter tends to zero. -/
theorem densityIdentityRegularization_scale_tendsto [Nonempty b]
    (sigma : MState b) :
    Filter.Tendsto
      (fun epsilon : ℝ =>
        (((sigma.m + epsilon • (1 : CMatrix b)).trace).re)⁻¹)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 : ℝ)) := by
  have htrace :
      Filter.Tendsto
        (fun epsilon : ℝ =>
          ((sigma.m + epsilon • (1 : CMatrix b)).trace).re)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 : ℝ)) := by
    have hpath :
        (fun epsilon : ℝ =>
          ((sigma.m + epsilon • (1 : CMatrix b)).trace).re) =
        (fun epsilon : ℝ => 1 + epsilon * (Fintype.card b : ℝ)) := by
      funext epsilon
      exact add_smul_one_trace_re sigma epsilon
    have hcont : Continuous fun epsilon : ℝ =>
        1 + epsilon * (Fintype.card b : ℝ) := by
      fun_prop
    rw [hpath]
    simpa using
      (hcont.continuousWithinAt (x := (0 : ℝ))
        (s := Set.Ioi (0 : ℝ))).tendsto
  simpa using htrace.inv₀ one_ne_zero

/-- The identity regularization `(σ + ε I) / Tr(σ + ε I)` converges to `σ` as
`ε → 0⁺`, so a positive definite domain recovers the whole value set. -/
theorem densityIdentityRegularization_matrix_tendsto [Nonempty b]
    (sigma : MState b) :
    Filter.Tendsto
      (fun epsilon : ℝ => (densityIdentityRegularization sigma epsilon).m)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds sigma.m) := by
  have hraw : Filter.Tendsto
      (fun epsilon : ℝ => sigma.m + epsilon • (1 : CMatrix b))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds sigma.m) := by
    have hcont : Continuous (fun epsilon : ℝ =>
        sigma.m + epsilon • (1 : CMatrix b)) := by fun_prop
    have hnhds : Filter.Tendsto
        (fun epsilon : ℝ => sigma.m + epsilon • (1 : CMatrix b))
        (nhds (0 : ℝ)) (nhds sigma.m) := by
      simpa using hcont.tendsto (0 : ℝ)
    exact hnhds.mono_left inf_le_left
  have hscale := densityIdentityRegularization_scale_tendsto sigma
  have hscaled' : Filter.Tendsto
      (fun epsilon : ℝ =>
        ((sigma.m + epsilon • (1 : CMatrix b)).trace.re)⁻¹ •
          (sigma.m + epsilon • (1 : CMatrix b)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds sigma.m) := by
    simpa using hscale.smul hraw
  apply hscaled'.congr'
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  rw [densityIdentityRegularization_eq_of_pos sigma hepsilon,
    stateOfPosDefReference_matrix]

/-- Explicit lower spectral cutoff carried by normalized identity
regularization. -/
def densityIdentityRegularizationCutoff
    (sigma : MState b) (epsilon : ℝ) : ℝ :=
  (((sigma.m + epsilon • (1 : CMatrix b)).trace).re)⁻¹ * epsilon

/-- The explicit cutoff is positive for a positive regularization parameter. -/
theorem densityIdentityRegularizationCutoff_pos [Nonempty b]
    (sigma : MState b) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < densityIdentityRegularizationCutoff sigma epsilon := by
  have hpd : (sigma.m + epsilon • (1 : CMatrix b)).PosDef :=
    cMatrix_posSemidef_add_pos_smul_one_posDef sigma.psd hepsilon
  have htrace :
      0 < ((sigma.m + epsilon • (1 : CMatrix b)).trace).re :=
    (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hpd)).1
  exact mul_pos (inv_pos.mpr htrace) hepsilon

/-- Every positive identity regularization belongs to the compact density
domain with its explicit positive lower spectral cutoff. -/
theorem densityIdentityRegularization_mem_uniformlyPositive [Nonempty b]
    (sigma : MState b) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (densityIdentityRegularization sigma epsilon).m ∈
      uniformlyPositiveDensityMatrixSet
        (densityIdentityRegularizationCutoff sigma epsilon) b := by
  let raw : CMatrix b := sigma.m + epsilon • (1 : CMatrix b)
  have hpd : raw.PosDef := by
    exact cMatrix_posSemidef_add_pos_smul_one_posDef sigma.psd hepsilon
  have htrace : 0 < raw.trace.re :=
    (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hpd)).1
  have hscale : 0 ≤ raw.trace.re⁻¹ := inv_nonneg.mpr htrace.le
  have hmatrix :
      (densityIdentityRegularization sigma epsilon).m =
        raw.trace.re⁻¹ • raw := by
    rw [densityIdentityRegularization_eq_of_pos sigma hepsilon]
    exact stateOfPosDefReference_matrix raw hpd
  refine ⟨state_matrix_mem_densityMatrixSet
    (densityIdentityRegularization sigma epsilon), ?_⟩
  rw [hmatrix, Matrix.le_iff]
  have hscaled : (raw.trace.re⁻¹ • sigma.m).PosSemidef :=
    Matrix.PosSemidef.smul sigma.psd hscale
  have heq :
      raw.trace.re⁻¹ • raw -
          densityIdentityRegularizationCutoff sigma epsilon • (1 : CMatrix b) =
        raw.trace.re⁻¹ • sigma.m := by
    ext i j
    simp [raw, densityIdentityRegularizationCutoff, Matrix.smul_apply]
    ring
  rw [heq]
  exact hscaled

end MState

namespace QIT

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

end QIT

namespace Ket

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

/-- The positive `AC` weight `I_A tensor tau_C^p` in the common bracket. -/
def upwardRenyiDualityACWeight (tau : CMatrix c) (p : ℝ) : CMatrix (a × c) :=
  (1 : CMatrix a) ⊗ₖ (CFC.rpow tau p)

/-- Reorder the `ABC` amplitude as an `AC:B` amplitude. -/
def upwardRenyiDualityACBAmplitude
    (psi : Ket ((a × b) × c)) : (a × c) × b → ℂ :=
  fun x => psi.vec ((x.1.1, x.2), x.1.2)

/-- The `B`-amplitude slice at fixed `A,C` coordinates. -/
def upwardRenyiDualityBSlice
    (psi : Ket ((a × b) × c)) (i : a) (k : c) : b → ℂ :=
  fun j => psi.vec ((i, j), k)

/-- The `B` marginal is the finite sum of the rank-one matrices associated
with the `A,C` amplitude slices. -/
theorem marginalBOfABC_matrix_eq_sum_rankOne_BSlice
    (psi : Ket ((a × b) × c)) :
    psi.state.marginalBOfABC.m =
      ∑ x : a × c,
        rankOneMatrix (psi.upwardRenyiDualityBSlice x.1 x.2) := by
  ext j j'
  simp [MState.marginalBOfABC, MState.marginalAB,
    Matrix.traceLeft, Matrix.traceRight,
    Matrix.sum_apply, rankOneMatrix_apply, upwardRenyiDualityBSlice,
    Fintype.sum_prod_type]

/-- Every rank-one `B` amplitude slice is supported by the `B` marginal. -/
theorem rankOne_BSlice_supports_marginalBOfABC
    (psi : Ket ((a × b) × c)) (i : a) (k : c) :
    Matrix.Supports
      (rankOneMatrix (psi.upwardRenyiDualityBSlice i k))
      psi.state.marginalBOfABC.m := by
  classical
  let x : a × c := (i, k)
  let rest : CMatrix b :=
    ∑ y ∈ (Finset.univ.erase x),
      rankOneMatrix (psi.upwardRenyiDualityBSlice y.1 y.2)
  have hrest : rest.PosSemidef := by
    dsimp [rest]
    let s : Finset (a × c) := Finset.univ.erase x
    change (∑ y ∈ s,
      rankOneMatrix (psi.upwardRenyiDualityBSlice y.1 y.2)).PosSemidef
    induction s using Finset.induction_on with
    | empty => simpa using (Matrix.PosSemidef.zero : (0 : CMatrix b).PosSemidef)
    | @insert y s hy ih =>
        simpa [Finset.sum_insert hy] using
          (rankOneMatrix_pos (psi.upwardRenyiDualityBSlice y.1 y.2)).add ih
  have hdecomp :
      psi.state.marginalBOfABC.m =
        rankOneMatrix (psi.upwardRenyiDualityBSlice i k) + rest := by
    rw [psi.marginalBOfABC_matrix_eq_sum_rankOne_BSlice]
    have hx : x ∈ (Finset.univ : Finset (a × c)) := Finset.mem_univ x
    rw [← Finset.add_sum_erase _ _ hx]
  rw [hdecomp]
  exact Matrix.Supports.left_of_posSemidef_add
    (rankOneMatrix_pos (psi.upwardRenyiDualityBSlice i k)) hrest

/-- Apply the square root of `I_A tensor tau_C^p` to the `AC` leg. -/
def upwardRenyiDualityACWeightedAmplitude
    (psi : Ket ((a × b) × c)) (tau : CMatrix c) (p : ℝ) :
    (a × c) × b → ℂ :=
  Matrix.mulVec
    ((CFC.sqrt (upwardRenyiDualityACWeight (a := a) tau p)) ⊗ₖ
      (1 : CMatrix b))
    psi.upwardRenyiDualityACBAmplitude

/-- The effective `B`-side PSD matrix paired with `sigma_B^{-p}` in the
source common bracket. -/
def upwardRenyiDualityEffectiveBMatrix
    (psi : Ket ((a × b) × c)) (tau : CMatrix c) (p : ℝ) : CMatrix b :=
  Matrix.traceLeft
    (rankOneMatrix (psi.upwardRenyiDualityACWeightedAmplitude tau p))

/-- The effective matrix can be computed by applying the positive `AC`
weight before tracing out `AC`. -/
theorem upwardRenyiDualityEffectiveBMatrix_eq_partialTrace_weight_mul
    (psi : Ket ((a × b) × c)) (tau : CMatrix c) (p : ℝ)
    (htau : tau.PosSemidef) :
    psi.upwardRenyiDualityEffectiveBMatrix tau p =
      Matrix.traceLeft
        (((upwardRenyiDualityACWeight (a := a) tau p) ⊗ₖ (1 : CMatrix b)) *
          rankOneMatrix psi.upwardRenyiDualityACBAmplitude) := by
  let W : CMatrix (a × c) := upwardRenyiDualityACWeight (a := a) tau p
  let S : CMatrix (a × c) := CFC.sqrt W
  have hW : W.PosSemidef := by
    simpa [W, upwardRenyiDualityACWeight] using
      Matrix.PosSemidef.one.kronecker
        (cMatrix_rpow_posSemidef (A := tau) (s := p) htau)
  have hS : S.IsHermitian := by
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg W)).isHermitian
  have hSS : S * S = W := by
    exact CFC.sqrt_mul_sqrt_self W hW.nonneg
  calc
    psi.upwardRenyiDualityEffectiveBMatrix tau p =
        Matrix.traceLeft
          (rankOneMatrix
            (Matrix.mulVec (S ⊗ₖ (1 : CMatrix b))
              psi.upwardRenyiDualityACBAmplitude)) := by
          simp [upwardRenyiDualityEffectiveBMatrix,
            upwardRenyiDualityACWeightedAmplitude, S, W]
    _ = Matrix.traceLeft
          (((S * S) ⊗ₖ (1 : CMatrix b)) *
            rankOneMatrix psi.upwardRenyiDualityACBAmplitude) :=
      traceLeft_rankOne_kron_left_mulVec_eq_weight_mul
        S hS psi.upwardRenyiDualityACBAmplitude
    _ = Matrix.traceLeft
          ((W ⊗ₖ (1 : CMatrix b)) *
            rankOneMatrix psi.upwardRenyiDualityACBAmplitude) := by rw [hSS]

/-- Coordinate form of the effective `B`-side matrix. -/
theorem upwardRenyiDualityEffectiveBMatrix_apply
    (psi : Ket ((a × b) × c)) (tau : CMatrix c) (p : ℝ)
    (htau : tau.PosSemidef) (j j' : b) :
    psi.upwardRenyiDualityEffectiveBMatrix tau p j j' =
      ∑ i : a, ∑ k : c, ∑ k' : c,
        CFC.rpow tau p k k' * psi.vec ((i, j), k') * star (psi.vec ((i, j'), k)) := by
  rw [upwardRenyiDualityEffectiveBMatrix_eq_partialTrace_weight_mul psi tau p htau]
  simp [upwardRenyiDualityACWeight, upwardRenyiDualityACBAmplitude,
    Matrix.traceLeft, rankOneMatrix_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, mul_assoc]

private theorem sum_a_b_c_b_c_reorder
    {aa bb cc : Type*} [Fintype aa] [Fintype bb] [Fintype cc]
    (f : aa → bb → cc → bb → cc → ℂ) :
    (∑ i : aa, ∑ j : bb, ∑ k : cc, ∑ j' : bb, ∑ k' : cc, f i j k j' k') =
      ∑ j : bb, ∑ j' : bb, ∑ i : aa, ∑ k : cc, ∑ k' : cc, f i j k j' k' := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ i : aa, ∑ k : cc, ∑ j' : bb, ∑ k' : cc, f i j k j' k') =
        ∑ i : aa, ∑ j' : bb, ∑ k : cc, ∑ k' : cc, f i j k j' k' := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ j' : bb, ∑ i : aa, ∑ k : cc, ∑ k' : cc, f i j k j' k' := by
      rw [Finset.sum_comm]

/-- Trace-pairing form of the common source bracket. This is the handoff to
the support-aware reverse-Holder objective. -/
theorem abcSidePowerTraceRe_eq_effectiveBMatrix_pairing
    (psi : Ket ((a × b) × c))
    (sigma : CMatrix b) (tau : CMatrix c) (p : ℝ)
    (htau : tau.PosSemidef) :
    MState.abcSidePowerTraceRe (a := a) psi.state.m sigma tau p =
      ((CFC.rpow sigma (-p) * psi.upwardRenyiDualityEffectiveBMatrix tau p).trace).re := by
  classical
  rw [Ket.state_matrix]
  unfold MState.abcSidePowerTraceRe
  congr 1
  simpa [Matrix.trace, Matrix.mul_apply,
      upwardRenyiDualityEffectiveBMatrix_apply psi tau p htau,
      Matrix.kroneckerMap_apply, Matrix.one_apply, rankOneMatrix_apply,
      Fintype.sum_prod_type, Finset.mul_sum, mul_assoc] using
    (sum_a_b_c_b_c_reorder
      (f := fun i j k j' k' =>
        CFC.rpow sigma (-p) j j' *
          (CFC.rpow tau p k k' *
            (psi.vec ((i, j'), k') * star (psi.vec ((i, j), k))))))

/-- The effective `B`-side matrix is positive semidefinite. -/
theorem upwardRenyiDualityEffectiveBMatrix_posSemidef
    (psi : Ket ((a × b) × c)) (tau : CMatrix c) (p : ℝ) :
    (psi.upwardRenyiDualityEffectiveBMatrix tau p).PosSemidef :=
  traceLeft_posSemidef
    (rankOneMatrix_pos (psi.upwardRenyiDualityACWeightedAmplitude tau p))

/-- Every induced effective matrix is supported by the physical `B`
marginal. This is the forward half of the source support restriction. -/
theorem upwardRenyiDualityEffectiveBMatrix_supports_marginalBOfABC
    (psi : Ket ((a × b) × c)) (tau : CMatrix c) (p : ℝ)
    (htau : tau.PosSemidef) :
    Matrix.Supports
      (psi.upwardRenyiDualityEffectiveBMatrix tau p)
      psi.state.marginalBOfABC.m := by
  intro v hv
  have hpair : ∀ i : a, ∀ k : c,
      dotProduct (star (psi.upwardRenyiDualityBSlice i k)) v = 0 := by
    intro i k
    exact dotProduct_star_eq_zero_of_rankOne_mulVec_eq_zero
      (psi.upwardRenyiDualityBSlice i k) v
      (psi.rankOne_BSlice_supports_marginalBOfABC i k v hv)
  ext j
  simp only [Matrix.mulVec, dotProduct,
    psi.upwardRenyiDualityEffectiveBMatrix_apply tau p htau]
  change (∑ x : b,
    (∑ i : a, ∑ k : c, ∑ k' : c,
      CFC.rpow tau p k k' * psi.vec ((i, j), k') *
        star (psi.vec ((i, x), k))) * v x) = 0
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k' _ => ?_
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]
  have hpair' := hpair i k
  have hzero :
      (∑ x : b, star (psi.vec ((i, x), k)) * v x) = 0 := by
    simpa [upwardRenyiDualityBSlice, dotProduct] using hpair'
  rw [hzero]
  simp

/-- The power of the maximally mixed state is the corresponding scalar
multiple of the identity. -/
theorem uniform_rpow_eq_smul_one [Nonempty c]
    (p : ℝ) :
    CFC.rpow (MState.uniform : MState c).m p =
      (((Fintype.card c : ℝ)⁻¹ ^ p : ℝ) • (1 : CMatrix c)) := by
  have hcard : 0 ≤ (Fintype.card c : ℝ)⁻¹ := by positivity
  rw [MState.uniform_matrix]
  change CFC.rpow (((Fintype.card c : ℝ)⁻¹ : ℝ) • (1 : CMatrix c)) p =
    (((Fintype.card c : ℝ)⁻¹ ^ p : ℝ) • (1 : CMatrix c))
  rw [cMatrix_rpow_real_smul_posSemidef_schatten Matrix.PosSemidef.one hcard]
  rw [show CFC.rpow (1 : CMatrix c) p = 1 by exact CFC.one_rpow]

/-- At the maximally mixed `C` state, the effective matrix is a strictly
positive scalar multiple of the physical `B` marginal. -/
theorem upwardRenyiDualityEffectiveBMatrix_uniform_eq
    [Nonempty c]
    (psi : Ket ((a × b) × c)) (p : ℝ) :
    psi.upwardRenyiDualityEffectiveBMatrix (MState.uniform : MState c).m p =
      ((Fintype.card c : ℝ)⁻¹ ^ p : ℝ) •
        psi.state.marginalBOfABC.m := by
  ext j j'
  rw [psi.upwardRenyiDualityEffectiveBMatrix_apply
    (MState.uniform : MState c).m p (MState.uniform : MState c).psd]
  rw [uniform_rpow_eq_smul_one (c := c) p]
  simp [Matrix.smul_apply, Matrix.one_apply, MState.marginalBOfABC,
    MState.marginalAB, Matrix.traceLeft, Matrix.traceRight,
    Finset.mul_sum, mul_assoc]

/-- A side matrix supports the physical `B` marginal exactly when it supports
all effective matrices induced by normalized `C` states. This identifies the
support extension with Tomamichel's source restriction on `sigma_B`. -/
theorem marginalBOfABC_supports_iff_forall_effectiveBMatrix_supports
    [Nonempty c]
    (psi : Ket ((a × b) × c)) (sigma : CMatrix b) (p : ℝ) :
    Matrix.Supports psi.state.marginalBOfABC.m sigma ↔
      ∀ tau : CMatrix c, tau ∈ MState.densityMatrixSet c →
        Matrix.Supports
          (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma := by
  constructor
  · intro hMarginal tau hTau
    exact (psi.upwardRenyiDualityEffectiveBMatrix_supports_marginalBOfABC
      tau p hTau.1).trans hMarginal
  · intro hAll
    have hMixed := hAll (MState.uniform : MState c).m
      (MState.state_matrix_mem_densityMatrixSet (MState.uniform : MState c))
    rw [psi.upwardRenyiDualityEffectiveBMatrix_uniform_eq p] at hMixed
    intro v hv
    have hscaled := hMixed v hv
    have hcard : 0 < (Fintype.card c : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card c)
    have hscalar : 0 < (Fintype.card c : ℝ)⁻¹ ^ p :=
      Real.rpow_pos_of_pos (inv_pos.mpr hcard) p
    rw [Matrix.smul_mulVec] at hscaled
    exact (smul_eq_zero.mp hscaled).resolve_left hscalar.ne'

/-- Support-aware extended-real common bracket. Unsupported side states have
value `top`, exactly as in the reverse-Holder variational convention. -/
def upwardRenyiDualitySourceBracketEReal
    (psi : Ket ((a × b) × c))
    (sigma : CMatrix b) (tau : CMatrix c) (p : ℝ) : EReal := by
  classical
  exact if Matrix.Supports (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma then
      (MState.abcSidePowerTraceRe (a := a) psi.state.m sigma tau p : EReal)
    else
      ⊤

@[simp]
theorem upwardRenyiDualitySourceBracketEReal_of_supports
    (psi : Ket ((a × b) × c))
    (sigma : CMatrix b) (tau : CMatrix c) (p : ℝ)
    (h : Matrix.Supports (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma) :
    psi.upwardRenyiDualitySourceBracketEReal sigma tau p =
      (MState.abcSidePowerTraceRe (a := a) psi.state.m sigma tau p : EReal) := by
  simp [upwardRenyiDualitySourceBracketEReal, h]

@[simp]
theorem upwardRenyiDualitySourceBracketEReal_of_not_supports
    (psi : Ket ((a × b) × c))
    (sigma : CMatrix b) (tau : CMatrix c) (p : ℝ)
    (h : ¬ Matrix.Supports (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma) :
    psi.upwardRenyiDualitySourceBracketEReal sigma tau p = ⊤ := by
  simp [upwardRenyiDualitySourceBracketEReal, h]

/-- The source Sion equality on the explicit compact cutoff domain generated
by a positive identity regularization. -/
theorem upwardRenyiDualitySource_regularizationCutoff_sion
    [Nonempty b] [Nonempty c]
    (psi : Ket ((a × b) × c)) (sigma0 : MState b)
    {epsilon p : ℝ} (hepsilon : 0 < epsilon)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (⨅ sigma ∈ MState.uniformlyPositiveDensityMatrixSet
        (MState.densityIdentityRegularizationCutoff sigma0 epsilon) b,
      ⨆ tau ∈ MState.densityMatrixSet c,
        (MState.abcSidePowerTraceRe (a := a)
          psi.state.m sigma tau p : EReal)) =
      ⨆ tau ∈ MState.densityMatrixSet c,
        ⨅ sigma ∈ MState.uniformlyPositiveDensityMatrixSet
          (MState.densityIdentityRegularizationCutoff sigma0 epsilon) b,
          (MState.abcSidePowerTraceRe (a := a)
            psi.state.m sigma tau p : EReal) := by
  exact MState.uniformlyPositiveDensityMatrixSet_sion_abcSidePowerTraceRe_EReal
    (MState.densityIdentityRegularizationCutoff_pos sigma0 hepsilon)
    ⟨(MState.densityIdentityRegularization sigma0 epsilon).m,
      MState.densityIdentityRegularization_mem_uniformlyPositive sigma0 hepsilon⟩
    psi.state.psd hp0 hp1

/-- The source bracket converges along normalized full-rank identity
regularization whenever its effective matrix is supported by the limiting
side state. This is the `delta → 0` boundary step in Tomamichel's proof. -/
theorem abcSidePowerTraceRe_densityIdentityRegularization_tendsto
    [Nonempty b]
    (psi : Ket ((a × b) × c)) (sigma : MState b)
    (tau : CMatrix c) {p : ℝ} (htau : tau.PosSemidef)
    (hSupport : Matrix.Supports
      (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma.m) :
    Filter.Tendsto
      (fun epsilon : ℝ =>
        MState.abcSidePowerTraceRe (a := a) psi.state.m
          (MState.densityIdentityRegularization sigma epsilon).m tau p)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (MState.abcSidePowerTraceRe (a := a) psi.state.m
        sigma.m tau p)) := by
  let M : CMatrix b := psi.upwardRenyiDualityEffectiveBMatrix tau p
  have hraw :
      Filter.Tendsto
        (fun epsilon : ℝ =>
          ((M * CFC.rpow (sigma.m + epsilon • (1 : CMatrix b)) (-p)).trace).re)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((M * CFC.rpow sigma.m (-p)).trace).re) :=
    trace_mul_cMatrix_rpow_add_pos_smul_one_tendsto_of_support
      sigma.psd (by simpa [M] using hSupport) (-p)
  have hscale :
      Filter.Tendsto
        (fun epsilon : ℝ =>
          (((sigma.m + epsilon • (1 : CMatrix b)).trace).re)⁻¹ ^ (-p))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 : ℝ)) := by
    have hs := MState.densityIdentityRegularization_scale_tendsto sigma
    have hcont : ContinuousAt (fun x : ℝ => x ^ (-p)) (1 : ℝ) :=
      Real.continuousAt_rpow_const 1 (-p) (Or.inl one_ne_zero)
    simpa [Function.comp_def] using hcont.tendsto.comp hs
  have hprod :
      Filter.Tendsto
        (fun epsilon : ℝ =>
          (((sigma.m + epsilon • (1 : CMatrix b)).trace).re)⁻¹ ^ (-p) *
            ((M * CFC.rpow
              (sigma.m + epsilon • (1 : CMatrix b)) (-p)).trace).re)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((M * CFC.rpow sigma.m (-p)).trace).re) := by
    simpa [one_mul] using hscale.mul hraw
  rw [abcSidePowerTraceRe_eq_effectiveBMatrix_pairing psi sigma.m tau p htau]
  rw [Matrix.trace_mul_comm (CFC.rpow sigma.m (-p)) M]
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  have hpos : 0 < epsilon := hepsilon
  have hpd :
      (sigma.m + epsilon • (1 : CMatrix b)).PosDef :=
    MState.cMatrix_posSemidef_add_pos_smul_one_posDef sigma.psd hpos
  rw [abcSidePowerTraceRe_eq_effectiveBMatrix_pairing psi
    (MState.densityIdentityRegularization sigma epsilon).m tau p htau]
  rw [MState.densityIdentityRegularization_eq_of_pos sigma hpos]
  change _ =
    ((CFC.rpow
      (MState.stateOfPosDefReference
        (sigma.m + epsilon • (1 : CMatrix b)) hpd).m (-p) * M).trace).re
  have hscale_nonneg :
      0 ≤ (((sigma.m + epsilon • (1 : CMatrix b)).trace).re)⁻¹ := by
    have htr_pos :
        0 < ((sigma.m + epsilon • (1 : CMatrix b)).trace).re :=
      (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hpd)).1
    exact inv_nonneg.mpr htr_pos.le
  have hpow :
      CFC.rpow
          (MState.stateOfPosDefReference
            (sigma.m + epsilon • (1 : CMatrix b)) hpd).m (-p) =
        ((((sigma.m + epsilon • (1 : CMatrix b)).trace).re)⁻¹ ^ (-p) : ℝ) •
          CFC.rpow (sigma.m + epsilon • (1 : CMatrix b)) (-p) := by
    rw [MState.stateOfPosDefReference_matrix]
    exact cMatrix_rpow_real_smul_posSemidef_schatten
      hpd.posSemidef hscale_nonneg
  rw [hpow]
  rw [Matrix.smul_mul, Matrix.trace_smul]
  rw [Matrix.trace_mul_comm
    (CFC.rpow (sigma.m + epsilon • (1 : CMatrix b)) (-p)) M]
  simp [Complex.real_smul]

/-- For fixed `tau`, the source support extension makes the infimum over all
density matrices equal to the infimum over full-rank density matrices.

The nontrivial direction is the normalized identity-regularization limit;
unsupported candidates have value `top` and therefore cannot lower the
infimum. -/
theorem upwardRenyiDualitySourceBracketEReal_fullRank_iInf_eq_density_iInf
    [Nonempty b]
    (psi : Ket ((a × b) × c)) (tau : CMatrix c)
    (htau : tau ∈ MState.densityMatrixSet c) (p : ℝ) :
    (⨅ sigma : CMatrix b,
      ⨅ _hSigma : sigma ∈ MState.fullRankDensityMatrixSet b,
        (MState.abcSidePowerTraceRe (a := a) psi.state.m sigma tau p : EReal)) =
      ⨅ sigma : CMatrix b,
        ⨅ _hSigma : sigma ∈ MState.densityMatrixSet b,
          psi.upwardRenyiDualitySourceBracketEReal sigma tau p := by
  apply le_antisymm
  · refine le_iInf fun sigma => ?_
    refine le_iInf fun hSigma => ?_
    by_cases hSupport : Matrix.Supports
        (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma
    · rw [psi.upwardRenyiDualitySourceBracketEReal_of_supports sigma tau p hSupport]
      let sigmaState : MState b := MState.densityMatrixSetState sigma hSigma
      have hSupportState : Matrix.Supports
          (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigmaState.m := by
        simp only [sigmaState, MState.densityMatrixSetState_matrix]
        exact hSupport
      have htendReal :=
        psi.abcSidePowerTraceRe_densityIdentityRegularization_tendsto
          sigmaState tau htau.1 hSupportState
      have htendE :
          Filter.Tendsto
            (fun epsilon : ℝ =>
              (MState.abcSidePowerTraceRe (a := a) psi.state.m
                (MState.densityIdentityRegularization sigmaState epsilon).m
                tau p : EReal))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (MState.abcSidePowerTraceRe (a := a) psi.state.m
              sigma tau p : EReal)) := by
        simpa [sigmaState, MState.densityMatrixSetState_matrix] using
          EReal.tendsto_coe.mpr htendReal
      refine ge_of_tendsto htendE ?_
      filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
      have hpos : 0 < epsilon := hepsilon
      let sigmaEpsilon : MState b :=
        MState.densityIdentityRegularization sigmaState epsilon
      have hFull : sigmaEpsilon.m ∈ MState.fullRankDensityMatrixSet b := by
        exact ⟨MState.densityIdentityRegularization_posDef_of_pos sigmaState hpos,
          sigmaEpsilon.tr'⟩
      exact iInf_le_of_le sigmaEpsilon.m
        (iInf_le_of_le hFull le_rfl)
    · rw [psi.upwardRenyiDualitySourceBracketEReal_of_not_supports
        sigma tau p hSupport]
      exact le_top
  · refine le_iInf fun sigma => ?_
    refine le_iInf fun hSigma => ?_
    have hDensity : sigma ∈ MState.densityMatrixSet b :=
      MState.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma
    have hSupport : Matrix.Supports
        (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma :=
      Matrix.Supports.of_right_posDef
        (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma hSigma.1
    calc
      (⨅ sigma' : CMatrix b,
        ⨅ _hSigma' : sigma' ∈ MState.densityMatrixSet b,
          psi.upwardRenyiDualitySourceBracketEReal sigma' tau p) ≤
          psi.upwardRenyiDualitySourceBracketEReal sigma tau p :=
        iInf_le_of_le sigma (iInf_le_of_le hDensity le_rfl)
      _ = (MState.abcSidePowerTraceRe (a := a) psi.state.m sigma tau p : EReal) :=
        psi.upwardRenyiDualitySourceBracketEReal_of_supports sigma tau p hSupport

/-- Tomamichel's source minimax equality on the complete density domains.

The proof first applies Sion on the full-rank side-state domain, then removes
the full-support restriction by normalized identity regularization. The
support-aware extended bracket assigns `top` to precisely the candidates
excluded by the source reverse-Holder convention. -/
theorem upwardRenyiDualitySource_minimax
    [Nonempty b] [Nonempty c]
    (psi : Ket ((a × b) × c))
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (⨅ sigma : CMatrix b,
      ⨅ _hSigma : sigma ∈ MState.densityMatrixSet b,
        ⨆ tau : CMatrix c,
          ⨆ _hTau : tau ∈ MState.densityMatrixSet c,
            psi.upwardRenyiDualitySourceBracketEReal sigma tau p) =
      ⨆ tau : CMatrix c,
        ⨆ _hTau : tau ∈ MState.densityMatrixSet c,
          ⨅ sigma : CMatrix b,
            ⨅ _hSigma : sigma ∈ MState.densityMatrixSet b,
              psi.upwardRenyiDualitySourceBracketEReal sigma tau p := by
  let F :
      {tau : CMatrix c // tau ∈ MState.densityMatrixSet c} →
      {sigma : CMatrix b // sigma ∈ MState.densityMatrixSet b} → EReal :=
    fun tau sigma =>
      psi.upwardRenyiDualitySourceBracketEReal sigma.1 tau.1 p
  have hgeneralSub :
      (⨆ tau : {tau : CMatrix c // tau ∈ MState.densityMatrixSet c},
        ⨅ sigma : {sigma : CMatrix b // sigma ∈ MState.densityMatrixSet b},
          F tau sigma) ≤
        ⨅ sigma : {sigma : CMatrix b // sigma ∈ MState.densityMatrixSet b},
          ⨆ tau : {tau : CMatrix c // tau ∈ MState.densityMatrixSet c},
            F tau sigma :=
    iSup_iInf_le_iInf_iSup F
  have hgeneral :
      (⨆ tau : CMatrix c,
        ⨆ _hTau : tau ∈ MState.densityMatrixSet c,
          ⨅ sigma : CMatrix b,
            ⨅ _hSigma : sigma ∈ MState.densityMatrixSet b,
              psi.upwardRenyiDualitySourceBracketEReal sigma tau p) ≤
        ⨅ sigma : CMatrix b,
          ⨅ _hSigma : sigma ∈ MState.densityMatrixSet b,
            ⨆ tau : CMatrix c,
              ⨆ _hTau : tau ∈ MState.densityMatrixSet c,
                psi.upwardRenyiDualitySourceBracketEReal sigma tau p := by
    simpa [F, iInf_subtype', iSup_subtype'] using hgeneralSub
  have hleft :
      (⨅ sigma : CMatrix b,
        ⨅ _hSigma : sigma ∈ MState.densityMatrixSet b,
          ⨆ tau : CMatrix c,
            ⨆ _hTau : tau ∈ MState.densityMatrixSet c,
              psi.upwardRenyiDualitySourceBracketEReal sigma tau p) ≤
        ⨅ sigma : CMatrix b,
          ⨅ _hSigma : sigma ∈ MState.fullRankDensityMatrixSet b,
            ⨆ tau : CMatrix c,
              ⨆ _hTau : tau ∈ MState.densityMatrixSet c,
                (MState.abcSidePowerTraceRe (a := a)
                  psi.state.m sigma tau p : EReal) := by
    refine le_iInf fun sigma => ?_
    refine le_iInf fun hSigma => ?_
    have hDensity : sigma ∈ MState.densityMatrixSet b :=
      MState.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma
    calc
      (⨅ sigma' : CMatrix b,
        ⨅ _hSigma' : sigma' ∈ MState.densityMatrixSet b,
          ⨆ tau : CMatrix c,
            ⨆ _hTau : tau ∈ MState.densityMatrixSet c,
              psi.upwardRenyiDualitySourceBracketEReal sigma' tau p) ≤
          ⨆ tau : CMatrix c,
            ⨆ _hTau : tau ∈ MState.densityMatrixSet c,
              psi.upwardRenyiDualitySourceBracketEReal sigma tau p :=
        iInf_le_of_le sigma (iInf_le_of_le hDensity le_rfl)
      _ = ⨆ tau : CMatrix c,
          ⨆ _hTau : tau ∈ MState.densityMatrixSet c,
            (MState.abcSidePowerTraceRe (a := a)
              psi.state.m sigma tau p : EReal) := by
        apply iSup_congr
        intro tau
        apply iSup_congr
        intro hTau
        have hSupport : Matrix.Supports
            (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma :=
          Matrix.Supports.of_right_posDef
            (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma hSigma.1
        exact psi.upwardRenyiDualitySourceBracketEReal_of_supports
          sigma tau p hSupport
  have hsion :=
    MState.fullRankDensityMatrixSet_sion_abcSidePowerTraceRe_EReal
      (a := a) (b := b) (c := c) psi.state.psd hp0 hp1.le
  have hright :
      (⨆ tau : CMatrix c,
        ⨆ _hTau : tau ∈ MState.densityMatrixSet c,
          ⨅ sigma : CMatrix b,
            ⨅ _hSigma : sigma ∈ MState.fullRankDensityMatrixSet b,
              (MState.abcSidePowerTraceRe (a := a)
                psi.state.m sigma tau p : EReal)) =
        ⨆ tau : CMatrix c,
          ⨆ _hTau : tau ∈ MState.densityMatrixSet c,
            ⨅ sigma : CMatrix b,
              ⨅ _hSigma : sigma ∈ MState.densityMatrixSet b,
                psi.upwardRenyiDualitySourceBracketEReal sigma tau p := by
    apply iSup_congr
    intro tau
    apply iSup_congr
    intro hTau
    exact psi.upwardRenyiDualitySourceBracketEReal_fullRank_iInf_eq_density_iInf
      tau hTau p
  apply le_antisymm
  · exact hleft.trans_eq (hsion.trans hright)
  · exact hgeneral

end Ket

namespace QIT

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

end QIT
