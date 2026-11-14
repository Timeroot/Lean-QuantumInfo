/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.SmoothComparisonFidelity
public import QIT.OneShot.SmoothNormalizedExtension
public import QIT.States.Geometry.PurifiedDistanceAngle
public import QIT.Information.Entropy.Log2Lemmas

/-!
# Smooth conditional min/max entropy comparison

This module follows the normalized-extension and fidelity-block route in
Tomamichel, `calculus.tex:525-554,653-694`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QIT

universe u v

noncomputable section

namespace SmoothComparison

private theorem generalizedFidelity_ge_one_sub_sq_of_purifiedDistance_le
    {a : Type u} [Fintype a] [DecidableEq a]
    (ρ σ : SubnormalizedState a) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdist : ρ.purifiedDistance σ ≤ δ) :
    1 - δ ^ 2 ≤ ρ.generalizedFidelity σ := by
  have hgf_le : ρ.generalizedFidelity σ ≤ 1 := by
    let ρhat : State (Sum PUnit.{u + 1} a) := ρ.hatExtension
    let σhat : State (Sum PUnit.{u + 1} a) := σ.hatExtension
    have hgf : ρ.generalizedFidelity σ = ρhat.squaredFidelity σhat := by
      simpa [ρhat, σhat] using
        (SubnormalizedState.generalizedFidelity_eq_squaredFidelity_hatExtension ρ σ)
    rw [hgf]
    exact State.squaredFidelity_le_one_of_uhlmann ρhat σhat
  have hinside : 0 ≤ 1 - ρ.generalizedFidelity σ := sub_nonneg.mpr hgf_le
  have hdist_nonneg : 0 ≤ ρ.purifiedDistance σ := by
    rw [SubnormalizedState.purifiedDistance_eq]
    exact Real.sqrt_nonneg _
  have hsq : (ρ.purifiedDistance σ) ^ 2 = 1 - ρ.generalizedFidelity σ := by
    rw [SubnormalizedState.purifiedDistance_eq, Real.sq_sqrt hinside]
  nlinarith

end SmoothComparison

namespace State

private theorem smoothConditionalMinEntropy_le_smoothConditionalMaxEntropy_add_distancePenalty
    {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) {ε ε' δ : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hε'0 : 0 ≤ ε') (hε'1 : ε' < 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hcompose : ∀ {c : Type (max u v)} [Fintype c] [DecidableEq c]
      (center left right : SubnormalizedState c),
      center.purifiedBall ε left → center.purifiedBall ε' right →
        left.purifiedDistance right ≤ δ) :
    ρ.smoothConditionalMinEntropy ε hε0 hε1 ≤
      ρ.smoothConditionalMaxEntropy ε' hε'0 hε'1 +
        log2 (1 / (1 - δ ^ 2)) := by
  rcases
      SmoothNormalizedExtension.exists_normalizedExtension_smoothConditionalMinEntropy
        ρ hε0 hε1 with
    ⟨n, Tmin, σB, ρhat, hTmin, hTnorm, hρhat_feas, hρhat_ball,
      hρhat_value, hmin_eq⟩
  let extra := Fin (n + 1)
  let V : ReferenceIsometry a (Sum extra a) := ReferenceIsometry.sumInr extra a
  have hε'sub : ε' < Real.sqrt ρ.toSubnormalized.matrix.trace.re :=
    ρ.epsilon_lt_sqrt_toSubnormalized_trace hε'1
  rcases ρ.toSubnormalized.smoothConditionalMaxEntropy_exists_optimizer
      (a := a) hε'0 hε'sub with
    ⟨ρmax, hρmax, hρmax_ball, hmax_eq, _hmax_opt⟩
  let ρmaxPlus : SubnormalizedState (Prod (Sum extra a) b) :=
    ρmax.sourceIsometryApply V
  have hρmaxPlus_ball :
      (ρ.toSubnormalized.sourceIsometryApply V).purifiedBall ε' ρmaxPlus := by
    exact SubnormalizedState.purifiedBall_sourceIsometryApply V hρmax_ball
  have htrace_pos : 0 < ρmaxPlus.matrix.trace.re := by
    have hcenter_trace :
        (ρ.toSubnormalized.sourceIsometryApply V).matrix.trace.re = 1 := by
      rw [SubnormalizedState.sourceIsometryApply_trace_re,
        State.toSubnormalized_matrix, ρ.trace_re_eq_one]
    apply SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      (ρ.toSubnormalized.sourceIsometryApply V) ρmaxPlus
    · rw [hcenter_trace, Real.sqrt_one]
      exact hε'1
    · exact hρmaxPlus_ball
  let ω : State (Prod (Sum extra a) b) := ρmaxPlus.normalize htrace_pos.ne'
  have hscale :
      SubnormalizedState.ofStateScale ω ρmaxPlus.matrix.trace.re
          htrace_pos.le ρmaxPlus.trace_le_one = ρmaxPlus := by
    exact SubnormalizedState.ofStateScale_normalize_trace_eq ρmaxPlus htrace_pos
  have htri : ρhat.toSubnormalized.purifiedDistance ρmaxPlus ≤ δ :=
    hcompose (ρ.toSubnormalized.sourceIsometryApply V)
      ρhat.toSubnormalized ρmaxPlus hρhat_ball hρmaxPlus_ball
  have hgf_lower :
      1 - δ ^ 2 ≤
        ρhat.toSubnormalized.generalizedFidelity ρmaxPlus :=
    SmoothComparison.generalizedFidelity_ge_one_sub_sq_of_purifiedDistance_le
      ρhat.toSubnormalized ρmaxPlus hδ0 htri
  have hgf_scale :
      ρhat.toSubnormalized.generalizedFidelity ρmaxPlus =
        ρmaxPlus.matrix.trace.re * ρhat.squaredFidelity ω := by
    calc
      ρhat.toSubnormalized.generalizedFidelity ρmaxPlus =
          ρhat.toSubnormalized.generalizedFidelity
            (SubnormalizedState.ofStateScale ω ρmaxPlus.matrix.trace.re
              htrace_pos.le ρmaxPlus.trace_le_one) := by rw [hscale]
      _ = ρmaxPlus.matrix.trace.re * ρhat.squaredFidelity ω :=
        SubnormalizedState.generalizedFidelity_toSubnormalized_ofStateScale
          ρhat ω htrace_pos.le ρmaxPlus.trace_le_one
  have hpenalty_pos : 0 < 1 - δ ^ 2 := by
    nlinarith
  have hfid_sq_pos : 0 < ρhat.squaredFidelity ω := by
    rw [hgf_scale] at hgf_lower
    have hprod_pos :
        0 < ρmaxPlus.matrix.trace.re * ρhat.squaredFidelity ω :=
      lt_of_lt_of_le hpenalty_pos hgf_lower
    exact pos_of_mul_pos_right hprod_pos ρmaxPlus.trace_nonneg
  have hfid_pos : 0 < ω.fidelity ρhat := by
    have hcomm : ρhat.squaredFidelity ω = ω.squaredFidelity ρhat :=
      State.squaredFidelity_comm_of_uhlmann ρhat ω
    rw [hcomm, State.squaredFidelity_eq_fidelity_sq] at hfid_sq_pos
    nlinarith [State.fidelity_nonneg ω ρhat]
  have hρhat_bound :
      ρhat.matrix ≤
        ((Tmin.trace.re : ℂ) • State.identityTensorStateMatrix
          (a := Sum extra a) σB) := by
    calc
      ρhat.matrix ≤ Matrix.kronecker (1 : CMatrix (Sum extra a)) Tmin :=
        hρhat_feas.2
      _ = (Tmin.trace.re : ℂ) •
          State.identityTensorStateMatrix (a := Sum extra a) σB := by
        have hkron := congrArg
          (fun T : CMatrix b => Matrix.kronecker (1 : CMatrix (Sum extra a)) T)
          hTnorm
        calc
          Matrix.kronecker (1 : CMatrix (Sum extra a)) Tmin =
              Matrix.kronecker (1 : CMatrix (Sum extra a))
                ((Tmin.trace.re : ℂ) • σB.matrix) := hkron.symm
          _ = (Tmin.trace.re : ℂ) •
              Matrix.kronecker (1 : CMatrix (Sum extra a)) σB.matrix :=
            Matrix.kronecker_smul _ _ _
  have hsdp := State.neg_log2_add_log2_fidelity_sq_le_conditionalMaxEntropy
    ω ρhat σB hTmin hfid_pos hρhat_bound
  have hmax_scale :
      ρmaxPlus.conditionalMaxEntropyRaw =
        ω.conditionalMaxEntropy + log2 ρmaxPlus.matrix.trace.re := by
    calc
      ρmaxPlus.conditionalMaxEntropyRaw =
          (SubnormalizedState.ofStateScale ω ρmaxPlus.matrix.trace.re
            htrace_pos.le ρmaxPlus.trace_le_one).conditionalMaxEntropyRaw := by rw [hscale]
      _ = ω.conditionalMaxEntropy + log2 ρmaxPlus.matrix.trace.re :=
        SubnormalizedState.conditionalMaxEntropy_ofStateScale
          (a := Sum extra a) (b := b) ω htrace_pos ρmaxPlus.trace_le_one
  have hmax_isometry :
      ρmaxPlus.conditionalMaxEntropyRaw = ρmax.conditionalMaxEntropyRaw := by
    exact SmoothNormalizedExtension.conditionalMaxEntropyRaw_sourceIsometryApply_sumInr
      (extra := extra) ρmax
  have hfid_product :
      1 - δ ^ 2 ≤
        ρmaxPlus.matrix.trace.re * (ω.fidelity ρhat) ^ 2 := by
    rw [hgf_scale, State.squaredFidelity_comm_of_uhlmann ρhat ω,
      State.squaredFidelity_eq_fidelity_sq] at hgf_lower
    exact hgf_lower
  have hlog_product :
      log2 (1 - δ ^ 2) ≤
        log2 (ρmaxPlus.matrix.trace.re * (ω.fidelity ρhat) ^ 2) :=
    QIT.log2_mono_of_pos hpenalty_pos hfid_product
  have hlog_mul :
      log2 (ρmaxPlus.matrix.trace.re * (ω.fidelity ρhat) ^ 2) =
        log2 ρmaxPlus.matrix.trace.re + log2 ((ω.fidelity ρhat) ^ 2) := by
    unfold log2
    rw [Real.log_mul htrace_pos.ne' (sq_pos_of_pos hfid_pos).ne']
    ring
  rw [hlog_mul] at hlog_product
  rw [← hmin_eq, State.smoothConditionalMaxEntropy_eq_toSubnormalized, hmax_eq]
  change ρhat.conditionalMinEntropy ≤
    ρmax.conditionalMaxEntropyRaw + log2 (1 / (1 - δ ^ 2))
  rw [← hmax_isometry, hmax_scale, QIT.log2_one_div, hρhat_value]
  linarith

/-- Smooth min/max comparison in the epsilon form used by the fixed-error
AEP proof.  The proof uses Tomamichel's normalized extension of a smooth
min-entropy optimizer and the fidelity-block SDP comparison. -/
theorem smoothConditionalMinEntropy_le_smoothConditionalMaxEntropy_add_epsilonPenalty
    {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) {ε ε' : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hε'0 : 0 ≤ ε') (hε'1 : ε' < 1)
    (hsum : ε + ε' < 1) :
    ρ.smoothConditionalMinEntropy ε hε0 hε1 ≤
      ρ.smoothConditionalMaxEntropy ε' hε'0 hε'1 +
        log2 (1 / (1 - (ε + ε') ^ 2)) := by
  apply smoothConditionalMinEntropy_le_smoothConditionalMaxEntropy_add_distancePenalty
    ρ hε0 hε1 hε'0 hε'1 (add_nonneg hε0 hε'0) hsum
  intro c _ _ center left right hleft hright
  calc
    left.purifiedDistance right ≤
        left.purifiedDistance center + center.purifiedDistance right :=
      SubnormalizedState.purifiedDistance_triangle _ _ _
    _ ≤ ε + ε' := by
      have hleft' : left.purifiedDistance center ≤ ε := by
        rw [SubnormalizedState.purifiedDistance_comm]
        exact hleft
      exact add_le_add hleft' hright

/-- Tomamichel's source-shaped smooth min/max comparison
`pr:min-max-smooth` (`calculus.tex:653-694`). -/
theorem smoothConditionalMinEntropy_le_smoothConditionalMaxEntropy
    {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) {φ θ : ℝ}
    (hφ : 0 ≤ φ) (hθ : 0 ≤ θ) (hsum : φ + θ < Real.pi / 2) :
    ρ.smoothConditionalMinEntropy (Real.sin φ)
        (by
          exact Real.sin_nonneg_of_nonneg_of_le_pi hφ
            (by linarith [Real.pi_pos]))
        (by
          have hcos : 0 < Real.cos φ :=
            Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
          nlinarith [Real.sin_sq_add_cos_sq φ, sq_pos_of_pos hcos]) ≤
      ρ.smoothConditionalMaxEntropy (Real.sin θ)
          (by
            exact Real.sin_nonneg_of_nonneg_of_le_pi hθ
              (by linarith [Real.pi_pos]))
          (by
            have hcos : 0 < Real.cos θ :=
              Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
            nlinarith [Real.sin_sq_add_cos_sq θ, sq_pos_of_pos hcos]) +
        2 * log2 (1 / Real.cos (φ + θ)) := by
  have hφpi : φ ≤ Real.pi := by linarith [Real.pi_pos]
  have hθpi : θ ≤ Real.pi := by linarith [Real.pi_pos]
  have hsinφ0 : 0 ≤ Real.sin φ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hφ hφpi
  have hsinθ0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ hθpi
  have hcosφ : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hcosθ : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hsinφ1 : Real.sin φ < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq φ, sq_pos_of_pos hcosφ]
  have hsinθ1 : Real.sin θ < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_pos_of_pos hcosθ]
  have hsum0 : 0 ≤ φ + θ := add_nonneg hφ hθ
  have hsindelta0 : 0 ≤ Real.sin (φ + θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hsum0 (by linarith [Real.pi_pos])
  have hcossum : 0 < Real.cos (φ + θ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hsum⟩
  have hsindelta1 : Real.sin (φ + θ) < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (φ + θ), sq_pos_of_pos hcossum]
  have hbase :=
    smoothConditionalMinEntropy_le_smoothConditionalMaxEntropy_add_distancePenalty
      ρ hsinφ0 hsinφ1 hsinθ0 hsinθ1 hsindelta0 hsindelta1 (by
        intro c _ _ center left right hleft hright
        apply SubnormalizedState.purifiedDistance_le_sin_add
          left center right hφ hθ hsum
        · rw [SubnormalizedState.purifiedDistance_comm]
          exact hleft
        · exact hright)
  have htrig : 1 - Real.sin (φ + θ) ^ 2 = Real.cos (φ + θ) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (φ + θ)]
  have hcorr :
      log2 (1 / (1 - Real.sin (φ + θ) ^ 2)) =
        2 * log2 (1 / Real.cos (φ + θ)) := by
    rw [htrig]
    have hdiv : 1 / Real.cos (φ + θ) ^ 2 =
        (1 / Real.cos (φ + θ)) ^ 2 := by
      field_simp [hcossum.ne']
    rw [hdiv]
    unfold log2
    rw [Real.log_pow]
    ring
  rw [hcorr] at hbase
  exact hbase

end State

end

end QIT
