/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Basic
public import QuantumLib.QIT.Information.Renyi.SandwichedRenyiOptimizedUSC
public import QuantumLib.QIT.Information.Entropy.MutualInformationDPI
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Sandwiched-Renyi channel mutual-information alpha-to-one support

This module contains support facts for the Khatri--Wilde
sandwiched-Renyi channel mutual-information `alpha → 1+` route
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:1869-1907].

The source proof for the sandwiched side is:

* monotonicity in `alpha` changes the right limit into `inf_{alpha > 1}`;
* the Mosonyi--Hiai minimax theorem exchanges `inf_alpha` and `sup_psi`;
* fixed-reference convergence sends `D~_alpha` to ordinary relative entropy;
* optimizing the side state recovers ordinary channel mutual information.

The file proves the fixed-output endpoint layer and the order-theoretic
`alpha → 1+`/`iInf` handoff.  The sandwiched monotonicity and the
Mosonyi/minimax application to the optimized pure-input function
`psi ↦ inf_sigma D~_alpha(N(psi) || psi_R ⊗ sigma_B)` enter the channel theorem
as hypotheses.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Topology
open Filter

noncomputable section
universe u v
variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable {E β : Type*} [TopologicalSpace E] [LinearOrder β]

open QIT

namespace QIT

section MosonyiHiai

/-- Mosonyi--Hiai minimax, in the exact order-topology form used by
Khatri--Wilde's sandwiched channel mutual-information limit.

The compact variable is `X`; the parameter variable ranges over an arbitrary
nonempty linearly ordered set `Y`.  Lower semicontinuity in the compact
variable and monotonicity in the parameter variable are enough to exchange
`inf_X sup_Y` with `sup_Y inf_X`. -/
theorem mosonyiHiai_iInf_iSup_eq_iSup_iInf
    {X : Set E} {Y : Set β} (hXne : X.Nonempty) (hXc : IsCompact X)
    (_hYne : Y.Nonempty) (F : E → β → EReal)
    (hlsc : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => F x y) X)
    (hmono :
      ∀ x ∈ X, ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ ≤ y₂ → F x y₁ ≤ F x y₂) :
    (⨅ x : X, ⨆ y : Y, F x.1 y.1) =
      (⨆ y : Y, ⨅ x : X, F x.1 y.1) := by
  classical
  refine le_antisymm ?_ ?_
  · refine le_of_forall_lt fun c hc => ?_
    obtain ⟨d, hcd, hdL⟩ := exists_between hc
    have hchoose :
        ∀ x : X, ∃ y : Y, d < F x.1 y.1 := by
      intro x
      have hxSup : d < ⨆ y : Y, F x.1 y.1 :=
        hdL.trans_le (iInf_le (fun x : X => ⨆ y : Y, F x.1 y.1) x)
      exact lt_iSup_iff.mp hxSup
    choose yOf hyOf using hchoose
    have hopen :
        ∀ x : X, ∃ U : Set E, IsOpen U ∧
          X ∩ (fun z : E => F z (yOf x).1) ⁻¹' Set.Ioi d = X ∩ U :=
      fun x =>
        lowerSemicontinuousOn_iff_preimage_Ioi.mp
          (hlsc (yOf x).1 (yOf x).2) d
    choose U hUopen hUeq using hopen
    have hcover : X ⊆ ⋃ x : X, U x := by
      intro z hz
      refine Set.mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
      have hzPre :
          z ∈ X ∩ (fun w : E => F w (yOf ⟨z, hz⟩).1) ⁻¹' Set.Ioi d := by
        exact ⟨hz, hyOf ⟨z, hz⟩⟩
      exact (Set.ext_iff.mp (hUeq ⟨z, hz⟩) z).mp hzPre |>.2
    obtain ⟨t, htcover⟩ := hXc.elim_finite_subcover U hUopen hcover
    have htne : t.Nonempty := by
      rcases hXne with ⟨x₀, hx₀⟩
      have hxcover := htcover hx₀
      rcases Set.mem_iUnion.mp hxcover with ⟨x, hxcover'⟩
      rcases Set.mem_iUnion.mp hxcover' with ⟨hxt, _⟩
      exact ⟨x, hxt⟩
    let yset : Finset Y := t.image yOf
    have hysetne : yset.Nonempty := htne.image yOf
    let y₀ : Y := yset.max' hysetne
    have hy_le_y₀ : ∀ x : X, x ∈ t → (yOf x).1 ≤ y₀.1 := by
      intro x hx
      have hxmem : yOf x ∈ yset := Finset.mem_image_of_mem yOf hx
      exact yset.le_max' (yOf x) hxmem
    have hd_le_inf : d ≤ ⨅ x : X, F x.1 y₀.1 := by
      refine le_iInf fun x => ?_
      have hxcover := htcover x.2
      rcases Set.mem_iUnion.mp hxcover with ⟨x', hxcover'⟩
      rcases Set.mem_iUnion.mp hxcover' with ⟨hx't, hxUx'⟩
      have hxPre :
          x.1 ∈ X ∩ (fun z : E => F z (yOf x').1) ⁻¹' Set.Ioi d := by
        exact (Set.ext_iff.mp (hUeq x') x.1).mpr ⟨x.2, hxUx'⟩
      exact le_of_lt ((hxPre.2).trans_le
        (hmono x.1 x.2 (yOf x').1 (yOf x').2 y₀.1 y₀.2 (hy_le_y₀ x' hx't)))
    exact hcd.trans_le (hd_le_inf.trans (le_iSup (fun y : Y => ⨅ x : X, F x.1 y.1) y₀))
  · refine iSup_le fun y => ?_
    refine le_iInf fun x => ?_
    exact (iInf_le (fun x : X => F x.1 y.1) x).trans
      (le_iSup (fun y : Y => F x.1 y.1) y)

/-- Dual Mosonyi--Hiai minimax in the form used directly by the
Khatri--Wilde sandwiched channel mutual-information proof:
`inf_parameter sup_compact = sup_compact inf_parameter`.

This is the upper-semicontinuous/monotone counterpart of
`mosonyiHiai_iInf_iSup_eq_iSup_iInf`.  Its proof follows the same source route:
upper semicontinuity gives closed overlevel sets on the compact pure-input
space; finite intersections are reduced to the minimum parameter in the finite
subfamily; compactness then gives a point in the full intersection. -/
theorem mosonyiHiai_iInf_iSup_eq_iSup_iInf_dual
    {X : Set E} {Y : Set β} (hXne : X.Nonempty) (hXc : IsCompact X)
    (_hYne : Y.Nonempty) (F : E → β → EReal)
    (husc : ∀ y ∈ Y, UpperSemicontinuousOn (fun x : E => F x y) X)
    (hmono :
      ∀ x ∈ X, ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ ≤ y₂ → F x y₁ ≤ F x y₂) :
    (⨅ y : Y, ⨆ x : X, F x.1 y.1) =
      (⨆ x : X, ⨅ y : Y, F x.1 y.1) := by
  classical
  refine le_antisymm ?_ ?_
  · refine le_of_forall_lt fun c hc => ?_
    obtain ⟨d, hcd, hdL⟩ := exists_between hc
    let S : Set E := X ∩ ⋂ y : Y, (fun x : E => F x y.1) ⁻¹' Set.Ici d
    have hSne : S.Nonempty := by
      by_contra hSempty
      have hSempty_eq : S = ∅ := by
        ext x
        constructor
        · intro hx
          exact (hSempty ⟨x, hx⟩).elim
        · intro hx
          exact False.elim hx
      have hfinite :
          ∃ u : Finset Y, ∀ x ∈ X, ∃ y ∈ u, F x y.1 < d := by
        have hfi :
            ∀ y ∈ Y, UpperSemicontinuousOn
              ((fun y x => F x y) y) X := by
          intro y hy
          exact husc y hy
        have hSempty_eq_source :
            X ∩ ⋂ y ∈ Y, (fun x : E => F x y) ⁻¹' Set.Ici d = ∅ := by
          simpa [S, Set.iInter_subtype] using hSempty_eq
        simpa [S] using
          (UpperSemicontinuousOn.inter_biInter_preimage_Ici_eq_empty_iff_exists_finset
            (s := X) (I := Y) (f := fun y x => F x y) hXc (c := d) hfi).mp
              hSempty_eq_source
      rcases hfinite with ⟨u, hu⟩
      by_cases hune : u.Nonempty
      · let y₀ : Y := u.min' hune
        have hy₀mem : y₀ ∈ u := u.min'_mem hune
        have hy₀sup : d < ⨆ x : X, F x.1 y₀.1 :=
          hdL.trans_le (iInf_le (fun y : Y => ⨆ x : X, F x.1 y.1) y₀)
        rcases lt_iSup_iff.mp hy₀sup with ⟨x₀, hx₀d⟩
        rcases hu x₀.1 x₀.2 with ⟨y, hyu, hyd⟩
        have hy₀le : y₀.1 ≤ y.1 := u.min'_le y hyu
        have hFy : F x₀.1 y₀.1 ≤ F x₀.1 y.1 :=
          hmono x₀.1 x₀.2 y₀.1 y₀.2 y.1 y.2 hy₀le
        exact (hx₀d.trans_le hFy).not_gt hyd
      · rcases hXne with ⟨x₀, hx₀⟩
        rcases hu x₀ hx₀ with ⟨y, hyu, _⟩
        exact hune ⟨y, hyu⟩
    rcases hSne with ⟨x₀, hxS⟩
    have hdinf : d ≤ ⨅ y : Y, F x₀ y.1 := by
      refine le_iInf fun y => ?_
      have hxAll : ∀ y : Y, x₀ ∈ (fun x : E => F x y.1) ⁻¹' Set.Ici d := by
        simpa [Set.mem_iInter] using hxS.2
      exact hxAll y
    exact hcd.trans_le (hdinf.trans
      (le_iSup (fun x : X => ⨅ y : Y, F x.1 y.1) ⟨x₀, hxS.1⟩))
  · refine iSup_le fun x => ?_
    refine le_iInf fun y => ?_
    exact (iInf_le (fun y : Y => F x.1 y.1) y).trans
      (le_iSup (fun x : X => F x.1 y.1) x)

end MosonyiHiai

end QIT

namespace MState

/-- Along the right-neighborhood filter `alpha → 1+`, every fixed
`alpha₀ > 1` is eventually above the varying parameter. -/
theorem relativeEntropyHighAlphaRightToOne_eventually_le
    (alpha₀ : {alpha : ℝ // 1 < alpha}) :
    ∀ᶠ alpha in relativeEntropyHighAlphaRightToOne, alpha.1 ≤ alpha₀.1 := by
  have hlt :
      ∀ᶠ x in nhdsWithin (1 : ℝ) (Set.Ioi 1), x < alpha₀.1 := by
    exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds alpha₀.2)
  rw [relativeEntropyHighAlphaRightToOne]
  filter_upwards [hlt.comap (fun alpha : {alpha : ℝ // 1 < alpha} => alpha.1)]
    with alpha halpha
  exact le_of_lt halpha

/-- The source right-neighborhood filter `alpha → 1+` is the `atBot` filter
on the subtype `{alpha // 1 < alpha}`.

This is the order-topology bridge behind the Khatri--Wilde step
`lim_{alpha → 1+} f(alpha) = inf_{alpha > 1} f(alpha)` for monotone
high-`alpha` quantities. -/
theorem relativeEntropyHighAlphaRightToOne_eq_atBot :
    relativeEntropyHighAlphaRightToOne = (atBot : Filter {alpha : ℝ // 1 < alpha}) := by
  unfold relativeEntropyHighAlphaRightToOne
  exact comap_coe_Ioi_nhdsGT (a := (1 : ℝ))

/-- A monotone high-`alpha` extended-real curve tends to its infimum as
`alpha → 1+`.

This is the source-shaped order handoff used in
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:1869-1907]. -/
theorem tendsto_relativeEntropyHighAlphaRightToOne_iInf_of_monotone
    {f : {alpha : ℝ // 1 < alpha} → EReal}
    (hmono :
      ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 → f alpha ≤ f beta) :
    Tendsto f relativeEntropyHighAlphaRightToOne (nhds (⨅ alpha, f alpha)) := by
  have hmono' : Monotone f := by
    intro alpha beta hle
    exact hmono alpha beta hle
  rw [relativeEntropyHighAlphaRightToOne_eq_atBot]
  exact tendsto_atBot_iInf hmono'

/-- A monotone high-`alpha` curve whose right endpoint is at least `lower`
is pointwise bounded below by `lower` on the whole source range.

This is the topology/order skeleton behind the source statement that
sandwiched Renyi divergences with `alpha > 1` dominate their `alpha → 1+`
trace-log endpoint.  The analytic input is the monotonicity hypothesis. -/
theorem le_of_tendsto_relativeEntropyHighAlphaRightToOne_of_monotone
    {f : {alpha : ℝ // 1 < alpha} → EReal} {limit lower : EReal}
    (htend : Tendsto f relativeEntropyHighAlphaRightToOne (nhds limit))
    (hmono :
      ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 → f alpha ≤ f beta)
    (hlower : lower ≤ limit) :
    ∀ alpha : {alpha : ℝ // 1 < alpha}, lower ≤ f alpha := by
  intro alpha
  have : Filter.NeBot relativeEntropyHighAlphaRightToOne :=
    relativeEntropyHighAlphaRightToOne_neBot
  have hconst :
      Tendsto (fun _ : {alpha : ℝ // 1 < alpha} => f alpha)
        relativeEntropyHighAlphaRightToOne (nhds (f alpha)) := tendsto_const_nhds
  have hevent :
      ∀ᶠ beta in relativeEntropyHighAlphaRightToOne, f beta ≤ f alpha := by
    filter_upwards [relativeEntropyHighAlphaRightToOne_eventually_le alpha] with beta hbeta
    exact hmono beta alpha hbeta
  exact hlower.trans (le_of_tendsto_of_tendsto htend hconst hevent)

/-- Every fixed side-information candidate has the correct PSD-reference
right-endpoint.

This is the pointwise endpoint layer underneath the state optimized
`inf_sigmaB` step.  The endpoint is still the candidate's own trace-log
relative entropy; comparing that endpoint uniformly with `I(A;B)_rho` is the
remaining chain-rule/monotonicity input. -/
theorem sandwichedRenyiMutualInformationCandidateE_tendsto_relativeEntropyPSDReferenceE
    (rhoAB : MState (a × b)) (sigmaB : MState b) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1)
      relativeEntropyHighAlphaRightToOne
      (nhds
        (relativeEntropyPSDReferenceE rhoAB
          (rhoAB.traceRight.prod sigmaB).m
          (rhoAB.traceRight.prod sigmaB).psd)) := by
  classical
  let sigmaAB : MState (a × b) := rhoAB.traceRight.prod sigmaB
  by_cases hSupport : Matrix.Supports rhoAB.m sigmaAB.m
  · have hlim :
        Tendsto
          (fun alpha : {alpha : ℝ // 1 < alpha} =>
            sandwichedRenyiPSDReferenceHighAlphaCurve rhoAB sigmaAB.m
              sigmaAB.psd alpha)
          relativeEntropyHighAlphaRightToOne
          (nhds
            (relativeEntropyPSDReferenceTraceLogFinite
              rhoAB sigmaAB.m sigmaAB.psd hSupport : EReal)) :=
      sandwichedRenyiPSDReferenceHighAlphaCurve_tendsto_traceLogFinite_of_supports
        rhoAB sigmaAB.psd hSupport
    have hendpoint :
        relativeEntropyPSDReferenceE rhoAB sigmaAB.m sigmaAB.psd =
          (relativeEntropyPSDReferenceTraceLogFinite
            rhoAB sigmaAB.m sigmaAB.psd hSupport : EReal) := by
      rw [relativeEntropyPSDReferenceE_eq_traceLogE rhoAB sigmaAB.psd]
      rw [relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports rhoAB sigmaAB.psd hSupport]
    rw [hendpoint]
    simpa [MState.sandwichedRenyiMutualInformationCandidateE,
      sandwichedRenyiPSDReferenceHighAlphaCurve, sigmaAB] using hlim
  · have hconst :
        Tendsto
          (fun _alpha : {alpha : ℝ // 1 < alpha} => (⊤ : EReal))
          relativeEntropyHighAlphaRightToOne
          (nhds (⊤ : EReal)) := tendsto_const_nhds
    have hendpoint :
        relativeEntropyPSDReferenceE rhoAB sigmaAB.m sigmaAB.psd = (⊤ : EReal) :=
      relativeEntropyPSDReferenceE_eq_top_of_not_supports rhoAB sigmaAB.psd hSupport
    have hendpoint' :
        relativeEntropyPSDReferenceE rhoAB
            (rhoAB.traceRight.prod sigmaB).m
            (rhoAB.traceRight.prod sigmaB).psd =
          (⊤ : EReal) := by
      simpa [sigmaAB] using hendpoint
    have heq :
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
          rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1) =ᶠ[
            relativeEntropyHighAlphaRightToOne]
          (fun _alpha : {alpha : ℝ // 1 < alpha} => (⊤ : EReal)) := by
      filter_upwards with alpha
      unfold MState.sandwichedRenyiMutualInformationCandidateE
      change sandwichedRenyiPSDReferenceE rhoAB sigmaAB.m sigmaAB.psd alpha.1 = ⊤
      rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt rhoAB sigmaAB.psd alpha.2]
      exact sandwichedRenyiPSDReferenceHighAlphaE_eq_top_of_not_supports
        rhoAB sigmaAB.psd alpha.1 hSupport
    rw [hendpoint']
    exact hconst.congr' heq.symm

/-- The fixed product-marginal sandwiched-Renyi mutual-information candidate
converges to ordinary mutual information as `alpha → 1+`.

This is the pointwise fixed-input/fixed-side-state limit used before the
Mosonyi minimax exchange in
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:1869-1907]. -/
theorem sandwichedRenyiMutualInformationCandidateE_traceLeft_tendsto_mutualInformation
    (rhoAB : MState (a × b)) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        rhoAB.sandwichedRenyiMutualInformationCandidateE rhoAB.traceLeft alpha.1)
      relativeEntropyHighAlphaRightToOne
      (nhds (mutualInformation rhoAB : EReal)) := by
  let sigmaAB : MState (a × b) := rhoAB.traceRight.prod rhoAB.traceLeft
  have hlim :
      Tendsto
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
          rhoAB.sandwichedRenyiMutualInformationCandidateE rhoAB.traceLeft alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds
          (relativeEntropyPSDReferenceE rhoAB
            (rhoAB.traceRight.prod rhoAB.traceLeft).m
            (rhoAB.traceRight.prod rhoAB.traceLeft).psd)) :=
    rhoAB.sandwichedRenyiMutualInformationCandidateE_tendsto_relativeEntropyPSDReferenceE
      rhoAB.traceLeft
  have hendpoint :
      relativeEntropyPSDReferenceE rhoAB
          (rhoAB.traceRight.prod rhoAB.traceLeft).m
          (rhoAB.traceRight.prod rhoAB.traceLeft).psd =
        (mutualInformation rhoAB : EReal) := by
    calc
      relativeEntropyPSDReferenceE rhoAB
          (rhoAB.traceRight.prod rhoAB.traceLeft).m
          (rhoAB.traceRight.prod rhoAB.traceLeft).psd =
          rhoAB.relativeEntropy (rhoAB.traceRight.prod rhoAB.traceLeft) := by
            rw [relativeEntropyPSDReferenceE_eq_traceLogE]
            rfl
      _ = (mutualInformation rhoAB : EReal) :=
            rhoAB.relativeEntropy_prod_marginals_eq_mutualInformation
  rw [hendpoint] at hlim
  exact hlim

/-- Order-theoretic handoff from the missing source lower bound to the
optimized state sandwiched-Renyi mutual-information limit.

The upper squeeze is the already proved product-marginal candidate limit.  The
hypothesis is exactly the remaining `inf_sigmaB` lower half: near `alpha = 1+`,
the optimized sandwiched-Renyi state mutual information is bounded below by the
ordinary mutual information. -/
theorem sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_eventually_lower
    (rhoAB : MState (a × b))
    (hlower :
      ∀ᶠ alpha in relativeEntropyHighAlphaRightToOne,
        (mutualInformation rhoAB : EReal) ≤
          rhoAB.sandwichedRenyiMutualInformationE alpha.1) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        rhoAB.sandwichedRenyiMutualInformationE alpha.1)
      relativeEntropyHighAlphaRightToOne
      (nhds (mutualInformation rhoAB : EReal)) := by
  have hconst :
      Tendsto
        (fun _alpha : {alpha : ℝ // 1 < alpha} => (mutualInformation rhoAB : EReal))
        relativeEntropyHighAlphaRightToOne
        (nhds (mutualInformation rhoAB : EReal)) := tendsto_const_nhds
  have hupper_tendsto :
      Tendsto
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
          rhoAB.sandwichedRenyiMutualInformationCandidateE rhoAB.traceLeft alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds (mutualInformation rhoAB : EReal)) :=
    rhoAB.sandwichedRenyiMutualInformationCandidateE_traceLeft_tendsto_mutualInformation
  have hupper :
      ∀ alpha : {alpha : ℝ // 1 < alpha},
        rhoAB.sandwichedRenyiMutualInformationE alpha.1 ≤
          rhoAB.sandwichedRenyiMutualInformationCandidateE rhoAB.traceLeft alpha.1 := by
    intro alpha
    exact rhoAB.sandwichedRenyiMutualInformationE_le_candidate rhoAB.traceLeft alpha.1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hconst hupper_tendsto hlower
    (Filter.Eventually.of_forall hupper)

/-- Candidate-wise lower bounds lift through the side-information infimum.

This isolates the order-theoretic `inf_sigmaB` step in the state
sandwiched-Renyi mutual-information endpoint proof.  The remaining analytic
content is the source lower bound for every side-information candidate. -/
theorem sandwichedRenyiMutualInformationE_eventually_lower_of_eventually_candidate_lower
    (rhoAB : MState (a × b))
    (hcandidate :
      ∀ᶠ alpha in relativeEntropyHighAlphaRightToOne,
        ∀ sigmaB : MState b,
          (mutualInformation rhoAB : EReal) ≤
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1) :
    ∀ᶠ alpha in relativeEntropyHighAlphaRightToOne,
      (mutualInformation rhoAB : EReal) ≤
        rhoAB.sandwichedRenyiMutualInformationE alpha.1 := by
  classical
  have : Nonempty b := by
    rcases rhoAB.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  filter_upwards [hcandidate] with alpha halpha
  rw [MState.sandwichedRenyiMutualInformationE_eq_sInf]
  refine le_csInf (rhoAB.sandwichedRenyiMutualInformationEValueSet_nonempty alpha.1) ?_
  intro y hy
  rcases hy with ⟨sigmaB, rfl⟩
  exact halpha sigmaB

/-- The optimized state sandwiched-Renyi mutual information converges to
ordinary mutual information once every side-information candidate satisfies the
source lower bound near `alpha = 1+`. -/
theorem sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_eventually_candidate_lower
    (rhoAB : MState (a × b))
    (hcandidate :
      ∀ᶠ alpha in relativeEntropyHighAlphaRightToOne,
        ∀ sigmaB : MState b,
          (mutualInformation rhoAB : EReal) ≤
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        rhoAB.sandwichedRenyiMutualInformationE alpha.1)
      relativeEntropyHighAlphaRightToOne
      (nhds (mutualInformation rhoAB : EReal)) :=
  rhoAB.sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_eventually_lower
    (rhoAB.sandwichedRenyiMutualInformationE_eventually_lower_of_eventually_candidate_lower
      hcandidate)

/-- A fixed side-information candidate is pointwise bounded below by ordinary
mutual information if its high-`alpha` curve is monotone and its right endpoint
dominates ordinary mutual information. -/
theorem sandwichedRenyiMutualInformationCandidateE_lower_of_tendsto_of_monotone
    (rhoAB : MState (a × b)) (sigmaB : MState b) {limit : EReal}
    (htend :
      Tendsto
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
          rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds limit))
    (hmono :
      ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1 ≤
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB beta.1)
    (hlower : (mutualInformation rhoAB : EReal) ≤ limit) :
    ∀ alpha : {alpha : ℝ // 1 < alpha},
      (mutualInformation rhoAB : EReal) ≤
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1 :=
  le_of_tendsto_relativeEntropyHighAlphaRightToOne_of_monotone htend hmono hlower

/-- Upper semicontinuity of every fixed side-information candidate lifts through
the `inf_sigmaB` state optimization. -/
theorem sandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_candidate
    {X : Type*} [TopologicalSpace X] {s : Set X}
    (rho : X → MState (a × b)) (alpha : ℝ)
    (husc :
      ∀ sigmaB : MState b,
        UpperSemicontinuousOn
          (fun x : X => (rho x).sandwichedRenyiMutualInformationCandidateE sigmaB alpha)
          s) :
    UpperSemicontinuousOn
      (fun x : X => (rho x).sandwichedRenyiMutualInformationE alpha) s := by
  have h :=
    upperSemicontinuousOn_iInf
      (f := fun sigmaB x =>
        (rho x).sandwichedRenyiMutualInformationCandidateE sigmaB alpha)
      husc
  exact h

/-- MState-level optimized `inf_sigmaB` alpha-to-one theorem from the analytic
fixed-candidate route.

For every side-information state, the remaining analytic inputs are:
endpoint convergence, endpoint lower bound by ordinary mutual information, and
monotonicity in `alpha`.  The conclusion is the actual optimized state limit,
not merely a fixed-candidate statement. -/
theorem sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_candidate_limits
    (rhoAB : MState (a × b))
    (hcandidate :
      ∀ sigmaB : MState b, ∃ limit : EReal,
        Tendsto
          (fun alpha : {alpha : ℝ // 1 < alpha} =>
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1)
          relativeEntropyHighAlphaRightToOne
          (nhds limit) ∧
        (mutualInformation rhoAB : EReal) ≤ limit ∧
        ∀ alpha beta : {alpha : ℝ // 1 < alpha},
          alpha.1 ≤ beta.1 →
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1 ≤
              rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB beta.1) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        rhoAB.sandwichedRenyiMutualInformationE alpha.1)
      relativeEntropyHighAlphaRightToOne
      (nhds (mutualInformation rhoAB : EReal)) := by
  refine
    rhoAB.sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_eventually_candidate_lower
      ?_
  exact Filter.Eventually.of_forall fun alpha sigmaB => by
    obtain ⟨limit, htend, hlower, hmono⟩ := hcandidate sigmaB
    exact
      rhoAB.sandwichedRenyiMutualInformationCandidateE_lower_of_tendsto_of_monotone
        sigmaB htend hmono hlower alpha

/-- Unsupported side-information candidates satisfy the endpoint lower bound
automatically by the source convention `D(rho || sigma) = +infty`. -/
theorem sandwichedRenyiMutualInformationCandidateEndpoint_lower_of_not_supports
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hSupport :
      ¬ Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m) :
    (mutualInformation rhoAB : EReal) ≤
      relativeEntropyPSDReferenceE rhoAB
        (rhoAB.traceRight.prod sigmaB).m
        (rhoAB.traceRight.prod sigmaB).psd := by
  rw [relativeEntropyPSDReferenceE_eq_top_of_not_supports rhoAB
    (rhoAB.traceRight.prod sigmaB).psd hSupport]
  exact le_top

/-- Supported side-information candidates reduce the endpoint lower bound to
the finite trace-log branch.  This is the exact remaining chain-rule inequality
`I(A;B)_rho ≤ D(rho_AB || rho_A \otimes sigma_B)`. -/
theorem sandwichedRenyiMutualInformationCandidateEndpoint_lower_of_traceLogFinite_lower
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hSupport :
      Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m)
    (hlower :
      (mutualInformation rhoAB : EReal) ≤
        (relativeEntropyPSDReferenceTraceLogFinite rhoAB
          (rhoAB.traceRight.prod sigmaB).m
          (rhoAB.traceRight.prod sigmaB).psd hSupport : EReal)) :
    (mutualInformation rhoAB : EReal) ≤
      relativeEntropyPSDReferenceE rhoAB
        (rhoAB.traceRight.prod sigmaB).m
        (rhoAB.traceRight.prod sigmaB).psd := by
  have hendpoint :
      relativeEntropyPSDReferenceE rhoAB
          (rhoAB.traceRight.prod sigmaB).m
          (rhoAB.traceRight.prod sigmaB).psd =
        (relativeEntropyPSDReferenceTraceLogFinite rhoAB
          (rhoAB.traceRight.prod sigmaB).m
          (rhoAB.traceRight.prod sigmaB).psd hSupport : EReal) := by
    rw [relativeEntropyPSDReferenceE_eq_traceLogE rhoAB
      (rhoAB.traceRight.prod sigmaB).psd]
    rw [relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports rhoAB
      (rhoAB.traceRight.prod sigmaB).psd hSupport]
  rwa [hendpoint]

/-- The source trace-log relative entropy of the unit state against the unit
reference is zero. -/
private theorem relativeEntropyPSDReferenceTraceLogE_unit_one_eq_zero :
    relativeEntropyPSDReferenceTraceLogE (MState.unit : MState PUnit.{1})
      (1 : CMatrix PUnit.{1}) Matrix.PosSemidef.one = (0 : EReal) := by
  have hSupport :
      Matrix.Supports (MState.unit.m : CMatrix PUnit.{1}) (1 : CMatrix PUnit.{1}) :=
    Matrix.Supports.of_right_posDef (MState.unit.m : CMatrix PUnit.{1})
      (1 : CMatrix PUnit.{1}) Matrix.PosDef.one
  rw [relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports
    (MState.unit : MState PUnit.{1}) Matrix.PosSemidef.one hSupport]
  congr 1
  have hUnitEntropy : (MState.unit : MState PUnit.{1}).vonNeumann = 0 :=
    MState.vonNeumann_punit_eq_zero _
  have hCompressedEntropy :
      (_root_.QIT.psdSupportCompressedState (MState.unit : MState PUnit.{1})
          Matrix.PosSemidef.one hSupport).vonNeumann = 0 := by
    have hEntropyEq :=
      @MState.vonNeumann_psdSupportCompressedState_eq PUnit.{1}
        inferInstance inferInstance (MState.unit : MState PUnit.{1})
        (1 : CMatrix PUnit.{1}) Matrix.PosSemidef.one hSupport
    rw [hEntropyEq]
    exact hUnitEntropy
  let f : ℝ → ℝ := fun x => if x = 0 then 0 else Real.log x
  have hTraceOriginal :
      (((MState.unit.m : CMatrix PUnit.{1}) * cfc f (1 : CMatrix PUnit.{1})).trace).re =
        0 := by
    simp [f]
  have hTraceCompressed := by
    have htrace :=
      @trace_mul_psdSupportLog_eq_trace_mul_cfc_logZero PUnit.{1}
        inferInstance inferInstance (MState.unit : MState PUnit.{1})
        (1 : CMatrix PUnit.{1}) Matrix.PosSemidef.one hSupport
    simpa [f, hTraceOriginal] using htrace
  simp [relativeEntropyPSDReferenceTraceLogFinite, hCompressedEntropy, hTraceCompressed]

/-- Source trace-log relative entropy is nonnegative for PSD references.

This singular-reference version follows from trace-log data processing to the
terminal one-outcome channel, so it keeps the source support convention rather
than imposing full-rank hypotheses. -/
theorem relativeEntropy_nonneg
    (rho sigma : MState a) :
    (0 : EReal) ≤
      rho.relativeEntropy sigma := by
  let Phi : CPTPMap a PUnit.{1} := terminalMeasureChannel a
  have hDPI :=
    relativeEntropy_dataProcessing_channel_ge rho sigma Phi
  have hOutState : Phi rho = MState.unit := by
    simpa [Phi] using terminalMeasureChannel_applyState rho
  have hOutSigma : Phi sigma = MState.unit := by
    simpa [Phi] using terminalMeasureChannel_applyState sigma
  have hOut :
      MState.relativeEntropy (Phi rho) (Phi sigma) =
        (0 : EReal) := by
    simpa [MState.relativeEntropy, hOutState, hOutSigma, MState.unit] using
      relativeEntropyPSDReferenceTraceLogE_unit_one_eq_zero
  simpa [hOut] using hDPI

/-- Support of `rho_AB` under `rho_A tensor sigma_B` descends to support of the
`B` marginal under `sigma_B`.

This is the singular-side-state support bridge needed for the
`inf_sigmaB` endpoint optimization in the Khatri--Wilde proof. -/
theorem traceLeft_supports_of_supports_prod_left_side
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hSupport :
      Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m) :
    Matrix.Supports rhoAB.traceLeft.m sigmaB.m := by
  have hOut :
      Matrix.Supports
        ((CPTPOp.traceOutLeft a b) rhoAB).m
        ((CPTPOp.traceOutLeft a b).map
          (rhoAB.traceRight.prod sigmaB).m) :=
    channel_applyState_supports_of_supports rhoAB
      (rhoAB.traceRight.prod sigmaB).psd
      (CPTPOp.traceOutLeft a b) hSupport
  rw [CPTPOp.traceOutLeft_applyState, CPTPOp.traceOutLeft_map,
    MState.traceLeft_prod] at hOut
  exact hOut

/-- The side-state trace-log relative entropy term in the Khatri--Wilde
endpoint optimization is nonnegative. -/
theorem relativeEntropyPSDReferenceTraceLogFinite_traceLeft_nonneg_of_supports
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hSupport :
      Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m) :
    0 ≤
      relativeEntropyPSDReferenceTraceLogFinite rhoAB.traceLeft sigmaB.m sigmaB.psd
        (rhoAB.traceLeft_supports_of_supports_prod_left_side sigmaB hSupport) := by
  let hSupportB : Matrix.Supports rhoAB.traceLeft.m sigmaB.m :=
    rhoAB.traceLeft_supports_of_supports_prod_left_side sigmaB hSupport
  have hE := relativeEntropy_nonneg rhoAB.traceLeft sigmaB
  rw [relativeEntropy_eq_coe_of_supports rhoAB.traceLeft sigmaB hSupportB] at hE
  simpa [hSupportB] using EReal.coe_le_coe_iff.mp hE

/-- If a matrix is supported on a nonnegative diagonal reference, every zero
reference coordinate has zero diagonal coefficient. -/
private theorem supports_diagonal_zero_entry
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : CMatrix ι} {d : ι → ℝ}
    (hSupport :
      Matrix.Supports M
        ((Matrix.diagonal fun i : ι => ((d i : ℂ))) : CMatrix ι))
    {i : ι} (hi : d i = 0) :
    M i i = 0 := by
  let D : CMatrix ι := Matrix.diagonal fun i : ι => ((d i : ℂ))
  let e : ι → ℂ := Pi.single i 1
  have hDiagVec :
      Matrix.mulVec D e = 0 := by
    ext k
    rw [Matrix.mulVec, dotProduct]
    by_cases hki : k = i
    · subst k
      rw [Finset.sum_eq_single i]
      · simp [D, e, Matrix.diagonal, hi]
      · intro j _ hj
        simp [D, e, Matrix.diagonal, hj]
      · intro hi_not
        simp at hi_not
    · rw [Finset.sum_eq_single i]
      · simp [D, e, Matrix.diagonal, hki]
      · intro j _ hj
        simp [D, e, Matrix.diagonal, hj]
      · intro hi_not
        simp at hi_not
  have hMVec := hSupport e hDiagVec
  have hEntry := congrFun hMVec i
  rw [Matrix.mulVec, dotProduct] at hEntry
  have hSum : (∑ j, M i j * e j) = M i i := by
    rw [Finset.sum_eq_single i]
    · simp [e]
    · intro j _ hj
      simp [e, hj]
    · intro hi_not
      simp at hi_not
  simpa [hSum] using hEntry

/-- Product eigenbasis for `rho_A tensor sigma_B`, where the right reference is
an arbitrary side state rather than the actual `B` marginal. -/
private def productLeftReferenceEigenvectorUnitary
    (rhoA : MState a) (sigmaB : MState b) : Matrix.unitaryGroup (a × b) ℂ :=
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoA.psd.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ :=
    sigmaB.psd.isHermitian.eigenvectorUnitary
  ⟨Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b),
    Matrix.kronecker_mem_unitary UA.2 UB.2⟩

/-- The product reference `rho_A tensor sigma_B` is diagonal in the tensor
product of the two single-system eigenbases. -/
private theorem productLeftReference_matrix_eq_productEigenbasis_diagonal
    (rhoA : MState a) (sigmaB : MState b) :
    (rhoA.prod sigmaB).m =
      (productLeftReferenceEigenvectorUnitary rhoA sigmaB : CMatrix (a × b)) *
        Matrix.diagonal
          (fun y : a × b =>
            (((BinaryHypothesisTest.stateSpectralWeight rhoA y.1 *
                BinaryHypothesisTest.stateSpectralWeight sigmaB y.2 : NNReal) : ℝ) : ℂ)) *
        star (productLeftReferenceEigenvectorUnitary rhoA sigmaB : CMatrix (a × b)) := by
  classical
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoA.psd.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ :=
    sigmaB.psd.isHermitian.eigenvectorUnitary
  have hA :
      rhoA.m =
        (UA : CMatrix a) *
          Matrix.diagonal
            (fun x : a =>
              (((BinaryHypothesisTest.stateSpectralWeight rhoA x : NNReal) : ℝ) : ℂ)) *
          star (UA : CMatrix a) := by
    simpa [UA, BinaryHypothesisTest.coe_stateSpectralWeight, Function.comp_def,
      Unitary.conjStarAlgAut_apply] using rhoA.psd.isHermitian.spectral_theorem
  have hB :
      sigmaB.m =
        (UB : CMatrix b) *
          Matrix.diagonal
            (fun y : b =>
              (((BinaryHypothesisTest.stateSpectralWeight sigmaB y : NNReal) : ℝ) : ℂ)) *
          star (UB : CMatrix b) := by
    simpa [UB, BinaryHypothesisTest.coe_stateSpectralWeight, Function.comp_def,
      Unitary.conjStarAlgAut_apply] using sigmaB.psd.isHermitian.spectral_theorem
  rw [MState.prod_m, hA, hB]
  simp [productLeftReferenceEigenvectorUnitary, UA, UB,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal,
    Matrix.mul_assoc]

/-- In the product eigenbasis for `rho_A tensor sigma_B`, the support
hypothesis forces `rho_AB` to have zero diagonal coefficient at zero product
reference eigenvalues. -/
private theorem productLeftReference_support_diagonal_coeff_zero
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hSupport :
      Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m) :
    let U : Matrix.unitaryGroup (a × b) ℂ :=
      productLeftReferenceEigenvectorUnitary rhoAB.traceRight sigmaB
    let M : CMatrix (a × b) := star (U : CMatrix (a × b)) * rhoAB.m * U
    let d : a × b → ℝ := fun y =>
      ((BinaryHypothesisTest.stateSpectralWeight rhoAB.traceRight y.1 *
        BinaryHypothesisTest.stateSpectralWeight sigmaB y.2 : NNReal) : ℝ)
    ∀ y : a × b, d y = 0 → M y y = 0 := by
  classical
  intro U M d y hy
  let D : CMatrix (a × b) := Matrix.diagonal fun y : a × b => ((d y : ℂ))
  let Uinv : Matrix.unitaryGroup (a × b) ℂ := U⁻¹
  have hRefSpec :=
    productLeftReference_matrix_eq_productEigenbasis_diagonal rhoAB.traceRight sigmaB
  have hRefDiag :
      (Uinv : CMatrix (a × b)) * (rhoAB.traceRight.prod sigmaB).m *
      star (Uinv : CMatrix (a × b)) =
        D := by
    have hUinv : (Uinv : CMatrix (a × b)) = star (U : CMatrix (a × b)) := by
      rfl
    rw [hUinv, star_star, hRefSpec]
    have hUU : star (U : CMatrix (a × b)) * (U : CMatrix (a × b)) = 1 :=
      Unitary.coe_star_mul_self U
    calc
      star (U : CMatrix (a × b)) *
            ((U : CMatrix (a × b)) * D * star (U : CMatrix (a × b))) *
          (U : CMatrix (a × b)) =
          (star (U : CMatrix (a × b)) * (U : CMatrix (a × b))) *
            D * (star (U : CMatrix (a × b)) * (U : CMatrix (a × b))) := by
            noncomm_ring
      _ = D := by
            rw [hUU]
            simp
  have hSupportBasis :
      Matrix.Supports M D := by
    have hconj := Matrix.Supports.unitary_conj hSupport Uinv
    rw [hRefDiag] at hconj
    simpa [M, Uinv] using hconj
  exact supports_diagonal_zero_entry hSupportBasis hy

/-- Summing the product-reference diagonal coefficients over `B` recovers the
spectral weight of the actual `A` marginal. -/
private theorem productLeftReference_diag_fst_sum
    (rhoAB : MState (a × b)) (sigmaB : MState b) (i : a) :
    let U : Matrix.unitaryGroup (a × b) ℂ :=
      productLeftReferenceEigenvectorUnitary rhoAB.traceRight sigmaB
    let M : CMatrix (a × b) := star (U : CMatrix (a × b)) * rhoAB.m * U
    ∑ j : b, (M (i, j) (i, j)).re =
      ((BinaryHypothesisTest.stateSpectralWeight rhoAB.traceRight i : NNReal) : ℝ) := by
  classical
  intro U M
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoAB.traceRight.psd.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ :=
    sigmaB.psd.isHermitian.eigenvectorUnitary
  have hU :
      (U : CMatrix (a × b)) = Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b) := by
    rfl
  have hptM :
      Matrix.traceRight M =
        star (UA : CMatrix a) * rhoAB.traceRight.m * (UA : CMatrix a) := by
    have hpt := traceRight_local_unitary_conj (a := a) (b := b) rhoAB.m UA UB
    simpa [M, U, hU, MState.traceRight_m] using hpt
  have hdiag :
      star (UA : CMatrix a) * rhoAB.traceRight.m * (UA : CMatrix a) =
        Matrix.diagonal
          (fun k : a =>
            (((BinaryHypothesisTest.stateSpectralWeight rhoAB.traceRight k : NNReal)
              : ℝ) : ℂ)) := by
    have hspec := rhoAB.traceRight.psd.isHermitian.spectral_theorem
    have hA :
        rhoAB.traceRight.m =
          (UA : CMatrix a) *
            Matrix.diagonal
              (fun k : a =>
                (((BinaryHypothesisTest.stateSpectralWeight rhoAB.traceRight k : NNReal)
                  : ℝ) : ℂ)) *
            star (UA : CMatrix a) := by
      simpa [UA, BinaryHypothesisTest.coe_stateSpectralWeight, Function.comp_def,
        Unitary.conjStarAlgAut_apply] using hspec
    calc
      star (UA : CMatrix a) * rhoAB.traceRight.m * (UA : CMatrix a)
          = star (UA : CMatrix a) *
              ((UA : CMatrix a) *
                Matrix.diagonal
                  (fun k : a =>
                    (((BinaryHypothesisTest.stateSpectralWeight rhoAB.traceRight k : NNReal)
                      : ℝ) : ℂ)) *
                star (UA : CMatrix a)) *
              (UA : CMatrix a) := by
                rw [hA]
      _ = (star (UA : CMatrix a) * (UA : CMatrix a)) *
            Matrix.diagonal
              (fun k : a =>
                (((BinaryHypothesisTest.stateSpectralWeight rhoAB.traceRight k : NNReal)
                  : ℝ) : ℂ)) *
            (star (UA : CMatrix a) * (UA : CMatrix a)) := by
              noncomm_ring
      _ = Matrix.diagonal
            (fun k : a =>
              (((BinaryHypothesisTest.stateSpectralWeight rhoAB.traceRight k : NNReal)
                : ℝ) : ℂ)) := by
              rw [Unitary.coe_star_mul_self]
              simp
  have hentry :
      (Matrix.traceRight M) i i =
        (Matrix.diagonal
          (fun k : a =>
            (((BinaryHypothesisTest.stateSpectralWeight rhoAB.traceRight k : NNReal)
              : ℝ) : ℂ)) : CMatrix a) i i := by
    rw [hptM, hdiag]
  have hre := congrArg Complex.re hentry
  simpa [Matrix.traceRight, Matrix.diagonal, M] using hre

/-- Summing the product-reference diagonal coefficients over `A` recovers the
`B` marginal diagonal in the side-reference eigenbasis. -/
private theorem productLeftReference_diag_snd_sum
    (rhoAB : MState (a × b)) (sigmaB : MState b) (j : b) :
    let U : Matrix.unitaryGroup (a × b) ℂ :=
      productLeftReferenceEigenvectorUnitary rhoAB.traceRight sigmaB
    let M : CMatrix (a × b) := star (U : CMatrix (a × b)) * rhoAB.m * U
    let UB : Matrix.unitaryGroup b ℂ :=
      sigmaB.psd.isHermitian.eigenvectorUnitary
    ∑ i : a, (M (i, j) (i, j)).re =
      ((star (UB : CMatrix b) * rhoAB.traceLeft.m * (UB : CMatrix b)) j j).re := by
  classical
  intro U M UB
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoAB.traceRight.psd.isHermitian.eigenvectorUnitary
  have hU :
      (U : CMatrix (a × b)) = Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b) := by
    rfl
  have hptM :
      Matrix.traceLeft M =
        star (UB : CMatrix b) * rhoAB.traceLeft.m * (UB : CMatrix b) := by
    have hpt := traceLeft_local_unitary_conj (a := a) (b := b) rhoAB.m UA UB
    simpa [M, U, hU, MState.traceLeft_m] using hpt
  have hentry :=
    congrFun (congrFun hptM j) j
  have hre := congrArg Complex.re hentry
  simpa [Matrix.traceLeft, M] using hre

/-- Trace-log split for an arbitrary side reference:
`Tr rho_AB log(rho_A tensor sigma_B)` is the sum of the `A` marginal entropy
trace and the `B` marginal trace against `log sigma_B`, with the source support
convention handling zero product eigenvalues. -/
private theorem trace_mul_cfc_logZero_prod_leftReference_eq
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hSupport :
      Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m) :
    let f : ℝ → ℝ := fun x => if x = 0 then 0 else Real.log x
    ((rhoAB.m * cfc f (rhoAB.traceRight.prod sigmaB).m).trace).re /
        Real.log 2 =
      -rhoAB.traceRight.vonNeumann +
        ((rhoAB.traceLeft.m * cfc f sigmaB.m).trace).re / Real.log 2 := by
  classical
  intro f
  let U : Matrix.unitaryGroup (a × b) ℂ :=
    productLeftReferenceEigenvectorUnitary rhoAB.traceRight sigmaB
  let M : CMatrix (a × b) := star (U : CMatrix (a × b)) * rhoAB.m * U
  let UB : Matrix.unitaryGroup b ℂ :=
    sigmaB.psd.isHermitian.eigenvectorUnitary
  let coeff : a × b → ℝ := fun y => (M y y).re
  let coeffB : b → ℝ := fun j =>
    ((star (UB : CMatrix b) * rhoAB.traceLeft.m * (UB : CMatrix b)) j j).re
  let muA : a → ℝ := fun i =>
    ((BinaryHypothesisTest.stateSpectralWeight rhoAB.traceRight i : NNReal) : ℝ)
  let nuB : b → ℝ := fun j =>
    ((BinaryHypothesisTest.stateSpectralWeight sigmaB j : NNReal) : ℝ)
  let d : a × b → ℝ := fun y => muA y.1 * nuB y.2
  have hmuA_nonneg : ∀ i, 0 ≤ muA i := by
    intro i
    exact NNReal.coe_nonneg _
  have hnuB_nonneg : ∀ j, 0 ≤ nuB j := by
    intro j
    exact NNReal.coe_nonneg _
  have hRefSpec :
      (rhoAB.traceRight.prod sigmaB).m =
        (U : CMatrix (a × b)) *
          Matrix.diagonal (fun y : a × b => ((d y : ℂ))) *
          star (U : CMatrix (a × b)) := by
    simpa [U, d, muA, nuB, NNReal.coe_mul] using
      productLeftReference_matrix_eq_productEigenbasis_diagonal rhoAB.traceRight sigmaB
  have hlogRef :
      cfc f (rhoAB.traceRight.prod sigmaB).m =
        (U : CMatrix (a × b)) *
          Matrix.diagonal (fun y : a × b => ((f (d y) : ℂ))) *
          star (U : CMatrix (a × b)) := by
    rw [hRefSpec]
    exact cfc_unitary_conj_diagonal_ofReal U d f
  have htraceAB :
      ((rhoAB.m * cfc f (rhoAB.traceRight.prod sigmaB).m).trace).re =
        ∑ y : a × b, coeff y * f (d y) := by
    rw [hlogRef]
    simpa [coeff, M, U] using
      Matrix.trace_mul_unitary_conj_diagonal_right_re U rhoAB.m (fun y => f (d y))
  have hcoeff_zero : ∀ y : a × b, d y = 0 → coeff y = 0 := by
    intro y hy
    have hMzero :=
      productLeftReference_support_diagonal_coeff_zero rhoAB sigmaB hSupport y
    exact congrArg Complex.re (hMzero hy)
  have hsplit_pointwise :
      ∀ y : a × b,
        coeff y * f (d y) = coeff y * f (muA y.1) + coeff y * f (nuB y.2) := by
    intro y
    by_cases hyd : d y = 0
    · have hc : coeff y = 0 := hcoeff_zero y hyd
      simp [hc]
    · have hmu_pos : 0 < muA y.1 := by
        have hmul : muA y.1 * nuB y.2 ≠ 0 := by
          simpa [d] using hyd
        exact lt_of_le_of_ne (hmuA_nonneg y.1) (Ne.symm (mul_ne_zero_iff.mp hmul).1)
      have hnu_pos : 0 < nuB y.2 := by
        have hmul : muA y.1 * nuB y.2 ≠ 0 := by
          simpa [d] using hyd
        exact lt_of_le_of_ne (hnuB_nonneg y.2) (Ne.symm (mul_ne_zero_iff.mp hmul).2)
      have hd_pos : 0 < d y := by
        exact mul_pos hmu_pos hnu_pos
      simp [f, d, hyd, hmu_pos.ne', hnu_pos.ne',
        Real.log_mul hmu_pos.ne' hnu_pos.ne', mul_add]
  have hsumSplit :
      (∑ y : a × b, coeff y * f (d y)) =
        (∑ i : a, muA i * f (muA i)) +
          (∑ j : b, coeffB j * f (nuB j)) := by
    calc
      (∑ y : a × b, coeff y * f (d y)) =
          ∑ y : a × b, (coeff y * f (muA y.1) + coeff y * f (nuB y.2)) := by
            refine Finset.sum_congr rfl ?_
            intro y _hy
            exact hsplit_pointwise y
      _ = (∑ i : a, ∑ j : b, coeff (i, j) * f (muA i)) +
            (∑ i : a, ∑ j : b, coeff (i, j) * f (nuB j)) := by
            rw [Fintype.sum_prod_type]
            simp [Finset.sum_add_distrib]
      _ = (∑ i : a, (∑ j : b, coeff (i, j)) * f (muA i)) +
            (∑ j : b, (∑ i : a, coeff (i, j)) * f (nuB j)) := by
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro i _hi
              simp [Finset.sum_mul]
            · rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro j _hj
              simp [Finset.sum_mul]
      _ = (∑ i : a, muA i * f (muA i)) +
            (∑ j : b, coeffB j * f (nuB j)) := by
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro i _hi
              have hfst := productLeftReference_diag_fst_sum rhoAB sigmaB i
              simpa [U, M, coeff, muA] using congrArg (fun x => x * f (muA i)) hfst
            · refine Finset.sum_congr rfl ?_
              intro j _hj
              have hsnd := productLeftReference_diag_snd_sum rhoAB sigmaB j
              simpa [U, M, UB, coeff, coeffB] using
                congrArg (fun x => x * f (nuB j)) hsnd
  have hAterm :
      (∑ i : a, muA i * f (muA i)) / Real.log 2 =
        -rhoAB.traceRight.vonNeumann := by
    have hpoint : ∀ i : a, muA i * f (muA i) = muA i * Real.log (muA i) := by
      intro i
      by_cases hi : muA i = 0
      · simp [f, hi]
      · simp [f, hi]
    have hsum :
        (∑ i : a, muA i * f (muA i)) =
          ∑ i : a, muA i * Real.log (muA i) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      exact hpoint i
    rw [hsum]
    simpa [muA] using
      MState.spectralWeight_mul_log_div_log_two_eq_neg_vonNeumann rhoAB.traceRight
  have hSigmaSpec :
      sigmaB.m =
        (UB : CMatrix b) *
          Matrix.diagonal (fun j : b => ((nuB j : ℂ))) *
          star (UB : CMatrix b) := by
    simpa [UB, nuB, BinaryHypothesisTest.coe_stateSpectralWeight, Function.comp_def,
      Unitary.conjStarAlgAut_apply] using sigmaB.psd.isHermitian.spectral_theorem
  have hlogSigma :
      cfc f sigmaB.m =
        (UB : CMatrix b) *
          Matrix.diagonal (fun j : b => ((f (nuB j) : ℂ))) *
          star (UB : CMatrix b) := by
    rw [hSigmaSpec]
    exact cfc_unitary_conj_diagonal_ofReal UB nuB f
  have hTraceB :
      ((rhoAB.traceLeft.m * cfc f sigmaB.m).trace).re =
        ∑ j : b, coeffB j * f (nuB j) := by
    rw [hlogSigma]
    simpa [coeffB, UB] using
      Matrix.trace_mul_unitary_conj_diagonal_right_re UB rhoAB.traceLeft.m
        (fun j => f (nuB j))
  calc
    ((rhoAB.m * cfc f (rhoAB.traceRight.prod sigmaB).m).trace).re /
        Real.log 2 =
        (∑ y : a × b, coeff y * f (d y)) / Real.log 2 := by
          rw [htraceAB]
    _ = ((∑ i : a, muA i * f (muA i)) +
          (∑ j : b, coeffB j * f (nuB j))) / Real.log 2 := by
          rw [hsumSplit]
    _ = (∑ i : a, muA i * f (muA i)) / Real.log 2 +
          (∑ j : b, coeffB j * f (nuB j)) / Real.log 2 := by
          field_simp [ne_of_gt (Real.log_pos one_lt_two)]
    _ = -rhoAB.traceRight.vonNeumann +
          ((rhoAB.traceLeft.m * cfc f sigmaB.m).trace).re / Real.log 2 := by
          rw [hAterm, hTraceB]

/-- Finite trace-log chain rule for the arbitrary side reference:
`D(rho_AB || rho_A tensor sigma_B) = I(A;B)_rho + D(rho_B || sigma_B)`. -/
theorem relativeEntropyPSDReferenceTraceLogFinite_prod_leftReference_eq_mutualInformation_add
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hSupport :
      Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m) :
    let hSupportB : Matrix.Supports rhoAB.traceLeft.m sigmaB.m :=
      rhoAB.traceLeft_supports_of_supports_prod_left_side sigmaB hSupport
    relativeEntropyPSDReferenceTraceLogFinite rhoAB
        (rhoAB.traceRight.prod sigmaB).m
        (rhoAB.traceRight.prod sigmaB).psd hSupport =
      mutualInformation rhoAB +
        relativeEntropyPSDReferenceTraceLogFinite rhoAB.traceLeft
          sigmaB.m sigmaB.psd hSupportB := by
  classical
  intro hSupportB
  let sigmaAB : MState (a × b) := rhoAB.traceRight.prod sigmaB
  let f : ℝ → ℝ := fun x => if x = 0 then 0 else Real.log x
  have hEntropyAB :
      (_root_.QIT.psdSupportCompressedState rhoAB sigmaAB.psd hSupport).vonNeumann =
        rhoAB.vonNeumann :=
    MState.vonNeumann_psdSupportCompressedState_eq rhoAB sigmaAB.psd hSupport
  have hEntropyB :
      (_root_.QIT.psdSupportCompressedState rhoAB.traceLeft sigmaB.psd hSupportB).vonNeumann =
        rhoAB.traceLeft.vonNeumann :=
    MState.vonNeumann_psdSupportCompressedState_eq rhoAB.traceLeft sigmaB.psd hSupportB
  have hTraceAB :
      ((psdSupportCompress sigmaAB.m sigmaAB.psd rhoAB.m *
        MState.psdLog (psdSupportCompress sigmaAB.m sigmaAB.psd sigmaAB.m)
          (psdSupportCompress_self_posDef sigmaAB.m sigmaAB.psd)).trace).re =
        ((rhoAB.m * cfc f sigmaAB.m).trace).re := by
    simpa [f, sigmaAB] using
      trace_mul_psdSupportLog_eq_trace_mul_cfc_logZero rhoAB sigmaAB.psd hSupport
  have hTraceB :
      ((psdSupportCompress sigmaB.m sigmaB.psd rhoAB.traceLeft.m *
        MState.psdLog (psdSupportCompress sigmaB.m sigmaB.psd sigmaB.m)
          (psdSupportCompress_self_posDef sigmaB.m sigmaB.psd)).trace).re =
        ((rhoAB.traceLeft.m * cfc f sigmaB.m).trace).re := by
    simpa [f] using
      trace_mul_psdSupportLog_eq_trace_mul_cfc_logZero rhoAB.traceLeft
        sigmaB.psd hSupportB
  have hSplit :
      ((psdSupportCompress sigmaAB.m sigmaAB.psd rhoAB.m *
        MState.psdLog (psdSupportCompress sigmaAB.m sigmaAB.psd sigmaAB.m)
          (psdSupportCompress_self_posDef sigmaAB.m sigmaAB.psd)).trace).re /
          Real.log 2 =
        -rhoAB.traceRight.vonNeumann +
          ((psdSupportCompress sigmaB.m sigmaB.psd rhoAB.traceLeft.m *
            MState.psdLog (psdSupportCompress sigmaB.m sigmaB.psd sigmaB.m)
              (psdSupportCompress_self_posDef sigmaB.m sigmaB.psd)).trace).re /
            Real.log 2 := by
    rw [hTraceAB, hTraceB]
    simpa [f, sigmaAB] using
      trace_mul_cfc_logZero_prod_leftReference_eq rhoAB sigmaB hSupport
  simp [relativeEntropyPSDReferenceTraceLogFinite, sigmaAB, hEntropyAB, hEntropyB,
    hSplit, mutualInformation]
  ring_nf

/-- The finite trace-log branch of every supported side-information candidate
dominates the ordinary mutual information. -/
theorem relativeEntropyPSDReferenceTraceLogFinite_prod_leftReference_lower_mutualInformation
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hSupport :
      Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m) :
    (mutualInformation rhoAB : EReal) ≤
      (relativeEntropyPSDReferenceTraceLogFinite rhoAB
        (rhoAB.traceRight.prod sigmaB).m
        (rhoAB.traceRight.prod sigmaB).psd hSupport : EReal) := by
  have hEq :=
    relativeEntropyPSDReferenceTraceLogFinite_prod_leftReference_eq_mutualInformation_add
      rhoAB sigmaB hSupport
  have hNonneg :=
    relativeEntropyPSDReferenceTraceLogFinite_traceLeft_nonneg_of_supports
      rhoAB sigmaB hSupport
  have hreal :
      mutualInformation rhoAB ≤
        relativeEntropyPSDReferenceTraceLogFinite rhoAB
          (rhoAB.traceRight.prod sigmaB).m
          (rhoAB.traceRight.prod sigmaB).psd hSupport := by
    rw [hEq]
    linarith
  exact EReal.coe_le_coe_iff.mpr hreal

/-- Per-side-state lower bound on the PSD-reference relative entropy endpoint,
handling both supported and unsupported references uniformly.

This is the pointwise `sigmaB` input to the Khatri--Wilde relative-entropy
inf-optimizer: for every side state, the endpoint
`D(rho_AB || rho_A \otimes sigma_B)` dominates the ordinary mutual information,
trivially so on the unsupported branch where the endpoint is `+infty`. -/
theorem relativeEntropyPSDReferenceE_prod_leftReference_lower_mutualInformation
    (rhoAB : MState (a × b)) (sigmaB : MState b) :
    (mutualInformation rhoAB : EReal) ≤
      relativeEntropyPSDReferenceE rhoAB
        (rhoAB.traceRight.prod sigmaB).m
        (rhoAB.traceRight.prod sigmaB).psd := by
  by_cases hSupport : Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m
  · exact
      rhoAB.sandwichedRenyiMutualInformationCandidateEndpoint_lower_of_traceLogFinite_lower
        sigmaB hSupport
        (relativeEntropyPSDReferenceTraceLogFinite_prod_leftReference_lower_mutualInformation
          rhoAB sigmaB hSupport)
  · exact
      rhoAB.sandwichedRenyiMutualInformationCandidateEndpoint_lower_of_not_supports
        sigmaB hSupport

/-- Khatri--Wilde relative-entropy inf-optimizer across the `B` cut.

This is the source step `inf_{sigma_B} D(rho_{RB} || rho_R \otimes sigma_B) =
D(rho_{RB} || rho_R \otimes rho_B)` from
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:1869-1907].  The
minimizer is `sigma_B = rho_B` itself: the lower bound
`D(rho || rho_R \otimes sigma_B) \geq D(rho || rho_R \otimes rho_B)` is exactly
the chain-rule decomposition
`D(rho || rho_R \otimes sigma_B) = I(R;B)_rho + D(rho_B || sigma_B)`, and the
upper bound is achieved at `sigma_B = rho_B`.  The chain-rule ingredients are
the per-side-state endpoint lower bound
`relativeEntropyPSDReferenceE_prod_leftReference_lower_mutualInformation` and
the product-marginal endpoint identification
`relativeEntropy_prod_marginals_eq_mutualInformation`. -/
theorem relativeEntropyPSDReferenceE_prod_leftReference_iInf_eq_mutualInformation
    (rhoAB : MState (a × b)) :
    (⨅ sigmaB : MState b,
        relativeEntropyPSDReferenceE rhoAB
          (rhoAB.traceRight.prod sigmaB).m
          (rhoAB.traceRight.prod sigmaB).psd) =
      (mutualInformation rhoAB : EReal) := by
  classical
  have : Nonempty b := by
    rcases rhoAB.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  refine le_antisymm ?_ ?_
  · refine le_trans
        ((iInf_le fun sigmaB : MState b =>
            relativeEntropyPSDReferenceE rhoAB
              (rhoAB.traceRight.prod sigmaB).m
              (rhoAB.traceRight.prod sigmaB).psd) rhoAB.traceLeft) ?_
    have hEndpoint :
        relativeEntropyPSDReferenceE rhoAB
            (rhoAB.traceRight.prod rhoAB.traceLeft).m
            (rhoAB.traceRight.prod rhoAB.traceLeft).psd =
          (mutualInformation rhoAB : EReal) := by
      calc
        relativeEntropyPSDReferenceE rhoAB
            (rhoAB.traceRight.prod rhoAB.traceLeft).m
            (rhoAB.traceRight.prod rhoAB.traceLeft).psd =
            rhoAB.relativeEntropy (rhoAB.traceRight.prod rhoAB.traceLeft) := by
              rw [relativeEntropyPSDReferenceE_eq_traceLogE]
              rfl
        _ = (mutualInformation rhoAB : EReal) :=
              rhoAB.relativeEntropy_prod_marginals_eq_mutualInformation
    exact hEndpoint.le
  · refine le_iInf fun sigmaB => ?_
    exact
      rhoAB.relativeEntropyPSDReferenceE_prod_leftReference_lower_mutualInformation
        sigmaB

/-- Unconditional per-candidate `alpha`-monotonicity of the sandwiched-Renyi
mutual-information candidate.

This is the Bridge A input needed by the Bridge C state-level assembly:
`Bridge A`'s `sandwichedRenyiPSDReferenceHighAlphaFinite_mono_posSemidef_state_posDef_reference`
(Monotonicity:1731) discharges the support-compress hypothesis of
`sandwichedRenyiMutualInformationCandidateE_mono_of_supportCompress_mono`
(Monotonicity:919) on the positive spectral support of every side-information
reference `rho_A \ot sigma_B`, since on that compressed space the reference is
positive definite (`psdSupportCompress_self_posDef`) and the state is PSD.
Faithful to KW `entropies.tex:2347-2372`. -/
theorem sandwichedRenyiMutualInformationCandidateE_mono
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (alpha beta : {alpha : ℝ // 1 < alpha}) (hab : alpha.1 ≤ beta.1) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1 ≤
      rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB beta.1 := by
  refine
    rhoAB.sandwichedRenyiMutualInformationCandidateE_mono_of_supportCompress_mono
      sigmaB hab ?_
  intro hSupport
  exact
    sandwichedRenyiPSDReferenceHighAlphaFinite_mono_posSemidef_state_posDef_reference
      (psdSupportCompressedState rhoAB (rhoAB.traceRight.prod sigmaB).psd hSupport)
      (psdSupportCompress_self_posDef _ (rhoAB.traceRight.prod sigmaB).psd)
      alpha.2 beta.2 hab

/-- Fixed-`sigma_B` infimum over `alpha > 1` of the sandwiched-Renyi
mutual-information candidate equals the PSD-reference relative entropy
endpoint.

This is Bridge C step 2 (the pointwise `alpha → 1+` limit at fixed reference,
converted to an `inf_alpha` endpoint via the per-candidate monotonicity above).
The order-topology handoff
`tendsto_relativeEntropyHighAlphaRightToOne_iInf_of_monotone` converts the
source right-neighbourhood limit
`sandwichedRenyiMutualInformationCandidateE_tendsto_relativeEntropyPSDReferenceE`
(Limit:569) into the `inf_alpha` equality once the candidate curve is known to
be monotone in `alpha`. -/
theorem sandwichedRenyiMutualInformationCandidateE_iInf_eq_relativeEntropyPSDReferenceE
    (rhoAB : MState (a × b)) (sigmaB : MState b) :
    (⨅ alpha : {alpha : ℝ // 1 < alpha},
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1) =
      relativeEntropyPSDReferenceE rhoAB
        (rhoAB.traceRight.prod sigmaB).m
        (rhoAB.traceRight.prod sigmaB).psd := by
  have hmono :
      ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1 ≤
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB beta.1 :=
    fun alpha beta hab =>
      rhoAB.sandwichedRenyiMutualInformationCandidateE_mono sigmaB alpha beta hab
  have hlimInf :
      Tendsto
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
          rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds
          (⨅ alpha : {alpha : ℝ // 1 < alpha},
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1)) :=
    tendsto_relativeEntropyHighAlphaRightToOne_iInf_of_monotone hmono
  have hlimMI :
      Tendsto
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
          rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds
          (relativeEntropyPSDReferenceE rhoAB
            (rhoAB.traceRight.prod sigmaB).m
            (rhoAB.traceRight.prod sigmaB).psd)) :=
    rhoAB.sandwichedRenyiMutualInformationCandidateE_tendsto_relativeEntropyPSDReferenceE
      sigmaB
  have : Filter.NeBot relativeEntropyHighAlphaRightToOne :=
    relativeEntropyHighAlphaRightToOne_neBot
  exact tendsto_nhds_unique hlimInf hlimMI

/-- Khatri--Wilde state-level `inf_alpha` endpoint via the Bridge C route.

This is the source-faithful assembly
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:1869-1907]:

1. `inf_alpha inf_sigmaB = inf_sigmaB inf_alpha` (free `iInf_comm` over the
   independent index sets);
2. `inf_alpha D~_alpha(rho || rho_A \ot sigma_B) = D(rho || rho_A \ot sigma_B)`
   for every fixed `sigma_B` (Bridge C step 2, the per-candidate
   `inf_alpha`/right-limit handoff via Bridge A monotonicity);
3. `inf_sigma_B D(rho || rho_A \ot sigma_B) = D(rho || rho_A \ot rho_B)`
   (Bridge C step 3, the relative-entropy inf-optimizer
   `relativeEntropyPSDReferenceE_prod_leftReference_iInf_eq_mutualInformation`).

The conclusion is the optimized `inf_alpha inf_sigmaB` value: the ordinary
mutual information. -/
theorem sandwichedRenyiMutualInformationE_iInf_eq_mutualInformation
    (rhoAB : MState (a × b)) :
    (⨅ alpha : {alpha : ℝ // 1 < alpha},
        rhoAB.sandwichedRenyiMutualInformationE alpha.1) =
      (mutualInformation rhoAB : EReal) := by
  classical
  have : Nonempty b := by
    rcases rhoAB.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  -- Bridge C step 1: free `iInf_comm` over the independent index sets.
  have hswap :
      (⨅ alpha : {alpha : ℝ // 1 < alpha},
          ⨅ sigmaB : MState b,
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1) =
        (⨅ sigmaB : MState b,
          ⨅ alpha : {alpha : ℝ // 1 < alpha},
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1) :=
    iInf_comm
  -- Bridge C step 2: per-candidate inf_alpha endpoint.
  have hper : ∀ sigmaB : MState b,
      (⨅ alpha : {alpha : ℝ // 1 < alpha},
          rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1) =
        relativeEntropyPSDReferenceE rhoAB
          (rhoAB.traceRight.prod sigmaB).m
          (rhoAB.traceRight.prod sigmaB).psd :=
    fun sigmaB =>
      rhoAB.sandwichedRenyiMutualInformationCandidateE_iInf_eq_relativeEntropyPSDReferenceE
        sigmaB
  -- Bridge C step 3: rel-entropy inf-optimizer.
  have hopt :
      (⨅ sigmaB : MState b,
          relativeEntropyPSDReferenceE rhoAB
            (rhoAB.traceRight.prod sigmaB).m
            (rhoAB.traceRight.prod sigmaB).psd) =
        (mutualInformation rhoAB : EReal) :=
    rhoAB.relativeEntropyPSDReferenceE_prod_leftReference_iInf_eq_mutualInformation
  -- Assemble via the iInf equality `inf_alpha E = inf_alpha inf_sigmaB candidate`.
  -- Bridge C step 1: free `iInf_comm` over the independent index sets;
  -- step 2 (per-candidate `inf_alpha` endpoint via Bridge A monotonicity);
  -- step 3 (rel-entropy inf-optimizer at `sigma_B = rho_B`).
  rw [iInf_congr fun alpha : {alpha : ℝ // 1 < alpha} =>
        rhoAB.sandwichedRenyiMutualInformationE_eq_iInf alpha.1,
    hswap, iInf_congr hper]
  exact hopt

/-- Unconditional state-level `alpha → 1+` tendsto of the optimized
sandwiched-Renyi mutual information to ordinary mutual information.

This is the Bridge C deliverable, feeding `hState` of the channel-level
`sandwichedRenyiMutualInformationE_iInf_eq_information_of_mosonyi_hiai`
(Limit:2470). The tendsto follows from the Bridge C `inf_alpha` endpoint above
combined with the optimized `alpha`-monotonicity (Bridge A's
`MState.sandwichedRenyiMutualInformationE_mono`): a monotone high-`alpha` curve
tends to its `inf_alpha` value along the right-neighbourhood filter, and the
Bridge C `inf_alpha` value is exactly the ordinary mutual information. -/
theorem sandwichedRenyiMutualInformationE_tendsto_mutualInformation
    (rhoAB : MState (a × b)) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        rhoAB.sandwichedRenyiMutualInformationE alpha.1)
      relativeEntropyHighAlphaRightToOne
      (nhds (mutualInformation rhoAB : EReal)) := by
  have hstateMono :
      ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          rhoAB.sandwichedRenyiMutualInformationE alpha.1 ≤
            rhoAB.sandwichedRenyiMutualInformationE beta.1 :=
    fun alpha beta hab => rhoAB.sandwichedRenyiMutualInformationE_mono alpha beta hab
  have hlimInf :
      Tendsto
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
          rhoAB.sandwichedRenyiMutualInformationE alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds
          (⨅ alpha : {alpha : ℝ // 1 < alpha},
            rhoAB.sandwichedRenyiMutualInformationE alpha.1)) :=
    tendsto_relativeEntropyHighAlphaRightToOne_iInf_of_monotone hstateMono
  have hiInf :
      (⨅ alpha : {alpha : ℝ // 1 < alpha},
          rhoAB.sandwichedRenyiMutualInformationE alpha.1) =
        (mutualInformation rhoAB : EReal) :=
    rhoAB.sandwichedRenyiMutualInformationE_iInf_eq_mutualInformation
  rw [hiInf] at hlimInf
  exact hlimInf

/-- MState-level optimized `inf_sigmaB` alpha-to-one theorem with the actual
PSD-reference endpoint for every side-information candidate.

The fixed-candidate convergence is proved above.  The remaining mathematical
inputs are the source endpoint lower bound
`I(A;B)_rho ≤ D(rhoAB || rhoA \otimes sigmaB)` and high-`alpha` monotonicity
of each fixed sandwiched-Renyi candidate. -/
theorem sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_endpoint_lower_and_monotone
    (rhoAB : MState (a × b))
    (hlower :
      ∀ sigmaB : MState b,
        (mutualInformation rhoAB : EReal) ≤
          relativeEntropyPSDReferenceE rhoAB
            (rhoAB.traceRight.prod sigmaB).m
            (rhoAB.traceRight.prod sigmaB).psd)
    (hmono :
      ∀ sigmaB : MState b, ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1 ≤
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB beta.1) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        rhoAB.sandwichedRenyiMutualInformationE alpha.1)
      relativeEntropyHighAlphaRightToOne
      (nhds (mutualInformation rhoAB : EReal)) := by
  refine
    rhoAB.sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_candidate_limits
      ?_
  intro sigmaB
  refine
    ⟨relativeEntropyPSDReferenceE rhoAB
      (rhoAB.traceRight.prod sigmaB).m
      (rhoAB.traceRight.prod sigmaB).psd, ?_, ?_, ?_⟩
  · exact rhoAB.sandwichedRenyiMutualInformationCandidateE_tendsto_relativeEntropyPSDReferenceE
      sigmaB
  · exact hlower sigmaB
  · exact hmono sigmaB

/-- MState-level optimized `inf_sigmaB` alpha-to-one theorem after discharging
the unsupported side-information branch.

The only lower-bound input left is the supported finite trace-log chain-rule
inequality; unsupported candidates are handled by the extended-real `top`
convention. -/
theorem sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_supported_traceLog_lower_and_monotone
    (rhoAB : MState (a × b))
    (hsupportedLower :
      ∀ sigmaB : MState b,
        ∀ hSupport : Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m,
          (mutualInformation rhoAB : EReal) ≤
            (relativeEntropyPSDReferenceTraceLogFinite rhoAB
              (rhoAB.traceRight.prod sigmaB).m
              (rhoAB.traceRight.prod sigmaB).psd hSupport : EReal))
    (hmono :
      ∀ sigmaB : MState b, ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1 ≤
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB beta.1) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        rhoAB.sandwichedRenyiMutualInformationE alpha.1)
      relativeEntropyHighAlphaRightToOne
      (nhds (mutualInformation rhoAB : EReal)) := by
  refine
    rhoAB.sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_endpoint_lower_and_monotone
      ?_ hmono
  intro sigmaB
  by_cases hSupport : Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m
  · exact
      rhoAB.sandwichedRenyiMutualInformationCandidateEndpoint_lower_of_traceLogFinite_lower
        sigmaB hSupport (hsupportedLower sigmaB hSupport)
  · exact
      rhoAB.sandwichedRenyiMutualInformationCandidateEndpoint_lower_of_not_supports
        sigmaB hSupport

/-- MState-level optimized `inf_sigmaB` alpha-to-one theorem after discharging
the source trace-log chain rule for all side-information candidates.

The only remaining mathematical input is the fixed-candidate sandwiched-Renyi
monotonicity in `alpha > 1`, matching the Khatri--Wilde use of
`prop-sand_rel_ent_properties` before the Mosonyi--Hiai channel minimax step. -/
theorem sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_chainRule_and_monotone
    (rhoAB : MState (a × b))
    (hmono :
      ∀ sigmaB : MState b, ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1 ≤
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB beta.1) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        rhoAB.sandwichedRenyiMutualInformationE alpha.1)
      relativeEntropyHighAlphaRightToOne
      (nhds (mutualInformation rhoAB : EReal)) := by
  refine
    rhoAB.sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_supported_traceLog_lower_and_monotone
      ?_ hmono
  intro sigmaB hSupport
  exact
    relativeEntropyPSDReferenceTraceLogFinite_prod_leftReference_lower_mutualInformation
      rhoAB sigmaB hSupport

/-- MState optimized alpha-to-one theorem reduced to the finite supported
branch of Khatri--Wilde's sandwiched-Renyi monotonicity in `alpha`.

This discharges the `inf_sigmaB` layer: all side-state endpoint and support
convention work is handled in this file, and the only remaining source
obligation is the finite-branch monotonicity theorem from
`prop-sand_rel_ent_properties`. -/
theorem sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_chainRule_and_finite_mono
    (rhoAB : MState (a × b))
    (hfinite :
      ∀ sigmaB : MState b, ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          ∀ _hSupport : Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m,
            sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
                (rhoAB.traceRight.prod sigmaB).m
                (rhoAB.traceRight.prod sigmaB).psd alpha.1 ≤
              sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
                (rhoAB.traceRight.prod sigmaB).m
                (rhoAB.traceRight.prod sigmaB).psd beta.1) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        rhoAB.sandwichedRenyiMutualInformationE alpha.1)
      relativeEntropyHighAlphaRightToOne
      (nhds (mutualInformation rhoAB : EReal)) := by
  refine rhoAB.sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_chainRule_and_monotone ?_
  intro sigmaB alpha beta hab
  exact
    rhoAB.sandwichedRenyiMutualInformationCandidateE_mono_of_highAlphaFinite_mono
      sigmaB hab (hfinite sigmaB alpha beta hab)

/-- MState optimized alpha-to-one theorem reduced to the support-compressed
finite branch of Khatri--Wilde's sandwiched-Renyi monotonicity in `alpha`.

This is the direct state-level `inf_sigmaB` completion:
`I~_alpha(A;B)_rho → I(A;B)_rho` follows from monotonicity in `alpha` on the
strictly positive support of each reference `rho_A ⊗ sigma_B`. -/
theorem sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_chainRule_and_supportCompress_mono
    (rhoAB : MState (a × b))
    (hcompressed :
      ∀ sigmaB : MState b, ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          ∀ hSupport : Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m,
            sandwichedRenyiPSDReferenceHighAlphaFinite
                (psdSupportCompressedState
                  rhoAB (rhoAB.traceRight.prod sigmaB).psd hSupport)
                (psdSupportCompress
                  (rhoAB.traceRight.prod sigmaB).m
                  (rhoAB.traceRight.prod sigmaB).psd
                  (rhoAB.traceRight.prod sigmaB).m)
                (psdSupportCompress_self_posDef _
                  (rhoAB.traceRight.prod sigmaB).psd).posSemidef
                alpha.1 ≤
              sandwichedRenyiPSDReferenceHighAlphaFinite
                (psdSupportCompressedState
                  rhoAB (rhoAB.traceRight.prod sigmaB).psd hSupport)
                (psdSupportCompress
                  (rhoAB.traceRight.prod sigmaB).m
                  (rhoAB.traceRight.prod sigmaB).psd
                  (rhoAB.traceRight.prod sigmaB).m)
                (psdSupportCompress_self_posDef _
                  (rhoAB.traceRight.prod sigmaB).psd).posSemidef
                beta.1) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        rhoAB.sandwichedRenyiMutualInformationE alpha.1)
      relativeEntropyHighAlphaRightToOne
      (nhds (mutualInformation rhoAB : EReal)) := by
  refine rhoAB.sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_chainRule_and_monotone ?_
  intro sigmaB alpha beta hab
  exact
    rhoAB.sandwichedRenyiMutualInformationCandidateE_mono_of_supportCompress_mono
      sigmaB hab (hcompressed sigmaB alpha beta hab)

/-- Khatri--Wilde state optimized `inf_alpha` endpoint.

This is the state-level version of the third and fourth equalities in
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:1869-1907]: after the
fixed-candidate sandwiched-Renyi monotonicity from
`prop-sand_rel_ent_properties`, the optimized state quantity has
`inf_{alpha > 1} I~_alpha(A;B)_rho = I(A;B)_rho`.

The proof deliberately uses the same route as the source: monotonicity turns the
right endpoint into an `inf_alpha`, and the already proved chain-rule endpoint
identifies that endpoint with ordinary mutual information. -/
theorem sandwichedRenyiMutualInformationE_iInf_eq_mutualInformation_of_chainRule_and_monotone
    (rhoAB : MState (a × b))
    (hmono :
      ∀ sigmaB : MState b, ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1 ≤
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB beta.1) :
    (⨅ alpha : {alpha : ℝ // 1 < alpha},
        rhoAB.sandwichedRenyiMutualInformationE alpha.1) =
      (mutualInformation rhoAB : EReal) := by
  have : Nonempty b := by
    rcases rhoAB.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  have : Filter.NeBot relativeEntropyHighAlphaRightToOne :=
    relativeEntropyHighAlphaRightToOne_neBot
  have hstateMono :
      ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          rhoAB.sandwichedRenyiMutualInformationE alpha.1 ≤
            rhoAB.sandwichedRenyiMutualInformationE beta.1 :=
    rhoAB.sandwichedRenyiMutualInformationE_mono_of_candidate_mono hmono
  have hlimInf :
      Tendsto
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
          rhoAB.sandwichedRenyiMutualInformationE alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds
          (⨅ alpha : {alpha : ℝ // 1 < alpha},
            rhoAB.sandwichedRenyiMutualInformationE alpha.1)) :=
    tendsto_relativeEntropyHighAlphaRightToOne_iInf_of_monotone hstateMono
  have hlimMI :
      Tendsto
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
          rhoAB.sandwichedRenyiMutualInformationE alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds (mutualInformation rhoAB : EReal)) :=
    rhoAB.sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_chainRule_and_monotone
      hmono
  exact tendsto_nhds_unique hlimInf hlimMI

/-- MState optimized `inf_alpha` endpoint reduced to the finite supported branch
of Khatri--Wilde's sandwiched-Renyi monotonicity. -/
theorem sandwichedRenyiMutualInformationE_iInf_eq_mutualInformation_of_chainRule_and_finite_mono
    (rhoAB : MState (a × b))
    (hfinite :
      ∀ sigmaB : MState b, ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          ∀ _hSupport : Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m,
            sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
                (rhoAB.traceRight.prod sigmaB).m
                (rhoAB.traceRight.prod sigmaB).psd alpha.1 ≤
              sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
                (rhoAB.traceRight.prod sigmaB).m
                (rhoAB.traceRight.prod sigmaB).psd beta.1) :
    (⨅ alpha : {alpha : ℝ // 1 < alpha},
        rhoAB.sandwichedRenyiMutualInformationE alpha.1) =
      (mutualInformation rhoAB : EReal) := by
  refine
    rhoAB.sandwichedRenyiMutualInformationE_iInf_eq_mutualInformation_of_chainRule_and_monotone
      ?_
  intro sigmaB alpha beta hab
  exact
    rhoAB.sandwichedRenyiMutualInformationCandidateE_mono_of_highAlphaFinite_mono
      sigmaB hab (hfinite sigmaB alpha beta hab)

/-- MState optimized `inf_alpha` endpoint reduced to the support-compressed
finite branch of Khatri--Wilde's sandwiched-Renyi monotonicity.

This is the same state-level `inf_sigmaB` completion as
`sandwichedRenyiMutualInformationE_iInf_eq_mutualInformation_of_chainRule_and_finite_mono`,
but the remaining monotonicity obligation now lives on the strictly positive
support of each side-information reference. -/
theorem sandwichedRenyiMutualInformationE_iInf_eq_mutualInformation_of_chainRule_and_supportCompress_mono
    (rhoAB : MState (a × b))
    (hcompressed :
      ∀ sigmaB : MState b, ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          ∀ hSupport : Matrix.Supports rhoAB.m (rhoAB.traceRight.prod sigmaB).m,
            sandwichedRenyiPSDReferenceHighAlphaFinite
                (psdSupportCompressedState
                  rhoAB (rhoAB.traceRight.prod sigmaB).psd hSupport)
                (psdSupportCompress
                  (rhoAB.traceRight.prod sigmaB).m
                  (rhoAB.traceRight.prod sigmaB).psd
                  (rhoAB.traceRight.prod sigmaB).m)
                (psdSupportCompress_self_posDef _
                  (rhoAB.traceRight.prod sigmaB).psd).posSemidef
                alpha.1 ≤
              sandwichedRenyiPSDReferenceHighAlphaFinite
                (psdSupportCompressedState
                  rhoAB (rhoAB.traceRight.prod sigmaB).psd hSupport)
                (psdSupportCompress
                  (rhoAB.traceRight.prod sigmaB).m
                  (rhoAB.traceRight.prod sigmaB).psd
                  (rhoAB.traceRight.prod sigmaB).m)
                (psdSupportCompress_self_posDef _
                  (rhoAB.traceRight.prod sigmaB).psd).posSemidef
                beta.1) :
    (⨅ alpha : {alpha : ℝ // 1 < alpha},
        rhoAB.sandwichedRenyiMutualInformationE alpha.1) =
      (mutualInformation rhoAB : EReal) := by
  refine
    rhoAB.sandwichedRenyiMutualInformationE_iInf_eq_mutualInformation_of_chainRule_and_monotone
      ?_
  intro sigmaB alpha beta hab
  exact
    rhoAB.sandwichedRenyiMutualInformationCandidateE_mono_of_supportCompress_mono
      sigmaB hab (hcompressed sigmaB alpha beta hab)

/-- Convert the state optimized `alpha → 1+` limit into the `inf_alpha`
endpoint used by the Mosonyi--Hiai channel exchange.

Convergence and monotonicity in `alpha` are the two hypotheses: once the
state-level `inf_sigmaB` curve is known to converge to `I(A;B)_rho` and to be
monotone, its source endpoint is exactly the infimum over `alpha > 1`. -/
theorem sandwichedRenyiMutualInformationE_iInf_eq_mutualInformation_of_tendsto_and_mono
    (rhoAB : MState (a × b))
    (htend :
      Tendsto
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
          rhoAB.sandwichedRenyiMutualInformationE alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds (mutualInformation rhoAB : EReal)))
    (hmono :
      ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          rhoAB.sandwichedRenyiMutualInformationE alpha.1 ≤
            rhoAB.sandwichedRenyiMutualInformationE beta.1) :
    (⨅ alpha : {alpha : ℝ // 1 < alpha},
        rhoAB.sandwichedRenyiMutualInformationE alpha.1) =
      (mutualInformation rhoAB : EReal) := by
  have : Filter.NeBot relativeEntropyHighAlphaRightToOne :=
    relativeEntropyHighAlphaRightToOne_neBot
  have hlimInf :
      Tendsto
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
          rhoAB.sandwichedRenyiMutualInformationE alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds
          (⨅ alpha : {alpha : ℝ // 1 < alpha},
            rhoAB.sandwichedRenyiMutualInformationE alpha.1)) :=
    tendsto_relativeEntropyHighAlphaRightToOne_iInf_of_monotone hmono
  exact tendsto_nhds_unique hlimInf htend

/-- MState optimized `inf_alpha` endpoint from a full-rank side-state
restriction and a derivative-sign proof for all full-rank fixed candidates.

The convergence to ordinary mutual information remains an explicit state-level
input; this theorem only packages the full-rank approximation and derivative
monotonicity bridges into the order endpoint used by the channel minimax step. -/
theorem sandwichedRenyiMutualInformationE_iInf_eq_mutualInformation_of_tendsto_and_posDef_candidate_approx_deriv_nonneg
    (rhoAB : MState (a × b)) (hrhoA : rhoAB.traceRight.m.PosDef)
    (htend :
      Tendsto
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
          rhoAB.sandwichedRenyiMutualInformationE alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds (mutualInformation rhoAB : EReal)))
    (happrox :
      ∀ gamma : {gamma : ℝ // 1 < gamma}, ∀ sigmaB : MState b,
        (⨅ tauB : {tauB : MState b // tauB.m.PosDef},
          rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 gamma.1) ≤
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB gamma.1)
    (hcont :
      ∀ sigmaB : {sigmaB : MState b // sigmaB.m.PosDef},
        ContinuousOn
          (fun alpha : ℝ =>
            sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
              (rhoAB.traceRight.prod sigmaB.1).m
              (rhoAB.traceRight.prod sigmaB.1).psd alpha)
          (Set.Ioi (1 : ℝ)))
    (hdiff :
      ∀ sigmaB : {sigmaB : MState b // sigmaB.m.PosDef},
        DifferentiableOn ℝ
          (fun alpha : ℝ =>
            sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
              (rhoAB.traceRight.prod sigmaB.1).m
              (rhoAB.traceRight.prod sigmaB.1).psd alpha)
          (Set.Ioi (1 : ℝ)))
    (hderiv :
      ∀ sigmaB : {sigmaB : MState b // sigmaB.m.PosDef},
        ∀ alpha : ℝ, 1 < alpha →
          0 ≤ deriv
            (fun beta : ℝ =>
              sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
                (rhoAB.traceRight.prod sigmaB.1).m
                (rhoAB.traceRight.prod sigmaB.1).psd beta)
            alpha) :
    (⨅ alpha : {alpha : ℝ // 1 < alpha},
        rhoAB.sandwichedRenyiMutualInformationE alpha.1) =
      (mutualInformation rhoAB : EReal) := by
  refine
    rhoAB.sandwichedRenyiMutualInformationE_iInf_eq_mutualInformation_of_tendsto_and_mono
      htend ?_
  exact
    rhoAB.sandwichedRenyiMutualInformationE_mono_of_posDef_candidate_approx_and_deriv_nonneg
      hrhoA happrox hcont hdiff hderiv

end MState

end

noncomputable section

namespace CPTPOp

open QIT

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable {E β : Type*} [TopologicalSpace E] [LinearOrder β]

variable (N : CPTPMap a b)

/-- Fixed-input channel endpoint for the product-marginal side-information
candidate, expressed as the ordinary entanglement-assisted mutual information
of that input. -/
theorem inputSandwichedRenyiProductMarginalEndpoint_eq_entanglementAssistedMutualInformation
    (psi : Ket (a × a)) :
    MState.relativeEntropyPSDReferenceE (N.hypothesisTestingOutputState psi)
        ((N.hypothesisTestingOutputState psi).traceRight.prod
          (N.hypothesisTestingOutputState psi).traceLeft).m
        ((N.hypothesisTestingOutputState psi).traceRight.prod
          (N.hypothesisTestingOutputState psi).traceLeft).psd =
      (N.entanglementAssistedMutualInformation psi : EReal) := by
  calc
    MState.relativeEntropyPSDReferenceE (N.hypothesisTestingOutputState psi)
        ((N.hypothesisTestingOutputState psi).traceRight.prod
          (N.hypothesisTestingOutputState psi).traceLeft).m
        ((N.hypothesisTestingOutputState psi).traceRight.prod
          (N.hypothesisTestingOutputState psi).traceLeft).psd =
        (N.hypothesisTestingOutputState psi).relativeEntropy
        ((N.hypothesisTestingOutputState psi).traceRight.prod
          (N.hypothesisTestingOutputState psi).traceLeft) := by
          rw [MState.relativeEntropyPSDReferenceE_eq_traceLogE]
          rfl
    _ =
        (mutualInformation (N.hypothesisTestingOutputState psi) : EReal) := by
          exact
            MState.relativeEntropy_prod_marginals_eq_mutualInformation
              (N.hypothesisTestingOutputState psi)
    _ = (N.entanglementAssistedMutualInformation psi : EReal) := by
          rfl

/-- Fixed-input, product-marginal side-information candidate convergence for a
channel output state. -/
theorem inputSandwichedRenyiProductMarginalCandidate_tendsto_entanglementAssistedMutualInformation
    (psi : Ket (a × a)) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
          (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
            (N.hypothesisTestingOutputState psi).traceLeft alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedMutualInformation psi : EReal)) := by
  simpa [CPTPOp.entanglementAssistedMutualInformation,
    CPTPOp.entanglementAssistedOutputState, CPTPOp.hypothesisTestingOutputState] using
    MState.sandwichedRenyiMutualInformationCandidateE_traceLeft_tendsto_mutualInformation
      (N.hypothesisTestingOutputState psi)

/-- Some fixed input attains the ordinary channel mutual information, and the
same input therefore attains the product-marginal endpoint value in the
right-limit expression. -/
theorem exists_inputSandwichedRenyiProductMarginalEndpoint_eq_information
    [Nonempty a] :
    Exists fun psi : Ket (a × a) =>
      MState.relativeEntropyPSDReferenceE (N.hypothesisTestingOutputState psi)
          ((N.hypothesisTestingOutputState psi).traceRight.prod
            (N.hypothesisTestingOutputState psi).traceLeft).m
          ((N.hypothesisTestingOutputState psi).traceRight.prod
            (N.hypothesisTestingOutputState psi).traceLeft).psd =
        (N.entanglementAssistedInformation : EReal) := by
  match N.exists_entanglementAssistedInformation_maximizer with
  | Exists.intro psi hpsi =>
      refine Exists.intro psi ?_
      rw [N.inputSandwichedRenyiProductMarginalEndpoint_eq_entanglementAssistedMutualInformation]
      rw [hpsi]

/-- Some fixed input attains the ordinary channel mutual information, and the
product-marginal side-information candidate for that input tends to `I(N)`. -/
theorem exists_inputSandwichedRenyiProductMarginalCandidate_tendsto_information
    [Nonempty a] :
    Exists fun psi : Ket (a × a) =>
      Tendsto
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
            (N.hypothesisTestingOutputState psi).traceLeft alpha.1)
        MState.relativeEntropyHighAlphaRightToOne
        (nhds (N.entanglementAssistedInformation : EReal)) := by
  match N.exists_entanglementAssistedInformation_maximizer with
  | Exists.intro psi hpsi =>
      refine Exists.intro psi ?_
      simpa [hpsi] using
        N.inputSandwichedRenyiProductMarginalCandidate_tendsto_entanglementAssistedMutualInformation
          psi

/-- The channel sandwiched-Renyi mutual information is the indexed supremum
over pure input-reference states. -/
theorem sandwichedRenyiMutualInformationE_eq_iSup (alpha : ℝ) :
    N.sandwichedRenyiMutualInformationE alpha =
      ⨆ psi : Ket (a × a), N.inputSandwichedRenyiMutualInformationE psi alpha := by
  rw [CPTPOp.sandwichedRenyiMutualInformationE_eq_sSup,
    CPTPOp.sandwichedRenyiMutualInformationEValueSet, sSup_range]

/-- Khatri--Wilde monotonicity lift for the channel `sup_psi` expression.

Once every fixed input's optimized state sandwiched-Renyi mutual information is
monotone in `alpha`, the channel quantity remains monotone after the pure-input
supremum. -/
theorem sandwichedRenyiMutualInformationE_mono_of_input_mono
    [Nonempty a]
    (hmono :
      ∀ psi : Ket (a × a), ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          N.inputSandwichedRenyiMutualInformationE psi alpha.1 ≤
            N.inputSandwichedRenyiMutualInformationE psi beta.1) :
    ∀ alpha beta : {alpha : ℝ // 1 < alpha},
      alpha.1 ≤ beta.1 →
        N.sandwichedRenyiMutualInformationE alpha.1 ≤
          N.sandwichedRenyiMutualInformationE beta.1 := by
  intro alpha beta hab
  rw [CPTPOp.sandwichedRenyiMutualInformationE_eq_sSup,
    CPTPOp.sandwichedRenyiMutualInformationE_eq_sSup]
  refine sSup_le ?_
  intro y hy
  rcases hy with ⟨psi, rfl⟩
  exact (hmono psi alpha beta hab).trans
    (le_sSup (N.inputSandwichedRenyiMutualInformationE_mem_valueSet psi beta.1))

/-- Khatri--Wilde monotonicity lift all the way from fixed side-information
candidates to the channel sandwiched-Renyi mutual information.

This is still only an order bridge: the source property
`prop-sand_rel_ent_properties`, monotonicity of fixed-reference sandwiched
relative entropy in `alpha`, remains the mathematical input. -/
theorem sandwichedRenyiMutualInformationE_mono_of_candidate_mono
    [Nonempty a]
    (hmono :
      ∀ psi : Ket (a × a), ∀ sigmaB : MState b,
        ∀ alpha beta : {alpha : ℝ // 1 < alpha},
          alpha.1 ≤ beta.1 →
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
              sigmaB alpha.1 ≤
              (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
                sigmaB beta.1) :
    ∀ alpha beta : {alpha : ℝ // 1 < alpha},
      alpha.1 ≤ beta.1 →
        N.sandwichedRenyiMutualInformationE alpha.1 ≤
          N.sandwichedRenyiMutualInformationE beta.1 := by
  refine N.sandwichedRenyiMutualInformationE_mono_of_input_mono ?_
  intro psi alpha beta hab
  have : Nonempty b := by
    rcases (N.hypothesisTestingOutputState psi).nonempty with ⟨x⟩
    exact ⟨x.2⟩
  simpa [CPTPOp.inputSandwichedRenyiMutualInformationE] using
    (N.hypothesisTestingOutputState psi)
      |>.sandwichedRenyiMutualInformationE_mono_of_candidate_mono
        (hmono psi) alpha beta hab

/-- Channel monotonicity from a full-rank side-state restriction and
full-rank fixed-candidate monotonicity for every pure input. -/
theorem sandwichedRenyiMutualInformationE_mono_of_input_iInf_posDef_candidates_and_candidate_mono
    [Nonempty a]
    (hfullRankInf :
      ∀ psi : Ket (a × a), ∀ gamma : {gamma : ℝ // 1 < gamma},
        (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE gamma.1 =
          ⨅ sigmaB : {sigmaB : MState b // sigmaB.m.PosDef},
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
              sigmaB.1 gamma.1)
    (hmono :
      ∀ psi : Ket (a × a),
        ∀ sigmaB : {sigmaB : MState b // sigmaB.m.PosDef},
          ∀ alpha beta : {alpha : ℝ // 1 < alpha},
            alpha.1 ≤ beta.1 →
              (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
                sigmaB.1 alpha.1 ≤
                (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
                  sigmaB.1 beta.1) :
    ∀ alpha beta : {alpha : ℝ // 1 < alpha},
      alpha.1 ≤ beta.1 →
        N.sandwichedRenyiMutualInformationE alpha.1 ≤
          N.sandwichedRenyiMutualInformationE beta.1 := by
  refine N.sandwichedRenyiMutualInformationE_mono_of_input_mono ?_
  intro psi alpha beta hab
  simpa [CPTPOp.inputSandwichedRenyiMutualInformationE] using
    (N.hypothesisTestingOutputState psi)
      |>.sandwichedRenyiMutualInformationE_mono_of_iInf_posDef_candidates_and_candidate_mono
        (hfullRankInf psi) (hmono psi) alpha beta hab

/-- Khatri--Wilde order step for the channel sandwiched-Renyi mutual
information curve:
`lim_{alpha → 1+} I~_alpha(N) = inf_{alpha > 1} I~_alpha(N)` once the source
monotonicity in `alpha` is available.

This corresponds to the first equality in
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:1869-1907]. -/
theorem sandwichedRenyiMutualInformationE_tendsto_iInf_of_monotone
    (hmono :
      ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          N.sandwichedRenyiMutualInformationE alpha.1 ≤
            N.sandwichedRenyiMutualInformationE beta.1) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds
        (⨅ alpha : {alpha : ℝ // 1 < alpha},
          N.sandwichedRenyiMutualInformationE alpha.1)) :=
  MState.tendsto_relativeEntropyHighAlphaRightToOne_iInf_of_monotone hmono

/-- Khatri--Wilde alpha-to-one handoff: after monotonicity and the
Mosonyi/minimax identification
`inf_{alpha > 1} I~_alpha(N) = I(N)`, the channel sandwiched-Renyi mutual
information tends to the ordinary entanglement-assisted mutual information.

The nontrivial mathematical content is the minimax identification, corresponding
to [KhatriWilde2024Principles, Chapters/EA_capacity.tex:1869-1907]. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information_of_iInf_eq
    (hmono :
      ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          N.sandwichedRenyiMutualInformationE alpha.1 ≤
            N.sandwichedRenyiMutualInformationE beta.1)
    (hInf :
      (⨅ alpha : {alpha : ℝ // 1 < alpha},
          N.sandwichedRenyiMutualInformationE alpha.1) =
        (N.entanglementAssistedInformation : EReal)) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  have hlim := N.sandwichedRenyiMutualInformationE_tendsto_iInf_of_monotone hmono
  simpa [hInf] using hlim

/-- Source-shaped Khatri--Wilde handoff for
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:1869-1907].

Fixed-candidate sandwiched-Renyi monotonicity supplies the first source step,
turning the right limit into an `inf_alpha`; the remaining hypothesis is exactly
the Mosonyi--Hiai/minimax identification of that `inf_alpha` with ordinary
entanglement-assisted mutual information. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information_of_candidate_mono_and_iInf_eq
    [Nonempty a]
    (hmono :
      ∀ psi : Ket (a × a), ∀ sigmaB : MState b,
        ∀ alpha beta : {alpha : ℝ // 1 < alpha},
          alpha.1 ≤ beta.1 →
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
              sigmaB alpha.1 ≤
              (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
                sigmaB beta.1)
    (hInf :
      (⨅ alpha : {alpha : ℝ // 1 < alpha},
          N.sandwichedRenyiMutualInformationE alpha.1) =
        (N.entanglementAssistedInformation : EReal)) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  exact
    N.sandwichedRenyiMutualInformationE_tendsto_information_of_iInf_eq
      (N.sandwichedRenyiMutualInformationE_mono_of_candidate_mono hmono) hInf

/-- The one-shot output-state map used in the channel sandwiched route is
continuous in the pure input. -/
theorem hypothesisTestingOutputState_continuous {r : Type u} [Fintype r] [DecidableEq r] :
    Continuous (fun psi : Ket (r × a) => N.hypothesisTestingOutputState psi) := by
  simpa [CPTPOp.hypothesisTestingOutputState, Function.comp_def] using
    (((CPTPOp.id (dIn := r)).prod N).applyState_continuous).comp Ket.state_continuous

/-- Pull state-level optimized upper semicontinuity back along the channel
pure-input output-state map.

This is the continuity-in-`psi` hypothesis appearing in the Khatri--Wilde
Mosonyi--Hiai step, `Chapters/EA_capacity.tex:1902-1906`, phrased as a
state-level obligation. -/
theorem inputSandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_state
    (alpha : {alpha : ℝ // 1 < alpha})
    (husc :
      UpperSemicontinuousOn
        (fun rho : MState (a × b) => rho.sandwichedRenyiMutualInformationE alpha.1)
        Set.univ) :
    UpperSemicontinuousOn
      (fun psi : Ket (a × a) =>
        N.inputSandwichedRenyiMutualInformationE psi alpha.1)
      Set.univ := by
  have hcont :
      ContinuousOn
        (fun psi : Ket (a × a) => N.hypothesisTestingOutputState psi)
        Set.univ :=
    (N.hypothesisTestingOutputState_continuous (r := a)).continuousOn
  have hmaps :
      Set.MapsTo
        (fun psi : Ket (a × a) => N.hypothesisTestingOutputState psi)
        Set.univ
        Set.univ := by
    intro psi hpsi
    exact trivial
  have hcomp := husc.comp (t := Set.univ) hcont hmaps
  simpa [Function.comp_def, CPTPOp.inputSandwichedRenyiMutualInformationE] using hcomp

/-- Pull the full-rank-candidate optimized upper semicontinuity bridge back to
the channel pure-input objective. -/
theorem inputSandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_iInf_posDef_candidates
    (alpha : {alpha : ℝ // 1 < alpha})
    (hposA :
      ∀ psi : Ket (a × a),
        (N.hypothesisTestingOutputState psi).traceRight.m.PosDef)
    (hfullRankInf :
      ∀ rho : MState (a × b),
        rho.sandwichedRenyiMutualInformationE alpha.1 =
          ⨅ sigmaB : {sigmaB : MState b // sigmaB.m.PosDef},
            rho.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha.1) :
    UpperSemicontinuousOn
      (fun psi : Ket (a × a) =>
        N.inputSandwichedRenyiMutualInformationE psi alpha.1)
      Set.univ := by
  let s : Set (MState (a × b)) := {rho | rho.traceRight.m.PosDef}
  have hstate :
      UpperSemicontinuousOn
        (fun rho : MState (a × b) => rho.sandwichedRenyiMutualInformationE alpha.1)
        s :=
    MState.sandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_iInf_posDef_candidates
      alpha.2 (by intro rho hrho; exact hrho) hfullRankInf
  have hcont :
      ContinuousOn
        (fun psi : Ket (a × a) => N.hypothesisTestingOutputState psi)
        Set.univ :=
    (N.hypothesisTestingOutputState_continuous (r := a)).continuousOn
  have hmaps :
      Set.MapsTo
        (fun psi : Ket (a × a) => N.hypothesisTestingOutputState psi)
        Set.univ
        s := by
    intro psi _hpsi
    exact hposA psi
  have hcomp := hstate.comp (t := Set.univ) hcont hmaps
  simpa [s, Function.comp_def, CPTPOp.inputSandwichedRenyiMutualInformationE] using hcomp

/-- Channel pure-input upper semicontinuity from the full-rank approximation
lower-bound form of the side-state restriction. -/
theorem inputSandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_posDef_candidate_approx
    (alpha : {alpha : ℝ // 1 < alpha})
    (hposA :
      ∀ psi : Ket (a × a),
        (N.hypothesisTestingOutputState psi).traceRight.m.PosDef)
    (happrox :
      ∀ rho : MState (a × b), ∀ sigmaB : MState b,
        (⨅ tauB : {tauB : MState b // tauB.m.PosDef},
          rho.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha.1) ≤
            rho.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1) :
    UpperSemicontinuousOn
      (fun psi : Ket (a × a) =>
        N.inputSandwichedRenyiMutualInformationE psi alpha.1)
      Set.univ := by
  refine
    N.inputSandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_iInf_posDef_candidates
      alpha hposA ?_
  intro rho
  exact
    MState.sandwichedRenyiMutualInformationE_eq_iInf_posDef_candidates_of_le_candidate
      rho alpha.1 (happrox rho)

/-- Channel pure-input upper semicontinuity using the full-rank side-state
restriction proved by approximation. -/
theorem inputSandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_fullRankApprox
    (alpha : {alpha : ℝ // 1 < alpha})
    (hposA :
      ∀ psi : Ket (a × a),
        (N.hypothesisTestingOutputState psi).traceRight.m.PosDef) :
    UpperSemicontinuousOn
      (fun psi : Ket (a × a) =>
        N.inputSandwichedRenyiMutualInformationE psi alpha.1)
      Set.univ := by
  refine
    N.inputSandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_iInf_posDef_candidates
      alpha hposA ?_
  intro rho
  exact
    MState.sandwichedRenyiMutualInformationE_eq_iInf_posDef_candidates_highAlpha
      rho alpha.2

/-- Khatri--Wilde Mosonyi--Hiai exchange for the channel sandwiched-Renyi
mutual information objective.

This is the direct Lean form of the source step
`inf_alpha sup_psi = sup_psi inf_alpha` in
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:1869-1907].  The analytic
inputs are exactly the source hypotheses: upper semicontinuity/continuity in
the pure input and monotonicity in the high-`alpha` parameter. -/
theorem sandwichedRenyiMutualInformationE_iInf_iSup_eq_iSup_iInf_of_mosonyi_hiai
    [Nonempty a]
    (husc :
      ∀ alpha : {alpha : ℝ // 1 < alpha},
        UpperSemicontinuousOn
          (fun psi : Ket (a × a) =>
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE alpha.1)
          Set.univ)
    (hmono :
      ∀ psi : Ket (a × a), ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE alpha.1 ≤
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE beta.1) :
    (⨅ alpha : {alpha : ℝ // 1 < alpha},
        N.sandwichedRenyiMutualInformationE alpha.1) =
      (⨆ psi : Ket (a × a),
        ⨅ alpha : {alpha : ℝ // 1 < alpha},
          (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE alpha.1) := by
  have : Nonempty (Ket (a × a)) := ⟨default⟩
  let X : Set (Ket (a × a)) := Set.univ
  let Y : Set {alpha : ℝ // 1 < alpha} := Set.univ
  let F : Ket (a × a) → {alpha : ℝ // 1 < alpha} → EReal :=
    fun psi alpha =>
      (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE alpha.1
  have hXne : X.Nonempty := Set.univ_nonempty
  have hYne : Y.Nonempty := by
    refine ⟨⟨2, ?_⟩, trivial⟩
    norm_num
  have hUSC : ∀ alpha ∈ Y, UpperSemicontinuousOn (fun psi => F psi alpha) X := by
    intro alpha _halpha
    exact husc alpha
  have hMono :
      ∀ psi ∈ X, ∀ alpha ∈ Y, ∀ beta ∈ Y,
        alpha ≤ beta → F psi alpha ≤ F psi beta := by
    intro psi _hpsi alpha _halpha beta _hbeta hab
    exact hmono psi alpha beta hab
  have hMH :=
    mosonyiHiai_iInf_iSup_eq_iSup_iInf_dual
      (X := X) (Y := Y) hXne isCompact_univ hYne F hUSC hMono
  simpa [X, Y, F, iInf_subtype, iSup_subtype, CPTPOp.inputSandwichedRenyiMutualInformationE,
    CPTPOp.sandwichedRenyiMutualInformationE_eq_iSup] using hMH

/-- Upper semicontinuity of fixed side-information candidates lifts to the
state-optimized input objective used in the channel sandwiched-Renyi mutual
information. -/
theorem inputSandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_candidate
    (alpha : {alpha : ℝ // 1 < alpha})
    (husc :
      ∀ sigmaB : MState b,
        UpperSemicontinuousOn
          (fun psi : Ket (a × a) =>
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
              sigmaB alpha.1)
          Set.univ) :
    UpperSemicontinuousOn
      (fun psi : Ket (a × a) =>
        N.inputSandwichedRenyiMutualInformationE psi alpha.1)
      Set.univ := by
  simpa [CPTPOp.inputSandwichedRenyiMutualInformationE] using
    MState.sandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_candidate
      (rho := fun psi : Ket (a × a) => N.hypothesisTestingOutputState psi)
      alpha.1 husc

/-- Khatri--Wilde Mosonyi--Hiai exchange from fixed-candidate upper
semicontinuity and fixed-candidate monotonicity. -/
theorem sandwichedRenyiMutualInformationE_iInf_iSup_eq_iSup_iInf_of_candidate_husc_and_mono
    [Nonempty a]
    (husc :
      ∀ alpha : {alpha : ℝ // 1 < alpha}, ∀ sigmaB : MState b,
        UpperSemicontinuousOn
          (fun psi : Ket (a × a) =>
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
              sigmaB alpha.1)
          Set.univ)
    (hmono :
      ∀ psi : Ket (a × a), ∀ sigmaB : MState b,
        ∀ alpha beta : {alpha : ℝ // 1 < alpha},
          alpha.1 ≤ beta.1 →
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
              sigmaB alpha.1 ≤
              (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
                sigmaB beta.1) :
    (⨅ alpha : {alpha : ℝ // 1 < alpha},
        N.sandwichedRenyiMutualInformationE alpha.1) =
      (⨆ psi : Ket (a × a),
        ⨅ alpha : {alpha : ℝ // 1 < alpha},
          (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE alpha.1) := by
  refine N.sandwichedRenyiMutualInformationE_iInf_iSup_eq_iSup_iInf_of_mosonyi_hiai ?_ ?_
  · intro alpha
    simpa [CPTPOp.inputSandwichedRenyiMutualInformationE] using
      N.inputSandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_candidate
        alpha (husc alpha)
  · intro psi alpha beta hab
    have : Nonempty b := by
      rcases (N.hypothesisTestingOutputState psi).nonempty with ⟨x⟩
      exact ⟨x.2⟩
    exact
      (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE_mono_of_candidate_mono
        (hmono psi) alpha beta hab

/-- Mosonyi--Hiai exchange reduced to fixed-candidate upper semicontinuity and
the finite supported branch of Khatri--Wilde sandwiched-Renyi monotonicity. -/
theorem sandwichedRenyiMutualInformationE_iInf_iSup_eq_iSup_iInf_of_candidate_husc_and_finite_mono
    [Nonempty a]
    (husc :
      ∀ alpha : {alpha : ℝ // 1 < alpha}, ∀ sigmaB : MState b,
        UpperSemicontinuousOn
          (fun psi : Ket (a × a) =>
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
              sigmaB alpha.1)
          Set.univ)
    (hfinite :
      ∀ psi : Ket (a × a), ∀ sigmaB : MState b,
        ∀ alpha beta : {alpha : ℝ // 1 < alpha},
          alpha.1 ≤ beta.1 →
            ∀ _hSupport : Matrix.Supports (N.hypothesisTestingOutputState psi).m
                ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m,
              MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                  (N.hypothesisTestingOutputState psi)
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                  alpha.1 ≤
                MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                  (N.hypothesisTestingOutputState psi)
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                  beta.1) :
    (⨅ alpha : {alpha : ℝ // 1 < alpha},
        N.sandwichedRenyiMutualInformationE alpha.1) =
      (⨆ psi : Ket (a × a),
        ⨅ alpha : {alpha : ℝ // 1 < alpha},
          (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE alpha.1) := by
  refine
    N.sandwichedRenyiMutualInformationE_iInf_iSup_eq_iSup_iInf_of_candidate_husc_and_mono
      husc ?_
  intro psi sigmaB alpha beta hab
  exact
    (N.hypothesisTestingOutputState psi)
      |>.sandwichedRenyiMutualInformationCandidateE_mono_of_highAlphaFinite_mono
        sigmaB hab (hfinite psi sigmaB alpha beta hab)

/-- Coercion bridge for the last line of the Khatri--Wilde channel limit proof.

The ordinary entanglement-assisted information is a real supremum over pure
inputs, while the sandwiched route lives in `EReal`.  This theorem identifies
the `EReal` supremum over the coerced input mutual informations with the
coercion of `I(N)`. -/
theorem iSup_entanglementAssistedMutualInformation_coe_eq_information
    [Nonempty a] :
    (⨆ psi : Ket (a × a),
        (N.entanglementAssistedMutualInformation psi : EReal)) =
      (N.entanglementAssistedInformation : EReal) := by
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro psi
    exact EReal.coe_le_coe_iff.mpr
      (N.entanglementAssistedMutualInformation_le_information psi)
  · obtain ⟨psi, hpsi⟩ := N.exists_entanglementAssistedInformation_maximizer
    have hcoe :
        (N.entanglementAssistedInformation : EReal) =
          (N.entanglementAssistedMutualInformation psi : EReal) := by
      rw [hpsi]
    rw [hcoe]
    exact le_iSup
      (fun psi : Ket (a × a) =>
        (N.entanglementAssistedMutualInformation psi : EReal))
      psi

/-- Khatri--Wilde Mosonyi--Hiai assembly for the channel `inf_alpha` value.

This theorem follows the source equalities
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:1869-1907]:

* `hMosonyi` is exactly the Mosonyi--Hiai exchange of `inf_alpha` and
  `sup_psi`;
* `hState` is the pointwise state optimized endpoint
  `inf_alpha I~_alpha(R;B)_psi = I(R;B)_psi`;
* the final line is the definition of `I(N)` as the supremum over pure inputs.

No minimax or monotonicity statement is hidden in this theorem; those remain
separate source obligations. -/
theorem sandwichedRenyiMutualInformationE_iInf_eq_information_of_mosonyi_hiai
    [Nonempty a]
    (hMosonyi :
      (⨅ alpha : {alpha : ℝ // 1 < alpha},
          N.sandwichedRenyiMutualInformationE alpha.1) =
        (⨆ psi : Ket (a × a),
          ⨅ alpha : {alpha : ℝ // 1 < alpha},
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE
              alpha.1))
    (hState :
      ∀ psi : Ket (a × a),
        (⨅ alpha : {alpha : ℝ // 1 < alpha},
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE
              alpha.1) =
          (N.entanglementAssistedMutualInformation psi : EReal)) :
    (⨅ alpha : {alpha : ℝ // 1 < alpha},
        N.sandwichedRenyiMutualInformationE alpha.1) =
      (N.entanglementAssistedInformation : EReal) := by
  have hpoint :
      (fun psi : Ket (a × a) =>
          (⨅ alpha : {alpha : ℝ // 1 < alpha},
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE
              alpha.1)) =
        fun psi : Ket (a × a) =>
          (N.entanglementAssistedMutualInformation psi : EReal) := by
    funext psi
    exact hState psi
  calc
    (⨅ alpha : {alpha : ℝ // 1 < alpha},
        N.sandwichedRenyiMutualInformationE alpha.1) =
        (⨆ psi : Ket (a × a),
          ⨅ alpha : {alpha : ℝ // 1 < alpha},
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE
              alpha.1) := hMosonyi
    _ = (⨆ psi : Ket (a × a),
          (N.entanglementAssistedMutualInformation psi : EReal)) := by
          rw [hpoint]
    _ = (N.entanglementAssistedInformation : EReal) :=
          N.iSup_entanglementAssistedMutualInformation_coe_eq_information

/-- Khatri--Wilde channel `inf_alpha` identification from the source
monotonicity and Mosonyi--Hiai exchange.

The fixed-candidate monotonicity discharges the state endpoint through
`sandwichedRenyiMutualInformationE_iInf_eq_mutualInformation_of_chainRule_and_monotone`;
the remaining channel-level input is exactly Mosonyi--Hiai's
`inf_alpha/sup_psi` exchange. -/
theorem sandwichedRenyiMutualInformationE_iInf_eq_information_of_candidate_mono_and_mosonyi_hiai
    [Nonempty a]
    (hmono :
      ∀ psi : Ket (a × a), ∀ sigmaB : MState b,
        ∀ alpha beta : {alpha : ℝ // 1 < alpha},
          alpha.1 ≤ beta.1 →
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
              sigmaB alpha.1 ≤
              (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
                sigmaB beta.1)
    (hMosonyi :
      (⨅ alpha : {alpha : ℝ // 1 < alpha},
          N.sandwichedRenyiMutualInformationE alpha.1) =
        (⨆ psi : Ket (a × a),
          ⨅ alpha : {alpha : ℝ // 1 < alpha},
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE
              alpha.1)) :
    (⨅ alpha : {alpha : ℝ // 1 < alpha},
        N.sandwichedRenyiMutualInformationE alpha.1) =
      (N.entanglementAssistedInformation : EReal) := by
  refine
    N.sandwichedRenyiMutualInformationE_iInf_eq_information_of_mosonyi_hiai
      hMosonyi ?_
  intro psi
  simpa [CPTPOp.entanglementAssistedMutualInformation,
    CPTPOp.entanglementAssistedOutputState, CPTPOp.hypothesisTestingOutputState] using
    MState.sandwichedRenyiMutualInformationE_iInf_eq_mutualInformation_of_chainRule_and_monotone
      (N.hypothesisTestingOutputState psi) (hmono psi)

/-- Source-shaped Khatri--Wilde channel alpha-to-one theorem, with the
Mosonyi--Hiai exchange exposed as the final channel optimization obligation. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information_of_candidate_mono_and_mosonyi_hiai
    [Nonempty a]
    (hmono :
      ∀ psi : Ket (a × a), ∀ sigmaB : MState b,
        ∀ alpha beta : {alpha : ℝ // 1 < alpha},
          alpha.1 ≤ beta.1 →
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
              sigmaB alpha.1 ≤
              (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
                sigmaB beta.1)
    (hMosonyi :
      (⨅ alpha : {alpha : ℝ // 1 < alpha},
          N.sandwichedRenyiMutualInformationE alpha.1) =
        (⨆ psi : Ket (a × a),
          ⨅ alpha : {alpha : ℝ // 1 < alpha},
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE
              alpha.1)) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  exact
    N.sandwichedRenyiMutualInformationE_tendsto_information_of_candidate_mono_and_iInf_eq
      hmono
      (N.sandwichedRenyiMutualInformationE_iInf_eq_information_of_candidate_mono_and_mosonyi_hiai
        hmono hMosonyi)

/-- Source-faithful Khatri--Wilde channel alpha-to-one theorem.

This version follows [KhatriWilde2024Principles, Chapters/EA_capacity.tex:1869-1907]
literally: Mosonyi--Hiai is applied to the already optimized pure-input function
`psi ↦ inf_sigmaB D~_alpha(N(psi) || psi_R ⊗ sigmaB)`, which is required to be
upper semicontinuous in `psi` and monotone in `alpha`.

The fixed-candidate lemmas below are only sufficient routes for proving these
hypotheses; they are not the source shape of the final channel theorem. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information_of_optimized_mosonyi_hiai
    [Nonempty a]
    (husc :
      ∀ alpha : {alpha : ℝ // 1 < alpha},
        UpperSemicontinuousOn
          (fun psi : Ket (a × a) =>
            N.inputSandwichedRenyiMutualInformationE psi alpha.1)
          Set.univ)
    (hstateMono :
      ∀ psi : Ket (a × a), ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE alpha.1 ≤
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE beta.1)
    (hstateEndpoint :
      ∀ psi : Ket (a × a),
        (⨅ alpha : {alpha : ℝ // 1 < alpha},
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE
              alpha.1) =
          (N.entanglementAssistedMutualInformation psi : EReal)) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  have hMosonyi :
      (⨅ alpha : {alpha : ℝ // 1 < alpha},
          N.sandwichedRenyiMutualInformationE alpha.1) =
        (⨆ psi : Ket (a × a),
          ⨅ alpha : {alpha : ℝ // 1 < alpha},
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE
              alpha.1) :=
    N.sandwichedRenyiMutualInformationE_iInf_iSup_eq_iSup_iInf_of_mosonyi_hiai
      husc hstateMono
  refine N.sandwichedRenyiMutualInformationE_tendsto_information_of_iInf_eq ?_ ?_
  · exact N.sandwichedRenyiMutualInformationE_mono_of_input_mono hstateMono
  · exact
      N.sandwichedRenyiMutualInformationE_iInf_eq_information_of_mosonyi_hiai
        hMosonyi hstateEndpoint

/-- Channel pure-input optimization exchange from a completed state optimized
`alpha → 1+` limit.

This theorem is the clean two-step assembly for the channel limit:

* `hstateTendsto` is the state-level `inf_sigmaB` theorem
  `I~_alpha(A;B)_rho → I(A;B)_rho`;
* `husc` and `hstateMono` are exactly the Mosonyi--Hiai hypotheses needed to
  exchange the channel `sup_psi` with the high-`alpha` infimum.

No fixed-candidate theorem is used as the channel statement here. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information_of_state_limit_and_mosonyi_hiai
    [Nonempty a]
    (husc :
      ∀ alpha : {alpha : ℝ // 1 < alpha},
        UpperSemicontinuousOn
          (fun psi : Ket (a × a) =>
            N.inputSandwichedRenyiMutualInformationE psi alpha.1)
          Set.univ)
    (hstateTendsto :
      ∀ psi : Ket (a × a),
        Tendsto
          (fun alpha : {alpha : ℝ // 1 < alpha} =>
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE alpha.1)
          MState.relativeEntropyHighAlphaRightToOne
          (nhds (N.entanglementAssistedMutualInformation psi : EReal)))
    (hstateMono :
      ∀ psi : Ket (a × a), ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE alpha.1 ≤
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE beta.1) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  refine
    N.sandwichedRenyiMutualInformationE_tendsto_information_of_optimized_mosonyi_hiai
      husc hstateMono ?_
  intro psi
  have hstateEndpoint :=
    MState.sandwichedRenyiMutualInformationE_iInf_eq_mutualInformation_of_tendsto_and_mono
      (N.hypothesisTestingOutputState psi) ?_ (hstateMono psi)
  simpa [CPTPOp.entanglementAssistedMutualInformation,
    CPTPOp.entanglementAssistedOutputState,
    CPTPOp.hypothesisTestingOutputState] using hstateEndpoint
  simpa [CPTPOp.entanglementAssistedMutualInformation,
    CPTPOp.entanglementAssistedOutputState,
    CPTPOp.hypothesisTestingOutputState] using hstateTendsto psi

/-- Channel pure-input optimization exchange from state-level upper
semicontinuity and a completed state optimized `alpha → 1+` theorem.

This is the same two-step assembly as
`sandwichedRenyiMutualInformationE_tendsto_information_of_state_limit_and_mosonyi_hiai`,
but obtains the Mosonyi--Hiai pure-input upper semicontinuity hypothesis by
pulling back state-level optimized upper semicontinuity along the continuous
channel output-state map. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information_of_state_limit_and_state_husc
    [Nonempty a]
    (hstateUSC :
      ∀ alpha : {alpha : ℝ // 1 < alpha},
        UpperSemicontinuousOn
          (fun rho : MState (a × b) => rho.sandwichedRenyiMutualInformationE alpha.1)
          Set.univ)
    (hstateTendsto :
      ∀ psi : Ket (a × a),
        Tendsto
          (fun alpha : {alpha : ℝ // 1 < alpha} =>
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE alpha.1)
          MState.relativeEntropyHighAlphaRightToOne
          (nhds (N.entanglementAssistedMutualInformation psi : EReal)))
    (hstateMono :
      ∀ psi : Ket (a × a), ∀ alpha beta : {alpha : ℝ // 1 < alpha},
        alpha.1 ≤ beta.1 →
          (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE alpha.1 ≤
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE beta.1) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  refine
    N.sandwichedRenyiMutualInformationE_tendsto_information_of_state_limit_and_mosonyi_hiai
      ?_ hstateTendsto hstateMono
  intro alpha
  exact N.inputSandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_state
    alpha (hstateUSC alpha)

/-- Channel alpha-to-one theorem from the full-rank approximation and
derivative-sign bridges.

The state optimized convergence is kept as an explicit hypothesis.  The
full-rank approximation lower bound supplies optimized upper semicontinuity,
and the derivative-sign hypotheses supply optimized monotonicity in the
high-parameter variable. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information_of_state_limit_and_posDef_candidate_approx_deriv_nonneg
    [Nonempty a]
    (hposA :
      ∀ psi : Ket (a × a),
        (N.hypothesisTestingOutputState psi).traceRight.m.PosDef)
    (happrox :
      ∀ gamma : {gamma : ℝ // 1 < gamma},
        ∀ rho : MState (a × b), ∀ sigmaB : MState b,
          (⨅ tauB : {tauB : MState b // tauB.m.PosDef},
            rho.sandwichedRenyiMutualInformationCandidateE tauB.1 gamma.1) ≤
              rho.sandwichedRenyiMutualInformationCandidateE sigmaB gamma.1)
    (hstateTendsto :
      ∀ psi : Ket (a × a),
        Tendsto
          (fun alpha : {alpha : ℝ // 1 < alpha} =>
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE alpha.1)
          MState.relativeEntropyHighAlphaRightToOne
          (nhds (N.entanglementAssistedMutualInformation psi : EReal)))
    (hcont :
      ∀ psi : Ket (a × a),
        ∀ sigmaB : {sigmaB : MState b // sigmaB.m.PosDef},
          ContinuousOn
            (fun alpha : ℝ =>
              MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                (N.hypothesisTestingOutputState psi)
                ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB.1).m
                ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB.1).psd alpha)
            (Set.Ioi (1 : ℝ)))
    (hdiff :
      ∀ psi : Ket (a × a),
        ∀ sigmaB : {sigmaB : MState b // sigmaB.m.PosDef},
          DifferentiableOn ℝ
            (fun alpha : ℝ =>
              MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                (N.hypothesisTestingOutputState psi)
                ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB.1).m
                ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB.1).psd alpha)
            (Set.Ioi (1 : ℝ)))
    (hderiv :
      ∀ psi : Ket (a × a),
        ∀ sigmaB : {sigmaB : MState b // sigmaB.m.PosDef},
          ∀ alpha : ℝ, 1 < alpha →
            0 ≤ deriv
              (fun beta : ℝ =>
                MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                  (N.hypothesisTestingOutputState psi)
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB.1).m
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB.1).psd beta)
              alpha) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  refine
    N.sandwichedRenyiMutualInformationE_tendsto_information_of_state_limit_and_mosonyi_hiai
      ?_ hstateTendsto ?_
  · intro alpha
    exact
      N.inputSandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_posDef_candidate_approx
        alpha hposA (happrox alpha)
  · intro psi
    exact
      (N.hypothesisTestingOutputState psi)
        |>.sandwichedRenyiMutualInformationE_mono_of_posDef_candidate_approx_and_deriv_nonneg
          (hposA psi)
          (fun gamma => happrox gamma (N.hypothesisTestingOutputState psi))
          (hcont psi) (hdiff psi) (hderiv psi)

/-- Channel alpha-to-one theorem after the full-rank side-state approximation
has been proved internally.  The remaining analytic inputs are state optimized
convergence and the derivative-sign package for full-rank side states. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information_of_state_limit_and_fullRankApprox_deriv_nonneg
    [Nonempty a]
    (hposA :
      ∀ psi : Ket (a × a),
        (N.hypothesisTestingOutputState psi).traceRight.m.PosDef)
    (hstateTendsto :
      ∀ psi : Ket (a × a),
        Tendsto
          (fun alpha : {alpha : ℝ // 1 < alpha} =>
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE alpha.1)
          MState.relativeEntropyHighAlphaRightToOne
          (nhds (N.entanglementAssistedMutualInformation psi : EReal)))
    (hcont :
      ∀ psi : Ket (a × a),
        ∀ sigmaB : {sigmaB : MState b // sigmaB.m.PosDef},
          ContinuousOn
            (fun alpha : ℝ =>
              MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                (N.hypothesisTestingOutputState psi)
                ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB.1).m
                ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB.1).psd alpha)
            (Set.Ioi (1 : ℝ)))
    (hdiff :
      ∀ psi : Ket (a × a),
        ∀ sigmaB : {sigmaB : MState b // sigmaB.m.PosDef},
          DifferentiableOn ℝ
            (fun alpha : ℝ =>
              MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                (N.hypothesisTestingOutputState psi)
                ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB.1).m
                ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB.1).psd alpha)
            (Set.Ioi (1 : ℝ)))
    (hderiv :
      ∀ psi : Ket (a × a),
        ∀ sigmaB : {sigmaB : MState b // sigmaB.m.PosDef},
          ∀ alpha : ℝ, 1 < alpha →
            0 ≤ deriv
              (fun beta : ℝ =>
                MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                  (N.hypothesisTestingOutputState psi)
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB.1).m
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB.1).psd beta)
              alpha) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  refine
    N.sandwichedRenyiMutualInformationE_tendsto_information_of_state_limit_and_mosonyi_hiai
      ?_ hstateTendsto ?_
  · intro alpha
    exact
      N.inputSandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_fullRankApprox
        alpha hposA
  · intro psi
    exact
      (N.hypothesisTestingOutputState psi)
        |>.sandwichedRenyiMutualInformationE_mono_of_posDef_candidate_approx_and_deriv_nonneg
          (hposA psi)
          (fun gamma =>
            MState.posDef_candidate_approx_of_fullRankApprox
              (N.hypothesisTestingOutputState psi) gamma.2)
          (hcont psi) (hdiff psi) (hderiv psi)

/-- Source-faithful Khatri--Wilde channel theorem with the state monotonicity
and endpoint obligations reduced to the finite supported sandwiched-Renyi
branch.

Unlike `sandwichedRenyiMutualInformationE_tendsto_information_of_candidate_husc_and_finite_mono`,
this theorem keeps the Mosonyi--Hiai hypothesis in the book's optimized
pure-input form. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information_of_optimized_husc_and_finite_mono
    [Nonempty a]
    (husc :
      ∀ alpha : {alpha : ℝ // 1 < alpha},
        UpperSemicontinuousOn
          (fun psi : Ket (a × a) =>
            N.inputSandwichedRenyiMutualInformationE psi alpha.1)
          Set.univ)
    (hfinite :
      ∀ psi : Ket (a × a), ∀ sigmaB : MState b,
        ∀ alpha beta : {alpha : ℝ // 1 < alpha},
          alpha.1 ≤ beta.1 →
            ∀ _hSupport : Matrix.Supports (N.hypothesisTestingOutputState psi).m
                ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m,
              MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                  (N.hypothesisTestingOutputState psi)
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                  alpha.1 ≤
                MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                  (N.hypothesisTestingOutputState psi)
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                  beta.1) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  refine
    N.sandwichedRenyiMutualInformationE_tendsto_information_of_optimized_mosonyi_hiai
      husc ?_ ?_
  · intro psi alpha beta hab
    have : Nonempty b := by
      rcases (N.hypothesisTestingOutputState psi).nonempty with ⟨w⟩
      exact ⟨w.2⟩
    refine
      (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE_mono_of_candidate_mono
        ?_ alpha beta hab
    intro sigmaB alpha' beta' hab'
    exact
      (N.hypothesisTestingOutputState psi)
        |>.sandwichedRenyiMutualInformationCandidateE_mono_of_highAlphaFinite_mono
          sigmaB hab' (hfinite psi sigmaB alpha' beta' hab')
  · intro psi
    simpa [CPTPOp.entanglementAssistedMutualInformation,
    CPTPOp.entanglementAssistedOutputState, CPTPOp.hypothesisTestingOutputState] using
      MState.sandwichedRenyiMutualInformationE_iInf_eq_mutualInformation_of_chainRule_and_finite_mono
        (N.hypothesisTestingOutputState psi) (hfinite psi)

/-- Source-faithful Khatri--Wilde channel theorem reduced to the
support-compressed finite monotonicity branch.

This keeps the Mosonyi--Hiai hypothesis on the optimized pure-input function,
while moving the remaining sandwiched-Renyi monotonicity proof to the strictly
positive reference support of each `psi_R ⊗ sigma_B`. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information_of_optimized_husc_and_supportCompress_mono
    [Nonempty a]
    (husc :
      ∀ alpha : {alpha : ℝ // 1 < alpha},
        UpperSemicontinuousOn
          (fun psi : Ket (a × a) =>
            N.inputSandwichedRenyiMutualInformationE psi alpha.1)
          Set.univ)
    (hcompressed :
      ∀ psi : Ket (a × a), ∀ sigmaB : MState b,
        ∀ alpha beta : {alpha : ℝ // 1 < alpha},
          alpha.1 ≤ beta.1 →
            ∀ hSupport : Matrix.Supports (N.hypothesisTestingOutputState psi).m
                ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m,
              MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                  (_root_.QIT.psdSupportCompressedState
                    (N.hypothesisTestingOutputState psi)
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                    hSupport)
                  (psdSupportCompress
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m)
                  (_root_.QIT.psdSupportCompress_self_posDef _
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd).posSemidef
                  alpha.1 ≤
                MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                  (_root_.QIT.psdSupportCompressedState
                    (N.hypothesisTestingOutputState psi)
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                    hSupport)
                  (psdSupportCompress
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m)
                  (_root_.QIT.psdSupportCompress_self_posDef _
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd).posSemidef
                  beta.1) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  refine
    N.sandwichedRenyiMutualInformationE_tendsto_information_of_optimized_husc_and_finite_mono
      husc ?_
  intro psi sigmaB alpha beta hab hSupport
  exact
    MState.sandwichedRenyiPSDReferenceHighAlphaFinite_mono_of_supportCompress_mono
      (N.hypothesisTestingOutputState psi)
      ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
      hSupport
      (hcompressed psi sigmaB alpha beta hab hSupport)

/-- Source-faithful Khatri--Wilde channel theorem with the pure-input
Mosonyi--Hiai continuity hypothesis reduced to state-level optimized upper
semicontinuity.

This matches the proof route in `Chapters/EA_capacity.tex:1902-1906`: the
function used in Mosonyi--Hiai is already optimized over `sigmaB`; continuity
in `psi` is obtained by composing state-level upper semicontinuity with the
continuous channel output-state map. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information_of_state_husc_and_supportCompress_mono
    [Nonempty a]
    (hstateUSC :
      ∀ alpha : {alpha : ℝ // 1 < alpha},
        UpperSemicontinuousOn
          (fun rho : MState (a × b) => rho.sandwichedRenyiMutualInformationE alpha.1)
          Set.univ)
    (hcompressed :
      ∀ psi : Ket (a × a), ∀ sigmaB : MState b,
        ∀ alpha beta : {alpha : ℝ // 1 < alpha},
          alpha.1 ≤ beta.1 →
            ∀ hSupport : Matrix.Supports (N.hypothesisTestingOutputState psi).m
                ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m,
              MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                  (_root_.QIT.psdSupportCompressedState
                    (N.hypothesisTestingOutputState psi)
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                    hSupport)
                  (psdSupportCompress
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m)
                  (_root_.QIT.psdSupportCompress_self_posDef _
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd).posSemidef
                  alpha.1 ≤
                MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                  (_root_.QIT.psdSupportCompressedState
                    (N.hypothesisTestingOutputState psi)
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                    hSupport)
                  (psdSupportCompress
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m)
                  (_root_.QIT.psdSupportCompress_self_posDef _
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd).posSemidef
                  beta.1) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  refine
    N.sandwichedRenyiMutualInformationE_tendsto_information_of_optimized_husc_and_supportCompress_mono
      ?_ hcompressed
  intro alpha
  exact N.inputSandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_state
    alpha (hstateUSC alpha)

/-- Source-faithful Khatri--Wilde channel theorem with the Mosonyi--Hiai
continuity hypothesis reduced first to state-level optimized upper
semicontinuity, and then to fixed side-state candidates.

The proof still applies Mosonyi--Hiai to the optimized function
`psi ↦ inf_sigmaB D~_alpha(...)`; fixed-candidate upper semicontinuity is only a
supporting route for proving that optimized-function hypothesis. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information_of_state_candidate_husc_and_supportCompress_mono
    [Nonempty a]
    (hstateCandidateUSC :
      ∀ alpha : {alpha : ℝ // 1 < alpha}, ∀ sigmaB : MState b,
        UpperSemicontinuousOn
          (fun rho : MState (a × b) =>
            rho.sandwichedRenyiMutualInformationCandidateE sigmaB alpha.1)
          Set.univ)
    (hcompressed :
      ∀ psi : Ket (a × a), ∀ sigmaB : MState b,
        ∀ alpha beta : {alpha : ℝ // 1 < alpha},
          alpha.1 ≤ beta.1 →
            ∀ hSupport : Matrix.Supports (N.hypothesisTestingOutputState psi).m
                ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m,
              MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                  (_root_.QIT.psdSupportCompressedState
                    (N.hypothesisTestingOutputState psi)
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                    hSupport)
                  (psdSupportCompress
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m)
                  (_root_.QIT.psdSupportCompress_self_posDef _
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd).posSemidef
                  alpha.1 ≤
                MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                  (_root_.QIT.psdSupportCompressedState
                    (N.hypothesisTestingOutputState psi)
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                    hSupport)
                  (psdSupportCompress
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m)
                  (_root_.QIT.psdSupportCompress_self_posDef _
                    ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd).posSemidef
                  beta.1) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  refine
    N.sandwichedRenyiMutualInformationE_tendsto_information_of_state_husc_and_supportCompress_mono
      ?_ hcompressed
  intro alpha
  exact MState.sandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_candidate
    (fun rho : MState (a × b) => rho) alpha (hstateCandidateUSC alpha)

/-- Khatri--Wilde channel `inf_alpha` identification from fixed-candidate upper
semicontinuity and finite-branch monotonicity.

This is a stronger sufficient route to the Mosonyi--Hiai continuity hypothesis,
not the literal optimized-function route stated in the source. -/
theorem sandwichedRenyiMutualInformationE_iInf_eq_information_of_candidate_husc_and_finite_mono
    [Nonempty a]
    (husc :
      ∀ alpha : {alpha : ℝ // 1 < alpha}, ∀ sigmaB : MState b,
        UpperSemicontinuousOn
          (fun psi : Ket (a × a) =>
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
              sigmaB alpha.1)
          Set.univ)
    (hfinite :
      ∀ psi : Ket (a × a), ∀ sigmaB : MState b,
        ∀ alpha beta : {alpha : ℝ // 1 < alpha},
          alpha.1 ≤ beta.1 →
            ∀ _hSupport : Matrix.Supports (N.hypothesisTestingOutputState psi).m
                ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m,
              MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                  (N.hypothesisTestingOutputState psi)
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                  alpha.1 ≤
                MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                  (N.hypothesisTestingOutputState psi)
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                  beta.1) :
    (⨅ alpha : {alpha : ℝ // 1 < alpha},
        N.sandwichedRenyiMutualInformationE alpha.1) =
      (N.entanglementAssistedInformation : EReal) := by
  refine N.sandwichedRenyiMutualInformationE_iInf_eq_information_of_mosonyi_hiai ?_ ?_
  · exact
      N.sandwichedRenyiMutualInformationE_iInf_iSup_eq_iSup_iInf_of_candidate_husc_and_finite_mono
        husc hfinite
  · intro psi
    simpa [CPTPOp.entanglementAssistedMutualInformation,
    CPTPOp.entanglementAssistedOutputState, CPTPOp.hypothesisTestingOutputState] using
      MState.sandwichedRenyiMutualInformationE_iInf_eq_mutualInformation_of_chainRule_and_finite_mono
        (N.hypothesisTestingOutputState psi) (hfinite psi)

/-- Source-shaped channel alpha-to-one theorem after the pure-input
Mosonyi--Hiai exchange has been reduced to fixed-candidate upper semicontinuity
and finite-branch sandwiched-Renyi monotonicity. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information_of_candidate_husc_and_finite_mono
    [Nonempty a]
    (husc :
      ∀ alpha : {alpha : ℝ // 1 < alpha}, ∀ sigmaB : MState b,
        UpperSemicontinuousOn
          (fun psi : Ket (a × a) =>
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
              sigmaB alpha.1)
          Set.univ)
    (hfinite :
      ∀ psi : Ket (a × a), ∀ sigmaB : MState b,
        ∀ alpha beta : {alpha : ℝ // 1 < alpha},
          alpha.1 ≤ beta.1 →
            ∀ _hSupport : Matrix.Supports (N.hypothesisTestingOutputState psi).m
                ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m,
              MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                  (N.hypothesisTestingOutputState psi)
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                  alpha.1 ≤
                MState.sandwichedRenyiPSDReferenceHighAlphaFinite
                  (N.hypothesisTestingOutputState psi)
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m
                  ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                  beta.1) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  refine N.sandwichedRenyiMutualInformationE_tendsto_information_of_iInf_eq ?_ ?_
  · intro alpha beta hab
    refine N.sandwichedRenyiMutualInformationE_mono_of_candidate_mono ?_ alpha beta hab
    intro psi sigmaB alpha' beta' hab'
    exact
      (N.hypothesisTestingOutputState psi)
        |>.sandwichedRenyiMutualInformationCandidateE_mono_of_highAlphaFinite_mono
          sigmaB hab' (hfinite psi sigmaB alpha' beta' hab')
  · exact
      N.sandwichedRenyiMutualInformationE_iInf_eq_information_of_candidate_husc_and_finite_mono
        husc hfinite

/-- A maximizing ordinary input also has the optimized state sandwiched-Renyi
limit, provided the output state satisfies the candidate-wise source lower
bound near `alpha = 1+`. -/
theorem exists_inputSandwichedRenyiMutualInformationE_tendsto_information_of_eventually_candidate_lower
    [Nonempty a]
    (hlower :
      ∀ psi : Ket (a × a),
        N.entanglementAssistedInformation =
          N.entanglementAssistedMutualInformation psi →
        ∀ᶠ alpha in MState.relativeEntropyHighAlphaRightToOne,
          ∀ sigmaB : MState b,
            (mutualInformation (N.hypothesisTestingOutputState psi) : EReal) ≤
              (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
                sigmaB alpha.1) :
    Exists fun psi : Ket (a × a) =>
      Tendsto
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
          N.inputSandwichedRenyiMutualInformationE psi alpha.1)
        MState.relativeEntropyHighAlphaRightToOne
        (nhds (N.entanglementAssistedInformation : EReal)) := by
  match N.exists_entanglementAssistedInformation_maximizer with
  | Exists.intro psi hpsi =>
      refine Exists.intro psi ?_
      have hstate :
          Tendsto
            (fun alpha : {alpha : ℝ // 1 < alpha} =>
              (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE
                alpha.1)
            MState.relativeEntropyHighAlphaRightToOne
            (nhds (mutualInformation (N.hypothesisTestingOutputState psi) : EReal)) :=
        MState.sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_eventually_candidate_lower
          (N.hypothesisTestingOutputState psi) (hlower psi hpsi)
      simpa [CPTPOp.inputSandwichedRenyiMutualInformationE,
        CPTPOp.entanglementAssistedMutualInformation,
        CPTPOp.entanglementAssistedOutputState,
        CPTPOp.hypothesisTestingOutputState, hpsi] using hstate

/-- Channel-level squeeze from a `sup_psi` upper bound near `alpha = 1+`.

The lower squeeze is any fixed input whose optimized state sandwiched-Renyi
mutual information tends to the ordinary channel mutual information.  The
upper squeeze is the Mosonyi minimax / optimization-limit exchange, taken here
as a hypothesis. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information_of_input_tendsto_of_eventually_upper
    [Nonempty a]
    {psi : Ket (a × a)}
    (hfixed :
      Tendsto
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
          N.inputSandwichedRenyiMutualInformationE psi alpha.1)
        MState.relativeEntropyHighAlphaRightToOne
        (nhds (N.entanglementAssistedInformation : EReal)))
    (hupper :
      ∀ᶠ alpha in MState.relativeEntropyHighAlphaRightToOne,
        N.sandwichedRenyiMutualInformationE alpha.1 ≤
          (N.entanglementAssistedInformation : EReal)) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  have hconst :
      Tendsto
        (fun _alpha : {alpha : ℝ // 1 < alpha} =>
          (N.entanglementAssistedInformation : EReal))
        MState.relativeEntropyHighAlphaRightToOne
        (nhds (N.entanglementAssistedInformation : EReal)) := tendsto_const_nhds
  have hlower :
      ∀ alpha : {alpha : ℝ // 1 < alpha},
        N.inputSandwichedRenyiMutualInformationE psi alpha.1 ≤
          N.sandwichedRenyiMutualInformationE alpha.1 := by
    intro alpha
    exact N.inputSandwichedRenyiMutualInformationE_le_channel psi alpha.1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hfixed hconst
    (Filter.Eventually.of_forall hlower) hupper

/-- Final assembly handoff: candidate-wise state lower bounds plus a
channel-wide upper bound near `alpha = 1+` imply the source-shaped channel
alpha-to-one limit.

The two hypotheses are the remaining analytic pieces of the source route: the
`inf_sigmaB` lower half for maximizing output states and the Mosonyi minimax
upper half for the pure-input supremum. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information_of_eventually_candidate_lower_of_eventually_upper
    [Nonempty a]
    (hlower :
      ∀ psi : Ket (a × a),
        N.entanglementAssistedInformation =
          N.entanglementAssistedMutualInformation psi →
        ∀ᶠ alpha in MState.relativeEntropyHighAlphaRightToOne,
          ∀ sigmaB : MState b,
            (mutualInformation (N.hypothesisTestingOutputState psi) : EReal) ≤
              (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
                sigmaB alpha.1)
    (hupper :
      ∀ᶠ alpha in MState.relativeEntropyHighAlphaRightToOne,
        N.sandwichedRenyiMutualInformationE alpha.1 ≤
          (N.entanglementAssistedInformation : EReal)) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  obtain ⟨psi, hfixed⟩ :=
    N.exists_inputSandwichedRenyiMutualInformationE_tendsto_information_of_eventually_candidate_lower
      hlower
  exact
    N.sandwichedRenyiMutualInformationE_tendsto_information_of_input_tendsto_of_eventually_upper
      hfixed hupper

/-- Channel-level handoff from fixed-candidate endpoint/monotonicity data.

This version exposes the analytic obligations in the same shape as the state
optimized theorem: for every side-information candidate of every maximizing
output state, prove endpoint convergence, endpoint lower bound, and
high-`alpha` monotonicity.  Together with the Mosonyi/minimax upper bound on
the channel supremum, this yields the channel alpha-to-one limit. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information_of_candidate_limits_of_eventually_upper
    [Nonempty a]
    (hlower :
      ∀ psi : Ket (a × a),
        N.entanglementAssistedInformation =
          N.entanglementAssistedMutualInformation psi →
        ∀ sigmaB : MState b, ∃ limit : EReal,
          Tendsto
            (fun alpha : {alpha : ℝ // 1 < alpha} =>
              (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
                sigmaB alpha.1)
            MState.relativeEntropyHighAlphaRightToOne
            (nhds limit) ∧
          (mutualInformation (N.hypothesisTestingOutputState psi) : EReal) ≤ limit ∧
          ∀ alpha beta : {alpha : ℝ // 1 < alpha},
            alpha.1 ≤ beta.1 →
              (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
                sigmaB alpha.1 ≤
              (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
                sigmaB beta.1)
    (hupper :
      ∀ᶠ alpha in MState.relativeEntropyHighAlphaRightToOne,
        N.sandwichedRenyiMutualInformationE alpha.1 ≤
          (N.entanglementAssistedInformation : EReal)) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  refine
    N.sandwichedRenyiMutualInformationE_tendsto_information_of_eventually_candidate_lower_of_eventually_upper
      ?_ hupper
  intro psi hpsi
  have hlower_eventual :
      ∀ᶠ alpha in MState.relativeEntropyHighAlphaRightToOne,
        ∀ sigmaB : MState b,
          (mutualInformation (N.hypothesisTestingOutputState psi) : EReal) ≤
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
              sigmaB alpha.1 := by
    exact Filter.Eventually.of_forall fun alpha sigmaB => by
      obtain ⟨limit, htend, hlowerLimit, hmono⟩ := hlower psi hpsi sigmaB
      exact
        (N.hypothesisTestingOutputState psi)
          |>.sandwichedRenyiMutualInformationCandidateE_lower_of_tendsto_of_monotone
              sigmaB htend hmono hlowerLimit alpha
  exact hlower_eventual

/-- Channel-level handoff with the actual PSD-reference endpoints in the
state optimized `inf_sigmaB` step.

For every ordinary maximizer `psi`, the first two hypotheses are precisely the
state-side mathematical obligations left after proving fixed-candidate endpoint
convergence: endpoint lower bounds against all side states and high-`alpha`
monotonicity of each fixed candidate.  The last hypothesis is the separate
Mosonyi/minimax upper bound for the pure-input channel supremum. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information_of_endpoint_lower_and_monotone_of_eventually_upper
    [Nonempty a]
    (hlower :
      ∀ psi : Ket (a × a),
        N.entanglementAssistedInformation =
          N.entanglementAssistedMutualInformation psi →
        ∀ sigmaB : MState b,
          (mutualInformation (N.hypothesisTestingOutputState psi) : EReal) ≤
            MState.relativeEntropyPSDReferenceE (N.hypothesisTestingOutputState psi)
              ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m
              ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd)
    (hmono :
      ∀ psi : Ket (a × a),
        N.entanglementAssistedInformation =
          N.entanglementAssistedMutualInformation psi →
        ∀ sigmaB : MState b, ∀ alpha beta : {alpha : ℝ // 1 < alpha},
          alpha.1 ≤ beta.1 →
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
              sigmaB alpha.1 ≤
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
              sigmaB beta.1)
    (hupper :
      ∀ᶠ alpha in MState.relativeEntropyHighAlphaRightToOne,
        N.sandwichedRenyiMutualInformationE alpha.1 ≤
          (N.entanglementAssistedInformation : EReal)) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  obtain ⟨psi, hpsi⟩ := N.exists_entanglementAssistedInformation_maximizer
  have hstate :
      Tendsto
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
          (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE alpha.1)
        MState.relativeEntropyHighAlphaRightToOne
        (nhds (mutualInformation (N.hypothesisTestingOutputState psi) : EReal)) :=
    (N.hypothesisTestingOutputState psi)
      |>.sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_endpoint_lower_and_monotone
        (hlower psi hpsi) (hmono psi hpsi)
  have hfixed :
      Tendsto
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
          N.inputSandwichedRenyiMutualInformationE psi alpha.1)
        MState.relativeEntropyHighAlphaRightToOne
        (nhds (N.entanglementAssistedInformation : EReal)) := by
    simpa [CPTPOp.inputSandwichedRenyiMutualInformationE,
      CPTPOp.entanglementAssistedMutualInformation,
      CPTPOp.entanglementAssistedOutputState,
      CPTPOp.hypothesisTestingOutputState, hpsi] using hstate
  exact
    N.sandwichedRenyiMutualInformationE_tendsto_information_of_input_tendsto_of_eventually_upper
      hfixed hupper

/-- Channel-level handoff after discharging unsupported side-information
candidates at the state level.

This exposes only the state lower-bound branch:
for supported `rho_A \otimes sigma_B` references, prove the finite trace-log
chain-rule inequality.  Candidate monotonicity and the channel supremum upper
bound remain as separate source obligations. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information_of_supported_traceLog_lower_monotone_of_eventually_upper
    [Nonempty a]
    (hsupportedLower :
      ∀ psi : Ket (a × a),
        N.entanglementAssistedInformation =
          N.entanglementAssistedMutualInformation psi →
        ∀ sigmaB : MState b,
          ∀ hSupport : Matrix.Supports (N.hypothesisTestingOutputState psi).m
              ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m,
            (mutualInformation (N.hypothesisTestingOutputState psi) : EReal) ≤
              (MState.relativeEntropyPSDReferenceTraceLogFinite
                (N.hypothesisTestingOutputState psi)
                ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).m
                ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd
                hSupport : EReal))
    (hmono :
      ∀ psi : Ket (a × a),
        N.entanglementAssistedInformation =
          N.entanglementAssistedMutualInformation psi →
        ∀ sigmaB : MState b, ∀ alpha beta : {alpha : ℝ // 1 < alpha},
          alpha.1 ≤ beta.1 →
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
              sigmaB alpha.1 ≤
            (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationCandidateE
              sigmaB beta.1)
    (hupper :
      ∀ᶠ alpha in MState.relativeEntropyHighAlphaRightToOne,
        N.sandwichedRenyiMutualInformationE alpha.1 ≤
          (N.entanglementAssistedInformation : EReal)) :
    Tendsto
      (fun alpha : {alpha : ℝ // 1 < alpha} =>
        N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  obtain ⟨psi, hpsi⟩ := N.exists_entanglementAssistedInformation_maximizer
  have hstate :
      Tendsto
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
          (N.hypothesisTestingOutputState psi).sandwichedRenyiMutualInformationE alpha.1)
        MState.relativeEntropyHighAlphaRightToOne
        (nhds (mutualInformation (N.hypothesisTestingOutputState psi) : EReal)) :=
    (N.hypothesisTestingOutputState psi)
      |>.sandwichedRenyiMutualInformationE_tendsto_mutualInformation_of_supported_traceLog_lower_and_monotone
        (hsupportedLower psi hpsi) (hmono psi hpsi)
  have hfixed :
      Tendsto
        (fun alpha : {alpha : ℝ // 1 < alpha} =>
          N.inputSandwichedRenyiMutualInformationE psi alpha.1)
        MState.relativeEntropyHighAlphaRightToOne
        (nhds (N.entanglementAssistedInformation : EReal)) := by
    simpa [CPTPOp.inputSandwichedRenyiMutualInformationE,
      CPTPOp.entanglementAssistedMutualInformation,
      CPTPOp.entanglementAssistedOutputState,
      CPTPOp.hypothesisTestingOutputState, hpsi] using hstate
  exact
    N.sandwichedRenyiMutualInformationE_tendsto_information_of_input_tendsto_of_eventually_upper
      hfixed hupper

/-- The unconditional sandwiched-Rényi channel mutual-information `α → 1+` limit
(Khatri–Wilde `EA_capacity.tex:1869-1907`): `Ĩ_α(N) → I(N)` as `α → 1+`.

Assembled unconditionally from Bridge A (α-monotonicity, threaded through the
support-compressed finite branch via
`sandwichedRenyiPSDReferenceHighAlphaFinite_mono_posSemidef_state_posDef_reference`)
and Bridge B (optimized state upper semicontinuity at a singular left marginal,
`MState.sandwichedRenyiMutualInformationE_upperSemicontinuousOn`), fed into the
`..._tendsto_information_of_state_husc_and_supportCompress_mono`, whose
internal Mosonyi–Hiai + state-limit chain carries the pointwise optimized
endpoint. -/
theorem sandwichedRenyiMutualInformationE_tendsto_information [Nonempty a] :
    Tendsto (fun alpha : {alpha : ℝ // 1 < alpha} =>
      N.sandwichedRenyiMutualInformationE alpha.1)
      MState.relativeEntropyHighAlphaRightToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  apply N.sandwichedRenyiMutualInformationE_tendsto_information_of_state_husc_and_supportCompress_mono
  · -- hstateUSC (Bridge B): the unconditional state optimized USC.
    intro alpha
    exact MState.sandwichedRenyiMutualInformationE_upperSemicontinuousOn alpha.2
  · -- hcompressed (Bridge A): the support-compressed finite-branch α-monotonicity.
    intro psi sigmaB alpha beta hab hSupport
    exact MState.sandwichedRenyiPSDReferenceHighAlphaFinite_mono_posSemidef_state_posDef_reference
      (_root_.QIT.psdSupportCompressedState (N.hypothesisTestingOutputState psi)
        ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd hSupport)
      (_root_.QIT.psdSupportCompress_self_posDef _
        ((N.hypothesisTestingOutputState psi).traceRight.prod sigmaB).psd)
      alpha.2 beta.2 hab

end CPTPOp

end
