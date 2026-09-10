/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Renyi.ConditionalRenyiClassical
public import QuantumLib.QIT.Information.Renyi.ConditionalPetzRenyiAlternative
public import QuantumLib.QIT.Util.Order.EReal

/-!
# Petz Renyi conditioning on a classical register

This module records the Petz part of `cond.tex:214-249`.  The public state is
presented as an ensemble `Y → (A x B)`; the shared layer performs the finite
reindexing to `A x (B x Y)`.  The two declarations at the end retain the
extended-real definitions, while the lemmas immediately before them expose the
block and power identities used by the source proof.
-/

@[expose] public section

open scoped BigOperators ComplexOrder MatrixOrder NNReal
open Matrix

noncomputable section
universe u v w
variable {A : Type u} {B : Type v} {Y : Type w}
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable [Fintype Y] [DecidableEq Y]

open QIT

namespace MState

/-- For `0 < α < 1`, the Petz trace term against a state reference is at most the `α`-th power of
the closed-form optimum. -/
private theorem petz_conditionalTrace_le_closed_of_lt_one
    (ρ : MState (A × (B × Y))) (σ : MState (B × Y))
    (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    ρ.conditionalPetzRenyiTraceTerm σ α ≤
      (ρ.conditionalPetzRenyiUpClosedTrace α) ^ α := by
  rw [ρ.conditionalPetzRenyiTraceTerm_eq_traceLeft]
  have hpq : (1 / α).HolderConjugate (1 / (1 - α)) := by
    simpa [one_div] using Real.HolderConjugate.inv_one_sub_inv hα_pos hα_lt_one
  have htr : σ.m.trace.re = 1 := by
    rw [σ.tr']
    simp
  have hr : 1 - α = 1 / (1 / (1 - α)) := by
    field_simp [sub_ne_zero.mpr hα_lt_one.ne]
  have hholder :=
    psd_trace_rpow_holder_variational_upper
      (M := ρ.conditionalPetzRenyiUpTraceMatrix α) (N := σ.m)
      (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α) σ.psd htr hpq hr
  have hrecip : 1 / (1 / α) = α := by field_simp [hα_pos.ne']
  simpa [psdSchattenPNorm, Internal.psdSchattenExpression,
    conditionalPetzRenyiUpClosedTrace,
    conditionalPetzRenyiUpClosedTrace_eq_psdTracePower, hrecip] using hholder

private theorem petz_up_candidateE_eq_coe_fullReference
    (E : MEnsemble (A × B) Y) (σ : MState (B × Y))
    (hσ : σ.m.PosDef) (α : ℝ) (hα_pos : 0 < α)
    (hα_lt_one : α < 1) (hα_ne_one : α ≠ 1) :
    -(MState.cqConditioningState E).petzRenyiReferenceE
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef (a := A) σ)
        α hα_pos hα_ne_one =
      (MState.cqConditioningState E).conditionalPetzRenyiEntropyCandidateFullReference
        σ hσ α hα_pos hα_ne_one := by
  let ρ := MState.cqConditioningState E
  let τ := identityTensorStateMatrix (a := A) σ
  have hτ : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := A) σ hσ
  have hq : 0 < (CFC.rpow ρ.m α * CFC.rpow τ (1 - α)).trace.re := by
    simpa [ρ, τ, MState.conditionalPetzRenyiTraceTerm] using
      ρ.conditionalPetzRenyiTraceTerm_pos_of_fullReference σ hσ α
  have he := petzRenyiReferenceE_eq_coe_of_lt_one_of_trace_ne_zero
    ρ τ hτ.posSemidef α hα_pos hα_ne_one hα_lt_one hq.ne'
  rw [he]
  have hreal :
      -ρ.petzRenyiReferenceFinite τ hτ.posSemidef α hα_pos hα_ne_one =
        (1 / (1 - α)) * log2
          ((CFC.rpow ρ.m α * CFC.rpow τ (1 - α)).trace.re) := by
    unfold petzRenyiReferenceFinite
    have hleft : α - 1 ≠ 0 := sub_ne_zero.mpr hα_ne_one
    have hright : 1 - α ≠ 0 := sub_ne_zero.mpr hα_ne_one.symm
    have hcoef : -(1 / (α - 1)) = 1 / (1 - α) := by
      field_simp [hleft, hright]
      ring
    calc
      -(1 / (α - 1) *
          log2 ((CFC.rpow ρ.m α * CFC.rpow τ (1 - α)).trace.re)) =
          (-(1 / (α - 1))) *
            log2 ((CFC.rpow ρ.m α * CFC.rpow τ (1 - α)).trace.re) := by ring
      _ = _ := by rw [hcoef]
  simpa [EReal.coe_neg, ρ, τ, MState.conditionalPetzRenyiTraceTerm] using
    congrArg (fun x : ℝ => (x : EReal)) hreal

private theorem petz_up_candidateE_le_closed_of_lt_one
    (E : MEnsemble (A × B) Y) (σ : MState (B × Y)) (α : ℝ)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) (hα_ne_one : α ≠ 1) :
    -(MState.cqConditioningState E).petzRenyiReferenceE
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef (a := A) σ)
        α hα_pos hα_ne_one ≤
      ((MState.cqConditioningState E).conditionalPetzRenyiUpAlternative α : EReal) := by
  let ρ := MState.cqConditioningState E
  let τ := identityTensorStateMatrix (a := A) σ
  have hτ : τ.PosSemidef := identityTensorStateMatrix_posSemidef (a := A) σ
  have hq_nonneg : 0 ≤ (CFC.rpow ρ.m α * CFC.rpow τ (1 - α)).trace.re := by
    simpa [ρ, τ, MState.conditionalPetzRenyiTraceTerm] using
      ρ.conditionalPetzRenyiTraceTerm_nonneg σ α
  by_cases hqzero : (CFC.rpow ρ.m α * CFC.rpow τ (1 - α)).trace.re = 0
  · rw [petzRenyiReferenceE_eq_top_of_lt_one_of_trace_eq_zero _ _ hτ
        α hα_pos hα_ne_one hα_lt_one hqzero]
    simp
  · have hq_pos : 0 < (CFC.rpow ρ.m α * CFC.rpow τ (1 - α)).trace.re :=
      lt_of_le_of_ne hq_nonneg (Ne.symm hqzero)
    rw [petzRenyiReferenceE_eq_coe_of_lt_one_of_trace_ne_zero _ _ hτ
      α hα_pos hα_ne_one hα_lt_one hqzero]
    apply EReal.coe_le_coe_iff.mpr
    have htrace_le := petz_conditionalTrace_le_closed_of_lt_one
      ρ σ α hα_pos hα_lt_one
    have hclosed_pos : 0 < ρ.conditionalPetzRenyiUpClosedTrace α :=
      ρ.conditionalPetzRenyiUpClosedTrace_pos α
    have hlog_le :
        log2 ((CFC.rpow ρ.m α * CFC.rpow τ (1 - α)).trace.re) ≤
          α * log2 (ρ.conditionalPetzRenyiUpClosedTrace α) := by
      have h := log2_mono_of_pos hq_pos htrace_le
      simpa [log2_rpow_pos hclosed_pos] using h
    have hcoef : 0 ≤ 1 / (1 - α) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlog_le hcoef
    change -((1 / (α - 1)) *
      log2 ((CFC.rpow ρ.m α * CFC.rpow τ (1 - α)).trace.re)) ≤
      (α / (1 - α)) * log2 (ρ.conditionalPetzRenyiUpClosedTrace α)
    calc
      -((1 / (α - 1)) *
          log2 ((CFC.rpow ρ.m α * CFC.rpow τ (1 - α)).trace.re)) =
          (1 / (1 - α)) *
            log2 ((CFC.rpow ρ.m α * CFC.rpow τ (1 - α)).trace.re) := by
              field_simp [hα_ne_one]
              ring
      _ ≤ (1 / (1 - α)) *
          (α * log2 (ρ.conditionalPetzRenyiUpClosedTrace α)) := hmul
      _ = (α / (1 - α)) * log2 (ρ.conditionalPetzRenyiUpClosedTrace α) := by ring

private theorem petz_up_candidateE_le_closed_of_one_lt
    (E : MEnsemble (A × B) Y) (σ : MState (B × Y)) (α : ℝ)
    (hα_gt_one : 1 < α) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    -(MState.cqConditioningState E).petzRenyiReferenceE
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef (a := A) σ)
        α hα_pos hα_ne_one ≤
      ((MState.cqConditioningState E).conditionalPetzRenyiUpAlternative α : EReal) := by
  let ρ := MState.cqConditioningState E
  let τ := identityTensorStateMatrix (a := A) σ
  have hτ : τ.PosSemidef := identityTensorStateMatrix_posSemidef (a := A) σ
  by_cases hsupport : Matrix.Supports ρ.m τ
  · rw [petzRenyiReferenceE_eq_coe_of_one_lt_of_supports
      ρ τ hτ α hα_pos hα_ne_one hα_gt_one hsupport]
    apply EReal.coe_le_coe_iff.mpr
    have hpowSupport : Matrix.Supports (CFC.rpow ρ.m α) τ :=
      (cMatrix_rpow_supports_self ρ.psd hα_pos).trans hsupport
    have hMSupport : Matrix.Supports
        (ρ.conditionalPetzRenyiUpTraceMatrix α) σ.m := by
      unfold conditionalPetzRenyiUpTraceMatrix
      apply traceLeft_supports_of_identityTensor_support
      simpa [τ, identityTensorStateMatrix] using hpowSupport
    have htr : σ.m.trace.re = 1 := by
      rw [σ.tr']
      simp
    have hp0 : 0 < 1 / α := one_div_pos.mpr hα_pos
    have hp1 : 1 / α < 1 := by
      rw [div_lt_iff₀ hα_pos]
      simpa using hα_gt_one
    have hr : 1 - α = 1 - 1 / (1 / α) := by
      field_simp [hα_pos.ne']
    have hrev :
        psdSchattenPNorm (ρ.conditionalPetzRenyiUpTraceMatrix α)
            (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α)
            ⟨1 / α, one_div_pos.mpr hα_pos⟩ ≤
          ((ρ.conditionalPetzRenyiUpTraceMatrix α) *
            CFC.rpow σ.m (1 - α)).trace.re :=
      psd_trace_rpow_reverse_holder_variational
        (M := ρ.conditionalPetzRenyiUpTraceMatrix α)
        (N := σ.m) (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α)
        σ.psd htr hMSupport hp0 hp1 hr
    have hrecip : 1 / (1 / α) = α := by field_simp [hα_pos.ne']
    have htrace_ge :
        (ρ.conditionalPetzRenyiUpClosedTrace α) ^ α ≤
          ρ.conditionalPetzRenyiTraceTerm σ α := by
      rw [ρ.conditionalPetzRenyiTraceTerm_eq_traceLeft]
      simpa [psdSchattenPNorm, Internal.psdSchattenExpression,
        conditionalPetzRenyiUpClosedTrace,
        conditionalPetzRenyiUpClosedTrace_eq_psdTracePower, hrecip,
        conditionalPetzRenyiTraceTerm] using hrev
    have hMne : CFC.rpow ρ.m α ≠ 0 := by
      intro hzero
      have hpow_pos : 0 < psdTracePower ρ.m ρ.psd α :=
        psdTracePower_pos_of_ne_zero ρ.m ρ.psd ρ.matrix_ne_zero
      have htrace_zero : psdTracePower ρ.m ρ.psd α = 0 := by
        simpa [psdTracePower] using
          congrArg (fun X : CMatrix (A × (B × Y)) => X.trace.re) hzero
      linarith
    have htrace_pos : 0 < ρ.conditionalPetzRenyiTraceTerm σ α :=
      trace_mul_cMatrix_rpow_pos_of_support
        (M := CFC.rpow ρ.m α) (N := τ)
        (cMatrix_rpow_posSemidef (A := ρ.m) (s := α) ρ.psd)
        hτ hMne hpowSupport (1 - α)
    have hclosed_pos : 0 < ρ.conditionalPetzRenyiUpClosedTrace α :=
      ρ.conditionalPetzRenyiUpClosedTrace_pos α
    have hlog_ge :
        α * log2 (ρ.conditionalPetzRenyiUpClosedTrace α) ≤
          log2 (ρ.conditionalPetzRenyiTraceTerm σ α) := by
      have h := log2_mono_of_pos
        (Real.rpow_pos_of_pos hclosed_pos α) htrace_ge
      simpa [log2_rpow_pos hclosed_pos] using h
    have hcoef_nonpos : 1 / (1 - α) ≤ 0 := by
      exact div_nonpos_of_nonneg_of_nonpos zero_le_one
        (sub_nonpos.mpr hα_gt_one.le)
    have hmul := mul_le_mul_of_nonpos_left hlog_ge hcoef_nonpos
    change -((1 / (α - 1)) *
      log2 ((CFC.rpow ρ.m α * CFC.rpow τ (1 - α)).trace.re)) ≤
      (α / (1 - α)) * log2 (ρ.conditionalPetzRenyiUpClosedTrace α)
    calc
      -((1 / (α - 1)) *
          log2 ((CFC.rpow ρ.m α * CFC.rpow τ (1 - α)).trace.re)) =
          (1 / (1 - α)) *
            log2 ((CFC.rpow ρ.m α * CFC.rpow τ (1 - α)).trace.re) := by
              field_simp [hα_ne_one]
              ring
      _ ≤ (1 / (1 - α)) *
          (α * log2 (ρ.conditionalPetzRenyiUpClosedTrace α)) := hmul
      _ = (α / (1 - α)) * log2
          (ρ.conditionalPetzRenyiUpClosedTrace α) := by ring
  · rw [petzRenyiReferenceE_eq_top_of_one_lt_of_not_supports
      ρ τ hτ α hα_pos hα_ne_one hα_gt_one hsupport]
    simp

private theorem petz_up_candidateE_eq_coe_fullReference_of_one_lt
    (E : MEnsemble (A × B) Y) (σ : MState (B × Y))
    (hσ : σ.m.PosDef) (α : ℝ) (hα_pos : 0 < α)
    (hα_gt_one : 1 < α) (hα_ne_one : α ≠ 1) :
    -(MState.cqConditioningState E).petzRenyiReferenceE
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef (a := A) σ)
        α hα_pos hα_ne_one =
      ((MState.cqConditioningState E).conditionalPetzRenyiEntropyCandidateFullReference
        σ hσ α hα_pos hα_ne_one : EReal) := by
  let ρ := MState.cqConditioningState E
  let τ := identityTensorStateMatrix (a := A) σ
  have hτ : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := A) σ hσ
  have hsupport : Matrix.Supports ρ.m τ :=
    Matrix.Supports.of_right_posDef ρ.m τ hτ
  rw [petzRenyiReferenceE_eq_coe_of_one_lt_of_supports
      ρ τ hτ.posSemidef α hα_pos hα_ne_one hα_gt_one hsupport]
  have hreal :
      -ρ.petzRenyiReferenceFinite τ hτ.posSemidef α hα_pos hα_ne_one =
        ρ.conditionalPetzRenyiEntropyCandidateFullReference
          σ hσ α hα_pos hα_ne_one := by
    unfold petzRenyiReferenceFinite
    have hleft : α - 1 ≠ 0 := sub_ne_zero.mpr hα_ne_one
    have hright : 1 - α ≠ 0 := sub_ne_zero.mpr hα_ne_one.symm
    have hcoef : -(1 / (α - 1)) = 1 / (1 - α) := by
      field_simp [hleft, hright]
      ring
    calc
      -(1 / (α - 1) *
          log2 ((CFC.rpow ρ.m α * CFC.rpow τ (1 - α)).trace.re)) =
          (-(1 / (α - 1))) *
            log2 ((CFC.rpow ρ.m α * CFC.rpow τ (1 - α)).trace.re) := by
              ring
      _ = _ := by
        rw [hcoef]
        rfl
  simpa [EReal.coe_neg] using congrArg (fun x : ℝ => (x : EReal)) hreal

private theorem petz_up_fullReference_range_bddAbove_of_one_lt
    (E : MEnsemble (A × B) Y) (α : ℝ) (hα_pos : 0 < α)
    (hα_gt_one : 1 < α) (hα_ne_one : α ≠ 1) :
    BddAbove (Set.range (fun p : {s : MState (B × Y) // s.m.PosDef} =>
      (MState.cqConditioningState E).conditionalPetzRenyiEntropyCandidateFullReference
        p.1 p.2 α hα_pos hα_ne_one)) := by
  let ρ := MState.cqConditioningState E
  refine ⟨ρ.conditionalPetzRenyiUpAlternative α, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact ρ.conditionalPetzRenyiEntropyCandidateFullReference_le_alternative_of_one_lt
    p.1 p.2 hα_gt_one hα_pos hα_ne_one

private theorem petz_up_fullReference_range_bddAbove
    (E : MEnsemble (A × B) Y) (α : ℝ) (hα_pos : 0 < α)
    (hα_lt_one : α < 1) (hα_ne_one : α ≠ 1) :
    BddAbove (Set.range (fun p : {s : MState (B × Y) // s.m.PosDef} =>
      (MState.cqConditioningState E).conditionalPetzRenyiEntropyCandidateFullReference
        p.1 p.2 α hα_pos hα_ne_one)) := by
  let ρ := MState.cqConditioningState E
  refine ⟨ρ.conditionalPetzRenyiUpAlternative α, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact ρ.conditionalPetzRenyiEntropyCandidateFullReference_le_alternative_of_lt_one
    p.1 p.2 hα_pos hα_lt_one hα_ne_one

/-- For `0 < α < 1` the upward optimization over conditioning states is attained, and equals the
closed form `conditionalPetzRenyiUpAlternative`.  The upper bound ranges over every positive
semidefinite reference; the lower bound comes from the full-rank references, whose supremum is
already that closed expression. -/
theorem conditionalPetzRenyiUp_classicalConditioning_eq_closed_of_lt_one
    [Nonempty (B × Y)] (E : MEnsemble (A × B) Y) (α : ℝ)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) (hα_ne_one : α ≠ 1) :
    conditionalPetzRenyiUpE E α hα_pos hα_ne_one =
      ((MState.cqConditioningState E).conditionalPetzRenyiUpAlternative α : EReal) := by
  let ρ := MState.cqConditioningState E
  have hup : ∀ h : EReal,
      (∃ σ : MState (B × Y),
        h = -ρ.petzRenyiReferenceE
          (identityTensorStateMatrix (a := A) σ)
          (identityTensorStateMatrix_posSemidef (a := A) σ)
          α hα_pos hα_ne_one) →
      h ≤ (ρ.conditionalPetzRenyiUpAlternative α : EReal) := by
    intro h hh
    rcases hh with ⟨σ, rfl⟩
    exact petz_up_candidateE_le_closed_of_lt_one E σ α hα_pos hα_lt_one hα_ne_one
  have hupper : conditionalPetzRenyiUpE E α hα_pos hα_ne_one ≤
      (ρ.conditionalPetzRenyiUpAlternative α : EReal) := by
    unfold conditionalPetzRenyiUpE
    exact sSup_le (by
      intro h hh
      exact hup h hh)
  let I := {s : MState (B × Y) // s.m.PosDef}
  let f : I → ℝ := fun p =>
    ρ.conditionalPetzRenyiEntropyCandidateFullReference
      p.1 p.2 α hα_pos hα_ne_one
  have hI : Nonempty I := by
    rcases ρ.conditionalPetzRenyiUpValueSet_nonempty α hα_pos hα_ne_one with
      ⟨_, ⟨σ, hσ, _⟩⟩
    exact ⟨⟨σ, hσ⟩⟩
  let := hI
  have hf_bdd : BddAbove (Set.range f) := by
    exact petz_up_fullReference_range_bddAbove E α hα_pos hα_lt_one hα_ne_one
  have hf_range : Set.range f =
      ρ.conditionalPetzRenyiUpValueSet α hα_pos hα_ne_one := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.2, rfl⟩
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨⟨σ, hσ⟩, rfl⟩
  have hreal : sSup (Set.range f) = ρ.conditionalPetzRenyiUp α hα_pos hα_ne_one := by
    rw [hf_range, conditionalPetzRenyiUp_eq]
  have hcoerced :
      sSup (Set.range (fun p : I => (f p : EReal))) =
        ((ρ.conditionalPetzRenyiUp α hα_pos hα_ne_one : ℝ) : EReal) := by
    rw [ereal_sSup_range_coe_eq_coe_real_sSup f hf_bdd, hreal]
  have hlower :
      ((ρ.conditionalPetzRenyiUpAlternative α : ℝ) : EReal) ≤
        conditionalPetzRenyiUpE E α hα_pos hα_ne_one := by
    rw [← ρ.conditionalPetzRenyiUp_eq_alternative hα_pos hα_ne_one, ← hcoerced]
    refine sSup_le ?_
    intro x hx
    rcases hx with ⟨p, rfl⟩
    refine le_sSup ⟨p.1, ?_⟩
    exact (petz_up_candidateE_eq_coe_fullReference E p.1 p.2 α hα_pos
      hα_lt_one hα_ne_one).symm
  exact le_antisymm hupper hlower

theorem conditionalPetzRenyiUp_classicalConditioning_eq_closed_of_one_lt
    [Nonempty (B × Y)] (E : MEnsemble (A × B) Y) (α : ℝ)
    (hα_pos : 0 < α) (hα_gt_one : 1 < α) (hα_ne_one : α ≠ 1) :
    conditionalPetzRenyiUpE E α hα_pos hα_ne_one =
      ((MState.cqConditioningState E).conditionalPetzRenyiUpAlternative α : EReal) := by
  let ρ := MState.cqConditioningState E
  have hup : ∀ h : EReal,
      (∃ σ : MState (B × Y),
        h = -ρ.petzRenyiReferenceE
          (identityTensorStateMatrix (a := A) σ)
          (identityTensorStateMatrix_posSemidef (a := A) σ)
          α hα_pos hα_ne_one) →
      h ≤ (ρ.conditionalPetzRenyiUpAlternative α : EReal) := by
    intro h hh
    rcases hh with ⟨σ, rfl⟩
    exact petz_up_candidateE_le_closed_of_one_lt E σ α hα_gt_one hα_pos hα_ne_one
  have hupper : conditionalPetzRenyiUpE E α hα_pos hα_ne_one ≤
      (ρ.conditionalPetzRenyiUpAlternative α : EReal) := by
    unfold conditionalPetzRenyiUpE
    exact sSup_le (by
      intro h hh
      exact hup h hh)
  let I := {s : MState (B × Y) // s.m.PosDef}
  let f : I → ℝ := fun p =>
    ρ.conditionalPetzRenyiEntropyCandidateFullReference
      p.1 p.2 α hα_pos hα_ne_one
  have hI : Nonempty I := by
    rcases ρ.conditionalPetzRenyiUpValueSet_nonempty α hα_pos hα_ne_one with
      ⟨_, ⟨σ, hσ, _⟩⟩
    exact ⟨⟨σ, hσ⟩⟩
  let := hI
  have hf_bdd : BddAbove (Set.range f) := by
    exact petz_up_fullReference_range_bddAbove_of_one_lt E α hα_pos
      hα_gt_one hα_ne_one
  let := Classical.decEq I
  have hf_range : Set.range f =
      ρ.conditionalPetzRenyiUpValueSet α hα_pos hα_ne_one := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.2, rfl⟩
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨⟨σ, hσ⟩, rfl⟩
  have hreal : sSup (Set.range f) =
      ρ.conditionalPetzRenyiUp α hα_pos hα_ne_one := by
    rw [hf_range, conditionalPetzRenyiUp_eq]
  have hcoerced :
      sSup (Set.range (fun p : I => (f p : EReal))) =
        ((ρ.conditionalPetzRenyiUp α hα_pos hα_ne_one : ℝ) : EReal) := by
    rw [ereal_sSup_range_coe_eq_coe_real_sSup f hf_bdd, hreal]
  have hlower :
      ((ρ.conditionalPetzRenyiUpAlternative α : ℝ) : EReal) ≤
        conditionalPetzRenyiUpE E α hα_pos hα_ne_one := by
    rw [← ρ.conditionalPetzRenyiUp_eq_alternative hα_pos hα_ne_one,
      ← hcoerced]
    refine sSup_le ?_
    intro x hx
    rcases hx with ⟨p, rfl⟩
    refine le_sSup ⟨p.1, ?_⟩
    exact (petz_up_candidateE_eq_coe_fullReference_of_one_lt E p.1 p.2 α
      hα_pos hα_gt_one hα_ne_one).symm
  exact le_antisymm hupper hlower

theorem petz_blockDiagonal_trace_decomposition_all
    (rho sigma : Y → CMatrix (A × B))
    (hrho : ∀ y, (rho y).PosSemidef)
    (hsigma : ∀ y, (sigma y).PosSemidef) (s t : ℝ) :
    (CFC.rpow (Classical.blockDiagonal rho) s *
      CFC.rpow (Classical.blockDiagonal sigma) t).trace.re =
      ∑ y, (CFC.rpow (rho y) s * CFC.rpow (sigma y) t).trace.re := by
  rw [Classical.blockDiagonal_rpow rho hrho s,
    Classical.blockDiagonal_rpow sigma hsigma t,
    Classical.blockDiagonal_mul, Classical.blockDiagonal_trace, Complex.re_sum]

theorem petz_conditionalQ_classical_decomposition_all
    (E : MEnsemble (A × B) Y) (s t : ℝ) :
    (CFC.rpow (MState.cqConditioningState E).m s *
      CFC.rpow
        (identityTensorStateMatrix (a := A)
          (MState.cqConditioningState E).traceLeft) t).trace.re =
      ∑ y, (CFC.rpow (conditionalRenyiBlock E y) s *
        CFC.rpow
          ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
            (E.states y).traceLeft) t).trace.re := by
  rw [conditionalRenyiState_eq_rightBlockDiagonal E,
    conditionalReference_blockDiagonal E,
    conditionalRenyiRightBlockDiagonal_rpow_support
      (conditionalRenyiBlock E)
      (fun y => conditionalRenyiBlock_posSemidef E y) s,
    conditionalRenyiRightBlockDiagonal_rpow_support
      (fun y => (E.probs y : ℂ) • identityTensorStateMatrix (a := A)
        (E.states y).traceLeft)
      (fun y => by
        have hp : 0 ≤ (E.probs y : ℂ) := by
          exact_mod_cast NNReal.coe_nonneg (E.probs y)
        exact (identityTensorStateMatrix_posSemidef
          (a := A) (E.states y).traceLeft).smul hp) t,
    conditionalRenyiRightBlockDiagonal_mul,
    conditionalRenyiRightBlockDiagonal_trace, Complex.re_sum]

private theorem petz_real_smul_trace_weight
    {X : Type*} [Fintype X] [DecidableEq X]
    (M N : CMatrix X) (hM : M.PosSemidef) (hN : N.PosSemidef)
    (p : ℝ≥0) {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    (CFC.rpow ((p : ℂ) • M) α *
      CFC.rpow ((p : ℂ) • N) (1 - α)).trace.re =
      (p : ℝ) * (CFC.rpow M α * CFC.rpow N (1 - α)).trace.re := by
  by_cases hpzero : p = 0
  · subst p
    rw [show ((0 : ℝ≥0) : ℂ) • M = 0 by simp,
      show ((0 : ℝ≥0) : ℂ) • N = 0 by simp,
      CFC.zero_rpow (A := CMatrix X) (ne_of_gt hα_pos),
      CFC.zero_rpow (A := CMatrix X) (ne_of_gt (sub_pos.mpr hα_lt_one))]
    simp
  · have hp : 0 ≤ (p : ℝ) := p.coe_nonneg
    rw [show ((p : ℂ) • M : CMatrix X) = (p : ℝ) • M by simp,
      show ((p : ℂ) • N : CMatrix X) = (p : ℝ) • N by simp,
      cMatrix_rpow_real_smul_posSemidef_schatten hM hp,
      cMatrix_rpow_real_smul_posSemidef_schatten hN hp]
    simp [Matrix.trace_smul, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, add_zero]
    have hp' : 0 < (p : ℝ) := by
      exact_mod_cast (pos_of_ne_zero hpzero)
    rw [← mul_assoc, ← Real.rpow_add hp']
    have hsum : 1 - α + α = 1 := by ring
    rw [hsum, Real.rpow_one]

private theorem petz_real_smul_trace_weight_of_one_lt
    {X : Type*} [Fintype X] [DecidableEq X]
    (M N : CMatrix X) (hM : M.PosSemidef) (hN : N.PosSemidef)
    (p : ℝ≥0) {α : ℝ} (hα_pos : 0 < α) (_hα_gt_one : 1 < α) :
    (CFC.rpow ((p : ℂ) • M) α *
      CFC.rpow ((p : ℂ) • N) (1 - α)).trace.re =
      (p : ℝ) * (CFC.rpow M α * CFC.rpow N (1 - α)).trace.re := by
  by_cases hpzero : p = 0
  · subst p
    rw [show ((0 : ℝ≥0) : ℂ) • M = 0 by simp,
      show ((0 : ℝ≥0) : ℂ) • N = 0 by simp,
      CFC.zero_rpow (A := CMatrix X) (ne_of_gt hα_pos)]
    simp
  · have hp : 0 ≤ (p : ℝ) := p.coe_nonneg
    rw [show ((p : ℂ) • M : CMatrix X) = (p : ℝ) • M by simp,
      show ((p : ℂ) • N : CMatrix X) = (p : ℝ) • N by simp,
      cMatrix_rpow_real_smul_posSemidef_schatten hM hp,
      cMatrix_rpow_real_smul_posSemidef_schatten hN hp]
    simp [Matrix.trace_smul, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, add_zero]
    have hp' : 0 < (p : ℝ) := by
      exact_mod_cast (pos_of_ne_zero hpzero)
    rw [← mul_assoc, ← Real.rpow_add hp']
    have hsum : 1 - α + α = 1 := by ring
    rw [hsum, Real.rpow_one]

theorem petz_conditionalQ_branch_weighted_of_one_lt
    (E : MEnsemble (A × B) Y) (y : Y) (α : ℝ)
    (hα_pos : 0 < α) (hα_gt_one : 1 < α) :
    (CFC.rpow (conditionalRenyiBlock E y) α *
      CFC.rpow
        ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
          (E.states y).traceLeft) (1 - α)).trace.re =
      (E.probs y : ℝ) *
        (CFC.rpow (E.states y).m α *
          CFC.rpow (identityTensorStateMatrix (a := A)
            (E.states y).traceLeft) (1 - α)).trace.re := by
  rw [conditionalRenyiBlock_eq_weighted_state]
  exact petz_real_smul_trace_weight_of_one_lt
    (E.states y).m
    (identityTensorStateMatrix (a := A) (E.states y).traceLeft)
    (E.states y).psd
    (identityTensorStateMatrix_posSemidef
      (a := A) (E.states y).traceLeft)
    (E.probs y) hα_pos hα_gt_one

theorem petz_conditionalQ_branch_weighted
    (E : MEnsemble (A × B) Y) (y : Y) (α : ℝ)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    (CFC.rpow (conditionalRenyiBlock E y) α *
      CFC.rpow
        ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
          (E.states y).traceLeft) (1 - α)).trace.re =
      (E.probs y : ℝ) *
        (CFC.rpow (E.states y).m α *
          CFC.rpow (identityTensorStateMatrix (a := A)
            (E.states y).traceLeft) (1 - α)).trace.re := by
  rw [conditionalRenyiBlock_eq_weighted_state]
  exact petz_real_smul_trace_weight
    (E.states y).m
    (identityTensorStateMatrix (a := A) (E.states y).traceLeft)
    (E.states y).psd
    (identityTensorStateMatrix_posSemidef
      (a := A) (E.states y).traceLeft)
    (E.probs y) hα_pos hα_lt_one

/-- The upward trace of the `y` block carries a single factor of `p y`.  Since `α > 0`, a
zero-probability branch is already zero before the `1/α` power is taken, so no support hypothesis
is needed. -/
theorem petz_conditionalUp_branch_trace_weighted
    (E : MEnsemble (A × B) Y) (y : Y) (α : ℝ) (hα_pos : 0 < α) :
    ((CFC.rpow
        (Matrix.traceLeft
          (CFC.rpow (conditionalRenyiBlock E y) α)) (1 / α)).trace).re =
      (E.probs y : ℝ) *
        (E.states y).conditionalPetzRenyiUpClosedTrace α := by
  rw [conditionalRenyiBlock_eq_weighted_state]
  have hp : 0 ≤ (E.probs y : ℝ) := (E.probs y).coe_nonneg
  rw [show ((E.probs y : ℂ) • (E.states y).m : CMatrix (A × B)) =
      (E.probs y : ℝ) • (E.states y).m by simp,
    cMatrix_rpow_real_smul_posSemidef_schatten (E.states y).psd hp]
  have hpartial : ∀ (c : ℝ) (X : CMatrix (A × B)),
      Matrix.traceLeft (c • X) =
        c • Matrix.traceLeft X := by
    intro c X
    ext i j
    simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.smul_apply]
    exact (Finset.mul_sum Finset.univ
      (fun x : A => X (x, i) (x, j)) (↑c : ℂ)).symm
  rw [hpartial]
  have hpα : 0 ≤ (E.probs y : ℝ) ^ α := Real.rpow_nonneg hp α
  rw [cMatrix_rpow_real_smul_posSemidef_schatten
    (traceLeft_posSemidef
      (cMatrix_rpow_posSemidef (A := (E.states y).m)
        (s := α) (E.states y).psd)) hpα]
  have hpow :
      ((E.probs y : ℝ) ^ α) ^ (1 / α) = (E.probs y : ℝ) := by
    by_cases hpzero : E.probs y = 0
    · simp [hpzero, hα_pos.ne']
    · have hp' : 0 < (E.probs y : ℝ) := by
        exact_mod_cast (pos_of_ne_zero hpzero)
      rw [← Real.rpow_mul hp'.le]
      rw [show α * (1 / α) = 1 by field_simp [hα_pos.ne']]
      exact Real.rpow_one _
  rw [hpow]
  simp [conditionalPetzRenyiUpClosedTrace,
    conditionalPetzRenyiUpTraceMatrix, Matrix.trace_smul, Complex.real_smul]

/-- For `0 < α < 1`, the Petz trace of the cq state against its own conditioning marginal is the
probability-weighted sum of the branch traces. -/
theorem petz_conditionalQ_classical_weighted
    (E : MEnsemble (A × B) Y) (α : ℝ)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    (CFC.rpow (MState.cqConditioningState E).m α *
      CFC.rpow
        (identityTensorStateMatrix (a := A)
          (MState.cqConditioningState E).traceLeft) (1 - α)).trace.re =
      ∑ y, (E.probs y : ℝ) *
        (CFC.rpow (E.states y).m α *
          CFC.rpow (identityTensorStateMatrix (a := A)
            (E.states y).traceLeft) (1 - α)).trace.re := by
  rw [petz_conditionalQ_classical_decomposition_all E α (1 - α)]
  apply Finset.sum_congr rfl
  intro y hy
  exact petz_conditionalQ_branch_weighted E y α hα_pos hα_lt_one

/-- The branch value entering the upward scalar optimization: the closed-form upward Petz entropy
of the normalized component at `y`.  Only labels of positive probability are ever weighted by it,
so its value on a zero-probability branch is immaterial. -/
noncomputable def petzConditionalBranch
    (E : MEnsemble (A × B) Y) (y : Y) (α : ℝ)
    (_hα_pos : 0 < α) (_hα_ne_one : α ≠ 1) : ℝ :=
  (E.states y).conditionalPetzRenyiUpAlternative α

/-- The parameter domain of the downward classical-conditioning results. -/
def petzDownRange (α : ℝ) : Prop := 0 < α ∧ α ≠ 1

/-- The parameter domain of the upward classical-conditioning results, which additionally caps
`α` at `2`. -/
def petzUpRange (α : ℝ) : Prop := 0 < α ∧ α ≤ 2 ∧ α ≠ 1

theorem petzDownRange_of_parameters (α : ℝ) (hα_pos : 0 < α)
    (hα_ne_one : α ≠ 1) : petzDownRange α := ⟨hα_pos, hα_ne_one⟩

theorem petzUpRange_of_parameters (α : ℝ) (hα_pos : 0 < α)
    (hα_le_two : α ≤ 2) (hα_ne_one : α ≠ 1) : petzUpRange α :=
  ⟨hα_pos, hα_le_two, hα_ne_one⟩

private theorem petz_down_normalized_q_pos
    (ρ : MState (A × B)) (α : ℝ) (hα_pos : 0 < α) :
    0 < (CFC.rpow ρ.m α *
      CFC.rpow (identityTensorStateMatrix (a := A) ρ.traceLeft)
        (1 - α)).trace.re := by
  have hSupport :
      Matrix.Supports ρ.m
        (identityTensorStateMatrix (a := A) ρ.traceLeft) := by
    simpa [identityTensorStateMatrix] using
      (matrix_supports_identityTensor_traceLeft ρ)
  have hpowSupport :
      Matrix.Supports (CFC.rpow ρ.m α)
        (identityTensorStateMatrix (a := A) ρ.traceLeft) :=
    (cMatrix_rpow_supports_self ρ.psd hα_pos).trans hSupport
  have hpow_ne : CFC.rpow ρ.m α ≠ 0 := by
    have hpow_pos : 0 < psdTracePower ρ.m ρ.psd α :=
      psdTracePower_pos_of_ne_zero ρ.m ρ.psd ρ.matrix_ne_zero
    intro hzero
    have htrace_zero : psdTracePower ρ.m ρ.psd α = 0 := by
      simpa [psdTracePower] using
        congrArg (fun X : CMatrix (A × B) => X.trace.re) hzero
    linarith
  exact trace_mul_cMatrix_rpow_pos_of_support
    (M := CFC.rpow ρ.m α)
    (N := identityTensorStateMatrix (a := A) ρ.traceLeft)
    (cMatrix_rpow_posSemidef (A := ρ.m) (s := α) ρ.psd)
    (identityTensorStateMatrix_posSemidef (a := A) ρ.traceLeft)
    hpow_ne hpowSupport (1 - α)

/-- The real Petz down-arrow entropy of the normalized `y`-component. -/
noncomputable def petzDownComponentEntropy
    (E : MEnsemble (A × B) Y) (y : Y) (α : ℝ) : ℝ :=
  (1 / (1 - α)) * log2
    ((CFC.rpow (E.states y).m α *
      CFC.rpow (identityTensorStateMatrix (a := A)
        (E.states y).traceLeft) (1 - α)).trace.re)

omit [DecidableEq Y] in
/-- The Petz `Q_α` value of every normalized component is strictly positive. -/
theorem petzDownComponentQ_pos
    (E : MEnsemble (A × B) Y) (y : Y) (α : ℝ) (hα_pos : 0 < α) :
    0 < (CFC.rpow (E.states y).m α *
      CFC.rpow (identityTensorStateMatrix (a := A)
        (E.states y).traceLeft) (1 - α)).trace.re :=
  petz_down_normalized_q_pos (E.states y) α hα_pos

/-- The Petz `Q_α` value of the normalized global cq state is strictly positive. -/
theorem petzDownClassicalQ_pos
    (E : MEnsemble (A × B) Y) (α : ℝ) (hα_pos : 0 < α) :
    0 < (CFC.rpow (MState.cqConditioningState E).m α *
      CFC.rpow
        (identityTensorStateMatrix (a := A)
          (MState.cqConditioningState E).traceLeft) (1 - α)).trace.re :=
  petz_down_normalized_q_pos (MState.cqConditioningState E) α hα_pos

omit [DecidableEq Y] in
/-- Exponentiating the component entropy recovers its strictly positive
Petz `Q_α` value. -/
theorem petzDownComponentQ_eq_rpow_entropy
    (E : MEnsemble (A × B) Y) (y : Y) (α : ℝ)
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    Real.rpow 2 ((1 - α) * petzDownComponentEntropy E y α) =
      (CFC.rpow (E.states y).m α *
        CFC.rpow (identityTensorStateMatrix (a := A)
          (E.states y).traceLeft) (1 - α)).trace.re := by
  have hq := petzDownComponentQ_pos E y α hα_pos
  unfold petzDownComponentEntropy
  have hcancel :
      (1 - α) * ((1 / (1 - α)) * log2
        ((CFC.rpow (E.states y).m α *
          CFC.rpow (identityTensorStateMatrix (a := A)
            (E.states y).traceLeft) (1 - α)).trace.re)) =
        log2 ((CFC.rpow (E.states y).m α *
          CFC.rpow (identityTensorStateMatrix (a := A)
            (E.states y).traceLeft) (1 - α)).trace.re) := by
    field_simp [hα_ne_one]
  rw [hcancel, rpow_two_log2_pos hq]

/-- A zero-probability label contributes the zero block, so no product with an extended-real
infinity is ever formed. -/
theorem petz_branch_block_zero_of_zero_probability
    (E : MEnsemble (A × B) Y) (y : Y) (hy : E.probs y = 0) :
    conditionalRenyiBlock E y = 0 := by
  rw [conditionalRenyiBlock_eq_weighted_state]
  simp [hy]

/-- The trace expression under the logarithm of the downward divergence, summed only over labels
of positive probability so that no term `0 * (+∞)` is formed. -/
noncomputable def petzDownFiniteSupportTrace
    (E : MEnsemble (A × B) Y) (α : ℝ) : ℝ :=
  ∑ y ∈ (MEnsemble.conditionalRenyiSupport E),
    ((CFC.rpow (conditionalRenyiBlock E y) α *
        CFC.rpow
          ((E.probs y : ℂ) •
            identityTensorStateMatrix (a := A) (E.states y).traceLeft)
          (1 - α)).trace.re)

theorem petzDownFiniteSupportTrace_eq_classicalQ
    (E : MEnsemble (A × B) Y) (α : ℝ)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    ((CFC.rpow (MState.cqConditioningState E).m α *
      CFC.rpow
        (identityTensorStateMatrix (a := A)
          (MState.cqConditioningState E).traceLeft) (1 - α)).trace.re) =
      petzDownFiniteSupportTrace E α := by
  calc
    _ = ∑ y, (E.probs y : ℝ) *
        (CFC.rpow (E.states y).m α *
          CFC.rpow (identityTensorStateMatrix (a := A)
            (E.states y).traceLeft) (1 - α)).trace.re :=
      petz_conditionalQ_classical_weighted E α hα_pos hα_lt_one
    _ = ∑ y, (CFC.rpow (conditionalRenyiBlock E y) α *
        CFC.rpow
          ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
            (E.states y).traceLeft) (1 - α)).trace.re := by
      apply Finset.sum_congr rfl
      intro y hy
      symm
      exact petz_conditionalQ_branch_weighted E y α hα_pos hα_lt_one
    _ = ∑ y ∈ MEnsemble.conditionalRenyiSupport E,
        (CFC.rpow (conditionalRenyiBlock E y) α *
          CFC.rpow
            ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
              (E.states y).traceLeft) (1 - α)).trace.re := by
      rw [← Finset.sum_subset (Finset.subset_univ
        (MEnsemble.conditionalRenyiSupport E))]
      intro y hy hnot
      have hprob : E.probs y = 0 :=
        (MEnsemble.not_mem_conditionalRenyiSupport_iff E y).mp hnot
      rw [petz_conditionalQ_branch_weighted E y α hα_pos hα_lt_one]
      simp [hprob]
    _ = petzDownFiniteSupportTrace E α := rfl

theorem petzDownFiniteSupportTrace_eq_classicalQ_of_one_lt
    (E : MEnsemble (A × B) Y) (α : ℝ)
    (hα_pos : 0 < α) (hα_gt_one : 1 < α) :
    ((CFC.rpow (MState.cqConditioningState E).m α *
      CFC.rpow
        (identityTensorStateMatrix (a := A)
          (MState.cqConditioningState E).traceLeft) (1 - α)).trace.re) =
      petzDownFiniteSupportTrace E α := by
  calc
    _ = ∑ y, (CFC.rpow (conditionalRenyiBlock E y) α *
        CFC.rpow
          ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
            (E.states y).traceLeft) (1 - α)).trace.re :=
      petz_conditionalQ_classical_decomposition_all E α (1 - α)
    _ = ∑ y, (E.probs y : ℝ) *
        (CFC.rpow (E.states y).m α *
          CFC.rpow (identityTensorStateMatrix (a := A)
            (E.states y).traceLeft) (1 - α)).trace.re := by
      apply Finset.sum_congr rfl
      intro y hy
      exact petz_conditionalQ_branch_weighted_of_one_lt
        E y α hα_pos hα_gt_one
    _ = ∑ y ∈ MEnsemble.conditionalRenyiSupport E,
        (E.probs y : ℝ) *
          (CFC.rpow (E.states y).m α *
            CFC.rpow (identityTensorStateMatrix (a := A)
              (E.states y).traceLeft) (1 - α)).trace.re := by
      rw [← Finset.sum_subset (Finset.subset_univ
        (MEnsemble.conditionalRenyiSupport E))]
      intro y hy hnot
      have hprob : E.probs y = 0 :=
        (MEnsemble.not_mem_conditionalRenyiSupport_iff E y).mp hnot
      simp [hprob]
    _ = ∑ y ∈ MEnsemble.conditionalRenyiSupport E,
        (CFC.rpow (conditionalRenyiBlock E y) α *
          CFC.rpow
            ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
              (E.states y).traceLeft) (1 - α)).trace.re := by
      apply Finset.sum_congr rfl
      intro y hy
      exact (petz_conditionalQ_branch_weighted_of_one_lt
        E y α hα_pos hα_gt_one).symm
    _ = petzDownFiniteSupportTrace E α := rfl

/-- The finite-support trace is the all-branch weighted exponential of the
normalized component entropies throughout the source Petz range. -/
theorem petzDownFiniteSupportTrace_eq_weightedComponentEntropy
    (E : MEnsemble (A × B) Y) (α : ℝ)
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    petzDownFiniteSupportTrace E α =
      ∑ y, (E.probs y : ℝ) * Real.rpow 2
        ((1 - α) * petzDownComponentEntropy E y α) := by
  rcases lt_or_gt_of_ne hα_ne_one with hα_lt_one | hα_gt_one
  · calc
      petzDownFiniteSupportTrace E α =
          (CFC.rpow (MState.cqConditioningState E).m α *
            CFC.rpow
              (identityTensorStateMatrix (a := A)
                (MState.cqConditioningState E).traceLeft) (1 - α)).trace.re :=
        (petzDownFiniteSupportTrace_eq_classicalQ
          E α hα_pos hα_lt_one).symm
      _ = ∑ y, (E.probs y : ℝ) *
          (CFC.rpow (E.states y).m α *
            CFC.rpow (identityTensorStateMatrix (a := A)
              (E.states y).traceLeft) (1 - α)).trace.re :=
        petz_conditionalQ_classical_weighted E α hα_pos hα_lt_one
      _ = ∑ y, (E.probs y : ℝ) * Real.rpow 2
          ((1 - α) * petzDownComponentEntropy E y α) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [petzDownComponentQ_eq_rpow_entropy E y α hα_pos hα_ne_one]
  · calc
      petzDownFiniteSupportTrace E α =
          (CFC.rpow (MState.cqConditioningState E).m α *
            CFC.rpow
              (identityTensorStateMatrix (a := A)
                (MState.cqConditioningState E).traceLeft) (1 - α)).trace.re :=
        (petzDownFiniteSupportTrace_eq_classicalQ_of_one_lt
          E α hα_pos hα_gt_one).symm
      _ = ∑ y, (CFC.rpow (conditionalRenyiBlock E y) α *
          CFC.rpow
            ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
              (E.states y).traceLeft) (1 - α)).trace.re :=
        petz_conditionalQ_classical_decomposition_all E α (1 - α)
      _ = ∑ y, (E.probs y : ℝ) *
          (CFC.rpow (E.states y).m α *
            CFC.rpow (identityTensorStateMatrix (a := A)
              (E.states y).traceLeft) (1 - α)).trace.re := by
        apply Finset.sum_congr rfl
        intro y hy
        exact petz_conditionalQ_branch_weighted_of_one_lt
          E y α hα_pos hα_gt_one
      _ = ∑ y, (E.probs y : ℝ) * Real.rpow 2
          ((1 - α) * petzDownComponentEntropy E y α) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [petzDownComponentQ_eq_rpow_entropy E y α hα_pos hα_ne_one]

/-- The downward conditional Petz Rényi entropy of a classically conditioned ensemble, as a real
number: `log₂` of `petzDownFiniteSupportTrace` divided by `1 - α`. -/
noncomputable def petzDownFiniteSupportFormulaReal
    (E : MEnsemble (A × B) Y) (α : ℝ) : ℝ :=
  (1 / (1 - α)) * log2 (petzDownFiniteSupportTrace E α)

/-- The unnormalized weight `p y · 2^((1-α)/α · branch value)` that the optimal conditioning state
of the upward program puts on the label `y`. -/
noncomputable def petzUpOptimizerWeight
  (E : MEnsemble (A × B) Y) (y : Y) (α : ℝ)
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  (E.probs y : ℝ) *
    Real.rpow 2 (((1 - α) / α) *
      petzConditionalBranch E y α hα_pos hα_ne_one)

/-- The normalization of `petzUpOptimizerWeight` over the labels of positive probability. -/
noncomputable def petzUpOptimizerNormalization
    (E : MEnsemble (A × B) Y) (α : ℝ)
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  ∑ y ∈ (MEnsemble.conditionalRenyiSupport E),
    petzUpOptimizerWeight E y α hα_pos hα_ne_one

/-- The upward conditional Petz Rényi entropy written out as the optimization over conditioning
states that defines it, with the parameter hypotheses carried explicitly. -/
noncomputable def petzUpSourceFormula
    (E : MEnsemble (A × B) Y) (α : ℝ) (hα_pos : 0 < α)
    (hα_ne_one : α ≠ 1) : EReal :=
  sSup {h : EReal |
    ∃ σ : MState (B × Y),
      h = -(MState.cqConditioningState E).petzRenyiReferenceE
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef (a := A) σ)
        α (hα_pos := hα_pos) (hα_ne_one := hα_ne_one)}

/-- For `0 < α < 1` and a nonvanishing Petz trace, the extended-real downward entropy is the
coercion of the finite-support logarithmic sum.  The trace hypothesis is discharged by
`petzDownClassicalQ_pos` in `conditionalPetzRenyiDown_classicalConditioning`. -/
theorem conditionalPetzRenyiDown_classicalConditioning_source_formula_of_lt_one
    (E : MEnsemble (A × B) Y) (α : ℝ) (hα_pos : 0 < α)
    (hα_lt_one : α < 1) (hα_ne_one : α ≠ 1)
    (hQne :
      (CFC.rpow (MState.cqConditioningState E).m α *
        CFC.rpow
          (identityTensorStateMatrix (a := A)
            (MState.cqConditioningState E).traceLeft) (1 - α)).trace.re ≠ 0) :
    conditionalPetzRenyiDownE E α hα_pos hα_ne_one =
      (petzDownFiniteSupportFormulaReal E α : EReal) := by
  unfold conditionalPetzRenyiDownE
  rw [petzRenyiReferenceE_eq_coe_of_lt_one_of_trace_ne_zero _ _ _
    α hα_pos hα_ne_one hα_lt_one hQne]
  unfold petzRenyiReferenceFinite
  rw [petzDownFiniteSupportTrace_eq_classicalQ E α hα_pos hα_lt_one]
  unfold petzDownFiniteSupportFormulaReal
  rw [← EReal.coe_neg]
  congr 1
  field_simp [sub_eq_add_neg, hα_ne_one]
  ring

/-- For `1 < α` the downward entropy is finite, because a cq state is supported by
`I_A ⊗ ρ_BY`. -/
theorem conditionalPetzRenyiDown_classicalConditioning_source_formula_of_one_lt
    (E : MEnsemble (A × B) Y) (α : ℝ) (hα_pos : 0 < α)
    (hα_gt_one : 1 < α) (hα_ne_one : α ≠ 1) :
    conditionalPetzRenyiDownE E α hα_pos hα_ne_one =
      -(petzRenyiReferenceFinite
        (MState.cqConditioningState E)
        (identityTensorStateMatrix (a := A)
          (MState.cqConditioningState E).traceLeft)
        (identityTensorStateMatrix_posSemidef
          (a := A) (MState.cqConditioningState E).traceLeft)
        α hα_pos hα_ne_one : EReal) := by
  have hSupport :
      Matrix.Supports (MState.cqConditioningState E).m
        (identityTensorStateMatrix (a := A)
          (MState.cqConditioningState E).traceLeft) := by
    simpa [identityTensorStateMatrix] using
      (matrix_supports_identityTensor_traceLeft
        (MState.cqConditioningState E))
  unfold conditionalPetzRenyiDownE
  rw [petzRenyiReferenceE_eq_coe_of_one_lt_of_supports _ _ _ α
    hα_pos hα_ne_one hα_gt_one hSupport]

theorem conditionalPetzRenyiDown_classicalConditioning_explicit_of_one_lt
    (E : MEnsemble (A × B) Y) (α : ℝ) (hα_pos : 0 < α)
    (hα_gt_one : 1 < α) (hα_ne_one : α ≠ 1) :
    conditionalPetzRenyiDownE E α hα_pos hα_ne_one =
      (petzDownFiniteSupportFormulaReal E α : EReal) := by
  have hSupport :
      Matrix.Supports (MState.cqConditioningState E).m
        (identityTensorStateMatrix (a := A)
          (MState.cqConditioningState E).traceLeft) := by
    simpa [identityTensorStateMatrix] using
      (matrix_supports_identityTensor_traceLeft
        (MState.cqConditioningState E))
  unfold conditionalPetzRenyiDownE
  rw [petzRenyiReferenceE_eq_coe_of_one_lt_of_supports _ _ _ α
    hα_pos hα_ne_one hα_gt_one hSupport]
  unfold petzRenyiReferenceFinite petzDownFiniteSupportFormulaReal
  rw [petzDownFiniteSupportTrace_eq_classicalQ_of_one_lt E α hα_pos hα_gt_one]
  rw [← EReal.coe_neg]
  congr 1
  field_simp [hα_ne_one]
  ring

/-- The downward conditional Petz Rényi entropy of a classically conditioned ensemble, at every
`α > 0` with `α ≠ 1`: `log₂` of the component entropies averaged as `2^((1-α) H)`, divided by
`1 - α`. -/
theorem conditionalPetzRenyiDown_classicalConditioning
    (E : MEnsemble (A × B) Y) (α : ℝ) (hα_pos : 0 < α)
    (hα_ne_one : α ≠ 1) :
    conditionalPetzRenyiDownE E α hα_pos hα_ne_one =
      (↑((1 / (1 - α)) * log2
        (∑ y, (E.probs y : ℝ) * Real.rpow 2
          ((1 - α) * petzDownComponentEntropy E y α))) : EReal) := by
  have htrace :=
    petzDownFiniteSupportTrace_eq_weightedComponentEntropy
      E α hα_pos hα_ne_one
  rcases lt_or_gt_of_ne hα_ne_one with hα_lt_one | hα_gt_one
  · have hQne :
        (CFC.rpow (MState.cqConditioningState E).m α *
          CFC.rpow
            (identityTensorStateMatrix (a := A)
              (MState.cqConditioningState E).traceLeft) (1 - α)).trace.re ≠ 0 :=
      ne_of_gt (petzDownClassicalQ_pos E α hα_pos)
    calc
      conditionalPetzRenyiDownE E α hα_pos hα_ne_one =
          (petzDownFiniteSupportFormulaReal E α : EReal) :=
        conditionalPetzRenyiDown_classicalConditioning_source_formula_of_lt_one
          E α hα_pos hα_lt_one hα_ne_one hQne
      _ = (↑((1 / (1 - α)) * log2
          (∑ y, (E.probs y : ℝ) * Real.rpow 2
            ((1 - α) * petzDownComponentEntropy E y α))) : EReal) := by
        simp only [petzDownFiniteSupportFormulaReal, htrace]
  · calc
      conditionalPetzRenyiDownE E α hα_pos hα_ne_one =
          (petzDownFiniteSupportFormulaReal E α : EReal) :=
        conditionalPetzRenyiDown_classicalConditioning_explicit_of_one_lt
          E α hα_pos hα_gt_one hα_ne_one
      _ = (↑((1 / (1 - α)) * log2
          (∑ y, (E.probs y : ℝ) * Real.rpow 2
            ((1 - α) * petzDownComponentEntropy E y α))) : EReal) := by
        simp only [petzDownFiniteSupportFormulaReal, htrace]

/-- A `Y`-indexed family of `B` blocks assembled block-diagonally in the `B × Y` grouping, the
conditioning-side counterpart of `conditionalRenyiRightBlockDiagonal`. -/
noncomputable def petzUpRightBlockDiagonal
    (blocks : Y → CMatrix B) : CMatrix (B × Y) :=
  (Classical.blockDiagonal blocks).submatrix
    (Equiv.prodComm B Y) (Equiv.prodComm B Y)

omit [DecidableEq A] [Fintype B] [DecidableEq B] in
theorem petz_traceLeft_rightBlockDiagonal
    (blocks : Y → CMatrix (A × B)) :
    Matrix.traceLeft
        (conditionalRenyiRightBlockDiagonal blocks) =
      petzUpRightBlockDiagonal (fun y =>
        Matrix.traceLeft (blocks y)) := by
  ext ⟨b, y⟩ ⟨b', y'⟩
  by_cases hyy : y = y'
  · subst y'
    simp [Matrix.traceLeft, petzUpRightBlockDiagonal,
      conditionalRenyiRightBlockDiagonal, Matrix.sum_apply,
      Matrix.submatrix_apply,
      Classical.blockDiagonal, Matrix.kroneckerMap_apply, Matrix.single_apply]
  · have hxy : ∀ x : Y, ¬(x = y ∧ x = y') := by
      intro x h
      exact hyy (h.1.symm.trans h.2)
    simp [Matrix.traceLeft, petzUpRightBlockDiagonal,
      conditionalRenyiRightBlockDiagonal, Matrix.sum_apply,
      Matrix.submatrix_apply, hxy,
      Classical.blockDiagonal, Matrix.kroneckerMap_apply]

theorem petz_conditionalUpTraceMatrix_classical_decomposition
    (E : MEnsemble (A × B) Y) (α : ℝ) :
    (MState.cqConditioningState E).conditionalPetzRenyiUpTraceMatrix α =
      petzUpRightBlockDiagonal (fun y =>
        Matrix.traceLeft
          (CFC.rpow (conditionalRenyiBlock E y) α)) := by
  unfold conditionalPetzRenyiUpTraceMatrix
  rw [conditionalRenyiState_eq_rightBlockDiagonal E,
    conditionalRenyiRightBlockDiagonal_rpow_support
      (conditionalRenyiBlock E)
      (fun y => conditionalRenyiBlock_posSemidef E y) α,
    petz_traceLeft_rightBlockDiagonal]

theorem petz_conditionalUpClosedTrace_classical_decomposition
    (E : MEnsemble (A × B) Y) (α : ℝ) (hα_pos : 0 < α) :
    (MState.cqConditioningState E).conditionalPetzRenyiUpClosedTrace α =
      ∑ y, (E.probs y : ℝ) *
        (E.states y).conditionalPetzRenyiUpClosedTrace α := by
  unfold conditionalPetzRenyiUpClosedTrace
  rw [petz_conditionalUpTraceMatrix_classical_decomposition E α]
  unfold petzUpRightBlockDiagonal
  have he : (Equiv.prodComm Y B).symm = Equiv.prodComm B Y := by
    apply Equiv.ext
    intro x
    rcases x with ⟨b, y⟩
    rfl
  have hpow := conditionalRenyi_rpow_reindex_posSemidef_support
      (e := Equiv.prodComm Y B)
      (M := Classical.blockDiagonal (fun y =>
        Matrix.traceLeft
          (CFC.rpow (conditionalRenyiBlock E y) α)))
      (Classical.blockDiagonal_posSemidef _ (fun y =>
        traceLeft_posSemidef
          (cMatrix_rpow_posSemidef (A := conditionalRenyiBlock E y)
            (s := α) (conditionalRenyiBlock_posSemidef E y)))) (1 / α)
  rw [he] at hpow
  rw [hpow]
  rw [Matrix.trace_submatrix,
    Classical.blockDiagonal_rpow _ (fun y =>
    traceLeft_posSemidef
      (cMatrix_rpow_posSemidef (A := conditionalRenyiBlock E y)
        (s := α) (conditionalRenyiBlock_posSemidef E y))) (1 / α),
    Classical.blockDiagonal_trace, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro y hy
  exact petz_conditionalUp_branch_trace_weighted E y α hα_pos

/-- The closed form of the upward conditional Petz Rényi entropy of a classically conditioned
ensemble: `α/(1-α)` times `log₂` of the branch values `2^((1-α)/α · H↑_α)` averaged over the
labels of positive probability. -/
noncomputable def petzUpClassicalFormulaReal
    (E : MEnsemble (A × B) Y) (α : ℝ)
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  (α / (1 - α)) * log2
    (∑ y ∈ MEnsemble.conditionalRenyiSupport E,
      (E.probs y : ℝ) * Real.rpow 2
        (((1 - α) / α) * petzConditionalBranch E y α hα_pos hα_ne_one))

theorem conditionalPetzRenyiUpAlternative_classicalFormula
    (E : MEnsemble (A × B) Y) (α : ℝ) (hα_pos : 0 < α)
    (hα_ne_one : α ≠ 1) :
    (MState.cqConditioningState E).conditionalPetzRenyiUpAlternative α =
      petzUpClassicalFormulaReal E α hα_pos hα_ne_one := by
  unfold conditionalPetzRenyiUpAlternative petzUpClassicalFormulaReal
  rw [petz_conditionalUpClosedTrace_classical_decomposition E α hα_pos]
  apply congrArg (fun x : ℝ => (α / (1 - α)) * log2 x)
  calc
    ∑ y, (E.probs y : ℝ) *
        (E.states y).conditionalPetzRenyiUpClosedTrace α =
      ∑ y ∈ MEnsemble.conditionalRenyiSupport E,
        (E.probs y : ℝ) *
          (E.states y).conditionalPetzRenyiUpClosedTrace α := by
      rw [← Finset.sum_subset (Finset.subset_univ
        (MEnsemble.conditionalRenyiSupport E))]
      intro y hy hnot
      have hprob : E.probs y = 0 :=
        (MEnsemble.not_mem_conditionalRenyiSupport_iff E y).mp hnot
      simp [hprob]
    _ = ∑ y ∈ MEnsemble.conditionalRenyiSupport E,
        (E.probs y : ℝ) * Real.rpow 2
          (((1 - α) / α) * petzConditionalBranch E y α hα_pos hα_ne_one) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [show petzConditionalBranch E y α hα_pos hα_ne_one =
          ((E.states y).conditionalPetzRenyiUpAlternative α) by rfl]
      unfold conditionalPetzRenyiUpAlternative
      have htrace_pos := (E.states y).conditionalPetzRenyiUpClosedTrace_pos α
      have hpow :
          ((1 - α) / α) *
              (α / (1 - α) *
                log2 ((E.states y).conditionalPetzRenyiUpClosedTrace α)) =
            log2 ((E.states y).conditionalPetzRenyiUpClosedTrace α) := by
        field_simp [hα_pos.ne', hα_ne_one]
      rw [hpow, QIT.rpow_two_log2_pos htrace_pos]

theorem conditionalPetzRenyiUp_classicalConditioning_explicit_of_lt_one
    [Nonempty (B × Y)] (E : MEnsemble (A × B) Y) (α : ℝ)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) (hα_ne_one : α ≠ 1) :
    conditionalPetzRenyiUpE E α hα_pos hα_ne_one =
      (petzUpClassicalFormulaReal E α hα_pos hα_ne_one : EReal) := by
  rw [conditionalPetzRenyiUp_classicalConditioning_eq_closed_of_lt_one
    E α hα_pos hα_lt_one hα_ne_one]
  exact congrArg (fun x : ℝ => (x : EReal))
    (conditionalPetzRenyiUpAlternative_classicalFormula
      E α hα_pos hα_ne_one)

theorem conditionalPetzRenyiUp_classicalConditioning
    [Nonempty (B × Y)] (E : MEnsemble (A × B) Y) (α : ℝ) (hα_pos : 0 < α)
    (hα_le_two : α ≤ 2) (hα_ne_one : α ≠ 1) :
    conditionalPetzRenyiUpE E α hα_pos hα_ne_one =
      (petzUpClassicalFormulaReal E α hα_pos hα_ne_one : EReal) := by
  have _hα_le_two_used : α ≤ 2 := hα_le_two
  rcases lt_or_gt_of_ne hα_ne_one with hα_lt_one | hα_gt_one
  · rw [conditionalPetzRenyiUp_classicalConditioning_eq_closed_of_lt_one
      E α hα_pos hα_lt_one hα_ne_one]
    exact congrArg (fun x : ℝ => (x : EReal))
      (conditionalPetzRenyiUpAlternative_classicalFormula
        E α hα_pos hα_ne_one)
  · rw [conditionalPetzRenyiUp_classicalConditioning_eq_closed_of_one_lt
      E α hα_pos hα_gt_one hα_ne_one]
    exact congrArg (fun x : ℝ => (x : EReal))
      (conditionalPetzRenyiUpAlternative_classicalFormula
        E α hα_pos hα_ne_one)

end MState
