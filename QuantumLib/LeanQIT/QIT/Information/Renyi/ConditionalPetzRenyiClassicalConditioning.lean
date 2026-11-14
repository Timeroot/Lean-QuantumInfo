/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.ConditionalRenyiClassical
public import QIT.Information.Renyi.ConditionalPetzRenyiAlternative
public import QIT.Util.Order.EReal

/-!
# Petz Renyi conditioning on a classical register

This module records the Petz part of `cond.tex:214-249`.  The public state is
presented as an ensemble `Y -> (A x B)`; the shared layer performs the finite
reindexing to `A x (B x Y)`.  The two declarations at the end retain the
extended-real definitions, while the lemmas immediately before them expose the
block and power identities used by the source proof.
-/

@[expose] public section

open scoped BigOperators ComplexOrder MatrixOrder NNReal
open Matrix

namespace QIT

universe u v w

noncomputable section

variable {A : Type u} {B : Type v} {Y : Type w}
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable [Fintype Y] [DecidableEq Y]

namespace State

/-! The scalar optimization below uses only the source-shaped Holder API.  In
particular, it does not use any conditional duality declaration. -/

private theorem petz_log2_mono_of_pos {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    log2 x ≤ log2 y := by
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
    (le_of_lt (Real.log_pos one_lt_two))

private theorem petz_log2_rpow_pos {x y : ℝ} (hx : 0 < x) :
    log2 (x ^ y) = y * log2 x := by
  dsimp [log2]
  rw [Real.log_rpow hx]
  ring

private theorem petz_rpow_two_log2_pos {x : ℝ} (hx : 0 < x) :
    Real.rpow 2 (log2 x) = x := by
  apply Real.log_injOn_pos
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    hx
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  unfold log2
  field_simp [ne_of_gt (Real.log_pos one_lt_two)]

private theorem petz_conditionalTrace_le_closed_of_lt_one
    (ρ : State (Prod A (B × Y))) (σ : State (B × Y))
    (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    ρ.conditionalPetzRenyiTraceTerm σ α ≤
      (ρ.conditionalPetzRenyiUpClosedTrace α) ^ α := by
  rw [ρ.conditionalPetzRenyiTraceTerm_eq_partialTraceA]
  have hpq : (1 / α).HolderConjugate (1 / (1 - α)) := by
    simpa [one_div] using Real.HolderConjugate.inv_one_sub_inv hα_pos hα_lt_one
  have htr : σ.matrix.trace.re = 1 := by
    rw [σ.trace_eq_one]
    simp
  have hr : 1 - α = 1 / (1 / (1 - α)) := by
    field_simp [sub_ne_zero.mpr hα_lt_one.ne]
  have hholder :=
    psd_trace_rpow_holder_variational_upper
      (M := ρ.conditionalPetzRenyiUpTraceMatrix α) (N := σ.matrix)
      (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α) σ.pos htr hpq hr
  have hrecip : 1 / (1 / α) = α := by field_simp [hα_pos.ne']
  simpa [psdSchattenPNorm, Internal.psdSchattenExpression,
    conditionalPetzRenyiUpClosedTrace,
    conditionalPetzRenyiUpClosedTrace_eq_psdTracePower, hrecip] using hholder

private theorem petz_up_candidateE_eq_coe_fullReference
    (E : Ensemble Y (A × B)) (σ : State (B × Y))
    (hσ : σ.matrix.PosDef) (α : ℝ) (hα_pos : 0 < α)
    (hα_lt_one : α < 1) (hα_ne_one : α ≠ 1) :
    -(State.cqConditioningState E).petzRenyiReferenceE
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
        α hα_pos hα_ne_one =
      (State.cqConditioningState E).conditionalPetzRenyiEntropyCandidateFullReference
        σ hσ α hα_pos hα_ne_one := by
  let ρ := State.cqConditioningState E
  let τ := identityTensorStateMatrix (a := A) σ
  have hτ : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := A) σ hσ
  have hq : 0 < (CFC.rpow ρ.matrix α * CFC.rpow τ (1 - α)).trace.re := by
    simpa [ρ, τ, State.conditionalPetzRenyiTraceTerm] using
      ρ.conditionalPetzRenyiTraceTerm_pos_of_fullReference σ hσ α
  have he := petzRenyiReferenceE_eq_coe_of_lt_one_of_trace_ne_zero
    ρ τ hτ.posSemidef α hα_pos hα_ne_one hα_lt_one hq.ne'
  rw [he]
  have hreal :
      -ρ.petzRenyiReferenceFinite τ hτ.posSemidef α hα_pos hα_ne_one =
        (1 / (1 - α)) * log2
          ((CFC.rpow ρ.matrix α * CFC.rpow τ (1 - α)).trace.re) := by
    unfold petzRenyiReferenceFinite
    have hleft : α - 1 ≠ 0 := sub_ne_zero.mpr hα_ne_one
    have hright : 1 - α ≠ 0 := sub_ne_zero.mpr hα_ne_one.symm
    have hcoef : -(1 / (α - 1)) = 1 / (1 - α) := by
      field_simp [hleft, hright]
      ring
    calc
      -(1 / (α - 1) *
          log2 ((CFC.rpow ρ.matrix α * CFC.rpow τ (1 - α)).trace.re)) =
          (-(1 / (α - 1))) *
            log2 ((CFC.rpow ρ.matrix α * CFC.rpow τ (1 - α)).trace.re) := by ring
      _ = _ := by rw [hcoef]
  simpa [EReal.coe_neg] using congrArg (fun x : ℝ => (x : EReal)) hreal

private theorem petz_up_candidateE_le_closed_of_lt_one
    (E : Ensemble Y (A × B)) (σ : State (B × Y)) (α : ℝ)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) (hα_ne_one : α ≠ 1) :
    -(State.cqConditioningState E).petzRenyiReferenceE
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
        α hα_pos hα_ne_one ≤
      ((State.cqConditioningState E).conditionalPetzRenyiUpAlternative α : EReal) := by
  let ρ := State.cqConditioningState E
  let τ := identityTensorStateMatrix (a := A) σ
  have hτ : τ.PosSemidef := identityTensorStateMatrix_posSemidef_of_state (a := A) σ
  have hq_nonneg : 0 ≤ (CFC.rpow ρ.matrix α * CFC.rpow τ (1 - α)).trace.re := by
    simpa [ρ, τ, State.conditionalPetzRenyiTraceTerm] using
      ρ.conditionalPetzRenyiTraceTerm_nonneg σ α
  by_cases hqzero : (CFC.rpow ρ.matrix α * CFC.rpow τ (1 - α)).trace.re = 0
  · rw [petzRenyiReferenceE_eq_top_of_lt_one_of_trace_eq_zero _ _ hτ
        α hα_pos hα_ne_one hα_lt_one hqzero]
    simp
  · have hq_pos : 0 < (CFC.rpow ρ.matrix α * CFC.rpow τ (1 - α)).trace.re :=
      lt_of_le_of_ne hq_nonneg (Ne.symm hqzero)
    rw [petzRenyiReferenceE_eq_coe_of_lt_one_of_trace_ne_zero _ _ hτ
      α hα_pos hα_ne_one hα_lt_one hqzero]
    apply EReal.coe_le_coe_iff.mpr
    have htrace_le := petz_conditionalTrace_le_closed_of_lt_one
      ρ σ α hα_pos hα_lt_one
    have hclosed_pos : 0 < ρ.conditionalPetzRenyiUpClosedTrace α :=
      ρ.conditionalPetzRenyiUpClosedTrace_pos α
    have hlog_le :
        log2 ((CFC.rpow ρ.matrix α * CFC.rpow τ (1 - α)).trace.re) ≤
          α * log2 (ρ.conditionalPetzRenyiUpClosedTrace α) := by
      have h := petz_log2_mono_of_pos hq_pos htrace_le
      simpa [petz_log2_rpow_pos hclosed_pos] using h
    have hcoef : 0 ≤ 1 / (1 - α) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlog_le hcoef
    change -((1 / (α - 1)) *
      log2 ((CFC.rpow ρ.matrix α * CFC.rpow τ (1 - α)).trace.re)) ≤
      (α / (1 - α)) * log2 (ρ.conditionalPetzRenyiUpClosedTrace α)
    calc
      -((1 / (α - 1)) *
          log2 ((CFC.rpow ρ.matrix α * CFC.rpow τ (1 - α)).trace.re)) =
          (1 / (1 - α)) *
            log2 ((CFC.rpow ρ.matrix α * CFC.rpow τ (1 - α)).trace.re) := by
              field_simp [hα_ne_one]
              ring
      _ ≤ (1 / (1 - α)) *
          (α * log2 (ρ.conditionalPetzRenyiUpClosedTrace α)) := hmul
      _ = (α / (1 - α)) * log2 (ρ.conditionalPetzRenyiUpClosedTrace α) := by ring

private theorem petz_up_candidateE_le_closed_of_one_lt
    (E : Ensemble Y (A × B)) (σ : State (B × Y)) (α : ℝ)
    (hα_gt_one : 1 < α) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    -(State.cqConditioningState E).petzRenyiReferenceE
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
        α hα_pos hα_ne_one ≤
      ((State.cqConditioningState E).conditionalPetzRenyiUpAlternative α : EReal) := by
  let ρ := State.cqConditioningState E
  let τ := identityTensorStateMatrix (a := A) σ
  have hτ : τ.PosSemidef := identityTensorStateMatrix_posSemidef_of_state (a := A) σ
  by_cases hsupport : Matrix.Supports ρ.matrix τ
  · rw [petzRenyiReferenceE_eq_coe_of_one_lt_of_supports
      ρ τ hτ α hα_pos hα_ne_one hα_gt_one hsupport]
    apply EReal.coe_le_coe_iff.mpr
    have hpowSupport : Matrix.Supports (CFC.rpow ρ.matrix α) τ :=
      (cMatrix_rpow_supports_self ρ.pos hα_pos).trans hsupport
    have hMSupport : Matrix.Supports
        (ρ.conditionalPetzRenyiUpTraceMatrix α) σ.matrix := by
      unfold conditionalPetzRenyiUpTraceMatrix
      apply partialTraceA_supports_of_identityTensor_support
      simpa [τ, identityTensorStateMatrix] using hpowSupport
    have htr : σ.matrix.trace.re = 1 := by
      rw [σ.trace_eq_one]
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
            CFC.rpow σ.matrix (1 - α)).trace.re :=
      psd_trace_rpow_reverse_holder_variational
        (M := ρ.conditionalPetzRenyiUpTraceMatrix α)
        (N := σ.matrix) (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α)
        σ.pos htr hMSupport hp0 hp1 hr
    have hrecip : 1 / (1 / α) = α := by field_simp [hα_pos.ne']
    have htrace_ge :
        (ρ.conditionalPetzRenyiUpClosedTrace α) ^ α ≤
          ρ.conditionalPetzRenyiTraceTerm σ α := by
      rw [ρ.conditionalPetzRenyiTraceTerm_eq_partialTraceA]
      simpa [psdSchattenPNorm, Internal.psdSchattenExpression,
        conditionalPetzRenyiUpClosedTrace,
        conditionalPetzRenyiUpClosedTrace_eq_psdTracePower, hrecip,
        conditionalPetzRenyiTraceTerm] using hrev
    have hMne : CFC.rpow ρ.matrix α ≠ 0 := by
      intro hzero
      have hpow_pos : 0 < psdTracePower ρ.matrix ρ.pos α :=
        psdTracePower_pos_of_ne_zero ρ.matrix ρ.pos ρ.matrix_ne_zero
      have htrace_zero : psdTracePower ρ.matrix ρ.pos α = 0 := by
        simpa [psdTracePower] using
          congrArg (fun X : CMatrix (Prod A (B × Y)) => X.trace.re) hzero
      linarith
    have htrace_pos : 0 < ρ.conditionalPetzRenyiTraceTerm σ α :=
      trace_mul_cMatrix_rpow_pos_of_support
        (M := CFC.rpow ρ.matrix α) (N := τ)
        (cMatrix_rpow_posSemidef (A := ρ.matrix) (s := α) ρ.pos)
        hτ hMne hpowSupport (1 - α)
    have hclosed_pos : 0 < ρ.conditionalPetzRenyiUpClosedTrace α :=
      ρ.conditionalPetzRenyiUpClosedTrace_pos α
    have hlog_ge :
        α * log2 (ρ.conditionalPetzRenyiUpClosedTrace α) ≤
          log2 (ρ.conditionalPetzRenyiTraceTerm σ α) := by
      have h := petz_log2_mono_of_pos
        (Real.rpow_pos_of_pos hclosed_pos α) htrace_ge
      simpa [petz_log2_rpow_pos hclosed_pos] using h
    have hcoef_nonpos : 1 / (1 - α) ≤ 0 := by
      exact div_nonpos_of_nonneg_of_nonpos zero_le_one
        (sub_nonpos.mpr hα_gt_one.le)
    have hmul := mul_le_mul_of_nonpos_left hlog_ge hcoef_nonpos
    change -((1 / (α - 1)) *
      log2 ((CFC.rpow ρ.matrix α * CFC.rpow τ (1 - α)).trace.re)) ≤
      (α / (1 - α)) * log2 (ρ.conditionalPetzRenyiUpClosedTrace α)
    calc
      -((1 / (α - 1)) *
          log2 ((CFC.rpow ρ.matrix α * CFC.rpow τ (1 - α)).trace.re)) =
          (1 / (1 - α)) *
            log2 ((CFC.rpow ρ.matrix α * CFC.rpow τ (1 - α)).trace.re) := by
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
    (E : Ensemble Y (A × B)) (σ : State (B × Y))
    (hσ : σ.matrix.PosDef) (α : ℝ) (hα_pos : 0 < α)
    (hα_gt_one : 1 < α) (hα_ne_one : α ≠ 1) :
    -(State.cqConditioningState E).petzRenyiReferenceE
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
        α hα_pos hα_ne_one =
      ((State.cqConditioningState E).conditionalPetzRenyiEntropyCandidateFullReference
        σ hσ α hα_pos hα_ne_one : EReal) := by
  let ρ := State.cqConditioningState E
  let τ := identityTensorStateMatrix (a := A) σ
  have hτ : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := A) σ hσ
  have hsupport : Matrix.Supports ρ.matrix τ :=
    Matrix.Supports.of_right_posDef ρ.matrix τ hτ
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
          log2 ((CFC.rpow ρ.matrix α * CFC.rpow τ (1 - α)).trace.re)) =
          (-(1 / (α - 1))) *
            log2 ((CFC.rpow ρ.matrix α * CFC.rpow τ (1 - α)).trace.re) := by
              ring
      _ = _ := by
        rw [hcoef]
        rfl
  simpa [EReal.coe_neg] using congrArg (fun x : ℝ => (x : EReal)) hreal

private theorem petz_up_fullReference_range_bddAbove_of_one_lt
    (E : Ensemble Y (A × B)) (α : ℝ) (hα_pos : 0 < α)
    (hα_gt_one : 1 < α) (hα_ne_one : α ≠ 1) :
    BddAbove (Set.range (fun p : {s : State (B × Y) // s.matrix.PosDef} =>
      (State.cqConditioningState E).conditionalPetzRenyiEntropyCandidateFullReference
        p.1 p.2 α hα_pos hα_ne_one)) := by
  let ρ := State.cqConditioningState E
  refine ⟨ρ.conditionalPetzRenyiUpAlternative α, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact ρ.conditionalPetzRenyiEntropyCandidateFullReference_le_alternative_of_one_lt
    p.1 p.2 hα_gt_one hα_pos hα_ne_one

private theorem petz_up_fullReference_range_bddAbove
    (E : Ensemble Y (A × B)) (α : ℝ) (hα_pos : 0 < α)
    (hα_lt_one : α < 1) (hα_ne_one : α ≠ 1) :
    BddAbove (Set.range (fun p : {s : State (B × Y) // s.matrix.PosDef} =>
      (State.cqConditioningState E).conditionalPetzRenyiEntropyCandidateFullReference
        p.1 p.2 α hα_pos hα_ne_one)) := by
  let ρ := State.cqConditioningState E
  refine ⟨ρ.conditionalPetzRenyiUpAlternative α, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact ρ.conditionalPetzRenyiEntropyCandidateFullReference_le_alternative_of_lt_one
    p.1 p.2 hα_pos hα_lt_one hα_ne_one

/-! The strict subunit scalar optimization is now a genuine equality for the
extended-real API.  The upper inequality ranges over every PSD reference;
the lower inequality uses the full-rank source set, whose supremum is the same
closed expression by the source optimizer theorem. -/

theorem conditionalPetzRenyiUp_classicalConditioning_eq_closed_of_lt_one
    [Nonempty (B × Y)] (E : Ensemble Y (A × B)) (α : ℝ)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) (hα_ne_one : α ≠ 1) :
    conditionalPetzRenyiUpE E α hα_pos hα_ne_one =
      ((State.cqConditioningState E).conditionalPetzRenyiUpAlternative α : EReal) := by
  let ρ := State.cqConditioningState E
  have hup : ∀ h : EReal,
      (∃ σ : State (B × Y),
        h = -ρ.petzRenyiReferenceE
          (identityTensorStateMatrix (a := A) σ)
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
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
  let I := {s : State (B × Y) // s.matrix.PosDef}
  let f : I → ℝ := fun p =>
    ρ.conditionalPetzRenyiEntropyCandidateFullReference
      p.1 p.2 α hα_pos hα_ne_one
  have hI : Nonempty I := by
    rcases ρ.conditionalPetzRenyiUpValueSet_nonempty α hα_pos hα_ne_one with
      ⟨_, ⟨σ, hσ, _⟩⟩
    exact ⟨⟨σ, hσ⟩⟩
  letI := hI
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
    [Nonempty (B × Y)] (E : Ensemble Y (A × B)) (α : ℝ)
    (hα_pos : 0 < α) (hα_gt_one : 1 < α) (hα_ne_one : α ≠ 1) :
    conditionalPetzRenyiUpE E α hα_pos hα_ne_one =
      ((State.cqConditioningState E).conditionalPetzRenyiUpAlternative α : EReal) := by
  let ρ := State.cqConditioningState E
  have hup : ∀ h : EReal,
      (∃ σ : State (B × Y),
        h = -ρ.petzRenyiReferenceE
          (identityTensorStateMatrix (a := A) σ)
          (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
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
  let I := {s : State (B × Y) // s.matrix.PosDef}
  let f : I → ℝ := fun p =>
    ρ.conditionalPetzRenyiEntropyCandidateFullReference
      p.1 p.2 α hα_pos hα_ne_one
  have hI : Nonempty I := by
    rcases ρ.conditionalPetzRenyiUpValueSet_nonempty α hα_pos hα_ne_one with
      ⟨_, ⟨σ, hσ, _⟩⟩
    exact ⟨⟨σ, hσ⟩⟩
  letI := hI
  have hf_bdd : BddAbove (Set.range f) := by
    exact petz_up_fullReference_range_bddAbove_of_one_lt E α hα_pos
      hα_gt_one hα_ne_one
  letI := Classical.decEq I
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

/-! The block power step is inherited from the shared classical functional
calculus layer; keeping this wrapper local makes the source route explicit. -/

theorem petz_blockDiagonal_rpow_nonneg
    (blocks : Y → CMatrix (A × B))
    (hblocks : ∀ y, (blocks y).PosSemidef) {s : ℝ} (hs : 0 ≤ s) :
    CFC.rpow (Classical.blockDiagonal blocks) s =
      Classical.blockDiagonal (fun y => CFC.rpow (blocks y) s) := by
  exact Classical.blockDiagonal_rpow_nonneg blocks hblocks hs

/-! The high-alpha branch uses the negative exponent `1 - α`.  The block
decomposition therefore has to be proved for arbitrary real powers, not only
for nonnegative ones.  The spectral basis of each PSD block gives a global
block-diagonal unitary, so zero eigenvalues are handled by the same `rpow`
convention as in the scalar source formula. -/

theorem petz_blockDiagonal_rpow
    (blocks : Y → CMatrix (A × B))
    (hblocks : ∀ y, (blocks y).PosSemidef) (s : ℝ) :
    CFC.rpow (Classical.blockDiagonal blocks) s =
      Classical.blockDiagonal (fun y => CFC.rpow (blocks y) s) := by
  let d : Y → (A × B) → ℝ :=
    fun y => (hblocks y).isHermitian.eigenvalues
  let U : Y → Matrix.unitaryGroup (A × B) ℂ :=
    fun y => (hblocks y).isHermitian.eigenvectorUnitary
  let W : Matrix.unitaryGroup (Y × (A × B)) ℂ :=
    ⟨Classical.blockDiagonal (fun y => (U y : CMatrix (A × B))), by
      rw [Matrix.mem_unitaryGroup_iff]
      simp only [star_eq_conjTranspose]
      rw [Classical.blockDiagonal_conjTranspose,
        Classical.blockDiagonal_mul]
      rw [show (1 : CMatrix (Y × (A × B))) =
          Matrix.kronecker (1 : CMatrix Y) (1 : CMatrix (A × B)) by simp]
      rw [Classical.identityTensor_eq_blockDiagonal (ι := Y)
        (a := A × B) (1 : CMatrix (A × B))]
      apply congrArg Classical.blockDiagonal
      funext y
      exact Matrix.mem_unitaryGroup_iff.mp (U y).2⟩
  have hd : ∀ y x, 0 ≤ d y x := by
    intro y x
    exact (hblocks y).eigenvalues_nonneg x
  have hdiag :
      Classical.blockDiagonal blocks =
        Unitary.conjStarAlgAut ℂ _ W
          (Classical.blockDiagonal (fun y =>
            Matrix.diagonal (fun x => (d y x : ℂ)))) := by
    have hspec : blocks = fun y =>
        Unitary.conjStarAlgAut ℂ _ (U y)
          (Matrix.diagonal (fun x => (d y x : ℂ))) := by
      funext y
      simpa [d, U, Function.comp_def] using
        (hblocks y).isHermitian.spectral_theorem
    rw [hspec]
    simp [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, W,
      Classical.blockDiagonal_conjTranspose, Classical.blockDiagonal_mul]
  have hdiag_block (f : Y → (A × B) → ℝ) :
      Classical.blockDiagonal (fun y =>
        Matrix.diagonal (fun x => (f y x : ℂ))) =
        Matrix.diagonal (fun p : Y × (A × B) => (f p.1 p.2 : ℂ)) := by
    ext ⟨y, x⟩ ⟨y', x'⟩
    by_cases hyy : y = y'
    · subst y'
      change Classical.block (Classical.blockDiagonal (fun y =>
        Matrix.diagonal (fun x => (f y x : ℂ)))) y y x x' = _
      have h := congrFun (congrFun
        (Classical.blockDiagonal_block_self (fun y =>
          Matrix.diagonal (fun x => (f y x : ℂ))) y) x) x'
      simp [Matrix.diagonal]
    · change Classical.block (Classical.blockDiagonal (fun y =>
      Matrix.diagonal (fun x => (f y x : ℂ)))) y y' x x' = _
      have h := congrFun (congrFun
        (Classical.blockDiagonal_block_ne (fun y =>
          Matrix.diagonal (fun x => (f y x : ℂ))) hyy) x) x'
      simp [Matrix.diagonal, hyy]
  have hpow :
      CFC.rpow (Classical.blockDiagonal blocks) s =
        Unitary.conjStarAlgAut ℂ _ W
          (Classical.blockDiagonal (fun y =>
            Matrix.diagonal (fun x => ((d y x ^ s : ℝ) : ℂ)))) := by
    rw [hdiag, hdiag_block d]
    rw [Unitary.conjStarAlgAut_apply,
      cMatrix_rpow_unitary_conj_diagonal_ofReal W
      (fun p : Y × (A × B) => d p.1 p.2) (fun p => hd p.1 p.2) s]
    simp only [Unitary.conjStarAlgAut_apply]
    rw [← hdiag_block (fun y x => d y x ^ s)]
  rw [hpow]
  simp only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
    W, Classical.blockDiagonal_conjTranspose, Classical.blockDiagonal_mul]
  apply congrArg Classical.blockDiagonal
  funext y
  have hy :
      blocks y =
        Unitary.conjStarAlgAut ℂ _ (U y)
          (Matrix.diagonal (fun x => (d y x : ℂ))) := by
    simpa [d, U, Function.comp_def] using
      (hblocks y).isHermitian.spectral_theorem
  rw [hy, Unitary.conjStarAlgAut_apply,
    cMatrix_rpow_unitary_conj_diagonal_ofReal (U y)
      (fun x => d y x) (fun x => hd y x) s]
  simp [star_eq_conjTranspose]

theorem petz_blockDiagonal_trace_decomposition_all
    (rho sigma : Y → CMatrix (A × B))
    (hrho : ∀ y, (rho y).PosSemidef)
    (hsigma : ∀ y, (sigma y).PosSemidef) (s t : ℝ) :
    (CFC.rpow (Classical.blockDiagonal rho) s *
      CFC.rpow (Classical.blockDiagonal sigma) t).trace.re =
      ∑ y, (CFC.rpow (rho y) s * CFC.rpow (sigma y) t).trace.re := by
    rw [petz_blockDiagonal_rpow rho hrho s,
    petz_blockDiagonal_rpow sigma hsigma t,
    Classical.blockDiagonal_mul, Classical.blockDiagonal_trace, Complex.re_sum]

/-! The fixed down-arrow reference has the same classical block structure as
the cq input.  The proof is written entrywise so that the zero-probability
case is visible rather than hidden in a scalar-times-infinity expression. -/

theorem petz_conditionalReference_blockDiagonal
    (E : Ensemble Y (A × B)) :
    identityTensorStateMatrix (a := A) (State.cqConditioningState E).marginalB =
      conditionalRenyiRightBlockDiagonal (fun y =>
        (E.probs y : ℂ) • identityTensorStateMatrix (a := A)
          (E.states y).marginalB) := by
  rw [Ensemble.conditionalRenyiState_marginalB_eq_conditionalMarginalBYState]
  ext ⟨a, b, y⟩ ⟨a', b', y'⟩
  by_cases hyy : y = y'
  · subst y'
    simp [conditionalRenyiRightBlockDiagonal, identityTensorStateMatrix,
      Ensemble.conditionalMarginalBYState, Ensemble.conditionalMarginalB,
      Ensemble.cqState_matrix, State.reindex_matrix, Matrix.kronecker,
      Matrix.kroneckerMap_apply, State.classicalConditioningEquiv_symm_apply,
      partialTraceA, Matrix.sum_apply]
    simp only [Matrix.one_apply]
    rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y)]
    · conv_rhs =>
        unfold Classical.blockDiagonal
        rw [Matrix.sum_apply]
        rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y) (by
          intro z _ hzy
          simp [hzy])]
      simp [Matrix.kronecker,
        Matrix.kroneckerMap_apply, partialTraceA]
      by_cases haa : a = a'
      · subst a'
        rw [NNReal.smul_def]
        simp [Complex.real_smul]
      · simp [haa]
    · intro z _ hzy
      simp [hzy]
  · have hxy : ∀ x : Y, ¬(x = y ∧ x = y') := by
      intro x h
      exact hyy (h.1.symm.trans h.2)
    simp [conditionalRenyiRightBlockDiagonal, identityTensorStateMatrix,
      Ensemble.conditionalMarginalBYState, Ensemble.conditionalMarginalB,
      Ensemble.cqState_matrix, State.reindex_matrix, Matrix.kronecker,
      Matrix.kroneckerMap_apply, State.classicalConditioningEquiv_symm_apply,
      partialTraceA, Matrix.sum_apply,
      Classical.blockDiagonal, hxy]

theorem petz_conditionalQ_classical_decomposition_all
    (E : Ensemble Y (A × B)) (s t : ℝ) :
    (CFC.rpow (State.cqConditioningState E).matrix s *
      CFC.rpow
        (identityTensorStateMatrix (a := A)
          (State.cqConditioningState E).marginalB) t).trace.re =
      ∑ y, (CFC.rpow (conditionalRenyiBlock E y) s *
        CFC.rpow
          ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
            (E.states y).marginalB) t).trace.re := by
  rw [conditionalRenyiState_eq_rightBlockDiagonal E,
    petz_conditionalReference_blockDiagonal E,
    conditionalRenyiRightBlockDiagonal_rpow_support
      (conditionalRenyiBlock E)
      (fun y => conditionalRenyiBlock_posSemidef E y) s,
    conditionalRenyiRightBlockDiagonal_rpow_support
      (fun y => (E.probs y : ℂ) • identityTensorStateMatrix (a := A)
        (E.states y).marginalB)
      (fun y => by
        have hp : 0 ≤ (E.probs y : ℂ) := by
          exact_mod_cast NNReal.coe_nonneg (E.probs y)
        exact (identityTensorStateMatrix_posSemidef_of_state
          (a := A) (E.states y).marginalB).smul hp) t,
    conditionalRenyiRightBlockDiagonal_mul,
    conditionalRenyiRightBlockDiagonal_trace, Complex.re_sum]

/-! This is the matrix-level `Q` identity in `eq:qc-div`: the trace of the
product of two nonnegative powers splits into the finite classical sum of
the corresponding branch traces. -/
theorem petz_blockDiagonal_trace_decomposition
    (rho sigma : Y → CMatrix (A × B))
    (hrho : ∀ y, (rho y).PosSemidef)
    (hsigma : ∀ y, (sigma y).PosSemidef)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (CFC.rpow (conditionalRenyiRightBlockDiagonal rho) s *
      CFC.rpow (conditionalRenyiRightBlockDiagonal sigma) t).trace.re =
      ∑ y, (CFC.rpow (rho y) s * CFC.rpow (sigma y) t).trace.re := by
    rw [conditionalRenyiRightBlockDiagonal_rpow_nonneg
      rho hrho hs,
    conditionalRenyiRightBlockDiagonal_rpow_nonneg
      sigma hsigma ht,
    conditionalRenyiRightBlockDiagonal_mul,
    conditionalRenyiRightBlockDiagonal_trace,
    Complex.re_sum]

/-! Instantiating the preceding block trace identity with an actual ensemble
is the source `eq:qc-div` numerator identity for the down-arrow reference. -/

theorem petz_conditionalQ_classical_decomposition
    (E : Ensemble Y (A × B)) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (CFC.rpow (State.cqConditioningState E).matrix s *
      CFC.rpow
        (identityTensorStateMatrix (a := A)
          (State.cqConditioningState E).marginalB) t).trace.re =
      ∑ y, (CFC.rpow (conditionalRenyiBlock E y) s *
        CFC.rpow
          ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
            (E.states y).marginalB) t).trace.re := by
  rw [conditionalRenyiState_eq_rightBlockDiagonal E,
    petz_conditionalReference_blockDiagonal E]
  exact petz_blockDiagonal_trace_decomposition
    (rho := fun y => conditionalRenyiBlock E y)
    (sigma := fun y => (E.probs y : ℂ) • identityTensorStateMatrix
      (a := A) (E.states y).marginalB)
    (hrho := fun y => conditionalRenyiBlock_posSemidef E y)
    (hsigma := fun y => by
      have hp : 0 ≤ (E.probs y : ℂ) := by
        exact_mod_cast NNReal.coe_nonneg (E.probs y)
      exact (identityTensorStateMatrix_posSemidef_of_state
        (a := A) (E.states y).marginalB).smul hp)
    (s := s) (t := t) hs ht

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
    (E : Ensemble Y (A × B)) (y : Y) (α : ℝ)
    (hα_pos : 0 < α) (hα_gt_one : 1 < α) :
    (CFC.rpow (conditionalRenyiBlock E y) α *
      CFC.rpow
        ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
          (E.states y).marginalB) (1 - α)).trace.re =
      (E.probs y : ℝ) *
        (CFC.rpow (E.states y).matrix α *
          CFC.rpow (identityTensorStateMatrix (a := A)
            (E.states y).marginalB) (1 - α)).trace.re := by
  rw [conditionalRenyiBlock_eq_weighted_state]
  exact petz_real_smul_trace_weight_of_one_lt
    (E.states y).matrix
    (identityTensorStateMatrix (a := A) (E.states y).marginalB)
    (E.states y).pos
    (identityTensorStateMatrix_posSemidef_of_state
      (a := A) (E.states y).marginalB)
    (E.probs y) hα_pos hα_gt_one

theorem petz_conditionalQ_branch_weighted
    (E : Ensemble Y (A × B)) (y : Y) (α : ℝ)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    (CFC.rpow (conditionalRenyiBlock E y) α *
      CFC.rpow
        ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
          (E.states y).marginalB) (1 - α)).trace.re =
      (E.probs y : ℝ) *
        (CFC.rpow (E.states y).matrix α *
          CFC.rpow (identityTensorStateMatrix (a := A)
            (E.states y).marginalB) (1 - α)).trace.re := by
  rw [conditionalRenyiBlock_eq_weighted_state]
  exact petz_real_smul_trace_weight
    (E.states y).matrix
    (identityTensorStateMatrix (a := A) (E.states y).marginalB)
    (E.states y).pos
    (identityTensorStateMatrix_posSemidef_of_state
      (a := A) (E.states y).marginalB)
    (E.probs y) hα_pos hα_lt_one

/-! The upward alternative uses the same source scaling after taking the
partial trace.  Since `α > 0`, the zero-probability branch is killed before
the `1 / α` power is taken, so this identity is valid without a support
qualification. -/

theorem petz_conditionalUp_branch_trace_weighted
    (E : Ensemble Y (A × B)) (y : Y) (α : ℝ) (hα_pos : 0 < α) :
    ((CFC.rpow
        (partialTraceA (a := A) (b := B)
          (CFC.rpow (conditionalRenyiBlock E y) α)) (1 / α)).trace).re =
      (E.probs y : ℝ) *
        (E.states y).conditionalPetzRenyiUpClosedTrace α := by
  rw [conditionalRenyiBlock_eq_weighted_state]
  have hp : 0 ≤ (E.probs y : ℝ) := (E.probs y).coe_nonneg
  rw [show ((E.probs y : ℂ) • (E.states y).matrix : CMatrix (A × B)) =
      (E.probs y : ℝ) • (E.states y).matrix by simp,
    cMatrix_rpow_real_smul_posSemidef_schatten (E.states y).pos hp]
  have hpartial : ∀ (c : ℝ) (X : CMatrix (A × B)),
      partialTraceA (a := A) (b := B) (c • X) =
        c • partialTraceA (a := A) (b := B) X := by
    intro c X
    ext i j
    simp only [partialTraceA, Matrix.smul_apply]
    exact (Finset.mul_sum Finset.univ
      (fun x : A => X (x, i) (x, j)) (↑c : ℂ)).symm
  rw [hpartial]
  have hpα : 0 ≤ (E.probs y : ℝ) ^ α := Real.rpow_nonneg hp α
  rw [cMatrix_rpow_real_smul_posSemidef_schatten
    (partialTraceA_posSemidef
      (cMatrix_rpow_posSemidef (A := (E.states y).matrix)
        (s := α) (E.states y).pos)) hpα]
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

/-! The preceding two lemmas now give the scalar version of `eq:qc-div` for
the strict subunit branch.  The source's support convention is represented by
the explicit finite-support sum in the definition of the left-hand side. -/

theorem petz_conditionalQ_classical_weighted
    (E : Ensemble Y (A × B)) (α : ℝ)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    (CFC.rpow (State.cqConditioningState E).matrix α *
      CFC.rpow
        (identityTensorStateMatrix (a := A)
          (State.cqConditioningState E).marginalB) (1 - α)).trace.re =
      ∑ y, (E.probs y : ℝ) *
        (CFC.rpow (E.states y).matrix α *
          CFC.rpow (identityTensorStateMatrix (a := A)
            (E.states y).marginalB) (1 - α)).trace.re := by
  rw [petz_conditionalQ_classical_decomposition E hα_pos.le
    (sub_nonneg.mpr (le_of_lt hα_lt_one))]
  apply Finset.sum_congr rfl
  intro y hy
  exact petz_conditionalQ_branch_weighted E y α hα_pos hα_lt_one

/-! A source-facing branch for the upward scalar optimization is the closed
Petz upward entropy of the normalized component.  The zero-probability
component is never multiplied by this value in the support-indexed source
sums. -/

noncomputable def petzConditionalBranch
    (E : Ensemble Y (A × B)) (y : Y) (α : ℝ)
    (_hα_pos : 0 < α) (_hα_ne_one : α ≠ 1) : ℝ :=
  (E.states y).conditionalPetzRenyiUpAlternative α

/-! These are the source's two parameter domains, kept as propositions so the
registered declarations make the endpoint conventions explicit. -/

def petzDownRange (α : ℝ) : Prop := 0 < α ∧ α ≠ 1

def petzUpRange (α : ℝ) : Prop := 0 < α ∧ α ≤ 2 ∧ α ≠ 1

theorem petzDownRange_of_parameters (α : ℝ) (hα_pos : 0 < α)
    (hα_ne_one : α ≠ 1) : petzDownRange α := ⟨hα_pos, hα_ne_one⟩

theorem petzUpRange_of_parameters (α : ℝ) (hα_pos : 0 < α)
    (hα_le_two : α ≤ 2) (hα_ne_one : α ≠ 1) : petzUpRange α :=
  ⟨hα_pos, hα_le_two, hα_ne_one⟩

private theorem petz_down_normalized_q_pos
    (ρ : State (A × B)) (α : ℝ) (hα_pos : 0 < α) :
    0 < (CFC.rpow ρ.matrix α *
      CFC.rpow (identityTensorStateMatrix (a := A) ρ.marginalB)
        (1 - α)).trace.re := by
  have hSupport :
      Matrix.Supports ρ.matrix
        (identityTensorStateMatrix (a := A) ρ.marginalB) := by
    simpa [identityTensorStateMatrix] using
      (matrix_supports_identityTensor_marginalB ρ)
  have hpowSupport :
      Matrix.Supports (CFC.rpow ρ.matrix α)
        (identityTensorStateMatrix (a := A) ρ.marginalB) :=
    (cMatrix_rpow_supports_self ρ.pos hα_pos).trans hSupport
  have hpow_ne : CFC.rpow ρ.matrix α ≠ 0 := by
    have hpow_pos : 0 < psdTracePower ρ.matrix ρ.pos α :=
      psdTracePower_pos_of_ne_zero ρ.matrix ρ.pos ρ.matrix_ne_zero
    intro hzero
    have htrace_zero : psdTracePower ρ.matrix ρ.pos α = 0 := by
      simpa [psdTracePower] using
        congrArg (fun X : CMatrix (A × B) => X.trace.re) hzero
    linarith
  exact trace_mul_cMatrix_rpow_pos_of_support
    (M := CFC.rpow ρ.matrix α)
    (N := identityTensorStateMatrix (a := A) ρ.marginalB)
    (cMatrix_rpow_posSemidef (A := ρ.matrix) (s := α) ρ.pos)
    (identityTensorStateMatrix_posSemidef_of_state (a := A) ρ.marginalB)
    hpow_ne hpowSupport (1 - α)

/-- The real Petz down-arrow entropy of the normalized `y`-component. -/
noncomputable def petzDownComponentEntropy
    (E : Ensemble Y (A × B)) (y : Y) (α : ℝ) : ℝ :=
  (1 / (1 - α)) * log2
    ((CFC.rpow (E.states y).matrix α *
      CFC.rpow (identityTensorStateMatrix (a := A)
        (E.states y).marginalB) (1 - α)).trace.re)

omit [DecidableEq Y] in
/-- The Petz `Q_α` value of every normalized component is strictly positive. -/
theorem petzDownComponentQ_pos
    (E : Ensemble Y (A × B)) (y : Y) (α : ℝ) (hα_pos : 0 < α) :
    0 < (CFC.rpow (E.states y).matrix α *
      CFC.rpow (identityTensorStateMatrix (a := A)
        (E.states y).marginalB) (1 - α)).trace.re :=
  petz_down_normalized_q_pos (E.states y) α hα_pos

/-- The Petz `Q_α` value of the normalized global cq state is strictly positive. -/
theorem petzDownClassicalQ_pos
    (E : Ensemble Y (A × B)) (α : ℝ) (hα_pos : 0 < α) :
    0 < (CFC.rpow (State.cqConditioningState E).matrix α *
      CFC.rpow
        (identityTensorStateMatrix (a := A)
          (State.cqConditioningState E).marginalB) (1 - α)).trace.re :=
  petz_down_normalized_q_pos (State.cqConditioningState E) α hα_pos

omit [DecidableEq Y] in
/-- Exponentiating the component entropy recovers its strictly positive
Petz `Q_α` value. -/
theorem petzDownComponentQ_eq_rpow_entropy
    (E : Ensemble Y (A × B)) (y : Y) (α : ℝ)
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    Real.rpow 2 ((1 - α) * petzDownComponentEntropy E y α) =
      (CFC.rpow (E.states y).matrix α *
        CFC.rpow (identityTensorStateMatrix (a := A)
          (E.states y).marginalB) (1 - α)).trace.re := by
  have hq := petzDownComponentQ_pos E y α hα_pos
  unfold petzDownComponentEntropy
  have hcancel :
      (1 - α) * ((1 / (1 - α)) * log2
        ((CFC.rpow (E.states y).matrix α *
          CFC.rpow (identityTensorStateMatrix (a := A)
            (E.states y).marginalB) (1 - α)).trace.re)) =
        log2 ((CFC.rpow (E.states y).matrix α *
          CFC.rpow (identityTensorStateMatrix (a := A)
            (E.states y).marginalB) (1 - α)).trace.re) := by
    field_simp [hα_ne_one]
  rw [hcancel, petz_rpow_two_log2_pos hq]

/-! The diagonal block identity is the first algebraic step of `eq:qc-div`.
It records the exact weighted component state, including its zero-weight
case, without forming a product with an extended-real infinity. -/

theorem petz_branch_block_decomposition
    (E : Ensemble Y (A × B)) (y : Y) :
    conditionalRenyiBlock E y =
      (E.probs y : ℂ) • (E.states y).matrix := by
  exact conditionalRenyiBlock_eq_weighted_state E y

theorem petz_branch_block_zero_of_zero_probability
    (E : Ensemble Y (A × B)) (y : Y) (hy : E.probs y = 0) :
    conditionalRenyiBlock E y = 0 := by
  rw [petz_branch_block_decomposition]
  simp [hy]

/-! This is the finite-support trace expression appearing before taking the
logarithm in `eq:qc-div`.  Its index set excludes zero-probability branches,
so no term of the form `0 * (+infinity)` is constructed. -/

noncomputable def petzDownFiniteSupportTrace
    (E : Ensemble Y (A × B)) (α : ℝ) : ℝ :=
  ∑ y ∈ (Ensemble.conditionalRenyiSupport E),
    ((CFC.rpow (conditionalRenyiBlock E y) α *
        CFC.rpow
          ((E.probs y : ℂ) •
            identityTensorStateMatrix (a := A) (E.states y).marginalB)
          (1 - α)).trace.re)

theorem petzDownFiniteSupportTrace_eq_classicalQ
    (E : Ensemble Y (A × B)) (α : ℝ)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    ((CFC.rpow (State.cqConditioningState E).matrix α *
      CFC.rpow
        (identityTensorStateMatrix (a := A)
          (State.cqConditioningState E).marginalB) (1 - α)).trace.re) =
      petzDownFiniteSupportTrace E α := by
  calc
    _ = ∑ y, (E.probs y : ℝ) *
        (CFC.rpow (E.states y).matrix α *
          CFC.rpow (identityTensorStateMatrix (a := A)
            (E.states y).marginalB) (1 - α)).trace.re :=
      petz_conditionalQ_classical_weighted E α hα_pos hα_lt_one
    _ = ∑ y, (CFC.rpow (conditionalRenyiBlock E y) α *
        CFC.rpow
          ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
            (E.states y).marginalB) (1 - α)).trace.re := by
      apply Finset.sum_congr rfl
      intro y hy
      symm
      exact petz_conditionalQ_branch_weighted E y α hα_pos hα_lt_one
    _ = ∑ y ∈ Ensemble.conditionalRenyiSupport E,
        (CFC.rpow (conditionalRenyiBlock E y) α *
          CFC.rpow
            ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
              (E.states y).marginalB) (1 - α)).trace.re := by
      rw [← Finset.sum_subset (Finset.subset_univ
        (Ensemble.conditionalRenyiSupport E))]
      intro y hy hnot
      have hprob : E.probs y = 0 :=
        (Ensemble.not_mem_conditionalRenyiSupport_iff E y).mp hnot
      rw [petz_conditionalQ_branch_weighted E y α hα_pos hα_lt_one]
      simp [hprob]
    _ = petzDownFiniteSupportTrace E α := rfl

theorem petzDownFiniteSupportTrace_eq_classicalQ_of_one_lt
    (E : Ensemble Y (A × B)) (α : ℝ)
    (hα_pos : 0 < α) (hα_gt_one : 1 < α) :
    ((CFC.rpow (State.cqConditioningState E).matrix α *
      CFC.rpow
        (identityTensorStateMatrix (a := A)
          (State.cqConditioningState E).marginalB) (1 - α)).trace.re) =
      petzDownFiniteSupportTrace E α := by
  calc
    _ = ∑ y, (CFC.rpow (conditionalRenyiBlock E y) α *
        CFC.rpow
          ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
            (E.states y).marginalB) (1 - α)).trace.re :=
      petz_conditionalQ_classical_decomposition_all E α (1 - α)
    _ = ∑ y, (E.probs y : ℝ) *
        (CFC.rpow (E.states y).matrix α *
          CFC.rpow (identityTensorStateMatrix (a := A)
            (E.states y).marginalB) (1 - α)).trace.re := by
      apply Finset.sum_congr rfl
      intro y hy
      exact petz_conditionalQ_branch_weighted_of_one_lt
        E y α hα_pos hα_gt_one
    _ = ∑ y ∈ Ensemble.conditionalRenyiSupport E,
        (E.probs y : ℝ) *
          (CFC.rpow (E.states y).matrix α *
            CFC.rpow (identityTensorStateMatrix (a := A)
              (E.states y).marginalB) (1 - α)).trace.re := by
      rw [← Finset.sum_subset (Finset.subset_univ
        (Ensemble.conditionalRenyiSupport E))]
      intro y hy hnot
      have hprob : E.probs y = 0 :=
        (Ensemble.not_mem_conditionalRenyiSupport_iff E y).mp hnot
      simp [hprob]
    _ = ∑ y ∈ Ensemble.conditionalRenyiSupport E,
        (CFC.rpow (conditionalRenyiBlock E y) α *
          CFC.rpow
            ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
              (E.states y).marginalB) (1 - α)).trace.re := by
      apply Finset.sum_congr rfl
      intro y hy
      exact (petz_conditionalQ_branch_weighted_of_one_lt
        E y α hα_pos hα_gt_one).symm
    _ = petzDownFiniteSupportTrace E α := rfl

/-- The finite-support trace is the all-branch weighted exponential of the
normalized component entropies throughout the source Petz range. -/
theorem petzDownFiniteSupportTrace_eq_weightedComponentEntropy
    (E : Ensemble Y (A × B)) (α : ℝ)
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    petzDownFiniteSupportTrace E α =
      ∑ y, (E.probs y : ℝ) * Real.rpow 2
        ((1 - α) * petzDownComponentEntropy E y α) := by
  rcases lt_or_gt_of_ne hα_ne_one with hα_lt_one | hα_gt_one
  · calc
      petzDownFiniteSupportTrace E α =
          (CFC.rpow (State.cqConditioningState E).matrix α *
            CFC.rpow
              (identityTensorStateMatrix (a := A)
                (State.cqConditioningState E).marginalB) (1 - α)).trace.re :=
        (petzDownFiniteSupportTrace_eq_classicalQ
          E α hα_pos hα_lt_one).symm
      _ = ∑ y, (E.probs y : ℝ) *
          (CFC.rpow (E.states y).matrix α *
            CFC.rpow (identityTensorStateMatrix (a := A)
              (E.states y).marginalB) (1 - α)).trace.re :=
        petz_conditionalQ_classical_weighted E α hα_pos hα_lt_one
      _ = ∑ y, (E.probs y : ℝ) * Real.rpow 2
          ((1 - α) * petzDownComponentEntropy E y α) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [petzDownComponentQ_eq_rpow_entropy E y α hα_pos hα_ne_one]
  · calc
      petzDownFiniteSupportTrace E α =
          (CFC.rpow (State.cqConditioningState E).matrix α *
            CFC.rpow
              (identityTensorStateMatrix (a := A)
                (State.cqConditioningState E).marginalB) (1 - α)).trace.re :=
        (petzDownFiniteSupportTrace_eq_classicalQ_of_one_lt
          E α hα_pos hα_gt_one).symm
      _ = ∑ y, (CFC.rpow (conditionalRenyiBlock E y) α *
          CFC.rpow
            ((E.probs y : ℂ) • identityTensorStateMatrix (a := A)
              (E.states y).marginalB) (1 - α)).trace.re :=
        petz_conditionalQ_classical_decomposition_all E α (1 - α)
      _ = ∑ y, (E.probs y : ℝ) *
          (CFC.rpow (E.states y).matrix α *
            CFC.rpow (identityTensorStateMatrix (a := A)
              (E.states y).marginalB) (1 - α)).trace.re := by
        apply Finset.sum_congr rfl
        intro y hy
        exact petz_conditionalQ_branch_weighted_of_one_lt
          E y α hα_pos hα_gt_one
      _ = ∑ y, (E.probs y : ℝ) * Real.rpow 2
          ((1 - α) * petzDownComponentEntropy E y α) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [petzDownComponentQ_eq_rpow_entropy E y α hα_pos hα_ne_one]

noncomputable def petzDownFiniteSupportFormulaReal
    (E : Ensemble Y (A × B)) (α : ℝ) : ℝ :=
  (1 / (1 - α)) * log2 (petzDownFiniteSupportTrace E α)

noncomputable def petzUpOptimizerWeight
  (E : Ensemble Y (A × B)) (y : Y) (α : ℝ)
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  (E.probs y : ℝ) *
    Real.rpow 2 (((1 - α) / α) *
      petzConditionalBranch E y α hα_pos hα_ne_one)

noncomputable def petzUpOptimizerNormalization
    (E : Ensemble Y (A × B)) (α : ℝ)
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  ∑ y ∈ (Ensemble.conditionalRenyiSupport E),
    petzUpOptimizerWeight E y α hα_pos hα_ne_one

noncomputable def petzUpSourceFormula
    (E : Ensemble Y (A × B)) (α : ℝ) (hα_pos : 0 < α)
    (hα_ne_one : α ≠ 1) : EReal :=
  sSup {h : EReal |
    ∃ σ : State (B × Y),
      h = -(State.cqConditioningState E).petzRenyiReferenceE
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef_of_state (a := A) σ)
        α (hα_pos := hα_pos) (hα_ne_one := hα_ne_one)}

/-! On the strict subunit branch, the public EReal value is the coercion of
the source finite-support logarithmic sum.  The internal nonzero hypothesis
is discharged by `petzDownClassicalQ_pos` in the public theorem below. -/

theorem conditionalPetzRenyiDown_classicalConditioning_source_formula_of_lt_one
    (E : Ensemble Y (A × B)) (α : ℝ) (hα_pos : 0 < α)
    (hα_lt_one : α < 1) (hα_ne_one : α ≠ 1)
    (hQne :
      (CFC.rpow (State.cqConditioningState E).matrix α *
        CFC.rpow
          (identityTensorStateMatrix (a := A)
            (State.cqConditioningState E).marginalB) (1 - α)).trace.re ≠ 0) :
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

/-! The high-alpha reference is finite for the cq state because its support is
contained in the identity on A tensored with the B,Y marginal. -/

theorem conditionalPetzRenyiDown_classicalConditioning_source_formula_of_one_lt
    (E : Ensemble Y (A × B)) (α : ℝ) (hα_pos : 0 < α)
    (hα_gt_one : 1 < α) (hα_ne_one : α ≠ 1) :
    conditionalPetzRenyiDownE E α hα_pos hα_ne_one =
      -(petzRenyiReferenceFinite
        (State.cqConditioningState E)
        (identityTensorStateMatrix (a := A)
          (State.cqConditioningState E).marginalB)
        (identityTensorStateMatrix_posSemidef_of_state
          (a := A) (State.cqConditioningState E).marginalB)
        α hα_pos hα_ne_one : EReal) := by
  have hSupport :
      Matrix.Supports (State.cqConditioningState E).matrix
        (identityTensorStateMatrix (a := A)
          (State.cqConditioningState E).marginalB) := by
    simpa [identityTensorStateMatrix] using
      (matrix_supports_identityTensor_marginalB
        (State.cqConditioningState E))
  unfold conditionalPetzRenyiDownE
  rw [petzRenyiReferenceE_eq_coe_of_one_lt_of_supports _ _ _ α
    hα_pos hα_ne_one hα_gt_one hSupport]

theorem conditionalPetzRenyiDown_classicalConditioning_explicit_of_one_lt
    (E : Ensemble Y (A × B)) (α : ℝ) (hα_pos : 0 < α)
    (hα_gt_one : 1 < α) (hα_ne_one : α ≠ 1) :
    conditionalPetzRenyiDownE E α hα_pos hα_ne_one =
      (petzDownFiniteSupportFormulaReal E α : EReal) := by
  have hSupport :
      Matrix.Supports (State.cqConditioningState E).matrix
        (identityTensorStateMatrix (a := A)
          (State.cqConditioningState E).marginalB) := by
    simpa [identityTensorStateMatrix] using
      (matrix_supports_identityTensor_marginalB
        (State.cqConditioningState E))
  unfold conditionalPetzRenyiDownE
  rw [petzRenyiReferenceE_eq_coe_of_one_lt_of_supports _ _ _ α
    hα_pos hα_ne_one hα_gt_one hSupport]
  unfold petzRenyiReferenceFinite petzDownFiniteSupportFormulaReal
  rw [petzDownFiniteSupportTrace_eq_classicalQ_of_one_lt E α hα_pos hα_gt_one]
  rw [← EReal.coe_neg]
  congr 1
  field_simp [hα_ne_one]
  ring

/-! The public Petz down-arrow identity directly exposes the source's weighted
component-entropy formula.  Positivity of the normalized global cq `Q_α`
discharges the low-order finite-value side condition internally. -/

theorem conditionalPetzRenyiDown_classicalConditioning
    (E : Ensemble Y (A × B)) (α : ℝ) (hα_pos : 0 < α)
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
        (CFC.rpow (State.cqConditioningState E).matrix α *
          CFC.rpow
            (identityTensorStateMatrix (a := A)
              (State.cqConditioningState E).marginalB) (1 - α)).trace.re ≠ 0 :=
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

noncomputable def petzUpRightBlockDiagonal
    (blocks : Y → CMatrix B) : CMatrix (B × Y) :=
  (Classical.blockDiagonal blocks).submatrix
    (Equiv.prodComm B Y) (Equiv.prodComm B Y)

omit [DecidableEq A] [Fintype B] [DecidableEq B] in
theorem petz_partialTraceA_rightBlockDiagonal
    (blocks : Y → CMatrix (A × B)) :
    partialTraceA (a := A) (b := B × Y)
        (conditionalRenyiRightBlockDiagonal blocks) =
      petzUpRightBlockDiagonal (fun y =>
        partialTraceA (a := A) (b := B) (blocks y)) := by
  ext ⟨b, y⟩ ⟨b', y'⟩
  by_cases hyy : y = y'
  · subst y'
    simp [partialTraceA, petzUpRightBlockDiagonal,
      conditionalRenyiRightBlockDiagonal, Matrix.sum_apply,
      Matrix.submatrix_apply,
      Classical.blockDiagonal, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.single_apply]
  · have hxy : ∀ x : Y, ¬(x = y ∧ x = y') := by
      intro x h
      exact hyy (h.1.symm.trans h.2)
    simp [partialTraceA, petzUpRightBlockDiagonal,
      conditionalRenyiRightBlockDiagonal, Matrix.sum_apply,
      Matrix.submatrix_apply, hxy,
      Classical.blockDiagonal, Matrix.kronecker, Matrix.kroneckerMap_apply]

theorem petz_conditionalUpTraceMatrix_classical_decomposition
    (E : Ensemble Y (A × B)) (α : ℝ) :
    (State.cqConditioningState E).conditionalPetzRenyiUpTraceMatrix α =
      petzUpRightBlockDiagonal (fun y =>
        partialTraceA (a := A) (b := B)
          (CFC.rpow (conditionalRenyiBlock E y) α)) := by
  unfold conditionalPetzRenyiUpTraceMatrix
  rw [conditionalRenyiState_eq_rightBlockDiagonal E,
    conditionalRenyiRightBlockDiagonal_rpow_support
      (conditionalRenyiBlock E)
      (fun y => conditionalRenyiBlock_posSemidef E y) α,
    petz_partialTraceA_rightBlockDiagonal]

theorem petz_conditionalUpClosedTrace_classical_decomposition
    (E : Ensemble Y (A × B)) (α : ℝ) (hα_pos : 0 < α) :
    (State.cqConditioningState E).conditionalPetzRenyiUpClosedTrace α =
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
        partialTraceA (a := A) (b := B)
          (CFC.rpow (conditionalRenyiBlock E y) α)))
      (Classical.blockDiagonal_posSemidef _ (fun y =>
        partialTraceA_posSemidef
          (cMatrix_rpow_posSemidef (A := conditionalRenyiBlock E y)
            (s := α) (conditionalRenyiBlock_posSemidef E y)))) (1 / α)
  rw [he] at hpow
  rw [hpow]
  rw [conditionalRenyi_submatrix_equiv_trace,
    Classical.blockDiagonal_rpow _ (fun y =>
    partialTraceA_posSemidef
      (cMatrix_rpow_posSemidef (A := conditionalRenyiBlock E y)
        (s := α) (conditionalRenyiBlock_posSemidef E y))) (1 / α),
    Classical.blockDiagonal_trace, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro y hy
  exact petz_conditionalUp_branch_trace_weighted E y α hα_pos

noncomputable def petzUpClassicalFormulaReal
    (E : Ensemble Y (A × B)) (α : ℝ)
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  (α / (1 - α)) * log2
    (∑ y ∈ Ensemble.conditionalRenyiSupport E,
      (E.probs y : ℝ) * Real.rpow 2
        (((1 - α) / α) * petzConditionalBranch E y α hα_pos hα_ne_one))

theorem conditionalPetzRenyiUpAlternative_classicalFormula
    (E : Ensemble Y (A × B)) (α : ℝ) (hα_pos : 0 < α)
    (hα_ne_one : α ≠ 1) :
    (State.cqConditioningState E).conditionalPetzRenyiUpAlternative α =
      petzUpClassicalFormulaReal E α hα_pos hα_ne_one := by
  unfold conditionalPetzRenyiUpAlternative petzUpClassicalFormulaReal
  rw [petz_conditionalUpClosedTrace_classical_decomposition E α hα_pos]
  apply congrArg (fun x : ℝ => (α / (1 - α)) * log2 x)
  calc
    ∑ y, (E.probs y : ℝ) *
        (E.states y).conditionalPetzRenyiUpClosedTrace α =
      ∑ y ∈ Ensemble.conditionalRenyiSupport E,
        (E.probs y : ℝ) *
          (E.states y).conditionalPetzRenyiUpClosedTrace α := by
      rw [← Finset.sum_subset (Finset.subset_univ
        (Ensemble.conditionalRenyiSupport E))]
      intro y hy hnot
      have hprob : E.probs y = 0 :=
        (Ensemble.not_mem_conditionalRenyiSupport_iff E y).mp hnot
      simp [hprob]
    _ = ∑ y ∈ Ensemble.conditionalRenyiSupport E,
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
    [Nonempty (B × Y)] (E : Ensemble Y (A × B)) (α : ℝ)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) (hα_ne_one : α ≠ 1) :
    conditionalPetzRenyiUpE E α hα_pos hα_ne_one =
      (petzUpClassicalFormulaReal E α hα_pos hα_ne_one : EReal) := by
  rw [conditionalPetzRenyiUp_classicalConditioning_eq_closed_of_lt_one
    E α hα_pos hα_lt_one hα_ne_one]
  exact congrArg (fun x : ℝ => (x : EReal))
    (conditionalPetzRenyiUpAlternative_classicalFormula
      E α hα_pos hα_ne_one)

theorem conditionalPetzRenyiUp_classicalConditioning
    [Nonempty (B × Y)] (E : Ensemble Y (A × B)) (α : ℝ) (hα_pos : 0 < α)
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

end State

end

end QIT
