/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.ConditionalRenyiSource
public import QIT.Information.Renyi.SandwichedRenyiOptimizedUSC
public import QIT.Information.Entropy.Log2Lemmas

/-!
# Alternative expression for upward Petz conditional Renyi entropy

Source-shaped API and proof kernels for Tomamichel2015FiniteResources,
`cond.tex:173-200`, Lemma `lm:dau-new` and optimizer `eq:opt-sigma`.

The proof follows the source route: rewrite the fixed-reference Petz trace term
through the partial trace `Tr_A(ρ_AB^α)`, then specialize the Holder and
reverse-Holder Schatten variational formulas from `metric.tex:87-138`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

open Matrix

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace State

private theorem petzUp_log2_rpow_pos {x y : ℝ} (hx : 0 < x) :
    log2 (x ^ y) = y * log2 x := by
  dsimp [log2]
  rw [Real.log_rpow hx]
  ring

/-- The side-system PSD matrix `Tr_A(ρ_AB^α)` in
Tomamichel2015FiniteResources, `cond.tex:185-190`. -/
def conditionalPetzRenyiUpTraceMatrix (ρ : State (Prod a b)) (α : ℝ) : CMatrix b :=
  partialTraceA (a := a) (b := b) (CFC.rpow ρ.matrix α)

/-- `Tr_A(ρ_AB^α)` is positive semidefinite. -/
theorem conditionalPetzRenyiUpTraceMatrix_posSemidef
    (ρ : State (Prod a b)) (α : ℝ) :
    (ρ.conditionalPetzRenyiUpTraceMatrix α).PosSemidef := by
  exact partialTraceA_posSemidef
    (cMatrix_rpow_posSemidef (A := ρ.matrix) (s := α) ρ.pos)

/-- Closed trace scalar from Tomamichel2015FiniteResources,
`cond.tex:177`: `Tr((Tr_A ρ_AB^α)^(1/α))`. -/
def conditionalPetzRenyiUpClosedTrace
    (ρ : State (Prod a b)) (α : ℝ) : ℝ :=
  ((CFC.rpow (ρ.conditionalPetzRenyiUpTraceMatrix α) (1 / α)).trace).re

/-- Closed expression from Tomamichel2015FiniteResources, `cond.tex:177`. -/
def conditionalPetzRenyiUpAlternative
    (ρ : State (Prod a b)) (α : ℝ) : ℝ :=
  (α / (1 - α)) * log2 (ρ.conditionalPetzRenyiUpClosedTrace α)

@[simp]
theorem conditionalPetzRenyiUpAlternative_eq
    (ρ : State (Prod a b)) (α : ℝ) :
    ρ.conditionalPetzRenyiUpAlternative α =
      (α / (1 - α)) * log2 (ρ.conditionalPetzRenyiUpClosedTrace α) :=
  rfl

/-- Source rewrite from `cond.tex:185-186`:
the Petz fixed-reference trace term is the side trace pairing against
`Tr_A(ρ_AB^α)`. -/
theorem conditionalPetzRenyiTraceTerm_eq_partialTraceA
    (ρ : State (Prod a b)) (σ : State b) (α : ℝ) :
    ρ.conditionalPetzRenyiTraceTerm σ α =
      ((ρ.conditionalPetzRenyiUpTraceMatrix α *
        CFC.rpow σ.matrix (1 - α)).trace).re := by
  dsimp only [conditionalPetzRenyiTraceTerm, conditionalPetzRenyiUpTraceMatrix]
  change
    ((CFC.rpow ρ.matrix α *
      CFC.rpow (identityTensorStateMatrix (a := a) σ) (1 - α)).trace).re =
      ((partialTraceA (a := a) (b := b) (CFC.rpow ρ.matrix α) *
        CFC.rpow σ.matrix (1 - α)).trace).re
  rw [show CFC.rpow (identityTensorStateMatrix (a := a) σ) (1 - α) =
      Matrix.kronecker (1 : CMatrix a) (CFC.rpow σ.matrix (1 - α)) from by
        simpa [identityTensorStateMatrix] using
          cMatrix_rpow_identity_kronecker (a := a) σ.matrix σ.pos (1 - α)]
  calc
    ((CFC.rpow ρ.matrix α *
        Matrix.kronecker (1 : CMatrix a) (CFC.rpow σ.matrix (1 - α))).trace).re =
        ((Matrix.kronecker (1 : CMatrix a) (CFC.rpow σ.matrix (1 - α)) *
          CFC.rpow ρ.matrix α).trace).re := by
          rw [Matrix.trace_mul_comm]
    _ = ((CFC.rpow σ.matrix (1 - α) *
          partialTraceA (a := a) (b := b) (CFC.rpow ρ.matrix α)).trace).re := by
          rw [trace_kronecker_one_mul_eq_trace_mul_partialTraceA]
    _ = ((partialTraceA (a := a) (b := b) (CFC.rpow ρ.matrix α) *
          CFC.rpow σ.matrix (1 - α)).trace).re := by
          rw [Matrix.trace_mul_comm]

/-- The closed trace is the PSD Schatten `1/α` expression of
`Tr_A(ρ_AB^α)`, raised to the same exponent. -/
theorem conditionalPetzRenyiUpClosedTrace_eq_psdTracePower
    (ρ : State (Prod a b)) (α : ℝ) :
    ρ.conditionalPetzRenyiUpClosedTrace α =
      psdTracePower (ρ.conditionalPetzRenyiUpTraceMatrix α)
        (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α) (1 / α) := by
  rfl

/-- `Tr_A(ρ_AB^α)` is nonzero for a normalized left state. -/
theorem conditionalPetzRenyiUpTraceMatrix_ne_zero
    (ρ : State (Prod a b)) (α : ℝ) :
    ρ.conditionalPetzRenyiUpTraceMatrix α ≠ 0 := by
  intro hzero
  have htrace_eq :
      (ρ.conditionalPetzRenyiUpTraceMatrix α).trace.re =
        psdTracePower ρ.matrix ρ.pos α := by
    simp [conditionalPetzRenyiUpTraceMatrix, psdTracePower, partialTraceA_trace]
  have htrace_zero :
      (ρ.conditionalPetzRenyiUpTraceMatrix α).trace.re = 0 := by
    rw [hzero, Matrix.trace_zero]
    simp
  have hpow_pos : 0 < psdTracePower ρ.matrix ρ.pos α :=
    psdTracePower_pos_of_ne_zero ρ.matrix ρ.pos ρ.matrix_ne_zero
  linarith

/-- The closed trace scalar is strictly positive. -/
theorem conditionalPetzRenyiUpClosedTrace_pos
    (ρ : State (Prod a b)) (α : ℝ) :
    0 < ρ.conditionalPetzRenyiUpClosedTrace α := by
  have hMne : ρ.conditionalPetzRenyiUpTraceMatrix α ≠ 0 :=
    ρ.conditionalPetzRenyiUpTraceMatrix_ne_zero α
  simpa [conditionalPetzRenyiUpClosedTrace_eq_psdTracePower] using
    psdTracePower_pos_of_ne_zero
      (ρ.conditionalPetzRenyiUpTraceMatrix α)
      (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α)
      (p := 1 / α)
      hMne

/-- Source optimizer matrix from Tomamichel2015FiniteResources,
`cond.tex:188-190`, implemented through the reusable reverse-Holder optimizer. -/
def conditionalPetzRenyiUpOptimizerMatrix
    (ρ : State (Prod a b)) (α : ℝ) : CMatrix b :=
  psdTraceReverseHolderOptimizer
    (ρ.conditionalPetzRenyiUpTraceMatrix α)
    (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α)
    (1 / α)

/-- The optimizer matrix has the source expression
`(Tr_A(ρ_AB^α))^(1/α) / Tr((Tr_A(ρ_AB^α))^(1/α))`. -/
theorem conditionalPetzRenyiUpOptimizerMatrix_eq_source
    (ρ : State (Prod a b)) (α : ℝ) :
    ρ.conditionalPetzRenyiUpOptimizerMatrix α =
      (((ρ.conditionalPetzRenyiUpClosedTrace α)⁻¹ : ℝ) : ℂ) •
        CFC.rpow (ρ.conditionalPetzRenyiUpTraceMatrix α) (1 / α) := by
  simpa [conditionalPetzRenyiUpOptimizerMatrix,
    conditionalPetzRenyiUpClosedTrace_eq_psdTracePower] using
    (psdTraceReverseHolderOptimizer_eq_inv_tracePower_smul_rpow
      (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α) (p := 1 / α))

/-- The source optimizer as a normalized state on `B`. -/
def conditionalPetzRenyiUpOptimizer
    (ρ : State (Prod a b)) (α : ℝ) (hα_pos : 0 < α) : State b where
  matrix := ρ.conditionalPetzRenyiUpOptimizerMatrix α
  pos := by
    have hp : 0 < 1 / α := one_div_pos.mpr hα_pos
    have hSpos : 0 <
        psdTracePower (ρ.conditionalPetzRenyiUpTraceMatrix α)
          (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α) (1 / α) := by
      simpa [conditionalPetzRenyiUpClosedTrace_eq_psdTracePower] using
        ρ.conditionalPetzRenyiUpClosedTrace_pos α
    rcases psdTraceReverseHolderOptimizer_props
      (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α) hp hSpos with
      ⟨hN, _hNtr, _hSupport, _hattain⟩
    simpa [conditionalPetzRenyiUpOptimizerMatrix] using hN
  trace_eq_one := by
    have hp : 0 < 1 / α := one_div_pos.mpr hα_pos
    have hSpos : 0 <
        psdTracePower (ρ.conditionalPetzRenyiUpTraceMatrix α)
          (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α) (1 / α) := by
      simpa [conditionalPetzRenyiUpClosedTrace_eq_psdTracePower] using
        ρ.conditionalPetzRenyiUpClosedTrace_pos α
    rcases psdTraceReverseHolderOptimizer_props
      (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α) hp hSpos with
      ⟨hN, hNtr, _hSupport, _hattain⟩
    apply Complex.ext
    · simpa [conditionalPetzRenyiUpOptimizerMatrix] using hNtr
    · change
        (trace (psdTraceReverseHolderOptimizer
          (ρ.conditionalPetzRenyiUpTraceMatrix α)
          (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α)
          (1 / α))).im = 0
      exact (Matrix.PosSemidef.trace_nonneg hN).2.symm

@[simp]
theorem conditionalPetzRenyiUpOptimizer_matrix
    (ρ : State (Prod a b)) (α : ℝ) (hα_pos : 0 < α) :
    (ρ.conditionalPetzRenyiUpOptimizer α hα_pos).matrix =
      ρ.conditionalPetzRenyiUpOptimizerMatrix α :=
  rfl

/-- The source optimizer attains the Schatten variational trace objective. -/
theorem conditionalPetzRenyiUpOptimizer_trace_objective_eq_schatten
    (ρ : State (Prod a b)) {α : ℝ} (hα_pos : 0 < α) :
    ((ρ.conditionalPetzRenyiUpTraceMatrix α *
      CFC.rpow (ρ.conditionalPetzRenyiUpOptimizer α hα_pos).matrix
        (1 - α)).trace).re =
      psdSchattenPNorm (ρ.conditionalPetzRenyiUpTraceMatrix α)
        (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α)
        ⟨1 / α, one_div_pos.mpr hα_pos⟩ := by
  have hp : 0 < 1 / α := one_div_pos.mpr hα_pos
  have hSpos : 0 <
      psdTracePower (ρ.conditionalPetzRenyiUpTraceMatrix α)
        (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α) (1 / α) := by
    simpa [conditionalPetzRenyiUpClosedTrace_eq_psdTracePower] using
      ρ.conditionalPetzRenyiUpClosedTrace_pos α
  rcases psdTraceReverseHolderOptimizer_props
      (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α) hp hSpos with
    ⟨_hN, _hNtr, _hSupport, hattain⟩
  have hexp : 1 - 1 / (1 / α) = 1 - α := by
    field_simp [hα_pos.ne']
  change
    ((ρ.conditionalPetzRenyiUpTraceMatrix α *
      CFC.rpow (psdTraceReverseHolderOptimizer
        (ρ.conditionalPetzRenyiUpTraceMatrix α)
        (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α)
        (1 / α)) (1 - α)).trace).re =
      psdSchattenPNorm (ρ.conditionalPetzRenyiUpTraceMatrix α)
        (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α)
        ⟨1 / α, one_div_pos.mpr hα_pos⟩
  rw [← hexp]
  exact hattain.symm

/-- The source optimizer attains the Petz trace term at the closed trace
quantity raised to `α`. -/
theorem conditionalPetzRenyiUpOptimizer_traceTerm_eq_closedTrace_rpow
    (ρ : State (Prod a b)) {α : ℝ} (hα_pos : 0 < α) :
    ρ.conditionalPetzRenyiTraceTerm
        (ρ.conditionalPetzRenyiUpOptimizer α hα_pos) α =
      (ρ.conditionalPetzRenyiUpClosedTrace α) ^ α := by
  rw [ρ.conditionalPetzRenyiTraceTerm_eq_partialTraceA]
  rw [ρ.conditionalPetzRenyiUpOptimizer_trace_objective_eq_schatten hα_pos]
  dsimp [psdSchattenPNorm, Internal.psdSchattenExpression,
    conditionalPetzRenyiUpClosedTrace,
    conditionalPetzRenyiUpClosedTrace_eq_psdTracePower]
  have hrecip : 1 / (1 / α) = α := by field_simp [hα_pos.ne']
  rw [hrecip]

/-- Entropy-level attainment by the source optimizer from
Tomamichel2015FiniteResources, `cond.tex:188-190`, `eq:opt-sigma`.

The optimizer is a normalized PSD state. It may be singular, so this theorem is
the source-shaped optimizer statement before the full-rank `sSup` bridge. -/
theorem conditionalPetzRenyiUpOptimizer_entropy_eq_alternative
    (ρ : State (Prod a b)) {α : ℝ} (hα_pos : 0 < α) :
    (1 / (1 - α)) *
        log2 (ρ.conditionalPetzRenyiTraceTerm
          (ρ.conditionalPetzRenyiUpOptimizer α hα_pos) α) =
      ρ.conditionalPetzRenyiUpAlternative α := by
  rw [ρ.conditionalPetzRenyiUpOptimizer_traceTerm_eq_closedTrace_rpow hα_pos]
  have hclosed_pos : 0 < ρ.conditionalPetzRenyiUpClosedTrace α :=
    ρ.conditionalPetzRenyiUpClosedTrace_pos α
  rw [petzUp_log2_rpow_pos hclosed_pos]
  simp [conditionalPetzRenyiUpAlternative]
  ring

/-- Holder side of Tomamichel2015FiniteResources, `cond.tex:184-187`:
for `0 < α < 1`, every normalized side state has trace objective at most the
closed expression's trace factor. -/
theorem conditionalPetzRenyiTraceTerm_le_closedTrace_rpow_of_lt_one
    (ρ : State (Prod a b)) (σ : State b) {α : ℝ}
    (hα_pos : 0 < α) (hα_lt_one : α < 1) :
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
  have hholder :
      ((ρ.conditionalPetzRenyiUpTraceMatrix α *
        CFC.rpow σ.matrix (1 - α)).trace).re ≤
        psdSchattenPNorm (ρ.conditionalPetzRenyiUpTraceMatrix α)
          (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α)
          ⟨1 / α, one_div_pos.mpr hα_pos⟩ :=
    psd_trace_rpow_holder_variational_upper
      (M := ρ.conditionalPetzRenyiUpTraceMatrix α) (N := σ.matrix)
      (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α) σ.pos htr hpq hr
  have hrecip : 1 / (1 / α) = α := by field_simp [hα_pos.ne']
  simpa [psdSchattenPNorm, Internal.psdSchattenExpression,
    conditionalPetzRenyiUpClosedTrace,
    conditionalPetzRenyiUpClosedTrace_eq_psdTracePower, hrecip] using hholder

/-- Reverse-Holder side of Tomamichel2015FiniteResources, `cond.tex:184-187`:
for `1 < α`, every full-rank normalized side state has trace objective at least
the closed expression's trace factor. -/
theorem closedTrace_rpow_le_conditionalPetzRenyiTraceTerm_of_one_lt
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) {α : ℝ}
    (hα_gt_one : 1 < α) :
    (ρ.conditionalPetzRenyiUpClosedTrace α) ^ α ≤
      ρ.conditionalPetzRenyiTraceTerm σ α := by
  rw [ρ.conditionalPetzRenyiTraceTerm_eq_partialTraceA]
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_gt_one
  have hp0 : 0 < 1 / α := one_div_pos.mpr hα_pos
  have hp1 : 1 / α < 1 := by
    rw [div_lt_iff₀ hα_pos]
    simpa using hα_gt_one
  have htr : σ.matrix.trace.re = 1 := by
    rw [σ.trace_eq_one]
    simp
  have hSupport : Matrix.Supports (ρ.conditionalPetzRenyiUpTraceMatrix α) σ.matrix :=
    Matrix.Supports.of_right_posDef (ρ.conditionalPetzRenyiUpTraceMatrix α) σ.matrix hσ
  have hr : 1 - α = 1 - 1 / (1 / α) := by
    field_simp [hα_pos.ne']
  have hrev :
      psdSchattenPNorm (ρ.conditionalPetzRenyiUpTraceMatrix α)
          (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α)
          ⟨1 / α, one_div_pos.mpr hα_pos⟩ ≤
        ((ρ.conditionalPetzRenyiUpTraceMatrix α *
          CFC.rpow σ.matrix (1 - α)).trace).re :=
    psd_trace_rpow_reverse_holder_variational
      (M := ρ.conditionalPetzRenyiUpTraceMatrix α) (N := σ.matrix)
      (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α) σ.pos htr hSupport
      hp0 hp1 hr
  have hrecip : 1 / (1 / α) = α := by field_simp [hα_pos.ne']
  simpa [psdSchattenPNorm, Internal.psdSchattenExpression,
    conditionalPetzRenyiUpClosedTrace,
    conditionalPetzRenyiUpClosedTrace_eq_psdTracePower, hrecip] using hrev

/-- Entropy-level Holder upper bound for full-rank side references,
`0 < α < 1`. -/
theorem conditionalPetzRenyiEntropyCandidateFullReference_le_alternative_of_lt_one
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1) (hα_ne_one : α ≠ 1) :
    ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α hα_pos hα_ne_one ≤
      ρ.conditionalPetzRenyiUpAlternative α := by
  have htrace_pos : 0 < ρ.conditionalPetzRenyiTraceTerm σ α :=
    ρ.conditionalPetzRenyiTraceTerm_pos_of_fullReference σ hσ α
  have hclosed_pos : 0 < ρ.conditionalPetzRenyiUpClosedTrace α :=
    ρ.conditionalPetzRenyiUpClosedTrace_pos α
  have htrace_le :
      ρ.conditionalPetzRenyiTraceTerm σ α ≤
        (ρ.conditionalPetzRenyiUpClosedTrace α) ^ α :=
    ρ.conditionalPetzRenyiTraceTerm_le_closedTrace_rpow_of_lt_one
      σ hα_pos hα_lt_one
  have hlog_le :
      log2 (ρ.conditionalPetzRenyiTraceTerm σ α) ≤
        α * log2 (ρ.conditionalPetzRenyiUpClosedTrace α) := by
    have h := log2_mono_of_pos htrace_pos htrace_le
    simpa [petzUp_log2_rpow_pos hclosed_pos] using h
  have hcoef_nonneg : 0 ≤ 1 / (1 - α) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlog_le hcoef_nonneg
  simpa [conditionalPetzRenyiEntropyCandidateFullReference] using
    calc
      (1 / (1 - α)) * log2 (ρ.conditionalPetzRenyiTraceTerm σ α) ≤
          (1 / (1 - α)) *
            (α * log2 (ρ.conditionalPetzRenyiUpClosedTrace α)) := hmul
      _ = ρ.conditionalPetzRenyiUpAlternative α := by
          simp [conditionalPetzRenyiUpAlternative]
          ring

/-- Entropy-level reverse-Holder upper bound for full-rank side references,
`1 < α`. -/
theorem conditionalPetzRenyiEntropyCandidateFullReference_le_alternative_of_one_lt
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef)
    {α : ℝ} (hα_gt_one : 1 < α) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α hα_pos hα_ne_one ≤
      ρ.conditionalPetzRenyiUpAlternative α := by
  have htrace_pos : 0 < ρ.conditionalPetzRenyiTraceTerm σ α :=
    ρ.conditionalPetzRenyiTraceTerm_pos_of_fullReference σ hσ α
  have hclosed_pos : 0 < ρ.conditionalPetzRenyiUpClosedTrace α :=
    ρ.conditionalPetzRenyiUpClosedTrace_pos α
  have hclosed_pow_pos : 0 < (ρ.conditionalPetzRenyiUpClosedTrace α) ^ α :=
    Real.rpow_pos_of_pos hclosed_pos α
  have htrace_ge :
      (ρ.conditionalPetzRenyiUpClosedTrace α) ^ α ≤
        ρ.conditionalPetzRenyiTraceTerm σ α :=
    ρ.closedTrace_rpow_le_conditionalPetzRenyiTraceTerm_of_one_lt
      σ hσ hα_gt_one
  have hlog_ge :
      α * log2 (ρ.conditionalPetzRenyiUpClosedTrace α) ≤
        log2 (ρ.conditionalPetzRenyiTraceTerm σ α) := by
    have h := log2_mono_of_pos hclosed_pow_pos htrace_ge
    simpa [petzUp_log2_rpow_pos hclosed_pos] using h
  have hcoef_nonpos : 1 / (1 - α) ≤ 0 := by
    exact div_nonpos_of_nonneg_of_nonpos zero_le_one (sub_nonpos.mpr hα_gt_one.le)
  have hmul := mul_le_mul_of_nonpos_left hlog_ge hcoef_nonpos
  simpa [conditionalPetzRenyiEntropyCandidateFullReference] using
    calc
      (1 / (1 - α)) * log2 (ρ.conditionalPetzRenyiTraceTerm σ α) ≤
          (1 / (1 - α)) *
            (α * log2 (ρ.conditionalPetzRenyiUpClosedTrace α)) := hmul
      _ = ρ.conditionalPetzRenyiUpAlternative α := by
          simp [conditionalPetzRenyiUpAlternative]
          ring

/-- The full-rank upward Petz value set is bounded above by the alternative
expression for `0 < α < 1`. -/
theorem conditionalPetzRenyiUp_le_alternative_of_lt_one [Nonempty b]
    (ρ : State (Prod a b)) {α : ℝ}
    (hα_pos : 0 < α) (hα_lt_one : α < 1) (hα_ne_one : α ≠ 1) :
    ρ.conditionalPetzRenyiUp α hα_pos hα_ne_one ≤
      ρ.conditionalPetzRenyiUpAlternative α :=
  ρ.conditionalPetzRenyiUp_le_of_forall_candidate_le α hα_pos hα_ne_one
    (fun σ hσ =>
      ρ.conditionalPetzRenyiEntropyCandidateFullReference_le_alternative_of_lt_one
        σ hσ hα_pos hα_lt_one hα_ne_one)

/-- The source optimizer supports the side matrix `Tr_A(ρ_AB^α)`. -/
theorem conditionalPetzRenyiUpTraceMatrix_supports_optimizer
    (ρ : State (Prod a b)) {α : ℝ} (hα_pos : 0 < α) :
    Matrix.Supports
      (ρ.conditionalPetzRenyiUpTraceMatrix α)
      (ρ.conditionalPetzRenyiUpOptimizer α hα_pos).matrix := by
  have hp : 0 < 1 / α := one_div_pos.mpr hα_pos
  have hSpos : 0 <
      psdTracePower (ρ.conditionalPetzRenyiUpTraceMatrix α)
        (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α) (1 / α) := by
    simpa [conditionalPetzRenyiUpClosedTrace_eq_psdTracePower] using
      ρ.conditionalPetzRenyiUpClosedTrace_pos α
  rcases psdTraceReverseHolderOptimizer_props
      (ρ.conditionalPetzRenyiUpTraceMatrix_posSemidef α) hp hSpos with
    ⟨_hN, _hNtr, hSupport, _hattain⟩
  simpa [conditionalPetzRenyiUpOptimizer_matrix, conditionalPetzRenyiUpOptimizerMatrix]
    using hSupport

/-- Full-rank normalized identity regularization of the source optimizer.

For `ε > 0`, this is `(σ* + ε I) / Tr(σ* + ε I)`; outside the source filter
it is filled by `σ*` only to make a total path. -/
def conditionalPetzRenyiUpOptimizerRegularizationState [Nonempty b]
    (ρ : State (Prod a b)) (α : ℝ) (hα_pos : 0 < α) (ε : ℝ) : State b :=
  if hε : 0 < ε then
    stateOfPosDefReference
      ((ρ.conditionalPetzRenyiUpOptimizer α hα_pos).matrix + ε • (1 : CMatrix b))
      (cMatrix_posSemidef_add_pos_smul_one_posDef
        (ρ.conditionalPetzRenyiUpOptimizer α hα_pos).pos hε)
  else
    ρ.conditionalPetzRenyiUpOptimizer α hα_pos

@[simp]
theorem conditionalPetzRenyiUpOptimizerRegularizationState_eq_of_pos [Nonempty b]
    (ρ : State (Prod a b)) (α : ℝ) (hα_pos : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ρ.conditionalPetzRenyiUpOptimizerRegularizationState α hα_pos ε =
      stateOfPosDefReference
        ((ρ.conditionalPetzRenyiUpOptimizer α hα_pos).matrix + ε • (1 : CMatrix b))
        (cMatrix_posSemidef_add_pos_smul_one_posDef
          (ρ.conditionalPetzRenyiUpOptimizer α hα_pos).pos hε) := by
  simp [conditionalPetzRenyiUpOptimizerRegularizationState, hε]

/-- The identity-regularized optimizer path is full-rank for `ε > 0`. -/
theorem conditionalPetzRenyiUpOptimizerRegularizationState_posDef_of_pos [Nonempty b]
    (ρ : State (Prod a b)) (α : ℝ) (hα_pos : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    (ρ.conditionalPetzRenyiUpOptimizerRegularizationState α hα_pos ε).matrix.PosDef := by
  rw [ρ.conditionalPetzRenyiUpOptimizerRegularizationState_eq_of_pos α hα_pos hε]
  exact stateOfPosDefReference_posDef
    ((ρ.conditionalPetzRenyiUpOptimizer α hα_pos).matrix + ε • (1 : CMatrix b))
    (cMatrix_posSemidef_add_pos_smul_one_posDef
      (ρ.conditionalPetzRenyiUpOptimizer α hα_pos).pos hε)

/-- The trace of the unnormalized optimizer identity regularization. -/
theorem conditionalPetzRenyiUpOptimizer_add_smul_one_trace_re [Nonempty b]
    (ρ : State (Prod a b)) {α : ℝ} (hα_pos : 0 < α) (ε : ℝ) :
    (((ρ.conditionalPetzRenyiUpOptimizer α hα_pos).matrix +
      ε • (1 : CMatrix b)).trace).re =
        1 + ε * (Fintype.card b : ℝ) := by
  have htr :
      (ρ.conditionalPetzRenyiUpOptimizerMatrix α).trace.re = 1 := by
    simpa [conditionalPetzRenyiUpOptimizer_matrix] using
      congrArg Complex.re
        (ρ.conditionalPetzRenyiUpOptimizer α hα_pos).trace_eq_one
  rw [Matrix.trace_add, Matrix.trace_smul,
    conditionalPetzRenyiUpOptimizer_matrix, Matrix.trace_one]
  simp [Complex.add_re, Complex.real_smul, htr]

/-- The trace-normalizing scalar in the optimizer identity regularization
tends to `1` as `ε → 0+`. -/
theorem conditionalPetzRenyiUpOptimizerRegularization_scale_tendsto [Nonempty b]
    (ρ : State (Prod a b)) {α : ℝ} (hα_pos : 0 < α) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ((((ρ.conditionalPetzRenyiUpOptimizer α hα_pos).matrix +
          ε • (1 : CMatrix b)).trace).re)⁻¹)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 : ℝ)) := by
  have htrace :
      Filter.Tendsto
        (fun ε : ℝ =>
          (((ρ.conditionalPetzRenyiUpOptimizer α hα_pos).matrix +
            ε • (1 : CMatrix b)).trace).re)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 : ℝ)) := by
    have htr :
        (ρ.conditionalPetzRenyiUpOptimizerMatrix α).trace.re = 1 := by
      simpa [conditionalPetzRenyiUpOptimizer_matrix] using
        congrArg Complex.re
          (ρ.conditionalPetzRenyiUpOptimizer α hα_pos).trace_eq_one
    have hcont : Continuous fun ε : ℝ => 1 + ε * (Fintype.card b : ℝ) := by
      fun_prop
    simpa [Matrix.trace_add, Matrix.trace_smul, conditionalPetzRenyiUpOptimizer_matrix,
      Matrix.trace_one, Complex.add_re, Complex.real_smul, htr] using
      (hcont.continuousWithinAt (x := (0 : ℝ)) (s := Set.Ioi (0 : ℝ))).tendsto
  simpa using htrace.inv₀ one_ne_zero

/-- Trace-term convergence along the normalized full-rank identity
regularization of the source optimizer. This is the full-rank bridge for
Tomamichel2015FiniteResources, `cond.tex:188-190`. -/
theorem conditionalPetzRenyiTraceTerm_optimizerRegularization_tendsto [Nonempty b]
    (ρ : State (Prod a b)) {α : ℝ} (hα_pos : 0 < α) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ρ.conditionalPetzRenyiTraceTerm
          (ρ.conditionalPetzRenyiUpOptimizerRegularizationState α hα_pos ε) α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (ρ.conditionalPetzRenyiTraceTerm
          (ρ.conditionalPetzRenyiUpOptimizer α hα_pos) α)) := by
  let σstar : State b := ρ.conditionalPetzRenyiUpOptimizer α hα_pos
  let M : CMatrix b := ρ.conditionalPetzRenyiUpTraceMatrix α
  have hSupport : Matrix.Supports M σstar.matrix := by
    simpa [M, σstar] using
      ρ.conditionalPetzRenyiUpTraceMatrix_supports_optimizer hα_pos
  have hraw :
      Filter.Tendsto
        (fun ε : ℝ =>
          ((M * CFC.rpow (σstar.matrix + ε • (1 : CMatrix b)) (1 - α)).trace).re)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((M * CFC.rpow σstar.matrix (1 - α)).trace).re) :=
    trace_mul_cMatrix_rpow_add_pos_smul_one_tendsto_of_support
      σstar.pos hSupport (1 - α)
  have hscale :
      Filter.Tendsto
        (fun ε : ℝ =>
          ((((σstar.matrix + ε • (1 : CMatrix b)).trace).re)⁻¹) ^ (1 - α))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 : ℝ)) := by
    have hs :
        Filter.Tendsto
          (fun ε : ℝ => (((σstar.matrix + ε • (1 : CMatrix b)).trace).re)⁻¹)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 : ℝ)) := by
      simpa [σstar] using
        ρ.conditionalPetzRenyiUpOptimizerRegularization_scale_tendsto hα_pos
    have hcont : ContinuousAt (fun x : ℝ => x ^ (1 - α)) (1 : ℝ) :=
      Real.continuousAt_rpow_const 1 (1 - α) (Or.inl one_ne_zero)
    simpa using hcont.tendsto.comp hs
  have hprod :
      Filter.Tendsto
        (fun ε : ℝ =>
          ((((σstar.matrix + ε • (1 : CMatrix b)).trace).re)⁻¹) ^ (1 - α) *
            ((M * CFC.rpow (σstar.matrix + ε • (1 : CMatrix b)) (1 - α)).trace).re)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((M * CFC.rpow σstar.matrix (1 - α)).trace).re) := by
    simpa [one_mul] using hscale.mul hraw
  rw [ρ.conditionalPetzRenyiTraceTerm_eq_partialTraceA]
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : 0 < ε := hε
  have hpd :
      (σstar.matrix + ε • (1 : CMatrix b)).PosDef :=
    cMatrix_posSemidef_add_pos_smul_one_posDef σstar.pos hεpos
  rw [ρ.conditionalPetzRenyiUpOptimizerRegularizationState_eq_of_pos α hα_pos hεpos]
  rw [ρ.conditionalPetzRenyiTraceTerm_eq_partialTraceA]
  have hscale_nonneg :
      0 ≤ (((σstar.matrix + ε • (1 : CMatrix b)).trace).re)⁻¹ := by
    have htr_pos : 0 < ((σstar.matrix + ε • (1 : CMatrix b)).trace).re :=
      (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hpd)).1
    exact inv_nonneg.mpr htr_pos.le
  have hpow :
      CFC.rpow (stateOfPosDefReference
        (σstar.matrix + ε • (1 : CMatrix b)) hpd).matrix (1 - α) =
        ((((σstar.matrix + ε • (1 : CMatrix b)).trace).re)⁻¹ ^ (1 - α) : ℝ) •
          CFC.rpow (σstar.matrix + ε • (1 : CMatrix b)) (1 - α) := by
    rw [stateOfPosDefReference_matrix]
    exact cMatrix_rpow_real_smul_posSemidef_schatten hpd.posSemidef hscale_nonneg
  rw [hpow]
  simp [M, σstar, Matrix.trace_smul, Complex.mul_re]

/-- Entropy-value convergence along the normalized full-rank identity
regularization of the source optimizer. -/
theorem conditionalPetzRenyiEntropy_optimizerRegularization_tendsto_alternative [Nonempty b]
    (ρ : State (Prod a b)) {α : ℝ} (hα_pos : 0 < α) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (1 / (1 - α)) *
          log2 (ρ.conditionalPetzRenyiTraceTerm
            (ρ.conditionalPetzRenyiUpOptimizerRegularizationState α hα_pos ε) α))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (ρ.conditionalPetzRenyiUpAlternative α)) := by
  have htrace := ρ.conditionalPetzRenyiTraceTerm_optimizerRegularization_tendsto hα_pos
  have hlimit_pos :
      0 < ρ.conditionalPetzRenyiTraceTerm
        (ρ.conditionalPetzRenyiUpOptimizer α hα_pos) α := by
    rw [ρ.conditionalPetzRenyiUpOptimizer_traceTerm_eq_closedTrace_rpow hα_pos]
    exact Real.rpow_pos_of_pos (ρ.conditionalPetzRenyiUpClosedTrace_pos α) α
  have hlog2_cont : ContinuousAt (fun x : ℝ => log2 x)
      (ρ.conditionalPetzRenyiTraceTerm
        (ρ.conditionalPetzRenyiUpOptimizer α hα_pos) α) := by
    unfold log2
    exact (Real.continuousAt_log hlimit_pos.ne').div_const _
  have hlog := hlog2_cont.tendsto.comp htrace
  have hmul :
      Filter.Tendsto
        (fun ε : ℝ =>
          (1 / (1 - α)) *
            log2 (ρ.conditionalPetzRenyiTraceTerm
              (ρ.conditionalPetzRenyiUpOptimizerRegularizationState α hα_pos ε) α))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((1 / (1 - α)) *
          log2 (ρ.conditionalPetzRenyiTraceTerm
            (ρ.conditionalPetzRenyiUpOptimizer α hα_pos) α))) :=
    (continuous_const_mul _).tendsto _ |>.comp hlog
  rw [ρ.conditionalPetzRenyiUpOptimizer_entropy_eq_alternative hα_pos] at hmul
  exact hmul

/-- The full-rank `sSup` upward Petz API is bounded below by the source closed
alternative expression. The proof approximates the possibly singular source
optimizer by normalized full-rank identity regularizations. -/
theorem conditionalPetzRenyiUpAlternative_le_conditionalPetzRenyiUp_of_bddAbove
    [Nonempty b] (ρ : State (Prod a b)) {α : ℝ}
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1)
    (hbdd : BddAbove (ρ.conditionalPetzRenyiUpValueSet α hα_pos hα_ne_one)) :
    ρ.conditionalPetzRenyiUpAlternative α ≤
      ρ.conditionalPetzRenyiUp α hα_pos hα_ne_one := by
  refine le_of_tendsto
    (ρ.conditionalPetzRenyiEntropy_optimizerRegularization_tendsto_alternative hα_pos) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hpd :
      (ρ.conditionalPetzRenyiUpOptimizerRegularizationState α hα_pos ε).matrix.PosDef :=
    ρ.conditionalPetzRenyiUpOptimizerRegularizationState_posDef_of_pos α hα_pos hε
  have hle :
      ρ.conditionalPetzRenyiEntropyCandidateFullReference
          (ρ.conditionalPetzRenyiUpOptimizerRegularizationState α hα_pos ε)
          hpd α hα_pos hα_ne_one ≤
        ρ.conditionalPetzRenyiUp α hα_pos hα_ne_one :=
    ρ.conditionalPetzRenyiEntropyCandidateFullReference_le_conditionalPetzRenyiUp_of_bddAbove
      (ρ.conditionalPetzRenyiUpOptimizerRegularizationState α hα_pos ε)
      hpd α hα_pos hα_ne_one hbdd
  simpa [conditionalPetzRenyiEntropyCandidateFullReference] using hle

/-- For `0 < α < 1`, the full-rank upward Petz API equals Tomamichel's closed
alternative expression. -/
theorem conditionalPetzRenyiUp_eq_alternative_of_lt_one [Nonempty b]
    (ρ : State (Prod a b)) {α : ℝ}
    (hα_pos : 0 < α) (hα_lt_one : α < 1) (hα_ne_one : α ≠ 1) :
    ρ.conditionalPetzRenyiUp α hα_pos hα_ne_one =
      ρ.conditionalPetzRenyiUpAlternative α := by
  have hbdd : BddAbove (ρ.conditionalPetzRenyiUpValueSet α hα_pos hα_ne_one) :=
    ρ.conditionalPetzRenyiUpValueSet_bddAbove_of_forall_candidate_le
      α hα_pos hα_ne_one
      (C := ρ.conditionalPetzRenyiUpAlternative α)
      (fun σ hσ =>
        ρ.conditionalPetzRenyiEntropyCandidateFullReference_le_alternative_of_lt_one
          σ hσ hα_pos hα_lt_one hα_ne_one)
  exact le_antisymm
    (ρ.conditionalPetzRenyiUp_le_alternative_of_lt_one
      hα_pos hα_lt_one hα_ne_one)
    (ρ.conditionalPetzRenyiUpAlternative_le_conditionalPetzRenyiUp_of_bddAbove
      hα_pos hα_ne_one hbdd)

/-- The full-rank upward Petz value set is bounded above by the alternative
expression for `1 < α`. -/
theorem conditionalPetzRenyiUp_le_alternative_of_one_lt [Nonempty b]
    (ρ : State (Prod a b)) {α : ℝ}
    (hα_gt_one : 1 < α) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalPetzRenyiUp α hα_pos hα_ne_one ≤
      ρ.conditionalPetzRenyiUpAlternative α :=
  ρ.conditionalPetzRenyiUp_le_of_forall_candidate_le α hα_pos hα_ne_one
    (fun σ hσ =>
      ρ.conditionalPetzRenyiEntropyCandidateFullReference_le_alternative_of_one_lt
        σ hσ hα_gt_one hα_pos hα_ne_one)

/-- For `1 < α`, the full-rank upward Petz API equals Tomamichel's closed
alternative expression. -/
theorem conditionalPetzRenyiUp_eq_alternative_of_one_lt [Nonempty b]
    (ρ : State (Prod a b)) {α : ℝ}
    (hα_gt_one : 1 < α) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalPetzRenyiUp α hα_pos hα_ne_one =
      ρ.conditionalPetzRenyiUpAlternative α := by
  have hbdd : BddAbove (ρ.conditionalPetzRenyiUpValueSet α hα_pos hα_ne_one) :=
    ρ.conditionalPetzRenyiUpValueSet_bddAbove_of_forall_candidate_le
      α hα_pos hα_ne_one
      (C := ρ.conditionalPetzRenyiUpAlternative α)
      (fun σ hσ =>
        ρ.conditionalPetzRenyiEntropyCandidateFullReference_le_alternative_of_one_lt
          σ hσ hα_gt_one hα_pos hα_ne_one)
  exact le_antisymm
    (ρ.conditionalPetzRenyiUp_le_alternative_of_one_lt
      hα_gt_one hα_pos hα_ne_one)
    (ρ.conditionalPetzRenyiUpAlternative_le_conditionalPetzRenyiUp_of_bddAbove
      hα_pos hα_ne_one hbdd)

/-- Tomamichel2015FiniteResources, `cond.tex:173-200`, Lemma `lm:dau-new`:
closed-form alternative expression for upward Petz conditional Renyi entropy. -/
theorem conditionalPetzRenyiUp_eq_alternative [Nonempty b]
    (ρ : State (Prod a b)) {α : ℝ}
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalPetzRenyiUp α hα_pos hα_ne_one =
      ρ.conditionalPetzRenyiUpAlternative α := by
  rcases lt_or_gt_of_ne hα_ne_one with hα_lt_one | hα_gt_one
  · exact ρ.conditionalPetzRenyiUp_eq_alternative_of_lt_one
      hα_pos hα_lt_one hα_ne_one
  · exact ρ.conditionalPetzRenyiUp_eq_alternative_of_one_lt
      hα_gt_one hα_pos hα_ne_one

end State

end

end QIT
