/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Classical.CQState
public import QIT.Core.POVMProbability

/-!
# Local classical bridge

This module ties the local classical-register view to cq-state marginals and
POVM measurement outputs. Classical systems are represented as diagonal
matrices in a fixed finite basis, following the classical-system and
classical-quantum decompositions in [Tomamichel2015FiniteResources,
prelim.tex:321-327,617-624] and the measurement-output route in
[Tomamichel2015FiniteResources, prelim.tex:813-817].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT
namespace Classical

universe u v

noncomputable section

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [DecidableEq ι]

/-- A classical probability distribution as a diagonal density state. -/
def diagonalState (p : ι → ℝ≥0) (hsum : ∑ i, p i = 1) : State ι where
  matrix := Matrix.diagonal fun i => (p i : ℂ)
  pos := by
    exact Matrix.PosSemidef.diagonal fun i => by
      simp
  trace_eq_one := by
    rw [Matrix.trace]
    simp only [Matrix.diag, Matrix.diagonal_apply_eq]
    simpa using congrArg (fun r : ℝ≥0 => (r : ℂ)) hsum

/-- The diagonal-state matrix is the diagonal matrix of probabilities. -/
@[simp]
theorem diagonalState_matrix (p : ι → ℝ≥0) (hsum : ∑ i, p i = 1) :
    (diagonalState p hsum).matrix = Matrix.diagonal fun i => (p i : ℂ) := by
  rfl

/-- The diagonal entry of a classical diagonal state is its probability. -/
@[simp]
theorem diagonalState_apply_self (p : ι → ℝ≥0) (hsum : ∑ i, p i = 1) (i : ι) :
    (diagonalState p hsum).matrix i i = (p i : ℂ) := by
  simp [diagonalState]

/-- Off-diagonal entries of a classical diagonal state vanish. -/
@[simp]
theorem diagonalState_apply_ne (p : ι → ℝ≥0) (hsum : ∑ i, p i = 1) {i j : ι}
    (h : i ≠ j) :
    (diagonalState p hsum).matrix i j = 0 := by
  simp [diagonalState, Matrix.diagonal_apply_ne _ h]

/-- The pure classical basis state supported on one label. -/
def basisState (x : ι) : State ι where
  matrix := Matrix.single x x (1 : ℂ)
  pos := posSemidef_single x
  trace_eq_one := by
    rw [trace_single_one, if_pos rfl]

@[simp]
theorem basisState_matrix (x : ι) :
    (basisState x).matrix = Matrix.single x x (1 : ℂ) :=
  rfl

@[simp]
theorem basisState_prod_matrix_apply
    {a : Type v} [Fintype a] [DecidableEq a]
    (x y y' : ι) (σ : State a) (i j : a) :
    ((basisState x).prod σ).matrix (y, i) (y', j) =
      Matrix.single x x (1 : ℂ) y y' * σ.matrix i j := by
  rfl

variable [Fintype a] [DecidableEq a]

omit [DecidableEq ι] [Fintype a] [DecidableEq a] in
/-- Tracing out the left classical register is the sum of the diagonal
classical blocks. -/
theorem partialTraceA_eq_sum_blocks (X : CMatrix (Prod ι a)) :
    partialTraceA X = ∑ x : ι, block X x x := by
  ext i j
  simp [partialTraceA, block, Matrix.sum_apply]

omit [Fintype ι] [DecidableEq ι] [Fintype a] [DecidableEq a] in
/-- Taking a diagonal classical block preserves Loewner order. -/
theorem block_le_block_of_le {X Y : CMatrix (Prod ι a)} (h : X ≤ Y) (x : ι) :
    block X x x ≤ block Y x x := by
  rw [Matrix.le_iff] at h ⊢
  have hblock := h.submatrix (fun i : a => (x, i))
  convert hblock using 1

omit [DecidableEq ι] [DecidableEq a] in
/-- Partial trace over the left classical register preserves Loewner order. -/
theorem partialTraceA_mono {X Y : CMatrix (Prod ι a)} (h : X ≤ Y) :
    partialTraceA X ≤ partialTraceA Y := by
  rw [Matrix.le_iff] at h ⊢
  have hdiff := partialTraceA_posSemidef (a := ι) (b := a) h
  convert hdiff using 1
  ext i j
  simp [partialTraceA, Matrix.sub_apply, Finset.sum_sub_distrib]

/-- The classical marginal of a cq-state is the diagonal state of ensemble weights. -/
theorem partialTraceB_cqState_eq_diagonalState (E : Ensemble ι a) :
    partialTraceB E.cqState.matrix = (diagonalState E.probs E.weights_sum).matrix := by
  simpa [diagonalState] using partialTraceB_cqState E

variable {y : Type u}
variable [Fintype y] [DecidableEq y]

/-- The classical state associated to a POVM measurement output. -/
def measuredState (M : POVM y a) (rho : State a) : State y :=
  diagonalState (fun outcome => M.prob rho outcome) (M.sum_prob rho)

/-- A complex number with zero imaginary part is its real part embedded in `ℂ`. -/
private theorem ofReal_re_eq_of_im_eq_zero {z : ℂ} (h : z.im = 0) :
    ((Complex.re z : ℝ) : ℂ) = z := by
  apply Complex.ext <;> simp [h]

/-- Measured-state diagonal entries are the POVM outcome probabilities. -/
@[simp]
theorem measuredState_apply_self (M : POVM y a) (rho : State a) (outcome : y) :
    (measuredState M rho).matrix outcome outcome = (M.prob rho outcome : ℂ) := by
  simp [measuredState]

/-- Off-diagonal entries of measured classical states vanish. -/
@[simp]
theorem measuredState_apply_ne (M : POVM y a) (rho : State a) {outcome outcome' : y}
    (h : outcome ≠ outcome') :
    (measuredState M rho).matrix outcome outcome' = 0 := by
  simp [measuredState, diagonalState_apply_ne _ _ h]

/-- The local measured-state view agrees with the measurement channel output. -/
theorem measuredState_eq_measure_applyState (M : POVM y a) (rho : State a) :
    measuredState M rho = (Channel.measure M).applyState rho := by
  apply State.ext
  ext outcome outcome₂
  by_cases h : outcome = outcome₂
  · subst outcome₂
    rw [measuredState_apply_self]
    unfold POVM.prob
    simp only
    let sigma := (Channel.measure M).applyState rho
    change ((⟨Complex.re (sigma.matrix outcome outcome),
      (Complex.nonneg_iff.mp (sigma.pos.diag_nonneg (i := outcome))).1⟩ : ℝ≥0) : ℂ) =
        sigma.matrix outcome outcome
    exact ofReal_re_eq_of_im_eq_zero
      (Complex.nonneg_iff.mp (sigma.pos.diag_nonneg (i := outcome))).2.symm
  · rw [measuredState_apply_ne M rho h]
    change 0 = (Channel.measure M).map rho.matrix outcome outcome₂
    rw [Channel.measure_map_state_diagonal]
    exact (Matrix.diagonal_apply_ne _ h).symm

end

end Classical
end QIT
