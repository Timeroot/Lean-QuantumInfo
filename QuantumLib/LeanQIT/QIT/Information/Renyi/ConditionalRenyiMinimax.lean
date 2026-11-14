/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.ConditionalRenyiTraceBridge
public import QIT.Information.Renyi.FrankLieb.ScalarOperator
public import QIT.States.TraceNorm.Spectral
public import QIT.States.PosSqrtOrder
public import QIT.Classical.Bridge
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder
public import Mathlib.Topology.Sion

/-!
# Sion minimax bridge for conditional Renyi trace functionals

This module isolates the minimax exchange needed in Tomamichel's upward
sandwiched conditional Renyi duality proof.

Source alignment:
* Tomamichel2015FiniteResources, `cond.tex`, Proposition `pr:dual-new`,
  proof lines 390-396 reduces the last step to interchanging a minimum over
  side states and a maximum over side states.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:1128-1165] gives the
  sandwiched mutual-information alternate-expression route whose proof invokes
  the same Sion minimax pattern.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal

namespace QIT

universe u v w

noncomputable section

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]

noncomputable local instance instCMatrixCStarAlgebraForConditionalMinimax (n : Type u)
    [Fintype n] [DecidableEq n] : CStarAlgebra (CMatrix n) := {}

/-- Matrix-level density-state domain used as the compact convex optimization
set in the conditional Renyi minimax route. -/
def densityMatrixSet (a : Type u) [Fintype a] : Set (CMatrix a) :=
  {M | M.PosSemidef ∧ M.trace = 1}

/-- Full-rank normalized density matrices.  This is the side-state domain used
by the current conditional-Renyi candidate API; it embeds into the compact
closed density domain, but is not itself the compact Sion domain because the
positive-definite condition is open. -/
def fullRankDensityMatrixSet (a : Type u) [Fintype a] : Set (CMatrix a) :=
  {M | M.PosDef ∧ M.trace = 1}

/-- Density matrices whose spectrum is uniformly bounded below by `delta`.

This is the compact full-support side-state domain used to make the negative
power `sigma^{-p}` analytic hypotheses source-faithful.  Tomamichel's proof
first restricts the `sigma_B` optimization to such a compact set before
invoking Sion. -/
def uniformlyPositiveDensityMatrixSet (delta : ℝ) (a : Type u)
    [Fintype a] [DecidableEq a] : Set (CMatrix a) :=
  {M | M ∈ densityMatrixSet a ∧ delta • (1 : CMatrix a) ≤ M}

omit [DecidableEq a] in
theorem mem_densityMatrixSet_iff {M : CMatrix a} :
    M ∈ densityMatrixSet a ↔ M.PosSemidef ∧ M.trace = 1 := by
  rfl

omit [DecidableEq a] in
theorem mem_fullRankDensityMatrixSet_iff {M : CMatrix a} :
    M ∈ fullRankDensityMatrixSet a ↔ M.PosDef ∧ M.trace = 1 := by
  rfl

theorem mem_uniformlyPositiveDensityMatrixSet_iff {delta : ℝ} {M : CMatrix a} :
    M ∈ uniformlyPositiveDensityMatrixSet delta a ↔
      M ∈ densityMatrixSet a ∧ delta • (1 : CMatrix a) ≤ M := by
  rfl

omit [DecidableEq a] in
/-- Full-rank density matrices are density matrices. -/
theorem fullRankDensityMatrixSet_subset_densityMatrixSet :
    fullRankDensityMatrixSet a ⊆ densityMatrixSet a := by
  intro M hM
  exact ⟨hM.1.posSemidef, hM.2⟩

/-- The uniformly positive density domain lies in the closed density domain. -/
theorem uniformlyPositiveDensityMatrixSet_subset_densityMatrixSet {delta : ℝ} :
    uniformlyPositiveDensityMatrixSet delta a ⊆ densityMatrixSet a := by
  intro M hM
  exact hM.1

omit [Fintype a] in
/-- A positive real scalar multiple of the identity is positive definite. -/
theorem cMatrix_real_smul_one_posDef_forConditionalMinimax {r : ℝ} (hr : 0 < r) :
    (r • (1 : CMatrix a)).PosDef := by
  rw [show r • (1 : CMatrix a) = Matrix.diagonal (fun _ : a => (r : ℂ)) by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]]
  rw [Matrix.posDef_diagonal_iff]
  intro i
  exact_mod_cast hr

/-- A positive lower spectral bound turns a uniformly positive density matrix
into a positive-definite matrix. -/
theorem uniformlyPositiveDensityMatrixSet_subset_posDef {delta : ℝ} (hdelta : 0 < delta) :
    uniformlyPositiveDensityMatrixSet delta a ⊆
      ({M : CMatrix a | M.PosDef} : Set (CMatrix a)) := by
  intro M hM
  have hstrict_left : IsStrictlyPositive (delta • (1 : CMatrix a)) :=
    (cMatrix_real_smul_one_posDef_forConditionalMinimax (a := a) hdelta).isStrictlyPositive
  exact Matrix.isStrictlyPositive_iff_posDef.mp (IsStrictlyPositive.of_le hstrict_left hM.2)

/-- Every normalized `State` matrix lies in the matrix-level density domain. -/
theorem state_matrix_mem_densityMatrixSet (ρ : State a) :
    ρ.matrix ∈ densityMatrixSet a := by
  exact ⟨ρ.pos, ρ.trace_eq_one⟩

/-- Repackage a matrix-level density operator as a normalized `State`.

This is proof-irrelevant in the density-membership witness and lets the Sion
statement work over compact matrix domains while the surrounding conditional
Renyi API continues to use `State`. -/
def densityMatrixSetState (M : CMatrix a) (hM : M ∈ densityMatrixSet a) : State a where
  matrix := M
  pos := hM.1
  trace_eq_one := hM.2

@[simp]
theorem densityMatrixSetState_matrix (M : CMatrix a) (hM : M ∈ densityMatrixSet a) :
    (densityMatrixSetState M hM).matrix = M :=
  rfl

/-- The matrix-level density-state domain is nonempty for a nonempty finite
index type. -/
theorem densityMatrixSet_nonempty [Nonempty a] :
    (densityMatrixSet a).Nonempty := by
  classical
  let p : a → ℝ≥0 := fun _ => (Fintype.card a : ℝ≥0)⁻¹
  have hsum : ∑ i, p i = 1 := by
    simp [p, Finset.sum_const, nsmul_eq_mul, Fintype.card_ne_zero]
  exact ⟨(Classical.diagonalState p hsum).matrix,
    state_matrix_mem_densityMatrixSet (Classical.diagonalState p hsum)⟩

/-- The full-rank density-state domain is nonempty for a nonempty finite index
type. -/
theorem fullRankDensityMatrixSet_nonempty [Nonempty a] :
    (fullRankDensityMatrixSet a).Nonempty := by
  classical
  let p : a → ℝ≥0 := fun _ => (Fintype.card a : ℝ≥0)⁻¹
  have hsum : ∑ i, p i = 1 := by
    simp [p, Finset.sum_const, nsmul_eq_mul, Fintype.card_ne_zero]
  have hpos : ∀ i, 0 < (p i : ℝ) := by
    intro i
    have hcard_pos : 0 < (Fintype.card a : ℝ≥0) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i⟩)
    exact_mod_cast inv_pos.mpr hcard_pos
  refine ⟨(Classical.diagonalState p hsum).matrix, ?_⟩
  exact
    ⟨Classical.diagonalState_posDef p hsum hpos,
      (Classical.diagonalState p hsum).trace_eq_one⟩

/-- The uniformly positive density-state domain is nonempty whenever the lower
bound is no larger than the maximally mixed eigenvalue. -/
theorem uniformlyPositiveDensityMatrixSet_nonempty [Nonempty a] {delta : ℝ}
    (hdelta : delta ≤ (Fintype.card a : ℝ)⁻¹) :
    (uniformlyPositiveDensityMatrixSet delta a).Nonempty := by
  refine ⟨(maximallyMixed a).matrix, state_matrix_mem_densityMatrixSet (maximallyMixed a), ?_⟩
  rw [maximallyMixed_matrix]
  rw [Matrix.le_iff]
  have hdiff :
      (((((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) • (1 : CMatrix a)) -
          delta • (1 : CMatrix a)) =
        (((Fintype.card a : ℝ)⁻¹ - delta) : ℝ) • (1 : CMatrix a) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Complex.real_smul]
    · simp [hij]
  rw [hdiff]
  exact Matrix.PosSemidef.smul Matrix.PosSemidef.one (sub_nonneg.mpr hdelta)

omit [DecidableEq a] in
/-- The matrix-level density-state domain is convex. -/
theorem densityMatrixSet_convex :
    Convex ℝ (densityMatrixSet a) := by
  intro x hx y hy s t hs ht hst
  rcases hx with ⟨hxpos, hxtr⟩
  rcases hy with ⟨hypos, hytr⟩
  constructor
  · exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hxpos hs)
      (Matrix.PosSemidef.smul hypos ht)
  · rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hxtr, hytr]
    norm_num [Complex.real_smul, ← Complex.ofReal_add, hst]

/-- The uniformly positive density-state domain is convex. -/
theorem uniformlyPositiveDensityMatrixSet_convex {delta : ℝ} :
    Convex ℝ (uniformlyPositiveDensityMatrixSet delta a) := by
  intro x hx y hy s t hs ht hst
  constructor
  · exact densityMatrixSet_convex hx.1 hy.1 hs ht hst
  · calc
      delta • (1 : CMatrix a) =
          s • (delta • (1 : CMatrix a)) + t • (delta • (1 : CMatrix a)) := by
        rw [← add_smul, hst, one_smul]
      _ ≤ s • x + t • y := by
        exact add_le_add
          (smul_le_smul_of_nonneg_left hx.2 hs)
          (smul_le_smul_of_nonneg_left hy.2 ht)

omit [DecidableEq a] in
/-- The full-rank density-state domain is convex.  This is useful for linking
the current full-rank conditional-Renyi candidate API to the closed density
domain used by Sion. -/
theorem fullRankDensityMatrixSet_convex :
    Convex ℝ (fullRankDensityMatrixSet a) := by
  intro x hx y hy s t hs ht hst
  rcases hx with ⟨hxpos, hxtr⟩
  rcases hy with ⟨hypos, hytr⟩
  constructor
  · have hs1 : s ≤ 1 := by linarith
    have ht_eq : t = 1 - s := by linarith
    have hpos : (s • x + (1 - s) • y).PosDef :=
      Matrix.PosDef.convexCombination hxpos hypos hs hs1
    simpa [ht_eq] using hpos
  · rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hxtr, hytr]
    norm_num [Complex.real_smul, ← Complex.ofReal_add, hst]

/-- The matrix-level density-state domain is closed. -/
theorem densityMatrixSet_isClosed :
    IsClosed (densityMatrixSet a) := by
  have htrace :
      IsClosed ({M : CMatrix a | M.trace = 1} : Set (CMatrix a)) :=
    isClosed_eq (Continuous.matrix_trace continuous_id) continuous_const
  have hset :
      densityMatrixSet a =
        ({M : CMatrix a | M.PosSemidef} ∩ {M : CMatrix a | M.trace = 1}) := by
    ext M
    rfl
  rw [hset]
  exact (isClosed_cMatrix_posSemidef (ι := a)).inter htrace

/-- The matrix-level density-state domain is bounded. -/
theorem densityMatrixSet_isBounded :
    Bornology.IsBounded (densityMatrixSet a) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨‖(1 : CMatrix a)‖, ?_⟩
  intro M hM
  rcases hM with ⟨hMpsd, hMtr⟩
  have hnorm := norm_le_trace_re_mul_norm_one_of_posSemidef (a := a) hMpsd
  have htrace_re : M.trace.re = 1 := by
    rw [hMtr]
    norm_num
  simpa [htrace_re] using hnorm

/-- The matrix-level density-state domain is compact. -/
theorem densityMatrixSet_isCompact :
    IsCompact (densityMatrixSet a) :=
  Metric.isCompact_of_isClosed_isBounded densityMatrixSet_isClosed densityMatrixSet_isBounded

/-- The lower spectral bound condition is closed. -/
theorem uniformlyPositiveDensityMatrixSet_lowerBound_isClosed {delta : ℝ} :
    IsClosed ({M : CMatrix a | delta • (1 : CMatrix a) ≤ M} : Set (CMatrix a)) := by
  have hclosed :
      IsClosed ({M : CMatrix a | (M - delta • (1 : CMatrix a)).PosSemidef} :
        Set (CMatrix a)) := by
    exact (isClosed_cMatrix_posSemidef (ι := a)).preimage (continuous_id.sub continuous_const)
  simpa [Matrix.le_iff] using hclosed

/-- The uniformly positive density-state domain is closed. -/
theorem uniformlyPositiveDensityMatrixSet_isClosed {delta : ℝ} :
    IsClosed (uniformlyPositiveDensityMatrixSet delta a) := by
  have hset :
      uniformlyPositiveDensityMatrixSet delta a =
        densityMatrixSet a ∩
          ({M : CMatrix a | delta • (1 : CMatrix a) ≤ M} : Set (CMatrix a)) := by
    ext M
    rfl
  rw [hset]
  exact densityMatrixSet_isClosed.inter uniformlyPositiveDensityMatrixSet_lowerBound_isClosed

/-- The uniformly positive density-state domain is compact. -/
theorem uniformlyPositiveDensityMatrixSet_isCompact {delta : ℝ} :
    IsCompact (uniformlyPositiveDensityMatrixSet delta a) := by
  have hset :
      uniformlyPositiveDensityMatrixSet delta a =
        densityMatrixSet a ∩
          ({M : CMatrix a | delta • (1 : CMatrix a) ≤ M} : Set (CMatrix a)) := by
    ext M
    rfl
  rw [hset]
  exact densityMatrixSet_isCompact.inter_right uniformlyPositiveDensityMatrixSet_lowerBound_isClosed

variable {b : Type v} {c : Type w}
variable [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]

/-- The real source bracket
`⟨ρ| σ_B^{-α'} ⊗ τ_C^{α'} |ρ⟩`, read on matrix-level density domains.

Outside the density domains the value is set to zero only to obtain a total
function. All minimax theorems below restrict the arguments to
`densityMatrixSet`, where the `if` branches reduce to the source expression. -/
def upwardRenyiDualityBracketRe
    (ψ : PureVector (Prod (Prod a b) c))
    (σ : CMatrix b) (τ : CMatrix c) (alphaPrime : ℝ) : ℝ := by
  classical
  exact
    if hσ : σ ∈ densityMatrixSet b then
      if hτ : τ ∈ densityMatrixSet c then
        (PureVector.upwardRenyiDualityCommonBracket ψ
          (densityMatrixSetState σ hσ) (densityMatrixSetState τ hτ) alphaPrime).re
      else 0
    else 0

@[simp]
theorem upwardRenyiDualityBracketRe_of_mem
    (ψ : PureVector (Prod (Prod a b) c))
    {σ : CMatrix b} (hσ : σ ∈ densityMatrixSet b)
    {τ : CMatrix c} (hτ : τ ∈ densityMatrixSet c)
    (alphaPrime : ℝ) :
    upwardRenyiDualityBracketRe (a := a) ψ σ τ alphaPrime =
      (PureVector.upwardRenyiDualityCommonBracket ψ
        (densityMatrixSetState σ hσ) (densityMatrixSetState τ hτ) alphaPrime).re := by
  simp [upwardRenyiDualityBracketRe, hσ, hτ]

/-- Extended-real lift of the source bracket, matching mathlib's Sion API. -/
def upwardRenyiDualityBracketEReal
    (ψ : PureVector (Prod (Prod a b) c))
    (σ : CMatrix b) (τ : CMatrix c) (alphaPrime : ℝ) : EReal :=
  upwardRenyiDualityBracketRe (a := a) ψ σ τ alphaPrime

/-- Raw matrix form of the source bracket
`Tr[(I_A ⊗ σ_B^{-p} ⊗ τ_C^p) R]`.

This avoids repackaging side matrices as normalized `State`s while proving the
analytic Sion hypotheses.  On density matrices and `R = |ψ⟩⟨ψ|` it coincides
with `upwardRenyiDualityBracketRe`. -/
def abcSidePowerTraceRe
    (R : CMatrix (Prod (Prod a b) c))
    (σ : CMatrix b) (τ : CMatrix c) (p : ℝ) : ℝ :=
  ((Matrix.kronecker
      (Matrix.kronecker (1 : CMatrix a) (CFC.rpow σ (-p)))
      (CFC.rpow τ p) * R).trace).re

theorem upwardRenyiDualityBracketRe_eq_abcSidePowerTraceRe
    (ψ : PureVector (Prod (Prod a b) c))
    {σ : CMatrix b} (hσ : σ ∈ densityMatrixSet b)
    {τ : CMatrix c} (hτ : τ ∈ densityMatrixSet c)
    (alphaPrime : ℝ) :
    upwardRenyiDualityBracketRe (a := a) ψ σ τ alphaPrime =
      abcSidePowerTraceRe (a := a) ψ.state.matrix σ τ alphaPrime := by
  rw [upwardRenyiDualityBracketRe_of_mem (a := a) ψ hσ hτ alphaPrime]
  rfl

omit [DecidableEq a] [DecidableEq b] [DecidableEq c] in
private theorem trace_kronecker_right_add_smul_add_smul_re
    (K : CMatrix (Prod a b)) (R : CMatrix (Prod (Prod a b) c))
    (T U V : CMatrix c) (s t : ℝ) :
    ((Matrix.kronecker K (T + (s • U + t • V)) * R).trace).re =
      ((Matrix.kronecker K T * R).trace).re +
        (s * ((Matrix.kronecker K U * R).trace).re +
          t * ((Matrix.kronecker K V * R).trace).re) := by
  unfold Matrix.kronecker
  rw [Matrix.kronecker_add K T (s • U + t • V)]
  rw [Matrix.kronecker_add K (s • U) (t • V)]
  rw [Matrix.kronecker_smul s K U, Matrix.kronecker_smul t K V]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, Complex.add_re,
    Complex.smul_re, smul_eq_mul]

omit [DecidableEq b] [DecidableEq c] in
private theorem trace_kronecker_middle_add_smul_add_smul_re
    (R : CMatrix (Prod (Prod a b) c)) (K : CMatrix c)
    (T U V : CMatrix b) (s t : ℝ) :
    ((Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) (T + (s • U + t • V))) K *
          R).trace).re =
      ((Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) T) K * R).trace).re +
        (s * ((Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) U) K * R).trace).re +
          t * ((Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) V) K * R).trace).re) := by
  unfold Matrix.kronecker
  rw [Matrix.kroneckerMap_add_right (fun x y : ℂ => x * y)
    (by intro x y z; exact mul_add x y z) (1 : CMatrix a) T (s • U + t • V)]
  rw [Matrix.kroneckerMap_add_left (fun x y : ℂ => x * y)
    (by intro x y z; exact add_mul x y z)
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : CMatrix a) T)
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : CMatrix a) (s • U + t • V))
    K]
  rw [Matrix.kroneckerMap_add_right (fun x y : ℂ => x * y)
    (by intro x y z; exact mul_add x y z) (1 : CMatrix a) (s • U) (t • V)]
  rw [Matrix.kroneckerMap_add_left (fun x y : ℂ => x * y)
    (by intro x y z; exact add_mul x y z)
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : CMatrix a) (s • U))
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : CMatrix a) (t • V))
    K]
  rw [Matrix.kroneckerMap_smul_right (fun x y : ℂ => x * y) s
    (by intro x y; exact mul_smul_comm s x y) (1 : CMatrix a) U]
  rw [Matrix.kroneckerMap_smul_right (fun x y : ℂ => x * y) t
    (by intro x y; exact mul_smul_comm t x y) (1 : CMatrix a) V]
  rw [Matrix.kroneckerMap_smul_left (fun x y : ℂ => x * y) s
    (by intro x y; exact smul_mul_assoc s x y)
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : CMatrix a) U) K]
  rw [Matrix.kroneckerMap_smul_left (fun x y : ℂ => x * y) t
    (by intro x y; exact smul_mul_assoc t x y)
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : CMatrix a) V) K]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.smul_re, smul_eq_mul]

omit [DecidableEq a] [DecidableEq b] [DecidableEq c] in
private theorem trace_kronecker_right_continuous
    (K : CMatrix (Prod a b)) (R : CMatrix (Prod (Prod a b) c)) :
    Continuous fun T : CMatrix c => ((Matrix.kronecker K T * R).trace).re := by
  have hkr :
      Continuous fun T : CMatrix c => Matrix.kronecker K T := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply] using
        continuous_const.mul (continuous_id.matrix_elem x.2 y.2)
  exact Complex.continuous_re.comp
    (Continuous.matrix_trace (hkr.matrix_mul continuous_const))

omit [DecidableEq b] [DecidableEq c] in
private theorem trace_kronecker_middle_continuous
    (R : CMatrix (Prod (Prod a b) c)) (K : CMatrix c) :
    Continuous fun T : CMatrix b =>
      ((Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) T) K * R).trace).re := by
  have hinner :
      Continuous fun T : CMatrix b => Matrix.kronecker (1 : CMatrix a) T := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply] using
        continuous_const.mul (continuous_id.matrix_elem x.2 y.2)
  have hkr :
      Continuous fun T : CMatrix b => Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) T) K := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply] using
        ((hinner.matrix_elem x.1 y.1).mul continuous_const)
  exact Complex.continuous_re.comp
    (Continuous.matrix_trace (hkr.matrix_mul continuous_const))

/-- Source side condition `0 < α' < 1` gives the positive-power range for
`τ_C^{α'}`. -/
theorem alphaPrime_mem_Icc_zero_one {alphaPrime : ℝ}
    (hα : 0 < alphaPrime ∧ alphaPrime < 1) :
    alphaPrime ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_of_lt hα.1, le_of_lt hα.2⟩

/-- Source side condition `0 < α' < 1` gives the negative-power range for
`σ_B^{-α'}`.  This is the precise operator-convexity range used by
`cMatrix_rpow_convexOn_posDef_of_mem_Icc_neg_one_zero`. -/
theorem neg_alphaPrime_mem_Icc_neg_one_zero {alphaPrime : ℝ}
    (hα : 0 < alphaPrime ∧ alphaPrime < 1) :
    -alphaPrime ∈ Set.Icc (-1 : ℝ) 0 := by
  constructor <;> linarith

omit [DecidableEq a] in
/-- The positive-definite cone is convex. -/
theorem posDefMatrixSet_convex :
    Convex ℝ ({M : CMatrix a | M.PosDef} : Set (CMatrix a)) := by
  intro x hx y hy s t hs ht hst
  have hs1 : s ≤ 1 := by linarith
  have ht_eq : t = 1 - s := by linarith
  have hpos : (s • x + (1 - s) • y).PosDef :=
    Matrix.PosDef.convexCombination hx hy hs hs1
  simpa [ht_eq] using hpos

/-- Real matrix powers are continuous on the positive-definite cone for every
real exponent. -/
theorem cMatrix_rpow_continuousOn_posDef (p : ℝ) :
    ContinuousOn (fun M : CMatrix a => CFC.rpow M p)
      ({M : CMatrix a | M.PosDef} : Set (CMatrix a)) := by
  change ContinuousOn (fun M : CMatrix a => M ^ p)
    ({M : CMatrix a | M.PosDef} : Set (CMatrix a))
  exact (CFC.continuousOn_rpow (A := CMatrix a) p).mono fun M hM =>
    Matrix.PosDef.isStrictlyPositive hM

/-- Negative-power operator convexity on positive-definite matrices.

This is the finite-dimensional `CMatrix` form needed for the
`σ_B^{-α'}` side of the Sion minimax bracket.  The domain is the positive
definite cone: extending this statement to the closed PSD cone would be false
for mathlib's total `rpow` at zero. -/
theorem cMatrix_rpow_convexOn_posDef_of_mem_Icc_neg_one_zero
    {p : ℝ} (hp : p ∈ Set.Icc (-1 : ℝ) 0) :
    ConvexOn ℝ ({M : CMatrix a | M.PosDef} : Set (CMatrix a))
      (fun M : CMatrix a => CFC.rpow M p) := by
  let q : ℝ := -p
  have hq0 : 0 ≤ q := by
    dsimp [q]
    linarith [hp.2]
  have hq1 : q ≤ 1 := by
    dsimp [q]
    linarith [hp.1]
  have hp_eq : p = -q := by
    dsimp [q]
    ring
  constructor
  · exact posDefMatrixSet_convex (a := a)
  · intro x hx y hy s t hs ht hst
    by_cases hq_zero : q = 0
    · have hp_zero : p = 0 := by
        rw [hp_eq, hq_zero]
        norm_num
      have hright :
          s • (1 : CMatrix a) + t • (1 : CMatrix a) = (1 : CMatrix a) := by
        rw [← add_smul, hst, one_smul]
      have hcombo_pos : (s • x + t • y).PosSemidef :=
        ((posDefMatrixSet_convex (a := a)) hx hy hs ht hst).posSemidef
      rw [hp_zero]
      change (s • x + t • y) ^ (0 : ℝ) ≤
        s • (x ^ (0 : ℝ)) + t • (y ^ (0 : ℝ))
      rw [CFC.rpow_zero x (ha := Matrix.nonneg_iff_posSemidef.mpr hx.posSemidef),
        CFC.rpow_zero y (ha := Matrix.nonneg_iff_posSemidef.mpr hy.posSemidef),
        CFC.rpow_zero (s • x + t • y)
          (ha := Matrix.nonneg_iff_posSemidef.mpr hcombo_pos),
        hright]
    · have hq_mem : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq0, hq1⟩
      have hx_psd : x ∈ Set.Ici (0 : CMatrix a) :=
        Matrix.nonneg_iff_posSemidef.mpr hx.posSemidef
      have hy_psd : y ∈ Set.Ici (0 : CMatrix a) :=
        Matrix.nonneg_iff_posSemidef.mpr hy.posSemidef
      have hpow :=
        (CFC.concaveOn_rpow (A := CMatrix a) hq_mem).2 hx_psd hy_psd hs ht hst
      have hcombo_pos : (s • x + t • y).PosDef :=
        (posDefMatrixSet_convex (a := a)) hx hy hs ht hst
      have hx_strict : IsStrictlyPositive x := Matrix.PosDef.isStrictlyPositive hx
      have hy_strict : IsStrictlyPositive y := Matrix.PosDef.isStrictlyPositive hy
      have hcombo_strict : IsStrictlyPositive (s • x + t • y) :=
        Matrix.PosDef.isStrictlyPositive hcombo_pos
      have hxq_strict : IsStrictlyPositive (CFC.rpow x q) := by
        exact IsStrictlyPositive.rpow x q hx_strict
      have hyq_strict : IsStrictlyPositive (CFC.rpow y q) := by
        exact IsStrictlyPositive.rpow y q hy_strict
      have hcomboq_strict : IsStrictlyPositive (CFC.rpow (s • x + t • y) q) := by
        exact IsStrictlyPositive.rpow (s • x + t • y) q hcombo_strict
      have hInvConv := CStarAlgebra.convexOn_ringInverse (A := CMatrix a)
      have hweighted_q_strict :
          IsStrictlyPositive (s • CFC.rpow x q + t • CFC.rpow y q) :=
        hInvConv.1 hxq_strict hyq_strict hs ht hst
      have hanti :
          Ring.inverse (CFC.rpow (s • x + t • y) q) ≤
            Ring.inverse (s • CFC.rpow x q + t • CFC.rpow y q) :=
        CStarAlgebra.antitoneOn_ringInverse hweighted_q_strict hcomboq_strict hpow
      have hinv_conv :
          Ring.inverse (s • CFC.rpow x q + t • CFC.rpow y q) ≤
            s • Ring.inverse (CFC.rpow x q) + t • Ring.inverse (CFC.rpow y q) :=
        hInvConv.2 hxq_strict hyq_strict hs ht hst
      have hcombo_inv :
          Ring.inverse (CFC.rpow (s • x + t • y) q) =
            CFC.rpow (s • x + t • y) (-q) :=
        CFC.inverse_rpow (s • x + t • y) q hq_zero hcombo_strict
      have hx_inv :
          Ring.inverse (CFC.rpow x q) = CFC.rpow x (-q) :=
        CFC.inverse_rpow x q hq_zero hx_strict
      have hy_inv :
          Ring.inverse (CFC.rpow y q) = CFC.rpow y (-q) :=
        CFC.inverse_rpow y q hq_zero hy_strict
      have hmain :
          CFC.rpow (s • x + t • y) (-q) ≤
            s • CFC.rpow x (-q) + t • CFC.rpow y (-q) := by
        calc
          CFC.rpow (s • x + t • y) (-q)
              = Ring.inverse (CFC.rpow (s • x + t • y) q) := hcombo_inv.symm
          _ ≤ Ring.inverse (s • CFC.rpow x q + t • CFC.rpow y q) := hanti
          _ ≤ s • Ring.inverse (CFC.rpow x q) + t • Ring.inverse (CFC.rpow y q) :=
            hinv_conv
          _ = s • CFC.rpow x (-q) + t • CFC.rpow y (-q) := by
            rw [hx_inv, hy_inv]
      simpa [hp_eq] using hmain

/-- Endpoint negative-power operator convexity on positive-definite matrices.

This is the `p = -1` specialization of the full `[-1, 0]` negative-power
operator-convexity theorem. -/
theorem cMatrix_rpow_neg_one_convexOn_posDef :
    ConvexOn ℝ ({M : CMatrix a | M.PosDef} : Set (CMatrix a))
      (fun M : CMatrix a => CFC.rpow M (-1 : ℝ)) := by
  exact cMatrix_rpow_convexOn_posDef_of_mem_Icc_neg_one_zero (a := a) (by norm_num)

/-- Pairing negative matrix powers with a fixed PSD weight preserves convexity
on the positive-definite cone. -/
theorem cMatrix_trace_mul_rpow_convexOn_posDef_of_mem_Icc_neg_one_zero
    {W : CMatrix a} (hW : W.PosSemidef) {p : ℝ} (hp : p ∈ Set.Icc (-1 : ℝ) 0) :
    ConvexOn ℝ ({M : CMatrix a | M.PosDef} : Set (CMatrix a))
      (fun M : CMatrix a => ((W * CFC.rpow M p).trace).re) := by
  constructor
  · exact posDefMatrixSet_convex (a := a)
  · intro x hx y hy s t hs ht hst
    have hpow :=
      (cMatrix_rpow_convexOn_posDef_of_mem_Icc_neg_one_zero (a := a) hp).2
        hx hy hs ht hst
    have hdiff_nonneg :
        0 ≤ (s • CFC.rpow x p + t • CFC.rpow y p) -
          CFC.rpow (s • x + t • y) p := by
      exact sub_nonneg.mpr hpow
    have hdiff_psd :
        ((s • CFC.rpow x p + t • CFC.rpow y p) -
          CFC.rpow (s • x + t • y) p).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp hdiff_nonneg
    have htrace := cMatrix_trace_mul_posSemidef_re_nonneg hW hdiff_psd
    have hlinear :
        ((W * ((s • CFC.rpow x p + t • CFC.rpow y p) -
          CFC.rpow (s • x + t • y) p)).trace).re =
          (s * ((W * CFC.rpow x p).trace).re +
            t * ((W * CFC.rpow y p).trace).re) -
            ((W * CFC.rpow (s • x + t • y) p).trace).re := by
      simp [Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul, Complex.real_smul,
        sub_eq_add_neg]
    rw [hlinear] at htrace
    have hle :
        ((W * CFC.rpow (s • x + t • y) p).trace).re ≤
          s * ((W * CFC.rpow x p).trace).re +
            t * ((W * CFC.rpow y p).trace).re := by
      nlinarith
    simpa [smul_eq_mul] using hle

/-- Trace-pairing quasiconvexity corollary for negative matrix powers. -/
theorem cMatrix_trace_mul_rpow_quasiconvexOn_posDef_of_mem_Icc_neg_one_zero
    {W : CMatrix a} (hW : W.PosSemidef) {p : ℝ} (hp : p ∈ Set.Icc (-1 : ℝ) 0) :
    QuasiconvexOn ℝ ({M : CMatrix a | M.PosDef} : Set (CMatrix a))
      (fun M : CMatrix a => ((W * CFC.rpow M p).trace).re) :=
  (cMatrix_trace_mul_rpow_convexOn_posDef_of_mem_Icc_neg_one_zero
    (a := a) hW hp).quasiconvexOn

/-- Trace-pairing form of real-power continuity on the positive-definite cone. -/
theorem cMatrix_trace_mul_rpow_continuousOn_posDef
    (W : CMatrix a) (p : ℝ) :
    ContinuousOn
      (fun M : CMatrix a => ((W * CFC.rpow M p).trace).re)
      ({M : CMatrix a | M.PosDef} : Set (CMatrix a)) := by
  have hpow := cMatrix_rpow_continuousOn_posDef (a := a) p
  have htrace : Continuous fun M : CMatrix a => ((W * M).trace).re := by
    exact Complex.continuous_re.comp
      (Continuous.matrix_trace (continuous_const.mul continuous_id))
  simpa [Function.comp_def] using htrace.comp_continuousOn hpow

/-- Lower semicontinuity corollary for trace-pairing real powers on the
positive-definite cone. -/
theorem cMatrix_trace_mul_rpow_lowerSemicontinuousOn_posDef
    (W : CMatrix a) (p : ℝ) :
    LowerSemicontinuousOn
      (fun M : CMatrix a => ((W * CFC.rpow M p).trace).re)
      ({M : CMatrix a | M.PosDef} : Set (CMatrix a)) :=
  ContinuousOn.lowerSemicontinuousOn
    (cMatrix_trace_mul_rpow_continuousOn_posDef (a := a) W p)

/-- Upper semicontinuity corollary for trace-pairing real powers on the
positive-definite cone. -/
theorem cMatrix_trace_mul_rpow_upperSemicontinuousOn_posDef
    (W : CMatrix a) (p : ℝ) :
    UpperSemicontinuousOn
      (fun M : CMatrix a => ((W * CFC.rpow M p).trace).re)
      ({M : CMatrix a | M.PosDef} : Set (CMatrix a)) :=
  ContinuousOn.upperSemicontinuousOn
    (cMatrix_trace_mul_rpow_continuousOn_posDef (a := a) W p)

/-- Pairing the inverse endpoint with a fixed PSD weight preserves convexity. -/
theorem cMatrix_trace_mul_rpow_neg_one_convexOn_posDef
    {W : CMatrix a} (hW : W.PosSemidef) :
    ConvexOn ℝ ({M : CMatrix a | M.PosDef} : Set (CMatrix a))
      (fun M : CMatrix a => ((W * CFC.rpow M (-1 : ℝ)).trace).re) := by
  exact cMatrix_trace_mul_rpow_convexOn_posDef_of_mem_Icc_neg_one_zero
    (a := a) hW (by norm_num)

/-- Trace-pairing quasiconvexity corollary for the inverse endpoint. -/
theorem cMatrix_trace_mul_rpow_neg_one_quasiconvexOn_posDef
    {W : CMatrix a} (hW : W.PosSemidef) :
    QuasiconvexOn ℝ ({M : CMatrix a | M.PosDef} : Set (CMatrix a))
      (fun M : CMatrix a => ((W * CFC.rpow M (-1 : ℝ)).trace).re) :=
  (cMatrix_trace_mul_rpow_neg_one_convexOn_posDef (a := a) hW).quasiconvexOn

/-- Positive matrix powers are operator-concave on the PSD cone for the strict
source range `0 < p ≤ 1`.

This proves the analytic input for the `τ_C^{α'}` side of the source bracket.
The dual `σ_B^{-α'}` side uses
`cMatrix_rpow_convexOn_posDef_of_mem_Icc_neg_one_zero`. -/
theorem cMatrix_rpow_concaveOn_posSemidef_of_pos
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ConcaveOn ℝ ({M : CMatrix a | M.PosSemidef} : Set (CMatrix a))
      (fun M : CMatrix a => CFC.rpow M p) := by
  let q : ℝ≥0 := ⟨p, le_of_lt hp0⟩
  have hq : q ∈ Set.Icc (0 : ℝ≥0) 1 := by
    constructor
    · exact zero_le
    · exact_mod_cast hp1
  have hset :
      ({M : CMatrix a | M.PosSemidef} : Set (CMatrix a)) =
        Set.Ici (0 : CMatrix a) := by
    ext M
    exact ⟨fun hM => Matrix.nonneg_iff_posSemidef.mpr hM,
      fun hM => Matrix.nonneg_iff_posSemidef.mp hM⟩
  have hqpos : 0 < q := by
    exact_mod_cast hp0
  change ConcaveOn ℝ ({M : CMatrix a | M.PosSemidef} : Set (CMatrix a))
    (fun M : CMatrix a => M ^ (q : ℝ))
  rw [hset]
  simpa only [← CFC.nnrpow_eq_rpow hqpos] using
    (CFC.concaveOn_nnrpow (A := CMatrix a) hq)

/-- Positive matrix powers are quasiconcave on the PSD cone in the source range
`0 < p ≤ 1`; this is the Sion-form corollary of operator concavity for the
`τ_C^{α'}` side of the bracket. -/
theorem cMatrix_rpow_quasiconcaveOn_posSemidef_of_pos
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    QuasiconcaveOn ℝ ({M : CMatrix a | M.PosSemidef} : Set (CMatrix a))
      (fun M : CMatrix a => CFC.rpow M p) :=
  (cMatrix_rpow_concaveOn_posSemidef_of_pos (a := a) hp0 hp1).quasiconcaveOn

/-- Positive matrix powers are continuous on the PSD cone. -/
theorem cMatrix_rpow_continuousOn_posSemidef_of_pos
    {p : ℝ} (hp0 : 0 < p) :
    ContinuousOn (fun M : CMatrix a => CFC.rpow M p)
      ({M : CMatrix a | M.PosSemidef} : Set (CMatrix a)) := by
  let q : ℝ≥0 := ⟨p, le_of_lt hp0⟩
  have hset :
      ({M : CMatrix a | M.PosSemidef} : Set (CMatrix a)) =
        Set.Ici (0 : CMatrix a) := by
    ext M
    exact ⟨fun hM => Matrix.nonneg_iff_posSemidef.mpr hM,
      fun hM => Matrix.nonneg_iff_posSemidef.mp hM⟩
  have hqpos : 0 < q := by
    exact_mod_cast hp0
  change ContinuousOn (fun M : CMatrix a => M ^ (q : ℝ))
    ({M : CMatrix a | M.PosSemidef} : Set (CMatrix a))
  rw [hset]
  simpa only [← CFC.nnrpow_eq_rpow hqpos] using
    (CFC.continuousOn_nnrpow (A := CMatrix a) q)

/-- Trace-pairing form of positive-power continuity on the PSD cone. -/
theorem cMatrix_trace_mul_rpow_continuousOn_posSemidef_of_pos
    (W : CMatrix a) {p : ℝ} (hp0 : 0 < p) :
    ContinuousOn
      (fun M : CMatrix a => ((W * CFC.rpow M p).trace).re)
      ({M : CMatrix a | M.PosSemidef} : Set (CMatrix a)) := by
  have hpow := cMatrix_rpow_continuousOn_posSemidef_of_pos (a := a) hp0
  have htrace : Continuous fun M : CMatrix a => ((W * M).trace).re := by
    exact Complex.continuous_re.comp
      (Continuous.matrix_trace (continuous_const.mul continuous_id))
  simpa [Function.comp_def] using htrace.comp_continuousOn hpow

/-- Lower semicontinuity corollary for the positive-power trace pairing. -/
theorem cMatrix_trace_mul_rpow_lowerSemicontinuousOn_posSemidef_of_pos
    (W : CMatrix a) {p : ℝ} (hp0 : 0 < p) :
    LowerSemicontinuousOn
      (fun M : CMatrix a => ((W * CFC.rpow M p).trace).re)
      ({M : CMatrix a | M.PosSemidef} : Set (CMatrix a)) :=
  ContinuousOn.lowerSemicontinuousOn
    (cMatrix_trace_mul_rpow_continuousOn_posSemidef_of_pos (a := a) W hp0)

/-- Upper semicontinuity corollary for the positive-power trace pairing. -/
theorem cMatrix_trace_mul_rpow_upperSemicontinuousOn_posSemidef_of_pos
    (W : CMatrix a) {p : ℝ} (hp0 : 0 < p) :
    UpperSemicontinuousOn
      (fun M : CMatrix a => ((W * CFC.rpow M p).trace).re)
      ({M : CMatrix a | M.PosSemidef} : Set (CMatrix a)) :=
  ContinuousOn.upperSemicontinuousOn
    (cMatrix_trace_mul_rpow_continuousOn_posSemidef_of_pos (a := a) W hp0)

/-- Pairing positive matrix powers with a fixed PSD weight preserves concavity.

This scalar form is the trace-pairing input for the `τ_C^{α'}` side of the
conditional-Renyi minimax bracket. -/
theorem cMatrix_trace_mul_rpow_concaveOn_posSemidef_of_pos
    {W : CMatrix a} (hW : W.PosSemidef) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ConcaveOn ℝ ({M : CMatrix a | M.PosSemidef} : Set (CMatrix a))
      (fun M : CMatrix a => ((W * CFC.rpow M p).trace).re) := by
  constructor
  · intro x hx y hy s t hs ht hst
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hx hs)
      (Matrix.PosSemidef.smul hy ht)
  · intro x hx y hy s t hs ht hst
    have hpow :=
      (cMatrix_rpow_concaveOn_posSemidef_of_pos (a := a) hp0 hp1).2 hx hy hs ht hst
    have hdiff_nonneg :
        0 ≤ CFC.rpow (s • x + t • y) p -
          (s • CFC.rpow x p + t • CFC.rpow y p) := by
      exact sub_nonneg.mpr hpow
    have hdiff_psd :
        (CFC.rpow (s • x + t • y) p -
          (s • CFC.rpow x p + t • CFC.rpow y p)).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp hdiff_nonneg
    have htrace := cMatrix_trace_mul_posSemidef_re_nonneg hW hdiff_psd
    have hlinear :
        ((W * (CFC.rpow (s • x + t • y) p -
          (s • CFC.rpow x p + t • CFC.rpow y p))).trace).re =
          ((W * CFC.rpow (s • x + t • y) p).trace).re -
            (s * ((W * CFC.rpow x p).trace).re +
              t * ((W * CFC.rpow y p).trace).re) := by
      simp [Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul, Complex.real_smul,
        sub_eq_add_neg, add_comm]
    rw [hlinear] at htrace
    have hle :
        s * ((W * CFC.rpow x p).trace).re + t * ((W * CFC.rpow y p).trace).re ≤
          ((W * CFC.rpow (s • x + t • y) p).trace).re := by
      nlinarith
    simpa [smul_eq_mul] using hle

/-- Trace-pairing quasiconcavity corollary for positive matrix powers. -/
theorem cMatrix_trace_mul_rpow_quasiconcaveOn_posSemidef_of_pos
    {W : CMatrix a} (hW : W.PosSemidef) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    QuasiconcaveOn ℝ ({M : CMatrix a | M.PosSemidef} : Set (CMatrix a))
      (fun M : CMatrix a => ((W * CFC.rpow M p).trace).re) :=
  (cMatrix_trace_mul_rpow_concaveOn_posSemidef_of_pos (a := a) hW hp0 hp1).quasiconcaveOn

/-- The raw source bracket is concave in the positive-power side variable. -/
theorem abcSidePowerTraceRe_concaveOn_tau
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    {σ : CMatrix b} (hσ : σ.PosSemidef)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ConcaveOn ℝ ({τ : CMatrix c | τ.PosSemidef} : Set (CMatrix c))
      (fun τ : CMatrix c => abcSidePowerTraceRe (a := a) R σ τ p) := by
  constructor
  · intro x hx y hy s t hs ht hst
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hx hs)
      (Matrix.PosSemidef.smul hy ht)
  · intro x hx y hy s t hs ht hst
    let S : CMatrix b := CFC.rpow σ (-p)
    let K : CMatrix (Prod a b) := Matrix.kronecker (1 : CMatrix a) S
    let T : CMatrix c := CFC.rpow (s • x + t • y) p
    let U : CMatrix c := CFC.rpow x p
    let V : CMatrix c := CFC.rpow y p
    let D : CMatrix c :=
      T + ((-s) • U + (-t) • V)
    have hpow :=
      (cMatrix_rpow_concaveOn_posSemidef_of_pos (a := c) hp0 hp1).2 hx hy hs ht hst
    have hdiff_nonneg :
        0 ≤ CFC.rpow (s • x + t • y) p -
          (s • CFC.rpow x p + t • CFC.rpow y p) := by
      exact sub_nonneg.mpr hpow
    have hD_nonneg : 0 ≤ D := by
      simpa [D, T, U, V, sub_eq_add_neg, neg_add_rev, add_comm, add_left_comm, add_assoc]
        using hdiff_nonneg
    have hD : D.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hD_nonneg
    have hS : S.PosSemidef :=
      cMatrix_rpow_posSemidef (A := σ) (s := -p) hσ
    have hleft : K.PosSemidef :=
      Matrix.PosSemidef.one.kronecker hS
    have hfull : (Matrix.kronecker K D).PosSemidef :=
      hleft.kronecker hD
    have htrace := cMatrix_trace_mul_posSemidef_re_nonneg hfull hR
    change 0 ≤ ((Matrix.kronecker K D * R).trace).re at htrace
    have htrace' :
        0 ≤ abcSidePowerTraceRe (a := a) R σ (s • x + t • y) p +
          (-s * abcSidePowerTraceRe (a := a) R σ x p +
            -t * abcSidePowerTraceRe (a := a) R σ y p) := by
      rw [trace_kronecker_right_add_smul_add_smul_re K R T U V (-s) (-t)] at htrace
      have hT :
          ((Matrix.kronecker K T * R).trace).re =
            abcSidePowerTraceRe (a := a) R σ (s • x + t • y) p := by
        simp [abcSidePowerTraceRe, K, S, T]
      have hU :
          ((Matrix.kronecker K U * R).trace).re =
            abcSidePowerTraceRe (a := a) R σ x p := by
        simp [abcSidePowerTraceRe, K, S, U]
      have hV :
          ((Matrix.kronecker K V * R).trace).re =
            abcSidePowerTraceRe (a := a) R σ y p := by
        simp [abcSidePowerTraceRe, K, S, V]
      rw [hT, hU, hV] at htrace
      exact htrace
    have hle :
        s * abcSidePowerTraceRe (a := a) R σ x p +
          t * abcSidePowerTraceRe (a := a) R σ y p ≤
            abcSidePowerTraceRe (a := a) R σ (s • x + t • y) p := by
      nlinarith
    simpa [smul_eq_mul] using hle

/-- The raw source bracket is quasiconcave in the positive-power side variable. -/
theorem abcSidePowerTraceRe_quasiconcaveOn_tau
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    {σ : CMatrix b} (hσ : σ.PosSemidef)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    QuasiconcaveOn ℝ ({τ : CMatrix c | τ.PosSemidef} : Set (CMatrix c))
      (fun τ : CMatrix c => abcSidePowerTraceRe (a := a) R σ τ p) :=
  (abcSidePowerTraceRe_concaveOn_tau (a := a) hR hσ hp0 hp1).quasiconcaveOn

/-- The raw source bracket is continuous in the positive-power side variable on
the PSD cone. -/
theorem abcSidePowerTraceRe_continuousOn_tau_posSemidef
    (R : CMatrix (Prod (Prod a b) c)) (σ : CMatrix b)
    {p : ℝ} (hp0 : 0 < p) :
    ContinuousOn
      (fun τ : CMatrix c => abcSidePowerTraceRe (a := a) R σ τ p)
      ({τ : CMatrix c | τ.PosSemidef} : Set (CMatrix c)) := by
  let K : CMatrix (Prod a b) := Matrix.kronecker (1 : CMatrix a) (CFC.rpow σ (-p))
  have htrace := trace_kronecker_right_continuous (a := a) (b := b) (c := c) K R
  have hpow := cMatrix_rpow_continuousOn_posSemidef_of_pos (a := c) hp0
  simpa [abcSidePowerTraceRe, K, Function.comp_def] using htrace.comp_continuousOn hpow

/-- Lower semicontinuity in the positive-power side variable on the PSD cone. -/
theorem abcSidePowerTraceRe_lowerSemicontinuousOn_tau_posSemidef
    (R : CMatrix (Prod (Prod a b) c)) (σ : CMatrix b)
    {p : ℝ} (hp0 : 0 < p) :
    LowerSemicontinuousOn
      (fun τ : CMatrix c => abcSidePowerTraceRe (a := a) R σ τ p)
      ({τ : CMatrix c | τ.PosSemidef} : Set (CMatrix c)) :=
  ContinuousOn.lowerSemicontinuousOn
    (abcSidePowerTraceRe_continuousOn_tau_posSemidef (a := a) R σ hp0)

/-- Upper semicontinuity in the positive-power side variable on the PSD cone. -/
theorem abcSidePowerTraceRe_upperSemicontinuousOn_tau_posSemidef
    (R : CMatrix (Prod (Prod a b) c)) (σ : CMatrix b)
    {p : ℝ} (hp0 : 0 < p) :
    UpperSemicontinuousOn
      (fun τ : CMatrix c => abcSidePowerTraceRe (a := a) R σ τ p)
      ({τ : CMatrix c | τ.PosSemidef} : Set (CMatrix c)) :=
  ContinuousOn.upperSemicontinuousOn
    (abcSidePowerTraceRe_continuousOn_tau_posSemidef (a := a) R σ hp0)

/-- The raw source bracket is convex in the negative-power side variable on the
positive-definite cone. -/
theorem abcSidePowerTraceRe_convexOn_sigma_posDef
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    {τ : CMatrix c} (hτ : τ.PosSemidef)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ConvexOn ℝ ({σ : CMatrix b | σ.PosDef} : Set (CMatrix b))
      (fun σ : CMatrix b => abcSidePowerTraceRe (a := a) R σ τ p) := by
  constructor
  · exact posDefMatrixSet_convex (a := b)
  · intro x hx y hy s t hs ht hst
    let S : CMatrix b := CFC.rpow (s • x + t • y) (-p)
    let U : CMatrix b := CFC.rpow x (-p)
    let V : CMatrix b := CFC.rpow y (-p)
    let T : CMatrix c := CFC.rpow τ p
    let D : CMatrix b := (-1 : ℝ) • S + (s • U + t • V)
    have hp_neg : -p ∈ Set.Icc (-1 : ℝ) 0 := by
      constructor <;> linarith
    have hpow :=
      (cMatrix_rpow_convexOn_posDef_of_mem_Icc_neg_one_zero (a := b) hp_neg).2
        hx hy hs ht hst
    have hdiff_nonneg :
        0 ≤ (s • CFC.rpow x (-p) + t • CFC.rpow y (-p)) -
          CFC.rpow (s • x + t • y) (-p) := by
      exact sub_nonneg.mpr hpow
    have hD_nonneg : 0 ≤ D := by
      simpa [D, S, U, V, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using hdiff_nonneg
    have hD : D.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hD_nonneg
    have hT : T.PosSemidef :=
      cMatrix_rpow_posSemidef (A := τ) (s := p) hτ
    have hleft : (Matrix.kronecker (1 : CMatrix a) D).PosSemidef :=
      Matrix.PosSemidef.one.kronecker hD
    have hfull : (Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) D) T).PosSemidef :=
      hleft.kronecker hT
    have htrace := cMatrix_trace_mul_posSemidef_re_nonneg hfull hR
    change 0 ≤
      ((Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) D) T * R).trace).re at htrace
    have htrace' :
        0 ≤ -abcSidePowerTraceRe (a := a) R (s • x + t • y) τ p +
          (s * abcSidePowerTraceRe (a := a) R x τ p +
            t * abcSidePowerTraceRe (a := a) R y τ p) := by
      rw [trace_kronecker_middle_add_smul_add_smul_re R T ((-1 : ℝ) • S) U V s t]
        at htrace
      have hS :
          ((Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) ((-1 : ℝ) • S)) T *
            R).trace).re =
            -abcSidePowerTraceRe (a := a) R (s • x + t • y) τ p := by
        simp only [abcSidePowerTraceRe, S, T]
        unfold Matrix.kronecker
        rw [Matrix.kroneckerMap_smul_right (fun x y : ℂ => x * y) (-1 : ℝ)
          (by intro x y; exact mul_smul_comm (-1 : ℝ) x y) (1 : CMatrix a)
          (CFC.rpow (s • x + t • y) (-p))]
        rw [Matrix.kroneckerMap_smul_left (fun x y : ℂ => x * y) (-1 : ℝ)
          (by intro x y; exact smul_mul_assoc (-1 : ℝ) x y)
          (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : CMatrix a)
            (CFC.rpow (s • x + t • y) (-p)))
          (CFC.rpow τ p)]
        rw [Matrix.smul_mul, Matrix.trace_smul]
        simp
      have hU :
          ((Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) U) T * R).trace).re =
            abcSidePowerTraceRe (a := a) R x τ p := by
        simp [abcSidePowerTraceRe, U, T]
      have hV :
          ((Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) V) T * R).trace).re =
            abcSidePowerTraceRe (a := a) R y τ p := by
        simp [abcSidePowerTraceRe, V, T]
      rw [hS, hU, hV] at htrace
      exact htrace
    have hle :
        abcSidePowerTraceRe (a := a) R (s • x + t • y) τ p ≤
          s * abcSidePowerTraceRe (a := a) R x τ p +
            t * abcSidePowerTraceRe (a := a) R y τ p := by
      nlinarith
    simpa [smul_eq_mul] using hle

/-- The raw source bracket is quasiconvex in the negative-power side variable
on the positive-definite cone. -/
theorem abcSidePowerTraceRe_quasiconvexOn_sigma_posDef
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    {τ : CMatrix c} (hτ : τ.PosSemidef)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    QuasiconvexOn ℝ ({σ : CMatrix b | σ.PosDef} : Set (CMatrix b))
      (fun σ : CMatrix b => abcSidePowerTraceRe (a := a) R σ τ p) :=
  (abcSidePowerTraceRe_convexOn_sigma_posDef (a := a) hR hτ hp0 hp1).quasiconvexOn

/-- The raw source bracket is continuous in the negative-power side variable on
the positive-definite cone. -/
theorem abcSidePowerTraceRe_continuousOn_sigma_posDef
    (R : CMatrix (Prod (Prod a b) c)) (τ : CMatrix c) (p : ℝ) :
    ContinuousOn
      (fun σ : CMatrix b => abcSidePowerTraceRe (a := a) R σ τ p)
      ({σ : CMatrix b | σ.PosDef} : Set (CMatrix b)) := by
  have htrace :=
    trace_kronecker_middle_continuous (a := a) (b := b) (c := c) R (CFC.rpow τ p)
  have hpow := cMatrix_rpow_continuousOn_posDef (a := b) (-p)
  simpa [abcSidePowerTraceRe, Function.comp_def] using htrace.comp_continuousOn hpow

/-- Lower semicontinuity in the negative-power side variable on the
positive-definite cone. -/
theorem abcSidePowerTraceRe_lowerSemicontinuousOn_sigma_posDef
    (R : CMatrix (Prod (Prod a b) c)) (τ : CMatrix c) (p : ℝ) :
    LowerSemicontinuousOn
      (fun σ : CMatrix b => abcSidePowerTraceRe (a := a) R σ τ p)
      ({σ : CMatrix b | σ.PosDef} : Set (CMatrix b)) :=
  ContinuousOn.lowerSemicontinuousOn
    (abcSidePowerTraceRe_continuousOn_sigma_posDef (a := a) R τ p)

/-- Upper semicontinuity in the negative-power side variable on the
positive-definite cone. -/
theorem abcSidePowerTraceRe_upperSemicontinuousOn_sigma_posDef
    (R : CMatrix (Prod (Prod a b) c)) (τ : CMatrix c) (p : ℝ) :
    UpperSemicontinuousOn
      (fun σ : CMatrix b => abcSidePowerTraceRe (a := a) R σ τ p)
      ({σ : CMatrix b | σ.PosDef} : Set (CMatrix b)) :=
  ContinuousOn.upperSemicontinuousOn
    (abcSidePowerTraceRe_continuousOn_sigma_posDef (a := a) R τ p)

/-- Sion's minimax theorem in the exact `inf_sigma sup_tau = sup_tau inf_sigma`
shape used by the conditional Renyi trace-functional route. -/
theorem sion_iInf_iSup_eq_iSup_iInf
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {X : Set E} {Y : Set F} {f : E → F → EReal}
    (hneX : X.Nonempty) (hconvX : Convex ℝ X) (hcompactX : IsCompact X)
    (hlscX : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (hqconvX : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)
    (hconvY : Convex ℝ Y)
    (huscY : ∀ x ∈ X, UpperSemicontinuousOn (fun y : F => f x y) Y)
    (hqconcY : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y) :
    (⨅ x ∈ X, ⨆ y ∈ Y, f x y) = ⨆ y ∈ Y, ⨅ x ∈ X, f x y := by
  exact Sion.minimax' hneX hconvX hcompactX hlscX hqconvX hconvY huscY hqconcY

/-- Real-valued Sion minimax specialized to the saddle-point output supplied by
mathlib.  The `EReal` equality form above is convenient for source formulas
written as `inf sup = sup inf`; this real-valued form is the bridge used before
coercing a continuous trace functional into the extended-real Sion route. -/
theorem sion_exists_isSaddlePointOn
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {X : Set E} {Y : Set F} {f : E → F → ℝ}
    (hneX : X.Nonempty) (hconvX : Convex ℝ X) (hcompactX : IsCompact X)
    (hlscX : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (hqconvX : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)
    (hconvY : Convex ℝ Y) (hneY : Y.Nonempty) (hcompactY : IsCompact Y)
    (huscY : ∀ x ∈ X, UpperSemicontinuousOn (fun y : F => f x y) Y)
    (hqconcY : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y) :
    ∃ x ∈ X, ∃ y ∈ Y, IsSaddlePointOn X Y f x y := by
  exact Sion.exists_isSaddlePointOn
    hneX hconvX hcompactX hlscX hqconvX hconvY hneY hcompactY huscY hqconcY

/-- Sion's minimax theorem specialized to finite-dimensional density-matrix
domains on the two side systems.

This is the reusable side-state optimization shape needed by the conditional
Renyi duality route: the first domain contributes the compactness hypothesis,
while the second contributes the convexity hypothesis exactly as in Sion's
asymmetric statement. -/
theorem densityMatrixSet_sion_iInf_iSup_eq_iSup_iInf
    {b : Type u} {c : Type v} [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] {f : CMatrix b → CMatrix c → EReal}
    (hlscB : ∀ τ ∈ densityMatrixSet c,
      LowerSemicontinuousOn (fun σ : CMatrix b => f σ τ) (densityMatrixSet b))
    (hqconvB : ∀ τ ∈ densityMatrixSet c,
      QuasiconvexOn ℝ (densityMatrixSet b) fun σ => f σ τ)
    (huscC : ∀ σ ∈ densityMatrixSet b,
      UpperSemicontinuousOn (fun τ : CMatrix c => f σ τ) (densityMatrixSet c))
    (hqconcC : ∀ σ ∈ densityMatrixSet b,
      QuasiconcaveOn ℝ (densityMatrixSet c) fun τ => f σ τ) :
    (⨅ σ ∈ densityMatrixSet b, ⨆ τ ∈ densityMatrixSet c, f σ τ) =
      ⨆ τ ∈ densityMatrixSet c, ⨅ σ ∈ densityMatrixSet b, f σ τ := by
  exact sion_iInf_iSup_eq_iSup_iInf
    (densityMatrixSet_nonempty (a := b))
    (densityMatrixSet_convex (a := b))
    (densityMatrixSet_isCompact (a := b))
    hlscB hqconvB
    (densityMatrixSet_convex (a := c))
    huscC hqconcC

/-- Source-shaped Sion exchange for the conditional-Renyi pure-state bracket.

This theorem is the direct minimax expression used at the final step of
Tomamichel's proof of `pr:dual-new`.  It discharges the compact convex
density-domain side of Sion and leaves exactly the analytic facts about the
concrete bracket as hypotheses: lower semicontinuity and quasiconvexity in
`σ_B`, upper semicontinuity and quasiconcavity in `τ_C`. -/
theorem densityMatrixSet_sion_upwardRenyiDualityBracketEReal
    {a : Type u} {b : Type v} {c : Type w}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (ψ : PureVector (Prod (Prod a b) c)) (alphaPrime : ℝ)
    (hlscB : ∀ τ ∈ densityMatrixSet c,
      LowerSemicontinuousOn
        (fun σ : CMatrix b =>
          upwardRenyiDualityBracketEReal (a := a) ψ σ τ alphaPrime)
        (densityMatrixSet b))
    (hqconvB : ∀ τ ∈ densityMatrixSet c,
      QuasiconvexOn ℝ (densityMatrixSet b) fun σ : CMatrix b =>
        upwardRenyiDualityBracketEReal (a := a) ψ σ τ alphaPrime)
    (huscC : ∀ σ ∈ densityMatrixSet b,
      UpperSemicontinuousOn
        (fun τ : CMatrix c =>
          upwardRenyiDualityBracketEReal (a := a) ψ σ τ alphaPrime)
        (densityMatrixSet c))
    (hqconcC : ∀ σ ∈ densityMatrixSet b,
      QuasiconcaveOn ℝ (densityMatrixSet c) fun τ : CMatrix c =>
        upwardRenyiDualityBracketEReal (a := a) ψ σ τ alphaPrime) :
    (⨅ σ ∈ densityMatrixSet b, ⨆ τ ∈ densityMatrixSet c,
        upwardRenyiDualityBracketEReal (a := a) ψ σ τ alphaPrime) =
      ⨆ τ ∈ densityMatrixSet c, ⨅ σ ∈ densityMatrixSet b,
        upwardRenyiDualityBracketEReal (a := a) ψ σ τ alphaPrime := by
  exact densityMatrixSet_sion_iInf_iSup_eq_iSup_iInf
    (b := b) (c := c)
    (f := fun σ τ => upwardRenyiDualityBracketEReal (a := a) ψ σ τ alphaPrime)
    hlscB hqconvB huscC hqconcC

/-- Real-valued Sion saddle-point theorem specialized to finite-dimensional
density-matrix domains on the two side systems.

This packages the exact compact-convex domain hypotheses for the source trace
functional.  The remaining downstream work is to prove the listed continuity and
quasiconvexity/quasiconcavity hypotheses for the concrete conditional-Renyi
trace functional, including the extended-value treatment at singular boundary
points. -/
theorem densityMatrixSet_sion_exists_isSaddlePointOn
    {b : Type u} {c : Type v} [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c] {f : CMatrix b → CMatrix c → ℝ}
    (hlscB : ∀ τ ∈ densityMatrixSet c,
      LowerSemicontinuousOn (fun σ : CMatrix b => f σ τ) (densityMatrixSet b))
    (hqconvB : ∀ τ ∈ densityMatrixSet c,
      QuasiconvexOn ℝ (densityMatrixSet b) fun σ => f σ τ)
    (huscC : ∀ σ ∈ densityMatrixSet b,
      UpperSemicontinuousOn (fun τ : CMatrix c => f σ τ) (densityMatrixSet c))
    (hqconcC : ∀ σ ∈ densityMatrixSet b,
      QuasiconcaveOn ℝ (densityMatrixSet c) fun τ => f σ τ) :
    ∃ σ ∈ densityMatrixSet b, ∃ τ ∈ densityMatrixSet c,
      IsSaddlePointOn (densityMatrixSet b) (densityMatrixSet c) f σ τ := by
  exact sion_exists_isSaddlePointOn
    (densityMatrixSet_nonempty (a := b))
    (densityMatrixSet_convex (a := b))
    (densityMatrixSet_isCompact (a := b))
    hlscB hqconvB
    (densityMatrixSet_convex (a := c))
    (densityMatrixSet_nonempty (a := c))
    (densityMatrixSet_isCompact (a := c))
    huscC hqconcC

/-- Real-valued source-bracket Sion saddle point.

This is the same density-domain specialization as
`densityMatrixSet_sion_upwardRenyiDualityBracketEReal`, but in the real-valued
form used by mathlib's saddle-point theorem.  It is ready for downstream
assembly once the concrete bracket's semicontinuity and quasi-convex/concave
facts are supplied. -/
theorem densityMatrixSet_sion_upwardRenyiDualityBracketRe_saddle
    {a : Type u} {b : Type v} {c : Type w}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c)) (alphaPrime : ℝ)
    (hlscB : ∀ τ ∈ densityMatrixSet c,
      LowerSemicontinuousOn
        (fun σ : CMatrix b =>
          upwardRenyiDualityBracketRe (a := a) ψ σ τ alphaPrime)
        (densityMatrixSet b))
    (hqconvB : ∀ τ ∈ densityMatrixSet c,
      QuasiconvexOn ℝ (densityMatrixSet b) fun σ : CMatrix b =>
        upwardRenyiDualityBracketRe (a := a) ψ σ τ alphaPrime)
    (huscC : ∀ σ ∈ densityMatrixSet b,
      UpperSemicontinuousOn
        (fun τ : CMatrix c =>
          upwardRenyiDualityBracketRe (a := a) ψ σ τ alphaPrime)
        (densityMatrixSet c))
    (hqconcC : ∀ σ ∈ densityMatrixSet b,
      QuasiconcaveOn ℝ (densityMatrixSet c) fun τ : CMatrix c =>
        upwardRenyiDualityBracketRe (a := a) ψ σ τ alphaPrime) :
    ∃ σ ∈ densityMatrixSet b, ∃ τ ∈ densityMatrixSet c,
      IsSaddlePointOn (densityMatrixSet b) (densityMatrixSet c)
        (fun σ τ => upwardRenyiDualityBracketRe (a := a) ψ σ τ alphaPrime) σ τ := by
  exact densityMatrixSet_sion_exists_isSaddlePointOn
    (b := b) (c := c)
    (f := fun σ τ => upwardRenyiDualityBracketRe (a := a) ψ σ τ alphaPrime)
    hlscB hqconvB huscC hqconcC

/-- Source-faithful real-valued Sion saddle point for the raw conditional-Renyi
trace bracket on a compact full-support `sigma` domain.

The positive lower bound `delta • 1 ≤ sigma` is the Lean form of the source
restriction to a compact full-rank side-state set.  Under this restriction all
analytic Sion hypotheses for
`Tr[(I_A ⊗ sigma_B^{-p} ⊗ tau_C^p) R]` are discharged from the proved
positive-definite negative-power and PSD positive-power trace facts above. -/
theorem uniformlyPositiveDensityMatrixSet_sion_abcSidePowerTraceRe_saddle
    {a : Type u} {b : Type v} {c : Type w}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    {delta p : ℝ} (hdelta : 0 < delta)
    (hneB : (uniformlyPositiveDensityMatrixSet delta b).Nonempty)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ σ ∈ uniformlyPositiveDensityMatrixSet delta b, ∃ τ ∈ densityMatrixSet c,
      IsSaddlePointOn (uniformlyPositiveDensityMatrixSet delta b) (densityMatrixSet c)
        (fun σ τ => abcSidePowerTraceRe (a := a) R σ τ p) σ τ := by
  exact sion_exists_isSaddlePointOn
    hneB
    (uniformlyPositiveDensityMatrixSet_convex (a := b) (delta := delta))
    (uniformlyPositiveDensityMatrixSet_isCompact (a := b) (delta := delta))
    (fun τ hτ =>
      (abcSidePowerTraceRe_lowerSemicontinuousOn_sigma_posDef (a := a) R τ p).mono
        (uniformlyPositiveDensityMatrixSet_subset_posDef (a := b) hdelta))
    (fun τ hτ =>
      Convex.quasiconvexOn_restrict
        (abcSidePowerTraceRe_quasiconvexOn_sigma_posDef (a := a) hR hτ.1 hp0 hp1)
        (uniformlyPositiveDensityMatrixSet_subset_posDef (a := b) hdelta)
        (uniformlyPositiveDensityMatrixSet_convex (a := b) (delta := delta)))
    (densityMatrixSet_convex (a := c))
    (densityMatrixSet_nonempty (a := c))
    (densityMatrixSet_isCompact (a := c))
    (fun σ hσ =>
      (abcSidePowerTraceRe_upperSemicontinuousOn_tau_posSemidef (a := a) R σ hp0).mono
        (fun τ hτ => hτ.1))
    (fun σ hσ =>
      Convex.quasiconcaveOn_restrict
        (abcSidePowerTraceRe_quasiconcaveOn_tau (a := a) hR hσ.1.1 hp0 hp1)
        (fun τ hτ => hτ.1)
        (densityMatrixSet_convex (a := c)))

/-- Source-faithful Sion minimax equality for the raw conditional-Renyi trace
bracket on a compact full-support `sigma` domain.

This is the `inf_sigma sup_tau = sup_tau inf_sigma` form used by the
conditional-Renyi duality proof after the source restriction to side states
whose eigenvalues are bounded below by a positive constant. -/
theorem uniformlyPositiveDensityMatrixSet_sion_abcSidePowerTraceRe_EReal
    {a : Type u} {b : Type v} {c : Type w}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    {delta p : ℝ} (hdelta : 0 < delta)
    (hneB : (uniformlyPositiveDensityMatrixSet delta b).Nonempty)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (⨅ σ ∈ uniformlyPositiveDensityMatrixSet delta b, ⨆ τ ∈ densityMatrixSet c,
        (abcSidePowerTraceRe (a := a) R σ τ p : EReal)) =
      ⨆ τ ∈ densityMatrixSet c, ⨅ σ ∈ uniformlyPositiveDensityMatrixSet delta b,
        (abcSidePowerTraceRe (a := a) R σ τ p : EReal) := by
  exact sion_iInf_iSup_eq_iSup_iInf
    hneB
    (uniformlyPositiveDensityMatrixSet_convex (a := b) (delta := delta))
    (uniformlyPositiveDensityMatrixSet_isCompact (a := b) (delta := delta))
    (fun τ hτ => by
      exact continuous_coe_real_ereal.comp_lowerSemicontinuousOn
        ((abcSidePowerTraceRe_lowerSemicontinuousOn_sigma_posDef (a := a) R τ p).mono
          (uniformlyPositiveDensityMatrixSet_subset_posDef (a := b) hdelta))
        EReal.coe_strictMono.monotone)
    (fun τ hτ => by
      simpa [Function.comp_def] using
        (Convex.quasiconvexOn_restrict
          (abcSidePowerTraceRe_quasiconvexOn_sigma_posDef (a := a) hR hτ.1 hp0 hp1)
          (uniformlyPositiveDensityMatrixSet_subset_posDef (a := b) hdelta)
          (uniformlyPositiveDensityMatrixSet_convex (a := b) (delta := delta))).monotone_comp
            EReal.coe_strictMono.monotone)
    (densityMatrixSet_convex (a := c))
    (fun σ hσ => by
      exact continuous_coe_real_ereal.comp_upperSemicontinuousOn
        ((abcSidePowerTraceRe_upperSemicontinuousOn_tau_posSemidef (a := a) R σ hp0).mono
          (fun τ hτ => hτ.1))
        EReal.coe_strictMono.monotone)
    (fun σ hσ => by
      simpa [Function.comp_def] using
        (Convex.quasiconcaveOn_restrict
          (abcSidePowerTraceRe_quasiconcaveOn_tau (a := a) hR hσ.1.1 hp0 hp1)
          (fun τ hτ => hτ.1)
          (densityMatrixSet_convex (a := c))).monotone_comp
            EReal.coe_strictMono.monotone)

end State

end

end QIT
