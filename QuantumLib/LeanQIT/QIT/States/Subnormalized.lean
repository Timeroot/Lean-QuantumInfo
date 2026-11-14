/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.PosSqrt
public import QIT.States.TraceNorm.Distance
public import QIT.Channels.Diamond
public import QIT.States.Geometry.Fidelity
public import QIT.States.TraceNorm.BlockMatrix

/-!
# Subnormalized finite-dimensional states

This module provides the finite-dimensional subnormalized-state carrier needed
by the smooth-entropy, AEP, and decoupling proof routes. A subnormalized state is
a positive semidefinite matrix with trace at most one. The metric layer below
follows the registered generalized-fidelity and purified-distance source
claims [Tomamichel2015FiniteResources, metric.tex:390-416] and
[Tomamichel2015FiniteResources, metric.tex:512-513].

The API is intentionally infrastructure-only: smooth min/max duality and AEP
inequalities live in downstream information-theoretic modules.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u v

noncomputable section

/-- A finite-dimensional subnormalized density state. -/
structure SubnormalizedState (a : Type u) [Fintype a] [DecidableEq a] where
  matrix : CMatrix a
  pos : matrix.PosSemidef
  trace_le_one : matrix.trace.re ≤ 1

namespace SubnormalizedState

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Subnormalized states are equal when their matrices are equal. -/
@[ext]
theorem ext {ρ σ : SubnormalizedState a} (h : ρ.matrix = σ.matrix) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

/-- The density matrix of a subnormalized state is Hermitian. -/
theorem isHermitian (ρ : SubnormalizedState a) : ρ.matrix.IsHermitian :=
  ρ.pos.isHermitian

/-- The trace of a subnormalized state is nonnegative. -/
theorem trace_nonneg (ρ : SubnormalizedState a) : 0 ≤ ρ.matrix.trace.re :=
  (Matrix.PosSemidef.trace_nonneg ρ.pos).1

/-- The trace of a subnormalized state is real. -/
theorem trace_im_zero (ρ : SubnormalizedState a) : ρ.matrix.trace.im = 0 :=
  (Matrix.PosSemidef.trace_nonneg ρ.pos).2.symm

/-- The trace of a subnormalized state lies in the real unit interval. -/
theorem trace_mem_Icc (ρ : SubnormalizedState a) :
    ρ.matrix.trace.re ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨ρ.trace_nonneg, ρ.trace_le_one⟩

/-- A subnormalized state with nonzero trace has strictly positive trace. -/
theorem trace_pos_of_trace_ne_zero (ρ : SubnormalizedState a)
    (htr : ρ.matrix.trace.re ≠ 0) :
    0 < ρ.matrix.trace.re :=
  lt_of_le_of_ne ρ.trace_nonneg htr.symm

/-- Normalize a nonzero subnormalized state by dividing by its trace. -/
def normalize (ρ : SubnormalizedState a) (htr : ρ.matrix.trace.re ≠ 0) : State a where
  matrix := (ρ.matrix.trace.re)⁻¹ • ρ.matrix
  pos := Matrix.PosSemidef.smul ρ.pos (inv_nonneg.mpr ρ.trace_nonneg)
  trace_eq_one := by
    rw [Matrix.trace_smul]
    apply Complex.ext
    · simp [Complex.real_smul, htr]
    · simp [Complex.real_smul, ρ.trace_im_zero]

@[simp]
theorem normalize_matrix (ρ : SubnormalizedState a) (htr : ρ.matrix.trace.re ≠ 0) :
    (ρ.normalize htr).matrix = (ρ.matrix.trace.re)⁻¹ • ρ.matrix :=
  rfl

/-- Product of subnormalized states as a Kronecker product. -/
def prod (ρ : SubnormalizedState a) (σ : SubnormalizedState b) :
    SubnormalizedState (Prod a b) where
  matrix := Matrix.kronecker ρ.matrix σ.matrix
  pos := ρ.pos.kronecker σ.pos
  trace_le_one := by
    change ((Matrix.kroneckerMap (fun x y => x * y) ρ.matrix σ.matrix).trace).re ≤ 1
    rw [Matrix.trace_kronecker]
    rw [Complex.mul_re, ρ.trace_im_zero, σ.trace_im_zero]
    nlinarith [ρ.trace_nonneg, σ.trace_nonneg, ρ.trace_le_one, σ.trace_le_one]

/-- `Tr_A` of a product subnormalized state leaves the second factor scaled by
the trace of the first. -/
theorem partialTraceA_prod (ρ : SubnormalizedState a) (σ : SubnormalizedState b) :
    partialTraceA (a := a) (b := b) (ρ.prod σ).matrix =
      matrixScale ρ.matrix.trace σ.matrix := by
  rw [prod, partialTraceA_kronecker]

/-- `Tr_B` of a product subnormalized state leaves the first factor scaled by
the trace of the second. -/
theorem partialTraceB_prod (ρ : SubnormalizedState a) (σ : SubnormalizedState b) :
    partialTraceB (a := a) (b := b) (ρ.prod σ).matrix =
      matrixScale σ.matrix.trace ρ.matrix := by
  rw [prod, partialTraceB_kronecker]

/-- Marginal subnormalized state on the first subsystem. -/
def marginalA (ρ : SubnormalizedState (Prod a b)) : SubnormalizedState a where
  matrix := partialTraceB (a := a) (b := b) ρ.matrix
  pos := partialTraceB_posSemidef ρ.pos
  trace_le_one := by
    rw [partialTraceB_trace]
    exact ρ.trace_le_one

/-- Marginal subnormalized state on the second subsystem. -/
def marginalB (ρ : SubnormalizedState (Prod a b)) : SubnormalizedState b where
  matrix := partialTraceA (a := a) (b := b) ρ.matrix
  pos := partialTraceA_posSemidef ρ.pos
  trace_le_one := by
    rw [partialTraceA_trace]
    exact ρ.trace_le_one

@[simp]
theorem marginalA_matrix (ρ : SubnormalizedState (Prod a b)) :
    ρ.marginalA.matrix = partialTraceB (a := a) (b := b) ρ.matrix := rfl

@[simp]
theorem marginalB_matrix (ρ : SubnormalizedState (Prod a b)) :
    ρ.marginalB.matrix = partialTraceA (a := a) (b := b) ρ.matrix := rfl

/-- Generalized fidelity for finite-dimensional subnormalized states, following
the squared convention used by the Tomamichel purified-distance route. -/
def generalizedFidelity (ρ σ : SubnormalizedState a) : ℝ :=
  (traceNorm (psdSqrt ρ.matrix * psdSqrt σ.matrix) +
    Real.sqrt ((1 - ρ.matrix.trace.re) * (1 - σ.matrix.trace.re))) ^ 2

@[simp]
theorem generalizedFidelity_eq (ρ σ : SubnormalizedState a) :
    ρ.generalizedFidelity σ =
      (traceNorm (psdSqrt ρ.matrix * psdSqrt σ.matrix) +
        Real.sqrt ((1 - ρ.matrix.trace.re) * (1 - σ.matrix.trace.re))) ^ 2 :=
  rfl

/-- Purified distance for finite-dimensional subnormalized states,
`P(ρ,σ) = sqrt(1 - F_*(ρ,σ))`. -/
def purifiedDistance (ρ σ : SubnormalizedState a) : ℝ :=
  Real.sqrt (1 - ρ.generalizedFidelity σ)

@[simp]
theorem purifiedDistance_eq (ρ σ : SubnormalizedState a) :
    ρ.purifiedDistance σ = Real.sqrt (1 - ρ.generalizedFidelity σ) :=
  rfl

/-- Closed purified-distance epsilon ball around a subnormalized state. -/
def purifiedBall (ρ : SubnormalizedState a) (ε : ℝ) (σ : SubnormalizedState a) : Prop :=
  ρ.purifiedDistance σ ≤ ε

@[simp]
theorem purifiedBall_eq (ρ σ : SubnormalizedState a) (ε : ℝ) :
    ρ.purifiedBall ε σ ↔ ρ.purifiedDistance σ ≤ ε :=
  Iff.rfl

/-- Purified-distance balls are monotone in the smoothing radius. -/
theorem purifiedBall_mono {ρ σ : SubnormalizedState a} {ε δ : ℝ} (hεδ : ε ≤ δ) :
    ρ.purifiedBall ε σ → ρ.purifiedBall δ σ := by
  intro hball
  exact le_trans hball hεδ

/-! ## Hat extension to a normalized failure register -/

/-- Failure weight added by the hat extension, `1 - Tr ρ`. -/
def hatFailureMass (ρ : SubnormalizedState a) : ℝ :=
  1 - ρ.matrix.trace.re

theorem hatFailureMass_nonneg (ρ : SubnormalizedState a) :
    0 ≤ ρ.hatFailureMass := by
  dsimp [hatFailureMass]
  exact sub_nonneg.mpr ρ.trace_le_one

theorem hatFailureMass_add_trace_re (ρ : SubnormalizedState a) :
    ρ.hatFailureMass + ρ.matrix.trace.re = 1 := by
  dsimp [hatFailureMass]
  ring

/-- The one-dimensional failure block used by the hat extension. -/
def hatFailureBlock (ρ : SubnormalizedState a) : CMatrix PUnit :=
  fun _ _ => ((ρ.hatFailureMass : ℝ) : ℂ)

theorem hatFailureBlock_pos (ρ : SubnormalizedState a) :
    ρ.hatFailureBlock.PosSemidef := by
  have hdiag :
      ρ.hatFailureBlock =
        Matrix.diagonal (fun _ : PUnit => ((ρ.hatFailureMass : ℝ) : ℂ)) := by
    ext i j
    cases i
    cases j
    simp [hatFailureBlock, Matrix.diagonal]
  rw [hdiag]
  exact Matrix.PosSemidef.diagonal fun _ =>
    Complex.nonneg_iff.mpr ⟨ρ.hatFailureMass_nonneg, by simp⟩

/-- The block-diagonal matrix `ρ ⊕ (1 - Tr ρ)` on a one-dimensional failure
register plus the original system.  The failure register is the `Sum.inl`
summand; the original system is the `Sum.inr` summand. -/
def hatExtensionMatrix (ρ : SubnormalizedState a) : CMatrix (Sum PUnit a) :=
  Matrix.fromBlocks ρ.hatFailureBlock 0 0 ρ.matrix

@[simp]
theorem hatExtensionMatrix_fail_fail (ρ : SubnormalizedState a) (i j : PUnit) :
    ρ.hatExtensionMatrix (Sum.inl i) (Sum.inl j) =
      ((ρ.hatFailureMass : ℝ) : ℂ) :=
  rfl

@[simp]
theorem hatExtensionMatrix_fail_state (ρ : SubnormalizedState a) (i : PUnit) (j : a) :
    ρ.hatExtensionMatrix (Sum.inl i) (Sum.inr j) = 0 := by
  simp [hatExtensionMatrix]

@[simp]
theorem hatExtensionMatrix_state_fail (ρ : SubnormalizedState a) (i : a) (j : PUnit) :
    ρ.hatExtensionMatrix (Sum.inr i) (Sum.inl j) = 0 := by
  simp [hatExtensionMatrix]

@[simp]
theorem hatExtensionMatrix_state_state (ρ : SubnormalizedState a) (i j : a) :
    ρ.hatExtensionMatrix (Sum.inr i) (Sum.inr j) = ρ.matrix i j :=
  rfl

theorem hatExtensionMatrix_pos (ρ : SubnormalizedState a) :
    ρ.hatExtensionMatrix.PosSemidef := by
  classical
  exact Matrix.fromBlocks_diagonal_posSemidef ρ.hatFailureBlock_pos ρ.pos

theorem hatExtensionMatrix_trace (ρ : SubnormalizedState a) :
    ρ.hatExtensionMatrix.trace = 1 := by
  classical
  rw [hatExtensionMatrix, Matrix.trace_fromBlocks_diagonal]
  have hfail_trace :
      ρ.hatFailureBlock.trace = ((ρ.hatFailureMass : ℝ) : ℂ) := by
    simp [hatFailureBlock, Matrix.trace]
  rw [hfail_trace]
  apply Complex.ext
  · simp [hatFailureMass]
  · simp [ρ.trace_im_zero]

/-- Hat extension of a subnormalized state to a normalized state by adjoining a
one-dimensional failure register with weight `1 - Tr ρ`.  This is the finite
Lean version of Tomamichel's block-diagonal `ρ̂ = ρ ⊕ (1 - Tr ρ)` construction
from `metric.tex`, lines 246-248 and 414-416. -/
def hatExtension (ρ : SubnormalizedState a) : State (Sum PUnit a) where
  matrix := ρ.hatExtensionMatrix
  pos := ρ.hatExtensionMatrix_pos
  trace_eq_one := ρ.hatExtensionMatrix_trace

@[simp]
theorem hatExtension_matrix (ρ : SubnormalizedState a) :
    ρ.hatExtension.matrix = ρ.hatExtensionMatrix :=
  rfl

theorem hatExtension_trace_one (ρ : SubnormalizedState a) :
    ρ.hatExtension.matrix.trace = 1 :=
  ρ.hatExtension.trace_eq_one

private theorem punit_psdSqrt_const (r : ℝ) (hr : 0 ≤ r) :
    psdSqrt (fun _ _ : PUnit => ((r : ℝ) : ℂ) : CMatrix PUnit) =
      (fun _ _ : PUnit => ((Real.sqrt r : ℝ) : ℂ) : CMatrix PUnit) := by
  let A : CMatrix PUnit := fun _ _ => ((r : ℝ) : ℂ)
  let S : CMatrix PUnit := fun _ _ => ((Real.sqrt r : ℝ) : ℂ)
  have hsqrt_sq : ((Real.sqrt r : ℂ) * (Real.sqrt r : ℂ)) = (r : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr]
  have hSsq : S * S = A := by
    ext i j
    cases i
    cases j
    simp [S, A, Matrix.mul_apply, hsqrt_sq]
  have hSpos : S.PosSemidef := by
    have hdiag : S = Matrix.diagonal (fun _ : PUnit => ((Real.sqrt r : ℝ) : ℂ)) := by
      ext i j
      cases i
      cases j
      simp [S, Matrix.diagonal]
    rw [hdiag]
    exact Matrix.PosSemidef.diagonal fun _ =>
      Complex.nonneg_iff.mpr ⟨Real.sqrt_nonneg r, by simp⟩
  change psdSqrt A = S
  simpa [psdSqrt] using (CFC.sqrt_unique (a := A) (b := S) hSsq hSpos.nonneg)

private theorem traceNorm_punit_const_of_nonneg (r : ℝ) (hr : 0 ≤ r) :
    traceNorm (fun _ _ : PUnit => ((r : ℝ) : ℂ) : CMatrix PUnit) = r := by
  let A : CMatrix PUnit := fun _ _ => ((r : ℝ) : ℂ)
  have hgram : Aᴴ * A = (fun _ _ : PUnit => ((r * r : ℝ) : ℂ) : CMatrix PUnit) := by
    ext i j
    cases i
    cases j
    simp [A, Matrix.mul_apply, ← Complex.ofReal_mul]
  have hsqrt : psdSqrt (Aᴴ * A) = A := by
    rw [hgram]
    rw [punit_psdSqrt_const (r * r) (mul_self_nonneg r)]
    ext i j
    cases i
    cases j
    simp [A, Real.sqrt_mul_self hr]
  rw [traceNorm]
  rw [hsqrt]
  simp [A, Matrix.trace]

/-- The generalized fidelity of subnormalized states is the squared fidelity of
their normalized hat extensions.  This is Tomamichel's
`F_g(ρ,σ) = F(ρ̂,σ̂)` route from `metric.tex`, lines 390-416. -/
theorem generalizedFidelity_eq_squaredFidelity_hatExtension
    (ρ σ : SubnormalizedState a) :
    ρ.generalizedFidelity σ =
      ρ.hatExtension.squaredFidelity σ.hatExtension := by
  rw [generalizedFidelity_eq, State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq]
  have hρfail : 0 ≤ ρ.hatFailureMass := ρ.hatFailureMass_nonneg
  have hσfail : 0 ≤ σ.hatFailureMass := σ.hatFailureMass_nonneg
  have hρsqrt :
      ρ.hatExtension.sqrtMatrix =
        Matrix.fromBlocks
          (fun _ _ : PUnit => ((Real.sqrt ρ.hatFailureMass : ℝ) : ℂ))
          0 0 (psdSqrt ρ.matrix) := by
    rw [State.sqrtMatrix, hatExtension_matrix, hatExtensionMatrix]
    rw [Matrix.fromBlocks_diagonal_psdSqrt ρ.hatFailureBlock_pos ρ.pos]
    rw [show psdSqrt ρ.hatFailureBlock =
        (fun _ _ : PUnit => ((Real.sqrt ρ.hatFailureMass : ℝ) : ℂ)) by
      simpa [hatFailureBlock] using punit_psdSqrt_const ρ.hatFailureMass hρfail]
  have hσsqrt :
      σ.hatExtension.sqrtMatrix =
        Matrix.fromBlocks
          (fun _ _ : PUnit => ((Real.sqrt σ.hatFailureMass : ℝ) : ℂ))
          0 0 (psdSqrt σ.matrix) := by
    rw [State.sqrtMatrix, hatExtension_matrix, hatExtensionMatrix]
    rw [Matrix.fromBlocks_diagonal_psdSqrt σ.hatFailureBlock_pos σ.pos]
    rw [show psdSqrt σ.hatFailureBlock =
        (fun _ _ : PUnit => ((Real.sqrt σ.hatFailureMass : ℝ) : ℂ)) by
      simpa [hatFailureBlock] using punit_psdSqrt_const σ.hatFailureMass hσfail]
  rw [hρsqrt, hσsqrt]
  have hprod :
      (Matrix.fromBlocks
          (fun _ _ : PUnit => ((Real.sqrt ρ.hatFailureMass : ℝ) : ℂ))
          0 0 (psdSqrt ρ.matrix) *
        Matrix.fromBlocks
          (fun _ _ : PUnit => ((Real.sqrt σ.hatFailureMass : ℝ) : ℂ))
          0 0 (psdSqrt σ.matrix) :
        CMatrix (Sum PUnit a)) =
        Matrix.fromBlocks
          ((fun _ _ : PUnit => ((Real.sqrt ρ.hatFailureMass : ℝ) : ℂ)) *
            (fun _ _ : PUnit => ((Real.sqrt σ.hatFailureMass : ℝ) : ℂ)) :
            CMatrix PUnit)
          0 0 (psdSqrt ρ.matrix * psdSqrt σ.matrix) := by
    rw [Matrix.fromBlocks_multiply]
    ext x y
    cases x with
    | inl xi =>
        cases y with
        | inl yj =>
            cases xi
            cases yj
            simp [Matrix.mul_apply]
        | inr yj =>
            simp
    | inr xi =>
        cases y with
        | inl yj =>
            simp
        | inr yj =>
            simp [Matrix.mul_apply]
  rw [hprod]
  rw [Matrix.traceNorm_fromBlocks_diagonal]
  have hfail_prod_nonneg :
      0 ≤ Real.sqrt ρ.hatFailureMass * Real.sqrt σ.hatFailureMass :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hfail_norm :
      traceNorm
          ((fun _ _ : PUnit => ((Real.sqrt ρ.hatFailureMass : ℝ) : ℂ)) *
            (fun _ _ : PUnit => ((Real.sqrt σ.hatFailureMass : ℝ) : ℂ)) :
            CMatrix PUnit) =
        Real.sqrt ρ.hatFailureMass * Real.sqrt σ.hatFailureMass := by
    have hprod :
        ((fun _ _ : PUnit => ((Real.sqrt ρ.hatFailureMass : ℝ) : ℂ)) *
            (fun _ _ : PUnit => ((Real.sqrt σ.hatFailureMass : ℝ) : ℂ)) :
            CMatrix PUnit) =
          (fun _ _ : PUnit =>
            (((Real.sqrt ρ.hatFailureMass * Real.sqrt σ.hatFailureMass : ℝ)) : ℂ)) := by
      ext i j
      cases i
      cases j
      simp [← Complex.ofReal_mul]
    rw [hprod]
    exact traceNorm_punit_const_of_nonneg
      (Real.sqrt ρ.hatFailureMass * Real.sqrt σ.hatFailureMass) hfail_prod_nonneg
  rw [hfail_norm]
  have hsqrt_mul :
      Real.sqrt ((1 - ρ.matrix.trace.re) * (1 - σ.matrix.trace.re)) =
        Real.sqrt ρ.hatFailureMass * Real.sqrt σ.hatFailureMass := by
    rw [hatFailureMass, hatFailureMass]
    exact Real.sqrt_mul (sub_nonneg.mpr ρ.trace_le_one) _
  rw [hsqrt_mul]
  ring

/-! ## Trace-nonincreasing CP maps -/

/-- Apply a trace-nonincreasing completely positive matrix map to a
subnormalized state. -/
def applyTraceNonincreasingCP (ρ : SubnormalizedState a) (Φ : MatrixMap a b)
    (hΦ : MatrixMap.TraceNonincreasingCP Φ) : SubnormalizedState b where
  matrix := Φ ρ.matrix
  pos := hΦ.mapsPositive ρ.matrix ρ.pos
  trace_le_one := le_trans (hΦ.traceNonincreasing ρ.matrix ρ.pos) ρ.trace_le_one

@[simp]
theorem applyTraceNonincreasingCP_matrix (ρ : SubnormalizedState a)
    (Φ : MatrixMap a b) (hΦ : MatrixMap.TraceNonincreasingCP Φ) :
    (ρ.applyTraceNonincreasingCP Φ hΦ).matrix = Φ ρ.matrix :=
  rfl

theorem hatExtension_applyTraceNonincreasingCP (ρ : SubnormalizedState a)
    (Φ : MatrixMap a b) (hΦ : MatrixMap.TraceNonincreasingCP Φ) :
    (ρ.applyTraceNonincreasingCP Φ hΦ).hatExtension =
      hΦ.hatCompletion.applyState ρ.hatExtension := by
  classical
  apply State.ext
  change
    (ρ.applyTraceNonincreasingCP Φ hΦ).hatExtensionMatrix =
      hΦ.hatCompletion.map ρ.hatExtensionMatrix
  change
    (Matrix.fromBlocks (ρ.applyTraceNonincreasingCP Φ hΦ).hatFailureBlock 0 0
        (ρ.applyTraceNonincreasingCP Φ hΦ).matrix : CMatrix (Sum PUnit b)) =
      (MatrixMap.TraceNonincreasingCP.hatCompletion hΦ).map
        (Matrix.fromBlocks ρ.hatFailureBlock 0 0 ρ.matrix : CMatrix (Sum PUnit a))
  have hloss_trace :
      (ρ.matrix * hΦ.lossEffect).trace =
        ρ.matrix.trace - (Φ ρ.matrix).trace := by
    rw [MatrixMap.TraceNonincreasingCP.lossEffect, Matrix.mul_sub, Matrix.trace_sub,
      Matrix.mul_one]
    have hdual := MatrixMap.ofKraus_trace_duality hΦ.kraus ρ.matrix (1 : CMatrix b)
    have hmap : MatrixMap.ofKraus hΦ.kraus ρ.matrix = Φ ρ.matrix := by
      rw [hΦ.ofKraus_kraus]
    rw [Matrix.mul_one] at hdual
    rw [hmap] at hdual
    exact congrArg (fun z => ρ.matrix.trace - z) hdual.symm
  have hΦρ_im_zero : (Φ ρ.matrix).trace.im = 0 :=
    (Matrix.PosSemidef.trace_nonneg (hΦ.mapsPositive ρ.matrix ρ.pos)).2.symm
  have hfail :
      (ρ.applyTraceNonincreasingCP Φ hΦ).hatFailureBlock =
        (fun i j : PUnit =>
          ρ.hatFailureBlock i j + (ρ.matrix * hΦ.lossEffect).trace) := by
    ext i j
    cases i
    cases j
    apply Complex.ext
    · simp [hatFailureBlock, hatFailureMass, hloss_trace]
    · simp [hatFailureBlock, hatFailureMass, hloss_trace, ρ.trace_im_zero, hΦρ_im_zero]
  let S : CMatrix a := psdSqrt hΦ.lossEffect
  have hHermS : Matrix.conjTranspose S = S := by
    exact (psdSqrt_isHermitian hΦ.lossEffect).eq
  have hsqrtS : S * S = hΦ.lossEffect := by
    simpa [S] using psdSqrt_mul_self_of_posSemidef hΦ.lossEffect_posSemidef
  have hloss_kraus :
      (∑ x : a, ∑ x_1 : a,
          (∑ x_2 : a, psdSqrt hΦ.lossEffect x x_2 * ρ.matrix x_2 x_1) *
            (starRingEnd ℂ) (psdSqrt hΦ.lossEffect x x_1)) =
        (ρ.matrix * hΦ.lossEffect).trace := by
    calc
      (∑ x : a, ∑ x_1 : a,
          (∑ x_2 : a, psdSqrt hΦ.lossEffect x x_2 * ρ.matrix x_2 x_1) *
            (starRingEnd ℂ) (psdSqrt hΦ.lossEffect x x_1)) =
          (S * ρ.matrix * Matrix.conjTranspose S).trace := by
            simp [S, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
              Finset.sum_mul]
      _ = (Matrix.conjTranspose S * (S * ρ.matrix)).trace := by
            rw [Matrix.trace_mul_comm]
      _ = ((Matrix.conjTranspose S * S) * ρ.matrix).trace := by
            rw [← Matrix.mul_assoc]
      _ = (ρ.matrix * (Matrix.conjTranspose S * S)).trace := by
            rw [Matrix.trace_mul_comm]
      _ = (ρ.matrix * hΦ.lossEffect).trace := by
            rw [hHermS, hsqrtS]
  rw [hfail]
  apply Matrix.ext
  intro x y
  cases x with
  | inl xi =>
      cases y with
      | inl yj =>
          cases xi
          cases yj
          simp [applyTraceNonincreasingCP_matrix, MatrixMap.TraceNonincreasingCP.hatCompletion,
            MatrixMap.ofKraus, MatrixMap.TraceNonincreasingCP.hatCompletionKraus,
            Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Fintype.sum_sum_type, hloss_kraus]
          rfl
      | inr yj =>
          simp [applyTraceNonincreasingCP_matrix, MatrixMap.TraceNonincreasingCP.hatCompletion,
            MatrixMap.ofKraus, MatrixMap.TraceNonincreasingCP.hatCompletionKraus,
            Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Fintype.sum_sum_type]
  | inr xi =>
      cases y with
      | inl yj =>
          simp [applyTraceNonincreasingCP_matrix, MatrixMap.TraceNonincreasingCP.hatCompletion,
            MatrixMap.ofKraus, MatrixMap.TraceNonincreasingCP.hatCompletionKraus,
            Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Fintype.sum_sum_type]
      | inr yj =>
          calc
            (ρ.applyTraceNonincreasingCP Φ hΦ).matrix xi yj =
                MatrixMap.ofKraus hΦ.kraus ρ.matrix xi yj := by
              simp [applyTraceNonincreasingCP_matrix, hΦ.ofKraus_kraus]
            _ = (MatrixMap.ofKraus hΦ.hatCompletionKraus
                (Matrix.fromBlocks ρ.hatFailureBlock 0 0 ρ.matrix))
                (Sum.inr xi) (Sum.inr yj) := by
              simp [MatrixMap.ofKraus, MatrixMap.TraceNonincreasingCP.hatCompletionKraus,
                Matrix.sum_apply, Matrix.conjTranspose_apply, Matrix.mul_apply,
                Fintype.sum_sum_type]

end SubnormalizedState

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- View a normalized density state as a subnormalized state. -/
def toSubnormalized (ρ : State a) : SubnormalizedState a where
  matrix := ρ.matrix
  pos := ρ.pos
  trace_le_one := by
    rw [ρ.trace_eq_one]
    norm_num

@[simp]
theorem toSubnormalized_matrix (ρ : State a) :
    ρ.toSubnormalized.matrix = ρ.matrix := rfl

@[simp]
theorem toSubnormalized_trace (ρ : State a) :
    ρ.toSubnormalized.matrix.trace = 1 :=
  ρ.trace_eq_one

end State

theorem State.toSubnormalized_reindex_eq
    {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rho : State a) (e : a ≃ b) :
    (rho.reindex e).toSubnormalized =
      rho.toSubnormalized.applyTraceNonincreasingCP
        (Channel.reindex e).map (Channel.reindex e).traceNonincreasingCP_map := by
  apply SubnormalizedState.ext
  have h := congrArg State.matrix (Channel.reindex_applyState e rho)
  exact h.symm

namespace SubnormalizedState

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Drop the one-dimensional failure block from the hat extension, recovering a
subnormalized state on the original system. -/
def dropHatExtension (ρ : SubnormalizedState a) : SubnormalizedState a :=
  let ρhat : State (Sum PUnit.{u + 1} a) := ρ.hatExtension
  ρhat.toSubnormalized.applyTraceNonincreasingCP
    (MatrixMap.sumInrCompression (α := a))
    (MatrixMap.sumInrCompression_traceNonincreasingCP (α := a))

/-- Dropping the success block of a hat extension recovers the original
subnormalized state. -/
theorem dropHatExtension_eq (ρ : SubnormalizedState a) :
    ρ.dropHatExtension = ρ := by
  apply SubnormalizedState.ext
  ext i j
  simp [dropHatExtension, State.toSubnormalized, MatrixMap.sumInrCompression,
    SubnormalizedState.applyTraceNonincreasingCP]

end SubnormalizedState

end

end QIT
