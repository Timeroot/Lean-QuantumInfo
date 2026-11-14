/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Geometry.Fidelity
public import QIT.States.TraceNorm.Distance
public import QIT.States.Purification.PureGeometry
public import QIT.States.Purification.Uhlmann
import QIT.States.TraceNorm.Spectral
import QIT.States.TraceNorm.Audenaert
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Fuchs--van de Graaf inequality

## Lower bound `1 - F(ρ,σ) ≤ (1/2)·‖ρ-σ‖₁`

We use the already-formalized Audenaert trace inequality at `s = 1/2`:
`Re Tr(√ρ√σ) ≥ 1 - (1/2)‖ρ-σ‖₁`, then bound
`Re Tr(√ρ√σ) ≤ ‖√ρ√σ‖₁ = F(ρ,σ)` by the trace-norm variational theorem.

## Upper bound `(1/2)·‖ρ-σ‖₁ ≤ √(1 - F²)`

Requires Uhlmann's fidelity-maximisation (`QIT.States.Purification.Uhlmann`, proved),
trace-distance contraction under partial trace, and the pure-state formula
`‖|ψ⟩⟨ψ|-|φ⟩⟨φ|‖₁ = 2·√(1 - |⟨ψ|φ⟩|²)`.  Registered as
`m7-s0b-fuchs-vdG-upper`.
-/

@[expose] public section

namespace QIT

universe u v

noncomputable section

open scoped ComplexOrder MatrixOrder

variable {a : Type u} [Fintype a] [DecidableEq a]

private theorem partialTraceA_mul_kronecker_one
    {b : Type v} [Fintype b] (X : CMatrix (Prod a b)) (U : CMatrix b) :
    partialTraceA (a := a) (b := b) (X * Matrix.kronecker (1 : CMatrix a) U) =
      partialTraceA (a := a) (b := b) X * U := by
  ext j j'
  simp [partialTraceA, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem partialTraceA_mul_trace_eq_trace_mul_kronecker_one
    {b : Type v} [Fintype b] (X : CMatrix (Prod a b)) (U : CMatrix b) :
    ((partialTraceA (a := a) (b := b) X) * U).trace =
      (X * Matrix.kronecker (1 : CMatrix a) U).trace := by
  rw [← partialTraceA_mul_kronecker_one X U]
  exact partialTraceA_trace (a := a) (b := b)
    (X * Matrix.kronecker (1 : CMatrix a) U)

private theorem kronecker_one_mem_unitaryGroup
    {b : Type v} [Fintype b] [DecidableEq b] (U : Matrix.unitaryGroup b ℂ) :
    Matrix.kronecker (1 : CMatrix a) (U : CMatrix b) ∈
      Matrix.unitaryGroup (Prod a b) ℂ := by
  let I : Matrix.unitaryGroup a ℂ := ⟨1, by simp⟩
  simpa using Matrix.kronecker_mem_unitary I.2 U.2

/-- Trace norm is contractive under tracing out the first subsystem. -/
theorem traceNorm_partialTraceA_le
    {b : Type v} [Fintype b] [DecidableEq b] (X : CMatrix (Prod a b)) :
    traceNorm (partialTraceA (a := a) (b := b) X) ≤ traceNorm X := by
  classical
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace
    (partialTraceA (a := a) (b := b) X)
  let Ubig : Matrix.unitaryGroup (Prod a b) ℂ :=
    ⟨Matrix.kronecker (1 : CMatrix a) (U : CMatrix b), kronecker_one_mem_unitaryGroup U⟩
  calc
    traceNorm (partialTraceA (a := a) (b := b) X)
        = Complex.abs (((partialTraceA (a := a) (b := b) X) * (U : CMatrix b)).trace) :=
          hU.symm
    _ = Complex.abs ((X * (Ubig : CMatrix (Prod a b))).trace) := by
          congr 1
          simpa [Ubig] using partialTraceA_mul_trace_eq_trace_mul_kronecker_one X
            (U : CMatrix b)
    _ ≤ traceNorm X := traceNorm_variational_unitary_abs_trace_le X Ubig

namespace PureVector

private theorem state_sub_state_toEuclideanLin_mem_span
    (ψ φ : PureVector a) (x : EuclideanSpace ℂ a) :
    (ψ.state.matrix - φ.state.matrix).toEuclideanLin x ∈
      Submodule.span ℂ
        ({WithLp.toLp 2 ψ.amp, WithLp.toLp 2 φ.amp} : Set (EuclideanSpace ℂ a)) := by
  let cψ : ℂ := ∑ j, star (ψ.amp j) * x j
  let cφ : ℂ := ∑ j, star (φ.amp j) * x j
  have hx : (ψ.state.matrix - φ.state.matrix).toEuclideanLin x =
      cψ • WithLp.toLp 2 ψ.amp - cφ • WithLp.toLp 2 φ.amp := by
    ext i
    simp [Matrix.toEuclideanLin, Matrix.toLpLin, Matrix.mulVec, dotProduct,
      PureVector.state_matrix, rankOneMatrix_apply, cψ, cφ, Finset.mul_sum, mul_comm,
      mul_left_comm]
  rw [hx]
  exact Submodule.sub_mem _
    (Submodule.smul_mem _ cψ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ cφ (Submodule.subset_span (by simp)))

private theorem state_sub_state_toEuclideanLin_finrank_range_le_two (ψ φ : PureVector a) :
    Module.finrank ℂ
      (LinearMap.range (ψ.state.matrix - φ.state.matrix).toEuclideanLin) ≤ 2 := by
  let s : Finset (EuclideanSpace ℂ a) :=
    {WithLp.toLp 2 ψ.amp, WithLp.toLp 2 φ.amp}
  let S : Submodule ℂ (EuclideanSpace ℂ a) := Submodule.span ℂ (s : Set _)
  have hle : LinearMap.range (ψ.state.matrix - φ.state.matrix).toEuclideanLin ≤ S := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    simpa [S, s] using state_sub_state_toEuclideanLin_mem_span ψ φ x
  have hfin : Module.finrank ℂ S ≤ s.card := by
    simpa [S] using finrank_span_finset_le_card (R := ℂ) s
  have hcard : s.card ≤ 2 := by
    simpa [s] using
      (Finset.card_le_two (a := WithLp.toLp 2 ψ.amp) (b := WithLp.toLp 2 φ.amp))
  exact (Submodule.finrank_mono hle).trans (hfin.trans hcard)

/--
Pure-state trace distance is bounded by the usual root-overlap expression.

This is the hard algebraic ingredient for the Fuchs--van de Graaf upper
bound after Uhlmann's theorem reduces the general case to purifications.
-/
theorem normalizedTraceDistance_le_sqrt_one_sub_overlapSq (ψ φ : PureVector a) :
    ψ.state.normalizedTraceDistance φ.state ≤
      Real.sqrt (1 - ψ.overlapSq φ) := by
  let D : CMatrix a := ψ.state.matrix - φ.state.matrix
  have hDherm : D.IsHermitian := ψ.state.pos.isHermitian.sub φ.state.pos.isHermitian
  have hstar : star D = D := hDherm.eq
  have hhs : ((star D * D).trace).re = 2 * (1 - ψ.overlapSq φ) := by
    rw [hstar]
    exact state_sub_state_sq_trace_re_eq_two_mul_one_sub_overlapSq ψ φ
  have htrace_nonneg : 0 ≤ ((star D * D).trace).re :=
    (Matrix.PosSemidef.trace_nonneg (Matrix.posSemidef_conjTranspose_mul_self D)).1
  have hoverlap_nonneg : 0 ≤ 1 - ψ.overlapSq φ := by
    rw [hhs] at htrace_nonneg
    nlinarith
  have hsq_traceNorm : traceNorm D ^ 2 ≤ 4 * (1 - ψ.overlapSq φ) := by
    have hrank : (Module.finrank ℂ (LinearMap.range D.toEuclideanLin) : ℝ) ≤ 2 := by
      exact_mod_cast state_sub_state_toEuclideanLin_finrank_range_le_two ψ φ
    have hmain := traceNorm_sq_le_finrank_range_mul_hilbertSchmidt D
    calc
      traceNorm D ^ 2
          ≤ (Module.finrank ℂ (LinearMap.range D.toEuclideanLin) : ℝ) *
              ((star D * D).trace).re := hmain
      _ ≤ 2 * ((star D * D).trace).re := by
          exact mul_le_mul_of_nonneg_right hrank htrace_nonneg
      _ = 4 * (1 - ψ.overlapSq φ) := by
          rw [hhs]
          ring
  have hsq_normDist : ((1 / 2 : ℝ) * traceNorm D) ^ 2 ≤ 1 - ψ.overlapSq φ := by
    nlinarith
  rw [State.normalizedTraceDistance_eq_matrix, QIT.normalizedTraceDistance_eq]
  change (1 / 2 : ℝ) * traceNormDistance ψ.state.matrix φ.state.matrix ≤
      Real.sqrt (1 - ψ.overlapSq φ)
  rw [traceNormDistance]
  change (1 / 2 : ℝ) * traceNorm D ≤ Real.sqrt (1 - ψ.overlapSq φ)
  exact Real.le_sqrt_of_sq_le hsq_normDist

/-- Uhlmann purification selection upgraded to a pure-state trace-distance
bound.  Given a purification `Ψ` of `ρ` on a sufficiently large reference,
choose a purification `Φ` of `σ` whose squared overlap attains the squared
fidelity, then apply the pure-state trace-distance estimate.  This is the
generic purification bridge used by the ADHW FQSW Bob-isometry assembly. -/
theorem exists_purification_normalizedTraceDistance_le_sqrt_one_sub_squaredFidelity
    {r : Type v} [Fintype r] [DecidableEq r]
    {ρ σ : State a} {Ψ : PureVector (Prod r a)}
    (hΨ : Ψ.Purifies ρ) (hcard : Fintype.card a ≤ Fintype.card r) :
    ∃ Φ : PureVector (Prod r a),
      Φ.Purifies σ ∧
        Ψ.state.normalizedTraceDistance Φ.state ≤
          Real.sqrt (1 - ρ.squaredFidelity σ) := by
  obtain ⟨Φ, hΦ, hoverlap⟩ :=
    exists_purification_with_overlapSq_eq_squaredFidelity hΨ hcard
  refine ⟨Φ, hΦ, ?_⟩
  calc
    Ψ.state.normalizedTraceDistance Φ.state
        ≤ Real.sqrt (1 - Ψ.overlapSq Φ) :=
          normalizedTraceDistance_le_sqrt_one_sub_overlapSq Ψ Φ
    _ = Real.sqrt (1 - ρ.squaredFidelity σ) := by
          rw [hoverlap]

end PureVector

namespace State

/-- Squared fidelity between normalized finite-dimensional states is at most
one.  This follows from Uhlmann's overlap maximizer and nonnegativity of the
pure-state overlap deficit. -/
theorem squaredFidelity_le_one (ρ σ : State a) :
    ρ.squaredFidelity σ ≤ 1 := by
  classical
  obtain ⟨U, hUeq, _⟩ :=
    State.exists_referenceUnitary_canonicalPurification_overlapSq_eq_squaredFidelity ρ σ
  have hdeficit :
      0 ≤ 1 -
        ρ.canonicalPurification.overlapSq
          (U.applyPureVector σ.canonicalPurification) :=
    PureVector.one_sub_overlapSq_nonneg ρ.canonicalPurification
      (U.applyPureVector σ.canonicalPurification)
  rw [← hUeq] at hdeficit
  linarith

/-- Root fidelity between normalized finite-dimensional states is at most one. -/
theorem fidelity_le_one (ρ σ : State a) : ρ.fidelity σ ≤ 1 := by
  have hsq := squaredFidelity_le_one ρ σ
  rw [State.squaredFidelity_eq_fidelity_sq] at hsq
  have hnon := State.fidelity_nonneg ρ σ
  nlinarith [sq_nonneg (ρ.fidelity σ - 1)]

private theorem audenaert_half_ge_one_sub_normalizedTraceDistance (ρ σ : State a) :
    ((ρ.sqrtMatrix * σ.sqrtMatrix).trace).re ≥
      1 - ρ.normalizedTraceDistance σ := by
  have hAud := audenaertTraceInequality (a := a) (s := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) ρ.pos σ.pos
  have hpowρ : CFC.rpow ρ.matrix (1 / 2 : ℝ) = ρ.sqrtMatrix := by
    simp [State.sqrtMatrix, psdSqrt, CFC.sqrt_eq_rpow]
  have hpowσ : CFC.rpow σ.matrix (1 - (1 / 2 : ℝ)) = σ.sqrtMatrix := by
    norm_num
    simp [State.sqrtMatrix, psdSqrt, CFC.sqrt_eq_rpow]
  have hAud' :
      ((ρ.sqrtMatrix * σ.sqrtMatrix).trace).re ≥
        ((ρ.matrix + σ.matrix - CFC.abs (ρ.matrix - σ.matrix)).trace).re / 2 := by
    rw [hpowρ, hpowσ] at hAud
    exact hAud
  have hnorm : traceNorm (ρ.matrix - σ.matrix) =
      (CFC.abs (ρ.matrix - σ.matrix)).trace.re := by
    rfl
  have hrhs :
      ((ρ.matrix + σ.matrix - CFC.abs (ρ.matrix - σ.matrix)).trace).re / 2 =
        1 - ρ.normalizedTraceDistance σ := by
    rw [State.normalizedTraceDistance_eq_matrix, QIT.normalizedTraceDistance_eq]
    simp [QIT.traceNormDistance]
    rw [hnorm]
    simp [ρ.trace_eq_one, σ.trace_eq_one]
    ring
  exact hrhs ▸ hAud'

private theorem trace_re_sqrt_mul_sqrt_le_fidelity (ρ σ : State a) :
    ((ρ.sqrtMatrix * σ.sqrtMatrix).trace).re ≤ ρ.fidelity σ := by
  calc
    ((ρ.sqrtMatrix * σ.sqrtMatrix).trace).re
        ≤ Complex.abs ((ρ.sqrtMatrix * σ.sqrtMatrix).trace) := Complex.re_le_norm _
    _ = Complex.abs (((ρ.sqrtMatrix * σ.sqrtMatrix) * (1 : CMatrix a)).trace) := by
          simp
    _ ≤ traceNorm (ρ.sqrtMatrix * σ.sqrtMatrix) := by
          simpa using traceNorm_variational_unitary_abs_trace_le
            (ρ.sqrtMatrix * σ.sqrtMatrix) (1 : Matrix.unitaryGroup a ℂ)
    _ = ρ.fidelity σ := rfl

/--
Fuchs--van de Graaf lower bound, using the local root-fidelity convention.

This proof uses Audenaert's finite-dimensional trace inequality at `s = 1/2`
to get `Re Tr(√ρ√σ) ≥ 1 - D(ρ,σ)`, then bounds that real trace by root
fidelity through the trace-norm variational theorem.
-/
theorem fuchs_van_de_graaf_lower (ρ σ : State a) :
    1 - ρ.fidelity σ ≤ ρ.normalizedTraceDistance σ := by
  have hAud := audenaert_half_ge_one_sub_normalizedTraceDistance ρ σ
  have hF := trace_re_sqrt_mul_sqrt_le_fidelity ρ σ
  linarith

/-- Squared-fidelity deficit is controlled by twice the normalized trace
distance.  This is the scalar form used by Uhlmann-to-protocol conversions. -/
theorem one_sub_squaredFidelity_le_two_mul_normalizedTraceDistance (ρ σ : State a) :
    1 - ρ.squaredFidelity σ ≤ 2 * ρ.normalizedTraceDistance σ := by
  let F : ℝ := ρ.fidelity σ
  let D : ℝ := ρ.normalizedTraceDistance σ
  have hFnon : 0 ≤ F := by
    simpa [F] using State.fidelity_nonneg ρ σ
  have hFle : F ≤ 1 := by
    simpa [F] using State.fidelity_le_one ρ σ
  have hDnon : 0 ≤ D := by
    simpa [D] using State.normalizedTraceDistance_nonneg ρ σ
  have hdef : 1 - F ≤ D := by
    simpa [F, D] using State.fuchs_van_de_graaf_lower ρ σ
  have hone_add_nonneg : 0 ≤ 1 + F := by linarith
  have hone_add_le : 1 + F ≤ 2 := by linarith
  have hmul : (1 - F) * (1 + F) ≤ D * 2 :=
    mul_le_mul hdef hone_add_le hone_add_nonneg hDnon
  rw [State.squaredFidelity_eq_fidelity_sq]
  change 1 - F ^ 2 ≤ 2 * D
  nlinarith

/--
Fuchs--van de Graaf upper bound, using the local root-fidelity convention.

The proof is non-circular: Uhlmann chooses purifications attaining squared
fidelity, trace norm contracts under the reference partial trace, and the
remaining pure-state estimate is `PureVector.normalizedTraceDistance_le_sqrt_one_sub_overlapSq`.
-/
theorem fuchs_van_de_graaf_upper (ρ σ : State a) :
    ρ.normalizedTraceDistance σ ≤ Real.sqrt (1 - ρ.squaredFidelity σ) := by
  classical
  obtain ⟨U, hUeq, _⟩ :=
    State.exists_referenceUnitary_canonicalPurification_overlapSq_eq_squaredFidelity ρ σ
  let Ψ : PureVector (Prod a a) := ρ.canonicalPurification
  let Φ : PureVector (Prod a a) := U.applyPureVector σ.canonicalPurification
  let D : CMatrix (Prod a a) := Ψ.state.matrix - Φ.state.matrix
  have hΨ : Ψ.Purifies ρ := by
    simpa [Ψ] using ρ.canonicalPurification_purifies
  have hΦ : Φ.Purifies σ := by
    simpa [Φ] using U.toReferenceIsometry.applyPureVector_purifies σ.canonicalPurification_purifies
  have hdiff :
      ρ.matrix - σ.matrix = partialTraceA (a := a) (b := a) D := by
    change ρ.matrix - σ.matrix =
      partialTraceA (a := a) (b := a) (Ψ.state.matrix - Φ.state.matrix)
    rw [partialTraceA_sub, PureVector.partialTraceA_state_matrix_eq_of_purifies hΨ,
      PureVector.partialTraceA_state_matrix_eq_of_purifies hΦ]
  calc
    ρ.normalizedTraceDistance σ =
        (1 / 2 : ℝ) * traceNorm (ρ.matrix - σ.matrix) := by
          simp [State.normalizedTraceDistance, QIT.normalizedTraceDistance,
            QIT.traceNormDistance]
    _ = (1 / 2 : ℝ) * traceNorm (partialTraceA (a := a) (b := a) D) := by
          rw [hdiff]
    _ ≤ (1 / 2 : ℝ) * traceNorm D := by
          exact mul_le_mul_of_nonneg_left (traceNorm_partialTraceA_le D) (by norm_num)
    _ = Ψ.state.normalizedTraceDistance Φ.state := by
          simp [State.normalizedTraceDistance, QIT.normalizedTraceDistance,
            QIT.traceNormDistance, D]
    _ ≤ Real.sqrt (1 - Ψ.overlapSq Φ) :=
          PureVector.normalizedTraceDistance_le_sqrt_one_sub_overlapSq Ψ Φ
    _ = Real.sqrt (1 - ρ.squaredFidelity σ) := by
          rw [hUeq]

/-- Fuchs--van de Graaf inequalities, packaged together. -/
theorem fuchs_van_de_graaf (ρ σ : State a) :
    (1 - ρ.fidelity σ ≤ ρ.normalizedTraceDistance σ) ∧
      ρ.normalizedTraceDistance σ ≤ Real.sqrt (1 - ρ.squaredFidelity σ) :=
  ⟨fuchs_van_de_graaf_lower ρ σ, fuchs_van_de_graaf_upper ρ σ⟩

end State

namespace PureVector

/-- Uhlmann purification selection controlled directly by the normalized trace
distance of the purified marginal.  This is the scalar bridge used in the ADHW
FQSW route after the decoupling estimate: Fuchs--van de Graaf lower gives
`1 - F(ρ,σ) ≤ D(ρ,σ)`, `F ≤ 1` gives `1 - F(ρ,σ)^2 ≤ 2D(ρ,σ)`, and the
previous Uhlmann-to-pure-distance bridge finishes the estimate. -/
theorem exists_purification_normalizedTraceDistance_le_sqrt_two_mul_normalizedTraceDistance
    {r : Type v} [Fintype r] [DecidableEq r]
    {ρ σ : State a} {Ψ : PureVector (Prod r a)}
    (hΨ : Ψ.Purifies ρ) (hcard : Fintype.card a ≤ Fintype.card r) :
    ∃ Φ : PureVector (Prod r a),
      Φ.Purifies σ ∧
        Ψ.state.normalizedTraceDistance Φ.state ≤
          Real.sqrt (2 * ρ.normalizedTraceDistance σ) := by
  obtain ⟨Φ, hΦ, hdist⟩ :=
    exists_purification_normalizedTraceDistance_le_sqrt_one_sub_squaredFidelity hΨ hcard
  refine ⟨Φ, hΦ, hdist.trans ?_⟩
  exact Real.sqrt_le_sqrt
    (State.one_sub_squaredFidelity_le_two_mul_normalizedTraceDistance ρ σ)

/-- Uhlmann plus purification equivalence as a reference-isometry bridge.
Given an actual purification `Ψ` of `ρ` and an ideal purification `Θ` of `σ`,
choose a reference-side isometry from the actual reference to the ideal
reference so that the transformed actual pure state is close to the ideal pure
state.  The bound is controlled by the marginal normalized trace distance. -/
theorem exists_referenceIsometry_applyPureVector_normalizedTraceDistance_le_sqrt_two_mul_normalizedTraceDistance
    {r₁ : Type v} {r₂ : Type*} [Fintype r₁] [DecidableEq r₁]
    [Fintype r₂] [DecidableEq r₂]
    {ρ σ : State a} {Ψ : PureVector (Prod r₁ a)} {Θ : PureVector (Prod r₂ a)}
    (hΨ : Ψ.Purifies ρ) (hΘ : Θ.Purifies σ)
    (hcardTarget : Fintype.card a ≤ Fintype.card r₁)
    (hcardRef : Fintype.card r₁ ≤ Fintype.card r₂) :
    ∃ V : ReferenceIsometry r₁ r₂,
      (V.applyPureVector Ψ).state.normalizedTraceDistance Θ.state ≤
        Real.sqrt (2 * ρ.normalizedTraceDistance σ) := by
  obtain ⟨Φ, hΦ, hoverlap⟩ :=
    exists_purification_with_overlapSq_eq_squaredFidelity hΨ hcardTarget
  obtain ⟨V, hV⟩ :=
    exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state hΦ hΘ hcardRef
  refine ⟨V, ?_⟩
  calc
    (V.applyPureVector Ψ).state.normalizedTraceDistance Θ.state
        = (V.applyPureVector Ψ).state.normalizedTraceDistance
            (V.applyPureVector Φ).state := by
          rw [← hV]
    _ ≤ Real.sqrt (1 - (V.applyPureVector Ψ).overlapSq (V.applyPureVector Φ)) :=
          normalizedTraceDistance_le_sqrt_one_sub_overlapSq
            (V.applyPureVector Ψ) (V.applyPureVector Φ)
    _ = Real.sqrt (1 - Ψ.overlapSq Φ) := by
          rw [V.overlapSq_applyPureVector Ψ Φ]
    _ = Real.sqrt (1 - ρ.squaredFidelity σ) := by
          rw [hoverlap]
    _ ≤ Real.sqrt (2 * ρ.normalizedTraceDistance σ) :=
          Real.sqrt_le_sqrt
            (State.one_sub_squaredFidelity_le_two_mul_normalizedTraceDistance ρ σ)

end PureVector

end

end QIT
