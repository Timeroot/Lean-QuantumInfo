/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Subnormalized
public import QIT.States.TraceNorm.Spectral
public import QIT.Util.SDP.PSDCone
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Topology and compactness for subnormalized states

This module equips `SubnormalizedState a` with the topology induced by its
density matrix and proves the finite-dimensional compactness facts needed by
smooth one-shot optimization arguments.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open Matrix

namespace QIT

universe u v

noncomputable section

noncomputable local instance instCMatrixCStarAlgebraForSubnormalizedTopology
    (n : Type u) [Fintype n] [DecidableEq n] : CStarAlgebra (CMatrix n) := {}

namespace SubnormalizedState

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- The matrix-level subnormalized-state domain. -/
def subnormalizedMatrixSet (a : Type u) [Fintype a] : Set (CMatrix a) :=
  {M | M.PosSemidef ∧ M.trace.re ≤ 1}

omit [DecidableEq a] in
theorem mem_subnormalizedMatrixSet_iff {M : CMatrix a} :
    M ∈ subnormalizedMatrixSet a ↔ M.PosSemidef ∧ M.trace.re ≤ 1 :=
  Iff.rfl

/-- `SubnormalizedState a` carries the topology induced by its matrix field. -/
instance instTopologicalSpace : TopologicalSpace (SubnormalizedState a) :=
  TopologicalSpace.induced SubnormalizedState.matrix inferInstance

/-- The matrix projection from subnormalized states is continuous. -/
theorem continuous_matrix : Continuous (fun ρ : SubnormalizedState a => ρ.matrix) :=
  continuous_induced_dom

private theorem matrix_injective :
    Function.Injective (fun ρ : SubnormalizedState a => ρ.matrix) := by
  intro ρ σ hρσ
  exact ext hρσ

private theorem isEmbedding_matrix :
    Topology.IsEmbedding (fun ρ : SubnormalizedState a => ρ.matrix) :=
  Function.Injective.isEmbedding_induced matrix_injective

omit [DecidableEq a] in
/-- The matrix-level subnormalized-state domain is closed. -/
theorem subnormalizedMatrixSet_isClosed :
    IsClosed (subnormalizedMatrixSet a) := by
  classical
  have hpsd : IsClosed ({M : CMatrix a | M.PosSemidef} : Set (CMatrix a)) := by
    simpa using (psdCone a).isClosed
  have htrace :
      IsClosed ({M : CMatrix a | M.trace.re ≤ 1} : Set (CMatrix a)) := by
    exact isClosed_le
      (Complex.continuous_re.comp (Continuous.matrix_trace continuous_id))
      continuous_const
  have hset :
      subnormalizedMatrixSet a =
        ({M : CMatrix a | M.PosSemidef} ∩
          {M : CMatrix a | M.trace.re ≤ 1}) := by
    ext M
    rfl
  rw [hset]
  exact hpsd.inter htrace

/-- The matrix-level subnormalized-state domain is bounded. -/
theorem subnormalizedMatrixSet_isBounded :
    Bornology.IsBounded (subnormalizedMatrixSet a) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨‖(1 : CMatrix a)‖, ?_⟩
  intro M hM
  rcases hM with ⟨hMpsd, hMtr⟩
  have hnorm := State.norm_le_trace_re_mul_norm_one_of_posSemidef (a := a) hMpsd
  have htrace_bound :
      M.trace.re * ‖(1 : CMatrix a)‖ ≤ 1 * ‖(1 : CMatrix a)‖ :=
    mul_le_mul_of_nonneg_right hMtr (norm_nonneg _)
  exact le_trans hnorm (by simpa using htrace_bound)

/-- The matrix-level subnormalized-state domain is compact. -/
theorem subnormalizedMatrixSet_isCompact :
    IsCompact (subnormalizedMatrixSet a) :=
  Metric.isCompact_of_isClosed_isBounded subnormalizedMatrixSet_isClosed
    subnormalizedMatrixSet_isBounded

private theorem matrix_image_univ :
    (fun ρ : SubnormalizedState a => ρ.matrix) '' Set.univ =
      subnormalizedMatrixSet a := by
  ext M
  constructor
  · rintro ⟨ρ, -, rfl⟩
    exact ⟨ρ.pos, ρ.trace_le_one⟩
  · intro hM
    refine ⟨⟨M, hM.1, hM.2⟩, Set.mem_univ _, rfl⟩

/-- The full type of finite-dimensional subnormalized states is compact. -/
theorem isCompact_univ :
    IsCompact (Set.univ : Set (SubnormalizedState a)) := by
  rw [isEmbedding_matrix.isCompact_iff]
  rw [matrix_image_univ]
  exact subnormalizedMatrixSet_isCompact (a := a)

theorem traceNorm_continuous_forTopology :
    Continuous (traceNorm : CMatrix a → ℝ) := by
  have hgram : Continuous (fun M : CMatrix a => star M * M) := by
    exact (Continuous.star continuous_id).matrix_mul continuous_id
  have hnonneg : ∀ M : CMatrix a, (star M * M) ∈ {A : CMatrix a | 0 ≤ A} := by
    intro M
    exact Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.posSemidef_conjTranspose_mul_self M)
  have hsqrtOn :
      ContinuousOn (CFC.sqrt : CMatrix a → CMatrix a) {A : CMatrix a | 0 ≤ A} := by
    exact CFC.continuousOn_sqrt
  have hsqrt : Continuous (fun M : CMatrix a => CFC.sqrt (star M * M)) := by
    exact hsqrtOn.comp_continuous hgram hnonneg
  have htrace : Continuous (fun M : CMatrix a => (CFC.sqrt (star M * M)).trace) :=
    Continuous.matrix_trace hsqrt
  simpa [traceNorm, psdSqrt] using Complex.continuous_re.comp htrace

theorem continuous_psdSqrt_matrix :
    Continuous fun ρ : SubnormalizedState a => psdSqrt ρ.matrix := by
  have hsqrtOn :
      ContinuousOn (CFC.sqrt : CMatrix a → CMatrix a) {A : CMatrix a | 0 ≤ A} := by
    exact CFC.continuousOn_sqrt
  have hnonneg : ∀ ρ : SubnormalizedState a, ρ.matrix ∈ {A : CMatrix a | 0 ≤ A} := by
    intro ρ
    exact Matrix.nonneg_iff_posSemidef.mpr ρ.pos
  simpa [psdSqrt] using hsqrtOn.comp_continuous continuous_matrix hnonneg

/-- For fixed left input, generalized fidelity is continuous in the right
subnormalized state. -/
theorem continuous_generalizedFidelity_right (ρ : SubnormalizedState a) :
    Continuous fun σ : SubnormalizedState a => ρ.generalizedFidelity σ := by
  have hmul : Continuous fun σ : SubnormalizedState a =>
      psdSqrt ρ.matrix * psdSqrt σ.matrix :=
    continuous_const.matrix_mul continuous_psdSqrt_matrix
  have hnorm : Continuous fun σ : SubnormalizedState a =>
      traceNorm (psdSqrt ρ.matrix * psdSqrt σ.matrix) :=
    traceNorm_continuous_forTopology.comp hmul
  have htrace : Continuous fun σ : SubnormalizedState a => σ.matrix.trace.re :=
    Complex.continuous_re.comp (Continuous.matrix_trace continuous_matrix)
  have hslack : Continuous fun σ : SubnormalizedState a =>
      (1 - ρ.matrix.trace.re) * (1 - σ.matrix.trace.re) :=
    continuous_const.mul (continuous_const.sub htrace)
  have hsqrt : Continuous fun σ : SubnormalizedState a =>
      Real.sqrt ((1 - ρ.matrix.trace.re) * (1 - σ.matrix.trace.re)) :=
    Real.continuous_sqrt.comp hslack
  simpa [generalizedFidelity] using (hnorm.add hsqrt).pow 2

/-- For fixed left input, purified distance is continuous in the right
subnormalized state. -/
theorem continuous_purifiedDistance_right (ρ : SubnormalizedState a) :
    Continuous fun σ : SubnormalizedState a => ρ.purifiedDistance σ := by
  have hfid := continuous_generalizedFidelity_right (a := a) ρ
  simpa [purifiedDistance] using
    Real.continuous_sqrt.comp (continuous_const.sub hfid)

/-- A closed purified-distance ball in the subnormalized-state topology. -/
theorem purifiedBall_isClosed (ρ : SubnormalizedState a) (ε : ℝ) :
    IsClosed ({σ : SubnormalizedState a | ρ.purifiedBall ε σ}) := by
  simpa [purifiedBall] using
    isClosed_le (continuous_purifiedDistance_right (a := a) ρ) continuous_const

/-- A purified-distance ball is compact as a closed subset of the compact
subnormalized-state space. -/
theorem purifiedBall_isCompact (ρ : SubnormalizedState a) (ε : ℝ) :
    IsCompact ({σ : SubnormalizedState a | ρ.purifiedBall ε σ}) := by
  have hcompact :=
    (isCompact_univ (a := a)).inter_right (purifiedBall_isClosed (a := a) ρ ε)
  simpa [Set.univ_inter] using hcompact

section psdTraceBoundedMatrix

variable {b : Type v} [Fintype b] [DecidableEq b]

omit [Fintype a] [Fintype b] [DecidableEq b] in
/-- The map `T_B ↦ I_A ⊗ T_B` is continuous on side-information matrices. -/
theorem continuous_kronecker_one_matrix :
    Continuous fun T : CMatrix b => Matrix.kronecker (1 : CMatrix a) T := by
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro j
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
  exact continuous_const.mul
    ((continuous_apply j.2).comp ((continuous_apply i.2).comp continuous_id))

/-- PSD matrices with trace bounded by `R`. -/
def psdTraceBoundedMatrixSet (b : Type v) [Fintype b] (R : ℝ) : Set (CMatrix b) :=
  {T | T.PosSemidef ∧ T.trace.re ≤ R}

omit [DecidableEq b] in
theorem mem_psdTraceBoundedMatrixSet_iff {R : ℝ} {T : CMatrix b} :
    T ∈ psdTraceBoundedMatrixSet b R ↔ T.PosSemidef ∧ T.trace.re ≤ R :=
  Iff.rfl

omit [DecidableEq b] in
/-- The trace-bounded PSD matrix domain is closed. -/
theorem psdTraceBoundedMatrixSet_isClosed (R : ℝ) :
    IsClosed (psdTraceBoundedMatrixSet b R) := by
  classical
  have hpsd : IsClosed ({T : CMatrix b | T.PosSemidef} : Set (CMatrix b)) := by
    simpa using (psdCone b).isClosed
  have htrace :
      IsClosed ({T : CMatrix b | T.trace.re ≤ R} : Set (CMatrix b)) := by
    exact isClosed_le
      (Complex.continuous_re.comp (Continuous.matrix_trace continuous_id))
      continuous_const
  have hset :
      psdTraceBoundedMatrixSet b R =
        ({T : CMatrix b | T.PosSemidef} ∩
          {T : CMatrix b | T.trace.re ≤ R}) := by
    ext T
    rfl
  rw [hset]
  exact hpsd.inter htrace

/-- The trace-bounded PSD matrix domain is bounded. -/
theorem psdTraceBoundedMatrixSet_isBounded {R : ℝ} :
    Bornology.IsBounded (psdTraceBoundedMatrixSet b R) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨R * ‖(1 : CMatrix b)‖, ?_⟩
  intro T hT
  rcases hT with ⟨hTpsd, hTtrace⟩
  have hnorm := State.norm_le_trace_re_mul_norm_one_of_posSemidef (a := b) hTpsd
  have htrace_bound :
      T.trace.re * ‖(1 : CMatrix b)‖ ≤ R * ‖(1 : CMatrix b)‖ :=
    mul_le_mul_of_nonneg_right hTtrace (norm_nonneg _)
  exact le_trans hnorm htrace_bound

/-- The trace-bounded PSD matrix domain is compact. -/
theorem psdTraceBoundedMatrixSet_isCompact {R : ℝ} :
    IsCompact (psdTraceBoundedMatrixSet b R) :=
  Metric.isCompact_of_isClosed_isBounded
    (psdTraceBoundedMatrixSet_isClosed (b := b) R)
    (psdTraceBoundedMatrixSet_isBounded (b := b))

end psdTraceBoundedMatrix

end SubnormalizedState

end

end QIT
