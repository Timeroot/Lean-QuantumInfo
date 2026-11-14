/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Pure
public import QIT.States.SubnormalizedTopology
public import QIT.States.Geometry.PurifiedDistance
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Topology for finite-dimensional states and pure vectors

This module contains the canonical finite-dimensional topology attached to
density states and normalized pure vectors.  High-level information-theoretic
modules should import this surface rather than introduce these global
instances themselves.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
open Matrix

namespace QIT

universe u v

noncomputable section

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- The matrix-level normalized-state domain. -/
def stateMatrixSet (a : Type u) [Fintype a] : Set (CMatrix a) :=
  {M | M.PosSemidef ∧ M.trace = 1}

omit [DecidableEq a] in
theorem mem_stateMatrixSet_iff {M : CMatrix a} :
    M ∈ stateMatrixSet a ↔ M.PosSemidef ∧ M.trace = 1 :=
  Iff.rfl

/-- States carry the topology induced by their density matrices. -/
instance instTopologicalSpace : TopologicalSpace (State a) :=
  TopologicalSpace.induced State.matrix inferInstance

/-- The matrix projection from states is continuous. -/
@[fun_prop]
theorem continuous_matrix : Continuous (fun ρ : State a => ρ.matrix) :=
  continuous_induced_dom

private theorem matrix_injective :
    Function.Injective (fun ρ : State a => ρ.matrix) := by
  intro ρ σ hρσ
  exact ext hρσ

theorem isEmbedding_matrix :
    Topology.IsEmbedding (fun ρ : State a => ρ.matrix) :=
  Function.Injective.isEmbedding_induced matrix_injective

/-- The matrix-level normalized-state domain is compact. -/
theorem stateMatrixSet_isCompact :
    IsCompact (stateMatrixSet a) := by
  have hsubcompact :
      IsCompact (SubnormalizedState.subnormalizedMatrixSet a) :=
    SubnormalizedState.subnormalizedMatrixSet_isCompact (a := a)
  have htrace_closed : IsClosed ({M : CMatrix a | M.trace = 1} : Set (CMatrix a)) := by
    exact isClosed_eq (Continuous.matrix_trace continuous_id) continuous_const
  have hset :
      stateMatrixSet a =
        SubnormalizedState.subnormalizedMatrixSet a ∩ {M : CMatrix a | M.trace = 1} := by
    ext M
    constructor
    · rintro ⟨hMpos, hMtrace⟩
      constructor
      · exact ⟨hMpos, by rw [hMtrace]; norm_num⟩
      · exact hMtrace
    · rintro ⟨hMsub, hMtrace⟩
      exact ⟨hMsub.1, hMtrace⟩
  rw [hset]
  exact hsubcompact.inter_right htrace_closed

private theorem matrix_image_univ :
    (fun ρ : State a => ρ.matrix) '' Set.univ =
      stateMatrixSet a := by
  ext M
  constructor
  · rintro ⟨ρ, -, rfl⟩
    exact ⟨ρ.pos, ρ.trace_eq_one⟩
  · intro hM
    refine ⟨⟨M, hM.1, hM.2⟩, Set.mem_univ _, rfl⟩

/-- The full type of finite-dimensional normalized states is compact. -/
theorem isCompact_univ :
    IsCompact (Set.univ : Set (State a)) := by
  rw [isEmbedding_matrix.isCompact_iff]
  rw [matrix_image_univ]
  exact stateMatrixSet_isCompact (a := a)

/-- Normalized states form a compact space in the density-matrix topology. -/
instance instCompactSpace : CompactSpace (State a) :=
  isCompact_univ_iff.mp isCompact_univ

/-- The embedding of a normalized state as a subnormalized state is continuous. -/
theorem continuous_toSubnormalized :
    Continuous (fun ρ : State a => ρ.toSubnormalized) := by
  rw [continuous_induced_rng]
  change Continuous fun ρ : State a => ρ.toSubnormalized.matrix
  simpa [State.toSubnormalized_matrix] using continuous_matrix

/-- A closed purified-distance ball in the normalized-state topology. -/
theorem purifiedBall_isClosed (ρ : State a) (ε : ℝ) :
    IsClosed ({σ : State a | ρ.purifiedBall ε σ}) := by
  have hclosed :
      IsClosed
        ({σ : State a |
          ρ.toSubnormalized.purifiedBall ε σ.toSubnormalized}) :=
    (SubnormalizedState.purifiedBall_isClosed (a := a) ρ.toSubnormalized ε).preimage
      State.continuous_toSubnormalized
  have hset :
      {σ : State a | ρ.purifiedBall ε σ} =
        {σ : State a | ρ.toSubnormalized.purifiedBall ε σ.toSubnormalized} := by
    ext σ
    show ρ.purifiedBall ε σ ↔
      ρ.toSubnormalized.purifiedBall ε σ.toSubnormalized
    rw [State.purifiedBall_eq, SubnormalizedState.purifiedBall_eq,
      State.toSubnormalized_purifiedDistance_eq]
  rwa [hset]

/-- A purified-distance ball is compact as a closed subset of the compact
normalized-state space. -/
theorem purifiedBall_isCompact (ρ : State a) (ε : ℝ) :
    IsCompact ({σ : State a | ρ.purifiedBall ε σ}) := by
  have hcompact :=
    (State.isCompact_univ (a := a)).inter_right (purifiedBall_isClosed (a := a) ρ ε)
  simpa [Set.univ_inter] using hcompact

variable {b : Type v} [Fintype b] [DecidableEq b]

/-- The first marginal is continuous in the density-matrix topology. -/
theorem marginalA_continuous :
    Continuous (fun ρ : State (Prod a b) => ρ.marginalA) := by
  rw [continuous_induced_rng]
  change Continuous fun ρ : State (Prod a b) =>
    partialTraceB (a := a) (b := b) ρ.matrix
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro i'
  simp only [partialTraceB]
  refine continuous_finsetSum Finset.univ ?_
  intro j _
  exact (continuous_apply (i', j)).comp
    ((continuous_apply (i, j)).comp State.continuous_matrix)

/-- The second marginal is continuous in the density-matrix topology. -/
theorem marginalB_continuous :
    Continuous (fun ρ : State (Prod a b) => ρ.marginalB) := by
  rw [continuous_induced_rng]
  change Continuous fun ρ : State (Prod a b) =>
    partialTraceA (a := a) (b := b) ρ.matrix
  refine continuous_pi ?_
  intro j
  refine continuous_pi ?_
  intro j'
  simp only [partialTraceA]
  refine continuous_finsetSum Finset.univ ?_
  intro i _
  exact (continuous_apply (i, j')).comp
    ((continuous_apply (i, j)).comp State.continuous_matrix)

end State

namespace PureVector

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Pure vectors carry the topology induced by their amplitudes. -/
instance instTopologicalSpace : TopologicalSpace (PureVector a) :=
  TopologicalSpace.induced PureVector.amp inferInstance

/-- The amplitude projection from normalized pure vectors is continuous. -/
@[fun_prop]
theorem continuous_amp : Continuous (fun ψ : PureVector a => ψ.amp) :=
  continuous_induced_dom

omit [Fintype a] [DecidableEq a] in
/-- The rank-one matrix kernel depends continuously on the amplitude vector. -/
theorem rankOneMatrix_continuous : Continuous (fun ψ : a → ℂ => rankOneMatrix ψ) := by
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro j
  simp only [rankOneMatrix_apply]
  exact (continuous_apply i).mul (continuous_star.comp (continuous_apply j))

/-- The state associated to a normalized pure vector is continuous. -/
theorem state_continuous : Continuous (fun ψ : PureVector a => ψ.state) := by
  rw [continuous_induced_rng]
  change Continuous fun ψ : PureVector a => rankOneMatrix ψ.amp
  exact rankOneMatrix_continuous.comp PureVector.continuous_amp

/-- The amplitude vectors underlying normalized pure vectors. -/
private def normalizedAmplitudeSet (a : Type u) [Fintype a] : Set (a → ℂ) :=
  {ψ | (rankOneMatrix ψ).trace = 1}

omit [DecidableEq a] in
private theorem trace_eq_sum_norm_sq {ψ : a → ℂ}
    (hψ : (rankOneMatrix ψ).trace = 1) :
    ∑ i, ‖ψ i‖ ^ 2 = (1 : ℝ) := by
  have hre := congrArg Complex.re hψ
  rw [rankOneMatrix_trace] at hre
  simp [dotProduct] at hre
  calc
    ∑ i, ‖ψ i‖ ^ 2 =
        ∑ i, ((ψ i).re * (ψ i).re + (ψ i).im * (ψ i).im) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Complex.sq_norm, Complex.normSq_apply]
    _ = 1 := hre

omit [DecidableEq a] in
private theorem norm_le_one_of_mem_normalizedAmplitudeSet
    {ψ : a → ℂ} (hψ : ψ ∈ normalizedAmplitudeSet a) (i : a) :
    ‖ψ i‖ ≤ 1 := by
  have hsum : ∑ j, ‖ψ j‖ ^ 2 = (1 : ℝ) :=
    trace_eq_sum_norm_sq hψ
  have hsingle : ‖ψ i‖ ^ 2 ≤ ∑ j, ‖ψ j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (‖ψ j‖)) (Finset.mem_univ i)
  have hsquare : ‖ψ i‖ ^ 2 ≤ 1 := by simpa [hsum] using hsingle
  exact (sq_le_one_iff₀ (norm_nonneg (ψ i))).mp hsquare

omit [DecidableEq a] in
private theorem normalizedAmplitudeSet_isClosed :
    IsClosed (normalizedAmplitudeSet a) := by
  unfold normalizedAmplitudeSet
  exact isClosed_eq (Continuous.matrix_trace rankOneMatrix_continuous) continuous_const

omit [DecidableEq a] in
private theorem normalizedAmplitudeSet_isBounded :
    Bornology.IsBounded (normalizedAmplitudeSet a) := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : a → ℂ)]
  refine ⟨1, ?_⟩
  intro ψ hψ
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  exact norm_le_one_of_mem_normalizedAmplitudeSet hψ i

omit [DecidableEq a] in
private theorem normalizedAmplitudeSet_isCompact :
    IsCompact (normalizedAmplitudeSet a) :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨normalizedAmplitudeSet_isClosed, normalizedAmplitudeSet_isBounded⟩

private def ampSubtypeEquiv :
    PureVector a ≃ {ψ : a → ℂ // ψ ∈ normalizedAmplitudeSet a} where
  toFun ψ := ⟨ψ.amp, ψ.trace_rankOne_eq_one⟩
  invFun ψ := ⟨ψ.1, ψ.2⟩
  left_inv ψ := by
    cases ψ
    rfl
  right_inv ψ := by
    cases ψ
    rfl

private noncomputable def ampSubtypeHomeomorph :
    PureVector a ≃ₜ {ψ : a → ℂ // ψ ∈ normalizedAmplitudeSet a} where
  toEquiv := ampSubtypeEquiv
  continuous_toFun := PureVector.continuous_amp.subtype_mk fun ψ => ψ.trace_rankOne_eq_one
  continuous_invFun := by
    rw [continuous_induced_rng]
    change Continuous fun ψ : {ψ : a → ℂ // ψ ∈ normalizedAmplitudeSet a} => ψ.1
    exact continuous_subtype_val

/-- Finite-dimensional normalized pure vectors form a compact space. -/
instance instCompactSpace : CompactSpace (PureVector a) := by
  haveI : CompactSpace {ψ : a → ℂ // ψ ∈ normalizedAmplitudeSet a} :=
    isCompact_iff_compactSpace.mp normalizedAmplitudeSet_isCompact
  exact ampSubtypeHomeomorph.symm.compactSpace

end PureVector

end

end QIT
