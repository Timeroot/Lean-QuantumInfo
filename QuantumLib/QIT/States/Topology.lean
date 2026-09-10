/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Core.Pure
public import QuantumLib.QIT.States.SubnormalizedTopology
public import QuantumLib.QIT.States.Geometry.PurifiedDistance
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Topology for finite-dimensional states and kets

This module contains the canonical finite-dimensional topology attached to
density states and normalized kets.  High-level information-theoretic
modules should import this surface rather than introduce these global
instances themselves.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
open Matrix

noncomputable section
universe u v

open QIT

namespace MState

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- The matrix-level normalized-state domain. -/
def stateMatrixSet (a : Type u) [Fintype a] : Set (CMatrix a) :=
  {M | M.PosSemidef ∧ M.trace = 1}

omit [DecidableEq a] in
theorem mem_stateMatrixSet_iff {M : CMatrix a} :
    M ∈ stateMatrixSet a ↔ M.PosSemidef ∧ M.trace = 1 :=
  Iff.rfl

/-- The matrix projection from states is continuous. -/
@[fun_prop]
theorem continuous_matrix : Continuous (fun ρ : MState a => ρ.m) :=
  HermitianMat.continuous_mat.comp continuous_induced_dom

private theorem matrix_injective :
    Function.Injective (fun ρ : MState a => ρ.m) := by
  intro ρ σ hρσ
  exact ext hρσ

theorem isEmbedding_matrix :
    Topology.IsEmbedding (fun ρ : MState a => ρ.m) where
  eq_induced := by
    rw [show (fun ρ : MState a => ρ.m) = HermitianMat.mat ∘ DensityOp.M from rfl,
      ← induced_compose]
    rfl
  injective := matrix_injective

/-- A map into states is continuous as soon as the density matrices vary continuously. -/
theorem continuous_of_continuous_m {X : Type*} [TopologicalSpace X] {f : X → MState a}
    (hf : Continuous fun x => (f x).m) : Continuous f :=
  isEmbedding_matrix.continuous_iff.mpr hf

/-- A family of states converges as soon as its density matrices converge. -/
theorem tendsto_of_tendsto_m {X : Type*} {l : Filter X} {f : X → MState a} {ρ : MState a}
    (hf : Filter.Tendsto (fun x => (f x).m) l (nhds ρ.m)) : Filter.Tendsto f l (nhds ρ) :=
  isEmbedding_matrix.tendsto_nhds_iff.mpr hf

/-- Square-root matrices vary continuously along state paths. -/
theorem sqrtMatrix_tendsto_of_tendsto {X : Type*} {l : Filter X}
    {ρF : X → MState a} {ρ : MState a} (hρF : Filter.Tendsto ρF l (nhds ρ)) :
    Filter.Tendsto (fun x : X => (ρF x).sqrtMatrix) l (nhds ρ.sqrtMatrix) := by
  have hmatrix : Filter.Tendsto (fun x : X => (ρF x).m) l (nhds ρ.m) :=
    continuous_matrix.tendsto ρ |>.comp hρF
  have hpsd : ∀ᶠ x in l, (ρF x).m.PosSemidef :=
    Filter.Eventually.of_forall fun x => (ρF x).psd
  have hpow :=
    _root_.QIT.cMatrix_rpow_tendsto_of_tendsto_posSemidef
      (a := a) (p := (1 / 2 : ℝ)) (by norm_num) hmatrix hpsd ρ.psd
  simpa [MState.sqrtMatrix, psdSqrt, CFC.sqrt_eq_rpow] using hpow

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
    (fun ρ : MState a => ρ.m) '' Set.univ =
      stateMatrixSet a := by
  ext M
  constructor
  · rintro ⟨ρ, -, rfl⟩
    exact ⟨ρ.psd, ρ.tr'⟩
  · intro hM
    exact ⟨MState.ofMatrix M hM.1 hM.2, Set.mem_univ _, MState.matrix_ofMatrix _ _ _⟩

/-- The full type of finite-dimensional normalized states is compact. -/
theorem isCompact_univ :
    IsCompact (Set.univ : Set (MState a)) := by
  rw [isEmbedding_matrix.isCompact_iff]
  rw [matrix_image_univ]
  exact stateMatrixSet_isCompact (a := a)

/-- The embedding of a normalized state as a subnormalized state is continuous. -/
theorem continuous_toSubnormalized :
    Continuous (fun ρ : MState a => ρ.toSubnormalized) := by
  rw [continuous_induced_rng]
  change Continuous fun ρ : MState a => ρ.toSubnormalized.matrix
  simpa [MState.toSubnormalized_matrix] using continuous_matrix

/-- A closed purified-distance ball in the normalized-state topology. -/
theorem purifiedBall_isClosed (ρ : MState a) (ε : ℝ) :
    IsClosed ({σ : MState a | ρ.purifiedBall ε σ}) := by
  have hclosed :
      IsClosed
        ({σ : MState a |
          ρ.toSubnormalized.purifiedBall ε σ.toSubnormalized}) :=
    (SubnormalizedState.purifiedBall_isClosed (a := a) ρ.toSubnormalized ε).preimage
      MState.continuous_toSubnormalized
  have hset :
      {σ : MState a | ρ.purifiedBall ε σ} =
        {σ : MState a | ρ.toSubnormalized.purifiedBall ε σ.toSubnormalized} := by
    ext σ
    show ρ.purifiedBall ε σ ↔
      ρ.toSubnormalized.purifiedBall ε σ.toSubnormalized
    rw [MState.purifiedBall_eq, SubnormalizedState.purifiedBall_eq,
      MState.toSubnormalized_purifiedDistance_eq]
  rwa [hset]

/-- A purified-distance ball is compact as a closed subset of the compact
normalized-state space. -/
theorem purifiedBall_isCompact (ρ : MState a) (ε : ℝ) :
    IsCompact ({σ : MState a | ρ.purifiedBall ε σ}) := by
  have hcompact :=
    (MState.isCompact_univ (a := a)).inter_right (purifiedBall_isClosed (a := a) ρ ε)
  simpa [Set.univ_inter] using hcompact

variable {b : Type v} [Fintype b] [DecidableEq b]

/-- The first marginal is continuous in the density-matrix topology. -/
theorem traceRight_continuous :
    Continuous (fun ρ : MState (a × b) => ρ.traceRight) := by
  refine continuous_of_continuous_m ?_
  simp only [MState.traceRight_m]
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro i'
  simp only [Matrix.traceRight, Matrix.of_apply]
  refine continuous_finsetSum Finset.univ ?_
  intro j _
  exact (continuous_apply (i', j)).comp
    ((continuous_apply (i, j)).comp MState.continuous_matrix)

/-- The second marginal is continuous in the density-matrix topology. -/
theorem traceLeft_continuous :
    Continuous (fun ρ : MState (a × b) => ρ.traceLeft) := by
  refine continuous_of_continuous_m ?_
  simp only [MState.traceLeft_m]
  refine continuous_pi ?_
  intro j
  refine continuous_pi ?_
  intro j'
  simp only [Matrix.traceLeft, Matrix.of_apply]
  refine continuous_finsetSum Finset.univ ?_
  intro i _
  exact (continuous_apply (i, j')).comp
    ((continuous_apply (i, j)).comp MState.continuous_matrix)

end MState

namespace Ket

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Kets carry the topology induced by their amplitudes. -/
instance instTopologicalSpace : TopologicalSpace (Ket a) :=
  TopologicalSpace.induced Ket.vec inferInstance

omit [DecidableEq a] in
/-- The amplitude projection from normalized kets is continuous. -/
@[fun_prop]
theorem continuous_vec : Continuous (fun ψ : Ket a => ψ.vec) :=
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

/-- The state associated to a normalized ket is continuous. -/
theorem state_continuous : Continuous (fun ψ : Ket a => ψ.state) := by
  refine MState.continuous_of_continuous_m ?_
  simp only [Ket.state_matrix]
  exact rankOneMatrix_continuous.comp Ket.continuous_vec

/-- The amplitude vectors underlying normalized kets. -/
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
    Ket a ≃ {ψ : a → ℂ // ψ ∈ normalizedAmplitudeSet a} where
  toFun ψ := ⟨ψ.vec, ψ.trace_rankOne_eq_one⟩
  invFun ψ := Ket.ofRankOne ψ.1 ψ.2
  left_inv ψ := by
    cases ψ
    rfl
  right_inv ψ := by
    cases ψ
    rfl

private noncomputable def ampSubtypeHomeomorph :
    Ket a ≃ₜ {ψ : a → ℂ // ψ ∈ normalizedAmplitudeSet a} where
  toEquiv := ampSubtypeEquiv
  continuous_toFun := Ket.continuous_vec.subtype_mk fun ψ => ψ.trace_rankOne_eq_one
  continuous_invFun := by
    rw [continuous_induced_rng]
    change Continuous fun ψ : {ψ : a → ℂ // ψ ∈ normalizedAmplitudeSet a} => ψ.1
    exact continuous_subtype_val

/-- Finite-dimensional normalized kets form a compact space. -/
instance instCompactSpace : CompactSpace (Ket a) := by
  have : CompactSpace {ψ : a → ℂ // ψ ∈ normalizedAmplitudeSet a} :=
    isCompact_iff_compactSpace.mp normalizedAmplitudeSet_isCompact
  exact ampSubtypeHomeomorph.symm.compactSpace

end Ket
