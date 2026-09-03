/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Geometry.Fidelity
public import QIT.States.Purification.PureGeometry
public import QIT.States.Purification.Uhlmann
public import QIT.States.Subnormalized

/-!
# Purified distance

Foundational normalized and subnormalized purified-distance geometry. This
module contains the metric, its Uhlmann realization, symmetry and triangle
inequalities, and the normalized/subnormalized hat-extension bridge. Smooth
entropy optimization remains in `QIT.OneShot.Smooth`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

open Matrix

namespace QIT

universe u v

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

namespace State

/-- A normalized state satisfies the canonical subnormalized smoothing-radius
condition exactly when the radius is below one. -/
theorem epsilon_lt_sqrt_toSubnormalized_trace (rho : State a) {epsilon : ℝ}
    (hepsilon : epsilon < 1) :
    epsilon < Real.sqrt rho.toSubnormalized.matrix.trace.re := by
  rw [State.toSubnormalized_trace]
  simpa using hepsilon

/-- Purified distance between normalized finite-dimensional states,
`P(ρ,σ) = sqrt(1 - F(ρ,σ)^2)`, using the local squared-fidelity convention. -/
def purifiedDistance (ρ σ : State a) : ℝ :=
  Real.sqrt (1 - ρ.squaredFidelity σ)

@[simp]
theorem purifiedDistance_eq (ρ σ : State a) :
    ρ.purifiedDistance σ = Real.sqrt (1 - ρ.squaredFidelity σ) :=
  rfl

/-- The closed purified-distance epsilon ball around a normalized state. -/
def purifiedBall (ρ : State a) (ε : ℝ) (σ : State a) : Prop :=
  ρ.purifiedDistance σ ≤ ε

@[simp]
theorem purifiedBall_eq (ρ σ : State a) (ε : ℝ) :
    ρ.purifiedBall ε σ ↔ ρ.purifiedDistance σ ≤ ε :=
  Iff.rfl

/-- Purified-distance balls are monotone in the smoothing radius. -/
theorem purifiedBall_mono {ρ σ : State a} {ε δ : ℝ} (hεδ : ε ≤ δ) :
    ρ.purifiedBall ε σ → ρ.purifiedBall δ σ := by
  intro hball
  exact le_trans hball hεδ

/-- Purified distance is antitone in squared fidelity.

This is the algebraic handoff used by fidelity-monotonicity arguments: once a
map is known to increase squared fidelity, its output purified distance is
bounded by the input purified distance. -/
theorem purifiedDistance_le_of_squaredFidelity_le
    {b : Type v} [Fintype b] [DecidableEq b]
    {ρ σ : State a} {τ υ : State b}
    (hF : ρ.squaredFidelity σ ≤ τ.squaredFidelity υ) :
    τ.purifiedDistance υ ≤ ρ.purifiedDistance σ := by
  rw [State.purifiedDistance_eq, State.purifiedDistance_eq]
  exact Real.sqrt_le_sqrt (by linarith)

/-- The same squared-fidelity monotonicity handoff, phrased for purified balls. -/
theorem purifiedBall_of_squaredFidelity_le
    {b : Type v} [Fintype b] [DecidableEq b]
    {ρ σ : State a} {τ υ : State b} {ε : ℝ}
    (hF : ρ.squaredFidelity σ ≤ τ.squaredFidelity υ)
    (hball : ρ.purifiedBall ε σ) :
    τ.purifiedBall ε υ := by
  exact le_trans (purifiedDistance_le_of_squaredFidelity_le hF) hball

/-- Squared fidelity is symmetric, proved here from Uhlmann's purification
characterization so the basic purified-distance layer can use it without
importing endpoint trace-norm symmetry. -/
theorem squaredFidelity_comm_of_uhlmann (ρ σ : State a) :
    ρ.squaredFidelity σ = σ.squaredFidelity ρ := by
  let Ψ : PureVector (Prod a a) := ρ.canonicalPurification
  have hΨ : Ψ.Purifies ρ := by
    simpa [Ψ] using ρ.canonicalPurification_purifies
  obtain ⟨Φ, hΦ, hΦeq⟩ :=
    PureVector.exists_purification_with_overlapSq_eq_squaredFidelity
      (ρ := ρ) (σ := σ) hΨ (le_refl (Fintype.card a))
  have hle_forward : ρ.squaredFidelity σ ≤ σ.squaredFidelity ρ := by
    calc
      ρ.squaredFidelity σ = Ψ.overlapSq Φ := hΦeq.symm
      _ = Φ.overlapSq Ψ := PureVector.overlapSq_comm Φ Ψ
      _ ≤ σ.squaredFidelity ρ :=
          PureVector.overlapSq_le_squaredFidelity_of_purifies hΦ hΨ
  let Ω : PureVector (Prod a a) := σ.canonicalPurification
  have hΩ : Ω.Purifies σ := by
    simpa [Ω] using σ.canonicalPurification_purifies
  obtain ⟨Θ, hΘ, hΘeq⟩ :=
    PureVector.exists_purification_with_overlapSq_eq_squaredFidelity
      (ρ := σ) (σ := ρ) hΩ (le_refl (Fintype.card a))
  have hle_reverse : σ.squaredFidelity ρ ≤ ρ.squaredFidelity σ := by
    calc
      σ.squaredFidelity ρ = Ω.overlapSq Θ := hΘeq.symm
      _ = Θ.overlapSq Ω := PureVector.overlapSq_comm Θ Ω
      _ ≤ ρ.squaredFidelity σ :=
          PureVector.overlapSq_le_squaredFidelity_of_purifies hΘ hΩ
  exact le_antisymm hle_forward hle_reverse

/-- Squared fidelity is bounded by one. -/
theorem squaredFidelity_le_one_of_uhlmann (ρ σ : State a) :
    ρ.squaredFidelity σ ≤ 1 := by
  let Ψ : PureVector (Prod a a) := ρ.canonicalPurification
  have hΨ : Ψ.Purifies ρ := by
    simpa [Ψ] using ρ.canonicalPurification_purifies
  obtain ⟨Φ, _hΦ, hΦeq⟩ :=
    PureVector.exists_purification_with_overlapSq_eq_squaredFidelity
      (ρ := ρ) (σ := σ) hΨ (le_refl (Fintype.card a))
  have hoverlap := PureVector.one_sub_overlapSq_nonneg Ψ Φ
  rw [← hΦeq]
  linarith

/-- Purified distance is symmetric on normalized states. -/
theorem purifiedDistance_comm (ρ σ : State a) :
    σ.purifiedDistance ρ = ρ.purifiedDistance σ := by
  rw [State.purifiedDistance_eq, State.purifiedDistance_eq,
    squaredFidelity_comm_of_uhlmann σ ρ]

/-- Any two purifications give an upper bound on the purified distance of
their reduced states. -/
theorem purifiedDistance_le_sqrt_one_sub_overlapSq_of_purifies
    {r : Type v} [Fintype r] [DecidableEq r]
    {ρ σ : State a} {Ψ Φ : PureVector (Prod r a)}
    (hΨ : Ψ.Purifies ρ) (hΦ : Φ.Purifies σ) :
    ρ.purifiedDistance σ ≤ Real.sqrt (1 - Ψ.overlapSq Φ) := by
  rw [State.purifiedDistance_eq]
  exact Real.sqrt_le_sqrt (by
    have hF := PureVector.overlapSq_le_squaredFidelity_of_purifies hΨ hΦ
    linarith)

/-- Uhlmann's theorem, phrased directly for purified distance: for a fixed
purification of `ρ` on a large enough reference, one can choose a purification
of `σ` whose pure overlap realizes the purified distance. -/
theorem exists_purification_purifiedDistance_eq_sqrt_one_sub_overlapSq
    {r : Type v} [Fintype r] [DecidableEq r]
    {ρ σ : State a} {Ψ : PureVector (Prod r a)}
    (hΨ : Ψ.Purifies ρ) (hcard : Fintype.card a ≤ Fintype.card r) :
    ∃ Φ : PureVector (Prod r a),
      Φ.Purifies σ ∧
        ρ.purifiedDistance σ = Real.sqrt (1 - Ψ.overlapSq Φ) := by
  obtain ⟨Φ, hΦ, hΦeq⟩ :=
    PureVector.exists_purification_with_overlapSq_eq_squaredFidelity
      (ρ := ρ) (σ := σ) hΨ hcard
  refine ⟨Φ, hΦ, ?_⟩
  rw [State.purifiedDistance_eq, hΦeq]

/-- Purified distance satisfies the triangle inequality on normalized finite
states. -/
theorem purifiedDistance_triangle (ρ σ τ : State a) :
    ρ.purifiedDistance τ ≤ ρ.purifiedDistance σ + σ.purifiedDistance τ := by
  let Ψ : PureVector (Prod a a) := ρ.canonicalPurification
  have hΨ : Ψ.Purifies ρ := by
    simpa [Ψ] using ρ.canonicalPurification_purifies
  obtain ⟨Φ, hΦ, hρσ⟩ :=
    exists_purification_purifiedDistance_eq_sqrt_one_sub_overlapSq
      (ρ := ρ) (σ := σ) hΨ (le_refl (Fintype.card a))
  obtain ⟨Ω, hΩ, hστ⟩ :=
    exists_purification_purifiedDistance_eq_sqrt_one_sub_overlapSq
      (ρ := σ) (σ := τ) hΦ (le_refl (Fintype.card a))
  calc
    ρ.purifiedDistance τ ≤ Real.sqrt (1 - Ψ.overlapSq Ω) :=
      purifiedDistance_le_sqrt_one_sub_overlapSq_of_purifies hΨ hΩ
    _ ≤ Real.sqrt (1 - Ψ.overlapSq Φ) +
          Real.sqrt (1 - Φ.overlapSq Ω) :=
      PureVector.sqrt_one_sub_overlapSq_triangle Ψ Φ Ω
    _ = ρ.purifiedDistance σ + σ.purifiedDistance τ := by
      rw [← hρσ, ← hστ]

/-! ## Normalized/subnormalized purified-distance bridge -/

/-- Generalized fidelity reduces to squared fidelity for normalized states. -/
theorem toSubnormalized_generalizedFidelity_eq_squaredFidelity (ρ σ : State a) :
    ρ.toSubnormalized.generalizedFidelity σ.toSubnormalized = ρ.squaredFidelity σ := by
  rw [SubnormalizedState.generalizedFidelity_eq,
    State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq]
  have hρ : ρ.matrix.trace.re = 1 := by
    rw [ρ.trace_eq_one]
    norm_num
  have hσ : σ.matrix.trace.re = 1 := by
    rw [σ.trace_eq_one]
    norm_num
  simp [State.sqrtMatrix, hρ, hσ]

/-- The subnormalized purified distance agrees with the normalized one after
embedding normalized states via `State.toSubnormalized`. -/
theorem toSubnormalized_purifiedDistance_eq (ρ σ : State a) :
    ρ.toSubnormalized.purifiedDistance σ.toSubnormalized = ρ.purifiedDistance σ := by
  rw [SubnormalizedState.purifiedDistance_eq, State.purifiedDistance_eq,
    toSubnormalized_generalizedFidelity_eq_squaredFidelity]

end State

namespace PureVector

/-- The squared overlap of two pure vectors is bounded by the squared fidelity
of their rank-one states. -/
theorem overlapSq_le_state_squaredFidelity (Ψ Φ : PureVector a) :
    Ψ.overlapSq Φ ≤ Ψ.state.squaredFidelity Φ.state := by
  classical
  let e : a ≃ Prod PUnit.{u + 1} a := (Equiv.punitProd a).symm
  let Ψ' : PureVector (Prod PUnit.{u + 1} a) := Ψ.reindex e
  let Φ' : PureVector (Prod PUnit.{u + 1} a) := Φ.reindex e
  have hΨm : Ψ'.state.marginalB = Ψ.state := by
    apply State.ext
    ext i j
    simp [Ψ', e, PureVector.reindex_state, State.reindex, State.marginalB,
      partialTraceA, PureVector.state_matrix, rankOneMatrix_apply]
  have hΦm : Φ'.state.marginalB = Φ.state := by
    apply State.ext
    ext i j
    simp [Φ', e, PureVector.reindex_state, State.reindex, State.marginalB,
      partialTraceA, PureVector.state_matrix, rankOneMatrix_apply]
  have hΨpur : Ψ'.Purifies Ψ.state := by
    simpa [hΨm] using PureVector.purifies_marginalB Ψ'
  have hΦpur : Φ'.Purifies Φ.state := by
    simpa [hΦm] using PureVector.purifies_marginalB Φ'
  have hbound := PureVector.overlapSq_le_squaredFidelity_of_purifies hΨpur hΦpur
  simpa [Ψ', Φ', e, PureVector.overlapSq_reindex] using hbound

end PureVector

/-- Subnormalized purified distance agrees with normalized purified distance
after adjoining the one-dimensional failure register in the hat extension.
This is the purified-distance specialization of Tomamichel's hat route from
`metric.tex`, lines 512-513 and 584-604. -/
theorem SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension
    (ρ σ : SubnormalizedState a) :
    ρ.purifiedDistance σ =
      ρ.hatExtension.purifiedDistance σ.hatExtension := by
  rw [SubnormalizedState.purifiedDistance_eq, State.purifiedDistance_eq,
    SubnormalizedState.generalizedFidelity_eq_squaredFidelity_hatExtension]

/-- Subnormalized purified balls are exactly normalized purified balls after
hat extension. -/
theorem SubnormalizedState.purifiedBall_iff_hatExtension_purifiedBall
    (ρ σ : SubnormalizedState a) (ε : ℝ) :
    ρ.purifiedBall ε σ ↔ ρ.hatExtension.purifiedBall ε σ.hatExtension := by
  rw [SubnormalizedState.purifiedBall_eq, State.purifiedBall_eq,
    SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension]

/-- Purified distance is monotone under trace-nonincreasing completely positive
maps between subnormalized states. -/
theorem SubnormalizedState.purifiedDistance_mono_traceNonincreasingCP
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ σ : SubnormalizedState a) (Φ : MatrixMap a b)
    (hΦ : MatrixMap.TraceNonincreasingCP Φ) :
    (ρ.applyTraceNonincreasingCP Φ hΦ).purifiedDistance
        (σ.applyTraceNonincreasingCP Φ hΦ) ≤
      ρ.purifiedDistance σ := by
  let τ : SubnormalizedState b := ρ.applyTraceNonincreasingCP Φ hΦ
  let υ : SubnormalizedState b := σ.applyTraceNonincreasingCP Φ hΦ
  let ρhat : State (Sum PUnit.{max u v + 1} a) := ρ.hatExtension
  let σhat : State (Sum PUnit.{max u v + 1} a) := σ.hatExtension
  let τhat : State (Sum PUnit.{max u v + 1} b) := τ.hatExtension
  let υhat : State (Sum PUnit.{max u v + 1} b) := υ.hatExtension
  have hρP : ρ.purifiedDistance σ = ρhat.purifiedDistance σhat := by
    simpa [ρhat, σhat] using
      (SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension ρ σ)
  have hτP : τ.purifiedDistance υ = τhat.purifiedDistance υhat := by
    simpa [τhat, υhat] using
      (SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension τ υ)
  have hτhat : τhat = hΦ.hatCompletion.applyState ρhat := by
    simpa [τ, τhat, ρhat] using
      (SubnormalizedState.hatExtension_applyTraceNonincreasingCP ρ Φ hΦ)
  have hυhat : υhat = hΦ.hatCompletion.applyState σhat := by
    simpa [υ, υhat, σhat] using
      (SubnormalizedState.hatExtension_applyTraceNonincreasingCP σ Φ hΦ)
  change τ.purifiedDistance υ ≤ ρ.purifiedDistance σ
  rw [hτP, hρP, hτhat, hυhat]
  exact State.purifiedDistance_le_of_squaredFidelity_le
    (State.squaredFidelity_le_applyState_squaredFidelity hΦ.hatCompletion ρhat σhat)

/-- Trace-nonincreasing completely positive maps transport purified-distance
balls between subnormalized states. -/
theorem SubnormalizedState.purifiedBall_of_traceNonincreasingCP
    {b : Type v} [Fintype b] [DecidableEq b]
    {ρ σ : SubnormalizedState a} {ε : ℝ} (Φ : MatrixMap a b)
    (hΦ : MatrixMap.TraceNonincreasingCP Φ)
    (hball : ρ.purifiedBall ε σ) :
    (ρ.applyTraceNonincreasingCP Φ hΦ).purifiedBall ε
      (σ.applyTraceNonincreasingCP Φ hΦ) :=
  le_trans (SubnormalizedState.purifiedDistance_mono_traceNonincreasingCP ρ σ Φ hΦ) hball

/-- Relabeling normalized states transports their subnormalized
purified-distance ball without changing the radius. -/
theorem State.toSubnormalized_purifiedBall_reindex
    {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {rho sigma : State a} {epsilon : Real} (e : a ≃ b)
    (hball : rho.toSubnormalized.purifiedBall epsilon sigma.toSubnormalized) :
    (rho.reindex e).toSubnormalized.purifiedBall epsilon
      (sigma.reindex e).toSubnormalized := by
  simpa only [State.toSubnormalized_reindex_eq] using
    (SubnormalizedState.purifiedBall_of_traceNonincreasingCP
      (Channel.reindex e).map (Channel.reindex e).traceNonincreasingCP_map hball)

/-- Hat extension is injective on subnormalized states. -/
theorem SubnormalizedState.eq_of_hatExtension_eq {ρ σ : SubnormalizedState a}
    (h : ρ.hatExtension = σ.hatExtension) :
    ρ = σ := by
  apply SubnormalizedState.ext
  ext i j
  have hmatrix := congrArg State.matrix h
  have hentry :
      ρ.hatExtension.matrix (Sum.inr i) (Sum.inr j) =
        σ.hatExtension.matrix (Sum.inr i) (Sum.inr j) := by
    rw [hmatrix]
  simpa [SubnormalizedState.hatExtension_matrix,
    SubnormalizedState.hatExtensionMatrix_state_state] using hentry

/-- Subnormalized purified distance is symmetric via the normalized
hat-extension bridge. -/
theorem SubnormalizedState.purifiedDistance_comm
    (ρ σ : SubnormalizedState a) :
    σ.purifiedDistance ρ = ρ.purifiedDistance σ := by
  let ρhat : State (Sum PUnit.{u + 1} a) := ρ.hatExtension
  let σhat : State (Sum PUnit.{u + 1} a) := σ.hatExtension
  have hσρ : σ.purifiedDistance ρ = σhat.purifiedDistance ρhat := by
    simpa [σhat, ρhat] using
      (SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension
        (a := a) σ ρ)
  have hρσ : ρ.purifiedDistance σ = ρhat.purifiedDistance σhat := by
    simpa [ρhat, σhat] using
      (SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension
        (a := a) ρ σ)
  rw [hσρ, hρσ, State.purifiedDistance_comm ρhat σhat]

/-- Subnormalized purified distance satisfies the triangle inequality via the
normalized hat-extension bridge. -/
theorem SubnormalizedState.purifiedDistance_triangle
    (ρ σ τ : SubnormalizedState a) :
    ρ.purifiedDistance τ ≤ ρ.purifiedDistance σ + σ.purifiedDistance τ := by
  let ρhat : State (Sum PUnit.{u + 1} a) := ρ.hatExtension
  let σhat : State (Sum PUnit.{u + 1} a) := σ.hatExtension
  let τhat : State (Sum PUnit.{u + 1} a) := τ.hatExtension
  have hρτ : ρ.purifiedDistance τ = ρhat.purifiedDistance τhat := by
    simpa [ρhat, τhat] using
      (SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension
        (a := a) ρ τ)
  have hρσ : ρ.purifiedDistance σ = ρhat.purifiedDistance σhat := by
    simpa [ρhat, σhat] using
      (SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension
        (a := a) ρ σ)
  have hστ : σ.purifiedDistance τ = σhat.purifiedDistance τhat := by
    simpa [σhat, τhat] using
      (SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension
        (a := a) σ τ)
  rw [hρτ, hρσ, hστ]
  exact State.purifiedDistance_triangle ρhat σhat τhat

end

end QIT
