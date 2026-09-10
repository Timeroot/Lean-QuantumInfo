/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Symmetry.DeFinetti.ProfilesMixtures
public import QuantumLib.QIT.Util.MatrixInstances

/-!
# Operator domination and the trace-distance bounds it yields

`MState.MatrixDominatedBy ρ c σ` is `ρ.m ≤ c • σ.m` in the Loewner order.  It is what the
post-selection and de Finetti arguments carry around, because it propagates cheaply — it is
reflexive, transitive with the factors multiplying, monotone in the factor, and preserved by
applying the same channel to both sides — and because it converts to a metric statement at the
end: `normalizedTraceDistance_le_factor_sub_one_of_matrixDominatedBy` turns `ρ ≤ c σ` into
`T(ρ, σ) ≤ c - 1`, by testing the difference against the positive spectral projector of `ρ - σ`.

The reference state is `symmetricProjectionReferenceState n`, the symmetric projection on
`TensorPower a n` normalized to unit trace.  Any state supported on the symmetric subspace is
dominated by it with factor the number of type profiles, `Fintype.card (TensorPowerProfile a n)`,
and so with the polynomial factor `(n + 1) ^ Fintype.card a`.  Domination also survives permutation
twirling on the left whenever the target is permutation invariant, and is an equivalence there when
the dominated state is itself invariant.

The library has no diamond norm, so the channel-level conclusions are expression layers:
`ChannelOutputTraceDistanceBound` for a single pair of inputs, `AncillaChannelTraceDistanceBound`
uniformly over joint inputs with one reference register, and `DiamondTraceDistanceBound` uniformly
over all finite reference registers.

The de Finetti statements are phrased as predicates rather than proved here:
`IsDominatedByFiniteIidMixture`, `HasFiniteIidDomination`, the packaged witness
`FiniteIidDomination`, and `SymmetricFiniteIidDominationRoute`, which is the hypothesis that every
symmetric state has a finite IID domination with a given factor.  Anything supplying such a route —
a full de Finetti theorem being one — gets the approximation and channel-output corollaries from
the lemmas below.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal QIT.MatrixL2
open MeasureTheory

noncomputable section
universe u v w x
variable {ι : Type u} {a : Type v}
variable [Fintype ι] [Fintype a] [DecidableEq a]

open QIT

namespace QIT

end QIT

namespace MState

variable {n : ℕ}

/-- Normalized trace distance to a finite Renner `m`-IID mixture unfolds to
the matrix-level distance against the explicit finite barycenter. -/
theorem normalizedTraceDistance_finiteRennerMIIDMixture_state_eq
    {m r : ℕ} (ρ : MState (TensorPower a (m + r)))
    (M : FiniteRennerMIIDMixture ι a m r) :
    ρ.normalizedTraceDistance M.state =
      QIT.normalizedTraceDistance ρ.m
        (∑ i, (M.probs i) • (M.vectors i).state.m) := by
  rw [MState.normalizedTraceDistance_eq_matrix, M.state_matrix]

/-- The normalized symmetric-subspace projection state.

Its matrix is the symmetric projection `P_sym` divided by its trace.  This is
basic symmetric-subspace infrastructure, not the CKR mixed reference state from
the source theorem. -/
def symmetricProjectionReferenceState [Nonempty a] (n : ℕ) :
    MState (TensorPower a n) := .ofMatrix
  (matrix := ((Fintype.card (TensorPowerProfile a n) : ℝ)⁻¹) •
    symmetricProjectionMatrix (a := a) n)
  (pos := by
    exact (symmetricProjectionMatrix_posSemidef (a := a) n).smul
      (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (TensorPowerProfile a n)))))
  (trace_eq_one := by
    rw [Matrix.trace_smul, symmetricProjectionMatrix_trace_eq_profile_card]
    have hne : (Fintype.card (TensorPowerProfile a n) : ℂ) ≠ 0 := by
      exact_mod_cast TensorPowerProfile.card_ne_zero (a := a) n
    change ((Fintype.card (TensorPowerProfile a n) : ℝ)⁻¹ •
        (Fintype.card (TensorPowerProfile a n) : ℂ) = 1)
    rw [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
      inv_mul_cancel₀ hne])

@[simp]
theorem symmetricProjectionReferenceState_matrix [Nonempty a] (n : ℕ) :
    (symmetricProjectionReferenceState (a := a) n).m =
      ((Fintype.card (TensorPowerProfile a n) : ℝ)⁻¹) •
        symmetricProjectionMatrix (a := a) n :=
  MState.matrix_ofMatrix _ _ _

/-- A state is bounded by the symmetric Reynolds projection in the
positive-semidefinite order.

This is the support-shaped hypothesis needed for the finite-dimensional core
of the post-selection domination inequality. It is stronger than mere
permutation invariance: invariant mixed states may still have support outside
the symmetric subspace. -/
def SupportedOnSymmetricSubspace (ρ : MState (TensorPower a n)) : Prop :=
  ρ.m ≤ symmetricProjectionMatrix (a := a) n

theorem supportedOnSymmetricSubspace_iff (ρ : MState (TensorPower a n)) :
    ρ.SupportedOnSymmetricSubspace (a := a) ↔
      ρ.m ≤ symmetricProjectionMatrix (a := a) n := by
  rfl

/-- The normalized symmetric projection reference state is supported on the
symmetric tensor-power subspace. -/
theorem symmetricProjectionReferenceState_supportedOnSymmetricSubspace
    [Nonempty a] (n : ℕ) :
    (symmetricProjectionReferenceState (a := a) n).SupportedOnSymmetricSubspace
      (a := a) := by
  dsimp [SupportedOnSymmetricSubspace]
  rw [Matrix.le_iff]
  have hcard_one : (1 : ℝ) ≤ Fintype.card (TensorPowerProfile a n) := by
    exact_mod_cast Nat.succ_le_of_lt (TensorPowerProfile.card_pos (a := a) n)
  have hscale : 0 ≤ (1 : ℝ) - (Fintype.card (TensorPowerProfile a n) : ℝ)⁻¹ := by
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hcard_one)
  have hEq : symmetricProjectionMatrix (a := a) n -
      ((Fintype.card (TensorPowerProfile a n) : ℝ)⁻¹) •
        symmetricProjectionMatrix (a := a) n =
      ((1 : ℝ) - (Fintype.card (TensorPowerProfile a n) : ℝ)⁻¹) •
        symmetricProjectionMatrix (a := a) n := by
    rw [sub_smul, one_smul]
  rw [symmetricProjectionReferenceState_matrix, hEq]
  exact (symmetricProjectionMatrix_posSemidef (a := a) n).smul hscale

/-- Matrix domination of states in the positive-semidefinite order.

`ρ.MatrixDominatedBy c σ` means `ρ ≤ c σ` at the matrix level. This is the
operator-order expression used by post-selection/de Finetti domination bounds. -/
def MatrixDominatedBy (ρ : MState a) (c : ℝ) (σ : MState a) : Prop :=
  ρ.m ≤ (c : ℂ) • σ.m

theorem matrixDominatedBy_iff (ρ σ : MState a) (c : ℝ) :
    ρ.MatrixDominatedBy c σ ↔ ρ.m ≤ (c : ℂ) • σ.m := by
  rfl

/-- Every state is dominated by itself with factor `1`. -/
theorem matrixDominatedBy_refl (ρ : MState a) :
    ρ.MatrixDominatedBy 1 ρ := by
  simp [MatrixDominatedBy]

@[simp]
theorem symmetricProjectionReferenceState_matrixDominatedBy_self
    [Nonempty a] (n : ℕ) :
    (symmetricProjectionReferenceState (a := a) n).MatrixDominatedBy 1
      (symmetricProjectionReferenceState (a := a) n) :=
  matrixDominatedBy_refl (symmetricProjectionReferenceState (a := a) n)

/-- Equality gives domination with factor `1`. -/
theorem matrixDominatedBy_of_eq {ρ σ : MState a} (h : ρ = σ) :
    ρ.MatrixDominatedBy 1 σ := by
  subst h
  exact matrixDominatedBy_refl ρ

/-- Matrix domination is monotone in the scalar factor. -/
theorem matrixDominatedBy_mono_factor {ρ σ : MState a} {c d : ℝ}
    (h : ρ.MatrixDominatedBy c σ) (hcd : c ≤ d) :
    ρ.MatrixDominatedBy d σ := by
  dsimp [MatrixDominatedBy] at h ⊢
  exact le_trans h (by
    change (((d : ℂ) • σ.m) - ((c : ℂ) • σ.m)).PosSemidef
    convert σ.psd.smul (by exact_mod_cast sub_nonneg.mpr hcd) using 1
    ext i j
    simp [sub_smul])

/-- Core post-selection domination: any state already bounded by the symmetric
projection is dominated by the normalized symmetric reference state with factor
equal to the symmetric profile dimension. -/
theorem matrixDominatedBy_symmetricProjectionReferenceState_of_supported
    [Nonempty a] {ρ : MState (TensorPower a n)}
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    ρ.MatrixDominatedBy (Fintype.card (TensorPowerProfile a n) : ℝ)
      (symmetricProjectionReferenceState (a := a) n) := by
  dsimp [MatrixDominatedBy, SupportedOnSymmetricSubspace] at hρ ⊢
  convert hρ using 1
  have hne : (Fintype.card (TensorPowerProfile a n) : ℂ) ≠ 0 := by
    exact_mod_cast TensorPowerProfile.card_ne_zero (a := a) n
  rw [symmetricProjectionReferenceState_matrix]
  change (Fintype.card (TensorPowerProfile a n) : ℂ) •
      ((Fintype.card (TensorPowerProfile a n) : ℝ)⁻¹ •
        symmetricProjectionMatrix (a := a) n) =
    symmetricProjectionMatrix (a := a) n
  ext x y
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_natCast, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- Polynomial-factor form of the core post-selection domination inequality,
using the profile-count bound `(n+1)^|a|`. -/
theorem matrixDominatedBy_symmetricProjectionReferenceState_pow_succ_of_supported
    [Nonempty a] {ρ : MState (TensorPower a n)}
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    ρ.MatrixDominatedBy ((n + 1) ^ Fintype.card a : ℝ)
      (symmetricProjectionReferenceState (a := a) n) := by
  exact matrixDominatedBy_mono_factor
    (matrixDominatedBy_symmetricProjectionReferenceState_of_supported
      (a := a) hρ)
    (by exact_mod_cast tensorPowerProfile_card_le_pow_succ (a := a) n)

theorem symmetricProjectionReferenceState_matrixDominatedBy_profile_count
    [Nonempty a] (n : ℕ) :
    (symmetricProjectionReferenceState (a := a) n).MatrixDominatedBy
      (Fintype.card (TensorPowerProfile a n) : ℝ)
      (symmetricProjectionReferenceState (a := a) n) :=
  matrixDominatedBy_symmetricProjectionReferenceState_of_supported
    (a := a)
    (symmetricProjectionReferenceState_supportedOnSymmetricSubspace
      (a := a) n)

/-- Matrix domination composes multiplicatively in the scalar factor. -/
theorem matrixDominatedBy_trans {ρ σ τ : MState a} {c d : ℝ}
    (hc : 0 ≤ c) (hρσ : ρ.MatrixDominatedBy c σ)
    (hστ : σ.MatrixDominatedBy d τ) :
    ρ.MatrixDominatedBy (c * d) τ := by
  dsimp [MatrixDominatedBy] at hρσ hστ ⊢
  refine le_trans hρσ ?_
  change (((c * d : ℝ) : ℂ) • τ.m - (c : ℂ) • σ.m).PosSemidef
  have hsmul : (c • ((d : ℂ) • τ.m - σ.m)).PosSemidef :=
    (Matrix.le_iff.mp hστ).smul hc
  have hEq : c • ((d : ℂ) • τ.m - σ.m) =
      ((c * d : ℝ) : ℂ) • τ.m - (c : ℂ) • σ.m := by
    ext i j
    simp [Matrix.smul_apply, Matrix.sub_apply, Complex.real_smul, mul_sub, mul_assoc]
  rwa [hEq] at hsmul

/-- Matrix domination implies the corresponding trace inequality. -/
theorem matrixDominatedBy_trace_re_le {ρ σ : MState a} {c : ℝ}
    (hρσ : ρ.MatrixDominatedBy c σ) :
    ρ.m.trace.re ≤ c * σ.m.trace.re := by
  dsimp [MatrixDominatedBy] at hρσ
  have hnon : 0 ≤ ((((c : ℂ) • σ.m) - ρ.m).trace).re :=
    (Matrix.PosSemidef.trace_nonneg hρσ).1
  have htrace : ((((c : ℂ) • σ.m) - ρ.m).trace).re =
      c * σ.m.trace.re - ρ.m.trace.re := by
    simp [Matrix.trace_sub, Matrix.trace_smul]
  rw [htrace] at hnon
  linarith

/-- A domination factor between normalized states is necessarily at least
`1`. -/
theorem one_le_factor_of_matrixDominatedBy {ρ σ : MState a} {c : ℝ}
    (hρσ : ρ.MatrixDominatedBy c σ) :
    1 ≤ c := by
  have htrace := matrixDominatedBy_trace_re_le hρσ
  have hρtr : ρ.m.trace.re = 1 := by
    rw [ρ.tr']
    norm_num
  have hσtr : σ.m.trace.re = 1 := by
    rw [σ.tr']
    norm_num
  rw [hρtr, hσtr, mul_one] at htrace
  exact htrace

/-- Matrix domination by a normalized state gives a normalized trace-distance
bound.  This is the state-level norm expression used by post-selection-style
channel-output estimates: from `ρ ≤ c σ` one obtains
`T(ρ, σ) ≤ c - 1`. -/
theorem normalizedTraceDistance_le_factor_sub_one_of_matrixDominatedBy
    {ρ σ : MState a} {c : ℝ} (hρσ : ρ.MatrixDominatedBy c σ) :
    ρ.normalizedTraceDistance σ ≤ c - 1 := by
  let H : CMatrix a := ρ.m - σ.m
  have hH : H.IsHermitian := ρ.psd.isHermitian.sub σ.psd.isHermitian
  let P : CMatrix a := positiveSpectralProjector H hH
  have hPpos : P.PosSemidef := positiveSpectralProjector_posSemidef H hH
  have hPle : P ≤ 1 := positiveSpectralProjector_le_one H hH
  have hdiff_le : H ≤ ((c - 1 : ℝ) : ℂ) • σ.m := by
    dsimp [H]
    have hρσ_le : ρ.m ≤ (c : ℂ) • σ.m := by
      simpa [MatrixDominatedBy] using hρσ
    rw [Matrix.le_iff] at hρσ_le ⊢
    convert hρσ_le using 1
    ext i j
    simp [Matrix.smul_apply]
    ring
  have hscore :
      ((P * H).trace).re = (H⁺).trace.re := by
    rw [Matrix.trace_mul_comm P H]
    exact positiveSpectralProjector_score_eq_posPart_trace H hH
  have htrace_le :
      ((P * H).trace).re ≤ ((P * (((c - 1 : ℝ) : ℂ) • σ.m)).trace).re :=
    cMatrix_trace_mul_le_of_le_posSemidef_left hPpos hdiff_le
  have hσP_le_one : ((P * σ.m).trace).re ≤ 1 := by
    have h := cMatrix_trace_mul_le_of_le_posSemidef_left σ.psd hPle
    have hcomm : ((P * σ.m).trace).re = ((σ.m * P).trace).re := by
      rw [Matrix.trace_mul_comm P σ.m]
    have hone : ((σ.m * (1 : CMatrix a)).trace).re = 1 := by
      rw [Matrix.mul_one, σ.tr']
      norm_num
    calc
      ((P * σ.m).trace).re = ((σ.m * P).trace).re := hcomm
      _ ≤ ((σ.m * (1 : CMatrix a)).trace).re := h
      _ = 1 := hone
  have hc_nonneg : 0 ≤ c - 1 := sub_nonneg.mpr (one_le_factor_of_matrixDominatedBy hρσ)
  have hscaled :
      ((P * (((c - 1 : ℝ) : ℂ) • σ.m)).trace).re =
        (c - 1) * ((P * σ.m).trace).re := by
    rw [Matrix.mul_smul, Matrix.trace_smul]
    simp
  have hscaled_le :
      ((P * (((c - 1 : ℝ) : ℂ) • σ.m)).trace).re ≤ c - 1 := by
    rw [hscaled]
    have hmul := mul_le_mul_of_nonneg_left hσP_le_one hc_nonneg
    simpa [mul_one] using hmul
  rw [MState.normalizedTraceDistance_eq_posPart_trace]
  calc
    ((ρ.m - σ.m)⁺).trace.re = (H⁺).trace.re := by rfl
    _ = ((P * H).trace).re := hscore.symm
    _ ≤ ((P * (((c - 1 : ℝ) : ℂ) • σ.m)).trace).re := htrace_le
    _ ≤ c - 1 := hscaled_le

/-- Channel-output trace-distance bound associated to a chosen reference
output state. This is the trace-norm expression layer parallel to the matrix
domination post-selection bounds, phrased for the two output states a channel
produces from a fixed pair of inputs rather than as a supremum over all inputs
and references. -/
def ChannelOutputTraceDistanceBound {b : Type w} [Fintype b] [DecidableEq b]
    (Φ : CPTPMap a b) (ρ σ : MState a) (ε : ℝ) : Prop :=
  MState.normalizedTraceDistance (Φ ρ) (Φ σ) ≤ ε

/-- Matrix domination is preserved by applying the same channel to both
states. -/
theorem matrixDominatedBy_applyChannel {b : Type w} [Fintype b] [DecidableEq b]
    {ρ σ : MState a} {c : ℝ} (Φ : CPTPMap a b)
    (hρσ : ρ.MatrixDominatedBy c σ) :
    MState.MatrixDominatedBy (Φ ρ) c (Φ σ) := by
  dsimp [MatrixDominatedBy] at hρσ
  change (((c : ℂ) • (Φ σ).m) - (Φ ρ).m).PosSemidef
  simp only [CPTPOp.mat_coe_eq_apply_mat]
  have hpos := Φ.mapsPositive (((c : ℂ) • σ.m) - ρ.m) hρσ
  convert hpos using 1
  rw [map_sub, map_smul]

/-- Matrix domination gives a channel-output normalized trace-distance bound
after applying the same channel to both states. -/
theorem channelOutputTraceDistanceBound_of_matrixDominatedBy
    {b : Type w} [Fintype b] [DecidableEq b]
    {ρ σ : MState a} {c : ℝ} (Φ : CPTPMap a b)
    (hρσ : ρ.MatrixDominatedBy c σ) :
    ChannelOutputTraceDistanceBound Φ ρ σ (c - 1) :=
  normalizedTraceDistance_le_factor_sub_one_of_matrixDominatedBy
    (matrixDominatedBy_applyChannel Φ hρσ)

/-- Finite-reference channel-distance expression for a pair of channels.

This is the operational finite-ancilla layer underlying diamond-distance
statements: every joint input state on `A × R` is tested after applying either
channel to `A` and the identity channel to `R`. -/
def AncillaChannelTraceDistanceBound
    {b : Type w} [Fintype b] [DecidableEq b]
    {r : Type x} [Fintype r] [DecidableEq r]
    (Φ Ψ : CPTPMap a b) (ε : ℝ) : Prop :=
  ∀ ω : MState (a × r),
    MState.normalizedTraceDistance ((Φ.prod (CPTPOp.id (dIn := r))) ω)
      ((Ψ.prod (CPTPOp.id (dIn := r))) ω) ≤ ε

/-- Diamond-distance-shaped expression for a pair of finite-dimensional
channels, stated as a uniform bound over all finite reference systems.

This is an expression layer rather than a numeric norm API. -/
def DiamondTraceDistanceBound
    {b : Type w} [Fintype b] [DecidableEq b]
    (Φ Ψ : CPTPMap a b) (ε : ℝ) : Prop :=
  ∀ {r : Type x} [Fintype r] [DecidableEq r],
    AncillaChannelTraceDistanceBound (a := a) (b := b) (r := r) Φ Ψ ε

/-- A uniform matrix-domination bound on every finite-reference channel output
implies the corresponding diamond-distance-shaped trace-distance bound. -/
theorem diamondTraceDistanceBound_of_ancilla_matrixDominatedBy
    {b : Type w} [Fintype b] [DecidableEq b]
    {Φ Ψ : CPTPMap a b} {c : ℝ}
    (h : ∀ {r : Type x} [Fintype r] [DecidableEq r]
      (ω : MState (a × r)),
        MState.MatrixDominatedBy ((Φ.prod (CPTPOp.id (dIn := r))) ω) c
          ((Ψ.prod (CPTPOp.id (dIn := r))) ω)) :
    ∀ {r : Type x} [Fintype r] [DecidableEq r],
      AncillaChannelTraceDistanceBound (a := a) (b := b) (r := r) Φ Ψ (c - 1) := by
  intro r _ _ ω
  exact normalizedTraceDistance_le_factor_sub_one_of_matrixDominatedBy (h (r := r) ω)

/-- The de-Finetti/post-selection input-reference expression layer feeds the
numeric source-shaped diamond trace distance. -/
theorem diamondTraceDistance_le_of_inputReferenceBound [Nonempty a]
    {b : Type w} [Fintype b] [DecidableEq b]
    {Φ Ψ : CPTPMap a b} {ε : ℝ}
    (h : AncillaChannelTraceDistanceBound (a := a) (b := b) (r := a) Φ Ψ ε) :
    Φ.diamondTraceDistance Ψ ≤ ε :=
  CPTPOp.diamondTraceDistance_le_of_ancillaBound
    (a := a) (b := b) (Φ := Φ) (Ψ := Ψ) (ε := ε) h

/-- A universe-specialized de-Finetti/post-selection finite-ancilla expression
layer feeds the numeric source-shaped diamond trace distance. -/
theorem diamondTraceDistance_le_of_DiamondTraceDistanceBound [Nonempty a]
    {b : Type w} [Fintype b] [DecidableEq b]
    {Φ Ψ : CPTPMap a b} {ε : ℝ}
    (h : DiamondTraceDistanceBound.{v, w, v} (a := a) (b := b) Φ Ψ ε) :
    Φ.diamondTraceDistance Ψ ≤ ε :=
  diamondTraceDistance_le_of_inputReferenceBound
    (a := a) (b := b) (Φ := Φ) (Ψ := Ψ) (ε := ε) (h (r := a))

/-- Applying a channel to a state supported in the symmetric tensor-power
subspace gives the channel-output form of the core post-selection domination
bound with the exact profile-count factor. -/
theorem matrixDominatedBy_applyChannel_symmetricProjectionReferenceState_of_supported
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    {ρ : MState (TensorPower a n)} (Φ : CPTPMap (TensorPower a n) b)
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    MState.MatrixDominatedBy (Φ ρ)
      (Fintype.card (TensorPowerProfile a n) : ℝ)
      (Φ (symmetricProjectionReferenceState (a := a) n)) :=
  matrixDominatedBy_applyChannel Φ
    (matrixDominatedBy_symmetricProjectionReferenceState_of_supported
      (a := a) hρ)

/-- Polynomial-factor channel-output form of the core post-selection
domination bound. -/
theorem matrixDominatedBy_applyChannel_symmetricProjectionReferenceState_pow_succ_of_supported
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    {ρ : MState (TensorPower a n)} (Φ : CPTPMap (TensorPower a n) b)
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    MState.MatrixDominatedBy (Φ ρ) ((n + 1) ^ Fintype.card a : ℝ)
      (Φ (symmetricProjectionReferenceState (a := a) n)) :=
  matrixDominatedBy_applyChannel Φ
    (matrixDominatedBy_symmetricProjectionReferenceState_pow_succ_of_supported
      (a := a) hρ)

/-- Polynomial-factor trace-distance form of the state-level post-selection
bound for a supported symmetric input. -/
theorem stateLevelPostSelectionTraceDistanceBound_of_supported
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    {ρ : MState (TensorPower a n)} (Φ : CPTPMap (TensorPower a n) b)
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    ChannelOutputTraceDistanceBound Φ ρ
      (symmetricProjectionReferenceState (a := a) n)
      (((n + 1) ^ Fintype.card a : ℝ) - 1) :=
  channelOutputTraceDistanceBound_of_matrixDominatedBy Φ
    (matrixDominatedBy_symmetricProjectionReferenceState_pow_succ_of_supported
      (a := a) hρ)

/-- Exact profile-count trace-distance form of the state-level post-selection
bound for a supported symmetric input. -/
theorem stateLevelPostSelectionTraceDistanceBound_profile_count_of_supported
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    {ρ : MState (TensorPower a n)} (Φ : CPTPMap (TensorPower a n) b)
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    ChannelOutputTraceDistanceBound Φ ρ
      (symmetricProjectionReferenceState (a := a) n)
      ((Fintype.card (TensorPowerProfile a n) : ℝ) - 1) :=
  channelOutputTraceDistanceBound_of_matrixDominatedBy Φ
    (matrixDominatedBy_symmetricProjectionReferenceState_of_supported
      (a := a) hρ)

@[simp]
theorem symmetricProjectionReferenceState_applyChannel_matrixDominatedBy_self
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (Φ : CPTPMap (TensorPower a n) b) :
    MState.MatrixDominatedBy (Φ (symmetricProjectionReferenceState (a := a) n)) 1
      (Φ (symmetricProjectionReferenceState (a := a) n)) :=
  matrixDominatedBy_refl
    (Φ (symmetricProjectionReferenceState (a := a) n))

theorem symmetricProjectionReferenceState_applyChannel_matrixDominatedBy_profile_count
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (Φ : CPTPMap (TensorPower a n) b) :
    MState.MatrixDominatedBy (Φ (symmetricProjectionReferenceState (a := a) n))
      (Fintype.card (TensorPowerProfile a n) : ℝ)
      (Φ (symmetricProjectionReferenceState (a := a) n)) :=
  matrixDominatedBy_applyChannel Φ
    (symmetricProjectionReferenceState_matrixDominatedBy_profile_count
      (a := a) n)

/-- Matrix domination is preserved when both states are acted on by the same
tensor-factor permutation channel. -/
theorem matrixDominatedBy_apply_permutationChannel
    {ρ τ : MState (TensorPower a n)} {c : ℝ}
    (hρτ : ρ.MatrixDominatedBy c τ) (σ : Equiv.Perm (Fin n)) :
    MState.MatrixDominatedBy ((permutationChannel (a := a) n σ) ρ) c
      ((permutationChannel (a := a) n σ) τ) :=
  matrixDominatedBy_applyChannel (permutationChannel (a := a) n σ) hρτ

/-- Applying a tensor-factor permutation channel to the left side preserves
domination by a permutation-invariant target. -/
theorem matrixDominatedBy_apply_permutationChannel_of_target_invariant
    {ρ τ : MState (TensorPower a n)} {c : ℝ}
    (hτ : τ.IsPermutationInvariant (a := a)) (hρτ : ρ.MatrixDominatedBy c τ)
    (σ : Equiv.Perm (Fin n)) :
    MState.MatrixDominatedBy ((permutationChannel (a := a) n σ) ρ) c τ := by
  dsimp [MatrixDominatedBy] at hρτ
  change (((c : ℂ) • τ.m) -
    ((permutationChannel (a := a) n σ) ρ).m).PosSemidef
  simp only [CPTPOp.mat_coe_eq_apply_mat]
  have hpos := (permutationChannel (a := a) n σ).mapsPositive
    (((c : ℂ) • τ.m) - ρ.m) hρτ
  convert hpos using 1
  rw [map_sub, map_smul]
  have hτmatrix := congrArg DensityOp.m (hτ σ)
  rw [CPTPOp.mat_coe_eq_apply_mat] at hτmatrix
  rw [hτmatrix]

/-- Permutation twirling the left side preserves domination by a
permutation-invariant target. -/
theorem permutationTwirling_matrixDominatedBy_of_target_invariant
    {ρ τ : MState (TensorPower a n)} {c : ℝ}
    (hτ : τ.IsPermutationInvariant (a := a)) (hρτ : ρ.MatrixDominatedBy c τ) :
    ρ.permutationTwirling.MatrixDominatedBy c τ := by
  dsimp [MatrixDominatedBy]
  change (((c : ℂ) • τ.m) - ρ.permutationTwirling.m).PosSemidef
  let α : ℝ := (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      (((c : ℂ) • τ.m) -
        ((permutationChannel (a := a) n σ) ρ).m).PosSemidef := by
    intro σ
    exact matrixDominatedBy_apply_permutationChannel_of_target_invariant
      (a := a) hτ hρτ σ
  have hsum : (∑ σ : Equiv.Perm (Fin n), α •
      (((c : ℂ) • τ.m) -
        ((permutationChannel (a := a) n σ) ρ).m)).PosSemidef := by
    exact Matrix.posSemidef_sum Finset.univ fun σ _ =>
      (hterm σ).smul (inv_nonneg.mpr
        (Nat.cast_nonneg (Fintype.card (Equiv.Perm (Fin n)))))
  convert hsum using 1
  rw [MState.permutationTwirling_matrix]
  change ((c : ℂ) • τ.m) -
      (α • ∑ σ : Equiv.Perm (Fin n),
        ((permutationChannel (a := a) n σ) ρ).m) =
    ∑ σ : Equiv.Perm (Fin n), α •
      (((c : ℂ) • τ.m) -
        ((permutationChannel (a := a) n σ) ρ).m)
  have hcoeff :
      (∑ _σ : Equiv.Perm (Fin n), α • ((c : ℂ) • τ.m)) =
        ((c : ℂ) • τ.m) := by
    rw [← Finset.sum_smul]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hα : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * α = 1 := by
      dsimp [α]
      field_simp [Nat.cast_ne_zero.mpr
        (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin n)) ≠ 0)]
    rw [hα, one_smul]
  calc
    ((c : ℂ) • τ.m) -
        (α • ∑ σ : Equiv.Perm (Fin n),
          ((permutationChannel (a := a) n σ) ρ).m)
        = (∑ _σ : Equiv.Perm (Fin n), α • ((c : ℂ) • τ.m)) -
          (α • ∑ σ : Equiv.Perm (Fin n),
            ((permutationChannel (a := a) n σ) ρ).m) := by
            rw [hcoeff]
    _ = (∑ _σ : Equiv.Perm (Fin n), α • ((c : ℂ) • τ.m)) -
          (∑ σ : Equiv.Perm (Fin n), α •
            ((permutationChannel (a := a) n σ) ρ).m) := by
            rw [Finset.smul_sum]
    _ = ∑ σ : Equiv.Perm (Fin n), (α • ((c : ℂ) • τ.m) -
          α • ((permutationChannel (a := a) n σ) ρ).m) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ σ : Equiv.Perm (Fin n), α •
          (((c : ℂ) • τ.m) -
            ((permutationChannel (a := a) n σ) ρ).m) := by
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [smul_sub]

/-- Permutation twirling preserves matrix domination when applied to both
sides. -/
theorem permutationTwirling_matrixDominatedBy
    {ρ τ : MState (TensorPower a n)} {c : ℝ}
    (hρτ : ρ.MatrixDominatedBy c τ) :
    ρ.permutationTwirling.MatrixDominatedBy c τ.permutationTwirling := by
  dsimp [MatrixDominatedBy]
  change (((c : ℂ) • τ.permutationTwirling.m) -
    ρ.permutationTwirling.m).PosSemidef
  let α : ℝ := (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      (((c : ℂ) • ((permutationChannel (a := a) n σ) τ).m) -
        ((permutationChannel (a := a) n σ) ρ).m).PosSemidef := by
    intro σ
    exact matrixDominatedBy_apply_permutationChannel (a := a) hρτ σ
  have hsum : (∑ σ : Equiv.Perm (Fin n), α •
      (((c : ℂ) • ((permutationChannel (a := a) n σ) τ).m) -
        ((permutationChannel (a := a) n σ) ρ).m)).PosSemidef := by
    exact Matrix.posSemidef_sum Finset.univ fun σ _ =>
      (hterm σ).smul (inv_nonneg.mpr
        (Nat.cast_nonneg (Fintype.card (Equiv.Perm (Fin n)))))
  convert hsum using 1
  ext x y
  simp only [MState.permutationTwirling_matrix, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.sub_apply, smul_sub, Finset.sum_sub_distrib]
  simp [Finset.mul_sum, mul_left_comm, α]

/-- If an invariant state's twirling is dominated by a target, then the state
itself is dominated by that target. -/
theorem matrixDominatedBy_of_permutationTwirling_left
    {ρ τ : MState (TensorPower a n)} {c : ℝ}
    (hρ : ρ.IsPermutationInvariant (a := a))
    (h : ρ.permutationTwirling.MatrixDominatedBy c τ) :
    ρ.MatrixDominatedBy c τ := by
  rwa [MState.permutationTwirling_apply_of_isPermutationInvariant (a := a) hρ] at h

/-- For a permutation-invariant state, domination can be checked after
twirling the left side. -/
theorem matrixDominatedBy_twirling_left_iff_of_invariant
    {ρ τ : MState (TensorPower a n)} {c : ℝ}
    (hρ : ρ.IsPermutationInvariant (a := a)) :
    ρ.permutationTwirling.MatrixDominatedBy c τ ↔ ρ.MatrixDominatedBy c τ := by
  rw [MState.permutationTwirling_apply_of_isPermutationInvariant (a := a) hρ]

/-- A state is dominated by a specified finite IID mixture if its matrix is
bounded by a constant multiple of the mixture state's matrix. -/
def IsDominatedByFiniteIidMixture (ρ : MState (TensorPower a n)) (c : ℝ)
    (M : FiniteIidMixture ι a n) : Prop :=
  ρ.MatrixDominatedBy c M.state

theorem isDominatedByFiniteIidMixture_iff (ρ : MState (TensorPower a n)) (c : ℝ)
    (M : FiniteIidMixture ι a n) :
    ρ.IsDominatedByFiniteIidMixture c M ↔
      ρ.m ≤ (c : ℂ) • M.state.m := by
  rfl

/-- Existence of some finite IID mixture dominating a tensor-power state.

This is the de Finetti representation entrypoint shape. A full de Finetti
theorem would prove this predicate, with a source-specific factor, for the
appropriate class of symmetric states. -/
def HasFiniteIidDomination (ρ : MState (TensorPower a n)) (c : ℝ) : Prop :=
  ∃ M : FiniteIidMixture ι a n, ρ.IsDominatedByFiniteIidMixture c M

/-- Existence of some finite IID mixture approximating a tensor-power state in
normalized trace distance. -/
def HasFiniteIidMixtureApproximation (ρ : MState (TensorPower a n)) (ε : ℝ) : Prop :=
  ∃ M : FiniteIidMixture ι a n, ρ.normalizedTraceDistance M.state ≤ ε

/-- Existence of a finite IID mixture whose channel image approximates the
channel image of a tensor-power state in normalized trace distance. -/
def HasFiniteIidChannelOutputApproximation
    {b : Type w} [Fintype b] [DecidableEq b]
    (ρ : MState (TensorPower a n)) (Φ : CPTPMap (TensorPower a n) b)
    (ε : ℝ) : Prop :=
  ∃ M : FiniteIidMixture ι a n, ChannelOutputTraceDistanceBound Φ ρ M.state ε

/-- A packaged finite-IID-mixture domination witness for a tensor-power state.

This is an expression layer for de Finetti/post-selection routes: it packages a
finite IID mixture together with the hard matrix-domination proof. It does not
assert that every symmetric state has such a witness. -/
structure FiniteIidDomination (ρ : MState (TensorPower a n)) (c : ℝ) where
  /-- The finite IID mixture that serves as the reference state. -/
  mixture : FiniteIidMixture ι a n
  /-- The dominated state is bounded by the mixture at matrix level. -/
  domination : ρ.IsDominatedByFiniteIidMixture c mixture

namespace FiniteIidDomination

/-- A finite-IID domination witness gives the channel-output matrix domination
bound for any finite output channel. -/
theorem applyChannel_matrixDominatedBy
    {ρ : MState (TensorPower a n)} {c : ℝ}
    (W : ρ.FiniteIidDomination (ι := ι) c)
    {b : Type w} [Fintype b] [DecidableEq b]
    (Φ : CPTPMap (TensorPower a n) b) :
    MState.MatrixDominatedBy (Φ ρ) c (Φ W.mixture.state) :=
  matrixDominatedBy_applyChannel Φ W.domination

/-- A finite-IID domination witness gives a channel-output normalized
trace-distance bound for any finite output channel. -/
theorem applyChannel_traceDistanceBound
    {ρ : MState (TensorPower a n)} {c : ℝ}
    (W : ρ.FiniteIidDomination (ι := ι) c)
    {b : Type w} [Fintype b] [DecidableEq b]
    (Φ : CPTPMap (TensorPower a n) b) :
    ChannelOutputTraceDistanceBound Φ ρ W.mixture.state (c - 1) :=
  channelOutputTraceDistanceBound_of_matrixDominatedBy Φ W.domination

end FiniteIidDomination

/-- A packaged finite-IID domination witness gives the existential de Finetti
domination entrypoint. -/
theorem hasFiniteIidDomination_of_witness
    {ρ : MState (TensorPower a n)} {c : ℝ}
    (W : ρ.FiniteIidDomination (ι := ι) c) :
    ρ.HasFiniteIidDomination (ι := ι) c := by
  exact ⟨W.mixture, W.domination⟩

/-- Tensor-power states have the one-point finite-IID domination witness. -/
def FiniteIidDomination.onePoint (ρ : MState a) (n : ℕ) :
    (ρ.tensorPower n).FiniteIidDomination (ι := PUnit) 1 where
  mixture := FiniteIidMixture.onePoint (a := a) ρ n
  domination := by
    exact matrixDominatedBy_of_eq
      (FiniteIidMixture.onePoint_state (a := a) ρ n).symm

/-- Finite-IID domination implies finite-IID approximation in normalized trace
distance with loss `c - 1`. -/
theorem hasFiniteIidMixtureApproximation_of_hasFiniteIidDomination
    {ρ : MState (TensorPower a n)} {c : ℝ}
    (hρ : ρ.HasFiniteIidDomination (ι := ι) c) :
    ρ.HasFiniteIidMixtureApproximation (ι := ι) (c - 1) := by
  rcases hρ with ⟨M, hρM⟩
  exact ⟨M, normalizedTraceDistance_le_factor_sub_one_of_matrixDominatedBy hρM⟩

/-- Finite-IID domination implies a finite-IID channel-output approximation
after applying any finite output channel. -/
theorem hasFiniteIidChannelOutputApproximation_of_hasFiniteIidDomination
    {ρ : MState (TensorPower a n)} {c : ℝ}
    (hρ : ρ.HasFiniteIidDomination (ι := ι) c)
    {b : Type w} [Fintype b] [DecidableEq b]
    (Φ : CPTPMap (TensorPower a n) b) :
    ρ.HasFiniteIidChannelOutputApproximation (ι := ι) Φ (c - 1) := by
  rcases hρ with ⟨M, hρM⟩
  exact ⟨M, channelOutputTraceDistanceBound_of_matrixDominatedBy Φ hρM⟩

/-- Route predicate for finite-IID domination of symmetric tensor-power states.

Phrasing this as a predicate lets the consumers below be proved from any source
of the domination bound with the given factor `c`; the de Finetti representation
theorem is one such source. -/
def SymmetricFiniteIidDominationRoute (ι : Type u) (a : Type v)
    [Fintype ι] [Fintype a] [DecidableEq a] (n : ℕ) (c : ℝ) : Prop :=
  ∀ ρ : MState (TensorPower a n),
    ρ.SupportedOnSymmetricSubspace (a := a) →
      ρ.HasFiniteIidDomination (ι := ι) c

namespace SymmetricFiniteIidDominationRoute

/-- A symmetric finite-IID domination route gives the corresponding trace-
distance approximation statement for every supported state. -/
theorem toApproximation {n : ℕ} {c : ℝ}
    (route : SymmetricFiniteIidDominationRoute ι a n c)
    {ρ : MState (TensorPower a n)}
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    ρ.HasFiniteIidMixtureApproximation (ι := ι) (c - 1) :=
  MState.hasFiniteIidMixtureApproximation_of_hasFiniteIidDomination (route ρ hρ)

/-- A symmetric finite-IID domination route gives a finite-IID approximation
after applying any finite output channel. -/
theorem toChannelOutputApproximation {n : ℕ} {c : ℝ}
    (route : SymmetricFiniteIidDominationRoute ι a n c)
    {ρ : MState (TensorPower a n)}
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a))
    {b : Type w} [Fintype b] [DecidableEq b]
    (Φ : CPTPMap (TensorPower a n) b) :
    ρ.HasFiniteIidChannelOutputApproximation (ι := ι) Φ (c - 1) :=
  MState.hasFiniteIidChannelOutputApproximation_of_hasFiniteIidDomination (route ρ hρ) Φ

end SymmetricFiniteIidDominationRoute

/-- Domination by a specified finite IID mixture is monotone in the scalar
factor. -/
theorem isDominatedByFiniteIidMixture_mono_factor {ρ : MState (TensorPower a n)}
    {M : FiniteIidMixture ι a n} {c d : ℝ}
    (h : ρ.IsDominatedByFiniteIidMixture c M) (hcd : c ≤ d) :
    ρ.IsDominatedByFiniteIidMixture d M :=
  matrixDominatedBy_mono_factor h hcd

/-- Domination by a finite IID mixture composes with matrix domination of that
mixture state. -/
theorem isDominatedByFiniteIidMixture_of_matrixDominatedBy_trans
    {ρ : MState (TensorPower a n)} {M : FiniteIidMixture ι a n}
    {τ : MState (TensorPower a n)} {c d : ℝ}
    (hc : 0 ≤ c) (hρM : ρ.IsDominatedByFiniteIidMixture c M)
    (hMτ : M.state.MatrixDominatedBy d τ) :
    ρ.MatrixDominatedBy (c * d) τ :=
  matrixDominatedBy_trans hc hρM hMτ

/-- Applying a channel to a state dominated by a finite IID mixture preserves
the domination relation at the matrix level. -/
theorem isDominatedByFiniteIidMixture_applyChannel
    {b : Type w} [Fintype b] [DecidableEq b]
    {ρ : MState (TensorPower a n)} {M : FiniteIidMixture ι a n} {c : ℝ}
    (Φ : CPTPMap (TensorPower a n) b)
    (hρM : ρ.IsDominatedByFiniteIidMixture c M) :
    MState.MatrixDominatedBy (Φ ρ) c (Φ M.state) :=
  matrixDominatedBy_applyChannel Φ hρM

/-- Applying a channel to a state dominated by a finite IID mixture and then
bounding the image mixture by a target state gives a composed domination
bound. -/
theorem isDominatedByFiniteIidMixture_applyChannel_trans
    {b : Type w} [Fintype b] [DecidableEq b]
    {ρ : MState (TensorPower a n)} {M : FiniteIidMixture ι a n}
    {τ : MState b} {c d : ℝ}
    (Φ : CPTPMap (TensorPower a n) b) (hc : 0 ≤ c)
    (hρM : ρ.IsDominatedByFiniteIidMixture c M)
    (hMτ : MState.MatrixDominatedBy (Φ M.state) d τ) :
    MState.MatrixDominatedBy (Φ ρ) (c * d) τ :=
  matrixDominatedBy_trans hc
    (isDominatedByFiniteIidMixture_applyChannel Φ hρM) hMτ

/-- Applying a channel to a state dominated by a finite IID mixture and then
bounding the image mixture by an output finite IID mixture gives a composed
finite-mixture domination bound. -/
theorem isDominatedByFiniteIidMixture_applyChannel_trans_mixture
    {κ : Type x} {b : Type w} [Fintype κ] [Fintype b] [DecidableEq b]
    {ρ : MState (TensorPower a n)} {M : FiniteIidMixture ι a n}
    {N : FiniteIidMixture κ b n} {c d : ℝ}
    (Φ : CPTPMap (TensorPower a n) (TensorPower b n)) (hc : 0 ≤ c)
    (hρM : ρ.IsDominatedByFiniteIidMixture c M)
    (hMN : MState.IsDominatedByFiniteIidMixture (Φ M.state) d N) :
    MState.IsDominatedByFiniteIidMixture (Φ ρ) (c * d) N :=
  isDominatedByFiniteIidMixture_applyChannel_trans Φ hc hρM hMN

/-- Permutation twirling preserves domination by a finite IID mixture. -/
theorem permutationTwirling_isDominatedByFiniteIidMixture
    {ρ : MState (TensorPower a n)} {M : FiniteIidMixture ι a n} {c : ℝ}
    (hρM : ρ.IsDominatedByFiniteIidMixture c M) :
    ρ.permutationTwirling.IsDominatedByFiniteIidMixture c M :=
  permutationTwirling_matrixDominatedBy_of_target_invariant
    M.state_isPermutationInvariant hρM

/-- If an invariant state's twirling is dominated by a finite IID mixture, then
the state itself is dominated by that mixture. -/
theorem isDominatedByFiniteIidMixture_of_permutationTwirling_left
    {ρ : MState (TensorPower a n)} {M : FiniteIidMixture ι a n} {c : ℝ}
    (hρ : ρ.IsPermutationInvariant (a := a))
    (h : ρ.permutationTwirling.IsDominatedByFiniteIidMixture c M) :
    ρ.IsDominatedByFiniteIidMixture c M :=
  matrixDominatedBy_of_permutationTwirling_left hρ h

/-- For a permutation-invariant state, finite-IID-mixture domination can be
checked after twirling the state. -/
theorem isDominatedByFiniteIidMixture_twirling_iff_of_invariant
    {ρ : MState (TensorPower a n)} {M : FiniteIidMixture ι a n} {c : ℝ}
    (hρ : ρ.IsPermutationInvariant (a := a)) :
    ρ.permutationTwirling.IsDominatedByFiniteIidMixture c M ↔
      ρ.IsDominatedByFiniteIidMixture c M :=
  matrixDominatedBy_twirling_left_iff_of_invariant hρ

/-- A tensor-power state is dominated with factor `1` by the one-point IID
mixture concentrated on the underlying state. -/
theorem tensorPower_isDominatedBy_onePoint (ρ : MState a) (n : ℕ) :
    (ρ.tensorPower n).IsDominatedByFiniteIidMixture 1
      (FiniteIidMixture.onePoint (a := a) ρ n) := by
  exact matrixDominatedBy_of_eq
    (FiniteIidMixture.onePoint_state (a := a) ρ n).symm

/-- The one-point IID domination of a tensor-power state can be enlarged to any
factor at least `1`. -/
theorem tensorPower_isDominatedBy_onePoint_mono_factor (ρ : MState a) (n : ℕ)
    {c : ℝ} (hc : 1 ≤ c) :
    (ρ.tensorPower n).IsDominatedByFiniteIidMixture c
      (FiniteIidMixture.onePoint (a := a) ρ n) :=
  isDominatedByFiniteIidMixture_mono_factor
    (tensorPower_isDominatedBy_onePoint (a := a) ρ n) hc

end MState
