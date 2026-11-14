/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy.Entropy
public import QIT.Information.Entropy.EntropyTensorPower
public import QIT.OneShot.SmoothEndpoint
public import QIT.Information.AlickiFannesWinter
public import QIT.States.Geometry.FuchsVdG
public import QIT.Asymptotic.Typicality
public import QIT.Symmetry.DeFinetti
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Real.Sqrt

/-!
# Quantum Asymptotic Equipartition Property

Statements of the finite-N and asymptotic AEP for smooth conditional entropy.
The full proof requires spectral concentration of rho^{kron n} eigenvalues
and smooth-entropy machinery over nested tensor-power types, which is not
yet available.
-/

@[expose] public section

namespace QIT

universe u v

noncomputable section

open scoped ComplexOrder MatrixOrder

open Filter

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace State

/-- Conditional entropy of the IID bipartite state, read as `A^n|B^n`. -/
def tensorPowerConditionalEntropy (ρ : State (Prod a b)) (n : ℕ) : ℝ :=
  (ρ.tensorPowerBipartite n).conditionalEntropy

@[simp]
theorem tensorPowerConditionalEntropy_eq (ρ : State (Prod a b)) (n : ℕ) :
    ρ.tensorPowerConditionalEntropy n =
      (ρ.tensorPowerBipartite n).conditionalEntropy :=
  rfl

/-- Normalized-candidate smooth conditional min-entropy variant for the IID
bipartite state, read as `A^n|B^n`. -/
def tensorPowerSmoothConditionalMinEntropyNormalizedCandidates
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ) : ℝ :=
  (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyNormalizedCandidates ε

@[simp]
theorem tensorPowerSmoothConditionalMinEntropyNormalizedCandidates_eq
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ) :
    ρ.tensorPowerSmoothConditionalMinEntropyNormalizedCandidates ε n =
      (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyNormalizedCandidates ε :=
  rfl

/-- Unrestricted totalized smooth conditional min-entropy helper for the IID
bipartite state, read as `A^n|B^n`.

Source-facing finite-AEP statements use the canonical finite-domain wrapper
below, which makes the normalized-center conditions `0 ≤ ε < 1` explicit. -/
def tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ) : ℝ :=
  (ρ.tensorPowerBipartite n).toSubnormalized.smoothConditionalMinEntropyRaw ε

@[simp]
theorem tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_eq
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ) :
    ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw ε n =
      (ρ.tensorPowerBipartite n).toSubnormalized.smoothConditionalMinEntropyRaw ε :=
  rfl

/-- Canonical finite-domain tensor-power subnormalized smooth min-entropy. -/
def tensorPowerSubnormalizedSmoothConditionalMinEntropy
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ)
    (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1) : ℝ :=
  (ρ.tensorPowerBipartite n).toSubnormalized.smoothConditionalMinEntropy ε
    hε_nonneg (by rw [State.toSubnormalized_trace]; simpa using hε_lt_one)

@[simp]
theorem tensorPowerSubnormalizedSmoothConditionalMinEntropy_eq
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ)
    (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1) :
    ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_nonneg hε_lt_one =
      (ρ.tensorPowerBipartite n).toSubnormalized.smoothConditionalMinEntropy ε
        hε_nonneg (by rw [State.toSubnormalized_trace]; simpa using hε_lt_one) :=
  rfl

/-- Normalized-candidate smooth conditional max-entropy variant for the IID
bipartite state, read as `A^n|B^n`. -/
def tensorPowerSmoothConditionalMaxEntropyNormalizedCandidates
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ) : ℝ :=
  (ρ.tensorPowerBipartite n).smoothConditionalMaxEntropyNormalizedCandidates ε

@[simp]
theorem tensorPowerSmoothConditionalMaxEntropyNormalizedCandidates_eq
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ) :
    ρ.tensorPowerSmoothConditionalMaxEntropyNormalizedCandidates ε n =
      (ρ.tensorPowerBipartite n).smoothConditionalMaxEntropyNormalizedCandidates ε :=
  rfl

/-- Subnormalized smooth conditional max-entropy of the IID bipartite state,
read as `A^n|B^n`.

This is the max-entropy analogue of
`tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw`: the smoothing ball is
formed by subnormalized nearby states, matching the source convention used in
TCR 2008. -/
def tensorPowerSubnormalizedSmoothConditionalMaxEntropyRaw
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ) : ℝ :=
  (ρ.tensorPowerBipartite n).toSubnormalized.smoothConditionalMaxEntropyRaw ε

@[simp]
theorem tensorPowerSubnormalizedSmoothConditionalMaxEntropyRaw_eq
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ) :
    ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRaw ε n =
      (ρ.tensorPowerBipartite n).toSubnormalized.smoothConditionalMaxEntropyRaw ε :=
  rfl

/-- Canonical finite-domain tensor-power subnormalized smooth max-entropy. -/
def tensorPowerSubnormalizedSmoothConditionalMaxEntropy
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ)
    (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1) : ℝ :=
  (ρ.tensorPowerBipartite n).toSubnormalized.smoothConditionalMaxEntropy ε
    hε_nonneg (by rw [State.toSubnormalized_trace]; simpa using hε_lt_one)

@[simp]
theorem tensorPowerSubnormalizedSmoothConditionalMaxEntropy_eq
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ)
    (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1) :
    ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropy ε n hε_nonneg hε_lt_one =
      (ρ.tensorPowerBipartite n).toSubnormalized.smoothConditionalMaxEntropy ε
        hε_nonneg (by rw [State.toSubnormalized_trace]; simpa using hε_lt_one) :=
  rfl

/-- Positive-definiteness is preserved by the grouped IID bipartite tensor
power `ρ_AB^{⊗ n}` read as a state on `A^n × B^n`. -/
theorem tensorPowerBipartite_posDef_forAEP
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef) (n : ℕ) :
    (ρ.tensorPowerBipartite n).matrix.PosDef := by
  rw [State.tensorPowerBipartite_matrix]
  exact (State.tensorPower_posDef hρ n).submatrix
    (Equiv.injective (tensorPowerProdEquiv a b n).symm)

/-- If `ρ_AB` is positive-definite, then the `B^n` marginal of the grouped IID
bipartite tensor power is positive-definite whenever `ρ_B` is. -/
theorem tensorPowerBipartite_marginalB_posDef_forAEP
    (ρ : State (Prod a b)) (_hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef) (n : ℕ) :
    (ρ.tensorPowerBipartite n).marginalB.matrix.PosDef := by
  rw [State.tensorPowerBipartite_marginalB ρ n]
  exact State.tensorPower_posDef hρB n

/-- Conditional entropy is additive for grouped IID bipartite tensor powers:
`H(A^n|B^n)_{ρ^{⊗ n}} = n H(A|B)_ρ`. -/
theorem tensorPowerBipartite_conditionalEntropy
    (ρ : State (Prod a b)) (n : ℕ) :
    (ρ.tensorPowerBipartite n).conditionalEntropy =
      (n : ℝ) * ρ.conditionalEntropy := by
  have hAB :
      State.vonNeumann (ρ.tensorPowerBipartite n) =
        State.vonNeumann (ρ.tensorPower n) := by
    change State.vonNeumann
        ((ρ.tensorPower n).reindex (tensorPowerProdEquiv a b n)) =
      State.vonNeumann (ρ.tensorPower n)
    rw [State.vonNeumann_reindex]
  rw [conditionalEntropy_eq, conditionalEntropy_eq]
  rw [hAB]
  rw [State.tensorPowerBipartite_marginalB]
  rw [State.vonNeumann_tensorPower, State.vonNeumann_tensorPower]
  ring

end State

/-- Source-shaped finite-N AEP error constant
`δ(ε, η) = 4 log₂(η) sqrt(log₂(2 / ε²))`.

This declaration only records the analytic error term. The finite-N AEP theorem
itself remains a downstream proof obligation.
-/
def finiteAEPDelta (ε η : ℝ) : ℝ :=
  4 * log2 η * Real.sqrt (log2 (2 / ε ^ 2))

/-- The finite-AEP error constant is monotone in the eta parameter on the
positive half-line. -/
public theorem finiteAEPDelta_mono_eta {ε η₁ η₂ : ℝ}
    (hη₁_pos : 0 < η₁) (hη_le : η₁ ≤ η₂) :
    finiteAEPDelta ε η₁ ≤ finiteAEPDelta ε η₂ := by
  have hlog_le : log2 η₁ ≤ log2 η₂ := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hη₁_pos hη_le)
      (le_of_lt (Real.log_pos one_lt_two))
  unfold finiteAEPDelta
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hlog_le
        (Real.sqrt_nonneg (log2 (2 / ε ^ 2))))
      (by norm_num : (0 : ℝ) ≤ 4)

/-- Scalar optimization identity for the finite-AEP penalty.

For positive `M`, `L`, and blocklength parameter `n`, choosing
`α = 1 + sqrt(M) / (2 L sqrt(n))` makes the two penalty terms add to
`4 L sqrt(M) sqrt(n)`. -/
public theorem finiteAEP_penalty_optimized_eq_real {M L n : ℝ}
    (hM : 0 < M) (hL : 0 < L) (hn : 0 < n) :
    let α := 1 + Real.sqrt M / (2 * L * Real.sqrt n)
    4 * (α - 1) * n * L ^ 2 + (1 / (α - 1)) * M =
      4 * L * Real.sqrt M * Real.sqrt n := by
  dsimp
  have hsM : Real.sqrt M ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hM)
  have hsN : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn)
  have hLne : L ≠ 0 := ne_of_gt hL
  field_simp [hsM, hsN, hLne]
  ring_nf
  rw [Real.sq_sqrt (le_of_lt hM), Real.sq_sqrt (le_of_lt hn)]
  ring

/-- Source-shaped finite-AEP scalar optimization identity.

With `M = log₂(2 / ε²)`, `L = log₂ η`, and
`α = 1 + sqrt(M) / (2 L sqrt(n))`, the tensor-power penalty is exactly
`finiteAEPDelta ε η * sqrt(n)`.  Dividing this identity by `n` is the scalar
route to the normalized `finiteAEPDelta ε η / sqrt(n)` term. -/
public theorem finiteAEP_penalty_optimized_eq (ε η : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2)) (hL : 0 < log2 η) (hn : 0 < n) :
    let M := log2 (2 / ε ^ 2)
    let L := log2 η
    let α := 1 + Real.sqrt M / (2 * L * Real.sqrt (n : ℝ))
    4 * (α - 1) * (n : ℝ) * L ^ 2 + (1 / (α - 1)) * M =
      finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  simpa [finiteAEPDelta, mul_assoc, mul_left_comm, mul_comm] using
    (finiteAEP_penalty_optimized_eq_real
      (M := log2 (2 / ε ^ 2)) (L := log2 η) (n := (n : ℝ)) hM hL hnR)

/-- For the source smoothing range `0 < ε < 1`, the logarithmic budget
`log₂(2 / ε²)` is strictly positive. -/
public theorem finiteAEP_log2_two_div_sq_pos {ε : ℝ}
    (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    0 < log2 (2 / ε ^ 2) := by
  unfold log2
  have hε_sq_pos : 0 < ε ^ 2 := sq_pos_of_ne_zero hε_pos.ne'
  have hε_sq_lt_one : ε ^ 2 < 1 := by
    nlinarith
  have hone_lt : 1 < 2 / ε ^ 2 := by
    rw [lt_div_iff₀ hε_sq_pos]
    nlinarith
  exact div_pos (Real.log_pos hone_lt) (Real.log_pos one_lt_two)

/-- Direct scalar window lemma for the source choice of `α`.

This packages the cancellation of the positive `L` denominator.  The remaining
assumption is the root-ratio inequality produced by whatever blocklength
condition is available. -/
public theorem finiteAEP_alpha_window_of_sqrt_ratio_lt (ε η : ℝ) {n : ℕ}
    (hL : 0 < log2 η) (hn : 0 < n)
    (hratio :
      Real.sqrt (log2 (2 / ε ^ 2)) / Real.sqrt (n : ℝ) < log2 3 / 2) :
    let M := log2 (2 / ε ^ 2)
    let L := log2 η
    let α := 1 + Real.sqrt M / (2 * L * Real.sqrt (n : ℝ))
    α < 1 + log2 3 / (4 * L) := by
  dsimp
  rw [add_lt_add_iff_left]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsNpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hden1 : 0 < 2 * log2 η * Real.sqrt (n : ℝ) := by positivity
  have hden2 : 0 < 4 * log2 η := by positivity
  rw [div_lt_div_iff₀ hden1 hden2]
  have hmul := mul_lt_mul_of_pos_right hratio hsNpos
  field_simp [ne_of_gt hsNpos] at hmul
  nlinarith [hmul, hL, hsNpos]

/-- Convert the source-style blocklength condition into the root-ratio bound,
assuming the explicit numerical logarithm inequality. -/
public theorem finiteAEP_sqrt_ratio_lt_of_n_ge {M n : ℝ}
    (hM : 0 ≤ M) (hn : 0 < n)
    (hn_ge : (8 / 5 : ℝ) * M ≤ n)
    (hconst : Real.sqrt ((5 : ℝ) / 8) < log2 3 / 2) :
    Real.sqrt M / Real.sqrt n < log2 3 / 2 := by
  have hmn : M / n ≤ (5 : ℝ) / 8 := by
    rw [div_le_iff₀ hn]
    nlinarith
  have hsqrt_le :
      Real.sqrt (M / n) ≤ Real.sqrt ((5 : ℝ) / 8) :=
    Real.sqrt_le_sqrt hmn
  have hsqrt_div : Real.sqrt M / Real.sqrt n = Real.sqrt (M / n) := by
    rw [Real.sqrt_div hM]
  rw [hsqrt_div]
  exact lt_of_le_of_lt hsqrt_le hconst

/-- Numerical constant used in TCR's source blocklength condition
`n ≥ 8/5 log₂(2/ε²)`. -/
public theorem finiteAEP_sqrt_five_eighth_lt_log2_three_half :
    Real.sqrt ((5 : ℝ) / 8) < log2 3 / 2 := by
  have hsqrt_lt : Real.sqrt ((5 : ℝ) / 8) < (791 : ℝ) / 1000 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (791 : ℝ) / 1000)]
    norm_num
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog_lower : (791 : ℝ) / 1000 < log2 3 / 2 := by
    unfold log2
    rw [div_div]
    rw [lt_div_iff₀ (mul_pos hlog2_pos (by norm_num : (0 : ℝ) < 2))]
    nlinarith [Real.log_three_gt_d9, Real.log_two_lt_d9]
  exact lt_trans hsqrt_lt hlog_lower

/-- Source-style scalar window from `n ≥ 8/5 M`, with the close numerical
constant discharged locally. -/
public theorem finiteAEP_alpha_window_of_n_ge (ε η : ℝ) {n : ℕ}
    (hM : 0 ≤ log2 (2 / ε ^ 2)) (hL : 0 < log2 η) (hn : 0 < n)
    (hn_ge : (8 / 5 : ℝ) * log2 (2 / ε ^ 2) ≤ (n : ℝ)) :
    let M := log2 (2 / ε ^ 2)
    let L := log2 η
    let α := 1 + Real.sqrt M / (2 * L * Real.sqrt (n : ℝ))
    α < 1 + log2 3 / (4 * L) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  exact finiteAEP_alpha_window_of_sqrt_ratio_lt ε η hL hn
    (finiteAEP_sqrt_ratio_lt_of_n_ge
      (M := log2 (2 / ε ^ 2)) (n := (n : ℝ)) hM hnR hn_ge
      finiteAEP_sqrt_five_eighth_lt_log2_three_half)

/-- The source blocklength condition also keeps the optimized `α` inside the
operator-convexity range `α ≤ 2`, provided the TCR eta lower bound `η ≥ 3`
holds. -/
public theorem finiteAEP_alpha_le_two_of_n_ge (ε η : ℝ) {n : ℕ}
    (hM : 0 ≤ log2 (2 / ε ^ 2)) (hL : 0 < log2 η)
    (hη3 : 3 ≤ η) (hn : 0 < n)
    (hn_ge : (8 / 5 : ℝ) * log2 (2 / ε ^ 2) ≤ (n : ℝ)) :
    let M := log2 (2 / ε ^ 2)
    let L := log2 η
    let α := 1 + Real.sqrt M / (2 * L * Real.sqrt (n : ℝ))
    α ≤ 2 := by
  have hwindow := finiteAEP_alpha_window_of_n_ge ε η hM hL hn hn_ge
  dsimp at hwindow ⊢
  have hlog2_three_le : log2 3 ≤ log2 η := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (by norm_num : (0 : ℝ) < 3) hη3)
      (le_of_lt (Real.log_pos one_lt_two))
  have hquot_le_one : log2 3 / (4 * log2 η) ≤ 1 := by
    rw [div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hL)]
    nlinarith
  have hupper : 1 + log2 3 / (4 * log2 η) ≤ 2 := by
    nlinarith
  exact le_of_lt (lt_of_lt_of_le hwindow hupper)

/-- Normalize a tensor-power lower bound by the blocklength. -/
public theorem finiteAEP_normalized_rate_of_tensor_lower_bound
    {S H δ : ℝ} {n : ℕ} (hn : 0 < n)
    (hbound : S ≥ (n : ℝ) * H - δ * Real.sqrt (n : ℝ)) :
    (1 / (n : ℝ)) * S ≥ H - δ / Real.sqrt (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hscale_nonneg : 0 ≤ (1 / (n : ℝ)) := by positivity
  have hmul :
      (1 / (n : ℝ)) * ((n : ℝ) * H - δ * Real.sqrt (n : ℝ)) ≤
        (1 / (n : ℝ)) * S :=
    mul_le_mul_of_nonneg_left hbound hscale_nonneg
  calc
    H - δ / Real.sqrt (n : ℝ) =
        (1 / (n : ℝ)) * ((n : ℝ) * H - δ * Real.sqrt (n : ℝ)) := by
          have hsqrt_sq :
              Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
            rw [← pow_two, Real.sq_sqrt hnR.le]
          field_simp [hnR.ne', hsqrt_pos.ne']
          calc
            (H * Real.sqrt (n : ℝ) - δ) * (n : ℝ) =
                H * (n : ℝ) * Real.sqrt (n : ℝ) - δ * (n : ℝ) := by ring
            _ = H * (n : ℝ) * Real.sqrt (n : ℝ) -
                  δ * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by
                rw [hsqrt_sq]
            _ = Real.sqrt (n : ℝ) *
                  (H * (n : ℝ) - δ * Real.sqrt (n : ℝ)) := by ring
    _ ≤ (1 / (n : ℝ)) * S := hmul

/-- A double-limit AEP statement encoded through an explicit inner limit:
first `n → ∞` at fixed smoothing parameter, then `ε → 0+`.

`rate ε n` is intended to be a normalized smooth-entropy rate, while
`innerLimit ε` records the value of the `n → ∞` limit before taking
`ε → 0+`.
-/
def AEPDoubleLimit (rate : ℝ → ℕ → ℝ) (innerLimit : ℝ → ℝ) (limit : ℝ) : Prop :=
  (∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      Tendsto (fun n : ℕ => rate ε n) atTop (nhds (innerLimit ε))) ∧
    Tendsto innerLimit (nhdsWithin 0 (Set.Ioi 0)) (nhds limit)

@[simp]
theorem AEPDoubleLimit_eq (rate : ℝ → ℕ → ℝ) (innerLimit : ℝ → ℝ) (limit : ℝ) :
    AEPDoubleLimit rate innerLimit limit ↔
      (∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
          Tendsto (fun n : ℕ => rate ε n) atTop (nhds (innerLimit ε))) ∧
        Tendsto innerLimit (nhdsWithin 0 (Set.Ioi 0)) (nhds limit) :=
  Iff.rfl

/-- Package already-proved inner and outer limits as a double-limit statement. -/
theorem AEPDoubleLimit.of_inner_outer {rate : ℝ → ℕ → ℝ}
    {innerLimit : ℝ → ℝ} {limit : ℝ}
    (hinner : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      Tendsto (fun n : ℕ => rate ε n) atTop (nhds (innerLimit ε)))
    (houter : Tendsto innerLimit (nhdsWithin 0 (Set.Ioi 0)) (nhds limit)) :
    AEPDoubleLimit rate innerLimit limit :=
  ⟨hinner, houter⟩

/-- An eventually-valid family of inner-limit proofs, together with the outer
limit, gives the double-limit AEP statement. -/
theorem AEPDoubleLimit.of_eventually_inner {rate : ℝ → ℕ → ℝ}
    {innerLimit : ℝ → ℝ} {limit : ℝ}
    (hinner : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      Tendsto (fun n : ℕ => rate ε n) atTop (nhds (innerLimit ε)))
    (houter : Tendsto innerLimit (nhdsWithin 0 (Set.Ioi 0)) (nhds limit)) :
    AEPDoubleLimit rate innerLimit limit :=
  AEPDoubleLimit.of_inner_outer hinner houter

/-- Two-sided finite-N bounds with an error tending to zero imply convergence of
the rate to the limiting entropy. -/
theorem tendsto_of_eventually_two_sided_error {rate error : ℕ → ℝ} {limit : ℝ}
    (herror : Tendsto error atTop (nhds 0))
    (hlower : ∀ᶠ n in atTop, limit - error n ≤ rate n)
    (hupper : ∀ᶠ n in atTop, rate n ≤ limit + error n) :
    Tendsto rate atTop (nhds limit) := by
  have hlow : Tendsto (fun n : ℕ => limit - error n) atTop (nhds limit) := by
    simpa using tendsto_const_nhds.sub herror
  have hhigh : Tendsto (fun n : ℕ => limit + error n) atTop (nhds limit) := by
    simpa using tendsto_const_nhds.add herror
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh hlower hupper

/-- Absolute-error finite-N bounds imply convergence once the error term tends
to zero. -/
theorem tendsto_of_eventually_abs_error {rate error : ℕ → ℝ} {limit : ℝ}
    (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ᶠ n in atTop, |rate n - limit| ≤ error n) :
    Tendsto rate atTop (nhds limit) := by
  refine tendsto_of_eventually_two_sided_error herror ?_ ?_
  · filter_upwards [hbound] with n hn
    have h := abs_le.mp hn
    linarith
  · filter_upwards [hbound] with n hn
    have h := abs_le.mp hn
    linarith

/-- If finite-N two-sided bounds hold for small positive smoothing parameters
and the error vanishes as `n → ∞`, then the packaged double-limit statement
follows. -/
theorem AEPDoubleLimit.of_eventually_two_sided_error {rate error : ℝ → ℕ → ℝ}
    {innerLimit : ℝ → ℝ} {limit : ℝ}
    (herror : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      Tendsto (fun n : ℕ => error ε n) atTop (nhds 0))
    (hlower : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      ∀ᶠ n in atTop, innerLimit ε - error ε n ≤ rate ε n)
    (hupper : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      ∀ᶠ n in atTop, rate ε n ≤ innerLimit ε + error ε n)
    (houter : Tendsto innerLimit (nhdsWithin 0 (Set.Ioi 0)) (nhds limit)) :
    AEPDoubleLimit rate innerLimit limit := by
  refine AEPDoubleLimit.of_inner_outer ?_ houter
  filter_upwards [herror, hlower, hupper] with ε hε hε_lower hε_upper
  exact tendsto_of_eventually_two_sided_error hε hε_lower hε_upper

/-- Absolute-error finite-N bounds are a convenient special case of the
double-limit squeeze bridge. -/
theorem AEPDoubleLimit.of_eventually_abs_error {rate error : ℝ → ℕ → ℝ}
    {innerLimit : ℝ → ℝ} {limit : ℝ}
    (herror : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      Tendsto (fun n : ℕ => error ε n) atTop (nhds 0))
    (hbound : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      ∀ᶠ n in atTop, |rate ε n - innerLimit ε| ≤ error ε n)
    (houter : Tendsto innerLimit (nhdsWithin 0 (Set.Ioi 0)) (nhds limit)) :
    AEPDoubleLimit rate innerLimit limit := by
  refine AEPDoubleLimit.of_inner_outer ?_ houter
  filter_upwards [herror, hbound] with ε hε hε_bound
  exact tendsto_of_eventually_abs_error hε hε_bound

/-- Literal iterated-limit statement for smooth-entropy rates on their
mathematical domain `0 < ε < 1`.

The proof arguments keep calls to the canonical finite-domain smoothing API
explicit. The inner limit is taken at each fixed admissible smoothing radius,
and the outer limit approaches zero through the same admissible domain. -/
def FiniteDomainAEPDoubleLimit
    (rate : (ε : ℝ) → 0 ≤ ε → ε < 1 → ℕ → ℝ)
    (innerLimit : ℝ → ℝ) (limit : ℝ) : Prop :=
  (∀ᶠ ε in nhdsWithin 0 (Set.Ioo 0 1),
      ∀ (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1),
        Tendsto (fun n : ℕ => rate ε hε_nonneg hε_lt_one n)
          atTop (nhds (innerLimit ε))) ∧
    Tendsto innerLimit (nhdsWithin 0 (Set.Ioo 0 1)) (nhds limit)

@[simp]
theorem FiniteDomainAEPDoubleLimit_eq
    (rate : (ε : ℝ) → 0 ≤ ε → ε < 1 → ℕ → ℝ)
    (innerLimit : ℝ → ℝ) (limit : ℝ) :
    FiniteDomainAEPDoubleLimit rate innerLimit limit ↔
      (∀ᶠ ε in nhdsWithin 0 (Set.Ioo 0 1),
          ∀ (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1),
            Tendsto (fun n : ℕ => rate ε hε_nonneg hε_lt_one n)
              atTop (nhds (innerLimit ε))) ∧
        Tendsto innerLimit (nhdsWithin 0 (Set.Ioo 0 1)) (nhds limit) :=
  Iff.rfl

/-- Package fixed-smoothing inner limits and their outer limit as a
finite-domain literal iterated limit. -/
theorem FiniteDomainAEPDoubleLimit.of_inner_outer
    {rate : (ε : ℝ) → 0 ≤ ε → ε < 1 → ℕ → ℝ}
    {innerLimit : ℝ → ℝ} {limit : ℝ}
    (hinner : ∀ᶠ ε in nhdsWithin 0 (Set.Ioo 0 1),
      ∀ (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1),
        Tendsto (fun n : ℕ => rate ε hε_nonneg hε_lt_one n)
          atTop (nhds (innerLimit ε)))
    (houter : Tendsto innerLimit (nhdsWithin 0 (Set.Ioo 0 1)) (nhds limit)) :
    FiniteDomainAEPDoubleLimit rate innerLimit limit :=
  ⟨hinner, houter⟩

/-- A constant divided by `sqrt n` tends to zero. -/
theorem tendsto_const_div_sqrt_nat (C : ℝ) :
    Tendsto (fun n : ℕ => C / Real.sqrt (n : ℝ)) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  simpa using tendsto_const_nhds.div_atTop hsqrt

/-- The finite-N AEP error profile `δ(ε,η)/sqrt n` vanishes as `n → ∞`. -/
theorem finiteAEPDelta_div_sqrt_tendsto_zero (ε η : ℝ) :
    Tendsto (fun n : ℕ => finiteAEPDelta ε η / Real.sqrt (n : ℝ))
      atTop (nhds 0) :=
  tendsto_const_div_sqrt_nat (finiteAEPDelta ε η)

/-- Source-shaped nested limit directly used by TCR's proof of `thm:qaep`.

The statement says that for every final tolerance, sufficiently small positive
smoothness and then sufficiently large blocklength put the rate within that
tolerance of the claimed entropy.  This is the Lean surface for
`lim_{ε → 0} lim_{n → ∞}` used in the source proof, without asserting a
stronger fixed-`ε` inner limit than the source derives from AFW continuity. -/
def SourceTwoStageLimitTo (rate : ℝ → ℕ → ℝ) (limit : ℝ) : Prop :=
  ∀ γ : ℝ, 0 < γ →
    ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      ∀ᶠ n in atTop, |rate ε n - limit| < γ

@[simp]
theorem SourceTwoStageLimitTo_eq (rate : ℝ → ℕ → ℝ) (limit : ℝ) :
    SourceTwoStageLimitTo rate limit ↔
      ∀ γ : ℝ, 0 < γ →
        ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
          ∀ᶠ n in atTop, |rate ε n - limit| < γ :=
  Iff.rfl

/-- Source-shaped nested limit for a smoothing rate whose mathematical domain
is `0 ≤ ε < 1`.

The proof arguments are explicit so source-facing statements cannot silently
apply a totalized smooth-entropy helper outside the finite-resource domain. -/
def SourceFiniteDomainTwoStageLimitTo
    (rate : (ε : ℝ) → 0 ≤ ε → ε < 1 → ℕ → ℝ) (limit : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      ∀ (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1),
        ∀ᶠ n in atTop, |rate ε hε_nonneg hε_lt_one n - limit| < δ

/-- Finite-domain version of the source-shaped squeeze principle. -/
theorem SourceFiniteDomainTwoStageLimitTo.of_eventually_squeeze
    {rate : (ε : ℝ) → 0 ≤ ε → ε < 1 → ℕ → ℝ} {limit : ℝ}
    (hlower : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
        ∀ (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1),
          ∀ᶠ n in atTop, limit - δ ≤ rate ε hε_nonneg hε_lt_one n)
    (hupper : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
        ∀ (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1),
          ∀ᶠ n in atTop, rate ε hε_nonneg hε_lt_one n ≤ limit + δ) :
    SourceFiniteDomainTwoStageLimitTo rate limit := by
  intro δ hδ
  have hhalf : 0 < δ / 2 := half_pos hδ
  filter_upwards [hlower (δ / 2) hhalf, hupper (δ / 2) hhalf] with ε hε_lower hε_upper
  intro hε_nonneg hε_lt_one
  filter_upwards [hε_lower hε_nonneg hε_lt_one, hε_upper hε_nonneg hε_lt_one]
    with n hn_lower hn_upper
  rw [abs_lt]
  constructor <;> linarith

/-- Source-shaped squeeze principle for the nested AEP limit.

The lower side is supplied by the finite-N AEP with an `n`-vanishing penalty;
the upper side is supplied by the ordering lemma plus AFW/Fannes continuity,
whose residual error only has to vanish as `ε → 0`. -/
theorem SourceTwoStageLimitTo.of_eventually_squeeze {rate : ℝ → ℕ → ℝ}
    {limit : ℝ}
    (hlower : ∀ γ : ℝ, 0 < γ →
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
        ∀ᶠ n in atTop, limit - γ ≤ rate ε n)
    (hupper : ∀ γ : ℝ, 0 < γ →
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
        ∀ᶠ n in atTop, rate ε n ≤ limit + γ) :
    SourceTwoStageLimitTo rate limit := by
  intro γ hγ
  have hhalf : 0 < γ / 2 := half_pos hγ
  filter_upwards [hlower (γ / 2) hhalf, hupper (γ / 2) hhalf] with ε hε_lower hε_upper
  filter_upwards [hε_lower, hε_upper] with n hn_lower hn_upper
  rw [abs_lt]
  constructor <;> linarith

/- Von Neumann entropy is additive under tensor products.

S(rho^{kron n}) = n * S(rho). Requires spectral theory of
Kronecker products (eigenvalues of A kron B = pairwise products). -/
def State.vonNeumann_tensorPower_statement
    (ρ : State a) (n : ℕ) : Prop :=
  State.vonNeumann (ρ.tensorPower n) = n * State.vonNeumann ρ

/- Finite-N AEP bound (thm:qep):

For i.i.d. rho_AB^{kron n},
(1/n) H^eps_min(A^n|B^n) >= H(A|B)_rho - delta(eps,eta)/sqrt(n),
where delta(eps,eta) = 4 log eta sqrt(log(2/eps^2)).

The parameter `eta` is the source convergence parameter
`Upsilon(A|B)_{rho|rho}`.  It is kept explicit at this lightweight statement
surface to avoid importing the heavier positive-definite proof layer back into
`AEP.lean`. -/
def finiteNAEP_statement
    (ρ : State (Prod a b)) (ε η : ℝ) (n : ℕ)
    (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1) : Prop :=
  0 < ε →
    (8 / 5 : ℝ) * log2 (2 / ε ^ 2) ≤ (n : ℝ) →
      (1 / (n : ℝ)) *
          ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy
            ε n hε_nonneg hε_lt_one ≥
        ρ.conditionalEntropy - finiteAEPDelta ε η / Real.sqrt (n : ℝ)

namespace State

/-- Unrestricted normalized smooth-min rate helper for internal limit proofs. -/
def tensorPowerSubnormalizedSmoothConditionalMinEntropyRateRaw
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw ε n

@[simp]
theorem tensorPowerSubnormalizedSmoothConditionalMinEntropyRateRaw_eq
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ) :
    ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRateRaw ε n =
      (1 / (n : ℝ)) * ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw ε n :=
  rfl

/-- Canonical finite-domain normalized tensor-power smooth-min rate. -/
def tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ)
    (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1) : ℝ :=
  (1 / (n : ℝ)) *
    ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_nonneg hε_lt_one

@[simp]
theorem tensorPowerSubnormalizedSmoothConditionalMinEntropyRate_eq
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ)
    (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1) :
    ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate ε n hε_nonneg hε_lt_one =
      (1 / (n : ℝ)) *
        ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_nonneg hε_lt_one :=
  rfl

/-- Unrestricted normalized smooth-max rate helper for internal limit proofs. -/
def tensorPowerSubnormalizedSmoothConditionalMaxEntropyRateRaw
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRaw ε n

@[simp]
theorem tensorPowerSubnormalizedSmoothConditionalMaxEntropyRateRaw_eq
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ) :
    ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRateRaw ε n =
      (1 / (n : ℝ)) * ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRaw ε n :=
  rfl

/-- Canonical finite-domain normalized tensor-power smooth-max rate. -/
def tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ)
    (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1) : ℝ :=
  (1 / (n : ℝ)) *
    ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropy ε n hε_nonneg hε_lt_one

@[simp]
theorem tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate_eq
    (ρ : State (Prod a b)) (ε : ℝ) (n : ℕ)
    (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1) :
    ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate ε n hε_nonneg hε_lt_one =
      (1 / (n : ℝ)) *
        ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropy ε n hε_nonneg hε_lt_one :=
  rfl

end State

namespace PureVector

variable {c : Type*} [Fintype c] [DecidableEq c]

private theorem State.reindex_trans
    {α : Type*} {β : Type*} {γ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (ρ : State α) (e : α ≃ β) (f : β ≃ γ) :
    ρ.reindex (e.trans f) = (ρ.reindex e).reindex f := by
  apply State.ext
  ext i j
  rfl

/-- Regroup the tensor power of a left-associated tripartite system as
`(A^n × B^n) × C^n`. -/
def tensorPowerTripartiteGroupedEquiv (a : Type u) (b : Type v) (c : Type*)
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] (n : ℕ) :
    TensorPower (Prod (Prod a b) c) n ≃
      Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower c n) :=
  (tensorPowerProdEquiv (Prod a b) c n).trans
    (Equiv.prodCongr (tensorPowerProdEquiv a b n) (Equiv.refl (TensorPower c n)))

@[simp]
private theorem tensorPowerTripartiteGroupedEquiv_symm_succ_apply
    (n : ℕ) (a₀ : a) (as : TensorPower a n)
    (b₀ : b) (bs : TensorPower b n) (c₀ : c) (cs : TensorPower c n) :
    (tensorPowerTripartiteGroupedEquiv a b c (n + 1)).symm
        (((a₀, as), (b₀, bs)), (c₀, cs)) =
      (((a₀, b₀), c₀),
        (tensorPowerTripartiteGroupedEquiv a b c n).symm ((as, bs), cs)) := by
  simp [tensorPowerTripartiteGroupedEquiv, tensorPowerProdEquiv]

/-- Grouped IID tensor power of a pure tripartite vector, read as
`(A^nB^n)C^n`. -/
def tensorPowerTripartiteGrouped (Ψ : PureVector (Prod (Prod a b) c)) (n : ℕ) :
    PureVector (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower c n)) :=
  (Ψ.tensorPower n).reindex (tensorPowerTripartiteGroupedEquiv a b c n)

@[simp]
theorem tensorPowerTripartiteGrouped_state
    (Ψ : PureVector (Prod (Prod a b) c)) (n : ℕ) :
    (Ψ.tensorPowerTripartiteGrouped n).state =
      (Ψ.state.tensorPower n).reindex (tensorPowerTripartiteGroupedEquiv a b c n) := by
  rw [tensorPowerTripartiteGrouped, PureVector.reindex_state, PureVector.tensorPower_state]

/-- The `A^nB^n` marginal of the grouped pure tensor power is the grouped IID
tensor power of the single-copy `AB` marginal. -/
theorem tensorPowerTripartiteGrouped_marginalAB
    (Ψ : PureVector (Prod (Prod a b) c)) (n : ℕ) :
    (Ψ.tensorPowerTripartiteGrouped n).state.marginalAB =
      Ψ.state.marginalAB.tensorPowerBipartite n := by
  rw [tensorPowerTripartiteGrouped_state]
  change
    (((Ψ.state.tensorPower n).reindex
      ((tensorPowerProdEquiv (Prod a b) c n).trans
        (Equiv.prodCongr (tensorPowerProdEquiv a b n)
          (Equiv.refl (TensorPower c n))))).marginalA) =
      Ψ.state.marginalAB.tensorPowerBipartite n
  rw [State.reindex_trans]
  rw [State.marginalA_reindex_prodCongr]
  change ((Ψ.state.tensorPowerBipartite n).marginalA).reindex
      (tensorPowerProdEquiv a b n) =
    Ψ.state.marginalAB.tensorPowerBipartite n
  rw [State.tensorPowerBipartite_marginalA Ψ.state n]
  rfl

private theorem State.tensorPowerTripartiteGrouped_marginalAC
    (ρ : State (Prod (Prod a b) c)) :
    (n : ℕ) →
      ((ρ.tensorPower n).reindex (tensorPowerTripartiteGroupedEquiv a b c n)).marginalAC =
        ρ.marginalAC.tensorPowerBipartite n
  | 0 => by
      apply State.ext
      ext x y
      rcases x with ⟨xA, xC⟩
      rcases y with ⟨yA, yC⟩
      cases xA
      cases xC
      cases yA
      cases yC
      simp [tensorPowerTripartiteGroupedEquiv, State.tensorPowerBipartite,
        State.tensorPower, State.unit, State.reindex, State.marginalAC_matrix,
        tensorPowerProdEquiv, TensorPower]
  | n + 1 => by
      apply State.ext
      ext x y
      rcases x with ⟨xA, xC⟩
      rcases y with ⟨yA, yC⟩
      rcases xA with ⟨xA0, xAs⟩
      rcases yA with ⟨yA0, yAs⟩
      rcases xC with ⟨xC0, xCs⟩
      rcases yC with ⟨yC0, yCs⟩
      have hih := congrArg
        (fun σ : State (Prod (TensorPower a n) (TensorPower c n)) =>
          σ.matrix (xAs, xCs) (yAs, yCs))
        (State.tensorPowerTripartiteGrouped_marginalAC ρ n)
      simp [tensorPowerTripartiteGroupedEquiv, State.tensorPowerBipartite,
        State.tensorPower, State.prod, State.reindex, State.marginalAC_matrix,
        Matrix.kronecker, Matrix.kroneckerMap_apply, TensorPower] at hih ⊢
      have hih_grouped :
          (∑ rest : TensorPower b n,
            (ρ.tensorPower n).matrix
              ((tensorPowerTripartiteGroupedEquiv a b c n).symm ((xAs, rest), xCs))
              ((tensorPowerTripartiteGroupedEquiv a b c n).symm ((yAs, rest), yCs))) =
            (ρ.marginalAC.tensorPowerBipartite n).matrix (xAs, xCs) (yAs, yCs) := by
        simpa [tensorPowerTripartiteGroupedEquiv, State.tensorPowerBipartite]
          using hih
      calc
        (∑ x : Prod b (TensorPower b n),
            ρ.matrix ((xA0, x.1), xC0) ((yA0, x.1), yC0) *
              (ρ.tensorPower n).matrix
                ((tensorPowerTripartiteGroupedEquiv a b c n).symm ((xAs, x.2), xCs))
                ((tensorPowerTripartiteGroupedEquiv a b c n).symm ((yAs, x.2), yCs))) =
            ∑ j : b, ∑ rest : TensorPower b n,
              ρ.matrix ((xA0, j), xC0) ((yA0, j), yC0) *
                (ρ.tensorPower n).matrix
                  ((tensorPowerTripartiteGroupedEquiv a b c n).symm ((xAs, rest), xCs))
                  ((tensorPowerTripartiteGroupedEquiv a b c n).symm ((yAs, rest), yCs)) := by
          simp [Fintype.sum_prod_type]
        _ = ∑ j : b,
            ρ.matrix ((xA0, j), xC0) ((yA0, j), yC0) *
              (∑ rest : TensorPower b n,
                (ρ.tensorPower n).matrix
                  ((tensorPowerTripartiteGroupedEquiv a b c n).symm ((xAs, rest), xCs))
                  ((tensorPowerTripartiteGroupedEquiv a b c n).symm ((yAs, rest), yCs))) := by
          simp [Finset.mul_sum]
        _ = ∑ j : b,
            ρ.matrix ((xA0, j), xC0) ((yA0, j), yC0) *
              (ρ.marginalAC.tensorPowerBipartite n).matrix (xAs, xCs) (yAs, yCs) := by
          simp [hih_grouped]
        _ = (∑ j : b, ρ.matrix ((xA0, j), xC0) ((yA0, j), yC0)) *
              (ρ.marginalAC.tensorPowerBipartite n).matrix (xAs, xCs) (yAs, yCs) := by
          simpa using (Finset.sum_mul Finset.univ
            (fun j : b => ρ.matrix ((xA0, j), xC0) ((yA0, j), yC0))
            ((ρ.marginalAC.tensorPowerBipartite n).matrix (xAs, xCs) (yAs, yCs))).symm

/-- The `A^nC^n` marginal of the grouped pure tensor power is the grouped IID
tensor power of the single-copy `AC` marginal. -/
theorem tensorPowerTripartiteGrouped_marginalAC
    (Ψ : PureVector (Prod (Prod a b) c)) (n : ℕ) :
    (Ψ.tensorPowerTripartiteGrouped n).state.marginalAC =
      Ψ.state.marginalAC.tensorPowerBipartite n := by
  rw [tensorPowerTripartiteGrouped_state]
  exact State.tensorPowerTripartiteGrouped_marginalAC
    (a := a) (b := b) (c := c) Ψ.state n

private theorem ofStateScale_one_eq_toSubnormalized
    (ρ : State a) (h0 : (0 : ℝ) ≤ 1) (h1 : (1 : ℝ) ≤ 1) :
    SubnormalizedState.ofStateScale ρ 1 h0 h1 = ρ.toSubnormalized := by
  apply SubnormalizedState.ext
  simp [SubnormalizedState.ofStateScale, State.toSubnormalized]

/-- Pointwise tensor-power smooth min/max duality for the `A^nB^n` marginal
and the actual complementary `A^nC^n` marginal of the grouped pure tensor
power.  Identifying the latter with `(ψ_AC)^{⊗ n}` is the remaining tensor-word
reindexing step. -/
theorem tensorPowerSubnormalizedSmoothConditionalMaxEntropyRateRaw_marginalAB_eq_neg_grouped_marginalAC
    [Nonempty a] [Nonempty b] [Nonempty c]
    (Ψ : PureVector (Prod (Prod a b) c)) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < 1) (n : ℕ) :
    Ψ.state.marginalAB.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRateRaw ε n =
      -((1 / (n : ℝ)) *
        SubnormalizedState.smoothConditionalMinEntropyRaw
          (Ψ.tensorPowerTripartiteGrouped n).state.marginalAC.toSubnormalized ε) := by
  let Ω := Ψ.tensorPowerTripartiteGrouped n
  have hdual :=
    SubnormalizedState.smoothConditionalMaxEntropy_marginalAB_eq_neg_smoothConditionalMinEntropy_marginalAC_of_scaled_pure
      (a := TensorPower a n) (b := TensorPower b n) (c := TensorPower c n)
      Ω (t := 1) (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 1)
      hε0 (by simpa using hε)
  change
    (SubnormalizedState.abMarginalFromScaledTripartitePure
        (a := TensorPower a n) (b := TensorPower b n) (c := TensorPower c n)
        Ω 1 (by norm_num) (by norm_num)).smoothConditionalMaxEntropyRaw ε =
      -(SubnormalizedState.acMarginalFromScaledTripartitePure
        (a := TensorPower a n) (b := TensorPower b n) (c := TensorPower c n)
        Ω 1 (by norm_num) (by norm_num)).smoothConditionalMinEntropyRaw ε at hdual
  have hABsub :
      SubnormalizedState.abMarginalFromScaledTripartitePure
          (a := TensorPower a n) (b := TensorPower b n) (c := TensorPower c n)
          Ω 1 (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1) =
        (Ψ.state.marginalAB.tensorPowerBipartite n).toSubnormalized := by
    rw [SubnormalizedState.abMarginalFromScaledTripartitePure]
    rw [ofStateScale_one_eq_toSubnormalized]
    rw [tensorPowerTripartiteGrouped_marginalAB]
  have hACsub :
      SubnormalizedState.acMarginalFromScaledTripartitePure
          (a := TensorPower a n) (b := TensorPower b n) (c := TensorPower c n)
          Ω 1 (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1) =
        Ω.state.marginalAC.toSubnormalized := by
    rw [SubnormalizedState.acMarginalFromScaledTripartitePure]
    rw [ofStateScale_one_eq_toSubnormalized]
  rw [hABsub, hACsub] at hdual
  rw [State.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRateRaw_eq,
    State.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRaw_eq]
  rw [hdual]
  ring

/-- Pointwise tensor-power smooth min/max duality for complementary marginals
of a pure tripartite state, grouped as `A^nB^n` and `A^nC^n`. -/
theorem tensorPowerSubnormalizedSmoothConditionalMaxEntropyRateRaw_marginalAB_eq_neg_min_marginalAC
    [Nonempty a] [Nonempty b] [Nonempty c]
    (Ψ : PureVector (Prod (Prod a b) c)) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < 1) (n : ℕ) :
    Ψ.state.marginalAB.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRateRaw ε n =
      -Ψ.state.marginalAC.tensorPowerSubnormalizedSmoothConditionalMinEntropyRateRaw ε n := by
  have hgroup :=
    tensorPowerSubnormalizedSmoothConditionalMaxEntropyRateRaw_marginalAB_eq_neg_grouped_marginalAC
      (a := a) (b := b) (c := c) Ψ hε0 hε n
  have hAC :
      (Ψ.tensorPowerTripartiteGrouped n).state.marginalAC =
        Ψ.state.marginalAC.tensorPowerBipartite n :=
    tensorPowerTripartiteGrouped_marginalAC (a := a) (b := b) (c := c) Ψ n
  rw [hgroup]
  rw [State.tensorPowerSubnormalizedSmoothConditionalMinEntropyRateRaw_eq,
    State.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_eq]
  rw [hAC]

/-- Canonical finite-domain pointwise tensor-power smooth min/max duality. -/
theorem tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate_marginalAB_eq_neg_min_marginalAC
    [Nonempty a] [Nonempty b] [Nonempty c]
    (Ψ : PureVector (Prod (Prod a b) c)) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < 1) (n : ℕ) :
    Ψ.state.marginalAB.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate
        ε n hε0 hε =
      -Ψ.state.marginalAC.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
        ε n hε0 hε := by
  change
    Ψ.state.marginalAB.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRateRaw ε n =
      -Ψ.state.marginalAC.tensorPowerSubnormalizedSmoothConditionalMinEntropyRateRaw ε n
  exact tensorPowerSubnormalizedSmoothConditionalMaxEntropyRateRaw_marginalAB_eq_neg_min_marginalAC
    (a := a) (b := b) (c := c) Ψ hε0 hε n

end PureVector

namespace State

/-- Lower-rate handoff supplied by the finite-N AEP theorem `thm:qep`.

This interface is intentionally phrased as the source proof uses it: after
choosing the final tolerance and then a small positive smoothing radius,
sufficiently large blocklengths place the smooth-min rate above
`H(A|B)_ρ` up to the requested tolerance. -/
def SmoothMinRateLowerFromFiniteNAEP (ρ : State (Prod a b)) : Prop :=
  ∀ γ : ℝ, 0 < γ →
    ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      ∀ (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1),
        ∀ᶠ n in atTop,
          ρ.conditionalEntropy - γ ≤
            ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
              ε n hε_nonneg hε_lt_one

/-- Upper-rate handoff supplied by the ordering lemma and AFW/Fannes
continuity in TCR's proof of `thm:qaep`.

The eventual `ε` layer is where the continuity modulus is made small; the
eventual `n` layer corresponds to the tensor-power rate normalization. -/
def SmoothMinRateUpperFromContinuity (ρ : State (Prod a b)) : Prop :=
  ∀ γ : ℝ, 0 < γ →
    ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      ∀ (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1),
        ∀ᶠ n in atTop,
          ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
              ε n hε_nonneg hε_lt_one ≤
            ρ.conditionalEntropy + γ

/-- Quantitative continuity profile behind the source's `O(ε)` upper bound.

Later AFW formalization should prove this by combining the ordering lemma with
conditional-entropy continuity for subnormalized smoothing witnesses. -/
def SmoothMinRateContinuityUpperProfile
    (ρ : State (Prod a b)) (modulus : ℝ → ℝ) : Prop :=
  Tendsto modulus (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      ∀ (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1),
        ∀ᶠ n in atTop,
          ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
              ε n hε_nonneg hε_lt_one ≤
            ρ.conditionalEntropy + modulus ε

/-- A vanishing AFW/Fannes continuity modulus gives the upper half of the
source min-entropy squeeze. -/
theorem SmoothMinRateUpperFromContinuity.of_profile
    (ρ : State (Prod a b)) {modulus : ℝ → ℝ}
    (hprofile : ρ.SmoothMinRateContinuityUpperProfile modulus) :
    ρ.SmoothMinRateUpperFromContinuity := by
  intro γ hγ
  rcases hprofile with ⟨hmod_tend, hupper⟩
  have hmod_small :
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0), modulus ε < γ :=
    hmod_tend.eventually (Iio_mem_nhds hγ)
  filter_upwards [hupper, hmod_small] with ε hε_upper hε_small
  intro hε_nonneg hε_lt_one
  filter_upwards [hε_upper hε_nonneg hε_lt_one] with n hn_upper
  linarith

omit [DecidableEq a] in
/-- Tensor-power cardinalities turn the AFW dimension term into an exactly
linear entropy contribution, `log₂ |A^n| = n log₂ |A|`. -/
theorem log2_tensorPower_card (n : ℕ) :
    log2 (Fintype.card (TensorPower a n) : ℝ) =
      (n : ℝ) * log2 (Fintype.card a : ℝ) := by
  unfold log2
  rw [tensorPower_card (a := a) n, Nat.cast_pow, Real.log_pow]
  ring

omit [DecidableEq a] in
/-- For fixed smoothing radius, the normalized AFW tensor-power modulus has
the source rate limit `2 ε log₂ |A|`.

This is the scalar part of the upper half of TCR `thm:qaep`: after applying
AFW to an `A^nB^n` state, dividing by `n` leaves the linear dimension term and
the binary-entropy term vanishes as `n → ∞`. -/
theorem tendsto_afwContinuityModulus_tensorPower_rate
    (ε : ℝ) :
    Tendsto
      (fun n : ℕ =>
        afwContinuityModulus (Fintype.card (TensorPower a n)) ε / (n : ℝ))
      atTop
      (nhds (2 * ε * log2 (Fintype.card a : ℝ))) := by
  have hnonzero : ∀ᶠ n : ℕ in atTop, n ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact Nat.ne_zero_of_lt hn
  have hvanish :
      Tendsto
        (fun n : ℕ =>
          ((1 + ε) * binaryEntropy (ε / (1 + ε))) / (n : ℝ))
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsum :
      Tendsto
        (fun n : ℕ =>
          2 * ε * log2 (Fintype.card a : ℝ) +
            ((1 + ε) * binaryEntropy (ε / (1 + ε))) / (n : ℝ))
        atTop
        (nhds (2 * ε * log2 (Fintype.card a : ℝ) + 0)) :=
    tendsto_const_nhds.add hvanish
  have hsum' :
      Tendsto
        (fun n : ℕ =>
          2 * ε * log2 (Fintype.card a : ℝ) +
            ((1 + ε) * binaryEntropy (ε / (1 + ε))) / (n : ℝ))
        atTop
        (nhds (2 * ε * log2 (Fintype.card a : ℝ))) := by
    simpa using hsum
  refine hsum'.congr' ?_
  filter_upwards [hnonzero] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  unfold afwContinuityModulus
  rw [log2_tensorPower_card (a := a) n]
  field_simp [hnR]

/-- Source upper profile from the pointwise ordering `H_min ≤ H` and AFW.

This is the quantitative form of the upper half of TCR `thm:qaep`: normalize a
subnormalized smoothing witness, use Fuchs--van de Graaf to apply AFW at the
same smoothing radius, and divide the remaining trace-normalization penalty by
the blocklength.  The ordering hypothesis is deliberately local to the
tensor-power registers so that the endpoint theorem can be supplied separately.
-/
theorem SmoothMinRateUpperFromContinuity.afw_of_tensorPower_ordering
    (ρ : State (Prod a b))
    (horder :
      ∀ n : ℕ, ∀ τ : State (Prod (TensorPower a n) (TensorPower b n)),
        τ.conditionalMinEntropy ≤ τ.conditionalEntropy) :
    ρ.SmoothMinRateUpperFromContinuity := by
  classical
  letI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  letI : Nonempty b := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  intro γ hγ
  have hthird : 0 < γ / 3 := by positivity
  have hlin_tend :
      Tendsto (fun ε : ℝ => 2 * ε * log2 (Fintype.card a : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hε :
        Tendsto (fun ε : ℝ => ε)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa [mul_assoc] using
      ((tendsto_const_nhds.mul hε).mul tendsto_const_nhds :
        Tendsto (fun ε : ℝ => 2 * ε * log2 (Fintype.card a : ℝ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (2 * 0 * log2 (Fintype.card a : ℝ))))
  have hlin_small :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        2 * ε * log2 (Fintype.card a : ℝ) < γ / 3 :=
    hlin_tend.eventually (Iio_mem_nhds hthird)
  have hε_pos :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
    self_mem_nhdsWithin
  have hε_lt_one :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hlin_small, hε_pos, hε_lt_one] with ε hlin hε0 hε1
  intro _hε_nonneg _hε_lt_one
  let δ : ℝ := (1 - ε) ^ 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact sq_pos_of_pos (sub_pos.mpr hε1)
  have hafw_tend :
      Tendsto
        (fun n : ℕ =>
          afwContinuityModulus (Fintype.card (TensorPower a n)) ε / (n : ℝ))
        atTop
        (nhds (2 * ε * log2 (Fintype.card a : ℝ))) :=
    tendsto_afwContinuityModulus_tensorPower_rate (a := a) (ε := ε)
  have hafw_small :
      ∀ᶠ n : ℕ in atTop,
        afwContinuityModulus (Fintype.card (TensorPower a n)) ε / (n : ℝ) <
          2 * ε * log2 (Fintype.card a : ℝ) + γ / 3 :=
    hafw_tend.eventually (Iio_mem_nhds (by linarith))
  have htrace_tend :
      Tendsto (fun n : ℕ => (-log2 δ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have htrace_small :
      ∀ᶠ n : ℕ in atTop, (-log2 δ) / (n : ℝ) < γ / 3 :=
    htrace_tend.eventually (Iio_mem_nhds hthird)
  have hn_pos : ∀ᶠ n : ℕ in atTop, 0 < n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact Nat.succ_le_iff.mp hn
  filter_upwards [hafw_small, htrace_small, hn_pos] with n hafw_bound htrace_bound hn
  let ρn : State (Prod (TensorPower a n) (TensorPower b n)) := ρ.tensorPowerBipartite n
  let center : SubnormalizedState (Prod (TensorPower a n) (TensorPower b n)) :=
    ρn.toSubnormalized
  let B : ℝ :=
    ρn.conditionalEntropy +
      afwContinuityModulus (Fintype.card (TensorPower a n)) ε - log2 δ
  have hcenter_trace : center.matrix.trace.re = 1 := by
    have htr : center.matrix.trace = 1 := by
      simpa [center] using (State.toSubnormalized_trace ρn)
    rw [htr]
    norm_num
  have hε_sqrt : ε < Real.sqrt center.matrix.trace.re := by
    rw [hcenter_trace]
    simpa using hε1
  have hne :
      ({h : ℝ |
        SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := TensorPower a n)
          center ε h}).Nonempty :=
    center.SmoothConditionalMinEntropyCandidateRaw_set_nonempty_of_nonneg
      (a := TensorPower a n) (le_of_lt hε0)
  have hbdd :
      BddAbove {h : ℝ |
        SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := TensorPower a n)
          center ε h} :=
    center.SmoothConditionalMinEntropyCandidateRaw_bddAbove_of_lt_sqrt_trace
      (a := TensorPower a n) hε_sqrt
  have hcand_le :
      ∀ h : ℝ,
        SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := TensorPower a n)
          center ε h →
        h ≤ B := by
    intro h hh
    rcases hh with ⟨τ, hball, rfl⟩
    have hτ_trace_floor : δ ≤ τ.matrix.trace.re := by
      dsimp [δ]
      simpa [hcenter_trace] using center.purifiedBall_trace_lower_bound τ hε_sqrt hball
    have hτ_trace_pos : 0 < τ.matrix.trace.re := lt_of_lt_of_le hδpos hτ_trace_floor
    let τhat : State (Prod (TensorPower a n) (TensorPower b n)) :=
      τ.normalize hτ_trace_pos.ne'
    have hmin_norm :
        τ.conditionalMinEntropyRaw ≤ τhat.conditionalEntropy - log2 τ.matrix.trace.re := by
      rw [SubnormalizedState.conditionalMinEntropy_eq_normalize_sub_log2_trace
        (a := TensorPower a n) (b := TensorPower b n) τ hτ_trace_pos]
      exact sub_le_sub_right (horder n τhat) _
    have hball_norm : ρn.purifiedBall ε τhat := by
      exact SubnormalizedState.purifiedBall_normalize_of_toSubnormalized_purifiedBall
        (ρ := ρn) (τ := τ) hτ_trace_pos hball
    have hdist : ρn.normalizedTraceDistance τhat ≤ ε := by
      exact (State.fuchs_van_de_graaf_upper ρn τhat).trans hball_norm
    have hafw :
        |ρn.conditionalEntropy - τhat.conditionalEntropy| ≤
          afwContinuityModulus (Fintype.card (TensorPower a n)) ε :=
      State.alickiFannesWinter_conditionalEntropy ρn τhat ε hdist
    have hent_le :
        τhat.conditionalEntropy ≤
          ρn.conditionalEntropy +
            afwContinuityModulus (Fintype.card (TensorPower a n)) ε := by
      have hleft := (abs_le.mp hafw).1
      linarith
    have hlog :
        -log2 τ.matrix.trace.re ≤ -log2 δ := by
      unfold log2
      have hlog_le : Real.log δ ≤ Real.log τ.matrix.trace.re :=
        Real.log_le_log hδpos hτ_trace_floor
      have hdiv := div_le_div_of_nonneg_right hlog_le
        (le_of_lt (Real.log_pos one_lt_two))
      exact neg_le_neg hdiv
    dsimp [B, τhat] at *
    linarith
  have hsmooth_le :
      center.smoothConditionalMinEntropyRaw ε ≤ B := by
    rw [SubnormalizedState.smoothConditionalMinEntropyRaw_eq_sSup_candidates]
    exact csSup_le hne hcand_le
  have hrate_le :
      ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRateRaw ε n ≤
        ρ.conditionalEntropy +
          afwContinuityModulus (Fintype.card (TensorPower a n)) ε / (n : ℝ) +
          (-log2 δ) / (n : ℝ) := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hmul := mul_le_mul_of_nonneg_left hsmooth_le
      (by positivity : 0 ≤ (1 / (n : ℝ)))
    have hentropy : ρn.conditionalEntropy = (n : ℝ) * ρ.conditionalEntropy := by
      dsimp [ρn]
      exact ρ.tensorPowerBipartite_conditionalEntropy n
    rw [State.tensorPowerSubnormalizedSmoothConditionalMinEntropyRateRaw_eq,
      State.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_eq]
    change (1 / (n : ℝ)) * center.smoothConditionalMinEntropyRaw ε ≤ _ at hmul
    change (1 / (n : ℝ)) * center.smoothConditionalMinEntropyRaw ε ≤ _
    calc
      (1 / (n : ℝ)) * center.smoothConditionalMinEntropyRaw ε
          ≤ (1 / (n : ℝ)) * B := hmul
      _ = (1 / (n : ℝ)) *
            (ρn.conditionalEntropy +
              afwContinuityModulus (Fintype.card (TensorPower a n)) ε - log2 δ) := by
          rfl
      _ ≤ ρ.conditionalEntropy +
            afwContinuityModulus (Fintype.card (TensorPower a n)) ε / (n : ℝ) +
            (-log2 δ) / (n : ℝ) := by
          rw [hentropy]
          field_simp [hnR.ne']
          ring_nf
          exact le_rfl
  change ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRateRaw ε n ≤
    ρ.conditionalEntropy + γ
  exact le_of_lt <| by
    calc
      ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRateRaw ε n
          ≤ ρ.conditionalEntropy +
            afwContinuityModulus (Fintype.card (TensorPower a n)) ε / (n : ℝ) +
            (-log2 δ) / (n : ℝ) := hrate_le
      _ < ρ.conditionalEntropy +
            (2 * ε * log2 (Fintype.card a : ℝ) + γ / 3) + γ / 3 := by
          linarith
      _ < ρ.conditionalEntropy + γ := by
          linarith

/-- Max-rate handoff supplied by smooth min/max duality and von Neumann
conditional-entropy duality in the source proof. -/
def SmoothMaxRateFromMinDuality (ρ : State (Prod a b)) : Prop :=
  SourceFiniteDomainTwoStageLimitTo
    (fun ε hε_nonneg hε_lt_one n =>
      ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate
        ε n hε_nonneg hε_lt_one)
    ρ.conditionalEntropy

/-- Pointwise duality profile behind the source's max-entropy half.

`dualMinRate` is the normalized smooth-min rate of the complementary purified
system, while `dualEntropy` is its conditional von Neumann entropy.  The two
equalities are the smooth min/max duality and conditional-entropy duality used
in TCR 2008 after the min half is proved. -/
def SmoothMaxRateDualityProfile
    (ρ : State (Prod a b))
    (dualMinRate : (ε : ℝ) → 0 ≤ ε → ε < 1 → ℕ → ℝ)
    (dualEntropy : ℝ) : Prop :=
  SourceFiniteDomainTwoStageLimitTo dualMinRate dualEntropy ∧
    (∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      ∀ (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1),
        ∀ᶠ n in atTop,
          ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate
              ε n hε_nonneg hε_lt_one =
            -dualMinRate ε hε_nonneg hε_lt_one n) ∧
    ρ.conditionalEntropy = -dualEntropy

/-- Source max half obtained from the min half on a complementary system plus
the two dualities stated in `SmoothMaxRateDualityProfile`. -/
theorem SmoothMaxRateFromMinDuality.of_profile
    (ρ : State (Prod a b))
    {dualMinRate : (ε : ℝ) → 0 ≤ ε → ε < 1 → ℕ → ℝ}
    {dualEntropy : ℝ}
    (hprofile : ρ.SmoothMaxRateDualityProfile dualMinRate dualEntropy) :
    ρ.SmoothMaxRateFromMinDuality := by
  rcases hprofile with ⟨hdual_limit, hrate_dual, hentropy_dual⟩
  intro γ hγ
  filter_upwards [hdual_limit γ hγ, hrate_dual] with ε hε hεrate
  intro hε_nonneg hε_lt_one
  filter_upwards [hε hε_nonneg hε_lt_one, hεrate hε_nonneg hε_lt_one]
    with n hn hnrate
  rw [hnrate, hentropy_dual]
  have hdiff :
      -dualMinRate ε hε_nonneg hε_lt_one n - -dualEntropy =
        -(dualMinRate ε hε_nonneg hε_lt_one n - dualEntropy) := by
    ring
  rw [hdiff]
  simpa only [abs_neg] using hn

/-- Source max half for a pure tripartite state: smooth min/max duality plus
conditional von Neumann entropy duality transport the min AEP on `AC` to the
max AEP on `AB`. -/
theorem SmoothMaxRateFromMinDuality.of_pure_min_complement
    {c : Type*} [Fintype c] [DecidableEq c]
    [Nonempty a] [Nonempty b] [Nonempty c]
    (Ψ : PureVector (Prod (Prod a b) c))
    (hminAC :
      SourceFiniteDomainTwoStageLimitTo
        (fun ε hε_nonneg hε_lt_one n =>
          Ψ.state.marginalAC.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
            ε n hε_nonneg hε_lt_one)
        Ψ.state.marginalAC.conditionalEntropy) :
    State.SmoothMaxRateFromMinDuality Ψ.state.marginalAB := by
  refine State.SmoothMaxRateFromMinDuality.of_profile Ψ.state.marginalAB
    (dualMinRate :=
      fun ε hε_nonneg hε_lt_one n =>
        Ψ.state.marginalAC.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
          ε n hε_nonneg hε_lt_one)
    (dualEntropy := Ψ.state.marginalAC.conditionalEntropy) ?_
  refine ⟨hminAC, ?_, ?_⟩
  · filter_upwards [] with ε
    intro hε0 hε1
    filter_upwards [] with n
    exact
      PureVector.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate_marginalAB_eq_neg_min_marginalAC
        (a := a) (b := b) (c := c) Ψ hε0 hε1 n
  · simpa using
      (State.PureVector.conditionalEntropy_marginalAB_eq_neg_marginalAC
        (a := a) (b := b) (c := c) Ψ)

/-- Source max half for an arbitrary bipartite state, assuming the min half is
available for every finite complementary system.

This packages the exact TCR route for the smooth-max limit: choose a
purification of `ρ_AB`, apply the already-proved smooth min AEP to the
complementary `AC` marginal, then use smooth min/max duality and conditional
von Neumann entropy duality. -/
theorem SmoothMaxRateFromMinDuality.of_all_min
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b))
    (hminAll :
      ∀ {c : Type (max u v)} [Fintype c] [DecidableEq c] [Nonempty c],
        ∀ σ : State (Prod a c),
          SourceFiniteDomainTwoStageLimitTo
            (fun ε hε_nonneg hε_lt_one n =>
              σ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
                ε n hε_nonneg hε_lt_one)
            σ.conditionalEntropy) :
    ρ.SmoothMaxRateFromMinDuality := by
  let Ω : PureVector (Prod (Prod a b) (Prod a b)) :=
    ρ.canonicalPurification.reindex (Equiv.prodComm (Prod a b) (Prod a b))
  have hAB : Ω.state.marginalAB = ρ := by
    apply State.ext
    simpa [Ω, State.marginalAB_eq_marginalA, PureVector.reindex_state, State.reindex,
      State.marginalA, State.marginalB, partialTraceA, partialTraceB,
      PureVector.state_matrix, rankOneMatrix_apply] using
      ρ.canonicalPurification_purifies
  have hmaxΩ : Ω.state.marginalAB.SmoothMaxRateFromMinDuality :=
    State.SmoothMaxRateFromMinDuality.of_pure_min_complement
      (a := a) (b := b) (c := Prod a b) Ω
      (hminAll (c := Prod a b) Ω.state.marginalAC)
  rwa [hAB] at hmaxΩ

end State

/- Asymptotic AEP (thm:qaep):

lim_{eps->0} lim_{n->infty} (1/n) H^eps_min(A^n|B^n) = H(A|B)_rho,
and the analogous statement for smooth max-entropy.

This declaration records the source-shaped statement.  The min half follows
from the finite-N AEP lower bound plus the ordering/AFW continuity upper
bound; the max half is transported by smooth min/max duality and conditional
von Neumann entropy duality. -/
def asymptoticAEPTwoStage_statement
    (ρ : State (Prod a b)) : Prop :=
  SourceFiniteDomainTwoStageLimitTo
      (fun ε hε_nonneg hε_lt_one n =>
        ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
          ε n hε_nonneg hε_lt_one)
      ρ.conditionalEntropy ∧
    SourceFiniteDomainTwoStageLimitTo
      (fun ε hε_nonneg hε_lt_one n =>
        ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate
          ε n hε_nonneg hε_lt_one)
      ρ.conditionalEntropy

/-- Literal finite-domain iterated-limit statement of the fully quantum AEP.

For every fixed `ε ∈ (0,1)`, the inner blocklength limit exists and equals
`H(A|B)_ρ`; the outer limit is therefore the limit of the constant inner-limit
function as `ε → 0` within the source domain. -/
def asymptoticAEP_statement
    (ρ : State (Prod a b)) : Prop :=
  FiniteDomainAEPDoubleLimit
      (fun ε hε_nonneg hε_lt_one n =>
        ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
          ε n hε_nonneg hε_lt_one)
      (fun _ => ρ.conditionalEntropy) ρ.conditionalEntropy ∧
    FiniteDomainAEPDoubleLimit
      (fun ε hε_nonneg hε_lt_one n =>
        ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate
          ε n hε_nonneg hε_lt_one)
      (fun _ => ρ.conditionalEntropy) ρ.conditionalEntropy

namespace State

/-- Source-aligned assembly of the min-entropy half of `thm:qaep`.

The two inputs are exactly the two mathematical ingredients used in the source:
the finite-N AEP lower bound and the ordering-plus-continuity upper bound. -/
theorem asymptoticAEPMin_statement_of_finiteNAEP_and_continuity
    (ρ : State (Prod a b))
    (hlower : ρ.SmoothMinRateLowerFromFiniteNAEP)
    (hupper : ρ.SmoothMinRateUpperFromContinuity) :
    SourceFiniteDomainTwoStageLimitTo
      (fun ε hε_nonneg hε_lt_one n =>
        ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
          ε n hε_nonneg hε_lt_one)
      ρ.conditionalEntropy :=
  SourceFiniteDomainTwoStageLimitTo.of_eventually_squeeze hlower hupper

/-- Source-aligned assembly of the full asymptotic fully quantum AEP.

The max-entropy half is deliberately exposed as a duality handoff: in TCR 2008
it is obtained from the min-entropy half by smooth min/max duality and
conditional von Neumann entropy duality, not by a separate finite-N max bound. -/
theorem asymptoticAEPTwoStage_statement_of_min_and_max_duality
    (ρ : State (Prod a b))
    (hmin :
      SourceFiniteDomainTwoStageLimitTo
        (fun ε hε_nonneg hε_lt_one n =>
          ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
            ε n hε_nonneg hε_lt_one)
        ρ.conditionalEntropy)
    (hmax : ρ.SmoothMaxRateFromMinDuality) :
    QIT.asymptoticAEPTwoStage_statement ρ :=
  ⟨hmin, hmax⟩

/-- Assemble the literal AEP statement from fixed-smoothing inner limits.

This is the analysis bridge absent from the earlier two-stage formulation:
the hypotheses assert an actual `n → ∞` limit for each admissible smoothing
radius, not merely a jointly eventual squeeze as `ε → 0`. -/
theorem asymptoticAEP_statement_of_fixed_epsilon_limits
    (ρ : State (Prod a b))
    (hmin : ∀ (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_one : ε < 1),
      Tendsto
        (fun n : ℕ =>
          ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
            ε n (le_of_lt hε_pos) hε_lt_one)
        atTop (nhds ρ.conditionalEntropy))
    (hmax : ∀ (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_one : ε < 1),
      Tendsto
        (fun n : ℕ =>
          ρ.tensorPowerSubnormalizedSmoothConditionalMaxEntropyRate
            ε n (le_of_lt hε_pos) hε_lt_one)
        atTop (nhds ρ.conditionalEntropy)) :
    QIT.asymptoticAEP_statement ρ := by
  constructor
  · refine FiniteDomainAEPDoubleLimit.of_inner_outer ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with ε hε
    intro hε_nonneg hε_lt_one
    simpa only using hmin ε hε.1 hε.2
  · refine FiniteDomainAEPDoubleLimit.of_inner_outer ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with ε hε
    intro hε_nonneg hε_lt_one
    simpa only using hmax ε hε.1 hε.2

end State

end

end QIT
