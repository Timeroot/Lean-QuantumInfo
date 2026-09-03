/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.HypothesisTesting.Basic
public import QIT.States.TraceNorm.Audenaert
public import QIT.Symmetry.SymmetricSubspace
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Topology.Instances.EReal.Lemmas
public import QIT.Information.BinaryHypothesisTest

/-!
# Chernoff and Nussbaum--Szkola support

This module contains the reusable Chernoff coefficient, classical finite-alphabet,
method-of-types, and single-copy Nussbaum--Szkola support used by both the
Renyi endpoint layer and the downstream asymptotic QCB theorem route.

It intentionally stops before the tensor-power quantum-to-classical comparison
route and the final asymptotic quantum Chernoff bound theorem.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal ENNReal Topology
open Filter Matrix Polynomial

namespace QIT

universe u v

noncomputable section


variable {a : Type u} [Fintype a] [DecidableEq a]

namespace State


/-- Audenaert's trace inequality gives the one-shot Chernoff coefficient lower bound.

This is the equal-prior direct-bound bridge:
`1 - D(ρ,σ) ≤ Tr(ρ^s σ^(1-s))` for `0 ≤ s ≤ 1`, with `D` the repository's
normalized trace distance.  It is derived from the registered Audenaert
primitive [Audenaert2006QuantumChernoff, audenaert-2006-quantum-chernoff.tex:296-306]. -/
theorem one_sub_normalizedTraceDistance_le_petzRenyiCoefficient
    (rho sigma : State a) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    1 - rho.normalizedTraceDistance sigma ≤
      (rho.petzRenyiCoefficient sigma s : ℝ) := by
  have hAud := audenaertTraceInequality (a := a) (s := s) hs0 hs1 rho.pos sigma.pos
  have hcoeff :
      (rho.petzRenyiCoefficient sigma s : ℝ) =
        ((CFC.rpow rho.matrix s * CFC.rpow sigma.matrix (1 - s)).trace).re := rfl
  have htraceNorm :
      traceNorm (rho.matrix - sigma.matrix) =
        (CFC.abs (rho.matrix - sigma.matrix)).trace.re := rfl
  have hrhs :
      ((rho.matrix + sigma.matrix - CFC.abs (rho.matrix - sigma.matrix)).trace).re / 2 =
        1 - rho.normalizedTraceDistance sigma := by
    rw [State.normalizedTraceDistance_eq_matrix, QIT.normalizedTraceDistance_eq]
    simp [QIT.traceNormDistance]
    rw [htraceNorm]
    simp [rho.trace_eq_one, sigma.trace_eq_one]
    ring
  rw [hcoeff]
  exact hrhs ▸ hAud


end State

namespace BinaryHypothesisTest

/-- The normalized extended negative log `-(1/(n+1)) log x`. -/
def normalizedNegLog (n : Nat) (x : ℝ≥0∞) : EReal :=
  -(((((n + 1 : Nat) : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log x)

/-- The finite real counterpart of `normalizedNegLog`, using `ENNReal.toReal`. -/
def normalizedNegLogReal (n : Nat) (x : ℝ≥0∞) : ℝ :=
  -((((n + 1 : Nat) : ℝ)⁻¹ : ℝ) * Real.log x.toReal)

/-- A zero input makes the normalized extended negative log equal to `⊤`. -/
theorem normalizedNegLog_eq_top_of_eq_zero (n : Nat) (x : ℝ≥0∞) (hx : x = 0) :
    normalizedNegLog n x = ⊤ := by
  have hpos : 0 < ((↑n + 1 : ℝ)⁻¹ : ℝ) := by
    exact inv_pos.mpr (by positivity)
  simp [normalizedNegLog, hx, EReal.coe_mul_bot_of_pos hpos]

/-- On positive finite inputs, `normalizedNegLog` is the coercion of its real counterpart. -/
theorem normalizedNegLog_eq_coe_real_of_ne_zero_ne_top
    (n : Nat) (x : ℝ≥0∞) (h0 : x ≠ 0) (htop : x ≠ ⊤) :
    normalizedNegLog n x = ((normalizedNegLogReal n x : ℝ) : EReal) := by
  simp [normalizedNegLog, normalizedNegLogReal, ENNReal.log_pos_real h0 htop,
    EReal.coe_mul, EReal.coe_neg]

/-- Positive real inputs reduce the normalized extended negative log to the
ordinary natural-log expression. -/
theorem normalizedNegLog_ofReal_eq_coe_real (n : Nat) {x : ℝ}
    (hx : 0 < x) :
    normalizedNegLog n (ENNReal.ofReal x) =
      ((-((((n + 1 : Nat) : ℝ)⁻¹) * Real.log x) : ℝ) : EReal) := by
  rw [normalizedNegLog_eq_coe_real_of_ne_zero_ne_top]
  · unfold normalizedNegLogReal
    rw [ENNReal.toReal_ofReal hx.le]
  · exact ENNReal.ofReal_ne_zero_iff.mpr hx
  · exact ENNReal.ofReal_ne_top

/-- The normalized extended negative log is order reversing in its error input. -/
theorem normalizedNegLog_antitone (n : Nat) {x y : ℝ≥0∞} (hxy : x ≤ y) :
    normalizedNegLog n y ≤ normalizedNegLog n x := by
  unfold normalizedNegLog
  have hlog : ENNReal.log x ≤ ENNReal.log y := ENNReal.log_le_log hxy
  have hcoef : (0 : EReal) ≤ (((((n + 1 : Nat) : ℝ)⁻¹ : ℝ) : EReal)) := by
    positivity
  apply EReal.neg_le_neg_iff.mpr
  exact mul_le_mul_of_nonneg_left hlog hcoef

/-- A probability-valued `ℝ≥0∞` input bounded by one is finite. -/
theorem ennreal_ne_top_of_le_one (x : ℝ≥0∞) (hx : x ≤ 1) : x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top hx

/-- Finite real normalized logs lift to finite `EReal` limits. -/
theorem normalizedNegLog_tendsto_coe_of_eventually_ne_zero_ne_top_real_tendsto
    {x : Nat → ℝ≥0∞} {L : ℝ}
    (hfinite : ∀ᶠ n in atTop, x n ≠ 0 ∧ x n ≠ ⊤)
    (hlim : Tendsto (fun n : Nat => normalizedNegLogReal n (x n)) atTop (𝓝 L)) :
    Tendsto (fun n : Nat => normalizedNegLog n (x n)) atTop (𝓝 (L : EReal)) := by
  refine (EReal.tendsto_coe.mpr hlim).congr' (hfinite.mono ?_)
  intro n hn
  exact (normalizedNegLog_eq_coe_real_of_ne_zero_ne_top n (x n) hn.1 hn.2).symm

/-- Real normalized logs tending to `+∞` lift to the `EReal` top limit. -/
theorem normalizedNegLog_tendsto_top_of_eventually_ne_top_real_tendsto_atTop
    {x : Nat → ℝ≥0∞}
    (htop : ∀ᶠ n in atTop, x n ≠ ⊤)
    (hlim : Tendsto (fun n : Nat => normalizedNegLogReal n (x n)) atTop atTop) :
    Tendsto (fun n : Nat => normalizedNegLog n (x n)) atTop (𝓝 (⊤ : EReal)) := by
  have hnonzero : ∀ᶠ n in atTop, x n ≠ 0 := by
    have hgt : ∀ᶠ n in atTop, (0 : ℝ) < normalizedNegLogReal n (x n) :=
      hlim.eventually_gt_atTop 0
    filter_upwards [hgt] with n hn hx
    have hz : normalizedNegLogReal n (x n) = 0 := by
      simp [normalizedNegLogReal, hx]
    linarith
  refine (EReal.tendsto_coe_nhds_top_iff.mpr hlim).congr'
    ((hnonzero.and htop).mono ?_)
  intro n hn
  exact (normalizedNegLog_eq_coe_real_of_ne_zero_ne_top n (x n) hn.1 hn.2).symm

/-- If the input sequence is eventually zero, the normalized extended negative log tends to `⊤`. -/
theorem normalizedNegLog_tendsto_top_of_eventually_eq_zero
    {x : Nat → ℝ≥0∞}
    (hzero : ∀ᶠ n in atTop, x n = 0) :
    Tendsto (fun n : Nat => normalizedNegLog n (x n)) atTop (𝓝 (⊤ : EReal)) := by
  refine tendsto_const_nhds.congr' (hzero.mono ?_)
  intro n hn
  exact (normalizedNegLog_eq_top_of_eq_zero n (x n) hn).symm

/-- Optimal equal-prior error over all binary tests on `n` IID copies. -/
def optimalEqualPriorTensorPowerError (rho sigma : State a) (n : Nat) : ℝ≥0∞ :=
  ⨅ T : TensorPowerHypothesisTest a n, (T.equalPriorTensorPowerError rho sigma : ℝ≥0∞)

/-- The optimal tensor-power equal-prior error is bounded by one. -/
theorem optimalEqualPriorTensorPowerError_le_one (rho sigma : State a) (n : Nat) :
    optimalEqualPriorTensorPowerError rho sigma n ≤ 1 := by
  classical
  have hT :
      (BinaryHypothesisTest.equalPriorTensorPowerError
        ((State.tensorPower rho n).helstromTest (State.tensorPower sigma n))
        rho sigma : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast (BinaryHypothesisTest.equalPriorError_le_one
      ((State.tensorPower rho n).helstromTest (State.tensorPower sigma n))
      (State.tensorPower rho n) (State.tensorPower sigma n))
  exact (iInf_le _ ((State.tensorPower rho n).helstromTest (State.tensorPower sigma n))).trans hT

/-- The optimal tensor-power equal-prior error is finite. -/
theorem optimalEqualPriorTensorPowerError_ne_top (rho sigma : State a) (n : Nat) :
    optimalEqualPriorTensorPowerError rho sigma n ≠ ⊤ :=
  ennreal_ne_top_of_le_one
    (optimalEqualPriorTensorPowerError rho sigma n)
    (optimalEqualPriorTensorPowerError_le_one rho sigma n)

/-- Audenaert-derived finite-`n` upper bound for the optimal equal-prior error.

For every `0 ≤ s ≤ 1`, the optimal error on `n` IID copies is bounded by
`1/2 * (Tr(ρ^s σ^(1-s)))^n`, matching the direct finite-copy route registered
from [Gour2024Resources, BookQRT.tex:15887-15909].  The asymptotic squeeze and
converse are intentionally downstream. -/
theorem optimalEqualPriorTensorPowerError_le_half_petzRenyiCoefficient_pow
    (rho sigma : State a) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n : Nat) :
    optimalEqualPriorTensorPowerError rho sigma n ≤
      (((1 / 2 : ℝ≥0) * (rho.petzRenyiCoefficient sigma s) ^ n : ℝ≥0) : ℝ≥0∞) := by
  classical
  let T : TensorPowerHypothesisTest a n :=
    (State.tensorPower rho n).helstromTest (State.tensorPower sigma n)
  have hChernoff :
      1 - (State.tensorPower rho n).normalizedTraceDistance (State.tensorPower sigma n) ≤
        ((rho.petzRenyiCoefficient sigma s) ^ n : ℝ) := by
    have h :=
      State.one_sub_normalizedTraceDistance_le_petzRenyiCoefficient
        (rho.tensorPower n) (sigma.tensorPower n) hs0 hs1
    rwa [State.petzRenyiCoefficient_tensorPower rho sigma hs0 hs1 n] at h
  have hHelstrom :
      (T.equalPriorTensorPowerError rho sigma : ℝ) =
        (1 / 2 : ℝ) *
          (1 - (State.tensorPower rho n).normalizedTraceDistance (State.tensorPower sigma n)) := by
    simpa [T, BinaryHypothesisTest.equalPriorTensorPowerError] using
      State.helstromTest_equalPriorError_eq (rho.tensorPower n) (sigma.tensorPower n)
  have hTest :
      (T.equalPriorTensorPowerError rho sigma : ℝ) ≤
        ((1 / 2 : ℝ≥0) * (rho.petzRenyiCoefficient sigma s) ^ n : ℝ≥0) := by
    rw [hHelstrom]
    exact mul_le_mul_of_nonneg_left hChernoff (by norm_num)
  have hTestENN :
      (T.equalPriorTensorPowerError rho sigma : ℝ≥0∞) ≤
        (((1 / 2 : ℝ≥0) * (rho.petzRenyiCoefficient sigma s) ^ n : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast hTest
  exact (iInf_le _ T).trans hTestENN

/-- The `1 / 2` finite-copy prefactor does not change the direct Chernoff exponent lift.

For copy number `n + 1`, the inequality is proved by taking the
`1 / (n + 1)`-power of `(1 / 2) * c ^ (n + 1)` and using
`((1 / 2) * c ^ (n + 1)) ^ (1 / (n + 1)) ≤ c`. This explicitly covers the
zero-coefficient case, where both logarithmic sides are infinite after negation. -/
theorem petzChernoffExponent_le_normalizedNegLog_half_petzRenyiCoefficient_pow
    (rho sigma : State a) (s : ℝ) (n : Nat) :
    rho.petzChernoffExponent sigma s ≤
      normalizedNegLog n
        ((((1 / 2 : ℝ≥0) * (rho.petzRenyiCoefficient sigma s) ^ (n + 1) : ℝ≥0) :
          ℝ≥0∞)) := by
  let c : ℝ≥0 := rho.petzRenyiCoefficient sigma s
  have hroot :
      (((((1 / 2 : ℝ≥0) * c ^ (n + 1) : ℝ≥0) : ℝ≥0∞) ^
          (((n + 1 : Nat) : ℝ)⁻¹)) ≤ (c : ℝ≥0∞)) := by
    have hN : (n + 1 : Nat) ≠ 0 := by omega
    have ha_nonneg : 0 ≤ (((n + 1 : Nat) : ℝ)⁻¹) := by positivity
    calc
      ((((1 / 2 : ℝ≥0) * c ^ (n + 1) : ℝ≥0) : ℝ≥0∞) ^
          (((n + 1 : Nat) : ℝ)⁻¹))
          = (((1 / 2 : ℝ≥0) : ℝ≥0∞) * ((c : ℝ≥0∞) ^ (n + 1))) ^
              (((n + 1 : Nat) : ℝ)⁻¹) := by
            norm_num
      _ = (((1 / 2 : ℝ≥0) : ℝ≥0∞) ^ (((n + 1 : Nat) : ℝ)⁻¹)) *
            (((c : ℝ≥0∞) ^ (n + 1)) ^ (((n + 1 : Nat) : ℝ)⁻¹)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ ha_nonneg]
      _ = (((1 / 2 : ℝ≥0) : ℝ≥0∞) ^ (((n + 1 : Nat) : ℝ)⁻¹)) *
            (c : ℝ≥0∞) := by
          rw [ENNReal.pow_rpow_inv_natCast hN]
      _ ≤ 1 * (c : ℝ≥0∞) := by
          gcongr
          exact ENNReal.rpow_le_one (by norm_num) ha_nonneg
      _ = (c : ℝ≥0∞) := by simp
  have hlogroot := ENNReal.log_le_log hroot
  unfold normalizedNegLog
  apply EReal.neg_le_neg_iff.mpr
  simpa [State.petzChernoffExponent, c, ENNReal.log_rpow] using hlogroot

/-- Exact exponent sequence `n ↦ -(1/(n+1)) log P*_{e,n+1}`. -/
def optimalEqualPriorTensorPowerErrorExponent (rho sigma : State a) (n : Nat) : EReal :=
  normalizedNegLog n (optimalEqualPriorTensorPowerError rho sigma (n + 1))

/-- The optimal-error exponent is the normalized extended negative log at index `n + 1`. -/
theorem optimalEqualPriorTensorPowerErrorExponent_eq_normalizedNegLog
    (rho sigma : State a) (n : Nat) :
    optimalEqualPriorTensorPowerErrorExponent rho sigma n =
      normalizedNegLog n (optimalEqualPriorTensorPowerError rho sigma (n + 1)) := rfl

/-- Direct finite-copy exponent lift from Audenaert's upper bound.

The exponent index `n` uses exactly `n + 1` tensor copies through
`optimalEqualPriorTensorPowerErrorExponent`, so the finite-copy theorem is
instantiated at copy number `n + 1`. -/
theorem petzChernoffExponent_le_optimalEqualPriorTensorPowerErrorExponent
    (rho sigma : State a) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n : Nat) :
    rho.petzChernoffExponent sigma s ≤
      optimalEqualPriorTensorPowerErrorExponent rho sigma n := by
  have hfinite :
      optimalEqualPriorTensorPowerError rho sigma (n + 1) ≤
        ((((1 / 2 : ℝ≥0) * (rho.petzRenyiCoefficient sigma s) ^ (n + 1) : ℝ≥0) :
          ℝ≥0∞)) :=
    optimalEqualPriorTensorPowerError_le_half_petzRenyiCoefficient_pow
      rho sigma hs0 hs1 (n + 1)
  have hnormalized :
      normalizedNegLog n
          ((((1 / 2 : ℝ≥0) * (rho.petzRenyiCoefficient sigma s) ^ (n + 1) :
            ℝ≥0) : ℝ≥0∞)) ≤
        optimalEqualPriorTensorPowerErrorExponent rho sigma n := by
    simpa [optimalEqualPriorTensorPowerErrorExponent] using
      normalizedNegLog_antitone n hfinite
  exact
    (petzChernoffExponent_le_normalizedNegLog_half_petzRenyiCoefficient_pow
      rho sigma s n).trans hnormalized

/-- The direct QCB upper-side exponent hypothesis supplied unconditionally by the
finite-copy Audenaert bound.

This is the direct-side hypothesis consumed by the liminf bridge. -/
theorem eventually_petzChernoffExponent_le_optimalEqualPriorTensorPowerErrorExponent
    (rho sigma : State a) :
    ∀ s : Set.Icc (0 : ℝ) 1,
      ∀ᶠ n in atTop,
        rho.petzChernoffExponent sigma s.1 ≤
          optimalEqualPriorTensorPowerErrorExponent rho sigma n := by
  intro s
  exact Filter.Eventually.of_forall fun n =>
    petzChernoffExponent_le_optimalEqualPriorTensorPowerErrorExponent
      rho sigma s.2.1 s.2.2 n

/-- Nussbaum--Szkola alphabet size used by the source-backed quantum-to-classical
Chernoff converse route.

For spectral decompositions of two states on a `d`-dimensional space, the
classical comparison distributions are indexed by eigenvector pairs, so the
finite alphabet has `d * d` letters
[Gour2024Resources, BookQRT.tex:15911-15949]. -/
def nussbaumSzkolaAlphabetCard {a : Type u} [Fintype a] : Nat :=
  Fintype.card a * Fintype.card a

/-- The method-of-types polynomial prefactor `(n+1)^(-m)`.

Here `m` is the Nussbaum--Szkola alphabet size.  This records the exact
finite-copy polynomial loss required by the classical Chernoff converse
[Gour2024Resources, BookQRT.tex:15414-15469]. -/
def methodOfTypesPolynomialPrefactor {a : Type u} [Fintype a] (n : Nat) : ℝ≥0∞ :=
  (((n + 1 : Nat) : ℝ≥0∞) ^ nussbaumSzkolaAlphabetCard (a := a))⁻¹

/-- The normalized logarithmic penalty contributed by the method-of-types prefactor.

For the exponent sequence indexed as `n ↦ error (n + 1)`, the source prefactor
`(N + 1)^(-m)` is evaluated at `N = n + 1`, giving the vanishing term
`m * log(n + 2) / (n + 1)`.  The finite alphabet size is the
Nussbaum--Szkola alphabet cardinality `m`
[Gour2024Resources, BookQRT.tex:15414-15469]. -/
def methodOfTypesPolynomialPenalty {a : Type u} [Fintype a] (n : Nat) : EReal :=
  (((nussbaumSzkolaAlphabetCard (a := a) : ℝ) *
      Real.log (((n + 2 : Nat) : ℝ))) / (((n + 1 : Nat) : ℝ)) : ℝ)

/-- Generic finite-alphabet method-of-types prefactor `(n+1)^(-|α|)`.

This is the source prefactor from the classical method-of-types proof before
specializing the alphabet to the Nussbaum--Szkola pair alphabet
[Gour2024Resources, BookQRT.tex:15414-15469]. -/
def finiteAlphabetMethodOfTypesPolynomialPrefactor
    (α : Type u) [Fintype α] (n : Nat) : ℝ≥0∞ :=
  ((((n + 1 : Nat) : ℝ≥0∞) ^ Fintype.card α)⁻¹)

/-- Real form of the generic finite-alphabet method-of-types prefactor. -/
theorem finiteAlphabetMethodOfTypesPolynomialPrefactor_toReal
    (α : Type u) [Fintype α] (n : Nat) :
    (finiteAlphabetMethodOfTypesPolynomialPrefactor α n).toReal =
      ((((n + 1 : Nat) : ℝ) ^ Fintype.card α)⁻¹) := by
  have hbase :
      (((n + 1 : Nat) : ℝ≥0∞).toReal) =
        ((((n + 1 : Nat) : ℝ≥0) : ℝ)) := by
    rw [show ((n + 1 : Nat) : ℝ≥0∞) = (n : ℝ≥0∞) + 1 by norm_num]
    rw [ENNReal.toReal_add (ENNReal.natCast_ne_top n) ENNReal.one_ne_top]
    simp [ENNReal.toReal_natCast, Nat.cast_add, Nat.cast_one]
  unfold finiteAlphabetMethodOfTypesPolynomialPrefactor
  rw [ENNReal.toReal_inv, ENNReal.toReal_pow, hbase]
  simp

/-- A positive lower bound of the form `c * exp (-R*d) ≤ E` converts to the
normalized negative-log upper bound with prefactor penalty. -/
theorem neg_log_div_le_of_mul_exp_neg_le
    {E c d R : ℝ}
    (hR : 0 < R)
    (hc : 0 < c)
    (hE : 0 < E)
    (hbound : c * Real.exp (-R * d) ≤ E) :
    -Real.log E / R ≤ d + (-Real.log c) / R := by
  have hce : 0 < c * Real.exp (-R * d) :=
    mul_pos hc (Real.exp_pos _)
  have hlogle : Real.log (c * Real.exp (-R * d)) ≤ Real.log E :=
    (Real.log_le_log_iff hce hE).mpr hbound
  have hlogeq :
      Real.log (c * Real.exp (-R * d)) =
        Real.log c + (-R * d) := by
    rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hlinear : Real.log c + (-R * d) ≤ Real.log E := by
    rw [hlogeq] at hlogle
    exact hlogle
  have hnum : -Real.log E ≤ R * d + (-Real.log c) := by
    linarith
  rw [div_le_iff₀ hR]
  calc
    -Real.log E ≤ R * d + (-Real.log c) := hnum
    _ = (d + (-Real.log c) / R) * R := by
      field_simp [hR.ne']

/-- The exact natural-log penalty produced by the equal-prior factor and the
finite-alphabet method-of-types prefactor. -/
theorem equalPriorMethodOfTypesPrefactor_log_penalty
    (α : Type u) [Fintype α] {N : Nat} (hN : 0 < N) :
    (-Real.log
        ((1 / 2 : ℝ) *
          (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal)) / (N : ℝ) =
      (Fintype.card α : ℝ) * Real.log (((N + 1 : Nat) : ℝ)) / (N : ℝ) +
        Real.log 2 / (N : ℝ) := by
  have hN_ne : (N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hN
  have hNp1_pos : 0 < (((N + 1 : Nat) : ℝ)) := by
    positivity
  have hpow_pos :
      0 < (((N + 1 : Nat) : ℝ) ^ Fintype.card α) :=
    pow_pos hNp1_pos _
  have hinv_pos :
      0 < ((((N + 1 : Nat) : ℝ) ^ Fintype.card α)⁻¹) :=
    inv_pos.mpr hpow_pos
  rw [finiteAlphabetMethodOfTypesPolynomialPrefactor_toReal]
  have hlog_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    rw [Real.log_inv]
  have hlog_inv :
      Real.log ((((N + 1 : Nat) : ℝ) ^ Fintype.card α)⁻¹) =
        -((Fintype.card α : ℝ) * Real.log (((N + 1 : Nat) : ℝ))) := by
    rw [Real.log_inv]
    rw [Real.log_pow]
  rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) hinv_pos.ne',
    hlog_half, hlog_inv]
  field_simp [hN_ne]
  ring

/-- Empirical binomial mass at the observed count `k`.

This is the binomial probability of observing `k` successes in `N` trials under
the empirical success probability `k / N`. -/
def empiricalBinomialMass (N k : Nat) : ℝ≥0 :=
  (Nat.choose N k : ℝ≥0) *
    (((k : ℝ≥0) / (N : ℝ≥0)) ^ k) *
    ((((N - k : Nat) : ℝ≥0) / (N : ℝ≥0)) ^ (N - k))

/-- Binomial mass at an arbitrary count `j`, using the empirical parameter
selected by the count `k`. -/
def binomialMassAt (N k j : Nat) : ℝ≥0 :=
  (Nat.choose N j : ℝ≥0) *
    (((k : ℝ≥0) / (N : ℝ≥0)) ^ j) *
    ((((N - k : Nat) : ℝ≥0) / (N : ℝ≥0)) ^ (N - j))

private theorem binomialMassAt_succ_cross {N k j : Nat} (hk : k ≤ N) (hj : j < N) :
    binomialMassAt N k (j + 1) *
        (((j + 1 : Nat) * (N - k : Nat) : Nat) : ℝ≥0) =
      binomialMassAt N k j *
        (((N - j : Nat) * k : Nat) : ℝ≥0) := by
  unfold binomialMassAt
  have hchoose := Nat.choose_succ_right_eq N j
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le j) hj))
  have hsub : N - j = N - (j + 1) + 1 := by omega
  have hchooseR :
      ((Nat.choose N (j + 1) : ℝ) * ((j + 1 : Nat) : ℝ)) =
        ((Nat.choose N j : ℝ) * ((N - j : Nat) : ℝ)) := by
    exact_mod_cast hchoose
  have hchooseR' :
      ((Nat.choose N (j + 1) : ℝ) * ((j : ℝ) + 1)) =
        ((Nat.choose N j : ℝ) * ((N : ℝ) - (j : ℝ))) := by
    simpa [Nat.cast_add, Nat.cast_one, Nat.cast_sub hj.le] using hchooseR
  have hchooseRnn :
      ((Nat.choose N (j + 1) : ℝ) * ((j : ℝ) + 1)) =
        ((Nat.choose N j : ℝ) *
          ((((N : ℝ≥0) - (j : ℝ≥0)) : ℝ≥0) : ℝ)) := by
    have hjnn : (j : ℝ≥0) ≤ (N : ℝ≥0) := by exact_mod_cast hj.le
    simpa [NNReal.coe_sub hjnn] using hchooseR'
  have hfrac :
      ((k : ℝ) / (N : ℝ) *
          ((((N : ℝ≥0) - (k : ℝ≥0)) : ℝ≥0) : ℝ)) =
        ((((((N : ℝ≥0) - (k : ℝ≥0)) : ℝ≥0) : ℝ) / (N : ℝ)) * (k : ℝ)) := by
    have hknn : (k : ℝ≥0) ≤ (N : ℝ≥0) := by exact_mod_cast hk
    rw [NNReal.coe_sub hknn]
    field_simp [hN0]
  apply NNReal.eq
  norm_num
  rw [pow_succ']
  rw [hsub, pow_succ']
  rw [show
      ((Nat.choose N (j + 1) : ℝ) *
          ((k : ℝ) / (N : ℝ) * ((k : ℝ) / (N : ℝ)) ^ j) *
          (((((N : ℝ≥0) - (k : ℝ≥0)) : ℝ≥0) : ℝ) / (N : ℝ)) ^ (N - (j + 1)) *
          (((j : ℝ) + 1) *
            (((N : ℝ≥0) - (k : ℝ≥0) : ℝ≥0) : ℝ))) =
        (((Nat.choose N (j + 1) : ℝ) * ((j : ℝ) + 1)) *
          ((k : ℝ) / (N : ℝ)) ^ j *
          (((((N : ℝ≥0) - (k : ℝ≥0)) : ℝ≥0) : ℝ) / (N : ℝ)) ^ (N - (j + 1)) *
          (((k : ℝ) / (N : ℝ)) *
            (((N : ℝ≥0) - (k : ℝ≥0) : ℝ≥0) : ℝ))) by ring]
  rw [show
      ((Nat.choose N j : ℝ) * ((k : ℝ) / (N : ℝ)) ^ j *
          ((((((N : ℝ≥0) - (k : ℝ≥0)) : ℝ≥0) : ℝ) / (N : ℝ)) *
            (((((N : ℝ≥0) - (k : ℝ≥0)) : ℝ≥0) : ℝ) / (N : ℝ)) ^ (N - (j + 1))) *
          (((((N : ℝ≥0) - (j : ℝ≥0)) : ℝ≥0) : ℝ) * (k : ℝ))) =
        (((Nat.choose N j : ℝ) *
            ((((N : ℝ≥0) - (j : ℝ≥0)) : ℝ≥0) : ℝ)) *
          ((k : ℝ) / (N : ℝ)) ^ j *
          (((((N : ℝ≥0) - (k : ℝ≥0)) : ℝ≥0) : ℝ) / (N : ℝ)) ^ (N - (j + 1)) *
          ((((((N : ℝ≥0) - (k : ℝ≥0)) : ℝ≥0) : ℝ) / (N : ℝ)) * (k : ℝ))) by ring]
  rw [hchooseRnn, hfrac]

private theorem binomial_left_cross_le_right {N k j : Nat} (hjk : j < k) :
    (j + 1) * (N - k) ≤ (N - j) * k := by
  have hjk_succ : j + 1 ≤ k := Nat.succ_le_of_lt hjk
  have hNk_le_Nj : N - k ≤ N - j := Nat.sub_le_sub_left (Nat.le_of_lt hjk) N
  calc
    (j + 1) * (N - k) ≤ k * (N - k) := Nat.mul_le_mul_right _ hjk_succ
    _ = (N - k) * k := Nat.mul_comm _ _
    _ ≤ (N - j) * k := Nat.mul_le_mul_right _ hNk_le_Nj

private theorem binomial_right_cross_le_left {N k j : Nat} (hkj : k ≤ j) :
    (N - j) * k ≤ (j + 1) * (N - k) := by
  have hkj_succ : k ≤ j + 1 := hkj.trans (Nat.le_succ j)
  have hNj_le_Nk : N - j ≤ N - k := Nat.sub_le_sub_left hkj N
  calc
    (N - j) * k ≤ (N - j) * (j + 1) := Nat.mul_le_mul_left _ hkj_succ
    _ = (j + 1) * (N - j) := Nat.mul_comm _ _
    _ ≤ (j + 1) * (N - k) := Nat.mul_le_mul_left _ hNj_le_Nk

private theorem binomialMassAt_le_succ {N k j : Nat}
    (hk : k ≤ N) (hj : j < N) (hjk : j < k) :
    binomialMassAt N k j ≤ binomialMassAt N k (j + 1) := by
  have hcross := binomialMassAt_succ_cross (N := N) (k := k) (j := j) hk hj
  have hc_le_d :
      (((j + 1 : Nat) * (N - k : Nat) : Nat) : ℝ≥0) ≤
        (((N - j : Nat) * k : Nat) : ℝ≥0) := by
    exact_mod_cast binomial_left_cross_le_right (N := N) (k := k) (j := j) hjk
  have hd_pos : 0 < ((((N - j : Nat) * k : Nat) : ℝ≥0)) := by
    exact_mod_cast Nat.mul_pos (Nat.sub_pos_of_lt hj) (Nat.lt_of_le_of_lt (Nat.zero_le j) hjk)
  have hmul :
      binomialMassAt N k j * ((((N - j : Nat) * k : Nat) : ℝ≥0)) ≤
        binomialMassAt N k (j + 1) * ((((N - j : Nat) * k : Nat) : ℝ≥0)) := by
    calc
      binomialMassAt N k j * ((((N - j : Nat) * k : Nat) : ℝ≥0))
          = binomialMassAt N k (j + 1) *
              (((j + 1 : Nat) * (N - k : Nat) : Nat) : ℝ≥0) := hcross.symm
      _ ≤ binomialMassAt N k (j + 1) *
            ((((N - j : Nat) * k : Nat) : ℝ≥0)) :=
          mul_le_mul_of_nonneg_left hc_le_d (by positivity)
  exact (mul_le_mul_iff_right₀ hd_pos).mp (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)

private theorem binomialMassAt_succ_le {N k j : Nat}
    (hk : k ≤ N) (hj : j < N) (hkj : k ≤ j) :
    binomialMassAt N k (j + 1) ≤ binomialMassAt N k j := by
  have hcross := binomialMassAt_succ_cross (N := N) (k := k) (j := j) hk hj
  have hd_le_c :
      (((N - j : Nat) * k : Nat) : ℝ≥0) ≤
        (((j + 1 : Nat) * (N - k : Nat) : Nat) : ℝ≥0) := by
    exact_mod_cast binomial_right_cross_le_left (N := N) (k := k) (j := j) hkj
  have hc_pos : 0 < ((((j + 1 : Nat) * (N - k : Nat) : Nat) : ℝ≥0)) := by
    have hk_lt_N : k < N := hkj.trans_lt hj
    exact_mod_cast Nat.mul_pos (Nat.succ_pos j) (Nat.sub_pos_of_lt hk_lt_N)
  have hmul :
      binomialMassAt N k (j + 1) *
          ((((j + 1 : Nat) * (N - k : Nat) : Nat) : ℝ≥0)) ≤
        binomialMassAt N k j *
          ((((j + 1 : Nat) * (N - k : Nat) : Nat) : ℝ≥0)) := by
    calc
      binomialMassAt N k (j + 1) *
          ((((j + 1 : Nat) * (N - k : Nat) : Nat) : ℝ≥0))
          = binomialMassAt N k j *
              (((N - j : Nat) * k : Nat) : ℝ≥0) := hcross
      _ ≤ binomialMassAt N k j *
            ((((j + 1 : Nat) * (N - k : Nat) : Nat) : ℝ≥0)) :=
          mul_le_mul_of_nonneg_left hd_le_c (by positivity)
  exact (mul_le_mul_iff_right₀ hc_pos).mp (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)

/-- The empirical binomial mass is a mode of the binomial distribution with
parameter `k / N`. -/
theorem binomialMassAt_le_empiricalBinomialMass {N k j : Nat} (hk : k ≤ N) (hj : j ≤ N) :
    binomialMassAt N k j ≤ empiricalBinomialMass N k := by
  have hmode : binomialMassAt N k k = empiricalBinomialMass N k := by
    simp [binomialMassAt, empiricalBinomialMass]
  by_cases hjk : j ≤ k
  · have hchain : binomialMassAt N k j ≤ binomialMassAt N k k := by
      have haux :
          ∀ n (hjn : j ≤ n), n ≤ k -> binomialMassAt N k j ≤ binomialMassAt N k n := by
        intro n hjn
        induction n, hjn using Nat.le_induction with
        | base =>
            intro _
            rfl
        | succ n _ ih =>
            intro hn_succ_le
            have hn_le_k : n ≤ k := Nat.le_of_succ_le hn_succ_le
            have hn_lt_k : n < k := Nat.lt_of_succ_le hn_succ_le
            have hn_lt_N : n < N := hn_lt_k.trans_le hk
            exact (ih hn_le_k).trans (binomialMassAt_le_succ hk hn_lt_N hn_lt_k)
      exact haux k hjk le_rfl
    simpa [hmode] using hchain
  · have hkj : k ≤ j := Nat.le_of_not_ge hjk
    have hchain : binomialMassAt N k j ≤ binomialMassAt N k k := by
      have haux :
          ∀ n (hkn : k ≤ n), n ≤ N -> binomialMassAt N k n ≤ binomialMassAt N k k := by
        intro n hkn
        induction n, hkn using Nat.le_induction with
        | base =>
            intro _
            rfl
        | succ n hkn ih =>
            intro hn_succ_le_N
            have hn_lt_N : n < N := Nat.lt_of_succ_le hn_succ_le_N
            have hn_le_N : n ≤ N := hn_lt_N.le
            exact (binomialMassAt_succ_le hk hn_lt_N hkn).trans (ih hn_le_N)
      exact haux j hkj hj
    simpa [hmode] using hchain

private theorem binomialMassAt_sum_eq_one {N k : Nat} (hN : 0 < N) (hk : k ≤ N) :
    (∑ j : Fin (N + 1), binomialMassAt N k j) = 1 := by
  have hsum :
      (((k : ℝ≥0) / (N : ℝ≥0)) +
        (((N - k : Nat) : ℝ≥0) / (N : ℝ≥0))) = 1 := by
    rw [← add_div]
    have hsum : (k : ℝ≥0) + ((N - k : Nat) : ℝ≥0) = (N : ℝ≥0) := by
      exact_mod_cast (Nat.add_sub_of_le hk)
    rw [hsum]
    exact div_self (by exact_mod_cast hN.ne')
  calc
    (∑ j : Fin (N + 1), binomialMassAt N k j)
        = (((k : ℝ≥0) / (N : ℝ≥0)) +
            (((N - k : Nat) : ℝ≥0) / (N : ℝ≥0))) ^ N := by
          rw [show (((k : ℝ≥0) / (N : ℝ≥0)) +
              (((N - k : Nat) : ℝ≥0) / (N : ℝ≥0))) ^ N =
              ∑ m ∈ Finset.range (N + 1),
                (((k : ℝ≥0) / (N : ℝ≥0)) ^ m *
                  ((((N - k : Nat) : ℝ≥0) / (N : ℝ≥0)) ^ (N - m)) *
                  (Nat.choose N m : ℝ≥0)) by
            rw [add_pow]]
          rw [Finset.sum_fin_eq_sum_range]
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [Finset.mem_range] at hj
          simp [binomialMassAt, hj]
          ring
    _ = 1 := by rw [hsum]; simp

/-- Source-level empirical binomial mode lower bound:
one of the `N+1` binomial masses is at least the average mass. -/
theorem inv_succ_le_empiricalBinomialMass {N k : Nat}
    (hN : 0 < N) (hk : k ≤ N) :
    ((N + 1 : ℝ≥0)⁻¹) ≤ empiricalBinomialMass N k := by
  have hsum := binomialMassAt_sum_eq_one (N := N) (k := k) hN hk
  have hsum_le :
      (∑ j : Fin (N + 1), binomialMassAt N k j) ≤
        ∑ _j : Fin (N + 1), empiricalBinomialMass N k := by
    refine Finset.sum_le_sum ?_
    intro j _
    exact binomialMassAt_le_empiricalBinomialMass
      (N := N) (k := k) (j := j) hk (Nat.le_of_lt_succ j.2)
  have hone_le :
      (1 : ℝ≥0) ≤ (N + 1 : ℝ≥0) * empiricalBinomialMass N k := by
    calc
      (1 : ℝ≥0) = ∑ j : Fin (N + 1), binomialMassAt N k j := hsum.symm
      _ ≤ ∑ _j : Fin (N + 1), empiricalBinomialMass N k := hsum_le
      _ = (N + 1 : ℝ≥0) * empiricalBinomialMass N k := by
        simp [Finset.card_univ]
  have hpos : 0 < (N + 1 : ℝ≥0) := by exact_mod_cast Nat.succ_pos N
  apply (mul_le_mul_iff_right₀ hpos).mp
  calc
    (N + 1 : ℝ≥0) * ((N + 1 : ℝ≥0)⁻¹)
        = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
    _ ≤ (N + 1 : ℝ≥0) * empiricalBinomialMass N k := hone_le

/-- Empirical multinomial mass at the profile itself.

This is the multinomial probability of a type/profile under its empirical
distribution. -/
def empiricalMultinomialMass {α : Type u} [Fintype α] [DecidableEq α]
    {N : Nat} (profile : TensorPowerProfile α N) : ℝ≥0 :=
  (Nat.multinomial Finset.univ profile.1 : ℝ≥0) *
    ∏ z : α, (((profile.1 z : ℝ≥0) / (N : ℝ≥0)) ^ profile.1 z)

private def empiricalMultinomialMassFin {m N : Nat} (f : Fin m → Nat) : ℝ≥0 :=
  (Nat.multinomial Finset.univ f : ℝ≥0) *
    ∏ z : Fin m, (((f z : ℝ≥0) / (N : ℝ≥0)) ^ f z)

private def finTailCounts {m : Nat} (f : Fin (m + 1) → Nat) : Fin m → Nat :=
  fun i => f i.castSucc

private theorem fin_multinomial_last_factor {m : Nat} (f : Fin (m + 1) → Nat) :
    Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) f =
      Nat.choose (∑ i : Fin (m + 1), f i) (f (Fin.last m)) *
        Nat.multinomial (Finset.univ : Finset (Fin m)) (finTailCounts f) := by
  classical
  let s : Finset (Fin (m + 1)) := (Finset.univ : Finset (Fin m)).map Fin.castSuccEmb
  have hlast_not : Fin.last m ∉ s := by
    simp [s]
  have huniv : (Finset.univ : Finset (Fin (m + 1))) = insert (Fin.last m) s := by
    ext i
    constructor
    · intro _
      by_cases hi : i = Fin.last m
      · simp [hi]
      · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        simp [s]
    · intro _
      simp
  have hsum_s :
      ∑ x ∈ s, f x = ∑ i : Fin m, finTailCounts f i := by
    simp [s, finTailCounts]
  have hchoose :
      f (Fin.last m) + ∑ x ∈ s, f x = ∑ i : Fin (m + 1), f i := by
    rw [hsum_s, Fin.sum_univ_castSucc]
    simp [finTailCounts, add_comm]
  have hmult_s :
      Nat.multinomial s f =
        Nat.multinomial (Finset.univ : Finset (Fin m)) (finTailCounts f) := by
    unfold Nat.multinomial
    simp [s, finTailCounts]
  rw [huniv, Nat.multinomial_insert hlast_not]
  rw [hmult_s]
  congr 1
  rw [Finset.sum_insert hlast_not]

private theorem fin_empirical_tail_product_factor {m N : Nat} (f : Fin (m + 1) → Nat)
    (hN : 0 < N)
    (htail_sum : ∑ i : Fin m, finTailCounts f i = N - f (Fin.last m)) :
    (∏ i : Fin m, (((f i.castSucc : ℝ≥0) / (N : ℝ≥0)) ^ f i.castSucc)) =
      ((((N - f (Fin.last m) : Nat) : ℝ≥0) / (N : ℝ≥0)) ^
          (N - f (Fin.last m))) *
        ∏ i : Fin m,
          ((((f i.castSucc : ℝ≥0) /
              ((N - f (Fin.last m) : Nat) : ℝ≥0)) ^ f i.castSucc)) := by
  classical
  by_cases htail0 : N - f (Fin.last m) = 0
  · have hsum0 : ∑ i : Fin m, finTailCounts f i = 0 := by
      simpa [htail0] using htail_sum
    have hcounts0_fun : finTailCounts f = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg
        (fun i => Nat.zero_le (finTailCounts f i))).mp hsum0
    have hcounts0 : ∀ i : Fin m, finTailCounts f i = 0 := by
      intro i
      exact congrFun hcounts0_fun i
    have hleft :
        (∏ i : Fin m, (((f i.castSucc : ℝ≥0) / (N : ℝ≥0)) ^ f i.castSucc)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      have hi : f i.castSucc = 0 := by simpa [finTailCounts] using hcounts0 i
      simp [hi]
    have hright :
        ((((N - f (Fin.last m) : Nat) : ℝ≥0) / (N : ℝ≥0)) ^
            (N - f (Fin.last m))) *
          ∏ i : Fin m,
            ((((f i.castSucc : ℝ≥0) /
                ((N - f (Fin.last m) : Nat) : ℝ≥0)) ^ f i.castSucc)) = 1 := by
      rw [htail0]
      simp only [pow_zero, one_mul]
      apply Finset.prod_eq_one
      intro i _
      have hi : f i.castSucc = 0 := by simpa [finTailCounts] using hcounts0 i
      simp [hi]
    exact hleft.trans hright.symm
  · have htail_pos : 0 < N - f (Fin.last m) := Nat.pos_of_ne_zero htail0
    have hterm : ∀ i : Fin m,
        ((f i.castSucc : ℝ≥0) / (N : ℝ≥0)) =
          (((N - f (Fin.last m) : Nat) : ℝ≥0) / (N : ℝ≥0)) *
            ((f i.castSucc : ℝ≥0) /
              ((N - f (Fin.last m) : Nat) : ℝ≥0)) := by
      intro i
      apply NNReal.eq
      have hN_real : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
      have htail_real : ((N - f (Fin.last m) : Nat) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt htail_pos
      simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
      field_simp [hN_real, htail_real]
    calc
      (∏ i : Fin m, (((f i.castSucc : ℝ≥0) / (N : ℝ≥0)) ^ f i.castSucc)) =
          ∏ i : Fin m,
            ((((N - f (Fin.last m) : Nat) : ℝ≥0) / (N : ℝ≥0)) *
              ((f i.castSucc : ℝ≥0) /
                ((N - f (Fin.last m) : Nat) : ℝ≥0))) ^ f i.castSucc := by
        simp [hterm]
      _ =
          ∏ i : Fin m,
            (((((N - f (Fin.last m) : Nat) : ℝ≥0) / (N : ℝ≥0)) ^
                f i.castSucc) *
              (((f i.castSucc : ℝ≥0) /
                ((N - f (Fin.last m) : Nat) : ℝ≥0)) ^ f i.castSucc)) := by
        simp [mul_pow]
      _ =
          (∏ i : Fin m,
            ((((N - f (Fin.last m) : Nat) : ℝ≥0) / (N : ℝ≥0)) ^
              f i.castSucc)) *
            ∏ i : Fin m,
              (((f i.castSucc : ℝ≥0) /
                ((N - f (Fin.last m) : Nat) : ℝ≥0)) ^ f i.castSucc) := by
        rw [Finset.prod_mul_distrib]
      _ =
          ((((N - f (Fin.last m) : Nat) : ℝ≥0) / (N : ℝ≥0)) ^
              (∑ i : Fin m, f i.castSucc)) *
            ∏ i : Fin m,
              (((f i.castSucc : ℝ≥0) /
                ((N - f (Fin.last m) : Nat) : ℝ≥0)) ^ f i.castSucc) := by
        rw [Finset.prod_pow_eq_pow_sum]
      _ =
          ((((N - f (Fin.last m) : Nat) : ℝ≥0) / (N : ℝ≥0)) ^
              (N - f (Fin.last m))) *
            ∏ i : Fin m,
              (((f i.castSucc : ℝ≥0) /
                ((N - f (Fin.last m) : Nat) : ℝ≥0)) ^ f i.castSucc) := by
        rw [show (∑ i : Fin m, f i.castSucc) = N - f (Fin.last m) by
          simpa [finTailCounts] using htail_sum]

private theorem empiricalMultinomialMassFin_last_factor {m N : Nat} (f : Fin (m + 1) → Nat)
    (hN : 0 < N)
    (hsum : ∑ i : Fin (m + 1), f i = N) :
    empiricalMultinomialMassFin (N := N) f =
      empiricalBinomialMass N (f (Fin.last m)) *
        empiricalMultinomialMassFin (N := N - f (Fin.last m)) (finTailCounts f) := by
  classical
  have htail_sum :
      ∑ i : Fin m, finTailCounts f i = N - f (Fin.last m) := by
    have hsplit :
        (∑ i : Fin (m + 1), f i) =
          (∑ i : Fin m, finTailCounts f i) + f (Fin.last m) := by
      rw [Fin.sum_univ_castSucc]
      rfl
    rw [hsum] at hsplit
    omega
  unfold empiricalMultinomialMassFin empiricalBinomialMass
  rw [fin_multinomial_last_factor f, hsum]
  rw [Fin.prod_univ_castSucc]
  simp only [finTailCounts]
  rw [fin_empirical_tail_product_factor (N := N) f hN htail_sum]
  simp only [Nat.cast_mul]
  ring_nf
  rw [show
      (∏ x : Fin m,
          (↑(f x.castSucc) : ℝ≥0) ^ f x.castSucc *
            (↑(N - f (Fin.last m)) : ℝ≥0)⁻¹ ^ f x.castSucc) =
        ∏ x : Fin m,
          (↑(N - f (Fin.last m)) : ℝ≥0)⁻¹ ^ f x.castSucc *
            (↑(f x.castSucc) : ℝ≥0) ^ f x.castSucc by
    apply Finset.prod_congr rfl
    intro x _
    ring]
  ring_nf

private theorem inv_pow_succ_le_inv_mul_inv_pow {N k m : Nat} :
    (((N + 1 : Nat) : ℝ≥0) ^ (m + 1))⁻¹ ≤
      (((N + 1 : Nat) : ℝ≥0))⁻¹ *
        ((((N - k + 1 : Nat) : ℝ≥0) ^ m)⁻¹) := by
  have hbase :
      (((N - k + 1 : Nat) : ℝ≥0)) ≤ (((N + 1 : Nat) : ℝ≥0)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.sub_le N k)
  have hpow :
      (((N - k + 1 : Nat) : ℝ≥0) ^ m) ≤
        (((N + 1 : Nat) : ℝ≥0) ^ m) :=
    pow_le_pow_left₀ (by positivity) hbase m
  have hden :
      (((N + 1 : Nat) : ℝ≥0) * (((N - k + 1 : Nat) : ℝ≥0) ^ m)) ≤
        (((N + 1 : Nat) : ℝ≥0) * (((N + 1 : Nat) : ℝ≥0) ^ m)) :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have hleft_pos :
      0 < (((N + 1 : Nat) : ℝ≥0) * (((N + 1 : Nat) : ℝ≥0) ^ m)) := by
    positivity
  have hright_pos :
      0 < (((N + 1 : Nat) : ℝ≥0) * (((N - k + 1 : Nat) : ℝ≥0) ^ m)) := by
    positivity
  calc
    (((N + 1 : Nat) : ℝ≥0) ^ (m + 1))⁻¹ =
        ((((N + 1 : Nat) : ℝ≥0) * (((N + 1 : Nat) : ℝ≥0) ^ m))⁻¹) := by
      rw [pow_succ']
    _ ≤ ((((N + 1 : Nat) : ℝ≥0) *
          (((N - k + 1 : Nat) : ℝ≥0) ^ m))⁻¹) :=
      (inv_le_inv₀ hleft_pos hright_pos).mpr hden
    _ = (((N + 1 : Nat) : ℝ≥0))⁻¹ *
        ((((N - k + 1 : Nat) : ℝ≥0) ^ m)⁻¹) := by
      rw [_root_.mul_inv_rev, mul_comm]

private theorem inv_pow_card_le_empiricalMultinomialMassFin {m N : Nat}
    (hN : 0 < N) (f : Fin m → Nat)
    (hsum : ∑ i : Fin m, f i = N) :
    (((N + 1 : Nat) : ℝ≥0) ^ m)⁻¹ ≤
      empiricalMultinomialMassFin (N := N) f := by
  induction m generalizing N with
  | zero =>
      simp [empiricalMultinomialMassFin]
  | succ m ih =>
      let k := f (Fin.last m)
      have hk : k ≤ N := by
        rw [← hsum, Fin.sum_univ_castSucc]
        exact Nat.le_add_left _ _
      have htail_sum :
          ∑ i : Fin m, finTailCounts f i = N - k := by
        have hsplit :
            (∑ i : Fin (m + 1), f i) =
              (∑ i : Fin m, finTailCounts f i) + k := by
          rw [Fin.sum_univ_castSucc]
          rfl
        rw [hsum] at hsplit
        omega
      rw [empiricalMultinomialMassFin_last_factor (N := N) f hN hsum]
      have hbin : (((N + 1 : Nat) : ℝ≥0))⁻¹ ≤ empiricalBinomialMass N k :=
        by simpa [Nat.cast_add, Nat.cast_one] using
          inv_succ_le_empiricalBinomialMass hN hk
      by_cases htail0 : N - k = 0
      · have hsum0 : ∑ i : Fin m, finTailCounts f i = 0 := by
          simpa [htail0] using htail_sum
        have hcounts0_fun : finTailCounts f = 0 :=
          (Fintype.sum_eq_zero_iff_of_nonneg
            (fun i => Nat.zero_le (finTailCounts f i))).mp hsum0
        have hcounts0 : ∀ i : Fin m, finTailCounts f i = 0 := by
          intro i
          exact congrFun hcounts0_fun i
        have htail_mass :
            empiricalMultinomialMassFin (N := N - k) (finTailCounts f) = 1 := by
          unfold empiricalMultinomialMassFin
          have hmulti :
              Nat.multinomial (Finset.univ : Finset (Fin m)) (finTailCounts f) = 1 := by
            unfold Nat.multinomial
            simp [hcounts0]
          rw [hmulti]
          simp [htail0, hcounts0]
        have hpref :
            (((N + 1 : Nat) : ℝ≥0) ^ (m + 1))⁻¹ ≤
              (((N + 1 : Nat) : ℝ≥0))⁻¹ := by
          simpa [htail0] using
            (inv_pow_succ_le_inv_mul_inv_pow (N := N) (k := k) (m := m))
        exact hpref.trans (by simpa [htail_mass] using hbin)
      · have htail_pos : 0 < N - k := Nat.pos_of_ne_zero htail0
        have htail :
            ((((N - k + 1 : Nat) : ℝ≥0) ^ m)⁻¹) ≤
              empiricalMultinomialMassFin (N := N - k) (finTailCounts f) :=
          ih htail_pos (finTailCounts f) htail_sum
        have hpref :
            (((N + 1 : Nat) : ℝ≥0) ^ (m + 1))⁻¹ ≤
              (((N + 1 : Nat) : ℝ≥0))⁻¹ *
                ((((N - k + 1 : Nat) : ℝ≥0) ^ m)⁻¹) :=
          inv_pow_succ_le_inv_mul_inv_pow (N := N) (k := k) (m := m)
        have hprod :
            (((N + 1 : Nat) : ℝ≥0))⁻¹ *
                ((((N - k + 1 : Nat) : ℝ≥0) ^ m)⁻¹) ≤
              empiricalBinomialMass N k *
                empiricalMultinomialMassFin (N := N - k) (finTailCounts f) :=
          mul_le_mul' hbin htail
        exact hpref.trans hprod

/-- Source-level empirical multinomial mass lower bound:
one of the finitely many type classes has mass at least the average
`(N+1)^(-|α|)`. -/
theorem inv_pow_card_le_empiricalMultinomialMass {α : Type u} [Fintype α] [DecidableEq α]
    {N : Nat} (hN : 0 < N) (profile : TensorPowerProfile α N) :
    ((((N + 1 : Nat) : ℝ≥0) ^ Fintype.card α)⁻¹) ≤
      empiricalMultinomialMass (α := α) profile := by
  classical
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let f : Fin (Fintype.card α) → Nat := fun i => profile.1 (e.symm i)
  have hprofile_sum : ∑ z : α, profile.1 z = N :=
    tensorPowerTypeProfile_sum_of_mem_profiles (a := α) N profile.2
  have hsum : ∑ i : Fin (Fintype.card α), f i = N := by
    have hreindex :
        (∑ i : Fin (Fintype.card α), profile.1 (e.symm i)) =
          ∑ z : α, profile.1 z :=
      Equiv.sum_comp e.symm profile.1
    simpa [f] using hreindex.trans hprofile_sum
  have hfin :=
    inv_pow_card_le_empiricalMultinomialMassFin
      (N := N) (m := Fintype.card α) hN f hsum
  have hmulti :
      Nat.multinomial (Finset.univ : Finset α) profile.1 =
        Nat.multinomial (Finset.univ : Finset (Fin (Fintype.card α))) f := by
    have hsum_reindex :
        (∑ i : Fin (Fintype.card α), f i) = ∑ z : α, profile.1 z := by
      simpa [f] using Equiv.sum_comp e.symm profile.1
    have hprod_reindex :
        (∏ i : Fin (Fintype.card α), Nat.factorial (f i)) =
          ∏ z : α, Nat.factorial (profile.1 z) := by
      simpa [f] using
        Equiv.prod_comp e.symm (fun z : α => Nat.factorial (profile.1 z))
    unfold Nat.multinomial
    simp [hsum_reindex, hprod_reindex]
  have hprod :
      (∏ z : α, (((profile.1 z : ℝ≥0) / (N : ℝ≥0)) ^ profile.1 z)) =
        ∏ i : Fin (Fintype.card α), (((f i : ℝ≥0) / (N : ℝ≥0)) ^ f i) := by
    have hreindex :
        (∏ i : Fin (Fintype.card α),
            (((profile.1 (e.symm i) : ℝ≥0) / (N : ℝ≥0)) ^
              profile.1 (e.symm i))) =
          ∏ z : α, (((profile.1 z : ℝ≥0) / (N : ℝ≥0)) ^ profile.1 z) :=
      Equiv.prod_comp e.symm
        (fun z : α => (((profile.1 z : ℝ≥0) / (N : ℝ≥0)) ^ profile.1 z))
    simpa [f] using hreindex.symm
  simpa [empiricalMultinomialMass, empiricalMultinomialMassFin, hmulti, hprod,
    Nat.cast_add, Nat.cast_one] using hfin

theorem empiricalProfileProduct_toReal_eq_exp_sum_log
    {α : Type u} [Fintype α] [DecidableEq α]
    {N : Nat} (hN : 0 < N) (profile : TensorPowerProfile α N) :
    ((∏ z : α,
      (((profile.1 z : ℝ≥0) / (N : ℝ≥0)) ^ (profile.1 z)) : ℝ) =
        Real.exp
          (∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) := by
  classical
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  let nnTerm : α → ℝ≥0 := fun z =>
    (((profile.1 z : ℝ≥0) / (N : ℝ≥0)) ^ (profile.1 z))
  let realTerm : α → ℝ := fun z =>
    (((profile.1 z : ℝ) / (N : ℝ)) ^ (profile.1 z))
  let expTerm : α → ℝ := fun z =>
    Real.exp
      ((profile.1 z : ℝ) *
        Real.log ((profile.1 z : ℝ) / (N : ℝ)))
  have hcoe :
      ((Finset.univ.prod nnTerm : ℝ≥0) : ℝ) = Finset.univ.prod realTerm := by
    simp [nnTerm, realTerm, NNReal.coe_div]
  have hterms :
      Finset.univ.prod realTerm = Finset.univ.prod expTerm := by
    apply Finset.prod_congr rfl
    intro z _
    by_cases hz : profile.1 z = 0
    · simp [realTerm, expTerm, hz]
    · have hzreal : 0 < (profile.1 z : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hz
      have hx : 0 < (profile.1 z : ℝ) / (N : ℝ) := div_pos hzreal hNreal
      calc
        realTerm z =
            ((profile.1 z : ℝ) / (N : ℝ)) ^ (profile.1 z) := by
          rfl
        _ =
            (Real.exp (Real.log ((profile.1 z : ℝ) / (N : ℝ)))) ^ (profile.1 z) := by
          rw [Real.exp_log hx]
        _ =
            expTerm z := by
          unfold expTerm
          rw [← Real.exp_nat_mul]
  have hexp :
      Finset.univ.prod expTerm =
        Real.exp
          (∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ))) := by
    unfold expTerm
    rw [Real.exp_sum]
  simpa [nnTerm] using hcoe.trans (hterms.trans hexp)

/-- Source-backed type-class cardinality lower bound with the exact
`(N+1)^(-|α|)` polynomial prefactor. -/
theorem tensorPowerProfileClass_card_source_lower_bound
    {α : Type u} [Fintype α] [DecidableEq α]
    {N : Nat} (hN : 0 < N) (profile : TensorPowerProfile α N) :
    (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
        Real.exp
          (-(∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) ≤
      ((tensorPowerProfileClass (a := α) profile).card : ℝ) := by
  classical
  let S : ℝ :=
    ∑ z : α,
      (profile.1 z : ℝ) *
        Real.log ((profile.1 z : ℝ) / (N : ℝ))
  have hprob := inv_pow_card_le_empiricalMultinomialMass (α := α) hN profile
  have hprob_real0 :
      (((((N + 1 : Nat) : ℝ≥0) ^ Fintype.card α)⁻¹ : ℝ≥0) : ℝ) ≤
        (((Nat.multinomial (Finset.univ : Finset α) profile.1 : ℝ≥0) *
          ∏ z : α,
            (((profile.1 z : ℝ≥0) / (N : ℝ≥0)) ^ profile.1 z) : ℝ≥0) : ℝ) := by
    exact_mod_cast (by
      simpa [empiricalMultinomialMass] using hprob)
  have hprodlog := empiricalProfileProduct_toReal_eq_exp_sum_log (α := α) hN profile
  have hprodlogR :
      (∏ z : α, (((profile.1 z : ℝ) / (N : ℝ)) ^ profile.1 z)) =
        Real.exp S := by
    simpa [S, NNReal.coe_div] using hprodlog
  have hprob_real :
      (((((N + 1 : Nat) : ℝ≥0) ^ Fintype.card α)⁻¹ : ℝ≥0) : ℝ) ≤
        (Nat.multinomial (Finset.univ : Finset α) profile.1 : ℝ) * Real.exp S := by
    simpa [S, NNReal.coe_mul, hprodlogR] using hprob_real0
  have hpref :
      (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal =
        (((((N + 1 : Nat) : ℝ≥0) ^ Fintype.card α)⁻¹ : ℝ≥0) : ℝ) := by
    have hbase :
        (((N + 1 : Nat) : ℝ≥0∞).toReal) =
          ((((N + 1 : Nat) : ℝ≥0) : ℝ)) := by
      rw [show ((N + 1 : Nat) : ℝ≥0∞) = (N : ℝ≥0∞) + 1 by norm_num]
      rw [ENNReal.toReal_add (ENNReal.natCast_ne_top N) ENNReal.one_ne_top]
      simp [ENNReal.toReal_natCast, Nat.cast_add, Nat.cast_one]
    unfold finiteAlphabetMethodOfTypesPolynomialPrefactor
    rw [ENNReal.toReal_inv, ENNReal.toReal_pow, hbase]
    simp
  have hcard :
      ((tensorPowerProfileClass (a := α) profile).card : ℝ) =
        (Nat.multinomial (Finset.univ : Finset α) profile.1 : ℝ) := by
    exact_mod_cast tensorPowerProfileClass_card_eq_multinomial (a := α) profile
  have hmul := mul_le_mul_of_nonneg_right hprob_real (Real.exp_pos (-S)).le
  calc
    (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
        Real.exp
          (-(∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) =
        (((((N + 1 : Nat) : ℝ≥0) ^ Fintype.card α)⁻¹ : ℝ≥0) : ℝ) *
          Real.exp (-S) := by
      simp [hpref, S]
    _ ≤ ((Nat.multinomial (Finset.univ : Finset α) profile.1 : ℝ) *
          Real.exp S) * Real.exp (-S) := hmul
    _ = (Nat.multinomial (Finset.univ : Finset α) profile.1 : ℝ) := by
      rw [mul_assoc, ← Real.exp_add]
      simp [S]
    _ = ((tensorPowerProfileClass (a := α) profile).card : ℝ) := hcard.symm

/-- Generic finite-alphabet normalized logarithmic method-of-types penalty.

For exponent index `n`, the source copy number is `N = n + 1`, so the source
factor `(N+1)^(-m)` contributes `m * log(n+2) / (n+1)` in natural-log
normalization. -/
def finiteAlphabetMethodOfTypesPolynomialPenalty
    (α : Type u) [Fintype α] (n : Nat) : EReal :=
  (((Fintype.card α : ℝ) * Real.log (((n + 2 : Nat) : ℝ))) /
    (((n + 1 : Nat) : ℝ)) : ℝ)

/-- Extra finite-copy logarithmic penalty introduced when the source error
probability is converted to the repository's equal-prior average convention. -/
def equalPriorAverageLogPenalty (n : Nat) : EReal :=
  ((Real.log 2) / (((n + 1 : Nat) : ℝ)) : ℝ)

/-- The generic finite-alphabet polynomial penalty vanishes after
normalization. -/
theorem finiteAlphabetMethodOfTypesPolynomialPenalty_tendsto_zero
    (α : Type u) [Fintype α] :
    Tendsto (fun n : Nat => finiteAlphabetMethodOfTypesPolynomialPenalty α n)
      atTop (𝓝 (0 : EReal)) := by
  have hlog :
      Tendsto
        (fun x : ℝ => Real.log x ^ (1 : Nat) / (1 * x + (-1)))
        atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
  have harg : Tendsto (fun n : Nat => (((n + 2 : Nat) : ℝ))) atTop atTop := by
    simpa [Nat.cast_add] using
      (tendsto_atTop_add_const_right _ (2 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hbase :
      Tendsto
        (fun n : Nat =>
          Real.log (((n + 2 : Nat) : ℝ)) / (((n + 1 : Nat) : ℝ)))
        atTop (𝓝 0) := by
    convert hlog.comp harg using 1
    ext n
    simp [one_mul, Nat.cast_add]
    ring
  have hreal :
      Tendsto
        (fun n : Nat =>
          ((Fintype.card α : ℝ) *
            Real.log (((n + 2 : Nat) : ℝ))) / (((n + 1 : Nat) : ℝ)))
        atTop (𝓝 0) := by
    simpa [mul_div_assoc] using hbase.const_mul (Fintype.card α : ℝ)
  exact EReal.tendsto_coe.mpr hreal

/-- The equal-prior `log 2 / (n+1)` normalization penalty vanishes. -/
theorem equalPriorAverageLogPenalty_tendsto_zero :
    Tendsto (fun n : Nat => equalPriorAverageLogPenalty n)
      atTop (𝓝 (0 : EReal)) := by
  have hden :
      Tendsto (fun n : Nat => (((n + 1 : Nat) : ℝ))) atTop atTop := by
    simpa [Nat.cast_add] using
      (tendsto_atTop_add_const_right _ (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hreal :
      Tendsto (fun n : Nat => (Real.log 2) / (((n + 1 : Nat) : ℝ)))
        atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hden) :
        Tendsto (fun n : Nat => (Real.log 2) * ((((n + 1 : Nat) : ℝ))⁻¹))
          atTop (𝓝 (Real.log 2 * 0)))
  exact EReal.tendsto_coe.mpr hreal

/-- Multiplying a finite `ℝ≥0` error by the quantum-to-classical `1 / 2`
constant can increase the normalized negative log by at most
`log 2 / (n+1)`. -/
theorem normalizedNegLog_half_mul_coe_le_add_equalPriorAverageLogPenalty
    (n : Nat) (x : ℝ≥0) :
    normalizedNegLog n ((((1 / 2 : ℝ≥0) * x : ℝ≥0) : ℝ≥0∞)) ≤
      normalizedNegLog n (x : ℝ≥0∞) + equalPriorAverageLogPenalty n := by
  by_cases hx : x = 0
  · subst x
    rw [normalizedNegLog_eq_top_of_eq_zero n
        ((((1 / 2 : ℝ≥0) * 0 : ℝ≥0) : ℝ≥0∞)) (by simp),
      normalizedNegLog_eq_top_of_eq_zero n ((0 : ℝ≥0) : ℝ≥0∞) (by simp)]
    simp [equalPriorAverageLogPenalty]
  · have hxpos_nn : 0 < x := lt_of_le_of_ne (by positivity) (Ne.symm hx)
    have hxpos : 0 < (x : ℝ) := by exact_mod_cast hxpos_nn
    have hmul_ne_zero :
        (((1 / 2 : ℝ≥0) * x : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast mul_ne_zero (by norm_num : (1 / 2 : ℝ≥0) ≠ 0) hx
    have hx_ne_zero : (x : ℝ≥0∞) ≠ 0 := by exact_mod_cast hx
    have hmul_ne_top :
        ((((1 / 2 : ℝ≥0) * x : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ :=
      ENNReal.coe_ne_top
    rw [normalizedNegLog_eq_coe_real_of_ne_zero_ne_top
          n ((((1 / 2 : ℝ≥0) * x : ℝ≥0) : ℝ≥0∞))
          hmul_ne_zero hmul_ne_top,
        normalizedNegLog_eq_coe_real_of_ne_zero_ne_top
          n (x : ℝ≥0∞) hx_ne_zero (by simp)]
    unfold equalPriorAverageLogPenalty
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    unfold normalizedNegLogReal
    simp only [ENNReal.coe_toReal, NNReal.coe_mul]
    have hhalf_ne : (((1 / 2 : ℝ≥0) : ℝ) ≠ 0) := by norm_num
    have hlog_half : Real.log (((1 / 2 : ℝ≥0) : ℝ)) = -Real.log 2 := by
      rw [show (((1 / 2 : ℝ≥0) : ℝ)) = (2 : ℝ)⁻¹ by norm_num]
      rw [Real.log_inv]
    rw [Real.log_mul hhalf_ne hxpos.ne', hlog_half]
    ring_nf
    rfl

/-- The method-of-types polynomial penalty vanishes after normalization. -/
theorem methodOfTypesPolynomialPenalty_tendsto_zero {a : Type u} [Fintype a] :
    Tendsto (fun n : Nat => methodOfTypesPolynomialPenalty (a := a) n)
      atTop (𝓝 (0 : EReal)) := by
  have hlog :
      Tendsto
        (fun x : ℝ => Real.log x ^ (1 : Nat) / (1 * x + (-1)))
        atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
  have harg : Tendsto (fun n : Nat => (((n + 2 : Nat) : ℝ))) atTop atTop := by
    simpa [Nat.cast_add] using
      (tendsto_atTop_add_const_right _ (2 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hbase :
      Tendsto
        (fun n : Nat =>
          Real.log (((n + 2 : Nat) : ℝ)) / (((n + 1 : Nat) : ℝ)))
        atTop (𝓝 0) := by
    convert hlog.comp harg using 1
    ext n
    simp [one_mul, Nat.cast_add]
    ring
  have hreal :
      Tendsto
        (fun n : Nat =>
          ((nussbaumSzkolaAlphabetCard (a := a) : ℝ) *
            Real.log (((n + 2 : Nat) : ℝ))) / (((n + 1 : Nat) : ℝ)))
        atTop (𝓝 0) := by
    simpa [mul_div_assoc] using hbase.const_mul (nussbaumSzkolaAlphabetCard (a := a) : ℝ)
  exact EReal.tendsto_coe.mpr hreal

/-- The quantum-to-classical converse comparison constant from the Gour route.

Gour's Nussbaum--Szkola comparison lower-bounds the quantum symmetric error by
one half of the associated classical error
[Gour2024Resources, BookQRT.tex:15911-15949]. -/
def quantumChernoffConverseComparisonConstant : ℝ≥0∞ :=
  (1 / 2 : ℝ≥0∞)

namespace ClassicalDistribution

variable {α : Type u} [Fintype α]


/-- Empirical counts obtained by flooring every non-base coordinate and placing
the remaining mass on a fixed support point.  This gives exact total count `N`
while keeping the support contained in the original distribution's support. -/
noncomputable def roundedCounts [DecidableEq α]
    (r : ClassicalDistribution α) (N : Nat) : α → Nat :=
  fun x =>
    if x = r.supportPoint then
      N - ∑ y ∈ (Finset.univ.erase r.supportPoint),
        Nat.floor ((N : ℝ) * (r.prob y : ℝ))
    else
      Nat.floor ((N : ℝ) * (r.prob x : ℝ))

theorem roundedCounts_sum [DecidableEq α]
    (r : ClassicalDistribution α) (N : Nat) :
    ∑ x : α, r.roundedCounts N x = N := by
  classical
  let x0 := r.supportPoint
  have hsubset :
      ∑ y ∈ (Finset.univ.erase x0), Nat.floor ((N : ℝ) * (r.prob y : ℝ)) ≤ N := by
    calc
      ∑ y ∈ (Finset.univ.erase x0), Nat.floor ((N : ℝ) * (r.prob y : ℝ))
          ≤ ∑ y : α, Nat.floor ((N : ℝ) * (r.prob y : ℝ)) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by intro y hy; simp at hy ⊢)
              (by intro y _ _; exact Nat.zero_le _)
      _ ≤ N := floor_scaled_sum_le r N
  have hsum_erase :
      ∑ x ∈ (Finset.univ.erase x0), r.roundedCounts N x =
        ∑ x ∈ (Finset.univ.erase x0),
          Nat.floor ((N : ℝ) * (r.prob x : ℝ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxne : x ≠ x0 := by
      simpa using (Finset.mem_erase.mp hx).1
    simp [roundedCounts, x0, hxne]
  have hsplit :
      ∑ x : α, r.roundedCounts N x =
        r.roundedCounts N x0 +
          ∑ x ∈ (Finset.univ.erase x0), r.roundedCounts N x := by
    rw [← Finset.sum_insert]
    · simp
    · simp
  rw [hsplit, hsum_erase]
  let S := ∑ y ∈ Finset.univ.erase x0,
    Nat.floor ((N : ℝ) * (r.prob y : ℝ))
  have hx0 : r.roundedCounts N x0 = N - S := by
    simp [roundedCounts, x0, S]
  have hS : S ≤ N := hsubset
  rw [hx0]
  exact Nat.sub_add_cancel hS

@[simp]
theorem roundedCounts_supportPoint [DecidableEq α]
    (r : ClassicalDistribution α) (N : Nat) :
    r.roundedCounts N r.supportPoint =
      N - ∑ y ∈ (Finset.univ.erase r.supportPoint),
        Nat.floor ((N : ℝ) * (r.prob y : ℝ)) := by
  simp [roundedCounts]

theorem roundedCounts_of_ne_supportPoint [DecidableEq α]
    (r : ClassicalDistribution α) (N : Nat) {x : α}
    (hx : x ≠ r.supportPoint) :
    r.roundedCounts N x =
      Nat.floor ((N : ℝ) * (r.prob x : ℝ)) := by
  simp [roundedCounts, hx]

theorem roundedCounts_of_ne_supportPoint_abs_sub_le_inv [DecidableEq α]
    (r : ClassicalDistribution α) {N : Nat} (hN : 0 < N)
    {x : α} (hx : x ≠ r.supportPoint) :
    |((r.roundedCounts N x : ℝ) / (N : ℝ)) - (r.prob x : ℝ)| ≤
      1 / (N : ℝ) := by
  rw [roundedCounts_of_ne_supportPoint r N hx]
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have ha_nonneg : 0 ≤ (N : ℝ) * (r.prob x : ℝ) := by
    positivity
  have hfloor_le :
      ((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) ≤
        (N : ℝ) * (r.prob x : ℝ) :=
    Nat.floor_le ha_nonneg
  have hlt_floor :
      (N : ℝ) * (r.prob x : ℝ) <
        ((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) + 1 :=
    Nat.lt_floor_add_one ((N : ℝ) * (r.prob x : ℝ))
  have hleft :
      ((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) / (N : ℝ) -
          (r.prob x : ℝ) ≤
        1 / (N : ℝ) := by
    have hfloor_le' :
        ((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) ≤
          (r.prob x : ℝ) * (N : ℝ) := by
      nlinarith [hfloor_le]
    have hdiv_le :
        ((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) / (N : ℝ) ≤
          (r.prob x : ℝ) := by
      exact (div_le_iff₀ hNreal).mpr hfloor_le'
    have hnonpos :
        ((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) / (N : ℝ) -
            (r.prob x : ℝ) ≤ 0 := by
      exact sub_nonpos.mpr hdiv_le
    have hpos : 0 ≤ 1 / (N : ℝ) := by positivity
    exact hnonpos.trans hpos
  have hright :
      (r.prob x : ℝ) -
          ((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) / (N : ℝ) ≤
        1 / (N : ℝ) := by
    have hle_num :
        (r.prob x : ℝ) * (N : ℝ) ≤
          ((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) + 1 := by
      nlinarith [hlt_floor]
    have hp_le :
        (r.prob x : ℝ) ≤
          (((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) + 1) /
            (N : ℝ) := by
      exact (le_div_iff₀ hNreal).mpr hle_num
    have hsum :
        ((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) / (N : ℝ) +
            1 / (N : ℝ) =
          (((Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : Nat) : ℝ) + 1) /
            (N : ℝ) := by
      field_simp [hNreal.ne']
    exact (sub_le_iff_le_add'.mpr (by simpa [← hsum] using hp_le))
  exact abs_sub_le_iff.mpr ⟨hleft, hright⟩

theorem roundedCounts_supportPoint_abs_sub_le_card_div [DecidableEq α]
    (r : ClassicalDistribution α) {N : Nat} (hN : 0 < N) :
    |((r.roundedCounts N r.supportPoint : ℝ) / (N : ℝ)) -
        (r.prob r.supportPoint : ℝ)| ≤
      (Fintype.card α : ℝ) / (N : ℝ) := by
  classical
  let x0 := r.supportPoint
  let S : Nat := ∑ y ∈ (Finset.univ.erase x0),
    Nat.floor ((N : ℝ) * (r.prob y : ℝ))
  let Sreal : ℝ := ∑ y ∈ (Finset.univ.erase x0),
    ((Nat.floor ((N : ℝ) * (r.prob y : ℝ)) : Nat) : ℝ)
  let Psum : ℝ := ∑ y ∈ (Finset.univ.erase x0),
    (N : ℝ) * (r.prob y : ℝ)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hSleN : S ≤ N := by
    calc
      S ≤ ∑ y : α, Nat.floor ((N : ℝ) * (r.prob y : ℝ)) := by
        unfold S
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (by intro y hy; simp at hy ⊢)
          (by intro y _ _; exact Nat.zero_le _)
      _ ≤ N := floor_scaled_sum_le r N
  have hSreal : (S : ℝ) = Sreal := by
    simp [S, Sreal]
  have hcount :
      (r.roundedCounts N x0 : ℝ) = (N : ℝ) - Sreal := by
    rw [roundedCounts_supportPoint]
    change ((N - S : Nat) : ℝ) = (N : ℝ) - Sreal
    rw [Nat.cast_sub hSleN]
    rw [hSreal]
  have hsum_all : ∑ x : α, (r.prob x : ℝ) = 1 := by
    exact_mod_cast r.sum_eq_one
  have hsum_split :
      ∑ x : α, (r.prob x : ℝ) =
        (r.prob x0 : ℝ) +
          ∑ y ∈ (Finset.univ.erase x0), (r.prob y : ℝ) := by
    calc
      ∑ x : α, (r.prob x : ℝ)
          = ∑ x ∈ insert x0 (Finset.univ.erase x0), (r.prob x : ℝ) := by
            simp
      _ = (r.prob x0 : ℝ) +
            ∑ y ∈ (Finset.univ.erase x0), (r.prob y : ℝ) := by
            rw [Finset.sum_insert]
            simp [x0]
  have hsum_prob :
      (r.prob x0 : ℝ) +
          ∑ y ∈ (Finset.univ.erase x0), (r.prob y : ℝ) = 1 := by
    rw [← hsum_split, hsum_all]
  have hPsum :
      Psum = (N : ℝ) *
        ∑ y ∈ (Finset.univ.erase x0), (r.prob y : ℝ) := by
    unfold Psum
    rw [Finset.mul_sum]
  have hscaled_sum :
      (r.prob x0 : ℝ) * (N : ℝ) + Psum = (N : ℝ) := by
    rw [hPsum]
    nlinarith [hsum_prob, hNreal]
  have hSreal_le_Psum : Sreal ≤ Psum := by
    unfold Sreal Psum
    exact Finset.sum_le_sum fun y _ => by
      exact Nat.floor_le (by positivity :
        0 ≤ (N : ℝ) * (r.prob y : ℝ))
  have hPsum_le_Sreal_add_cardErase :
      Psum ≤ Sreal + ((Finset.univ.erase x0).card : ℝ) := by
    unfold Sreal Psum
    calc
      ∑ y ∈ Finset.univ.erase x0, (N : ℝ) * (r.prob y : ℝ)
          ≤ ∑ y ∈ Finset.univ.erase x0,
              (((Nat.floor ((N : ℝ) * (r.prob y : ℝ)) : Nat) : ℝ) + 1) := by
            exact Finset.sum_le_sum fun y _ =>
              le_of_lt (Nat.lt_floor_add_one
                ((N : ℝ) * (r.prob y : ℝ)))
      _ =
          (∑ y ∈ Finset.univ.erase x0,
            ((Nat.floor ((N : ℝ) * (r.prob y : ℝ)) : Nat) : ℝ)) +
            ((Finset.univ.erase x0).card : ℝ) := by
            simp [Finset.sum_add_distrib]
  have hcard_erase :
      ((Finset.univ.erase x0).card : ℝ) ≤ (Fintype.card α : ℝ) := by
    exact_mod_cast Finset.card_le_univ (Finset.univ.erase x0)
  have hprob_le_count_div :
      (r.prob x0 : ℝ) ≤ (r.roundedCounts N x0 : ℝ) / (N : ℝ) := by
    have hnum :
        (r.prob x0 : ℝ) * (N : ℝ) ≤ (r.roundedCounts N x0 : ℝ) := by
      rw [hcount]
      nlinarith [hscaled_sum, hSreal_le_Psum]
    exact (le_div_iff₀ hNreal).mpr hnum
  have hcount_sub_prob_le_card :
      (r.roundedCounts N x0 : ℝ) - (r.prob x0 : ℝ) * (N : ℝ) ≤
        (Fintype.card α : ℝ) := by
    rw [hcount]
    nlinarith [hscaled_sum, hPsum_le_Sreal_add_cardErase, hcard_erase]
  have hcount_div_le :
      (r.roundedCounts N x0 : ℝ) / (N : ℝ) ≤
        (r.prob x0 : ℝ) + (Fintype.card α : ℝ) / (N : ℝ) := by
    have hnum :
        (r.roundedCounts N x0 : ℝ) ≤
          ((r.prob x0 : ℝ) + (Fintype.card α : ℝ) / (N : ℝ)) *
            (N : ℝ) := by
      have hright :
          ((r.prob x0 : ℝ) + (Fintype.card α : ℝ) / (N : ℝ)) *
              (N : ℝ) =
            (r.prob x0 : ℝ) * (N : ℝ) + (Fintype.card α : ℝ) := by
        field_simp [hNreal.ne']
      rw [hright]
      linarith [hcount_sub_prob_le_card]
    exact (div_le_iff₀ hNreal).mpr hnum
  have hleft :
      (r.roundedCounts N x0 : ℝ) / (N : ℝ) -
          (r.prob x0 : ℝ) ≤
        (Fintype.card α : ℝ) / (N : ℝ) :=
    sub_le_iff_le_add'.mpr hcount_div_le
  have hright :
      (r.prob x0 : ℝ) -
          (r.roundedCounts N x0 : ℝ) / (N : ℝ) ≤
        (Fintype.card α : ℝ) / (N : ℝ) := by
    have hnonpos :
        (r.prob x0 : ℝ) -
            (r.roundedCounts N x0 : ℝ) / (N : ℝ) ≤ 0 :=
      sub_nonpos.mpr hprob_le_count_div
    have hnonneg : 0 ≤ (Fintype.card α : ℝ) / (N : ℝ) := by
      positivity
    exact hnonpos.trans hnonneg
  simpa [x0] using abs_sub_le_iff.mpr ⟨hleft, hright⟩

theorem roundedCounts_abs_sub_le_card_div [DecidableEq α]
    (r : ClassicalDistribution α) {N : Nat} (hN : 0 < N) (x : α) :
    |((r.roundedCounts N x : ℝ) / (N : ℝ)) - (r.prob x : ℝ)| ≤
      (Fintype.card α : ℝ) / (N : ℝ) := by
  classical
  by_cases hx : x = r.supportPoint
  · simpa [hx] using roundedCounts_supportPoint_abs_sub_le_card_div
      (r := r) hN
  · have hfloor :=
      roundedCounts_of_ne_supportPoint_abs_sub_le_inv
        (r := r) hN hx
    have hcard_pos : 0 < Fintype.card α :=
      Fintype.card_pos_iff.mpr ⟨r.supportPoint⟩
    have hcard_ge_one : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by
      exact_mod_cast hcard_pos
    have hNreal_nonneg : 0 ≤ (N : ℝ) := by
      exact le_of_lt (by exact_mod_cast hN : 0 < (N : ℝ))
    have hscale :
        1 / (N : ℝ) ≤ (Fintype.card α : ℝ) / (N : ℝ) := by
      exact div_le_div_of_nonneg_right hcard_ge_one hNreal_nonneg
    exact hfloor.trans hscale

/-- The tensor-power profile associated with `roundedCounts`. -/
noncomputable def roundedProfile [DecidableEq α]
    (r : ClassicalDistribution α) (N : Nat) : TensorPowerProfile α N :=
  (TensorPowerProfile.equivWeakCompositions (a := α) (n := N)).symm
    ⟨r.roundedCounts N, roundedCounts_sum r N⟩

end ClassicalDistribution

end BinaryHypothesisTest

namespace TensorPowerProfile

variable {α : Type u} [DecidableEq α] [Fintype α]

/-- The empirical distribution associated with a positive-length tensor-power
profile. -/
noncomputable def empiricalDistribution {N : Nat} (profile : TensorPowerProfile α N)
    (hN : 0 < N) : BinaryHypothesisTest.ClassicalDistribution α :=
  { prob := fun z => (profile.1 z : ℝ≥0) / (N : ℝ≥0)
    sum_eq_one := by
      apply NNReal.eq
      change (↑(∑ z : α, (profile.1 z : ℝ≥0) / (N : ℝ≥0)) : ℝ) = (1 : ℝ)
      rw [NNReal.coe_sum]
      simp only [NNReal.coe_div, NNReal.coe_natCast]
      rw [← Finset.sum_div]
      have hsum_nat :
          ∑ z : α, profile.1 z = N :=
        tensorPowerTypeProfile_sum_of_mem_profiles (a := α) N profile.2
      have hsum_real : ∑ z : α, (profile.1 z : ℝ) = (N : ℝ) := by
        exact_mod_cast hsum_nat
      rw [hsum_real]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)] }

@[simp]
theorem empiricalDistribution_prob {N : Nat} (profile : TensorPowerProfile α N)
    (hN : 0 < N) :
    (profile.empiricalDistribution hN).prob =
      fun z => (profile.1 z : ℝ≥0) / (N : ℝ≥0) := rfl

end TensorPowerProfile

namespace BinaryHypothesisTest

namespace ClassicalDistribution

variable {α : Type u} [Fintype α] [DecidableEq α]

theorem roundedCounts_support
    (r : ClassicalDistribution α) (N : Nat) {x : α}
    (hcount : r.roundedCounts N x ≠ 0) :
    r.prob x ≠ 0 := by
  classical
  by_cases hx : x = r.supportPoint
  · rw [hx]
    exact supportPoint_prob_ne_zero r
  · simp [roundedCounts, hx] at hcount
    by_contra hp0
    simp [hp0] at hcount
    exact (by norm_num : ¬ (1 : ℝ) ≤ 0) hcount

/-- The empirical distribution obtained from rounded counts has support
contained in the original finite distribution. -/
theorem roundedProfile_empiricalDistribution_supportedBy
    (r : ClassicalDistribution α) {N : Nat} (hN : 0 < N) :
    ((r.roundedProfile N).empiricalDistribution hN).SupportedBy r.prob := by
  intro x hx
  have hprofile : (r.roundedProfile N).1 = r.roundedCounts N := by
    unfold roundedProfile
    rfl
  have hcount : (r.roundedProfile N).1 x ≠ 0 := by
    by_contra hzero
    rw [TensorPowerProfile.empiricalDistribution_prob] at hx
    simp [hzero] at hx
  exact roundedCounts_support r N (by simpa [hprofile] using hcount)

theorem roundedProfile_empiricalDistribution_prob_abs_sub_le_card_div
    (r : ClassicalDistribution α) {N : Nat} (hN : 0 < N) (x : α) :
    |(((r.roundedProfile N).empiricalDistribution hN).prob x : ℝ) -
        (r.prob x : ℝ)| ≤
      (Fintype.card α : ℝ) / (N : ℝ) := by
  have hprofile : (r.roundedProfile N).1 = r.roundedCounts N := by
    unfold roundedProfile
    rfl
  simpa [TensorPowerProfile.empiricalDistribution_prob, hprofile,
    NNReal.coe_div, NNReal.coe_natCast] using
      roundedCounts_abs_sub_le_card_div (r := r) hN x

theorem roundedProfile_empiricalDistribution_prob_tendsto
    (r : ClassicalDistribution α) (x : α) :
    Tendsto
      (fun n : Nat =>
        (((r.roundedProfile (n + 1)).empiricalDistribution
          (Nat.succ_pos n)).prob x : ℝ))
      atTop (𝓝 (r.prob x : ℝ)) := by
  have hden :
      Tendsto (fun n : Nat => ((n + 1 : Nat) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hbound :
      ∀ n : Nat,
        |(((r.roundedProfile (n + 1)).empiricalDistribution
            (Nat.succ_pos n)).prob x : ℝ) - (r.prob x : ℝ)| ≤
          (Fintype.card α : ℝ) / ((n + 1 : Nat) : ℝ) := by
    intro n
    exact roundedProfile_empiricalDistribution_prob_abs_sub_le_card_div
      (r := r) (N := n + 1) (Nat.succ_pos n) x
  have hpenalty :
      Tendsto
        (fun n : Nat => (Fintype.card α : ℝ) / ((n + 1 : Nat) : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have habs :
      Tendsto
        (fun n : Nat =>
          |(((r.roundedProfile (n + 1)).empiricalDistribution
              (Nat.succ_pos n)).prob x : ℝ) - (r.prob x : ℝ)|)
        atTop (𝓝 0) :=
    squeeze_zero
      (fun n => abs_nonneg _)
      hbound
      hpenalty
  rw [tendsto_iff_dist_tendsto_zero]
  simpa [Real.dist_eq, abs_sub_comm] using habs

theorem roundedProfile_empiricalDistribution_prob_eq_zero_of_prob_eq_zero
    (r : ClassicalDistribution α) {N : Nat} (hN : 0 < N)
    {x : α} (hx : r.prob x = 0) :
    ((r.roundedProfile N).empiricalDistribution hN).prob x = 0 := by
  by_contra hne
  exact ((roundedProfile_empiricalDistribution_supportedBy r hN) x hne) hx

theorem relativeEntropySummandReal_roundedProfile_tendsto
    (r p : ClassicalDistribution α) (hp : r.SupportedBy p.prob) (x : α) :
    Tendsto
      (fun n : Nat =>
        relativeEntropySummandReal
          ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n))
          p x)
      atTop (𝓝 (relativeEntropySummandReal r p x)) := by
  by_cases hr0 : r.prob x = 0
  · have hzero :
      ∀ n : Nat,
        (((r.roundedProfile (n + 1)).empiricalDistribution
          (Nat.succ_pos n)).prob x) = 0 := by
      intro n
      exact roundedProfile_empiricalDistribution_prob_eq_zero_of_prob_eq_zero
        (r := r) (N := n + 1) (Nat.succ_pos n) hr0
    have heq :
        (fun n : Nat =>
          relativeEntropySummandReal
            ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n))
            p x) = fun _n : Nat => 0 := by
      funext n
      simp [relativeEntropySummandReal, hzero n]
    rw [heq]
    simp [relativeEntropySummandReal, hr0]
  · let f : Nat → ℝ := fun n =>
      (((r.roundedProfile (n + 1)).empiricalDistribution
        (Nat.succ_pos n)).prob x : ℝ)
    let a : ℝ := (r.prob x : ℝ)
    have hf : Tendsto f atTop (𝓝 a) := by
      simpa [f, a] using
        roundedProfile_empiricalDistribution_prob_tendsto (r := r) x
    have ha : a ≠ 0 := by
      exact NNReal.coe_ne_zero.mpr hr0
    have hp0_nn : p.prob x ≠ 0 := hp x hr0
    have hp0 : (p.prob x : ℝ) ≠ 0 :=
      NNReal.coe_ne_zero.mpr hp0_nn
    have hcont :
        ContinuousAt
          (fun t : ℝ => t * Real.log (t / (p.prob x : ℝ))) a := by
      exact continuousAt_id.mul
        ((continuousAt_id.div_const (p.prob x : ℝ)).log
          (div_ne_zero ha hp0))
    have hmain :
        Tendsto
          (fun n : Nat => f n * Real.log (f n / (p.prob x : ℝ)))
          atTop
          (𝓝 (a * Real.log (a / (p.prob x : ℝ)))) :=
      hcont.tendsto.comp hf
    have hne_eventually : ∀ᶠ n : Nat in atTop, f n ≠ 0 :=
      hf.eventually_ne ha
    have htarget :
        relativeEntropySummandReal r p x =
          a * Real.log (a / (p.prob x : ℝ)) := by
      simp [relativeEntropySummandReal, hr0, a]
    rw [htarget]
    refine hmain.congr' ?_
    filter_upwards [hne_eventually] with n hn
    have hprob_ne :
        ((r.roundedProfile (n + 1)).empiricalDistribution
          (Nat.succ_pos n)).prob x ≠ 0 := by
      exact NNReal.coe_ne_zero.mp (by simpa [f] using hn)
    rw [relativeEntropySummandReal, if_neg hprob_ne]

theorem relativeEntropyReal_roundedProfile_tendsto
    (r p : ClassicalDistribution α) (hp : r.SupportedBy p.prob) :
    Tendsto
      (fun n : Nat =>
        relativeEntropyReal
          ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n))
          p)
      atTop (𝓝 (relativeEntropyReal r p)) := by
  unfold relativeEntropyReal
  simpa using
    tendsto_finsetSum (Finset.univ : Finset α)
      (fun x _ => relativeEntropySummandReal_roundedProfile_tendsto
        (r := r) (p := p) hp x)

end ClassicalDistribution

end BinaryHypothesisTest

namespace BinaryHypothesisTest


namespace ClassicalBinaryModel

variable {α : Type u} [Fintype α]

variable [DecidableEq α]

/-- Product probability of a tensor word, expressed over the canonical
`Fin n -> α` tensor-power equivalence. -/
def tensorPowerProbabilityP (M : ClassicalBinaryModel α) (n : Nat)
    (x : TensorPower α n) : ℝ≥0 :=
  ∏ i : Fin n, M.p (tensorPowerEquiv (a := α) n x i)

/-- Product `q`-probability of a tensor word, expressed over the canonical
`Fin n -> α` tensor-power equivalence. -/
def tensorPowerProbabilityQ (M : ClassicalBinaryModel α) (n : Nat)
    (x : TensorPower α n) : ℝ≥0 :=
  ∏ i : Fin n, M.q (tensorPowerEquiv (a := α) n x i)

omit [DecidableEq α] in
@[simp]
theorem tensorPower_p_eq_tensorPowerProbabilityP
    (M : ClassicalBinaryModel α) (n : Nat) (x : TensorPower α n) :
    (M.tensorPower n).p x = M.tensorPowerProbabilityP n x := by
  induction n with
  | zero =>
      cases x
      simp [tensorPower, tensorPowerProbabilityP]
  | succ n ih =>
      rcases x with ⟨x0, xs⟩
      change M.p x0 * (M.tensorPower n).p xs =
        ∏ i : Fin (n + 1), M.p (tensorPowerEquiv (a := α) (n + 1) (x0, xs) i)
      rw [ih xs, Fin.prod_univ_succ]
      rfl

omit [DecidableEq α] in
@[simp]
theorem tensorPower_q_eq_tensorPowerProbabilityQ
    (M : ClassicalBinaryModel α) (n : Nat) (x : TensorPower α n) :
    (M.tensorPower n).q x = M.tensorPowerProbabilityQ n x := by
  induction n with
  | zero =>
      cases x
      simp [tensorPower, tensorPowerProbabilityQ]
  | succ n ih =>
      rcases x with ⟨x0, xs⟩
      change M.q x0 * (M.tensorPower n).q xs =
        ∏ i : Fin (n + 1), M.q (tensorPowerEquiv (a := α) (n + 1) (x0, xs) i)
      rw [ih xs, Fin.prod_univ_succ]
      rfl

omit [DecidableEq α] in
@[simp]
theorem tensorPowerProbabilityP_permEquiv
    (M : ClassicalBinaryModel α) (n : Nat) (σ : Equiv.Perm (Fin n))
    (x : TensorPower α n) :
    M.tensorPowerProbabilityP n (permEquiv (a := α) n σ x) =
      M.tensorPowerProbabilityP n x := by
  unfold tensorPowerProbabilityP
  rw [tensorPowerEquiv_permEquiv]
  exact Equiv.prod_comp σ.symm (fun i => M.p (tensorPowerEquiv (a := α) n x i))

omit [DecidableEq α] in
@[simp]
theorem tensorPowerProbabilityQ_permEquiv
    (M : ClassicalBinaryModel α) (n : Nat) (σ : Equiv.Perm (Fin n))
    (x : TensorPower α n) :
    M.tensorPowerProbabilityQ n (permEquiv (a := α) n σ x) =
      M.tensorPowerProbabilityQ n x := by
  unfold tensorPowerProbabilityQ
  rw [tensorPowerEquiv_permEquiv]
  exact Equiv.prod_comp σ.symm (fun i => M.q (tensorPowerEquiv (a := α) n x i))

/-- Product `p`-probability is constant on tensor-power type classes. -/
theorem tensorPower_p_eq_of_typeProfile_eq
    (M : ClassicalBinaryModel α) {n : Nat} {x y : TensorPower α n}
    (hxy :
      tensorPowerTypeProfile (a := α) n x =
        tensorPowerTypeProfile (a := α) n y) :
    (M.tensorPower n).p x = (M.tensorPower n).p y := by
  rw [tensorPower_p_eq_tensorPowerProbabilityP,
    tensorPower_p_eq_tensorPowerProbabilityP]
  obtain ⟨σ, hσ⟩ := exists_permEquiv_of_tensorPowerTypeProfile_eq
    (a := α) n x y hxy
  rw [← hσ]
  exact (tensorPowerProbabilityP_permEquiv M n σ x).symm

/-- Product `q`-probability is constant on tensor-power type classes. -/
theorem tensorPower_q_eq_of_typeProfile_eq
    (M : ClassicalBinaryModel α) {n : Nat} {x y : TensorPower α n}
    (hxy :
      tensorPowerTypeProfile (a := α) n x =
        tensorPowerTypeProfile (a := α) n y) :
    (M.tensorPower n).q x = (M.tensorPower n).q y := by
  rw [tensorPower_q_eq_tensorPowerProbabilityQ,
    tensorPower_q_eq_tensorPowerProbabilityQ]
  obtain ⟨σ, hσ⟩ := exists_permEquiv_of_tensorPowerTypeProfile_eq
    (a := α) n x y hxy
  rw [← hσ]
  exact (tensorPowerProbabilityQ_permEquiv M n σ x).symm

/-- The `p`-mass of one type class. -/
def profileClassMassP
    (M : ClassicalBinaryModel α) {n : Nat} (profile : TensorPowerProfile α n) : ℝ≥0 :=
  (tensorPowerProfileClass (a := α) profile).sum (fun x => (M.tensorPower n).p x)

/-- The `q`-mass of one type class. -/
def profileClassMassQ
    (M : ClassicalBinaryModel α) {n : Nat} (profile : TensorPowerProfile α n) : ℝ≥0 :=
  (tensorPowerProfileClass (a := α) profile).sum (fun x => (M.tensorPower n).q x)

/-- Type-class `p`-mass is cardinality times any representative probability. -/
theorem profileClassMassP_eq_card_mul
    (M : ClassicalBinaryModel α) {n : Nat} (profile : TensorPowerProfile α n) :
    (tensorPowerProfileClass (a := α) profile).sum (fun x => (M.tensorPower n).p x) =
      ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
        (M.tensorPower n).p profile.rep := by
  calc
    (tensorPowerProfileClass (a := α) profile).sum (fun x => (M.tensorPower n).p x)
        = (tensorPowerProfileClass (a := α) profile).sum
            (fun _x => (M.tensorPower n).p profile.rep) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          apply tensorPower_p_eq_of_typeProfile_eq
          exact ((mem_tensorPowerProfileClass (a := α) profile x).mp hx).trans
            (TensorPowerProfile.rep_typeProfile (a := α) profile).symm
    _ = ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
        (M.tensorPower n).p profile.rep := by
          simp

/-- Type-class `q`-mass is cardinality times any representative probability. -/
theorem profileClassMassQ_eq_card_mul
    (M : ClassicalBinaryModel α) {n : Nat} (profile : TensorPowerProfile α n) :
    (tensorPowerProfileClass (a := α) profile).sum (fun x => (M.tensorPower n).q x) =
      ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
        (M.tensorPower n).q profile.rep := by
  calc
    (tensorPowerProfileClass (a := α) profile).sum (fun x => (M.tensorPower n).q x)
        = (tensorPowerProfileClass (a := α) profile).sum
            (fun _x => (M.tensorPower n).q profile.rep) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          apply tensorPower_q_eq_of_typeProfile_eq
          exact ((mem_tensorPowerProfileClass (a := α) profile x).mp hx).trans
            (TensorPowerProfile.rep_typeProfile (a := α) profile).symm
    _ = ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
        (M.tensorPower n).q profile.rep := by
          simp

/-- Tensor-power `p` probability as a product over the type profile. -/
theorem tensorPower_p_eq_profile_prod
    (M : ClassicalBinaryModel α) (n : Nat) (x : TensorPower α n) :
    (M.tensorPower n).p x =
      ∏ z : α, M.p z ^ tensorPowerTypeProfile (a := α) n x z := by
  induction n with
  | zero =>
      cases x
      simp [tensorPower, tensorPowerTypeProfile]
  | succ n ih =>
      rcases x with ⟨x0, xs⟩
      rw [tensorPower_succ_p, ih xs]
      rw [show
          (∏ z : α, M.p z ^ tensorPowerTypeProfile (a := α) (n + 1) (x0, xs) z) =
            ∏ z : α, M.p z ^ ((if x0 = z then 1 else 0) +
              tensorPowerTypeProfile (a := α) n xs z) by
        refine Finset.prod_congr rfl ?_
        intro z _
        rw [tensorPowerTypeProfile_succ]]
      have hsingle :
          (∏ z : α, M.p z ^ (if x0 = z then 1 else 0)) = M.p x0 := by
        rw [Finset.prod_eq_single x0]
        · simp
        · intro z _ hz
          have hx0z : x0 ≠ z := fun h => hz h.symm
          simp [hx0z]
        · intro hx
          simp at hx
      calc
        M.p x0 * ∏ z : α, M.p z ^ tensorPowerTypeProfile (a := α) n xs z =
            (∏ z : α, M.p z ^ (if x0 = z then 1 else 0)) *
              ∏ z : α, M.p z ^ tensorPowerTypeProfile (a := α) n xs z := by
              rw [hsingle]
        _ = ∏ z : α, (M.p z ^ (if x0 = z then 1 else 0)) *
              (M.p z ^ tensorPowerTypeProfile (a := α) n xs z) := by
              rw [Finset.prod_mul_distrib]
        _ = ∏ z : α, M.p z ^ ((if x0 = z then 1 else 0) +
              tensorPowerTypeProfile (a := α) n xs z) := by
              refine Finset.prod_congr rfl ?_
              intro z _
              rw [pow_add]

/-- Tensor-power `q` probability as a product over the type profile. -/
theorem tensorPower_q_eq_profile_prod
    (M : ClassicalBinaryModel α) (n : Nat) (x : TensorPower α n) :
    (M.tensorPower n).q x =
      ∏ z : α, M.q z ^ tensorPowerTypeProfile (a := α) n x z := by
  induction n with
  | zero =>
      cases x
      simp [tensorPower, tensorPowerTypeProfile]
  | succ n ih =>
      rcases x with ⟨x0, xs⟩
      rw [tensorPower_succ_q, ih xs]
      rw [show
          (∏ z : α, M.q z ^ tensorPowerTypeProfile (a := α) (n + 1) (x0, xs) z) =
            ∏ z : α, M.q z ^ ((if x0 = z then 1 else 0) +
              tensorPowerTypeProfile (a := α) n xs z) by
        refine Finset.prod_congr rfl ?_
        intro z _
        rw [tensorPowerTypeProfile_succ]]
      have hsingle :
          (∏ z : α, M.q z ^ (if x0 = z then 1 else 0)) = M.q x0 := by
        rw [Finset.prod_eq_single x0]
        · simp
        · intro z _ hz
          have hx0z : x0 ≠ z := fun h => hz h.symm
          simp [hx0z]
        · intro hx
          simp at hx
      calc
        M.q x0 * ∏ z : α, M.q z ^ tensorPowerTypeProfile (a := α) n xs z =
            (∏ z : α, M.q z ^ (if x0 = z then 1 else 0)) *
              ∏ z : α, M.q z ^ tensorPowerTypeProfile (a := α) n xs z := by
              rw [hsingle]
        _ = ∏ z : α, (M.q z ^ (if x0 = z then 1 else 0)) *
              (M.q z ^ tensorPowerTypeProfile (a := α) n xs z) := by
              rw [Finset.prod_mul_distrib]
        _ = ∏ z : α, M.q z ^ ((if x0 = z then 1 else 0) +
              tensorPowerTypeProfile (a := α) n xs z) := by
              refine Finset.prod_congr rfl ?_
              intro z _
              rw [pow_add]

/-- Product-form lower bound for the `p`-mass of one type class. -/
theorem profileClassMassP_source_lower_bound_product
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N) :
    (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
        Real.exp
          (-(∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) *
        (∏ z : α, ((M.p z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) ≤
      (M.profileClassMassP profile : ℝ) := by
  have hcard :=
    tensorPowerProfileClass_card_source_lower_bound (α := α) hN profile
  have hprob :
      (M.tensorPower N).p profile.rep =
        ∏ z : α, M.p z ^ profile.1 z := by
    rw [← TensorPowerProfile.rep_typeProfile (a := α) profile]
    exact tensorPower_p_eq_profile_prod (M := M) N profile.rep
  have hmass :
      (M.profileClassMassP profile : ℝ) =
        ((tensorPowerProfileClass (a := α) profile).card : ℝ) *
          (∏ z : α, ((M.p z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) := by
    rw [profileClassMassP, profileClassMassP_eq_card_mul, hprob]
    simp
  rw [hmass]
  exact mul_le_mul_of_nonneg_right hcard (by positivity)

/-- Product-form lower bound for the `q`-mass of one type class. -/
theorem profileClassMassQ_source_lower_bound_product
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N) :
    (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
        Real.exp
          (-(∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) *
        (∏ z : α, ((M.q z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) ≤
      (M.profileClassMassQ profile : ℝ) := by
  have hcard :=
    tensorPowerProfileClass_card_source_lower_bound (α := α) hN profile
  have hprob :
      (M.tensorPower N).q profile.rep =
        ∏ z : α, M.q z ^ profile.1 z := by
    rw [← TensorPowerProfile.rep_typeProfile (a := α) profile]
    exact tensorPower_q_eq_profile_prod (M := M) N profile.rep
  have hmass :
      (M.profileClassMassQ profile : ℝ) =
        ((tensorPowerProfileClass (a := α) profile).card : ℝ) *
          (∏ z : α, ((M.q z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) := by
    rw [profileClassMassQ, profileClassMassQ_eq_card_mul, hprob]
    simp
  rw [hmass]
  exact mul_le_mul_of_nonneg_right hcard (by positivity)

/-- The contribution of one type class to equal-prior error is the minimum of
the two equal-prior type-class masses. -/
theorem profileClassErrorContribution_eq_min_mass
    (M : ClassicalBinaryModel α) {N : Nat}
    (profile : TensorPowerProfile α N) :
    ((tensorPowerProfileClass (a := α) profile).sum
        (fun x => min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p x)
          ((1 / 2 : ℝ≥0) * (M.tensorPower N).q x))) =
      min ((1 / 2 : ℝ≥0) * M.profileClassMassP profile)
        ((1 / 2 : ℝ≥0) * M.profileClassMassQ profile) := by
  have hp :
      (tensorPowerProfileClass (a := α) profile).sum
          (fun x => (M.tensorPower N).p x) =
        ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
          (M.tensorPower N).p profile.rep :=
    profileClassMassP_eq_card_mul M profile
  have hq :
      (tensorPowerProfileClass (a := α) profile).sum
          (fun x => (M.tensorPower N).q x) =
        ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
          (M.tensorPower N).q profile.rep :=
    profileClassMassQ_eq_card_mul M profile
  have hsum :
      (tensorPowerProfileClass (a := α) profile).sum
        (fun x => min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p x)
          ((1 / 2 : ℝ≥0) * (M.tensorPower N).q x)) =
        ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
          min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p profile.rep)
            ((1 / 2 : ℝ≥0) * (M.tensorPower N).q profile.rep) := by
    calc
      (tensorPowerProfileClass (a := α) profile).sum
        (fun x => min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p x)
          ((1 / 2 : ℝ≥0) * (M.tensorPower N).q x))
          =
        (tensorPowerProfileClass (a := α) profile).sum
          (fun _x => min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p profile.rep)
            ((1 / 2 : ℝ≥0) * (M.tensorPower N).q profile.rep)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hprof :
                tensorPowerTypeProfile (a := α) N x = profile.1 :=
              (mem_tensorPowerProfileClass (a := α) profile x).mp hx
            have hprof_rep :
                tensorPowerTypeProfile (a := α) N profile.rep = profile.1 :=
              TensorPowerProfile.rep_typeProfile (a := α) profile
            have hp_eq :
                (M.tensorPower N).p x = (M.tensorPower N).p profile.rep :=
              tensorPower_p_eq_of_typeProfile_eq M (hprof.trans hprof_rep.symm)
            have hq_eq :
                (M.tensorPower N).q x = (M.tensorPower N).q profile.rep :=
              tensorPower_q_eq_of_typeProfile_eq M (hprof.trans hprof_rep.symm)
            change
              min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p x)
                  ((1 / 2 : ℝ≥0) * (M.tensorPower N).q x) =
                min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p profile.rep)
                  ((1 / 2 : ℝ≥0) * (M.tensorPower N).q profile.rep)
            rw [hp_eq, hq_eq]
      _ = ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
          min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p profile.rep)
            ((1 / 2 : ℝ≥0) * (M.tensorPower N).q profile.rep) := by
            simp
  rw [hsum]
  rw [profileClassMassP, profileClassMassQ, hp, hq]
  rw [← mul_assoc, ← mul_assoc]
  rw [show
      ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
          min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p profile.rep)
            ((1 / 2 : ℝ≥0) * (M.tensorPower N).q profile.rep) =
        min (((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
              ((1 / 2 : ℝ≥0) * (M.tensorPower N).p profile.rep))
          (((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) *
              ((1 / 2 : ℝ≥0) * (M.tensorPower N).q profile.rep)) by
    exact mul_min_of_nonneg
      ((1 / 2 : ℝ≥0) * (M.tensorPower N).p profile.rep)
      ((1 / 2 : ℝ≥0) * (M.tensorPower N).q profile.rep)
      (show (0 : ℝ≥0) ≤ ((tensorPowerProfileClass (a := α) profile).card : ℝ≥0) by
        positivity)]
  congr 1 <;> ring

/-- A single type class contributes no more than the total classical
equal-prior error. -/
theorem profileClassErrorContribution_le_equalPriorError
    (M : ClassicalBinaryModel α) {N : Nat}
    (profile : TensorPowerProfile α N) :
    ((tensorPowerProfileClass (a := α) profile).sum
        (fun x => min ((1 / 2 : ℝ≥0) * (M.tensorPower N).p x)
          ((1 / 2 : ℝ≥0) * (M.tensorPower N).q x))) ≤
      (M.tensorPower N).equalPriorError := by
  unfold equalPriorError
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro x hx
      simp)
    (by
      intro x _ _
      positivity)

/-- Source-backed product-form lower bound contributed by one type class to the
classical equal-prior error. -/
theorem equalPriorError_source_lower_bound_profile_product
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N) :
    (1 / 2 : ℝ) *
        min
          ((finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
            Real.exp
              (-(∑ z : α,
                (profile.1 z : ℝ) *
                  Real.log ((profile.1 z : ℝ) / (N : ℝ)))) *
            (∏ z : α, ((M.p z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ))
          ((finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
            Real.exp
              (-(∑ z : α,
                (profile.1 z : ℝ) *
                  Real.log ((profile.1 z : ℝ) / (N : ℝ)))) *
            (∏ z : α, ((M.q z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ))
      ≤ ((M.tensorPower N).equalPriorError : ℝ) := by
  let Lp : ℝ :=
    (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
      Real.exp
        (-(∑ z : α,
          (profile.1 z : ℝ) *
            Real.log ((profile.1 z : ℝ) / (N : ℝ)))) *
      (∏ z : α, ((M.p z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ)
  let Lq : ℝ :=
    (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
      Real.exp
        (-(∑ z : α,
          (profile.1 z : ℝ) *
            Real.log ((profile.1 z : ℝ) / (N : ℝ)))) *
      (∏ z : α, ((M.q z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ)
  have hLp :
      Lp ≤ (M.profileClassMassP profile : ℝ) := by
    simpa [Lp] using
      profileClassMassP_source_lower_bound_product (M := M) hN profile
  have hLq :
      Lq ≤ (M.profileClassMassQ profile : ℝ) := by
    simpa [Lq] using
      profileClassMassQ_source_lower_bound_product (M := M) hN profile
  have hmin :
      (1 / 2 : ℝ) * min Lp Lq ≤
        (min ((1 / 2 : ℝ≥0) * M.profileClassMassP profile)
          ((1 / 2 : ℝ≥0) * M.profileClassMassQ profile) : ℝ) := by
    have hhalfP :
        (1 / 2 : ℝ) * Lp ≤
          (((1 / 2 : ℝ≥0) * M.profileClassMassP profile : ℝ≥0) : ℝ) := by
      simpa [NNReal.coe_mul, NNReal.coe_div] using
        mul_le_mul_of_nonneg_left hLp (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ))
    have hhalfQ :
        (1 / 2 : ℝ) * Lq ≤
          (((1 / 2 : ℝ≥0) * M.profileClassMassQ profile : ℝ≥0) : ℝ) := by
      simpa [NNReal.coe_mul, NNReal.coe_div] using
        mul_le_mul_of_nonneg_left hLq (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ))
    have hmulmin :
        (1 / 2 : ℝ) * min Lp Lq =
          min ((1 / 2 : ℝ) * Lp) ((1 / 2 : ℝ) * Lq) := by
      rw [mul_min_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ))]
    rw [hmulmin]
    exact min_le_min hhalfP hhalfQ
  have hclass :=
    profileClassErrorContribution_eq_min_mass (M := M) profile
  have hclass_le :=
    profileClassErrorContribution_le_equalPriorError (M := M) profile
  exact hmin.trans (by
    have htarget :
        ((min ((1 / 2 : ℝ≥0) * M.profileClassMassP profile)
            ((1 / 2 : ℝ≥0) * M.profileClassMassQ profile) : ℝ≥0) : ℝ) ≤
          ((M.tensorPower N).equalPriorError : ℝ) := by
      rw [← hclass]
      exact_mod_cast hclass_le
    simpa [NNReal.coe_mul, NNReal.coe_div] using htarget)

/-- Source product-form lower bound attached to one finite type/profile. -/
def profileProductErrorLowerBound
    (M : ClassicalBinaryModel α) {N : Nat} (profile : TensorPowerProfile α N) : ℝ :=
  (1 / 2 : ℝ) *
    min
      ((finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
        Real.exp
          (-(∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) *
        (∏ z : α, ((M.p z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ))
      ((finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
        Real.exp
          (-(∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) *
        (∏ z : α, ((M.q z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ))

/-- Finite-type Chernoff value obtained by minimizing the source product-form
type-class lower bound over all `N`-types. -/
def finiteTypeChernoffValue (M : ClassicalBinaryModel α) (N : Nat) : EReal :=
  ⨅ profile : TensorPowerProfile α N,
    normalizedNegLog (N - 1)
      (ENNReal.ofReal (M.profileProductErrorLowerBound profile))

theorem profileProductErrorLowerBound_nonneg
    (M : ClassicalBinaryModel α) {N : Nat} (profile : TensorPowerProfile α N) :
    0 ≤ M.profileProductErrorLowerBound profile := by
  unfold profileProductErrorLowerBound
  positivity

/-- On common support, the source profile lower bound is strictly positive. -/
theorem profileProductErrorLowerBound_pos_of_supported
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N)
    (hp : (profile.empiricalDistribution hN).SupportedBy M.p)
    (hq : (profile.empiricalDistribution hN).SupportedBy M.q) :
    0 < M.profileProductErrorLowerBound profile := by
  have hN_nn : (0 : ℝ≥0) < (N : ℝ≥0) := by
    exact_mod_cast hN
  have hp_pos_factor :
      ∀ z : α, 0 < M.p z ^ profile.1 z := by
    intro z
    by_cases hz : profile.1 z = 0
    · simp [hz]
    · have hz_nat : 0 < profile.1 z :=
        Nat.pos_of_ne_zero hz
      have hz_nn : (0 : ℝ≥0) < (profile.1 z : ℝ≥0) := by
        exact_mod_cast hz_nat
      have he :
          (profile.empiricalDistribution hN).prob z ≠ 0 := by
        rw [TensorPowerProfile.empiricalDistribution_prob]
        exact ne_of_gt (div_pos hz_nn hN_nn)
      have hpz : M.p z ≠ 0 := hp z he
      have hpz_pos : 0 < M.p z :=
        lt_of_le_of_ne (by positivity) (Ne.symm hpz)
      exact pow_pos hpz_pos _
  have hq_pos_factor :
      ∀ z : α, 0 < M.q z ^ profile.1 z := by
    intro z
    by_cases hz : profile.1 z = 0
    · simp [hz]
    · have hz_nat : 0 < profile.1 z :=
        Nat.pos_of_ne_zero hz
      have hz_nn : (0 : ℝ≥0) < (profile.1 z : ℝ≥0) := by
        exact_mod_cast hz_nat
      have he :
          (profile.empiricalDistribution hN).prob z ≠ 0 := by
        rw [TensorPowerProfile.empiricalDistribution_prob]
        exact ne_of_gt (div_pos hz_nn hN_nn)
      have hqz : M.q z ≠ 0 := hq z he
      have hqz_pos : 0 < M.q z :=
        lt_of_le_of_ne (by positivity) (Ne.symm hqz)
      exact pow_pos hqz_pos _
  have hp_prod_nn : 0 < ∏ z : α, M.p z ^ profile.1 z :=
    Finset.prod_pos fun z _ => hp_pos_factor z
  have hq_prod_nn : 0 < ∏ z : α, M.q z ^ profile.1 z :=
    Finset.prod_pos fun z _ => hq_pos_factor z
  have hp_prod : 0 < ((∏ z : α, M.p z ^ profile.1 z : ℝ≥0) : ℝ) := by
    exact_mod_cast hp_prod_nn
  have hq_prod : 0 < ((∏ z : α, M.q z ^ profile.1 z : ℝ≥0) : ℝ) := by
    exact_mod_cast hq_prod_nn
  have hp_prod' :
      0 < ∏ z : α, (((M.p z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) := by
    simpa using hp_prod
  have hq_prod' :
      0 < ∏ z : α, (((M.q z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) := by
    simpa using hq_prod
  have hpref :
      0 < (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal := by
    unfold finiteAlphabetMethodOfTypesPolynomialPrefactor
    apply ENNReal.toReal_pos
    · exact ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    · apply ENNReal.inv_ne_top.mpr
      apply ENNReal.pow_ne_zero
      norm_num
  let common : ℝ :=
    (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
      Real.exp
        (-(∑ z : α,
          (profile.1 z : ℝ) *
            Real.log ((profile.1 z : ℝ) / (N : ℝ))))
  have hcommon : 0 < common := by
    unfold common
    positivity
  have hpterm :
      0 < common * (∏ z : α, ((M.p z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) :=
    mul_pos hcommon hp_prod'
  have hqterm :
      0 < common * (∏ z : α, ((M.q z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) :=
    mul_pos hcommon hq_prod'
  unfold profileProductErrorLowerBound
  change 0 <
    (1 / 2 : ℝ) *
      min
        (common * (∏ z : α, ((M.p z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ))
        (common * (∏ z : α, ((M.q z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ))
  exact mul_pos (by positivity) (lt_min hpterm hqterm)

/-- The real KL of a supported empirical profile expands as the expected
log-ratio. -/
theorem profileEmpirical_relativeEntropyReal_eq_sum_log_ratio
    {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N)
    (p : ClassicalDistribution α)
    (hp : (profile.empiricalDistribution hN).SupportedBy p.prob) :
    relativeEntropyReal (profile.empiricalDistribution hN) p =
      ∑ z : α,
        ((profile.1 z : ℝ) / (N : ℝ)) *
          (Real.log ((profile.1 z : ℝ) / (N : ℝ)) -
            Real.log (p.prob z : ℝ)) := by
  classical
  unfold relativeEntropyReal relativeEntropySummandReal
  refine Finset.sum_congr rfl ?_
  intro z _
  by_cases hz : profile.1 z = 0
  · have hemp : (profile.empiricalDistribution hN).prob z = 0 := by
      rw [TensorPowerProfile.empiricalDistribution_prob]
      simp [hz]
    simp [hemp, hz]
  · have hN_nn : (0 : ℝ≥0) < (N : ℝ≥0) := by
      exact_mod_cast hN
    have hz_nat : 0 < profile.1 z := Nat.pos_of_ne_zero hz
    have hz_nn : (0 : ℝ≥0) < (profile.1 z : ℝ≥0) := by
      exact_mod_cast hz_nat
    have hemp_ne : (profile.empiricalDistribution hN).prob z ≠ 0 := by
      rw [TensorPowerProfile.empiricalDistribution_prob]
      exact ne_of_gt (div_pos hz_nn hN_nn)
    have hpz_ne : p.prob z ≠ 0 := hp z hemp_ne
    have hemp_pos : 0 < ((profile.empiricalDistribution hN).prob z : ℝ) := by
      have hemp_nn : (0 : ℝ≥0) < (profile.empiricalDistribution hN).prob z :=
        lt_of_le_of_ne (by positivity) (Ne.symm hemp_ne)
      exact_mod_cast hemp_nn
    have hpz_pos : 0 < (p.prob z : ℝ) := by
      have hpz_nn : (0 : ℝ≥0) < p.prob z :=
        lt_of_le_of_ne (by positivity) (Ne.symm hpz_ne)
      exact_mod_cast hpz_nn
    have hlog :
        Real.log (((profile.empiricalDistribution hN).prob z : ℝ) /
            (p.prob z : ℝ)) =
          Real.log ((profile.empiricalDistribution hN).prob z : ℝ) -
            Real.log (p.prob z : ℝ) := by
      rw [Real.log_div hemp_pos.ne' hpz_pos.ne']
    rw [TensorPowerProfile.empiricalDistribution_prob] at hlog
    simp [TensorPowerProfile.empiricalDistribution_prob, hz, Nat.ne_of_gt hN,
      NNReal.coe_div]
    simpa [NNReal.coe_div] using hlog

/-- Multiplying the empirical-profile KL by the copy number removes the
empirical normalization. -/
theorem profileEmpirical_mul_relativeEntropyReal_eq_sum_log_sub
    {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N)
    (p : ClassicalDistribution α)
    (hp : (profile.empiricalDistribution hN).SupportedBy p.prob) :
    (N : ℝ) * relativeEntropyReal (profile.empiricalDistribution hN) p =
      (∑ z : α,
        (profile.1 z : ℝ) *
          Real.log ((profile.1 z : ℝ) / (N : ℝ))) -
        ∑ z : α, (profile.1 z : ℝ) * Real.log (p.prob z : ℝ) := by
  classical
  have hN_ne : (N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hN
  rw [profileEmpirical_relativeEntropyReal_eq_sum_log_ratio hN profile p hp]
  calc
    (N : ℝ) *
        (∑ z : α,
          (↑(profile.1 z) / ↑N) *
            (Real.log (↑(profile.1 z) / ↑N) - Real.log ↑(p.prob z)))
        =
      ∑ z : α,
        (N : ℝ) *
          ((↑(profile.1 z) / ↑N) *
            (Real.log (↑(profile.1 z) / ↑N) - Real.log ↑(p.prob z))) := by
          rw [Finset.mul_sum]
    _ =
      ∑ z : α,
        ((profile.1 z : ℝ) * Real.log ((profile.1 z : ℝ) / (N : ℝ)) -
          (profile.1 z : ℝ) * Real.log (p.prob z : ℝ)) := by
        refine Finset.sum_congr rfl ?_
        intro z _
        field_simp [hN_ne]
    _ =
      (∑ z : α,
        (profile.1 z : ℝ) *
          Real.log ((profile.1 z : ℝ) / (N : ℝ))) -
        ∑ z : α, (profile.1 z : ℝ) * Real.log (p.prob z : ℝ) := by
        rw [Finset.sum_sub_distrib]

/-- Supported profile probabilities rewrite the KL exponent into the product
probability factor used by the method-of-types lower bound. -/
theorem exp_neg_mul_profileEmpirical_relativeEntropyReal_eq_prod
    {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N)
    (p : ClassicalDistribution α)
    (hp : (profile.empiricalDistribution hN).SupportedBy p.prob) :
    Real.exp
        (-(N : ℝ) *
          relativeEntropyReal (profile.empiricalDistribution hN) p) =
      Real.exp
          (-(∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) *
        (∏ z : α, ((p.prob z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) := by
  classical
  let S : ℝ :=
    ∑ z : α,
      (profile.1 z : ℝ) *
        Real.log ((profile.1 z : ℝ) / (N : ℝ))
  let L : ℝ := ∑ z : α, (profile.1 z : ℝ) * Real.log (p.prob z : ℝ)
  have hmul :=
    profileEmpirical_mul_relativeEntropyReal_eq_sum_log_sub
      hN profile p hp
  have hprod :
      Real.exp L =
        (∏ z : α, ((p.prob z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) := by
    let realTerm : α → ℝ := fun z => ((p.prob z : ℝ) ^ profile.1 z)
    let expTerm : α → ℝ := fun z =>
      Real.exp ((profile.1 z : ℝ) * Real.log (p.prob z : ℝ))
    have hcoe :
        (∏ z : α, ((p.prob z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) =
          ∏ z : α, realTerm z := by
      simp [realTerm]
    have hterms : Finset.univ.prod realTerm = Finset.univ.prod expTerm := by
      refine Finset.prod_congr rfl ?_
      intro z _
      by_cases hz : profile.1 z = 0
      · simp [realTerm, expTerm, hz]
      · have hN_nn : (0 : ℝ≥0) < (N : ℝ≥0) := by
          exact_mod_cast hN
        have hz_nat : 0 < profile.1 z := Nat.pos_of_ne_zero hz
        have hz_nn : (0 : ℝ≥0) < (profile.1 z : ℝ≥0) := by
          exact_mod_cast hz_nat
        have hemp_ne : (profile.empiricalDistribution hN).prob z ≠ 0 := by
          rw [TensorPowerProfile.empiricalDistribution_prob]
          exact ne_of_gt (div_pos hz_nn hN_nn)
        have hpz_ne : p.prob z ≠ 0 := hp z hemp_ne
        have hpz_pos : 0 < (p.prob z : ℝ) := by
          have hpz_nn : (0 : ℝ≥0) < p.prob z :=
            lt_of_le_of_ne (by positivity) (Ne.symm hpz_ne)
          exact_mod_cast hpz_nn
        calc
          realTerm z = ((p.prob z : ℝ) ^ profile.1 z) := by
            rfl
          _ = (Real.exp (Real.log (p.prob z : ℝ))) ^ profile.1 z := by
            rw [Real.exp_log hpz_pos]
          _ = expTerm z := by
            unfold expTerm
            rw [← Real.exp_nat_mul]
    have hexp : Finset.univ.prod expTerm = Real.exp L := by
      unfold expTerm L
      rw [Real.exp_sum]
    exact (hcoe.trans (hterms.trans hexp)).symm
  have hmul' :
      (N : ℝ) * relativeEntropyReal (profile.empiricalDistribution hN) p =
        S - L := by
    simpa [S, L] using hmul
  calc
    Real.exp
        (-(N : ℝ) *
          relativeEntropyReal (profile.empiricalDistribution hN) p)
        = Real.exp (-(S - L)) := by
          congr 1
          rw [neg_mul, hmul']
    _ = Real.exp (-S) * Real.exp L := by
          rw [show -(S - L) = -S + L by ring, Real.exp_add]
    _ = Real.exp (-S) *
        (∏ z : α, ((p.prob z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ) := by
          rw [hprod]

/-- Source-shaped positive lower bound used before taking logarithms. -/
theorem profileProductErrorLowerBound_source_exp_lower_bound
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N)
    (hp : (profile.empiricalDistribution hN).SupportedBy M.p)
    (hq : (profile.empiricalDistribution hN).SupportedBy M.q) :
    (1 / 2 : ℝ) *
        (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
        Real.exp
          (-(N : ℝ) *
            max
              (relativeEntropyReal (profile.empiricalDistribution hN) M.pDistribution)
              (relativeEntropyReal (profile.empiricalDistribution hN) M.qDistribution))
      ≤ M.profileProductErrorLowerBound profile := by
  classical
  let Dp : ℝ :=
    relativeEntropyReal (profile.empiricalDistribution hN) M.pDistribution
  let Dq : ℝ :=
    relativeEntropyReal (profile.empiricalDistribution hN) M.qDistribution
  let common : ℝ :=
    (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
      Real.exp
        (-(∑ z : α,
          (profile.1 z : ℝ) *
            Real.log ((profile.1 z : ℝ) / (N : ℝ))))
  let P : ℝ :=
    (∏ z : α, ((M.p z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ)
  let Q : ℝ :=
    (∏ z : α, ((M.q z : ℝ≥0) ^ profile.1 z : ℝ≥0) : ℝ)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hp' : (profile.empiricalDistribution hN).SupportedBy M.pDistribution.prob := by
    simpa [pDistribution] using hp
  have hq' : (profile.empiricalDistribution hN).SupportedBy M.qDistribution.prob := by
    simpa [qDistribution] using hq
  have hp_exp :
      Real.exp (-(N : ℝ) * Dp) =
        Real.exp
          (-(∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) * P := by
    simpa [Dp, P, pDistribution] using
      exp_neg_mul_profileEmpirical_relativeEntropyReal_eq_prod
        hN profile M.pDistribution hp'
  have hq_exp :
      Real.exp (-(N : ℝ) * Dq) =
        Real.exp
          (-(∑ z : α,
            (profile.1 z : ℝ) *
              Real.log ((profile.1 z : ℝ) / (N : ℝ)))) * Q := by
    simpa [Dq, Q, qDistribution] using
      exp_neg_mul_profileEmpirical_relativeEntropyReal_eq_prod
        hN profile M.qDistribution hq'
  have hpmax :
      Real.exp (-(N : ℝ) * max Dp Dq) ≤ Real.exp (-(N : ℝ) * Dp) := by
    exact Real.exp_le_exp.mpr (by
      have hle : Dp ≤ max Dp Dq := le_max_left _ _
      nlinarith)
  have hqmax :
      Real.exp (-(N : ℝ) * max Dp Dq) ≤ Real.exp (-(N : ℝ) * Dq) := by
    exact Real.exp_le_exp.mpr (by
      have hle : Dq ≤ max Dp Dq := le_max_right _ _
      nlinarith)
  have hc_nonneg :
      0 ≤ (1 / 2 : ℝ) *
        (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal := by
    positivity
  have hp_bound :
      (1 / 2 : ℝ) *
          (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
          Real.exp (-(N : ℝ) * max Dp Dq) ≤
        (1 / 2 : ℝ) * (common * P) := by
    calc
      (1 / 2 : ℝ) *
          (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
          Real.exp (-(N : ℝ) * max Dp Dq)
          ≤
        (1 / 2 : ℝ) *
          (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
          Real.exp (-(N : ℝ) * Dp) := by
            exact mul_le_mul_of_nonneg_left hpmax hc_nonneg
      _ = (1 / 2 : ℝ) * (common * P) := by
            rw [hp_exp]
            simp [common, P]
            ring
  have hq_bound :
      (1 / 2 : ℝ) *
          (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
          Real.exp (-(N : ℝ) * max Dp Dq) ≤
        (1 / 2 : ℝ) * (common * Q) := by
    calc
      (1 / 2 : ℝ) *
          (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
          Real.exp (-(N : ℝ) * max Dp Dq)
          ≤
        (1 / 2 : ℝ) *
          (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
          Real.exp (-(N : ℝ) * Dq) := by
            exact mul_le_mul_of_nonneg_left hqmax hc_nonneg
      _ = (1 / 2 : ℝ) * (common * Q) := by
            rw [hq_exp]
            simp [common, Q]
            ring
  have hmin :
      (1 / 2 : ℝ) *
          (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
          Real.exp (-(N : ℝ) * max Dp Dq) ≤
        min ((1 / 2 : ℝ) * (common * P))
          ((1 / 2 : ℝ) * (common * Q)) :=
    le_min hp_bound hq_bound
  have hmin_half :
      min ((1 / 2 : ℝ) * (common * P))
          ((1 / 2 : ℝ) * (common * Q)) =
        (1 / 2 : ℝ) * min (common * P) (common * Q) := by
    rw [← mul_min_of_nonneg (common * P) (common * Q)
      (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ))]
  calc
    (1 / 2 : ℝ) *
        (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal *
        Real.exp (-(N : ℝ) * max Dp Dq)
        ≤ min ((1 / 2 : ℝ) * (common * P))
            ((1 / 2 : ℝ) * (common * Q)) := hmin
    _ = M.profileProductErrorLowerBound profile := by
          rw [hmin_half]
          simp [profileProductErrorLowerBound, common, P, Q]

/-- Supported-profile real logarithmic method-of-types bound. -/
theorem normalizedNegLog_profileProductErrorLowerBound_le
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N)
    (hp : (profile.empiricalDistribution hN).SupportedBy M.p)
    (hq : (profile.empiricalDistribution hN).SupportedBy M.q) :
    -Real.log (M.profileProductErrorLowerBound profile) / (N : ℝ) ≤
      max
          (relativeEntropyReal (profile.empiricalDistribution hN) M.pDistribution)
          (relativeEntropyReal (profile.empiricalDistribution hN) M.qDistribution) +
        (Fintype.card α : ℝ) * Real.log (((N + 1 : Nat) : ℝ)) / (N : ℝ) +
        Real.log 2 / (N : ℝ) := by
  classical
  let c : ℝ :=
    (1 / 2 : ℝ) *
      (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal
  let d : ℝ :=
    max
      (relativeEntropyReal (profile.empiricalDistribution hN) M.pDistribution)
      (relativeEntropyReal (profile.empiricalDistribution hN) M.qDistribution)
  have hR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hc : 0 < c := by
    unfold c
    have hpref :
        0 < (finiteAlphabetMethodOfTypesPolynomialPrefactor α N).toReal := by
      rw [finiteAlphabetMethodOfTypesPolynomialPrefactor_toReal]
      positivity
    positivity
  have hE :
      0 < M.profileProductErrorLowerBound profile :=
    profileProductErrorLowerBound_pos_of_supported (M := M) hN profile hp hq
  have hbound : c * Real.exp (-(N : ℝ) * d) ≤
      M.profileProductErrorLowerBound profile := by
    simpa [c, d, mul_assoc] using
      profileProductErrorLowerBound_source_exp_lower_bound
        (M := M) hN profile hp hq
  have hlog :=
    neg_log_div_le_of_mul_exp_neg_le (E := M.profileProductErrorLowerBound profile)
      (c := c) (d := d) (R := (N : ℝ)) hR hc hE hbound
  have hpen :=
    equalPriorMethodOfTypesPrefactor_log_penalty (α := α) hN
  calc
    -Real.log (M.profileProductErrorLowerBound profile) / (N : ℝ)
        ≤ d + (-Real.log c) / (N : ℝ) := hlog
    _ =
      d +
        ((Fintype.card α : ℝ) * Real.log (((N + 1 : Nat) : ℝ)) / (N : ℝ) +
          Real.log 2 / (N : ℝ)) := by
          rw [show (-Real.log c) / (N : ℝ) =
              (Fintype.card α : ℝ) * Real.log (((N + 1 : Nat) : ℝ)) / (N : ℝ) +
                Real.log 2 / (N : ℝ) by
            simpa [c] using hpen]
    _ =
      max
          (relativeEntropyReal (profile.empiricalDistribution hN) M.pDistribution)
          (relativeEntropyReal (profile.empiricalDistribution hN) M.qDistribution) +
        (Fintype.card α : ℝ) * Real.log (((N + 1 : Nat) : ℝ)) / (N : ℝ) +
        Real.log 2 / (N : ℝ) := by
          simp [d]
          ring_nf

/-- The source product-form lower bound is below the actual classical
equal-prior error. -/
theorem profileProductErrorLowerBound_le_equalPriorError
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N) :
    ENNReal.ofReal (M.profileProductErrorLowerBound profile) ≤
      (M.tensorPower N).equalPriorErrorENNReal := by
  have hreal :=
    equalPriorError_source_lower_bound_profile_product (M := M) hN profile
  unfold equalPriorErrorENNReal
  rw [ENNReal.ofReal_le_iff_le_toReal]
  · simpa [profileProductErrorLowerBound] using hreal
  · simp

/-- Pointwise finite-copy method-of-types bound through the finite-type value. -/
theorem normalizedNegLog_le_finiteTypeChernoffValue
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N) :
    normalizedNegLog (N - 1) ((M.tensorPower N).equalPriorErrorENNReal) ≤
      M.finiteTypeChernoffValue N := by
  unfold finiteTypeChernoffValue
  refine le_iInf ?_
  intro profile
  exact normalizedNegLog_antitone (N - 1)
    (profileProductErrorLowerBound_le_equalPriorError (M := M) hN profile)

/-- EReal lift of the supported-profile logarithmic method-of-types bound,
with unsupported profiles handled by the support-aware `⊤` convention. -/
theorem normalizedNegLog_profileProductErrorLowerBound_le_distributionKLMax
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N) :
    normalizedNegLog (N - 1)
        (ENNReal.ofReal (M.profileProductErrorLowerBound profile)) ≤
      M.distributionKLMax (profile.empiricalDistribution hN) +
        finiteAlphabetMethodOfTypesPolynomialPenalty α (N - 1) +
        equalPriorAverageLogPenalty (N - 1) := by
  classical
  have hcoe_max : ∀ x y : ℝ,
      max (x : EReal) (y : EReal) = ((max x y : ℝ) : EReal) := by
    intro x y
    by_cases hxy : x ≤ y
    · rw [max_eq_right (EReal.coe_le_coe_iff.mpr hxy), max_eq_right hxy]
    · have hyx : y ≤ x := le_of_not_ge hxy
      rw [max_eq_left (EReal.coe_le_coe_iff.mpr hyx), max_eq_left hyx]
  by_cases hp :
      (profile.empiricalDistribution hN).SupportedBy M.pDistribution.prob
  · have hp' : (profile.empiricalDistribution hN).SupportedBy M.p := by
      simpa [pDistribution] using hp
    by_cases hq :
        (profile.empiricalDistribution hN).SupportedBy M.qDistribution.prob
    · have hq' : (profile.empiricalDistribution hN).SupportedBy M.q := by
        simpa [qDistribution] using hq
      have hpos :
          0 < M.profileProductErrorLowerBound profile :=
        profileProductErrorLowerBound_pos_of_supported (M := M) hN profile hp' hq'
      have hNreal : (N : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hN
      have hleft :
          normalizedNegLog (N - 1)
              (ENNReal.ofReal (M.profileProductErrorLowerBound profile)) =
            ((-Real.log (M.profileProductErrorLowerBound profile) / (N : ℝ) : ℝ) :
              EReal) := by
        rw [normalizedNegLog_ofReal_eq_coe_real (N - 1) hpos]
        rw [Nat.sub_add_cancel hN]
        congr 1
        field_simp [hNreal]
      have hrhs :
          M.distributionKLMax (profile.empiricalDistribution hN) +
              finiteAlphabetMethodOfTypesPolynomialPenalty α (N - 1) +
              equalPriorAverageLogPenalty (N - 1) =
            ((max
                (relativeEntropyReal (profile.empiricalDistribution hN) M.pDistribution)
                (relativeEntropyReal (profile.empiricalDistribution hN) M.qDistribution) +
              (Fintype.card α : ℝ) *
                Real.log (((N + 1 : Nat) : ℝ)) / (N : ℝ) +
              Real.log 2 / (N : ℝ) : ℝ) : EReal) := by
        unfold distributionKLMax relativeEntropy
        simp [pDistribution, qDistribution, hp', hq',
          finiteAlphabetMethodOfTypesPolynomialPenalty,
          equalPriorAverageLogPenalty, hcoe_max, EReal.coe_add]
        have hsub_real : ((N - 1 : Nat) : ℝ) = (N : ℝ) - 1 := by
          rw [Nat.cast_sub (Nat.succ_le_of_lt hN)]
          norm_num
        rw [hsub_real]
        field_simp [hNreal]
        ring_nf
      rw [hleft, hrhs, EReal.coe_le_coe_iff]
      exact normalizedNegLog_profileProductErrorLowerBound_le (M := M) hN profile hp' hq'
    · have hq' : ¬(profile.empiricalDistribution hN).SupportedBy M.q := by
        simpa [qDistribution] using hq
      have hrhs :
          M.distributionKLMax (profile.empiricalDistribution hN) +
              finiteAlphabetMethodOfTypesPolynomialPenalty α (N - 1) +
              equalPriorAverageLogPenalty (N - 1) = ⊤ := by
        simp [distributionKLMax, relativeEntropy, pDistribution, qDistribution,
          hp', hq', finiteAlphabetMethodOfTypesPolynomialPenalty,
          equalPriorAverageLogPenalty]
      rw [hrhs]
      exact le_top
  · have hp' : ¬(profile.empiricalDistribution hN).SupportedBy M.p := by
      simpa [pDistribution] using hp
    have hrhs :
        M.distributionKLMax (profile.empiricalDistribution hN) +
            finiteAlphabetMethodOfTypesPolynomialPenalty α (N - 1) +
            equalPriorAverageLogPenalty (N - 1) = ⊤ := by
      simp [distributionKLMax, relativeEntropy, pDistribution, qDistribution,
        hp', finiteAlphabetMethodOfTypesPolynomialPenalty,
        equalPriorAverageLogPenalty]
    rw [hrhs]
    exact le_top

/-- Finite-type KL minimax value over empirical distributions of `N`-profiles.
For `N = 0` this is set to `⊤`; all method-of-types applications use
positive copy number `N = n + 1`. -/
noncomputable def finiteTypeKLDualValue
    (M : ClassicalBinaryModel α) [DecidableEq α] (N : Nat) : EReal :=
  if hN : 0 < N then
    ⨅ profile : TensorPowerProfile α N,
      M.distributionKLMax (profile.empiricalDistribution hN)
  else
    ⊤

omit [DecidableEq α] in
theorem finiteTypeKLDualValue_eq_iInf_of_pos
    (M : ClassicalBinaryModel α) [DecidableEq α] {N : Nat} (hN : 0 < N) :
    M.finiteTypeKLDualValue N =
      ⨅ profile : TensorPowerProfile α N,
        M.distributionKLMax (profile.empiricalDistribution hN) := by
  simp [finiteTypeKLDualValue, hN]

omit [DecidableEq α] in
theorem finiteTypeKLDualValue_zero
    (M : ClassicalBinaryModel α) [DecidableEq α] :
    M.finiteTypeKLDualValue 0 = ⊤ := by
  simp [finiteTypeKLDualValue]

/-- The finite-type KL dual value is bounded by every empirical profile
candidate. -/
theorem finiteTypeKLDualValue_le_distributionKLMax
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N)
    (profile : TensorPowerProfile α N) :
    M.finiteTypeKLDualValue N ≤
      M.distributionKLMax (profile.empiricalDistribution hN) := by
  classical
  rw [finiteTypeKLDualValue_eq_iInf_of_pos (M := M) hN]
  exact iInf_le _ profile

/-- Rounded empirical profiles are admissible candidates for the finite-type
KL dual value. -/
theorem finiteTypeKLDualValue_le_roundedDistributionKLMax
    (M : ClassicalBinaryModel α) (r : ClassicalDistribution α)
    {N : Nat} (hN : 0 < N) :
    M.finiteTypeKLDualValue N ≤
      M.distributionKLMax ((r.roundedProfile N).empiricalDistribution hN) := by
  exact finiteTypeKLDualValue_le_distributionKLMax
    (M := M) hN (r.roundedProfile N)

/-- The KL minimax objective is continuous along rounded empirical profiles
whose limiting distribution is supported on both model distributions. -/
theorem distributionKLMax_roundedProfile_tendsto
    (M : ClassicalBinaryModel α) (r : ClassicalDistribution α)
    (hp : r.SupportedBy M.p) (hq : r.SupportedBy M.q) :
    Tendsto
      (fun n : Nat =>
        M.distributionKLMax
          ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n)))
      atTop (𝓝 (M.distributionKLMax r)) := by
  classical
  have hp' : r.SupportedBy M.pDistribution.prob := by
    simpa [pDistribution] using hp
  have hq' : r.SupportedBy M.qDistribution.prob := by
    simpa [qDistribution] using hq
  have hptend :
      Tendsto
        (fun n : Nat =>
          relativeEntropyReal
            ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n))
            M.pDistribution)
        atTop (𝓝 (relativeEntropyReal r M.pDistribution)) :=
    ClassicalDistribution.relativeEntropyReal_roundedProfile_tendsto
      (r := r) (p := M.pDistribution) hp'
  have hqtend :
      Tendsto
        (fun n : Nat =>
          relativeEntropyReal
            ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n))
            M.qDistribution)
        atTop (𝓝 (relativeEntropyReal r M.qDistribution)) :=
    ClassicalDistribution.relativeEntropyReal_roundedProfile_tendsto
      (r := r) (p := M.qDistribution) hq'
  have hmaxtend :
      Tendsto
        (fun n : Nat =>
          max
            (relativeEntropyReal
              ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n))
              M.pDistribution)
            (relativeEntropyReal
              ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n))
              M.qDistribution))
        atTop
        (𝓝 (max (relativeEntropyReal r M.pDistribution)
          (relativeEntropyReal r M.qDistribution))) :=
    hptend.max hqtend
  have htarget :
      M.distributionKLMax r =
        ((max (relativeEntropyReal r M.pDistribution)
            (relativeEntropyReal r M.qDistribution) : ℝ) : EReal) :=
    distributionKLMax_eq_coe_real_of_supported (M := M) (r := r) hp hq
  rw [htarget]
  refine (EReal.tendsto_coe.mpr hmaxtend).congr' ?_
  filter_upwards [] with n
  let rn :=
    (r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n)
  have hrn : rn.SupportedBy r.prob := by
    exact ClassicalDistribution.roundedProfile_empiricalDistribution_supportedBy
      (r := r) (N := n + 1) (Nat.succ_pos n)
  have hp_rn : rn.SupportedBy M.p := hrn.trans hp
  have hq_rn : rn.SupportedBy M.q := hrn.trans hq
  exact (distributionKLMax_eq_coe_real_of_supported
    (M := M) (r := rn) hp_rn hq_rn).symm

/-- The finite-type KL dual limsup is bounded by the KL minimax objective of
any common-support distribution, via rounded empirical approximants. -/
theorem limsup_finiteTypeKLDualValue_le_distributionKLMax
    (M : ClassicalBinaryModel α) (r : ClassicalDistribution α)
    (hp : r.SupportedBy M.p) (hq : r.SupportedBy M.q) :
    Filter.limsup
        (fun n : Nat => M.finiteTypeKLDualValue (n + 1))
        atTop ≤ M.distributionKLMax r := by
  classical
  have hpoint :
      (fun n : Nat => M.finiteTypeKLDualValue (n + 1)) ≤ᶠ[atTop]
        fun n : Nat =>
          M.distributionKLMax
            ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n)) := by
    exact Filter.Eventually.of_forall fun n =>
      finiteTypeKLDualValue_le_roundedDistributionKLMax
        (M := M) (r := r) (N := n + 1) (Nat.succ_pos n)
  have htend :=
    distributionKLMax_roundedProfile_tendsto (M := M) (r := r) hp hq
  calc
    Filter.limsup
        (fun n : Nat => M.finiteTypeKLDualValue (n + 1))
        atTop
        ≤
      Filter.limsup
        (fun n : Nat =>
          M.distributionKLMax
            ((r.roundedProfile (n + 1)).empiricalDistribution (Nat.succ_pos n)))
        atTop :=
          Filter.limsup_le_limsup hpoint (β := EReal)
    _ = M.distributionKLMax r := htend.limsup_eq

/-- Finite-copy method-of-types bound through the finite-type KL dual value,
including the polynomial type-counting penalty and the equal-prior `log 2`
penalty. -/
theorem finiteTypeChernoffValue_le_finiteTypeKLDualValue_add_penalties
    (M : ClassicalBinaryModel α) {N : Nat} (hN : 0 < N) :
    M.finiteTypeChernoffValue N ≤
      M.finiteTypeKLDualValue N +
        finiteAlphabetMethodOfTypesPolynomialPenalty α (N - 1) +
        equalPriorAverageLogPenalty (N - 1) := by
  classical
  by_cases hprofiles : Nonempty (TensorPowerProfile α N)
  · let g : TensorPowerProfile α N → EReal := fun profile =>
      M.distributionKLMax (profile.empiricalDistribution hN)
    haveI : Nonempty (TensorPowerProfile α N) := hprofiles
    obtain ⟨profile, hprofile⟩ := exists_eq_ciInf_of_finite (f := g)
    have hdual :
        M.distributionKLMax (profile.empiricalDistribution hN) =
          M.finiteTypeKLDualValue N := by
      rw [finiteTypeKLDualValue_eq_iInf_of_pos (M := M) hN]
      exact hprofile
    have hchernoff :
        M.finiteTypeChernoffValue N ≤
          normalizedNegLog (N - 1)
            (ENNReal.ofReal (M.profileProductErrorLowerBound profile)) := by
      unfold finiteTypeChernoffValue
      exact iInf_le _ profile
    calc
      M.finiteTypeChernoffValue N
          ≤ normalizedNegLog (N - 1)
              (ENNReal.ofReal (M.profileProductErrorLowerBound profile)) := hchernoff
      _ ≤ M.distributionKLMax (profile.empiricalDistribution hN) +
            finiteAlphabetMethodOfTypesPolynomialPenalty α (N - 1) +
            equalPriorAverageLogPenalty (N - 1) :=
          normalizedNegLog_profileProductErrorLowerBound_le_distributionKLMax
            (M := M) hN profile
      _ = M.finiteTypeKLDualValue N +
            finiteAlphabetMethodOfTypesPolynomialPenalty α (N - 1) +
            equalPriorAverageLogPenalty (N - 1) := by
          rw [hdual]
  · haveI : IsEmpty (TensorPowerProfile α N) := not_nonempty_iff.mp hprofiles
    unfold finiteTypeKLDualValue finiteTypeChernoffValue
    simp [hN]
    rw [iInf_of_empty, iInf_of_empty]
    simp [finiteAlphabetMethodOfTypesPolynomialPenalty, equalPriorAverageLogPenalty]

/-- The finite-copy profile bridge reduces the classical converse to the
finite-type KL dual limsup.  The two explicit method-of-types penalties vanish:
the alphabet polynomial prefactor contributes `|α| * log(N+1) / N`, and the
equal-prior average contributes `log 2 / N`. -/
theorem finiteTypeChernoffValue_limsup_le_of_finiteTypeKLDualValue_limsup_le
    (M : ClassicalBinaryModel α)
    (hkl :
      Filter.limsup
        (fun n : Nat => M.finiteTypeKLDualValue (n + 1))
        atTop ≤ M.chernoffDistance) :
    Filter.limsup
        (fun n : Nat => M.finiteTypeChernoffValue (n + 1))
        atTop ≤ M.chernoffDistance := by
  classical
  let polynomialPenalty : Nat → EReal := fun n =>
    finiteAlphabetMethodOfTypesPolynomialPenalty α n
  let priorPenalty : Nat → EReal := fun n =>
    equalPriorAverageLogPenalty n
  have hpoint :
      (fun n : Nat => M.finiteTypeChernoffValue (n + 1)) ≤ᶠ[atTop]
        fun n : Nat =>
          M.finiteTypeKLDualValue (n + 1) + polynomialPenalty n + priorPenalty n := by
    exact Filter.Eventually.of_forall fun n => by
      simpa [polynomialPenalty, priorPenalty, Nat.add_sub_cancel] using
        finiteTypeChernoffValue_le_finiteTypeKLDualValue_add_penalties
          (M := M) (N := n + 1) (Nat.succ_pos n)
  have hpolynomial_limsup :
      Filter.limsup polynomialPenalty atTop = (0 : EReal) := by
    exact (finiteAlphabetMethodOfTypesPolynomialPenalty_tendsto_zero
      (α := α)).limsup_eq
  have hprior_limsup :
      Filter.limsup priorPenalty atTop = (0 : EReal) := by
    exact equalPriorAverageLogPenalty_tendsto_zero.limsup_eq
  have hsum1 :
      Filter.limsup
          (fun n : Nat =>
            M.finiteTypeKLDualValue (n + 1) + polynomialPenalty n)
          atTop ≤
        Filter.limsup
            (fun n : Nat => M.finiteTypeKLDualValue (n + 1))
            atTop +
          Filter.limsup polynomialPenalty atTop := by
    simpa only [Pi.add_apply] using
      EReal.limsup_add_le
        (u := fun n : Nat => M.finiteTypeKLDualValue (n + 1))
        (v := polynomialPenalty)
        (f := atTop)
        (Or.inr (by rw [hpolynomial_limsup]; simp))
        (Or.inr (by rw [hpolynomial_limsup]; simp))
  have hsum2 :
      Filter.limsup
          (fun n : Nat =>
            M.finiteTypeKLDualValue (n + 1) + polynomialPenalty n + priorPenalty n)
          atTop ≤
        Filter.limsup
            (fun n : Nat =>
              M.finiteTypeKLDualValue (n + 1) + polynomialPenalty n)
            atTop +
          Filter.limsup priorPenalty atTop := by
    simpa only [Pi.add_apply] using
      EReal.limsup_add_le
        (u := fun n : Nat =>
          M.finiteTypeKLDualValue (n + 1) + polynomialPenalty n)
        (v := priorPenalty)
        (f := atTop)
        (Or.inr (by rw [hprior_limsup]; simp))
        (Or.inr (by rw [hprior_limsup]; simp))
  have hbridge :=
    Filter.limsup_le_limsup hpoint (β := EReal)
      (u := fun n : Nat => M.finiteTypeChernoffValue (n + 1))
      (v := fun n : Nat =>
        M.finiteTypeKLDualValue (n + 1) + polynomialPenalty n + priorPenalty n)
  calc
    Filter.limsup
        (fun n : Nat => M.finiteTypeChernoffValue (n + 1))
        atTop
        ≤
      Filter.limsup
        (fun n : Nat =>
          M.finiteTypeKLDualValue (n + 1) + polynomialPenalty n + priorPenalty n)
        atTop := hbridge
    _ ≤
      Filter.limsup
          (fun n : Nat =>
            M.finiteTypeKLDualValue (n + 1) + polynomialPenalty n)
          atTop +
        Filter.limsup priorPenalty atTop := hsum2
    _ =
      Filter.limsup
          (fun n : Nat =>
            M.finiteTypeKLDualValue (n + 1) + polynomialPenalty n)
          atTop := by
        rw [hprior_limsup]
        simp
    _ ≤
      Filter.limsup
          (fun n : Nat => M.finiteTypeKLDualValue (n + 1))
          atTop +
        Filter.limsup polynomialPenalty atTop := hsum1
    _ =
      Filter.limsup
          (fun n : Nat => M.finiteTypeKLDualValue (n + 1))
          atTop := by
        rw [hpolynomial_limsup]
        simp
    _ ≤ M.chernoffDistance := hkl

/-- The generic method-of-types converse reduces to the finite-type KL dual
limsup bound.  This packages the pointwise type-class lower bound, the
finite-type bridge, and the vanishing polynomial/equal-prior penalties. -/
theorem methodOfTypesChernoffConverse_of_finiteTypeKLDualValue_limsup_le
    (M : ClassicalBinaryModel α)
    (hkl :
      Filter.limsup
        (fun n : Nat => M.finiteTypeKLDualValue (n + 1))
        atTop ≤ M.chernoffDistance) :
    Filter.limsup
        (fun n : Nat =>
          normalizedNegLog n ((M.tensorPower (n + 1)).equalPriorErrorENNReal))
        atTop ≤ M.chernoffDistance := by
  classical
  have hpoint :
      (fun n : Nat =>
          normalizedNegLog n ((M.tensorPower (n + 1)).equalPriorErrorENNReal)) ≤ᶠ[atTop]
        fun n : Nat => M.finiteTypeChernoffValue (n + 1) := by
    exact Filter.Eventually.of_forall fun n => by
      simpa using
        normalizedNegLog_le_finiteTypeChernoffValue
          (M := M) (N := n + 1) (Nat.succ_pos n)
  have hlimsup :=
    Filter.limsup_le_limsup hpoint (β := EReal)
      (u := fun n : Nat =>
        normalizedNegLog n ((M.tensorPower (n + 1)).equalPriorErrorENNReal))
      (v := fun n : Nat => M.finiteTypeChernoffValue (n + 1))
  exact hlimsup.trans
    (finiteTypeChernoffValue_limsup_le_of_finiteTypeKLDualValue_limsup_le
      (M := M) hkl)

/-- Infinite Chernoff distance is the immediate support-boundary case for the
finite-type KL dual limsup. -/
theorem limsup_finiteTypeKLDualValue_le_chernoffDistance_of_eq_top
    (M : ClassicalBinaryModel α)
    (htop : M.chernoffDistance = ⊤) :
    Filter.limsup
        (fun n : Nat => M.finiteTypeKLDualValue (n + 1))
        atTop ≤ M.chernoffDistance := by
  rw [htop]
  exact le_top

omit [DecidableEq α] in
/-- The finite-type KL dual limsup is bounded by the classical Chernoff
distance.  Infinite Chernoff distance is immediate; otherwise the direct
tilted-distribution witness supplies a common-support distribution whose KL
maximum is at most the Chernoff distance. -/
theorem limsup_finiteTypeKLDualValue_le_chernoffDistance
    (M : ClassicalBinaryModel α) [DecidableEq α] :
    Filter.limsup
        (fun n : Nat => M.finiteTypeKLDualValue (n + 1))
        atTop ≤ M.chernoffDistance := by
  classical
  by_cases htop : M.chernoffDistance = ⊤
  · exact limsup_finiteTypeKLDualValue_le_chernoffDistance_of_eq_top
      (M := M) htop
  · obtain ⟨r, hp, hq, hkl⟩ :=
      exists_distribution_klMax_le_chernoffDistance (M := M) htop
    exact
      (limsup_finiteTypeKLDualValue_le_distributionKLMax
        (M := M) (r := r) hp hq).trans hkl

omit [DecidableEq α] in
/-- Generic finite-alphabet classical method-of-types Chernoff converse. -/
theorem methodOfTypesChernoffConverse
    (M : ClassicalBinaryModel α) [DecidableEq α] :
    Filter.limsup
        (fun n : Nat =>
          normalizedNegLog n ((M.tensorPower (n + 1)).equalPriorErrorENNReal))
        atTop ≤ M.chernoffDistance :=
  methodOfTypesChernoffConverse_of_finiteTypeKLDualValue_limsup_le
    (M := M) (limsup_finiteTypeKLDualValue_le_chernoffDistance (M := M))

end ClassicalBinaryModel

end BinaryHypothesisTest

end

end QIT
