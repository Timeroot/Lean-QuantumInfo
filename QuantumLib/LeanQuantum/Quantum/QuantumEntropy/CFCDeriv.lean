/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumMechanics.QuantumChannel
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.RCLike.Basic

/-!
# Differentiation of operator powers in the exponent (CFC)

Infrastructure for the `α → 1` limit of the sandwiched Rényi divergence
(`SandwichedRenyiUmegaki`).

The key obstacle there is differentiating continuous-functional-calculus
expressions, for which Mathlib has no dedicated API. This file provides the one
genuinely needed building block on the operator algebra `L ℋ`:

* `CFC.rpow_eq_normedSpace_exp_smul_log` — for a strictly positive `a : L ℋ`,
  `a ^ s = exp (s • log a)`.
* `CFC.hasDerivAt_rpow_exponent` — **fixed-base exponent derivative**:
  `HasDerivAt (fun s ↦ a ^ s) (a ^ s₀ * log a) s₀`.

The derivative reduces, via the identity above, to Mathlib's
`hasDerivAt_exp_smul_const` (the derivative of `t ↦ exp (t • x)` for fixed `x`):
`s ↦ s • log a` is an affine path into a *commuting* exponent, so no
Daleckii–Krein / Duhamel machinery is needed for this (fixed-base) piece. The
varying-base part of the sandwiched-Rényi limit is handled separately by
continuity (`tendsto_cfc_fun`), not by differentiation.
-/

namespace CFC

open QuantumState
open scoped Topology

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- For a strictly positive operator, the real power equals the Banach-algebra
    exponential of the scaled logarithm: `a ^ s = exp (s • log a)`. -/
lemma rpow_eq_normedSpace_exp_smul_log {a : L ℋ} (ha : IsStrictlyPositive a) (s : ℝ) :
    CFC.rpow a s = NormedSpace.exp (s • CFC.log a) := by
  have hclog : ContinuousOn Real.log (spectrum ℝ a) :=
    fun x hx => (Real.continuousAt_log (ne_of_gt (ha.spectrum_pos hx))).continuousWithinAt
  have hcg : ContinuousOn (fun x : ℝ => s * Real.log x) (spectrum ℝ a) :=
    continuousOn_const.mul hclog
  rw [← CFC.real_exp_eq_normedSpace_exp (a := s • CFC.log a)]
  have h1 : s • CFC.log a = cfc (fun x : ℝ => s * Real.log x) a := by
    rw [CFC.log, ← cfc_smul s Real.log a hclog]; simp only [smul_eq_mul]
  rw [h1, ← cfc_comp Real.exp (fun x : ℝ => s * Real.log x) a (hf := hcg)]
  rw [show CFC.rpow a s = cfc (fun x : ℝ => x ^ s) a from CFC.rpow_eq_cfc_real]
  apply cfc_congr
  intro x hx
  have hxpos : 0 < x := ha.spectrum_pos hx
  simp only [Function.comp_apply]
  rw [Real.rpow_def_of_pos hxpos s, mul_comm]

/-- **Fixed-base exponent derivative.** For a strictly positive `a : L ℋ`, the
    operator power `s ↦ a ^ s` is differentiable in the exponent with
    `HasDerivAt (fun s ↦ a ^ s) (a ^ s₀ * log a) s₀`. -/
lemma hasDerivAt_rpow_exponent {a : L ℋ} (ha : IsStrictlyPositive a) (s₀ : ℝ) :
    HasDerivAt (fun s => CFC.rpow a s) (CFC.rpow a s₀ * CFC.log a) s₀ := by
  simp only [rpow_eq_normedSpace_exp_smul_log ha]
  exact hasDerivAt_exp_smul_const (CFC.log a) s₀

/-- **Chain rule** for the fixed-base power in a differentiable exponent `u`:
    `HasDerivAt (fun α ↦ a ^ u α) (u' • (a ^ u α₀ * log a)) α₀`. -/
lemma hasDerivAt_rpow_exponent_comp {a : L ℋ} (ha : IsStrictlyPositive a)
    {u : ℝ → ℝ} {u' α₀ : ℝ} (hu : HasDerivAt u u' α₀) :
    HasDerivAt (fun α => CFC.rpow a (u α)) (u' • (CFC.rpow a (u α₀) * CFC.log a)) α₀ :=
  (hasDerivAt_rpow_exponent ha (u α₀)).scomp α₀ hu

/-- `s ↦ a ^ s` is continuous (fixed strictly positive base `a`). -/
lemma continuous_rpow_exponent {a : L ℋ} (ha : IsStrictlyPositive a) :
    Continuous (fun s : ℝ => CFC.rpow a s) :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_rpow_exponent ha s).continuousAt

end CFC

/-! ### Pushing a derivative through `X ↦ Re Tr (ρ * X)` -/

namespace QuantumState

universe v

variable {ℋ : Type v} [Qudit ℋ]

/-- The real-linear functional `X ↦ Re Tr (ρ * X)` on `L ℋ`. -/
noncomputable def reTraceMulLeft (ρ : L ℋ) : L ℋ →ₗ[ℝ] ℝ where
  toFun X := (Tr (ρ * X)).re
  map_add' X Y := by rw [mul_add, map_add, Complex.add_re]
  map_smul' r X := by
    change (Tr (ρ * (r • X))).re = r * (Tr (ρ * X)).re
    rw [← Complex.coe_smul, mul_smul_comm, map_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- A derivative of an `L ℋ`-valued path pushes through `X ↦ Re Tr (ρ * X)`
    (a continuous real-linear functional in finite dimension). -/
lemma hasDerivAt_reTrace_mul_left {F : ℝ → L ℋ} {F' : L ℋ} {α₀ : ℝ} (ρ : L ℋ)
    (hF : HasDerivAt F F' α₀) :
    HasDerivAt (fun α => (Tr (ρ * F α)).re) ((Tr (ρ * F')).re) α₀ := by
  have hcomp := (reTraceMulLeft ρ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt α₀ hF
  simpa [reTraceMulLeft, LinearMap.coe_toContinuousLinearMap] using hcomp

/-- The Banach-algebra exponential is continuous on `L ℋ` (via the field `ℝ`). -/
lemma continuous_normedSpace_exp : Continuous (NormedSpace.exp : L ℋ → L ℋ) := by
  rw [← continuousOn_univ, ← Metric.eball_top_eq_univ (0 : L ℋ),
    ← NormedSpace.expSeries_radius_eq_top ℝ (L ℋ)]
  exact NormedSpace.continuousOn_exp

/-- `X ↦ Re Tr X` is continuous on `L ℋ` (finite dimension). -/
lemma continuous_re_trace : Continuous (fun X : L ℋ => (Tr X).re) :=
  Complex.continuous_re.comp (LinearMap.continuous_of_finiteDimensional (Tr : L ℋ →ₗ[ℂ] ℂ))

end QuantumState
