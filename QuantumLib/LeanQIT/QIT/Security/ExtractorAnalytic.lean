/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Security.ExtractorAveraging
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite analytic bridge for extractor bounds

This module contains the finite real-analysis inequalities used to turn the
per-seed quadratic estimates in the extractor proof into a squared
trace-distance average bound.
-/

@[expose] public section

open scoped NNReal

namespace QIT.Security

universe u

variable {F : Type u} [Fintype F]

private theorem nnreal_sum_coe_eq_one {τ : F → ℝ≥0} (hτ : (∑ f, τ f) = 1) :
    (∑ f, (τ f : ℝ)) = 1 := by
  exact_mod_cast hτ

/-- Weighted square-root Jensen/Cauchy bridge for a finite probability mass. -/
theorem weighted_sum_sqrt_sq_le_sum (τ : F → ℝ≥0) (hτ : (∑ f, τ f) = 1)
    (q : F → ℝ) (hq : ∀ f, 0 ≤ q f) :
    (∑ f, (τ f : ℝ) * Real.sqrt (q f)) ^ 2 ≤ ∑ f, (τ f : ℝ) * q f := by
  classical
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := Finset.univ)
    (R := ℝ)
    (r := fun f : F => (τ f : ℝ) * Real.sqrt (q f))
    (f := fun f : F => (τ f : ℝ))
    (g := fun f : F => (τ f : ℝ) * q f)
    (fun f _ => NNReal.coe_nonneg (τ f))
    (fun f _ => mul_nonneg (NNReal.coe_nonneg (τ f)) (hq f))
    (fun f _ => by
      rw [mul_pow, Real.sq_sqrt (hq f)]
      let t : ℝ := τ f
      change t ^ 2 * q f ≤ t * (t * q f)
      rw [show t * (t * q f) = t ^ 2 * q f by ring])
  have hτ_real : (∑ f, (τ f : ℝ)) = 1 := nnreal_sum_coe_eq_one hτ
  simpa [hτ_real] using hcs

/--
Scaled quadratic bridge for Tomamichel's extractor proof.

If every per-seed trace-distance-like quantity is bounded by
`sqrt (d * q f)`, then the squared weighted average is bounded by
`d * average(q)`.
-/
theorem weighted_average_sq_le_scaled_quadratic_sum (τ : F → ℝ≥0)
    (hτ : (∑ f, τ f) = 1) (d : ℝ) (δ q : F → ℝ)
    (hd : 0 ≤ d) (hδ : ∀ f, 0 ≤ δ f) (hq : ∀ f, 0 ≤ q f)
    (hbound : ∀ f, δ f ≤ Real.sqrt (d * q f)) :
    (∑ f, (τ f : ℝ) * δ f) ^ 2 ≤ d * ∑ f, (τ f : ℝ) * q f := by
  classical
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := Finset.univ)
    (R := ℝ)
    (r := fun f : F => (τ f : ℝ) * δ f)
    (f := fun f : F => (τ f : ℝ))
    (g := fun f : F => (τ f : ℝ) * (d * q f))
    (fun f _ => NNReal.coe_nonneg (τ f))
    (fun f _ => mul_nonneg (NNReal.coe_nonneg (τ f))
      (mul_nonneg hd (hq f)))
      (fun f _ => by
      have hdq : 0 ≤ d * q f := mul_nonneg hd (hq f)
      have hsq : δ f ^ 2 ≤ (Real.sqrt (d * q f)) ^ 2 :=
        (sq_le_sq₀ (hδ f) (Real.sqrt_nonneg _)).2 (hbound f)
      rw [Real.sq_sqrt hdq] at hsq
      calc
        ((τ f : ℝ) * δ f) ^ 2 = (τ f : ℝ) * ((τ f : ℝ) * δ f ^ 2) := by ring
        _ ≤ (τ f : ℝ) * ((τ f : ℝ) * (d * q f)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsq (NNReal.coe_nonneg (τ f)))
            (NNReal.coe_nonneg (τ f))
        _ = (τ f : ℝ) * ((τ f : ℝ) * (d * q f)) := rfl)
  have hτ_real : (∑ f, (τ f : ℝ)) = 1 := nnreal_sum_coe_eq_one hτ
  calc
    (∑ f, (τ f : ℝ) * δ f) ^ 2 ≤
        (∑ f, (τ f : ℝ)) * ∑ f, (τ f : ℝ) * (d * q f) := hcs
    _ = ∑ f, (τ f : ℝ) * (d * q f) := by simp [hτ_real]
    _ = d * ∑ f, (τ f : ℝ) * q f := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      ring

/--
Extractor trace-distance average bridge.

The names `traceDist` and `quadratic` mirror Tomamichel's proof route: the
first is the per-seed trace-distance term, and the second is the corresponding
quadratic expression obtained from the Holder step.
-/
theorem extractor_traceDistance_average_sq_le (τ : F → ℝ≥0)
    (hτ : (∑ f, τ f) = 1) (d : ℝ) (traceDist quadratic : F → ℝ)
    (hd : 0 ≤ d) (htrace : ∀ f, 0 ≤ traceDist f) (hquad : ∀ f, 0 ≤ quadratic f)
    (hholder : ∀ f, traceDist f ≤ Real.sqrt (d * quadratic f)) :
    (∑ f, (τ f : ℝ) * traceDist f) ^ 2 ≤
      d * ∑ f, (τ f : ℝ) * quadratic f :=
  weighted_average_sq_le_scaled_quadratic_sum τ hτ d traceDist quadratic
    hd htrace hquad hholder

namespace PrivacyAmplification

/-- Public catalog entrypoint for the finite extractor trace-distance averaging bridge. -/
public theorem main (τ : F → ℝ≥0)
    (hτ : (∑ f, τ f) = 1) (d : ℝ) (traceDist quadratic : F → ℝ)
    (hd : 0 ≤ d) (htrace : ∀ f, 0 ≤ traceDist f) (hquad : ∀ f, 0 ≤ quadratic f)
    (hholder : ∀ f, traceDist f ≤ Real.sqrt (d * quadratic f)) :
    (∑ f, (τ f : ℝ) * traceDist f) ^ 2 ≤
      d * ∑ f, (τ f : ℝ) * quadratic f :=
  extractor_traceDistance_average_sq_le τ hτ d traceDist quadratic
    hd htrace hquad hholder

end PrivacyAmplification

end QIT.Security
