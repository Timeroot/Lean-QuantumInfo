/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The exponential over a real Banach algebra, and the Lie product formula

Mathlib's general API for `NormedSpace.exp` — `exp_add_of_commute`, `exp_nsmul`, `exp_continuous`,
`map_exp` — is stated for algebras over `ℚ`, which for a noncommutative algebra does not follow
from being an algebra over `ℝ`. The primed lemmas below are the versions over `ℝ`, obtained from
the `_of_mem_ball` forms and `expSeries_radius_eq_top`.

The main result is the **Lie product formula** `tendsto_exp_smul_mul_exp_smul_pow`,
`(exp (x/n) * exp (y/n)) ^ n → exp (x + y)`, in the general form
`tendsto_pow_inv_of_hasDerivAt`: a curve `f` with `f 0 = 1` and `f' 0 = z` satisfies
`f (1/n) ^ n → exp z`. The comparison is with the curve `t ↦ exp (t • z)`, which has the same
value and derivative at `0`; the two are compared through the telescoping bound
`norm_pow_succ_sub_pow_succ_le` on `‖a ^ n - b ^ n‖`.

## Main results

* `norm_pow_succ_sub_pow_succ_le` — the telescoping estimate `‖aⁿ⁺¹ - bⁿ⁺¹‖ ≤ (n+1)Kⁿ‖a - b‖`;
* `NormedSpace.exp_add_of_commute'`, `NormedSpace.exp_nsmul'`, `NormedSpace.exp_continuous'`,
  `NormedSpace.map_exp'` — the exponential API over `ℝ`;
* `NormedSpace.tendsto_pow_inv_of_hasDerivAt`, `NormedSpace.tendsto_exp_smul_mul_exp_smul_pow` —
  the Lie product formula.
-/

open Filter Metric NormedSpace Set
open scoped Topology

section Telescope

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- The telescoping estimate `aⁿ⁺¹ - bⁿ⁺¹ = ∑ aᵏ (a - b) bⁿ⁻ᵏ`, in the form used to compare two
curves through `1` with the same derivative. -/
theorem norm_pow_succ_sub_pow_succ_le (a b : 𝔸) {K : ℝ} (ha : ‖a‖ ≤ K) (hb : ‖b‖ ≤ K) (n : ℕ) :
    ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ (n + 1) * K ^ n * ‖a - b‖ := by
  have hK : (0 : ℝ) ≤ K := le_trans (norm_nonneg a) ha
  induction n with
  | zero => simp
  | succ n ih =>
      have key : a ^ (n + 2) - b ^ (n + 2)
          = a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1) := by
        rw [mul_sub, sub_mul, ← pow_succ' a (n + 1), ← pow_succ' b (n + 1)]
        abel
      have hbn : ‖b ^ (n + 1)‖ ≤ K ^ (n + 1) :=
        (norm_pow_le' b n.succ_pos).trans (pow_le_pow_left₀ (norm_nonneg b) hb _)
      calc ‖a ^ (n + 2) - b ^ (n + 2)‖
          = ‖a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1)‖ := by rw [key]
        _ ≤ ‖a * (a ^ (n + 1) - b ^ (n + 1))‖ + ‖(a - b) * b ^ (n + 1)‖ := norm_add_le _ _
        _ ≤ ‖a‖ * ‖a ^ (n + 1) - b ^ (n + 1)‖ + ‖a - b‖ * ‖b ^ (n + 1)‖ :=
            add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ K * ((n + 1) * K ^ n * ‖a - b‖) + ‖a - b‖ * K ^ (n + 1) := by gcongr
        _ = ((n + 1 : ℕ) + 1) * K ^ (n + 1) * ‖a - b‖ := by
          push_cast
          ring

end Telescope

section Trotter

namespace NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `exp (x + y) = exp x * exp y` for commuting elements of a real Banach algebra. -/
theorem exp_add_of_commute' {x y : 𝔸} (h : Commute x y) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball h
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)

/-- `exp (n • x) = exp x ^ n` in a real Banach algebra. -/
theorem exp_nsmul' (n : ℕ) (x : 𝔸) : exp (n • x) = exp x ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, exp_zero]
  | succ n ih => rw [succ_nsmul, pow_succ, exp_add_of_commute' ((Commute.refl x).smul_left n), ih]

/-- The exponential of a real Banach algebra is continuous. -/
theorem exp_continuous' : Continuous (exp : 𝔸 → 𝔸) := by
  have h := continuousOn_exp (𝕂 := ℝ) (𝔸 := 𝔸)
  rw [expSeries_radius_eq_top ℝ 𝔸] at h
  rw [← continuousOn_univ]
  refine h.mono fun x _ => ?_
  simp

/-- Any continuous ring homomorphism between real Banach algebras commutes with `exp`. -/
theorem map_exp' {𝔹 : Type*} [NormedRing 𝔹] [NormedAlgebra ℝ 𝔹] {F : Type*} [FunLike F 𝔸 𝔹]
    [RingHomClass F 𝔸 𝔹] (f : F) (hf : Continuous f) (x : 𝔸) : f (exp x) = exp (f x) :=
  map_exp_of_mem_ball (𝕂 := ℝ) f hf x ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)

/-- The exponential of a finite product of real Banach algebras is computed componentwise. -/
theorem exp_pi_apply {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, NormedRing (A i)]
    [∀ i, NormedAlgebra ℝ (A i)] [∀ i, CompleteSpace (A i)] (a : ∀ i, A i) (i : ι) :
    exp a i = exp (a i) :=
  map_exp' (Pi.evalRingHom A i) (continuous_apply i) a

variable [NormOneClass 𝔸]

/-- **The exponential as a limit of powers.** If a curve `f` in a real Banach algebra satisfies
`f 0 = 1` and `f' 0 = z`, then `f (1/n) ^ n → exp z`: only the first-order behaviour of `f` at `0`
survives in the limit. -/
theorem tendsto_pow_inv_of_hasDerivAt {f : ℝ → 𝔸} {z : 𝔸} (hf0 : f 0 = 1)
    (hf : HasDerivAt f z 0) :
    Tendsto (fun n : ℕ => f ((n : ℝ)⁻¹) ^ n) atTop (𝓝 (exp z)) := by
  set g : ℝ → 𝔸 := fun t => exp (t • z) with hg_def
  have hg : HasDerivAt g z 0 := by
    simpa [hg_def] using hasDerivAt_exp_smul_const z (0 : ℝ)
  have hg0 : g 0 = 1 := by simp [hg_def]
  have hfo : (fun t : ℝ => f t - 1 - t • z) =o[𝓝 0] fun t : ℝ => t := by
    simpa [hf0] using hasDerivAt_iff_isLittleO.mp hf
  have hgo : (fun t : ℝ => g t - 1 - t • z) =o[𝓝 0] fun t : ℝ => t := by
    simpa [hg0] using hasDerivAt_iff_isLittleO.mp hg
  have hD : (fun t : ℝ => f t - g t) =o[𝓝 0] fun t : ℝ => t := by
    simpa using hfo.sub hgo
  set s : ℝ := ‖z‖ + 1 with hs_def
  have hs0 : 0 ≤ s := by positivity
  have hbound : ∀ h : ℝ → 𝔸, (fun t : ℝ => h t - 1 - t • z) =o[𝓝 0] (fun t : ℝ => t) →
      ∀ᶠ t : ℝ in 𝓝 0, ‖h t‖ ≤ 1 + s * |t| := by
    intro h ho
    filter_upwards [ho.def one_pos] with t ht
    have ht' : ‖h t - 1 - t • z‖ ≤ |t| := by simpa [Real.norm_eq_abs] using ht
    have e1 : (h t - 1 - t • z) + (1 + t • z) = h t := by abel
    calc ‖h t‖ = ‖(h t - 1 - t • z) + (1 + t • z)‖ := by rw [e1]
      _ ≤ ‖h t - 1 - t • z‖ + ‖(1 : 𝔸) + t • z‖ := norm_add_le _ _
      _ ≤ |t| + (1 + |t| * ‖z‖) := by
          gcongr
          calc ‖(1 : 𝔸) + t • z‖ ≤ ‖(1 : 𝔸)‖ + ‖t • z‖ := norm_add_le _ _
            _ = 1 + |t| * ‖z‖ := by simp [norm_smul, Real.norm_eq_abs]
      _ = 1 + s * |t| := by
        rw [hs_def]
        ring
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hgpow : ∀ n : ℕ, n ≠ 0 → g ((n : ℝ)⁻¹) ^ n = exp z := by
    intro n hn
    have hn' : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn
    calc g ((n : ℝ)⁻¹) ^ n = exp (n • ((n : ℝ)⁻¹ • z)) := by rw [hg_def, exp_nsmul']
      _ = exp z := by
          rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn', one_smul]
  rw [← tendsto_sub_nhds_zero_iff]
  have hmain : ∀ᶠ n : ℕ in atTop, ‖f ((n : ℝ)⁻¹) ^ n - exp z‖
      ≤ Real.exp s * ((n : ℝ) * ‖f ((n : ℝ)⁻¹) - g ((n : ℝ)⁻¹)‖) := by
    filter_upwards [hinv.eventually (hbound f hfo), hinv.eventually (hbound g hgo),
      eventually_gt_atTop 0] with n hfn hgn hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    set t : ℝ := ((m + 1 : ℕ) : ℝ)⁻¹ with ht_def
    have ht0 : 0 < t := by
      rw [ht_def]
      positivity
    have habs : |t| = t := abs_of_pos ht0
    set K : ℝ := 1 + s * |t| with hK_def
    have hKpow : K ^ m ≤ Real.exp s := by
      have h1 : K ≤ Real.exp (s * t) := by
        rw [hK_def, habs, add_comm]
        exact Real.add_one_le_exp _
      have h4 : (m : ℝ) * (s * t) ≤ s := by
        have hmt : (m : ℝ) * t ≤ 1 := by
          rw [ht_def, mul_inv_le_iff₀ (by positivity)]
          push_cast
          linarith
        calc (m : ℝ) * (s * t) = s * ((m : ℝ) * t) := by ring
          _ ≤ s * 1 := by gcongr
          _ = s := mul_one s
      calc K ^ m ≤ Real.exp (s * t) ^ m := pow_le_pow_left₀ (by positivity) h1 m
        _ = Real.exp ((m : ℝ) * (s * t)) := (Real.exp_nat_mul _ m).symm
        _ ≤ Real.exp s := Real.exp_le_exp.mpr h4
    calc ‖f t ^ (m + 1) - exp z‖ = ‖f t ^ (m + 1) - g t ^ (m + 1)‖ := by
          rw [hgpow (m + 1) (by omega)]
      _ ≤ ((m : ℝ) + 1) * K ^ m * ‖f t - g t‖ := by
          exact_mod_cast norm_pow_succ_sub_pow_succ_le (f t) (g t) hfn hgn m
      _ ≤ ((m : ℝ) + 1) * Real.exp s * ‖f t - g t‖ := by gcongr
      _ = Real.exp s * ((((m + 1 : ℕ) : ℝ)) * ‖f t - g t‖) := by
        push_cast
        ring
  have hzero : Tendsto
      (fun n : ℕ => Real.exp s * ((n : ℝ) * ‖f ((n : ℝ)⁻¹) - g ((n : ℝ)⁻¹)‖)) atTop (𝓝 0) := by
    have h2 : (fun n : ℕ => ‖f ((n : ℝ)⁻¹) - g ((n : ℝ)⁻¹)‖) =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) :=
      hD.norm_left.comp_tendsto hinv
    have h3 := h2.tendsto_div_nhds_zero
    have h4 : Tendsto (fun n : ℕ => (n : ℝ) * ‖f ((n : ℝ)⁻¹) - g ((n : ℝ)⁻¹)‖) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv, inv_inv, mul_comm] using h3
    simpa using h4.const_mul (Real.exp s)
  exact squeeze_zero_norm' hmain hzero

/-- **The Lie product formula**: `(exp (x/n) · exp (y/n))ⁿ → exp (x + y)`, for arbitrary `x` and
`y` in a real Banach algebra. -/
theorem tendsto_exp_smul_mul_exp_smul_pow (x y : 𝔸) :
    Tendsto (fun n : ℕ => (exp ((n : ℝ)⁻¹ • x) * exp ((n : ℝ)⁻¹ • y)) ^ n) atTop
      (𝓝 (exp (x + y))) := by
  have hx : HasDerivAt (fun t : ℝ => exp (t • x)) x 0 := by
    simpa only [zero_smul, exp_zero, one_mul] using hasDerivAt_exp_smul_const x (0 : ℝ)
  have hy : HasDerivAt (fun t : ℝ => exp (t • y)) y 0 := by
    simpa only [zero_smul, exp_zero, one_mul] using hasDerivAt_exp_smul_const y (0 : ℝ)
  have hxy : HasDerivAt (fun t : ℝ => exp (t • x) * exp (t • y)) (x + y) 0 := by
    have := hx.mul hy
    simp only [zero_smul, exp_zero, mul_one, one_mul] at this
    convert this using 1
    abel
  exact tendsto_pow_inv_of_hasDerivAt (by simp) hxy

end NormedSpace

end Trotter
