/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.SandwichedQuasiJensen
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.LinearAlgebra.Lagrange

/-!
# Sandwiched Rényi divergence on non-negative operators (Frank–Lieb extension)

This file extends the sandwiched Rényi divergence `D_α(ρ ‖ σ)` from the
positive-definite case to **non-negative** `ρ, σ ≥ 0`, following the convention
of Frank–Lieb (arXiv:1306.5358v3, §I.A).

## Main definitions

* `suppLE ρ σ` — support condition `ker σ ≤ ker ρ` (equivalent to `supp ρ ⊂ supp σ`).
* `sandwichedRenyiDivNN α ρ σ` — Frank–Lieb extension on `EReal`: equals
  `sandwichedRenyiDiv α ρ σ` when `α < 1` or `suppLE ρ σ`, and `⊤ : EReal`
  when `α > 1` and `¬ suppLE ρ σ`.

## Main theorem

* `sandwichedRenyiDivNN_monotone` — **Theorem 1** (Frank–Lieb): for any CPTP map
  `E : CPTP ℋ ℋ`, any `α ∈ [1/2, 1) ∪ (1, ∞)`, and any non-negative `ρ, σ`,
  `D_α^{NN}(E ρ ‖ E σ) ≤ D_α^{NN}(ρ ‖ σ)`.

## Proof structure

The main theorem reduces via case analysis:

* `α > 1`, `¬ suppLE ρ σ`: RHS is `⊤`, trivial.
* otherwise: real-valued inequality, proven via the faithful-approximation
  `F_λ := (1−λ) E + λ · depolarizing` (faithful for `λ > 0`), the perturbed
  Theorem 1 for faithful channels (`sandwichedRenyiDiv_monotone_nonneg_perturbed`),
  and boundary continuity of `sandwichedRenyiDiv` as `ε → 0+`.
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory TensorProduct
open scoped ComplexOrder NNReal Topology

universe u

set_option linter.style.longLine false

/-! ### Support condition `suppLE` -/

/-- **Support condition**: `ker σ ≤ ker ρ`, equivalent to `supp ρ ⊂ supp σ`. -/
def suppLE {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (ρ σ : L ℋ) : Prop :=
  LinearMap.ker σ ≤ LinearMap.ker ρ

/-- The support condition `suppLE ρ σ` holds trivially when `σ ∈ pdSetLM`. -/
lemma suppLE_of_pdSetLM_right
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (ρ : L ℋ) {σ : L ℋ} (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    suppLE ρ σ := by
  intro x hx
  have hker : LinearMap.ker σ = ⊥ := ker_eq_bot_of_pdSetLM hσ
  rw [hker, Submodule.mem_bot] at hx
  simp [hx]

/-! ### Frank–Lieb explicit formula -/

/-- **Frank–Lieb extended sandwiched Rényi divergence** for non-negative `ρ, σ`.

    For `α > 0`, `α ≠ 1`, the value is `⊤ : EReal` exactly on the region where the
    true divergence is `+∞`, and the real-valued `sandwichedRenyiDiv α ρ σ`
    (coerced to `EReal`) otherwise:

    * `α > 1` and `supp(ρ) ⊄ supp(σ)` (i.e. `¬ suppLE ρ σ`): value `⊤`.
      (`CFC.rpow σ ((1−α)/(2α))` would need the genuine inverse, divergent on `ker σ`.)
    * `α < 1` and `ρ ≠ 0` and `Q_α(ρ‖σ) = 0` (i.e. `ρ ⊥ σ`, orthogonal supports):
      value `⊤`. Here `Real.log 0 = 0` would otherwise give the *wrong* value `0`,
      whereas the true divergence is `+∞` (since `1/(α−1) < 0`).
    * otherwise: value `sandwichedRenyiDiv α ρ σ`.

    For `ρ, σ ∈ pdSetLM` the kernel of `σ` is trivial and `Q_α > 0`, so the formula
    agrees with the standard `sandwichedRenyiDiv α ρ σ` viewed in `EReal`. -/
noncomputable def sandwichedRenyiDivNN
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (α : ℝ) (ρ σ : L ℋ) : EReal :=
  letI : Decidable ((1 < α ∧ ¬ suppLE ρ σ) ∨
      (α < 1 ∧ ρ ≠ 0 ∧ (sandwichedQuasi α ρ σ).re = 0)) := Classical.propDecidable _
  if (1 < α ∧ ¬ suppLE ρ σ) ∨ (α < 1 ∧ ρ ≠ 0 ∧ (sandwichedQuasi α ρ σ).re = 0)
    then (⊤ : EReal)
  else ((sandwichedRenyiDiv α ρ σ : ℝ) : EReal)

/-! ### Auxiliary spectral / order lemmas -/

/-- The completely positive map underlying a `CPTP` preserves `≤` on its domain. -/
lemma map_le_map_of_nonneg
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (F : CompletelyPositiveMap (L ℋ) (L 𝒦))
    {a b : L ℋ} (hab : a ≤ b) :
    F.toLinearMap a ≤ F.toLinearMap b := by
  have h : 0 ≤ b - a := sub_nonneg.mpr hab
  have hF : 0 ≤ F.toLinearMap (b - a) := map_nonneg F h
  rw [LinearMap.map_sub] at hF
  exact sub_nonneg.mp hF

/-- For non-negative `ρ, σ` in finite dimension with `ker σ ≤ ker ρ`, there
    exists `lam > 0` with `ρ ≤ lam • σ`.

    **Proof**: Case split on `σ = 0` (then `ρ = 0` by `suppLE`) vs `σ ≠ 0`.
    For `σ ≠ 0`, use the spectral decomposition of `σ`: let `b` be an orthonormal
    eigenbasis with eigenvalues `eig i ≥ 0`. Let `S = {i | eig i > 0}` (nonempty
    since `σ ≠ 0`) and `s_min = min over S of eig`. By `suppLE`, `ρ` annihilates
    eigenvectors with zero eigenvalue. Then for any `x`, expanding in the eigenbasis,
    `re ⟨x, ρ x⟩ ≤ ‖ρ‖ · ∑_{i ∈ S} |⟨b i, x⟩|² ≤ (‖ρ‖ / s_min) · re ⟨x, σ x⟩`.
    Hence `ρ ≤ (‖ρ‖ / s_min + 1) • σ`.

    **Status**: Fully proven. -/
lemma nonneg_le_smul_of_suppLE
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (h : suppLE ρ σ) :
    ∃ lam > (0 : ℝ), ρ ≤ (lam : ℂ) • σ := by
  by_cases hσ_zero : σ = 0
  · -- `σ = 0`: then `ker σ = ⊤`, by `suppLE` also `ker ρ = ⊤`, so `ρ = 0`. Take `lam = 1`.
    have hker_σ : LinearMap.ker σ = ⊤ := by
      rw [hσ_zero, LinearMap.ker_zero]
    have hker_ρ : LinearMap.ker ρ = ⊤ := eq_top_iff.mpr (hker_σ ▸ h)
    have hρ_zero : ρ = 0 := by
      ext x
      have : x ∈ LinearMap.ker ρ := by rw [hker_ρ]; trivial
      exact this
    exact ⟨1, one_pos, by rw [hρ_zero, hσ_zero]; simp⟩
  · -- `σ ≠ 0`: spectral argument.
    classical
    have hρ_pos : ρ.IsPositive := (LinearMap.nonneg_iff_isPositive ρ).mp hρ
    have hσ_pos : σ.IsPositive := (LinearMap.nonneg_iff_isPositive σ).mp hσ
    have hσ_sym : σ.IsSymmetric := hσ_pos.isSymmetric
    have hρ_sym : ρ.IsSymmetric := hρ_pos.isSymmetric
    set n := Module.finrank ℂ ℋ with hn_def
    have hn : Module.finrank ℂ ℋ = n := rfl
    set b : OrthonormalBasis (Fin n) ℂ ℋ := hσ_sym.eigenvectorBasis hn with hb_def
    set eig : Fin n → ℝ := hσ_sym.eigenvalues hn with heig_def
    have h_eig_nn : ∀ i, (0:ℝ) ≤ eig i := fun i => hσ_pos.nonneg_eigenvalues hn i
    have h_eig_apply : ∀ i, σ (b i) = ((eig i : ℝ) : ℂ) • (b i : ℋ) :=
      hσ_sym.apply_eigenvectorBasis hn
    -- Show ∃ i, 0 < eig i (using σ ≠ 0).
    have h_exists_pos : ∃ i, 0 < eig i := by
      by_contra h_all
      push_neg at h_all
      have h_all_zero : ∀ i, eig i = 0 := fun i => le_antisymm (h_all i) (h_eig_nn i)
      apply hσ_zero
      ext v
      have hv : v = ∑ i, b.repr v i • (b i : ℋ) := (b.sum_repr v).symm
      conv_lhs => rw [hv]
      rw [map_sum]
      refine Finset.sum_eq_zero ?_
      intro i _
      rw [LinearMap.map_smul, h_eig_apply i, h_all_zero i]
      simp
    -- Define `S := {i | 0 < eig i}` and `s_min := min over S`.
    set S : Finset (Fin n) := Finset.univ.filter (fun i => 0 < eig i) with hS_def
    have hS_nonempty : S.Nonempty := by
      obtain ⟨i, hi⟩ := h_exists_pos
      exact ⟨i, by simp [S, hi]⟩
    set s_min : ℝ := S.inf' hS_nonempty eig with hs_min_def
    have hs_min_pos : 0 < s_min := by
      apply (Finset.lt_inf'_iff hS_nonempty).mpr
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    have hs_min_le : ∀ i ∈ S, s_min ≤ eig i := fun i hi => Finset.inf'_le _ hi
    -- Characterize membership in S: `i ∈ S ↔ 0 < eig i ↔ eig i ≠ 0`.
    have h_mem_S : ∀ i, i ∈ S ↔ eig i ≠ 0 := by
      intro i
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hi; exact ne_of_gt hi
      · intro hi
        rcases eq_or_lt_of_le (h_eig_nn i) with h_eq | h_lt
        · exact absurd h_eq.symm hi
        · exact h_lt
    -- For `i ∉ S`, `ρ (b i) = 0` (from `suppLE`).
    have h_ρ_ker : ∀ i, i ∉ S → ρ (b i) = 0 := by
      intro i hi
      have h_eig_i_zero : eig i = 0 := by
        by_contra h_ne
        exact hi ((h_mem_S i).mpr h_ne)
      have h_σ_bi : σ (b i) = 0 := by
        rw [h_eig_apply i, h_eig_i_zero]; simp
      have h_bi_ker : b i ∈ LinearMap.ker σ := h_σ_bi
      exact h h_bi_ker
    -- Set `lam := ‖ρ‖ / s_min + 1`.
    refine ⟨‖ρ‖ / s_min + 1, by positivity, ?_⟩
    -- Show `ρ ≤ lam • σ` via `IsPositive (lam • σ - ρ)`.
    rw [LinearMap.le_def]
    refine ⟨?_, ?_⟩
    · -- Symmetry of `lam • σ - ρ`.
      have hsmul_sym : (((‖ρ‖ / s_min + 1 : ℝ) : ℂ) • σ).IsSymmetric := by
        intro u w
        change inner ℂ (((‖ρ‖ / s_min + 1 : ℝ) : ℂ) • σ u) w =
          inner ℂ u (((‖ρ‖ / s_min + 1 : ℝ) : ℂ) • σ w)
        rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, hσ_sym u w]
      exact hsmul_sym.sub hρ_sym
    · -- `0 ≤ re ⟨(lam • σ - ρ) x, x⟩` for all x.
      intro x
      -- Step 1: `⟨b i, σ x⟩ = eig i * ⟨b i, x⟩`.
      have h_σ_inner : ∀ i, inner ℂ (b i : ℋ) (σ x) =
          ((eig i : ℝ) : ℂ) * inner ℂ (b i : ℋ) x := by
        intro i
        have h1 : inner ℂ (b i : ℋ) (σ x) = inner ℂ (σ (b i)) x := (hσ_sym (b i) x).symm
        rw [h1, h_eig_apply i, inner_smul_left, Complex.conj_ofReal]
      -- Step 2: `re ⟨x, σ x⟩ = ∑ i, eig i * ‖⟨b i, x⟩‖²`.
      have h_re_σ : RCLike.re (inner ℂ x (σ x)) =
          ∑ i, eig i * ‖inner ℂ (b i : ℋ) x‖^2 := by
        rw [← b.sum_inner_mul_inner x (σ x), map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [h_σ_inner i]
        rw [show inner ℂ x (b i : ℋ) =
              (starRingEnd ℂ) (inner ℂ (b i : ℋ) x) from (inner_conj_symm x (b i : ℋ)).symm]
        rw [show (starRingEnd ℂ) (inner ℂ (b i : ℋ) x) *
              (((eig i : ℝ) : ℂ) * inner ℂ (b i : ℋ) x) =
              ((eig i : ℝ) : ℂ) *
                ((starRingEnd ℂ) (inner ℂ (b i : ℋ) x) * inner ℂ (b i : ℋ) x) by ring]
        rw [show (starRingEnd ℂ) (inner ℂ (b i : ℋ) x) * inner ℂ (b i : ℋ) x =
              ((‖inner ℂ (b i : ℋ) x‖^2 : ℝ) : ℂ) by
                rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]]
        rw [show ((eig i : ℝ) : ℂ) * ((‖inner ℂ (b i : ℋ) x‖^2 : ℝ) : ℂ) =
              ((eig i * ‖inner ℂ (b i : ℋ) x‖^2 : ℝ) : ℂ) by push_cast; ring]
        exact Complex.ofReal_re _
      -- Step 3: each term in re ⟨x, σ x⟩ is nonneg, so re ⟨x, σ x⟩ ≥ 0 and
      -- the sum restricted to S is bounded: s_min * (∑ S terms) ≤ re ⟨x, σ x⟩.
      have h_sum_S_le : s_min * (∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2) ≤
          RCLike.re (inner ℂ x (σ x)) := by
        rw [h_re_σ, Finset.mul_sum]
        -- ∑ i ∈ S, s_min * ‖⟨b i, x⟩‖² ≤ ∑ i, eig i * ‖⟨b i, x⟩‖²
        have h_le_full : (∑ i ∈ S, s_min * ‖inner ℂ (b i : ℋ) x‖^2) ≤
            ∑ i ∈ S, eig i * ‖inner ℂ (b i : ℋ) x‖^2 := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_right (hs_min_le i hi) (sq_nonneg _)
        refine h_le_full.trans ?_
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        intros j _ hj
        rw [show eig j = 0 from by
          by_contra h_ne; exact hj ((h_mem_S j).mpr h_ne)]
        simp
      -- Step 4: bound `re ⟨ρ x, x⟩ ≤ ‖ρ‖ * ∑ i ∈ S, ‖⟨b i, x⟩‖²`.
      -- Define xS := ∑ i ∈ S, ⟨b i, x⟩ • b i.
      set xS : ℋ := ∑ i ∈ S, inner ℂ (b i : ℋ) x • (b i : ℋ) with hxS_def
      have hx_decomp : x = ∑ i, inner ℂ (b i : ℋ) x • (b i : ℋ) := by
        conv_lhs => rw [← b.sum_repr x]
        apply Finset.sum_congr rfl
        intro i _
        rw [b.repr_apply_apply]
      -- `ρ x = ρ xS` (using `h_ρ_ker`).
      have h_ρ_x_eq : ρ x = ρ xS := by
        rw [hx_decomp, map_sum, hxS_def, map_sum]
        refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
        intros i _ hi
        rw [LinearMap.map_smul, h_ρ_ker i hi, smul_zero]
      -- `inner ℂ (ρ x) x = inner ℂ (ρ xS) xS`:
      -- use orthogonality `⟨ρ xS, b i⟩ = ⟨xS, ρ b i⟩ = 0` for `i ∉ S`.
      have h_inner_ρ_eq : inner ℂ (ρ x) x = inner ℂ (ρ xS) xS := by
        rw [h_ρ_x_eq]
        -- Use sum_inner_mul_inner to expand both sides in the basis.
        rw [← b.sum_inner_mul_inner (ρ xS) x, ← b.sum_inner_mul_inner (ρ xS) xS]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ S
        · -- For `i ∈ S`: `⟨b i, x⟩ = ⟨b i, xS⟩` by orthonormality.
          have h_bi_xS : inner ℂ (b i : ℋ) xS = inner ℂ (b i : ℋ) x := by
            rw [hxS_def, inner_sum]
            rw [show ∑ j ∈ S, inner ℂ (b i : ℋ) (inner ℂ (b j : ℋ) x • (b j : ℋ)) =
                inner ℂ (b i : ℋ) x from by
              rw [Finset.sum_eq_single i (fun j _ hji => ?_) (fun hi' => absurd hi hi')]
              · rw [inner_smul_right, b.inner_eq_one i]; ring
              · rw [inner_smul_right]
                rw [show inner ℂ (b i : ℋ) (b j : ℋ) = 0 from
                    b.orthonormal.2 (by exact fun h => hji h.symm)]
                ring]
          rw [h_bi_xS]
        · -- For `i ∉ S`: `⟨ρ xS, b i⟩ = ⟨xS, ρ (b i)⟩ = 0`.
          have h_inner_zero : inner ℂ (ρ xS) (b i : ℋ) = 0 := by
            rw [show inner ℂ (ρ xS) (b i : ℋ) = inner ℂ xS (ρ (b i)) from hρ_sym xS (b i)]
            rw [h_ρ_ker i hi]
            simp
          rw [h_inner_zero, zero_mul, zero_mul]
      -- Operator-norm bound: `re ⟨ρ xS, xS⟩ ≤ ‖ρ‖ * ‖xS‖²`.
      have h_op_bound : RCLike.re (inner ℂ (ρ xS) xS) ≤ ‖ρ‖ * ‖xS‖^2 := by
        have h1 : RCLike.re (inner ℂ (ρ xS) xS) ≤ ‖inner ℂ (ρ xS) xS‖ := RCLike.re_le_norm _
        have h2 : ‖inner ℂ (ρ xS) xS‖ ≤ ‖ρ xS‖ * ‖xS‖ := norm_inner_le_norm _ _
        have h3 : ‖ρ xS‖ ≤ ‖ρ‖ * ‖xS‖ := by
          have := ρ.toContinuousLinearMap.le_opNorm xS
          simpa using this
        calc RCLike.re (inner ℂ (ρ xS) xS) ≤ ‖inner ℂ (ρ xS) xS‖ := h1
          _ ≤ ‖ρ xS‖ * ‖xS‖ := h2
          _ ≤ (‖ρ‖ * ‖xS‖) * ‖xS‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
          _ = ‖ρ‖ * ‖xS‖^2 := by ring
      -- ‖xS‖² = ∑ i ∈ S, ‖⟨b i, x⟩‖² (orthonormality + ‖∑ a_i e_i‖² = ∑ ‖a_i‖²).
      have h_xS_norm_sq : ‖xS‖^2 = ∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2 := by
        rw [hxS_def, @norm_sq_eq_re_inner ℂ]
        rw [inner_sum]
        simp_rw [sum_inner, inner_smul_left, inner_smul_right]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [show (∑ j ∈ S, (starRingEnd ℂ) (inner ℂ (b j : ℋ) x) *
                ((inner ℂ (b i : ℋ) x) * inner ℂ (b j : ℋ) (b i : ℋ))) =
                ((‖inner ℂ (b i : ℋ) x‖^2 : ℝ) : ℂ) from ?_]
        · exact Complex.ofReal_re _
        · rw [Finset.sum_eq_single i ?_ ?_]
          · rw [b.inner_eq_one i, mul_one, mul_comm, Complex.mul_conj,
                Complex.normSq_eq_norm_sq]
          · intros j _ hji
            rw [show inner ℂ (b j : ℋ) (b i : ℋ) = 0 from
                  b.orthonormal.2 hji]
            ring
          · intro hiS
            exact absurd hi hiS
      -- Step 5: combine into final inequality `re ⟨(lam • σ - ρ) x, x⟩ ≥ 0`.
      have h_sum_nn : (0 : ℝ) ≤ ∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have h_ρ_bound : RCLike.re (inner ℂ (ρ x) x) ≤
          ‖ρ‖ * ∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2 := by
        rw [h_inner_ρ_eq, ← h_xS_norm_sq]
        exact h_op_bound
      have h_σ_bound : s_min * (∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2) ≤
          RCLike.re (inner ℂ (σ x) x) := by
        rw [show inner ℂ (σ x) x = inner ℂ x (σ x) from hσ_sym x x]
        exact h_sum_S_le
      have h_σ_nn : (0 : ℝ) ≤ RCLike.re (inner ℂ (σ x) x) := hσ_pos.2 x
      have h_ρ_norm_nn : (0 : ℝ) ≤ ‖ρ‖ := norm_nonneg _
      have h_unfold_sub : (((‖ρ‖ / s_min + 1 : ℝ) : ℂ) • σ - ρ) x =
          ((‖ρ‖ / s_min + 1 : ℝ) : ℂ) • σ x - ρ x := by
        rw [LinearMap.sub_apply, LinearMap.smul_apply]
      rw [h_unfold_sub, inner_sub_left, inner_smul_left, Complex.conj_ofReal, map_sub]
      have h_re_eq : RCLike.re (((‖ρ‖ / s_min + 1 : ℝ) : ℂ) * inner ℂ (σ x) x) =
          (‖ρ‖ / s_min + 1) * RCLike.re (inner ℂ (σ x) x) := by
        change ((((‖ρ‖ / s_min + 1 : ℝ) : ℂ) * inner ℂ (σ x) x)).re = _
        rw [Complex.re_ofReal_mul]
        rfl
      rw [h_re_eq]
      -- Goal: 0 ≤ (‖ρ‖/s_min + 1) * re ⟨σ x, x⟩ - re ⟨ρ x, x⟩
      have h_combine : RCLike.re (inner ℂ (ρ x) x) ≤
          (‖ρ‖ / s_min + 1) * RCLike.re (inner ℂ (σ x) x) := by
        have h1 : ‖ρ‖ * (∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2) =
            (‖ρ‖ / s_min) * (s_min * (∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2)) := by
          field_simp
        have h2 : (‖ρ‖ / s_min) * (s_min * (∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2)) ≤
            (‖ρ‖ / s_min) * RCLike.re (inner ℂ (σ x) x) :=
          mul_le_mul_of_nonneg_left h_σ_bound (div_nonneg h_ρ_norm_nn hs_min_pos.le)
        have h3 : (‖ρ‖ / s_min) * RCLike.re (inner ℂ (σ x) x) ≤
            (‖ρ‖ / s_min + 1) * RCLike.re (inner ℂ (σ x) x) := by
          have h_le : ‖ρ‖ / s_min ≤ ‖ρ‖ / s_min + 1 := by linarith
          exact mul_le_mul_of_nonneg_right h_le h_σ_nn
        linarith
      linarith

/-- For a non-negative operator `A`, `re ⟨A x, x⟩ = 0` implies `A x = 0`.

    **Proof**: For positive `A`, take `s := CFC.sqrt A`. Then `s` is symmetric,
    `s * s = A`, and `re ⟨A x, x⟩ = re ⟨s (s x), x⟩ = re ⟨s x, s x⟩ = ‖s x‖² = 0`.
    Hence `s x = 0` and `A x = s (s x) = 0`. -/
lemma nonneg_apply_eq_zero_of_inner_self_eq_zero
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) {x : ℋ}
    (h_inner : RCLike.re (inner ℂ (A x) x) = 0) :
    A x = 0 := by
  set s : L ℋ := CFC.sqrt A with hs_def
  have hs_nn : (0 : L ℋ) ≤ s := CFC.sqrt_nonneg A
  have hs_sq : s * s = A := CFC.sqrt_mul_sqrt_self A
  have hs_pos : s.IsPositive := (LinearMap.nonneg_iff_isPositive s).mp hs_nn
  have hs_sym : s.IsSymmetric := hs_pos.1
  have h_s_apply : s (s x) = A x := by
    have : (s * s) x = A x := by rw [hs_sq]
    exact this
  have h_norm_sq : ‖s x‖ ^ 2 = RCLike.re (inner ℂ (A x) x) := by
    have h1 : inner ℂ (s x) (s x) = inner ℂ (s (s x)) x := (hs_sym (s x) x).symm
    have h2 : inner ℂ (s (s x)) x = inner ℂ (A x) x := by rw [h_s_apply]
    have h3 : (inner ℂ (s x) (s x) : ℂ) = inner ℂ (A x) x := h1.trans h2
    rw [← @inner_self_eq_norm_sq ℂ ℋ, h3]
  rw [h_inner] at h_norm_sq
  have h_sx_norm : ‖s x‖ = 0 := by
    have h_pow : ‖s x‖ ^ 2 = 0 := h_norm_sq
    exact pow_eq_zero_iff two_ne_zero |>.mp h_pow
  have h_sx : s x = 0 := norm_eq_zero.mp h_sx_norm
  rw [← h_s_apply, h_sx, LinearMap.map_zero]

/-- For non-negative `A ≤ B`, `B x = 0 ⇒ A x = 0`.

    **Proof**: From `A ≤ B`, `0 ≤ A`, and `B x = 0`, derive `re ⟨A x, x⟩ = 0`, then
    apply `nonneg_apply_eq_zero_of_inner_self_eq_zero`. -/
lemma nonneg_eq_zero_of_le_of_apply_eq_zero
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A B : L ℋ} (hA : 0 ≤ A) (hAB : A ≤ B) {x : ℋ} (hx : B x = 0) :
    A x = 0 := by
  -- Step 1: `re ⟪A x, x⟫ = 0`.
  have hBA : 0 ≤ B - A := sub_nonneg.mpr hAB
  have hA_pos : A.IsPositive := (LinearMap.nonneg_iff_isPositive A).mp hA
  have hBA_pos : (B - A).IsPositive := (LinearMap.nonneg_iff_isPositive _).mp hBA
  have h_A_nn : (0 : ℝ) ≤ RCLike.re (inner ℂ (A x) x) := hA_pos.2 x
  have h_BA_nn : (0 : ℝ) ≤ RCLike.re (inner ℂ ((B - A) x) x) := hBA_pos.2 x
  have hsub_x : (B - A) x = -A x := by
    change B x - A x = -A x
    rw [hx, zero_sub]
  have h_BA_eq : RCLike.re (inner ℂ ((B - A) x) x) = -RCLike.re (inner ℂ (A x) x) := by
    rw [hsub_x, inner_neg_left, map_neg]
  rw [h_BA_eq] at h_BA_nn
  have h_A_zero : RCLike.re (inner ℂ (A x) x) = 0 := le_antisymm (by linarith) h_A_nn
  -- Step 2: apply the core lemma.
  exact nonneg_apply_eq_zero_of_inner_self_eq_zero hA h_A_zero

/-! ### Support preservation under positive maps -/

/-- Positive maps preserve the support inclusion: if `supp ρ ⊂ supp σ` and `E` is
    a positive linear map (in particular, CPTP), then `supp (E ρ) ⊂ supp (E σ)`. -/
lemma suppLE_of_CPTP
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (h : suppLE ρ σ) :
    suppLE (E.toFun ρ) (E.toFun σ) := by
  intro x hx
  have hEρ_nn : 0 ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
  have hEσ_nn : 0 ≤ E.toFun σ := map_nonneg E.toCompletelyPositiveMap hσ
  obtain ⟨lam, hlam_pos, hlam_le⟩ := nonneg_le_smul_of_suppLE hρ hσ h
  have hEρ_le : E.toFun ρ ≤ (lam : ℂ) • E.toFun σ := by
    have h1 : E.toCompletelyPositiveMap.toLinearMap ρ ≤
        E.toCompletelyPositiveMap.toLinearMap ((lam : ℂ) • σ) :=
      map_le_map_of_nonneg E.toCompletelyPositiveMap hlam_le
    rw [LinearMap.map_smul] at h1
    exact h1
  exact nonneg_eq_zero_of_le_of_apply_eq_zero hEρ_nn hEρ_le (by
    rw [LinearMap.smul_apply, hx, smul_zero])

/-! ### Outer-product helpers and the depolarizing-channel Kraus decomposition -/

/-- Application of an outer product: `(|v⟩⟨u|) x = ⟪u, x⟫ • v`. -/
private lemma outer_product_apply {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]
    (u : ℋ₁) (v : ℋ₂) (x : ℋ₁) :
    outer_product u v x = (inner ℂ u x : ℂ) • v := by
  rw [outer_product_eq_rankOne]
  simp [InnerProductSpace.rankOne_apply]

/-- Adjoint of an outer product swaps its factors: `(|v⟩⟨u|)† = |u⟩⟨v|`. -/
private lemma adjoint_outer_product {ℋ : Type u} [Qudit ℋ] (u v : ℋ) :
    LinearMap.adjoint (outer_product u v) = outer_product v u := by
  apply LinearMap.ext; intro x
  apply ext_inner_right ℂ; intro y
  rw [LinearMap.adjoint_inner_left, outer_product_apply, outer_product_apply,
      inner_smul_right, inner_smul_left, inner_conj_symm]
  ring

/-- **Kraus sum for the (cross-space) depolarizing channel.** With `bp` an orthonormal basis
    of the target `𝒦`, `bq` an orthonormal basis of the source `ℋ`, and a real scalar `c`,
    `∑_{i,j} (c • |bp i⟩⟨bq j|) γ (c • |bp i⟩⟨bq j|)† = (c² · Tr γ) • 1_𝒦`. -/
private lemma depolarizing_kraus_sum
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Qudit 𝒦]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (bp : OrthonormalBasis ι ℂ 𝒦) (bq : OrthonormalBasis κ ℂ ℋ)
    (γ : L ℋ) (c : ℝ) :
    (∑ p : ι × κ, (krausTerm ((c : ℂ) • outer_product (bq p.2) (bp p.1)) : T ℋ 𝒦) γ)
      = ((c : ℂ) ^ 2 * Tr γ) • (1 : L 𝒦) := by
  classical
  -- Per-term: `(c•|eᵢ⟩⟨fⱼ|) γ (c•|eᵢ⟩⟨fⱼ|)† = c² ⟪fⱼ, γ fⱼ⟫ • |eᵢ⟩⟨eᵢ|`.
  have hterm : ∀ (i : ι) (j : κ),
      (krausTerm ((c : ℂ) • outer_product (bq j) (bp i)) : T ℋ 𝒦) γ
        = ((c : ℂ) ^ 2 * inner ℂ (bq j) (γ (bq j))) • outer_product (bp i) (bp i) := by
    intro i j
    have hadj : LinearMap.adjoint ((c : ℂ) • outer_product (bq j) (bp i))
        = (c : ℂ) • outer_product (bp i) (bq j) := by
      apply LinearMap.ext; intro x
      apply ext_inner_right ℂ; intro y
      rw [LinearMap.adjoint_inner_left]
      simp only [LinearMap.smul_apply, outer_product_apply, inner_smul_right,
        inner_smul_left, inner_conj_symm, Complex.conj_ofReal]
      ring
    apply LinearMap.ext; intro x
    have hkt : (krausTerm ((c : ℂ) • outer_product (bq j) (bp i)) : T ℋ 𝒦) γ
        = ((c : ℂ) • outer_product (bq j) (bp i)) ∘ₗ γ ∘ₗ
            ((c : ℂ) • outer_product (bp i) (bq j)) := by
      change ((c : ℂ) • outer_product (bq j) (bp i)) ∘ₗ γ ∘ₗ
          LinearMap.adjoint ((c : ℂ) • outer_product (bq j) (bp i)) = _
      rw [hadj]
    rw [hkt]
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, outer_product_apply,
      smul_smul]
    congr 1
    ring
  -- Reassemble the double sum into `(c² · Tr γ) • 1_𝒦`.
  have hTr : (∑ j, inner ℂ (bq j) (γ (bq j))) = Tr γ :=
    (LinearMap.trace_eq_sum_inner (T := γ) bq).symm
  have hId : (∑ i, outer_product (bp i) (bp i)) = (1 : L 𝒦) := by
    have h := linearMap_eq_sum_outer_product bp (1 : L 𝒦)
    simp only [Module.End.one_apply] at h
    exact h.symm
  simp_rw [hterm]
  rw [Fintype.sum_prod_type]
  have step1 : ∀ i : ι,
      (∑ j, ((c : ℂ) ^ 2 * inner ℂ (bq j) (γ (bq j))) • outer_product (bp i) (bp i))
        = ((c : ℂ) ^ 2 * Tr γ) • outer_product (bp i) (bp i) := by
    intro i
    rw [← Finset.sum_smul, ← Finset.mul_sum, hTr]
  simp_rw [step1]
  rw [← Finset.smul_sum, hId]

/-- The (cross-space) depolarizing channel's underlying linear map `γ ↦ (Tr γ / d_𝒦) • 1_𝒦`. -/
noncomputable def depolLinMap (ℋ 𝒦 : Type u) [Qudit ℋ] [Qudit 𝒦] [Nontrivial 𝒦] :
    L ℋ →ₗ[ℂ] L 𝒦 where
  toFun γ := (Tr γ / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)
  map_add' x y := by
    change (Tr (x + y) / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦) =
         (Tr x / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦) +
         (Tr y / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)
    rw [map_add, add_div, add_smul]
  map_smul' c x := by
    change (Tr (c • x) / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦) =
         (RingHom.id ℂ) c • ((Tr x / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦))
    rw [map_smul, smul_eq_mul, RingHom.id_apply, mul_div_assoc, mul_smul]

/-- **Complete positivity of the (cross-space) depolarizing channel**, via the Kraus
    decomposition `depolLinMap = ∑_{i,j} krausTerm ((√d_𝒦)⁻¹ • |i⟩⟨j|)`. -/
lemma depolLinMap_isCompletelyPositive (ℋ 𝒦 : Type u) [Qudit ℋ] [Qudit 𝒦] [Nontrivial 𝒦] :
    IsCompletelyPositive (depolLinMap ℋ 𝒦) := by
  classical
  set m := Module.finrank ℂ 𝒦 with hm
  set n := Module.finrank ℂ ℋ with hn
  set bp : OrthonormalBasis (Fin m) ℂ 𝒦 := stdOrthonormalBasis ℂ 𝒦 with hbp
  set bq : OrthonormalBasis (Fin n) ℂ ℋ := stdOrthonormalBasis ℂ ℋ with hbq
  set V : Fin m × Fin n → (ℋ →ₗ[ℂ] 𝒦) :=
    fun p => (((Real.sqrt (m : ℝ))⁻¹ : ℝ) : ℂ) • outer_product (bq p.2) (bp p.1) with hV
  have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hc2 : ((((Real.sqrt (m : ℝ))⁻¹ : ℝ)) : ℂ) ^ 2 = ((m : ℂ))⁻¹ := by
    rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt hm_nn, Complex.ofReal_inv,
        Complex.ofReal_natCast]
  have hmap : depolLinMap ℋ 𝒦 = ∑ p : Fin m × Fin n, krausTerm (V p) := by
    apply LinearMap.ext; intro γ
    rw [LinearMap.sum_apply]
    change (Tr γ / (m : ℂ)) • (1 : L 𝒦) =
        ∑ p : Fin m × Fin n, (krausTerm (V p) : T ℋ 𝒦) γ
    rw [depolarizing_kraus_sum bp bq γ ((Real.sqrt (m : ℝ))⁻¹), hc2]
    congr 1
    ring
  rw [hmap]
  exact sum_krausTerm_isCompletelyPositive V

/-! ### Faithful approximating channel `F_λ := (1−λ) E + λ · depolarizing` -/

/-- The (cross-space) depolarizing channel `γ ↦ (Tr γ / d_𝒦) • 1_𝒦`, as a CPTP map `ℋ → 𝒦`.

    Complete positivity comes from the Kraus decomposition
    (`depolLinMap_isCompletelyPositive`); trace preservation is
    `Tr((Tr γ / d_𝒦) • 1_𝒦) = (Tr γ / d_𝒦) · d_𝒦 = Tr γ`. -/
noncomputable def depolarizingChannel
    (ℋ 𝒦 : Type u) [Qudit ℋ] [Qudit 𝒦] [Nontrivial 𝒦] : CPTP ℋ 𝒦 where
  toFun γ := (Tr γ / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)
  map_add' x y := by
    change (Tr (x + y) / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦) =
         (Tr x / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦) +
         (Tr y / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)
    rw [map_add, add_div, add_smul]
  map_smul' c x := by
    change (Tr (c • x) / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦) =
         (RingHom.id ℂ) c • ((Tr x / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦))
    rw [map_smul, smul_eq_mul, RingHom.id_apply, mul_div_assoc, mul_smul]
  map_cstarMatrix_nonneg' k M hM := by
    -- Complete positivity via the Kraus decomposition of the underlying linear map.
    obtain ⟨Ψ, hΨ⟩ := depolLinMap_isCompletelyPositive ℋ 𝒦
    have h := Ψ.map_cstarMatrix_nonneg' k M hM
    rw [hΨ] at h
    exact h
  trace_map ρ := by
    show Tr ρ = Tr ((Tr ρ / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦))
    rw [map_smul, smul_eq_mul, LinearMap.trace_one,
        div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')]

/-- The underlying linear map of the faithful approximation
    `F_λ := (1 − λ) E + λ · depolarizing`. -/
noncomputable def faithfulApproxLin
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) (lam : ℝ) : L ℋ →ₗ[ℂ] L 𝒦 where
  toFun γ := ((1 - lam : ℝ) : ℂ) • E.toFun γ +
             ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun γ
  map_add' x y := by
    have hE : E.toFun (x + y) = E.toFun x + E.toFun y :=
      LinearMap.map_add E.toCompletelyPositiveMap.toLinearMap x y
    have hD : (depolarizingChannel ℋ 𝒦).toFun (x + y) =
              (depolarizingChannel ℋ 𝒦).toFun x + (depolarizingChannel ℋ 𝒦).toFun y :=
      LinearMap.map_add (depolarizingChannel ℋ 𝒦).toCompletelyPositiveMap.toLinearMap x y
    change ((1 - lam : ℝ) : ℂ) • E.toFun (x + y) +
         ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun (x + y) =
         (((1 - lam : ℝ) : ℂ) • E.toFun x +
           ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun x) +
         (((1 - lam : ℝ) : ℂ) • E.toFun y +
           ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun y)
    rw [hE, hD, smul_add, smul_add]
    abel
  map_smul' c x := by
    have hE : E.toFun (c • x) = c • E.toFun x :=
      LinearMap.map_smul E.toCompletelyPositiveMap.toLinearMap c x
    have hD : (depolarizingChannel ℋ 𝒦).toFun (c • x) = c • (depolarizingChannel ℋ 𝒦).toFun x :=
      LinearMap.map_smul (depolarizingChannel ℋ 𝒦).toCompletelyPositiveMap.toLinearMap c x
    change ((1 - lam : ℝ) : ℂ) • E.toFun (c • x) +
         ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun (c • x) =
         (RingHom.id ℂ) c •
           (((1 - lam : ℝ) : ℂ) • E.toFun x +
             ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun x)
    rw [hE, hD, RingHom.id_apply, smul_add]
    simp_rw [smul_smul]
    rw [mul_comm c (((1 - lam : ℝ) : ℂ)), mul_comm c (((lam : ℝ) : ℂ))]

/-- **Complete positivity of the convex combination** `F_λ = (1−λ) E + λ D`
    (`0 ≤ λ ≤ 1`): entrywise, `M.map F_λ = (1−λ) • M.map E + λ • M.map D`, a
    non-negative combination of the non-negative matrices `M.map E`, `M.map D`. -/
lemma faithfulApproxLin_isCompletelyPositive
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    IsCompletelyPositive (faithfulApproxLin E lam) := by
  refine (isCompletelyPositive_iff_cstarMatrix_nonneg _).mpr (fun k M hM => ?_)
  have hE : 0 ≤ M.map E.toLinearMap := E.map_cstarMatrix_nonneg' k M hM
  have hD : 0 ≤ M.map (depolarizingChannel ℋ 𝒦).toLinearMap :=
    (depolarizingChannel ℋ 𝒦).map_cstarMatrix_nonneg' k M hM
  have heq : M.map (faithfulApproxLin E lam)
      = ((1 - lam : ℝ) : ℂ) • M.map E.toLinearMap
        + ((lam : ℝ) : ℂ) • M.map (depolarizingChannel ℋ 𝒦).toLinearMap := by
    ext i j
    simp only [CStarMatrix.map_apply]
    rfl
  -- Non-negative real scalar multiples preserve positivity (via `c•X = star(√c•1)·X·(√c•1)`).
  have hsmul : ∀ (r : ℝ), 0 ≤ r → ∀ (X : CStarMatrix (Fin k) (Fin k) (L 𝒦)), 0 ≤ X →
      0 ≤ ((r : ℝ) : ℂ) • X := by
    intro r hr X hX
    exact smul_nonneg (Complex.zero_le_real.mpr hr) hX
  rw [heq]
  exact add_nonneg (hsmul (1 - lam) (by linarith) _ hE) (hsmul lam hlam0 _ hD)

/-- The faithful approximating channel `F_λ := (1 − λ) E + λ · depolarizing`. -/
noncomputable def faithfulApprox
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) (lam : ℝ) (_hlam0 : 0 ≤ lam) (_hlam1 : lam ≤ 1) : CPTP ℋ 𝒦 where
  toFun γ := ((1 - lam : ℝ) : ℂ) • E.toFun γ +
             ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun γ
  map_add' x y := by
    have hE : E.toFun (x + y) = E.toFun x + E.toFun y :=
      LinearMap.map_add E.toCompletelyPositiveMap.toLinearMap x y
    have hD : (depolarizingChannel ℋ 𝒦).toFun (x + y) =
              (depolarizingChannel ℋ 𝒦).toFun x + (depolarizingChannel ℋ 𝒦).toFun y :=
      LinearMap.map_add (depolarizingChannel ℋ 𝒦).toCompletelyPositiveMap.toLinearMap x y
    change ((1 - lam : ℝ) : ℂ) • E.toFun (x + y) +
         ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun (x + y) =
         (((1 - lam : ℝ) : ℂ) • E.toFun x +
           ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun x) +
         (((1 - lam : ℝ) : ℂ) • E.toFun y +
           ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun y)
    rw [hE, hD, smul_add, smul_add]
    abel
  map_smul' c x := by
    have hE : E.toFun (c • x) = c • E.toFun x :=
      LinearMap.map_smul E.toCompletelyPositiveMap.toLinearMap c x
    have hD : (depolarizingChannel ℋ 𝒦).toFun (c • x) = c • (depolarizingChannel ℋ 𝒦).toFun x :=
      LinearMap.map_smul (depolarizingChannel ℋ 𝒦).toCompletelyPositiveMap.toLinearMap c x
    change ((1 - lam : ℝ) : ℂ) • E.toFun (c • x) +
         ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun (c • x) =
         (RingHom.id ℂ) c •
           (((1 - lam : ℝ) : ℂ) • E.toFun x +
             ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun x)
    rw [hE, hD, RingHom.id_apply, smul_add]
    simp_rw [smul_smul]
    rw [mul_comm c (((1 - lam : ℝ) : ℂ)), mul_comm c (((lam : ℝ) : ℂ))]
  map_cstarMatrix_nonneg' k M hM := by
    -- Complete positivity of the convex combination (`faithfulApproxLin_isCompletelyPositive`).
    obtain ⟨Ψ, hΨ⟩ := faithfulApproxLin_isCompletelyPositive E _hlam0 _hlam1
    have h := Ψ.map_cstarMatrix_nonneg' k M hM
    rw [hΨ] at h
    exact h
  trace_map ρ := by
    show Tr ρ = Tr (((1 - lam : ℝ) : ℂ) • E.toFun ρ +
                    ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun ρ)
    rw [map_add, LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul, smul_eq_mul,
        ← E.trace_map ρ, ← (depolarizingChannel ℋ 𝒦).trace_map ρ]
    push_cast
    ring

/-- For a non-zero non-negative operator, the real part of the trace is strictly positive. -/
lemma trace_re_pos_of_ne_zero
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] {ρ : L ℋ} (hρ : 0 ≤ ρ) (hne : ρ ≠ 0) :
    0 < (Tr ρ).re := by
  have hρ_pos : ρ.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp hρ
  have hρ_sym := hρ_pos.isSymmetric
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  rw [show (Tr ρ).re = ∑ i, hρ_sym.eigenvalues hn i from
        hρ_sym.re_trace_eq_sum_eigenvalues hn]
  have h_eig_nn : ∀ i, 0 ≤ hρ_sym.eigenvalues hn i := fun i => hρ_pos.nonneg_eigenvalues hn i
  rcases eq_or_lt_of_le (Finset.sum_nonneg (fun i _ => h_eig_nn i)) with hsum | hsum
  · exfalso
    apply hne
    have h_all : ∀ i, hρ_sym.eigenvalues hn i = 0 := by
      intro i
      have hle : hρ_sym.eigenvalues hn i ≤ ∑ j, hρ_sym.eigenvalues hn j :=
        Finset.single_le_sum (f := fun j => hρ_sym.eigenvalues hn j)
          (fun j _ => h_eig_nn j) (Finset.mem_univ i)
      linarith [h_eig_nn i, hsum, hle]
    have h_apply : ∀ i, ρ (hρ_sym.eigenvectorBasis hn i) = 0 := by
      intro i
      rw [hρ_sym.apply_eigenvectorBasis hn i, h_all i]; simp
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply]
    conv_lhs => rw [← (hρ_sym.eigenvectorBasis hn).sum_repr x]
    rw [map_sum]
    exact Finset.sum_eq_zero (fun i _ => by rw [LinearMap.map_smul, h_apply i, smul_zero])
  · exact hsum

/-- For `0 < λ ≤ 1`, the approximating channel is faithful (`F_λ 1_ℋ` is positive definite
    in the target `𝒦`). -/
lemma faithfulApprox_one_pdSetLM
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    (faithfulApprox E lam hlam0.le hlam1).toFun (1 : L ℋ) ∈ pdSetLM (ℋ := 𝒦) := by
  -- `F_λ 1_ℋ = (1-λ) E 1 + λ • (Tr 1_ℋ / d_𝒦) • 1_𝒦 = (1-λ) E 1 + (λ·d_ℋ/d_𝒦) • 1_𝒦`.
  have hdℋ_pos : 0 < (Module.finrank ℂ ℋ : ℝ) := by exact_mod_cast Module.finrank_pos
  have hd𝒦_pos : 0 < (Module.finrank ℂ 𝒦 : ℝ) := by exact_mod_cast Module.finrank_pos
  have h_F1 : (faithfulApprox E lam hlam0.le hlam1).toFun (1 : L ℋ) =
      ((1 - lam : ℝ) : ℂ) • E.toFun (1 : L ℋ) +
        ((lam * Module.finrank ℂ ℋ / Module.finrank ℂ 𝒦 : ℝ) : ℂ) • (1 : L 𝒦) := by
    change ((1 - lam : ℝ) : ℂ) • E.toFun (1 : L ℋ) +
         ((lam : ℝ) : ℂ) •
           ((Tr (1 : L ℋ) / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)) = _
    rw [smul_smul, LinearMap.trace_one]
    congr 2
    push_cast
    ring
  rw [h_F1]
  -- `(1-λ) E 1 ≥ 0` (since `1 ≥ 0`, `E` preserves `≥ 0`, `1-λ ≥ 0`).
  have h_E1_nn : (0 : L 𝒦) ≤ E.toFun (1 : L ℋ) :=
    map_nonneg E.toCompletelyPositiveMap zero_le_one
  have h_coef_nn : (0 : ℂ) ≤ ((1 - lam : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr (by linarith)
  have h_first_nn : (0 : L 𝒦) ≤ ((1 - lam : ℝ) : ℂ) • E.toFun (1 : L ℋ) :=
    (LinearMap.nonneg_iff_isPositive _).mpr
      (((LinearMap.nonneg_iff_isPositive _).mp h_E1_nn).smul_of_nonneg h_coef_nn)
  -- `(λ·d_ℋ/d_𝒦) • 1_𝒦 ∈ pdSetLM` (positive scalar).
  have h_second_pd :
      ((lam * Module.finrank ℂ ℋ / Module.finrank ℂ 𝒦 : ℝ) : ℂ) • (1 : L 𝒦) ∈ pdSetLM (ℋ := 𝒦) :=
    pos_smul_one_pdSetLM (by positivity)
  exact pdSetLM_add_nonneg h_first_nn h_second_pd

/-- For `0 < λ ≤ 1` and `ρ ≠ 0` non-negative, `F_λ ρ` is positive definite:
    `F_λ ρ = (1−λ)·Eρ + λ·(Tr ρ / d)·1`, where the second summand is `(positive real)·1 ∈ pdSetLM`
    (since `Tr ρ > 0`) and the first is non-negative. -/
lemma faithfulApprox_pdSetLM
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    {ρ : L ℋ} (hρ : 0 ≤ ρ) (hρ0 : ρ ≠ 0) :
    (faithfulApprox E lam hlam0.le hlam1).toFun ρ ∈ pdSetLM (ℋ := 𝒦) := by
  have hd_pos : 0 < (Module.finrank ℂ 𝒦 : ℝ) := by exact_mod_cast Module.finrank_pos
  have hTrρ_pos : 0 < (Tr ρ).re := trace_re_pos_of_ne_zero hρ hρ0
  -- `Tr ρ` is real (`ρ` non-negative, hence self-adjoint).
  have hρ_pos : ρ.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp hρ
  have hTr_im : (Tr ρ).im = 0 := by
    have h := hρ_pos.trace_nonneg
    rw [Complex.le_def] at h
    exact h.2.symm
  have hTr_real : Tr ρ = ((Tr ρ).re : ℂ) := by
    apply Complex.ext <;> simp [hTr_im]
  have hscalar : ((lam : ℝ) : ℂ) * (Tr ρ / (Module.finrank ℂ 𝒦 : ℂ)) =
      ((lam * (Tr ρ).re / Module.finrank ℂ 𝒦 : ℝ) : ℂ) := by
    set t : ℝ := (Tr ρ).re with ht
    rw [hTr_real]; push_cast; ring
  have h_Fρ : (faithfulApprox E lam hlam0.le hlam1).toFun ρ =
      ((1 - lam : ℝ) : ℂ) • E.toFun ρ +
        ((lam * (Tr ρ).re / Module.finrank ℂ 𝒦 : ℝ) : ℂ) • (1 : L 𝒦) := by
    change ((1 - lam : ℝ) : ℂ) • E.toFun ρ +
         ((lam : ℝ) : ℂ) • ((Tr ρ / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)) = _
    rw [smul_smul, hscalar]
  rw [h_Fρ]
  have hEρ_nn : (0 : L 𝒦) ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
  have h_first_nn : (0 : L 𝒦) ≤ ((1 - lam : ℝ) : ℂ) • E.toFun ρ :=
    (LinearMap.nonneg_iff_isPositive _).mpr
      (((LinearMap.nonneg_iff_isPositive _).mp hEρ_nn).smul_of_nonneg
        (Complex.zero_le_real.mpr (by linarith)))
  have h_second_pd :
      ((lam * (Tr ρ).re / Module.finrank ℂ 𝒦 : ℝ) : ℂ) • (1 : L 𝒦) ∈ pdSetLM (ℋ := 𝒦) :=
    pos_smul_one_pdSetLM (div_pos (mul_pos hlam0 hTrρ_pos) hd_pos)
  exact pdSetLM_add_nonneg h_first_nn h_second_pd

/-- `F_λ X → E X` as `λ → 0+`. -/
lemma faithfulApprox_tendsto
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) (X : L ℋ) :
    Filter.Tendsto
      (fun (lam : {l : ℝ // 0 < l ∧ l ≤ 1}) =>
        (faithfulApprox E lam.val lam.property.1.le lam.property.2).toFun X)
      (Filter.comap (fun lam : {l : ℝ // 0 < l ∧ l ≤ 1} => lam.val)
        (nhdsWithin 0 (Set.Ioi 0))) (nhds (E.toFun X)) := by
  -- Extend to all `lam : ℝ`: `g lam = (1-lam) • E X + lam • c` where `c = (Tr X / d_𝒦) • 1_𝒦`.
  let c : L 𝒦 := (Tr X / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)
  let g : ℝ → L 𝒦 :=
    fun lam => ((1 - lam : ℝ) : ℂ) • E.toFun X + ((lam : ℝ) : ℂ) • c
  -- The defining formula of `F_λ X` matches `g lam.val` definitionally.
  have h_F_eq : ∀ (lam : {l : ℝ // 0 < l ∧ l ≤ 1}),
      (faithfulApprox E lam.val lam.property.1.le lam.property.2).toFun X = g lam.val :=
    fun _ => rfl
  simp_rw [h_F_eq]
  -- `g` is continuous on ℝ.
  have hg_cont : Continuous g := by
    change Continuous (fun lam : ℝ =>
      ((1 - lam : ℝ) : ℂ) • E.toFun X + ((lam : ℝ) : ℂ) • c)
    fun_prop
  -- `g 0 = E.toFun X`.
  have hg_zero : g 0 = E.toFun X := by
    change ((1 - (0 : ℝ) : ℝ) : ℂ) • E.toFun X + (((0 : ℝ)) : ℂ) • c = E.toFun X
    simp
  -- Tendsto in ℝ at 0 (from the right) follows from continuity at 0.
  have h_real : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds (E.toFun X)) := by
    rw [← hg_zero]
    exact (hg_cont.tendsto 0).mono_left nhdsWithin_le_nhds
  -- Transfer along the subtype projection via `comap`.
  exact h_real.comp Filter.tendsto_comap

/-! ### Continuity of `CFC.rpow` and `sandwichedQuasi` on the full non-negative cone

For a **non-negative exponent** `p ≥ 0` the map `x ↦ x^p` is continuous on all of
`ℝ≥0` (no pseudo-inverse discontinuity at `0`), so `A ↦ CFC.rpow A p` is continuous
on the whole non-negative cone `{A | 0 ≤ A}`, not just on the strictly-positive
`pdSetLM`. This is the analytic engine for the `α < 1` boundary continuity, where the
exponents `β = (1−α)/(2α) > 0` and `α > 0` are both non-negative. -/

/-- For a non-negative exponent `p`, `A ↦ CFC.rpow A p` is continuous on the
    non-negative cone `{A | 0 ≤ A}`. -/
private lemma rpow_continuousOn_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] {p : ℝ} (hp : 0 ≤ p) :
    ContinuousOn (fun A : L ℋ => CFC.rpow A p) {A : L ℋ | 0 ≤ A} := by
  have h_nhds : (Set.univ : Set ℝ≥0) ∈ 𝓝ˢ (⋃ A ∈ {A : L ℋ | 0 ≤ A}, spectrum ℝ≥0 A) :=
    Filter.univ_mem
  have h_id_cont : ContinuousOn (fun A : L ℋ => A) {A : L ℋ | 0 ≤ A} := continuousOn_id
  have h_nn : ∀ A ∈ {A : L ℋ | 0 ≤ A}, (0 : L ℋ) ≤ A := fun _ hA => hA
  have h_f_cont : ContinuousOn (fun x : ℝ≥0 => x ^ p) (Set.univ) :=
    NNReal.continuousOn_rpow_const (.inr hp)
  exact h_id_cont.cfc_nnreal_of_mem_nhdsSet (s := Set.univ) (f := (· ^ p))
    h_nhds (ha' := h_nn) (hf := h_f_cont)

/-- For non-negative `ρ, σ`, the conjugate `σ^β ρ σ^β` is non-negative. -/
private lemma rpow_conj_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (β : ℝ) {ρ σ : L ℋ}
    (hρ : 0 ≤ ρ) (_hσ : 0 ≤ σ) :
    (0 : L ℋ) ≤ CFC.rpow σ β * ρ * CFC.rpow σ β :=
  conjugate_nonneg_of_nonneg hρ CFC.rpow_nonneg

/-- Continuity of `(ρ, σ) ↦ σ^β ρ σ^β` on the non-negative cone, for `β ≥ 0`. -/
private lemma rpow_conj_continuousOn_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] {β : ℝ} (hβ : 0 ≤ β) :
    ContinuousOn (fun p : L ℋ × L ℋ => CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β)
      ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) := by
  have h_rpow_snd : ContinuousOn (fun p : L ℋ × L ℋ => CFC.rpow p.2 β)
      ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) :=
    (rpow_continuousOn_nonneg hβ).comp continuousOn_snd
      (fun _ hx => (Set.mem_prod.mp hx).2)
  have h_fst : ContinuousOn (fun p : L ℋ × L ℋ => p.1)
      ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) := continuousOn_fst
  exact (h_rpow_snd.mul h_fst).mul h_rpow_snd

/-- **Joint continuity of `(sandwichedQuasi α · ·).re` on the full non-negative cone**,
    valid for `0 < α ≤ 1` (both exponents `β = (1−α)/(2α) ≥ 0` and `α ≥ 0` are
    non-negative, so no pseudo-inverse discontinuity occurs). This is the `α < 1`
    analogue of `sandwichedQuasi_re_continuousOn_pdSetLM`. -/
lemma sandwichedQuasi_re_continuousOn_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ContinuousOn (Function.uncurry (fun (ρ σ : L ℋ) => (sandwichedQuasi α ρ σ).re))
      ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) := by
  set β : ℝ := (1 - α) / (2 * α) with hβ_def
  have hβ_nn : 0 ≤ β := by
    rw [hβ_def]; apply div_nonneg (by linarith) (by positivity)
  have h_inner_cont :
      ContinuousOn (fun p : L ℋ × L ℋ => CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β)
        ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) :=
    rpow_conj_continuousOn_nonneg hβ_nn
  have h_inner_nn : ∀ p ∈ {A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A},
      (0 : L ℋ) ≤ CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β := by
    rintro ⟨ρ, σ⟩ ⟨hρ, hσ⟩
    exact rpow_conj_nonneg β hρ hσ
  have h_nhds :
      (Set.univ : Set ℝ≥0) ∈
        𝓝ˢ (⋃ p ∈ {A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A},
          spectrum ℝ≥0 (CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β)) :=
    Filter.univ_mem
  have h_f_cont : ContinuousOn (fun x : ℝ≥0 => x ^ α) (Set.univ) :=
    NNReal.continuousOn_rpow_const (.inr hα0.le)
  have h_pow_cont :
      ContinuousOn
        (fun p : L ℋ × L ℋ => CFC.rpow (CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β) α)
        ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) :=
    h_inner_cont.cfc_nnreal_of_mem_nhdsSet (s := Set.univ) (f := (· ^ α))
      h_nhds (ha' := h_inner_nn) (hf := h_f_cont)
  have h_trace_cont : Continuous (fun A : L ℋ => Tr A) :=
    LinearMap.continuous_of_finiteDimensional _
  exact Complex.continuous_re.comp_continuousOn (h_trace_cont.comp_continuousOn h_pow_cont)

/-- For `0 < α ≤ 1`, `Q_α` is continuous along the non-negative perturbation path
    `ε ↦ (ρ + ε•P, σ + ε•P)` (with `P ≥ 0`) as `ε → 0⁺`. -/
private lemma sandwichedQuasi_tendsto_nonneg_lt
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {ρ σ P : L ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hP : 0 ≤ P) :
    Filter.Tendsto
      (fun ε : ℝ => (sandwichedQuasi α (ρ + (ε : ℂ) • P) (σ + (ε : ℂ) • P)).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedQuasi α ρ σ).re) := by
  have hcont := sandwichedQuasi_re_continuousOn_nonneg (ℋ := ℋ) hα0 hα1
  set S : Set (L ℋ × L ℋ) := {A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A} with hS
  set g : ℝ → L ℋ × L ℋ := fun ε => (ρ + (ε : ℂ) • P, σ + (ε : ℂ) • P) with hg_def
  have hg_cont : Continuous g := by fun_prop
  have hg0 : g 0 = (ρ, σ) := by simp [hg_def]
  have hg_tendsto : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin (ρ, σ) S) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · rw [← hg0]; exact (hg_cont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hεpos : (0 : ℝ) < ε := hε
      exact Set.mk_mem_prod
        (add_nonneg hρ (smul_nonneg (Complex.zero_le_real.mpr hεpos.le) hP))
        (add_nonneg hσ (smul_nonneg (Complex.zero_le_real.mpr hεpos.le) hP))
  have hcwa : ContinuousWithinAt
      (Function.uncurry (fun (ρ σ : L ℋ) => (sandwichedQuasi α ρ σ).re)) S (ρ, σ) :=
    hcont (ρ, σ) ⟨hρ, hσ⟩
  have hcomp := (hcwa.tendsto).comp hg_tendsto
  simpa only [Function.comp_def, Function.uncurry, hg_def] using hcomp

/-- **Boundary-continuity of `sandwichedRenyiDiv` for `α < 1`** along a non-negative
    perturbation direction `P`, at a point where `Q_α ≠ 0` and `Tr ρ ≠ 0`. No support
    condition is needed: the exponents are non-negative, so `Q_α` is jointly continuous
    on the whole non-negative cone. -/
private lemma sandwichedRenyiDiv_tendsto_nonneg_lt
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ σ P : L ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hP : 0 ≤ P)
    (hQ : (sandwichedQuasi α ρ σ).re ≠ 0) (hTr : (Tr ρ).re ≠ 0) :
    Filter.Tendsto
      (fun ε : ℝ => sandwichedRenyiDiv α (ρ + (ε : ℂ) • P) (σ + (ε : ℂ) • P))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedRenyiDiv α ρ σ)) := by
  unfold sandwichedRenyiDiv
  have hQc := sandwichedQuasi_tendsto_nonneg_lt hα0 hα1.le hρ hσ hP
  have hTc : Filter.Tendsto (fun ε : ℝ => (Tr (ρ + (ε : ℂ) • P)).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Tr ρ).re) := by
    have hform : ∀ ε : ℝ, (Tr (ρ + (ε : ℂ) • P)).re = (Tr ρ).re + ε * (Tr P).re := by
      intro ε
      rw [map_add, map_smul, smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul]
    simp_rw [hform]
    have h2 : Filter.Tendsto (fun ε : ℝ => (Tr ρ).re + ε * (Tr P).re)
        (nhds 0) (nhds ((Tr ρ).re + 0 * (Tr P).re)) :=
      tendsto_const_nhds.add ((continuous_id.mul continuous_const).tendsto 0)
    simpa using h2.mono_left nhdsWithin_le_nhds
  have hRatio : Filter.Tendsto
      (fun ε : ℝ => (sandwichedQuasi α (ρ + (ε : ℂ) • P) (σ + (ε : ℂ) • P)).re /
        (Tr (ρ + (ε : ℂ) • P)).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((sandwichedQuasi α ρ σ).re / (Tr ρ).re)) :=
    Filter.Tendsto.div hQc hTc hTr
  have h_div_ne : (sandwichedQuasi α ρ σ).re / (Tr ρ).re ≠ 0 := div_ne_zero hQ hTr
  have hLog := (Real.continuousAt_log h_div_ne).tendsto.comp hRatio
  exact hLog.const_mul _

/-- **Joint continuity (within the non-negative cone) of `sandwichedRenyiDiv` for `α < 1`**
    at a point `(ρ₀, σ₀)` with `Q_α ≠ 0` and `Tr ρ₀ ≠ 0`. Used to pass both the
    `λ → 0⁺` (channel) and `ε → 0⁺` (perturbation) limits. -/
private lemma sandwichedRenyiDiv_continuousWithinAt_lt
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ₀ σ₀ : L ℋ}
    (hρ₀ : 0 ≤ ρ₀) (hσ₀ : 0 ≤ σ₀)
    (hQ : (sandwichedQuasi α ρ₀ σ₀).re ≠ 0) (hTr : (Tr ρ₀).re ≠ 0) :
    ContinuousWithinAt (fun p : L ℋ × L ℋ => sandwichedRenyiDiv α p.1 p.2)
      ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) (ρ₀, σ₀) := by
  have hcont := sandwichedQuasi_re_continuousOn_nonneg (ℋ := ℋ) hα0 hα1.le
  have hQc : ContinuousWithinAt (fun p : L ℋ × L ℋ => (sandwichedQuasi α p.1 p.2).re)
      ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) (ρ₀, σ₀) :=
    hcont (ρ₀, σ₀) ⟨hρ₀, hσ₀⟩
  have h_trace_cont : Continuous (fun A : L ℋ => Tr A) :=
    LinearMap.continuous_of_finiteDimensional _
  have hTc : ContinuousWithinAt (fun p : L ℋ × L ℋ => (Tr p.1).re)
      ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) (ρ₀, σ₀) :=
    (Complex.continuous_re.comp (h_trace_cont.comp continuous_fst)).continuousWithinAt
  have hRatio := hQc.div hTc hTr
  have h_div_ne : (sandwichedQuasi α ρ₀ σ₀).re / (Tr ρ₀).re ≠ 0 := div_ne_zero hQ hTr
  have hLog := (Real.continuousAt_log h_div_ne).tendsto.comp hRatio
  exact hLog.const_mul (1 / (α - 1))

/-! ### Boundary continuity of `sandwichedRenyiDiv` along the perturbation path -/

/-! #### Eigenvector formulas for the continuous functional calculus -/

/-- Natural-power eigenvector formula: `A v = c • v ⟹ Aⁿ v = cⁿ • v`. -/
private lemma pow_apply_of_eigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} {v : ℋ} {c : ℂ} (hv : A v = c • v) :
    ∀ n : ℕ, (A ^ n) v = c ^ n • v
  | 0 => by rw [pow_zero, Module.End.one_apply, pow_zero, one_smul]
  | n + 1 => by
    rw [pow_succ, Module.End.mul_apply, hv, LinearMap.map_smul,
        pow_apply_of_eigenvector hv n, smul_smul]
    congr 1
    rw [← pow_succ']

/-- Real-polynomial eigenvector formula: `A v = (c:ℂ) • v ⟹ (aeval A p) v = (p.eval c) • v`. -/
private lemma aeval_apply_of_eigenvector_real
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} {v : ℋ} {c : ℝ} (hv : A v = ((c : ℝ) : ℂ) • v) (p : Polynomial ℝ) :
    (Polynomial.aeval A p) v = ((p.eval c : ℝ) : ℂ) • v := by
  induction p using Polynomial.induction_on with
  | C r =>
    rw [Polynomial.aeval_C, Polynomial.eval_C]
    rw [show ((algebraMap ℝ (L ℋ)) r : L ℋ) = ((r : ℝ) : ℂ) • (1 : L ℋ) from by
      rw [show ((r : ℝ) : ℂ) • (1 : L ℋ) = (algebraMap ℂ (L ℋ)) ((r : ℝ) : ℂ) from
        (Algebra.algebraMap_eq_smul_one ((r : ℝ) : ℂ)).symm]
      rfl]
    rw [LinearMap.smul_apply, Module.End.one_apply]
  | add p q hp hq =>
    rw [map_add, Polynomial.eval_add, LinearMap.add_apply, hp, hq,
        Complex.ofReal_add, add_smul]
  | monomial n r _ =>
    rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        Complex.ofReal_mul, Complex.ofReal_pow]
    rw [show ((algebraMap ℝ (L ℋ)) r : L ℋ) = ((r : ℝ) : ℂ) • (1 : L ℋ) from by
      rw [show ((r : ℝ) : ℂ) • (1 : L ℋ) = (algebraMap ℂ (L ℋ)) ((r : ℝ) : ℂ) from
        (Algebra.algebraMap_eq_smul_one ((r : ℝ) : ℂ)).symm]
      rfl]
    rw [smul_mul_assoc, one_mul, LinearMap.smul_apply,
        pow_apply_of_eigenvector hv (n + 1), smul_smul]

/-- `spectrum ℝ A` is finite for `A : L ℋ` (finite dimension). -/
private lemma spectrum_real_finite {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (A : L ℋ) :
    (spectrum ℝ A).Finite := by
  rw [← spectrum.preimage_algebraMap ℂ]
  exact (Module.End.finite_spectrum A).preimage
    (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

/-- **CFC on an eigenvector (real version).** If `A` is self-adjoint, `A v = μ • v`, and
    `μ ∈ spectrum ℝ A`, then `cfc f A v = f(μ) • v`. Proof by Lagrange interpolation:
    a polynomial `q` agreeing with `f` on the (finite) spectrum gives `cfc f A = aeval A q`,
    and `aeval A q v = q(μ) • v = f(μ) • v`. -/
lemma cfc_real_apply_eigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : IsSelfAdjoint A) (f : ℝ → ℝ)
    {v : ℋ} {μ : ℝ} (hv : A v = (μ : ℂ) • v) (hμ : μ ∈ spectrum ℝ A) :
    cfc f A v = ((f μ : ℝ) : ℂ) • v := by
  classical
  set S : Finset ℝ := (spectrum_real_finite A).toFinset with hS
  set q : Polynomial ℝ := Lagrange.interpolate S id f with hq
  have hInj : Set.InjOn (id : ℝ → ℝ) (S : Set ℝ) := Function.injective_id.injOn
  have hEvalNode : ∀ x ∈ S, q.eval x = f x := by
    intro x hx
    have := Lagrange.eval_interpolate_at_node (r := f) (v := id) hInj hx
    simpa using this
  have hEqOn : (spectrum ℝ A).EqOn f (fun x => q.eval x) := by
    intro x hx
    have hxS : x ∈ S := by rw [hS, Set.Finite.mem_toFinset]; exact hx
    exact (hEvalNode x hxS).symm
  have h1 : cfc f A = cfc (fun x => q.eval x) A := cfc_congr hEqOn
  have h2 : cfc (fun x => q.eval x) A = Polynomial.aeval A q := cfc_polynomial q A
  have hμS : μ ∈ S := by rw [hS, Set.Finite.mem_toFinset]; exact hμ
  rw [h1, h2, aeval_apply_of_eigenvector_real hv q, hEvalNode μ hμS]

/-- `CFC.rpow A y` on an eigenvector. -/
private lemma rpow_apply_eigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) (y : ℝ)
    {v : ℋ} {μ : ℝ} (hv : A v = (μ : ℂ) • v) (hμ : μ ∈ spectrum ℝ A) :
    CFC.rpow A y v = ((μ ^ y : ℝ) : ℂ) • v := by
  have hsa : IsSelfAdjoint A := (LinearMap.nonneg_iff_isPositive A).mp hA |>.isSelfAdjoint
  have heq : CFC.rpow A y = cfc (fun x : ℝ => x ^ y) A := by
    rw [CFC.rpow_eq_pow]; exact CFC.rpow_eq_cfc_real (ha := hA)
  rw [heq]
  exact cfc_real_apply_eigenvector hsa (fun x => x ^ y) hv hμ

/-- A real eigenvalue (with nonzero eigenvector) lies in `spectrum ℝ A`. -/
lemma mem_spectrum_real_of_eigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} {v : ℋ} {μ : ℝ} (hv0 : v ≠ 0) (hv : A v = (μ : ℂ) • v) :
    μ ∈ spectrum ℝ A := by
  have hev : Module.End.HasEigenvalue A (μ : ℂ) := by
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hv0⟩
    rw [Module.End.mem_eigenspace_iff]; exact hv
  have hmem : (μ : ℂ) ∈ spectrum ℂ A := hev.mem_spectrum
  rw [← spectrum.preimage_algebraMap ℂ] at *
  simpa using hmem

/-- `v ↦ outer_product u v` as a bundled (continuous) linear map. -/
private noncomputable def outerL {ℋ : Type u} [Qudit ℋ] (u : ℋ) : ℋ →ₗ[ℂ] L ℋ where
  toFun v := outer_product u v
  map_add' v w := by ext x; simp [outer_product_apply, smul_add]
  map_smul' c v := by
    ext x
    simp only [outer_product_apply, LinearMap.smul_apply, RingHom.id_apply]
    rw [smul_comm]

private lemma continuous_outerL {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (u : ℋ) :
    Continuous (fun v : ℋ => outer_product u v) :=
  (outerL u).continuous_of_finiteDimensional

/-- **Operator convergence under `suppLE` (α > 1).**
    `(σ+εI)^β (ρ+εI) (σ+εI)^β → σ^β ρ σ^β` as `ε → 0⁺`, where `β = (1-α)/(2α) < 0`.
    The pseudo-inverse blow-up of `(σ+εI)^β` on `ker σ` is killed because `ρ` vanishes
    there (`suppLE`); the residual `εI`-contribution on `ker σ` scales as `ε^{1/α} → 0`. -/
private lemma rpow_conj_tendsto_of_suppLE
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα_gt : 1 < α) {ρ σ : L ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : suppLE ρ σ) :
    Filter.Tendsto
      (fun ε : ℝ => CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) ((1-α)/(2*α)) * (ρ + (ε:ℂ)•(1:L ℋ))
        * CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) ((1-α)/(2*α)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (CFC.rpow σ ((1-α)/(2*α)) * ρ * CFC.rpow σ ((1-α)/(2*α)))) := by
  classical
  set β : ℝ := (1-α)/(2*α) with hβ
  have hαpos : 0 < α := by linarith
  have hβneg : β < 0 := by
    rw [hβ]; apply div_neg_of_neg_of_pos (by linarith) (by positivity)
  have h2β : (1:ℝ) + 2*β = 1/α := by rw [hβ]; field_simp; ring
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hσ_pos : σ.IsPositive := (LinearMap.nonneg_iff_isPositive σ).mp hσ
  have hσ_sym : σ.IsSymmetric := hσ_pos.isSymmetric
  have hρ_sym : ρ.IsSymmetric := ((LinearMap.nonneg_iff_isPositive ρ).mp hρ).isSymmetric
  set b := hσ_sym.eigenvectorBasis hn with hb
  set eig := hσ_sym.eigenvalues hn with heig
  have h_eig_nn : ∀ i, 0 ≤ eig i := fun i => hσ_pos.nonneg_eigenvalues hn i
  have h_eig_apply : ∀ i, σ (b i) = ((eig i : ℝ):ℂ) • b i := hσ_sym.apply_eigenvectorBasis hn
  have hb_ne : ∀ i, b i ≠ 0 := fun i => b.orthonormal.ne_zero i
  have h_ker : ∀ k, eig k = 0 → ρ (b k) = 0 := by
    intro k hk
    have hσbk : σ (b k) = 0 := by rw [h_eig_apply k, hk]; simp
    exact hsupp (LinearMap.mem_ker.mpr hσbk)
  have h_supp_zero : ∀ i j, (eig i = 0 ∨ eig j = 0) → inner ℂ (b j) (ρ (b i)) = (0:ℂ) := by
    intro i j hij
    rcases hij with hi | hj
    · rw [h_ker i hi]; simp
    · rw [show inner ℂ (b j) (ρ (b i)) = inner ℂ (ρ (b j)) (b i) from (hρ_sym (b j) (b i)).symm,
          h_ker j hj]; simp
  have hspec0 : ∀ i, eig i ∈ spectrum ℝ σ :=
    fun i => mem_spectrum_real_of_eigenvector (hb_ne i) (h_eig_apply i)
  have hS0b : ∀ i, CFC.rpow σ β (b i) = (((eig i)^β : ℝ):ℂ) • b i :=
    fun i => rpow_apply_eigenvector hσ β (h_eig_apply i) (hspec0 i)
  have hS0rho : ∀ i, CFC.rpow σ β (ρ (b i))
      = ∑ j, ((((eig j)^β : ℝ):ℂ) * inner ℂ (b j) (ρ (b i))) • b j := by
    intro i
    conv_lhs => rw [show ρ (b i) = ∑ j, inner ℂ (b j) (ρ (b i)) • b j from (b.sum_repr' (ρ (b i))).symm]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, hS0b j, smul_smul]
    congr 1; ring
  have hM0 : ∀ i, (CFC.rpow σ β * ρ * CFC.rpow σ β) (b i)
      = ∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (ρ (b i))) • b j := by
    intro i
    rw [Module.End.mul_apply, Module.End.mul_apply, hS0b i, map_smul, map_smul, hS0rho i,
        Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul]
    congr 1
    push_cast; ring
  have hMε : ∀ (ε : ℝ), 0 < ε → ∀ i,
      (CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β * (ρ + (ε:ℂ)•(1:L ℋ)) * CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β) (b i)
      = (∑ j, ((((eig i+ε)^β * (eig j+ε)^β : ℝ):ℂ) * inner ℂ (b j) (ρ (b i))) • b j)
        + (((ε * ((eig i+ε)^β)^2 : ℝ)):ℂ) • b i := by
    intro ε hε i
    have hε1_nn : (0:L ℋ) ≤ (ε:ℂ)•(1:L ℋ) :=
      smul_nonneg (Complex.zero_le_real.mpr hε.le) zero_le_one
    have hσε_nn : (0:L ℋ) ≤ σ + (ε:ℂ)•(1:L ℋ) := add_nonneg hσ hε1_nn
    have hσε_app : ∀ k, (σ + (ε:ℂ)•(1:L ℋ)) (b k) = ((eig k + ε : ℝ):ℂ) • b k := by
      intro k
      rw [LinearMap.add_apply, h_eig_apply k, LinearMap.smul_apply, Module.End.one_apply]
      rw [← add_smul]; push_cast; ring_nf
    have hσε_spec : ∀ k, (eig k + ε) ∈ spectrum ℝ (σ + (ε:ℂ)•(1:L ℋ)) :=
      fun k => mem_spectrum_real_of_eigenvector (hb_ne k) (hσε_app k)
    have hSb : ∀ k, CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β (b k) = (((eig k+ε)^β : ℝ):ℂ) • b k :=
      fun k => rpow_apply_eigenvector hσε_nn β (hσε_app k) (hσε_spec k)
    have hSrho : CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β (ρ (b i))
        = ∑ j, ((((eig j+ε)^β : ℝ):ℂ) * inner ℂ (b j) (ρ (b i))) • b j := by
      conv_lhs => rw [show ρ (b i) = ∑ j, inner ℂ (b j) (ρ (b i)) • b j from (b.sum_repr' (ρ (b i))).symm]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, hSb j, smul_smul]
      congr 1; ring
    rw [Module.End.mul_apply, Module.End.mul_apply, hSb i, map_smul, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul,
        hSrho, hSb i, smul_add, Finset.smul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      rw [smul_smul]
      congr 1
      push_cast; ring
    · rw [smul_smul, smul_smul]
      congr 1
      push_cast; ring
  have hrpow_tendsto : ∀ k, 0 < eig k →
      Filter.Tendsto (fun ε : ℝ => (eig k + ε)^β) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((eig k)^β)) := by
    intro k hk
    have h_add : Filter.Tendsto (fun ε : ℝ => eig k + ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds (eig k)) := by
      have hcont : Continuous (fun ε : ℝ => eig k + ε) := by fun_prop
      have h0 : Filter.Tendsto (fun ε : ℝ => eig k + ε) (nhds 0) (nhds (eig k)) := by
        simpa using hcont.tendsto (0:ℝ)
      exact h0.mono_left nhdsWithin_le_nhds
    exact ((Real.continuousAt_rpow_const (eig k) β (Or.inl (ne_of_gt hk))).tendsto).comp h_add
  have hextra : ∀ i, Filter.Tendsto (fun ε : ℝ => (((ε * ((eig i+ε)^β)^2 : ℝ)) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro i
    have hα_inv_pos : (0:ℝ) < 1/α := one_div_pos.mpr hαpos
    have hg : Filter.Tendsto (fun ε : ℝ => ε ^ (1/α)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hc := (Real.continuousAt_rpow_const 0 (1/α) (Or.inr hα_inv_pos.le)).tendsto
      rw [Real.zero_rpow (ne_of_gt hα_inv_pos)] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    have hreal : Filter.Tendsto (fun ε : ℝ => ε * ((eig i+ε)^β)^2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      apply squeeze_zero' (f := fun ε => ε * ((eig i+ε)^β)^2) (g := fun ε => ε ^ (1/α))
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        exact mul_nonneg hε.le (sq_nonneg _)
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        have hεpos : (0:ℝ) < ε := hε
        have hbase_nn : (0:ℝ) ≤ eig i + ε := add_nonneg (h_eig_nn i) hεpos.le
        have hsq : ((eig i+ε)^β)^2 = (eig i+ε)^(2*β) := by
          rw [← Real.rpow_natCast ((eig i+ε)^β) 2, ← Real.rpow_mul hbase_nn]
          ring_nf
        rw [hsq]
        have hle : (eig i+ε)^(2*β) ≤ ε^(2*β) :=
          Real.rpow_le_rpow_of_nonpos hεpos (by linarith [h_eig_nn i]) (by linarith)
        calc ε * (eig i+ε)^(2*β) ≤ ε * ε^(2*β) :=
              mul_le_mul_of_nonneg_left hle hεpos.le
          _ = ε^(1+2*β) := by rw [Real.rpow_add hεpos, Real.rpow_one]
          _ = ε^(1/α) := by rw [h2β]
      · exact hg
    have hcomp := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp hreal
    simpa only [Function.comp_def, Complex.ofReal_zero] using hcomp
  have key : ∀ i, Filter.Tendsto
      (fun ε : ℝ => (CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β * (ρ + (ε:ℂ)•(1:L ℋ)) * CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β) (b i))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((CFC.rpow σ β * ρ * CFC.rpow σ β) (b i))) := by
    intro i
    rw [hM0 i]
    have hEq : (fun ε : ℝ => (CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β * (ρ + (ε:ℂ)•(1:L ℋ)) * CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β) (b i))
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun ε => (∑ j, ((((eig i+ε)^β * (eig j+ε)^β : ℝ):ℂ) * inner ℂ (b j) (ρ (b i))) • b j)
          + (((ε * ((eig i+ε)^β)^2 : ℝ)):ℂ) • b i) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hMε ε hε i
    refine Filter.Tendsto.congr' hEq.symm ?_
    rw [show (∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (ρ (b i))) • b j)
        = (∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (ρ (b i))) • b j) + (0:ℋ) from
        (add_zero _).symm]
    apply Filter.Tendsto.add
    · apply tendsto_finset_sum
      intro j _
      by_cases hzero : eig i = 0 ∨ eig j = 0
      · have hin0 := h_supp_zero i j hzero
        rw [hin0]
        simp only [mul_zero, zero_smul]
        exact tendsto_const_nhds
      · push_neg at hzero
        obtain ⟨hi, hj⟩ := hzero
        have hi' : 0 < eig i := lt_of_le_of_ne (h_eig_nn i) (Ne.symm hi)
        have hj' : 0 < eig j := lt_of_le_of_ne (h_eig_nn j) (Ne.symm hj)
        have hsc : Filter.Tendsto (fun ε : ℝ => ((((eig i+ε)^β * (eig j+ε)^β : ℝ)):ℂ) * inner ℂ (b j) (ρ (b i)))
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (((((eig i)^β * (eig j)^β : ℝ)):ℂ) * inner ℂ (b j) (ρ (b i)))) := by
          apply Filter.Tendsto.mul_const
          have hr : Filter.Tendsto (fun ε : ℝ => ((eig i+ε)^β * (eig j+ε)^β : ℝ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds ((eig i)^β * (eig j)^β)) :=
            (hrpow_tendsto i hi').mul (hrpow_tendsto j hj')
          exact (Complex.continuous_ofReal.tendsto _).comp hr
        exact hsc.smul_const (b j)
    · rw [show (0:ℋ) = (0:ℂ) • b i from (zero_smul ℂ (b i)).symm]
      exact (hextra i).smul_const (b i)
  have hrecon0 : (CFC.rpow σ β * ρ * CFC.rpow σ β)
      = ∑ i, outer_product (b i) ((CFC.rpow σ β * ρ * CFC.rpow σ β) (b i)) :=
    linearMap_eq_sum_outer_product b _
  have hfun : (fun ε : ℝ => CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β * (ρ + (ε:ℂ)•(1:L ℋ)) * CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β)
      = (fun ε : ℝ => ∑ i, outer_product (b i)
          ((CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β * (ρ + (ε:ℂ)•(1:L ℋ)) * CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β) (b i))) :=
    funext fun ε => linearMap_eq_sum_outer_product b _
  rw [hrecon0, hfun]
  apply tendsto_finset_sum
  intro i _
  exact ((continuous_outerL (b i)).tendsto _).comp (key i)

/-- **Boundary-continuity of `sandwichedQuasi` (α > 1) under `suppLE`.** Under the support
    condition, `Q_α(ρ+εI ‖ σ+εI) → Q_α(ρ ‖ σ)` as `ε → 0⁺`. The pseudo-inverse blow-up of
    `(σ+εI)^β` (β < 0) on `ker σ` is killed by `suppLE` (`rpow_conj_tendsto_of_suppLE`); the
    outer `Tr(·^α)` is continuous on the non-negative cone (`α > 0`). -/
private lemma sandwichedQuasi_tendsto_of_suppLE
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα_gt : 1 < α)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : suppLE ρ σ) :
    Filter.Tendsto
      (fun ε : ℝ => sandwichedQuasi α (ρ + (ε : ℂ) • (1 : L ℋ)) (σ + (ε : ℂ) • (1 : L ℋ)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedQuasi α ρ σ)) := by
  have hαpos : 0 < α := by linarith
  set β : ℝ := (1-α)/(2*α) with hβ
  have hM := rpow_conj_tendsto_of_suppLE hα_gt hρ hσ hsupp
  have hMnn : ∀ A B : L ℋ, 0 ≤ B → (0:L ℋ) ≤ CFC.rpow A β * B * CFC.rpow A β :=
    fun A B hB => conjugate_nonneg_of_nonneg hB CFC.rpow_nonneg
  have hcont : ContinuousWithinAt (fun X : L ℋ => Tr (CFC.rpow X α)) {X : L ℋ | 0 ≤ X}
      (CFC.rpow σ β * ρ * CFC.rpow σ β) := by
    have h1 : ContinuousOn (fun X : L ℋ => CFC.rpow X α) {X : L ℋ | 0 ≤ X} :=
      rpow_continuousOn_nonneg (le_of_lt hαpos)
    have h2 : Continuous (fun A : L ℋ => Tr A) := LinearMap.continuous_of_finiteDimensional _
    exact (h2.comp_continuousOn h1).continuousWithinAt (hMnn σ ρ hρ)
  have hMwithin : Filter.Tendsto
      (fun ε : ℝ => CFC.rpow (σ+(ε:ℂ)•(1:L ℋ)) β * (ρ+(ε:ℂ)•(1:L ℋ)) * CFC.rpow (σ+(ε:ℂ)•(1:L ℋ)) β)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin (CFC.rpow σ β * ρ * CFC.rpow σ β) {X : L ℋ | 0 ≤ X}) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hM, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε1 : (0:L ℋ) ≤ (ε:ℂ)•(1:L ℋ) :=
      smul_nonneg (Complex.zero_le_real.mpr (le_of_lt hε)) zero_le_one
    exact hMnn _ _ (add_nonneg hρ hε1)
  have hcomp := Filter.Tendsto.comp hcont hMwithin
  have heqQ : ∀ ρ' σ' : L ℋ,
      sandwichedQuasi α ρ' σ' = Tr (CFC.rpow (CFC.rpow σ' β * ρ' * CFC.rpow σ' β) α) := by
    intro ρ' σ'; rfl
  simp_rw [heqQ]
  exact hcomp

/-- **Orthogonality core**: for `0 < α` and `ρ, σ ≥ 0`, the (real part of the)
    quasi-entropy vanishes iff the conjugated operator does:
    `Q_α(ρ‖σ).re = 0 ↔ σ^β ρ σ^β = 0` (where `β = (1−α)/(2α)`). The latter is the
    operator form of orthogonality `ρ ⊥ σ`. -/
private lemma sandwichedQuasi_re_eq_zero_iff
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    (sandwichedQuasi α ρ σ).re = 0 ↔
      CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α)) = 0 := by
  set β : ℝ := (1 - α) / (2 * α) with hβ
  set M : L ℋ := CFC.rpow σ β * ρ * CFC.rpow σ β with hM
  have hM_nn : (0 : L ℋ) ≤ M := rpow_conj_nonneg β hρ hσ
  have hMα_nn : (0 : L ℋ) ≤ CFC.rpow M α := CFC.rpow_nonneg
  have hQ_eq : sandwichedQuasi α ρ σ = Tr (CFC.rpow M α) := by
    unfold sandwichedQuasi; rw [← hβ, ← hM]
  rw [hQ_eq]
  constructor
  · intro htr
    have hMα0 : CFC.rpow M α = 0 := by
      by_contra hne
      exact absurd htr (ne_of_gt (trace_re_pos_of_ne_zero hMα_nn hne))
    have hαinv : α * (1 / α) = 1 := by rw [mul_one_div, div_self (ne_of_gt hα0)]
    have hcomp : CFC.rpow (CFC.rpow M α) (1 / α) = M := by
      have key := CFC.rpow_rpow_of_exponent_nonneg M α (1 / α) hα0.le (by positivity) hM_nn
      rw [hαinv, CFC.rpow_one M hM_nn] at key
      exact key
    rw [hMα0, CFC.zero_rpow (one_div_ne_zero (ne_of_gt hα0))] at hcomp
    exact hcomp.symm
  · intro hM0
    rw [hM0, CFC.zero_rpow (ne_of_gt hα0), map_zero, Complex.zero_re]

/-- **Support-overlap ⟹ `Q_α ≠ 0` (α > 1).** Under `suppLE ρ σ` with `ρ ≠ 0`, the
    quasi-entropy is non-zero. Indeed `Q_α.re = 0 ⟺ σ^β ρ σ^β = 0`; expanding in the
    eigenbasis of `σ`, this forces `⟨b_k, ρ b_i⟩ = 0` for all `i, k` (using `suppLE` to
    kill the `ker σ` directions and positivity of `eigᵢ^β` elsewhere), hence `ρ = 0`,
    contradicting `ρ ≠ 0`. -/
private lemma sandwichedQuasi_re_ne_zero_of_suppLE
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα_gt : 1 < α) {ρ σ : L ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : suppLE ρ σ) (hρ0 : ρ ≠ 0) :
    (sandwichedQuasi α ρ σ).re ≠ 0 := by
  intro hzre
  have hαpos : 0 < α := by linarith
  set β : ℝ := (1-α)/(2*α) with hβ
  rw [sandwichedQuasi_re_eq_zero_iff hαpos hρ hσ] at hzre
  apply hρ0
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hσ_pos : σ.IsPositive := (LinearMap.nonneg_iff_isPositive σ).mp hσ
  have hσ_sym : σ.IsSymmetric := hσ_pos.isSymmetric
  have hρ_sym : ρ.IsSymmetric := ((LinearMap.nonneg_iff_isPositive ρ).mp hρ).isSymmetric
  set b := hσ_sym.eigenvectorBasis hn with hb
  set eig := hσ_sym.eigenvalues hn with heig
  have h_eig_nn : ∀ i, 0 ≤ eig i := fun i => hσ_pos.nonneg_eigenvalues hn i
  have h_eig_apply : ∀ i, σ (b i) = ((eig i : ℝ):ℂ) • b i := hσ_sym.apply_eigenvectorBasis hn
  have hb_ne : ∀ i, b i ≠ 0 := fun i => b.orthonormal.ne_zero i
  have h_ker : ∀ k, eig k = 0 → ρ (b k) = 0 :=
    fun k hk => hsupp (LinearMap.mem_ker.mpr (by rw [h_eig_apply k, hk]; simp))
  have h_supp_zero : ∀ i j, (eig i = 0 ∨ eig j = 0) → inner ℂ (b j) (ρ (b i)) = (0:ℂ) := by
    intro i j hij
    rcases hij with hi | hj
    · rw [h_ker i hi]; simp
    · rw [show inner ℂ (b j) (ρ (b i)) = inner ℂ (ρ (b j)) (b i) from (hρ_sym (b j) (b i)).symm,
          h_ker j hj]; simp
  have hspec0 : ∀ i, eig i ∈ spectrum ℝ σ :=
    fun i => mem_spectrum_real_of_eigenvector (hb_ne i) (h_eig_apply i)
  have hS0b : ∀ i, CFC.rpow σ β (b i) = (((eig i)^β : ℝ):ℂ) • b i :=
    fun i => rpow_apply_eigenvector hσ β (h_eig_apply i) (hspec0 i)
  have hSsym : (CFC.rpow σ β).IsSymmetric :=
    ((LinearMap.nonneg_iff_isPositive _).mp CFC.rpow_nonneg).isSymmetric
  have hcoeff : ∀ i k, inner ℂ (b k) ((CFC.rpow σ β * ρ * CFC.rpow σ β) (b i))
      = (((eig i)^β : ℝ):ℂ) * (((eig k)^β : ℝ):ℂ) * inner ℂ (b k) (ρ (b i)) := by
    intro i k
    rw [Module.End.mul_apply, Module.End.mul_apply, hS0b i, map_smul, map_smul, inner_smul_right,
        show inner ℂ (b k) (CFC.rpow σ β (ρ (b i)))
          = inner ℂ (CFC.rpow σ β (b k)) (ρ (b i)) from (hSsym (b k) (ρ (b i))).symm,
        hS0b k, inner_smul_left, Complex.conj_ofReal]
    ring
  have hzero_all : ∀ i k, inner ℂ (b k) (ρ (b i)) = (0:ℂ) := by
    intro i k
    by_cases h : eig i = 0 ∨ eig k = 0
    · exact h_supp_zero i k h
    · push_neg at h
      have hi' : 0 < eig i := lt_of_le_of_ne (h_eig_nn i) (Ne.symm h.1)
      have hk' : 0 < eig k := lt_of_le_of_ne (h_eig_nn k) (Ne.symm h.2)
      have hc := hcoeff i k
      rw [hzre, LinearMap.zero_apply, inner_zero_right] at hc
      have hne : (((eig i)^β : ℝ):ℂ) * (((eig k)^β : ℝ):ℂ) ≠ 0 := by
        rw [← Complex.ofReal_mul]
        exact Complex.ofReal_ne_zero.mpr (ne_of_gt (mul_pos (Real.rpow_pos_of_pos hi' β)
          (Real.rpow_pos_of_pos hk' β)))
      exact (mul_eq_zero.mp hc.symm).resolve_left hne
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.zero_apply]
  conv_lhs => rw [← b.sum_repr' x]
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.map_smul,
      show ρ (b i) = ∑ k, inner ℂ (b k) (ρ (b i)) • b k from (b.sum_repr' (ρ (b i))).symm]
  rw [show (∑ k, inner ℂ (b k) (ρ (b i)) • b k) = 0 from
      Finset.sum_eq_zero fun k _ => by rw [hzero_all i k, zero_smul]]
  rw [smul_zero]

/-- Continuity of `Tr` on perturbed states: `Tr(ρ + εI) → Tr ρ` as `ε → 0+`. -/
private lemma trace_tendsto_perturbed
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (ρ : L ℋ) :
    Filter.Tendsto
      (fun ε : ℝ => (Tr (ρ + (ε : ℂ) • (1 : L ℋ)) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Tr ρ)) := by
  have h_eq : ∀ ε : ℝ,
      (Tr (ρ + (ε : ℂ) • (1 : L ℋ)) : ℂ) =
      Tr ρ + (ε : ℂ) * (Module.finrank ℂ ℋ : ℂ) := by
    intro ε
    rw [map_add, LinearMap.map_smul, LinearMap.trace_one, smul_eq_mul]
  simp_rw [h_eq]
  have h_real : Filter.Tendsto
      (fun ε : ℝ => Tr ρ + (ε : ℂ) * (Module.finrank ℂ ℋ : ℂ))
      (nhds 0) (nhds (Tr ρ + (0 : ℂ) * (Module.finrank ℂ ℋ : ℂ))) := by
    refine Filter.Tendsto.add tendsto_const_nhds ?_
    refine Filter.Tendsto.mul ?_ tendsto_const_nhds
    exact (Complex.continuous_ofReal.tendsto 0)
  simpa using h_real.mono_left nhdsWithin_le_nhds

/-- **Boundary-continuity** of `sandwichedRenyiDiv` for non-negative `ρ, σ` with `suppLE ρ σ`,
    `α > 1`, and `ρ ≠ 0`.

    Derived from `sandwichedQuasi_tendsto_of_suppLE` (continuity of the quasi-relative
    entropy under `suppLE`), continuity of `Tr`, and continuity of `log`. Under `ρ ≠ 0` the
    denominator `(Tr ρ).re > 0` (`trace_re_pos_of_ne_zero`) and, under `suppLE`, the numerator
    `Q_α(ρ‖σ).re ≠ 0` (`sandwichedQuasi_re_ne_zero_of_suppLE`), so the limiting quotient is a
    continuity point of `log`. -/
private lemma sandwichedRenyiDiv_tendsto_of_suppLE
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα_gt : 1 < α)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : suppLE ρ σ) (hρ0 : ρ ≠ 0) :
    Filter.Tendsto
      (fun ε : ℝ => sandwichedRenyiDiv α (ρ + (ε : ℂ) • (1 : L ℋ)) (σ + (ε : ℂ) • (1 : L ℋ)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedRenyiDiv α ρ σ)) := by
  unfold sandwichedRenyiDiv
  have h_tr : (Tr ρ).re ≠ 0 := ne_of_gt (trace_re_pos_of_ne_zero hρ hρ0)
  have h_Q : (sandwichedQuasi α ρ σ).re ≠ 0 :=
    sandwichedQuasi_re_ne_zero_of_suppLE hα_gt hρ hσ hsupp hρ0
  -- (1) `Q_α(ρ+εI ‖ σ+εI) → Q_α(ρ ‖ σ)` as ε → 0+ (deep step under `suppLE`).
  have hQ : Filter.Tendsto
      (fun ε : ℝ =>
        (sandwichedQuasi α (ρ + (ε : ℂ) • (1 : L ℋ))
          (σ + (ε : ℂ) • (1 : L ℋ))).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedQuasi α ρ σ).re) := by
    have hQ_C := sandwichedQuasi_tendsto_of_suppLE hα_gt hρ hσ hsupp
    exact (Complex.continuous_re.tendsto _).comp hQ_C
  -- (2) `Tr(ρ+εI) → Tr ρ` (immediate, linear).
  have hT : Filter.Tendsto
      (fun ε : ℝ => (Tr (ρ + (ε : ℂ) • (1 : L ℋ))).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Tr ρ).re) :=
    (Complex.continuous_re.tendsto _).comp (trace_tendsto_perturbed (ℋ := ℋ) ρ)
  -- (3)+(4) Quotient and `log`: continuous since both limits are nonzero.
  have hLog : Filter.Tendsto
      (fun ε : ℝ =>
        Real.log
          ((sandwichedQuasi α (ρ + (ε : ℂ) • (1 : L ℋ))
              (σ + (ε : ℂ) • (1 : L ℋ))).re /
            (Tr (ρ + (ε : ℂ) • (1 : L ℋ))).re))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.log ((sandwichedQuasi α ρ σ).re / (Tr ρ).re))) := by
    have hRatio : Filter.Tendsto
        (fun ε : ℝ =>
          (sandwichedQuasi α (ρ + (ε : ℂ) • (1 : L ℋ))
              (σ + (ε : ℂ) • (1 : L ℋ))).re /
            (Tr (ρ + (ε : ℂ) • (1 : L ℋ))).re)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((sandwichedQuasi α ρ σ).re / (Tr ρ).re)) :=
      Filter.Tendsto.div hQ hT h_tr
    have h_div_ne : (sandwichedQuasi α ρ σ).re / (Tr ρ).re ≠ 0 :=
      div_ne_zero h_Q h_tr
    exact (Real.continuousAt_log h_div_ne).tendsto.comp hRatio
  exact hLog.const_mul _

/-! ### Helpers for the `α < 1` main-theorem case -/

/-- `sandwichedRenyiDiv α 0 τ = 0`: with `ρ = 0`, `Tr ρ = 0` and `Real.log (· / 0) = 0`. -/
private lemma sandwichedRenyiDiv_zero_left
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (α : ℝ) (τ : L ℋ) :
    sandwichedRenyiDiv α (0 : L ℋ) τ = 0 := by
  unfold sandwichedRenyiDiv
  have h0 : (Tr (0 : L ℋ)).re = 0 := by simp
  rw [h0, div_zero, Real.log_zero, mul_zero]

/-- For positive-definite `ρ, σ` (in `pdSetLM`), the quasi-entropy is non-zero: `σ^β ρ σ^β`
    is a product of units (hence a unit, hence `≠ 0`), so by `sandwichedQuasi_re_eq_zero_iff`
    its `Q_α.re ≠ 0`. -/
lemma sandwichedQuasi_re_ne_zero_of_pdSetLM
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) {ρ σ : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    (sandwichedQuasi α ρ σ).re ≠ 0 := by
  have hrpow_unit : IsUnit (CFC.rpow σ ((1 - α) / (2 * α))) :=
    isUnit_of_pdSetLM (pdSetLM_rpow_ne hσ)
  have hρ_unit : IsUnit ρ := isUnit_of_pdSetLM hρ
  intro hzero
  rw [sandwichedQuasi_re_eq_zero_iff hα0 (nonneg_of_pdSetLM hρ) (nonneg_of_pdSetLM hσ)] at hzero
  exact (((hrpow_unit.mul hρ_unit).mul hrpow_unit).ne_zero) hzero

/-- The real part of the quasi-entropy is non-negative (it is `Tr` of a non-negative operator). -/
private lemma sandwichedQuasi_re_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (α : ℝ) (ρ σ : L ℋ) :
    0 ≤ (sandwichedQuasi α ρ σ).re := by
  have hpos : (0 : L ℋ) ≤ CFC.rpow
      (CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α))) α := CFC.rpow_nonneg
  have h := ((LinearMap.nonneg_iff_isPositive _).mp hpos).trace_nonneg
  rw [Complex.le_def] at h
  exact h.1

/-- **Faithful-approximation DPI** (`α < 1`): for each `λ ∈ (0,1]`, the faithful channel
    `F_λ` satisfies `D_α(F_λρ ‖ F_λσ) ≤ D_α(ρ‖σ)`. Obtained by taking `ε → 0⁺` in the
    perturbed PD inequality (`F_λρ, F_λσ` are positive-definite). -/
private lemma sandwichedRenyiDiv_faithfulApprox_le
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_lt : α < 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0) (hσ0 : σ ≠ 0)
    (hQρσ : (sandwichedQuasi α ρ σ).re ≠ 0)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    sandwichedRenyiDiv α ((faithfulApprox E lam hlam0.le hlam1).toFun ρ)
        ((faithfulApprox E lam hlam0.le hlam1).toFun σ) ≤ sandwichedRenyiDiv α ρ σ := by
  have hα0 : 0 < α := by linarith
  have hTrρ : (Tr ρ).re ≠ 0 := ne_of_gt (trace_re_pos_of_ne_zero hρ hρ0)
  set F := faithfulApprox E lam hlam0.le hlam1 with hF
  have hF1 : F.toFun 1 ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_one_pdSetLM E hlam0 hlam1
  have hFρ_pd : F.toFun ρ ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_pdSetLM E hlam0 hlam1 hρ hρ0
  have hFσ_pd : F.toFun σ ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_pdSetLM E hlam0 hlam1 hσ hσ0
  have hFρ_nn : (0 : L 𝒦) ≤ F.toFun ρ := nonneg_of_pdSetLM hFρ_pd
  have hFσ_nn : (0 : L 𝒦) ≤ F.toFun σ := nonneg_of_pdSetLM hFσ_pd
  have hF1_nn : (0 : L 𝒦) ≤ F.toFun 1 := nonneg_of_pdSetLM hF1
  have hQF : (sandwichedQuasi α (F.toFun ρ) (F.toFun σ)).re ≠ 0 :=
    sandwichedQuasi_re_ne_zero_of_pdSetLM hα0 hFρ_pd hFσ_pd
  have hTrFρ : (Tr (F.toFun ρ)).re ≠ 0 :=
    ne_of_gt (trace_re_pos_of_ne_zero hFρ_nn (isUnit_of_pdSetLM hFρ_pd).ne_zero)
  have h_pert : ∀ ε : ℝ, 0 < ε →
      sandwichedRenyiDiv α (F.toFun ρ + (ε : ℂ) • F.toFun 1) (F.toFun σ + (ε : ℂ) • F.toFun 1)
        ≤ sandwichedRenyiDiv α (ρ + (ε : ℂ) • (1 : L ℋ)) (σ + (ε : ℂ) • (1 : L ℋ)) := by
    intro ε hε
    have hpd := sandwichedRenyiDiv_monotone_nonneg_perturbed F hα_ge (ne_of_lt hα_lt) hρ hσ hF1 hε
    have hsmul := LinearMap.map_smul F.toCompletelyPositiveMap.toLinearMap (ε : ℂ) (1 : L ℋ)
    have eρ : F.toFun (ρ + (ε : ℂ) • (1 : L ℋ)) = F.toFun ρ + (ε : ℂ) • F.toFun (1 : L ℋ) := by
      have h1 := LinearMap.map_add F.toCompletelyPositiveMap.toLinearMap ρ ((ε : ℂ) • (1 : L ℋ))
      rw [hsmul] at h1; exact h1
    have eσ : F.toFun (σ + (ε : ℂ) • (1 : L ℋ)) = F.toFun σ + (ε : ℂ) • F.toFun (1 : L ℋ) := by
      have h1 := LinearMap.map_add F.toCompletelyPositiveMap.toLinearMap σ ((ε : ℂ) • (1 : L ℋ))
      rw [hsmul] at h1; exact h1
    rw [eρ, eσ] at hpd
    exact hpd
  have h_RHS := sandwichedRenyiDiv_tendsto_nonneg_lt hα0 hα_lt hρ hσ zero_le_one hQρσ hTrρ
  have h_LHS := sandwichedRenyiDiv_tendsto_nonneg_lt hα0 hα_lt hFρ_nn hFσ_nn hF1_nn hQF hTrFρ
  haveI : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  exact le_of_tendsto_of_tendsto h_LHS h_RHS
    (Filter.eventually_of_mem self_mem_nhdsWithin h_pert)

/-- **Orthogonality reflection** (`α < 1`): a CPTP map cannot create orthogonality.
    If `ρ ≠ 0` and `Q_α(ρ‖σ) ≠ 0` (i.e. `ρ`, `σ` are not orthogonal), then
    `Q_α(Eρ‖Eσ) ≠ 0`.

    **Proof** (no Stinespring needed): the faithful DPI gives, for each `λ ∈ (0,1]`,
    `D_α(F_λρ ‖ F_λσ) ≤ D_α(ρ‖σ)`; since `α < 1` (so `1/(α−1) < 0`) and `Tr(F_λρ) = Tr ρ`,
    this is equivalent to `Q_α(ρ‖σ) ≤ Q_α(F_λρ ‖ F_λσ)`. As `λ → 0⁺`, `Q_α(F_λρ‖F_λσ) →
    Q_α(Eρ‖Eσ)` by nonneg-cone continuity, so `0 < Q_α(ρ‖σ) ≤ Q_α(Eρ‖Eσ)`. -/
private lemma sandwichedQuasi_re_ne_zero_of_CPTP
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_lt : α < 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0)
    (hQ : (sandwichedQuasi α ρ σ).re ≠ 0) :
    (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re ≠ 0 := by
  have hα0 : 0 < α := by linarith
  have hαm : α - 1 < 0 := by linarith
  have hTrρ_pos : 0 < (Tr ρ).re := trace_re_pos_of_ne_zero hρ hρ0
  have hb_pos : 0 < (sandwichedQuasi α ρ σ).re :=
    lt_of_le_of_ne (sandwichedQuasi_re_nonneg α ρ σ) (Ne.symm hQ)
  have hβne : (1 - α) / (2 * α) ≠ 0 := div_ne_zero (by linarith) (by positivity)
  have hσ0 : σ ≠ 0 := by
    intro h
    apply hQ
    rw [sandwichedQuasi_re_eq_zero_iff hα0 hρ hσ, h, CFC.zero_rpow hβne, zero_mul, mul_zero]
  -- `Q_α(ρ‖σ) ≤ Q_α(F_λρ ‖ F_λσ)` for each `λ`.
  have hQ_ge : ∀ (l : {l : ℝ // 0 < l ∧ l ≤ 1}),
      (sandwichedQuasi α ρ σ).re ≤
        (sandwichedQuasi α ((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun σ)).re := by
    rintro ⟨lam, hlam0, hlam1⟩
    simp only
    set F := faithfulApprox E lam hlam0.le hlam1 with hF
    have hFρ_pd : F.toFun ρ ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_pdSetLM E hlam0 hlam1 hρ hρ0
    have hFσ_pd : F.toFun σ ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_pdSetLM E hlam0 hlam1 hσ hσ0
    have ha_pos : 0 < (sandwichedQuasi α (F.toFun ρ) (F.toFun σ)).re :=
      lt_of_le_of_ne (sandwichedQuasi_re_nonneg _ _ _)
        (Ne.symm (sandwichedQuasi_re_ne_zero_of_pdSetLM hα0 hFρ_pd hFσ_pd))
    have hTrF : (Tr (F.toFun ρ)).re = (Tr ρ).re := by
      rw [← F.trace_map ρ]
    have hD := sandwichedRenyiDiv_faithfulApprox_le E hα_ge hα_lt hρ hσ hρ0 hσ0 hQ hlam0 hlam1
    -- Convert `D_F ≤ D_ρ` to `Q_ρ ≤ Q_F`.
    unfold sandwichedRenyiDiv at hD
    rw [hTrF] at hD
    -- `(1/(α-1)) log (Q_F/t) ≤ (1/(α-1)) log (Q_ρ/t)` with `1/(α-1) < 0` ⟹ flip.
    have hlog : Real.log ((sandwichedQuasi α ρ σ).re / (Tr ρ).re) ≤
        Real.log ((sandwichedQuasi α (F.toFun ρ) (F.toFun σ)).re / (Tr ρ).re) := by
      have hinv_neg : 1 / (α - 1) < 0 := one_div_neg.mpr hαm
      by_contra hcon
      push_neg at hcon
      exact absurd hD (not_le.mpr (by
        apply mul_lt_mul_of_neg_left hcon hinv_neg))
    rw [Real.log_le_log_iff (by positivity) (by positivity),
        div_le_div_iff_of_pos_right hTrρ_pos] at hlog
    exact hlog
  -- `λ → 0⁺`: `Q_α(F_λρ‖F_λσ).re → Q_α(Eρ‖Eσ).re`.
  have hEρ : (0 : L 𝒦) ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
  have hEσ : (0 : L 𝒦) ≤ E.toFun σ := map_nonneg E.toCompletelyPositiveMap hσ
  have hcont := sandwichedQuasi_re_continuousOn_nonneg (ℋ := 𝒦) hα0 hα_lt.le
  have hcwa : ContinuousWithinAt
      (Function.uncurry (fun (ρ σ : L 𝒦) => (sandwichedQuasi α ρ σ).re))
      ({A : L 𝒦 | 0 ≤ A} ×ˢ {A : L 𝒦 | 0 ≤ A}) (E.toFun ρ, E.toFun σ) :=
    hcont (E.toFun ρ, E.toFun σ) ⟨hEρ, hEσ⟩
  have hpair : Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        (((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ),
         ((faithfulApprox E l.val l.property.1.le l.property.2).toFun σ)))
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (nhdsWithin 0 (Set.Ioi 0)))
      (nhdsWithin (E.toFun ρ, E.toFun σ) ({A : L 𝒦 | 0 ≤ A} ×ˢ {A : L 𝒦 | 0 ≤ A})) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(faithfulApprox_tendsto E ρ).prodMk_nhds (faithfulApprox_tendsto E σ), ?_⟩
    filter_upwards with l
    exact Set.mk_mem_prod
      (nonneg_of_pdSetLM (faithfulApprox_pdSetLM E l.property.1 l.property.2 hρ hρ0))
      (nonneg_of_pdSetLM (faithfulApprox_pdSetLM E l.property.1 l.property.2 hσ hσ0))
  have hlim := hcwa.tendsto.comp hpair
  haveI : (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
      (nhdsWithin 0 (Set.Ioi 0))).NeBot := by
    refine Filter.comap_neBot fun t ht => ?_
    obtain ⟨U, hU_open, hU0, hU_sub⟩ := mem_nhdsWithin.mp ht
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp (hU_open.mem_nhds hU0)
    have hx_pos : (0 : ℝ) < min (δ / 2) 1 := lt_min (by positivity) one_pos
    refine ⟨⟨min (δ / 2) 1, hx_pos, min_le_right _ _⟩, ?_⟩
    apply hU_sub
    refine ⟨hball ?_, hx_pos⟩
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx_pos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hle : (sandwichedQuasi α ρ σ).re ≤ (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hQ_ge)
  exact ne_of_gt (lt_of_lt_of_le hb_pos hle)

/-! ### Real-valued monotonicity (used in the main theorem) -/

/-- `Q_α` continuity along a pd perturbation path `ε ↦ (ρ+εP, σ+εP)` (all pd). -/
private lemma sandwichedQuasi_tendsto_pd
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (_hα0 : 0 < α) {ρ σ P : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) (hP : P ∈ pdSetLM (ℋ := ℋ)) :
    Filter.Tendsto
      (fun ε : ℝ => (sandwichedQuasi α (ρ + (ε : ℂ) • P) (σ + (ε : ℂ) • P)).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedQuasi α ρ σ).re) := by
  have hcont := sandwichedQuasi_re_continuousOn_pdSetLM (ℋ_aux := ℋ) α
  set S : Set (L ℋ × L ℋ) := pdSetLM (ℋ := ℋ) ×ˢ pdSetLM (ℋ := ℋ) with hS
  set g : ℝ → L ℋ × L ℋ := fun ε => (ρ + (ε : ℂ) • P, σ + (ε : ℂ) • P) with hg_def
  have hg_cont : Continuous g := by fun_prop
  have hg0 : g 0 = (ρ, σ) := by simp [hg_def]
  have hg_tendsto : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin (ρ, σ) S) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · rw [← hg0]; exact (hg_cont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hεP : (ε : ℂ) • P ∈ pdSetLM (ℋ := ℋ) := pdSetLM_pos_smul hP hε
      refine Set.mk_mem_prod ?_ ?_
      · rw [add_comm]; exact pdSetLM_add_nonneg (nonneg_of_pdSetLM hεP) hρ
      · rw [add_comm]; exact pdSetLM_add_nonneg (nonneg_of_pdSetLM hεP) hσ
  have hcwa : ContinuousWithinAt
      (Function.uncurry (fun (ρ σ : L ℋ) => (sandwichedQuasi α ρ σ).re)) S (ρ, σ) :=
    hcont (ρ, σ) ⟨hρ, hσ⟩
  have hcomp := (hcwa.tendsto).comp hg_tendsto
  simpa only [Function.comp_def, Function.uncurry, hg_def] using hcomp

/-- `D_α` continuity along a pd perturbation path. -/
private lemma sandwichedRenyiDiv_tendsto_pd
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) {ρ σ P : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) (hP : P ∈ pdSetLM (ℋ := ℋ)) :
    Filter.Tendsto
      (fun ε : ℝ => sandwichedRenyiDiv α (ρ + (ε : ℂ) • P) (σ + (ε : ℂ) • P))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedRenyiDiv α ρ σ)) := by
  unfold sandwichedRenyiDiv
  have hQc := sandwichedQuasi_tendsto_pd hα0 hρ hσ hP
  have hTr0 : (Tr ρ).re ≠ 0 :=
    ne_of_gt (trace_re_pos_of_ne_zero (nonneg_of_pdSetLM hρ) (isUnit_of_pdSetLM hρ).ne_zero)
  have hQ0 : (sandwichedQuasi α ρ σ).re ≠ 0 := sandwichedQuasi_re_ne_zero_of_pdSetLM hα0 hρ hσ
  have hTc : Filter.Tendsto (fun ε : ℝ => (Tr (ρ + (ε : ℂ) • P)).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Tr ρ).re) := by
    have hform : ∀ ε : ℝ, (Tr (ρ + (ε : ℂ) • P)).re = (Tr ρ).re + ε * (Tr P).re := by
      intro ε
      rw [map_add, map_smul, smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul]
    simp_rw [hform]
    have h2 : Filter.Tendsto (fun ε : ℝ => (Tr ρ).re + ε * (Tr P).re)
        (nhds 0) (nhds ((Tr ρ).re + 0 * (Tr P).re)) :=
      tendsto_const_nhds.add ((continuous_id.mul continuous_const).tendsto 0)
    simpa using h2.mono_left nhdsWithin_le_nhds
  have hRatio : Filter.Tendsto
      (fun ε : ℝ => (sandwichedQuasi α (ρ + (ε : ℂ) • P) (σ + (ε : ℂ) • P)).re /
        (Tr (ρ + (ε : ℂ) • P)).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((sandwichedQuasi α ρ σ).re / (Tr ρ).re)) :=
    Filter.Tendsto.div hQc hTc hTr0
  have hLog := (Real.continuousAt_log (div_ne_zero hQ0 hTr0)).tendsto.comp hRatio
  exact hLog.const_mul _

/-- **Faithful-approximation DPI** (`α > 1`): for each `λ ∈ (0,1]`, `D_α(F_λρ ‖ F_λσ) ≤
    D_α(ρ‖σ)`. Take `ε → 0⁺` in the perturbed PD inequality: the LHS limit at the PD pair
    `(F_λρ, F_λσ)` uses PD-continuity, the RHS limit uses `suppLE`-boundary continuity. -/
private lemma sandwichedRenyiDiv_faithfulApprox_le_gt
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ} (hα_gt : 1 < α)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0) (hsupp : suppLE ρ σ)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    sandwichedRenyiDiv α ((faithfulApprox E lam hlam0.le hlam1).toFun ρ)
        ((faithfulApprox E lam hlam0.le hlam1).toFun σ) ≤ sandwichedRenyiDiv α ρ σ := by
  have hα_ge : (1 : ℝ) / 2 ≤ α := by linarith
  have hα0 : 0 < α := by linarith
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    apply hρ0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply]
    exact LinearMap.mem_ker.mp (hsupp (LinearMap.mem_ker.mpr (by simp)))
  set F := faithfulApprox E lam hlam0.le hlam1 with hF
  have hF1 : F.toFun 1 ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_one_pdSetLM E hlam0 hlam1
  have hFρ_pd : F.toFun ρ ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_pdSetLM E hlam0 hlam1 hρ hρ0
  have hFσ_pd : F.toFun σ ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_pdSetLM E hlam0 hlam1 hσ hσ0
  have h_pert : ∀ ε : ℝ, 0 < ε →
      sandwichedRenyiDiv α (F.toFun ρ + (ε : ℂ) • F.toFun 1) (F.toFun σ + (ε : ℂ) • F.toFun 1)
        ≤ sandwichedRenyiDiv α (ρ + (ε : ℂ) • (1 : L ℋ)) (σ + (ε : ℂ) • (1 : L ℋ)) := by
    intro ε hε
    have hpd := sandwichedRenyiDiv_monotone_nonneg_perturbed F hα_ge (ne_of_gt hα_gt) hρ hσ hF1 hε
    have hsmul := LinearMap.map_smul F.toCompletelyPositiveMap.toLinearMap (ε : ℂ) (1 : L ℋ)
    have eρ : F.toFun (ρ + (ε : ℂ) • (1 : L ℋ)) = F.toFun ρ + (ε : ℂ) • F.toFun (1 : L ℋ) := by
      have h1 := LinearMap.map_add F.toCompletelyPositiveMap.toLinearMap ρ ((ε : ℂ) • (1 : L ℋ))
      rw [hsmul] at h1; exact h1
    have eσ : F.toFun (σ + (ε : ℂ) • (1 : L ℋ)) = F.toFun σ + (ε : ℂ) • F.toFun (1 : L ℋ) := by
      have h1 := LinearMap.map_add F.toCompletelyPositiveMap.toLinearMap σ ((ε : ℂ) • (1 : L ℋ))
      rw [hsmul] at h1; exact h1
    rw [eρ, eσ] at hpd
    exact hpd
  have h_RHS := sandwichedRenyiDiv_tendsto_of_suppLE hα_gt hρ hσ hsupp hρ0
  have h_LHS := sandwichedRenyiDiv_tendsto_pd hα0 hFρ_pd hFσ_pd hF1
  haveI : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  exact le_of_tendsto_of_tendsto h_LHS h_RHS
    (Filter.eventually_of_mem self_mem_nhdsWithin h_pert)

/-- **Operator convergence along the faithful path** (`α > 1`). With
    `Pσ λ := (1−λ)•A + (λ·cσ)•1` and `Pρ λ := (1−λ)•B + (λ·cρ)•1` (`A = Eσ`, `B = Eρ`,
    `cσ > 0`, `cρ ≥ 0`), `Pσ^β Pρ Pσ^β → A^β B A^β` as `λ → 0⁺`. The depolarizing shift
    `(λ·cσ)•1` commutes with `A`, so the pseudo-inverse blow-up on `ker A` is killed by
    `suppLE B A`; the residual `ker A`-contribution scales as `λ^{1/α} → 0`. -/
private lemma rpow_conj_tendsto_faithful
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα_gt : 1 < α) {A B : L ℋ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hsupp : suppLE B A)
    {cσ cρ : ℝ} (hcσ : 0 < cσ) (hcρ : 0 ≤ cρ) :
    Filter.Tendsto
      (fun lam : ℝ =>
        CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) ((1-α)/(2*α))
          * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ))
          * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) ((1-α)/(2*α)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (CFC.rpow A ((1-α)/(2*α)) * B * CFC.rpow A ((1-α)/(2*α)))) := by
  classical
  set β : ℝ := (1-α)/(2*α) with hβ
  have hαpos : 0 < α := by linarith
  have hβneg : β < 0 := by
    rw [hβ]; apply div_neg_of_neg_of_pos (by linarith) (by positivity)
  have h2β : (1:ℝ) + 2*β = 1/α := by rw [hβ]; field_simp; ring
  have hα_inv_pos : (0:ℝ) < 1/α := one_div_pos.mpr hαpos
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hA_pos : A.IsPositive := (LinearMap.nonneg_iff_isPositive A).mp hA
  have hA_sym : A.IsSymmetric := hA_pos.isSymmetric
  have hB_sym : B.IsSymmetric := ((LinearMap.nonneg_iff_isPositive B).mp hB).isSymmetric
  set b := hA_sym.eigenvectorBasis hn with hb
  set eig := hA_sym.eigenvalues hn with heig
  have h_eig_nn : ∀ i, 0 ≤ eig i := fun i => hA_pos.nonneg_eigenvalues hn i
  have h_eig_apply : ∀ i, A (b i) = ((eig i : ℝ):ℂ) • b i := hA_sym.apply_eigenvectorBasis hn
  have hb_ne : ∀ i, b i ≠ 0 := fun i => b.orthonormal.ne_zero i
  have h_ker : ∀ k, eig k = 0 → B (b k) = 0 := by
    intro k hk
    exact hsupp (LinearMap.mem_ker.mpr (by rw [h_eig_apply k, hk]; simp))
  have h_supp_zero : ∀ i j, (eig i = 0 ∨ eig j = 0) → inner ℂ (b j) (B (b i)) = (0:ℂ) := by
    intro i j hij
    rcases hij with hi | hj
    · rw [h_ker i hi]; simp
    · rw [show inner ℂ (b j) (B (b i)) = inner ℂ (B (b j)) (b i) from (hB_sym (b j) (b i)).symm,
          h_ker j hj]; simp
  -- eigenvalue of the perturbed operator `Pσ λ`.
  set ν : ℝ → Fin n → ℝ := fun lam i => (1-lam)*eig i + lam*cσ with hν
  have hPσ_app : ∀ (lam : ℝ) k,
      (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) (b k) = ((ν lam k : ℝ):ℂ) • b k := by
    intro lam k
    rw [LinearMap.add_apply, LinearMap.smul_apply, h_eig_apply k, LinearMap.smul_apply,
        Module.End.one_apply, smul_smul, ← add_smul, hν]
    push_cast; ring_nf
  have hν_pos : ∀ (lam : ℝ), 0 < lam → lam ≤ 1 → ∀ k, 0 < ν lam k := by
    intro lam hlam0 hlam1 k
    have h1 : 0 ≤ (1-lam)*eig k := mul_nonneg (by linarith) (h_eig_nn k)
    have h2 : 0 < lam*cσ := mul_pos hlam0 hcσ
    rw [hν]; linarith
  have hν_le : ∀ (lam : ℝ), 0 < lam → lam ≤ 1 → ∀ k, lam*cσ ≤ ν lam k := by
    intro lam hlam0 hlam1 k
    have h1 : 0 ≤ (1-lam)*eig k := mul_nonneg (by linarith) (h_eig_nn k)
    rw [hν]; linarith
  -- `A^β (b i) = (eig i)^β • b i`.
  have hspec0 : ∀ i, eig i ∈ spectrum ℝ A :=
    fun i => mem_spectrum_real_of_eigenvector (hb_ne i) (h_eig_apply i)
  have hS0b : ∀ i, CFC.rpow A β (b i) = (((eig i)^β : ℝ):ℂ) • b i :=
    fun i => rpow_apply_eigenvector hA β (h_eig_apply i) (hspec0 i)
  have hS0rho : ∀ i, CFC.rpow A β (B (b i))
      = ∑ j, ((((eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j := by
    intro i
    conv_lhs => rw [show B (b i) = ∑ j, inner ℂ (b j) (B (b i)) • b j from (b.sum_repr' (B (b i))).symm]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, hS0b j, smul_smul]
    congr 1; ring
  have hM0 : ∀ i, (CFC.rpow A β * B * CFC.rpow A β) (b i)
      = ∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j := by
    intro i
    rw [Module.End.mul_apply, Module.End.mul_apply, hS0b i, map_smul, map_smul, hS0rho i,
        Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul]
    congr 1
    push_cast; ring
  -- per-λ formula for `Pσ^β Pρ Pσ^β (b i)`.
  have hMlam : ∀ (lam : ℝ), 0 < lam → lam ≤ 1 → ∀ i,
      (CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β
        * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ))
        * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β) (b i)
      = (∑ j, (((1-lam : ℝ):ℂ) * (((ν lam i)^β * (ν lam j)^β : ℝ):ℂ)
            * inner ℂ (b j) (B (b i))) • b j)
        + (((lam*cρ * ((ν lam i)^β)^2 : ℝ)):ℂ) • b i := by
    intro lam hlam0 hlam1 i
    set Aε : L ℋ := ((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ) with hAε
    have hAε_nn : (0:L ℋ) ≤ Aε := by
      rw [hAε]
      exact add_nonneg (smul_nonneg (Complex.zero_le_real.mpr (by linarith)) hA)
        (smul_nonneg (Complex.zero_le_real.mpr (by positivity)) zero_le_one)
    have hAε_app : ∀ k, Aε (b k) = ((ν lam k : ℝ):ℂ) • b k := hPσ_app lam
    have hAε_spec : ∀ k, ν lam k ∈ spectrum ℝ Aε :=
      fun k => mem_spectrum_real_of_eigenvector (hb_ne k) (hAε_app k)
    have hSb : ∀ k, CFC.rpow Aε β (b k) = (((ν lam k)^β : ℝ):ℂ) • b k :=
      fun k => rpow_apply_eigenvector hAε_nn β (hAε_app k) (hAε_spec k)
    -- expand `(Pρ λ)(b i) = (1-λ)•B(b i) + (λcρ)•b i`.
    have hPρ_app : (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ)) (b i)
        = ((1-lam:ℝ):ℂ) • B (b i) + ((lam*cρ:ℝ):ℂ) • b i := by
      rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply]
    have hSrho : CFC.rpow Aε β (B (b i))
        = ∑ j, ((((ν lam j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j := by
      conv_lhs => rw [show B (b i) = ∑ j, inner ℂ (b j) (B (b i)) • b j from (b.sum_repr' (B (b i))).symm]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, hSb j, smul_smul]
      congr 1; ring
    rw [Module.End.mul_apply, Module.End.mul_apply, hSb i, map_smul, map_smul, hPρ_app,
        map_add, map_smul, map_smul, hSrho, hSb i, smul_add]
    congr 1
    · rw [smul_smul, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_smul]
      congr 1
      push_cast; ring
    · rw [smul_smul, smul_smul]
      congr 1
      push_cast; ring
  -- `ν lam k → eig k` as `λ → 0⁺`.
  have hν_tendsto : ∀ k, Filter.Tendsto (fun lam : ℝ => ν lam k)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (eig k)) := by
    intro k
    have hcont : Continuous (fun lam : ℝ => ν lam k) := by rw [hν]; fun_prop
    have h0 : Filter.Tendsto (fun lam : ℝ => ν lam k) (nhds 0) (nhds (ν 0 k)) := hcont.tendsto 0
    have : ν 0 k = eig k := by rw [hν]; ring
    rw [this] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hrpow_tendsto : ∀ k, 0 < eig k →
      Filter.Tendsto (fun lam : ℝ => (ν lam k)^β) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((eig k)^β)) :=
    fun k hk => ((Real.continuousAt_rpow_const (eig k) β (Or.inl (ne_of_gt hk))).tendsto).comp
      (hν_tendsto k)
  -- extra-term scalar `λ·cρ·(ν λ i)^{2β} → 0`.
  have hextra : ∀ i, Filter.Tendsto (fun lam : ℝ => (((lam*cρ * ((ν lam i)^β)^2 : ℝ)) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro i
    have hg : Filter.Tendsto (fun lam : ℝ => cρ * cσ^(2*β) * lam ^ (1/α))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hgc : Filter.Tendsto (fun lam : ℝ => lam ^ (1/α))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have h0 := (Real.continuousAt_rpow_const 0 (1/α) (Or.inr hα_inv_pos.le)).tendsto
        rw [Real.zero_rpow (ne_of_gt hα_inv_pos)] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      have := hgc.const_mul (cρ * cσ^(2*β))
      simpa using this
    have hIio : Set.Iio (1:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
    have hreal : Filter.Tendsto (fun lam : ℝ => lam*cρ * ((ν lam i)^β)^2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      apply squeeze_zero' (f := fun lam => lam*cρ * ((ν lam i)^β)^2)
        (g := fun lam => cρ * cσ^(2*β) * lam ^ (1/α))
      · filter_upwards [self_mem_nhdsWithin, hIio] with lam hlam hlam1
        have hlam0 : (0:ℝ) < lam := hlam
        exact mul_nonneg (mul_nonneg hlam0.le hcρ) (sq_nonneg _)
      · filter_upwards [self_mem_nhdsWithin, hIio] with lam hlam hlam1
        have hlam0 : (0:ℝ) < lam := hlam
        have hlam1' : lam ≤ 1 := le_of_lt hlam1
        have hνpos : 0 < ν lam i := hν_pos lam hlam0 hlam1' i
        have hsq : ((ν lam i)^β)^2 = (ν lam i)^(2*β) := by
          rw [← Real.rpow_natCast ((ν lam i)^β) 2, ← Real.rpow_mul hνpos.le]
          ring_nf
        rw [hsq]
        have hlamcσ : 0 < lam*cσ := mul_pos hlam0 hcσ
        have hle : (ν lam i)^(2*β) ≤ (lam*cσ)^(2*β) :=
          Real.rpow_le_rpow_of_nonpos hlamcσ (hν_le lam hlam0 hlam1' i) (by linarith)
        have hlampow : lam * lam^(2*β) = lam ^ (1/α) := by
          rw [← h2β, Real.rpow_add hlam0, Real.rpow_one]
        calc lam*cρ * (ν lam i)^(2*β) ≤ lam*cρ * (lam*cσ)^(2*β) :=
              mul_le_mul_of_nonneg_left hle (mul_nonneg hlam0.le hcρ)
          _ = cρ * cσ^(2*β) * lam ^ (1/α) := by
                rw [Real.mul_rpow hlam0.le hcσ.le, ← hlampow]; ring
      · exact hg
    have hcomp := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp hreal
    simpa only [Function.comp_def, Complex.ofReal_zero] using hcomp
  -- per-i vector convergence.
  have key : ∀ i, Filter.Tendsto
      (fun lam : ℝ =>
        (CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β
          * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ))
          * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β) (b i))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((CFC.rpow A β * B * CFC.rpow A β) (b i))) := by
    intro i
    rw [hM0 i]
    have hIio : Set.Iio (1:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
    have hEq : (fun lam : ℝ =>
        (CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β
          * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ))
          * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β) (b i))
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun lam => (∑ j, (((1-lam : ℝ):ℂ) * (((ν lam i)^β * (ν lam j)^β : ℝ):ℂ)
            * inner ℂ (b j) (B (b i))) • b j)
          + (((lam*cρ * ((ν lam i)^β)^2 : ℝ)):ℂ) • b i) := by
      filter_upwards [self_mem_nhdsWithin, hIio] with lam hlam hlam1
      exact hMlam lam hlam (le_of_lt hlam1) i
    refine Filter.Tendsto.congr' hEq.symm ?_
    rw [show (∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j)
        = (∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j) + (0:ℋ) from
        (add_zero _).symm]
    apply Filter.Tendsto.add
    · apply tendsto_finset_sum
      intro j _
      by_cases hzero : eig i = 0 ∨ eig j = 0
      · have hin0 := h_supp_zero i j hzero
        rw [hin0]
        simp only [mul_zero, zero_smul]
        exact tendsto_const_nhds
      · push_neg at hzero
        obtain ⟨hi, hj⟩ := hzero
        have hi' : 0 < eig i := lt_of_le_of_ne (h_eig_nn i) (Ne.symm hi)
        have hj' : 0 < eig j := lt_of_le_of_ne (h_eig_nn j) (Ne.symm hj)
        have hsc : Filter.Tendsto
            (fun lam : ℝ => ((1-lam : ℝ):ℂ) * (((ν lam i)^β * (ν lam j)^β : ℝ):ℂ)
              * inner ℂ (b j) (B (b i)))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i)))) := by
          have hone : Filter.Tendsto (fun lam : ℝ => ((1-lam : ℝ):ℂ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
            have hc : Continuous (fun lam : ℝ => ((1-lam : ℝ):ℂ)) := by fun_prop
            have := hc.tendsto 0
            simpa using this.mono_left nhdsWithin_le_nhds
          have hr : Filter.Tendsto (fun lam : ℝ => (((ν lam i)^β * (ν lam j)^β : ℝ):ℂ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds ((((eig i)^β * (eig j)^β : ℝ)):ℂ)) :=
            (Complex.continuous_ofReal.tendsto _).comp ((hrpow_tendsto i hi').mul (hrpow_tendsto j hj'))
          have hprod := (hone.mul hr).mul_const (inner ℂ (b j) (B (b i)))
          simpa using hprod
        simpa using hsc.smul_const (b j)
    · rw [show (0:ℋ) = (0:ℂ) • b i from (zero_smul ℂ (b i)).symm]
      exact (hextra i).smul_const (b i)
  -- assemble via outer-product reconstruction.
  have hrecon0 : (CFC.rpow A β * B * CFC.rpow A β)
      = ∑ i, outer_product (b i) ((CFC.rpow A β * B * CFC.rpow A β) (b i)) :=
    linearMap_eq_sum_outer_product b _
  have hfun : (fun lam : ℝ =>
        CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β
          * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ))
          * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β)
      = (fun lam : ℝ => ∑ i, outer_product (b i)
          ((CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β
            * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ))
            * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β) (b i))) :=
    funext fun lam => linearMap_eq_sum_outer_product b _
  rw [hrecon0, hfun]
  apply tendsto_finset_sum
  intro i _
  exact ((continuous_outerL (b i)).tendsto _).comp (key i)

/-- **`λ → 0⁺` boundary continuity along the faithful (depolarizing) path** (`α > 1`):
    `D_α(F_λρ ‖ F_λσ) → D_α(Eρ ‖ Eσ)`. The pseudo-inverse blow-up of `(F_λσ)^β` is killed by
    `suppLE (Eρ) (Eσ)` (the depolarizing perturbation commutes with `Eσ`). -/
private lemma sandwichedRenyiDiv_tendsto_faithful
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ} (hα_gt : 1 < α)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hσ0 : σ ≠ 0) (hρ0 : ρ ≠ 0)
    (hEsupp : suppLE (E.toFun ρ) (E.toFun σ)) :
    Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        sandwichedRenyiDiv α
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun σ))
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (nhdsWithin 0 (Set.Ioi 0)))
      (nhds (sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ))) := by
  classical
  have hαpos : 0 < α := by linarith
  set β : ℝ := (1-α)/(2*α) with hβ
  set Eρ : L 𝒦 := E.toFun ρ with hEρdef
  set Eσ : L 𝒦 := E.toFun σ with hEσdef
  have hEρ_nn : (0:L 𝒦) ≤ Eρ := map_nonneg E.toCompletelyPositiveMap hρ
  have hEσ_nn : (0:L 𝒦) ≤ Eσ := map_nonneg E.toCompletelyPositiveMap hσ
  have hd_pos : 0 < (Module.finrank ℂ 𝒦 : ℝ) := by exact_mod_cast Module.finrank_pos
  set cσ : ℝ := (Tr σ).re / (Module.finrank ℂ 𝒦 : ℝ) with hcσ
  set cρ : ℝ := (Tr ρ).re / (Module.finrank ℂ 𝒦 : ℝ) with hcρ
  have hcσ_pos : 0 < cσ := div_pos (trace_re_pos_of_ne_zero hσ hσ0) hd_pos
  have hcρ_nn : 0 ≤ cρ := div_nonneg (le_of_lt (trace_re_pos_of_ne_zero hρ hρ0)) hd_pos.le
  have hEρ0 : Eρ ≠ 0 := by
    intro h
    have hz : (Tr Eρ).re = 0 := by rw [h]; simp
    rw [hEρdef, ← E.trace_map ρ] at hz
    exact (trace_re_pos_of_ne_zero hρ hρ0).ne' hz
  -- Operator convergence along the faithful path (in the target space `𝒦`).
  have hM := rpow_conj_tendsto_faithful (ℋ := 𝒦) hα_gt hEσ_nn hEρ_nn hEsupp hcσ_pos hcρ_nn
  -- Wrap to `sandwichedQuasi` via continuity of `X ↦ Tr (X^α)` on the non-negative cone.
  have hMnn : ∀ X Y : L 𝒦, 0 ≤ Y → (0:L 𝒦) ≤ CFC.rpow X β * Y * CFC.rpow X β :=
    fun X Y hY => conjugate_nonneg_of_nonneg hY CFC.rpow_nonneg
  have hcont : ContinuousWithinAt (fun X : L 𝒦 => Tr (CFC.rpow X α)) {X : L 𝒦 | 0 ≤ X}
      (CFC.rpow Eσ β * Eρ * CFC.rpow Eσ β) := by
    have h1 : ContinuousOn (fun X : L 𝒦 => CFC.rpow X α) {X : L 𝒦 | 0 ≤ X} :=
      rpow_continuousOn_nonneg (le_of_lt hαpos)
    have h2 : Continuous (fun A : L 𝒦 => Tr A) := LinearMap.continuous_of_finiteDimensional _
    exact (h2.comp_continuousOn h1).continuousWithinAt (hMnn Eσ Eρ hEρ_nn)
  have hIio : Set.Iio (1:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
    nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
  have hMwithin : Filter.Tendsto
      (fun lam : ℝ => CFC.rpow (((1-lam:ℝ):ℂ)•Eσ + ((lam*cσ:ℝ):ℂ)•(1:L 𝒦)) β
        * (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1:L 𝒦))
        * CFC.rpow (((1-lam:ℝ):ℂ)•Eσ + ((lam*cσ:ℝ):ℂ)•(1:L 𝒦)) β)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin (CFC.rpow Eσ β * Eρ * CFC.rpow Eσ β) {X : L 𝒦 | 0 ≤ X}) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hM, ?_⟩
    filter_upwards [self_mem_nhdsWithin, hIio] with lam hlam hlam1
    have hlam0 : (0:ℝ) < lam := hlam
    have hlam1' : lam < 1 := hlam1
    have hPρ_nn : (0:L 𝒦) ≤ ((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1:L 𝒦) :=
      add_nonneg (smul_nonneg (Complex.zero_le_real.mpr (by linarith)) hEρ_nn)
        (smul_nonneg (Complex.zero_le_real.mpr (mul_nonneg hlam0.le hcρ_nn)) zero_le_one)
    exact hMnn _ _ hPρ_nn
  have hQcx := Filter.Tendsto.comp hcont hMwithin
  -- `sandwichedRenyiDiv` tendsto over the real parameter `λ`.
  have hTr0 : (Tr Eρ).re ≠ 0 := ne_of_gt (trace_re_pos_of_ne_zero hEρ_nn hEρ0)
  have hQ0 : (sandwichedQuasi α Eρ Eσ).re ≠ 0 :=
    sandwichedQuasi_re_ne_zero_of_suppLE hα_gt hEρ_nn hEσ_nn hEsupp hEρ0
  have hQre : Filter.Tendsto
      (fun lam : ℝ => (sandwichedQuasi α (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1:L 𝒦))
        (((1-lam:ℝ):ℂ)•Eσ + ((lam*cσ:ℝ):ℂ)•(1:L 𝒦))).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (sandwichedQuasi α Eρ Eσ).re) :=
    (Complex.continuous_re.tendsto _).comp hQcx
  have hTre : Filter.Tendsto
      (fun lam : ℝ => (Tr (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1:L 𝒦))).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Tr Eρ).re) := by
    have hform : ∀ lam : ℝ, (Tr (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1:L 𝒦))).re
        = (1-lam) * (Tr Eρ).re + (lam*cρ) * (Module.finrank ℂ 𝒦 : ℝ) := by
      intro lam
      rw [map_add, map_smul, map_smul, LinearMap.trace_one, smul_eq_mul, smul_eq_mul,
          Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.natCast_re]
    simp_rw [hform]
    have hcont : Continuous
        (fun lam : ℝ => (1-lam) * (Tr Eρ).re + (lam*cρ) * (Module.finrank ℂ 𝒦 : ℝ)) := by
      fun_prop
    have h2 := hcont.tendsto 0
    have h3 : (1-(0:ℝ)) * (Tr Eρ).re + (0*cρ) * (Module.finrank ℂ 𝒦 : ℝ) = (Tr Eρ).re := by ring
    rw [h3] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  have hD : Filter.Tendsto
      (fun lam : ℝ => sandwichedRenyiDiv α (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1:L 𝒦))
        (((1-lam:ℝ):ℂ)•Eσ + ((lam*cσ:ℝ):ℂ)•(1:L 𝒦)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (sandwichedRenyiDiv α Eρ Eσ)) := by
    unfold sandwichedRenyiDiv
    have hRatio := Filter.Tendsto.div hQre hTre hTr0
    exact ((Real.continuousAt_log (div_ne_zero hQ0 hTr0)).tendsto.comp hRatio).const_mul _
  -- Transfer to the subtype filter; identify `F_λ.toFun` with the explicit perturbation.
  have hFeq : ∀ (X : L ℋ) (cX : ℝ), cX = (Tr X).re / (Module.finrank ℂ 𝒦 : ℝ) → 0 ≤ X →
      ∀ (l : {l : ℝ // 0 < l ∧ l ≤ 1}),
        (faithfulApprox E l.val l.property.1.le l.property.2).toFun X
          = ((1-l.val:ℝ):ℂ)•E.toFun X + ((l.val*cX:ℝ):ℂ)•(1:L 𝒦) := by
    intro X cX hcX hX l
    have hTrX_re : Tr X = ((Tr X).re : ℂ) := by
      have h := ((LinearMap.nonneg_iff_isPositive X).mp hX).trace_nonneg
      rw [Complex.le_def] at h
      exact (Complex.ext rfl h.2.symm)
    change ((1-l.val:ℝ):ℂ)•E.toFun X + ((l.val:ℝ):ℂ)•((Tr X/(Module.finrank ℂ 𝒦:ℂ))•(1:L 𝒦)) = _
    rw [smul_smul]
    congr 2
    rw [hTrX_re, hcX]
    push_cast
    field_simp
  haveI : (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
      (nhdsWithin 0 (Set.Ioi 0))).NeBot := by
    refine Filter.comap_neBot fun t ht => ?_
    obtain ⟨U, hU_open, hU0, hU_sub⟩ := mem_nhdsWithin.mp ht
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp (hU_open.mem_nhds hU0)
    have hx_pos : (0 : ℝ) < min (δ / 2) 1 := lt_min (by positivity) one_pos
    refine ⟨⟨min (δ / 2) 1, hx_pos, min_le_right _ _⟩, ?_⟩
    apply hU_sub
    refine ⟨hball ?_, hx_pos⟩
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx_pos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htc : Filter.Tendsto (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (nhdsWithin 0 (Set.Ioi 0)))
      (nhdsWithin 0 (Set.Ioi 0)) := Filter.tendsto_comap
  have hcomp := hD.comp htc
  refine hcomp.congr' ?_
  filter_upwards with l
  rw [Function.comp_apply, hFeq ρ cρ hcρ hρ l, hFeq σ cσ hcσ hσ l]

/-- **Real-valued monotonicity for `α > 1`** with the support condition and `ρ ≠ 0`.

    Mirrors the `α < 1` proof (`sandwichedRenyiDivNN_monotone_real_aux_lt`):

    1. **Faithful DPI per `λ`** (`step1`): for each `λ ∈ (0, 1]`, `F_λ` is faithful
       (`F_λ 1 ∈ pdSetLM`), and `D_α(F_λρ ‖ F_λσ) ≤ D_α(ρ‖σ)` — obtained by taking
       `ε → 0⁺` in the perturbed PD inequality, with the LHS limit using PD-continuity
       (the path `F_λ(ρ+εI) = F_λρ + ε F_λ1` stays in `pdSetLM`) and the RHS limit using
       boundary continuity under `suppLE` (`sandwichedRenyiDiv_tendsto_of_suppLE`).
    2. **`λ → 0⁺`** (`step2`): `(F_λρ, F_λσ) → (Eρ, Eσ)` and `D_α(F_λρ ‖ F_λσ) →
       D_α(Eρ ‖ Eσ)` by boundary continuity along the faithful (depolarizing) path. -/
private lemma sandwichedRenyiDivNN_monotone_real_aux
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ} (hα_gt : 1 < α)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hsupp : suppLE ρ σ) (hEsupp : suppLE (E.toFun ρ) (E.toFun σ)) (hρ0 : ρ ≠ 0) :
    sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤ sandwichedRenyiDiv α ρ σ := by
  have hα_ge : (1 : ℝ) / 2 ≤ α := by linarith
  have hα0 : 0 < α := by linarith
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    apply hρ0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply]
    exact LinearMap.mem_ker.mp (hsupp (LinearMap.mem_ker.mpr (by simp)))
  -- **Step 1**: faithful DPI for each `λ ∈ (0,1]`.
  have step1 : ∀ (l : {l : ℝ // 0 < l ∧ l ≤ 1}),
      sandwichedRenyiDiv α
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun σ)
        ≤ sandwichedRenyiDiv α ρ σ := by
    rintro ⟨lam, hlam0, hlam1⟩
    exact sandwichedRenyiDiv_faithfulApprox_le_gt E hα_gt hρ hσ hρ0 hsupp hlam0 hlam1
  -- **Step 2**: `λ → 0⁺`, boundary continuity along the faithful path.
  haveI hNeBot : (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
      (nhdsWithin 0 (Set.Ioi 0))).NeBot := by
    refine Filter.comap_neBot fun t ht => ?_
    obtain ⟨U, hU_open, hU0, hU_sub⟩ := mem_nhdsWithin.mp ht
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp (hU_open.mem_nhds hU0)
    have hx_pos : (0 : ℝ) < min (δ / 2) 1 := lt_min (by positivity) one_pos
    refine ⟨⟨min (δ / 2) 1, hx_pos, min_le_right _ _⟩, ?_⟩
    apply hU_sub
    refine ⟨hball ?_, hx_pos⟩
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx_pos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have step2 : Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        sandwichedRenyiDiv α
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun σ))
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (nhdsWithin 0 (Set.Ioi 0)))
      (nhds (sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ))) :=
    sandwichedRenyiDiv_tendsto_faithful E hα_gt hρ hσ hσ0 hρ0 hEsupp
  exact le_of_tendsto step2 (Filter.Eventually.of_forall step1)

/-- Real-valued monotonicity for `α < 1`, in the non-orthogonal regime
    (`Q_α(ρ‖σ) ≠ 0` and `Q_α(Eρ‖Eσ) ≠ 0`).

    **Proof**: For each `λ ∈ (0,1]`, the faithful approximation `F_λ` satisfies
    `D_α(F_λρ ‖ F_λσ) ≤ D_α(ρ‖σ)` — obtained by taking `ε → 0⁺` in the perturbed PD
    inequality `sandwichedRenyiDiv_monotone_nonneg_perturbed` (`F_λρ, F_λσ` are pd, so
    no support condition is needed and `Q_α > 0` automatically). Taking `λ → 0⁺`, the
    LHS converges to `D_α(Eρ ‖ Eσ)` by nonneg-cone continuity (`Q_α(Eρ‖Eσ) ≠ 0`). -/
private lemma sandwichedRenyiDivNN_monotone_real_aux_lt
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_lt : α < 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0)
    (hQρσ : (sandwichedQuasi α ρ σ).re ≠ 0)
    (hQEρσ : (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re ≠ 0) :
    sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤ sandwichedRenyiDiv α ρ σ := by
  have hα0 : 0 < α := by linarith
  have hEρ : (0 : L 𝒦) ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
  have hEσ : (0 : L 𝒦) ≤ E.toFun σ := map_nonneg E.toCompletelyPositiveMap hσ
  have hTrρ : (Tr ρ).re ≠ 0 := ne_of_gt (trace_re_pos_of_ne_zero hρ hρ0)
  have hEρ0 : E.toFun ρ ≠ 0 := by
    intro h
    have hz : (Tr (E.toFun ρ)).re = 0 := by rw [h]; simp
    rw [← E.trace_map ρ] at hz
    exact hTrρ hz
  have hTrEρ : (Tr (E.toFun ρ)).re ≠ 0 := ne_of_gt (trace_re_pos_of_ne_zero hEρ hEρ0)
  -- `Q_α(ρ‖σ) ≠ 0` forces `σ ≠ 0` (otherwise `σ^β = 0` and `Q = 0`).
  have hβne : (1 - α) / (2 * α) ≠ 0 := div_ne_zero (by linarith) (by positivity)
  have hσ0 : σ ≠ 0 := by
    intro h
    apply hQρσ
    rw [sandwichedQuasi_re_eq_zero_iff hα0 hρ hσ, h, CFC.zero_rpow hβne, zero_mul, mul_zero]
  -- **Step 1**: for each `λ ∈ (0,1]`, `D_α(F_λρ ‖ F_λσ) ≤ D_α(ρ‖σ)`.
  have step1 : ∀ (l : {l : ℝ // 0 < l ∧ l ≤ 1}),
      sandwichedRenyiDiv α
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun σ)
        ≤ sandwichedRenyiDiv α ρ σ := by
    rintro ⟨lam, hlam0, hlam1⟩
    exact sandwichedRenyiDiv_faithfulApprox_le E hα_ge hα_lt hρ hσ hρ0 hσ0 hQρσ hlam0 hlam1
  -- **Step 2**: `λ → 0⁺`. `(F_λρ, F_λσ) → (Eρ, Eσ)` within the non-negative cone.
  have hpair : Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        (((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ),
         ((faithfulApprox E l.val l.property.1.le l.property.2).toFun σ)))
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (nhdsWithin 0 (Set.Ioi 0)))
      (nhdsWithin (E.toFun ρ, E.toFun σ) ({A : L 𝒦 | 0 ≤ A} ×ˢ {A : L 𝒦 | 0 ≤ A})) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(faithfulApprox_tendsto E ρ).prodMk_nhds (faithfulApprox_tendsto E σ), ?_⟩
    filter_upwards with l
    exact Set.mk_mem_prod
      (nonneg_of_pdSetLM (faithfulApprox_pdSetLM E l.property.1 l.property.2 hρ hρ0))
      (nonneg_of_pdSetLM (faithfulApprox_pdSetLM E l.property.1 l.property.2 hσ hσ0))
  have hcwa : ContinuousWithinAt (fun p : L 𝒦 × L 𝒦 => sandwichedRenyiDiv α p.1 p.2)
      ({A : L 𝒦 | 0 ≤ A} ×ˢ {A : L 𝒦 | 0 ≤ A}) (E.toFun ρ, E.toFun σ) :=
    sandwichedRenyiDiv_continuousWithinAt_lt hα0 hα_lt hEρ hEσ hQEρσ hTrEρ
  have hlim := hcwa.tendsto.comp hpair
  haveI : (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
      (nhdsWithin 0 (Set.Ioi 0))).NeBot := by
    refine Filter.comap_neBot fun t ht => ?_
    obtain ⟨U, hU_open, hU0, hU_sub⟩ := mem_nhdsWithin.mp ht
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp (hU_open.mem_nhds hU0)
    have hx_pos : (0 : ℝ) < min (δ / 2) 1 := lt_min (by positivity) one_pos
    refine ⟨⟨min (δ / 2) 1, hx_pos, min_le_right _ _⟩, ?_⟩
    apply hU_sub
    refine ⟨hball ?_, hx_pos⟩
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx_pos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  exact le_of_tendsto hlim (Filter.Eventually.of_forall step1)

/-! ### Main theorem: Theorem 1 for non-negative operators, general CPTP -/

/-- **Theorem 1 (Frank–Lieb, arXiv:1306.5358v3): Data-processing for the
    sandwiched Rényi relative entropy on non-negative operators.**

    For any CPTP map `E : CPTP ℋ ℋ`, any `α ∈ [1/2, 1) ∪ (1, ∞)`, and any
    non-negative `ρ, σ : L ℋ`,

      `D_α^{NN}(E ρ ‖ E σ) ≤ D_α^{NN}(ρ ‖ σ)`,

    where `D_α^{NN}` is the Frank–Lieb extension (`sandwichedRenyiDivNN`) with
    value `+∞ : EReal` on the support-mismatch region for `α > 1`. -/
theorem sandwichedRenyiDivNN_monotone
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    sandwichedRenyiDivNN α (E.toFun ρ) (E.toFun σ) ≤
      sandwichedRenyiDivNN α ρ σ := by
  have hEρ : (0 : L 𝒦) ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
  have hEσ : (0 : L 𝒦) ≤ E.toFun σ := map_nonneg E.toCompletelyPositiveMap hσ
  by_cases hα_gt : 1 < α
  · -- `α > 1`.
    by_cases hsupp : suppLE ρ σ
    · have hEsupp : suppLE (E.toFun ρ) (E.toFun σ) := suppLE_of_CPTP E hρ hσ hsupp
      by_cases hρ0 : ρ = 0
      · -- `ρ = 0`: both divergences are `0`.
        have hEρ0 : E.toFun ρ = 0 := by
          rw [hρ0]; exact map_zero E.toCompletelyPositiveMap.toLinearMap
        have h_LHS0 : sandwichedRenyiDivNN α (E.toFun ρ) (E.toFun σ) = ((0 : ℝ) : EReal) := by
          rw [hEρ0]
          unfold sandwichedRenyiDivNN
          rw [if_neg, sandwichedRenyiDiv_zero_left]
          rintro (⟨_, h⟩ | ⟨h, _⟩)
          · exact h (le_top.trans_eq (LinearMap.ker_zero).symm)
          · linarith
        have h_RHS0 : sandwichedRenyiDivNN α ρ σ = ((0 : ℝ) : EReal) := by
          rw [hρ0]
          unfold sandwichedRenyiDivNN
          rw [if_neg, sandwichedRenyiDiv_zero_left]
          rintro (⟨_, h⟩ | ⟨h, _⟩)
          · exact h (le_top.trans_eq (LinearMap.ker_zero).symm)
          · linarith
        rw [h_LHS0, h_RHS0]
      · have h_LHS : sandwichedRenyiDivNN α (E.toFun ρ) (E.toFun σ) =
            ((sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) : ℝ) : EReal) := by
          unfold sandwichedRenyiDivNN
          rw [if_neg]; rintro (⟨_, h⟩ | ⟨h, _⟩)
          · exact h hEsupp
          · linarith
        have h_RHS : sandwichedRenyiDivNN α ρ σ =
            ((sandwichedRenyiDiv α ρ σ : ℝ) : EReal) := by
          unfold sandwichedRenyiDivNN
          rw [if_neg]; rintro (⟨_, h⟩ | ⟨h, _⟩)
          · exact h hsupp
          · linarith
        rw [h_LHS, h_RHS]
        have h_real : sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤
            sandwichedRenyiDiv α ρ σ :=
          sandwichedRenyiDivNN_monotone_real_aux E hα_gt hρ hσ hsupp hEsupp hρ0
        exact_mod_cast h_real
    · have h_RHS_top : sandwichedRenyiDivNN α ρ σ = (⊤ : EReal) := by
        unfold sandwichedRenyiDivNN
        exact if_pos (Or.inl ⟨hα_gt, hsupp⟩)
      rw [h_RHS_top]
      exact le_top
  · -- `α < 1`.
    push_neg at hα_gt
    have hα_lt : α < 1 := lt_of_le_of_ne hα_gt hα_ne1
    have hα0 : 0 < α := by linarith
    by_cases hRtop : ρ ≠ 0 ∧ (sandwichedQuasi α ρ σ).re = 0
    · -- Orthogonal supports (`Q_α = 0`, `ρ ≠ 0`): RHS is `⊤`.
      have h_RHS_top : sandwichedRenyiDivNN α ρ σ = (⊤ : EReal) := by
        unfold sandwichedRenyiDivNN
        exact if_pos (Or.inr ⟨hα_lt, hRtop.1, hRtop.2⟩)
      rw [h_RHS_top]
      exact le_top
    · by_cases hρ0 : ρ = 0
      · -- `ρ = 0`: both divergences are `0`.
        have hEρ0 : E.toFun ρ = 0 := by rw [hρ0]; exact map_zero E.toCompletelyPositiveMap.toLinearMap
        have h_LHS0 : sandwichedRenyiDivNN α (E.toFun ρ) (E.toFun σ) = ((0 : ℝ) : EReal) := by
          rw [hEρ0]
          unfold sandwichedRenyiDivNN
          rw [if_neg, sandwichedRenyiDiv_zero_left]
          rintro (⟨h, _⟩ | ⟨_, h, _⟩)
          · linarith
          · exact h rfl
        have h_RHS0 : sandwichedRenyiDivNN α ρ σ = ((0 : ℝ) : EReal) := by
          rw [hρ0]
          unfold sandwichedRenyiDivNN
          rw [if_neg, sandwichedRenyiDiv_zero_left]
          rintro (⟨h, _⟩ | ⟨_, h, _⟩)
          · linarith
          · exact h rfl
        rw [h_LHS0, h_RHS0]
      · -- `ρ ≠ 0` and `Q_α(ρ‖σ) ≠ 0`: real-valued DPI applies (LHS also finite by reflection).
        have hQρσ : (sandwichedQuasi α ρ σ).re ≠ 0 := fun h => hRtop ⟨hρ0, h⟩
        have hQEρσ : (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re ≠ 0 :=
          sandwichedQuasi_re_ne_zero_of_CPTP E hα_ge hα_lt hρ hσ hρ0 hQρσ
        have h_LHS : sandwichedRenyiDivNN α (E.toFun ρ) (E.toFun σ) =
            ((sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) : ℝ) : EReal) := by
          unfold sandwichedRenyiDivNN
          rw [if_neg]; rintro (⟨h, _⟩ | ⟨_, _, h⟩)
          · linarith
          · exact hQEρσ h
        have h_RHS : sandwichedRenyiDivNN α ρ σ =
            ((sandwichedRenyiDiv α ρ σ : ℝ) : EReal) := by
          unfold sandwichedRenyiDivNN
          rw [if_neg]; rintro (⟨h, _⟩ | ⟨_, _, h⟩)
          · linarith
          · exact hQρσ h
        rw [h_LHS, h_RHS]
        have h_real : sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤
            sandwichedRenyiDiv α ρ σ :=
          sandwichedRenyiDivNN_monotone_real_aux_lt E hα_ge hα_lt hρ hσ hρ0 hQρσ hQEρσ
        exact_mod_cast h_real

/-! ### α = ∞ : max-relative entropy -/

section MaxRelEntropy

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

/-- The set of scalars `λ ≥ 0` with `ρ ≤ λ • σ`. -/
def maxRelSet (ρ σ : L ℋ) : Set ℝ := {lam : ℝ | 0 ≤ lam ∧ ρ ≤ (lam : ℂ) • σ}

omit [Nontrivial ℋ] in
/-- `0` is a lower bound of `maxRelSet ρ σ`. -/
lemma maxRelSet_bddBelow (ρ σ : L ℋ) : BddBelow (maxRelSet ρ σ) :=
  ⟨0, fun _ hx => hx.1⟩

omit [Nontrivial ℋ] in
/-- From `ρ ≤ (lam:ℂ) • σ` we get `re ⟨ρ x, x⟩ ≤ lam * re ⟨σ x, x⟩`. -/
lemma re_inner_le_of_le_smul {ρ σ : L ℋ} {lam : ℝ} (h : ρ ≤ (lam : ℂ) • σ) (x : ℋ) :
    RCLike.re (inner ℂ (ρ x) x) ≤ lam * RCLike.re (inner ℂ (σ x) x) := by
  rw [LinearMap.le_def] at h
  obtain ⟨_, h2⟩ := h
  have hx := h2 x
  have heq : ((lam : ℂ) • σ - ρ) x = (lam : ℂ) • σ x - ρ x := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply]
  rw [heq, inner_sub_left, inner_smul_left, Complex.conj_ofReal, map_sub] at hx
  have hre : RCLike.re ((lam : ℂ) * inner ℂ (σ x) x) = lam * RCLike.re (inner ℂ (σ x) x) := by
    change (((lam : ℂ) * inner ℂ (σ x) x)).re = _
    rw [Complex.re_ofReal_mul]; rfl
  rw [hre] at hx
  linarith

/-- For nonneg `ρ ≠ 0`, there is `x` with `re ⟨ρ x, x⟩ > 0`. -/
lemma exists_re_inner_pos_of_ne_zero {ρ : L ℋ} (hρ : 0 ≤ ρ) (hρ0 : ρ ≠ 0) :
    ∃ x, 0 < RCLike.re (inner ℂ (ρ x) x) := by
  by_contra h
  push_neg at h
  apply hρ0
  have hρ_pos : ρ.IsPositive := (LinearMap.nonneg_iff_isPositive ρ).mp hρ
  ext x
  have hle : RCLike.re (inner ℂ (ρ x) x) ≤ 0 := h x
  have hge : 0 ≤ RCLike.re (inner ℂ (ρ x) x) := hρ_pos.2 x
  have heq : RCLike.re (inner ℂ (ρ x) x) = 0 := le_antisymm hle hge
  have hzero := nonneg_apply_eq_zero_of_inner_self_eq_zero hρ heq
  rw [LinearMap.zero_apply]; exact hzero

/-- For nonneg `ρ ≠ 0` with `suppLE ρ σ`, `maxRelSet ρ σ` has a strictly positive lower bound. -/
lemma maxRelSet_pos_lowerBound {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hρ0 : ρ ≠ 0) (hsupp : suppLE ρ σ) :
    ∃ c > (0 : ℝ), ∀ lam ∈ maxRelSet ρ σ, c ≤ lam := by
  obtain ⟨x, hx⟩ := exists_re_inner_pos_of_ne_zero hρ hρ0
  have hσ_pos : σ.IsPositive := (LinearMap.nonneg_iff_isPositive σ).mp hσ
  -- re ⟨σ x, x⟩ > 0, else σ x = 0 ⇒ x ∈ ker σ ⊆ ker ρ ⇒ ρ x = 0 ⇒ re⟨ρx,x⟩ = 0.
  have hσx_pos : 0 < RCLike.re (inner ℂ (σ x) x) := by
    rcases eq_or_lt_of_le (hσ_pos.2 x) with h_eq | h_lt
    · exfalso
      have hσx : σ x = 0 := nonneg_apply_eq_zero_of_inner_self_eq_zero hσ h_eq.symm
      have hxker : x ∈ LinearMap.ker σ := hσx
      have hρx : ρ x = 0 := hsupp hxker
      rw [hρx] at hx; simp at hx
    · exact h_lt
  refine ⟨RCLike.re (inner ℂ (ρ x) x) / RCLike.re (inner ℂ (σ x) x), div_pos hx hσx_pos, ?_⟩
  intro lam hlam
  have hle := re_inner_le_of_le_smul hlam.2 x
  rw [div_le_iff₀ hσx_pos]
  linarith

/-- For nonneg `ρ ≠ 0` with `suppLE ρ σ`, `0 < sInf (maxRelSet ρ σ)`. -/
lemma sInf_maxRelSet_pos {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hρ0 : ρ ≠ 0) (hsupp : suppLE ρ σ) :
    0 < sInf (maxRelSet ρ σ) := by
  obtain ⟨c, hc_pos, hc_lb⟩ := maxRelSet_pos_lowerBound hρ hσ hρ0 hsupp
  obtain ⟨lam, hlam_pos, hlam_le⟩ := nonneg_le_smul_of_suppLE hρ hσ hsupp
  have hne : (maxRelSet ρ σ).Nonempty := ⟨lam, hlam_pos.le, hlam_le⟩
  exact lt_of_lt_of_le hc_pos (le_csInf hne hc_lb)

/-- **Max-relative entropy** for non-negative `ρ, σ` (the `α → ∞` limit of the
    sandwiched Rényi divergence), in the **explicit Frank–Lieb form**
    [arXiv:1306.5358]: `D_∞(ρ‖σ) = log ‖σ^{-1/2} ρ σ^{-1/2}‖` (with `σ^{-1/2}` the
    Moore–Penrose power), and value `⊤ : EReal` on the support-mismatch region
    `¬ suppLE ρ σ`. The equivalent order-theoretic form `log inf{λ ≥ 0 : ρ ≤ λ σ}` is
    `maxRelEntropyNN_eq_log_sInf`. -/
noncomputable def maxRelEntropyNN (ρ σ : L ℋ) : EReal :=
  letI : Decidable (suppLE ρ σ) := Classical.propDecidable _
  if suppLE ρ σ then ((Real.log ‖CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2))‖ : ℝ) : EReal)
  else (⊤ : EReal)

/-- `maxRelSet` is monotone under a positive map: every `λ` working for `ρ ≤ λσ`
    also works for `E ρ ≤ λ E σ`. -/
lemma maxRelSet_subset_of_CPTP
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦) {ρ σ : L ℋ} :
    maxRelSet ρ σ ⊆ maxRelSet (E.toFun ρ) (E.toFun σ) := by
  intro lam hlam
  refine ⟨hlam.1, ?_⟩
  have h1 : E.toCompletelyPositiveMap.toLinearMap ρ ≤
      E.toCompletelyPositiveMap.toLinearMap ((lam : ℂ) • σ) :=
    map_le_map_of_nonneg E.toCompletelyPositiveMap hlam.2
  rw [LinearMap.map_smul] at h1
  exact h1

/-- For nonneg `τ`, `maxRelSet 0 τ = [0, ∞)`. -/
lemma maxRelSet_zero_left {ℋ' : Type u} [Qudit ℋ'] [Nontrivial ℋ'] {τ : L ℋ'} (hτ : 0 ≤ τ) :
    maxRelSet (0 : L ℋ') τ = Set.Ici (0 : ℝ) := by
  ext lam
  simp only [maxRelSet, Set.mem_setOf_eq, Set.mem_Ici]
  refine ⟨fun h => h.1, fun hlam => ⟨hlam, ?_⟩⟩
  exact smul_nonneg (Complex.zero_le_real.mpr hlam) hτ

/-- `E ρ ≠ 0` for non-negative `ρ ≠ 0` and a CPTP map `E` (trace is preserved). -/
lemma CPTP_toFun_ne_zero
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {ρ : L ℋ} (hρ : 0 ≤ ρ) (hρ0 : ρ ≠ 0) :
    E.toFun ρ ≠ 0 := by
  intro h
  have htr : (Tr ρ).re = 0 := by rw [E.trace_map ρ, h]; simp
  exact absurd htr (ne_of_gt (trace_re_pos_of_ne_zero hρ hρ0))

/-! ### α = ∞ : the order-theoretic characterization and the data-processing inequality

`maxRelEntropyNN` is *defined* via the explicit Frank–Lieb formula
`D_∞(ρ‖σ) = log ‖σ^{-1/2} ρ σ^{-1/2}‖` [arXiv:1306.5358]. Here we prove it equals the
order-theoretic form `log inf{λ ≥ 0 : ρ ≤ λ σ}` (`maxRelEntropyNN_eq_log_sInf`), and use
that characterization to prove the data-processing inequality (Theorem 1, `α = ∞`). -/

omit [Nontrivial ℋ] in
/-- `CFC.rpow σ y` as a real continuous-functional-calculus expression. -/
private lemma rpow_eq_cfc_aux {σ : L ℋ} (hσ : 0 ≤ σ) (y : ℝ) :
    CFC.rpow σ y = cfc (fun x : ℝ => x ^ y) σ := by
  rw [CFC.rpow_eq_pow]; exact CFC.rpow_eq_cfc_real hσ

/-- Product of two real powers of `σ`, merged into a single `cfc`
    (valid even at singular `σ`, since the real spectrum is finite hence discrete). -/
private lemma rpow_mul_rpow_cfc {σ : L ℋ} (hσ : 0 ≤ σ) (a b : ℝ) :
    CFC.rpow σ a * CFC.rpow σ b = cfc (fun x : ℝ => x ^ a * x ^ b) σ := by
  have hcont : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ σ) :=
    fun g => (spectrum_real_finite σ).continuousOn g
  rw [rpow_eq_cfc_aux hσ a, rpow_eq_cfc_aux hσ b]
  exact (cfc_mul _ _ σ (hcont _) (hcont _)).symm

/-- Product of three real powers of `σ`, merged into a single `cfc`. -/
private lemma rpow_mul_rpow_mul_rpow_cfc {σ : L ℋ} (hσ : 0 ≤ σ) (a b c : ℝ) :
    CFC.rpow σ a * CFC.rpow σ b * CFC.rpow σ c
      = cfc (fun x : ℝ => x ^ a * x ^ b * x ^ c) σ := by
  have hcont : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ σ) :=
    fun g => (spectrum_real_finite σ).continuousOn g
  rw [rpow_mul_rpow_cfc hσ a b, rpow_eq_cfc_aux hσ c]
  exact (cfc_mul _ _ σ (hcont _) (hcont _)).symm

/-- `σ^{1/2} · σ^{1/2} = σ`. -/
private lemma rpow_half_sq {σ : L ℋ} (hσ : 0 ≤ σ) :
    CFC.rpow σ (1/2) * CFC.rpow σ (1/2) = σ := by
  rw [rpow_mul_rpow_cfc hσ]
  have hfun : (spectrum ℝ σ).EqOn (fun x : ℝ => x ^ (1/2:ℝ) * x ^ (1/2:ℝ)) (fun x : ℝ => x) := by
    intro x hx
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hσ hx
    change x ^ (1/2:ℝ) * x ^ (1/2:ℝ) = x
    rcases eq_or_lt_of_le hx0 with h0 | hpos
    · rw [← h0, Real.zero_rpow (show (1/2:ℝ) ≠ 0 by norm_num), mul_zero]
    · rw [← Real.rpow_add hpos, show (1/2:ℝ) + 1/2 = 1 by norm_num, Real.rpow_one]
  rw [cfc_congr hfun, cfc_id' ℝ σ]

/-- `σ^{1/2}` and `σ^{-1/2}` commute. -/
private lemma rpow_half_mul_rpow_neg_comm {σ : L ℋ} (hσ : 0 ≤ σ) :
    CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2)) = CFC.rpow σ (-(1/2)) * CFC.rpow σ (1/2) := by
  rw [rpow_mul_rpow_cfc hσ, rpow_mul_rpow_cfc hσ]
  exact cfc_congr (fun x _ => mul_comm _ _)

/-- `σ · (σ^{1/2} · σ^{-1/2}) = σ`: the support projection fixes `σ`. -/
private lemma self_mul_rpow_half_mul_rpow_neg {σ : L ℋ} (hσ : 0 ≤ σ) :
    σ * (CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2))) = σ := by
  rw [← mul_assoc]
  nth_rewrite 1 [show (σ : L ℋ) = CFC.rpow σ (1:ℝ) from (CFC.rpow_one σ hσ).symm]
  rw [rpow_mul_rpow_mul_rpow_cfc hσ]
  have hfun : (spectrum ℝ σ).EqOn
      (fun x : ℝ => x ^ (1:ℝ) * x ^ (1/2:ℝ) * x ^ (-(1/2):ℝ)) (fun x : ℝ => x) := by
    intro x hx
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hσ hx
    change x ^ (1:ℝ) * x ^ (1/2:ℝ) * x ^ (-(1/2):ℝ) = x
    rcases eq_or_lt_of_le hx0 with h0 | hpos
    · rw [← h0, Real.zero_rpow (show (1:ℝ) ≠ 0 by norm_num),
        Real.zero_rpow (show (1/2:ℝ) ≠ 0 by norm_num),
        Real.zero_rpow (show (-(1/2):ℝ) ≠ 0 by norm_num)]
      ring
    · rw [← Real.rpow_add hpos, ← Real.rpow_add hpos,
        show (1:ℝ) + 1/2 + (-(1/2)) = 1 by norm_num, Real.rpow_one]
  rw [cfc_congr hfun, cfc_id' ℝ σ]

/-- `σ^{-1/2} · σ · σ^{-1/2} ≤ 1`: the conjugate of `σ` by `σ^{-1/2}` is a projection. -/
private lemma rpow_neg_conj_self_le_one {σ : L ℋ} (hσ : 0 ≤ σ) :
    CFC.rpow σ (-(1/2)) * σ * CFC.rpow σ (-(1/2)) ≤ 1 := by
  nth_rewrite 2 [show (σ : L ℋ) = CFC.rpow σ (1:ℝ) from (CFC.rpow_one σ hσ).symm]
  rw [rpow_mul_rpow_mul_rpow_cfc hσ]
  apply cfc_le_one
  intro x hx
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hσ hx
  change x ^ (-(1/2):ℝ) * x ^ (1:ℝ) * x ^ (-(1/2):ℝ) ≤ 1
  rcases eq_or_lt_of_le hx0 with h0 | hpos
  · rw [← h0, Real.zero_rpow (show (-(1/2):ℝ) ≠ 0 by norm_num),
      Real.zero_rpow (show (1:ℝ) ≠ 0 by norm_num)]
    norm_num
  · refine le_of_eq ?_
    rw [← Real.rpow_add hpos, ← Real.rpow_add hpos,
      show (-(1/2):ℝ) + 1 + (-(1/2)) = 0 by norm_num, Real.rpow_zero]

/-- **Support-projection identity** under `suppLE`:
    `σ^{1/2} · (σ^{-1/2} ρ σ^{-1/2}) · σ^{1/2} = ρ`. -/
private lemma conjugate_rpow_self_eq {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : suppLE ρ σ) :
    CFC.rpow σ (1/2) * (CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2))) * CFC.rpow σ (1/2) = ρ := by
  have hsa_s : IsSelfAdjoint (CFC.rpow σ (1/2)) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hsa_t : IsSelfAdjoint (CFC.rpow σ (-(1/2))) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hcomm := rpow_half_mul_rpow_neg_comm hσ
  have hσP := self_mul_rpow_half_mul_rpow_neg hσ
  -- `P := σ^{1/2} σ^{-1/2}` is self-adjoint.
  have hP_sa : star (CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2)))
      = CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2)) := by
    rw [star_mul, hsa_t.star_eq, hsa_s.star_eq, ← hcomm]
  -- `ρ · P = ρ` (kernel of `σ` is killed by `ρ`).
  have hρP : ρ * (CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2))) = ρ := by
    refine LinearMap.ext fun v => ?_
    have hker : v - (CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2))) v ∈ LinearMap.ker σ := by
      rw [LinearMap.mem_ker, map_sub, ← Module.End.mul_apply, hσP, sub_self]
    have hv0 : ρ (v - (CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2))) v) = 0 :=
      LinearMap.mem_ker.mp (hsupp hker)
    rw [map_sub] at hv0
    change (ρ * (CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2)))) v = ρ v
    rw [Module.End.mul_apply]
    exact (sub_eq_zero.mp hv0).symm
  -- `P · ρ = ρ` (adjoint of the previous).
  have hPρ : (CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2))) * ρ = ρ := by
    have h := congrArg star hρP
    rwa [star_mul, hP_sa, (IsSelfAdjoint.of_nonneg hρ).star_eq] at h
  have key : CFC.rpow σ (1/2) * (CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2))) * CFC.rpow σ (1/2)
      = (CFC.rpow σ (1/2) * CFC.rpow σ (-(1/2))) * ρ * (CFC.rpow σ (-(1/2)) * CFC.rpow σ (1/2)) := by
    simp only [mul_assoc]
  rw [key, ← hcomm, hPρ, hρP]

/-- **Frank–Lieb operator-norm form.** For non-negative `ρ, σ` with `suppLE ρ σ`,
    `inf{λ ≥ 0 : ρ ≤ λ σ} = ‖σ^{-1/2} ρ σ^{-1/2}‖`. -/
lemma sInf_maxRelSet_eq_norm {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : suppLE ρ σ) :
    sInf (maxRelSet ρ σ) = ‖CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2))‖ := by
  set M := CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2)) with hM
  have hMnn : (0 : L ℋ) ≤ M := conjugate_nonneg_of_nonneg hρ CFC.rpow_nonneg
  have hsa_s : IsSelfAdjoint (CFC.rpow σ (1/2)) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hsa_t : IsSelfAdjoint (CFC.rpow σ (-(1/2))) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  -- `‖M‖ ∈ maxRelSet ρ σ`, i.e. `ρ ≤ ‖M‖ • σ`.
  have hmem : ‖M‖ ∈ maxRelSet ρ σ := by
    refine ⟨norm_nonneg _, ?_⟩
    have hMle : M ≤ algebraMap ℝ (L ℋ) ‖M‖ :=
      IsSelfAdjoint.le_algebraMap_norm_self (IsSelfAdjoint.of_nonneg hMnn)
    have hconj := hsa_s.conjugate_le_conjugate hMle
    rw [hM, conjugate_rpow_self_eq hρ hσ hsupp] at hconj
    have hRHS : CFC.rpow σ (1/2) * algebraMap ℝ (L ℋ) ‖M‖ * CFC.rpow σ (1/2)
        = (‖M‖ : ℝ) • σ := by
      rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, rpow_half_sq hσ]
    rw [hRHS] at hconj
    rw [Complex.coe_smul]; exact hconj
  -- `‖M‖` is a lower bound of `maxRelSet ρ σ`.
  have hlb : ∀ lam ∈ maxRelSet ρ σ, ‖M‖ ≤ lam := by
    intro lam hlam
    have hlam0 : 0 ≤ lam := hlam.1
    have hle : ρ ≤ (lam : ℝ) • σ := by
      have h := hlam.2; rwa [Complex.coe_smul] at h
    have hconj := hsa_t.conjugate_le_conjugate hle
    rw [← hM] at hconj
    have hrhs : CFC.rpow σ (-(1/2)) * ((lam : ℝ) • σ) * CFC.rpow σ (-(1/2))
        = (lam : ℝ) • (CFC.rpow σ (-(1/2)) * σ * CFC.rpow σ (-(1/2))) := by
      rw [mul_smul_comm, smul_mul_assoc]
    rw [hrhs] at hconj
    have hstep : (lam : ℝ) • (CFC.rpow σ (-(1/2)) * σ * CFC.rpow σ (-(1/2)))
        ≤ (lam : ℝ) • (1 : L ℋ) := by
      rw [← sub_nonneg, ← smul_sub]
      exact smul_nonneg hlam0 (sub_nonneg.mpr (rpow_neg_conj_self_le_one hσ))
    have hMle1 : M ≤ algebraMap ℝ (L ℋ) lam := by
      rw [Algebra.algebraMap_eq_smul_one]; exact le_trans hconj hstep
    exact (CStarAlgebra.norm_le_iff_le_algebraMap M hlam0 hMnn).mpr hMle1
  exact le_antisymm (csInf_le (maxRelSet_bddBelow ρ σ) hmem) (le_csInf ⟨‖M‖, hmem⟩ hlb)

/-- **Exponent-continuity of `CFC.rpow` at a possibly-singular operator**, along the
    sandwiched-Rényi exponent path `α ↦ (1-α)/(2α) → -1/2` as `α → ∞`. Valid even for
    singular `σ` (Moore–Penrose power): on the finite spectrum, the eigenvalue `0` stays
    pinned to `0` (the exponent is eventually negative), and positive eigenvalues move
    continuously. Proved by eigenbasis reconstruction. -/
lemma tendsto_rpow_exponent_atTop {σ : L ℋ} (hσ : 0 ≤ σ) :
    Filter.Tendsto (fun α : ℝ => CFC.rpow σ ((1 - α) / (2 * α))) Filter.atTop
      (nhds (CFC.rpow σ (-(1/2)))) := by
  classical
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hσ_pos : σ.IsPositive := (LinearMap.nonneg_iff_isPositive σ).mp hσ
  have hσ_sym : σ.IsSymmetric := hσ_pos.isSymmetric
  set b := hσ_sym.eigenvectorBasis hn with hb
  set eig := hσ_sym.eigenvalues hn with heig
  have h_eig_nn : ∀ i, 0 ≤ eig i := fun i => hσ_pos.nonneg_eigenvalues hn i
  have h_eig_apply : ∀ i, σ (b i) = ((eig i : ℝ) : ℂ) • b i := hσ_sym.apply_eigenvectorBasis hn
  have hb_ne : ∀ i, b i ≠ 0 := fun i => b.orthonormal.ne_zero i
  have hspec : ∀ i, eig i ∈ spectrum ℝ σ :=
    fun i => mem_spectrum_real_of_eigenvector (hb_ne i) (h_eig_apply i)
  have hβ : Filter.Tendsto (fun α : ℝ => (1 - α) / (2 * α)) Filter.atTop (𝓝 (-(1/2))) := by
    have heq : (fun α : ℝ => (1 - α) / (2 * α)) =ᶠ[Filter.atTop] (fun α => 1 / (2 * α) - 1/2) := by
      filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with α hα
      have hαne : α ≠ 0 := ne_of_gt hα
      field_simp
    rw [Filter.tendsto_congr' heq]
    have h2α : Filter.Tendsto (fun α : ℝ => 2 * α) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) Filter.tendsto_id
    have h0 : Filter.Tendsto (fun α : ℝ => 1 / (2 * α)) Filter.atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds h2α
    simpa using h0.sub_const (1/2)
  have key : ∀ i, Filter.Tendsto (fun α : ℝ => CFC.rpow σ ((1 - α) / (2 * α)) (b i)) Filter.atTop
      (𝓝 (CFC.rpow σ (-(1/2)) (b i))) := by
    intro i
    have hrw : ∀ s : ℝ, CFC.rpow σ s (b i) = (((eig i) ^ s : ℝ) : ℂ) • b i :=
      fun s => rpow_apply_eigenvector hσ s (h_eig_apply i) (hspec i)
    simp only [hrw]
    apply Filter.Tendsto.smul_const
    apply (Complex.continuous_ofReal.tendsto _).comp
    rcases eq_or_lt_of_le (h_eig_nn i) with h0 | hpos
    · rw [← h0, Real.zero_rpow (show (-(1/2):ℝ) ≠ 0 by norm_num)]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (1:ℝ)] with α hα
      have hne : (1 - α) / (2 * α) ≠ 0 :=
        ne_of_lt (div_neg_of_neg_of_pos (by linarith) (by positivity))
      rw [Real.zero_rpow hne]
    · exact ((Real.continuous_const_rpow (ne_of_gt hpos)).tendsto _).comp hβ
  have hrecon : CFC.rpow σ (-(1/2)) = ∑ i, outer_product (b i) (CFC.rpow σ (-(1/2)) (b i)) :=
    linearMap_eq_sum_outer_product b _
  have hfun : (fun α : ℝ => CFC.rpow σ ((1 - α) / (2 * α)))
      = (fun α => ∑ i, outer_product (b i) (CFC.rpow σ ((1 - α) / (2 * α)) (b i))) :=
    funext fun α => linearMap_eq_sum_outer_product b _
  rw [hrecon, hfun]
  apply tendsto_finset_sum
  intro i _
  exact ((continuous_outerL (b i)).tendsto _).comp (key i)

/-- `maxRelEntropyNN` unfolds to the Frank–Lieb operator-norm form on the `suppLE`
    region (definitional). -/
lemma maxRelEntropyNN_eq_log_norm {ρ σ : L ℋ} (hsupp : suppLE ρ σ) :
    maxRelEntropyNN ρ σ =
      ((Real.log ‖CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2))‖ : ℝ) : EReal) := by
  unfold maxRelEntropyNN; rw [if_pos hsupp]

/-- **Order-theoretic characterization** of the max-relative entropy on the `suppLE`
    region: `D_∞(ρ‖σ) = log inf{λ ≥ 0 : ρ ≤ λ σ}`. -/
lemma maxRelEntropyNN_eq_log_sInf {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : suppLE ρ σ) :
    maxRelEntropyNN ρ σ = ((Real.log (sInf (maxRelSet ρ σ)) : ℝ) : EReal) := by
  rw [maxRelEntropyNN_eq_log_norm hsupp, sInf_maxRelSet_eq_norm hρ hσ hsupp]

/-- **Data-processing inequality for the max-relative entropy** (`α = ∞`).
    For any CPTP map `E` and non-negative `ρ, σ`, `D_∞(E ρ ‖ E σ) ≤ D_∞(ρ ‖ σ)`.
    Proved through the order-theoretic characterization: `maxRelSet ρ σ ⊆ maxRelSet (Eρ)(Eσ)`
    (positivity of `E`), so the infimum decreases and `log` is monotone. -/
theorem maxRelEntropyNN_monotone
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    maxRelEntropyNN (E.toFun ρ) (E.toFun σ) ≤ maxRelEntropyNN ρ σ := by
  by_cases hsupp : suppLE ρ σ
  · -- support condition holds on both sides
    have hEsupp : suppLE (E.toFun ρ) (E.toFun σ) := suppLE_of_CPTP E hρ hσ hsupp
    have hEρ : (0 : L 𝒦) ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
    have hEσ : (0 : L 𝒦) ≤ E.toFun σ := map_nonneg E.toCompletelyPositiveMap hσ
    rw [maxRelEntropyNN_eq_log_sInf hEρ hEσ hEsupp, maxRelEntropyNN_eq_log_sInf hρ hσ hsupp,
      EReal.coe_le_coe_iff]
    by_cases hρ0 : ρ = 0
    · -- both infima are `0`, both logs are `0`
      have hEρ0 : E.toFun ρ = 0 := by
        rw [hρ0]; exact map_zero E.toCompletelyPositiveMap.toLinearMap
      rw [hEρ0, hρ0, maxRelSet_zero_left hEσ, maxRelSet_zero_left hσ]
    · -- ρ ≠ 0: both infima positive, use subset + log monotonicity
      have hEρ0 : E.toFun ρ ≠ 0 := CPTP_toFun_ne_zero E hρ hρ0
      have h_sub : maxRelSet ρ σ ⊆ maxRelSet (E.toFun ρ) (E.toFun σ) :=
        maxRelSet_subset_of_CPTP E
      have h_ne : (maxRelSet ρ σ).Nonempty := by
        obtain ⟨lam, hlam_pos, hlam_le⟩ := nonneg_le_smul_of_suppLE hρ hσ hsupp
        exact ⟨lam, hlam_pos.le, hlam_le⟩
      have h_inf_le : sInf (maxRelSet (E.toFun ρ) (E.toFun σ)) ≤ sInf (maxRelSet ρ σ) :=
        csInf_le_csInf (maxRelSet_bddBelow _ _) h_ne h_sub
      have h_pos_E : 0 < sInf (maxRelSet (E.toFun ρ) (E.toFun σ)) :=
        sInf_maxRelSet_pos hEρ hEσ hEρ0 hEsupp
      exact Real.log_le_log h_pos_E h_inf_le
  · -- support fails: RHS is ⊤
    have h_RHS : maxRelEntropyNN ρ σ = (⊤ : EReal) := by
      unfold maxRelEntropyNN; rw [if_neg hsupp]
    rw [h_RHS]; exact le_top

/-- **Theorem 1 (Frank–Lieb), `α = ∞`, paper form.** For a CPTP map `E` and
    non-negative `ρ, σ` with `suppLE ρ σ`,
    `log ‖(Eσ)^{-1/2} (Eρ) (Eσ)^{-1/2}‖ ≤ log ‖σ^{-1/2} ρ σ^{-1/2}‖`. -/
theorem maxRelEntropy_norm_monotone
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : suppLE ρ σ) :
    Real.log ‖CFC.rpow (E.toFun σ) (-(1/2)) * E.toFun ρ * CFC.rpow (E.toFun σ) (-(1/2))‖
      ≤ Real.log ‖CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2))‖ := by
  have hEρ : (0 : L 𝒦) ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
  have hEσ : (0 : L 𝒦) ≤ E.toFun σ := map_nonneg E.toCompletelyPositiveMap hσ
  have hEsupp : suppLE (E.toFun ρ) (E.toFun σ) := suppLE_of_CPTP E hρ hσ hsupp
  have hmono := maxRelEntropyNN_monotone E hρ hσ
  rw [maxRelEntropyNN_eq_log_norm hEsupp, maxRelEntropyNN_eq_log_norm hsupp,
    EReal.coe_le_coe_iff] at hmono
  exact hmono

end MaxRelEntropy

end SandwichedRenyiRelativeEntropy
