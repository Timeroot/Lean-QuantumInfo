/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.RenyiDPI.ReferenceOrder
public import QIT.Measurements.OverlapDomination

/-!
# Renyi offset from overlap domination

The sandwiched-Renyi offset produced by the measurement-overlap domination.
Given the Loewner-order domination `σ_small ≤ c · τ` (the matrix inequality of
`QIT.Measurements.OverlapDomination`), reference antitonicity shifts the
comparison by `-log₂ c`.

Source: Tomamichel2015FiniteResources, `apps.tex` lines 208-214 (the
overlap-domination step and the substitution into `eq:ur-proof1` toward
`eq:ucr-dual`).
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

namespace State

/-- The algebraic `-log₂ c` Renyi offset from overlap domination.

Given the Loewner-order domination `σ_small ≤ c · τ` and a hypothesis that the
sandwiched Renyi divergence is order-monotone in its (positive-definite)
reference argument, the reference comparison shifts by `-log₂ c`:

    D̃_α(ρ ‖ τ) - log₂ c ≤ D̃_α(ρ ‖ σ_small).

The scaling step uses `sandwichedRenyiReference_real_smul_reference`
(`Renyi.lean`), which yields `D̃_α(ρ ‖ c·τ) = D̃_α(ρ ‖ τ) - log₂ c`; combined
with the order-monotonicity hypothesis applied to `σ_small ≤ c·τ`, this is the
substitution step of `apps.tex:214`. This compatibility theorem retains the
former assumption-based surface; the canonical theorem below discharges the
reference-order step using `sandwichedRenyiReference_antitone_reference`. -/
theorem overlap_domination_renyi_offset_algebraicTarget
    (ρ : State a) (τ σ_small : CMatrix a)
    (hρ : ρ.matrix.PosDef) (hτ : τ.PosDef) (hσ_small : σ_small.PosDef)
    (c : ℝ) (hc : 0 < c)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1)
    (hdom : σ_small ≤ c • τ)
    (hmono : ∀ (σ σ' : CMatrix a) (hσ : σ.PosDef) (hσ' : σ'.PosDef),
       σ ≤ σ' →
         sandwichedRenyiReference ρ σ' hρ hσ' α hα_pos hα_ne_one ≤
           sandwichedRenyiReference ρ σ hρ hσ α hα_pos hα_ne_one) :
    sandwichedRenyiReference ρ τ hρ hτ α hα_pos hα_ne_one - log2 c ≤
      sandwichedRenyiReference ρ σ_small hρ hσ_small α hα_pos hα_ne_one := by
  have hτc : (c • τ).PosDef := Matrix.PosDef.smul hτ hc
  have hle :=
    hmono σ_small (c • τ) hσ_small hτc hdom
  rw [sandwichedRenyiReference_real_smul_reference ρ hρ hτ hc α hα_pos hα_ne_one]
    at hle
  exact hle

/-- The source `-log₂ c` Renyi offset from overlap domination, with reference
antitonicity discharged by the closed-order theorem. -/
theorem overlap_domination_renyi_offset
    (ρ : State a) (τ σ_small : CMatrix a)
    (hρ : ρ.matrix.PosDef) (hτ : τ.PosDef) (hσ_small : σ_small.PosDef)
    (c : ℝ) (hc : 0 < c)
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1)
    (hdom : σ_small ≤ c • τ) :
    sandwichedRenyiReference ρ τ hρ hτ α
        (lt_of_lt_of_le (by norm_num) hα_half) hα_ne_one - log2 c ≤
      sandwichedRenyiReference ρ σ_small hρ hσ_small α
        (lt_of_lt_of_le (by norm_num) hα_half) hα_ne_one := by
  have hτc : (c • τ).PosDef := Matrix.PosDef.smul hτ hc
  have hle := sandwichedRenyiReference_antitone_reference ρ hρ hσ_small hτc
    hdom hα_half hα_ne_one
  rw [sandwichedRenyiReference_real_smul_reference ρ hρ hτ hc α
      (lt_of_lt_of_le (by norm_num) hα_half) hα_ne_one] at hle
  exact hle

/-- Shape check at equality in the overlap domination. -/
example (ρ : State a) (τ : CMatrix a) (hρ : ρ.matrix.PosDef) (hτ : τ.PosDef)
    (c : ℝ) (hc : 0 < c) (α : ℝ) (hα_half : 1 / 2 ≤ α)
    (hα_ne_one : α ≠ 1) :
    sandwichedRenyiReference ρ τ hρ hτ α
        (lt_of_lt_of_le (by norm_num) hα_half) hα_ne_one - log2 c ≤
      sandwichedRenyiReference ρ (c • τ) hρ (Matrix.PosDef.smul hτ hc) α
        (lt_of_lt_of_le (by norm_num) hα_half) hα_ne_one := by
  have hτc : (c • τ).PosDef := Matrix.PosDef.smul hτ hc
  exact overlap_domination_renyi_offset ρ τ (c • τ) hρ hτ hτc c hc α hα_half
    hα_ne_one (le_refl _)

end State

end

end QIT
