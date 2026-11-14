/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder

/-!
# Operator convexity of `x ↦ x^p` on `[1, 2]`

This module adds the local Lean-QIT API for the mathlib TODO proving that
`a ↦ a ^ p` is operator convex for `p ∈ [1, 2]`. The proof follows the
existing integral representation in mathlib for `Real.rpowIntegrand₁₂`.
-/

@[expose] public section

open Set MeasureTheory
open scoped NNReal

namespace CFC

section UnitalCStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `rpowIntegrand₁₂ p t` is operator convex for every `0 < t`. -/
lemma convexOn_cfc_rpowIntegrand₁₂ {p t : ℝ} (ht : 0 < t) :
    ConvexOn ℝ (Ici (0 : A)) (cfc (Real.rpowIntegrand₁₂ p t)) := by
  have h₁ : (Ici (0 : A)).EqOn (cfc (Real.rpowIntegrand₁₂ p t))
      (fun x : A =>
        t ^ (p - 1) •
          (t⁻¹ • x + t • Ring.inverse (algebraMap ℝ A t + x) - 1)) := by
    intro x hx
    unfold Real.rpowIntegrand₁₂
    have hcont_inv : ContinuousOn (fun z : ℝ => (t + z)⁻¹) (spectrum ℝ x) := by
      fun_prop (disch := grind -abstractProof)
    have hspectrum : ∀ r ∈ spectrum ℝ x, t + r ≠ 0 := by grind
    rw [cfc_const_mul
      (t ^ (p - 1))
      (fun z : ℝ => t⁻¹ * z + t * (t + z)⁻¹ - 1) x
      (hf := by fun_prop (disch := grind -abstractProof))]
    rw [cfc_sub
      (f := fun z : ℝ => t⁻¹ * z + t * (t + z)⁻¹)
      (g := fun _ : ℝ => 1) (a := x)
      (hf := by fun_prop (disch := grind -abstractProof))
      (hg := by fun_prop)]
    rw [cfc_add
      (f := fun z : ℝ => t⁻¹ * z)
      (g := fun z : ℝ => t * (t + z)⁻¹) (a := x)
      (hf := by fun_prop)
      (hg := hcont_inv.const_mul t)]
    rw [cfc_const_mul_id (R := ℝ) t⁻¹ x (ha := hx.isSelfAdjoint)]
    rw [cfc_const_mul t (fun z : ℝ => (t + z)⁻¹) x (hf := hcont_inv)]
    rw [cfc_inv
      (fun z : ℝ => t + z) x hspectrum
      (hf := by fun_prop)
      (ha := hx.isSelfAdjoint)]
    rw [cfc_const_add t (fun z : ℝ => z) x
      (hf := by fun_prop)
      (ha := hx.isSelfAdjoint)]
    rw [cfc_id' (R := ℝ) (a := x) (ha := hx.isSelfAdjoint)]
    rw [cfc_const (R := ℝ) (A := A) 1 x (ha := hx.isSelfAdjoint)]
    simp [sub_eq_add_neg, smul_add]
  refine ConvexOn.congr ?_ h₁.symm
  refine ConvexOn.smul (by positivity) ?_
  refine ConvexOn.sub ?_ (concaveOn_const _ (convex_Ici _))
  refine ConvexOn.add ?_ ?_
  · simpa only [id_eq] using
      ConvexOn.smul (by positivity : 0 ≤ t⁻¹) (convexOn_id (convex_Ici (0 : A)))
  · exact ConvexOn.smul ht.le <| CStarAlgebra.convexOn_ringInverse_algebraMap_add ht

end UnitalCStarAlgebra

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Non-unital version of `CFC.convexOn_cfc_rpowIntegrand₁₂`. -/
lemma convexOn_cfcₙ_rpowIntegrand₁₂ {p t : ℝ} (ht : 0 < t) :
    ConvexOn ℝ (Ici (0 : A)) (cfcₙ (Real.rpowIntegrand₁₂ p t)) := by
  apply CStarAlgebra.convexOn_cfcₙ_of_convexOn_cfc
  refine ConvexOn.subset
    (convexOn_cfc_rpowIntegrand₁₂ (A := Unitization ℂ A) (p := p) (t := t) ht)
    CStarAlgebra.inr_map_Ici_zero ?_
  exact Convex.linear_image (convex_Ici _) (Unitization.inrHom ℝ ℂ A)

/-- The square map, written as `a ↦ a ^ (2 : ℝ≥0)`, is operator convex. -/
lemma convexOn_nnrpow_two :
    ConvexOn ℝ (Ici (0 : A)) (fun a : A => a ^ (2 : ℝ≥0)) := by
  refine ConvexOn.congr ?_ (fun a ha => (CFC.nnrpow_two a ha).symm)
  refine ⟨convex_Ici _, ?_⟩
  intro x hx y hy c d hc hd hcd
  rw [← sub_nonneg]
  have hsq : 0 ≤ (c * d) • ((x - y) * (x - y)) := by
    exact smul_nonneg (mul_nonneg hc hd)
      (hx.isSelfAdjoint.sub hy.isSelfAdjoint).mul_self_nonneg
  convert hsq using 1
  rw [show d = 1 - c by linarith]
  simp only [smul_sub, mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm]
  module

/-- Interior case of operator convexity for `a ↦ a ^ p`, proved from the integral representation. -/
private lemma convexOn_nnrpow_Ioo_one_two {p : ℝ≥0} (hp : p ∈ Ioo 1 2) :
    ConvexOn ℝ (Ici (0 : A)) (fun a : A => a ^ p) := by
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂ A hp
  have h₃' : (Ici 0).EqOn (fun a : A => a ^ p)
      (fun a : A => ∫ t in Ioi 0, cfcₙ (Real.rpowIntegrand₁₂ p t) a ∂μ) :=
    fun a ha => (hμ a ha).2
  refine ConvexOn.congr ?_ h₃'.symm
  refine integral_convexOn_of_integrand_ae (convex_Ici _) ?_ fun a ha => (hμ a ha).1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact convexOn_cfcₙ_rpowIntegrand₁₂ ht

/-- `a ↦ a ^ p` is operator convex for `p ∈ [1, 2]`. -/
lemma convexOn_nnrpow_one_two {p : ℝ≥0} (hp : p ∈ Icc 1 2) :
    ConvexOn ℝ (Ici (0 : A)) (fun a : A => a ^ p) := by
  have hIcc : Icc (1 : ℝ≥0) 2 = Ioo 1 2 ∪ {1} ∪ {2} := by ext; simp
  rw [hIcc] at hp
  obtain (hp | hp) | hp := hp
  · exact convexOn_nnrpow_Ioo_one_two hp
  · simp only [mem_singleton_iff] at hp
    simp only [hp]
    exact ConvexOn.congr (convexOn_id (convex_Ici _)) CFC.nnrpow_one_eqOn.symm
  · simp only [mem_singleton_iff] at hp
    simp only [hp]
    exact convexOn_nnrpow_two

end NonUnitalCStarAlgebra

section UnitalRpow

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `a ↦ a ^ p` is operator convex for real exponents `p ∈ [1, 2]`. -/
lemma convexOn_rpow_one_two {p : ℝ} (hp : p ∈ Icc 1 2) :
    ConvexOn ℝ (Ici (0 : A)) (fun a : A => a ^ p) := by
  let q : ℝ≥0 := ⟨p, le_trans (by norm_num : (0 : ℝ) ≤ 1) hp.1⟩
  change ConvexOn ℝ (Ici (0 : A)) (fun a : A => a ^ (q : ℝ))
  have hqpos : 0 < q := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hp.1
  simp_rw [← CFC.nnrpow_eq_rpow hqpos]
  exact convexOn_nnrpow_one_two hp

end UnitalRpow

end CFC
