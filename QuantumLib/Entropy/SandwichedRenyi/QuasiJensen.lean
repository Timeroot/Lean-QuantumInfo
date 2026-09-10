/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazumi Kasaura, Hayata Yamasaki
-/

import QuantumLib.Entropy.SandwichedRenyi.Defs
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Jensen–Haar inequality and monotonicity of the sandwiched Rényi divergence

This file proves the central Jensen-style inequality
(`sandwichedQuasi_jensen_haar`) underlying monotonicity of the sandwiched Rényi
divergence under CPTP maps, and the main monotonicity theorem
(`sandwichedRenyiDiv_monotone`).

The proof is structured in three layers:

1. `jensen_haar_core` — Frank–Lieb's central inequality before tensor
   multiplicativity collapses the LHS / RHS to `Re Q_α(E ρ‖E σ)` and
   `Re Q_α(ρ‖σ)`. Proved by passing to a closed convex sub-cone of `pdSet`
   cut out by explicit spectral bounds and applying Mathlib's Bochner-integral
   Jensen (`HaarUnitary.jointly_convex_integral_le` /
   `HaarUnitary.jointly_concave_le_integral`).

2. `sandwichedQuasi_jensen_haar` — the abstract Jensen–Haar interface, obtained
   from `jensen_haar_core` by tensor multiplicativity and the self-quasi
   identity `sandwichedQuasi α τ τ = Tr τ`.

3. `sandwichedRenyiDiv_monotone` — the main theorem
   `D_α(E ρ ‖ E σ) ≤ D_α(ρ ‖ σ)`, obtained from `sandwichedQuasi_jensen_haar`
   by applying the Stinespring dilation (`CPTPOp.exists_stinespring_dilation`)
   and the monotonic log transform.

The closed sub-cone construction in layer 1 uses
`CFC.exists_pos_algebraMap_le_iff` for the lower bound (positive spectrum gives
`∃ ε > 0, ε • 1 ≤ A`) and operator-norm bounds for the upper bound.
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory HaarUnitary TensorProduct
open GeneralizedPerspectiveFunction
open scoped ComplexOrder NNReal Topology

universe u


/-! ### Spectral bounds for operators in `pdSet` -/

/-- For any `A ∈ pdSet`, there exists a positive real `ε` such that `ε • 1 ≤ A`. -/
private lemma pdSet_exists_pos_lower_bound {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : A ∈ pdSet (ℋ := ℋ)) :
    ∃ ε : ℝ, 0 < ε ∧ (ε • (1 : L ℋ) : L ℋ) ≤ A := by
  obtain ⟨hA_sa, hA_spec⟩ := hA
  obtain ⟨r, hr_pos, hr_le⟩ : ∃ r > 0, algebraMap ℝ (L ℋ) r ≤ A :=
    (CFC.exists_pos_algebraMap_le_iff hA_sa).mpr fun _x hx => hA_spec hx
  refine ⟨r, hr_pos, ?_⟩
  rwa [Algebra.algebraMap_eq_smul_one] at hr_le

/-- For any self-adjoint element `A` in a `CStarAlgebra` of operators on a
    finite-dim Hilbert space, there exists `M` such that `A ≤ M • 1`
    (we may take `M = ‖A‖`). -/
private lemma exists_upper_bound_self_adjoint {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : IsSelfAdjoint A) :
    ∃ M : ℝ, A ≤ (M • (1 : L ℋ) : L ℋ) := by
  refine ⟨‖A‖, ?_⟩
  rw [show (‖A‖ • (1 : L ℋ) : L ℋ) = algebraMap ℝ (L ℋ) ‖A‖ from
    (Algebra.algebraMap_eq_smul_one ‖A‖).symm]
  exact hA.le_algebraMap_norm_self

/-! ### The closed convex sub-cone -/

/-- The closed convex sub-cone of `L ℋ` cut out by `ε • 1 ≤ A ≤ M • 1`. -/
private def pdSubCone {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (ε M : ℝ) : Set (L ℋ) :=
  {A | ε • (1 : L ℋ) ≤ A ∧ A ≤ M • (1 : L ℋ)}

/-- `star (1 ⊗ g) = 1 ⊗ (star g)` for the right tensor factor. -/
private lemma tensorMap_right_star {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]
    (g : L ℋ₂) :
    star (TensorProduct.mapL (1 : L ℋ₁) g : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      TensorProduct.mapL (1 : L ℋ₁) (star g) := by
  rw [ContinuousLinearMap.star_eq_adjoint, TensorProduct.adjoint_mapL,
    ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint, star_one]

/-- For unitary `u : L ℋ₂`, `TensorProduct.mapL 1 u` is unitary on `L (ℋ₁ ⊗[ℂ] ℋ₂)`. -/
private lemma tensorMap_right_unitary_of_unitary
    {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂] [Nontrivial ℋ₁] [Nontrivial ℋ₂]
    (u : unitary (L ℋ₂)) :
    TensorProduct.mapL (1 : L ℋ₁) ((u : L ℋ₂)) ∈ unitary (L (ℋ₁ ⊗[ℂ] ℋ₂)) := by
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
  · rw [tensorMap_right_star, ← TensorProduct.mapL_mul, one_mul,
      (Unitary.mem_iff.mp u.property).1]
    exact TensorProduct.mapL_id_id
  · rw [tensorMap_right_star, ← TensorProduct.mapL_mul, one_mul,
      (Unitary.mem_iff.mp u.property).2]
    exact TensorProduct.mapL_id_id

/-- The non-negative cone `{A | 0 ≤ A}` in `L 𝒦` is convex: it is `Ici 0`. -/
private lemma convex_nonneg_cone {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] :
    Convex ℝ {A : L 𝒦 | (0 : L 𝒦) ≤ A} :=
  convex_Ici 0

/-- The non-negative cone `{A | 0 ≤ A}` in `L 𝒦` is closed: it is `Ici 0`. -/
private lemma isClosed_nonneg_cone {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] :
    IsClosed {A : L 𝒦 | (0 : L 𝒦) ≤ A} :=
  isClosed_Ici

/-- The sub-cone is contained in `pdSet` when `ε > 0`. -/
private lemma pdSubCone_subset_pdSet {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {ε M : ℝ} (hε : 0 < ε) : pdSubCone (ℋ := ℋ) ε M ⊆ pdSet (ℋ := ℋ) := by
  intro A ⟨h_lower, _⟩
  -- `ε • 1 = algebraMap ℝ _ ε`, and `algebraMap ε ≤ A` gives both self-adjointness
  -- (via positivity) and the spectrum bound.
  have h_eq : ε • (1 : L ℋ) = algebraMap ℝ (L ℋ) ε := by
    rw [Algebra.algebraMap_eq_smul_one]
  rw [h_eq] at h_lower
  have h_pos_1 : (0 : L ℋ) ≤ algebraMap ℝ (L ℋ) ε := by
    rw [← h_eq]
    exact smul_nonneg hε.le zero_le_one
  have hA_sa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg (le_trans h_pos_1 h_lower)
  refine ⟨hA_sa, fun r hr ↦ ?_⟩
  exact lt_of_lt_of_le hε ((algebraMap_le_iff_le_spectrum (R := ℝ) (ha := hA_sa)).mp h_lower r hr)

/-! ### Helper lemmas for the Form A Jensen–Haar proof -/

/-- **Non-unital ⋆-algebra hom** `σ ↦ V σ V*` for an isometric `V` (`V*V = 1`).
    This is multiplicative because of `V*V = 1`, and `*`-preserving in general.
    It is non-unital because `1 ↦ V V* ≠ 1` when `V` is not surjective. -/
private noncomputable def isometricConjHom
    {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →L[ℂ] ℋ') (hV : (V†).comp V = (1 : L ℋ)) :
    L ℋ →⋆ₙₐ[ℂ] L ℋ' where
  toFun σ := (V.comp σ).comp (V†)
  map_add' σ τ := by
    ext x
    simp
  map_smul' c σ := by
    ext x
    simp
  map_zero' := by
    ext x
    simp
  map_mul' σ τ := by
    have h_id : ∀ y : ℋ, (V†) (V y) = y := fun y ↦ by
      simpa using DFunLike.congr_fun hV y
    ext x
    simp [h_id]
  map_star' σ := by
    simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
    ext x
    rfl

/-- The isometric-conjugation map `σ ↦ V σ V*` as a *linear* map; this captures the
    underlying linear structure separately from the `NonUnitalStarAlgHom`. -/
private noncomputable def isometricConjLM
    {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →L[ℂ] ℋ') : L ℋ →ₗ[ℂ] L ℋ' where
  toFun σ := (V.comp σ).comp (V†)
  map_add' σ τ := by
    ext x
    simp
  map_smul' c σ := by
    ext x
    simp

/-- Continuity of the isometric-conjugation map (needed to apply `map_cfcₙ`).
    Follows from `continuous_of_finiteDimensional` on the underlying linear map. -/
private lemma isometricConjHom_continuous
    {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →L[ℂ] ℋ') (hV : (V†).comp V = (1 : L ℋ)) :
    Continuous (isometricConjHom V hV) := by
  have h_coe : (isometricConjHom V hV : L ℋ → L ℋ') = isometricConjLM V := rfl
  rw [h_coe]
  exact (isometricConjLM V).continuous_of_finiteDimensional

/-- **Isometric `rpow` covariance.** For an isometry `V` with `V*V = 1`, a non-negative
    `ω`, and any *nonzero* real `p`: `(V ω V*)^p = V (ω^p) V*`. This is valid even for
    `p < 0`: the function `x ↦ x ^ p` is globally discontinuous at `0`, but the
    quasispectrum of any operator here is finite (so `0` is isolated), hence the function
    is `ContinuousOn` it and the non-unital ⋆-hom naturality `map_cfcₙ` applies. -/
private lemma isometricConj_rpow {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →L[ℂ] ℋ') (hV : (V†).comp V = (1 : L ℋ))
    {ω : L ℋ} (hω : (0 : L ℋ) ≤ ω) {p : ℝ} (hp : p ≠ 0) :
    CFC.rpow ((V.comp ω).comp (V†)) p = (V.comp (CFC.rpow ω p)).comp (V†) := by
  set φ : L ℋ →⋆ₙₐ[ℂ] L ℋ' := isometricConjHom V hV with hφ_def
  have hφ_cont : Continuous φ := isometricConjHom_continuous V hV
  have hφ_apply : ∀ ν : L ℋ, φ ν = (V.comp ν).comp (V†) := fun _ => rfl
  have hφ_nn : (0 : L ℋ') ≤ φ ω := by
    rw [hφ_apply, ContinuousLinearMap.nonneg_iff_isPositive]
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hω).conj_adjoint V
  let f : ℝ → ℝ := fun x => x ^ p
  have hf_zero : f 0 = 0 := by simp [f, Real.zero_rpow hp]
  have h_Vω_eq : φ ω = (V.comp ω).comp (V†) := hφ_apply ω
  have h_rpow_eq_ω : CFC.rpow ω p = cfc f ω := CFC.rpow_eq_cfc_real (ha := hω)
  have h_rpow_eq_Vω : CFC.rpow ((V.comp ω).comp (V†)) p =
      cfc f ((V.comp ω).comp (V†)) := by
    have := CFC.rpow_eq_cfc_real (a := φ ω) (y := p) (ha := hφ_nn)
    rw [h_Vω_eq] at this
    exact this
  rw [h_rpow_eq_ω, h_rpow_eq_Vω]
  have hcont_ω : ContinuousOn f (quasispectrum ℝ ω) := (finite_quasispectrum_real ω).continuousOn _
  have hcont_Vω : ContinuousOn f (quasispectrum ℝ (φ ω)) :=
    (finite_quasispectrum_real (φ ω)).continuousOn _
  have h_cfcₙ_eq_ω : cfcₙ f ω = cfc f ω := cfcₙ_eq_cfc hcont_ω hf_zero
  have h_cfcₙ_eq_Vω : cfcₙ f (φ ω) = cfc f (φ ω) := cfcₙ_eq_cfc hcont_Vω hf_zero
  have h_map : φ (cfcₙ f ω) = cfcₙ f (φ ω) :=
    NonUnitalStarAlgHomClass.map_cfcₙ (S := ℂ) φ f ω hcont_ω hf_zero hφ_cont
      (IsSelfAdjoint.of_nonneg hω) (IsSelfAdjoint.of_nonneg hφ_nn)
  change cfc f ((V.comp ω).comp (V†)) = (V.comp (cfc f ω)).comp (V†)
  rw [← h_Vω_eq, ← h_cfcₙ_eq_Vω, ← h_map, h_cfcₙ_eq_ω, hφ_apply]

/-- **Isometric invariance of sandwichedQuasi** (valid for all `α > 0`, `α ≠ 1`).

    For an isometry `V : ℋ →L[ℂ] ℋ'` with `V*V = I` and `ρ, σ ≥ 0`,
    `sandwichedQuasi α (V ρ V*) (V σ V*) = sandwichedQuasi α ρ σ`.

    **No convention obstruction in finite dimensions.** Even for `α > 1`, where
    `β = (1 − α) / (2 α) < 0`, the identity still holds: `CFC.rpow (V σ V*) β`
    does *not* collapse to `0`. The function `x ↦ x ^ β` is discontinuous at `0`
    on `ℝ`, but the *quasispectrum* of `V σ V*` is finite (so `0` is an isolated
    point), hence `x ↦ x ^ β` is `ContinuousOn` it and the non-unital ⋆-hom
    naturality `NonUnitalStarAlgHomClass.map_cfcₙ` — which requires only
    `ContinuousOn` over the quasispectrum, not global continuity — applies. The
    result is the support-restricted `V σ^β V*`, exactly as in the `α < 1` case. -/
private lemma sandwichedQuasi_isometric_conj
    {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →L[ℂ] ℋ') (hV : (V†).comp V = (1 : L ℋ))
    {α : ℝ} (hα0 : 0 < α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : (0 : L ℋ) ≤ ρ) (hσ : (0 : L ℋ) ≤ σ) :
    sandwichedQuasi α ((V.comp ρ).comp (V†)) ((V.comp σ).comp (V†)) =
      sandwichedQuasi α ρ σ := by
  set φ : L ℋ →⋆ₙₐ[ℂ] L ℋ' := isometricConjHom V hV with hφ_def
  have hφ_apply : ∀ ω : L ℋ, φ ω = (V.comp ω).comp (V†) := fun _ => rfl
  -- Cyclic trace identity `Tr (V X V*) = Tr X`, using `V* V = 1`.
  have h_tr_conj : ∀ X : L ℋ, Tr ((V.comp X).comp (V†)) = Tr X := fun X ↦ by
    have h : Tr ((V.comp X).comp (V†)) = Tr (X * ((V†).comp V)) :=
      LinearMap.trace_comp_comm' ((X ∘L V† : ℋ' →L[ℂ] ℋ) : ℋ' →ₗ[ℂ] ℋ)
        ((V : ℋ →L[ℂ] ℋ') : ℋ →ₗ[ℂ] ℋ')
    rw [h, hV, mul_one]
  unfold sandwichedQuasi
  set β := (1 - α) / (2 * α) with hβ_def
  have hβ_ne : β ≠ 0 := by
    rw [hβ_def]
    exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hα_ne1)) (by positivity)
  -- Step 1: `(V σ V*)^β = V (σ^β) V*`.
  rw [isometricConj_rpow V hV hσ hβ_ne]
  -- Step 2: `(V σ^β V*)(V ρ V*)(V σ^β V*) = V (σ^β ρ σ^β) V*`, by multiplicativity of `φ`.
  have h_inner : (V.comp (CFC.rpow σ β)).comp (V†) * (V.comp ρ).comp (V†) *
      (V.comp (CFC.rpow σ β)).comp (V†) =
      (V.comp (CFC.rpow σ β * ρ * CFC.rpow σ β)).comp (V†) := by
    have hX : φ (CFC.rpow σ β) * φ ρ * φ (CFC.rpow σ β) =
        φ (CFC.rpow σ β * ρ * CFC.rpow σ β) := by
      rw [map_mul φ, map_mul φ]
    simpa only [hφ_apply] using hX
  rw [h_inner]
  -- Step 3: `(V Y V*)^α = V (Y^α) V*` for `Y = σ^β ρ σ^β ≥ 0`, then take traces.
  have h_inner_nn : (0 : L ℋ) ≤ CFC.rpow σ β * ρ * CFC.rpow σ β := by
    have hP_sa : IsSelfAdjoint (CFC.rpow σ β) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    have h := star_left_conjugate_nonneg hρ (CFC.rpow σ β)
    rwa [hP_sa.star_eq] at h
  rw [isometricConj_rpow V hV h_inner_nn (ne_of_gt hα0)]
  exact h_tr_conj _

/-- **Isometric covariance of the variational functional `quasiVar`** (all `α > 0`,
    `α ≠ 1`). For an isometry `V` (`V*V = 1`), nonneg `σ`, nonneg `G`,
    `quasiVar α (V ρ V*) (V σ V*) G = quasiVar α ρ σ (V* G V)`.

    All `CFC.rpow` exponents appearing (`(α−1)/(2α)` and `α/(α−1)`) are nonzero, so
    `isometricConj_rpow` applies; the inner sandwich identity
    `(V σ^c V*) G (V σ^c V*) = V (σ^c (V* G V) σ^c) V*` is pure associativity. -/
private lemma quasiVar_isometric_conj {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →L[ℂ] ℋ') (hV : (V†).comp V = (1 : L ℋ))
    {α : ℝ} (hα0 : 0 < α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hσ : (0 : L ℋ) ≤ σ) {G : L ℋ'} (hG : (0 : L ℋ') ≤ G) :
    quasiVar α ((V.comp ρ).comp (V†)) ((V.comp σ).comp (V†)) G =
      quasiVar α ρ σ ((V†).comp (G.comp V)) := by
  set GV : L ℋ := (V†).comp (G.comp V) with hGV_def
  set c : ℝ := (α - 1) / (2 * α) with hc_def
  set q : ℝ := α / (α - 1) with hq_def
  have hc_ne : c ≠ 0 := div_ne_zero (sub_ne_zero.mpr hα_ne1) (by positivity)
  have hq_ne : q ≠ 0 := div_ne_zero (ne_of_gt hα0) (sub_ne_zero.mpr hα_ne1)
  -- `GV = V* G V ≥ 0` (conjugation of `G ≥ 0` by the adjoint of `V`).
  have hGV_nn : (0 : L ℋ) ≤ GV := by
    rw [hGV_def, ContinuousLinearMap.nonneg_iff_isPositive]
    have h := ((ContinuousLinearMap.nonneg_iff_isPositive G).mp hG).conj_adjoint (V†)
    rw [ContinuousLinearMap.adjoint_adjoint] at h
    exact h
  -- Cyclic trace identity `Tr (V X V*) = Tr X`.
  have h_tr_conj : ∀ X : L ℋ, Tr ((V.comp X).comp (V†)) = Tr X := fun X ↦ by
    have h : Tr ((V.comp X).comp (V†)) = Tr (X * ((V†).comp V)) :=
      LinearMap.trace_comp_comm' ((X ∘L V† : ℋ' →L[ℂ] ℋ) : ℋ' →ₗ[ℂ] ℋ)
        ((V : ℋ →L[ℂ] ℋ') : ℋ →ₗ[ℂ] ℋ')
    rw [h, hV, mul_one]
  -- Term 1: `Tr (G * V ρ V*) = Tr (GV * ρ)`.
  have hterm1 : Tr (G * (V.comp ρ).comp (V†)) = Tr (GV * ρ) := by
    have h : Tr (G * (V.comp ρ).comp (V†)) = Tr (ρ * GV) := by
      rw [hGV_def]
      exact LinearMap.trace_comp_comm' ((ρ ∘L V† : ℋ' →L[ℂ] ℋ) : ℋ' →ₗ[ℂ] ℋ)
        ((G ∘L V : ℋ →L[ℂ] ℋ') : ℋ →ₗ[ℂ] ℋ')
    rw [h, Tr_mul_comm]
  -- Inner sandwich identity (pure associativity): `(Vσ^cV*) G (Vσ^cV*) = V (σ^c GV σ^c) V*`.
  have hinner : ((V.comp (CFC.rpow σ c)).comp (V†)) * G *
      ((V.comp (CFC.rpow σ c)).comp (V†)) =
      (V.comp (CFC.rpow σ c * GV * CFC.rpow σ c)).comp (V†) := by
    rw [hGV_def]
    exact ContinuousLinearMap.ext fun x ↦ rfl
  -- `σ^c (V* G V) σ^c ≥ 0` (conjugation of `GV ≥ 0` by self-adjoint `σ^c`).
  have hY_nn : (0 : L ℋ) ≤ CFC.rpow σ c * GV * CFC.rpow σ c := by
    have hP_sa : IsSelfAdjoint (CFC.rpow σ c) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    have h := star_left_conjugate_nonneg hGV_nn (CFC.rpow σ c)
    rwa [hP_sa.star_eq] at h
  unfold quasiVar
  rw [← hc_def, ← hq_def, isometricConj_rpow V hV hσ hc_ne, hinner,
      isometricConj_rpow V hV hY_nn hq_ne, h_tr_conj, hterm1]

/-! ### Positive-definite perturbations `A + ε • 1` (used for the cone arguments) -/

/-- Sum of non-negative and positive-definite is positive-definite. -/
lemma pdSet_add_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A B : L ℋ} (hA : 0 ≤ A) (hB : B ∈ pdSet (ℋ := ℋ)) :
    (A + B) ∈ pdSet (ℋ := ℋ) := by
  obtain ⟨εB, hεB_pos, hεB_le⟩ := pdSet_exists_pos_lower_bound hB
  obtain ⟨MA, hMA_le⟩ := exists_upper_bound_self_adjoint (IsSelfAdjoint.of_nonneg hA)
  obtain ⟨MB, hMB_le⟩ := exists_upper_bound_self_adjoint hB.1
  refine pdSubCone_subset_pdSet (ℋ := ℋ) hεB_pos (M := MA + MB) ⟨?_, ?_⟩
  · rw [show εB • (1 : L ℋ) = (0 : L ℋ) + εB • (1 : L ℋ) from (zero_add _).symm]
    exact add_le_add hA hεB_le
  · rw [add_smul]
    exact add_le_add hMA_le hMB_le

/-- The scalar operator `ε • 1` is positive-definite for `ε > 0` real. -/
lemma pos_smul_one_pdSet
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {ε : ℝ} (hε : 0 < ε) :
    ((ε : ℂ) • (1 : L ℋ)) ∈ pdSet (ℋ := ℋ) := by
  have hε_ne : (ε : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hε
  refine mem_pdSet_of_nonneg_of_isUnit
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (ContinuousLinearMap.isPositive_one.smul_of_nonneg
        (Complex.zero_le_real.mpr hε.le))) ?_
  -- `ε • 1` is a unit, with inverse `ε⁻¹ • 1`.
  refine ⟨⟨(ε : ℂ) • 1, ((ε : ℂ))⁻¹ • 1, ?_, ?_⟩, rfl⟩
  · rw [smul_mul_smul_comm, mul_inv_cancel₀ hε_ne, mul_one, one_smul]
  · rw [smul_mul_smul_comm, inv_mul_cancel₀ hε_ne, mul_one, one_smul]

/-- For non-negative `A` and `ε > 0`, the perturbation `A + ε • 1` is pd. -/
lemma nonneg_add_pos_smul_one_pdSet
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) {ε : ℝ} (hε : 0 < ε) :
    (A + (ε : ℂ) • (1 : L ℋ)) ∈ pdSet (ℋ := ℋ) :=
  pdSet_add_nonneg hA (pos_smul_one_pdSet hε)

/-! ### Continuity / concavity of `Re Q_α` on the non-negative cone (`α < 1`) -/

/-- For `0 ≤ p`, the map `A ↦ CFC.rpow A p` is continuous on the cone of non-negative
    operators. (A positive power `x ↦ x^p` is continuous up to `0` in `ℝ≥0`, so unlike the
    `pdSet` version no spectral gap away from `0` is required.) -/
lemma rpow_continuousOn_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {p : ℝ} (hp : 0 ≤ p) :
    ContinuousOn (fun A : L 𝒦 => CFC.rpow A p) {A : L 𝒦 | (0 : L 𝒦) ≤ A} :=
  (continuousOn_id (s := {A : L 𝒦 | (0 : L 𝒦) ≤ A})).cfc_nnreal_of_mem_nhdsSet
    (s := Set.univ) (f := (· ^ p)) Filter.univ_mem (ha' := fun _ hA => hA)
    (hf := (NNReal.continuous_rpow_const hp).continuousOn)

/-- For `0 < α ≤ 1`, the real part of `sandwichedQuasi` is jointly continuous on the
    non-negative cone. Both exponents `β = (1-α)/(2α)` and `α` are non-negative, so every
    `CFC.rpow` in the definition is continuous up to the boundary of the cone. -/
lemma sandwichedQuasi_re_continuousOn_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ContinuousOn (Function.uncurry (fun (ρ σ : L 𝒦) => (sandwichedQuasi α ρ σ).re))
      ({A : L 𝒦 | (0 : L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0 : L 𝒦) ≤ A}) := by
  set β : ℝ := (1 - α) / (2 * α) with hβ
  have hβ_nn : 0 ≤ β := div_nonneg (by linarith) (by linarith)
  set S : Set (L 𝒦) := {A : L 𝒦 | (0 : L 𝒦) ≤ A} with hS
  have h_rpow_snd : ContinuousOn (fun p : L 𝒦 × L 𝒦 => CFC.rpow p.2 β) (S ×ˢ S) :=
    (rpow_continuousOn_nonneg hβ_nn).comp continuousOn_snd (fun _ hx => (Set.mem_prod.mp hx).2)
  have h_fst : ContinuousOn (fun p : L 𝒦 × L 𝒦 => p.1) (S ×ˢ S) := continuousOn_fst
  have h_inner_cont :
      ContinuousOn (fun p : L 𝒦 × L 𝒦 => CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β) (S ×ˢ S) :=
    (h_rpow_snd.mul h_fst).mul h_rpow_snd
  have h_inner_nn : ∀ p ∈ S ×ˢ S, (0 : L 𝒦) ≤ CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β := by
    rintro ⟨ρ, σ⟩ ⟨hρ, _hσ⟩
    have hP_sa : IsSelfAdjoint (CFC.rpow σ β) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    have h := star_left_conjugate_nonneg hρ (CFC.rpow σ β)
    rwa [hP_sa.star_eq] at h
  have h_pow_cont :
      ContinuousOn (fun p : L 𝒦 × L 𝒦 => CFC.rpow (CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β) α)
        (S ×ˢ S) :=
    h_inner_cont.cfc_nnreal_of_mem_nhdsSet (s := Set.univ) (f := (· ^ α))
      Filter.univ_mem (ha' := h_inner_nn)
      (hf := (NNReal.continuous_rpow_const hα0.le).continuousOn)
  have h_trace_cont : Continuous (fun A : L 𝒦 => Tr A) :=
    LinearMap.continuous_of_finiteDimensional _
  exact Complex.continuous_re.comp_continuousOn (h_trace_cont.comp_continuousOn h_pow_cont)

/-- For `α > 1` and a fixed non-negative `H`, the real part of the variational functional
    `quasiVar α ρ σ H` is jointly continuous on the non-negative cone. The `σ`-exponents
    `(α-1)/(2α)` and `α/(α-1)` are both positive (continuous up to the cone boundary), and
    the `ρ`-term `α (Tr (H ρ))` is linear hence continuous everywhere. -/
private lemma quasiVar_re_continuousOn_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {α : ℝ} (hα : 1 < α) {H : L 𝒦} (hH : (0 : L 𝒦) ≤ H) :
    ContinuousOn (Function.uncurry (fun (ρ σ : L 𝒦) => (quasiVar α ρ σ H).re))
      ({A : L 𝒦 | (0 : L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0 : L 𝒦) ≤ A}) := by
  set c : ℝ := (α - 1) / (2 * α) with hc
  have hc_nn : 0 ≤ c := le_of_lt (div_pos (by linarith) (by linarith))
  set q : ℝ := α / (α - 1) with hq
  have hq_nn : 0 ≤ q := le_of_lt (div_pos (by linarith) (by linarith))
  set S : Set (L 𝒦) := {A : L 𝒦 | (0 : L 𝒦) ≤ A} with hS
  -- `ρ`-term `(Tr (H * ρ)).re`, continuous everywhere.
  have hTr : Continuous (fun A : L 𝒦 => Tr A) := LinearMap.continuous_of_finiteDimensional _
  have h_rho : Continuous (fun p : L 𝒦 × L 𝒦 => (Tr (H * p.1)).re) :=
    Complex.continuous_re.comp (hTr.comp (continuous_const.mul continuous_fst))
  -- `σ`-term `(Tr ((σ^c H σ^c)^q)).re`, continuous on the cone.
  have h_rpow_snd : ContinuousOn (fun p : L 𝒦 × L 𝒦 => CFC.rpow p.2 c) (S ×ˢ S) :=
    (rpow_continuousOn_nonneg hc_nn).comp continuousOn_snd (fun _ hx => (Set.mem_prod.mp hx).2)
  have h_inner_cont :
      ContinuousOn (fun p : L 𝒦 × L 𝒦 => CFC.rpow p.2 c * H * CFC.rpow p.2 c) (S ×ˢ S) :=
    (h_rpow_snd.mul continuousOn_const).mul h_rpow_snd
  have h_inner_nn : ∀ p ∈ S ×ˢ S, (0 : L 𝒦) ≤ CFC.rpow p.2 c * H * CFC.rpow p.2 c := by
    rintro ⟨ρ, σ⟩ _
    have hP_sa : IsSelfAdjoint (CFC.rpow σ c) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    have h := star_left_conjugate_nonneg hH (CFC.rpow σ c)
    rwa [hP_sa.star_eq] at h
  have h_pow_cont :
      ContinuousOn (fun p : L 𝒦 × L 𝒦 => CFC.rpow (CFC.rpow p.2 c * H * CFC.rpow p.2 c) q)
        (S ×ˢ S) :=
    h_inner_cont.cfc_nnreal_of_mem_nhdsSet (s := Set.univ) (f := (· ^ q))
      Filter.univ_mem (ha' := h_inner_nn)
      (hf := (NNReal.continuous_rpow_const hq_nn).continuousOn)
  have h_sigma :
      ContinuousOn (fun p : L 𝒦 × L 𝒦 =>
        (Tr (CFC.rpow (CFC.rpow p.2 c * H * CFC.rpow p.2 c) q)).re) (S ×ˢ S) :=
    Complex.continuous_re.comp_continuousOn (hTr.comp_continuousOn h_pow_cont)
  -- Combine: `Re quasiVar = α (Tr Hρ).re − (α−1) (σ-term).re`.
  have h_eq : (Function.uncurry (fun (ρ σ : L 𝒦) => (quasiVar α ρ σ H).re)) =
      fun p : L 𝒦 × L 𝒦 => α * (Tr (H * p.1)).re -
        (α - 1) * (Tr (CFC.rpow (CFC.rpow p.2 c * H * CFC.rpow p.2 c) q)).re := by
    funext p
    obtain ⟨ρ, σ⟩ := p
    change (quasiVar α ρ σ H).re = _
    unfold quasiVar
    rw [← hc, ← hq, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  rw [h_eq]
  exact (continuous_const.mul h_rho).continuousOn.sub (continuousOn_const.mul h_sigma)

section JointlyConvexNonneg
attribute [local irreducible] quasiVar

/-- Joint convexity of `(ρ, σ) ↦ Re quasiVar α ρ σ H` extends from `pdSet` to the whole
    non-negative cone (fixed pd `H`, `α > 1`), by the same `ε → 0⁺` perturbation + joint
    continuity (`quasiVar_re_continuousOn_nonneg`) argument as the concave case. -/
private lemma quasiVar_re_jointlyConvex_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {α : ℝ} (hα : 1 < α) {H : L 𝒦} (hH : H ∈ pdSet (ℋ := 𝒦)) :
    JointlyConvexOn {A : L 𝒦 | (0 : L 𝒦) ≤ A} {A : L 𝒦 | (0 : L 𝒦) ≤ A}
      (fun ρ σ => (quasiVar (ℋ := 𝒦) α ρ σ H).re) := by
  have hcont := quasiVar_re_continuousOn_nonneg (𝒦 := 𝒦) hα (nonneg_of_pdSet hH)
  have hpd := quasiVar_re_jointlyConvex_pdSet (ℋ := 𝒦) hα hH
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [Set.mem_ofPred_eq] at hρ₁ hρ₂ hσ₁ hσ₂
  have key : ∀ a b : L 𝒦, (0 : L 𝒦) ≤ a → (0 : L 𝒦) ≤ b →
      Filter.Tendsto
        (fun ε : ℝ => (quasiVar α (a + (ε : ℂ) • 1) (b + (ε : ℂ) • 1) H).re)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (quasiVar α a b H).re) := by
    intro a b ha hb
    have hcurve : Continuous (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1)) := by fun_prop
    have h_into : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1) ∈
          ({A : L 𝒦 | (0 : L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0 : L 𝒦) ≤ A}) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      have hsmul : (0 : L 𝒦) ≤ (ε : ℂ) • (1 : L 𝒦) :=
        nonneg_of_pdSet (pos_smul_one_pdSet hε')
      exact ⟨by simpa using add_nonneg ha hsmul, by simpa using add_nonneg hb hsmul⟩
    have h_tendsto_curve :
        Filter.Tendsto (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhdsWithin (a, b) ({A : L 𝒦 | (0:L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0:L 𝒦) ≤ A})) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, h_into⟩
      have h0 : Filter.Tendsto (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1))
          (nhds (0 : ℝ)) (nhds (a, b)) := by
        have h := hcurve.tendsto 0
        simpa using h
      exact h0.mono_left nhdsWithin_le_nhds
    have hcwa : Filter.Tendsto
        (Function.uncurry (fun ρ σ : L 𝒦 => (quasiVar α ρ σ H).re))
        (nhdsWithin (a, b) ({A : L 𝒦 | (0:L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0:L 𝒦) ≤ A}))
        (nhds (quasiVar α a b H).re) :=
      hcont (a, b) ⟨ha, hb⟩
    exact hcwa.comp h_tendsto_curve
  have hρc : (0 : L 𝒦) ≤ (1 - θ) • ρ₁ + θ • ρ₂ :=
    add_nonneg (smul_nonneg (by linarith) hρ₁) (smul_nonneg hθ0 hρ₂)
  have hσc : (0 : L 𝒦) ≤ (1 - θ) • σ₁ + θ • σ₂ :=
    add_nonneg (smul_nonneg (by linarith) hσ₁) (smul_nonneg hθ0 hσ₂)
  have hcombo : ∀ a₁ a₂ : L 𝒦, ∀ ε : ℝ,
      ((1 - θ) • a₁ + θ • a₂) + (ε : ℂ) • 1 =
        (1 - θ) • (a₁ + (ε : ℂ) • 1) + θ • (a₂ + (ε : ℂ) • 1) := by
    intro a₁ a₂ ε
    have h1 : ((1 - θ : ℝ)) • ((ε : ℂ) • (1 : L 𝒦)) + (θ : ℝ) • ((ε : ℂ) • (1 : L 𝒦)) =
        (ε : ℂ) • (1 : L 𝒦) := by
      rw [← add_smul]
      norm_num
    simp only [smul_add]
    rw [show (1 - θ) • a₁ + (1 - θ) • (ε : ℂ) • 1 + (θ • a₂ + θ • (ε : ℂ) • 1) =
        ((1 - θ) • a₁ + θ • a₂) + ((1 - θ) • (ε : ℂ) • 1 + θ • (ε : ℂ) • 1) from by abel,
        h1]
  refine le_of_tendsto_of_tendsto (key _ _ hρc hσc)
    (((key ρ₁ σ₁ hρ₁ hσ₁).const_smul (1 - θ)).add ((key ρ₂ σ₂ hρ₂ hσ₂).const_smul θ)) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have hp₁ := nonneg_add_pos_smul_one_pdSet hρ₁ hε'
  have hp₂ := nonneg_add_pos_smul_one_pdSet hρ₂ hε'
  have hq₁ := nonneg_add_pos_smul_one_pdSet hσ₁ hε'
  have hq₂ := nonneg_add_pos_smul_one_pdSet hσ₂ hε'
  have hj := hpd hp₁ hp₂ hq₁ hq₂ hθ0 hθ1
  rw [hcombo ρ₁ ρ₂ ε, hcombo σ₁ σ₂ ε]
  exact hj

end JointlyConvexNonneg

section JointlyConcaveNonneg
-- `sandwichedQuasi` is treated as a black box here (only continuity, the pd Jensen
-- inequality, and limits are used), so making it irreducible avoids the unifier
-- unfolding the large CFC expression during def-eq checks.
attribute [local irreducible] sandwichedQuasi

/-- **Proposition 3 on the non-negative cone (concave case, `1/2 ≤ α < 1`).**
    Joint concavity of `(ρ, σ) ↦ Re Q_α(ρ‖σ)` extends from `pdSet` to the whole
    non-negative cone by an `ε → 0⁺` perturbation `(ρ, σ) ↦ (ρ + ε•1, σ + ε•1)`, using
    joint continuity on the cone (`sandwichedQuasi_re_continuousOn_nonneg`). -/
private lemma sandwichedQuasi_re_jointlyConcave_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {α : ℝ} (hα_ge : 1 / 2 ≤ α) (hα_lt : α < 1) :
    JointlyConcaveOn {A : L 𝒦 | (0 : L 𝒦) ≤ A} {A : L 𝒦 | (0 : L 𝒦) ≤ A}
      (fun ρ σ => (sandwichedQuasi (ℋ := 𝒦) α ρ σ).re) := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hcont := sandwichedQuasi_re_continuousOn_nonneg (𝒦 := 𝒦) hα0 hα_lt.le
  have hpd := sandwichedQuasi_re_jointlyConcave (ℋ := 𝒦) hα_ge hα_lt
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [Set.mem_ofPred_eq] at hρ₁ hρ₂ hσ₁ hσ₂
  -- Limit of `Re Q_α` at a non-negative pair, approached through pd perturbations `+ ε•1`.
  have key : ∀ a b : L 𝒦, (0 : L 𝒦) ≤ a → (0 : L 𝒦) ≤ b →
      Filter.Tendsto
        (fun ε : ℝ => (sandwichedQuasi α (a + (ε : ℂ) • 1) (b + (ε : ℂ) • 1)).re)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (sandwichedQuasi α a b).re) := by
    intro a b ha hb
    have hcurve : Continuous (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1)) := by fun_prop
    have h_into : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1) ∈
          ({A : L 𝒦 | (0 : L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0 : L 𝒦) ≤ A}) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      have hsmul : (0 : L 𝒦) ≤ (ε : ℂ) • (1 : L 𝒦) :=
        nonneg_of_pdSet (pos_smul_one_pdSet hε')
      exact ⟨by simpa using add_nonneg ha hsmul, by simpa using add_nonneg hb hsmul⟩
    have h_tendsto_curve :
        Filter.Tendsto (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhdsWithin (a, b) ({A : L 𝒦 | (0:L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0:L 𝒦) ≤ A})) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, h_into⟩
      have h0 : Filter.Tendsto (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1))
          (nhds (0 : ℝ)) (nhds (a, b)) := by
        have h := hcurve.tendsto 0
        simpa using h
      exact h0.mono_left nhdsWithin_le_nhds
    have hcwa : Filter.Tendsto
        (Function.uncurry (fun ρ σ : L 𝒦 => (sandwichedQuasi α ρ σ).re))
        (nhdsWithin (a, b) ({A : L 𝒦 | (0:L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0:L 𝒦) ≤ A}))
        (nhds (sandwichedQuasi α a b).re) :=
      hcont (a, b) ⟨ha, hb⟩
    exact hcwa.comp h_tendsto_curve
  -- Non-negativity of the convex combinations.
  have hρc : (0 : L 𝒦) ≤ (1 - θ) • ρ₁ + θ • ρ₂ :=
    add_nonneg (smul_nonneg (by linarith) hρ₁) (smul_nonneg hθ0 hρ₂)
  have hσc : (0 : L 𝒦) ≤ (1 - θ) • σ₁ + θ • σ₂ :=
    add_nonneg (smul_nonneg (by linarith) hσ₁) (smul_nonneg hθ0 hσ₂)
  -- The perturbed convex combination equals the convex combination of perturbations.
  have hcombo : ∀ a₁ a₂ : L 𝒦, ∀ ε : ℝ,
      ((1 - θ) • a₁ + θ • a₂) + (ε : ℂ) • 1 =
        (1 - θ) • (a₁ + (ε : ℂ) • 1) + θ • (a₂ + (ε : ℂ) • 1) := by
    intro a₁ a₂ ε
    have h1 : ((1 - θ : ℝ)) • ((ε : ℂ) • (1 : L 𝒦)) + (θ : ℝ) • ((ε : ℂ) • (1 : L 𝒦)) =
        (ε : ℂ) • (1 : L 𝒦) := by
      rw [← add_smul]
      norm_num
    simp only [smul_add]
    rw [show (1 - θ) • a₁ + (1 - θ) • (ε : ℂ) • 1 + (θ • a₂ + θ • (ε : ℂ) • 1) =
        ((1 - θ) • a₁ + θ • a₂) + ((1 - θ) • (ε : ℂ) • 1 + θ • (ε : ℂ) • 1) from by abel,
        h1]
  -- Pass the pd Jensen inequality to the limit `ε → 0⁺`.
  refine le_of_tendsto_of_tendsto
    (((key ρ₁ σ₁ hρ₁ hσ₁).const_smul (1 - θ)).add ((key ρ₂ σ₂ hρ₂ hσ₂).const_smul θ))
    (key _ _ hρc hσc) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have hp₁ := nonneg_add_pos_smul_one_pdSet hρ₁ hε'
  have hp₂ := nonneg_add_pos_smul_one_pdSet hρ₂ hε'
  have hq₁ := nonneg_add_pos_smul_one_pdSet hσ₁ hε'
  have hq₂ := nonneg_add_pos_smul_one_pdSet hσ₂ hε'
  have hj := hpd hp₁ hp₂ hq₁ hq₂ hθ0 hθ1
  rw [hcombo ρ₁ ρ₂ ε, hcombo σ₁ σ₂ ε]
  exact hj

end JointlyConcaveNonneg

section JensenHaarCore
-- `sandwichedQuasi`/`quasiVar` are treated as black boxes (only via lemmas), so making
-- them irreducible avoids the unifier unfolding their large CFC expressions during the
-- many `rw`/`isDefEq` checks in the proof.
attribute [local irreducible] sandwichedQuasi quasiVar

/-- **Inner Jensen–Haar inequality (Form A, isometric Stinespring).**

    Reformulation of the central Jensen-style inequality in terms of an
    *isometric* Stinespring map `V : ℋ →L[ℂ] (ℋ ⊗ ℋ_env)` with `V*V = I`,
    rather than the previous unitary-with-mixed-environment Form B
    (`TrLeft[U(τ ⊗ γ)U*]`). The inequality states:

    `Re sandwichedQuasi α ((E ρ) ⊗ τ_max) ((E σ) ⊗ τ_max)`
    `⋚ Re sandwichedQuasi α (V ρ V*) (V σ V*)`

    where `E γ := TrRight (V γ V*)` and `τ_max := (dim ℋ_env)⁻¹ • 1` on
    `ℋ_env`; direction `≤` for `α > 1`, `≥` for `α ∈ [1/2, 1)`.

    **Proof (Frank–Lieb arXiv:1306.5358, isometric variant).**
    The integrand `g_ρ u := (1_ℋ ⊗ u) · (V ρ V*) · (1_ℋ ⊗ u*)` is in general
    *rank-deficient* (supported on the range of `V V*`), so the original
    closed-pd-subcone Jensen argument no longer applies directly. We instead
    work on the whole non-negative cone `{A | 0 ≤ A}` (closed and convex):
      1. The right-twirl identity (`twirl_eq_partialTrace_right_smul_id`, the `TrRight` analogue of
         `HaarUnitary.twirl_eq_partialTrace_smul_id`) identifies
         `∫ g_ρ u du = (E ρ) ⊗ τ_max`.
      2. `g_ρ u` is non-negative (unitary conjugation of `V ρ V* ≥ 0`) and
         `Re Q_α` is jointly concave (`α < 1`) / convex (`α > 1`) and continuous
         on the non-negative cone.
      3. Bochner–Jensen (`jointly_concave_le_integral`) plus unitary invariance
         of `Q_α` (the integrand `Re Q_α(g_ρ u, g_σ u)` is *constant*
         `= Re Q_α(V ρ V*, V σ V*)`) gives the inequality.

    **Both cases are proved.** The `α ∈ [1/2, 1)` (concave) branch applies
    Bochner–Jensen to `Re Q_α` directly. For `α > 1` the exponent
    `β = (1-α)/(2α) < 0` makes `Re Q_α` discontinuous at singular `σ`, so joint
    convexity on the non-negative cone is unavailable; instead we use the
    Frank–Lieb variational functional `quasiVar`: at the (pd) integral point
    `Q_α = quasiVar(·,·,H*)` for the optimizer `H*`, `quasiVar(·,·,H*)` is jointly
    convex and continuous on the psd cone (only positive exponents of `σ`), and
    pointwise `quasiVar(g_ρ u, g_σ u, H*) ≤ Q_α(g_ρ u, g_σ u)` — reduced through
    the single isometry `(1 ⊗ u) ∘ V` to `quasiVar_le_quasi` on the pd pair. -/
private theorem jensen_haar_core
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {ℋ_env : Type u} [Qudit ℋ_env] [Nontrivial ℋ_env]
    {α : ℝ} (_hα_ge : (1 : ℝ) / 2 ≤ α) (_hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ}
    (_hρ : ρ ∈ pdSet (ℋ := ℋ)) (_hσ : σ ∈ pdSet (ℋ := ℋ))
    (V : ℋ →L[ℂ] (𝒦 ⊗[ℂ] ℋ_env))
    (_hV : (ContinuousLinearMap.adjoint V).comp V = (1 : L ℋ))
    (_hEρ : TrRight ((V.comp ρ).comp (ContinuousLinearMap.adjoint V)) ∈ pdSet (ℋ := 𝒦))
    (_hEσ : TrRight ((V.comp σ).comp (ContinuousLinearMap.adjoint V)) ∈ pdSet (ℋ := 𝒦)) :
    ((sandwichedQuasi α
        (TensorProduct.mapL
          (TrRight ((V.comp ρ).comp (ContinuousLinearMap.adjoint V)))
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))
        (TensorProduct.mapL
          (TrRight ((V.comp σ).comp (ContinuousLinearMap.adjoint V)))
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))).re -
      (sandwichedQuasi α
        ((V.comp ρ).comp (ContinuousLinearMap.adjoint V))
        ((V.comp σ).comp (ContinuousLinearMap.adjoint V))).re) * (α - 1) ≤ 0 := by
  -- `ℋ ⊗ ℋ_env` is again a (nontrivial) qudit.
  have : Nontrivial (𝒦 ⊗[ℂ] ℋ_env) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by
      rw [Module.finrank_tensorProduct]
      exact Nat.mul_pos (Module.finrank_pos) (Module.finrank_pos))
  rcases lt_or_gt_of_ne _hα_ne1 with hα_lt | hα_gt
  · -- **α ∈ [1/2, 1): concave Jensen–Haar.**
    -- Strategy: the Haar integrand `gρ u = (1⊗u)(VρV*)(1⊗u*)` is non-negative and
    -- `Re Q_α` is jointly concave + continuous on the whole non-negative cone, so
    -- Bochner–Jensen gives `∫ Re Q_α(gρ, gσ) ≤ Re Q_α(∫gρ, ∫gσ)`. The integrand is
    -- constant (`= Re Q_α(VρV*, VσV*)` by unitary invariance) and `∫gρ = Eρ ⊗ τmax`
    -- (right twirl), yielding `Re Q_α(VρV*, VσV*) ≤ Re Q_α(Eρ⊗τmax, Eσ⊗τmax)`.
    have hα0 : (0 : ℝ) < α := by linarith
    set Xρ : L (𝒦 ⊗[ℂ] ℋ_env) := (V.comp ρ).comp (ContinuousLinearMap.adjoint V) with hXρ_def
    set Xσ : L (𝒦 ⊗[ℂ] ℋ_env) := (V.comp σ).comp (ContinuousLinearMap.adjoint V) with hXσ_def
    have hρ_nn : (0 : L ℋ) ≤ ρ := nonneg_of_pdSet _hρ
    have hσ_nn : (0 : L ℋ) ≤ σ := nonneg_of_pdSet _hσ
    have hXρ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xρ := by
      rw [hXρ_def, ContinuousLinearMap.nonneg_iff_isPositive]
      exact ((ContinuousLinearMap.nonneg_iff_isPositive ρ).mp hρ_nn).conj_adjoint V
    have hXσ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xσ := by
      rw [hXσ_def, ContinuousLinearMap.nonneg_iff_isPositive]
      exact ((ContinuousLinearMap.nonneg_iff_isPositive σ).mp hσ_nn).conj_adjoint V
    -- Haar integrands.
    set gρ : unitary (L ℋ_env) → L (𝒦 ⊗[ℂ] ℋ_env) := fun u =>
        TensorProduct.mapL (1 : L 𝒦) ((u : L ℋ_env)) * Xρ *
          TensorProduct.mapL (1 : L 𝒦) (star (u : L ℋ_env)) with hgρ_def
    set gσ : unitary (L ℋ_env) → L (𝒦 ⊗[ℂ] ℋ_env) := fun u =>
        TensorProduct.mapL (1 : L 𝒦) ((u : L ℋ_env)) * Xσ *
          TensorProduct.mapL (1 : L 𝒦) (star (u : L ℋ_env)) with hgσ_def
    -- The integrand of `Re Q_α` is constant (unitary invariance of `Q_α`).
    have h_inv : ∀ u : unitary (L ℋ_env),
        (sandwichedQuasi α (gρ u) (gσ u)).re = (sandwichedQuasi α Xρ Xσ).re := by
      intro u
      set U : unitary (L (𝒦 ⊗[ℂ] ℋ_env)) :=
        ⟨TensorProduct.mapL (1 : L 𝒦) ((u : L ℋ_env)),
          tensorMap_right_unitary_of_unitary u⟩ with hU_def
      have hUcoe : ((U : unitary (L (𝒦 ⊗[ℂ] ℋ_env))) : L (𝒦 ⊗[ℂ] ℋ_env)) =
          TensorProduct.mapL (1 : L 𝒦) ((u : L ℋ_env)) := rfl
      have hUstar : ((star U : unitary (L (𝒦 ⊗[ℂ] ℋ_env))) : L (𝒦 ⊗[ℂ] ℋ_env)) =
          TensorProduct.mapL (1 : L 𝒦) (star (u : L ℋ_env)) := by
        rw [Unitary.coe_star, hUcoe, tensorMap_right_star]
      have hgρ_eq : gρ u =
          (U : L (𝒦 ⊗[ℂ] ℋ_env)) * Xρ * (star U : L (𝒦 ⊗[ℂ] ℋ_env)) := by
        simp only [hgρ_def, hUcoe, tensorMap_right_star]
      have hgσ_eq : gσ u =
          (U : L (𝒦 ⊗[ℂ] ℋ_env)) * Xσ * (star U : L (𝒦 ⊗[ℂ] ℋ_env)) := by
        simp only [hgσ_def, hUcoe, tensorMap_right_star]
      rw [hgρ_eq, hgσ_eq, sandwichedQuasi_unitary_conj α Xρ Xσ U]
    -- Non-negativity of the integrands (the cone membership for Jensen).
    have hgρ_mem : ∀ᵐ u ∂(haarUnitary ℋ_env),
        gρ u ∈ {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} := by
      filter_upwards with u
      show (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ gρ u
      have h := star_left_conjugate_nonneg hXρ_nn
          (star (TensorProduct.mapL (1 : L 𝒦) ((u : L ℋ_env))))
      rw [star_star, tensorMap_right_star] at h
      exact h
    have hgσ_mem : ∀ᵐ u ∂(haarUnitary ℋ_env),
        gσ u ∈ {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} := by
      filter_upwards with u
      show (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ gσ u
      have h := star_left_conjugate_nonneg hXσ_nn
          (star (TensorProduct.mapL (1 : L 𝒦) ((u : L ℋ_env))))
      rw [star_star, tensorMap_right_star] at h
      exact h
    -- Integrability.
    have hgρ_int : Integrable gρ (haarUnitary ℋ_env) :=
      integrable_unitaryConj_tensor_right Xρ
    have hgσ_int : Integrable gσ (haarUnitary ℋ_env) :=
      integrable_unitaryConj_tensor_right Xσ
    have hfg_int :
        Integrable (fun u => (sandwichedQuasi α (gρ u) (gσ u)).re) (haarUnitary ℋ_env) := by
      simp_rw [h_inv]
      exact integrable_const _
    -- The two integrals collapse via the right twirl.
    have hint_ρ : (∫ u, gρ u ∂(haarUnitary ℋ_env)) =
        TensorProduct.mapL (TrRight Xρ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) :=
      twirl_eq_partialTrace_right_smul_id Xρ
    have hint_σ : (∫ u, gσ u ∂(haarUnitary ℋ_env)) =
        TensorProduct.mapL (TrRight Xσ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) :=
      twirl_eq_partialTrace_right_smul_id Xσ
    -- The constant-integrand integral equals `Re Q_α(VρV*, VσV*)`.
    have h_lhs_int : (∫ u, (sandwichedQuasi α (gρ u) (gσ u)).re ∂(haarUnitary ℋ_env))
        = (sandwichedQuasi α Xρ Xσ).re := by
      simp_rw [h_inv]
      simp
    -- Membership of the (collapsed) integrals in the closed convex cone.
    have hmem_ρ : (∫ u, gρ u ∂(haarUnitary ℋ_env)) ∈
        {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} :=
      (convex_nonneg_cone (𝒦 := 𝒦 ⊗[ℂ] ℋ_env)).integral_mem (isClosed_nonneg_cone (𝒦 := 𝒦 ⊗[ℂ] ℋ_env)) hgρ_mem hgρ_int
    have hmem_σ : (∫ u, gσ u ∂(haarUnitary ℋ_env)) ∈
        {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} :=
      (convex_nonneg_cone (𝒦 := 𝒦 ⊗[ℂ] ℋ_env)).integral_mem (isClosed_nonneg_cone (𝒦 := 𝒦 ⊗[ℂ] ℋ_env)) hgσ_mem hgσ_int
    -- Bochner–Jensen on the non-negative cone.
    have hJ := jointly_concave_le_integral (μ := haarUnitary ℋ_env)
      (convex_nonneg_cone (𝒦 := 𝒦 ⊗[ℂ] ℋ_env)) (convex_nonneg_cone (𝒦 := 𝒦 ⊗[ℂ] ℋ_env))
      (isClosed_nonneg_cone (𝒦 := 𝒦 ⊗[ℂ] ℋ_env)) (isClosed_nonneg_cone (𝒦 := 𝒦 ⊗[ℂ] ℋ_env))
      (sandwichedQuasi_re_jointlyConcave_nonneg _hα_ge hα_lt)
      (sandwichedQuasi_re_continuousOn_nonneg hα0 hα_lt.le)
      hgρ_mem hgσ_mem hgρ_int hgσ_int hfg_int hmem_ρ hmem_σ
    rw [h_lhs_int, hint_ρ, hint_σ] at hJ
    -- `hJ : Re Q_α(VρV*, VσV*) ≤ Re Q_α(Eρ⊗τmax, Eσ⊗τmax)`; close with the sign of `α-1`.
    have hα1_neg : α - 1 ≤ 0 := by linarith
    have hD : (0 : ℝ) ≤ (sandwichedQuasi α
        (TensorProduct.mapL (TrRight Xρ) ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))
        (TensorProduct.mapL (TrRight Xσ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))).re -
        (sandwichedQuasi α Xρ Xσ).re := sub_nonneg.mpr hJ
    nlinarith [hD, hα1_neg, mul_nonneg hD (neg_nonneg.mpr hα1_neg)]
  · -- **α > 1: convex case, via the Frank–Lieb variational functional `quasiVar`.**
    -- `Re Q_α` is discontinuous at singular `σ`, so we cannot apply Jensen to it directly.
    -- Instead we use that at the (pd) integral point `Pρ = ∫gρ`, `Pσ = ∫gσ`,
    -- `Re Q_α(Pρ,Pσ) = Re quasiVar(Pρ,Pσ,H*)` for the optimizer `H*`, that
    -- `quasiVar(·,·,H*)` IS jointly convex + continuous on the psd cone (positive
    -- exponents), and that pointwise `quasiVar(gρu,gσu,H*) ≤ Q_α(gρu,gσu)` (reduced via
    -- the single isometry `(1⊗u)∘V` to `quasiVar_le_quasi` on the pd pair `ρ,σ`).
    have hα0 : (0 : ℝ) < α := by linarith
    have hα_ne1 : α ≠ 1 := ne_of_gt hα_gt
    set Xρ : L (𝒦 ⊗[ℂ] ℋ_env) := (V.comp ρ).comp (ContinuousLinearMap.adjoint V) with hXρ_def
    set Xσ : L (𝒦 ⊗[ℂ] ℋ_env) := (V.comp σ).comp (ContinuousLinearMap.adjoint V) with hXσ_def
    have hρ_nn : (0 : L ℋ) ≤ ρ := nonneg_of_pdSet _hρ
    have hσ_nn : (0 : L ℋ) ≤ σ := nonneg_of_pdSet _hσ
    have hXρ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xρ := by
      rw [hXρ_def, ContinuousLinearMap.nonneg_iff_isPositive]
      exact ((ContinuousLinearMap.nonneg_iff_isPositive ρ).mp hρ_nn).conj_adjoint V
    have hXσ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xσ := by
      rw [hXσ_def, ContinuousLinearMap.nonneg_iff_isPositive]
      exact ((ContinuousLinearMap.nonneg_iff_isPositive σ).mp hσ_nn).conj_adjoint V
    set gρ : unitary (L ℋ_env) → L (𝒦 ⊗[ℂ] ℋ_env) := fun u =>
        TensorProduct.mapL (1 : L 𝒦) ((u : L ℋ_env)) * Xρ *
          TensorProduct.mapL (1 : L 𝒦) (star (u : L ℋ_env)) with hgρ_def
    set gσ : unitary (L ℋ_env) → L (𝒦 ⊗[ℂ] ℋ_env) := fun u =>
        TensorProduct.mapL (1 : L 𝒦) ((u : L ℋ_env)) * Xσ *
          TensorProduct.mapL (1 : L 𝒦) (star (u : L ℋ_env)) with hgσ_def
    -- Unitary invariance: the `Re Q_α` integrand is constant.
    have h_inv : ∀ u : unitary (L ℋ_env),
        (sandwichedQuasi α (gρ u) (gσ u)).re = (sandwichedQuasi α Xρ Xσ).re := by
      intro u
      set U : unitary (L (𝒦 ⊗[ℂ] ℋ_env)) :=
        ⟨TensorProduct.mapL (1 : L 𝒦) ((u : L ℋ_env)),
          tensorMap_right_unitary_of_unitary u⟩ with hU_def
      have hUcoe : ((U : unitary (L (𝒦 ⊗[ℂ] ℋ_env))) : L (𝒦 ⊗[ℂ] ℋ_env)) =
          TensorProduct.mapL (1 : L 𝒦) ((u : L ℋ_env)) := rfl
      have hgρ_eq : gρ u =
          (U : L (𝒦 ⊗[ℂ] ℋ_env)) * Xρ * (star U : L (𝒦 ⊗[ℂ] ℋ_env)) := by
        simp only [hgρ_def, hUcoe, tensorMap_right_star]
      have hgσ_eq : gσ u =
          (U : L (𝒦 ⊗[ℂ] ℋ_env)) * Xσ * (star U : L (𝒦 ⊗[ℂ] ℋ_env)) := by
        simp only [hgσ_def, hUcoe, tensorMap_right_star]
      rw [hgρ_eq, hgσ_eq, sandwichedQuasi_unitary_conj α Xρ Xσ U]
    -- Non-negativity of the integrands (everywhere).
    have hgρ_nn_all : ∀ u, gρ u ∈ {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} := by
      intro u
      change (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ gρ u
      have h := star_left_conjugate_nonneg hXρ_nn
          (star (TensorProduct.mapL (1 : L 𝒦) ((u : L ℋ_env))))
      rw [star_star, tensorMap_right_star] at h
      exact h
    have hgσ_nn_all : ∀ u, gσ u ∈ {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} := by
      intro u
      change (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ gσ u
      have h := star_left_conjugate_nonneg hXσ_nn
          (star (TensorProduct.mapL (1 : L 𝒦) ((u : L ℋ_env))))
      rw [star_star, tensorMap_right_star] at h
      exact h
    have hgρ_mem : ∀ᵐ u ∂(haarUnitary ℋ_env),
        gρ u ∈ {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} :=
      Filter.Eventually.of_forall hgρ_nn_all
    have hgσ_mem : ∀ᵐ u ∂(haarUnitary ℋ_env),
        gσ u ∈ {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} :=
      Filter.Eventually.of_forall hgσ_nn_all
    -- Integrability of the integrands and of the `Re Q_α` integrand.
    have hgρ_int : Integrable gρ (haarUnitary ℋ_env) := integrable_unitaryConj_tensor_right Xρ
    have hgσ_int : Integrable gσ (haarUnitary ℋ_env) := integrable_unitaryConj_tensor_right Xσ
    have hfg_int :
        Integrable (fun u => (sandwichedQuasi α (gρ u) (gσ u)).re) (haarUnitary ℋ_env) := by
      simp_rw [h_inv]
      exact integrable_const _
    -- Right-twirl collapse of the integrals.
    have hint_ρ : (∫ u, gρ u ∂(haarUnitary ℋ_env)) =
        TensorProduct.mapL (TrRight Xρ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) := twirl_eq_partialTrace_right_smul_id Xρ
    have hint_σ : (∫ u, gσ u ∂(haarUnitary ℋ_env)) =
        TensorProduct.mapL (TrRight Xσ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) := twirl_eq_partialTrace_right_smul_id Xσ
    have h_lhs_int : (∫ u, (sandwichedQuasi α (gρ u) (gσ u)).re ∂(haarUnitary ℋ_env))
        = (sandwichedQuasi α Xρ Xσ).re := by
          simp_rw [h_inv]
          simp
    have hmem_ρ : (∫ u, gρ u ∂(haarUnitary ℋ_env)) ∈
        {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} :=
      (convex_nonneg_cone (𝒦 := 𝒦 ⊗[ℂ] ℋ_env)).integral_mem (isClosed_nonneg_cone (𝒦 := 𝒦 ⊗[ℂ] ℋ_env)) hgρ_mem hgρ_int
    have hmem_σ : (∫ u, gσ u ∂(haarUnitary ℋ_env)) ∈
        {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} :=
      (convex_nonneg_cone (𝒦 := 𝒦 ⊗[ℂ] ℋ_env)).integral_mem (isClosed_nonneg_cone (𝒦 := 𝒦 ⊗[ℂ] ℋ_env)) hgσ_mem hgσ_int
    -- The pd integral points `Pρ = ∫gρ`, `Pσ = ∫gσ`, and the optimizer `H*`.
    set Pρ : L (𝒦 ⊗[ℂ] ℋ_env) :=
      TensorProduct.mapL (TrRight Xρ) ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) with hPρ_def
    set Pσ : L (𝒦 ⊗[ℂ] ℋ_env) :=
      TensorProduct.mapL (TrRight Xσ) ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) with hPσ_def
    have hτmax_pd : ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) ∈ pdSet (ℋ := ℋ_env) :=
      maxmixed_pdSet ℋ_env
    have hPρ_pd : Pρ ∈ pdSet (ℋ := 𝒦 ⊗[ℂ] ℋ_env) := by
      rw [hPρ_def]
      exact pdSet_tensorMap (by rw [hXρ_def]; exact _hEρ) hτmax_pd
    have hPσ_pd : Pσ ∈ pdSet (ℋ := 𝒦 ⊗[ℂ] ℋ_env) := by
      rw [hPσ_def]
      exact pdSet_tensorMap (by rw [hXσ_def]; exact _hEσ) hτmax_pd
    set Hopt := quasiVarOpt α Pρ Pσ with hHopt_def
    have hHopt_pd : Hopt ∈ pdSet (ℋ := 𝒦 ⊗[ℂ] ℋ_env) :=
      quasiVarOpt_pdSet hα0 hα_ne1 hPρ_pd hPσ_pd
    have hHopt_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Hopt := nonneg_of_pdSet hHopt_pd
    have hHopt_pos : Hopt.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive _).mp hHopt_nn
    -- Attainment at the pd point: `Re Q_α(Pρ,Pσ) = Re quasiVar(Pρ,Pσ,H*)`.
    have hatt : (sandwichedQuasi α Pρ Pσ).re = (quasiVar α Pρ Pσ Hopt).re := by
      rw [hHopt_def, quasiVarOpt_eq_quasi_gt hα_gt hPρ_pd hPσ_pd]
    -- Integrability of `u ↦ Re quasiVar(gρu,gσu,H*)` (continuity + compact support).
    have hgρ_cont : Continuous gρ := continuous_unitaryConj_tensor_right Xρ
    have hgσ_cont : Continuous gσ := continuous_unitaryConj_tensor_right Xσ
    have hquasi_cont : Continuous (fun u => (quasiVar α (gρ u) (gσ u) Hopt).re) := by
      have h : Continuous (fun u => Function.uncurry
          (fun ρ σ => (quasiVar α ρ σ Hopt).re) (gρ u, gσ u)) :=
        (quasiVar_re_continuousOn_nonneg hα_gt hHopt_nn).comp_continuous
          (hgρ_cont.prodMk hgσ_cont) (fun u => Set.mk_mem_prod (hgρ_nn_all u) (hgσ_nn_all u))
      simpa only [Function.uncurry_apply_pair] using h
    have hquasi_int :
        Integrable (fun u => (quasiVar α (gρ u) (gσ u) Hopt).re) (haarUnitary ℋ_env) :=
      hquasi_cont.integrable_of_hasCompactSupport
        (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
    -- Jensen for the (convex, continuous) `quasiVar(·,·,H*)` on the psd cone.
    have hJ := jointly_convex_integral_le (μ := haarUnitary ℋ_env)
      (convex_nonneg_cone (𝒦 := 𝒦 ⊗[ℂ] ℋ_env)) (convex_nonneg_cone (𝒦 := 𝒦 ⊗[ℂ] ℋ_env))
      (isClosed_nonneg_cone (𝒦 := 𝒦 ⊗[ℂ] ℋ_env)) (isClosed_nonneg_cone (𝒦 := 𝒦 ⊗[ℂ] ℋ_env))
      (quasiVar_re_jointlyConvex_nonneg hα_gt hHopt_pd)
      (quasiVar_re_continuousOn_nonneg hα_gt hHopt_nn)
      hgρ_mem hgσ_mem hgρ_int hgσ_int hquasi_int hmem_ρ hmem_σ
    rw [hint_ρ, hint_σ] at hJ
    -- Pointwise `quasiVar(gρu,gσu,H*) ≤ Q_α(gρu,gσu)` via the isometry `Vu = (1⊗u)∘V`.
    have hpoint : ∀ u : unitary (L ℋ_env),
        (quasiVar α (gρ u) (gσ u) Hopt).re ≤ (sandwichedQuasi α (gρ u) (gσ u)).re := by
      intro u
      set W : L (𝒦 ⊗[ℂ] ℋ_env) := TensorProduct.mapL (1 : L 𝒦) ((u : L ℋ_env))
        with hW_def
      have hW_unit : W ∈ unitary (L (𝒦 ⊗[ℂ] ℋ_env)) := tensorMap_right_unitary_of_unitary u
      have hadjW : ContinuousLinearMap.adjoint W =
          TensorProduct.mapL (1 : L 𝒦) (star (u : L ℋ_env)) := by
        rw [hW_def, ← ContinuousLinearMap.star_eq_adjoint, tensorMap_right_star]
      set Vu : ℋ →L[ℂ] (𝒦 ⊗[ℂ] ℋ_env) := W.comp V with hVu_def
      have hVu_iso : (ContinuousLinearMap.adjoint Vu).comp Vu = 1 := by
        have hWadjW : ∀ y, (ContinuousLinearMap.adjoint W) (W y) = y := by
          have h := (Unitary.mem_iff.mp hW_unit).1
          rw [ContinuousLinearMap.star_eq_adjoint] at h
          exact fun y => DFunLike.congr_fun h y
        rw [hVu_def, ContinuousLinearMap.adjoint_comp, ← _hV]
        ext x
        simp [hWadjW]
      have hgρu_eq : gρ u = (Vu.comp ρ).comp (ContinuousLinearMap.adjoint Vu) := by
        simp only [hgρ_def]
        rw [hVu_def, hXρ_def, ContinuousLinearMap.adjoint_comp, ← hW_def, ← hadjW]
        ext x
        rfl
      have hgσu_eq : gσ u = (Vu.comp σ).comp (ContinuousLinearMap.adjoint Vu) := by
        simp only [hgσ_def]
        rw [hVu_def, hXσ_def, ContinuousLinearMap.adjoint_comp, ← hW_def, ← hadjW]
        ext x
        rfl
      rw [hgρu_eq, hgσu_eq, quasiVar_isometric_conj Vu hVu_iso hα0 hα_ne1 hσ_nn hHopt_nn,
        sandwichedQuasi_isometric_conj Vu hVu_iso hα0 hα_ne1 hρ_nn hσ_nn]
      exact (RCLike.le_iff_re_im.mp (quasiVar_le_quasi hα_gt
        ((ContinuousLinearMap.nonneg_iff_isPositive ρ).mp hρ_nn)
        ((ContinuousLinearMap.nonneg_iff_isPositive σ).mp hσ_nn)
        (hHopt_pos.adjoint_conj Vu) (isUnit_of_pdSet _hσ))).1
    -- Combine: `Re Q_α(Pρ,Pσ) ≤ ∫ Re quasiVar ≤ ∫ Re Q_α = Re Q_α(Xρ,Xσ)`.
    have hint_le : (∫ u, (quasiVar α (gρ u) (gσ u) Hopt).re ∂(haarUnitary ℋ_env)) ≤
        (sandwichedQuasi α Xρ Xσ).re := by
      calc (∫ u, (quasiVar α (gρ u) (gσ u) Hopt).re ∂(haarUnitary ℋ_env))
          ≤ ∫ u, (sandwichedQuasi α (gρ u) (gσ u)).re ∂(haarUnitary ℋ_env) :=
            integral_mono hquasi_int hfg_int hpoint
        _ = (sandwichedQuasi α Xρ Xσ).re := h_lhs_int
    have hfinal : (sandwichedQuasi α Pρ Pσ).re ≤ (sandwichedQuasi α Xρ Xσ).re := by
      rw [hatt]
      exact le_trans hJ hint_le
    have hα1_pos : (0 : ℝ) < α - 1 := by linarith
    nlinarith [hfinal, hα1_pos]

end JensenHaarCore

/-! ### The abstract Jensen-Haar interface -/

/-- **Jensen–Haar inequality (Form A, isometric Stinespring).**

    Given the data of an *isometric* Stinespring dilation — an environment
    Hilbert space `ℋ_env` and an isometry `V : ℋ →L[ℂ] (ℋ ⊗ ℋ_env)` with
    `V*V = I_ℋ` — let `E γ := TrRight (V γ V*)`. Then for any
    `α ∈ [1/2, 1) ∪ (1, ∞)` and any positive-definite `ρ, σ` with
    positive-definite images `E ρ`, `E σ`,

    `(Re sandwichedQuasi α (E ρ) (E σ) − Re sandwichedQuasi α ρ σ) · (α − 1) ≤ 0`.

    This is the data-processing inequality at the `Q_α`-functional level,
    in the form directly compatible with `CPTPOp.exists_stinespring_dilation`
    (Form A). The previous interface — taking a unitary `U` and a
    positive-definite density matrix `τ_env` on the environment — has been
    retired together with the Naimark dilation it relied on.

    **Proof outline (Frank–Lieb arXiv:1306.5358).**
    Apply the right-twirl identity to write
      `(E γ) ⊗ τ_max = ∫ (1 ⊗ u) (V γ V*) (1 ⊗ u*) du`
    over the Haar measure on `unitary (L ℋ_env)`. Combine with tensor
    multiplicativity of `sandwichedQuasi` (and the self-identity
    `sandwichedQuasi α τ_max τ_max = Tr τ_max`) to reduce the goal to
    the inner Jensen-style inequality `jensen_haar_core`. The latter is
    proved via Lieb (`α > 1`) or Ando (`α ∈ [1/2, 1)`) joint
    convexity / concavity of `sandwichedQuasi.re`, with rank-deficiency
    handled by the convention `Q_α(ρ, σ) = ∞ when ker σ ⊄ ker ρ`. -/
theorem sandwichedQuasi_jensen_haar
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {ℋ_env : Type u} [Qudit ℋ_env] [Nontrivial ℋ_env]
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ}
    (hρ : ρ ∈ pdSet (ℋ := ℋ)) (hσ : σ ∈ pdSet (ℋ := ℋ))
    (V : ℋ →L[ℂ] (𝒦 ⊗[ℂ] ℋ_env))
    (hV : (ContinuousLinearMap.adjoint V).comp V = (1 : L ℋ))
    (hEρ : TrRight ((V.comp ρ).comp (ContinuousLinearMap.adjoint V)) ∈ pdSet (ℋ := 𝒦))
    (hEσ : TrRight ((V.comp σ).comp (ContinuousLinearMap.adjoint V)) ∈ pdSet (ℋ := 𝒦)) :
    ((sandwichedQuasi α
        (TrRight ((V.comp ρ).comp (ContinuousLinearMap.adjoint V)))
        (TrRight ((V.comp σ).comp (ContinuousLinearMap.adjoint V)))).re -
      (sandwichedQuasi α ρ σ).re) * (α - 1) ≤ 0 := by
  -- Reduce `sandwichedQuasi_jensen_haar` to `jensen_haar_core` plus the
  -- two helper lemmas (tensor mult collapse + isometric invariance).
  have hα0 : 0 < α := by linarith
  have hα_ne0 : α ≠ 0 := ne_of_gt hα0
  set Eρ : L 𝒦 := TrRight ((V.comp ρ).comp (ContinuousLinearMap.adjoint V)) with hEρ_def
  set Eσ : L 𝒦 := TrRight ((V.comp σ).comp (ContinuousLinearMap.adjoint V)) with hEσ_def
  set τ_max : L ℋ_env := (Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env) with hτ_max_def
  -- `τ_max ∈ pdSet` and `Tr τ_max = 1`.
  have hτ_max_pd : τ_max ∈ pdSet (ℋ := ℋ_env) := maxmixed_pdSet ℋ_env
  have hτ_max_trace : Tr τ_max = 1 := by
    rw [hτ_max_def, map_smul, smul_eq_mul, Tr_one]
    have hd : (Module.finrank ℂ ℋ_env : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℂ) (M := ℋ_env)).ne'
    field_simp
  -- LHS factorisation: `Q_α(Eρ ⊗ τ_max, Eσ ⊗ τ_max) = Q_α(Eρ, Eσ)`.
  have hLHS_factor : sandwichedQuasi α
      (TensorProduct.mapL Eρ τ_max : L (𝒦 ⊗[ℂ] ℋ_env))
      (TensorProduct.mapL Eσ τ_max) =
      sandwichedQuasi α Eρ Eσ := by
    rw [sandwichedQuasi_tensor α Eρ Eσ τ_max τ_max
        (nonneg_of_pdSet hEρ) (nonneg_of_pdSet hEσ)
        (nonneg_of_pdSet hτ_max_pd) (nonneg_of_pdSet hτ_max_pd),
        sandwichedQuasi_self_pdSet hα_ne0 hτ_max_pd, hτ_max_trace, mul_one]
  -- RHS factorisation (isometric invariance):
  -- `Q_α(V ρ V*, V σ V*) = Q_α(ρ, σ)`, valid for all `α > 0`, `α ≠ 1`.
  -- (In finite dimensions there is no CFC convention obstruction even for `α > 1`;
  -- see `sandwichedQuasi_isometric_conj`.)
  have hRHS_factor : sandwichedQuasi α
      ((V.comp ρ).comp (ContinuousLinearMap.adjoint V))
      ((V.comp σ).comp (ContinuousLinearMap.adjoint V)) =
      sandwichedQuasi α ρ σ :=
    sandwichedQuasi_isometric_conj V hV hα0 hα_ne1
      (nonneg_of_pdSet hρ) (nonneg_of_pdSet hσ)
  -- Apply the inner Jensen-Haar (`jensen_haar_core`) and substitute.
  have h_core := jensen_haar_core hα_ge hα_ne1 hρ hσ V hV hEρ hEσ
  change ((sandwichedQuasi α Eρ Eσ).re - (sandwichedQuasi α ρ σ).re) * (α - 1) ≤ 0
  have hLHS_re : (sandwichedQuasi α
      (TensorProduct.mapL Eρ τ_max : L (𝒦 ⊗[ℂ] ℋ_env))
      (TensorProduct.mapL Eσ τ_max)).re = (sandwichedQuasi α Eρ Eσ).re := by
    rw [hLHS_factor]
  have hRHS_re : (sandwichedQuasi α
      ((V.comp ρ).comp (ContinuousLinearMap.adjoint V))
      ((V.comp σ).comp (ContinuousLinearMap.adjoint V))).re =
      (sandwichedQuasi α ρ σ).re := by
    rw [hRHS_factor]
  rw [← hLHS_re, ← hRHS_re]
  exact h_core

/-! ### Main monotonicity theorem -/

/-- Monotonicity of the sandwiched Rényi divergence under CPTP maps (data-processing inequality).

    For any quantum channel `E : CPTPOp ℋ ℋ`, any `α ∈ [1/2, 1) ∪ (1, ∞)`, and any
    positive-definite operators `ρ, σ` with positive-definite images `E ρ`, `E σ`,
        `D_α(E ρ ‖ E σ) ≤ D_α(ρ ‖ σ)`.

    **Proof.** Apply the isometric Stinespring dilation
    `E(γ) = TrRight (V γ V*)` (`CPTPOp.exists_stinespring_dilation`, Form A).
    The central inequality
        `(Re sandwichedQuasi α (Eρ) (Eσ) − Re sandwichedQuasi α ρ σ) · (α − 1) ≤ 0`
    follows from `sandwichedQuasi_jensen_haar` (the abstract Jensen–Haar
    inequality above). Dividing by `Tr Eρ = Tr ρ > 0` (trace preservation
    by `E`) and applying `(α−1)⁻¹ log(·)` gives the result, with sign
    tracking unifying the `α > 1` and `α < 1` cases. -/
theorem sandwichedRenyiDiv_monotone
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTPOp ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ}
    (hρ : ρ ∈ pdSet (ℋ := ℋ)) (hσ : σ ∈ pdSet (ℋ := ℋ))
    (hEρ : E.toLinearMap ρ ∈ pdSet (ℋ := 𝒦))
    (hEσ : E.toLinearMap σ ∈ pdSet (ℋ := 𝒦)) :
    sandwichedRenyiDiv α (E.toLinearMap ρ) (E.toLinearMap σ) ≤ sandwichedRenyiDiv α ρ σ := by
  have hα0 : 0 < α := by linarith
  have hα_ne0 : α ≠ 0 := ne_of_gt hα0
  -- Step 1: Isometric Stinespring dilation (Form A).
  obtain ⟨ℋ_env, h_qudit, h_nontriv, V, hV_iso, hV_eq⟩ :=
    CPTPOp.exists_stinespring_dilation E
  let := h_qudit
  let := h_nontriv
  -- Step 2: Eρ and Eσ as the (isometric) Stinespring images.
  have hEρ_eq : E.toLinearMap ρ = TrRight ((V.comp ρ).comp (ContinuousLinearMap.adjoint V)) := hV_eq ρ
  have hEσ_eq : E.toLinearMap σ = TrRight ((V.comp σ).comp (ContinuousLinearMap.adjoint V)) := hV_eq σ
  -- pdSet membership of the Stinespring images (re-stated in the form needed
  -- by `sandwichedQuasi_jensen_haar`).
  have hEρ' : TrRight ((V.comp ρ).comp (ContinuousLinearMap.adjoint V)) ∈ pdSet (ℋ := 𝒦) :=
    hEρ_eq ▸ hEρ
  have hEσ' : TrRight ((V.comp σ).comp (ContinuousLinearMap.adjoint V)) ∈ pdSet (ℋ := 𝒦) :=
    hEσ_eq ▸ hEσ
  -- Step 3: the central Q_α-inequality, from `sandwichedQuasi_jensen_haar`.
  have hQ_ineq :
      ((sandwichedQuasi α (E.toLinearMap ρ) (E.toLinearMap σ)).re - (sandwichedQuasi α ρ σ).re) *
        (α - 1) ≤ 0 := by
    have h := sandwichedQuasi_jensen_haar hα_ge hα_ne1 hρ hσ V hV_iso hEρ' hEσ'
    rw [hEρ_eq, hEσ_eq]
    exact h
  -- Step 4: unfold D_α and apply log monotonicity.
  unfold sandwichedRenyiDiv
  -- `E` preserves traces: `Tr (E ρ) = Tr ρ`.
  have hTr_Eρ : (Tr (E.toLinearMap ρ)).re = (Tr ρ).re := by
    rw [CPTPOp.Tr_map]
  -- Positivity of the relevant real parts.
  have hTr_ρ_pos : (0 : ℝ) < (Tr ρ).re := trace_re_pos_of_pdSet hρ
  -- Positivity of `Re sandwichedQuasi α ρ' σ'` for `ρ', σ' ∈ pdSet`: the inner
  -- operator `σ'^β ρ' σ'^β` is pd, hence `(·)^α` is pd, hence the trace is positive.
  have hQ_pos_aux : ∀ {𝒥 : Type u} [Qudit 𝒥] [Nontrivial 𝒥] {ρ' σ' : L 𝒥},
      ρ' ∈ pdSet (ℋ := 𝒥) → σ' ∈ pdSet (ℋ := 𝒥) →
      (0 : ℝ) < (sandwichedQuasi α ρ' σ').re := by
    intro 𝒥 _ _ ρ' σ' hρ' hσ'
    unfold sandwichedQuasi
    have hP_pd : CFC.rpow σ' ((1 - α) / (2 * α)) ∈ pdSet (ℋ := 𝒥) := pdSet_rpow hσ'
    have hP_sa : IsSelfAdjoint (CFC.rpow σ' ((1 - α) / (2 * α))) :=
      IsSelfAdjoint.of_nonneg (nonneg_of_pdSet hP_pd)
    have hP_unit : IsUnit (CFC.rpow σ' ((1 - α) / (2 * α))) := isUnit_of_pdSet hP_pd
    have h_inner_eq :
        CFC.rpow σ' ((1 - α) / (2 * α)) * ρ' * CFC.rpow σ' ((1 - α) / (2 * α)) =
        star (CFC.rpow σ' ((1 - α) / (2 * α))) * ρ' * CFC.rpow σ' ((1 - α) / (2 * α)) := by
      rw [hP_sa.star_eq]
    have h_inner_pd :
        (CFC.rpow σ' ((1 - α) / (2 * α)) * ρ' * CFC.rpow σ' ((1 - α) / (2 * α))) ∈
          pdSet (ℋ := 𝒥) := by
      rw [h_inner_eq]
      exact pdSet_conj hρ' hP_unit
    have h_pow_pd :
        CFC.rpow
            (CFC.rpow σ' ((1 - α) / (2 * α)) * ρ' * CFC.rpow σ' ((1 - α) / (2 * α))) α ∈
          pdSet (ℋ := 𝒥) := pdSet_rpow h_inner_pd
    exact trace_re_pos_of_pdSet h_pow_pd
  have hQρσ_pos : (0 : ℝ) < (sandwichedQuasi α ρ σ).re := hQ_pos_aux hρ hσ
  have hQEρEσ_pos : (0 : ℝ) < (sandwichedQuasi α (E.toLinearMap ρ) (E.toLinearMap σ)).re :=
    hQ_pos_aux hEρ hEσ
  -- Final step: deduce the log inequality.
  -- From `hQ_ineq`: `(Q_α(Eρ,Eσ).re − Q_α(ρ,σ).re) · (α-1) ≤ 0`.
  rcases lt_or_gt_of_ne hα_ne1 with hα_lt | hα_gt
  · -- α < 1: α - 1 < 0
    have hα1_neg : (α - 1 : ℝ) < 0 := by linarith
    have hQ_ge :
        (sandwichedQuasi α ρ σ).re ≤ (sandwichedQuasi α (E.toLinearMap ρ) (E.toLinearMap σ)).re := by
      nlinarith
    have hlog : Real.log ((sandwichedQuasi α ρ σ).re / (Tr ρ).re) ≤
        Real.log ((sandwichedQuasi α (E.toLinearMap ρ) (E.toLinearMap σ)).re /
          (Tr (E.toLinearMap ρ)).re) := by
      rw [hTr_Eρ]
      exact Real.log_le_log (div_pos hQρσ_pos hTr_ρ_pos)
        (div_le_div_of_nonneg_right hQ_ge (le_of_lt hTr_ρ_pos))
    have h1α : (1 / (α - 1) : ℝ) < 0 := by
      rw [one_div]
      exact inv_neg''.mpr hα1_neg
    nlinarith
  · -- α > 1: α - 1 > 0
    have hα1_pos : (0 : ℝ) < α - 1 := by linarith
    have hQ_le' :
        (sandwichedQuasi α (E.toLinearMap ρ) (E.toLinearMap σ)).re ≤ (sandwichedQuasi α ρ σ).re := by
      nlinarith
    have hlog : Real.log ((sandwichedQuasi α (E.toLinearMap ρ) (E.toLinearMap σ)).re /
        (Tr (E.toLinearMap ρ)).re) ≤
          Real.log ((sandwichedQuasi α ρ σ).re / (Tr ρ).re) := by
      rw [hTr_Eρ]
      exact Real.log_le_log (div_pos hQEρEσ_pos hTr_ρ_pos)
        (div_le_div_of_nonneg_right hQ_le' (le_of_lt hTr_ρ_pos))
    have h1α_pos : (0 : ℝ) < 1 / (α - 1) := by
      rw [one_div]
      exact inv_pos.mpr hα1_pos
    exact mul_le_mul_of_nonneg_left hlog (le_of_lt h1α_pos)

/-! ### Extension to non-negative operators (Frank–Lieb, arXiv:1306.5358 Thm 1)

The PDF formulates Theorem 1 for non-negative (rather than positive-definite)
operators `ρ, σ`. The natural extension is via perturbation: replace `ρ, σ` by
their pd perturbations `ρ + ε • 1`, `σ + ε • 1` for `ε > 0`. The existing
theorem applies whenever the four operators (`ρ + ε • 1`, `σ + ε • 1`,
`E (ρ + ε • 1)`, `E (σ + ε • 1)`) are all positive-definite.

For a **faithful** CPTP map `E` (i.e., `E 1` positive-definite), this is
automatic: by linearity of `E`, `E (ρ + ε • 1) = E ρ + ε • E 1`, which is a
non-negative operator plus a positive-definite operator, hence pd.

Below we add the helper lemmas (sum of nonneg and pd is pd, positive scalar
multiple of pd is pd, etc.) and then state the perturbed Theorem 1
`sandwichedRenyiDiv_monotone_nonneg_perturbed`. The "limit version"
(taking `ε → 0+`) requires continuity of `sandwichedRenyiDiv` at the boundary
of `pdSet`, which is finite when the kernels match and `+∞` otherwise.
-/

/-- A positive real scalar multiple of a pd operator is pd. -/
lemma pdSet_pos_smul
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : A ∈ pdSet (ℋ := ℋ)) {c : ℝ} (hc : 0 < c) :
    ((c : ℂ) • A) ∈ pdSet (ℋ := ℋ) := by
  obtain ⟨εA, hεA_pos, hεA_le⟩ := pdSet_exists_pos_lower_bound hA
  obtain ⟨MA, hMA_le⟩ := exists_upper_bound_self_adjoint hA.1
  -- `(c : ℂ) • A = c • A`, using the `ℝ ↪ ℂ` scalar tower.
  have h_smul_eq : (c : ℂ) • A = c • A := Complex.coe_smul c _
  refine pdSubCone_subset_pdSet (ℋ := ℋ) (ε := c * εA) (mul_pos hc hεA_pos)
      (M := c * MA) ⟨?_, ?_⟩
  · rw [h_smul_eq, mul_smul]
    have h_nn : (0 : L ℋ) ≤ c • A - c • (εA • (1 : L ℋ)) := by
      rw [← smul_sub]
      exact smul_nonneg hc.le (sub_nonneg.mpr hεA_le)
    exact sub_nonneg.mp h_nn
  · rw [h_smul_eq, mul_smul]
    have h_nn : (0 : L ℋ) ≤ c • (MA • (1 : L ℋ)) - c • A := by
      rw [← smul_sub]
      exact smul_nonneg hc.le (sub_nonneg.mpr hMA_le)
    exact sub_nonneg.mp h_nn

/-- **Theorem 1, non-negative perturbed version** (Frank–Lieb, arXiv:1306.5358).

    For any quantum channel `E : CPTPOp ℋ ℋ` whose unital image `E 1` is
    positive-definite (i.e., `E` is *faithful*), any `α ∈ [1/2, 1) ∪ (1, ∞)`,
    any **non-negative** `ρ, σ`, and any `ε > 0`:

      `D_α(E(ρ + ε•1) ‖ E(σ + ε•1)) ≤ D_α(ρ + ε•1 ‖ σ + ε•1)`.

    This is the perturbed form of Frank–Lieb's monotonicity theorem extended
    from positive-definite to non-negative operators. The unperturbed
    inequality (i.e., `D_α(E ρ ‖ E σ) ≤ D_α(ρ ‖ σ)` for non-negative `ρ, σ`
    using the extended definition with `+∞` for divergent cases) is recovered
    as `ε → 0+` via continuity of `D_α` (finite case) or vacuously (when both
    sides diverge to `+∞`). -/
theorem sandwichedRenyiDiv_monotone_nonneg_perturbed
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTPOp ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hEI : E.toLinearMap (1 : L ℋ) ∈ pdSet (ℋ := 𝒦))
    {ε : ℝ} (hε : 0 < ε) :
    sandwichedRenyiDiv α (E.toLinearMap (ρ + (ε : ℂ) • (1 : L ℋ)))
        (E.toLinearMap (σ + (ε : ℂ) • (1 : L ℋ))) ≤
      sandwichedRenyiDiv α (ρ + (ε : ℂ) • (1 : L ℋ)) (σ + (ε : ℂ) • (1 : L ℋ)) := by
  -- Positivity of `E` is automatic for completely-positive maps.
  have hE_pos : ∀ {X : L ℋ}, 0 ≤ X → 0 ≤ E.toLinearMap X := fun {_} hX => E.pos hX
  -- Perturbed operators are pd.
  have hρ_ε : (ρ + (ε : ℂ) • (1 : L ℋ)) ∈ pdSet (ℋ := ℋ) :=
    nonneg_add_pos_smul_one_pdSet hρ hε
  have hσ_ε : (σ + (ε : ℂ) • (1 : L ℋ)) ∈ pdSet (ℋ := ℋ) :=
    nonneg_add_pos_smul_one_pdSet hσ hε
  -- `E` is linear, so `E(ρ + ε • 1) = E ρ + ε • E 1`, and similarly for σ.
  have hE_linear : ∀ X, E.toLinearMap (X + (ε : ℂ) • (1 : L ℋ)) =
      E.toLinearMap X + (ε : ℂ) • E.toLinearMap (1 : L ℋ) := fun X => by
    rw [map_add, map_smul]
  -- `E(ρ + ε • 1) = E ρ + ε • E 1` is pd (non-negative + ε • pd).
  have hEρ_ε : E.toLinearMap (ρ + (ε : ℂ) • (1 : L ℋ)) ∈ pdSet (ℋ := 𝒦) := by
    rw [hE_linear]
    exact pdSet_add_nonneg (hE_pos hρ) (pdSet_pos_smul hEI hε)
  have hEσ_ε : E.toLinearMap (σ + (ε : ℂ) • (1 : L ℋ)) ∈ pdSet (ℋ := 𝒦) := by
    rw [hE_linear]
    exact pdSet_add_nonneg (hE_pos hσ) (pdSet_pos_smul hEI hε)
  -- Apply the pd Theorem 1.
  exact sandwichedRenyiDiv_monotone E hα_ge hα_ne1 hρ_ε hσ_ε hEρ_ε hEσ_ε

/-- The unit operator `1 : L ℋ` is positive-definite. -/
lemma one_pdSet {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] :
    (1 : L ℋ) ∈ pdSet (ℋ := ℋ) := by
  have h := pos_smul_one_pdSet (ℋ := ℋ) (one_pos : (0 : ℝ) < 1)
  rwa [show ((1 : ℝ) : ℂ) = 1 from by norm_cast, one_smul] at h

/-- For `σ ∈ pdSet`, the kernel is trivial: `ker σ = ⊥`. -/
lemma ker_eq_bot_of_pdSet
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {σ : L ℋ} (hσ : σ ∈ pdSet (ℋ := ℋ)) :
    LinearMap.ker (σ : ℋ →ₗ[ℂ] ℋ) = ⊥ := by
  obtain ⟨u, hu⟩ := isUnit_of_pdSet hσ
  rw [LinearMap.ker_eq_bot]
  intro x y hxy
  -- `u.inv * σ = 1` in `L ℋ`; apply to both sides.
  have h_invσ : (u.inv : L ℋ) * σ = 1 := by
    rw [← hu]
    exact u.inv_val
  -- For `f g : L ℋ` and `z : ℋ`, `(f * g) z = f (g z)` definitionally.
  have h_apply : ∀ z : ℋ, (u.inv : L ℋ) (σ z) = z := fun z => by
    have h : ((u.inv : L ℋ) * σ) z = z := by
      rw [h_invσ]
      rfl
    exact h
  rw [← h_apply x, ← h_apply y]
  exact congrArg _ hxy


end SandwichedRenyiRelativeEntropy
