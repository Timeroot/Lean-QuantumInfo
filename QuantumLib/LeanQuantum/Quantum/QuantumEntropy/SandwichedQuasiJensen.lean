/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.SandwichedRenyiRelativeEntropy
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
   `Re Q_α(ρ‖σ)`. Proved by passing to a closed convex sub-cone of `pdSetLM`
   cut out by explicit spectral bounds and applying Mathlib's Bochner-integral
   Jensen (`HaarUnitary.jointly_convex_integral_le` /
   `HaarUnitary.jointly_concave_le_integral`).

2. `sandwichedQuasi_jensen_haar` — the abstract Jensen–Haar interface, obtained
   from `jensen_haar_core` by tensor multiplicativity and the self-quasi
   identity `sandwichedQuasi α τ τ = Tr τ`.

3. `sandwichedRenyiDiv_monotone` — the main theorem
   `D_α(E ρ ‖ E σ) ≤ D_α(ρ ‖ σ)`, obtained from `sandwichedQuasi_jensen_haar`
   by applying the Stinespring dilation (`CPTP.exists_stinespring_dilation`)
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

set_option linter.style.longLine false

/-- The real scalars act on `L ℋ` compatibly through `ℂ`. This `Prop`-valued
    instance is needed by the `ℝ`-valued (non-unital) functional-calculus
    naturality lemma `NonUnitalStarAlgHomClass.map_cfcₙ`. -/
instance instIsScalarTowerRealComplexL {ℋ : Type u} [Qudit ℋ] :
    IsScalarTower ℝ ℂ (L ℋ) where
  smul_assoc r c x := by
    change (algebraMap ℝ ℂ r * c) • x = (algebraMap ℝ ℂ r) • (c • x)
    rw [mul_smul]

/-! ### Spectral bounds for operators in `pdSetLM` -/

/-- For any `A ∈ pdSetLM`, there exists a positive real `ε` such that
    `ε • 1 ≤ A.toCLM` in the CLM order. -/
private lemma pdSetLM_exists_pos_lower_bound {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    ∃ ε : ℝ, 0 < ε ∧
      (ε • (1 : LownerHeinzTheorem.L ℋ) : LownerHeinzTheorem.L ℋ) ≤
        A.toContinuousLinearMap := by
  obtain ⟨hA_sa, hA_spec⟩ := hA
  obtain ⟨r, hr_pos, hr_le⟩ : ∃ r > 0, algebraMap ℝ (LownerHeinzTheorem.L ℋ) r ≤
      A.toContinuousLinearMap :=
    (CFC.exists_pos_algebraMap_le_iff hA_sa).mpr fun _x hx => hA_spec hx
  refine ⟨r, hr_pos, ?_⟩
  rwa [Algebra.algebraMap_eq_smul_one] at hr_le

/-- For any self-adjoint element `A` in a `CStarAlgebra` of operators on a
    finite-dim Hilbert space, there exists `M` such that `A ≤ M • 1`
    (we may take `M = ‖A‖`). -/
private lemma exists_upper_bound_self_adjoint {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : LownerHeinzTheorem.L ℋ} (hA : IsSelfAdjoint A) :
    ∃ M : ℝ, A ≤ (M • (1 : LownerHeinzTheorem.L ℋ) : LownerHeinzTheorem.L ℋ) := by
  refine ⟨‖A‖, ?_⟩
  rw [show (‖A‖ • (1 : LownerHeinzTheorem.L ℋ) : LownerHeinzTheorem.L ℋ) =
    algebraMap ℝ (LownerHeinzTheorem.L ℋ) ‖A‖ from
      (Algebra.algebraMap_eq_smul_one ‖A‖).symm]
  exact hA.le_algebraMap_norm_self

/-! ### The closed convex sub-cone -/

/-- The closed convex sub-cone of `L ℋ` cut out by `ε • 1 ≤ A ≤ M • 1` (in the
    CLM order, transferred along `toContinuousLinearMap`). -/
private def pdSubCone {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (ε M : ℝ) : Set (L ℋ) :=
  {A | ε • (1 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap ∧
       A.toContinuousLinearMap ≤ M • (1 : LownerHeinzTheorem.L ℋ)}

/-- Monotonicity of the scalar-times-1 map in the CLM order: `r ≤ r'` implies
    `r • 1 ≤ r' • 1`. -/
private lemma smul_one_le_smul_one {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {r r' : ℝ} (hrr' : r ≤ r') :
    r • (1 : LownerHeinzTheorem.L ℋ) ≤ r' • (1 : LownerHeinzTheorem.L ℋ) := by
  have h_zero_le_one : (0 : LownerHeinzTheorem.L ℋ) ≤ 1 := zero_le_one
  have h_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ (r' - r) • (1 : LownerHeinzTheorem.L ℋ) :=
    smul_nonneg (sub_nonneg.mpr hrr') h_zero_le_one
  rw [sub_smul] at h_nn
  exact sub_nonneg.mp h_nn

/-- The sub-cone is convex. -/
private lemma pdSubCone_convex {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (ε M : ℝ) :
    Convex ℝ (pdSubCone (ℋ := ℋ) ε M) := by
  intro a ha b hb θ θ' hθ hθ' hsum
  refine ⟨?_, ?_⟩
  · have hA := ha.1
    have hB := hb.1
    have : ((θ : ℝ) • a + (θ' : ℝ) • b).toContinuousLinearMap =
        (θ : ℝ) • a.toContinuousLinearMap + (θ' : ℝ) • b.toContinuousLinearMap := by
      ext x; rfl
    rw [this]
    calc ε • (1 : LownerHeinzTheorem.L ℋ)
        = (θ + θ') • (ε • (1 : LownerHeinzTheorem.L ℋ)) := by rw [hsum]; simp
      _ = θ • (ε • (1 : LownerHeinzTheorem.L ℋ)) + θ' • (ε • (1 : LownerHeinzTheorem.L ℋ)) := by
          rw [add_smul]
      _ ≤ θ • a.toContinuousLinearMap + θ' • b.toContinuousLinearMap := by
          apply add_le_add
          · exact smul_le_smul_of_nonneg_left hA hθ
          · exact smul_le_smul_of_nonneg_left hB hθ'
  · have hA := ha.2
    have hB := hb.2
    have : ((θ : ℝ) • a + (θ' : ℝ) • b).toContinuousLinearMap =
        (θ : ℝ) • a.toContinuousLinearMap + (θ' : ℝ) • b.toContinuousLinearMap := by
      ext x; rfl
    rw [this]
    calc (θ : ℝ) • a.toContinuousLinearMap + (θ' : ℝ) • b.toContinuousLinearMap
        ≤ θ • (M • (1 : LownerHeinzTheorem.L ℋ)) + θ' • (M • (1 : LownerHeinzTheorem.L ℋ)) := by
          apply add_le_add
          · exact smul_le_smul_of_nonneg_left hA hθ
          · exact smul_le_smul_of_nonneg_left hB hθ'
      _ = (θ + θ') • (M • (1 : LownerHeinzTheorem.L ℋ)) := by rw [add_smul]
      _ = M • (1 : LownerHeinzTheorem.L ℋ) := by rw [hsum]; simp

/-- The sub-cone is closed (preimage of the closed interval `Icc (ε•1) (M•1)`
    in the CLM order under the continuous `toContinuousLinearMap`). -/
private lemma pdSubCone_isClosed {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (ε M : ℝ) :
    IsClosed (pdSubCone (ℋ := ℋ) ε M) := by
  have h_toCLM_cont : Continuous (fun A : L ℋ => A.toContinuousLinearMap) :=
    linear_isometry_equiv.continuous
  have h_eq : pdSubCone (ℋ := ℋ) ε M =
      (fun A : L ℋ => A.toContinuousLinearMap) ⁻¹'
        (Set.Icc (ε • (1 : LownerHeinzTheorem.L ℋ)) (M • (1 : LownerHeinzTheorem.L ℋ))) := by
    ext A
    simp only [pdSubCone, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc]
  rw [h_eq]
  exact isClosed_Icc.preimage h_toCLM_cont

/-- Auxiliary: for unitary `V` in CLM, `V * (r • 1) * V* = r • 1`. -/
private lemma smul_one_conj_unitary_eq {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (r : ℝ) {V : LownerHeinzTheorem.L ℋ} (hV : V * star V = 1) :
    V * (r • (1 : LownerHeinzTheorem.L ℋ)) * star V = r • (1 : LownerHeinzTheorem.L ℋ) :=
  calc V * (r • (1 : LownerHeinzTheorem.L ℋ)) * star V
      = r • (V * 1 * star V) := by rw [mul_smul_comm, smul_mul_assoc]
    _ = r • (V * star V) := by rw [mul_one]
    _ = r • (1 : LownerHeinzTheorem.L ℋ) := by rw [hV]

/-- For unitary `u : L ℋ₁`, `TensorProduct.map u 1` is unitary on `L (ℋ₁ ⊗[ℂ] ℋ₂)`. -/
private lemma tensorMap_unitary_of_unitary
    {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂] [Nontrivial ℋ₁] [Nontrivial ℋ₂]
    (u : unitary (L ℋ₁)) :
    TensorProduct.map (u : L ℋ₁) (LinearMap.id (M := ℋ₂)) ∈
      unitary (L (ℋ₁ ⊗[ℂ] ℋ₂)) := by
  -- `star (TensorProduct.map u id) = TensorProduct.map (star u) id`.
  have h_id_sa : star (LinearMap.id : L ℋ₂) = LinearMap.id := by
    have h_id_one : (LinearMap.id : L ℋ₂) = 1 := rfl
    rw [h_id_one, IsSelfAdjoint.star_eq (IsSelfAdjoint.one (R := L ℋ₂))]
  have h_star_eq :
      star (TensorProduct.map (u : L ℋ₁) (LinearMap.id (M := ℋ₂)) : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      TensorProduct.map (star (u : L ℋ₁)) (LinearMap.id (M := ℋ₂)) := by
    rw [LinearMap.star_eq_adjoint, TensorProduct.adjoint_map]
    rw [← LinearMap.star_eq_adjoint, ← LinearMap.star_eq_adjoint, h_id_sa]
  have h_id_mul_id : (LinearMap.id : L ℋ₂) * LinearMap.id = 1 := mul_one _
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
  · -- star (T(u,1)) * T(u,1) = T(star u * u, 1 * 1) = T(1, 1) = 1
    rw [h_star_eq, ← TensorProduct.map_mul, (Unitary.mem_iff.mp u.property).1, h_id_mul_id]
    exact TensorProduct.map_one
  · rw [h_star_eq, ← TensorProduct.map_mul, (Unitary.mem_iff.mp u.property).2, h_id_mul_id]
    exact TensorProduct.map_one

/-- `star (1 ⊗ g) = 1 ⊗ (star g)` for the right tensor factor. -/
private lemma tensorMap_right_star {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]
    (g : L ℋ₂) :
    star (TensorProduct.map (LinearMap.id (M := ℋ₁)) g : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      TensorProduct.map (LinearMap.id (M := ℋ₁)) (star g) := by
  have h_id_sa : star (LinearMap.id : L ℋ₁) = LinearMap.id := by
    rw [show (LinearMap.id : L ℋ₁) = 1 from rfl,
        IsSelfAdjoint.star_eq (IsSelfAdjoint.one (R := L ℋ₁))]
  rw [LinearMap.star_eq_adjoint, TensorProduct.adjoint_map, ← LinearMap.star_eq_adjoint,
      ← LinearMap.star_eq_adjoint, h_id_sa]

/-- For unitary `u : L ℋ₂`, `TensorProduct.map 1 u` is unitary on `L (ℋ₁ ⊗[ℂ] ℋ₂)`. -/
private lemma tensorMap_right_unitary_of_unitary
    {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂] [Nontrivial ℋ₁] [Nontrivial ℋ₂]
    (u : unitary (L ℋ₂)) :
    TensorProduct.map (LinearMap.id (M := ℋ₁)) ((u : L ℋ₂)) ∈
      unitary (L (ℋ₁ ⊗[ℂ] ℋ₂)) := by
  have h_id_mul_id : (LinearMap.id : L ℋ₁) * LinearMap.id = 1 := mul_one _
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
  · rw [tensorMap_right_star, ← TensorProduct.map_mul, h_id_mul_id,
        (Unitary.mem_iff.mp u.property).1]
    exact TensorProduct.map_one
  · rw [tensorMap_right_star, ← TensorProduct.map_mul, h_id_mul_id,
        (Unitary.mem_iff.mp u.property).2]
    exact TensorProduct.map_one

/-- The non-negative cone `{A | 0 ≤ A}` in `L 𝒦` is convex. -/
private lemma convex_nonneg_cone {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] :
    Convex ℝ {A : L 𝒦 | (0 : L 𝒦) ≤ A} := by
  intro a ha b hb θ θ' hθ hθ' _hsum
  simp only [Set.mem_setOf_eq] at ha hb ⊢
  exact add_nonneg (smul_nonneg hθ ha) (smul_nonneg hθ' hb)

/-- The non-negative cone `{A | 0 ≤ A}` in `L 𝒦` is closed (transferred along the
    continuous isometry `toContinuousLinearMap` to the closed positive cone in the
    C⋆-algebra of continuous operators). -/
private lemma isClosed_nonneg_cone {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] :
    IsClosed {A : L 𝒦 | (0 : L 𝒦) ≤ A} := by
  have h_toCLM_cont : Continuous (fun A : L 𝒦 => A.toContinuousLinearMap) :=
    linear_isometry_equiv.continuous
  have h_eq : {A : L 𝒦 | (0 : L 𝒦) ≤ A} =
      (fun A : L 𝒦 => A.toContinuousLinearMap) ⁻¹' (Set.Ici 0) := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici]
    rw [LinearMap.nonneg_iff_isPositive, ContinuousLinearMap.nonneg_iff_isPositive,
        LinearMap.isPositive_toContinuousLinearMap_iff]
  rw [h_eq]
  exact isClosed_Ici.preimage h_toCLM_cont

/-- Unitary conjugation preserves the closed convex sub-cone `pdSubCone ε M`. -/
private lemma pdSubCone_unitary_conj {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {ε M : ℝ} {A : L ℋ} (hA : A ∈ pdSubCone (ℋ := ℋ) ε M)
    (V : unitary (L ℋ)) :
    (V : L ℋ) * A * star (V : L ℋ) ∈ pdSubCone (ℋ := ℋ) ε M := by
  obtain ⟨hA_lower, hA_upper⟩ := hA
  -- Transfer to CLM: `(V * A * star V).toCLM = V.toCLM * A.toCLM * star V.toCLM`.
  have h_star_toCLM : (star (V : L ℋ)).toContinuousLinearMap =
      star ((V : L ℋ).toContinuousLinearMap) := by
    rw [LinearMap.star_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap,
        ContinuousLinearMap.star_eq_adjoint]
  have h_toCLM_eq : ((V : L ℋ) * A * star (V : L ℋ)).toContinuousLinearMap =
      (V : L ℋ).toContinuousLinearMap * A.toContinuousLinearMap *
        star ((V : L ℋ).toContinuousLinearMap) := by
    rw [show ((V : L ℋ) * A * star (V : L ℋ)).toContinuousLinearMap =
      (V : L ℋ).toContinuousLinearMap * A.toContinuousLinearMap *
      (star (V : L ℋ)).toContinuousLinearMap from by ext x; rfl, h_star_toCLM]
  -- V * star V = 1 in CLM.
  have hVV_LM : (V : L ℋ) * star (V : L ℋ) = 1 := (Unitary.mem_iff.mp V.property).2
  have hVV_CLM : (V : L ℋ).toContinuousLinearMap * star ((V : L ℋ).toContinuousLinearMap) = 1 := by
    rw [← h_star_toCLM]
    rw [show (V : L ℋ).toContinuousLinearMap * (star (V : L ℋ)).toContinuousLinearMap =
        ((V : L ℋ) * star (V : L ℋ)).toContinuousLinearMap from by ext x; rfl, hVV_LM]
    rfl
  -- For each scalar r, `V * (r • 1) * V* = r • 1`.
  have h_eps : (V : L ℋ).toContinuousLinearMap * (ε • (1 : LownerHeinzTheorem.L ℋ)) *
      star ((V : L ℋ).toContinuousLinearMap) = ε • (1 : LownerHeinzTheorem.L ℋ) :=
    smul_one_conj_unitary_eq ε hVV_CLM
  have h_M : (V : L ℋ).toContinuousLinearMap * (M • (1 : LownerHeinzTheorem.L ℋ)) *
      star ((V : L ℋ).toContinuousLinearMap) = M • (1 : LownerHeinzTheorem.L ℋ) :=
    smul_one_conj_unitary_eq M hVV_CLM
  refine ⟨?_, ?_⟩
  · -- ε • 1 ≤ (V * A * V*).toCLM
    rw [h_toCLM_eq, ← h_eps]
    -- Show: V * (ε • 1) * V* ≤ V * A.toCLM * V* via `star_left_conjugate` on the difference.
    have h_diff_nn : (0 : LownerHeinzTheorem.L ℋ) ≤
        A.toContinuousLinearMap - ε • (1 : LownerHeinzTheorem.L ℋ) := sub_nonneg.mpr hA_lower
    have h_conj_nn := star_left_conjugate_nonneg h_diff_nn (star ((V : L ℋ).toContinuousLinearMap))
    rw [star_star] at h_conj_nn
    rw [mul_sub, sub_mul] at h_conj_nn
    exact sub_nonneg.mp h_conj_nn
  · -- (V * A * V*).toCLM ≤ M • 1
    rw [h_toCLM_eq, ← h_M]
    have h_diff_nn : (0 : LownerHeinzTheorem.L ℋ) ≤
        M • (1 : LownerHeinzTheorem.L ℋ) - A.toContinuousLinearMap := sub_nonneg.mpr hA_upper
    have h_conj_nn := star_left_conjugate_nonneg h_diff_nn (star ((V : L ℋ).toContinuousLinearMap))
    rw [star_star] at h_conj_nn
    rw [mul_sub, sub_mul] at h_conj_nn
    exact sub_nonneg.mp h_conj_nn

/-- The sub-cone is contained in `pdSetLM` when `ε > 0`. -/
private lemma pdSubCone_subset_pdSetLM {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {ε M : ℝ} (hε : 0 < ε) : pdSubCone (ℋ := ℋ) ε M ⊆ pdSetLM (ℋ := ℋ) := by
  intro A ⟨h_lower, _⟩
  -- Use that `ε • 1 = algebraMap ℝ _ ε` and that `algebraMap ε ≤ A.toCLM` gives both
  -- self-adjointness (positivity) and the spectrum bound.
  have h_eq : ε • (1 : LownerHeinzTheorem.L ℋ) = algebraMap ℝ (LownerHeinzTheorem.L ℋ) ε := by
    rw [Algebra.algebraMap_eq_smul_one]
  rw [h_eq] at h_lower
  -- `0 ≤ ε • 1` for ε ≥ 0, hence `0 ≤ A.toCLM`.
  have h_pos_1 : (0 : LownerHeinzTheorem.L ℋ) ≤ algebraMap ℝ (LownerHeinzTheorem.L ℋ) ε := by
    have h_one_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ 1 := zero_le_one
    rw [← h_eq]
    exact smul_nonneg hε.le h_one_nn
  have h_A_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap :=
    le_trans h_pos_1 h_lower
  have h_A_sa : IsSelfAdjoint A.toContinuousLinearMap := IsSelfAdjoint.of_nonneg h_A_nn
  refine ⟨h_A_sa, ?_⟩
  intro r hr
  have h_spec_ge : ∀ x ∈ spectrum ℝ A.toContinuousLinearMap, ε ≤ x :=
    (algebraMap_le_iff_le_spectrum (R := ℝ)).mp h_lower
  exact lt_of_lt_of_le hε (h_spec_ge r hr)

/-! ### Helper lemmas for the Form A Jensen–Haar proof -/

/-- **Right-twirl identity** (TrRight analogue of
    `HaarUnitary.twirl_eq_partialTrace_smul_id`).

    For any `X ∈ L(ℋ ⊗ ℋ_env)`,
    `∫ (1 ⊗ u) X (1 ⊗ u*) du = TrRight X ⊗ ((dim ℋ_env)⁻¹ • 1)`,

    where the integral is taken over the normalized Haar measure on
    `unitary (L ℋ_env)`.

    Derived from `twirl_eq_partialTrace_smul_id` by symmetry of the tensor
    factors. The proof composes both sides with `TensorProduct.comm` (or
    equivalently, uses `TrRight = Tr₂ ∘ conjugateEnd (TensorProduct.comm)`). -/
private lemma right_twirl_eq
    {𝒦 : Type u} [Qudit 𝒦]
    {ℋ_env : Type u} [Qudit ℋ_env] [Nontrivial ℋ_env]
    (X : L (𝒦 ⊗[ℂ] ℋ_env)) :
    ∫ u : unitary (L ℋ_env),
        TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)) * X *
          TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env))
      ∂(HaarUnitary.haarUnitary ℋ_env) =
    TensorProduct.map (QuantumChannel.TrRight X)
      ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • LinearMap.id (M := ℋ_env)) :=
  HaarUnitary.twirl_eq_partialTrace_right_smul_id X

/-- **Non-unital ⋆-algebra hom** `σ ↦ V σ V*` for an isometric `V` (`V*V = 1`).
    This is multiplicative because of `V*V = 1`, and `*`-preserving in general.
    It is non-unital because `1 ↦ V V* ≠ 1` when `V` is not surjective. -/
private noncomputable def isometricConjHom
    {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →ₗ[ℂ] ℋ')
    (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ)) :
    L ℋ →⋆ₙₐ[ℂ] L ℋ' where
  toFun σ := (V.comp σ).comp (LinearMap.adjoint V)
  map_add' σ τ := by
    change (V.comp (σ + τ)).comp (LinearMap.adjoint V) =
         (V.comp σ).comp (LinearMap.adjoint V) + (V.comp τ).comp (LinearMap.adjoint V)
    rw [LinearMap.comp_add, LinearMap.add_comp]
  map_smul' c σ := by
    change (V.comp (c • σ)).comp (LinearMap.adjoint V) =
         c • ((V.comp σ).comp (LinearMap.adjoint V))
    rw [LinearMap.comp_smul, LinearMap.smul_comp]
  map_zero' := by
    change (V.comp 0).comp (LinearMap.adjoint V) = 0
    rw [LinearMap.comp_zero, LinearMap.zero_comp]
  map_mul' σ τ := by
    change (V.comp (σ * τ)).comp (LinearMap.adjoint V) =
         ((V.comp σ).comp (LinearMap.adjoint V)) * ((V.comp τ).comp (LinearMap.adjoint V))
    -- (σ * τ) = σ ∘ₗ τ in `L ℋ`; reduce to function equality.
    ext x
    change V (((σ : L ℋ) * τ) ((LinearMap.adjoint V) x)) =
         V (σ ((LinearMap.adjoint V) (V (τ ((LinearMap.adjoint V) x)))))
    -- (σ * τ) y = σ (τ y); use V.adjoint.comp V = 1.
    have h_id : ∀ y : ℋ, (LinearMap.adjoint V) (V y) = y := fun y => by
      have := LinearMap.congr_fun hV y
      simpa [LinearMap.comp_apply] using this
    change V (σ (τ ((LinearMap.adjoint V) x))) =
         V (σ ((LinearMap.adjoint V) (V (τ ((LinearMap.adjoint V) x)))))
    rw [h_id]
  map_star' σ := by
    change (V.comp (star σ)).comp (LinearMap.adjoint V) =
         star ((V.comp σ).comp (LinearMap.adjoint V))
    rw [show (star σ : L ℋ) = LinearMap.adjoint σ from LinearMap.star_eq_adjoint σ,
        show (star ((V.comp σ).comp (LinearMap.adjoint V)) : L ℋ') =
             LinearMap.adjoint ((V.comp σ).comp (LinearMap.adjoint V)) from
             LinearMap.star_eq_adjoint _,
        LinearMap.adjoint_comp, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
        ← LinearMap.comp_assoc]

/-- The isometric-conjugation map `σ ↦ V σ V*` as a *linear* map; this captures the
    underlying linear structure separately from the `NonUnitalStarAlgHom`. -/
private noncomputable def isometricConjLM
    {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →ₗ[ℂ] ℋ') : L ℋ →ₗ[ℂ] L ℋ' where
  toFun σ := (V.comp σ).comp (LinearMap.adjoint V)
  map_add' σ τ := by
    rw [LinearMap.comp_add, LinearMap.add_comp]
  map_smul' c σ := by
    rw [LinearMap.comp_smul, LinearMap.smul_comp]; rfl

/-- Continuity of the isometric-conjugation map (needed to apply `map_cfcₙ`).
    Follows from `continuous_of_finiteDimensional` on the underlying linear map. -/
private lemma isometricConjHom_continuous
    {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →ₗ[ℂ] ℋ')
    (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ)) :
    Continuous (isometricConjHom V hV) := by
  -- The underlying function of isometricConjHom and isometricConjLM are the same.
  have h_coe : (isometricConjHom V hV : L ℋ → L ℋ') = isometricConjLM V := rfl
  rw [h_coe]
  exact (isometricConjLM V).continuous_of_finiteDimensional

/-- The `ℝ`-quasispectrum of any operator on a finite-dimensional qudit is finite:
    `spectrum ℂ a` is finite (`Module.End.finite_spectrum`), `spectrum ℝ a` is its
    preimage under the injective `algebraMap ℝ ℂ`, and the quasispectrum adds only `0`. -/
private lemma quasispectrum_finite {ℋ : Type u} [Qudit ℋ] (a : L ℋ) :
    (quasispectrum ℝ a).Finite := by
  have hC : (spectrum ℂ a).Finite := Module.End.finite_spectrum a
  have hsp : (spectrum ℝ a).Finite := by
    rw [(spectrum.preimage_algebraMap ℂ (a := a)).symm]
    exact hC.preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn
  rw [quasispectrum_eq_spectrum_union_zero]
  exact hsp.union (Set.finite_singleton 0)

/-- **Isometric `rpow` covariance.** For an isometry `V` with `V*V = 1`, a non-negative
    `ω`, and any *nonzero* real `p`: `(V ω V*)^p = V (ω^p) V*`. This is valid even for
    `p < 0`: the function `x ↦ x ^ p` is globally discontinuous at `0`, but the
    quasispectrum of any operator here is finite (so `0` is isolated), hence the function
    is `ContinuousOn` it and the non-unital ⋆-hom naturality `map_cfcₙ` applies. -/
private lemma isometricConj_rpow {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →ₗ[ℂ] ℋ') (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ))
    {ω : L ℋ} (hω : (0 : L ℋ) ≤ ω) {p : ℝ} (hp : p ≠ 0) :
    CFC.rpow ((V.comp ω).comp (LinearMap.adjoint V)) p =
      (V.comp (CFC.rpow ω p)).comp (LinearMap.adjoint V) := by
  set φ : L ℋ →⋆ₙₐ[ℂ] L ℋ' := isometricConjHom V hV with hφ_def
  have hφ_cont : Continuous φ := isometricConjHom_continuous V hV
  have hφ_apply : ∀ ν : L ℋ, φ ν = (V.comp ν).comp (LinearMap.adjoint V) := fun _ => rfl
  have hφ_nn : (0 : L ℋ') ≤ φ ω := by
    rw [hφ_apply, LinearMap.nonneg_iff_isPositive]
    exact ((LinearMap.nonneg_iff_isPositive _).mp hω).conj_adjoint V
  let f : ℝ → ℝ := fun x => x ^ p
  have hf_zero : f 0 = 0 := by simp [f, Real.zero_rpow hp]
  have h_Vω_eq : φ ω = (V.comp ω).comp (LinearMap.adjoint V) := hφ_apply ω
  have h_rpow_eq_ω : CFC.rpow ω p = cfc f ω := CFC.rpow_eq_cfc_real (ha := hω)
  have h_rpow_eq_Vω : CFC.rpow ((V.comp ω).comp (LinearMap.adjoint V)) p =
      cfc f ((V.comp ω).comp (LinearMap.adjoint V)) := by
    have := CFC.rpow_eq_cfc_real (a := φ ω) (y := p) (ha := hφ_nn)
    rw [h_Vω_eq] at this; exact this
  rw [h_rpow_eq_ω, h_rpow_eq_Vω]
  have hcont_ω : ContinuousOn f (quasispectrum ℝ ω) := (quasispectrum_finite ω).continuousOn _
  have hcont_Vω : ContinuousOn f (quasispectrum ℝ (φ ω)) :=
    (quasispectrum_finite (φ ω)).continuousOn _
  have h_cfcₙ_eq_ω : cfcₙ f ω = cfc f ω := cfcₙ_eq_cfc hcont_ω hf_zero
  have h_cfcₙ_eq_Vω : cfcₙ f (φ ω) = cfc f (φ ω) := cfcₙ_eq_cfc hcont_Vω hf_zero
  have h_map : φ (cfcₙ f ω) = cfcₙ f (φ ω) :=
    NonUnitalStarAlgHomClass.map_cfcₙ (S := ℂ) φ f ω hcont_ω hf_zero hφ_cont
      (IsSelfAdjoint.of_nonneg hω) (IsSelfAdjoint.of_nonneg hφ_nn)
  change cfc f ((V.comp ω).comp (LinearMap.adjoint V)) =
      (V.comp (cfc f ω)).comp (LinearMap.adjoint V)
  rw [← h_Vω_eq, ← h_cfcₙ_eq_Vω, ← h_map, h_cfcₙ_eq_ω, hφ_apply]

/-- **Isometric invariance of sandwichedQuasi** (valid for all `α > 0`, `α ≠ 1`).

    For an isometry `V : ℋ →ₗ[ℂ] ℋ'` with `V*V = I` and `ρ, σ ≥ 0`,
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
    (V : ℋ →ₗ[ℂ] ℋ')
    (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ))
    {α : ℝ} (hα0 : 0 < α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : (0 : L ℋ) ≤ ρ) (hσ : (0 : L ℋ) ≤ σ) :
    sandwichedQuasi α ((V.comp ρ).comp (LinearMap.adjoint V))
        ((V.comp σ).comp (LinearMap.adjoint V)) =
      sandwichedQuasi α ρ σ := by
  set φ : L ℋ →⋆ₙₐ[ℂ] L ℋ' := isometricConjHom V hV with hφ_def
  have hφ_cont : Continuous φ := isometricConjHom_continuous V hV
  -- φ applied to σ unfolds to (V σ V*).
  have hφ_apply : ∀ ω : L ℋ, φ ω = (V.comp ω).comp (LinearMap.adjoint V) := fun _ => rfl
  -- φ ω ≥ 0 when ω ≥ 0 (positive *-hom).
  have hφ_nn : ∀ {ω : L ℋ}, (0 : L ℋ) ≤ ω → (0 : L ℋ') ≤ φ ω := by
    intro ω hω
    rw [hφ_apply, LinearMap.nonneg_iff_isPositive]
    exact ((LinearMap.nonneg_iff_isPositive _).mp hω).conj_adjoint V
  -- V*V = 1 reduces (V σ V*)(V τ V*) = V (σ τ) V*.
  have h_VV_id : ∀ y : ℋ, (LinearMap.adjoint V) (V y) = y := fun y => by
    have := LinearMap.congr_fun hV y
    simpa [LinearMap.comp_apply] using this
  -- Cyclic trace identity Tr(V X V*) = Tr X.
  have h_tr_conj : ∀ X : L ℋ, Tr ((V.comp X).comp (LinearMap.adjoint V)) = Tr X := by
    intro X
    have h_assoc : (V.comp X).comp (LinearMap.adjoint V) =
        V.comp (X.comp (LinearMap.adjoint V)) := by
      rw [LinearMap.comp_assoc]
    rw [h_assoc, LinearMap.trace_comp_comm']
    -- Tr ((X ∘ V*) ∘ V) = Tr (X ∘ (V* ∘ V)) = Tr (X ∘ 1) = Tr X
    rw [LinearMap.comp_assoc, hV]
    rfl
  -- Step 1: rpow conjugation `CFC.rpow (V ω V*) p = V (CFC.rpow ω p) V*` for `ω ≥ 0`,
  -- `p ≠ 0` (the extracted `isometricConj_rpow`).
  have h_rpow_conj : ∀ {ω : L ℋ} (_hω : (0 : L ℋ) ≤ ω) {p : ℝ} (hp : p ≠ 0),
      CFC.rpow ((V.comp ω).comp (LinearMap.adjoint V)) p =
        (V.comp (CFC.rpow ω p)).comp (LinearMap.adjoint V) := by
    intro ω hω p hp; exact isometricConj_rpow V hV hω hp
  -- Now compute the sandwichedQuasi identity.
  unfold sandwichedQuasi
  set β := (1 - α) / (2 * α) with hβ_def
  have hα_pos : 0 < α := hα0
  have hβ_ne : β ≠ 0 := by
    rw [hβ_def]
    exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hα_ne1)) (by positivity)
  -- Step 2: (V σ V*)^β = V (σ^β) V*.
  rw [h_rpow_conj hσ hβ_ne]
  -- Step 3: V (σ^β) V* · V ρ V* · V (σ^β) V* = V (σ^β · ρ · σ^β) V*. Uses V*V = 1.
  have h_inner : (V.comp (CFC.rpow σ β)).comp (LinearMap.adjoint V) *
      (V.comp ρ).comp (LinearMap.adjoint V) *
      (V.comp (CFC.rpow σ β)).comp (LinearMap.adjoint V) =
      (V.comp (CFC.rpow σ β * ρ * CFC.rpow σ β)).comp (LinearMap.adjoint V) := by
    -- Multiplicativity of φ at φ (CFC.rpow σ β), φ ρ, φ (CFC.rpow σ β).
    have hX : φ (CFC.rpow σ β) * φ ρ * φ (CFC.rpow σ β) =
        φ (CFC.rpow σ β * ρ * CFC.rpow σ β) := by
      rw [map_mul φ, map_mul φ]
    simpa [hφ_apply] using hX
  rw [h_inner]
  -- Step 4: (V Y V*)^α = V (Y^α) V* where Y = σ^β · ρ · σ^β ≥ 0, α > 0.
  have h_inner_nn : (0 : L ℋ) ≤ CFC.rpow σ β * ρ * CFC.rpow σ β := by
    have hP_nn : (0 : L ℋ) ≤ CFC.rpow σ β := CFC.rpow_nonneg
    have hP_sa : IsSelfAdjoint (CFC.rpow σ β) := IsSelfAdjoint.of_nonneg hP_nn
    rw [LinearMap.nonneg_iff_isPositive]
    have hρ_pos := (LinearMap.nonneg_iff_isPositive _).mp hρ
    have := hρ_pos.conj_adjoint (CFC.rpow σ β)
    rw [show LinearMap.adjoint (CFC.rpow σ β) = CFC.rpow σ β from by
        rw [← LinearMap.star_eq_adjoint]; exact hP_sa.star_eq] at this
    -- this : (CFC.rpow σ β ∘ₗ ρ ∘ₗ CFC.rpow σ β).IsPositive
    -- Need: (CFC.rpow σ β * ρ * CFC.rpow σ β).IsPositive
    convert this using 1
  rw [h_rpow_conj h_inner_nn (ne_of_gt hα_pos)]
  -- Step 5: Trace identity Tr (V X V*) = Tr X. Conclude.
  exact h_tr_conj _

/-- **Isometric covariance of the variational functional `quasiVar`** (all `α > 0`,
    `α ≠ 1`). For an isometry `V` (`V*V = 1`), nonneg `σ`, nonneg `G`,
    `quasiVar α (V ρ V*) (V σ V*) G = quasiVar α ρ σ (V* G V)`.

    All `CFC.rpow` exponents appearing (`(α−1)/(2α)` and `α/(α−1)`) are nonzero, so
    `isometricConj_rpow` applies; the inner sandwich identity
    `(V σ^c V*) G (V σ^c V*) = V (σ^c (V* G V) σ^c) V*` is pure associativity. -/
private lemma quasiVar_isometric_conj {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →ₗ[ℂ] ℋ') (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ))
    {α : ℝ} (hα0 : 0 < α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hσ : (0 : L ℋ) ≤ σ) {G : L ℋ'} (hG : (0 : L ℋ') ≤ G) :
    quasiVar α ((V.comp ρ).comp (LinearMap.adjoint V))
        ((V.comp σ).comp (LinearMap.adjoint V)) G =
      quasiVar α ρ σ ((LinearMap.adjoint V).comp (G.comp V)) := by
  set GV : L ℋ := (LinearMap.adjoint V).comp (G.comp V) with hGV_def
  -- exponents
  set c : ℝ := (α - 1) / (2 * α) with hc_def
  set q : ℝ := α / (α - 1) with hq_def
  have hc_ne : c ≠ 0 := div_ne_zero (sub_ne_zero.mpr hα_ne1) (by positivity)
  have hq_ne : q ≠ 0 := div_ne_zero (ne_of_gt hα0) (sub_ne_zero.mpr hα_ne1)
  -- `GV = V* G V ≥ 0` (conjugation of `G ≥ 0` by the adjoint of `V`).
  have hGV_nn : (0 : L ℋ) ≤ GV := by
    rw [hGV_def, LinearMap.nonneg_iff_isPositive]
    have h := ((LinearMap.nonneg_iff_isPositive G).mp hG).conj_adjoint (LinearMap.adjoint V)
    rw [LinearMap.adjoint_adjoint] at h
    exact h
  -- Cyclic trace identity `Tr (V X V*) = Tr X`.
  have h_tr_conj : ∀ X : L ℋ, Tr ((V.comp X).comp (LinearMap.adjoint V)) = Tr X := by
    intro X
    rw [LinearMap.comp_assoc, LinearMap.trace_comp_comm', LinearMap.comp_assoc, hV]; rfl
  -- Term 1: `Tr (G * V ρ V*) = Tr (GV * ρ)`.
  have hterm1 : Tr (G * (V.comp ρ).comp (LinearMap.adjoint V)) = Tr (GV * ρ) := by
    rw [hGV_def,
      show G * (V.comp ρ).comp (LinearMap.adjoint V) =
        ((G.comp V).comp ρ).comp (LinearMap.adjoint V) from by
          simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc],
      LinearMap.trace_comp_comm']
    simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
  -- Inner sandwich identity (pure associativity): `(Vσ^cV*) G (Vσ^cV*) = V (σ^c GV σ^c) V*`.
  have hinner : ((V.comp (CFC.rpow σ c)).comp (LinearMap.adjoint V)) * G *
      ((V.comp (CFC.rpow σ c)).comp (LinearMap.adjoint V)) =
      (V.comp (CFC.rpow σ c * GV * CFC.rpow σ c)).comp (LinearMap.adjoint V) := by
    rw [hGV_def]
    simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
  -- `σ^c (V*GV) σ^c ≥ 0` (conjugation of `GV ≥ 0` by self-adjoint `σ^c`).
  have hY_nn : (0 : L ℋ) ≤ CFC.rpow σ c * GV * CFC.rpow σ c := by
    have hP_sa : IsSelfAdjoint (CFC.rpow σ c) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    have h := star_left_conjugate_nonneg hGV_nn (CFC.rpow σ c)
    rwa [hP_sa.star_eq] at h
  -- Assemble.
  unfold quasiVar
  rw [← hc_def, ← hq_def, isometricConj_rpow V hV hσ hc_ne, hinner,
      isometricConj_rpow V hV hY_nn hq_ne, h_tr_conj, hterm1]

/-! ### Positive-definite perturbations `A + ε • 1` (used for the cone arguments) -/

/-- Sum of non-negative and positive-definite is positive-definite. -/
lemma pdSetLM_add_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A B : L ℋ} (hA : 0 ≤ A) (hB : B ∈ pdSetLM (ℋ := ℋ)) :
    (A + B) ∈ pdSetLM (ℋ := ℋ) := by
  obtain ⟨εB, hεB_pos, hεB_le⟩ := pdSetLM_exists_pos_lower_bound hB
  have h_A_clm : (0 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap :=
    map_nonneg (toCLMStarAlgHom (ℋ := ℋ)) hA
  have hA_sa : IsSelfAdjoint A.toContinuousLinearMap := IsSelfAdjoint.of_nonneg h_A_clm
  obtain ⟨MA, hMA_le⟩ := exists_upper_bound_self_adjoint hA_sa
  obtain ⟨MB, hMB_le⟩ := exists_upper_bound_self_adjoint hB.1
  have h_toCLM_add : (A + B).toContinuousLinearMap =
      A.toContinuousLinearMap + B.toContinuousLinearMap := by ext x; rfl
  refine pdSubCone_subset_pdSetLM (ℋ := ℋ) hεB_pos (M := MA + MB) ⟨?_, ?_⟩
  · rw [h_toCLM_add]
    have h_add : εB • (1 : LownerHeinzTheorem.L ℋ) =
        (0 : LownerHeinzTheorem.L ℋ) + εB • (1 : LownerHeinzTheorem.L ℋ) :=
      (zero_add _).symm
    rw [h_add]
    exact add_le_add h_A_clm hεB_le
  · rw [h_toCLM_add]
    have h_sum_eq : (MA + MB) • (1 : LownerHeinzTheorem.L ℋ) =
        MA • (1 : LownerHeinzTheorem.L ℋ) + MB • (1 : LownerHeinzTheorem.L ℋ) :=
      add_smul _ _ _
    rw [h_sum_eq]
    exact add_le_add hMA_le hMB_le

/-- The scalar operator `ε • 1` is positive-definite for `ε > 0` real. -/
lemma pos_smul_one_pdSetLM
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {ε : ℝ} (hε : 0 < ε) :
    ((ε : ℂ) • (1 : L ℋ)) ∈ pdSetLM (ℋ := ℋ) := by
  set τ : L ℋ := (ε : ℂ) • (1 : L ℋ) with hτ_def
  have hε_ne_complex : (ε : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hε
  have hε_nn_complex : (0 : ℂ) ≤ (ε : ℂ) := Complex.zero_le_real.mpr hε.le
  have h_isPos : τ.IsPositive :=
    LinearMap.isPositive_one.smul_of_nonneg hε_nn_complex
  have h_nn : (0 : L ℋ) ≤ τ :=
    (LinearMap.nonneg_iff_isPositive _).mpr h_isPos
  have h_unit : IsUnit τ := by
    refine ⟨⟨τ, ((ε : ℂ))⁻¹ • 1, ?_, ?_⟩, rfl⟩
    · rw [hτ_def, smul_mul_smul_comm, mul_inv_cancel₀ hε_ne_complex, mul_one, one_smul]
    · rw [hτ_def, smul_mul_smul_comm, inv_mul_cancel₀ hε_ne_complex, mul_one, one_smul]
  have h_clm_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ τ.toContinuousLinearMap :=
    map_nonneg (toCLMStarAlgHom (ℋ := ℋ)) h_nn
  have h_clm_unit : IsUnit τ.toContinuousLinearMap :=
    (toCLMStarAlgHom (ℋ := ℋ)).toRingHom.isUnit_map h_unit
  have h_clm_sa : IsSelfAdjoint τ.toContinuousLinearMap :=
    IsSelfAdjoint.of_nonneg h_clm_nn
  refine ⟨h_clm_sa, ?_⟩
  intro r hr
  have h_spec_nn : spectrum ℝ τ.toContinuousLinearMap ⊆ Set.Ici 0 :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := h_clm_sa)).1 h_clm_nn
  rcases lt_or_eq_of_le (by simpa [Set.Ici] using h_spec_nn hr) with h | h
  · exact h
  · exfalso; rw [← h] at hr
    exact (spectrum.zero_notMem_iff (R := ℝ)).mpr h_clm_unit hr

/-- For non-negative `A` and `ε > 0`, the perturbation `A + ε • 1` is pd. -/
lemma nonneg_add_pos_smul_one_pdSetLM
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) {ε : ℝ} (hε : 0 < ε) :
    (A + (ε : ℂ) • (1 : L ℋ)) ∈ pdSetLM (ℋ := ℋ) :=
  pdSetLM_add_nonneg hA (pos_smul_one_pdSetLM hε)

/-- From non-negativity and invertibility, conclude positive-definiteness in `pdSetLM`
    (the spectrum is `≥ 0` by positivity and avoids `0` by invertibility). -/
lemma pdSetLM_of_nonneg_isUnit {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (h_nn : (0 : L ℋ) ≤ A) (h_unit : IsUnit A) : A ∈ pdSetLM (ℋ := ℋ) := by
  have h_clm_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap :=
    map_nonneg (toCLMStarAlgHom (ℋ := ℋ)) h_nn
  have h_clm_unit : IsUnit A.toContinuousLinearMap :=
    (toCLMStarAlgHom (ℋ := ℋ)).toRingHom.isUnit_map h_unit
  have h_clm_sa : IsSelfAdjoint A.toContinuousLinearMap := IsSelfAdjoint.of_nonneg h_clm_nn
  refine ⟨h_clm_sa, ?_⟩
  intro r hr
  have h_spec_nn : spectrum ℝ A.toContinuousLinearMap ⊆ Set.Ici 0 :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := h_clm_sa)).1 h_clm_nn
  rcases lt_or_eq_of_le (by simpa [Set.Ici] using h_spec_nn hr) with h | h
  · exact h
  · exfalso; rw [← h] at hr
    exact (spectrum.zero_notMem_iff (R := ℝ)).mpr h_clm_unit hr

/-- The tensor product `A ⊗ B` of two positive-definite operators is positive-definite.
    Non-negativity comes from `A ⊗ B = T * T` with `T = √A ⊗ √B` self-adjoint
    (`T * T = T * T*` is positive); invertibility from the inverse `A⁻¹ ⊗ B⁻¹`. -/
lemma tensorMap_pdSetLM {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂] [Nontrivial ℋ₁] [Nontrivial ℋ₂]
    {A : L ℋ₁} {B : L ℋ₂} (hA : A ∈ pdSetLM (ℋ := ℋ₁)) (hB : B ∈ pdSetLM (ℋ := ℋ₂)) :
    TensorProduct.map A B ∈ pdSetLM (ℋ := ℋ₁ ⊗[ℂ] ℋ₂) := by
  haveI : Nontrivial (ℋ₁ ⊗[ℂ] ℋ₂) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by
      rw [Module.finrank_tensorProduct]
      exact Nat.mul_pos Module.finrank_pos Module.finrank_pos)
  have hA_nn : (0 : L ℋ₁) ≤ A := nonneg_of_pdSetLM hA
  have hB_nn : (0 : L ℋ₂) ≤ B := nonneg_of_pdSetLM hB
  refine pdSetLM_of_nonneg_isUnit ?_ ?_
  · -- Non-negativity: `A ⊗ B = T * T` with `T = √A ⊗ √B` self-adjoint.
    set sA := CFC.sqrt A with hsA
    set sB := CFC.sqrt B with hsB
    have hsA_sa : IsSelfAdjoint sA := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)
    have hsB_sa : IsSelfAdjoint sB := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)
    have hmap : TensorProduct.map A B =
        TensorProduct.map sA sB * TensorProduct.map sA sB := by
      conv_lhs => rw [(CFC.sqrt_mul_sqrt_self A hA_nn).symm, (CFC.sqrt_mul_sqrt_self B hB_nn).symm]
      rw [TensorProduct.map_mul]
    have hT_adj : LinearMap.adjoint (TensorProduct.map sA sB) = TensorProduct.map sA sB := by
      rw [TensorProduct.adjoint_map,
        show LinearMap.adjoint sA = sA from by
          rw [← LinearMap.star_eq_adjoint]; exact hsA_sa.star_eq,
        show LinearMap.adjoint sB = sB from by
          rw [← LinearMap.star_eq_adjoint]; exact hsB_sa.star_eq]
    rw [hmap, LinearMap.nonneg_iff_isPositive]
    have hp := LinearMap.isPositive_self_comp_adjoint (TensorProduct.map sA sB)
    rw [hT_adj] at hp
    exact hp
  · -- Invertibility via the explicit inverse `A⁻¹ ⊗ B⁻¹`.
    obtain ⟨uA, huA⟩ := isUnit_of_pdSetLM hA
    obtain ⟨uB, huB⟩ := isUnit_of_pdSetLM hB
    refine ⟨⟨TensorProduct.map A B,
      TensorProduct.map ((↑uA⁻¹ : L ℋ₁)) ((↑uB⁻¹ : L ℋ₂)), ?_, ?_⟩, rfl⟩
    · rw [← TensorProduct.map_mul, ← huA, ← huB, Units.mul_inv, Units.mul_inv,
        TensorProduct.map_one]
    · rw [← TensorProduct.map_mul, ← huA, ← huB, Units.inv_mul, Units.inv_mul,
        TensorProduct.map_one]

/-! ### Continuity / concavity of `Re Q_α` on the non-negative cone (`α < 1`) -/

/-- For `0 ≤ p`, the map `A ↦ CFC.rpow A p` is continuous on the cone of non-negative
    operators. (A positive power `x ↦ x^p` is continuous up to `0` in `ℝ≥0`, so unlike the
    `pdSetLM` version no spectral gap away from `0` is required.) -/
private lemma rpow_continuousOn_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {p : ℝ} (hp : 0 ≤ p) :
    ContinuousOn (fun A : L 𝒦 => CFC.rpow A p) {A : L 𝒦 | (0 : L 𝒦) ≤ A} :=
  (continuousOn_id (s := {A : L 𝒦 | (0 : L 𝒦) ≤ A})).cfc_nnreal_of_mem_nhdsSet
    (s := Set.univ) (f := (· ^ p)) Filter.univ_mem (ha' := fun _ hA => hA)
    (hf := (NNReal.continuous_rpow_const hp).continuousOn)

/-- For `0 < α < 1`, the real part of `sandwichedQuasi` is jointly continuous on the
    non-negative cone. Both exponents `β = (1-α)/(2α)` and `α` are positive, so every
    `CFC.rpow` in the definition is continuous up to the boundary of the cone. -/
private lemma sandwichedQuasi_re_continuousOn_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ContinuousOn (Function.uncurry (fun (ρ σ : L 𝒦) => (sandwichedQuasi α ρ σ).re))
      ({A : L 𝒦 | (0 : L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0 : L 𝒦) ≤ A}) := by
  set β : ℝ := (1 - α) / (2 * α) with hβ
  have hβ_nn : 0 ≤ β := le_of_lt (div_pos (by linarith) (by linarith))
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

/-- Joint convexity of `(ρ, σ) ↦ Re quasiVar α ρ σ H` extends from `pdSetLM` to the whole
    non-negative cone (fixed pd `H`, `α > 1`), by the same `ε → 0⁺` perturbation + joint
    continuity (`quasiVar_re_continuousOn_nonneg`) argument as the concave case. -/
private lemma quasiVar_re_jointlyConvex_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {α : ℝ} (hα : 1 < α) {H : L 𝒦} (hH : H ∈ pdSetLM (ℋ := 𝒦)) :
    JointlyConvexOn {A : L 𝒦 | (0 : L 𝒦) ≤ A} {A : L 𝒦 | (0 : L 𝒦) ≤ A}
      (fun ρ σ => (quasiVar (ℋ := 𝒦) α ρ σ H).re) := by
  have hcont := quasiVar_re_continuousOn_nonneg (𝒦 := 𝒦) hα (nonneg_of_pdSetLM hH)
  have hpd := quasiVar_re_jointlyConvex_pdSetLM (ℋ := 𝒦) hα hH
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [Set.mem_setOf_eq] at hρ₁ hρ₂ hσ₁ hσ₂
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
        nonneg_of_pdSetLM (pos_smul_one_pdSetLM hε')
      exact ⟨by simpa using add_nonneg ha hsmul, by simpa using add_nonneg hb hsmul⟩
    have h_tendsto_curve :
        Filter.Tendsto (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhdsWithin (a, b) ({A : L 𝒦 | (0:L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0:L 𝒦) ≤ A})) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, h_into⟩
      have h0 : Filter.Tendsto (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1))
          (nhds (0 : ℝ)) (nhds (a, b)) := by
        have h := hcurve.tendsto 0; simpa using h
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
      rw [← add_smul]; norm_num
    simp only [smul_add]
    rw [show (1 - θ) • a₁ + (1 - θ) • (ε : ℂ) • 1 + (θ • a₂ + θ • (ε : ℂ) • 1) =
        ((1 - θ) • a₁ + θ • a₂) + ((1 - θ) • (ε : ℂ) • 1 + θ • (ε : ℂ) • 1) from by abel,
        h1]
  refine le_of_tendsto_of_tendsto (key _ _ hρc hσc)
    (((key ρ₁ σ₁ hρ₁ hσ₁).const_smul (1 - θ)).add ((key ρ₂ σ₂ hρ₂ hσ₂).const_smul θ)) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have hp₁ := nonneg_add_pos_smul_one_pdSetLM hρ₁ hε'
  have hp₂ := nonneg_add_pos_smul_one_pdSetLM hρ₂ hε'
  have hq₁ := nonneg_add_pos_smul_one_pdSetLM hσ₁ hε'
  have hq₂ := nonneg_add_pos_smul_one_pdSetLM hσ₂ hε'
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
    Joint concavity of `(ρ, σ) ↦ Re Q_α(ρ‖σ)` extends from `pdSetLM` to the whole
    non-negative cone by an `ε → 0⁺` perturbation `(ρ, σ) ↦ (ρ + ε•1, σ + ε•1)`, using
    joint continuity on the cone (`sandwichedQuasi_re_continuousOn_nonneg`). -/
private lemma sandwichedQuasi_re_jointlyConcave_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {α : ℝ} (hα_ge : 1 / 2 ≤ α) (hα_lt : α < 1) :
    JointlyConcaveOn {A : L 𝒦 | (0 : L 𝒦) ≤ A} {A : L 𝒦 | (0 : L 𝒦) ≤ A}
      (fun ρ σ => (sandwichedQuasi (ℋ := 𝒦) α ρ σ).re) := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hcont := sandwichedQuasi_re_continuousOn_nonneg (𝒦 := 𝒦) hα0 hα_lt
  have hpd := sandwichedQuasi_re_jointlyConcave (ℋ := 𝒦) hα_ge hα_lt
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [Set.mem_setOf_eq] at hρ₁ hρ₂ hσ₁ hσ₂
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
        nonneg_of_pdSetLM (pos_smul_one_pdSetLM hε')
      exact ⟨by simpa using add_nonneg ha hsmul, by simpa using add_nonneg hb hsmul⟩
    have h_tendsto_curve :
        Filter.Tendsto (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhdsWithin (a, b) ({A : L 𝒦 | (0:L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0:L 𝒦) ≤ A})) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, h_into⟩
      have h0 : Filter.Tendsto (fun ε : ℝ => (a + (ε : ℂ) • 1, b + (ε : ℂ) • 1))
          (nhds (0 : ℝ)) (nhds (a, b)) := by
        have h := hcurve.tendsto 0; simpa using h
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
      rw [← add_smul]; norm_num
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
  have hp₁ := nonneg_add_pos_smul_one_pdSetLM hρ₁ hε'
  have hp₂ := nonneg_add_pos_smul_one_pdSetLM hρ₂ hε'
  have hq₁ := nonneg_add_pos_smul_one_pdSetLM hσ₁ hε'
  have hq₂ := nonneg_add_pos_smul_one_pdSetLM hσ₂ hε'
  have hj := hpd hp₁ hp₂ hq₁ hq₂ hθ0 hθ1
  rw [hcombo ρ₁ ρ₂ ε, hcombo σ₁ σ₂ ε]
  exact hj

end JointlyConcaveNonneg

section JensenHaarCore
-- `sandwichedQuasi`/`quasiVar` are treated as black boxes (only via lemmas), so making
-- them irreducible avoids the unifier unfolding their large CFC expressions during the
-- many `rw`/`isDefEq` checks in the proof.
attribute [local irreducible] sandwichedQuasi quasiVar

set_option maxHeartbeats 800000 in
-- The `α > 1` branch is a long variational assembly (Jensen on `quasiVar`, pointwise
-- bound, twirl); even with the irreducibility above it needs a raised heartbeat budget.
/-- **Inner Jensen–Haar inequality (Form A, isometric Stinespring).**

    Reformulation of the central Jensen-style inequality in terms of an
    *isometric* Stinespring map `V : ℋ →ₗ[ℂ] (ℋ ⊗ ℋ_env)` with `V*V = I`,
    rather than the previous unitary-with-mixed-environment Form B
    (`Tr₂[U(τ ⊗ γ)U*]`). The inequality states:

    `Re sandwichedQuasi α ((E ρ) ⊗ τ_max) ((E σ) ⊗ τ_max)`
    `⋚ Re sandwichedQuasi α (V ρ V*) (V σ V*)`

    where `E γ := TrRight (V γ V*)` and `τ_max := (dim ℋ_env)⁻¹ • 1` on
    `ℋ_env`; direction `≤` for `α > 1`, `≥` for `α ∈ [1/2, 1)`.

    **Proof (Frank–Lieb arXiv:1306.5358, isometric variant).**
    The integrand `g_ρ u := (1_ℋ ⊗ u) · (V ρ V*) · (1_ℋ ⊗ u*)` is in general
    *rank-deficient* (supported on the range of `V V*`), so the original
    closed-pd-subcone Jensen argument no longer applies directly. We instead
    work on the whole non-negative cone `{A | 0 ≤ A}` (closed and convex):
      1. The right-twirl identity (`right_twirl_eq`, the `TrRight` analogue of
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
    (_hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (_hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (V : ℋ →ₗ[ℂ] (𝒦 ⊗[ℂ] ℋ_env))
    (_hV : (LinearMap.adjoint V).comp V = (1 : L ℋ))
    (_hEρ : TrRight ((V.comp ρ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := 𝒦))
    (_hEσ : TrRight ((V.comp σ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := 𝒦)) :
    ((sandwichedQuasi α
        (TensorProduct.map
          (TrRight ((V.comp ρ).comp (LinearMap.adjoint V)))
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))
        (TensorProduct.map
          (TrRight ((V.comp σ).comp (LinearMap.adjoint V)))
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))).re -
      (sandwichedQuasi α
        ((V.comp ρ).comp (LinearMap.adjoint V))
        ((V.comp σ).comp (LinearMap.adjoint V))).re) * (α - 1) ≤ 0 := by
  -- `ℋ ⊗ ℋ_env` is again a (nontrivial) qudit.
  haveI : Nontrivial (𝒦 ⊗[ℂ] ℋ_env) :=
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
    set Xρ : L (𝒦 ⊗[ℂ] ℋ_env) := (V.comp ρ).comp (LinearMap.adjoint V) with hXρ_def
    set Xσ : L (𝒦 ⊗[ℂ] ℋ_env) := (V.comp σ).comp (LinearMap.adjoint V) with hXσ_def
    have hρ_nn : (0 : L ℋ) ≤ ρ := nonneg_of_pdSetLM _hρ
    have hσ_nn : (0 : L ℋ) ≤ σ := nonneg_of_pdSetLM _hσ
    have hXρ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xρ := by
      rw [hXρ_def, LinearMap.nonneg_iff_isPositive]
      exact ((LinearMap.nonneg_iff_isPositive ρ).mp hρ_nn).conj_adjoint V
    have hXσ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xσ := by
      rw [hXσ_def, LinearMap.nonneg_iff_isPositive]
      exact ((LinearMap.nonneg_iff_isPositive σ).mp hσ_nn).conj_adjoint V
    -- Haar integrands.
    set gρ : unitary (L ℋ_env) → L (𝒦 ⊗[ℂ] ℋ_env) := fun u =>
        TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)) * Xρ *
          TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)) with hgρ_def
    set gσ : unitary (L ℋ_env) → L (𝒦 ⊗[ℂ] ℋ_env) := fun u =>
        TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)) * Xσ *
          TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)) with hgσ_def
    -- The integrand of `Re Q_α` is constant (unitary invariance of `Q_α`).
    have h_inv : ∀ u : unitary (L ℋ_env),
        (sandwichedQuasi α (gρ u) (gσ u)).re = (sandwichedQuasi α Xρ Xσ).re := by
      intro u
      set U : unitary (L (𝒦 ⊗[ℂ] ℋ_env)) :=
        ⟨TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)),
          tensorMap_right_unitary_of_unitary u⟩ with hU_def
      have hUcoe : ((U : unitary (L (𝒦 ⊗[ℂ] ℋ_env))) : L (𝒦 ⊗[ℂ] ℋ_env)) =
          TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)) := rfl
      have hUstar : ((star U : unitary (L (𝒦 ⊗[ℂ] ℋ_env))) : L (𝒦 ⊗[ℂ] ℋ_env)) =
          TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)) := by
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
          (star (TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env))))
      rw [star_star, tensorMap_right_star] at h
      exact h
    have hgσ_mem : ∀ᵐ u ∂(haarUnitary ℋ_env),
        gσ u ∈ {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} := by
      filter_upwards with u
      show (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ gσ u
      have h := star_left_conjugate_nonneg hXσ_nn
          (star (TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env))))
      rw [star_star, tensorMap_right_star] at h
      exact h
    -- Integrability.
    have hgρ_int : Integrable gρ (haarUnitary ℋ_env) :=
      integrable_unitaryConj_tensor_right Xρ
    have hgσ_int : Integrable gσ (haarUnitary ℋ_env) :=
      integrable_unitaryConj_tensor_right Xσ
    have hfg_int :
        Integrable (fun u => (sandwichedQuasi α (gρ u) (gσ u)).re) (haarUnitary ℋ_env) := by
      simp_rw [h_inv]; exact integrable_const _
    -- The two integrals collapse via the right twirl.
    have hint_ρ : (∫ u, gρ u ∂(haarUnitary ℋ_env)) =
        TensorProduct.map (TrRight Xρ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) :=
      right_twirl_eq Xρ
    have hint_σ : (∫ u, gσ u ∂(haarUnitary ℋ_env)) =
        TensorProduct.map (TrRight Xσ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) :=
      right_twirl_eq Xσ
    -- The constant-integrand integral equals `Re Q_α(VρV*, VσV*)`.
    have h_lhs_int : (∫ u, (sandwichedQuasi α (gρ u) (gσ u)).re ∂(haarUnitary ℋ_env))
        = (sandwichedQuasi α Xρ Xσ).re := by
      simp_rw [h_inv]; simp
    -- Membership of the (collapsed) integrals in the closed convex cone.
    have hmem_ρ : (∫ u, gρ u ∂(haarUnitary ℋ_env)) ∈
        {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} :=
      convex_nonneg_cone.integral_mem isClosed_nonneg_cone hgρ_mem hgρ_int
    have hmem_σ : (∫ u, gσ u ∂(haarUnitary ℋ_env)) ∈
        {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} :=
      convex_nonneg_cone.integral_mem isClosed_nonneg_cone hgσ_mem hgσ_int
    -- Bochner–Jensen on the non-negative cone.
    have hJ := jointly_concave_le_integral (μ := haarUnitary ℋ_env)
      convex_nonneg_cone convex_nonneg_cone isClosed_nonneg_cone isClosed_nonneg_cone
      (sandwichedQuasi_re_jointlyConcave_nonneg _hα_ge hα_lt)
      (sandwichedQuasi_re_continuousOn_nonneg hα0 hα_lt)
      hgρ_mem hgσ_mem hgρ_int hgσ_int hfg_int hmem_ρ hmem_σ
    rw [h_lhs_int, hint_ρ, hint_σ] at hJ
    -- `hJ : Re Q_α(VρV*, VσV*) ≤ Re Q_α(Eρ⊗τmax, Eσ⊗τmax)`; close with the sign of `α-1`.
    have hα1_neg : α - 1 ≤ 0 := by linarith
    have hD : (0 : ℝ) ≤ (sandwichedQuasi α
        (TensorProduct.map (TrRight Xρ) ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)))
        (TensorProduct.map (TrRight Xσ)
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
    set Xρ : L (𝒦 ⊗[ℂ] ℋ_env) := (V.comp ρ).comp (LinearMap.adjoint V) with hXρ_def
    set Xσ : L (𝒦 ⊗[ℂ] ℋ_env) := (V.comp σ).comp (LinearMap.adjoint V) with hXσ_def
    have hρ_nn : (0 : L ℋ) ≤ ρ := nonneg_of_pdSetLM _hρ
    have hσ_nn : (0 : L ℋ) ≤ σ := nonneg_of_pdSetLM _hσ
    have hXρ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xρ := by
      rw [hXρ_def, LinearMap.nonneg_iff_isPositive]
      exact ((LinearMap.nonneg_iff_isPositive ρ).mp hρ_nn).conj_adjoint V
    have hXσ_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Xσ := by
      rw [hXσ_def, LinearMap.nonneg_iff_isPositive]
      exact ((LinearMap.nonneg_iff_isPositive σ).mp hσ_nn).conj_adjoint V
    set gρ : unitary (L ℋ_env) → L (𝒦 ⊗[ℂ] ℋ_env) := fun u =>
        TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)) * Xρ *
          TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)) with hgρ_def
    set gσ : unitary (L ℋ_env) → L (𝒦 ⊗[ℂ] ℋ_env) := fun u =>
        TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)) * Xσ *
          TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)) with hgσ_def
    -- Unitary invariance: the `Re Q_α` integrand is constant.
    have h_inv : ∀ u : unitary (L ℋ_env),
        (sandwichedQuasi α (gρ u) (gσ u)).re = (sandwichedQuasi α Xρ Xσ).re := by
      intro u
      set U : unitary (L (𝒦 ⊗[ℂ] ℋ_env)) :=
        ⟨TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)),
          tensorMap_right_unitary_of_unitary u⟩ with hU_def
      have hUcoe : ((U : unitary (L (𝒦 ⊗[ℂ] ℋ_env))) : L (𝒦 ⊗[ℂ] ℋ_env)) =
          TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)) := rfl
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
          (star (TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env))))
      rw [star_star, tensorMap_right_star] at h
      exact h
    have hgσ_nn_all : ∀ u, gσ u ∈ {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} := by
      intro u
      change (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ gσ u
      have h := star_left_conjugate_nonneg hXσ_nn
          (star (TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env))))
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
      simp_rw [h_inv]; exact integrable_const _
    -- Right-twirl collapse of the integrals.
    have hint_ρ : (∫ u, gρ u ∂(haarUnitary ℋ_env)) =
        TensorProduct.map (TrRight Xρ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) := right_twirl_eq Xρ
    have hint_σ : (∫ u, gσ u ∂(haarUnitary ℋ_env)) =
        TensorProduct.map (TrRight Xσ)
          ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) := right_twirl_eq Xσ
    have h_lhs_int : (∫ u, (sandwichedQuasi α (gρ u) (gσ u)).re ∂(haarUnitary ℋ_env))
        = (sandwichedQuasi α Xρ Xσ).re := by simp_rw [h_inv]; simp
    have hmem_ρ : (∫ u, gρ u ∂(haarUnitary ℋ_env)) ∈
        {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} :=
      convex_nonneg_cone.integral_mem isClosed_nonneg_cone hgρ_mem hgρ_int
    have hmem_σ : (∫ u, gσ u ∂(haarUnitary ℋ_env)) ∈
        {A : L (𝒦 ⊗[ℂ] ℋ_env) | (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ A} :=
      convex_nonneg_cone.integral_mem isClosed_nonneg_cone hgσ_mem hgσ_int
    -- The pd integral points `Pρ = ∫gρ`, `Pσ = ∫gσ`, and the optimizer `H*`.
    set Pρ : L (𝒦 ⊗[ℂ] ℋ_env) :=
      TensorProduct.map (TrRight Xρ) ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) with hPρ_def
    set Pσ : L (𝒦 ⊗[ℂ] ℋ_env) :=
      TensorProduct.map (TrRight Xσ) ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) with hPσ_def
    have hτmax_pd : ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) ∈ pdSetLM (ℋ := ℋ_env) :=
      maxmixed_pdSetLM ℋ_env
    have hPρ_pd : Pρ ∈ pdSetLM (ℋ := 𝒦 ⊗[ℂ] ℋ_env) := by
      rw [hPρ_def]; exact tensorMap_pdSetLM (by rw [hXρ_def]; exact _hEρ) hτmax_pd
    have hPσ_pd : Pσ ∈ pdSetLM (ℋ := 𝒦 ⊗[ℂ] ℋ_env) := by
      rw [hPσ_def]; exact tensorMap_pdSetLM (by rw [hXσ_def]; exact _hEσ) hτmax_pd
    set Hopt := quasiVarOpt α Pρ Pσ with hHopt_def
    have hHopt_pd : Hopt ∈ pdSetLM (ℋ := 𝒦 ⊗[ℂ] ℋ_env) :=
      quasiVarOpt_pdSetLM hα0 hα_ne1 hPρ_pd hPσ_pd
    have hHopt_nn : (0 : L (𝒦 ⊗[ℂ] ℋ_env)) ≤ Hopt := nonneg_of_pdSetLM hHopt_pd
    have hHopt_pos : Hopt.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp hHopt_nn
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
      convex_nonneg_cone convex_nonneg_cone isClosed_nonneg_cone isClosed_nonneg_cone
      (quasiVar_re_jointlyConvex_nonneg hα_gt hHopt_pd)
      (quasiVar_re_continuousOn_nonneg hα_gt hHopt_nn)
      hgρ_mem hgσ_mem hgρ_int hgσ_int hquasi_int hmem_ρ hmem_σ
    rw [hint_ρ, hint_σ] at hJ
    -- Pointwise `quasiVar(gρu,gσu,H*) ≤ Q_α(gρu,gσu)` via the isometry `Vu = (1⊗u)∘V`.
    have hpoint : ∀ u : unitary (L ℋ_env),
        (quasiVar α (gρ u) (gσ u) Hopt).re ≤ (sandwichedQuasi α (gρ u) (gσ u)).re := by
      intro u
      set W : L (𝒦 ⊗[ℂ] ℋ_env) := TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env))
        with hW_def
      have hW_unit : W ∈ unitary (L (𝒦 ⊗[ℂ] ℋ_env)) := tensorMap_right_unitary_of_unitary u
      have hadjW : LinearMap.adjoint W =
          TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env)) := by
        rw [hW_def, ← LinearMap.star_eq_adjoint, tensorMap_right_star]
      set Vu : ℋ →ₗ[ℂ] (𝒦 ⊗[ℂ] ℋ_env) := W.comp V with hVu_def
      have hVu_iso : (LinearMap.adjoint Vu).comp Vu = 1 := by
        have hWadjW : LinearMap.adjoint W * W = 1 := by
          have h := (Unitary.mem_iff.mp hW_unit).1
          rwa [LinearMap.star_eq_adjoint] at h
        rw [hVu_def, LinearMap.adjoint_comp]
        calc ((LinearMap.adjoint V).comp (LinearMap.adjoint W)).comp (W.comp V)
            = (LinearMap.adjoint V).comp ((LinearMap.adjoint W * W).comp V) := by
              simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
          _ = (LinearMap.adjoint V).comp V := by
              rw [hWadjW, Module.End.one_eq_id, LinearMap.id_comp]
          _ = 1 := _hV
      have hgρu_eq : gρ u = (Vu.comp ρ).comp (LinearMap.adjoint Vu) := by
        simp only [hgρ_def]
        rw [hVu_def, hXρ_def, LinearMap.adjoint_comp, ← hW_def, ← hadjW]
        simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
      have hgσu_eq : gσ u = (Vu.comp σ).comp (LinearMap.adjoint Vu) := by
        simp only [hgσ_def]
        rw [hVu_def, hXσ_def, LinearMap.adjoint_comp, ← hW_def, ← hadjW]
        simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
      rw [hgρu_eq, hgσu_eq, quasiVar_isometric_conj Vu hVu_iso hα0 hα_ne1 hσ_nn hHopt_nn,
        sandwichedQuasi_isometric_conj Vu hVu_iso hα0 hα_ne1 hρ_nn hσ_nn]
      exact (RCLike.le_iff_re_im.mp (quasiVar_le_quasi hα_gt
        ((LinearMap.nonneg_iff_isPositive ρ).mp hρ_nn)
        ((LinearMap.nonneg_iff_isPositive σ).mp hσ_nn)
        (hHopt_pos.adjoint_conj Vu) (isUnit_of_pdSetLM _hσ))).1
    -- Combine: `Re Q_α(Pρ,Pσ) ≤ ∫ Re quasiVar ≤ ∫ Re Q_α = Re Q_α(Xρ,Xσ)`.
    have hint_le : (∫ u, (quasiVar α (gρ u) (gσ u) Hopt).re ∂(haarUnitary ℋ_env)) ≤
        (sandwichedQuasi α Xρ Xσ).re := by
      calc (∫ u, (quasiVar α (gρ u) (gσ u) Hopt).re ∂(haarUnitary ℋ_env))
          ≤ ∫ u, (sandwichedQuasi α (gρ u) (gσ u)).re ∂(haarUnitary ℋ_env) :=
            integral_mono hquasi_int hfg_int hpoint
        _ = (sandwichedQuasi α Xρ Xσ).re := h_lhs_int
    have hfinal : (sandwichedQuasi α Pρ Pσ).re ≤ (sandwichedQuasi α Xρ Xσ).re := by
      rw [hatt]; exact le_trans hJ hint_le
    have hα1_pos : (0 : ℝ) < α - 1 := by linarith
    nlinarith [hfinal, hα1_pos]

end JensenHaarCore

/-! ### The abstract Jensen-Haar interface -/

/-- **Jensen–Haar inequality (Form A, isometric Stinespring).**

    Given the data of an *isometric* Stinespring dilation — an environment
    Hilbert space `ℋ_env` and an isometry `V : ℋ →ₗ[ℂ] (ℋ ⊗ ℋ_env)` with
    `V*V = I_ℋ` — let `E γ := TrRight (V γ V*)`. Then for any
    `α ∈ [1/2, 1) ∪ (1, ∞)` and any positive-definite `ρ, σ` with
    positive-definite images `E ρ`, `E σ`,

    `(Re sandwichedQuasi α (E ρ) (E σ) − Re sandwichedQuasi α ρ σ) · (α − 1) ≤ 0`.

    This is the data-processing inequality at the `Q_α`-functional level,
    in the form directly compatible with `CPTP.exists_stinespring_dilation`
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
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (V : ℋ →ₗ[ℂ] (𝒦 ⊗[ℂ] ℋ_env))
    (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ))
    (hEρ : TrRight ((V.comp ρ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := 𝒦))
    (hEσ : TrRight ((V.comp σ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := 𝒦)) :
    ((sandwichedQuasi α
        (TrRight ((V.comp ρ).comp (LinearMap.adjoint V)))
        (TrRight ((V.comp σ).comp (LinearMap.adjoint V)))).re -
      (sandwichedQuasi α ρ σ).re) * (α - 1) ≤ 0 := by
  -- Reduce `sandwichedQuasi_jensen_haar` to `jensen_haar_core` plus the
  -- two helper lemmas (tensor mult collapse + isometric invariance).
  have hα0 : 0 < α := by linarith
  have hα_ne0 : α ≠ 0 := ne_of_gt hα0
  set Eρ : L 𝒦 := TrRight ((V.comp ρ).comp (LinearMap.adjoint V)) with hEρ_def
  set Eσ : L 𝒦 := TrRight ((V.comp σ).comp (LinearMap.adjoint V)) with hEσ_def
  set τ_max : L ℋ_env := (Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env) with hτ_max_def
  -- `τ_max ∈ pdSetLM` and `Tr τ_max = 1`.
  have hτ_max_pd : τ_max ∈ pdSetLM (ℋ := ℋ_env) := maxmixed_pdSetLM ℋ_env
  have hτ_max_trace : Tr τ_max = 1 := by
    rw [hτ_max_def, map_smul, smul_eq_mul, LinearMap.trace_one]
    have hd : (Module.finrank ℂ ℋ_env : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℂ) (M := ℋ_env)).ne'
    field_simp
  -- LHS factorisation: `Q_α(Eρ ⊗ τ_max, Eσ ⊗ τ_max) = Q_α(Eρ, Eσ)`.
  have hLHS_factor : sandwichedQuasi α
      (TensorProduct.map Eρ τ_max : L (𝒦 ⊗[ℂ] ℋ_env))
      (TensorProduct.map Eσ τ_max) =
      sandwichedQuasi α Eρ Eσ := by
    rw [sandwichedQuasi_tensor α Eρ Eσ τ_max τ_max
        (nonneg_of_pdSetLM hEρ) (nonneg_of_pdSetLM hEσ)
        (nonneg_of_pdSetLM hτ_max_pd) (nonneg_of_pdSetLM hτ_max_pd),
        sandwichedQuasi_self_pdSetLM hα_ne0 hτ_max_pd, hτ_max_trace, mul_one]
  -- RHS factorisation (isometric invariance):
  -- `Q_α(V ρ V*, V σ V*) = Q_α(ρ, σ)`, valid for all `α > 0`, `α ≠ 1`.
  -- (In finite dimensions there is no CFC convention obstruction even for `α > 1`;
  -- see `sandwichedQuasi_isometric_conj`.)
  have hRHS_factor : sandwichedQuasi α
      ((V.comp ρ).comp (LinearMap.adjoint V))
      ((V.comp σ).comp (LinearMap.adjoint V)) =
      sandwichedQuasi α ρ σ :=
    sandwichedQuasi_isometric_conj V hV hα0 hα_ne1
      (nonneg_of_pdSetLM hρ) (nonneg_of_pdSetLM hσ)
  -- Apply the inner Jensen-Haar (`jensen_haar_core`) and substitute.
  have h_core := jensen_haar_core hα_ge hα_ne1 hρ hσ V hV hEρ hEσ
  change ((sandwichedQuasi α Eρ Eσ).re - (sandwichedQuasi α ρ σ).re) * (α - 1) ≤ 0
  have hLHS_re : (sandwichedQuasi α
      (TensorProduct.map Eρ τ_max : L (𝒦 ⊗[ℂ] ℋ_env))
      (TensorProduct.map Eσ τ_max)).re = (sandwichedQuasi α Eρ Eσ).re := by
    rw [hLHS_factor]
  have hRHS_re : (sandwichedQuasi α
      ((V.comp ρ).comp (LinearMap.adjoint V))
      ((V.comp σ).comp (LinearMap.adjoint V))).re =
      (sandwichedQuasi α ρ σ).re := by
    rw [hRHS_factor]
  rw [← hLHS_re, ← hRHS_re]; exact h_core

/-! ### Main monotonicity theorem -/

/-- Monotonicity of the sandwiched Rényi divergence under CPTP maps (data-processing inequality).

    For any quantum channel `E : CPTP ℋ ℋ`, any `α ∈ [1/2, 1) ∪ (1, ∞)`, and any
    positive-definite operators `ρ, σ` with positive-definite images `E ρ`, `E σ`,
        `D_α(E ρ ‖ E σ) ≤ D_α(ρ ‖ σ)`.

    **Proof.** Apply the isometric Stinespring dilation
    `E(γ) = TrRight (V γ V*)` (`CPTP.exists_stinespring_dilation`, Form A).
    The central inequality
        `(Re sandwichedQuasi α (Eρ) (Eσ) − Re sandwichedQuasi α ρ σ) · (α − 1) ≤ 0`
    follows from `sandwichedQuasi_jensen_haar` (the abstract Jensen–Haar
    inequality above). Dividing by `Tr Eρ = Tr ρ > 0` (trace preservation
    by `E`) and applying `(α−1)⁻¹ log(·)` gives the result, with sign
    tracking unifying the `α > 1` and `α < 1` cases. -/
theorem sandwichedRenyiDiv_monotone
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (hEρ : E.toFun ρ ∈ pdSetLM (ℋ := 𝒦))
    (hEσ : E.toFun σ ∈ pdSetLM (ℋ := 𝒦)) :
    sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤ sandwichedRenyiDiv α ρ σ := by
  have hα0 : 0 < α := by linarith
  have hα_ne0 : α ≠ 0 := ne_of_gt hα0
  -- Step 1: Isometric Stinespring dilation (Form A).
  obtain ⟨ℋ_env, h_qudit, h_nontriv, V, hV_iso, hV_eq⟩ :=
    CPTP.exists_stinespring_dilation E
  letI := h_qudit
  letI := h_nontriv
  -- Step 2: Eρ and Eσ as the (isometric) Stinespring images.
  have hEρ_eq : E.toFun ρ = TrRight ((V.comp ρ).comp (LinearMap.adjoint V)) := hV_eq ρ
  have hEσ_eq : E.toFun σ = TrRight ((V.comp σ).comp (LinearMap.adjoint V)) := hV_eq σ
  -- pdSetLM membership of the Stinespring images (re-stated in the form needed
  -- by `sandwichedQuasi_jensen_haar`).
  have hEρ' : TrRight ((V.comp ρ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := 𝒦) :=
    hEρ_eq ▸ hEρ
  have hEσ' : TrRight ((V.comp σ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := 𝒦) :=
    hEσ_eq ▸ hEσ
  -- Step 3: the central Q_α-inequality, from `sandwichedQuasi_jensen_haar`.
  have hQ_ineq :
      ((sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re - (sandwichedQuasi α ρ σ).re) *
        (α - 1) ≤ 0 := by
    have h := sandwichedQuasi_jensen_haar hα_ge hα_ne1 hρ hσ V hV_iso hEρ' hEσ'
    rw [hEρ_eq, hEσ_eq]
    exact h
  -- Step 4: unfold D_α and apply log monotonicity.
  unfold sandwichedRenyiDiv
  -- `E` preserves traces: `Tr (E.toFun ρ) = Tr ρ`.
  have hTr_Eρ : (Tr (E.toFun ρ)).re = (Tr ρ).re := by
    rw [← E.trace_map ρ]
  -- Positivity of the relevant real parts.
  have hTr_ρ_pos : (0 : ℝ) < (Tr ρ).re := trace_re_pos_of_pdSetLM hρ
  -- Positivity of `Re sandwichedQuasi α ρ' σ'` for `ρ', σ' ∈ pdSetLM`: the inner
  -- operator `σ'^β ρ' σ'^β` is pd, hence `(·)^α` is pd, hence the trace is positive.
  have hQ_pos_aux : ∀ {𝒥 : Type u} [Qudit 𝒥] [Nontrivial 𝒥] {ρ' σ' : L 𝒥},
      ρ' ∈ pdSetLM (ℋ := 𝒥) → σ' ∈ pdSetLM (ℋ := 𝒥) →
      (0 : ℝ) < (sandwichedQuasi α ρ' σ').re := by
    intro 𝒥 _ _ ρ' σ' hρ' hσ'
    unfold sandwichedQuasi
    have hP_pd : CFC.rpow σ' ((1 - α) / (2 * α)) ∈ pdSetLM (ℋ := 𝒥) := pdSetLM_rpow_ne hσ'
    have hP_sa : IsSelfAdjoint (CFC.rpow σ' ((1 - α) / (2 * α))) :=
      IsSelfAdjoint.of_nonneg (nonneg_of_pdSetLM hP_pd)
    have hP_unit : IsUnit (CFC.rpow σ' ((1 - α) / (2 * α))) := isUnit_of_pdSetLM hP_pd
    have h_inner_eq :
        CFC.rpow σ' ((1 - α) / (2 * α)) * ρ' * CFC.rpow σ' ((1 - α) / (2 * α)) =
        star (CFC.rpow σ' ((1 - α) / (2 * α))) * ρ' * CFC.rpow σ' ((1 - α) / (2 * α)) := by
      rw [hP_sa.star_eq]
    have h_inner_pd :
        (CFC.rpow σ' ((1 - α) / (2 * α)) * ρ' * CFC.rpow σ' ((1 - α) / (2 * α))) ∈
          pdSetLM (ℋ := 𝒥) := by
      rw [h_inner_eq]; exact pdSetLM_conj hρ' hP_unit
    have h_pow_pd :
        CFC.rpow
            (CFC.rpow σ' ((1 - α) / (2 * α)) * ρ' * CFC.rpow σ' ((1 - α) / (2 * α))) α ∈
          pdSetLM (ℋ := 𝒥) := pdSetLM_rpow_ne h_inner_pd
    exact trace_re_pos_of_pdSetLM h_pow_pd
  have hQρσ_pos : (0 : ℝ) < (sandwichedQuasi α ρ σ).re := hQ_pos_aux hρ hσ
  have hQEρEσ_pos : (0 : ℝ) < (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re :=
    hQ_pos_aux hEρ hEσ
  -- Final step: deduce the log inequality.
  -- From `hQ_ineq`: `(Q_α(Eρ,Eσ).re − Q_α(ρ,σ).re) · (α-1) ≤ 0`.
  rcases lt_or_gt_of_ne hα_ne1 with hα_lt | hα_gt
  · -- α < 1: α - 1 < 0
    have hα1_neg : (α - 1 : ℝ) < 0 := by linarith
    have hQ_ge :
        (sandwichedQuasi α ρ σ).re ≤ (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re := by
      nlinarith
    have hlog : Real.log ((sandwichedQuasi α ρ σ).re / (Tr ρ).re) ≤
        Real.log ((sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re /
          (Tr (E.toFun ρ)).re) := by
      rw [hTr_Eρ]
      exact Real.log_le_log (div_pos hQρσ_pos hTr_ρ_pos)
        (div_le_div_of_nonneg_right hQ_ge (le_of_lt hTr_ρ_pos))
    have h1α : (1 / (α - 1) : ℝ) < 0 := by
      rw [one_div]; exact inv_neg''.mpr hα1_neg
    nlinarith
  · -- α > 1: α - 1 > 0
    have hα1_pos : (0 : ℝ) < α - 1 := by linarith
    have hQ_le' :
        (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re ≤ (sandwichedQuasi α ρ σ).re := by
      nlinarith
    have hlog : Real.log ((sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re /
        (Tr (E.toFun ρ)).re) ≤
          Real.log ((sandwichedQuasi α ρ σ).re / (Tr ρ).re) := by
      rw [hTr_Eρ]
      exact Real.log_le_log (div_pos hQEρEσ_pos hTr_ρ_pos)
        (div_le_div_of_nonneg_right hQ_le' (le_of_lt hTr_ρ_pos))
    have h1α_pos : (0 : ℝ) < 1 / (α - 1) := by
      rw [one_div]; exact inv_pos.mpr hα1_pos
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
of `pdSetLM`, which is finite when the kernels match and `+∞` otherwise.
-/

/-- A positive real scalar multiple of a pd operator is pd. -/
lemma pdSetLM_pos_smul
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) {c : ℝ} (hc : 0 < c) :
    ((c : ℂ) • A) ∈ pdSetLM (ℋ := ℋ) := by
  obtain ⟨εA, hεA_pos, hεA_le⟩ := pdSetLM_exists_pos_lower_bound hA
  obtain ⟨MA, hMA_le⟩ := exists_upper_bound_self_adjoint hA.1
  have h_toCLM_smul : ((c : ℂ) • A).toContinuousLinearMap =
      (c : ℂ) • A.toContinuousLinearMap := by ext x; rfl
  -- `(c : ℂ) • A.toCLM = c • A.toCLM` (using ℝ ↪ ℂ tower).
  have h_smul_eq : (c : ℂ) • A.toContinuousLinearMap =
      c • A.toContinuousLinearMap := Complex.coe_smul c _
  refine pdSubCone_subset_pdSetLM (ℋ := ℋ) (ε := c * εA) (mul_pos hc hεA_pos)
      (M := c * MA) ⟨?_, ?_⟩
  · rw [h_toCLM_smul, h_smul_eq]
    have h_smul_lhs : (c * εA) • (1 : LownerHeinzTheorem.L ℋ) =
        c • (εA • (1 : LownerHeinzTheorem.L ℋ)) := by rw [mul_smul]
    rw [h_smul_lhs]
    have h_nn : (0 : LownerHeinzTheorem.L ℋ) ≤
        c • A.toContinuousLinearMap - c • (εA • (1 : LownerHeinzTheorem.L ℋ)) := by
      rw [← smul_sub]
      exact smul_nonneg hc.le (sub_nonneg.mpr hεA_le)
    exact sub_nonneg.mp h_nn
  · rw [h_toCLM_smul, h_smul_eq]
    have h_smul_rhs : (c * MA) • (1 : LownerHeinzTheorem.L ℋ) =
        c • (MA • (1 : LownerHeinzTheorem.L ℋ)) := by rw [mul_smul]
    rw [h_smul_rhs]
    have h_nn : (0 : LownerHeinzTheorem.L ℋ) ≤
        c • (MA • (1 : LownerHeinzTheorem.L ℋ)) - c • A.toContinuousLinearMap := by
      rw [← smul_sub]
      exact smul_nonneg hc.le (sub_nonneg.mpr hMA_le)
    exact sub_nonneg.mp h_nn

/-- **Theorem 1, non-negative perturbed version** (Frank–Lieb, arXiv:1306.5358).

    For any quantum channel `E : CPTP ℋ ℋ` whose unital image `E 1` is
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
    (E : CPTP ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hEI : E.toFun (1 : L ℋ) ∈ pdSetLM (ℋ := 𝒦))
    {ε : ℝ} (hε : 0 < ε) :
    sandwichedRenyiDiv α (E.toFun (ρ + (ε : ℂ) • (1 : L ℋ)))
        (E.toFun (σ + (ε : ℂ) • (1 : L ℋ))) ≤
      sandwichedRenyiDiv α (ρ + (ε : ℂ) • (1 : L ℋ)) (σ + (ε : ℂ) • (1 : L ℋ)) := by
  -- Positivity of `E` is automatic for completely-positive maps.
  have hE_pos : ∀ {X : L ℋ}, 0 ≤ X → 0 ≤ E.toFun X := fun {X} hX =>
    map_nonneg E.toCompletelyPositiveMap hX
  -- Perturbed operators are pd.
  have hρ_ε : (ρ + (ε : ℂ) • (1 : L ℋ)) ∈ pdSetLM (ℋ := ℋ) :=
    nonneg_add_pos_smul_one_pdSetLM hρ hε
  have hσ_ε : (σ + (ε : ℂ) • (1 : L ℋ)) ∈ pdSetLM (ℋ := ℋ) :=
    nonneg_add_pos_smul_one_pdSetLM hσ hε
  -- `E` is linear, so `E(ρ + ε • 1) = E ρ + ε • E 1`, and similarly for σ.
  set Elm : (L ℋ) →ₗ[ℂ] (L 𝒦) := E.toCompletelyPositiveMap.toLinearMap with hElm_def
  have hE_toFun_eq : ∀ X, E.toFun X = Elm X := fun _ => rfl
  have hE_linear : ∀ X, E.toFun (X + (ε : ℂ) • (1 : L ℋ)) =
      E.toFun X + (ε : ℂ) • E.toFun (1 : L ℋ) := by
    intro X
    rw [hE_toFun_eq, hE_toFun_eq, hE_toFun_eq, LinearMap.map_add, LinearMap.map_smul]
  -- `E(ρ + ε • 1) = E ρ + ε • E 1` is pd (non-negative + ε • pd).
  have hEρ_ε : E.toFun (ρ + (ε : ℂ) • (1 : L ℋ)) ∈ pdSetLM (ℋ := 𝒦) := by
    rw [hE_linear]
    exact pdSetLM_add_nonneg (hE_pos hρ) (pdSetLM_pos_smul hEI hε)
  have hEσ_ε : E.toFun (σ + (ε : ℂ) • (1 : L ℋ)) ∈ pdSetLM (ℋ := 𝒦) := by
    rw [hE_linear]
    exact pdSetLM_add_nonneg (hE_pos hσ) (pdSetLM_pos_smul hEI hε)
  -- Apply the pd Theorem 1.
  exact sandwichedRenyiDiv_monotone E hα_ge hα_ne1 hρ_ε hσ_ε hEρ_ε hEσ_ε

/-- The unit operator `1 : L ℋ` is positive-definite. -/
lemma one_pdSetLM {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] :
    (1 : L ℋ) ∈ pdSetLM (ℋ := ℋ) := by
  have h := pos_smul_one_pdSetLM (ℋ := ℋ) (one_pos : (0 : ℝ) < 1)
  rwa [show ((1 : ℝ) : ℂ) = 1 from by norm_cast, one_smul] at h

/-- For `σ ∈ pdSetLM`, the kernel is trivial: `LinearMap.ker σ = ⊥`. -/
lemma ker_eq_bot_of_pdSetLM
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {σ : L ℋ} (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    LinearMap.ker σ = ⊥ := by
  have h_unit : IsUnit σ := isUnit_of_pdSetLM hσ
  obtain ⟨u, hu⟩ := h_unit
  rw [LinearMap.ker_eq_bot]
  intro x y hxy
  -- `u.inv * σ = 1` in `L ℋ`; apply to both sides.
  have h_invσ : (u.inv : L ℋ) * σ = 1 := by rw [← hu]; exact u.inv_val
  -- For `f g : L ℋ` and `z : ℋ`, `(f * g) z = f (g z)` definitionally.
  have h_apply : ∀ z : ℋ, (u.inv : L ℋ) (σ z) = z := fun z => by
    have : ((u.inv : L ℋ) * σ) z = z := by rw [h_invσ]; rfl
    exact this
  rw [← h_apply x, ← h_apply y, hxy]


end SandwichedRenyiRelativeEntropy
