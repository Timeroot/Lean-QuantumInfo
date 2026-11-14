/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumMechanics.QuantumChannel
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Tensor product CFC infrastructure

Infrastructure for the continuous functional calculus on tensor products,
proving that `CFC.rpow` distributes over tensor products of operators:
`(A ⊗ B)^p = A^p ⊗ B^p`.

## Strategy

Factor `TensorProduct.map A B = A.rTensor ℋ₂ * B.lTensor ℋ₁` where the two factors commute,
then use `StarAlgHomClass.map_cfc` to distribute `CFC.rpow` through each factor.

## Main results

* `TensorCFC.rTensorStarAlgHom` / `lTensorStarAlgHom`:
  The maps `A ↦ A.rTensor ℋ₂` and `B ↦ B.lTensor ℋ₁` as star algebra homomorphisms.
* `TensorCFC.rpow_rTensor` / `rpow_lTensor`:
  `CFC.rpow` distributes through `rTensor` / `lTensor`.
* `TensorCFC.rpow_tensorProduct`:
  `CFC.rpow (map A B) p = map (CFC.rpow A p) (CFC.rpow B p)` (modulo `rpow_mul_comm_nonneg`).
-/

open QuantumState QuantumChannel TensorProduct
open scoped NNReal Polynomial

namespace TensorCFC

universe u v
variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable [Nontrivial ℋ₁] [Nontrivial ℋ₂]

/-! ### Scalar tower instances -/

instance instIsScalarTower₁ : IsScalarTower ℝ≥0 ℂ (L ℋ₁) :=
  ⟨fun r s a => smul_assoc (r : ℂ) s a⟩
instance instIsScalarTower₂ : IsScalarTower ℝ≥0 ℂ (L ℋ₂) :=
  ⟨fun r s a => smul_assoc (r : ℂ) s a⟩
instance instIsScalarTowerTensor : IsScalarTower ℝ≥0 ℂ (L (ℋ₁ ⊗[ℂ] ℋ₂)) :=
  ⟨fun r s a => smul_assoc (r : ℂ) s a⟩

/-! ### Star algebra homomorphisms for rTensor / lTensor -/

noncomputable def rTensorStarAlgHom : L ℋ₁ →⋆ₐ[ℂ] L (ℋ₁ ⊗[ℂ] ℋ₂) where
  toFun f := f.rTensor ℋ₂
  map_one' := TensorProduct.ext' fun _ _ => rfl
  map_mul' _ _ := TensorProduct.ext' fun _ _ => by simp
  map_zero' := TensorProduct.ext' fun _ _ => by simp
  map_add' _ _ := TensorProduct.ext' fun _ _ => by simp
  commutes' r := TensorProduct.ext' fun _ _ => by
    simp [Algebra.algebraMap_eq_smul_one, smul_tmul']
  map_star' f := by
    simp only [LinearMap.star_eq_adjoint]
    exact (LinearMap.adjoint_rTensor f).symm

noncomputable def lTensorStarAlgHom : L ℋ₂ →⋆ₐ[ℂ] L (ℋ₁ ⊗[ℂ] ℋ₂) where
  toFun g := g.lTensor ℋ₁
  map_one' := TensorProduct.ext' fun _ _ => rfl
  map_mul' _ _ := TensorProduct.ext' fun _ _ => by simp
  map_zero' := TensorProduct.ext' fun _ _ => by simp
  map_add' _ _ := TensorProduct.ext' fun _ _ => by simp
  commutes' r := TensorProduct.ext' fun _ _ => by
    simp [Algebra.algebraMap_eq_smul_one, smul_tmul']
  map_star' g := by
    simp only [LinearMap.star_eq_adjoint]
    exact (LinearMap.adjoint_lTensor g).symm

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
@[simp] lemma rTensorStarAlgHom_apply (f : L ℋ₁) :
    (rTensorStarAlgHom (ℋ₂ := ℋ₂)) f = f.rTensor ℋ₂ := rfl

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
@[simp] lemma lTensorStarAlgHom_apply (g : L ℋ₂) :
    (lTensorStarAlgHom (ℋ₁ := ℋ₁)) g = g.lTensor ℋ₁ := rfl

/-! ### Factorization and commutativity -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma map_eq_rTensor_mul_lTensor (f : L ℋ₁) (g : L ℋ₂) :
    (TensorProduct.map f g : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      (rTensorStarAlgHom (ℋ₂ := ℋ₂)) f * (lTensorStarAlgHom (ℋ₁ := ℋ₁)) g :=
  TensorProduct.ext' fun x y => by
    simp only [rTensorStarAlgHom_apply, lTensorStarAlgHom_apply]
    change TensorProduct.map f g (x ⊗ₜ y) =
      (f.rTensor ℋ₂).comp (g.lTensor ℋ₁) (x ⊗ₜ y)
    simp

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma map_eq_lTensor_mul_rTensor (f : L ℋ₁) (g : L ℋ₂) :
    (TensorProduct.map f g : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      (lTensorStarAlgHom (ℋ₁ := ℋ₁)) g * (rTensorStarAlgHom (ℋ₂ := ℋ₂)) f :=
  TensorProduct.ext' fun x y => by
    simp only [rTensorStarAlgHom_apply, lTensorStarAlgHom_apply]
    change TensorProduct.map f g (x ⊗ₜ y) =
      (g.lTensor ℋ₁).comp (f.rTensor ℋ₂) (x ⊗ₜ y)
    simp

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma commute_rTensor_lTensor (f : L ℋ₁) (g : L ℋ₂) :
    Commute ((rTensorStarAlgHom (ℋ₂ := ℋ₂)) f)
      ((lTensorStarAlgHom (ℋ₁ := ℋ₁)) g) := by
  change _ * _ = _ * _
  rw [← map_eq_rTensor_mul_lTensor, ← map_eq_lTensor_mul_rTensor]

/-! ### Continuity -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma continuous_rTensorStarAlgHom :
    Continuous (rTensorStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)) :=
  (rTensorStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).toAlgHom.toLinearMap.continuous_of_finiteDimensional

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma continuous_lTensorStarAlgHom :
    Continuous (lTensorStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)) :=
  (lTensorStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).toAlgHom.toLinearMap.continuous_of_finiteDimensional

/-! ### Nonneg preservation -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma rTensorStarAlgHom_nonneg (f : L ℋ₁) (hf : 0 ≤ f) :
    0 ≤ (rTensorStarAlgHom (ℋ₂ := ℋ₂)) f := by
  obtain ⟨p, hp, rfl⟩ := (StarOrderedRing.le_iff 0 f).mp hf
  rw [StarOrderedRing.le_iff]
  simp only [zero_add]
  exact ⟨rTensorStarAlgHom p,
    AddSubmonoid.closure_induction
      (fun x ⟨s, hs⟩ => AddSubmonoid.subset_closure
        ⟨rTensorStarAlgHom s, by
          change star (rTensorStarAlgHom s) * rTensorStarAlgHom s = rTensorStarAlgHom x
          rw [← map_star rTensorStarAlgHom, ← map_mul rTensorStarAlgHom]
          exact congr_arg rTensorStarAlgHom hs⟩)
      (by rw [map_zero]; exact AddSubmonoid.zero_mem _)
      (fun x y _ _ hx hy => by rw [map_add]; exact AddSubmonoid.add_mem _ hx hy)
      hp,
    rfl⟩

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma lTensorStarAlgHom_nonneg (g : L ℋ₂) (hg : 0 ≤ g) :
    0 ≤ (lTensorStarAlgHom (ℋ₁ := ℋ₁)) g := by
  obtain ⟨p, hp, rfl⟩ := (StarOrderedRing.le_iff 0 g).mp hg
  rw [StarOrderedRing.le_iff]
  simp only [zero_add]
  exact ⟨lTensorStarAlgHom p,
    AddSubmonoid.closure_induction
      (fun x ⟨s, hs⟩ => AddSubmonoid.subset_closure
        ⟨lTensorStarAlgHom s, by
          change star (lTensorStarAlgHom s) * lTensorStarAlgHom s = lTensorStarAlgHom x
          rw [← map_star lTensorStarAlgHom, ← map_mul lTensorStarAlgHom]
          exact congr_arg lTensorStarAlgHom hs⟩)
      (by rw [map_zero]; exact AddSubmonoid.zero_mem _)
      (fun x y _ _ hx hy => by rw [map_add]; exact AddSubmonoid.add_mem _ hx hy)
      hp,
    rfl⟩

/-! ### Unit reflection for rTensor / lTensor

In finite dimensions, `B.rTensor ℋ₂` is a unit iff `B` is a unit.
The forward direction uses a basis element to embed `ker B` into `ker (B.rTensor ℋ₂)`.
The reverse follows from flatness. -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma injective_rTensor_of_injective (B : L ℋ₁) (hB : Function.Injective B) :
    Function.Injective (B.rTensor ℋ₂) :=
  Module.Flat.rTensor_preserves_injective_linearMap B hB

omit [Nontrivial ℋ₁] in
private lemma injective_of_injective_rTensor (B : L ℋ₁) (hB : Function.Injective (B.rTensor ℋ₂)) :
    Function.Injective B := by
  intro v₁ v₂ hv
  have 𝒞 := Module.Free.chooseBasis ℂ ℋ₂
  haveI : Nonempty (Module.Free.ChooseBasisIndex ℂ ℋ₂) :=
    Fintype.card_pos_iff.mp (by
      have := Module.finrank_pos (R := ℂ) (M := ℋ₂)
      rwa [Module.finrank_eq_card_chooseBasisIndex] at this)
  obtain ⟨i₀⟩ := ‹Nonempty (Module.Free.ChooseBasisIndex ℂ ℋ₂)›
  have h : B.rTensor ℋ₂ (v₁ ⊗ₜ 𝒞 i₀) = B.rTensor ℋ₂ (v₂ ⊗ₜ 𝒞 i₀) := by
    simp [LinearMap.rTensor_tmul, hv]
  have hinj := hB h
  have key := congr_arg (TensorProduct.equivFinsuppOfBasisRight (M := ℋ₁) 𝒞) hinj
  simp only [TensorProduct.equivFinsuppOfBasisRight_apply_tmul,
    𝒞.repr_self, Finsupp.mapRange_single, one_smul] at key
  exact Finsupp.single_injective i₀ key

omit [Nontrivial ℋ₁] in
private lemma isUnit_rTensor_iff (B : L ℋ₁) :
    IsUnit (B.rTensor ℋ₂) ↔ IsUnit B := by
  simp only [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact ⟨injective_of_injective_rTensor B, injective_rTensor_of_injective B⟩

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma injective_lTensor_of_injective (B : L ℋ₂) (hB : Function.Injective B) :
    Function.Injective (B.lTensor ℋ₁) :=
  Module.Flat.lTensor_preserves_injective_linearMap B hB

omit [Nontrivial ℋ₂] in
private lemma injective_of_injective_lTensor (B : L ℋ₂) (hB : Function.Injective (B.lTensor ℋ₁)) :
    Function.Injective B := by
  intro v₁ v₂ hv
  have 𝒞 := Module.Free.chooseBasis ℂ ℋ₁
  haveI : Nonempty (Module.Free.ChooseBasisIndex ℂ ℋ₁) :=
    Fintype.card_pos_iff.mp (by
      have := Module.finrank_pos (R := ℂ) (M := ℋ₁)
      rwa [Module.finrank_eq_card_chooseBasisIndex] at this)
  obtain ⟨i₀⟩ := ‹Nonempty (Module.Free.ChooseBasisIndex ℂ ℋ₁)›
  have h : B.lTensor ℋ₁ (𝒞 i₀ ⊗ₜ v₁) = B.lTensor ℋ₁ (𝒞 i₀ ⊗ₜ v₂) := by
    simp [LinearMap.lTensor_tmul, hv]
  have hinj := hB h
  have key := congr_arg (fun x => (TensorProduct.equivFinsuppOfBasisLeft (N := ℋ₂) 𝒞 x) i₀) hinj
  simp only [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply] at key
  simp only [𝒞.repr_self, Finsupp.single_eq_same, one_smul] at key
  exact key

omit [Nontrivial ℋ₂] in
private lemma isUnit_lTensor_iff (B : L ℋ₂) :
    IsUnit (B.lTensor ℋ₁) ↔ IsUnit B := by
  simp only [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact ⟨injective_of_injective_lTensor B, injective_lTensor_of_injective B⟩

/-! ### Spectrum equality for tensor embeddings -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma rTensor_algebraMap (r : ℂ) :
    (algebraMap ℂ (L ℋ₁) r).rTensor ℋ₂ = algebraMap ℂ (L (ℋ₁ ⊗[ℂ] ℋ₂)) r :=
  TensorProduct.ext' fun _ _ => by simp [Algebra.algebraMap_eq_smul_one, smul_tmul']

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma lTensor_algebraMap (r : ℂ) :
    (algebraMap ℂ (L ℋ₂) r).lTensor ℋ₁ = algebraMap ℂ (L (ℋ₁ ⊗[ℂ] ℋ₂)) r :=
  TensorProduct.ext' fun _ _ => by simp [Algebra.algebraMap_eq_smul_one, smul_tmul']

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma rTensor_sub_algebraMap (A : L ℋ₁) (r : ℂ) :
    (algebraMap ℂ (L ℋ₁) r - A).rTensor ℋ₂ =
      algebraMap ℂ (L (ℋ₁ ⊗[ℂ] ℋ₂)) r - A.rTensor ℋ₂ := by
  rw [LinearMap.rTensor_sub, rTensor_algebraMap]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma lTensor_sub_algebraMap (B : L ℋ₂) (r : ℂ) :
    (algebraMap ℂ (L ℋ₂) r - B).lTensor ℋ₁ =
      algebraMap ℂ (L (ℋ₁ ⊗[ℂ] ℋ₂)) r - B.lTensor ℋ₁ := by
  rw [LinearMap.lTensor_sub, lTensor_algebraMap]

omit [Nontrivial ℋ₁] in
lemma spectrum_rTensorStarAlgHom (A : L ℋ₁) :
    spectrum ℝ≥0 ((rTensorStarAlgHom (ℋ₂ := ℋ₂)) A) = spectrum ℝ≥0 A := by
  simp only [← spectrum.preimage_algebraMap ℂ (R := ℝ≥0)]
  congr 1
  ext r
  simp only [spectrum.mem_iff, rTensorStarAlgHom_apply]
  constructor
  · intro h hunit
    apply h
    rw [← rTensor_sub_algebraMap]
    exact (isUnit_rTensor_iff _).mpr hunit
  · intro h hunit
    apply h
    rw [← rTensor_sub_algebraMap] at hunit
    exact (isUnit_rTensor_iff _).mp hunit

omit [Nontrivial ℋ₂] in
lemma spectrum_lTensorStarAlgHom (B : L ℋ₂) :
    spectrum ℝ≥0 ((lTensorStarAlgHom (ℋ₁ := ℋ₁)) B) = spectrum ℝ≥0 B := by
  simp only [← spectrum.preimage_algebraMap ℂ (R := ℝ≥0)]
  congr 1
  ext r
  simp only [spectrum.mem_iff, lTensorStarAlgHom_apply]
  constructor
  · intro h hunit
    apply h
    rw [← lTensor_sub_algebraMap]
    exact (isUnit_lTensor_iff _).mpr hunit
  · intro h hunit
    apply h
    rw [← lTensor_sub_algebraMap] at hunit
    exact (isUnit_lTensor_iff _).mp hunit

/-! ### CFC distribution through rTensor / lTensor -/

omit [Nontrivial ℋ₁] in
set_option backward.isDefEq.respectTransparency false in
lemma rpow_rTensor (A : L ℋ₁) (p : ℝ) (hA : 0 ≤ A) :
    CFC.rpow ((rTensorStarAlgHom (ℋ₂ := ℋ₂)) A) p =
      (rTensorStarAlgHom (ℋ₂ := ℋ₂)) (CFC.rpow A p) := by
  simp only [CFC.rpow]
  have hφ := continuous_rTensorStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)
  have hφA := rTensorStarAlgHom_nonneg (ℋ₂ := ℋ₂) A hA
  by_cases hf : ContinuousOn (· ^ p : ℝ≥0 → ℝ≥0) (spectrum ℝ≥0 A)
  · exact (rTensorStarAlgHom.map_cfc (· ^ p) A hf hφ hA hφA).symm
  · have hf' : ¬ContinuousOn (· ^ p : ℝ≥0 → ℝ≥0)
        (spectrum ℝ≥0 ((rTensorStarAlgHom (ℋ₂ := ℋ₂)) A)) := by
      rwa [spectrum_rTensorStarAlgHom]
    rw [cfc_apply_of_not_and A (not_and_of_not_right _ hf), map_zero,
      cfc_apply_of_not_and _ (not_and_of_not_right _ hf')]

omit [Nontrivial ℋ₂] in
set_option backward.isDefEq.respectTransparency false in
lemma rpow_lTensor (B : L ℋ₂) (p : ℝ) (hB : 0 ≤ B) :
    CFC.rpow ((lTensorStarAlgHom (ℋ₁ := ℋ₁)) B) p =
      (lTensorStarAlgHom (ℋ₁ := ℋ₁)) (CFC.rpow B p) := by
  simp only [CFC.rpow]
  have hφ := continuous_lTensorStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)
  have hφB := lTensorStarAlgHom_nonneg (ℋ₁ := ℋ₁) B hB
  by_cases hf : ContinuousOn (· ^ p : ℝ≥0 → ℝ≥0) (spectrum ℝ≥0 B)
  · exact (lTensorStarAlgHom.map_cfc (· ^ p) B hf hφ hB hφB).symm
  · have hf' : ¬ContinuousOn (· ^ p : ℝ≥0 → ℝ≥0)
        (spectrum ℝ≥0 ((lTensorStarAlgHom (ℋ₁ := ℋ₁)) B)) := by
      rwa [spectrum_lTensorStarAlgHom]
    rw [cfc_apply_of_not_and B (not_and_of_not_right _ hf), map_zero,
      cfc_apply_of_not_and _ (not_and_of_not_right _ hf')]

/-! ### CFC eigenvalue property

In finite dimensions, the CFC maps eigenvectors to eigenvectors with eigenvalues
transformed by the function: if `T v = μ • v` then `cfc f T v = f(μ) • v`.
The proof uses Lagrange interpolation on the finite spectrum combined with
`cfc_congr` and `cfc_polynomial`. -/

private lemma isScalarTower_real {ℋ : Type*} [Qudit ℋ] :
    IsScalarTower ℝ ℂ (L ℋ) :=
  ⟨fun r s a => by
    change ((r : ℂ) • s) • a = (r : ℂ) • s • a
    rw [smul_assoc]⟩

private lemma pow_apply_eigenvector {ℋ : Type*} [Qudit ℋ]
    (T : L ℋ) (μ : ℂ) (v : ℋ) (hv : T v = μ • v) (n : ℕ) :
    (T ^ n) v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : (T ^ (n + 1)) v = (T ^ n) (T v) := rfl
    rw [this, hv, map_smul, ih, smul_smul, pow_succ']

private lemma aeval_apply_eigenvector {ℋ : Type*} [Qudit ℋ]
    (T : L ℋ) (μ : ℂ) (v : ℋ) (hv : T v = μ • v) (q : ℝ[X]) :
    (Polynomial.aeval T q) v = (Polynomial.aeval μ q) • v := by
  haveI := isScalarTower_real (ℋ := ℋ)
  induction q using Polynomial.induction_on' with
  | add p₁ p₂ hp₁ hp₂ =>
    simp only [map_add, LinearMap.add_apply, hp₁, hp₂, add_smul]
  | monomial n r =>
    simp only [Polynomial.aeval_monomial]
    change (algebraMap ℝ (L ℋ) r) ((T ^ n) v) = _
    rw [pow_apply_eigenvector T μ v hv n, map_smul,
        IsScalarTower.algebraMap_apply ℝ ℂ (L ℋ)]
    simp only [Module.algebraMap_end_apply, smul_smul, mul_comm]

private lemma spectrum_real_finite {ℋ : Type*} [Qudit ℋ]
    (T : L ℋ) : Set.Finite (spectrum ℝ T) := by
  haveI := isScalarTower_real (ℋ := ℋ)
  rw [← spectrum.preimage_algebraMap ℂ (R := ℝ)]
  exact (Module.End.finite_spectrum T).preimage
    (fun _ _ _ _ h => RCLike.ofReal_injective h)

private lemma cfc_apply_eigenvector {ℋ : Type*} [Qudit ℋ]
    (T : L ℋ) (hT_sa : IsSelfAdjoint T) (f : ℝ → ℝ)
    (v : ℋ) (μ : ℝ) (hv : T v = (algebraMap ℝ ℂ μ) • v) (hμ : μ ∈ spectrum ℝ T) :
    (cfc f T : L ℋ) v = (algebraMap ℝ ℂ (f μ)) • v := by
  haveI := isScalarTower_real (ℋ := ℋ)
  have hfin := spectrum_real_finite T
  set S := hfin.toFinset
  have hS_mem : ∀ x : ℝ, x ∈ S ↔ x ∈ spectrum ℝ T := fun x => hfin.mem_toFinset
  have hμ_mem_S : μ ∈ S := (hS_mem μ).mpr hμ
  have hinj : Set.InjOn (id : ℝ → ℝ) (↑S : Set ℝ) :=
    Function.injective_id.injOn
  let q := Lagrange.interpolate S id (fun s => f s)
  have hq_eval : ∀ x ∈ S, Polynomial.eval x q = f x :=
    fun x hx => Lagrange.eval_interpolate_at_node (fun s => f s) hinj hx
  have hcfc_eq : cfc f T = cfc q.eval T := by
    apply cfc_congr
    intro x hx
    exact (hq_eval x ((hS_mem x).mpr hx)).symm
  have hpoly : cfc q.eval T = Polynomial.aeval T q :=
    cfc_polynomial q T
  rw [hcfc_eq, hpoly, aeval_apply_eigenvector T (algebraMap ℝ ℂ μ) v hv q]
  congr 1
  rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
  congr 1
  exact hq_eval μ hμ_mem_S

/-! ### Main result: rpow distributes over tensor products

Proved directly using eigenvector bases for A and B. The tensor product
of eigenvector bases provides a basis for `ℋ₁ ⊗ ℋ₂` of simultaneous
eigenvectors, reducing the proof to the scalar identity `(λμ)^p = λ^p μ^p`. -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma star_map (A : L ℋ₁) (B : L ℋ₂) :
    star (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      TensorProduct.map (star A) (star B) := by
  simp only [LinearMap.star_eq_adjoint, TensorProduct.adjoint_map]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma isSelfAdjoint_map_of_nonneg (A : L ℋ₁) (B : L ℋ₂)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    IsSelfAdjoint (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) := by
  rw [IsSelfAdjoint, star_map, (IsSelfAdjoint.of_nonneg hA).star_eq,
      (IsSelfAdjoint.of_nonneg hB).star_eq]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma map_nonneg_of_nonneg (A : L ℋ₁) (B : L ℋ₂)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) := by
  set sA := CFC.sqrt A
  set sB := CFC.sqrt B
  have hsA := CFC.sqrt_nonneg A
  have hsB := CFC.sqrt_nonneg B
  have : TensorProduct.map A B =
      star (TensorProduct.map sA sB) * TensorProduct.map sA sB := by
    rw [star_map, (IsSelfAdjoint.of_nonneg hsA).star_eq,
        (IsSelfAdjoint.of_nonneg hsB).star_eq, ← TensorProduct.map_mul,
        CFC.sqrt_mul_sqrt_self A, CFC.sqrt_mul_sqrt_self B]
  rw [this]
  exact star_mul_self_nonneg _

private lemma eigenvalue_nonneg_of_nonneg {ℋ : Type*} [Qudit ℋ]
    {n : ℕ} (T : L ℋ) (hT : 0 ≤ T) (hT_sym : T.IsSymmetric) (hn : Module.finrank ℂ ℋ = n)
    (i : Fin n) : 0 ≤ hT_sym.eigenvalues hn i := by
  have hpos := (LinearMap.nonneg_iff_isPositive T).mp hT
  set v := hT_sym.eigenvectorBasis hn i
  have hv_ne : v ≠ 0 := (hT_sym.eigenvectorBasis hn).toBasis.ne_zero i
  have hinn := hpos.2 v
  rw [hT_sym.apply_eigenvectorBasis, inner_smul_left, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul] at hinn
  refine nonneg_of_mul_nonneg_left hinn ?_
  rw [inner_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.mpr hv_ne) 2

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
set_option backward.isDefEq.respectTransparency false in
theorem rpow_tensorProduct (A : L ℋ₁) (B : L ℋ₂) (p : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    CFC.rpow (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) p =
      TensorProduct.map (CFC.rpow A p) (CFC.rpow B p) := by
  haveI := isScalarTower_real (ℋ := ℋ₁ ⊗[ℂ] ℋ₂)
  have hA_sa := IsSelfAdjoint.of_nonneg hA
  have hB_sa := IsSelfAdjoint.of_nonneg hB
  have hA_sym := (LinearMap.isSymmetric_iff_isSelfAdjoint A).mpr hA_sa
  have hB_sym := (LinearMap.isSymmetric_iff_isSelfAdjoint B).mpr hB_sa
  have hAB_sa := isSelfAdjoint_map_of_nonneg A B hA hB
  set n₁ := Module.finrank ℂ ℋ₁
  set n₂ := Module.finrank ℂ ℋ₂
  set eA := hA_sym.eigenvectorBasis (rfl : Module.finrank ℂ ℋ₁ = n₁)
  set eB := hB_sym.eigenvectorBasis (rfl : Module.finrank ℂ ℋ₂ = n₂)
  set eigA := hA_sym.eigenvalues (rfl : Module.finrank ℂ ℋ₁ = n₁)
  set eigB := hB_sym.eigenvalues (rfl : Module.finrank ℂ ℋ₂ = n₂)
  set f : ℝ → ℝ := fun x => ((x.toNNReal) ^ p : ℝ≥0)
  have hA_eig : ∀ i, A (eA i) = (algebraMap ℝ ℂ (eigA i)) • (eA i) := by
    intro i; rw [RCLike.algebraMap_eq_ofReal]; exact hA_sym.apply_eigenvectorBasis _ i
  have hB_eig : ∀ j, B (eB j) = (algebraMap ℝ ℂ (eigB j)) • (eB j) := by
    intro j; rw [RCLike.algebraMap_eq_ofReal]; exact hB_sym.apply_eigenvectorBasis _ j
  have heigA_nonneg : ∀ i, 0 ≤ eigA i :=
    fun i => eigenvalue_nonneg_of_nonneg A hA hA_sym _ i
  have heigB_nonneg : ∀ j, 0 ≤ eigB j :=
    fun j => eigenvalue_nonneg_of_nonneg B hB hB_sym _ j
  have hAB_nn := map_nonneg_of_nonneg A B hA hB
  -- Convert CFC.rpow to real-valued cfc via cfc_nnreal_eq_real
  have hrpow_eq_A : CFC.rpow A p = cfc f A := cfc_nnreal_eq_real ..
  have hrpow_eq_B : CFC.rpow B p = cfc f B := cfc_nnreal_eq_real ..
  have hrpow_eq_AB : CFC.rpow (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) p =
      cfc f (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) := cfc_nnreal_eq_real ..
  rw [hrpow_eq_A, hrpow_eq_B, hrpow_eq_AB]
  -- Prove by extension on the tensor product eigenvector basis
  apply (eA.toBasis.tensorProduct eB.toBasis).ext
  intro ⟨i, j⟩
  have htb : (eA.toBasis.tensorProduct eB.toBasis) (i, j) = eA i ⊗ₜ eB j := by
    rw [eA.toBasis.tensorProduct_apply]; simp [OrthonormalBasis.coe_toBasis]
  rw [htb, map_tmul]
  -- RHS: (cfc f A) (eA i) ⊗ₜ (cfc f B) (eB j)
  have heigA_spec : ∀ i, eigA i ∈ spectrum ℝ A := by
    intro i
    rw [← spectrum.preimage_algebraMap ℂ (R := ℝ), Set.mem_preimage]
    exact (hA_sym.hasEigenvalue_eigenvalues _ i).mem_spectrum
  have heigB_spec : ∀ j, eigB j ∈ spectrum ℝ B := by
    intro j
    rw [← spectrum.preimage_algebraMap ℂ (R := ℝ), Set.mem_preimage]
    exact (hB_sym.hasEigenvalue_eigenvalues _ j).mem_spectrum
  rw [cfc_apply_eigenvector A hA_sa f (eA i) (eigA i) (hA_eig i) (heigA_spec i),
      cfc_apply_eigenvector B hB_sa f (eB j) (eigB j) (hB_eig j) (heigB_spec j)]
  have hAB_eig : (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) (eA i ⊗ₜ eB j) =
      (algebraMap ℝ ℂ (eigA i * eigB j)) • (eA i ⊗ₜ eB j) := by
    rw [map_tmul, hA_eig i, hB_eig j, TensorProduct.smul_tmul_smul, ← map_mul]
  have hAB_spec : eigA i * eigB j ∈ spectrum ℝ (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) := by
    rw [← spectrum.preimage_algebraMap ℂ (R := ℝ), Set.mem_preimage]
    rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
    rw [Module.End.hasEigenvalue_iff]
    intro heq
    have hmem : eA i ⊗ₜ[ℂ] eB j ∈ (⊥ : Submodule ℂ (ℋ₁ ⊗[ℂ] ℋ₂)) :=
      heq ▸ Module.End.mem_eigenspace_iff.mpr hAB_eig
    rw [Submodule.mem_bot] at hmem
    have htp := eA.toBasis.tensorProduct_apply eB.toBasis i j
    exact (eA.toBasis.tensorProduct eB.toBasis).ne_zero (i, j) (htp.trans hmem)
  rw [cfc_apply_eigenvector _ hAB_sa f _ _ hAB_eig hAB_spec]
  -- Now both sides have form scalar • (eA i ⊗ₜ eB j), show scalars agree
  -- LHS: algebraMap ℝ ℂ (f (eigA i * eigB j)) • (eA i ⊗ₜ eB j)
  -- RHS: (algebraMap ℝ ℂ (f (eigA i))) • eA i ⊗ₜ (algebraMap ℝ ℂ (f (eigB j))) • eB j
  -- First simplify RHS tensor product scalar to single smul
  rw [TensorProduct.smul_tmul_smul]
  congr 1
  rw [← map_mul]
  congr 1
  show (f (eigA i * eigB j) : ℝ) = (f (eigA i) : ℝ) * (f (eigB j) : ℝ)
  simp only [f]
  rw [← NNReal.coe_mul]
  congr 1
  rw [Real.toNNReal_mul (heigA_nonneg i), NNReal.mul_rpow]

end TensorCFC
