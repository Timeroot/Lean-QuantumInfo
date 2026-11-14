/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumMechanics.QuantumState
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.LinearMapPiProd

-- These typeclasses are kept on several declarations as part of a stable API
-- (e.g. matching downstream signatures), even when the type does not literally
-- mention them; silence the Mathlib hygiene linters for the whole file.
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace QuantumChannel

open QuantumState
open TensorProduct

universe u v w

section Definition

-- The set of linear maps
abbrev T (ℋ₁ : Type u) (ℋ₂ : Type v)
  [AddCommGroup ℋ₁] [Module ℂ ℋ₁] [AddCommGroup ℋ₂] [Module ℂ ℋ₂] : Type (max u v) :=
  (L ℋ₁) →ₗ[ℂ] (L ℋ₂)

section ContinuousLinearMapsAreCStarAlgebras

noncomputable instance continuous_instance {ℋ : Type u} [Qudit ℋ] : CStarAlgebra (ℋ →L[ℂ] ℋ)
  := inferInstance

noncomputable instance (ℋ : Type u) [Qudit ℋ] : Norm (L ℋ) where
  norm := fun X => ‖X.toContinuousLinearMap‖

noncomputable instance (ℋ : Type u) [Qudit ℋ] : MetricSpace (L ℋ) :=
  MetricSpace.induced LinearMap.toContinuousLinearMap
    LinearMap.toContinuousLinearMap.injective inferInstance

noncomputable instance linear_isometry_equiv {ℋ : Type u} [Qudit ℋ] : (L ℋ) ≃ᵢ (ℋ →L[ℂ] ℋ) where
  toFun := fun X => X.toContinuousLinearMap
  invFun := fun X => X.toLinearMap
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  isometry_toFun := fun _ _ => rfl

noncomputable instance c_algebra_instance {ℋ : Type u} [Qudit ℋ] : Algebra ℂ (L ℋ) := inferInstance

noncomputable instance (ℋ : Type u) [Qudit ℋ] : CStarAlgebra (L ℋ) where
  dist_eq x y := continuous_instance.dist_eq x.toContinuousLinearMap y.toContinuousLinearMap
  norm_mul_le x y := continuous_instance.norm_mul_le x.toContinuousLinearMap y.toContinuousLinearMap
  complete := (linear_isometry_equiv.completeSpace_iff.mpr
    continuous_instance.toCompleteSpace).complete
  norm_mul_self_le x := continuous_instance.norm_mul_self_le x.toContinuousLinearMap
  algebraMap := c_algebra_instance.algebraMap
  commutes' := c_algebra_instance.commutes'
  smul_def' := c_algebra_instance.smul_def'
  norm_smul_le r x := continuous_instance.norm_smul_le r x.toContinuousLinearMap

noncomputable instance continuous_sor_instance {ℋ : Type u} [Qudit ℋ] : StarOrderedRing (ℋ →L[ℂ] ℋ)
  := inferInstance

private lemma closure_clm_of_closure_lm {ℋ : Type u} [Qudit ℋ]
    {p : L ℋ} (hp : p ∈ AddSubmonoid.closure (Set.range fun s : L ℋ ↦ star s * s)) :
    p.toContinuousLinearMap ∈
      AddSubmonoid.closure (Set.range fun s : ℋ →L[ℂ] ℋ ↦ star s * s) := by
  induction hp using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, hs⟩ := hx
    exact AddSubmonoid.subset_closure ⟨s.toContinuousLinearMap, by subst hs; rfl⟩
  | zero => exact AddSubmonoid.zero_mem _
  | add x y _ _ ihx ihy => exact AddSubmonoid.add_mem _ ihx ihy

private lemma closure_lm_of_closure_clm {ℋ : Type u} [Qudit ℋ]
    {p : ℋ →L[ℂ] ℋ} (hp : p ∈ AddSubmonoid.closure (Set.range fun s : ℋ →L[ℂ] ℋ ↦ star s * s)) :
    p.toLinearMap ∈
      AddSubmonoid.closure (Set.range fun s : L ℋ ↦ star s * s) := by
  induction hp using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, hs⟩ := hx
    exact AddSubmonoid.subset_closure ⟨s.toLinearMap, by subst hs; rfl⟩
  | zero => exact AddSubmonoid.zero_mem _
  | add x y _ _ ihx ihy => exact AddSubmonoid.add_mem _ ihx ihy

noncomputable instance (ℋ : Type u) [Qudit ℋ] : StarOrderedRing (L ℋ) where
  le_iff x y := by
    constructor
    · intro h
      obtain ⟨p, hp, hy⟩ :=
        (continuous_sor_instance.le_iff x.toContinuousLinearMap y.toContinuousLinearMap).mp h
      use p.toLinearMap
      exact ⟨closure_lm_of_closure_clm hp, LinearMap.toContinuousLinearMap.injective (hy.trans rfl)⟩
    · rintro ⟨p, hp, hy⟩
      apply (continuous_sor_instance.le_iff x.toContinuousLinearMap y.toContinuousLinearMap).mpr
      exact ⟨p.toContinuousLinearMap, closure_clm_of_closure_lm hp,
        congrArg LinearMap.toContinuousLinearMap hy⟩

end ContinuousLinearMapsAreCStarAlgebras


-- The structure of quantum channels
structure CPTP (ℋ₁ : Type u) (ℋ₂ : Type v) [Qudit ℋ₁] [Qudit ℋ₂]
  extends CompletelyPositiveMap (L ℋ₁) (L ℋ₂) where
  trace_map (ρ : L ℋ₁) : Tr ρ = Tr (toFun ρ)

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

-- def: Partial trace (1.121) https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
-- Tr₂(X) for X ∈ L(ℋ₁⊗ℋ₂)

noncomputable instance : Qudit (ℋ₁ ⊗[ℂ] ℋ₂) := by
  letI : Module.Finite ℂ (ℋ₁ ⊗[ℂ] ℋ₂) := inferInstance
  exact
    { toNormedAddCommGroup := inferInstance
      toInnerProductSpace := inferInstance
      toCompleteSpace := inferInstance
      fg_top := Module.Finite.fg_top }

noncomputable instance {κ : Type u} [Fintype κ] [DecidableEq κ] :
    Qudit (EuclideanSpace ℂ κ) := by
  letI : Module.Finite ℂ (EuclideanSpace ℂ κ) :=
    Module.Finite.of_basis (EuclideanSpace.basisFun κ ℂ).toBasis
  exact
    { toNormedAddCommGroup := inferInstance
      toInnerProductSpace := inferInstance
      toCompleteSpace := inferInstance
      fg_top := Module.Finite.fg_top }

noncomputable instance l_tensor_equiv {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂] :
  (L (ℋ₁ ⊗[ℂ] ℋ₂)) ≃ₗ[ℂ] (L ℋ₁ ⊗[ℂ] L ℋ₂) :=
  ((dualTensorHomEquiv ℂ (ℋ₁ ⊗[ℂ] ℋ₂) (ℋ₁ ⊗[ℂ] ℋ₂)).symm : LinearEquiv (RingHom.id ℂ) _ _).trans <|
  ((dualDistribEquiv ℂ ℋ₁ ℋ₂).symm.rTensor (ℋ₁ ⊗[ℂ] ℋ₂)).trans <|
  (TensorProduct.assoc ℂ (Module.Dual ℂ ℋ₁ ⊗[ℂ] Module.Dual ℂ ℋ₂) ℋ₁ ℋ₂).symm.trans <|
  ((TensorProduct.assoc ℂ (Module.Dual ℂ ℋ₁) (Module.Dual ℂ ℋ₂) ℋ₁).rTensor ℋ₂).trans <|
  (((TensorProduct.comm ℂ (Module.Dual ℂ ℋ₂) ℋ₁).lTensor (Module.Dual ℂ ℋ₁)).rTensor ℋ₂).trans <|
  ((TensorProduct.assoc ℂ (Module.Dual ℂ ℋ₁) ℋ₁ (Module.Dual ℂ ℋ₂)).symm.rTensor ℋ₂).trans <|
  (TensorProduct.assoc ℂ (Module.Dual ℂ ℋ₁ ⊗[ℂ] ℋ₁) (Module.Dual ℂ ℋ₂) ℋ₂).trans <|
  (TensorProduct.congr (dualTensorHomEquiv ℂ ℋ₁ ℋ₁) (dualTensorHomEquiv ℂ ℋ₂ ℋ₂))

-- It may be neccesary to add some lemmas to use l_tensor_equiv effectively

noncomputable def Tr₂ : T (ℋ₁ ⊗[ℂ] ℋ₂) ℋ₂ :=
  (TensorProduct.lid ℂ (L ℋ₂)).toLinearMap
  ∘ₗ (TensorProduct.map Tr LinearMap.id)
  ∘ₗ l_tensor_equiv.toLinearMap

lemma Tr₂_l_tensor_equiv_symm_tmul
    (X : L ℋ₁) (Y : L ℋ₂) :
    Tr₂ ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm (X ⊗ₜ[ℂ] Y)) = (Tr X) • Y := by
  simp [Tr₂, l_tensor_equiv]

lemma l_tensor_equiv_symm_tmul_aux
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (u : Module.Dual ℂ E ⊗[ℂ] E)
    (v : Module.Dual ℂ F ⊗[ℂ] F) :
    (l_tensor_equiv (ℋ₁ := E) (ℋ₂ := F)).symm
        ((dualTensorHom ℂ E E u) ⊗ₜ[ℂ] (dualTensorHom ℂ F F v)) =
      TensorProduct.map (dualTensorHom ℂ E E u) (dualTensorHom ℂ F F v) := by
  induction u using TensorProduct.induction_on with
  | zero =>
      simp [TensorProduct.map_zero_left]
  | tmul f p =>
      induction v using TensorProduct.induction_on with
      | zero =>
          simp [TensorProduct.map_zero_right]
      | tmul g q =>
          ext x y
          simp [l_tensor_equiv, TensorProduct.map, smul_smul]
      | add v₁ v₂ hv₁ hv₂ =>
          simp [TensorProduct.tmul_add, map_add, TensorProduct.map_add_right, hv₁, hv₂]
  | add u₁ u₂ hu₁ hu₂ =>
      simp [TensorProduct.add_tmul, map_add, TensorProduct.map_add_left, hu₁, hu₂]

lemma l_tensor_equiv_symm_tmul
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (B : L E) (C : L F) :
    (l_tensor_equiv (ℋ₁ := E) (ℋ₂ := F)).symm (B ⊗ₜ[ℂ] C) =
      TensorProduct.map B C := by
  let bE := Module.Free.chooseBasis ℂ E
  let bF := Module.Free.chooseBasis ℂ F
  let u : Module.Dual ℂ E ⊗[ℂ] E := (dualTensorHomEquivOfBasis bE).symm B
  let v : Module.Dual ℂ F ⊗[ℂ] F := (dualTensorHomEquivOfBasis bF).symm C
  have hu : dualTensorHom ℂ E E u = B := by
    simp [u]
  have hv : dualTensorHom ℂ F F v = C := by
    simp [v]
  rw [← hu, ← hv]
  exact l_tensor_equiv_symm_tmul_aux (E := E) (F := F) u v

lemma l_tensor_equiv_map_tmul
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (B : L E) (C : L F) :
    (l_tensor_equiv (ℋ₁ := E) (ℋ₂ := F)) (TensorProduct.map B C) =
      B ⊗ₜ[ℂ] C := by
  apply (l_tensor_equiv (ℋ₁ := E) (ℋ₂ := F)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (l_tensor_equiv_symm_tmul (E := E) (F := F) B C).symm

lemma Tr₂_l_tensor_equiv_symm_tmul_nonneg
    (X : L ℋ₁) (Y : L ℋ₂) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ Tr₂ ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm (X ⊗ₜ[ℂ] Y)) := by
  rw [Tr₂_l_tensor_equiv_symm_tmul]
  exact (LinearMap.nonneg_iff_isPositive _).mpr <|
    ((LinearMap.nonneg_iff_isPositive Y).mp hY).smul_of_nonneg
      ((LinearMap.nonneg_iff_isPositive X).mp hX).trace_nonneg

lemma Tr₂_sum_l_tensor_equiv_symm_tmul_nonneg
    {κ : Type u} [Fintype κ]
    (X : κ → L ℋ₁) (Y : κ → L ℋ₂)
    (hX : ∀ a, 0 ≤ X a) (hY : ∀ a, 0 ≤ Y a) :
    0 ≤ Tr₂
      (∑ a : κ,
        (l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm ((X a) ⊗ₜ[ℂ] (Y a))) := by
  rw [map_sum]
  exact Finset.sum_nonneg fun a _ =>
    Tr₂_l_tensor_equiv_symm_tmul_nonneg (X a) (Y a) (hX a) (hY a)

-- def: vec(A) (1.127) https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
-- vec[|u⟩⟨v|] := |u⟩⊗|v⟩ : (ℋ₁ →L[ℂ] ℋ₂) → ℋ₂⊗ℋ₁
noncomputable def vec (b : Module.Basis ι ℂ ℋ₂) :
  (ℋ₂ →ₗ[ℂ] ℋ₁) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂) :=
  (TensorProduct.comm ℂ ℋ₂ ℋ₁)
  ∘ₗ (TensorProduct.map b.toDualEquiv.symm.toLinearMap LinearMap.id)
  ∘ₗ (dualTensorHomEquiv ℂ ℋ₂ ℋ₁).symm.toLinearMap

noncomputable def vecLinearEquiv (b : Module.Basis ι ℂ ℋ₂) :
    (ℋ₂ →ₗ[ℂ] ℋ₁) ≃ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂) :=
  (dualTensorHomEquiv ℂ ℋ₂ ℋ₁).symm.trans <|
    (TensorProduct.congr b.toDualEquiv.symm (LinearEquiv.refl ℂ ℋ₁)).trans <|
      TensorProduct.comm ℂ ℋ₂ ℋ₁

lemma vecLinearEquiv_toLinearMap (b : Module.Basis ι ℂ ℋ₂) :
    (vecLinearEquiv (ℋ₁ := ℋ₁) b).toLinearMap = vec b := by
  ext A
  simp [vecLinearEquiv, vec, TensorProduct.congr]

-- (1.131) (1.132) https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
-- Lemma 5.12 http://www.ueltschi.org/AZschool/notes/EricCarlen.pdf
-- For any qudit ℋ, any A,B ∈ L(ℋ), and any K ∈ L(ℋ),
-- ⟨ vec[K] ∣ (A ⊗ B) vec[K] ⟩ = Tr[K† A K B.transpose]
noncomputable def l_transpose (b : Module.Basis ι ℂ ℋ₁)
  (A : L ℋ₁) : L ℋ₁ :=
  b.toDualEquiv.symm.toLinearMap ∘ₗ A.dualMap ∘ₗ b.toDualEquiv.toLinearMap

lemma dualTensorHom_map
    {R : Type*} [CommSemiring R]
    {M M' N N' : Type*}
    [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N] [AddCommMonoid N']
    [Module R M] [Module R M'] [Module R N] [Module R N']
    (f : M' →ₗ[R] M) (g : N →ₗ[R] N')
    (x : (Module.Dual R M) ⊗[R] N) :
    (dualTensorHom R M' N') (TensorProduct.map f.dualMap g x)
      = g ∘ₗ (dualTensorHom R M N x) ∘ₗ f := by
  refine TensorProduct.induction_on x ?h0 ?htmul ?hadd
  · simp
  · intro φ n
    -- 両辺とも線形写像なので ext で点ごとに見る
    ext m'
    -- `map_tmul`, `dualTensorHom_apply`, `dualMap_apply` を simp で畳む
    simp [dualTensorHom_apply]
  · intro x y hx hy
    simp only [map_add, hx, hy]
    ext _
    simp

lemma dualTensorHomEquiv_symm_map
    {R : Type*} [CommSemiring R]
    {M M' N N' : Type*}
    [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N] [AddCommMonoid N']
    [Module R M] [Module R M'] [Module R N] [Module R N']
    [Module.Free R M] [Module.Finite R M]
    [Module.Free R M'] [Module.Finite R M']
    (f : M' →ₗ[R] M) (g : N →ₗ[R] N')
    (K : M →ₗ[R] N) :
    TensorProduct.map f.dualMap g ((dualTensorHomEquiv R M N).symm K)
      = (dualTensorHomEquiv R M' N').symm (g ∘ₗ K ∘ₗ f) := by
  -- `dualTensorHomEquiv` は線形同型なので injective で Hom 側に落とす
  apply (dualTensorHomEquiv R M' N').injective
  -- `dualTensorHomEquiv` の forward は `dualTensorHom` なので、上の lemma で終わる
  simpa [dualTensorHomEquiv] using
    (dualTensorHom_map (R := R) (M := M) (M' := M') (N := N) (N' := N') f g
      ((dualTensorHomEquiv R M N).symm K))

set_option linter.unusedFintypeInType false in
lemma dual_comm {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] [Module.Free R M]
    (b : Module.Basis ι R M) (x y : M) :
  (b.toDual x) y = (b.toDual y) x := by
  rw [←(Module.Basis.sum_equivFun b x)]
  rw [map_sum, map_sum, LinearMap.sum_apply]
  congr
  ext i
  rw [map_smul, map_smul, LinearMap.smul_apply]
  congr 1
  rw [←(Module.Basis.sum_equivFun b y)]
  rw [map_sum, map_sum, LinearMap.sum_apply]
  congr
  ext j
  rw [map_smul, map_smul, LinearMap.smul_apply]
  congr 1
  rw [b.toDual_apply, b.toDual_apply]
  congr 1
  exact Eq.propIntro (fun a ↦ id (Eq.symm a)) fun a ↦ id (Eq.symm a)

set_option linter.unusedFintypeInType false in
lemma dual_symm_comm {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] [Module.Free R M]
    (b : Module.Basis ι R M) (x y : Module.Dual R M) :
  x (b.toDualEquiv.symm y) = y (b.toDualEquiv.symm x) := by
  nth_rw 1 [(by simp : x = b.toDualEquiv (b.toDualEquiv.symm x))]
  nth_rw 2 [(by simp : y = b.toDualEquiv (b.toDualEquiv.symm y))]
  rw [b.toDualEquiv_apply]
  apply dual_comm

lemma comp_dual_equiv_symm_eq (b : Module.Basis ι ℂ ℋ₂)
  (B : L ℋ₂) : B ∘ₗ b.toDualEquiv.symm.toLinearMap
    = ((Module.evalEquiv ℂ ℋ₂).symm.toLinearMap ∘ₗ
      ((l_transpose b B) ∘ₗ b.toDualEquiv.symm.toLinearMap).dualMap) := by
  ext x
  dsimp only [l_transpose]
  apply (Module.evalEquiv ℂ ℋ₂).injective
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Module.evalEquiv_apply,
    LinearEquiv.apply_symm_apply]
  ext y
  simp only [Module.Dual.eval_apply, LinearMap.dualMap_apply',
    LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.apply_symm_apply]
  have hxy := dual_symm_comm b (y ∘ₗ B) x
  simpa using hxy

set_option linter.unusedFintypeInType false in
lemma dual_equiv_symm_eq (b : Module.Basis ι ℂ ℋ₂)
  : b.toDualEquiv.symm.toLinearMap
    = ((Module.evalEquiv ℂ ℋ₂).symm.toLinearMap ∘ₗ (b.toDualEquiv.symm.toLinearMap).dualMap) := by
  let := comp_dual_equiv_symm_eq b (I ℋ₂)
  simp only [LinearMap.id_comp, l_transpose, LinearMap.dualMap_id, LinearEquiv.comp_coe,
    LinearEquiv.self_trans_symm,
    LinearEquiv.refl_toLinearMap] at this
  exact this

lemma map_vec_eq_vec (b : Module.Basis ι ℂ ℋ₂)
  (A : L ℋ₁) (B : L ℋ₂) (K : ℋ₂ →ₗ[ℂ] ℋ₁) :
  (TensorProduct.map A B) (vec b K) = vec b (A ∘ₗ K ∘ₗ (l_transpose b B)) := by
  simp only [vec, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [map_comm]
  congr 1
  rw [map_map]
  simp only [LinearMap.comp_id]
  nth_rw 2 [dual_equiv_symm_eq]
  rw [(by simp : LinearMap.id = LinearMap.id ∘ₗ LinearMap.id), map_comp]
  rw [comp_dual_equiv_symm_eq]
  rw [(by simp : A = LinearMap.id ∘ₗ A), map_comp]
  simp only [LinearMap.coe_comp, Function.comp_apply]
  congr 1
  rw [dualTensorHomEquiv_symm_map, dualTensorHomEquiv_symm_map]
  rfl

lemma vec_apply (b : Module.Basis ι ℂ ℋ₂)
  (C : ℋ₂ →ₗ[ℂ] ℋ₁) :
  vec b C = ∑ i : ι, (C (b i)) ⊗ₜ[ℂ] (b i) := by
  have h : dualTensorHomEquivOfBasis b = dualTensorHomEquiv ℂ ℋ₂ ℋ₁ := by
    exact LinearEquiv.toLinearMap_inj.mp rfl
  rw [vec, ←h]
  simp only [dualTensorHomEquivOfBasis, LinearEquiv.ofLinear, Module.Basis.coe_dualBasis,
    LinearMap.coe_sum, LinearMap.coe_comp, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_symm_mk', Finset.sum_apply,
    Function.comp_apply, LinearMap.applyₗ_apply_apply, mk_apply, map_sum,
    map_tmul, LinearMap.id_coe, id_eq, comm_tmul]
  congr
  ext i
  congr
  have h : b.toDualEquiv (b i) = b.coord i := by
    simpa [Module.Basis.toDualEquiv_apply] using (Module.Basis.coe_toDual_self (b := b) i)
  rw [←h]
  exact LinearEquiv.symm_apply_apply b.toDualEquiv (b i)

lemma inner_vec_eq_trace
  (b : OrthonormalBasis ι ℂ ℋ₂)
  (A B : ℋ₂ →ₗ[ℂ] ℋ₁) :
  inner ℂ (vec b.toBasis A) (vec b.toBasis B) = Tr (A† ∘ₗ B) := by
  calc
    inner ℂ (vec b.toBasis A) (vec b.toBasis B)
        = ∑ i : ι, inner ℂ (A (b i)) (B (b i)) := by
      simp [vec_apply, inner_sum, sum_inner, b.inner_eq_ite]
    _ = ∑ i : ι, inner ℂ (b i) ((A† ∘ₗ B) (b i)) := by
      simp [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
    _ = ∑ i : ι, b.toBasis.coord i ((A† ∘ₗ B) (b i)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hcoord : b.toBasis.coord i = (innerSL ℂ (b i)).toLinearMap := by
        ext j
        simp [b.repr_apply_apply]
      simp [hcoord]
    _ = Tr (A† ∘ₗ B) := by
      simp [Tr, LinearMap.trace_eq_matrix_trace (b := b.toBasis) (f := A† ∘ₗ B),
        Matrix.trace, LinearMap.toMatrix_apply]

lemma ando_identity (b : OrthonormalBasis ι ℂ ℋ₂)
  (A : L ℋ₁) (B : L ℋ₂) (K : ℋ₂ →ₗ[ℂ] ℋ₁) :
  inner ℂ (vec b.toBasis K) ((TensorProduct.map A B) (vec b.toBasis K))
    = Tr (K† ∘ₗ A ∘ₗ K ∘ₗ (l_transpose b.toBasis B)) := by
  rw [map_vec_eq_vec]
  apply inner_vec_eq_trace

-- def: Choi operator (2.64) https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- J(Φ) := (Φ⊗id)(vec[I(ℋ₂⊗ℋ₁)] vec[I(ℋ₂⊗ℋ₁)]†) for Φ ∈ T(ℋ₁,ℋ₂)

-- (1.57) in https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
noncomputable def outer_product
  (u : ℋ₁) (v : ℋ₂) : ℋ₁ →ₗ[ℂ] ℋ₂ :=
  (dualTensorHomEquiv ℂ ℋ₁ ℋ₂).toLinearMap <|
    ((InnerProductSpace.toDualMap ℂ ℋ₁ u) ⊗ₜ[ℂ] v)

lemma outer_product_eq_rankOne
    (u : ℋ₁) (v : ℋ₂) :
    outer_product u v = (InnerProductSpace.rankOne ℂ v u).toLinearMap := by
  ext x
  simp [outer_product, dualTensorHom_apply]

lemma outer_product_self_nonneg
    (u : ℋ₁) :
    0 ≤ outer_product u u := by
  rw [outer_product_eq_rankOne]
  have hcont : (InnerProductSpace.rankOne ℂ u u).IsPositive :=
    InnerProductSpace.isPositive_rankOne_self (𝕜 := ℂ) u
  exact (LinearMap.nonneg_iff_isPositive _).mpr <|
    (LinearMap.isPositive_toContinuousLinearMap_iff _).mp hcont

lemma outer_product_sum
    {κ : Type*} [Fintype κ]
    (x y : κ → ℋ₁) :
    outer_product (∑ a : κ, x a) (∑ a : κ, y a) =
      ∑ a : κ, ∑ b : κ, outer_product (x a) (y b) := by
  ext z
  simp [outer_product_eq_rankOne]

lemma Tr₂_simple_outer_product_sum_nonneg
    {κ : Type u} [Fintype κ]
    (x : κ → ℋ₁) (y : κ → ℋ₂) :
    0 ≤ Tr₂
      (∑ a : κ,
        (l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm
          ((outer_product (x a) (x a)) ⊗ₜ[ℂ] (outer_product (y a) (y a)))) := by
  exact Tr₂_sum_l_tensor_equiv_symm_tmul_nonneg
    (fun a => outer_product (x a) (x a))
    (fun a => outer_product (y a) (y a))
    (fun a => outer_product_self_nonneg (x a))
    (fun a => outer_product_self_nonneg (y a))

noncomputable def choi (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) : L (ℋ₂ ⊗[ℂ] ℋ₁) :=
  (l_tensor_equiv.symm.toLinearMap
  ∘ₗ (TensorProduct.map Φ LinearMap.id)
  ∘ₗ l_tensor_equiv.toLinearMap) (outer_product (vec b (I ℋ₁)) (vec b (I ℋ₁)))

end Definition

section RepresentationsOfChannels

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]

-- Proposition 2.17 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudit ℋ, and any P ∈ Pos(ℋ),
-- the map Φ(α):=αP ∈ T(ℂ,ℋ) is a completely positive ContinuourLinearMap.

-- Proposition 2.18 and its remark https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudits ℋ₁, ℋ₂, and any Φ ∈ T(ℋ₁,ℋ₂),
-- if Φ is a completely positive ContinuourLinearMap,
-- the adjoint map of Φ is a completely positive ContinuourLinearMap.

-- Corollary 2.19 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudit ℋ, Tr ∈ T(ℋ,ℂ) is a completely positive ContinuourLinearMap.

-- Proposition 2.20 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudits ℋ₁, ℋ₂, and any Φ ∈ T(ℋ₁,ℋ₂),
-- J(Φ)=∑_{a∈Σ} vec(Aₐ) vec(Bₐ)†
-- if and only if
-- for ℋ₃=ℂ^Σ, A,B∈(ℋ₁→L[ℂ]ℋ₂⊗ℋ₃) defined as
-- A=∑_{a∈Σ}Aₐ⊗eₐ,
-- B=∑_{a∈Σ}Aₐ⊗eₐ,
-- it holds for all X∈L(X) that
-- Φ(X)=Tr₃[Aₐ X Bₐ†]

-- Theorem 2.22 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudits ℋ₁, ℋ₂, and any Φ ∈ T(ℋ₁,ℋ₂), the following statements are equivalent:
-- 1: Φ is a completely positive ContinuosLinearMap;
-- 2: J(Φ) ∈ Pos(ℋ₂⊗ℋ₁);
-- 3: ∃qudit ℋ₃, ∃A∈(ℋ₁→L[ℂ]ℋ₂⊗ℋ₃), Φ(X)=Tr₃[A X A†]

theorem isCompletelyPositive_iff_cstarMatrix_nonneg
    (Φ : T ℋ₁ ℋ₂) :
    (∃ Ψ : CompletelyPositiveMap (L ℋ₁) (L ℋ₂), Ψ.toLinearMap = Φ) ↔
      ∀ (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) (L ℋ₁)),
        0 ≤ M → 0 ≤ M.map Φ := by
  constructor
  · rintro ⟨Ψ, rfl⟩ k M hM
    exact Ψ.map_cstarMatrix_nonneg' k M hM
  · intro hΦ
    exact ⟨{ Φ with map_cstarMatrix_nonneg' := hΦ }, rfl⟩

theorem card_nonzero_eigenvalues_eq_finrank_range
    {E : Type u} [Qudit E] (T : L E) (hT : 0 ≤ T) :
    let n := Module.finrank ℂ E
    let hSym : T.IsSymmetric := (LinearMap.nonneg_iff_isPositive T).mp hT |>.isSymmetric
    Fintype.card { i : Fin n // hSym.eigenvalues rfl i ≠ 0 } =
      Module.finrank ℂ (LinearMap.range T) := by
  classical
  dsimp
  let n := Module.finrank ℂ E
  let hSym : T.IsSymmetric := (LinearMap.nonneg_iff_isPositive T).mp hT |>.isSymmetric
  have hzero :
      Fintype.card { i : Fin n // hSym.eigenvalues rfl i = 0 } =
        Module.finrank ℂ (LinearMap.ker T) := by
    have hzero' := hSym.card_filter_eigenvalues_eq (hn := rfl) (μ := (0 : ℝ))
    have hker :
        Module.finrank ℂ (Module.End.eigenspace T 0) = Module.finrank ℂ (LinearMap.ker T) := by
      simpa using congrArg (fun S : Submodule ℂ E => Module.finrank ℂ S)
        (Module.End.eigenspace_zero (R := ℂ) T)
    simpa [Fintype.card_subtype] using hzero'.trans hker
  have hcard :
      Fintype.card { i : Fin n // hSym.eigenvalues rfl i ≠ 0 } =
        n - Module.finrank ℂ (LinearMap.ker T) := by
    rw [Fintype.card_subtype_compl]
    simp [n, hzero]
  rw [hcard]
  exact by
    simp [n, (Nat.eq_sub_of_add_eq (LinearMap.finrank_range_add_finrank_ker T)).symm]

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

def IsPositiveMap (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∀ X : L ℋ₁, 0 ≤ X → 0 ≤ Φ X

def IsKPositive (k : ℕ) (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∀ M : CStarMatrix (Fin k) (Fin k) (L ℋ₁), 0 ≤ M → 0 ≤ M.map Φ

noncomputable def amplifyWithId (Φ : T ℋ₁ ℋ₂) : T (ℋ₁ ⊗[ℂ] ℋ₁) (ℋ₂ ⊗[ℂ] ℋ₁) :=
  l_tensor_equiv.symm.toLinearMap
    ∘ₗ (TensorProduct.map Φ LinearMap.id)
    ∘ₗ l_tensor_equiv.toLinearMap

def IsCompletelyPositive (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∃ Ψ : CompletelyPositiveMap (L ℋ₁) (L ℋ₂), Ψ.toLinearMap = Φ

abbrev DS (k : ℕ) (ℋ : Type u) := PiLp 2 (fun _ : Fin k => ℋ)

noncomputable instance dsFiniteDimensional (k : ℕ) (ℋ : Type u) [Qudit ℋ] :
    FiniteDimensional ℂ (DS k ℋ) :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm.toLinearEquiv).finiteDimensional

noncomputable instance dsQudit (k : ℕ) (ℋ : Type u) [Qudit ℋ] : Qudit (DS k ℋ) where
  toNormedAddCommGroup := inferInstance
  toInnerProductSpace := inferInstance
  toCompleteSpace := inferInstance
  fg_top := by
    letI : Module.Finite ℂ (DS k ℋ) := dsFiniteDimensional k ℋ
    simpa using (Module.Finite.fg_top (R := ℂ) (M := DS k ℋ))

noncomputable def ampPlainEquiv (k : ℕ) (ℋ : Type u) [Qudit ℋ] :
    L (DS k ℋ) ≃ₐ[ℂ] Matrix (Fin k) (Fin k) (L ℋ) :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).toLinearEquiv.conjAlgEquiv ℂ).trans
    (endVecAlgEquivMatrixEnd (ι := Fin k) (R := ℂ) (A := ℂ) (M := ℋ))

lemma ampPlainEquiv_apply_apply
    (k : ℕ) (ℋ : Type u) [Qudit ℋ]
    (f : L (DS k ℋ)) (i j : Fin k) (x : ℋ) :
    ampPlainEquiv k ℋ f i j x =
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ))
        (f (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm) (Pi.single j x))) i := by
  rfl

lemma inner_symm_single
    (k : ℕ) (ℋ : Type u) [Qudit ℋ]
    (v : DS k ℋ) (i : Fin k) (x : ℋ) :
    inner ℂ v (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm) (Pi.single i x)) =
      inner ℂ (v i) x := by
  rw [PiLp.inner_apply]
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    simp at hi

lemma inner_single_symm
    (k : ℕ) (ℋ : Type u) [Qudit ℋ]
    (i : Fin k) (x : ℋ) (v : DS k ℋ) :
    inner ℂ (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm) (Pi.single i x)) v =
      inner ℂ x (v i) := by
  rw [PiLp.inner_apply]
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    simp at hi

lemma inner_coord_right
    (k : ℕ) (ℋ : Type u) [Qudit ℋ]
    (z : DS k ℋ) (i : Fin k) (y : ℋ) :
    inner ℂ ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)) z i) y =
      inner ℂ z (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm) (Pi.single i y)) := by
  simpa using (inner_symm_single (k := k) (ℋ := ℋ) (v := z) (i := i) (x := y)).symm

lemma inner_coord_left
    (k : ℕ) (ℋ : Type u) [Qudit ℋ]
    (i : Fin k) (x : ℋ) (z : DS k ℋ) :
    inner ℂ x ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)) z i) =
      inner ℂ (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm) (Pi.single i x)) z := by
  simpa using (inner_single_symm (k := k) (ℋ := ℋ) (i := i) (x := x) (v := z)).symm

lemma ampPlainEquiv_map_star
    (k : ℕ) (ℋ : Type u) [Qudit ℋ]
    (f : L (DS k ℋ)) :
    ampPlainEquiv k ℋ (star f) = star (ampPlainEquiv k ℋ f) := by
  ext i j x
  apply ext_inner_right ℂ
  intro y
  rw [ampPlainEquiv_apply_apply, Matrix.star_apply]
  have hstar :
      inner ℂ ((star ((ampPlainEquiv k ℋ) f j i)) x) y =
        inner ℂ x ((ampPlainEquiv k ℋ f j i) y) := by
    change inner ℂ (((ampPlainEquiv k ℋ f j i)†) x) y =
      inner ℂ x ((ampPlainEquiv k ℋ f j i) y)
    simpa using
      (LinearMap.adjoint_inner_left (A := ampPlainEquiv k ℋ f j i) (x := y) (y := x))
  rw [hstar, ampPlainEquiv_apply_apply, inner_coord_right, inner_coord_left]
  simpa using
    (LinearMap.adjoint_inner_left
      (A := f)
      (x := ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm (Pi.single i y)))
      (y := ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm (Pi.single j x))))

noncomputable def ampMatrixStarAlgEquiv (k : ℕ) (ℋ : Type u) [Qudit ℋ] :
    L (DS k ℋ) ≃⋆ₐ[ℂ] Matrix (Fin k) (Fin k) (L ℋ) :=
  StarAlgEquiv.ofAlgEquiv (ampPlainEquiv k ℋ) (ampPlainEquiv_map_star (k := k) (ℋ := ℋ))

noncomputable def ampCStarEquiv (k : ℕ) (ℋ : Type u) [Qudit ℋ] :
    L (DS k ℋ) ≃⋆ₐ[ℂ] CStarMatrix (Fin k) (Fin k) (L ℋ) :=
  (ampMatrixStarAlgEquiv k ℋ).trans CStarMatrix.ofMatrixStarAlgEquiv

noncomputable def ampSuper
    (k : ℕ) (Φ : T ℋ₁ ℋ₂) : T (DS k ℋ₁) (DS k ℋ₂) :=
  (ampCStarEquiv k ℋ₂).symm.toAlgEquiv.toLinearMap ∘ₗ
    (CStarMatrix.mapₗ Φ) ∘ₗ
      (ampCStarEquiv k ℋ₁).toAlgEquiv.toLinearMap

lemma ampCStarEquiv_ampSuper_apply
    (k : ℕ) (Φ : T ℋ₁ ℋ₂) (A : L (DS k ℋ₁)) :
    ampCStarEquiv k ℋ₂ (ampSuper k Φ A) = (ampCStarEquiv k ℋ₁ A).map Φ := by
  change
    ampCStarEquiv k ℋ₂
      ((ampCStarEquiv k ℋ₂).symm (((ampCStarEquiv k ℋ₁) A).map Φ)) =
        ((ampCStarEquiv k ℋ₁) A).map Φ
  exact (ampCStarEquiv k ℋ₂).apply_symm_apply _

lemma starAlgEquiv_mem_nonnegClosure
    {A B : Type*}
    [Semiring A] [StarRing A] [Algebra ℂ A] [PartialOrder A] [StarOrderedRing A]
    [Semiring B] [StarRing B] [Algebra ℂ B] [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) {x : A}
    (hx : x ∈ AddSubmonoid.closure (Set.range fun s : A => star s * s)) :
    e x ∈ AddSubmonoid.closure (Set.range fun t : B => star t * t) := by
  induction hx using AddSubmonoid.closure_induction with
  | mem y hy =>
      obtain ⟨s, rfl⟩ := hy
      refine AddSubmonoid.subset_closure ⟨e s, ?_⟩
      simpa using congrArg (fun z => z * e s) (map_star e s).symm
  | zero =>
      rw [map_zero]
      exact AddSubmonoid.zero_mem (AddSubmonoid.closure (Set.range fun t : B => star t * t))
  | add y z _ _ ihy ihz =>
      rw [map_add]
      exact AddSubmonoid.add_mem (AddSubmonoid.closure (Set.range fun t : B => star t * t)) ihy ihz

lemma starAlgEquiv_nonneg
    {A B : Type*}
    [Semiring A] [StarRing A] [Algebra ℂ A] [PartialOrder A] [StarOrderedRing A]
    [Semiring B] [StarRing B] [Algebra ℂ B] [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) {x : A} (hx : 0 ≤ x) :
    0 ≤ e x := by
  refine StarOrderedRing.nonneg_iff.mpr ?_
  exact starAlgEquiv_mem_nonnegClosure e (StarOrderedRing.nonneg_iff.mp hx)

lemma starAlgEquiv_nonneg_iff
    {A B : Type*}
    [Semiring A] [StarRing A] [Algebra ℂ A] [PartialOrder A] [StarOrderedRing A]
    [Semiring B] [StarRing B] [Algebra ℂ B] [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) {x : A} :
    0 ≤ e x ↔ 0 ≤ x := by
  constructor
  · intro hx
    simpa using starAlgEquiv_nonneg e.symm hx
  · intro hx
    exact starAlgEquiv_nonneg e hx

lemma isKPositive_iff_isPositiveMap_ampSuper
    (k : ℕ) (Φ : T ℋ₁ ℋ₂) :
    IsKPositive k Φ ↔ IsPositiveMap (ampSuper k Φ) := by
  constructor
  · intro hΦ A hA
    have hAmap :
        0 ≤ ampCStarEquiv k ℋ₁ A := starAlgEquiv_nonneg (ampCStarEquiv k ℋ₁) hA
    have hMap :
        0 ≤ ampCStarEquiv k ℋ₂ (ampSuper k Φ A) := by
      rw [ampCStarEquiv_ampSuper_apply]
      exact hΦ _ hAmap
    exact (starAlgEquiv_nonneg_iff (ampCStarEquiv k ℋ₂)).1 hMap
  · intro hΦ M hM
    let A : L (DS k ℋ₁) := (ampCStarEquiv k ℋ₁).symm M
    have hMA : ampCStarEquiv k ℋ₁ A = M := by
      simp [A]
    have hA : 0 ≤ A := by
      have hM' : 0 ≤ ampCStarEquiv k ℋ₁ A := by simpa [hMA] using hM
      exact (starAlgEquiv_nonneg_iff (ampCStarEquiv k ℋ₁)).1 hM'
    have hAmp : 0 ≤ ampSuper k Φ A := hΦ A hA
    have hMap : 0 ≤ ampCStarEquiv k ℋ₂ (ampSuper k Φ A) :=
      starAlgEquiv_nonneg (ampCStarEquiv k ℋ₂) hAmp
    have hEq :
        ampCStarEquiv k ℋ₂ (ampSuper k Φ A) = (ampCStarEquiv k ℋ₁ A).map Φ :=
      ampCStarEquiv_ampSuper_apply (k := k) (Φ := Φ) (A := A)
    simpa [hEq, hMA] using hMap

theorem completelyPositive_to_positiveMap
    (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → IsPositiveMap Φ := by
  rintro ⟨Ψ, rfl⟩ X hX
  exact map_nonneg Ψ hX

lemma conjugate_positive
    {ℋ₃ : Type w} [Qudit ℋ₃]
    (A : ℋ₁ →ₗ[ℂ] ℋ₃) :
    IsPositiveMap
      { toFun := fun X => A.comp (X.comp (LinearMap.adjoint A))
        map_add' := by
          intro X Y
          ext x
          simp
        map_smul' := by
          intro c X
          ext x
          simp } := by
  intro X hX
  exact (LinearMap.nonneg_iff_isPositive _).mpr <|
    (LinearMap.nonneg_iff_isPositive X).mp hX |>.conj_adjoint A

lemma comp_outer_product_adjoint
    {ℋ₃ : Type w} [Qudit ℋ₃]
    (A : ℋ₁ →ₗ[ℂ] ℋ₃) (u v : ℋ₁) :
    A.comp ((outer_product u v).comp (LinearMap.adjoint A)) =
      outer_product (A u) (A v) := by
  ext y
  simp [outer_product_eq_rankOne, LinearMap.adjoint_inner_right]

noncomputable def krausTerm
    (V : ℋ₁ →ₗ[ℂ] ℋ₂) : T ℋ₁ ℋ₂ where
  toFun := fun A => V ∘ₗ A ∘ₗ V†
  map_add' := by
    intro A B
    ext x
    simp [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' := by
    intro c A
    ext x
    simp [LinearMap.smul_comp, LinearMap.comp_smul]

lemma krausTerm_isPositiveMap
    (V : ℋ₁ →ₗ[ℂ] ℋ₂) :
    IsPositiveMap (krausTerm V) := by
  intro A hA
  have hAclm : A.toContinuousLinearMap.IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).1 (by simpa using hA)
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).2 <| by
    simpa [krausTerm, LinearMap.comp_assoc, LinearMap.star_eq_adjoint,
      ContinuousLinearMap.coe_comp] using hAclm.conj_adjoint V.toContinuousLinearMap

noncomputable def dsEquiv (k : ℕ) (ℋ : Type*) [Qudit ℋ] :
    DS k ℋ ≃L[ℂ] (Fin k → ℋ) :=
  PiLp.continuousLinearEquiv (p := (2 : ENNReal)) (𝕜 := ℂ) (β := fun _ : Fin k => ℋ)

noncomputable def dsProj (k : ℕ) (ℋ : Type*) [Qudit ℋ] (i : Fin k) :
    DS k ℋ →L[ℂ] ℋ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℋ) i) ∘L
    (dsEquiv k ℋ).toContinuousLinearMap

noncomputable def dsIncl (k : ℕ) (ℋ : Type*) [Qudit ℋ] (i : Fin k) :
    ℋ →L[ℂ] DS k ℋ :=
  (dsEquiv k ℋ).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.single ℂ (fun _ : Fin k => ℋ) i)

lemma dsProj_dsIncl_apply
    (k : ℕ) (ℋ : Type*) [Qudit ℋ] (i j : Fin k) (x : ℋ) :
    dsProj k ℋ i (dsIncl k ℋ j x) = if i = j then x else 0 := by
  by_cases h : i = j
  · subst h
    simp [dsProj, dsIncl, dsEquiv]
  · simp [dsProj, dsIncl, dsEquiv, h]

lemma dsIncl_adjoint
    (k : ℕ) (ℋ : Type*) [Qudit ℋ] (i : Fin k) :
    (dsIncl k ℋ i).adjoint = dsProj k ℋ i := by
  apply ContinuousLinearMap.ext
  intro x
  refine ext_inner_right ℂ fun y => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  simpa [dsProj, dsIncl, dsEquiv] using
    (inner_symm_single (k := k) (ℋ := ℋ) (v := x) (i := i) (x := y))

lemma dsProj_adjoint
    (k : ℕ) (ℋ : Type*) [Qudit ℋ] (i : Fin k) :
    (dsProj k ℋ i).adjoint = dsIncl k ℋ i := by
  calc
    (dsProj k ℋ i).adjoint = ((dsIncl k ℋ i).adjoint).adjoint := by rw [dsIncl_adjoint]
    _ = dsIncl k ℋ i := ContinuousLinearMap.adjoint_adjoint _

noncomputable def ampKrausFactorCLM
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) : DS k ℋ₁ →L[ℂ] DS k ℋ₂ :=
  ∑ i : Fin k, ((dsIncl k ℋ₂ i).comp V.toContinuousLinearMap).comp (dsProj k ℋ₁ i)

noncomputable def ampKrausFactor
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) : DS k ℋ₁ →ₗ[ℂ] DS k ℋ₂ :=
  (ampKrausFactorCLM k V).toLinearMap

lemma dsProj_ampKrausFactorCLM
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) (i : Fin k) (x : DS k ℋ₁) :
    dsProj k ℋ₂ i (ampKrausFactorCLM k V x) = V (dsProj k ℋ₁ i x) := by
  classical
  simp [ampKrausFactorCLM, Finset.sum_apply, dsProj_dsIncl_apply]

lemma ampKrausFactorCLM_dsIncl
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) (i : Fin k) (x : ℋ₁) :
    ampKrausFactorCLM k V (dsIncl k ℋ₁ i x) = dsIncl k ℋ₂ i (V x) := by
  apply (dsEquiv k ℋ₂).injective
  ext j
  have h :=
    dsProj_ampKrausFactorCLM (k := k) (V := V) (i := j) (x := dsIncl k ℋ₁ i x)
  by_cases hji : j = i
  · subst hji
    simpa [dsProj, dsIncl, dsEquiv] using h
  · simpa [dsProj, dsIncl, dsEquiv, hji] using h

lemma ampKrausFactorCLM_adjoint_dsIncl
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) (i : Fin k) (x : ℋ₂) :
    (ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x) = dsIncl k ℋ₁ i (V.adjoint x) := by
  classical
  apply (dsEquiv k ℋ₁).injective
  ext j
  apply ext_inner_right ℂ
  intro y
  rw [show
      inner ℂ
          ((dsEquiv k ℋ₁) ((ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x)) j) y =
        inner ℂ
          (dsProj k ℋ₁ j ((ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x))) y by
      rfl]
  rw [show
      inner ℂ ((dsEquiv k ℋ₁) (dsIncl k ℋ₁ i (V.adjoint x)) j) y =
        inner ℂ (dsProj k ℋ₁ j (dsIncl k ℋ₁ i (V.adjoint x))) y by
      rfl]
  by_cases hji : j = i
  · subst j
    calc
      inner ℂ
          (dsProj k ℋ₁ i ((ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x))) y =
        inner ℂ ((ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x))
          (dsIncl k ℋ₁ i y) := by
          simpa [dsIncl_adjoint] using
            (ContinuousLinearMap.adjoint_inner_left
              (A := dsIncl k ℋ₁ i)
              (x := y)
              (y := (ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x)))
      _ = inner ℂ (dsIncl k ℋ₂ i x)
          (ampKrausFactorCLM k V (dsIncl k ℋ₁ i y)) := by
          exact ContinuousLinearMap.adjoint_inner_left
            (A := ampKrausFactorCLM k V)
            (x := dsIncl k ℋ₁ i y)
            (y := dsIncl k ℋ₂ i x)
      _ = inner ℂ (dsIncl k ℋ₂ i x) (dsIncl k ℋ₂ i (V y)) := by
          rw [ampKrausFactorCLM_dsIncl]
      _ = inner ℂ (V.adjoint x) y := by
          rw [← ContinuousLinearMap.adjoint_inner_right
            (A := dsIncl k ℋ₂ i)
            (x := x)
            (y := dsIncl k ℋ₂ i (V y))]
          simp [dsIncl_adjoint, dsProj_dsIncl_apply,
            LinearMap.adjoint_inner_left]
      _ = inner ℂ (dsProj k ℋ₁ i (dsIncl k ℋ₁ i (V.adjoint x))) y := by
          simp [dsProj_dsIncl_apply]
  · calc
      inner ℂ
          (dsProj k ℋ₁ j ((ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x))) y =
        inner ℂ ((ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x))
          (dsIncl k ℋ₁ j y) := by
          simpa [dsIncl_adjoint] using
            (ContinuousLinearMap.adjoint_inner_left
              (A := dsIncl k ℋ₁ j)
              (x := y)
              (y := (ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x)))
      _ = inner ℂ (dsIncl k ℋ₂ i x)
          (ampKrausFactorCLM k V (dsIncl k ℋ₁ j y)) := by
          exact ContinuousLinearMap.adjoint_inner_left
            (A := ampKrausFactorCLM k V)
            (x := dsIncl k ℋ₁ j y)
            (y := dsIncl k ℋ₂ i x)
      _ = inner ℂ (dsIncl k ℋ₂ i x) (dsIncl k ℋ₂ j (V y)) := by
          rw [ampKrausFactorCLM_dsIncl]
      _ = 0 := by
          rw [← ContinuousLinearMap.adjoint_inner_right
            (A := dsIncl k ℋ₂ i)
            (x := x)
            (y := dsIncl k ℋ₂ j (V y))]
          have hij : i ≠ j := fun hij => hji hij.symm
          simp [dsIncl_adjoint, dsProj_dsIncl_apply, hij]
      _ = inner ℂ (dsProj k ℋ₁ j (dsIncl k ℋ₁ i (V.adjoint x))) y := by
          simp [dsProj_dsIncl_apply, hji]

lemma ampKrausFactor_adjoint_dsIncl
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) (i : Fin k) (x : ℋ₂) :
    ((ampKrausFactor k V)†) (dsIncl k ℋ₂ i x) = dsIncl k ℋ₁ i (V.adjoint x) := by
  change (ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x) = dsIncl k ℋ₁ i (V.adjoint x)
  exact ampKrausFactorCLM_adjoint_dsIncl (k := k) (V := V) (i := i) (x := x)

lemma dsProj_ampKrausFactor
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) (i : Fin k) (x : DS k ℋ₁) :
    dsProj k ℋ₂ i (ampKrausFactor k V x) = V (dsProj k ℋ₁ i x) := by
  exact dsProj_ampKrausFactorCLM (k := k) (V := V) (i := i) (x := x)

lemma ampKrausFactor_dsIncl
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) (i : Fin k) (x : ℋ₁) :
    ampKrausFactor k V (dsIncl k ℋ₁ i x) = dsIncl k ℋ₂ i (V x) := by
  exact ampKrausFactorCLM_dsIncl (k := k) (V := V) (i := i) (x := x)

lemma ampPlainEquiv_apply_apply_ds
    (k : ℕ) (ℋ : Type*) [Qudit ℋ]
    (f : L (DS k ℋ)) (i j : Fin k) (x : ℋ) :
    ampPlainEquiv k ℋ f i j x = dsProj k ℋ i (f (dsIncl k ℋ j x)) := by
  simpa [dsProj, dsIncl, dsEquiv] using
    (ampPlainEquiv_apply_apply (k := k) (ℋ := ℋ) (f := f) (i := i) (j := j) (x := x))

lemma ampPlainEquiv_symm_apply_apply
    (k : ℕ) (ℋ : Type*) [Qudit ℋ]
    (N : CStarMatrix (Fin k) (Fin k) (L ℋ))
    (i j : Fin k) (x : ℋ) :
    ampPlainEquiv k ℋ ((ampCStarEquiv k ℋ).symm N) i j x = N i j x := by
  simp [ampCStarEquiv, ampMatrixStarAlgEquiv, ampPlainEquiv]
  rfl

noncomputable def linearToContinuousEndStarAlgEquiv
    (ℋ : Type*) [Qudit ℋ] :
    L ℋ ≃⋆ₐ[ℂ] (ℋ →L[ℂ] ℋ) where
  toFun := LinearMap.toContinuousLinearMap
  invFun := ContinuousLinearMap.toLinearMap
  left_inv := by intro A; rfl
  right_inv := by intro A; ext x; rfl
  map_mul' := by intro A B; rfl
  map_add' := by intro A B; rfl
  map_smul' := by intro c A; rfl
  map_star' := by
    intro A
    simpa using (LinearMap.adjoint_toContinuousLinearMap (A := A))

noncomputable def basisPiTensorLinearEquiv
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) :
    DS n ℋ₂ ≃ₗ[ℂ] ℋ₂ ⊗[ℂ] ℋ₁ :=
  (dsEquiv n ℋ₂).toLinearEquiv.trans <|
    ((Finsupp.linearEquivFunOnFinite ℂ ℋ₂ (Fin n)).symm.trans
      (TensorProduct.equivFinsuppOfBasisRight b.toBasis).symm)

lemma basisPiTensorLinearEquiv_apply
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) (x : DS n ℋ₂) :
    basisPiTensorLinearEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b x =
      ∑ i, dsProj n ℋ₂ i x ⊗ₜ[ℂ] b i := by
  rw [basisPiTensorLinearEquiv]
  change
    (TensorProduct.equivFinsuppOfBasisRight b.toBasis).symm
        ((Finsupp.linearEquivFunOnFinite ℂ ℋ₂ (Fin n)).symm ((dsEquiv n ℋ₂) x)) =
      ∑ i, dsProj n ℋ₂ i x ⊗ₜ[ℂ] b i
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply]
  simp [Finsupp.sum_fintype, dsProj, dsEquiv]

lemma basisPiTensorLinearEquiv_dsIncl
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) (i : Fin n) (x : ℋ₂) :
    basisPiTensorLinearEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b (dsIncl n ℋ₂ i x) =
      x ⊗ₜ[ℂ] b i := by
  rw [basisPiTensorLinearEquiv_apply]
  classical
  rw [Finset.sum_eq_single i]
  · simp [dsProj_dsIncl_apply]
  · intro j _ hji
    simp [dsProj_dsIncl_apply, hji]
  · simp

lemma basisPiTensorLinearEquiv_inner
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) (x y : DS n ℋ₂) :
    inner ℂ
        (basisPiTensorLinearEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b x)
        (basisPiTensorLinearEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b y) =
      inner ℂ x y := by
  rw [basisPiTensorLinearEquiv_apply, basisPiTensorLinearEquiv_apply]
  classical
  simp only [inner_sum, sum_inner, TensorProduct.inner_tmul]
  simpa [PiLp.inner_apply] using
    (b.orthonormal.inner_left_right_finset
      (s := Finset.univ)
      (a := fun i j => inner ℂ (dsProj n ℋ₂ j x) (dsProj n ℋ₂ i y)))

noncomputable def basisPiTensorLinearIsometryEquiv
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) :
    DS n ℋ₂ ≃ₗᵢ[ℂ] ℋ₂ ⊗[ℂ] ℋ₁ :=
  (basisPiTensorLinearEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b).isometryOfInner
    (basisPiTensorLinearEquiv_inner (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b)

noncomputable def basisPiTensorEndAlgEquiv
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) :
    L (DS n ℋ₂) ≃⋆ₐ[ℂ] L (ℋ₂ ⊗[ℂ] ℋ₁) :=
  (linearToContinuousEndStarAlgEquiv (ℋ := DS n ℋ₂)).trans <|
    ((basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b).conjStarAlgEquiv.trans
      (linearToContinuousEndStarAlgEquiv (ℋ := ℋ₂ ⊗[ℂ] ℋ₁)).symm)

lemma basisPiTensorLinearIsometryEquiv_apply
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) (x : DS n ℋ₂) :
    basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b x =
      ∑ i, dsProj n ℋ₂ i x ⊗ₜ[ℂ] b i := by
  simpa using basisPiTensorLinearEquiv_apply (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b x

lemma basisPiTensorLinearIsometryEquiv_dsIncl
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) (i : Fin n) (x : ℋ₂) :
    basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b (dsIncl n ℋ₂ i x) =
      x ⊗ₜ[ℂ] b i := by
  exact basisPiTensorLinearEquiv_dsIncl (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b i x

lemma basisPiTensorLinearIsometryEquiv_symm_tmul
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) (i : Fin n) (x : ℋ₂) :
    (basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b).symm (x ⊗ₜ[ℂ] b i) =
      dsIncl n ℋ₂ i x := by
  apply (basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b).injective
  simpa using
    (basisPiTensorLinearIsometryEquiv_dsIncl (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b i x).symm

lemma basisPiTensorEndAlgEquiv_apply_apply
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁)
    (A : L (DS n ℋ₂)) (z : ℋ₂ ⊗[ℂ] ℋ₁) :
    basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b A z =
      basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b
        (A ((basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b).symm z)) := by
  rfl

lemma basisPiTensorEndAlgEquiv_apply_tmul_basis
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁)
    (A : L (DS n ℋ₂)) (x : ℋ₂) (j : Fin n) :
    basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b A (x ⊗ₜ[ℂ] b j) =
      ∑ i : Fin n, ((ampCStarEquiv n ℋ₂ A) i j) x ⊗ₜ[ℂ] b i := by
  rw [basisPiTensorEndAlgEquiv_apply_apply]
  rw [basisPiTensorLinearIsometryEquiv_symm_tmul]
  rw [basisPiTensorLinearIsometryEquiv_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  have hcoord :
      dsProj n ℋ₂ i (A (dsIncl n ℋ₂ j x)) =
        ampPlainEquiv n ℋ₂ A i j x := by
    symm
    exact ampPlainEquiv_apply_apply_ds
      (k := n) (ℋ := ℋ₂) (f := A) (i := i) (j := j) (x := x)
  rw [hcoord]
  rfl

lemma matrixUnit_apply_basis
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁)
    (i j k : Fin n) :
    outer_product (b j) (b i) (b k) = if j = k then b i else 0 := by
  by_cases h : j = k
  · subst h
    simp [outer_product, dualTensorHom_apply]
  · simp [outer_product, dualTensorHom_apply, h]

lemma basisPiTensorEndAlgEquiv_expansion
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁)
    (A : L (DS n ℋ₂)) :
    basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b A =
      ∑ i : Fin n, ∑ j : Fin n,
        (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
          (((ampCStarEquiv n ℋ₂ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i)) := by
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x v
    calc
      basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b A (x ⊗ₜ[ℂ] v) =
          ∑ j : Fin n,
            (b.repr v j) •
              basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b A (x ⊗ₜ[ℂ] b j) := by
          conv_lhs => rw [← b.sum_repr v]
          simp [TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum]
      _ =
          ∑ j : Fin n,
            (b.repr v j) •
              ∑ i : Fin n, ((ampCStarEquiv n ℋ₂ A) i j) x ⊗ₜ[ℂ] b i := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [basisPiTensorEndAlgEquiv_apply_tmul_basis]
      _ =
          ∑ i : Fin n, ∑ j : Fin n,
            (b.repr v j) • (((ampCStarEquiv n ℋ₂ A) i j) x ⊗ₜ[ℂ] b i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro i _
          simp [Finset.smul_sum]
      _ =
          (∑ i : Fin n, ∑ j : Fin n,
            (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
              (((ampCStarEquiv n ℋ₂ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i))) (x ⊗ₜ[ℂ] v) := by
          simp only [LinearMap.sum_apply]
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [l_tensor_equiv_symm_tmul]
          simp [outer_product, dualTensorHom_apply, TensorProduct.tmul_smul,
            OrthonormalBasis.repr_apply_apply]
  · intro z w hz hw
    simp only [hz, hw, map_add]

lemma basisPiTensorEndAlgEquiv_ampSuper
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁)
    (Φ : T ℋ₁ ℋ₂) (A : L (DS n ℋ₁)) :
    basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b (ampSuper n Φ A) =
      amplifyWithId Φ (basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁) n b A) := by
  rw [basisPiTensorEndAlgEquiv_expansion (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b (ampSuper n Φ A)]
  rw [basisPiTensorEndAlgEquiv_expansion (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁) n b A]
  simp only [amplifyWithId, LinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  have hentry :
      (ampCStarEquiv n ℋ₂ (ampSuper n Φ A)) i j =
        Φ ((ampCStarEquiv n ℋ₁ A) i j) := by
    have h := congrFun (congrFun (ampCStarEquiv_ampSuper_apply (k := n) (Φ := Φ) (A := A)) i) j
    simpa [CStarMatrix.map_apply] using h
  have hterm :
      ((ampCStarEquiv n ℋ₂ (ampSuper n Φ A)) i j) ⊗ₜ[ℂ] outer_product (b j) (b i) =
        Φ ((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i) := by
    exact congrArg (fun B : L ℋ₂ => B ⊗ₜ[ℂ] outer_product (b j) (b i)) hentry
  have hcancel :
      (l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
          ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁)).symm
            (((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i))) =
        ((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i) := by
    exact LinearEquiv.apply_symm_apply (l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
      (((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i))
  apply (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).injective
  rw [LinearEquiv.apply_symm_apply]
  have houter :
      (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁))
          ((l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
            ((TensorProduct.map Φ LinearMap.id)
              ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
                ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁)).symm
                  (((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i)))))) =
        (TensorProduct.map Φ LinearMap.id)
          ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
            ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁)).symm
              (((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i)))) := by
    exact LinearEquiv.apply_symm_apply (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁))
      ((TensorProduct.map Φ LinearMap.id)
        ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
          ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁)).symm
            (((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i)))))
  change
      ((ampCStarEquiv n ℋ₂ (ampSuper n Φ A)) i j) ⊗ₜ[ℂ] outer_product (b j) (b i) =
        (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁))
          ((l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
            ((TensorProduct.map Φ LinearMap.id)
              ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
                ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁)).symm
                  (((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i))))))
  rw [houter]
  rw [hcancel]
  rw [TensorProduct.map_tmul]
  exact hterm

lemma ampSuper_krausTerm_eq
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) :
    ampSuper k (krausTerm V) = krausTerm (ampKrausFactor k V) := by
  apply LinearMap.ext
  intro A
  apply (ampCStarEquiv k ℋ₂).injective
  trans (ampCStarEquiv k ℋ₁ A).map (krausTerm V)
  · simpa using ampCStarEquiv_ampSuper_apply (k := k) (Φ := krausTerm V) (A := A)
  ext i j x
  change (((ampCStarEquiv k ℋ₁ A).map (krausTerm V)) i j) x =
    ampPlainEquiv k ℋ₂ ((krausTerm (ampKrausFactor k V)) A) i j x
  rw [ampPlainEquiv_apply_apply_ds]
  have hentry :
      (ampCStarEquiv k ℋ₁ A i j) (V.adjoint x) =
        dsProj k ℋ₁ i (A (dsIncl k ℋ₁ j (V.adjoint x))) := by
    simpa using
      (ampPlainEquiv_apply_apply_ds (k := k) (ℋ := ℋ₁) (f := A) (i := i) (j := j)
        (x := V.adjoint x)).symm
  simp [CStarMatrix.map_apply, krausTerm, dsProj_ampKrausFactor,
    ampKrausFactor_adjoint_dsIncl, hentry]

lemma krausTerm_isCompletelyPositive
    (V : ℋ₁ →ₗ[ℂ] ℋ₂) :
    IsCompletelyPositive (krausTerm V) := by
  refine (isCompletelyPositive_iff_cstarMatrix_nonneg (krausTerm V)).mpr ?_
  intro k M hM
  have hK : IsKPositive k (krausTerm V) := by
    exact (isKPositive_iff_isPositiveMap_ampSuper (k := k) (Φ := krausTerm V)).mpr <| by
      simpa [ampSuper_krausTerm_eq] using
        krausTerm_isPositiveMap (V := ampKrausFactor k V)
  exact hK M hM

lemma sum_krausTerm_isCompletelyPositive
    {σ : Type*} [Fintype σ]
    (V : σ → (ℋ₁ →ₗ[ℂ] ℋ₂)) :
    IsCompletelyPositive (∑ r, krausTerm (V r)) := by
  classical
  refine (isCompletelyPositive_iff_cstarMatrix_nonneg (∑ r, krausTerm (V r))).mpr ?_
  intro k M hM
  have hmap : M.map (∑ r, (krausTerm (V r) : T ℋ₁ ℋ₂)) = ∑ r, M.map (krausTerm (V r)) := by
    have hmapFin (s : Finset σ) :
        M.map (Finset.sum s fun r => (krausTerm (V r) : T ℋ₁ ℋ₂)) =
          Finset.sum s fun r => M.map (krausTerm (V r)) := by
      ext i j x
      induction s using Finset.induction_on with
      | empty =>
          simp [CStarMatrix.map_apply]
      | @insert a s ha ih =>
          simp [Finset.sum_insert, ha, CStarMatrix.map_apply, LinearMap.sum_apply]
          simpa [CStarMatrix.map_apply, LinearMap.sum_apply] using ih
    simpa using hmapFin Finset.univ
  simpa [hmap] using
    (Finset.sum_nonneg fun r _ =>
      (isCompletelyPositive_iff_cstarMatrix_nonneg (krausTerm (V r))).mp
        (krausTerm_isCompletelyPositive (V r)) k M hM)

def AmplificationPositive (Φ : T ℋ₁ ℋ₂) : Prop :=
  IsPositiveMap (amplifyWithId Φ)

lemma cp_amplify
    (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → AmplificationPositive Φ := by
  intro hΦ X hX
  let n := Module.finrank ℂ ℋ₁
  let b : OrthonormalBasis (Fin n) ℂ ℋ₁ := stdOrthonormalBasis ℂ ℋ₁
  let e₁ := basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁) n b
  let e₂ := basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b
  let A : L (DS n ℋ₁) := e₁.symm X
  have hA : 0 ≤ A := by
    have hX' : 0 ≤ e₁ A := by
      simpa [A, e₁] using hX
    exact (starAlgEquiv_nonneg_iff e₁).1 hX'
  have hK : IsKPositive n Φ :=
    (isCompletelyPositive_iff_cstarMatrix_nonneg Φ).mp hΦ n
  have hAmp : 0 ≤ ampSuper n Φ A :=
    (isKPositive_iff_isPositiveMap_ampSuper (k := n) (Φ := Φ)).mp hK A hA
  have hTensor : 0 ≤ e₂ (ampSuper n Φ A) :=
    starAlgEquiv_nonneg e₂ hAmp
  have hEq : e₂ (ampSuper n Φ A) = amplifyWithId Φ X := by
    simpa [A, e₁, e₂] using
      (basisPiTensorEndAlgEquiv_ampSuper (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b Φ A)
  simpa [hEq] using hTensor

def ChoiPositive (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) : Prop :=
  0 ≤ choi b Φ

def KrausRep (Φ : T ℋ₁ ℋ₂) (κ : Type*) [DecidableEq κ] [Fintype κ] : Prop :=
  ∃ A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂),
    ∀ X : L ℋ₁, Φ X = ∑ a : κ, (A a).comp (X.comp (LinearMap.adjoint (A a)))

theorem fixed_kraus_to_cp
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (Φ : T ℋ₁ ℋ₂) :
    KrausRep Φ κ → IsCompletelyPositive Φ := by
  rintro ⟨A, hA⟩
  have hΦ : Φ = ∑ a : κ, krausTerm (A a) := by
    apply LinearMap.ext
    intro X
    simpa [krausTerm] using hA X
  rw [hΦ]
  exact sum_krausTerm_isCompletelyPositive A

noncomputable def choiRank (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) : ℕ :=
  Module.finrank ℂ (LinearMap.range (choi b Φ))

def HasKraus (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∃ (κ : Type u) (_ : DecidableEq κ) (_ : Fintype κ),
    @KrausRep ℋ₁ ℋ₂ _ _ Φ κ _ _

def HasRankKraus (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∃ (κ : Type u) (dec : DecidableEq κ) (inst : Fintype κ),
    Fintype.card κ = choiRank b Φ ∧
      @KrausRep ℋ₁ ℋ₂ _ _ Φ κ dec inst

lemma positive_full_spectral_outer_product
    {E : Type*} [Qudit E] (T : L E) (hT : 0 ≤ T) :
    let n := Module.finrank ℂ E
    let hTpos : T.IsPositive := (LinearMap.nonneg_iff_isPositive T).mp hT
    let hSym : T.IsSymmetric := hTpos.isSymmetric
    ∃ u : Fin n → E,
      T = ∑ i : Fin n, outer_product (u i) (u i) ∧
        ∀ i : Fin n, hSym.eigenvalues rfl i = 0 → u i = 0 := by
  classical
  dsimp
  let n := Module.finrank ℂ E
  let hTpos : T.IsPositive := (LinearMap.nonneg_iff_isPositive T).mp hT
  let hSym : T.IsSymmetric := hTpos.isSymmetric
  let u : Fin n → E :=
    fun i => ((hSym.eigenvalues rfl i).sqrt : ℂ) • hSym.eigenvectorBasis rfl i
  refine ⟨u, ?_, ?_⟩
  · ext x
    rw [show (∑ i : Fin n, outer_product (u i) (u i)) x =
        ∑ i : Fin n, inner ℂ (u i) x • u i by
      simp [outer_product_eq_rankOne]]
    simp_rw [u]
    simp_rw [inner_smul_left]
    simp_rw [smul_smul]
    simp_rw [mul_assoc]
    simp_rw [Complex.conj_ofReal]
    simp_rw [mul_comm (inner ℂ _ _)]
    simp_rw [← mul_assoc]
    simp_rw [← Complex.ofReal_mul]
    simp_rw [← Real.sqrt_mul (hTpos.nonneg_eigenvalues rfl _)]
    simp_rw [Real.sqrt_mul_self (hTpos.nonneg_eigenvalues rfl _)]
    simp_rw [mul_comm _ (inner ℂ _ _)]
    simp_rw [← smul_eq_mul]
    simp_rw [smul_assoc]
    have happly :
        ∀ i : Fin n,
          (hSym.eigenvalues rfl i : ℂ) • hSym.eigenvectorBasis rfl i =
            T (hSym.eigenvectorBasis rfl i) := by
      intro i
      exact (hSym.apply_eigenvectorBasis rfl i).symm
    simp_rw [happly]
    simp_rw [← map_smul]
    simp_rw [← map_sum]
    simp_rw [← OrthonormalBasis.repr_apply_apply]
    simp_rw [OrthonormalBasis.sum_repr]
  · intro i hi
    change ((hSym.eigenvalues rfl i).sqrt : ℂ) • hSym.eigenvectorBasis rfl i = 0
    simp [hi]

lemma positive_spectral_outer_product
    {E : Type*} [Qudit E] (T : L E) (hT : 0 ≤ T) :
    let n := Module.finrank ℂ E
    let hTpos : T.IsPositive := (LinearMap.nonneg_iff_isPositive T).mp hT
    let hSym : T.IsSymmetric := hTpos.isSymmetric
    ∃ u : { i : Fin n // hSym.eigenvalues rfl i ≠ 0 } → E,
      T = ∑ a, outer_product (u a) (u a) := by
  dsimp
  let n := Module.finrank ℂ E
  let hTpos : T.IsPositive := (LinearMap.nonneg_iff_isPositive T).mp hT
  let hSym : T.IsSymmetric := hTpos.isSymmetric
  let p : Fin n → Prop := fun i => hSym.eigenvalues rfl i ≠ 0
  obtain ⟨u, hsum, hzero⟩ :=
    positive_full_spectral_outer_product (T := T) (hT := hT)
  refine ⟨fun a => u a, ?_⟩
  have hzero_sum :
      (∑ a : { i : Fin n // ¬ p i }, outer_product (u a) (u a)) = 0 := by
    apply Fintype.sum_eq_zero
    intro a
    have ha : hSym.eigenvalues rfl a = 0 := not_not.mp a.property
    simp [hzero a ha, outer_product]
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype p
      (fun i : Fin n => outer_product (u i) (u i))
  calc
    T = ∑ i : Fin n, outer_product (u i) (u i) := hsum
    _ = ∑ a : { i : Fin n // p i }, outer_product (u a) (u a) := by
      rw [← hsplit, hzero_sum, add_zero]

lemma positive_to_rank_outer_product
    {E : Type*} [Qudit E] (T : L E) (hT : 0 ≤ T) :
    ∃ (κ : Type u) (_ : DecidableEq κ) (_ : Fintype κ),
      Fintype.card κ = Module.finrank ℂ (LinearMap.range T) ∧
        ∃ u : κ → E, T = ∑ a : κ, outer_product (u a) (u a) := by
  let n := Module.finrank ℂ E
  let hTpos : T.IsPositive := (LinearMap.nonneg_iff_isPositive T).mp hT
  let hSym : T.IsSymmetric := hTpos.isSymmetric
  let κ₀ := { i : Fin n // hSym.eigenvalues rfl i ≠ 0 }
  let κ := ULift κ₀
  have hcard₀ : Fintype.card κ₀ = Module.finrank ℂ (LinearMap.range T) := by
    exact card_nonzero_eigenvalues_eq_finrank_range T hT
  have hcard : Fintype.card κ = Module.finrank ℂ (LinearMap.range T) := by
    simpa [κ, Fintype.card_ulift] using hcard₀
  obtain ⟨u₀, hu₀⟩ :=
    positive_spectral_outer_product (T := T) (hT := hT)
  refine ⟨κ, inferInstance, inferInstance, hcard, ?_⟩
  refine ⟨fun a : κ => u₀ a.down, ?_⟩
  have hsum :
      (∑ a : κ, outer_product (u₀ a.down) (u₀ a.down)) =
        ∑ a : κ₀, outer_product (u₀ a) (u₀ a) := by
    symm
    refine Fintype.sum_equiv (Equiv.ulift.symm : κ₀ ≃ κ) _ _ ?_
    intro a
    rfl
  exact hu₀.trans hsum.symm

theorem hasRankKraus_to_hasKraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankKraus b Φ → HasKraus Φ := by
  rintro ⟨κ, dec, inst, _, hkraus⟩
  exact ⟨κ, dec, inst, hkraus⟩

theorem rankKraus_to_kraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankKraus b Φ → HasKraus Φ :=
  hasRankKraus_to_hasKraus b Φ

theorem kraus_to_positiveMap
    (Φ : T ℋ₁ ℋ₂) :
    HasKraus Φ → IsPositiveMap Φ := by
  rintro ⟨κ, hκ, hκ', A, hA⟩ X hX
  letI : DecidableEq κ := hκ
  letI : Fintype κ := hκ'
  rw [hA X]
  exact Finset.sum_nonneg fun a _ =>
    conjugate_positive (ℋ₁ := ℋ₁) (ℋ₃ := ℋ₂) (A a) X hX

theorem rankKraus_to_positiveMap
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankKraus b Φ → IsPositiveMap Φ :=
  kraus_to_positiveMap Φ ∘
    rankKraus_to_kraus b Φ

noncomputable def conjugateEnd {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (e : E ≃ₗ[ℂ] F) :
    (E →ₗ[ℂ] E) →ₗ[ℂ] (F →ₗ[ℂ] F) where
  toFun X := e.toLinearMap.comp (X.comp e.symm.toLinearMap)
  map_add' X Y := by
    ext x
    simp
  map_smul' c X := by
    ext x
    simp

lemma conjugateEnd_comm_positive
    {E : Type u} {F : Type v} [Qudit E] [Qudit F] :
    IsPositiveMap (conjugateEnd (TensorProduct.comm ℂ E F)) := by
  intro X hX
  have hXpos : X.IsPositive := (LinearMap.nonneg_iff_isPositive X).mp hX
  have hcomm :
      LinearMap.adjoint (TensorProduct.comm ℂ E F).toLinearMap =
        (TensorProduct.comm ℂ E F).symm.toLinearMap := by
    simpa [TensorProduct.toLinearEquiv_commIsometry] using
      (LinearIsometryEquiv.adjoint_toLinearMap_eq_symm
        (TensorProduct.commIsometry ℂ E F))
  exact (LinearMap.nonneg_iff_isPositive _).mpr <| by
    simpa [conjugateEnd, hcomm] using
      hXpos.conj_adjoint (TensorProduct.comm ℂ E F).toLinearMap

noncomputable def TrRight {ℋ₃ : Type u} [Qudit ℋ₃] : T (ℋ₂ ⊗[ℂ] ℋ₃) ℋ₂ :=
  (Tr₂ (ℋ₁ := ℋ₃) (ℋ₂ := ℋ₂)).comp
    (conjugateEnd (TensorProduct.comm ℂ ℋ₂ ℋ₃))

noncomputable def krausToStinespringOperator
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) :
    ℋ₁ →ₗ[ℂ] (ℋ₂ ⊗[ℂ] EuclideanSpace ℂ κ) where
  toFun x := ∑ a : κ, (A a x) ⊗ₜ[ℂ] (EuclideanSpace.basisFun κ ℂ a)
  map_add' x y := by
    simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp [TensorProduct.smul_tmul', Finset.smul_sum]

lemma krausToStinespringOperator_apply
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) (x : ℋ₁) :
    krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A x
      = ∑ a : κ, (A a x) ⊗ₜ[ℂ] (EuclideanSpace.basisFun κ ℂ a) :=
  rfl

lemma adjoint_krausToStinespringOperator_tmul_basisFun
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) (y : ℋ₂) (b : κ) :
    (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))
        (y ⊗ₜ[ℂ] EuclideanSpace.basisFun κ ℂ b) =
      (LinearMap.adjoint (A b)) y := by
  apply ext_inner_right ℂ
  intro x
  rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
  simp [krausToStinespringOperator_apply, inner_sum, TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

lemma conjugateEnd_krausToStinespringOperator_apply_basisFun_tmul
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) (X : L ℋ₁) (b : κ) (y : ℋ₂) :
    (conjugateEnd (TensorProduct.comm ℂ ℋ₂ (EuclideanSpace ℂ κ))
        (((krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A).comp X).comp
          (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))))
      ((EuclideanSpace.basisFun κ ℂ b) ⊗ₜ[ℂ] y) =
        ∑ a : κ, (EuclideanSpace.basisFun κ ℂ a) ⊗ₜ[ℂ]
          ((A a).comp (X.comp (LinearMap.adjoint (A b))) y) := by
  have hadj :
      (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))
          (y ⊗ₜ[ℂ] EuclideanSpace.single b (1 : ℂ)) =
        (LinearMap.adjoint (A b)) y := by
    simpa [EuclideanSpace.basisFun_apply] using
      (adjoint_krausToStinespringOperator_tmul_basisFun
        (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) (κ := κ) A y b)
  simp [conjugateEnd, krausToStinespringOperator_apply, LinearMap.comp_apply,
    EuclideanSpace.basisFun_apply, hadj]

lemma conjugateEnd_krausToStinespringOperator_apply_single_tmul
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) (X : L ℋ₁) (b : κ) (y : ℋ₂) :
    (conjugateEnd (TensorProduct.comm ℂ ℋ₂ (EuclideanSpace ℂ κ))
        (((krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A).comp X).comp
          (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))))
      ((EuclideanSpace.single b (1 : ℂ)) ⊗ₜ[ℂ] y) =
        ∑ a : κ, (EuclideanSpace.single a (1 : ℂ)) ⊗ₜ[ℂ]
          ((A a).comp (X.comp (LinearMap.adjoint (A b))) y) := by
  simpa [EuclideanSpace.basisFun_apply] using
    (conjugateEnd_krausToStinespringOperator_apply_basisFun_tmul
      (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A X b y)

lemma finrank_kraus_environment
    {κ : Type u} [DecidableEq κ] [Fintype κ] :
    Module.finrank ℂ (EuclideanSpace ℂ κ) = Fintype.card κ := by
  simp [finrank_euclideanSpace (𝕜 := ℂ) (ι := κ)]

lemma linearMap_eq_sum_outer_product
    {E : Type u} [Qudit E] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (T : L E) :
    T = ∑ i : ι, outer_product (b i) (T (b i)) := by
  ext x
  have hsum : T x = ∑ i : ι, inner ℂ (b i) x • T (b i) := by
    simpa using congrArg T (b.sum_repr' x).symm
  calc
    T x = ∑ i : ι, inner ℂ (b i) x • T (b i) := hsum
    _ = (∑ i : ι, outer_product (b i) (T (b i))) x := by
      simp [LinearMap.sum_apply, outer_product_eq_rankOne]

lemma basis_dual_inner
    {E : Type u} [Qudit E] {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι ℂ E) (i j : ι) :
    inner ℂ (b i)
      ((InnerProductSpace.toDual ℂ E).symm ((b.coord j).toContinuousLinearMap)) =
        if i = j then 1 else 0 := by
  rw [← inner_conj_symm]
  have h :
      inner ℂ
        ((InnerProductSpace.toDual ℂ E).symm ((b.coord j).toContinuousLinearMap))
        (b i) = if i = j then 1 else 0 := by
    simpa using (Module.Basis.dualBasis_apply_self b j i)
  rw [h]
  by_cases hij : i = j <;> simp [hij]

lemma basis_sum_dual
    {E : Type u} [Qudit E] {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι ℂ E) (x : E) :
    x =
      ∑ i : ι, inner ℂ (b i) x •
        ((InnerProductSpace.toDual ℂ E).symm ((b.coord i).toContinuousLinearMap)) := by
  apply InnerProductSpace.ext_inner_left_basis b
  intro j
  rw [inner_sum]
  simp [inner_smul_right, basis_dual_inner]

lemma linearMap_eq_sum_basis_outer_product
    {E : Type u} [Qudit E] {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι ℂ E) (T : L E) :
    T =
      ∑ i : ι, ∑ j : ι,
        (b.coord j
          (T ((InnerProductSpace.toDual ℂ E).symm ((b.coord i).toContinuousLinearMap)))) •
          outer_product (b i) (b j) := by
  ext x
  have hx := basis_sum_dual b x
  calc
    T x =
        T (∑ i : ι, inner ℂ (b i) x •
          ((InnerProductSpace.toDual ℂ E).symm ((b.coord i).toContinuousLinearMap))) := by
          rw [← hx]
    _ = ∑ i : ι, inner ℂ (b i) x •
          T ((InnerProductSpace.toDual ℂ E).symm ((b.coord i).toContinuousLinearMap)) := by
          simp [map_sum]
    _ = ∑ i : ι, inner ℂ (b i) x •
          (∑ j : ι,
            (b.coord j
              (T ((InnerProductSpace.toDual ℂ E).symm ((b.coord i).toContinuousLinearMap)))) •
              b j) := by
          simp [b.sum_repr]
    _ = (∑ i : ι, ∑ j : ι,
        (b.coord j
          (T ((InnerProductSpace.toDual ℂ E).symm ((b.coord i).toContinuousLinearMap)))) •
          outer_product (b i) (b j)) x := by
          simp only [LinearMap.sum_apply]
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          simp [outer_product, dualTensorHom_apply, smul_smul, mul_comm]

lemma basis_outer_coeff
    {E : Type u} [Qudit E] {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι ℂ E) (p q i j : ι) :
    b.coord q ((outer_product (b i) (b j))
      ((InnerProductSpace.toDual ℂ E).symm ((b.coord p).toContinuousLinearMap))) =
        if i = p then if j = q then 1 else 0 else 0 := by
  have hinner := basis_dual_inner b i p
  by_cases hip : i = p
  · subst hip
    by_cases hjq : j = q <;> simp [outer_product, dualTensorHom_apply, hinner, hjq]
  · simp [outer_product, dualTensorHom_apply, hinner, hip]

lemma l_tensor_equiv_symm_outer_product
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (u v : E) (x y : F) :
    (l_tensor_equiv (ℋ₁ := E) (ℋ₂ := F)).symm
      ((outer_product u v) ⊗ₜ[ℂ] (outer_product x y)) =
        outer_product (u ⊗ₜ[ℂ] x) (v ⊗ₜ[ℂ] y) := by
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro a b
    simp [l_tensor_equiv, outer_product, TensorProduct.inner_tmul, smul_tmul']
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂]

lemma l_tensor_equiv_outer_product_tmul
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (u v : E) (x y : F) :
    (l_tensor_equiv (ℋ₁ := E) (ℋ₂ := F))
      (outer_product (u ⊗ₜ[ℂ] x) (v ⊗ₜ[ℂ] y)) =
        (outer_product u v) ⊗ₜ[ℂ] (outer_product x y) := by
  apply (l_tensor_equiv (ℋ₁ := E) (ℋ₂ := F)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (l_tensor_equiv_symm_outer_product (E := E) (F := F) u v x y).symm

lemma choi_basis_expansion
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    choi b Φ =
      ∑ i : ι, ∑ j : ι,
        (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
          ((Φ (outer_product (b i) (b j))) ⊗ₜ[ℂ] outer_product (b i) (b j)) := by
  rw [choi, vec_apply]
  simp only [I, LinearMap.id_coe, id_eq]
  change (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
      ((TensorProduct.map Φ LinearMap.id)
        ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
          (outer_product (∑ i : ι, b i ⊗ₜ[ℂ] b i) (∑ i : ι, b i ⊗ₜ[ℂ] b i)))) =
    ∑ i : ι, ∑ j : ι,
      (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
        ((Φ (outer_product (b i) (b j))) ⊗ₜ[ℂ] outer_product (b i) (b j))
  rw [show outer_product (∑ i : ι, b i ⊗ₜ[ℂ] b i) (∑ i : ι, b i ⊗ₜ[ℂ] b i) =
      ∑ i : ι, ∑ j : ι, outer_product (b i ⊗ₜ[ℂ] b i) (b j ⊗ₜ[ℂ] b j) by
    exact outer_product_sum (fun i : ι => b i ⊗ₜ[ℂ] b i) (fun i : ι => b i ⊗ₜ[ℂ] b i)]
  simp only [map_sum]
  simp_rw [l_tensor_equiv_outer_product_tmul]
  simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq]

lemma tensor_basis_sum_coeff
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι ℂ E) (p q : ι) (S : ι → ι → L F) :
    (TensorProduct.rid ℂ (L F)).toLinearMap
      ((TensorProduct.map LinearMap.id
        { toFun := fun X : L E =>
            b.coord q (X ((InnerProductSpace.toDual ℂ E).symm ((b.coord p).toContinuousLinearMap)))
          map_add' := by intro X Y; simp
          map_smul' := by intro c X; simp })
        (∑ i : ι, ∑ j : ι, S i j ⊗ₜ[ℂ] outer_product (b i) (b j))) =
      S p q := by
  classical
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · have hcoeff :
          (b.repr ((outer_product (b p) (b q))
            ((InnerProductSpace.toDual ℂ E).symm
              (LinearMap.toContinuousLinearMap (b.coord p))))) q = 1 := by
          simpa using (basis_outer_coeff b p q p q)
      simp [Module.Basis.coord_apply, hcoeff]
    · intro j _ hjq
      have hcoeff :
          (b.repr ((outer_product (b p) (b j))
            ((InnerProductSpace.toDual ℂ E).symm
              (LinearMap.toContinuousLinearMap (b.coord p))))) q = 0 := by
          simpa [hjq] using (basis_outer_coeff b p q p j)
      simp [Module.Basis.coord_apply, hcoeff]
    · intro hq
      simp at hq
  · intro i _ hip
    apply Finset.sum_eq_zero
    intro j _
    have hcoeff :
        (b.repr ((outer_product (b i) (b j))
          ((InnerProductSpace.toDual ℂ E).symm
            (LinearMap.toContinuousLinearMap (b.coord p))))) q = 0 := by
        simpa [hip] using (basis_outer_coeff b p q i j)
    simp [Module.Basis.coord_apply, hcoeff]
  · intro hp
    simp at hp

lemma choi_basis_apply_eq_of_choi_eq
    (b : Module.Basis ι ℂ ℋ₁) {Φ Ψ : T ℋ₁ ℋ₂}
    (h : choi b Φ = choi b Ψ) (i j : ι) :
    Φ (outer_product (b i) (b j)) = Ψ (outer_product (b i) (b j)) := by
  have htensor :
      (∑ p : ι, ∑ q : ι,
        Φ (outer_product (b p) (b q)) ⊗ₜ[ℂ] outer_product (b p) (b q)) =
      (∑ p : ι, ∑ q : ι,
        Ψ (outer_product (b p) (b q)) ⊗ₜ[ℂ] outer_product (b p) (b q)) := by
    have h' := congrArg (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)) h
    simpa [choi_basis_expansion] using h'
  calc
    Φ (outer_product (b i) (b j)) =
        (TensorProduct.rid ℂ (L ℋ₂)).toLinearMap
          ((TensorProduct.map LinearMap.id
            { toFun := fun X : L ℋ₁ =>
                b.coord j
                  (X ((InnerProductSpace.toDual ℂ ℋ₁).symm ((b.coord i).toContinuousLinearMap)))
              map_add' := by intro X Y; simp
              map_smul' := by intro c X; simp })
            (∑ p : ι, ∑ q : ι,
              Φ (outer_product (b p) (b q)) ⊗ₜ[ℂ] outer_product (b p) (b q))) := by
          exact (tensor_basis_sum_coeff b i j
            (fun p q => Φ (outer_product (b p) (b q)))).symm
    _ =
        (TensorProduct.rid ℂ (L ℋ₂)).toLinearMap
          ((TensorProduct.map LinearMap.id
            { toFun := fun X : L ℋ₁ =>
                b.coord j
                  (X ((InnerProductSpace.toDual ℂ ℋ₁).symm ((b.coord i).toContinuousLinearMap)))
              map_add' := by intro X Y; simp
              map_smul' := by intro c X; simp })
            (∑ p : ι, ∑ q : ι,
              Ψ (outer_product (b p) (b q)) ⊗ₜ[ℂ] outer_product (b p) (b q))) := by
          rw [htensor]
    _ = Ψ (outer_product (b i) (b j)) := by
          exact tensor_basis_sum_coeff b i j
            (fun p q => Ψ (outer_product (b p) (b q)))

lemma choi_injective
    (b : Module.Basis ι ℂ ℋ₁) :
    Function.Injective (choi b : T ℋ₁ ℋ₂ → L (ℋ₂ ⊗[ℂ] ℋ₁)) := by
  intro Φ Ψ h
  apply LinearMap.ext
  intro X
  conv_lhs => rw [linearMap_eq_sum_basis_outer_product b X]
  conv_rhs => rw [linearMap_eq_sum_basis_outer_product b X]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [choi_basis_apply_eq_of_choi_eq b h i j]

lemma outer_product_vec_expansion
    (b : Module.Basis ι ℂ ℋ₁) (A : ℋ₁ →ₗ[ℂ] ℋ₂) :
    outer_product (vec b A) (vec b A) =
      ∑ i : ι, ∑ j : ι,
        (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
          ((outer_product (A (b i)) (A (b j))) ⊗ₜ[ℂ] outer_product (b i) (b j)) := by
  rw [vec_apply]
  rw [show outer_product (∑ i : ι, A (b i) ⊗ₜ[ℂ] b i)
      (∑ i : ι, A (b i) ⊗ₜ[ℂ] b i) =
      ∑ i : ι, ∑ j : ι,
        outer_product (A (b i) ⊗ₜ[ℂ] b i) (A (b j) ⊗ₜ[ℂ] b j) by
    exact outer_product_sum
      (fun i : ι => A (b i) ⊗ₜ[ℂ] b i)
      (fun i : ι => A (b i) ⊗ₜ[ℂ] b i)]
  simp_rw [← l_tensor_equiv_symm_outer_product]

lemma choi_kraus_expansion
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis ι ℂ ℋ₁) (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) :
    choi b
      { toFun := fun X => ∑ a : κ, (A a).comp (X.comp (LinearMap.adjoint (A a)))
        map_add' := by
          intro X Y
          simp [LinearMap.comp_add, LinearMap.add_comp, Finset.sum_add_distrib]
        map_smul' := by
          intro c X
          simp [LinearMap.comp_smul, LinearMap.smul_comp, Finset.smul_sum] } =
      ∑ a : κ, outer_product (vec b (A a)) (vec b (A a)) := by
  classical
  rw [choi_basis_expansion]
  change
    ∑ i : ι, ∑ j : ι,
      (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
        (((∑ a : κ, (A a).comp ((outer_product (b i) (b j)).comp
          (LinearMap.adjoint (A a)))) ⊗ₜ[ℂ] outer_product (b i) (b j))) =
      ∑ a : κ, outer_product (vec b (A a)) (vec b (A a))
  simp_rw [comp_outer_product_adjoint]
  simp_rw [TensorProduct.sum_tmul]
  simp only [map_sum]
  simp_rw [outer_product_vec_expansion]
  let F : ι → ι → κ → L (ℋ₂ ⊗[ℂ] ℋ₁) :=
    fun i j a =>
      (l_tensor_equiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
        ((outer_product (A a (b i)) (A a (b j))) ⊗ₜ[ℂ] outer_product (b i) (b j))
  change ∑ i : ι, ∑ j : ι, ∑ a : κ, F i j a =
    ∑ a : κ, ∑ i : ι, ∑ j : ι, F i j a
  calc
    ∑ i : ι, ∑ j : ι, ∑ a : κ, F i j a
        = ∑ i : ι, ∑ a : κ, ∑ j : ι, F i j a := by
          refine Finset.sum_congr rfl ?_
          intro i _
          exact Finset.sum_comm
    _ = ∑ a : κ, ∑ i : ι, ∑ j : ι, F i j a := by
          exact Finset.sum_comm

lemma choi_outer_product_kraus_apply
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂)
    (u : κ → ℋ₂ ⊗[ℂ] ℋ₁)
    (hΦ : choi b Φ = ∑ a : κ, outer_product (u a) (u a))
    (X : L ℋ₁) :
    let A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂) :=
      fun a => (vecLinearEquiv (ℋ₁ := ℋ₂) b).symm (u a)
    Φ X = ∑ a : κ, (A a).comp (X.comp (LinearMap.adjoint (A a))) := by
  classical
  let A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂) :=
    fun a => (vecLinearEquiv (ℋ₁ := ℋ₂) b).symm (u a)
  let Ψ : T ℋ₁ ℋ₂ :=
    { toFun := fun X => ∑ a : κ, (A a).comp (X.comp (LinearMap.adjoint (A a)))
      map_add' := by
        intro X Y
        simp [LinearMap.comp_add, LinearMap.add_comp, Finset.sum_add_distrib]
      map_smul' := by
        intro c X
        simp [LinearMap.comp_smul, LinearMap.smul_comp, Finset.smul_sum] }
  have hvec : ∀ a : κ, vec b (A a) = u a := by
    intro a
    rw [← vecLinearEquiv_toLinearMap (ℋ₁ := ℋ₂) b]
    exact LinearEquiv.apply_symm_apply (vecLinearEquiv (ℋ₁ := ℋ₂) b) (u a)
  have hΨ : choi b Ψ = choi b Φ := by
    rw [choi_kraus_expansion]
    simp_rw [hvec]
    exact hΦ.symm
  have hmap : Ψ = Φ := choi_injective b hΨ
  change Φ X = Ψ X
  exact (LinearMap.congr_fun hmap X).symm

lemma choi_outer_product_to_kraus
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂)
    (u : κ → ℋ₂ ⊗[ℂ] ℋ₁)
    (hΦ : choi b Φ = ∑ a : κ, outer_product (u a) (u a)) :
    KrausRep Φ κ := by
  refine ⟨fun a => (vecLinearEquiv (ℋ₁ := ℋ₂) b).symm (u a), ?_⟩
  intro X
  exact choi_outer_product_kraus_apply b Φ u hΦ X

theorem fixed_kraus_to_choi
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    KrausRep Φ κ → ChoiPositive b Φ := by
  rintro ⟨A, hA⟩
  have hΦ :
      Φ =
        { toFun := fun X => ∑ a : κ, (A a).comp (X.comp (LinearMap.adjoint (A a)))
          map_add' := by
            intro X Y
            simp [LinearMap.comp_add, LinearMap.add_comp, Finset.sum_add_distrib]
          map_smul' := by
            intro c X
            simp [LinearMap.comp_smul, LinearMap.smul_comp, Finset.smul_sum] } := by
    apply LinearMap.ext
    intro X
    exact hA X
  rw [hΦ]
  rw [ChoiPositive, choi_kraus_expansion]
  exact Finset.sum_nonneg fun a _ =>
    outer_product_self_nonneg (vec b (A a))

theorem kraus_to_choi
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasKraus Φ → ChoiPositive b Φ := by
  rintro ⟨κ, hκ, hκ', hΦ⟩
  letI : DecidableEq κ := hκ
  letI : Fintype κ := hκ'
  exact fixed_kraus_to_choi b Φ hΦ

theorem rank_kraus_to_choi
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankKraus b Φ → ChoiPositive b Φ :=
  kraus_to_choi b Φ ∘
    rankKraus_to_kraus b Φ

set_option linter.flexible false in
lemma l_tensor_equiv_symm_outer_product_apply
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (u v x : E) (T : L F) (y : F) :
    ((l_tensor_equiv (ℋ₁ := E) (ℋ₂ := F)).symm
      ((outer_product u v) ⊗ₜ[ℂ] T)) (x ⊗ₜ[ℂ] y) =
        (outer_product u v x) ⊗ₜ[ℂ] T y := by
  let b := stdOrthonormalBasis ℂ F
  rw [linearMap_eq_sum_outer_product b T]
  rw [TensorProduct.tmul_sum]
  rw [map_sum]
  simp only [LinearMap.sum_apply, l_tensor_equiv_symm_outer_product]
  simp [outer_product_eq_rankOne, TensorProduct.inner_tmul]
  rw [TensorProduct.tmul_sum]
  simp [smul_tmul', smul_smul, mul_comm]

lemma ite_tmul_zero_left
    {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (p : Prop) [Decidable p] (x : E) (y : F) :
    (if p then x else 0) ⊗ₜ[ℂ] y = if p then x ⊗ₜ[ℂ] y else 0 := by
  by_cases hp : p <;> simp [hp]

lemma trace_outer_product_basisFun
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (a b : κ) :
    Tr (outer_product (EuclideanSpace.basisFun κ ℂ a) (EuclideanSpace.basisFun κ ℂ b)) =
      if a = b then 1 else 0 := by
  rw [outer_product_eq_rankOne, InnerProductSpace.trace_rankOne]
  by_cases hab : a = b
  · subst hab
    simp [EuclideanSpace.basisFun_apply]
  · simpa [hab] using (EuclideanSpace.basisFun κ ℂ).inner_eq_ite a b

lemma trace_outer_product_single
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (a b : κ) :
    Tr (outer_product (EuclideanSpace.single a (1 : ℂ)) (EuclideanSpace.single b (1 : ℂ))) =
      if a = b then 1 else 0 := by
  simpa [EuclideanSpace.basisFun_apply] using
    (trace_outer_product_basisFun (κ := κ) a b)

lemma trace_outer_product
    {E : Type u} [Qudit E] (u v : E) :
    Tr (outer_product u v) = inner ℂ u v := by
  rw [outer_product_eq_rankOne]
  simpa using InnerProductSpace.trace_rankOne (𝕜 := ℂ) (E := E) v u

noncomputable def tensorRightSlice
    {κ : Type*} [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (i : κ) :
    E ⊗[ℂ] F →ₗ[ℂ] E :=
  (TensorProduct.rid ℂ E).toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (b.toBasis.coord i)

lemma tensorRightSlice_tmul
    {κ : Type*} [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (i : κ) (x : E) (y : F) :
    tensorRightSlice (E := E) (F := F) b i (x ⊗ₜ[ℂ] y) =
      b.toBasis.coord i y • x := by
  simp [tensorRightSlice]

lemma tensorRightSlice_expand
    {κ : Type*} [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (z : E ⊗[ℂ] F) :
    z = ∑ i : κ, tensorRightSlice (E := E) (F := F) b i z ⊗ₜ[ℂ] b i := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x y
    calc
      x ⊗ₜ[ℂ] y = x ⊗ₜ[ℂ] (∑ i : κ, b.repr y i • b i) := by
        rw [b.sum_repr]
      _ = ∑ i : κ, x ⊗ₜ[ℂ] (b.repr y i • b i) := by
        rw [TensorProduct.tmul_sum]
      _ = ∑ i : κ, (b.toBasis.coord i y • x) ⊗ₜ[ℂ] b i := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        simp [OrthonormalBasis.repr_apply_apply]
  · intro x y hx hy
    calc
      x + y =
          ∑ i, (tensorRightSlice (E := E) (F := F) b i) x ⊗ₜ[ℂ] b i +
            ∑ i, (tensorRightSlice (E := E) (F := F) b i) y ⊗ₜ[ℂ] b i := by
            exact congrArg₂ (fun a b => a + b) hx hy
      _ =
          ∑ i,
            ((tensorRightSlice (E := E) (F := F) b i) x ⊗ₜ[ℂ] b i +
              (tensorRightSlice (E := E) (F := F) b i) y ⊗ₜ[ℂ] b i) := by
            rw [Finset.sum_add_distrib]
      _ =
          ∑ i,
            ((tensorRightSlice (E := E) (F := F) b i) x +
              (tensorRightSlice (E := E) (F := F) b i) y) ⊗ₜ[ℂ] b i := by
            simp [TensorProduct.add_tmul]
      _ =
          ∑ i, (tensorRightSlice (E := E) (F := F) b i) (x + y) ⊗ₜ[ℂ] b i := by
            simp [map_add]

lemma TrRight_outer_product_tmul_basis
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (i j : κ) (x y : E) :
    TrRight (ℋ₂ := E) (ℋ₃ := F)
      (outer_product (x ⊗ₜ[ℂ] b i) (y ⊗ₜ[ℂ] b j)) =
        if i = j then outer_product x y else 0 := by
  dsimp [TrRight]
  have hconj :
      conjugateEnd (TensorProduct.comm ℂ E F)
        (outer_product (x ⊗ₜ[ℂ] b i) (y ⊗ₜ[ℂ] b j)) =
        outer_product (b i ⊗ₜ[ℂ] x) (b j ⊗ₜ[ℂ] y) := by
    apply LinearMap.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [conjugateEnd, outer_product]
    · intro a c
      simp [conjugateEnd, outer_product_eq_rankOne, TensorProduct.inner_tmul, mul_comm]
    · intro z w hz hw
      simp [hz, hw]
  rw [hconj]
  rw [← l_tensor_equiv_symm_outer_product (E := F) (F := E) (b i) (b j) x y]
  rw [Tr₂_l_tensor_equiv_symm_tmul]
  rw [trace_outer_product]
  by_cases hij : i = j
  · subst j
    simp
  · simp [b.inner_eq_ite, hij]

lemma TrRight_outer_product
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (u v : E ⊗[ℂ] F) :
    TrRight (ℋ₂ := E) (ℋ₃ := F) (outer_product u v) =
      ∑ i : κ,
        outer_product
          (tensorRightSlice (E := E) (F := F) b i u)
          (tensorRightSlice (E := E) (F := F) b i v) := by
  conv_lhs =>
    rw [tensorRightSlice_expand (E := E) (F := F) b u,
      tensorRightSlice_expand (E := E) (F := F) b v]
    rw [outer_product_sum]
  simp only [map_sum]
  classical
  calc
    ∑ a : κ, ∑ b' : κ,
        TrRight (ℋ₂ := E) (ℋ₃ := F)
          (outer_product
            (tensorRightSlice (E := E) (F := F) b a u ⊗ₜ[ℂ] b a)
            (tensorRightSlice (E := E) (F := F) b b' v ⊗ₜ[ℂ] b b')) =
      ∑ a : κ, ∑ b' : κ,
        (if a = b' then
          outer_product
            (tensorRightSlice (E := E) (F := F) b a u)
            (tensorRightSlice (E := E) (F := F) b b' v)
        else 0) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        refine Finset.sum_congr rfl ?_
        intro b' _
        exact TrRight_outer_product_tmul_basis (E := E) (F := F) b a b'
          (tensorRightSlice (E := E) (F := F) b a u)
          (tensorRightSlice (E := E) (F := F) b b' v)
    _ =
      ∑ i : κ,
        outer_product
          (tensorRightSlice (E := E) (F := F) b i u)
          (tensorRightSlice (E := E) (F := F) b i v) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [Finset.sum_eq_single a]
        · simp
        · intro b' _ hb'
          have hab : a ≠ b' := fun h => hb' h.symm
          simp [hab]
        · simp

lemma tensorRightSlice_comp_outer_product
    {κ : Type*} [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (i : κ) (u v : E ⊗[ℂ] F) :
    (tensorRightSlice (E := E) (F := F) b i).comp
        ((outer_product u v).comp
          (LinearMap.adjoint (tensorRightSlice (E := E) (F := F) b i))) =
      outer_product
        (tensorRightSlice (E := E) (F := F) b i u)
        (tensorRightSlice (E := E) (F := F) b i v) := by
  exact @comp_outer_product_adjoint (E ⊗[ℂ] F) inferInstance E inferInstance
    (tensorRightSlice (E := E) (F := F) b i) u v

lemma TrRight_eq_kraus_sum
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (X : L (E ⊗[ℂ] F)) :
    TrRight (ℋ₂ := E) (ℋ₃ := F) X =
      (∑ i : κ,
        (tensorRightSlice (E := E) (F := F) b i).comp
          (X.comp (LinearMap.adjoint (tensorRightSlice (E := E) (F := F) b i))) : L E) := by
  let c : OrthonormalBasis (Fin (Module.finrank ℂ (E ⊗[ℂ] F))) ℂ (E ⊗[ℂ] F) :=
    stdOrthonormalBasis ℂ (E ⊗[ℂ] F)
  rw [linearMap_eq_sum_outer_product c X]
  calc
    TrRight (ℋ₂ := E) (ℋ₃ := F) (∑ a, outer_product (c a) (X (c a))) =
        ∑ a, TrRight (ℋ₂ := E) (ℋ₃ := F) (outer_product (c a) (X (c a))) := by
          simp
    _ =
        ∑ a, ∑ i : κ,
          (outer_product
            (tensorRightSlice (E := E) (F := F) b i (c a))
            (tensorRightSlice (E := E) (F := F) b i (X (c a))) : L E) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          exact TrRight_outer_product (E := E) (F := F) b (c a) (X (c a))
    _ =
        ∑ i : κ, ∑ a,
          (outer_product
            (tensorRightSlice (E := E) (F := F) b i (c a))
            (tensorRightSlice (E := E) (F := F) b i (X (c a))) : L E) := by
          rw [Finset.sum_comm]
    _ =
        (∑ i : κ,
          (tensorRightSlice (E := E) (F := F) b i).comp
            ((∑ a, outer_product (c a) (X (c a))).comp
              (LinearMap.adjoint (tensorRightSlice (E := E) (F := F) b i))) : L E) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          calc
            (∑ a,
              (outer_product
                (tensorRightSlice (E := E) (F := F) b i (c a))
                (tensorRightSlice (E := E) (F := F) b i (X (c a))) : L E)) =
                ∑ a,
                  (tensorRightSlice (E := E) (F := F) b i).comp
                    ((outer_product (c a) (X (c a))).comp
                      (LinearMap.adjoint (tensorRightSlice (E := E) (F := F) b i))) := by
                refine Finset.sum_congr rfl ?_
                intro a _
                exact (tensorRightSlice_comp_outer_product
                  (E := E) (F := F) b i (c a) (X (c a))).symm
            _ =
                (tensorRightSlice (E := E) (F := F) b i).comp
                  ((∑ a, outer_product (c a) (X (c a))).comp
                    (LinearMap.adjoint (tensorRightSlice (E := E) (F := F) b i))) := by
                ext z
                simp [LinearMap.comp_apply]

theorem TrRight_krausRep
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) :
    KrausRep (ℋ₁ := E ⊗[ℂ] F) (ℋ₂ := E)
      (TrRight (ℋ₂ := E) (ℋ₃ := F)) κ := by
  refine ⟨fun i => tensorRightSlice (E := E) (F := F) b i, ?_⟩
  intro X
  exact TrRight_eq_kraus_sum b X

theorem TrRight_isCompletelyPositive
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) :
    IsCompletelyPositive (TrRight (ℋ₂ := E) (ℋ₃ := F)) := by
  exact fixed_kraus_to_cp
    (ℋ₁ := E ⊗[ℂ] F) (ℋ₂ := E)
    (TrRight (ℋ₂ := E) (ℋ₃ := F))
    (TrRight_krausRep b)

theorem comp_isCompletelyPositive
    {ℋ₃ : Type w} [Qudit ℋ₃]
    (Φ : T ℋ₁ ℋ₂) (Ψ : T ℋ₂ ℋ₃)
    (hΦ : IsCompletelyPositive Φ) (hΨ : IsCompletelyPositive Ψ) :
    IsCompletelyPositive (Ψ.comp Φ) := by
  refine (isCompletelyPositive_iff_cstarMatrix_nonneg (Ψ.comp Φ)).mpr ?_
  intro k M hM
  have hΦM :
      0 ≤ M.map Φ :=
    (isCompletelyPositive_iff_cstarMatrix_nonneg Φ).mp hΦ k M hM
  have hΨM :
      0 ≤ (M.map Φ).map Ψ :=
    (isCompletelyPositive_iff_cstarMatrix_nonneg Ψ).mp hΨ k (M.map Φ) hΦM
  have hmap : (M.map Φ).map Ψ = M.map (Ψ.comp Φ) := by
    ext i j X
    simp [CStarMatrix.map_apply]
  simpa [hmap] using hΨM

def StinespringRep (Φ : T ℋ₁ ℋ₂) (ℋ₃ : Type u) [Qudit ℋ₃] : Prop :=
  ∃ A : ℋ₁ →ₗ[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃),
    ∀ X : L ℋ₁,
      Φ X =
        (@TrRight ℋ₂ inferInstance ℋ₃ inferInstance
          (((A.comp X).comp
            (LinearMap.adjoint A : (ℋ₂ ⊗[ℂ] ℋ₃) →ₗ[ℂ] ℋ₁)) : L (ℋ₂ ⊗[ℂ] ℋ₃)) : L ℋ₂)

def HasStinespring (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∃ (ℋ₃ : Type u) (_ : Qudit ℋ₃), @StinespringRep ℋ₁ ℋ₂ _ _ Φ ℋ₃ _

def HasRankStinespring (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∃ (ℋ₃ : Type u) (inst : Qudit ℋ₃),
    Module.finrank ℂ ℋ₃ = choiRank b Φ ∧
      @StinespringRep ℋ₁ ℋ₂ _ _ Φ ℋ₃ inst

lemma stinespring_cstarMatrix_nonneg
    {ℋ₃ : Type u} [Qudit ℋ₃]
    (Φ : T ℋ₁ ℋ₂) (hΦ : StinespringRep Φ ℋ₃) :
    ∀ (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) (L ℋ₁)),
      0 ≤ M → 0 ≤ M.map Φ := by
  obtain ⟨A, hA⟩ := hΦ
  let K : T ℋ₁ (ℋ₂ ⊗[ℂ] ℋ₃) := krausTerm A
  have hK : IsCompletelyPositive K := krausTerm_isCompletelyPositive A
  have hTr : IsCompletelyPositive (TrRight (ℋ₂ := ℋ₂) (ℋ₃ := ℋ₃)) := by
    exact TrRight_isCompletelyPositive (stdOrthonormalBasis ℂ ℋ₃)
  have hΦeq : Φ = (TrRight (ℋ₂ := ℋ₂) (ℋ₃ := ℋ₃)).comp K := by
    apply LinearMap.ext
    intro X
    rw [hA X]
    simp [K, krausTerm, LinearMap.comp_assoc]
  have hCP : IsCompletelyPositive Φ := by
    rw [hΦeq]
    exact comp_isCompletelyPositive K (TrRight (ℋ₂ := ℋ₂) (ℋ₃ := ℋ₃)) hK hTr
  exact (isCompletelyPositive_iff_cstarMatrix_nonneg Φ).mp hCP

theorem hasRankStinespring_to_hasStinespring
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankStinespring b Φ → HasStinespring Φ := by
  rintro ⟨ℋ₃, inst, _, hstinespring⟩
  exact ⟨ℋ₃, inst, hstinespring⟩

theorem rankStinespring_to_stinespring
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankStinespring b Φ → HasStinespring Φ :=
  hasRankStinespring_to_hasStinespring b Φ

theorem tensor_to_choi
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    AmplificationPositive Φ → ChoiPositive b Φ := by
  intro hΦ
  exact hΦ (outer_product (vec b (I ℋ₁)) (vec b (I ℋ₁)))
    (outer_product_self_nonneg (vec b (I ℋ₁)))

-- (1) → (2)
theorem cp_to_tensor
    (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → AmplificationPositive Φ := by
  exact cp_amplify Φ

-- (3) → (5)
theorem choi_to_rank_kraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    ChoiPositive b Φ → HasRankKraus b Φ := by
  intro hΦ
  obtain ⟨κ, hκ, hκ', hcard, u, hu⟩ :=
    positive_to_rank_outer_product (choi b Φ) hΦ
  letI : DecidableEq κ := hκ
  letI : Fintype κ := hκ'
  refine ⟨κ, hκ, hκ', ?_, ?_⟩
  · exact hcard
  · exact choi_outer_product_to_kraus b Φ u hu

theorem choi_iff_rank_kraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    ChoiPositive b Φ ↔ HasRankKraus b Φ := by
  exact ⟨choi_to_rank_kraus b Φ, rank_kraus_to_choi b Φ⟩

theorem choi_to_positiveMap
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    ChoiPositive b Φ → IsPositiveMap Φ :=
  rankKraus_to_positiveMap b Φ ∘
    choi_to_rank_kraus b Φ

theorem choi_to_kraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    ChoiPositive b Φ → HasKraus Φ :=
  rankKraus_to_kraus b Φ ∘
    choi_to_rank_kraus b Φ

theorem choi_iff_kraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    ChoiPositive b Φ ↔ HasKraus Φ := by
  exact ⟨choi_to_kraus b Φ, kraus_to_choi b Φ⟩


theorem conjugate_kraus_expansion
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) (X : L ℋ₁) :
    conjugateEnd (TensorProduct.comm ℂ ℋ₂ (EuclideanSpace ℂ κ))
      (((krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A).comp X).comp
        (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))) =
      ∑ a : κ, ∑ b : κ,
        (l_tensor_equiv (ℋ₁ := EuclideanSpace ℂ κ) (ℋ₂ := ℋ₂)).symm
          ((outer_product (EuclideanSpace.basisFun κ ℂ b) (EuclideanSpace.basisFun κ ℂ a)) ⊗ₜ[ℂ]
            ((A a).comp (X.comp (LinearMap.adjoint (A b))))) := by
  classical
  apply TensorProduct.ext'
  intro z y
  rw [← (EuclideanSpace.basisFun κ ℂ).sum_repr' z]
  simp_rw [TensorProduct.sum_tmul]
  simp_rw [← TensorProduct.smul_tmul']
  simp [map_sum, map_smul,
    conjugateEnd_krausToStinespringOperator_apply_single_tmul,
    l_tensor_equiv_symm_outer_product_apply, EuclideanSpace.basisFun_apply]
  simp [outer_product_eq_rankOne, EuclideanSpace.inner_single_left, ite_tmul_zero_left]

theorem trRight_kraus
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) (X : L ℋ₁) :
    TrRight ((((krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A).comp X).comp
      (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A)))) =
      ∑ a : κ, (A a).comp (X.comp (LinearMap.adjoint (A a))) := by
  classical
  dsimp [TrRight]
  rw [conjugate_kraus_expansion (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A X]
  simp [Tr₂_l_tensor_equiv_symm_tmul, trace_outer_product_single, EuclideanSpace.basisFun_apply]

lemma trRight_kraus_positive
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) :
    IsPositiveMap
      { toFun := fun X =>
          TrRight ((((krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A).comp X).comp
            (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))))
        map_add' := by
          intro X Y
          ext y
          simp [LinearMap.comp_add, LinearMap.add_comp]
        map_smul' := by
          intro c X
          ext y
          simp [LinearMap.comp_smul, LinearMap.smul_comp] } := by
  intro X hX
  change 0 ≤ TrRight ((((krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A).comp X).comp
    (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))))
  rw [trRight_kraus (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A X]
  exact Finset.sum_nonneg fun a _ =>
    conjugate_positive (ℋ₁ := ℋ₁) (ℋ₃ := ℋ₂) (A a) X hX
theorem fixed_kraus_to_stinespring
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (Φ : T ℋ₁ ℋ₂) :
    KrausRep Φ κ → StinespringRep Φ (EuclideanSpace ℂ κ) := by
  rintro ⟨A, hA⟩
  refine ⟨krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A, ?_⟩
  intro X
  rw [hA X]
  simpa using (trRight_kraus (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A X).symm

-- (4) → (6)
theorem kraus_to_stinespring
    (Φ : T ℋ₁ ℋ₂) :
    HasKraus Φ → HasStinespring Φ := by
  rintro ⟨κ, hκ, hκ', hΦ⟩
  letI : DecidableEq κ := hκ
  letI : Fintype κ := hκ'
  exact ⟨EuclideanSpace ℂ κ, inferInstance,
    fixed_kraus_to_stinespring (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) Φ hΦ⟩

-- (5) → (7)
theorem rank_kraus_to_rank_stinespring
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankKraus b Φ → HasRankStinespring b Φ := by
  rintro ⟨κ, hκ, hκ', hcard, hΦ⟩
  letI : DecidableEq κ := hκ
  letI : Fintype κ := hκ'
  refine ⟨EuclideanSpace ℂ κ, inferInstance, ?_, ?_⟩
  · rw [finrank_kraus_environment]
    exact hcard
  · exact fixed_kraus_to_stinespring (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) Φ hΦ

theorem choi_to_stinespring
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    ChoiPositive b Φ → HasStinespring Φ :=
  kraus_to_stinespring Φ ∘
    choi_to_kraus b Φ

theorem choi_to_rank_stinespring
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    ChoiPositive b Φ → HasRankStinespring b Φ :=
  rank_kraus_to_rank_stinespring b Φ ∘
    choi_to_rank_kraus b Φ

theorem tensor_to_rank_kraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    AmplificationPositive Φ → HasRankKraus b Φ :=
  choi_to_rank_kraus b Φ ∘
    tensor_to_choi b Φ

theorem tensor_to_kraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    AmplificationPositive Φ → HasKraus Φ :=
  choi_to_kraus b Φ ∘
    tensor_to_choi b Φ

theorem tensor_to_stinespring
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    AmplificationPositive Φ → HasStinespring Φ :=
  choi_to_stinespring b Φ ∘
    tensor_to_choi b Φ

theorem tensor_to_rank_stinespring
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    AmplificationPositive Φ → HasRankStinespring b Φ :=
  choi_to_rank_stinespring b Φ ∘
    tensor_to_choi b Φ

theorem tensor_to_positiveMap
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    AmplificationPositive Φ → IsPositiveMap Φ :=
  choi_to_positiveMap b Φ ∘
    tensor_to_choi b Φ

-- (6) → (1)
theorem stinespring_to_cp
    (Φ : T ℋ₁ ℋ₂) :
    HasStinespring Φ → IsCompletelyPositive Φ := by
  rintro ⟨ℋ₃, inst, hΦ⟩
  letI : Qudit ℋ₃ := inst
  exact (isCompletelyPositive_iff_cstarMatrix_nonneg Φ).mpr
    (stinespring_cstarMatrix_nonneg Φ hΦ)

theorem tensor_to_cp
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    AmplificationPositive Φ → IsCompletelyPositive Φ :=
  stinespring_to_cp Φ ∘
    tensor_to_stinespring b Φ

theorem cp_to_choi
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → ChoiPositive b Φ :=
  tensor_to_choi b Φ ∘
    cp_to_tensor Φ

theorem cp_to_rank_kraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → HasRankKraus b Φ :=
  choi_to_rank_kraus b Φ ∘
    cp_to_choi b Φ

theorem cp_to_kraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → HasKraus Φ :=
  rankKraus_to_kraus b Φ ∘
    cp_to_rank_kraus b Φ

theorem cp_to_stinespring
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → HasStinespring Φ :=
  kraus_to_stinespring Φ ∘
    cp_to_kraus b Φ

theorem cp_to_rank_stinespring
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → HasRankStinespring b Φ :=
  rank_kraus_to_rank_stinespring b Φ ∘
    cp_to_rank_kraus b Φ

theorem choi_to_cp
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    ChoiPositive b Φ → IsCompletelyPositive Φ :=
  stinespring_to_cp Φ ∘
    rankStinespring_to_stinespring b Φ ∘
    rank_kraus_to_rank_stinespring b Φ ∘
    choi_to_rank_kraus b Φ

theorem kraus_to_cp
    (Φ : T ℋ₁ ℋ₂) :
    HasKraus Φ → IsCompletelyPositive Φ := by
  rintro ⟨κ, hκ, hκ', hΦ⟩
  letI : DecidableEq κ := hκ
  letI : Fintype κ := hκ'
  exact fixed_kraus_to_cp Φ hΦ

theorem rank_kraus_to_cp
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankKraus b Φ → IsCompletelyPositive Φ := by
  intro hΦ
  exact kraus_to_cp Φ (rankKraus_to_kraus b Φ hΦ)

theorem rank_stinespring_to_cp
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankStinespring b Φ → IsCompletelyPositive Φ :=
  stinespring_to_cp Φ ∘
    rankStinespring_to_stinespring b Φ

theorem cp_iff_tensor
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis κ ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ ↔ AmplificationPositive Φ := by
  refine ⟨cp_to_tensor Φ, ?_⟩
  intro hTensor
  exact choi_to_cp b Φ
    (tensor_to_choi b Φ hTensor)

theorem cp_iff_choi
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis κ ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ ↔ ChoiPositive b Φ := by
  exact ⟨cp_to_choi b Φ, choi_to_cp b Φ⟩

theorem cp_iff_kraus
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis κ ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ ↔ HasKraus Φ := by
  exact ⟨cp_to_kraus b Φ, kraus_to_cp Φ⟩

theorem cp_iff_rank_kraus
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis κ ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ ↔ HasRankKraus b Φ := by
  exact ⟨cp_to_rank_kraus b Φ,
    rank_kraus_to_cp b Φ⟩

theorem cp_iff_stinespring
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis κ ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ ↔ HasStinespring Φ := by
  exact ⟨cp_to_stinespring b Φ,
    stinespring_to_cp Φ⟩

theorem cp_iff_rank_stinespring
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis κ ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ ↔ HasRankStinespring b Φ := by
  exact ⟨cp_to_rank_stinespring b Φ,
    rank_stinespring_to_cp b Φ⟩


-- Theorem 2.26 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudits ℋ₁, ℋ₂, and any Φ ∈ T(ℋ₁,ℋ₂), the following statements are equivalent:
-- 1: Φ is a trace-preserving ContinuosLinearMap;
-- 2: Tr₂[J(Φ)] = I(ℋ₁);
-- 3: ∃qudit ℋ₃, ∃A,B∈(ℋ₁→L[ℂ]ℋ₂⊗ℋ₃), Φ(X)=Tr₃[A X B†] ∧ A† B = I(ℋ₁)

-- Corollary 2.27 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudits ℋ₁, ℋ₂, and any Φ ∈ T(ℋ₁,ℋ₂), the following statements are equivalent:
-- 1: Φ ∈ C(ℋ₁,ℋ₂);
-- 2: J(Φ)∈ Pos(ℋ₂⊗ℋ₁) ∧ Tr₂[J(Φ)] = I(ℋ₁);
-- 3: ∃qudit ℋ₃, ∃A∈(ℋ₁→L[ℂ]ℋ₂⊗ℋ₃), Φ(X)=Tr₃[A X A†] ∧ A† A = I(ℋ₁)

end RepresentationsOfChannels

end QuantumChannel
