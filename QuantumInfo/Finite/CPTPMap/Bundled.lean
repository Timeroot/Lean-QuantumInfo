import QuantumInfo.Finite.CPTPMap.Unbundled
import QuantumInfo.Finite.MState

import Mathlib.Topology.Order.Hom.Basic

/-! # Classes of Matrix Maps

The bundled `MatrixMap`s: `HPMap`, `UnitalMap`, `TPMap`, `PMap`, and `CPMap`.
These are defined over the bare minimum rings (`Semiring` or `RCLike`, respectively).

The combinations `PTPMap` (positive trace-preserving), `CPTPMap`, and `CPUMap`
(CP unital maps) take ℂ as the default class.

The majority of quantum theory revolves around `CPTPMap`s, so those are explored more
thoroughly in their file CPTP.lean.
-/

variable (d₁ d₂ R : Type*) (𝕜 : Type*)
variable [Fintype d₁] [Fintype d₂]
variable [Semiring R] [RCLike 𝕜]

/-- Hermitian-preserving linear maps. -/
structure HPMap extends MatrixMap d₁ d₂ 𝕜 where
  HP : MatrixMap.IsHermitianPreserving toLinearMap

notation:25 d₁ " →HP[" 𝕜 "] " d₂ => HPMap d₁ d₂ 𝕜

notation:25 d₁ " →HP " d₂ => HPMap d₁ d₂ ℂ

/-- `HermitianPreservingClass F α β 𝕜` states that `F` preserves Hermitian matrices over `𝕜`.

You should extend this class when you extend `HPMap`. -/
class HermitianPreservingClass (F : Type*) (α β 𝕜 : outParam Type*) [RCLike 𝕜]
    [FunLike F (Matrix α α 𝕜) (Matrix β β 𝕜)] extends LinearMapClass F 𝕜 (Matrix α α 𝕜) (Matrix β β 𝕜) where
  isHermitianPreserving (f : F) : MatrixMap.IsHermitianPreserving (LinearMapClass.linearMap f)

--Hermitian-presering maps: continuous linear maps on HermitianMats.
namespace HPMap

variable {d₁ d₂ R : Type*} {𝕜 : Type} [RCLike 𝕜]

attribute [coe] HPMap.toLinearMap
/-- Coerce Hermitian preserving maps to linear maps. -/
instance LinearMap.coe : Coe (d₁ →HP[𝕜] d₂) (MatrixMap d₁ d₂ 𝕜) := ⟨toLinearMap⟩

@[ext]
theorem ext {Λ₁ Λ₂ : HPMap d₁ d₂ 𝕜} (h : Λ₁.toLinearMap = Λ₂) : Λ₁ = Λ₂ := by
  rwa [HPMap.mk.injEq]

-- /-- Hermitian-preserving maps are functions from `Matrix`s to `Matrix`s. -/
-- instance instMFunLike : FunLike (HPMap d₁ d₂ 𝕜) (Matrix d₁ d₁ 𝕜) (Matrix d₂ d₂ 𝕜) where
--   coe Λ := Λ.map
--   coe_injective' _ _ h := ext (by rwa [DFunLike.coe_fn_eq] at h)

-- instance instMLinearMapClass : LinearMapClass (HPMap d₁ d₂ 𝕜) 𝕜 (Matrix d₁ d₁ 𝕜) (Matrix d₂ d₂ 𝕜) where
--   map_add f x y := LinearMap.map_add f.toLinearMap x y
--   map_smulₛₗ f c x := by simp [instMFunLike]

-- instance : HermitianPreservingClass (HPMap d₁ d₂ 𝕜) d₁ d₂ 𝕜 where
--   isHermitianPreserving Λ := Λ.HP

end HPMap

namespace HermitianPreservingClass

variable (F : Type*) [FunLike F (Matrix d₁ d₁ 𝕜) (Matrix d₂ d₂ 𝕜)]

instance [HermitianPreservingClass F d₁ d₂ 𝕜] : FunLike F (HermitianMat d₁ 𝕜) (HermitianMat d₂ 𝕜) where
  coe Λ ρ := ⟨Λ.map ρ.1, Λ.HP ρ.2⟩
  coe_injective' _ _ h := by
    sorry --Requires the fact the action on HermitianMat's determines action on all matrices

/-- Hermitian-preserving maps are functions from `Matrix`s to `Matrix`s. -/
instance instHFunLike : FunLike (HPMap d₁ d₂ 𝕜) (HermitianMat d₁ 𝕜) (HermitianMat d₂ 𝕜) where
  coe Λ := Λ.map
  coe_injective' _ _ h := by
    sorry --Requires the fact the action on HermitianMat's determines action on all matrices

instance instHLinearMapClass : LinearMapClass (HPMap d₁ d₂ 𝕜) ℝ (HermitianMat d₁ 𝕜) (HermitianMat d₂ 𝕜) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.toLinearMap x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp [instFunLike]

instance instContinuousMapClass : ContinuousMapClass (HPMap d₁ d₂ 𝕜) (HermitianMat d₁ 𝕜) (HermitianMat d₂ 𝕜) where
  map_continuous f :=
    Continuous.subtype_mk (f.map.continuous_of_finiteDimensional.comp continuous_subtype_val) _

end HermitianPreservingClass

/-- Trace-preserving linear maps. -/
structure TPMap extends MatrixMap d₁ d₂ R where
  TP : MatrixMap.IsTracePreserving toLinearMap

/-- Positive linear maps. -/
structure PMap extends HPMap d₁ d₂ 𝕜 where
  pos : Monotone toLinearMap
  HP := MatrixMap.Monotone.IsHermitianPreserving pos

/-- Completely positive linear maps. -/
structure CPMap [DecidableEq d₁] extends PMap d₁ d₂ 𝕜 where
  cp : MatrixMap.IsCompletelyPositive toLinearMap
  pos := cp.Monotone

/-- Positive trace-preserving linear maps. These includes all channels, but aren't
  necessarily *completely* positive, see `CPTPMap`. -/
structure PTPMap extends PMap d₁ d₂ 𝕜, TPMap d₁ d₂ 𝕜

attribute [simp] PTPMap.TP

/-- Completely positive trace-preserving linear maps. This is the most common
  meaning of "channel", often described as "the most general physically realizable
  quantum operation". -/
structure CPTPMap [DecidableEq d₁] extends PTPMap d₁ d₂ (𝕜 := 𝕜), CPMap d₁ d₂ 𝕜

/-- Completely positive unital maps. These are important because they are the
  dual to `CPTPMap`: they are the most general way to map *observables*. -/
structure CPUMap [DecidableEq d₁] [DecidableEq d₂] extends CPMap d₁ d₂ 𝕜,
  OneHom (Matrix d₁ d₁ 𝕜) (Matrix d₂ d₂ 𝕜)


--Positive-preserving maps: continuous linear order-preserving maps on HermitianMats.
namespace PMap

@[ext]
theorem ext {Λ₁ Λ₂ : PMap d₁ d₂ 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [PMap.mk.injEq]
  exact HPMap.ext h

theorem injective_toHPMap : (PMap.toHPMap (d₁ := d₁) (d₂ := d₂) (𝕜 := 𝕜)).Injective :=
  fun _ _ ↦ (mk.injEq _ _ _ _).mpr

/-- Positive maps are functions from `HermitianMat`s to `HermitianMat`s. -/
instance instFunLike : FunLike (PMap d₁ d₂ 𝕜) (HermitianMat d₁ 𝕜) (HermitianMat d₂ 𝕜) where
  coe := DFunLike.coe ∘ toHPMap
  coe_injective' := DFunLike.coe_injective'.comp injective_toHPMap

instance instLinearMapClass : LinearMapClass (PMap d₁ d₂ 𝕜) ℝ (HermitianMat d₁ 𝕜) (HermitianMat d₂ 𝕜) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.toLinearMap x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp [instFunLike]

instance instContinuousOrderHomClass : ContinuousOrderHomClass (PMap d₁ d₂ 𝕜)
    (HermitianMat d₁ 𝕜) (HermitianMat d₂ 𝕜) where
  map_continuous f := ContinuousMapClass.map_continuous f.toHPMap
  map_monotone f x y h := by
    simpa using f.pos h

/-- Positive-presering maps also preserve positivity on, specifically, Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : PMap d₁ d₂ 𝕜) {x : HermitianMat d₁ 𝕜} (h : 0 ≤ x) : 0 ≤ M x := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

end PMap


--Positive trace-preserving maps:
--  * Continuous linear order-preserving maps on HermitianMats.
--  * Continuous maps on MStates.
namespace PTPMap

@[ext]
theorem ext {Λ₁ Λ₂ : PTPMap d₁ d₂ 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [PTPMap.mk.injEq]
  exact PMap.ext h

theorem injective_toPMap : (PTPMap.toPMap (d₁ := d₁) (d₂ := d₂) (𝕜 := 𝕜)).Injective :=
  fun _ _ ↦ (mk.injEq _ _ _ _).mpr

/-- Positive trace-preserving maps are functions from `HermitianMat`s to `HermitianMat`s. -/
instance instHFunLike : FunLike (PTPMap d₁ d₂ 𝕜) (HermitianMat d₁ 𝕜) (HermitianMat d₂ 𝕜) where
  coe := DFunLike.coe ∘ toPMap
  coe_injective' := DFunLike.coe_injective'.comp injective_toPMap

set_option synthInstance.maxHeartbeats 40000 in
instance instLinearMapClass : LinearMapClass (PTPMap d₁ d₂ 𝕜) ℝ (HermitianMat d₁ 𝕜) (HermitianMat d₂ 𝕜) where
  map_add f x y := by simp [instHFunLike]
  map_smulₛₗ f c x := by simp [instHFunLike]

instance instHContinuousOrderHomClass : ContinuousOrderHomClass (PTPMap d₁ d₂ 𝕜)
    (HermitianMat d₁ 𝕜) (HermitianMat d₂ 𝕜) where
  map_continuous f := ContinuousMapClass.map_continuous f.toPMap
  map_monotone f x y h := by
    simpa using f.pos h

/-- PTP maps also preserve positivity on Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : PTPMap d₁ d₂ 𝕜) {x : HermitianMat d₁ 𝕜} (h : 0 ≤ x) : 0 ≤ M x := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

/-- `PTPMap`s are functions from `MState`s to `MState`s. -/
instance instMFunLike [DecidableEq d₁] [DecidableEq d₂] :
    FunLike (PTPMap d₁ d₂) (MState d₁) (MState d₂) where
  coe Λ ρ := MState.mk
    (Λ.toHPMap ρ.M) (HermitianMat.zero_le_iff.mpr (Λ.pos ρ.pos)) (ρ.tr ▸ Λ.TP ρ.m)
  coe_injective' _ _ h := by
    sorry --Requires the fact the action on MStates determines action on all matrices

instance instMContinuousMapClass [DecidableEq d₁] [DecidableEq d₂] :
    ContinuousMapClass (PTPMap d₁ d₂) (MState d₁) (MState d₂) where
  map_continuous f := by
    simp only [instMFunLike, MState.instTopoMState]
    rw [continuous_induced_rng]
    change Continuous (HermitianMat.toMat ∘ (f.toHPMap) ∘ MState.M)
    refine (Continuous.comp ?_ ?_).subtype_val
    · exact map_continuous f.toHPMap
    · exact MState.Continuous_Matrix

-- @[norm_cast]
theorem val_apply_MState [DecidableEq d₁] (M : PTPMap d₁ d₂) (ρ : MState d₁) :
    (M ρ : HermitianMat d₂ ℂ) = (instHFunLike.coe M) ρ := by
  rfl

--If we have a PTPMap, the input and output dimensions are always both nonempty (otherwise
--we can't preserve trace) - or they're both empty. So `[Nonempty d₁]` will always suffice.
-- This would be nice as an `instance` but that would leave `d₁` as a metavariable.
theorem nonemptyOut (Λ : PTPMap d₁ d₂) [hIn : Nonempty d₁] [DecidableEq d₁] : Nonempty d₂ := by
  by_contra h
  simp only [not_nonempty_iff] at h
  let M := (1 : Matrix d₁ d₁ ℂ)
  have := calc (Finset.univ.card (α := d₁) : ℂ)
    _ = M.trace := by simp [Matrix.trace, M]
    _ = (Λ.map M).trace := (Λ.TP M).symm
    _ = 0 := by simp only [Matrix.trace_eq_zero_of_isEmpty]
  norm_num [Finset.univ_eq_empty_iff] at this

end PTPMap

namespace CPTPMap
variable [DecidableEq d₁]

/-- Two `CPTPMap`s are equal if their `MatrixMap`s are equal. -/
@[ext]
theorem ext {Λ₁ Λ₂ : CPTPMap d₁ d₂ 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [CPTPMap.mk.injEq]
  exact PTPMap.ext h

theorem injective_toPTPMap : (CPTPMap.toPTPMap (d₁ := d₁) (d₂ := d₂) (𝕜 := 𝕜)).Injective :=
  fun _ _ ↦ (mk.injEq _ _ _ _).mpr

-- /-- Positive trace-preserving maps are functions from `HermitianMat`s to `HermitianMat`s. -/
-- instance instHFunLike : FunLike (CPTPMap d₁ d₂ 𝕜) (HermitianMat d₁ 𝕜) (HermitianMat d₂ 𝕜) where
--   coe :=  DFunLike.coe ∘ toPTPMap
--   coe_injective' := DFunLike.coe_injective'.comp injective_toPTPMap

-- set_option synthInstance.maxHeartbeats 40000 in
-- instance instHLinearMapClass : LinearMapClass (CPTPMap d₁ d₂ 𝕜) ℝ (HermitianMat d₁ 𝕜) (HermitianMat d₂ 𝕜) where
--   map_add f x y := by simp [instHFunLike]
--   map_smulₛₗ f c x := by simp [instHFunLike]

-- instance instHContinuousOrderHomClass : ContinuousOrderHomClass (CPTPMap d₁ d₂ 𝕜)
--     (HermitianMat d₁ 𝕜) (HermitianMat d₂ 𝕜) where
--   map_continuous f := ContinuousMapClass.map_continuous f.toPMap
--   map_monotone f x y h := by
    -- simpa using f.pos h

-- /-- PTP maps also preserve positivity on Hermitian matrices. -/
-- @[simp]
-- theorem pos_Hermitian (M : CPTPMap d₁ d₂ 𝕜) {x : HermitianMat d₁ 𝕜} (h : 0 ≤ x) : 0 ≤ M x := by
--   simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

/-- `CPTPMap`s are functions from `MState`s to `MState`s. -/
instance instMFunLike [DecidableEq d₂] : FunLike (CPTPMap d₁ d₂) (MState d₁) (MState d₂) where
  coe := DFunLike.coe ∘ toPTPMap
  coe_injective' := DFunLike.coe_injective'.comp injective_toPTPMap

-- @[norm_cast]
-- theorem val_apply_MState [DecidableEq d₂] (M : CPTPMap d₁ d₂) (ρ : MState d₁) :
--     (M ρ : HermitianMat d₂ ℂ) = (instHFunLike.coe M) ρ := by
--   rfl

@[simp]
theorem IsTracePreserving (Λ : CPTPMap d₁ d₂ 𝕜) : Λ.map.IsTracePreserving :=
  Λ.TP

end CPTPMap

namespace CPUMap
variable [DecidableEq d₁] [DecidableEq d₂]

@[ext]
theorem ext {Λ₁ Λ₂ : CPUMap d₁ d₂ 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [CPUMap.mk.injEq, CPMap.mk.injEq]
  exact PMap.ext h

theorem injective_toPMap : (CPMap.toPMap ∘ CPUMap.toCPMap (d₁ := d₁) (d₂ := d₂) (𝕜 := 𝕜)).Injective := by
  intro _ _ _
  rwa [CPUMap.mk.injEq, CPMap.mk.injEq]

/-- `CPUMap`s are functions from `HermitianMat`s to `HermitianMat`s. -/
instance instFunLike : FunLike (CPUMap d₁ d₂ 𝕜) (HermitianMat d₁ 𝕜) (HermitianMat d₂ 𝕜) where
  coe Λ := Λ.toPMap
  coe_injective' := (DFunLike.coe_injective' (F := PMap d₁ d₂ 𝕜)).comp injective_toPMap

instance instLinearMapClass : LinearMapClass (CPUMap d₁ d₂ 𝕜) ℝ (HermitianMat d₁ 𝕜) (HermitianMat d₂ 𝕜) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.toLinearMap x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp [instFunLike]

instance instHContinuousOrderHomClass : ContinuousOrderHomClass (CPUMap d₁ d₂ 𝕜)
    (HermitianMat d₁ 𝕜) (HermitianMat d₂ 𝕜) where
  map_continuous f := ContinuousMapClass.map_continuous f.toPMap
  map_monotone f x y h := by
    simpa using f.pos h

instance instOneHomClass : OneHomClass (CPUMap d₁ d₂ 𝕜)
    (HermitianMat d₁ 𝕜) (HermitianMat d₂ 𝕜) where
  map_one f := HermitianMat.ext (f.unital)

/-- CPTP maps also preserve positivity on Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : CPUMap d₁ d₂ 𝕜) {x : HermitianMat d₁ 𝕜} (h : 0 ≤ x) : 0 ≤ M x := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

end CPUMap


--Tests to make sure that our `simp`s and classe are all working like we want them too

section test
variable [DecidableEq d₁] [DecidableEq d₂]

#guard_msgs in
example (M : HPMap d₁ d₂ 𝕜) : (M (Real.pi • 1)) = Real.pi • M 1 := by simp

#guard_msgs in
example (M : PTPMap d₁ d₂ 𝕜) : (M (Real.pi • 1)) = Real.pi • M 1 := by simp

#guard_msgs in
example (M : CPTPMap d₁ d₂ 𝕜) (ρ : Matrix d₁ d₁ 𝕜) : (M.map ρ).trace = ρ.trace := by simp

#guard_msgs in
example (M : CPUMap d₁ d₂ ℂ) (T : HermitianMat d₁ ℂ) : M (1 + 2 • T) = 1 + 2 • M T := by simp

end test
