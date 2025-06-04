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

variable (dIn dOut R : Type*) (𝕜 : Type := ℂ)
variable [Fintype dIn] [Fintype dOut]
variable [Semiring R] [RCLike 𝕜]

/-- Hermitian-preserving linear maps. -/
structure HPMap extends MatrixMap dIn dOut 𝕜 where
  HP : MatrixMap.IsHermitianPreserving toLinearMap

/-- Unital linear maps. -/
structure UnitalMap [DecidableEq dIn] [DecidableEq dOut] extends MatrixMap dIn dOut R where
  unital : MatrixMap.Unital toLinearMap

/-- Trace-preserving linear maps. -/
structure TPMap extends MatrixMap dIn dOut R where
  TP : MatrixMap.IsTracePreserving toLinearMap

--Mark this as [simp] so that simp lemmas requiring `IsTracePreserving` can pick it up.
--In theory this could be making "IsTracePreserving" a typeclass ... or more realistically,
--defining a `TracePreservingClass` similar to `AddHomClass`
attribute [simp] TPMap.TP

/-- Positive linear maps. -/
structure PMap extends HPMap dIn dOut 𝕜 where
  pos : MatrixMap.IsPositive toLinearMap
  HP := pos.IsHermitianPreserving

/-- Completely positive linear maps. -/
structure CPMap [DecidableEq dIn] extends PMap dIn dOut 𝕜 where
  cp : MatrixMap.IsCompletelyPositive toLinearMap
  pos := cp.IsPositive

/-- Positive trace-preserving linear maps. These includes all channels, but aren't
  necessarily *completely* positive, see `CPTPMap`. -/
structure PTPMap extends PMap dIn dOut 𝕜, TPMap dIn dOut 𝕜

attribute [simp] PTPMap.TP

/-- Completely positive trace-preserving linear maps. This is the most common
  meaning of "channel", often described as "the most general physically realizable
  quantum operation". -/
structure CPTPMap [DecidableEq dIn] extends PTPMap dIn dOut (𝕜 := 𝕜), CPMap dIn dOut 𝕜 where

/-- Completely positive unital maps. These are important because they are the
  dual to `CPTPMap`: they are the most general way to map *observables*. -/
structure CPUMap [DecidableEq dIn] [DecidableEq dOut] extends CPMap dIn dOut 𝕜, UnitalMap dIn dOut 𝕜

variable {dIn dOut R} {𝕜 : Type} [RCLike 𝕜]

--Hermitian-presering maps: continuous linear maps on HermitianMats.
namespace HPMap
omit [Fintype dIn] [Fintype dOut]

abbrev map (M : HPMap dIn dOut 𝕜) : MatrixMap dIn dOut 𝕜 := M.toLinearMap

@[ext]
theorem ext {Λ₁ Λ₂ : HPMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rwa [HPMap.mk.injEq]

/-- Hermitian-preserving maps are functions from `HermitianMat`s to `HermitianMat`s. -/
instance instFunLike : FunLike (HPMap dIn dOut 𝕜) (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
  coe Λ ρ := ⟨Λ.map ρ.1, Λ.HP ρ.2⟩
  coe_injective' _ _ h := by
    sorry --Requires the fact the action on HermitianMat's determines action on all matrices

instance instLinearMapClass : LinearMapClass (HPMap dIn dOut 𝕜) ℝ (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.toLinearMap x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp [instFunLike]

instance instContinuousMapClass : ContinuousMapClass (HPMap dIn dOut 𝕜) (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
  map_continuous f :=
    Continuous.subtype_mk (f.map.continuous_of_finiteDimensional.comp continuous_subtype_val) _

end HPMap


--Positive-preserving maps: continuous linear order-preserving maps on HermitianMats.
namespace PMap

@[ext]
theorem ext {Λ₁ Λ₂ : PMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [PMap.mk.injEq]
  exact HPMap.ext h

theorem injective_toHPMap : (PMap.toHPMap (dIn := dIn) (dOut := dOut) (𝕜 := 𝕜)).Injective :=
  fun _ _ ↦ (mk.injEq _ _ _ _).mpr

/-- Positive maps are functions from `HermitianMat`s to `HermitianMat`s. -/
instance instFunLike : FunLike (PMap dIn dOut 𝕜) (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
  coe := DFunLike.coe ∘ toHPMap
  coe_injective' := DFunLike.coe_injective'.comp injective_toHPMap

instance instLinearMapClass : LinearMapClass (PMap dIn dOut 𝕜) ℝ (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.toLinearMap x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp [instFunLike]

instance instContinuousOrderHomClass : ContinuousOrderHomClass (PMap dIn dOut 𝕜)
    (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
  map_continuous f := ContinuousMapClass.map_continuous f.toHPMap
  map_monotone f x y h := by
    simpa using f.pos h

/-- Positive-presering maps also preserve positivity on, specifically, Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : PMap dIn dOut 𝕜) {x : HermitianMat dIn 𝕜} (h : 0 ≤ x) : 0 ≤ M x := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

end PMap


--Positive trace-preserving maps:
--  * Continuous linear order-preserving maps on HermitianMats.
--  * Continuous maps on MStates.
namespace PTPMap

@[ext]
theorem ext {Λ₁ Λ₂ : PTPMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [PTPMap.mk.injEq]
  exact PMap.ext h

theorem injective_toPMap : (PTPMap.toPMap (dIn := dIn) (dOut := dOut) (𝕜 := 𝕜)).Injective :=
  fun _ _ ↦ (mk.injEq _ _ _ _).mpr

/-- Positive trace-preserving maps are functions from `HermitianMat`s to `HermitianMat`s. -/
instance instHFunLike : FunLike (PTPMap dIn dOut 𝕜) (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
  coe := DFunLike.coe ∘ toPMap
  coe_injective' := DFunLike.coe_injective'.comp injective_toPMap

set_option synthInstance.maxHeartbeats 40000 in
instance instLinearMapClass : LinearMapClass (PTPMap dIn dOut 𝕜) ℝ (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
  map_add f x y := by simp [instHFunLike]
  map_smulₛₗ f c x := by simp [instHFunLike]

instance instHContinuousOrderHomClass : ContinuousOrderHomClass (PTPMap dIn dOut 𝕜)
    (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
  map_continuous f := ContinuousMapClass.map_continuous f.toPMap
  map_monotone f x y h := by
    simpa using f.pos h

/-- PTP maps also preserve positivity on Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : PTPMap dIn dOut 𝕜) {x : HermitianMat dIn 𝕜} (h : 0 ≤ x) : 0 ≤ M x := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

/-- `PTPMap`s are functions from `MState`s to `MState`s. -/
instance instMFunLike [DecidableEq dIn] [DecidableEq dOut] :
    FunLike (PTPMap dIn dOut) (MState dIn) (MState dOut) where
  coe Λ ρ := MState.mk
    (Λ.toHPMap ρ.M) (HermitianMat.zero_le_iff.mpr (Λ.pos ρ.pos)) (by
      rw [HermitianMat.trace_eq_one_iff, ← ρ.tr']
      exact Λ.TP ρ)
  coe_injective' _ _ h := by
    sorry --Requires the fact the action on MStates determines action on all matrices

instance instMContinuousMapClass [DecidableEq dIn] [DecidableEq dOut] :
    ContinuousMapClass (PTPMap dIn dOut) (MState dIn) (MState dOut) where
  map_continuous f := by
    simp only [instMFunLike, MState.instTopoMState]
    rw [continuous_induced_rng]
    change Continuous (HermitianMat.toMat ∘ (f.toHPMap) ∘ MState.M)
    refine (Continuous.comp ?_ ?_).subtype_val
    · exact map_continuous f.toHPMap
    · exact MState.Continuous_Matrix

-- @[norm_cast]
theorem val_apply_MState [DecidableEq dIn] (M : PTPMap dIn dOut) (ρ : MState dIn) :
    (M ρ : HermitianMat dOut ℂ) = (instHFunLike.coe M) ρ := by
  rfl

--If we have a PTPMap, the input and output dimensions are always both nonempty (otherwise
--we can't preserve trace) - or they're both empty. So `[Nonempty dIn]` will always suffice.
-- This would be nice as an `instance` but that would leave `dIn` as a metavariable.
theorem nonemptyOut (Λ : PTPMap dIn dOut) [hIn : Nonempty dIn] [DecidableEq dIn] : Nonempty dOut := by
  by_contra h
  simp only [not_nonempty_iff] at h
  let M := (1 : Matrix dIn dIn ℂ)
  have := calc (Finset.univ.card (α := dIn) : ℂ)
    _ = M.trace := by simp [Matrix.trace, M]
    _ = (Λ.map M).trace := (Λ.TP M).symm
    _ = 0 := by simp only [Matrix.trace_eq_zero_of_isEmpty]
  norm_num [Finset.univ_eq_empty_iff] at this

end PTPMap

namespace CPTPMap
variable [DecidableEq dIn]

/-- Two `CPTPMap`s are equal if their `MatrixMap`s are equal. -/
@[ext]
theorem ext {Λ₁ Λ₂ : CPTPMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [CPTPMap.mk.injEq]
  exact PTPMap.ext h

theorem injective_toPTPMap : (CPTPMap.toPTPMap (dIn := dIn) (dOut := dOut) (𝕜 := 𝕜)).Injective :=
  fun _ _ ↦ (mk.injEq _ _ _ _).mpr

-- /-- Positive trace-preserving maps are functions from `HermitianMat`s to `HermitianMat`s. -/
-- instance instHFunLike : FunLike (CPTPMap dIn dOut 𝕜) (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
--   coe :=  DFunLike.coe ∘ toPTPMap
--   coe_injective' := DFunLike.coe_injective'.comp injective_toPTPMap

-- set_option synthInstance.maxHeartbeats 40000 in
-- instance instHLinearMapClass : LinearMapClass (CPTPMap dIn dOut 𝕜) ℝ (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
--   map_add f x y := by simp [instHFunLike]
--   map_smulₛₗ f c x := by simp [instHFunLike]

-- instance instHContinuousOrderHomClass : ContinuousOrderHomClass (CPTPMap dIn dOut 𝕜)
--     (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
--   map_continuous f := ContinuousMapClass.map_continuous f.toPMap
--   map_monotone f x y h := by
    -- simpa using f.pos h

-- /-- PTP maps also preserve positivity on Hermitian matrices. -/
-- @[simp]
-- theorem pos_Hermitian (M : CPTPMap dIn dOut 𝕜) {x : HermitianMat dIn 𝕜} (h : 0 ≤ x) : 0 ≤ M x := by
--   simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

/-- `CPTPMap`s are functions from `MState`s to `MState`s. -/
instance instMFunLike [DecidableEq dOut] : FunLike (CPTPMap dIn dOut) (MState dIn) (MState dOut) where
  coe := DFunLike.coe ∘ toPTPMap
  coe_injective' := DFunLike.coe_injective'.comp injective_toPTPMap

-- @[norm_cast]
-- theorem val_apply_MState [DecidableEq dOut] (M : CPTPMap dIn dOut) (ρ : MState dIn) :
--     (M ρ : HermitianMat dOut ℂ) = (instHFunLike.coe M) ρ := by
--   rfl

@[simp]
theorem IsTracePreserving (Λ : CPTPMap dIn dOut 𝕜) : Λ.map.IsTracePreserving :=
  Λ.TP

end CPTPMap

namespace CPUMap
variable [DecidableEq dIn] [DecidableEq dOut]

@[ext]
theorem ext {Λ₁ Λ₂ : CPUMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [CPUMap.mk.injEq, CPMap.mk.injEq]
  exact PMap.ext h

theorem injective_toPMap : (CPMap.toPMap ∘ CPUMap.toCPMap (dIn := dIn) (dOut := dOut) (𝕜 := 𝕜)).Injective := by
  intro _ _ _
  rwa [CPUMap.mk.injEq, CPMap.mk.injEq]

/-- `CPUMap`s are functions from `HermitianMat`s to `HermitianMat`s. -/
instance instFunLike : FunLike (CPUMap dIn dOut 𝕜) (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
  coe Λ := Λ.toPMap
  coe_injective' := (DFunLike.coe_injective' (F := PMap dIn dOut 𝕜)).comp injective_toPMap

instance instLinearMapClass : LinearMapClass (CPUMap dIn dOut 𝕜) ℝ (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.toLinearMap x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp [instFunLike]

instance instHContinuousOrderHomClass : ContinuousOrderHomClass (CPUMap dIn dOut 𝕜)
    (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
  map_continuous f := ContinuousMapClass.map_continuous f.toPMap
  map_monotone f x y h := by
    simpa using f.pos h

instance instOneHomClass : OneHomClass (CPUMap dIn dOut 𝕜)
    (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
  map_one f := HermitianMat.ext (f.unital)

/-- CPTP maps also preserve positivity on Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : CPUMap dIn dOut 𝕜) {x : HermitianMat dIn 𝕜} (h : 0 ≤ x) : 0 ≤ M x := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

end CPUMap


--Tests to make sure that our `simp`s and classe are all working like we want them too

section test
variable [DecidableEq dIn] [DecidableEq dOut]

#guard_msgs in
example (M : HPMap dIn dOut 𝕜) : (M (Real.pi • 1)) = Real.pi • M 1 := by simp

#guard_msgs in
example (M : PTPMap dIn dOut 𝕜) : (M (Real.pi • 1)) = Real.pi • M 1 := by simp

#guard_msgs in
example (M : CPTPMap dIn dOut 𝕜) (ρ : Matrix dIn dIn 𝕜) : (M.map ρ).trace = ρ.trace := by simp

#guard_msgs in
example (M : CPUMap dIn dOut ℂ) (T : HermitianMat dIn ℂ) : M (1 + 2 • T) = 1 + 2 • M T := by simp

end test
