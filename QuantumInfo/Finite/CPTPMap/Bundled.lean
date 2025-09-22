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

--PULLOUT
open ComplexOrder in
theorem Matrix.PosSemidef.trace_pos {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) (h : A ≠ 0) : 0 < A.trace := by
  classical
  apply hA.trace_nonneg.lt_of_ne'
  rw [hA.left.trace_eq_sum_eigenvalues]
  suffices ∑ i, hA.left.eigenvalues i ≠ 0 from mod_cast this
  rwa [ne_eq, Fintype.sum_eq_zero_iff_of_nonneg hA.eigenvalues_nonneg,
    hA.left.eigenvalues_eq_zero_iff]

--PULLOUT
open ComplexOrder in
theorem HermitianMat.trace_pos {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜]
    {A : HermitianMat n 𝕜} (hA : 0 < A) : 0 < A.trace := by
  have hA' := hA.le
  rw [HermitianMat.zero_le_iff] at hA'
  have h_pos := Matrix.PosSemidef.trace_pos hA' (by simpa using hA.ne')
  rw [HermitianMat.trace_eq_re_trace]
  rw [RCLike.pos_iff] at h_pos
  exact h_pos.left

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
variable {Λ₁ Λ₂ : HPMap dIn dOut 𝕜}
variable {CΛ₁ CΛ₂ : HPMap dIn dOut ℂ}

abbrev map (M : HPMap dIn dOut 𝕜) : MatrixMap dIn dOut 𝕜 := M.toLinearMap

@[ext]
theorem ext (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rwa [HPMap.mk.injEq]

/-- Two maps are equal if they agree on all Hermitian inputs. -/
theorem funext_hermitian (h : ∀ M : HermitianMat dIn ℂ, CΛ₁.map M = CΛ₂.map M) :
    CΛ₁ = CΛ₂ := by
  ext M : 2
  have hH := h (realPart M)
  have hA := h (imaginaryPart M)
  convert congr($hH + Complex.I • $hA)
  <;> rw (occs := [1]) [← realPart_add_I_smul_imaginaryPart M, map_add, map_smul]


/-- Two maps are equal if they agree on all positive inputs. -/
theorem funext_pos [Fintype dIn] (h : ∀ M : HermitianMat dIn ℂ, 0 ≤ M → CΛ₁.map M = CΛ₂.map M) :
    CΛ₁ = CΛ₂ := by
  classical
  open scoped HermitianMat in
  apply funext_hermitian
  intro M
  have hPos := h M⁺ M.zero_le_posPart
  have hNeg := h M⁻ M.negPart_le_zero --TODO: this is named incorrectly
  rw [← M.posPart_add_negPart]
  simp [hPos, hNeg]

/-- Two maps are equal if they agree on all positive inputs with trace one -/
theorem funext_pos_trace [Fintype dIn]
  (h : ∀ M : HermitianMat dIn ℂ, 0 ≤ M → M.trace = 1 → CΛ₁.map M = CΛ₂.map M) :
    CΛ₁ = CΛ₂ := by
  apply funext_pos
  intro M hM'
  rcases hM'.eq_or_lt with rfl | hM
  · simp
  have h_tr : 0 < M.trace := M.trace_pos hM
  have := h (M.trace⁻¹ • M) ?_ ?_
  · simp only [selfAdjoint.val_smul, LinearMap.map_smul_of_tower] at this
    convert congr(M.trace • $this)
    · rw [smul_smul]
      field_simp
      simp
    · rw [smul_smul]
      field_simp
      simp
  · apply smul_nonneg (by positivity) hM'
  · simp [field]

/-- Two maps are equal if they agree on all `MState`s. -/
theorem funext_mstate [Fintype dIn] [DecidableEq dIn] {Λ₁ Λ₂ : HPMap dIn dOut ℂ}
  (h : ∀ ρ : MState dIn, Λ₁.map ρ.m = Λ₂.map ρ.m) :
    Λ₁ = Λ₂ :=
  funext_pos_trace fun M hM_pos hM_tr ↦ h ⟨M, hM_pos, hM_tr⟩

/-- Hermitian-preserving maps are functions from `HermitianMat`s to `HermitianMat`s. -/
instance instFunLike : FunLike (HPMap dIn dOut ℂ) (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  coe Λ ρ := ⟨Λ.map ρ.1, Λ.HP ρ.2⟩
  coe_injective' x y h := funext_hermitian fun M ↦
    by simpa using congrFun h M

instance : ContinuousLinearMapClass
    (HPMap dIn dOut ℂ) ℝ (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.toLinearMap x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp [instFunLike]
  map_continuous f := .subtype_mk (by fun_prop) _

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
instance instFunLike : FunLike (PMap dIn dOut ℂ) (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  coe := DFunLike.coe ∘ toHPMap
  coe_injective' := DFunLike.coe_injective'.comp injective_toHPMap

set_option synthInstance.maxHeartbeats 40000 in
instance instLinearMapClass : LinearMapClass (PMap dIn dOut ℂ) ℝ (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.toLinearMap x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp [instFunLike]

instance instContinuousOrderHomClass : ContinuousOrderHomClass (PMap dIn dOut ℂ)
    (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_continuous f := ContinuousMapClass.map_continuous f.toHPMap
  map_monotone f x y h := by
    simpa using f.pos h

/-- Positive-presering maps also preserve positivity on, specifically, Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : PMap dIn dOut ℂ) {x : HermitianMat dIn ℂ} (h : 0 ≤ x) : 0 ≤ M x := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

end PMap

namespace CPMap

def of_kraus_CPMap {κ : Type*} [Fintype κ] [DecidableEq dIn] (M : κ → Matrix dOut dIn 𝕜) : CPMap dIn dOut 𝕜 where
  toLinearMap := MatrixMap.of_kraus M M
  cp := MatrixMap.IsCompletelyPositive.of_kraus_isCompletelyPositive M

end CPMap

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
instance instFunLike : FunLike (PTPMap dIn dOut ℂ) (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  coe := DFunLike.coe ∘ toPMap
  coe_injective' := DFunLike.coe_injective'.comp injective_toPMap

instance instLinearMapClass : LinearMapClass (PTPMap dIn dOut ℂ) ℝ (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_add f x y := by simp [instFunLike]
  map_smulₛₗ f c x := by simp [instFunLike]

instance instHContinuousOrderHomClass : ContinuousOrderHomClass (PTPMap dIn dOut ℂ)
    (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_continuous f := ContinuousMapClass.map_continuous f.toPMap
  map_monotone f x y h := by
    simpa using f.pos h

/-- PTP maps also preserve positivity on Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : PTPMap dIn dOut ℂ) {x : HermitianMat dIn ℂ} (h : 0 ≤ x) : 0 ≤ M x := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

/-- `PTPMap`s are functions from `MState`s to `MState`s. -/
instance instMFunLike [DecidableEq dIn] [DecidableEq dOut] :
    FunLike (PTPMap dIn dOut) (MState dIn) (MState dOut) where
  coe Λ ρ := MState.mk
    (Λ.toHPMap ρ.M) (HermitianMat.zero_le_iff.mpr (Λ.pos ρ.pos)) (by
      rw [HermitianMat.trace_eq_one_iff, ← ρ.tr']
      exact Λ.TP ρ)
  coe_injective' x y h := injective_toPMap <| PMap.injective_toHPMap <|
    HPMap.funext_mstate fun ρ ↦ by
      have := congr($h ρ);
      rwa [MState.ext_iff, HermitianMat.ext_iff] at this

instance instMContinuousMapClass [DecidableEq dIn] [DecidableEq dOut] :
    ContinuousMapClass (PTPMap dIn dOut) (MState dIn) (MState dOut) where
  map_continuous f := by
    rw [continuous_induced_rng]
    exact (map_continuous f.toHPMap).comp MState.Continuous_HermitianMat

-- @[norm_cast]
theorem val_apply_MState [DecidableEq dIn] (M : PTPMap dIn dOut) (ρ : MState dIn) :
    (M ρ : HermitianMat dOut ℂ) = (instFunLike.coe M) ρ := by
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
-- instance instFunLike : FunLike (CPTPMap dIn dOut 𝕜) (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
--   coe :=  DFunLike.coe ∘ toPTPMap
--   coe_injective' := DFunLike.coe_injective'.comp injective_toPTPMap

-- set_option synthInstance.maxHeartbeats 40000 in
-- instance instLinearMapClass : LinearMapClass (CPTPMap dIn dOut 𝕜) ℝ (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
--   map_add f x y := by simp [instFunLike]
--   map_smulₛₗ f c x := by simp [instFunLike]

-- instance instContinuousOrderHomClass : ContinuousOrderHomClass (CPTPMap dIn dOut 𝕜)
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
--     (M ρ : HermitianMat dOut ℂ) = (instFunLike.coe M) ρ := by
--   rfl

@[simp]
theorem IsTracePreserving (Λ : CPTPMap dIn dOut 𝕜) : Λ.map.IsTracePreserving :=
  Λ.TP

def of_kraus_CPTPMap {κ : Type*} [Fintype κ] [DecidableEq dIn]
  (M : κ → Matrix dOut dIn 𝕜)
  (hTP : (∑ k, (M k).conjTranspose * (M k)) = 1) : CPTPMap dIn dOut 𝕜 where
  toLinearMap := MatrixMap.of_kraus M M
  cp := MatrixMap.IsCompletelyPositive.of_kraus_isCompletelyPositive M
  TP := MatrixMap.IsTracePreserving.of_kraus_isTracePreserving M M hTP

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
instance instFunLike : FunLike (CPUMap dIn dOut ℂ) (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  coe Λ := Λ.toPMap
  coe_injective' := (DFunLike.coe_injective' (F := PMap dIn dOut ℂ)).comp injective_toPMap

instance instLinearMapClass : LinearMapClass (CPUMap dIn dOut ℂ) ℝ (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.toLinearMap x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp [instFunLike]

instance instHContinuousOrderHomClass : ContinuousOrderHomClass (CPUMap dIn dOut ℂ)
    (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_continuous f := ContinuousMapClass.map_continuous f.toPMap
  map_monotone f x y h := by
    simpa using f.pos h

instance instOneHomClass : OneHomClass (CPUMap dIn dOut ℂ)
    (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_one f := HermitianMat.ext (f.unital)

/-- CPTP maps also preserve positivity on Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : CPUMap dIn dOut ℂ) {x : HermitianMat dIn ℂ} (h : 0 ≤ x) : 0 ≤ M x := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h

end CPUMap


--Tests to make sure that our `simp`s and classe are all working like we want them too

section test
variable [DecidableEq dIn] [DecidableEq dOut]

#guard_msgs in
example (M : HPMap dIn dOut ℂ) : (M (Real.pi • 1)) = Real.pi • M 1 := by simp

#guard_msgs in
example (M : PTPMap dIn dOut ℂ) : (M.toHPMap (Real.pi • 1)) = Real.pi • M.toHPMap 1 := by simp

#guard_msgs in
example (M : CPTPMap dIn dOut 𝕜) (ρ : Matrix dIn dIn 𝕜) : (M.map ρ).trace = ρ.trace := by simp

#guard_msgs in
example (M : CPUMap dIn dOut ℂ) (T : HermitianMat dIn ℂ) : M (1 + 2 • T) = 1 + 2 • M T := by simp

end test
