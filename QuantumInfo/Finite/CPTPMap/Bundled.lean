import QuantumInfo.Finite.CPTPMap.Unbundled
import QuantumInfo.Finite.MState

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
variable [DecidableEq dIn] [DecidableEq dOut]
variable [Semiring R] [RCLike 𝕜]

/-- Hermitian-preserving linear maps. -/
structure HPMap extends MatrixMap dIn dOut 𝕜 where
  HP : MatrixMap.IsHermitianPreserving toLinearMap

/-- Unital linear maps. -/
structure UnitalMap extends MatrixMap dIn dOut R where
  unital : MatrixMap.Unital toLinearMap

attribute [simp] UnitalMap.unital

/-- Trace-preserving linear maps. -/
structure TPMap extends MatrixMap dIn dOut R where
  TP : MatrixMap.IsTracePreserving toLinearMap

attribute [simp] TPMap.TP

/-- Positive linear maps. -/
structure PMap extends HPMap dIn dOut 𝕜 where
  pos : MatrixMap.IsPositive toLinearMap
  HP := pos.IsHermitianPreserving

/-- Completely positive linear maps. -/
structure CPMap extends PMap dIn dOut 𝕜 where
  cp : MatrixMap.IsCompletelyPositive toLinearMap
  pos := cp.IsPositive

/-- Positive trace-preserving linear maps. These includes all channels, but aren't
  necessarily *completely* positive, see `CPTPMap`. -/
structure PTPMap extends PMap dIn dOut 𝕜, TPMap dIn dOut 𝕜

attribute [simp] PTPMap.TP

/-- Completely positive trace-preserving linear maps. This is the most common
  meaning of "channel", often described as "the most general physically realizable
  quantum operation". -/
structure CPTPMap extends PTPMap dIn dOut (𝕜 := 𝕜), CPMap dIn dOut 𝕜 where

/-- Completely positive unital maps. These are important because they are the
  dual to `CPTPMap`: they are the most general way to map *observables*. -/
structure CPUMap extends CPMap dIn dOut 𝕜, UnitalMap dIn dOut 𝕜

attribute [simp] CPUMap.unital

variable {dIn dOut R} {𝕜 : Type} [RCLike 𝕜]

namespace HPMap
omit [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut]

abbrev map (M : HPMap dIn dOut 𝕜) : MatrixMap dIn dOut 𝕜 := M.toLinearMap

@[ext]
theorem ext {Λ₁ Λ₂ : HPMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rwa [HPMap.mk.injEq]

/-- `HPMap`s are functions from `HermitianMat`s to `HermitianMat`s. -/
instance instFunLike : FunLike (HPMap dIn dOut 𝕜) (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
  coe Λ ρ := ⟨Λ.map ρ.1, Λ.HP ρ.2⟩
  coe_injective' _ _ h := by
    sorry --Requires the fact the action on HermitianMat's determines action on all matrices

end HPMap

namespace PTPMap
omit [DecidableEq dIn] [DecidableEq dOut]

abbrev map (M : PTPMap dIn dOut 𝕜) : MatrixMap dIn dOut 𝕜 := M.toLinearMap

@[ext]
theorem ext {Λ₁ Λ₂ : PTPMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [PTPMap.mk.injEq, PMap.mk.injEq]
  exact HPMap.ext h

/-- `PTPMap`s are functions from `MState`s to `MState`s. -/
instance instFunLike : FunLike (PTPMap dIn dOut) (MState dIn) (MState dOut) where
  coe Λ ρ := MState.mk
    (Λ.toHPMap ρ.M) (HermitianMat.zero_le_iff.mpr (Λ.pos ρ.pos)) (ρ.tr ▸ Λ.TP ρ.m)
  coe_injective' _ _ h := by
    sorry --Requires the fact the action on MStates determines action on all matrices

open ComplexOrder in
theorem apply_PosSemidef (Λ : PTPMap dIn dOut 𝕜) {ρ : Matrix dIn dIn 𝕜} (hρ : ρ.PosSemidef) : (Λ.map ρ).PosSemidef :=
  Λ.pos hρ

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
omit [DecidableEq dOut]

abbrev map (M : CPTPMap dIn dOut 𝕜) : MatrixMap dIn dOut 𝕜 := M.toLinearMap

/-- Two `CPTPMap`s are equal if their `MatrixMap`s are equal. -/
@[ext]
theorem ext {Λ₁ Λ₂ : CPTPMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [CPTPMap.mk.injEq]
  exact PTPMap.ext h

/-- `CPTPMap`s are functions from `MState`s to `MState`s. -/
instance instFunLike : FunLike (CPTPMap dIn dOut) (MState dIn) (MState dOut) where
  coe Λ ρ := Λ.toPTPMap ρ
  coe_injective' x y h := by
    rw [CPTPMap.mk.injEq]
    exact DFunLike.ext _ _ (congrFun h ·)

@[simp]
theorem IsTracePreserving (Λ : CPTPMap dIn dOut 𝕜) : Λ.map.IsTracePreserving :=
  Λ.TP

open ComplexOrder in
theorem apply_PosSemidef (Λ : CPTPMap dIn dOut 𝕜) {ρ : Matrix dIn dIn 𝕜} (hρ : ρ.PosSemidef) : (Λ.map ρ).PosSemidef :=
  Λ.pos hρ

#guard_msgs in
example (M : CPTPMap dIn dOut 𝕜) (ρ : Matrix dIn dIn 𝕜) : (M.map ρ).trace = ρ.trace := by simp

end CPTPMap

namespace CPUMap

abbrev map (M : CPUMap dIn dOut 𝕜) : MatrixMap dIn dOut 𝕜 := M.toLinearMap

@[ext]
theorem ext {Λ₁ Λ₂ : CPUMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [CPUMap.mk.injEq, CPMap.mk.injEq, PMap.mk.injEq]
  exact HPMap.ext h

#guard_msgs in
example (M : CPUMap dIn dOut 𝕜) : M.map 1 = 1 := by simp

end CPUMap
