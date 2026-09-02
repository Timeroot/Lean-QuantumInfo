/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazumi Kasaura, Hayata Yamasaki
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.InnerProductSpace.StarOrder

namespace QuantumState

universe u v

-- Qudit
class Qudit (a : Type u) extends
  NormedAddCommGroup a,
  InnerProductSpace ℂ a,
  CompleteSpace a,
  FiniteDimensional ℂ a

abbrev L (ℋ : Type u) [AddCommGroup ℋ] [Module ℂ ℋ] : Type u :=
  ℋ →ₗ[ℂ] ℋ

-- Identity operator
abbrev I (ℋ : Type u) [AddCommGroup ℋ] [Module ℂ ℋ] : L ℋ :=
  LinearMap.id

-- Braket notation
notation "⟨" x "∣" y "⟩" => inner ℂ x y

-- Adjoint
notation X"†" => LinearMap.adjoint X

variable {ℋ : Type u} [Qudit ℋ]

-- Trace
noncomputable abbrev Tr : L ℋ →ₗ[ℂ] ℂ := LinearMap.trace ℂ ℋ

-- Normal operators are defined by IsStarNormal
example (X : L ℋ) : Prop := IsStarNormal X

-- Hermitian operators are defined by IsSelfAdjoint
example (X : L ℋ) : Prop := IsSelfAdjoint X

-- Positive semidefinite operators are defined by IsPositive
example (X : L ℋ) : Prop := X.IsPositive

-- Positive definite operators
def IsPositiveDefinite (X : L ℋ) : Prop :=
  X.IsPositive ∧ X.det ≠ 0

-- Projection operators
def IsProjective (X : L ℋ) : Prop :=
  X.IsPositive ∧ IsIdempotentElem X

-- Density operators
def IsDensity (X : L ℋ) : Prop :=
  X.IsPositive ∧ Tr X = 1

-- Unitary operators are defined by unitary
example (X : L ℋ) : Prop := X ∈ unitary (L ℋ)

-- Def: Function of normal operators (1.145) of https://cs.uwaterloo.ca/~watrous/TQI/TQI1.pdf
-- For any qudit ℋ, any A ∈ Normal(ℋ), any 𝒳 ⊆ ℂ, and any complex-valued function f: 𝒳 → ℂ,
-- suppose that A's spectral decomposition A=∑_{k=1,…,m} λₖ Πₖ satisfies λₖ ∈ 𝒳 for all k.
-- Then, we define
-- f(A) := ∑_{k=1,…,m} f(λₖ) Πₖ

/-! ### `L ℋ` as a C⋆-algebra

The operator algebra `L ℋ = ℋ →ₗ[ℂ] ℋ` carries the C⋆-algebra and
`StarOrderedRing` structures transported along the isometry with the continuous
linear maps `ℋ →L[ℂ] ℋ`, which agree with `L ℋ` because `ℋ` is finite-dimensional.
-/

section ContinuousLinearMapsAreCStarAlgebras

noncomputable instance continuous_instance {ℋ : Type u} [Qudit ℋ] : CStarAlgebra (ℋ →L[ℂ] ℋ)
  := inferInstance

noncomputable instance (ℋ : Type u) [Qudit ℋ] : Norm (L ℋ) where
  norm := fun X => ‖X.toContinuousLinearMap‖

noncomputable instance (ℋ : Type u) [Qudit ℋ] : MetricSpace (L ℋ) :=
  MetricSpace.induced LinearMap.toContinuousLinearMap
    LinearMap.toContinuousLinearMap.injective inferInstance

noncomputable def linear_isometry_equiv {ℋ : Type u} [Qudit ℋ] : (L ℋ) ≃ᵢ (ℋ →L[ℂ] ℋ) where
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


end QuantumState
