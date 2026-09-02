/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
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

end QuantumState
