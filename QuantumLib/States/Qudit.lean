/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazumi Kasaura, Hayata Yamasaki
-/

import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.LownerHeinzTheorem
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Qudits and their operator algebras

A `Qudit` is a finite-dimensional complex Hilbert space, and `L ℋ` is the algebra of operators on
it. Operators are the *continuous* linear maps `ℋ →L[ℂ] ℋ`, which is what carries the C⋆-algebra
structure in Mathlib, what `LownerHeinzTheorem.L` means, and what physlib's `OpMap`, `HermitianOp`
and `DensityOp` are built from. In finite dimensions every linear map is continuous, so nothing is
lost.

## Vocabulary

The operator classes are Mathlib's, under Mathlib's names: an operator `X : L ℋ` is normal when
`IsStarNormal X`, Hermitian when `IsSelfAdjoint X`, positive semidefinite when `X.IsPositive`, a
projection when `X.IsPositive ∧ IsIdempotentElem X`, and unitary when `X ∈ unitary (L ℋ)`. A
density operator is physlib's `DensityOp ℋ`. A function of a normal operator, sending a spectral
decomposition to the sum of the values of `f` on the eigenvalues against the eigenprojections
(Watrous, *The Theory of Quantum Information*, definition 1.145), is Mathlib's continuous
functional calculus `cfc f X`.
-/

namespace QuantumState

open scoped NNReal

universe u v

/-- A **qudit**: a finite-dimensional complex Hilbert space. -/
class Qudit (a : Type u) extends
  NormedAddCommGroup a,
  InnerProductSpace ℂ a,
  FiniteDimensional ℂ a

/-- A qudit is complete, being finite-dimensional. This is what makes `L ℋ` a C⋆-algebra, so it is
registered as an instance rather than being rediscovered at every use. -/
instance Qudit.toCompleteSpace (a : Type u) [Qudit a] : CompleteSpace a :=
  FiniteDimensional.complete ℂ a

/-- The algebra of operators on `ℋ`. This is `LownerHeinzTheorem.L ℋ`. -/
abbrev L (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] : Type u :=
  ℋ →L[ℂ] ℋ

/-- Identity operator -/
abbrev I (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] : L ℋ :=
  ContinuousLinearMap.id ℂ ℋ

/-- Adjoint -/
scoped notation X"†" => ContinuousLinearMap.adjoint X

variable {ℋ : Type u} [Qudit ℋ]

/-- Nonnegative reals act on operators through `ℂ`. -/
instance : IsScalarTower ℝ≥0 ℂ (L ℋ) :=
  ⟨fun r s A ↦ smul_assoc (r : ℂ) s A⟩

/-- Trace of an operator. -/
noncomputable abbrev Tr : L ℋ →ₗ[ℂ] ℂ :=
  LinearMap.trace ℂ ℋ ∘ₗ ContinuousLinearMap.coeLM ℂ

/-- The trace of an operator is the trace of the linear map underlying it. -/
theorem Tr_apply (A : L ℋ) : Tr A = LinearMap.trace ℂ ℋ (A : ℋ →ₗ[ℂ] ℋ) :=
  rfl

/-- The identity has trace the dimension of the space. -/
@[simp]
theorem Tr_one : Tr (1 : L ℋ) = (Module.finrank ℂ ℋ : ℂ) := by
  rw [Tr_apply, ContinuousLinearMap.toLinearMap_one, LinearMap.trace_one]

/-- The trace is cyclic on two factors. -/
theorem Tr_mul_comm (A B : L ℋ) : Tr (A * B) = Tr (B * A) := by
  simp only [Tr_apply, ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm]

/-- The trace is cyclic on three factors. -/
theorem Tr_mul_cycle (A B C : L ℋ) : Tr (A * B * C) = Tr (C * A * B) := by
  simp only [Tr_apply, ContinuousLinearMap.toLinearMap_mul]
  exact LinearMap.trace_mul_cycle (R := ℂ) (M := ℋ) _ _ _

/-- The complex spectrum of an operator on a qudit is finite: it agrees with the spectrum of the
underlying `Module.End`, which is cut out by the minimal polynomial. -/
theorem finite_spectrum_complex (A : L ℋ) : (spectrum ℂ A).Finite := by
  rw [ContinuousLinearMap.spectrum_eq]
  exact Module.End.finite_spectrum (A : ℋ →ₗ[ℂ] ℋ)

/-- The real spectrum of an operator on a qudit is finite. -/
theorem finite_spectrum_real (A : L ℋ) : (spectrum ℝ A).Finite := by
  rw [← spectrum.preimage_algebraMap ℂ]
  exact (finite_spectrum_complex A).preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

/-- The real quasispectrum of an operator on a qudit is finite; in particular every point of it
is isolated, so any function is `ContinuousOn` it. -/
theorem finite_quasispectrum_real (A : L ℋ) : (quasispectrum ℝ A).Finite := by
  rw [quasispectrum_eq_spectrum_union_zero]
  exact (finite_spectrum_real A).union (Set.finite_singleton 0)

end QuantumState
