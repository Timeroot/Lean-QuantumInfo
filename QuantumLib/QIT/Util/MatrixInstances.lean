/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Util.Matrix
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# Matrix structures for the L2-operator norm

`Matrix n n ℂ` carries several norms, so Mathlib keeps the ones that make it a
C⋆-algebra out of the global instance set: the L2-operator norm lives in the
`Matrix.Norms.L2Operator` scope. Everything downstream of it — the C⋆-algebra
structure, the continuous functional calculus, and the real normed-space
structure — therefore has to be turned on by hand as well.

Those structures are collected here in the `QIT.MatrixL2` scope, so a file that
works with the L2-operator norm opens both scopes:

```lean
open scoped Matrix.Norms.L2Operator QIT.MatrixL2
```
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QIT.MatrixL2

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The extended-norm structure induced by the L2-operator norm. -/
noncomputable scoped instance cMatrixContinuousENorm : ContinuousENorm (CMatrix n) :=
  SeminormedAddGroup.toContinuousENorm

/-- The extended-norm additive monoid structure induced by the L2-operator
norm. -/
noncomputable scoped instance cMatrixENormedAddMonoid : ENormedAddMonoid (CMatrix n) :=
  NormedAddGroup.toENormedAddMonoid

/-- The real normed-space structure induced by the L2-operator norm. -/
noncomputable scoped instance cMatrixNormedSpaceReal : NormedSpace ℝ (CMatrix n) :=
  inferInstance

/-- Square complex matrices under the L2-operator norm form a non-unital
C⋆-algebra. -/
noncomputable scoped instance cMatrixNonUnitalCStarAlgebra :
    NonUnitalCStarAlgebra (CMatrix n) :=
  ⟨⟩

/-- Square complex matrices under the L2-operator norm form a C⋆-algebra. -/
noncomputable scoped instance cMatrixCStarAlgebra : CStarAlgebra (CMatrix n) :=
  ⟨⟩

/-- The complex continuous functional calculus for normal matrices. -/
scoped instance cMatrixNormalCFC :
    ContinuousFunctionalCalculus ℂ (CMatrix n) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

/-- The complex continuous functional calculus for normal matrices is
isometric. -/
scoped instance cMatrixNormalIsometricCFC :
    IsometricContinuousFunctionalCalculus ℂ (CMatrix n) IsStarNormal :=
  IsStarNormal.instIsometricContinuousFunctionalCalculus

/-- The real continuous functional calculus for self-adjoint matrices. -/
scoped instance cMatrixSelfAdjointCFC :
    ContinuousFunctionalCalculus ℝ (CMatrix n) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- The real continuous functional calculus for self-adjoint matrices is
isometric. -/
scoped instance cMatrixSelfAdjointIsometricCFC :
    IsometricContinuousFunctionalCalculus ℝ (CMatrix n) IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

end QIT.MatrixL2

end
