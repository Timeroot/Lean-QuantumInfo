/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.State
public import QIT.Util.Matrix.PosSqrt

/-!
# State square roots

State-facing wrapper around the matrix positive semidefinite square-root API.
The underlying matrix construction and support lemmas live in
`QIT.Util.Matrix.PosSqrt`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

namespace State

/-- The positive semidefinite square-root matrix of a density state. -/
def sqrtMatrix (rho : State a) : CMatrix a :=
  psdSqrt rho.matrix

/-- A state's square-root matrix is positive semidefinite. -/
theorem sqrtMatrix_pos (rho : State a) :
    rho.sqrtMatrix.PosSemidef :=
  psdSqrt_pos rho.matrix

/-- A state's square-root matrix is Hermitian. -/
theorem sqrtMatrix_isHermitian (rho : State a) :
    rho.sqrtMatrix.IsHermitian :=
  psdSqrt_isHermitian rho.matrix

/-- A state's square-root matrix squares back to the state's density matrix. -/
@[simp]
theorem sqrtMatrix_mul_self (rho : State a) :
    rho.sqrtMatrix * rho.sqrtMatrix = rho.matrix :=
  psdSqrt_mul_self_of_posSemidef rho.pos

end State

end

end QIT
