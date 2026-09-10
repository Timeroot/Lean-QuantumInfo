/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Core.State
public import QuantumLib.QIT.Util.Matrix.PosSqrt

/-!
# MState square roots

MState-facing wrapper around the matrix positive semidefinite square-root API.
The underlying matrix construction and support lemmas live in
`QIT.Util.Matrix.PosSqrt`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

noncomputable section
universe u
variable {a : Type u} [Fintype a] [DecidableEq a]

open QIT

namespace MState

/-- The positive semidefinite square-root matrix of a density state. -/
def sqrtMatrix (rho : MState a) : CMatrix a :=
  psdSqrt rho.m

/-- A state's square-root matrix is positive semidefinite. -/
theorem sqrtMatrix_pos (rho : MState a) :
    rho.sqrtMatrix.PosSemidef :=
  psdSqrt_pos rho.m

/-- A state's square-root matrix is Hermitian. -/
theorem sqrtMatrix_isHermitian (rho : MState a) :
    rho.sqrtMatrix.IsHermitian :=
  psdSqrt_isHermitian rho.m

/-- A state's square-root matrix squares back to the state's density matrix. -/
@[simp]
theorem sqrtMatrix_mul_self (rho : MState a) :
    rho.sqrtMatrix * rho.sqrtMatrix = rho.m :=
  psdSqrt_mul_self_of_posSemidef rho.psd

end MState
