/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QIT.States.MaximallyMixed
import QuantumInfo.States.Mixed.MState

/-!
# Lean-QIT states and physlib mixed states

A `QIT.State a` is a `Matrix a a ℂ` bundled with positive semidefiniteness and unit trace. An
`MState a` is a positive unit-trace *operator* on `EuclideanSpace ℂ a`, whose matrix in the
computational basis is `ρ.m`. The two carry exactly the same information, and
`QIT.State.equivMState` is the resulting equivalence.

The identification respects the constructions the two libraries share: products are Kronecker
products on both sides, Lean-QIT's `partialTraceA` and `partialTraceB` are physlib's
`Matrix.traceLeft` and `Matrix.traceRight`, Lean-QIT's `reindex` along `e` is physlib's `relabel`
along `e.symm`, and the two maximally mixed states agree.

## Main definitions

* `QIT.State.toMState` and `QIT.State.ofMState` — the two directions of the identification.
* `QIT.State.equivMState` — the equivalence `QIT.State a ≃ MState a`.
-/

open scoped ComplexOrder MatrixOrder Kronecker

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

omit [DecidableEq a] [Fintype b] [DecidableEq b] in
/-- Lean-QIT's `partialTraceA` traces out the first factor, as physlib's `Matrix.traceLeft` does. -/
theorem partialTraceA_eq_traceLeft (X : CMatrix (a × b)) : partialTraceA X = X.traceLeft :=
  rfl

omit [Fintype a] [DecidableEq a] [DecidableEq b] in
/-- Lean-QIT's `partialTraceB` traces out the second factor, as physlib's `Matrix.traceRight`
does. -/
theorem partialTraceB_eq_traceRight (X : CMatrix (a × b)) : partialTraceB X = X.traceRight :=
  rfl

namespace State

/-- The density matrix of a Lean-QIT state, as a `HermitianMat`. -/
def toHermitianMat (rho : State a) : HermitianMat a ℂ :=
  ⟨rho.matrix, rho.pos.isHermitian⟩

@[simp]
theorem mat_toHermitianMat (rho : State a) : rho.toHermitianMat.mat = rho.matrix :=
  rfl

@[simp]
theorem trace_toHermitianMat (rho : State a) : rho.toHermitianMat.trace = 1 := by
  rw [HermitianMat.trace_eq_re_trace, mat_toHermitianMat, rho.trace_eq_one]
  norm_num

/-- The physlib mixed state with the same density matrix. -/
def toMState (rho : State a) : MState a :=
  DensityOp.ofMat rho.toHermitianMat (HermitianMat.zero_le_iff.mpr rho.pos)
    rho.trace_toHermitianMat

@[simp]
theorem M_toMState (rho : State a) : (rho.toMState.M : HermitianMat a ℂ) = rho.toHermitianMat := by
  rw [toMState, DensityOp.M_ofMat]

@[simp]
theorem m_toMState (rho : State a) : rho.toMState.m = rho.matrix := by
  rw [← DensityOp.mat_M, M_toMState, mat_toHermitianMat]

/-- The Lean-QIT state with the same density matrix. -/
def ofMState (rho : MState a) : State a where
  matrix := rho.m
  pos := rho.psd
  trace_eq_one := rho.tr'

@[simp]
theorem matrix_ofMState (rho : MState a) : (ofMState rho).matrix = rho.m :=
  rfl

@[simp]
theorem ofMState_toMState (rho : State a) : ofMState rho.toMState = rho :=
  State.ext (by simp)

@[simp]
theorem toMState_ofMState (rho : MState a) : (ofMState rho).toMState = rho :=
  DensityOp.ext_m (by simp)

/-- Lean-QIT states and physlib mixed states are the same data. -/
def equivMState : State a ≃ MState a where
  toFun := toMState
  invFun := ofMState
  left_inv := ofMState_toMState
  right_inv := toMState_ofMState

@[simp]
theorem equivMState_apply (rho : State a) : equivMState rho = rho.toMState :=
  rfl

@[simp]
theorem equivMState_symm_apply (rho : MState a) : equivMState.symm rho = ofMState rho :=
  rfl

theorem toMState_injective : Function.Injective (toMState (a := a)) :=
  equivMState.injective

@[simp]
theorem toMState_inj {rho sigma : State a} : rho.toMState = sigma.toMState ↔ rho = sigma :=
  toMState_injective.eq_iff

@[simp]
theorem toMState_prod (rho : State a) (sigma : State b) :
    (rho.prod sigma).toMState = rho.toMState.prod sigma.toMState :=
  DensityOp.ext_m (by simp [← DensityOp.mat_M, prod, Matrix.kronecker])

@[simp]
theorem toMState_marginalA (rho : State (a × b)) :
    rho.marginalA.toMState = rho.toMState.traceRight :=
  DensityOp.ext_m (by simp [partialTraceB_eq_traceRight])

@[simp]
theorem toMState_marginalB (rho : State (a × b)) :
    rho.marginalB.toMState = rho.toMState.traceLeft :=
  DensityOp.ext_m (by simp [partialTraceA_eq_traceLeft])

@[simp]
theorem toMState_reindex (rho : State a) (e : a ≃ b) :
    (rho.reindex e).toMState = rho.toMState.relabel e.symm :=
  DensityOp.ext_m (by simp)

@[simp]
theorem toMState_maximallyMixed [Nonempty a] :
    (maximallyMixed a).toMState = MState.uniform :=
  DensityOp.ext_m <| by
    rw [m_toMState, MState.uniform, ← DensityOp.mat_M, MState.coe_ofClassical]
    ext i j
    by_cases hij : i = j <;>
      simp [maximallyMixed, hij, HermitianMat.diagonal, Finset.card_univ]

end State

end

end QIT
