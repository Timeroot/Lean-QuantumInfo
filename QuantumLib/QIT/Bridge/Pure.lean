/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QIT.Core.Pure
import QuantumLib.QIT.Bridge.State

/-!
# Lean-QIT pure vectors and physlib kets

A `QIT.PureVector a` is an amplitude vector normalized by the requirement that its rank-one kernel
`|ψ⟩⟨ψ|` have trace one; a `Ket a` is an amplitude vector normalized by `∑ x, ‖ψ x‖ ^ 2 = 1`. Those
two conditions are the same one written in `ℂ` and in `ℝ`, so the two types carry the same data and
`QIT.PureVector.equivKet` is the resulting equivalence.

The rank-one state of a pure vector is the pure state of the corresponding ket, and products match
up on both sides.

## Main definitions

* `QIT.PureVector.toKet` and `QIT.PureVector.ofKet` — the two directions of the identification.
* `QIT.PureVector.equivKet` — the equivalence `QIT.PureVector a ≃ Ket a`.
-/

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

omit [DecidableEq a] in
/-- Unit trace of the rank-one kernel, in `ℂ`, is normalization of the amplitudes, in `ℝ`. -/
theorem trace_rankOneMatrix_eq_one_iff (amp : a → ℂ) :
    (rankOneMatrix amp).trace = 1 ↔ ∑ x, ‖amp x‖ ^ 2 = 1 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, rankOneMatrix_apply, ← starRingEnd_apply, Complex.mul_conj']
  exact_mod_cast Iff.rfl

namespace PureVector

/-- The physlib ket with the same amplitudes. -/
def toKet (psi : PureVector a) : Ket a where
  vec := psi.amp
  normalized' := (trace_rankOneMatrix_eq_one_iff _).mp psi.trace_rankOne_eq_one

@[simp]
theorem toKet_apply (psi : PureVector a) (i : a) : psi.toKet i = psi.amp i :=
  rfl

/-- The Lean-QIT pure vector with the same amplitudes. -/
def ofKet (psi : Ket a) : PureVector a where
  amp := psi
  trace_rankOne_eq_one := (trace_rankOneMatrix_eq_one_iff _).mpr psi.normalized'

@[simp]
theorem amp_ofKet (psi : Ket a) (i : a) : (ofKet psi).amp i = psi i :=
  rfl

@[simp]
theorem ofKet_toKet (psi : PureVector a) : ofKet psi.toKet = psi :=
  rfl

@[simp]
theorem toKet_ofKet (psi : Ket a) : (ofKet psi).toKet = psi :=
  rfl

/-- Lean-QIT pure vectors and physlib kets are the same data. -/
def equivKet : PureVector a ≃ Ket a where
  toFun := toKet
  invFun := ofKet
  left_inv := ofKet_toKet
  right_inv := toKet_ofKet

@[simp]
theorem equivKet_apply (psi : PureVector a) : equivKet psi = psi.toKet :=
  rfl

@[simp]
theorem equivKet_symm_apply (psi : Ket a) : equivKet.symm psi = ofKet psi :=
  rfl

/-- The rank-one state of a pure vector is the pure state of the corresponding ket. -/
@[simp]
theorem toMState_state (psi : PureVector a) : psi.state.toMState = MState.pure psi.toKet :=
  DensityOp.ext_m <| by
    ext i j
    simp [State.m_toMState]

@[simp]
theorem toKet_prod (psi : PureVector a) (phi : PureVector b) :
    (psi.prod phi).toKet = psi.toKet.prod phi.toKet :=
  Ket.ext fun _ => rfl

end PureVector

end QIT
