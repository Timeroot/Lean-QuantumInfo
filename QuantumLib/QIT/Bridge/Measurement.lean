/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QIT.Core.Channel
import QuantumLib.QIT.Bridge.Channel
import QuantumInfo.Measurements.POVM

/-!
# Lean-QIT POVMs and physlib POVMs

Both libraries define a POVM as a finite family of positive semidefinite effects summing to the
identity; Lean-QIT stores the effects as bare matrices with a separate positivity hypothesis, and
physlib stores them as `HermitianMat`s ordered against zero. `QIT.POVM.equivPOVM` is the resulting
equivalence.

The measurement channels agree too: Lean-QIT's `QIT.Channel.measure` sends a state to the diagonal
matrix of its Born-rule probabilities, which is exactly physlib's `POVM.measureDiscard`.

## Main definitions

* `QIT.POVM.toPOVM` and `QIT.POVM.ofPOVM` — the two directions of the identification.
* `QIT.POVM.equivPOVM` — the equivalence `QIT.POVM x a ≃ POVM x a`.
-/

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

variable {x : Type u} {a : Type v}
variable [Fintype x] [DecidableEq x] [Fintype a] [DecidableEq a]

namespace POVM

omit [DecidableEq x] in
/-- Two Lean-QIT POVMs with the same effects are equal. -/
@[ext]
theorem ext {M N : POVM x a} (h : M.effects = N.effects) : M = N := by
  cases M
  cases N
  cases h
  rfl

omit [DecidableEq x] in
/-- The effects of a Lean-QIT POVM, as `HermitianMat`s. -/
def hermitianEffects (M : POVM x a) (y : x) : HermitianMat a ℂ :=
  ⟨M.effects y, (M.pos y).isHermitian⟩

omit [DecidableEq x] in
@[simp]
theorem mat_hermitianEffects (M : POVM x a) (y : x) :
    (M.hermitianEffects y).mat = M.effects y :=
  rfl

omit [DecidableEq x] in
/-- The physlib POVM with the same effects. -/
def toPOVM (M : POVM x a) : _root_.POVM x a where
  mats := M.hermitianEffects
  nonneg y := HermitianMat.zero_le_iff.mpr (M.pos y)
  normalized := HermitianMat.ext <| by
    rw [HermitianMat.mat_finset_sum, HermitianMat.mat_one]
    simp only [mat_hermitianEffects]
    exact M.sum_eq_one

omit [DecidableEq x] in
@[simp]
theorem mats_toPOVM (M : POVM x a) (y : x) : M.toPOVM.mats y = M.hermitianEffects y :=
  rfl

omit [DecidableEq x] in
/-- The Lean-QIT POVM with the same effects. -/
def ofPOVM (M : _root_.POVM x a) : POVM x a where
  effects y := (M.mats y).mat
  pos y := HermitianMat.zero_le_iff.mp (M.nonneg y)
  sum_eq_one := by
    rw [← HermitianMat.mat_finset_sum, M.normalized, HermitianMat.mat_one]

omit [DecidableEq x] in
@[simp]
theorem effects_ofPOVM (M : _root_.POVM x a) (y : x) : (ofPOVM M).effects y = (M.mats y).mat :=
  rfl

omit [DecidableEq x] in
@[simp]
theorem ofPOVM_toPOVM (M : POVM x a) : ofPOVM M.toPOVM = M :=
  rfl

omit [DecidableEq x] in
@[simp]
theorem toPOVM_ofPOVM (M : _root_.POVM x a) : (ofPOVM M).toPOVM = M :=
  rfl

omit [DecidableEq x] in
/-- Lean-QIT POVMs and physlib POVMs are the same data. -/
def equivPOVM : POVM x a ≃ _root_.POVM x a where
  toFun := toPOVM
  invFun := ofPOVM
  left_inv := ofPOVM_toPOVM
  right_inv := toPOVM_ofPOVM

omit [DecidableEq x] in
@[simp]
theorem equivPOVM_apply (M : POVM x a) : equivPOVM M = M.toPOVM :=
  rfl

omit [DecidableEq x] in
@[simp]
theorem equivPOVM_symm_apply (M : _root_.POVM x a) : equivPOVM.symm M = ofPOVM M :=
  rfl

omit [DecidableEq x] in
/-- The Born-rule probability that Lean-QIT writes as a trace is the entry of the physlib outcome
distribution. -/
theorem coe_measure_toPOVM (M : POVM x a) (rho : MState a) (y : x) :
    ((M.toPOVM.measure rho y : ℝ) : ℂ) = (rho.m * M.effects y).trace := by
  have h := HermitianMat.inner_eq_trace_rc (M.hermitianEffects y) rho.M
  rw [mat_hermitianEffects, DensityOp.mat_M, Matrix.trace_mul_comm] at h
  exact h

end POVM

/-- Lean-QIT's measurement channel is physlib's measure-and-record channel. -/
theorem Channel.toCPTPMap_measure (M : POVM x a) :
    (Channel.measure M).toCPTPMap = M.toPOVM.measureDiscard := by
  rw [CPTPOp.funext_iff]
  intro rho
  refine DensityOp.ext_m ?_
  rw [CPTPOp.mat_coe_eq_apply_mat, Channel.map_toCPTPMap, Channel.measure_map,
    _root_.POVM.measureDiscard_apply, MState.ofClassical, DensityOp.m_ofMat,
    HermitianMat.diagonal_mat, ← Matrix.sum_single_eq_diagonal]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.smul_single, smul_eq_mul, mul_one]
  exact congrArg (Matrix.single y y) (POVM.coe_measure_toPOVM M rho y).symm

end QIT
