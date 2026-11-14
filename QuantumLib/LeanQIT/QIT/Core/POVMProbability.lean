/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Channel
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Data.NNReal.Basic

/-!
# POVM outcome probabilities

Finite POVM outcome probabilities are extracted from the measured classical
state of `Channel.measure`, following the Born-rule measurement map
[Tomamichel2015FiniteResources, prelim.tex:813-817].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v w

noncomputable section

namespace POVM

variable {y : Type u} {a : Type v}
variable [Fintype y] [DecidableEq y] [Fintype a] [DecidableEq a]

/-- The Born-rule probability of outcome `outcome` for state `rho`. -/
def prob (M : POVM y a) (rho : State a) (outcome : y) : ℝ≥0 :=
  let sigma := (Channel.measure M).applyState rho
  ⟨Complex.re (sigma.matrix outcome outcome),
    (Complex.nonneg_iff.mp (sigma.pos.diag_nonneg (i := outcome))).1⟩

/-- POVM outcome probabilities sum to one. -/
theorem sum_prob (M : POVM y a) (rho : State a) :
    ∑ outcome, M.prob rho outcome = 1 := by
  let sigma := (Channel.measure M).applyState rho
  change ∑ outcome, (⟨Complex.re (sigma.matrix outcome outcome),
    (Complex.nonneg_iff.mp (sigma.pos.diag_nonneg (i := outcome))).1⟩ : ℝ≥0) = 1
  apply NNReal.eq
  have htrace_re : Complex.re sigma.matrix.trace = 1 := by
    rw [sigma.trace_eq_one]
    simp
  rw [Matrix.trace, Complex.re_sum] at htrace_re
  let f : y → ℝ≥0 := fun outcome =>
    ⟨Complex.re (sigma.matrix outcome outcome),
      (Complex.nonneg_iff.mp (sigma.pos.diag_nonneg (i := outcome))).1⟩
  change ((∑ outcome, f outcome : ℝ≥0) : ℝ) = (1 : ℝ)
  calc
    ((∑ outcome, f outcome : ℝ≥0) : ℝ) =
        ∑ outcome, (f outcome : ℝ) := by
      simp
    _ = ∑ outcome, Complex.re (sigma.matrix outcome outcome) := by
      refine Finset.sum_congr rfl fun outcome _ => ?_
      rfl
    _ = 1 := by simpa using htrace_re

/-- A single POVM outcome probability is at most one. -/
theorem prob_le_one (M : POVM y a) (rho : State a) (outcome : y) :
    (M.prob rho outcome : ℝ) ≤ 1 := by
  have hle_nn :
      M.prob rho outcome ≤ ∑ y, M.prob rho y :=
    Finset.single_le_sum
      (fun y _ => (show (0 : ℝ≥0) ≤ M.prob rho y from zero_le))
      (Finset.mem_univ outcome)
  rw [M.sum_prob rho] at hle_nn
  exact_mod_cast hle_nn

/-- The `NNReal` probability is the real part of the Born-rule trace formula. -/
theorem prob_eq_trace_re (M : POVM y a) (rho : State a) (outcome : y) :
    (M.prob rho outcome : ℝ) =
      Complex.re ((rho.matrix * M.effects outcome).trace) := by
  unfold prob
  simp only
  change Complex.re (((Channel.measure M).map rho.matrix) outcome outcome) =
    Complex.re ((rho.matrix * M.effects outcome).trace)
  rw [Channel.measure_map_state_diagonal M rho]
  simp [Matrix.diagonal]

variable {b : Type w} [Fintype b] [DecidableEq b]

/-- The state obtained by embedding a system into a larger finite space through
an isometry. -/
def isometryLiftState (rho : State a) (V : Matrix b a ℂ)
    (_hV : Matrix.conjTranspose V * V = 1) : State b where
  matrix := V * rho.matrix * Matrix.conjTranspose V
  pos := rho.pos.mul_mul_conjTranspose_same V
  trace_eq_one := by
    calc
      (V * rho.matrix * Matrix.conjTranspose V).trace =
          ((Matrix.conjTranspose V * V) * rho.matrix).trace := by
            rw [Matrix.trace_mul_cycle]
      _ = rho.matrix.trace := by
            rw [_hV, Matrix.one_mul]
      _ = 1 := rho.trace_eq_one

@[simp]
theorem isometryLiftState_matrix (rho : State a) (V : Matrix b a ℂ)
    (hV : Matrix.conjTranspose V * V = 1) :
    (isometryLiftState rho V hV).matrix = V * rho.matrix * Matrix.conjTranspose V :=
  rfl

/-- Born-rule probabilities are preserved by compressing a POVM along the same
isometry used to lift the state. -/
theorem compressByIsometry_prob_eq (M : POVM y b) (rho : State a)
    (V : Matrix b a ℂ) (hV : Matrix.conjTranspose V * V = 1) (outcome : y) :
    ((M.compressByIsometry V hV).prob rho outcome : ℝ) =
      (M.prob (isometryLiftState rho V hV) outcome : ℝ) := by
  rw [prob_eq_trace_re, prob_eq_trace_re]
  change Complex.re ((rho.matrix *
      (Matrix.conjTranspose V * M.effects outcome * V)).trace) =
    Complex.re (((V * rho.matrix * Matrix.conjTranspose V) *
      M.effects outcome).trace)
  congr 1
  calc
    (rho.matrix * (Matrix.conjTranspose V * M.effects outcome * V)).trace =
        ((rho.matrix * Matrix.conjTranspose V * M.effects outcome) * V).trace := by
          simp only [Matrix.mul_assoc]
    _ = (V * (rho.matrix * Matrix.conjTranspose V * M.effects outcome)).trace := by
          rw [Matrix.trace_mul_comm]
    _ = ((V * rho.matrix * Matrix.conjTranspose V) * M.effects outcome).trace := by
          simp only [Matrix.mul_assoc]

end POVM

end

end QIT
