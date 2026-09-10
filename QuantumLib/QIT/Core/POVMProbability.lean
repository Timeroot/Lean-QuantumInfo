/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Core.Channel
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Data.NNReal.Basic

/-!
# POVM outcome probabilities

Finite POVM outcome probabilities are extracted from the measured classical
state of `POVM.measureDiscard`, following the Born-rule measurement map
[Tomamichel2015FiniteResources, prelim.tex:813-817].

`compressByIsometry`, `reindex` and `tensorRightIdentity` move a POVM to another system — along an
isometry, along a relabelling, and by padding with an unmeasured right register — and each comes
with the statement that the outcome probabilities are unchanged.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace POVM

open QIT

universe u v w

noncomputable section

variable {y : Type u} {a : Type v}
variable [Fintype y] [DecidableEq y] [Fintype a] [DecidableEq a]

/-- The Born-rule probability of outcome `outcome` for state `rho`. -/
def prob (M : POVM y a) (rho : MState a) (outcome : y) : ℝ≥0 :=
  let sigma := (POVM.measureDiscard M) rho
  ⟨Complex.re (sigma.m outcome outcome),
    (Complex.nonneg_iff.mp (sigma.psd.diag_nonneg (i := outcome))).1⟩

/-- POVM outcome probabilities sum to one. -/
theorem sum_prob (M : POVM y a) (rho : MState a) :
    ∑ outcome, M.prob rho outcome = 1 := by
  let sigma := (POVM.measureDiscard M) rho
  change ∑ outcome, (⟨Complex.re (sigma.m outcome outcome),
    (Complex.nonneg_iff.mp (sigma.psd.diag_nonneg (i := outcome))).1⟩ : ℝ≥0) = 1
  apply NNReal.eq
  have htrace_re : Complex.re sigma.m.trace = 1 := by
    rw [sigma.tr']
    simp
  rw [Matrix.trace, Complex.re_sum] at htrace_re
  let f : y → ℝ≥0 := fun outcome =>
    ⟨Complex.re (sigma.m outcome outcome),
      (Complex.nonneg_iff.mp (sigma.psd.diag_nonneg (i := outcome))).1⟩
  change ((∑ outcome, f outcome : ℝ≥0) : ℝ) = (1 : ℝ)
  calc
    ((∑ outcome, f outcome : ℝ≥0) : ℝ) =
        ∑ outcome, (f outcome : ℝ) := by
      simp
    _ = ∑ outcome, Complex.re (sigma.m outcome outcome) := by
      refine Finset.sum_congr rfl fun outcome _ => ?_
      rfl
    _ = 1 := by simpa using htrace_re

/-- A single POVM outcome probability is at most one. -/
theorem prob_le_one (M : POVM y a) (rho : MState a) (outcome : y) :
    (M.prob rho outcome : ℝ) ≤ 1 := by
  have hle_nn :
      M.prob rho outcome ≤ ∑ y, M.prob rho y :=
    Finset.single_le_sum
      (fun y _ => (show (0 : ℝ≥0) ≤ M.prob rho y from zero_le))
      (Finset.mem_univ outcome)
  rw [M.sum_prob rho] at hle_nn
  exact_mod_cast hle_nn

/-- The `NNReal` probability is the real part of the Born-rule trace formula. -/
theorem prob_eq_trace_re (M : POVM y a) (rho : MState a) (outcome : y) :
    (M.prob rho outcome : ℝ) =
      Complex.re ((rho.m * M.effects outcome).trace) := by
  unfold prob
  change Complex.re (((POVM.measureDiscard M) rho).m outcome outcome) =
    Complex.re ((rho.m * M.effects outcome).trace)
  rw [CPTPOp.mat_coe_eq_apply_mat, POVM.measureDiscard_map_state_diagonal M rho]
  simp [Matrix.diagonal]

variable {b : Type w} [Fintype b] [DecidableEq b]

/-- The state obtained by embedding a system into a larger finite space through
an isometry. -/
def isometryLiftState (rho : MState a) (V : Matrix b a ℂ)
    (_hV : Matrix.conjTranspose V * V = 1) : MState b := .ofMatrix
  (matrix := V * rho.m * Matrix.conjTranspose V)
  (pos := rho.psd.mul_mul_conjTranspose_same V)
  (trace_eq_one := by
    calc
      (V * rho.m * Matrix.conjTranspose V).trace =
          ((Matrix.conjTranspose V * V) * rho.m).trace := by
            rw [Matrix.trace_mul_cycle]
      _ = rho.m.trace := by
            rw [_hV, Matrix.one_mul]
      _ = 1 := rho.tr')

@[simp]
theorem isometryLiftState_matrix (rho : MState a) (V : Matrix b a ℂ)
    (hV : Matrix.conjTranspose V * V = 1) :
    (isometryLiftState rho V hV).m = V * rho.m * Matrix.conjTranspose V :=
  MState.matrix_ofMatrix _ _ _

/-- Born-rule probabilities are preserved by compressing a POVM along the same
isometry used to lift the state. -/
theorem compressByIsometry_prob_eq (M : POVM y b) (rho : MState a)
    (V : Matrix b a ℂ) (hV : Matrix.conjTranspose V * V = 1) (outcome : y) :
    ((M.compressByIsometry V hV).prob rho outcome : ℝ) =
      (M.prob (isometryLiftState rho V hV) outcome : ℝ) := by
  rw [prob_eq_trace_re, prob_eq_trace_re, isometryLiftState_matrix]
  change Complex.re ((rho.m *
      (Matrix.conjTranspose V * M.effects outcome * V)).trace) =
    Complex.re (((V * rho.m * Matrix.conjTranspose V) *
      M.effects outcome).trace)
  congr 1
  calc
    (rho.m * (Matrix.conjTranspose V * M.effects outcome * V)).trace =
        ((rho.m * Matrix.conjTranspose V * M.effects outcome) * V).trace := by
          simp only [Matrix.mul_assoc]
    _ = (V * (rho.m * Matrix.conjTranspose V * M.effects outcome)).trace := by
          rw [Matrix.trace_mul_comm]
    _ = ((V * rho.m * Matrix.conjTranspose V) * M.effects outcome).trace := by
          simp only [Matrix.mul_assoc]

/-- Relabel the measured system of a finite POVM. -/
def reindex (M : POVM y a) (e : a ≃ b) : POVM y b :=
  .ofMatrices (fun outcome => Matrix.reindex e e (M.effects outcome))
    (fun outcome => (M.pos outcome).submatrix e.symm) <| by
    ext i j
    have h := congrFun (congrFun M.sum_eq_one (e.symm i)) (e.symm j)
    simpa [Matrix.sum_apply, Matrix.reindex_apply, Matrix.one_apply] using h

omit [DecidableEq y] in
@[simp]
theorem reindex_effects (M : POVM y a) (e : a ≃ b) (outcome : y) :
    (M.reindex e).effects outcome = Matrix.reindex e e (M.effects outcome) :=
  rfl

/-- Born probabilities are invariant under simultaneous state/effect relabelling. -/
theorem prob_reindex_state (M : POVM y a) (rho : MState a) (e : a ≃ b) (outcome : y) :
    ((M.reindex e).prob (rho.reindex e) outcome : ℝ) = (M.prob rho outcome : ℝ) := by
  rw [prob_eq_trace_re, prob_eq_trace_re]
  simp only [MState.reindex_matrix]
  change Complex.re
      (((Matrix.reindex e e rho.m) *
        (Matrix.reindex e e (M.effects outcome))).trace) =
    Complex.re ((rho.m * M.effects outcome).trace)
  change Complex.re
      ((((Matrix.reindexAlgEquiv ℂ ℂ e) rho.m) *
        ((Matrix.reindexAlgEquiv ℂ ℂ e) (M.effects outcome))).trace) =
    Complex.re ((rho.m * M.effects outcome).trace)
  rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ e) rho.m (M.effects outcome)]
  change Complex.re ((Matrix.reindex e e (rho.m * M.effects outcome)).trace) =
    Complex.re ((rho.m * M.effects outcome).trace)
  rw [cMatrix_trace_reindex e]

/-- Extend a POVM to a product system by measuring the right factor with the identity effect. -/
def tensorRightIdentity (M : POVM y a) (tail : Type w) [Fintype tail] [DecidableEq tail] :
    POVM y (a × tail) :=
  .ofMatrices (fun outcome => Matrix.kronecker (M.effects outcome) (1 : CMatrix tail))
    (fun outcome => (M.pos outcome).kronecker Matrix.PosSemidef.one) <| by
    ext i j
    simp only [Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
    rw [← Finset.sum_mul]
    have hsum :
        (∑ outcome, M.effects outcome i.1 j.1) = (1 : CMatrix a) i.1 j.1 := by
      simpa [Matrix.sum_apply] using congrFun (congrFun M.sum_eq_one i.1) j.1
    rw [hsum]
    by_cases hleft : i.1 = j.1
    · by_cases hright : i.2 = j.2
      · have hij : i = j := Prod.ext hleft hright
        simp [Matrix.one_apply, hij]
      · have hij : i ≠ j := fun h => hright (congrArg Prod.snd h)
        simp [Matrix.one_apply, hleft, hright, hij]
    · have hij : i ≠ j := fun h => hleft (congrArg Prod.fst h)
      simp [Matrix.one_apply, hleft, hij]

/-- Ignoring an auxiliary right register preserves the original Born probability on product
states. -/
theorem tensorRightIdentity_prob_prod {tail : Type w} [Fintype tail] [DecidableEq tail]
    (M : POVM y a) (rho : MState a) (sigma : MState tail) (outcome : y) :
    ((M.tensorRightIdentity tail).prob (rho.prod sigma) outcome : ℝ) =
      (M.prob rho outcome : ℝ) := by
  rw [prob_eq_trace_re, prob_eq_trace_re, MState.prod_m]
  change Complex.re
      (((Matrix.kronecker rho.m sigma.m) *
        Matrix.kronecker (M.effects outcome) (1 : CMatrix tail)).trace) =
    Complex.re ((rho.m * M.effects outcome).trace)
  have hmul :
      Matrix.kronecker rho.m sigma.m *
          Matrix.kronecker (M.effects outcome) (1 : CMatrix tail) =
        Matrix.kronecker (rho.m * M.effects outcome) (sigma.m * 1) :=
    (Matrix.mul_kronecker_mul rho.m (M.effects outcome) sigma.m
      (1 : CMatrix tail)).symm
  rw [hmul, Matrix.mul_one]
  change Complex.re ((Matrix.kronecker (rho.m * M.effects outcome) sigma.m).trace) =
    Complex.re ((rho.m * M.effects outcome).trace)
  have htrace :
      (Matrix.kronecker (rho.m * M.effects outcome) sigma.m).trace =
        (rho.m * M.effects outcome).trace * sigma.m.trace :=
    Matrix.trace_kronecker (rho.m * M.effects outcome) sigma.m
  rw [htrace, sigma.tr']
  simp

end

end POVM
