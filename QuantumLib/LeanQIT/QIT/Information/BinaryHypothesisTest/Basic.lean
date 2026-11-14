/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States
public import QIT.States.TraceNorm.Audenaert
public import QIT.States.Schatten
public import QIT.Information.Renyi.Renyi
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Binary hypothesis test spectral API: basic quantum Chernoff quantities

This module contains the matrix/unitary helpers and the quantum Petz-Renyi
Chernoff coefficient, exponent, and Chernoff-distance definitions for states.
The API lives at information layer L2 because its consumers (RenyiLimit and
MutualInformationDPI) are L2, while QIT/Classical is reserved for classical-state
infrastructure.  These declarations were relocated from
QIT/HypothesisTesting/ChernoffSupport.lean as part of the L3-to-L2 layering cleanup.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal ENNReal Topology
open Filter Matrix Polynomial

namespace QIT

universe u v

noncomputable section

theorem cMatrix_rpow_kronecker
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A : CMatrix a} {B : CMatrix b} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {s : ℝ} (hs0 : 0 ≤ s) :
    CFC.rpow (Matrix.kronecker A B) s =
      Matrix.kronecker (CFC.rpow A s) (CFC.rpow B s) :=
  cMatrix_rpow_kronecker_nonneg hA hB hs0

private theorem matrix_mul_star_diag_re_eq_normSq_sum {n : Type u}
    [Fintype n] [DecidableEq n] (A : CMatrix n) (i : n) :
    ((A * star A) i i).re = ∑ j, Complex.normSq (A i j) := by
  simp [Matrix.mul_apply, Complex.normSq]

theorem projection_conjugate_diag_re_eq_row_normSq {n : Type u}
    [Fintype n] [DecidableEq n] (P : CMatrix n)
    (hPherm : P.IsHermitian) (hPidem : P * P = P)
    (U V : Matrix.unitaryGroup n ℂ) (i : n) :
    ((star (U : CMatrix n) * P * (U : CMatrix n)) i i).re =
      ∑ j, Complex.normSq ((star (U : CMatrix n) * P * (V : CMatrix n)) i j) := by
  let A : CMatrix n := star (U : CMatrix n) * P * (V : CMatrix n)
  have hAA :
      A * star A = star (U : CMatrix n) * P * (U : CMatrix n) := by
    have hV : (V : CMatrix n) * star (V : CMatrix n) = 1 :=
      Unitary.coe_mul_star_self V
    have hPstar : star P = P := hPherm
    simp [A, Matrix.mul_assoc]
    calc
      star (U : CMatrix n) * (P * ((V : CMatrix n) *
          (star (V : CMatrix n) * (star P * (U : CMatrix n))))) =
          star (U : CMatrix n) * (P *
            (((V : CMatrix n) * star (V : CMatrix n)) * (star P * (U : CMatrix n)))) := by
            rw [Matrix.mul_assoc]
      _ = star (U : CMatrix n) * (P * (1 * (star P * (U : CMatrix n)))) := by
            rw [hV]
      _ = star (U : CMatrix n) * (P * (P * (U : CMatrix n))) := by
            rw [hPstar]
            simp
      _ = star (U : CMatrix n) * ((P * P) * (U : CMatrix n)) := by
            rw [Matrix.mul_assoc]
      _ = star (U : CMatrix n) * (P * (U : CMatrix n)) := by
            rw [hPidem]
  have hdiag := congrFun (congrFun hAA i) i
  have hre := congrArg Complex.re hdiag
  rw [← hre]
  exact matrix_mul_star_diag_re_eq_normSq_sum A i

theorem trace_mul_unitary_conj_diagonal_ofReal_arbitrary_re {n : Type u}
    [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ) (B : CMatrix n) :
    ((((U : CMatrix n) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix n)) * B).trace).re =
      ∑ i : n, d i *
        ((star (U : CMatrix n) * B * (U : CMatrix n)) i i).re := by
  let D : CMatrix n := Matrix.diagonal fun i => (d i : ℂ)
  let B' : CMatrix n := star (U : CMatrix n) * B * (U : CMatrix n)
  have htrace :
      (((U : CMatrix n) * D * star (U : CMatrix n)) * B).trace =
        (D * B').trace := by
    calc
      (((U : CMatrix n) * D * star (U : CMatrix n)) * B).trace =
          ((U : CMatrix n) * (D * (star (U : CMatrix n) * B))).trace := by
            congr 1
            noncomm_ring
      _ = ((D * (star (U : CMatrix n) * B)) * (U : CMatrix n)).trace := by
            exact Matrix.trace_mul_comm (U : CMatrix n)
              (D * (star (U : CMatrix n) * B))
      _ = (D * B').trace := by
            simp [B', Matrix.mul_assoc]
  have hdiag :
      (D * B').trace = ∑ i, ((d i : ℝ) : ℂ) * B' i i := by
    simp [D, Matrix.trace, Matrix.diagonal_mul]
  have hre := congrArg Complex.re (htrace.trans hdiag)
  simpa [B', Complex.mul_re] using hre

theorem complex_normSq_add_le_two_sum (z w : ℂ) :
    Complex.normSq (z + w) ≤ 2 * (Complex.normSq z + Complex.normSq w) := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hnorm : ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le z w
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  have hw : 0 ≤ ‖w‖ := norm_nonneg w
  have hzw : 0 ≤ ‖z + w‖ := norm_nonneg (z + w)
  nlinarith [sq_nonneg (‖z‖ - ‖w‖), mul_self_nonneg (‖z + w‖), hnorm]

theorem half_min_weight_normSq_add_le_weighted_normSq
    {A B u v w : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw0 : 0 ≤ w)
    (hw : w ≤ 2 * (u + v)) :
    (1 / 2 : ℝ) * min (A * w) (B * w) ≤ A * u + B * v := by
  by_cases hAB : A ≤ B
  · have hmin : min (A * w) (B * w) = A * w := by
      exact min_eq_left (mul_le_mul_of_nonneg_right hAB hw0)
    rw [hmin]
    have hAw : A * w ≤ A * (2 * (u + v)) :=
      mul_le_mul_of_nonneg_left hw hA
    nlinarith
  · have hBA : B ≤ A := le_of_not_ge hAB
    have hmin : min (A * w) (B * w) = B * w := by
      exact min_eq_right (mul_le_mul_of_nonneg_right hBA hw0)
    rw [hmin]
    have hBw : B * w ≤ B * (2 * (u + v)) :=
      mul_le_mul_of_nonneg_left hw hB
    nlinarith


variable {a : Type u} [Fintype a] [DecidableEq a]

namespace State

/-- The Petz/Renyi Chernoff trace objective is real. -/
theorem petzRenyi_trace_im_eq_zero (rho sigma : State a) (s : ℝ) :
    ((CFC.rpow rho.matrix s * CFC.rpow sigma.matrix (1 - s)).trace).im = 0 :=
  trace_mul_posSemidef_im_eq_zero (rho.rpowMatrix_posSemidef s)
    (sigma.rpowMatrix_posSemidef (1 - s))

/-- The Petz/Renyi Chernoff trace objective is nonnegative. -/
theorem petzRenyi_trace_re_nonneg (rho sigma : State a) (s : ℝ) :
    0 ≤ ((CFC.rpow rho.matrix s * CFC.rpow sigma.matrix (1 - s)).trace).re :=
  trace_mul_posSemidef_re_nonneg (rho.rpowMatrix_posSemidef s)
    (sigma.rpowMatrix_posSemidef (1 - s))

/-- Nonnegative real coefficient `Tr(ρ^s σ^(1-s))` used by the Chernoff objective. -/
def petzRenyiCoefficient (rho sigma : State a) (s : ℝ) : ℝ≥0 :=
  ⟨((CFC.rpow rho.matrix s * CFC.rpow sigma.matrix (1 - s)).trace).re,
    rho.petzRenyi_trace_re_nonneg sigma s⟩

/-- Under full-rank hypotheses, the Petz/Renyi Chernoff coefficient is strictly positive. -/
theorem petzRenyiCoefficient_pos_of_posDef (rho sigma : State a)
    (hρ : rho.matrix.PosDef) (hσ : sigma.matrix.PosDef) (s : ℝ) :
    0 < rho.petzRenyiCoefficient sigma s := by
  haveI : Nonempty a := rho.nonempty
  dsimp [petzRenyiCoefficient]
  exact trace_mul_posDef_re_pos
    (rho.rpowMatrix_posDef_of_posDef hρ s)
    (sigma.rpowMatrix_posDef_of_posDef hσ (1 - s))

/-- The nonnegative coefficient is exactly the complex trace objective. -/
theorem petzRenyiCoefficient_trace_eq (rho sigma : State a) (s : ℝ) :
    ((rho.petzRenyiCoefficient sigma s : ℝ) : ℂ) =
      (CFC.rpow rho.matrix s * CFC.rpow sigma.matrix (1 - s)).trace := by
  apply Complex.ext
  · rfl
  · simpa [petzRenyiCoefficient] using (rho.petzRenyi_trace_im_eq_zero sigma s).symm

theorem petzRenyiCoefficient_prod {b : Type v} [Fintype b] [DecidableEq b]
    (rho₁ sigma₁ : State a) (rho₂ sigma₂ : State b)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (rho₁.prod rho₂).petzRenyiCoefficient (sigma₁.prod sigma₂) s =
      rho₁.petzRenyiCoefficient sigma₁ s * rho₂.petzRenyiCoefficient sigma₂ s := by
  apply NNReal.eq
  apply Complex.ofReal_injective
  calc
    (((rho₁.prod rho₂).petzRenyiCoefficient (sigma₁.prod sigma₂) s : ℝ) : ℂ) =
        (CFC.rpow (rho₁.prod rho₂).matrix s *
          CFC.rpow (sigma₁.prod sigma₂).matrix (1 - s)).trace := by
      exact State.petzRenyiCoefficient_trace_eq (rho₁.prod rho₂) (sigma₁.prod sigma₂) s
    _ =
        ((CFC.rpow rho₁.matrix s * CFC.rpow sigma₁.matrix (1 - s)).trace) *
          ((CFC.rpow rho₂.matrix s * CFC.rpow sigma₂.matrix (1 - s)).trace) := by
      rw [prod_matrix_kronecker rho₁ rho₂, prod_matrix_kronecker sigma₁ sigma₂]
      rw [cMatrix_rpow_kronecker rho₁.pos rho₂.pos hs0]
      rw [cMatrix_rpow_kronecker sigma₁.pos sigma₂.pos (sub_nonneg.mpr hs1)]
      change
        (Matrix.kroneckerMap (fun x y => x * y)
            (CFC.rpow rho₁.matrix s) (CFC.rpow rho₂.matrix s) *
          Matrix.kroneckerMap (fun x y => x * y)
            (CFC.rpow sigma₁.matrix (1 - s)) (CFC.rpow sigma₂.matrix (1 - s))).trace =
        (CFC.rpow rho₁.matrix s * CFC.rpow sigma₁.matrix (1 - s)).trace *
          (CFC.rpow rho₂.matrix s * CFC.rpow sigma₂.matrix (1 - s)).trace
      rw [← Matrix.mul_kronecker_mul]
      rw [Matrix.trace_kronecker]
    _ = (((rho₁.petzRenyiCoefficient sigma₁ s *
          rho₂.petzRenyiCoefficient sigma₂ s : ℝ≥0) : ℝ) : ℂ) := by
      rw [← State.petzRenyiCoefficient_trace_eq rho₁ sigma₁ s]
      rw [← State.petzRenyiCoefficient_trace_eq rho₂ sigma₂ s]
      simp

theorem petzRenyiCoefficient_tensorPower (rho sigma : State a)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n : Nat) :
    (rho.tensorPower n).petzRenyiCoefficient (sigma.tensorPower n) s =
      rho.petzRenyiCoefficient sigma s ^ n := by
  induction n with
  | zero =>
      rw [State.tensorPower_zero, State.tensorPower_zero]
      apply NNReal.eq
      apply Complex.ofReal_injective
      rw [State.petzRenyiCoefficient_trace_eq]
      change (((1 : CMatrix PUnit) ^ s * (1 : CMatrix PUnit) ^ (1 - s)).trace) = 1
      rw [CFC.one_rpow, CFC.one_rpow, one_mul, Matrix.trace_one]
      norm_num
  | succ n ih =>
      rw [State.tensorPower_succ, State.tensorPower_succ]
      calc
        (rho.prod (rho.tensorPower n)).petzRenyiCoefficient
            (sigma.prod (sigma.tensorPower n)) s =
            rho.petzRenyiCoefficient sigma s *
              (rho.tensorPower n).petzRenyiCoefficient (sigma.tensorPower n) s := by
          exact petzRenyiCoefficient_prod rho sigma (rho.tensorPower n) (sigma.tensorPower n)
            hs0 hs1
        _ = rho.petzRenyiCoefficient sigma s ^ (n + 1) := by
          rw [ih]
          simp [pow_succ, mul_comm]
/-- Extended-real Chernoff exponent `-log Tr(ρ^s σ^(1-s))`. -/
def petzChernoffExponent (rho sigma : State a) (s : ℝ) : EReal :=
  - ENNReal.log (rho.petzRenyiCoefficient sigma s : ℝ≥0∞)

/-- A zero Petz/Renyi coefficient gives infinite extended Chernoff exponent. -/
theorem petzChernoffExponent_eq_top_of_petzRenyiCoefficient_eq_zero
    (rho sigma : State a) (s : ℝ)
    (h : rho.petzRenyiCoefficient sigma s = 0) :
    rho.petzChernoffExponent sigma s = ⊤ := by
  simp [petzChernoffExponent, h]

/-- A positive Petz/Renyi coefficient gives the finite real-log Chernoff exponent. -/
theorem petzChernoffExponent_eq_coe_neg_log_of_petzRenyiCoefficient_pos
    (rho sigma : State a) (s : ℝ)
    (h : 0 < rho.petzRenyiCoefficient sigma s) :
    rho.petzChernoffExponent sigma s =
      ((- Real.log (rho.petzRenyiCoefficient sigma s : ℝ) : ℝ) : EReal) := by
  have h0 : (rho.petzRenyiCoefficient sigma s : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast h.ne'
  have htop : ((rho.petzRenyiCoefficient sigma s : ℝ≥0∞) ≠ ⊤) := by
    simp
  simp [petzChernoffExponent, ENNReal.log_pos_real h0 htop, EReal.coe_neg]

theorem petzChernoffExponent_tensorPower (rho sigma : State a)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n : Nat) :
    (rho.tensorPower n).petzChernoffExponent (sigma.tensorPower n) s =
      (n : EReal) * rho.petzChernoffExponent sigma s := by
  unfold State.petzChernoffExponent
  rw [State.petzRenyiCoefficient_tensorPower rho sigma hs0 hs1 n]
  rw [show ((rho.petzRenyiCoefficient sigma s ^ n : ℝ≥0) : ℝ≥0∞) =
      (rho.petzRenyiCoefficient sigma s : ℝ≥0∞) ^ n by norm_num]
  rw [ENNReal.log_pow]
  rw [mul_neg]

/-- Base-2 Chernoff exponent `-log₂ Tr(ρ^s σ^(1-s))`.

The existing `petzChernoffExponent` uses natural logarithms through
`ENNReal.log`; this real-valued companion uses the repository's `log2`
convention so it can be compared directly with `State.petzRenyi`. -/
def petzChernoffExponentLog2 (rho sigma : State a) (s : ℝ) : ℝ :=
  - log2 (rho.petzRenyiCoefficient sigma s : ℝ)

/-- The base-2 Chernoff exponent is `(1-s)` times the Petz Renyi divergence. -/
theorem petzChernoffExponentLog2_eq_one_sub_mul_petzRenyi
    (rho sigma : State a) (hρ : rho.matrix.PosDef) (hσ : sigma.matrix.PosDef)
    (s : ℝ) (hs_pos : 0 < s) (hs_ne_one : s ≠ 1) :
    rho.petzChernoffExponentLog2 sigma s =
      (1 - s) * rho.petzRenyi sigma hρ hσ s hs_pos hs_ne_one := by
  unfold petzChernoffExponentLog2 petzRenyi
  change
    - log2 ((CFC.rpow rho.matrix s * CFC.rpow sigma.matrix (1 - s)).trace.re) =
      (1 - s) *
        ((1 / (s - 1)) *
          log2 ((CFC.rpow rho.matrix s * CFC.rpow sigma.matrix (1 - s)).trace.re))
  unfold log2
  field_simp [hs_ne_one]
  ring

/-- Chernoff distance as the supremum of the extended-real Chernoff exponent over `0 ≤ s ≤ 1`. -/
def chernoffDistance (rho sigma : State a) : EReal :=
  ⨆ s : Set.Icc (0 : ℝ) 1, rho.petzChernoffExponent sigma s.1
end State


end

end QIT
