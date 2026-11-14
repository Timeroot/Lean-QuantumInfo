/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.HypothesisTesting.ChernoffSupport

/-!
# Asymptotic quantum Chernoff bound

This module owns the tensor-power quantum-to-classical comparison route and the
final asymptotic quantum Chernoff bound theorem.  Reusable Chernoff and
Nussbaum--Szkola support lives in `QIT.HypothesisTesting.ChernoffSupport` so
Renyi endpoint code can depend on that lower layer without importing this final
theorem module.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal ENNReal Topology
open Filter Matrix Polynomial

namespace QIT

universe u v

noncomputable section

namespace BinaryHypothesisTest

variable {a : Type u} [Fintype a] [DecidableEq a]
/-- Genuine product Nussbaum--Szkola classical model over the `n`-fold product
alphabet `(a × a)^n`. -/
def nussbaumSzkolaProductModel (rho sigma : State a) (n : Nat) :
    ClassicalBinaryModel (TensorPower (a × a) n) :=
  (nussbaumSzkolaModel rho sigma).tensorPower n

/-- Equal-prior Bayesian error of the genuine product Nussbaum--Szkola
classical model. -/
def nussbaumSzkolaProductClassicalError (rho sigma : State a) (n : Nat) : ℝ≥0∞ :=
  (nussbaumSzkolaProductModel rho sigma n).equalPriorErrorENNReal

/-- The canonical product Nussbaum--Szkola `p` distribution is the product
spectral weight times the product transition overlap. -/
theorem nussbaumSzkolaProductModel_p_eq
    (rho sigma : State a) (n : Nat) (x y : TensorPower a n) :
    (nussbaumSzkolaProductModel rho sigma n).p
        ((tensorPowerProdEquiv a a n).symm (x, y)) =
      tensorPowerSpectralWeight rho n x *
        tensorPowerNussbaumSzkolaOverlap rho sigma n x y := by
  induction n with
  | zero =>
      cases x
      cases y
      simp [nussbaumSzkolaProductModel, ClassicalBinaryModel.tensorPower,
        tensorPowerProdEquiv, tensorPowerSpectralWeight,
        tensorPowerNussbaumSzkolaOverlap]
  | succ n ih =>
      rcases x with ⟨x0, xs⟩
      rcases y with ⟨y0, ys⟩
      change
        (stateSpectralWeight rho x0 * nussbaumSzkolaOverlap rho sigma x0 y0) *
            (nussbaumSzkolaProductModel rho sigma n).p
              ((tensorPowerProdEquiv a a n).symm (xs, ys)) =
          (stateSpectralWeight rho x0 * tensorPowerSpectralWeight rho n xs) *
            (nussbaumSzkolaOverlap rho sigma x0 y0 *
              tensorPowerNussbaumSzkolaOverlap rho sigma n xs ys)
      rw [ih xs ys]
      ac_rfl

/-- The canonical product Nussbaum--Szkola `q` distribution is the product
sigma spectral weight times the product transition overlap. -/
theorem nussbaumSzkolaProductModel_q_eq
    (rho sigma : State a) (n : Nat) (x y : TensorPower a n) :
    (nussbaumSzkolaProductModel rho sigma n).q
        ((tensorPowerProdEquiv a a n).symm (x, y)) =
      tensorPowerSpectralWeight sigma n y *
        tensorPowerNussbaumSzkolaOverlap rho sigma n x y := by
  induction n with
  | zero =>
      cases x
      cases y
      simp [nussbaumSzkolaProductModel, ClassicalBinaryModel.tensorPower,
        tensorPowerProdEquiv, tensorPowerSpectralWeight,
        tensorPowerNussbaumSzkolaOverlap]
  | succ n ih =>
      rcases x with ⟨x0, xs⟩
      rcases y with ⟨y0, ys⟩
      change
        (stateSpectralWeight sigma y0 * nussbaumSzkolaOverlap rho sigma x0 y0) *
            (nussbaumSzkolaProductModel rho sigma n).q
              ((tensorPowerProdEquiv a a n).symm (xs, ys)) =
          (stateSpectralWeight sigma y0 * tensorPowerSpectralWeight sigma n ys) *
            (nussbaumSzkolaOverlap rho sigma x0 y0 *
              tensorPowerNussbaumSzkolaOverlap rho sigma n xs ys)
      rw [ih xs ys]
      ac_rfl

/-- Source-shaped finite comparison obligation for the genuine product
Nussbaum--Szkola classical sequence.

Unlike `HasNussbaumSzkolaFiniteComparison`, this predicate does not force the
classical sequence to be the spectral Nussbaum--Szkola model of tensor-power
states.  It pins the sequence to the canonical product model over
`(a × a)^n`, avoiding noncanonical choices in degenerate tensor-power
eigenspaces [Gour2024Resources, BookQRT.tex:15911-15949]. -/
def HasNussbaumSzkolaProductFiniteComparison
    (rho sigma : State a) (classicalError : Nat → ℝ≥0∞) : Prop :=
  classicalError = nussbaumSzkolaProductClassicalError rho sigma ∧
    ∀ n : Nat,
      quantumChernoffConverseComparisonConstant * classicalError n ≤
        optimalEqualPriorTensorPowerError rho sigma n

/-- Product Nussbaum--Szkola models have multiplicative classical Petz/Chernoff
coefficient. -/
theorem nussbaumSzkolaProductModel_petzChernoffCoefficient_eq_pow
    (rho sigma : State a) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n : Nat) :
    (nussbaumSzkolaProductModel rho sigma n).petzChernoffCoefficient s =
      rho.petzRenyiCoefficient sigma s ^ n := by
  calc
    (nussbaumSzkolaProductModel rho sigma n).petzChernoffCoefficient s =
        (nussbaumSzkolaModel rho sigma).petzChernoffCoefficient s ^ n := by
          exact ClassicalBinaryModel.tensorPower_petzChernoffCoefficient
            (nussbaumSzkolaModel rho sigma) s n
    _ = rho.petzRenyiCoefficient sigma s ^ n := by
          rw [nussbaumSzkolaModel_petzChernoffCoefficient_eq rho sigma hs0 hs1]

theorem tensorPower_trace_one_sub_projection_re_eq_nussbaumSzkolaProduct_source_sum
    (rho sigma : State a) (n : Nat) {P : CMatrix (TensorPower a n)}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    (((rho.tensorPower n).matrix * (1 - P)).trace).re =
      ∑ x : TensorPower a n, (tensorPowerSpectralWeight rho n x : ℝ) *
        ∑ y : TensorPower a n,
          Complex.normSq
            ((star (tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n :
                CMatrix (TensorPower a n)) *
                (1 - P) *
              (tensorPowerUnitary sigma.pos.isHermitian.eigenvectorUnitary n :
                CMatrix (TensorPower a n))) x y) := by
  classical
  let UrhoN : Matrix.unitaryGroup (TensorPower a n) ℂ :=
    tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n
  let UsigmaN : Matrix.unitaryGroup (TensorPower a n) ℂ :=
    tensorPowerUnitary sigma.pos.isHermitian.eigenvectorUnitary n
  have hdiag := tensorPower_matrix_eq_tensorPowerUnitary_diagonal rho n
  have htrace :=
    trace_mul_unitary_conj_diagonal_ofReal_arbitrary_re
      UrhoN (fun x : TensorPower a n => (tensorPowerSpectralWeight rho n x : ℝ))
      (1 - P)
  calc
    (((rho.tensorPower n).matrix * (1 - P)).trace).re =
        ((((UrhoN : CMatrix (TensorPower a n)) *
            (Matrix.diagonal
              fun x : TensorPower a n =>
                (((tensorPowerSpectralWeight rho n x : ℝ≥0) : ℝ) : ℂ)) *
              star (UrhoN : CMatrix (TensorPower a n))) *
            (1 - P)).trace).re := by
          rw [hdiag]
    _ = ∑ x : TensorPower a n, (tensorPowerSpectralWeight rho n x : ℝ) *
          ((star (UrhoN : CMatrix (TensorPower a n)) * (1 - P) *
            (UrhoN : CMatrix (TensorPower a n))) x x).re := by
          simpa [UrhoN] using htrace
    _ = ∑ x : TensorPower a n, (tensorPowerSpectralWeight rho n x : ℝ) *
          ∑ y : TensorPower a n,
            Complex.normSq
              ((star (UrhoN : CMatrix (TensorPower a n)) * (1 - P) *
                (UsigmaN : CMatrix (TensorPower a n))) x y) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [projection_conjugate_diag_re_eq_row_normSq
            (P := 1 - P)
            (projection_complement_isHermitian hPherm)
            (projection_complement_idempotent hPidem)
            UrhoN UsigmaN x]
    _ = ∑ x : TensorPower a n, (tensorPowerSpectralWeight rho n x : ℝ) *
          ∑ y : TensorPower a n,
            Complex.normSq
              ((star (tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n :
                  CMatrix (TensorPower a n)) *
                  (1 - P) *
                (tensorPowerUnitary sigma.pos.isHermitian.eigenvectorUnitary n :
                  CMatrix (TensorPower a n))) x y) := by
          rfl

theorem tensorPower_trace_projection_re_eq_nussbaumSzkolaProduct_source_sum
    (rho sigma : State a) (n : Nat) {P : CMatrix (TensorPower a n)}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    (((sigma.tensorPower n).matrix * P).trace).re =
      ∑ y : TensorPower a n, (tensorPowerSpectralWeight sigma n y : ℝ) *
        ∑ x : TensorPower a n,
          Complex.normSq
            ((star (tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n :
                CMatrix (TensorPower a n)) *
                P *
              (tensorPowerUnitary sigma.pos.isHermitian.eigenvectorUnitary n :
                CMatrix (TensorPower a n))) x y) := by
  classical
  let UrhoN : Matrix.unitaryGroup (TensorPower a n) ℂ :=
    tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n
  let UsigmaN : Matrix.unitaryGroup (TensorPower a n) ℂ :=
    tensorPowerUnitary sigma.pos.isHermitian.eigenvectorUnitary n
  have hdiag := tensorPower_matrix_eq_tensorPowerUnitary_diagonal sigma n
  have htrace :=
    trace_mul_unitary_conj_diagonal_ofReal_arbitrary_re
      UsigmaN (fun y : TensorPower a n => (tensorPowerSpectralWeight sigma n y : ℝ))
      P
  calc
    (((sigma.tensorPower n).matrix * P).trace).re =
        ((((UsigmaN : CMatrix (TensorPower a n)) *
            (Matrix.diagonal
              fun y : TensorPower a n =>
                (((tensorPowerSpectralWeight sigma n y : ℝ≥0) : ℝ) : ℂ)) *
              star (UsigmaN : CMatrix (TensorPower a n))) *
            P).trace).re := by
          rw [hdiag]
    _ = ∑ y : TensorPower a n, (tensorPowerSpectralWeight sigma n y : ℝ) *
          ((star (UsigmaN : CMatrix (TensorPower a n)) * P *
            (UsigmaN : CMatrix (TensorPower a n))) y y).re := by
          simpa [UsigmaN] using htrace
    _ = ∑ y : TensorPower a n, (tensorPowerSpectralWeight sigma n y : ℝ) *
          ∑ x : TensorPower a n,
            Complex.normSq
              ((star (UsigmaN : CMatrix (TensorPower a n)) * P *
                (UrhoN : CMatrix (TensorPower a n))) y x) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [projection_conjugate_diag_re_eq_row_normSq
            (P := P) hPherm hPidem UsigmaN UrhoN y]
    _ = ∑ y : TensorPower a n, (tensorPowerSpectralWeight sigma n y : ℝ) *
          ∑ x : TensorPower a n,
            Complex.normSq
              ((star (UrhoN : CMatrix (TensorPower a n)) * P *
                (UsigmaN : CMatrix (TensorPower a n))) x y) := by
          apply Finset.sum_congr rfl
          intro y _
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          rw [hermitian_projection_bridge_normSq_symm hPherm UrhoN UsigmaN x y]
    _ = ∑ y : TensorPower a n, (tensorPowerSpectralWeight sigma n y : ℝ) *
          ∑ x : TensorPower a n,
            Complex.normSq
              ((star (tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n :
                  CMatrix (TensorPower a n)) *
                  P *
                (tensorPowerUnitary sigma.pos.isHermitian.eigenvectorUnitary n :
                  CMatrix (TensorPower a n))) x y) := by
          rfl

/-- Finite projection comparison for the canonical product Nussbaum--Szkola
sequence, with Gour's exact `1 / 2` constant. -/
theorem half_nussbaumSzkolaProductModel_equalPriorError_le_projection_error
    (rho sigma : State a) (n : Nat) {P : CMatrix (TensorPower a n)}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    (1 / 2 : ℝ) * ((nussbaumSzkolaProductModel rho sigma n).equalPriorError : ℝ) ≤
      (1 / 2 : ℝ) *
        ((((rho.tensorPower n).matrix * (1 - P)).trace).re +
          (((sigma.tensorPower n).matrix * P).trace).re) := by
  classical
  let UrhoN : Matrix.unitaryGroup (TensorPower a n) ℂ :=
    tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n
  let UsigmaN : Matrix.unitaryGroup (TensorPower a n) ℂ :=
    tensorPowerUnitary sigma.pos.isHermitian.eigenvectorUnitary n
  let rejectAmp : TensorPower a n × TensorPower a n → ℂ := fun xy =>
    (star (UrhoN : CMatrix (TensorPower a n)) * (1 - P) *
      (UsigmaN : CMatrix (TensorPower a n))) xy.1 xy.2
  let acceptAmp : TensorPower a n × TensorPower a n → ℂ := fun xy =>
    (star (UrhoN : CMatrix (TensorPower a n)) * P *
      (UsigmaN : CMatrix (TensorPower a n))) xy.1 xy.2
  let rhsDouble : ℝ :=
    ∑ xy : TensorPower a n × TensorPower a n,
      (((1 / 2 : ℝ) * (tensorPowerSpectralWeight rho n xy.1 : ℝ)) *
          Complex.normSq (rejectAmp xy) +
        ((1 / 2 : ℝ) * (tensorPowerSpectralWeight sigma n xy.2 : ℝ)) *
          Complex.normSq (acceptAmp xy))
  have hentry_sum (xy : TensorPower a n × TensorPower a n) :
      rejectAmp xy + acceptAmp xy =
        ((star (UrhoN : CMatrix (TensorPower a n)) *
          (UsigmaN : CMatrix (TensorPower a n))) xy.1 xy.2) := by
    have hmat :
        star (UrhoN : CMatrix (TensorPower a n)) * (1 - P) *
            (UsigmaN : CMatrix (TensorPower a n)) +
          star (UrhoN : CMatrix (TensorPower a n)) * P *
            (UsigmaN : CMatrix (TensorPower a n)) =
          star (UrhoN : CMatrix (TensorPower a n)) *
            (UsigmaN : CMatrix (TensorPower a n)) := by
      noncomm_ring
    have hentry := congrFun (congrFun hmat xy.1) xy.2
    simpa [rejectAmp, acceptAmp] using hentry
  have hterm (xy : TensorPower a n × TensorPower a n) :
      (1 / 2 : ℝ) *
          min
            (((1 / 2 : ℝ) * (tensorPowerSpectralWeight rho n xy.1 : ℝ)) *
              (tensorPowerNussbaumSzkolaOverlap rho sigma n xy.1 xy.2 : ℝ))
            (((1 / 2 : ℝ) * (tensorPowerSpectralWeight sigma n xy.2 : ℝ)) *
              (tensorPowerNussbaumSzkolaOverlap rho sigma n xy.1 xy.2 : ℝ)) ≤
        ((1 / 2 : ℝ) * (tensorPowerSpectralWeight rho n xy.1 : ℝ)) *
            Complex.normSq (rejectAmp xy) +
          ((1 / 2 : ℝ) * (tensorPowerSpectralWeight sigma n xy.2 : ℝ)) *
            Complex.normSq (acceptAmp xy) := by
    have hnorm :
        (tensorPowerNussbaumSzkolaOverlap rho sigma n xy.1 xy.2 : ℝ) ≤
          2 * (Complex.normSq (rejectAmp xy) + Complex.normSq (acceptAmp xy)) := by
      have h := complex_normSq_add_le_two_sum (rejectAmp xy) (acceptAmp xy)
      rw [hentry_sum xy] at h
      simpa [UrhoN, UsigmaN, tensorPowerNussbaumSzkolaOverlap_eq_normSq]
        using h
    exact half_min_weight_normSq_add_le_weighted_normSq
      (by positivity) (by positivity)
      (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
      (by positivity) hnorm
  have hlhs_le_rhsDouble :
      (1 / 2 : ℝ) * ((nussbaumSzkolaProductModel rho sigma n).equalPriorError : ℝ) ≤
        rhsDouble := by
    let e := tensorPowerProdEquiv a a n
    calc
      (1 / 2 : ℝ) * ((nussbaumSzkolaProductModel rho sigma n).equalPriorError : ℝ) =
          ∑ z : TensorPower (a × a) n,
            (1 / 2 : ℝ) *
              min
                (((1 / 2 : ℝ) *
                  ((nussbaumSzkolaProductModel rho sigma n).p z : ℝ)))
                (((1 / 2 : ℝ) *
                  ((nussbaumSzkolaProductModel rho sigma n).q z : ℝ))) := by
            simp [ClassicalBinaryModel.equalPriorError, Finset.mul_sum]
      _ = ∑ xy : TensorPower a n × TensorPower a n,
            (1 / 2 : ℝ) *
              min
                (((1 / 2 : ℝ) * (tensorPowerSpectralWeight rho n xy.1 : ℝ)) *
                  (tensorPowerNussbaumSzkolaOverlap rho sigma n xy.1 xy.2 : ℝ))
                (((1 / 2 : ℝ) * (tensorPowerSpectralWeight sigma n xy.2 : ℝ)) *
                  (tensorPowerNussbaumSzkolaOverlap rho sigma n xy.1 xy.2 : ℝ)) := by
            refine Fintype.sum_equiv e _ _ ?_
            intro z
            have hp :=
              nussbaumSzkolaProductModel_p_eq rho sigma n (e z).1 (e z).2
            have hq :=
              nussbaumSzkolaProductModel_q_eq rho sigma n (e z).1 (e z).2
            have hz :
                (tensorPowerProdEquiv a a n).symm ((e z).1, (e z).2) = z := by
              exact e.left_inv z
            conv_lhs => rw [← hz]
            rw [hp, hq]
            apply congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
            apply congrArg₂ min <;> simp [NNReal.coe_mul, mul_assoc]
      _ ≤ rhsDouble := by
            unfold rhsDouble
            exact Finset.sum_le_sum fun xy _ => hterm xy
  have htrace_rho :=
    tensorPower_trace_one_sub_projection_re_eq_nussbaumSzkolaProduct_source_sum
      rho sigma n hPherm hPidem
  have htrace_sigma :=
    tensorPower_trace_projection_re_eq_nussbaumSzkolaProduct_source_sum
      rho sigma n hPherm hPidem
  have hrhsDouble :
      rhsDouble =
        (1 / 2 : ℝ) *
          ((((rho.tensorPower n).matrix * (1 - P)).trace).re +
            (((sigma.tensorPower n).matrix * P).trace).re) := by
    let rhoPart : ℝ := ∑ xy : TensorPower a n × TensorPower a n,
      ((1 / 2 : ℝ) * (tensorPowerSpectralWeight rho n xy.1 : ℝ)) *
        Complex.normSq (rejectAmp xy)
    let sigmaPart : ℝ := ∑ xy : TensorPower a n × TensorPower a n,
      ((1 / 2 : ℝ) * (tensorPowerSpectralWeight sigma n xy.2 : ℝ)) *
        Complex.normSq (acceptAmp xy)
    have hrhs_split : rhsDouble = rhoPart + sigmaPart := by
      unfold rhsDouble rhoPart sigmaPart
      rw [Finset.sum_add_distrib]
    have hrhoPart :
        rhoPart = (1 / 2 : ℝ) *
          (((rho.tensorPower n).matrix * (1 - P)).trace).re := by
      calc
        rhoPart =
            (1 / 2 : ℝ) *
              (∑ x : TensorPower a n, (tensorPowerSpectralWeight rho n x : ℝ) *
                ∑ y : TensorPower a n, Complex.normSq (rejectAmp (x, y))) := by
              unfold rhoPart
              rw [Fintype.sum_prod_type]
              simp [Finset.mul_sum, mul_assoc]
        _ = (1 / 2 : ℝ) *
              (((rho.tensorPower n).matrix * (1 - P)).trace).re := by
              rw [htrace_rho]
    have hsigmaPart :
        sigmaPart = (1 / 2 : ℝ) *
          (((sigma.tensorPower n).matrix * P).trace).re := by
      calc
        sigmaPart =
            (1 / 2 : ℝ) *
              (∑ y : TensorPower a n, (tensorPowerSpectralWeight sigma n y : ℝ) *
                ∑ x : TensorPower a n, Complex.normSq (acceptAmp (x, y))) := by
              unfold sigmaPart
              rw [Fintype.sum_prod_type, Finset.sum_comm]
              simp [Finset.mul_sum, mul_assoc]
        _ = (1 / 2 : ℝ) *
              (((sigma.tensorPower n).matrix * P).trace).re := by
              rw [htrace_sigma]
    rw [hrhs_split, hrhoPart, hsigmaPart]
    ring
  exact hlhs_le_rhsDouble.trans_eq hrhsDouble

private theorem half_nussbaumSzkolaModel_equalPriorError_le_projection_error
    (rho sigma : State a) {P : CMatrix a}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    (1 / 2 : ℝ) * ((nussbaumSzkolaModel rho sigma).equalPriorError : ℝ) ≤
      (1 / 2 : ℝ) *
        (((rho.matrix * (1 - P)).trace).re + ((sigma.matrix * P).trace).re) := by
  classical
  let Urho : Matrix.unitaryGroup a ℂ := rho.pos.isHermitian.eigenvectorUnitary
  let Usigma : Matrix.unitaryGroup a ℂ := sigma.pos.isHermitian.eigenvectorUnitary
  let rejectAmp : a × a → ℂ := fun xy =>
    (star (Urho : CMatrix a) * (1 - P) * (Usigma : CMatrix a)) xy.1 xy.2
  let acceptAmp : a × a → ℂ := fun xy =>
    (star (Urho : CMatrix a) * P * (Usigma : CMatrix a)) xy.1 xy.2
  let rhsDouble : ℝ :=
    ∑ xy : a × a,
      (((1 / 2 : ℝ) * (stateSpectralWeight rho xy.1 : ℝ)) *
          Complex.normSq (rejectAmp xy) +
        ((1 / 2 : ℝ) * (stateSpectralWeight sigma xy.2 : ℝ)) *
          Complex.normSq (acceptAmp xy))
  have hentry_sum (xy : a × a) :
      rejectAmp xy + acceptAmp xy =
        ((nussbaumSzkolaTransitionUnitary rho sigma : CMatrix a) xy.1 xy.2) := by
    have hmat :
        star (Urho : CMatrix a) * (1 - P) * (Usigma : CMatrix a) +
            star (Urho : CMatrix a) * P * (Usigma : CMatrix a) =
          star (Urho : CMatrix a) * (Usigma : CMatrix a) := by
      noncomm_ring
    have hentry := congrFun (congrFun hmat xy.1) xy.2
    simpa [rejectAmp, acceptAmp, Urho, Usigma, nussbaumSzkolaTransitionUnitary,
      Matrix.star_eq_conjTranspose] using hentry
  have hterm (xy : a × a) :
      (1 / 2 : ℝ) *
          min
            (((1 / 2 : ℝ) * (stateSpectralWeight rho xy.1 : ℝ)) *
              (nussbaumSzkolaOverlap rho sigma xy.1 xy.2 : ℝ))
            (((1 / 2 : ℝ) * (stateSpectralWeight sigma xy.2 : ℝ)) *
              (nussbaumSzkolaOverlap rho sigma xy.1 xy.2 : ℝ)) ≤
        ((1 / 2 : ℝ) * (stateSpectralWeight rho xy.1 : ℝ)) *
            Complex.normSq (rejectAmp xy) +
          ((1 / 2 : ℝ) * (stateSpectralWeight sigma xy.2 : ℝ)) *
            Complex.normSq (acceptAmp xy) := by
    have hnorm :
        (nussbaumSzkolaOverlap rho sigma xy.1 xy.2 : ℝ) ≤
          2 * (Complex.normSq (rejectAmp xy) + Complex.normSq (acceptAmp xy)) := by
      have h := complex_normSq_add_le_two_sum (rejectAmp xy) (acceptAmp xy)
      rw [hentry_sum xy] at h
      simpa [nussbaumSzkolaOverlap] using h
    exact half_min_weight_normSq_add_le_weighted_normSq
      (by positivity) (by positivity)
      (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
      (by positivity) hnorm
  have hlhs_le_rhsDouble :
      (1 / 2 : ℝ) * ((nussbaumSzkolaModel rho sigma).equalPriorError : ℝ) ≤
        rhsDouble := by
    calc
      (1 / 2 : ℝ) * ((nussbaumSzkolaModel rho sigma).equalPriorError : ℝ) =
          ∑ xy : a × a,
            (1 / 2 : ℝ) *
              min
                (((1 / 2 : ℝ) * (stateSpectralWeight rho xy.1 : ℝ)) *
                  (nussbaumSzkolaOverlap rho sigma xy.1 xy.2 : ℝ))
                (((1 / 2 : ℝ) * (stateSpectralWeight sigma xy.2 : ℝ)) *
                  (nussbaumSzkolaOverlap rho sigma xy.1 xy.2 : ℝ)) := by
            simp [ClassicalBinaryModel.equalPriorError, nussbaumSzkolaModel,
              Finset.mul_sum, mul_left_comm, mul_comm]
      _ ≤ rhsDouble := by
            unfold rhsDouble
            exact Finset.sum_le_sum fun xy _ => hterm xy
  have htrace_rho :=
    state_trace_one_sub_projection_re_eq_nussbaumSzkola_source_sum
      rho sigma hPherm hPidem
  have htrace_sigma :=
    state_trace_projection_re_eq_nussbaumSzkola_source_sum
      rho sigma hPherm hPidem
  have hrhsDouble :
      rhsDouble =
        (1 / 2 : ℝ) *
          (((rho.matrix * (1 - P)).trace).re + ((sigma.matrix * P).trace).re) := by
    let rhoPart : ℝ := ∑ xy : a × a,
      ((1 / 2 : ℝ) * (stateSpectralWeight rho xy.1 : ℝ)) *
        Complex.normSq (rejectAmp xy)
    let sigmaPart : ℝ := ∑ xy : a × a,
      ((1 / 2 : ℝ) * (stateSpectralWeight sigma xy.2 : ℝ)) *
        Complex.normSq (acceptAmp xy)
    have hrhs_split : rhsDouble = rhoPart + sigmaPart := by
      unfold rhsDouble rhoPart sigmaPart
      rw [Finset.sum_add_distrib]
    have hrhoPart :
        rhoPart = (1 / 2 : ℝ) * ((rho.matrix * (1 - P)).trace).re := by
      calc
        rhoPart =
            (1 / 2 : ℝ) *
              (∑ x : a, (stateSpectralWeight rho x : ℝ) *
                ∑ y : a, Complex.normSq (rejectAmp (x, y))) := by
              unfold rhoPart
              rw [Fintype.sum_prod_type]
              simp [Finset.mul_sum, mul_assoc]
        _ = (1 / 2 : ℝ) * ((rho.matrix * (1 - P)).trace).re := by
              rw [htrace_rho]
    have hsigmaPart :
        sigmaPart = (1 / 2 : ℝ) * ((sigma.matrix * P).trace).re := by
      calc
        sigmaPart =
            (1 / 2 : ℝ) *
              (∑ y : a, (stateSpectralWeight sigma y : ℝ) *
                ∑ x : a, Complex.normSq (acceptAmp (x, y))) := by
              unfold sigmaPart
              rw [Fintype.sum_prod_type, Finset.sum_comm]
              simp [Finset.mul_sum, mul_assoc]
        _ = (1 / 2 : ℝ) * ((sigma.matrix * P).trace).re := by
              rw [htrace_sigma]
    rw [hrhs_split, hrhoPart, hsigmaPart]
    ring
  exact hlhs_le_rhsDouble.trans_eq hrhsDouble

private theorem half_trace_accept_effect_error_eq_equalPriorError
    (T : BinaryHypothesisTest a) (rho sigma : State a) :
    (1 / 2 : ℝ) *
        (((rho.matrix * (1 - T.acceptRhoEffect)).trace).re +
          ((sigma.matrix * T.acceptRhoEffect).trace).re) =
      (T.equalPriorError rho sigma : ℝ) := by
  have hreject_trace :
      ((rho.matrix * (1 - T.acceptRhoEffect)).trace).re =
        (T.rejectProb rho : ℝ) := by
    rw [← T.rejectRhoEffect_eq_one_sub_acceptRhoEffect]
    exact (T.rejectProb_eq_trace_re rho).symm
  have haccept_trace :
      ((sigma.matrix * T.acceptRhoEffect).trace).re =
        (T.acceptProb sigma : ℝ) :=
    (T.acceptProb_eq_trace_re sigma).symm
  rw [hreject_trace, haccept_trace]
  unfold BinaryHypothesisTest.equalPriorError BinaryHypothesisTest.typeIError
    BinaryHypothesisTest.typeIIError
  simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_ofNat]
  ring

/-- The Nussbaum--Szkola classical error sequence for tensor powers.

At copy number `n`, this uses the spectral Nussbaum--Szkola model associated to
`rho^⊗n` and `sigma^⊗n`. -/
def nussbaumSzkolaClassicalError (rho sigma : State a) (n : Nat) : ℝ≥0∞ :=
  (nussbaumSzkolaModel (rho.tensorPower n) (sigma.tensorPower n)).equalPriorErrorENNReal

/-- The classical error sequence is the tensor-power Nussbaum--Szkola sequence. -/
def HasNussbaumSzkolaTensorPowerCompatibility
    (rho sigma : State a) (classicalError : Nat → ℝ≥0∞) : Prop :=
  classicalError = nussbaumSzkolaClassicalError rho sigma

/-- The canonical Nussbaum--Szkola classical error sequence satisfies the
tensor-power compatibility convention by definition. -/
theorem nussbaumSzkolaClassicalError_tensorPowerCompatible (rho sigma : State a) :
    HasNussbaumSzkolaTensorPowerCompatibility
      rho sigma (nussbaumSzkolaClassicalError rho sigma) :=
  rfl

/-- Source-shaped finite Nussbaum--Szkola comparison obligation.

The first field pins the sequence to the tensor-power Nussbaum--Szkola
construction.  The second field is the finite quantum-to-classical comparison
with the source's `1 / 2` constant. -/
def HasNussbaumSzkolaFiniteComparison
    (rho sigma : State a) (classicalError : Nat → ℝ≥0∞) : Prop :=
  HasNussbaumSzkolaTensorPowerCompatibility rho sigma classicalError ∧
    ∀ n : Nat,
      quantumChernoffConverseComparisonConstant * classicalError n ≤
        optimalEqualPriorTensorPowerError rho sigma n

/-- Source-shaped finite-copy quantum-to-classical comparison for the QCB converse.

The predicate states the reusable finite-`n` estimate supplied by the
Nussbaum--Szkola construction: the quantum optimal equal-prior tensor-power
error dominates one half of a corresponding classical error sequence
[Gour2024Resources, BookQRT.tex:15911-15949]. -/
def HasQuantumToClassicalChernoffComparison
    (rho sigma : State a) (classicalError : Nat → ℝ≥0∞) : Prop :=
  ∀ n : Nat,
    quantumChernoffConverseComparisonConstant * classicalError n ≤
      optimalEqualPriorTensorPowerError rho sigma n

/-- The source-shaped Nussbaum--Szkola finite comparison instantiates the
generic quantum-to-classical Chernoff comparison predicate. -/
theorem hasQuantumToClassicalChernoffComparison_of_nussbaumSzkola
    (rho sigma : State a)
    {classicalError : Nat → ℝ≥0∞}
    (hfinite : HasNussbaumSzkolaFiniteComparison rho sigma classicalError) :
    HasQuantumToClassicalChernoffComparison rho sigma classicalError :=
  hfinite.2

/-- Product Nussbaum--Szkola finite comparison instantiates the generic
quantum-to-classical Chernoff comparison predicate. -/
theorem hasQuantumToClassicalChernoffComparison_of_nussbaumSzkolaProduct
    (rho sigma : State a)
    {classicalError : Nat → ℝ≥0∞}
    (hfinite : HasNussbaumSzkolaProductFiniteComparison rho sigma classicalError) :
    HasQuantumToClassicalChernoffComparison rho sigma classicalError :=
  hfinite.2

/-- The canonical Nussbaum--Szkola sequence satisfies the finite quantum-to-classical
comparison with Gour's `1 / 2` constant. -/
theorem hasNussbaumSzkolaFiniteComparison
    (rho sigma : State a) :
    HasNussbaumSzkolaFiniteComparison
      rho sigma (nussbaumSzkolaClassicalError rho sigma) := by
  refine ⟨nussbaumSzkolaClassicalError_tensorPowerCompatible rho sigma, ?_⟩
  intro n
  classical
  let rhoN : State (TensorPower a n) := rho.tensorPower n
  let sigmaN : State (TensorPower a n) := sigma.tensorPower n
  let T0 : BinaryHypothesisTest (TensorPower a n) := rhoN.helstromTest sigmaN
  have hPherm : T0.acceptRhoEffect.IsHermitian :=
    T0.acceptRhoEffect_pos.isHermitian
  have hPidem : T0.acceptRhoEffect * T0.acceptRhoEffect = T0.acceptRhoEffect := by
    let H : CMatrix (TensorPower a n) := rhoN.matrix - sigmaN.matrix
    let hH : H.IsHermitian := rhoN.pos.isHermitian.sub sigmaN.pos.isHermitian
    simpa [T0, State.helstromTest, BinaryHypothesisTest.acceptRhoEffect, H, hH]
      using positiveSpectralProjector_idempotent H hH
  have hsource :
      (1 / 2 : ℝ) * ((nussbaumSzkolaModel rhoN sigmaN).equalPriorError : ℝ) ≤
        (T0.equalPriorError rhoN sigmaN : ℝ) := by
    have hprojection :=
      half_nussbaumSzkolaModel_equalPriorError_le_projection_error
        rhoN sigmaN hPherm hPidem
    exact hprojection.trans_eq
      (half_trace_accept_effect_error_eq_equalPriorError T0 rhoN sigmaN)
  have hsource_formula :
      (1 / 2 : ℝ) * ((nussbaumSzkolaModel rhoN sigmaN).equalPriorError : ℝ) ≤
        (1 / 2 : ℝ) * (1 - rhoN.normalizedTraceDistance sigmaN) := by
    exact hsource.trans_eq (State.helstromTest_equalPriorError_eq rhoN sigmaN)
  rw [optimalEqualPriorTensorPowerError]
  refine le_iInf ?_
  intro T
  have hTreal :
      (1 / 2 : ℝ) * ((nussbaumSzkolaModel rhoN sigmaN).equalPriorError : ℝ) ≤
        (T.equalPriorTensorPowerError rho sigma : ℝ) := by
    have hopt := (State.helstrom_equalPriorError_optimal rhoN sigmaN).2 T
    exact hsource_formula.trans (by
      simpa [BinaryHypothesisTest.equalPriorTensorPowerError, rhoN, sigmaN] using hopt)
  have hTnn :
      ((1 / 2 : ℝ≥0) * (nussbaumSzkolaModel rhoN sigmaN).equalPriorError) ≤
        T.equalPriorTensorPowerError rho sigma := by
    apply NNReal.coe_le_coe.mp
    simpa using hTreal
  have hTenn :
      (((1 / 2 : ℝ≥0) * (nussbaumSzkolaModel rhoN sigmaN).equalPriorError : ℝ≥0) :
          ℝ≥0∞) ≤
        (T.equalPriorTensorPowerError rho sigma : ℝ≥0∞) :=
    ENNReal.coe_le_coe.mpr hTnn
  unfold quantumChernoffConverseComparisonConstant nussbaumSzkolaClassicalError
  simpa [ClassicalBinaryModel.equalPriorErrorENNReal, rhoN, sigmaN] using hTenn

/-- The canonical product Nussbaum--Szkola sequence satisfies the finite
quantum-to-classical comparison with Gour's `1 / 2` constant. -/
theorem hasNussbaumSzkolaProductFiniteComparison
    (rho sigma : State a) :
    HasNussbaumSzkolaProductFiniteComparison
      rho sigma (nussbaumSzkolaProductClassicalError rho sigma) := by
  refine ⟨rfl, ?_⟩
  intro n
  classical
  let rhoN : State (TensorPower a n) := rho.tensorPower n
  let sigmaN : State (TensorPower a n) := sigma.tensorPower n
  let T0 : BinaryHypothesisTest (TensorPower a n) := rhoN.helstromTest sigmaN
  have hPherm : T0.acceptRhoEffect.IsHermitian :=
    T0.acceptRhoEffect_pos.isHermitian
  have hPidem : T0.acceptRhoEffect * T0.acceptRhoEffect = T0.acceptRhoEffect := by
    let H : CMatrix (TensorPower a n) := rhoN.matrix - sigmaN.matrix
    let hH : H.IsHermitian := rhoN.pos.isHermitian.sub sigmaN.pos.isHermitian
    simpa [T0, State.helstromTest, BinaryHypothesisTest.acceptRhoEffect, H, hH]
      using positiveSpectralProjector_idempotent H hH
  have hsource :
      (1 / 2 : ℝ) * ((nussbaumSzkolaProductModel rho sigma n).equalPriorError : ℝ) ≤
        (T0.equalPriorError rhoN sigmaN : ℝ) := by
    have hprojection :=
      half_nussbaumSzkolaProductModel_equalPriorError_le_projection_error
        rho sigma n hPherm hPidem
    exact hprojection.trans_eq
      (half_trace_accept_effect_error_eq_equalPriorError T0 rhoN sigmaN)
  have hsource_formula :
      (1 / 2 : ℝ) * ((nussbaumSzkolaProductModel rho sigma n).equalPriorError : ℝ) ≤
        (1 / 2 : ℝ) * (1 - rhoN.normalizedTraceDistance sigmaN) := by
    exact hsource.trans_eq (State.helstromTest_equalPriorError_eq rhoN sigmaN)
  rw [optimalEqualPriorTensorPowerError]
  refine le_iInf ?_
  intro T
  have hTreal :
      (1 / 2 : ℝ) * ((nussbaumSzkolaProductModel rho sigma n).equalPriorError : ℝ) ≤
        (T.equalPriorTensorPowerError rho sigma : ℝ) := by
    have hopt := (State.helstrom_equalPriorError_optimal rhoN sigmaN).2 T
    exact hsource_formula.trans (by
      simpa [BinaryHypothesisTest.equalPriorTensorPowerError, rhoN, sigmaN] using hopt)
  have hTnn :
      ((1 / 2 : ℝ≥0) * (nussbaumSzkolaProductModel rho sigma n).equalPriorError) ≤
        T.equalPriorTensorPowerError rho sigma := by
    apply NNReal.coe_le_coe.mp
    simpa using hTreal
  have hTenn :
      (((1 / 2 : ℝ≥0) * (nussbaumSzkolaProductModel rho sigma n).equalPriorError : ℝ≥0) :
          ℝ≥0∞) ≤
        (T.equalPriorTensorPowerError rho sigma : ℝ≥0∞) :=
    ENNReal.coe_le_coe.mpr hTnn
  unfold quantumChernoffConverseComparisonConstant nussbaumSzkolaProductClassicalError
  simpa [ClassicalBinaryModel.equalPriorErrorENNReal] using hTenn

/-- The canonical Nussbaum--Szkola sequence satisfies the generic
quantum-to-classical comparison predicate. -/
theorem hasQuantumToClassicalChernoffComparison_nussbaumSzkolaClassicalError
    (rho sigma : State a) :
    HasQuantumToClassicalChernoffComparison
      rho sigma (nussbaumSzkolaClassicalError rho sigma) :=
  hasQuantumToClassicalChernoffComparison_of_nussbaumSzkola
    rho sigma (hasNussbaumSzkolaFiniteComparison rho sigma)

/-- The canonical product Nussbaum--Szkola sequence satisfies the generic
quantum-to-classical comparison predicate. -/
theorem hasQuantumToClassicalChernoffComparison_nussbaumSzkolaProductClassicalError
    (rho sigma : State a) :
    HasQuantumToClassicalChernoffComparison
      rho sigma (nussbaumSzkolaProductClassicalError rho sigma) :=
  hasQuantumToClassicalChernoffComparison_of_nussbaumSzkolaProduct
    rho sigma (hasNussbaumSzkolaProductFiniteComparison rho sigma)

/-- Source-shaped classical method-of-types converse estimate.

The source proof lower-bounds classical errors using `(n+1)^(-m)` type-class
prefactors and then obtains the limsup orientation for the normalized negative
log error exponent [Gour2024Resources, BookQRT.tex:15414-15469]. -/
def HasClassicalMethodOfTypesChernoffConverse
    (rho sigma : State a) (classicalError : Nat → ℝ≥0∞) : Prop :=
  Filter.limsup (fun n : Nat => normalizedNegLog n (classicalError (n + 1)))
    atTop ≤ rho.chernoffDistance sigma

/-- Finite-copy exponent form of the classical method-of-types Chernoff converse.

This predicate records the source-backed finite-`n` conclusion after applying
the type-class lower bounds with the polynomial prefactor `(n+1)^(-m)`: the
normalized negative log of the classical error is eventually bounded by the
Chernoff distance plus the finite-alphabet polynomial penalty. -/
def HasClassicalMethodOfTypesFiniteExponentBound
    (rho sigma : State a) (classicalError : Nat → ℝ≥0∞) : Prop :=
  ∀ᶠ n in atTop,
    normalizedNegLog n (classicalError (n + 1)) ≤
      rho.chernoffDistance sigma + methodOfTypesPolynomialPenalty (a := a) n

/-- The finite method-of-types exponent bound implies the limsup converse
orientation required by `HasClassicalMethodOfTypesChernoffConverse`. -/
theorem classicalMethodOfTypes_limsup_le_of_finiteExponentBound
    (rho sigma : State a) (classicalError : Nat → ℝ≥0∞)
    (hfinite :
      ∀ᶠ n in atTop,
        normalizedNegLog n (classicalError (n + 1)) ≤
          rho.chernoffDistance sigma + methodOfTypesPolynomialPenalty (a := a) n) :
    Filter.limsup (fun n : Nat => normalizedNegLog n (classicalError (n + 1)))
        atTop ≤ rho.chernoffDistance sigma := by
  have hpenalty :
      Tendsto (fun n : Nat => methodOfTypesPolynomialPenalty (a := a) n)
        atTop (𝓝 (0 : EReal)) :=
    methodOfTypesPolynomialPenalty_tendsto_zero (a := a)
  have hsum :
      Tendsto
        (fun n : Nat => rho.chernoffDistance sigma + methodOfTypesPolynomialPenalty (a := a) n)
        atTop (𝓝 (rho.chernoffDistance sigma)) := by
    have hpair :
        Tendsto
          (fun n : Nat => (rho.chernoffDistance sigma, methodOfTypesPolynomialPenalty (a := a) n))
          atTop (𝓝 (rho.chernoffDistance sigma, (0 : EReal))) :=
      tendsto_const_nhds.prodMk_nhds hpenalty
    have hadd :
        ContinuousAt (fun p : EReal × EReal => p.1 + p.2)
          (rho.chernoffDistance sigma, (0 : EReal)) :=
      EReal.continuousAt_add (p := (rho.chernoffDistance sigma, (0 : EReal)))
        (Or.inr (by simp)) (Or.inr (by simp))
    simpa using hadd.tendsto.comp hpair
  have hlimsup_le :=
    Filter.limsup_le_limsup hfinite (β := EReal)
      (u := fun n : Nat => normalizedNegLog n (classicalError (n + 1)))
      (v := fun n : Nat => rho.chernoffDistance sigma + methodOfTypesPolynomialPenalty (a := a) n)
  exact hlimsup_le.trans (le_of_eq hsum.limsup_eq)

/-- Source-shaped classical method-of-types route packaged as the existing
converse predicate. -/
theorem hasClassicalMethodOfTypesChernoffConverse_of_finiteExponentBound
    (rho sigma : State a) (classicalError : Nat → ℝ≥0∞)
    (hfinite : HasClassicalMethodOfTypesFiniteExponentBound rho sigma classicalError) :
    HasClassicalMethodOfTypesChernoffConverse rho sigma classicalError :=
  classicalMethodOfTypes_limsup_le_of_finiteExponentBound rho sigma classicalError hfinite

/-- The generic finite-alphabet method-of-types converse instantiated for the
canonical product Nussbaum--Szkola classical error sequence. -/
theorem hasClassicalMethodOfTypesChernoffConverse_nussbaumSzkolaProductClassicalError
    (rho sigma : State a) :
    HasClassicalMethodOfTypesChernoffConverse
      rho sigma (nussbaumSzkolaProductClassicalError rho sigma) := by
  classical
  have h :=
    ClassicalBinaryModel.methodOfTypesChernoffConverse
      (M := nussbaumSzkolaModel rho sigma)
  simpa [HasClassicalMethodOfTypesChernoffConverse,
    nussbaumSzkolaProductClassicalError, nussbaumSzkolaProductModel,
    nussbaumSzkolaModel_chernoffDistance_eq] using h

/-- The finite quantum-to-classical comparison turns the product
Nussbaum--Szkola classical exponent into a pointwise upper bound on the quantum
optimal-error exponent, with the explicit `log 2 / (n+1)` penalty from the
source's `1 / 2` comparison constant. -/
theorem optimalErrorExponent_le_nussbaumSzkolaProductClassicalExponent_add_penalty
    (rho sigma : State a) (n : Nat) :
    optimalEqualPriorTensorPowerErrorExponent rho sigma n ≤
      normalizedNegLog n
        (nussbaumSzkolaProductClassicalError rho sigma (n + 1)) +
        equalPriorAverageLogPenalty n := by
  have hcomparison :
      quantumChernoffConverseComparisonConstant *
          nussbaumSzkolaProductClassicalError rho sigma (n + 1) ≤
        optimalEqualPriorTensorPowerError rho sigma (n + 1) :=
    hasQuantumToClassicalChernoffComparison_nussbaumSzkolaProductClassicalError
      rho sigma (n + 1)
  have hquantum :
      optimalEqualPriorTensorPowerErrorExponent rho sigma n ≤
        normalizedNegLog n
          (quantumChernoffConverseComparisonConstant *
            nussbaumSzkolaProductClassicalError rho sigma (n + 1)) := by
    simpa [optimalEqualPriorTensorPowerErrorExponent] using
      normalizedNegLog_antitone n hcomparison
  have hpenalty :=
    normalizedNegLog_half_mul_coe_le_add_equalPriorAverageLogPenalty
      n ((nussbaumSzkolaProductModel rho sigma (n + 1)).equalPriorError)
  exact hquantum.trans (by
    simpa [quantumChernoffConverseComparisonConstant,
      nussbaumSzkolaProductClassicalError,
      ClassicalBinaryModel.equalPriorErrorENNReal] using hpenalty)

/-- Limsup-side quantum Chernoff converse obtained from the product
Nussbaum--Szkola comparison and the generic classical method-of-types
converse. -/
theorem limsup_errorExponent_le_chernoffDistance_nussbaumSzkolaProduct
    (rho sigma : State a) :
    Filter.limsup
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop ≤ rho.chernoffDistance sigma := by
  let classicalSeq : Nat → EReal := fun n =>
    normalizedNegLog n (nussbaumSzkolaProductClassicalError rho sigma (n + 1))
  let priorPenalty : Nat → EReal := fun n => equalPriorAverageLogPenalty n
  have hpoint :
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n) ≤ᶠ[atTop]
        fun n : Nat => classicalSeq n + priorPenalty n := by
    exact Filter.Eventually.of_forall fun n => by
      simpa [classicalSeq, priorPenalty] using
        optimalErrorExponent_le_nussbaumSzkolaProductClassicalExponent_add_penalty
          rho sigma n
  have hprior_limsup :
      Filter.limsup priorPenalty atTop = (0 : EReal) :=
    equalPriorAverageLogPenalty_tendsto_zero.limsup_eq
  have hsum :
      Filter.limsup (fun n : Nat => classicalSeq n + priorPenalty n) atTop ≤
        Filter.limsup classicalSeq atTop + Filter.limsup priorPenalty atTop := by
    simpa only [Pi.add_apply] using
      EReal.limsup_add_le
        (u := classicalSeq) (v := priorPenalty) (f := atTop)
        (Or.inr (by rw [hprior_limsup]; simp))
        (Or.inr (by rw [hprior_limsup]; simp))
  have hclassical :
      Filter.limsup classicalSeq atTop ≤ rho.chernoffDistance sigma := by
    simpa [classicalSeq] using
      hasClassicalMethodOfTypesChernoffConverse_nussbaumSzkolaProductClassicalError
        rho sigma
  have hbridge :=
    Filter.limsup_le_limsup hpoint (β := EReal)
      (u := fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      (v := fun n : Nat => classicalSeq n + priorPenalty n)
  calc
    Filter.limsup
        (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
        atTop
        ≤ Filter.limsup (fun n : Nat => classicalSeq n + priorPenalty n) atTop :=
          hbridge
    _ ≤ Filter.limsup classicalSeq atTop + Filter.limsup priorPenalty atTop := hsum
    _ = Filter.limsup classicalSeq atTop := by
          rw [hprior_limsup]
          simp
    _ ≤ rho.chernoffDistance sigma := hclassical

/-- Source-backed QCB lower/converse route required before the final squeeze.

This is deliberately a route predicate, not the final unconditional QCB theorem:
the Nussbaum--Szkola comparison and classical method-of-types machinery are
explicit upstream obligations.  The last field records the required limsup
shape `limsup_errorExponent_le_chernoffDistance`, including arbitrary-state
and zero-overlap boundary cases, before the final squeeze theorem consumes it
[Gour2024Resources, BookQRT.tex:15373-15949]. -/
def QuantumChernoffConverseRoute (rho sigma : State a) : Prop :=
  ∃ classicalError : Nat → ℝ≥0∞,
    HasQuantumToClassicalChernoffComparison rho sigma classicalError ∧
    HasClassicalMethodOfTypesChernoffConverse rho sigma classicalError ∧
    Filter.limsup
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop ≤ rho.chernoffDistance sigma

/-- Unconditional product Nussbaum--Szkola converse route for the QCB squeeze. -/
theorem quantumChernoffConverseRoute (rho sigma : State a) :
    QuantumChernoffConverseRoute rho sigma := by
  refine ⟨nussbaumSzkolaProductClassicalError rho sigma,
    hasQuantumToClassicalChernoffComparison_nussbaumSzkolaProductClassicalError
      rho sigma,
    hasClassicalMethodOfTypesChernoffConverse_nussbaumSzkolaProductClassicalError
      rho sigma,
    limsup_errorExponent_le_chernoffDistance_nussbaumSzkolaProduct
      rho sigma⟩

/-- Limsup-side QCB bound extracted from a source-backed converse route.

This is the reusable lower/converse route API; it does not claim the final
asymptotic quantum Chernoff bound statement. -/
theorem limsup_errorExponent_le_chernoffDistance_of_converseRoute
    (rho sigma : State a)
    (h : QuantumChernoffConverseRoute rho sigma) :
    Filter.limsup
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop ≤ rho.chernoffDistance sigma := by
  rcases h with ⟨_classicalError, _hComparison, _hClassical, hlimsup⟩
  exact hlimsup

/-- Upper-side assembly of the QCB squeeze from pointwise Chernoff exponent
lower bounds.

If every Petz/Chernoff exponent indexed by `0 ≤ s ≤ 1` is eventually below the
optimal tensor-power error exponent, then the Chernoff distance, defined as the
supremum over those exponents, is below the `liminf` of the optimal exponent
sequence.  This is the reusable bridge from the finite-copy direct bound and
exponent calculus to the asymptotic squeeze
[Gour2024Resources, BookQRT.tex:15887-15909]. -/
theorem chernoffDistance_le_liminf_errorExponent_of_eventually_petzChernoffExponent_le
    (rho sigma : State a)
    (hupper :
      ∀ s : Set.Icc (0 : ℝ) 1,
        ∀ᶠ n in atTop,
          rho.petzChernoffExponent sigma s.1 ≤
            optimalEqualPriorTensorPowerErrorExponent rho sigma n) :
    rho.chernoffDistance sigma ≤
      Filter.liminf
        (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
        atTop := by
  rw [State.chernoffDistance]
  refine iSup_le ?_
  intro s
  exact le_liminf_of_le (by isBoundedDefault) (hupper s)

/-- Liminf/limsup squeeze bridge for the optimal-error exponent.

This theorem deliberately consumes the two squeeze sides as hypotheses, instead
of proving the asymptotic QCB statement by name.  A downstream statement can
instantiate this bridge after supplying the direct `liminf` side and the
converse `limsup` side. -/
theorem errorExponent_tendsto_chernoffDistance_of_liminf_limsup
    (rho sigma : State a)
    (hliminf :
      rho.chernoffDistance sigma ≤
        Filter.liminf
          (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
          atTop)
    (hlimsup :
      Filter.limsup
          (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
          atTop ≤ rho.chernoffDistance sigma) :
    Tendsto
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop (𝓝 (rho.chernoffDistance sigma)) := by
  exact tendsto_of_le_liminf_of_limsup_le hliminf hlimsup

/-- QCB squeeze bridge using the registered converse route.

The direct side is stated as the eventual pointwise Petz/Chernoff exponent
bound produced by the finite-copy upper-bound and exponent-calculus route; the
converse side is supplied by `QuantumChernoffConverseRoute`.  This is a bridge
for downstream use, not the public asymptotic QCB theorem entrypoint
[Gour2024Resources, BookQRT.tex:15373-15949]. -/
theorem errorExponent_tendsto_chernoffDistance_of_eventually_petzChernoffExponent_le_of_converseRoute
    (rho sigma : State a)
    (hupper :
      ∀ s : Set.Icc (0 : ℝ) 1,
        ∀ᶠ n in atTop,
          rho.petzChernoffExponent sigma s.1 ≤
            optimalEqualPriorTensorPowerErrorExponent rho sigma n)
    (hroute : QuantumChernoffConverseRoute rho sigma) :
    Tendsto
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop (𝓝 (rho.chernoffDistance sigma)) :=
  errorExponent_tendsto_chernoffDistance_of_liminf_limsup rho sigma
    (chernoffDistance_le_liminf_errorExponent_of_eventually_petzChernoffExponent_le
      rho sigma hupper)
    (limsup_errorExponent_le_chernoffDistance_of_converseRoute rho sigma hroute)

/-- Unconditional limsup-side QCB converse bound. -/
theorem limsup_errorExponent_le_chernoffDistance
    (rho sigma : State a) :
    Filter.limsup
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop ≤ rho.chernoffDistance sigma :=
  limsup_errorExponent_le_chernoffDistance_of_converseRoute
    rho sigma (quantumChernoffConverseRoute rho sigma)

/-- Unconditional direct-side lower bound for the liminf of optimal-error
exponents. -/
theorem chernoffDistance_le_liminf_errorExponent
    (rho sigma : State a) :
    rho.chernoffDistance sigma ≤
      Filter.liminf
        (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
        atTop :=
  chernoffDistance_le_liminf_errorExponent_of_eventually_petzChernoffExponent_le
    rho sigma
    (eventually_petzChernoffExponent_le_optimalEqualPriorTensorPowerErrorExponent
      rho sigma)

/-- Unconditional convergence of the optimal tensor-power error exponent to
the quantum Chernoff distance.  This is the squeeze API consumed by the
separate public QCB theorem. -/
theorem errorExponent_tendsto_chernoffDistance
    (rho sigma : State a) :
    Tendsto
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop (𝓝 (rho.chernoffDistance sigma)) :=
  errorExponent_tendsto_chernoffDistance_of_liminf_limsup rho sigma
    (chernoffDistance_le_liminf_errorExponent rho sigma)
    (limsup_errorExponent_le_chernoffDistance rho sigma)

/-- Zero optimal error gives infinite extended exponent. -/
theorem optimalEqualPriorTensorPowerErrorExponent_eq_top_of_optimalEqualPriorTensorPowerError_eq_zero
    (rho sigma : State a) (n : Nat)
    (h : optimalEqualPriorTensorPowerError rho sigma (n + 1) = 0) :
    optimalEqualPriorTensorPowerErrorExponent rho sigma n = ⊤ :=
  normalizedNegLog_eq_top_of_eq_zero n
    (optimalEqualPriorTensorPowerError rho sigma (n + 1)) h

/-- Positive optimal error gives the finite real-log exponent; finiteness follows from `≤ 1`. -/
theorem optimalEqualPriorTensorPowerErrorExponent_eq_coe_real_of_ne_zero
    (rho sigma : State a) (n : Nat)
    (h0 : optimalEqualPriorTensorPowerError rho sigma (n + 1) ≠ 0) :
    optimalEqualPriorTensorPowerErrorExponent rho sigma n =
      ((normalizedNegLogReal n
        (optimalEqualPriorTensorPowerError rho sigma (n + 1)) : ℝ) : EReal) :=
  normalizedNegLog_eq_coe_real_of_ne_zero_ne_top n
    (optimalEqualPriorTensorPowerError rho sigma (n + 1))
    h0
    (optimalEqualPriorTensorPowerError_ne_top rho sigma (n + 1))

/-- Finite real convergence of optimal-error exponents lifts to `EReal`.

This is the finite-limit bridge signature: the only boundary
assumption is eventual nonzero optimal error; finiteness is derived from the
probability bound. -/
theorem optimalEqualPriorTensorPowerErrorExponent_tendsto_of_eventually_finite_real_tendsto
    (rho sigma : State a) {L : ℝ}
    (h_nonzero : ∀ᶠ n in atTop,
      optimalEqualPriorTensorPowerError rho sigma (n + 1) ≠ 0)
    (hlim : Tendsto
      (fun n : Nat =>
        normalizedNegLogReal n
          (optimalEqualPriorTensorPowerError rho sigma (n + 1)))
      atTop (𝓝 L)) :
    Tendsto
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop (𝓝 (L : EReal)) := by
  have hfinite : ∀ᶠ n in atTop,
      optimalEqualPriorTensorPowerError rho sigma (n + 1) ≠ 0 ∧
        optimalEqualPriorTensorPowerError rho sigma (n + 1) ≠ ⊤ :=
    h_nonzero.and (Filter.Eventually.of_forall fun n =>
      optimalEqualPriorTensorPowerError_ne_top rho sigma (n + 1))
  exact normalizedNegLog_tendsto_coe_of_eventually_ne_zero_ne_top_real_tendsto
    hfinite hlim

/-- Real convergence to `+∞` of optimal-error exponents lifts to the `EReal` top limit. -/
theorem optimalEqualPriorTensorPowerErrorExponent_tendsto_top_of_real_tendsto_atTop
    (rho sigma : State a)
    (hlim : Tendsto
      (fun n : Nat =>
        normalizedNegLogReal n
          (optimalEqualPriorTensorPowerError rho sigma (n + 1)))
      atTop atTop) :
    Tendsto
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop (𝓝 (⊤ : EReal)) := by
  exact normalizedNegLog_tendsto_top_of_eventually_ne_top_real_tendsto_atTop
    (Filter.Eventually.of_forall fun n =>
      optimalEqualPriorTensorPowerError_ne_top rho sigma (n + 1))
    hlim

/-- Eventually zero optimal error forces the optimal-error exponent to tend to `⊤`. -/
theorem optimalEqualPriorTensorPowerErrorExponent_tendsto_top_of_eventually_zero
    (rho sigma : State a)
    (hzero : ∀ᶠ n in atTop,
      optimalEqualPriorTensorPowerError rho sigma (n + 1) = 0) :
    Tendsto
      (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
      atTop (𝓝 (⊤ : EReal)) :=
  normalizedNegLog_tendsto_top_of_eventually_eq_zero hzero

/-- Statement shape of the asymptotic quantum Chernoff bound, without proving it. -/
def asymptoticQuantumChernoffBoundStatement (rho sigma : State a) : Prop :=
  Tendsto (fun n : Nat => optimalEqualPriorTensorPowerErrorExponent rho sigma n)
    atTop (𝓝 (rho.chernoffDistance sigma))

/-- Asymptotic quantum Chernoff bound for finite-dimensional states.

This packages Tomamichel's asymptotic QCB statement using the Audenaert/Gour
finite-copy proof route already assembled in the convergence theorem. -/
theorem asymptoticQuantumChernoffBound
    (rho sigma : State a) :
    asymptoticQuantumChernoffBoundStatement rho sigma :=
  errorExponent_tendsto_chernoffDistance rho sigma

end BinaryHypothesisTest

end

end QIT
