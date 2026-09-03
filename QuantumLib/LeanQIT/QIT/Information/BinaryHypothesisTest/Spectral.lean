/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.BinaryHypothesisTest.Basic
public import QIT.Information.BinaryHypothesisTest.Classical
public import QIT.Information.Entropy.Entropy
public import QIT.Core
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Binary hypothesis test spectral API: Nussbaum-Szkola bridge

This module contains the spectral weight of a quantum state and the
Nussbaum-Szkola construction that reduces the quantum Chernoff coefficient to
its classical counterpart.  The API lives at information layer L2 because its
consumers (RenyiLimit and MutualInformationDPI) are L2, while QIT/Classical is
reserved for classical-state infrastructure.  These declarations were relocated
from QIT/HypothesisTesting/ChernoffSupport.lean as part of the L3-to-L2 layering cleanup.
-/

@[expose] public section

namespace QIT

universe u v

noncomputable section

open scoped ComplexOrder MatrixOrder NNReal ENNReal Topology
open Filter Matrix Polynomial

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace BinaryHypothesisTest

/-- Spectral probability weight of a state eigenvector. -/
def stateSpectralWeight (rho : State a) (x : a) : ℝ≥0 :=
  ⟨rho.pos.isHermitian.eigenvalues x, rho.pos.eigenvalues_nonneg x⟩

/-- Spectral weights of a density state sum to one. -/
theorem stateSpectralWeight_sum (rho : State a) :
    ∑ x : a, stateSpectralWeight rho x = 1 := by
  apply NNReal.eq
  apply Complex.ofReal_injective
  have htrace :
      (∑ x : a, ((rho.pos.isHermitian.eigenvalues x : ℝ) : ℂ)) = 1 := by
    exact rho.pos.isHermitian.trace_eq_sum_eigenvalues.symm.trans rho.trace_eq_one
  simpa [stateSpectralWeight] using htrace

/-- Transition unitary from the eigenbasis of `rho` to the eigenbasis of `sigma`. -/
def nussbaumSzkolaTransitionUnitary (rho sigma : State a) : Matrix.unitaryGroup a ℂ :=
  rho.pos.isHermitian.eigenvectorUnitary⁻¹ * sigma.pos.isHermitian.eigenvectorUnitary

/-- Nussbaum--Szkola overlap weight `|<psi_x|phi_y>|^2`. -/
def nussbaumSzkolaOverlap (rho sigma : State a) (x y : a) : ℝ≥0 :=
  ⟨Complex.normSq ((nussbaumSzkolaTransitionUnitary rho sigma : CMatrix a) x y),
    Complex.normSq_nonneg _⟩

/-- Nussbaum--Szkola overlap weights sum to one along each `rho` eigenvector. -/
theorem nussbaumSzkolaOverlap_row_sum (rho sigma : State a) (x : a) :
    ∑ y : a, nussbaumSzkolaOverlap rho sigma x y = 1 := by
  apply NNReal.eq
  simpa [nussbaumSzkolaOverlap] using
    unitary_row_normSq_sum (nussbaumSzkolaTransitionUnitary rho sigma) x

/-- Nussbaum--Szkola overlap weights sum to one along each `sigma` eigenvector. -/
theorem nussbaumSzkolaOverlap_col_sum (rho sigma : State a) (y : a) :
    ∑ x : a, nussbaumSzkolaOverlap rho sigma x y = 1 := by
  apply NNReal.eq
  simpa [nussbaumSzkolaOverlap] using
    unitary_col_normSq_sum (nussbaumSzkolaTransitionUnitary rho sigma) y

/-- Tensor product of a fixed one-copy unitary under the repository's
left-associated `TensorPower` convention. -/
def tensorPowerUnitary (U : Matrix.unitaryGroup a ℂ) :
    (n : Nat) → Matrix.unitaryGroup (TensorPower a n) ℂ
  | 0 => 1
  | n + 1 =>
      let Un := tensorPowerUnitary U n
      ⟨Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n)),
        Matrix.kronecker_mem_unitary U.2 Un.2⟩

/-- Product spectral weight of a tensor-power eigenbasis word. -/
def tensorPowerSpectralWeight (rho : State a) :
    (n : Nat) → TensorPower a n → ℝ≥0
  | 0, _ => 1
  | n + 1, x => stateSpectralWeight rho x.1 * tensorPowerSpectralWeight rho n x.2

/-- Product Nussbaum--Szkola overlap of two tensor-power eigenbasis words. -/
def tensorPowerNussbaumSzkolaOverlap (rho sigma : State a) :
    (n : Nat) → TensorPower a n → TensorPower a n → ℝ≥0
  | 0, _, _ => 1
  | n + 1, x, y =>
      nussbaumSzkolaOverlap rho sigma x.1 y.1 *
        tensorPowerNussbaumSzkolaOverlap rho sigma n x.2 y.2

/-- Tensor powers are diagonalized by the tensor product of the one-copy
eigenbasis unitary. -/
theorem tensorPower_matrix_eq_tensorPowerUnitary_diagonal
    (rho : State a) (n : Nat) :
    (rho.tensorPower n).matrix =
      (tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n :
          CMatrix (TensorPower a n)) *
        Matrix.diagonal
          (fun x : TensorPower a n => (((tensorPowerSpectralWeight rho n x : ℝ≥0) : ℝ) : ℂ)) *
          star
            (tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n :
              CMatrix (TensorPower a n)) := by
  induction n with
  | zero =>
      ext x y
      cases x
      cases y
      simp [State.tensorPower, State.unit, tensorPowerUnitary,
        tensorPowerSpectralWeight, Matrix.diagonal, Matrix.mul_apply,
        Matrix.one_apply]
  | succ n ih =>
      let U : Matrix.unitaryGroup a ℂ := rho.pos.isHermitian.eigenvectorUnitary
      let Un : Matrix.unitaryGroup (TensorPower a n) ℂ := tensorPowerUnitary U n
      let D : CMatrix a :=
        Matrix.diagonal fun x : a => (((stateSpectralWeight rho x : ℝ≥0) : ℝ) : ℂ)
      let Dn : CMatrix (TensorPower a n) :=
        Matrix.diagonal fun x : TensorPower a n =>
          (((tensorPowerSpectralWeight rho n x : ℝ≥0) : ℝ) : ℂ)
      have hrho :
          rho.matrix = (U : CMatrix a) * D * star (U : CMatrix a) := by
        simpa [U, D, stateSpectralWeight, Unitary.conjStarAlgAut_apply]
          using rho.pos.isHermitian.spectral_theorem
      change Matrix.kronecker rho.matrix (rho.tensorPower n).matrix =
        (Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n))) *
          Matrix.diagonal
            (fun x : Prod a (TensorPower a n) =>
              ((((stateSpectralWeight rho x.1 *
                tensorPowerSpectralWeight rho n x.2 : ℝ≥0) : ℝ)) : ℂ)) *
            star (Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n)))
      rw [hrho, ih]
      simp [U, Un, D,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
        Matrix.diagonal_kronecker_diagonal, Matrix.mul_assoc]

/-- Product Nussbaum--Szkola overlaps are squared transition amplitudes between
the tensor-product eigenbases. -/
theorem tensorPowerNussbaumSzkolaOverlap_eq_normSq
    (rho sigma : State a) (n : Nat) (x y : TensorPower a n) :
    (tensorPowerNussbaumSzkolaOverlap rho sigma n x y : ℝ) =
      Complex.normSq
        ((star (tensorPowerUnitary rho.pos.isHermitian.eigenvectorUnitary n :
            CMatrix (TensorPower a n)) *
          (tensorPowerUnitary sigma.pos.isHermitian.eigenvectorUnitary n :
            CMatrix (TensorPower a n))) x y) := by
  induction n with
  | zero =>
      cases x
      cases y
      simp [tensorPowerUnitary, tensorPowerNussbaumSzkolaOverlap, Matrix.mul_apply,
        Matrix.one_apply]
      change (1 : ℝ) = Complex.normSq (1 : ℂ)
      norm_num [Complex.normSq]
  | succ n ih =>
      rcases x with ⟨x0, xs⟩
      rcases y with ⟨y0, ys⟩
      let Urho : Matrix.unitaryGroup a ℂ := rho.pos.isHermitian.eigenvectorUnitary
      let Usigma : Matrix.unitaryGroup a ℂ := sigma.pos.isHermitian.eigenvectorUnitary
      let UrhoN : Matrix.unitaryGroup (TensorPower a n) ℂ := tensorPowerUnitary Urho n
      let UsigmaN : Matrix.unitaryGroup (TensorPower a n) ℂ := tensorPowerUnitary Usigma n
      have hentry :
          ((star (Matrix.kronecker (Urho : CMatrix a) (UrhoN : CMatrix (TensorPower a n))) *
              Matrix.kronecker (Usigma : CMatrix a) (UsigmaN : CMatrix (TensorPower a n)))
              (x0, xs) (y0, ys)) =
            ((star (Urho : CMatrix a) * (Usigma : CMatrix a)) x0 y0) *
              ((star (UrhoN : CMatrix (TensorPower a n)) *
                (UsigmaN : CMatrix (TensorPower a n))) xs ys) := by
        have hstar :
            star (Matrix.kronecker (Urho : CMatrix a)
                (UrhoN : CMatrix (TensorPower a n))) =
              Matrix.kronecker (star (Urho : CMatrix a))
                (star (UrhoN : CMatrix (TensorPower a n))) := by
          ext i j
          simp [Matrix.star_apply]
        rw [hstar]
        have hmul :
            Matrix.kronecker (star (Urho : CMatrix a))
                (star (UrhoN : CMatrix (TensorPower a n))) *
              Matrix.kronecker (Usigma : CMatrix a)
                (UsigmaN : CMatrix (TensorPower a n)) =
            Matrix.kronecker (star (Urho : CMatrix a) * (Usigma : CMatrix a))
              (star (UrhoN : CMatrix (TensorPower a n)) *
                (UsigmaN : CMatrix (TensorPower a n))) := by
          simpa [Matrix.kronecker] using
            (Matrix.mul_kronecker_mul
              (star (Urho : CMatrix a)) (Usigma : CMatrix a)
              (star (UrhoN : CMatrix (TensorPower a n)))
              (UsigmaN : CMatrix (TensorPower a n))).symm
        rw [hmul]
        simp
      change
        ((nussbaumSzkolaOverlap rho sigma x0 y0 *
            tensorPowerNussbaumSzkolaOverlap rho sigma n xs ys : ℝ≥0) : ℝ) =
          Complex.normSq
            ((star (Matrix.kronecker (Urho : CMatrix a)
                (UrhoN : CMatrix (TensorPower a n))) *
              Matrix.kronecker (Usigma : CMatrix a)
                (UsigmaN : CMatrix (TensorPower a n))) (x0, xs) (y0, ys))
      rw [hentry, Complex.normSq_mul]
      have hoverlap :
          (nussbaumSzkolaOverlap rho sigma x0 y0 : ℝ) =
            Complex.normSq ((star (Urho : CMatrix a) * (Usigma : CMatrix a)) x0 y0) := by
        simp only [nussbaumSzkolaOverlap, nussbaumSzkolaTransitionUnitary, Urho, Usigma,
          Matrix.star_eq_conjTranspose]
        rfl
      calc
        ((nussbaumSzkolaOverlap rho sigma x0 y0 *
            tensorPowerNussbaumSzkolaOverlap rho sigma n xs ys : ℝ≥0) : ℝ) =
            (nussbaumSzkolaOverlap rho sigma x0 y0 : ℝ) *
              (tensorPowerNussbaumSzkolaOverlap rho sigma n xs ys : ℝ) := by
              simp
        _ =
            Complex.normSq ((star (Urho : CMatrix a) * (Usigma : CMatrix a)) x0 y0) *
              (tensorPowerNussbaumSzkolaOverlap rho sigma n xs ys : ℝ) := by
              rw [hoverlap]
        _ =
            Complex.normSq ((star (Urho : CMatrix a) * (Usigma : CMatrix a)) x0 y0) *
              Complex.normSq
                ((star (UrhoN : CMatrix (TensorPower a n)) *
                  (UsigmaN : CMatrix (TensorPower a n))) xs ys) := by
              rw [ih xs ys]

omit [Fintype a] in
theorem projection_complement_isHermitian {P : CMatrix a}
    (hPherm : P.IsHermitian) :
    (1 - P).IsHermitian :=
  Matrix.isHermitian_one.sub hPherm

theorem projection_complement_idempotent {P : CMatrix a}
    (hPidem : P * P = P) :
    (1 - P) * (1 - P) = 1 - P := by
  calc
    (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    _ = 1 - P := by rw [hPidem]; abel

theorem hermitian_projection_bridge_normSq_symm {P : CMatrix a}
    (hPherm : P.IsHermitian)
    (U V : Matrix.unitaryGroup a ℂ) (x y : a) :
    Complex.normSq ((star (V : CMatrix a) * P * (U : CMatrix a)) y x) =
      Complex.normSq ((star (U : CMatrix a) * P * (V : CMatrix a)) x y) := by
  have hmatrix :
      star (star (U : CMatrix a) * P * (V : CMatrix a)) =
        star (V : CMatrix a) * P * (U : CMatrix a) := by
    simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    rw [hPherm]
  have hentry := congrFun (congrFun hmatrix y) x
  rw [← hentry]
  simp [Complex.normSq]

theorem state_trace_one_sub_projection_re_eq_nussbaumSzkola_source_sum
    (rho sigma : State a) {P : CMatrix a}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    ((rho.matrix * (1 - P)).trace).re =
      ∑ x : a, (stateSpectralWeight rho x : ℝ) *
        ∑ y : a,
          Complex.normSq
            ((star (rho.pos.isHermitian.eigenvectorUnitary : CMatrix a) *
                (1 - P) * (sigma.pos.isHermitian.eigenvectorUnitary : CMatrix a)) x y) := by
  classical
  let Urho : Matrix.unitaryGroup a ℂ := rho.pos.isHermitian.eigenvectorUnitary
  let Usigma : Matrix.unitaryGroup a ℂ := sigma.pos.isHermitian.eigenvectorUnitary
  have htrace :=
    posSemidef_trace_mul_eq_eigenvalue_conjugate_diag_sum
      (M := rho.matrix) (B := 1 - P) rho.pos
  calc
    ((rho.matrix * (1 - P)).trace).re =
        ∑ x : a, (stateSpectralWeight rho x : ℝ) *
          ((star (Urho : CMatrix a) * (1 - P) * (Urho : CMatrix a)) x x).re := by
          simpa [Urho, stateSpectralWeight] using htrace
    _ = ∑ x : a, (stateSpectralWeight rho x : ℝ) *
          ∑ y : a,
            Complex.normSq
              ((star (Urho : CMatrix a) * (1 - P) * (Usigma : CMatrix a)) x y) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [projection_conjugate_diag_re_eq_row_normSq
            (P := 1 - P)
            (projection_complement_isHermitian hPherm)
            (projection_complement_idempotent hPidem)
            Urho Usigma x]
    _ = ∑ x : a, (stateSpectralWeight rho x : ℝ) *
          ∑ y : a,
            Complex.normSq
              ((star (rho.pos.isHermitian.eigenvectorUnitary : CMatrix a) *
                  (1 - P) * (sigma.pos.isHermitian.eigenvectorUnitary : CMatrix a)) x y) := by
          rfl

theorem state_trace_projection_re_eq_nussbaumSzkola_source_sum
    (rho sigma : State a) {P : CMatrix a}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    ((sigma.matrix * P).trace).re =
      ∑ y : a, (stateSpectralWeight sigma y : ℝ) *
        ∑ x : a,
          Complex.normSq
            ((star (rho.pos.isHermitian.eigenvectorUnitary : CMatrix a) *
                P * (sigma.pos.isHermitian.eigenvectorUnitary : CMatrix a)) x y) := by
  classical
  let Urho : Matrix.unitaryGroup a ℂ := rho.pos.isHermitian.eigenvectorUnitary
  let Usigma : Matrix.unitaryGroup a ℂ := sigma.pos.isHermitian.eigenvectorUnitary
  have htrace :=
    posSemidef_trace_mul_eq_eigenvalue_conjugate_diag_sum
      (M := sigma.matrix) (B := P) sigma.pos
  calc
    ((sigma.matrix * P).trace).re =
        ∑ y : a, (stateSpectralWeight sigma y : ℝ) *
          ((star (Usigma : CMatrix a) * P * (Usigma : CMatrix a)) y y).re := by
          simpa [Usigma, stateSpectralWeight] using htrace
    _ = ∑ y : a, (stateSpectralWeight sigma y : ℝ) *
          ∑ x : a,
            Complex.normSq
              ((star (Usigma : CMatrix a) * P * (Urho : CMatrix a)) y x) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [projection_conjugate_diag_re_eq_row_normSq
            (P := P) hPherm hPidem Usigma Urho y]
    _ = ∑ y : a, (stateSpectralWeight sigma y : ℝ) *
          ∑ x : a,
            Complex.normSq
              ((star (Urho : CMatrix a) * P * (Usigma : CMatrix a)) x y) := by
          apply Finset.sum_congr rfl
          intro y _
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          rw [hermitian_projection_bridge_normSq_symm hPherm Urho Usigma x y]
    _ = ∑ y : a, (stateSpectralWeight sigma y : ℝ) *
          ∑ x : a,
            Complex.normSq
              ((star (rho.pos.isHermitian.eigenvectorUnitary : CMatrix a) *
                  P * (sigma.pos.isHermitian.eigenvectorUnitary : CMatrix a)) x y) := by
          rfl

/-- The Nussbaum--Szkola finite classical model
`p_xy = p_x |<psi_x|phi_y>|^2`,
`q_xy = q_y |<psi_x|phi_y>|^2`. -/
def nussbaumSzkolaModel (rho sigma : State a) : ClassicalBinaryModel (a × a) where
  p xy := stateSpectralWeight rho xy.1 * nussbaumSzkolaOverlap rho sigma xy.1 xy.2
  q xy := stateSpectralWeight sigma xy.2 * nussbaumSzkolaOverlap rho sigma xy.1 xy.2
  p_sum := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ x : a, ∑ y : a,
          stateSpectralWeight rho x * nussbaumSzkolaOverlap rho sigma x y)
          = ∑ x : a, stateSpectralWeight rho x *
              (∑ y : a, nussbaumSzkolaOverlap rho sigma x y) := by
            simp [Finset.mul_sum]
      _ = ∑ x : a, stateSpectralWeight rho x := by
            simp [nussbaumSzkolaOverlap_row_sum]
      _ = 1 := stateSpectralWeight_sum rho
  q_sum := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ x : a, ∑ y : a,
          stateSpectralWeight sigma y * nussbaumSzkolaOverlap rho sigma x y)
          = ∑ y : a, ∑ x : a,
              stateSpectralWeight sigma y * nussbaumSzkolaOverlap rho sigma x y := by
            rw [Finset.sum_comm]
      _ = ∑ y : a, stateSpectralWeight sigma y *
              (∑ x : a, nussbaumSzkolaOverlap rho sigma x y) := by
            simp [Finset.mul_sum]
      _ = ∑ y : a, stateSpectralWeight sigma y := by
            simp [nussbaumSzkolaOverlap_col_sum]
      _ = 1 := stateSpectralWeight_sum sigma

private theorem nussbaumSzkolaModel_petzChernoffCoefficient_term
    (p q r : ℝ≥0) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (p * r) ^ s * (q * r) ^ (1 - s) =
      p ^ s * q ^ (1 - s) * r := by
  have hs1' : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  calc
    (p * r) ^ s * (q * r) ^ (1 - s) =
        (p ^ s * r ^ s) * (q ^ (1 - s) * r ^ (1 - s)) := by
          rw [NNReal.mul_rpow, NNReal.mul_rpow]
    _ = p ^ s * q ^ (1 - s) * (r ^ s * r ^ (1 - s)) := by
          ac_rfl
    _ = p ^ s * q ^ (1 - s) * r ^ (s + (1 - s)) := by
          rw [NNReal.rpow_add_of_nonneg r hs0 hs1']
    _ = p ^ s * q ^ (1 - s) * r := by
          have hsum : s + (1 - s) = 1 := by ring
          rw [hsum, NNReal.rpow_one]

/-- Nussbaum--Szkola classical Chernoff coefficient equals the quantum Petz
Chernoff coefficient.  The exponent convention matches
`State.petzRenyiCoefficient`, namely `Tr(ρ^s σ^(1-s))`
[Gour2024Resources, BookQRT.tex:15911-15949]. -/
theorem nussbaumSzkolaModel_petzChernoffCoefficient_eq
    (rho sigma : State a) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (nussbaumSzkolaModel rho sigma).petzChernoffCoefficient s =
      rho.petzRenyiCoefficient sigma s := by
  classical
  let Urho : Matrix.unitaryGroup a ℂ := rho.pos.isHermitian.eigenvectorUnitary
  let Usigma : Matrix.unitaryGroup a ℂ := sigma.pos.isHermitian.eigenvectorUnitary
  have hrho :
      CFC.rpow rho.matrix s =
        (Urho : CMatrix a) *
          Matrix.diagonal (fun x => (((stateSpectralWeight rho x : ℝ) ^ s : ℝ) : ℂ)) *
            star (Urho : CMatrix a) := by
    simpa [Urho, stateSpectralWeight] using
      cMatrix_rpow_eq_eigenbasis_diagonal rho.pos s
  have hsigma :
      CFC.rpow sigma.matrix (1 - s) =
        (Usigma : CMatrix a) *
          Matrix.diagonal
            (fun y => (((stateSpectralWeight sigma y : ℝ) ^ (1 - s) : ℝ) : ℂ)) *
            star (Usigma : CMatrix a) := by
    simpa [Usigma, stateSpectralWeight] using
      cMatrix_rpow_eq_eigenbasis_diagonal sigma.pos (1 - s)
  have htrace :
      (rho.petzRenyiCoefficient sigma s : ℝ) =
        ∑ x : a, ∑ y : a,
          ((stateSpectralWeight rho x : ℝ) ^ s) *
            ((stateSpectralWeight sigma y : ℝ) ^ (1 - s)) *
              (nussbaumSzkolaOverlap rho sigma x y : ℝ) := by
    change ((CFC.rpow rho.matrix s * CFC.rpow sigma.matrix (1 - s)).trace).re = _
    rw [hrho, hsigma]
    simpa [Urho, Usigma, nussbaumSzkolaOverlap, nussbaumSzkolaTransitionUnitary,
      Matrix.star_eq_conjTranspose, mul_assoc, mul_left_comm, mul_comm] using
      trace_mul_two_unitary_conj_diagonal_ofReal_re
        Urho Usigma
        (fun x : a => (stateSpectralWeight rho x : ℝ) ^ s)
        (fun y : a => (stateSpectralWeight sigma y : ℝ) ^ (1 - s))
  apply NNReal.eq
  calc
    ((nussbaumSzkolaModel rho sigma).petzChernoffCoefficient s : ℝ) =
        ∑ xy : a × a,
          (((stateSpectralWeight rho xy.1) ^ s *
            (stateSpectralWeight sigma xy.2) ^ (1 - s) *
              nussbaumSzkolaOverlap rho sigma xy.1 xy.2 : ℝ≥0) : ℝ) := by
          simp [ClassicalBinaryModel.petzChernoffCoefficient, nussbaumSzkolaModel,
            nussbaumSzkolaModel_petzChernoffCoefficient_term _ _ _ hs0 hs1,
            mul_assoc]
    _ = ∑ x : a, ∑ y : a,
          ((stateSpectralWeight rho x : ℝ) ^ s) *
            ((stateSpectralWeight sigma y : ℝ) ^ (1 - s)) *
              (nussbaumSzkolaOverlap rho sigma x y : ℝ) := by
          rw [Fintype.sum_prod_type]
          simp [NNReal.coe_rpow, mul_assoc]
    _ = (rho.petzRenyiCoefficient sigma s : ℝ) := htrace.symm

/-- The one-copy Nussbaum--Szkola classical Chernoff distance matches the
quantum Chernoff distance. -/
theorem nussbaumSzkolaModel_chernoffDistance_eq
    (rho sigma : State a) :
    (nussbaumSzkolaModel rho sigma).chernoffDistance =
      rho.chernoffDistance sigma := by
  unfold ClassicalBinaryModel.chernoffDistance State.chernoffDistance
  apply iSup_congr
  intro s
  simp [ClassicalBinaryModel.chernoffExponent, State.petzChernoffExponent,
    nussbaumSzkolaModel_petzChernoffCoefficient_eq rho sigma s.2.1 s.2.2]



/-- Product eigenbasis unitary for the product of the two marginals of a
bipartite state. -/
def productMarginalEigenvectorUnitary
    (rhoAB : State (Prod a b)) : Matrix.unitaryGroup (Prod a b) ℂ :=
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoAB.marginalA.pos.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ :=
    rhoAB.marginalB.pos.isHermitian.eigenvectorUnitary
  ⟨Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b),
    Matrix.kronecker_mem_unitary UA.2 UB.2⟩

/-- Transition from the eigenbasis of `rhoAB` to the product eigenbasis of its
marginals. -/
def productMarginalNussbaumSzkolaTransitionUnitary
    (rhoAB : State (Prod a b)) : Matrix.unitaryGroup (Prod a b) ℂ :=
  rhoAB.pos.isHermitian.eigenvectorUnitary⁻¹ *
    productMarginalEigenvectorUnitary rhoAB

/-- Product-marginal Nussbaum--Szkola overlap
`|<rhoAB_x|rhoA_i tensor rhoB_j>|^2`. -/
def productMarginalNussbaumSzkolaOverlap
    (rhoAB : State (Prod a b)) (x y : Prod a b) : NNReal :=
  ⟨Complex.normSq
    ((productMarginalNussbaumSzkolaTransitionUnitary rhoAB : CMatrix (Prod a b)) x y),
    Complex.normSq_nonneg _⟩

theorem productMarginalNussbaumSzkolaOverlap_row_sum
    (rhoAB : State (Prod a b)) (x : Prod a b) :
    ∑ y : Prod a b, productMarginalNussbaumSzkolaOverlap rhoAB x y = 1 := by
  apply NNReal.eq
  simpa [productMarginalNussbaumSzkolaOverlap] using
    unitary_row_normSq_sum
      (productMarginalNussbaumSzkolaTransitionUnitary rhoAB) x

theorem productMarginalNussbaumSzkolaOverlap_col_sum
    (rhoAB : State (Prod a b)) (y : Prod a b) :
    ∑ x : Prod a b, productMarginalNussbaumSzkolaOverlap rhoAB x y = 1 := by
  apply NNReal.eq
  simpa [productMarginalNussbaumSzkolaOverlap] using
    unitary_col_normSq_sum
      (productMarginalNussbaumSzkolaTransitionUnitary rhoAB) y

/-- Spectral weights of a product of the two marginals, expressed in the
explicit product marginal eigenbasis. -/
def productMarginalSpectralWeight
    (rhoAB : State (Prod a b)) (y : Prod a b) : NNReal :=
  stateSpectralWeight rhoAB.marginalA y.1 *
    stateSpectralWeight rhoAB.marginalB y.2

theorem productMarginalSpectralWeight_sum
    (rhoAB : State (Prod a b)) :
    ∑ y : Prod a b, productMarginalSpectralWeight rhoAB y = 1 := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : a, ∑ y : b,
        stateSpectralWeight rhoAB.marginalA x *
          stateSpectralWeight rhoAB.marginalB y)
        =
      ∑ x : a, stateSpectralWeight rhoAB.marginalA x *
        (∑ y : b, stateSpectralWeight rhoAB.marginalB y) := by
        simp [Finset.mul_sum]
    _ = ∑ x : a, stateSpectralWeight rhoAB.marginalA x := by
        simp [stateSpectralWeight_sum]
    _ = 1 := stateSpectralWeight_sum rhoAB.marginalA

/-- The product of the two marginals is diagonalized by the explicit tensor
product of the marginal eigenbases. -/
theorem productMarginal_matrix_eq_productEigenbasis_diagonal
    (rhoAB : State (Prod a b)) :
    (rhoAB.marginalA.prod rhoAB.marginalB).matrix =
      (productMarginalEigenvectorUnitary rhoAB : CMatrix (Prod a b)) *
        Matrix.diagonal
          (fun y : Prod a b =>
            (((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) : ℂ)) *
        star (productMarginalEigenvectorUnitary rhoAB : CMatrix (Prod a b)) := by
  classical
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoAB.marginalA.pos.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ :=
    rhoAB.marginalB.pos.isHermitian.eigenvectorUnitary
  have hA :
      rhoAB.marginalA.matrix =
        (UA : CMatrix a) *
          Matrix.diagonal
            (fun x : a => (((stateSpectralWeight rhoAB.marginalA x : NNReal) : ℝ) : ℂ)) *
          star (UA : CMatrix a) := by
    simpa [UA, stateSpectralWeight, Function.comp_def,
      Unitary.conjStarAlgAut_apply]
      using rhoAB.marginalA.pos.isHermitian.spectral_theorem
  have hB :
      rhoAB.marginalB.matrix =
        (UB : CMatrix b) *
          Matrix.diagonal
            (fun y : b => (((stateSpectralWeight rhoAB.marginalB y : NNReal) : ℝ) : ℂ)) *
          star (UB : CMatrix b) := by
    simpa [UB, stateSpectralWeight, Function.comp_def,
      Unitary.conjStarAlgAut_apply]
      using rhoAB.marginalB.pos.isHermitian.spectral_theorem
  change Matrix.kronecker rhoAB.marginalA.matrix rhoAB.marginalB.matrix =
    (productMarginalEigenvectorUnitary rhoAB : CMatrix (Prod a b)) *
      Matrix.diagonal
        (fun y : Prod a b =>
          (((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) : ℂ)) *
      star (productMarginalEigenvectorUnitary rhoAB : CMatrix (Prod a b))
  rw [hA, hB]
  simp [productMarginalEigenvectorUnitary, productMarginalSpectralWeight, UA, UB,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal,
    Matrix.mul_assoc]

/-- Product-marginal Nussbaum--Szkola model.  Its second spectral basis is the
explicit tensor-product eigenbasis of `rhoAB.marginalA.prod rhoAB.marginalB`,
so the endpoint KL can be identified directly with entropy-form mutual
information. -/
def productMarginalNussbaumSzkolaModel
    (rhoAB : State (Prod a b)) :
    ClassicalBinaryModel ((Prod a b) × (Prod a b)) where
  p xy :=
    stateSpectralWeight rhoAB xy.1 *
      productMarginalNussbaumSzkolaOverlap rhoAB xy.1 xy.2
  q xy :=
    productMarginalSpectralWeight rhoAB xy.2 *
      productMarginalNussbaumSzkolaOverlap rhoAB xy.1 xy.2
  p_sum := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ x : Prod a b, ∑ y : Prod a b,
          stateSpectralWeight rhoAB x *
            productMarginalNussbaumSzkolaOverlap rhoAB x y)
          =
        ∑ x : Prod a b, stateSpectralWeight rhoAB x *
          (∑ y : Prod a b, productMarginalNussbaumSzkolaOverlap rhoAB x y) := by
          simp [Finset.mul_sum]
      _ = ∑ x : Prod a b, stateSpectralWeight rhoAB x := by
          simp [productMarginalNussbaumSzkolaOverlap_row_sum]
      _ = 1 := stateSpectralWeight_sum rhoAB
  q_sum := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ x : Prod a b, ∑ y : Prod a b,
          productMarginalSpectralWeight rhoAB y *
            productMarginalNussbaumSzkolaOverlap rhoAB x y)
          =
        ∑ y : Prod a b, ∑ x : Prod a b,
          productMarginalSpectralWeight rhoAB y *
            productMarginalNussbaumSzkolaOverlap rhoAB x y := by
          rw [Finset.sum_comm]
      _ =
        ∑ y : Prod a b, productMarginalSpectralWeight rhoAB y *
          (∑ x : Prod a b, productMarginalNussbaumSzkolaOverlap rhoAB x y) := by
          simp [Finset.mul_sum]
      _ = ∑ y : Prod a b, productMarginalSpectralWeight rhoAB y := by
          simp [productMarginalNussbaumSzkolaOverlap_col_sum]
      _ = 1 := productMarginalSpectralWeight_sum rhoAB

/-- The product-marginal Nussbaum--Szkola `p` distribution is supported by
its `q` distribution. -/
theorem productMarginalNussbaumSzkolaModel_p_supportedBy_q
    (rhoAB : State (Prod a b)) :
    (productMarginalNussbaumSzkolaModel rhoAB).pDistribution.SupportedBy
      (productMarginalNussbaumSzkolaModel rhoAB).q := by
  classical
  intro xy hp
  rcases xy with ⟨x, y⟩
  by_contra hq
  have hq_zero :
      (productMarginalNussbaumSzkolaModel rhoAB).q (x, y) = 0 := hq
  have hp_nonzero :
      (productMarginalNussbaumSzkolaModel rhoAB).p (x, y) ≠ 0 := hp
  have hweight_or_overlap :
      productMarginalSpectralWeight rhoAB y = 0 ∨
        productMarginalNussbaumSzkolaOverlap rhoAB x y = 0 := by
    simpa [productMarginalNussbaumSzkolaModel, mul_eq_zero] using hq_zero
  rcases hweight_or_overlap with hweight_zero | hoverlap_zero
  · let Urho : Matrix.unitaryGroup (Prod a b) ℂ :=
      rhoAB.pos.isHermitian.eigenvectorUnitary
    let Uprod : Matrix.unitaryGroup (Prod a b) ℂ :=
      productMarginalEigenvectorUnitary rhoAB
    let sigma : State (Prod a b) := rhoAB.marginalA.prod rhoAB.marginalB
    let Dprod : CMatrix (Prod a b) :=
      Matrix.diagonal
        (fun i : Prod a b =>
          (((productMarginalSpectralWeight rhoAB i : NNReal) : ℝ) : ℂ))
    have hsigma_spec :
        sigma.matrix = (Uprod : CMatrix (Prod a b)) * Dprod *
          star (Uprod : CMatrix (Prod a b)) := by
      simpa [sigma, Uprod, Dprod] using
        productMarginal_matrix_eq_productEigenbasis_diagonal rhoAB
    have hsigma_mul :
        sigma.matrix * (Uprod : CMatrix (Prod a b)) =
          (Uprod : CMatrix (Prod a b)) * Dprod := by
      rw [hsigma_spec]
      calc
        ((Uprod : CMatrix (Prod a b)) * Dprod *
            star (Uprod : CMatrix (Prod a b))) *
            (Uprod : CMatrix (Prod a b))
            =
          (Uprod : CMatrix (Prod a b)) * Dprod *
            (star (Uprod : CMatrix (Prod a b)) *
              (Uprod : CMatrix (Prod a b))) := by
            noncomm_ring
        _ = (Uprod : CMatrix (Prod a b)) * Dprod := by
            rw [Unitary.coe_star_mul_self]
            simp
    have hsigma_col :
        ∀ k, (sigma.matrix * (Uprod : CMatrix (Prod a b))) k y = 0 := by
      intro k
      rw [hsigma_mul]
      simp [Dprod, Matrix.mul_apply, Matrix.diagonal, hweight_zero]
    let v : Prod a b → ℂ := fun i => (Uprod : CMatrix (Prod a b)) i y
    have hsigma_v : sigma.matrix.mulVec v = 0 := by
      ext k
      simpa [v, Matrix.mulVec, dotProduct, Matrix.mul_apply] using hsigma_col k
    have hrho_v : rhoAB.matrix.mulVec v = 0 :=
      rhoAB.matrix_supports_prod_marginals v (by simpa [sigma] using hsigma_v)
    have hrho_col :
        ∀ k, (rhoAB.matrix * (Uprod : CMatrix (Prod a b))) k y = 0 := by
      intro k
      have hk := congrFun hrho_v k
      simpa [v, Matrix.mulVec, dotProduct, Matrix.mul_apply] using hk
    have hleft :
        (star (Urho : CMatrix (Prod a b)) * rhoAB.matrix *
          (Uprod : CMatrix (Prod a b))) x y = 0 := by
      rw [Matrix.mul_assoc]
      simp [Matrix.mul_apply, hrho_col]
    let T : CMatrix (Prod a b) :=
      star (Urho : CMatrix (Prod a b)) * (Uprod : CMatrix (Prod a b))
    let Drho : CMatrix (Prod a b) :=
      Matrix.diagonal
        (fun i : Prod a b =>
          (((stateSpectralWeight rhoAB i : NNReal) : ℝ) : ℂ))
    have hrho_diag :
        rhoAB.matrix = (Urho : CMatrix (Prod a b)) * Drho *
          star (Urho : CMatrix (Prod a b)) := by
      simpa [Urho, Drho, Function.comp_def, stateSpectralWeight,
        Unitary.conjStarAlgAut_apply]
        using rhoAB.pos.isHermitian.spectral_theorem
    have hleft_diag :
        (star (Urho : CMatrix (Prod a b)) * rhoAB.matrix *
          (Uprod : CMatrix (Prod a b))) x y =
          (((stateSpectralWeight rhoAB x : NNReal) : ℝ) : ℂ) * T x y := by
      have hmatrix :
          star (Urho : CMatrix (Prod a b)) * rhoAB.matrix *
            (Uprod : CMatrix (Prod a b)) =
              Drho * T := by
        rw [hrho_diag]
        dsimp [Drho, T]
        calc
          star (Urho : CMatrix (Prod a b)) *
              ((Urho : CMatrix (Prod a b)) * Drho *
                star (Urho : CMatrix (Prod a b))) *
                (Uprod : CMatrix (Prod a b))
              =
                (star (Urho : CMatrix (Prod a b)) *
                  (Urho : CMatrix (Prod a b))) *
                  (Drho * (star (Urho : CMatrix (Prod a b)) *
                    (Uprod : CMatrix (Prod a b)))) := by
                noncomm_ring
          _ = Drho *
                (star (Urho : CMatrix (Prod a b)) *
                  (Uprod : CMatrix (Prod a b)) ) := by
                rw [Unitary.coe_star_mul_self]
                simp
      have hentry := congrFun (congrFun hmatrix x) y
      simpa [Drho, T, Matrix.mul_apply, Matrix.diagonal] using hentry
    have hprod_zero :
        (((stateSpectralWeight rhoAB x : NNReal) : ℝ) : ℂ) * T x y = 0 := by
      rw [← hleft_diag]
      exact hleft
    have hp_zero :
        (productMarginalNussbaumSzkolaModel rhoAB).p (x, y) = 0 := by
      rcases mul_eq_zero.mp hprod_zero with hstate | htransition
      · have hstate_real : ((stateSpectralWeight rhoAB x : NNReal) : ℝ) = 0 :=
          Complex.ofReal_eq_zero.mp hstate
        have hstate_nn : stateSpectralWeight rhoAB x = 0 := by
          apply NNReal.eq
          simpa using hstate_real
        simp [productMarginalNussbaumSzkolaModel, hstate_nn]
      · have hoverlap_nn :
          productMarginalNussbaumSzkolaOverlap rhoAB x y = 0 := by
          have hT_entry :
              ((productMarginalNussbaumSzkolaTransitionUnitary rhoAB :
                CMatrix (Prod a b)) x y) = T x y := by
            simp [productMarginalNussbaumSzkolaTransitionUnitary, T, Urho, Uprod,
              Matrix.star_eq_conjTranspose]
          apply NNReal.eq
          change Complex.normSq
              ((productMarginalNussbaumSzkolaTransitionUnitary rhoAB :
                CMatrix (Prod a b)) x y) = 0
          rw [hT_entry, htransition]
          simp [Complex.normSq]
        simp [productMarginalNussbaumSzkolaModel, hoverlap_nn]
    exact hp_nonzero hp_zero
  · have hp_zero :
        (productMarginalNussbaumSzkolaModel rhoAB).p (x, y) = 0 := by
      simp [productMarginalNussbaumSzkolaModel, hoverlap_zero]
    exact hp_nonzero hp_zero

/-- The `p`-weighted transition probabilities, summed over the global
eigenbasis of `rhoAB`, give the diagonal of `rhoAB` in the product marginal
eigenbasis. -/
theorem productMarginalNussbaumSzkolaOverlap_weighted_col_sum_eq_productBasis_diag
    (rhoAB : State (Prod a b)) (y : Prod a b) :
    ∑ x : Prod a b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) =
      ((star (productMarginalEigenvectorUnitary rhoAB : CMatrix (Prod a b)) *
        rhoAB.matrix * (productMarginalEigenvectorUnitary rhoAB : CMatrix (Prod a b)))
          y y).re := by
  classical
  let Urho : Matrix.unitaryGroup (Prod a b) ℂ :=
    rhoAB.pos.isHermitian.eigenvectorUnitary
  let Uprod : Matrix.unitaryGroup (Prod a b) ℂ :=
    productMarginalEigenvectorUnitary rhoAB
  let D : CMatrix (Prod a b) :=
    Matrix.diagonal
      (fun x : Prod a b => (((stateSpectralWeight rhoAB x : NNReal) : ℝ) : ℂ))
  let T : CMatrix (Prod a b) :=
    star (Urho : CMatrix (Prod a b)) * (Uprod : CMatrix (Prod a b))
  have hrho :
      rhoAB.matrix = (Urho : CMatrix (Prod a b)) * D * star (Urho : CMatrix (Prod a b)) := by
    simpa [Urho, D, stateSpectralWeight, Function.comp_def,
      Unitary.conjStarAlgAut_apply]
      using rhoAB.pos.isHermitian.spectral_theorem
  have hmatrix :
      star (Uprod : CMatrix (Prod a b)) * rhoAB.matrix *
          (Uprod : CMatrix (Prod a b)) =
        star T * D * T := by
    rw [hrho]
    dsimp [T]
    calc
      star (Uprod : CMatrix (Prod a b)) *
          ((Urho : CMatrix (Prod a b)) * D * star (Urho : CMatrix (Prod a b))) *
          (Uprod : CMatrix (Prod a b))
          =
        (star (Uprod : CMatrix (Prod a b)) * (Urho : CMatrix (Prod a b))) *
          D * (star (Urho : CMatrix (Prod a b)) * (Uprod : CMatrix (Prod a b))) := by
            noncomm_ring
      _ = star (star (Urho : CMatrix (Prod a b)) * (Uprod : CMatrix (Prod a b))) *
          D * (star (Urho : CMatrix (Prod a b)) * (Uprod : CMatrix (Prod a b))) := by
            simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have hentry := congrFun (congrFun hmatrix y) y
  have hre := congrArg Complex.re hentry
  have hdiag :
      ((star T * D * T) y y).re =
        ∑ x : Prod a b,
          ((stateSpectralWeight rhoAB x : NNReal) : ℝ) * Complex.normSq (T x y) := by
    simp [D, Matrix.mul_apply, Matrix.diagonal,
      Matrix.star_eq_conjTranspose, Complex.normSq_apply,
      mul_left_comm, mul_comm]
  change
    ∑ x : Prod a b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) =
      ((star (Uprod : CMatrix (Prod a b)) * rhoAB.matrix *
        (Uprod : CMatrix (Prod a b))) y y).re
  rw [hre]
  rw [hdiag]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  have hoverlap :
      ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) =
        Complex.normSq (T x y) := by
    change Complex.normSq
        ((productMarginalNussbaumSzkolaTransitionUnitary rhoAB : CMatrix (Prod a b)) x y) =
      Complex.normSq (T x y)
    congr 1
  rw [hoverlap]

/-- The first marginal of the product-marginal Nussbaum--Szkola `p`
distribution is the spectral distribution of `rhoAB.marginalA`. -/
theorem productMarginalNussbaumSzkolaOverlap_weighted_fst_sum
    (rhoAB : State (Prod a b)) (i : a) :
    ∑ x : Prod a b, ∑ j : b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x (i, j) : NNReal) : ℝ) =
      ((stateSpectralWeight rhoAB.marginalA i : NNReal) : ℝ) := by
  classical
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoAB.marginalA.pos.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ :=
    rhoAB.marginalB.pos.isHermitian.eigenvectorUnitary
  let Uprod : Matrix.unitaryGroup (Prod a b) ℂ :=
    productMarginalEigenvectorUnitary rhoAB
  let M : CMatrix (Prod a b) :=
    star (Uprod : CMatrix (Prod a b)) * rhoAB.matrix * (Uprod : CMatrix (Prod a b))
  have hdiag_sum :
      ∑ j : b, (M (i, j) (i, j)).re =
        ((stateSpectralWeight rhoAB.marginalA i : NNReal) : ℝ) := by
    have hpt :=
      partialTraceB_local_unitary_conj (a := a) (b := b)
        rhoAB.matrix UA UB
    have hUprod :
        (Uprod : CMatrix (Prod a b)) =
          Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b) := by
      rfl
    have hptM :
        partialTraceB (a := a) (b := b) M =
          star (UA : CMatrix a) * rhoAB.marginalA.matrix * (UA : CMatrix a) := by
      simpa [M, Uprod, hUprod, State.marginalA_matrix] using hpt
    have hdiag :
        star (UA : CMatrix a) * rhoAB.marginalA.matrix * (UA : CMatrix a) =
          Matrix.diagonal
            (fun k : a => (((stateSpectralWeight rhoAB.marginalA k : NNReal) : ℝ) : ℂ)) := by
      have hspec := rhoAB.marginalA.pos.isHermitian.spectral_theorem
      have hρA :
          rhoAB.marginalA.matrix =
            (UA : CMatrix a) *
              Matrix.diagonal
                (fun k : a =>
                  (((stateSpectralWeight rhoAB.marginalA k : NNReal) : ℝ) : ℂ)) *
              star (UA : CMatrix a) := by
        simpa [UA, stateSpectralWeight, Function.comp_def,
          Unitary.conjStarAlgAut_apply] using hspec
      calc
        star (UA : CMatrix a) * rhoAB.marginalA.matrix * (UA : CMatrix a)
            = star (UA : CMatrix a) *
                ((UA : CMatrix a) *
                  Matrix.diagonal
                    (fun k : a =>
                      (((stateSpectralWeight rhoAB.marginalA k : NNReal) : ℝ) : ℂ)) *
                  star (UA : CMatrix a)) *
                (UA : CMatrix a) := by
                  rw [hρA]
        _ = (star (UA : CMatrix a) * (UA : CMatrix a)) *
              Matrix.diagonal
                (fun k : a =>
                  (((stateSpectralWeight rhoAB.marginalA k : NNReal) : ℝ) : ℂ)) *
              (star (UA : CMatrix a) * (UA : CMatrix a)) := by
                noncomm_ring
        _ = Matrix.diagonal
              (fun k : a =>
                (((stateSpectralWeight rhoAB.marginalA k : NNReal) : ℝ) : ℂ)) := by
              rw [Unitary.coe_star_mul_self]
              simp
    have hentry :
        (partialTraceB (a := a) (b := b) M) i i =
          (Matrix.diagonal
            (fun k : a => (((stateSpectralWeight rhoAB.marginalA k : NNReal) : ℝ) : ℂ))
              : CMatrix a) i i := by
      rw [hptM, hdiag]
    have hre := congrArg Complex.re hentry
    simpa [partialTraceB, Matrix.diagonal, M] using hre
  calc
    ∑ x : Prod a b, ∑ j : b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x (i, j) : NNReal) : ℝ)
        =
      ∑ j : b, ∑ x : Prod a b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x (i, j) : NNReal) : ℝ) := by
        rw [Finset.sum_comm]
    _ = ∑ j : b, (M (i, j) (i, j)).re := by
        refine Finset.sum_congr rfl ?_
        intro j _hj
        exact productMarginalNussbaumSzkolaOverlap_weighted_col_sum_eq_productBasis_diag
          rhoAB (i, j)
    _ = ((stateSpectralWeight rhoAB.marginalA i : NNReal) : ℝ) := hdiag_sum

/-- The second marginal of the product-marginal Nussbaum--Szkola `p`
distribution is the spectral distribution of `rhoAB.marginalB`. -/
theorem productMarginalNussbaumSzkolaOverlap_weighted_snd_sum
    (rhoAB : State (Prod a b)) (j : b) :
    ∑ x : Prod a b, ∑ i : a,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x (i, j) : NNReal) : ℝ) =
      ((stateSpectralWeight rhoAB.marginalB j : NNReal) : ℝ) := by
  classical
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoAB.marginalA.pos.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ :=
    rhoAB.marginalB.pos.isHermitian.eigenvectorUnitary
  let Uprod : Matrix.unitaryGroup (Prod a b) ℂ :=
    productMarginalEigenvectorUnitary rhoAB
  let M : CMatrix (Prod a b) :=
    star (Uprod : CMatrix (Prod a b)) * rhoAB.matrix * (Uprod : CMatrix (Prod a b))
  have hdiag_sum :
      ∑ i : a, (M (i, j) (i, j)).re =
        ((stateSpectralWeight rhoAB.marginalB j : NNReal) : ℝ) := by
    have hpt :=
      partialTraceA_local_unitary_conj (a := a) (b := b)
        rhoAB.matrix UA UB
    have hUprod :
        (Uprod : CMatrix (Prod a b)) =
          Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b) := by
      rfl
    have hptM :
        partialTraceA (a := a) (b := b) M =
          star (UB : CMatrix b) * rhoAB.marginalB.matrix * (UB : CMatrix b) := by
      simpa [M, Uprod, hUprod, State.marginalB_matrix] using hpt
    have hdiag :
        star (UB : CMatrix b) * rhoAB.marginalB.matrix * (UB : CMatrix b) =
          Matrix.diagonal
            (fun k : b => (((stateSpectralWeight rhoAB.marginalB k : NNReal) : ℝ) : ℂ)) := by
      have hspec := rhoAB.marginalB.pos.isHermitian.spectral_theorem
      have hρB :
          rhoAB.marginalB.matrix =
            (UB : CMatrix b) *
              Matrix.diagonal
                (fun k : b =>
                  (((stateSpectralWeight rhoAB.marginalB k : NNReal) : ℝ) : ℂ)) *
              star (UB : CMatrix b) := by
        simpa [UB, stateSpectralWeight, Function.comp_def,
          Unitary.conjStarAlgAut_apply] using hspec
      calc
        star (UB : CMatrix b) * rhoAB.marginalB.matrix * (UB : CMatrix b)
            = star (UB : CMatrix b) *
                ((UB : CMatrix b) *
                  Matrix.diagonal
                    (fun k : b =>
                      (((stateSpectralWeight rhoAB.marginalB k : NNReal) : ℝ) : ℂ)) *
                  star (UB : CMatrix b)) *
                (UB : CMatrix b) := by
                  rw [hρB]
        _ = (star (UB : CMatrix b) * (UB : CMatrix b)) *
              Matrix.diagonal
                (fun k : b =>
                  (((stateSpectralWeight rhoAB.marginalB k : NNReal) : ℝ) : ℂ)) *
              (star (UB : CMatrix b) * (UB : CMatrix b)) := by
                noncomm_ring
        _ = Matrix.diagonal
              (fun k : b =>
                (((stateSpectralWeight rhoAB.marginalB k : NNReal) : ℝ) : ℂ)) := by
              rw [Unitary.coe_star_mul_self]
              simp
    have hentry :
        (partialTraceA (a := a) (b := b) M) j j =
          (Matrix.diagonal
            (fun k : b => (((stateSpectralWeight rhoAB.marginalB k : NNReal) : ℝ) : ℂ))
              : CMatrix b) j j := by
      rw [hptM, hdiag]
    have hre := congrArg Complex.re hentry
    simpa [partialTraceA, Matrix.diagonal, M] using hre
  calc
    ∑ x : Prod a b, ∑ i : a,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x (i, j) : NNReal) : ℝ)
        =
      ∑ i : a, ∑ x : Prod a b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x (i, j) : NNReal) : ℝ) := by
        rw [Finset.sum_comm]
    _ = ∑ i : a, (M (i, j) (i, j)).re := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        exact productMarginalNussbaumSzkolaOverlap_weighted_col_sum_eq_productBasis_diag
          rhoAB (i, j)
    _ = ((stateSpectralWeight rhoAB.marginalB j : NNReal) : ℝ) := hdiag_sum

/-- The log of the product-marginal spectral weight splits after multiplying by
the joint diagonal weight.  If one marginal eigenvalue is zero, the support
bridge makes the joint diagonal weight zero as well. -/
theorem productMarginalNussbaumSzkolaModel_weighted_log_product
    (rhoAB : State (Prod a b)) (y : Prod a b) :
    (∑ x : Prod a b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ)) *
        Real.log ((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) =
      (∑ x : Prod a b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ)) *
        (Real.log ((stateSpectralWeight rhoAB.marginalA y.1 : NNReal) : ℝ) +
          Real.log ((stateSpectralWeight rhoAB.marginalB y.2 : NNReal) : ℝ)) := by
  classical
  by_cases hmu : productMarginalSpectralWeight rhoAB y = 0
  · have hcoeff_zero :
        ∑ x : Prod a b,
          ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
            ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x _hx
      have hq :
          (productMarginalNussbaumSzkolaModel rhoAB).q (x, y) = 0 := by
        simp [productMarginalNussbaumSzkolaModel, hmu]
      have hp :
          (productMarginalNussbaumSzkolaModel rhoAB).p (x, y) = 0 := by
        by_contra hp_ne
        exact (productMarginalNussbaumSzkolaModel_p_supportedBy_q rhoAB (x, y) hp_ne) hq
      have hfactor :
          ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
            ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) = 0 := by
        have hpR : (((productMarginalNussbaumSzkolaModel rhoAB).p (x, y) : NNReal) : ℝ) = 0 := by
          rw [hp]
          norm_num
        simpa [productMarginalNussbaumSzkolaModel, NNReal.coe_mul] using hpR
      exact hfactor
    simp [hcoeff_zero]
  · have hA_ne : stateSpectralWeight rhoAB.marginalA y.1 ≠ 0 :=
      (mul_ne_zero_iff.mp (by simpa [productMarginalSpectralWeight] using hmu)).1
    have hB_ne : stateSpectralWeight rhoAB.marginalB y.2 ≠ 0 :=
      (mul_ne_zero_iff.mp (by simpa [productMarginalSpectralWeight] using hmu)).2
    have hA_pos : 0 < ((stateSpectralWeight rhoAB.marginalA y.1 : NNReal) : ℝ) := by
      have hnn : (0 : NNReal) < stateSpectralWeight rhoAB.marginalA y.1 :=
        lt_of_le_of_ne (show (0 : NNReal) ≤ stateSpectralWeight rhoAB.marginalA y.1 from zero_le)
          (Ne.symm hA_ne)
      exact_mod_cast hnn
    have hB_pos : 0 < ((stateSpectralWeight rhoAB.marginalB y.2 : NNReal) : ℝ) := by
      have hnn : (0 : NNReal) < stateSpectralWeight rhoAB.marginalB y.2 :=
        lt_of_le_of_ne (show (0 : NNReal) ≤ stateSpectralWeight rhoAB.marginalB y.2 from zero_le)
          (Ne.symm hB_ne)
      exact_mod_cast hnn
    rw [productMarginalSpectralWeight, NNReal.coe_mul]
    rw [Real.log_mul hA_pos.ne' hB_pos.ne']

end BinaryHypothesisTest

namespace State

/-- Entropy as the spectral-weight sum used by the Nussbaum--Szkola models. -/
theorem vonNeumann_eq_neg_sum_stateSpectralWeight (ρ : State a) :
    ρ.vonNeumann =
      -∑ x : a, xlog2 ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) := by
  unfold State.vonNeumann BinaryHypothesisTest.stateSpectralWeight
  congr 1

/-- Change-of-base bridge for the entropy summand used in spectral sums. -/
private lemma xlog2_mul_log_two {x : ℝ} (hx : 0 ≤ x) :
    xlog2 x * Real.log 2 = x * Real.log x := by
  by_cases hzx : x = 0
  · simp [xlog2, hzx, Real.log_zero]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hzx)
    simp only [xlog2, if_neg (ne_of_gt hxp), log2]
    field_simp

/-- Spectral log sums are the negative von Neumann entropy after dividing by
`log 2`. -/
theorem spectralWeight_mul_log_div_log_two_eq_neg_vonNeumann
    (ρ : State a) :
    (∑ x : a,
        ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) *
          Real.log ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ)) /
      Real.log 2 =
        -ρ.vonNeumann := by
  classical
  have hlog_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hmul :
      (∑ x : a,
          xlog2 ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ)) *
        Real.log 2 =
      ∑ x : a,
        ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) *
          Real.log ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro x _hx
    exact xlog2_mul_log_two (NNReal.coe_nonneg _)
  have hdiv :
      (∑ x : a,
          ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) *
            Real.log ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ)) /
        Real.log 2 =
      ∑ x : a,
        xlog2 ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) := by
    calc
      ((∑ x : a,
          ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) *
            Real.log ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ)) /
          Real.log 2) =
        ((∑ x : a,
          xlog2 ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ)) *
          Real.log 2) / Real.log 2 := by
          rw [hmul]
      _ = ∑ x : a,
          xlog2 ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) := by
          field_simp [hlog_ne]
  rw [hdiv, vonNeumann_eq_neg_sum_stateSpectralWeight]
  ring

end State

end

end QIT
