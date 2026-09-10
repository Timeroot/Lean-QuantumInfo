/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.BinaryHypothesisTest.Basic
public import QuantumLib.QIT.Information.BinaryHypothesisTest.Classical
public import QuantumLib.QIT.Information.Entropy.Entropy
public import QuantumLib.QIT.Core
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
reserved for classical-state infrastructure.
-/

@[expose] public section

noncomputable section
universe u v
open scoped ComplexOrder MatrixOrder Kronecker NNReal ENNReal Topology
open Filter Polynomial
variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

open QIT

namespace QIT

namespace BinaryHypothesisTest

/-- Spectral probability weight of a state eigenvector. -/
def stateSpectralWeight (rho : MState a) (x : a) : ℝ≥0 :=
  ⟨rho.psd.isHermitian.eigenvalues x, rho.psd.eigenvalues_nonneg x⟩

/-- The real value of a spectral weight is the corresponding eigenvalue. -/
theorem coe_stateSpectralWeight (rho : MState a) (x : a) :
    ((stateSpectralWeight rho x : ℝ≥0) : ℝ) = rho.psd.isHermitian.eigenvalues x := rfl

/-- Spectral weights of a density state sum to one. -/
theorem stateSpectralWeight_sum (rho : MState a) :
    ∑ x : a, stateSpectralWeight rho x = 1 := by
  apply NNReal.eq
  apply Complex.ofReal_injective
  have htrace :
      (∑ x : a, ((rho.psd.isHermitian.eigenvalues x : ℝ) : ℂ)) = 1 := by
    exact rho.psd.isHermitian.trace_eq_sum_eigenvalues.symm.trans rho.tr'
  simpa [coe_stateSpectralWeight] using htrace

/-- Transition unitary from the eigenbasis of `rho` to the eigenbasis of `sigma`. -/
def nussbaumSzkolaTransitionUnitary (rho sigma : MState a) : Matrix.unitaryGroup a ℂ :=
  rho.psd.isHermitian.eigenvectorUnitary⁻¹ * sigma.psd.isHermitian.eigenvectorUnitary

/-- Nussbaum--Szkola overlap weight `|<psi_x|phi_y>|^2`. -/
def nussbaumSzkolaOverlap (rho sigma : MState a) (x y : a) : ℝ≥0 :=
  ⟨Complex.normSq ((nussbaumSzkolaTransitionUnitary rho sigma : CMatrix a) x y),
    Complex.normSq_nonneg _⟩

/-- The real value of an overlap weight is the squared transition amplitude. -/
theorem coe_nussbaumSzkolaOverlap (rho sigma : MState a) (x y : a) :
    ((nussbaumSzkolaOverlap rho sigma x y : ℝ≥0) : ℝ) =
      Complex.normSq ((nussbaumSzkolaTransitionUnitary rho sigma : CMatrix a) x y) := rfl

/-- Nussbaum--Szkola overlap weights sum to one along each `rho` eigenvector. -/
theorem nussbaumSzkolaOverlap_row_sum (rho sigma : MState a) (x : a) :
    ∑ y : a, nussbaumSzkolaOverlap rho sigma x y = 1 := by
  apply NNReal.eq
  simpa [coe_nussbaumSzkolaOverlap] using
    unitary_row_normSq_sum (nussbaumSzkolaTransitionUnitary rho sigma) x

/-- Nussbaum--Szkola overlap weights sum to one along each `sigma` eigenvector. -/
theorem nussbaumSzkolaOverlap_col_sum (rho sigma : MState a) (y : a) :
    ∑ x : a, nussbaumSzkolaOverlap rho sigma x y = 1 := by
  apply NNReal.eq
  simpa [coe_nussbaumSzkolaOverlap] using
    unitary_col_normSq_sum (nussbaumSzkolaTransitionUnitary rho sigma) y

/-- Product spectral weight of a tensor-power eigenbasis word. -/
def tensorPowerSpectralWeight (rho : MState a) :
    (n : ℕ) → TensorPower a n → ℝ≥0
  | 0, _ => 1
  | n + 1, x => stateSpectralWeight rho x.1 * tensorPowerSpectralWeight rho n x.2

/-- Product Nussbaum--Szkola overlap of two tensor-power eigenbasis words. -/
def tensorPowerNussbaumSzkolaOverlap (rho sigma : MState a) :
    (n : ℕ) → TensorPower a n → TensorPower a n → ℝ≥0
  | 0, _, _ => 1
  | n + 1, x, y =>
      nussbaumSzkolaOverlap rho sigma x.1 y.1 *
        tensorPowerNussbaumSzkolaOverlap rho sigma n x.2 y.2

/-- Tensor powers are diagonalized by the tensor product of the one-copy
eigenbasis unitary. -/
theorem tensorPower_matrix_eq_unitaryTensorPowerMatrix_diagonal
    (rho : MState a) (n : ℕ) :
    (rho.tensorPower n).m =
      (unitaryTensorPowerMatrix rho.psd.isHermitian.eigenvectorUnitary n :
          CMatrix (TensorPower a n)) *
        Matrix.diagonal
          (fun x : TensorPower a n => (((tensorPowerSpectralWeight rho n x : ℝ≥0) : ℝ) : ℂ)) *
          star
            (unitaryTensorPowerMatrix rho.psd.isHermitian.eigenvectorUnitary n :
              CMatrix (TensorPower a n)) := by
  induction n with
  | zero =>
      ext x y
      cases x
      cases y
      simp [MState.tensorPower_zero_matrix, unitaryTensorPowerMatrix,
        tensorPowerSpectralWeight]
  | succ n ih =>
      let U : Matrix.unitaryGroup a ℂ := rho.psd.isHermitian.eigenvectorUnitary
      let Un : Matrix.unitaryGroup (TensorPower a n) ℂ := unitaryTensorPowerMatrix U n
      let D : CMatrix a :=
        Matrix.diagonal fun x : a => (((stateSpectralWeight rho x : ℝ≥0) : ℝ) : ℂ)
      let Dn : CMatrix (TensorPower a n) :=
        Matrix.diagonal fun x : TensorPower a n =>
          (((tensorPowerSpectralWeight rho n x : ℝ≥0) : ℝ) : ℂ)
      have hrho :
          rho.m = (U : CMatrix a) * D * star (U : CMatrix a) := by
        simpa [U, D, coe_stateSpectralWeight, Function.comp_def, Unitary.conjStarAlgAut_apply]
          using rho.psd.isHermitian.spectral_theorem
      rw [MState.tensorPower_succ_matrix]
      change rho.m ⊗ₖ (rho.tensorPower n).m =
        ((U : CMatrix a) ⊗ₖ (Un : CMatrix (TensorPower a n))) *
          Matrix.diagonal
            (fun x : a × TensorPower a n =>
              ((((stateSpectralWeight rho x.1 *
                tensorPowerSpectralWeight rho n x.2 : ℝ≥0) : ℝ)) : ℂ)) *
            star ((U : CMatrix a) ⊗ₖ (Un : CMatrix (TensorPower a n)))
      rw [hrho, ih]
      simp [U, Un, D,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
        Matrix.diagonal_kronecker_diagonal, Matrix.mul_assoc]

/-- Product Nussbaum--Szkola overlaps are squared transition amplitudes between
the tensor-product eigenbases. -/
theorem tensorPowerNussbaumSzkolaOverlap_eq_normSq
    (rho sigma : MState a) (n : ℕ) (x y : TensorPower a n) :
    (tensorPowerNussbaumSzkolaOverlap rho sigma n x y : ℝ) =
      Complex.normSq
        ((star (unitaryTensorPowerMatrix rho.psd.isHermitian.eigenvectorUnitary n :
            CMatrix (TensorPower a n)) *
          (unitaryTensorPowerMatrix sigma.psd.isHermitian.eigenvectorUnitary n :
            CMatrix (TensorPower a n))) x y) := by
  induction n with
  | zero =>
      cases x
      cases y
      simp [unitaryTensorPowerMatrix, tensorPowerNussbaumSzkolaOverlap]
      change (1 : ℝ) = Complex.normSq (1 : ℂ)
      norm_num [Complex.normSq]
  | succ n ih =>
      rcases x with ⟨x0, xs⟩
      rcases y with ⟨y0, ys⟩
      let Urho : Matrix.unitaryGroup a ℂ := rho.psd.isHermitian.eigenvectorUnitary
      let Usigma : Matrix.unitaryGroup a ℂ := sigma.psd.isHermitian.eigenvectorUnitary
      let UrhoN : Matrix.unitaryGroup (TensorPower a n) ℂ := unitaryTensorPowerMatrix Urho n
      let UsigmaN : Matrix.unitaryGroup (TensorPower a n) ℂ := unitaryTensorPowerMatrix Usigma n
      have hentry :
          ((star ((Urho : CMatrix a) ⊗ₖ (UrhoN : CMatrix (TensorPower a n))) *
              ((Usigma : CMatrix a) ⊗ₖ (UsigmaN : CMatrix (TensorPower a n))))
              (x0, xs) (y0, ys)) =
            ((star (Urho : CMatrix a) * (Usigma : CMatrix a)) x0 y0) *
              ((star (UrhoN : CMatrix (TensorPower a n)) *
                (UsigmaN : CMatrix (TensorPower a n))) xs ys) := by
        have hstar :
            star ((Urho : CMatrix a) ⊗ₖ
                (UrhoN : CMatrix (TensorPower a n))) =
              (star (Urho : CMatrix a)) ⊗ₖ
                (star (UrhoN : CMatrix (TensorPower a n))) := by
          ext i j
          simp [Matrix.star_apply]
        rw [hstar]
        have hmul :
            ((star (Urho : CMatrix a)) ⊗ₖ
                (star (UrhoN : CMatrix (TensorPower a n)))) *
              ((Usigma : CMatrix a) ⊗ₖ
                (UsigmaN : CMatrix (TensorPower a n))) =
            (star (Urho : CMatrix a) * (Usigma : CMatrix a)) ⊗ₖ
              (star (UrhoN : CMatrix (TensorPower a n)) *
                (UsigmaN : CMatrix (TensorPower a n))) := by
          simpa using
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
            ((star ((Urho : CMatrix a) ⊗ₖ
                (UrhoN : CMatrix (TensorPower a n))) *
              ((Usigma : CMatrix a) ⊗ₖ
                (UsigmaN : CMatrix (TensorPower a n)))) (x0, xs) (y0, ys))
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
    (rho sigma : MState a) {P : CMatrix a}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    ((rho.m * (1 - P)).trace).re =
      ∑ x : a, (stateSpectralWeight rho x : ℝ) *
        ∑ y : a,
          Complex.normSq
            ((star (rho.psd.isHermitian.eigenvectorUnitary : CMatrix a) *
                (1 - P) * (sigma.psd.isHermitian.eigenvectorUnitary : CMatrix a)) x y) := by
  classical
  let Urho : Matrix.unitaryGroup a ℂ := rho.psd.isHermitian.eigenvectorUnitary
  let Usigma : Matrix.unitaryGroup a ℂ := sigma.psd.isHermitian.eigenvectorUnitary
  have htrace :=
    posSemidef_trace_mul_eq_eigenvalue_conjugate_diag_sum
      (M := rho.m) (B := 1 - P) rho.psd
  calc
    ((rho.m * (1 - P)).trace).re =
        ∑ x : a, (stateSpectralWeight rho x : ℝ) *
          ((star (Urho : CMatrix a) * (1 - P) * (Urho : CMatrix a)) x x).re := by
          simpa [Urho, coe_stateSpectralWeight] using htrace
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
              ((star (rho.psd.isHermitian.eigenvectorUnitary : CMatrix a) *
                  (1 - P) * (sigma.psd.isHermitian.eigenvectorUnitary : CMatrix a)) x y) := by
          rfl

theorem state_trace_projection_re_eq_nussbaumSzkola_source_sum
    (rho sigma : MState a) {P : CMatrix a}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    ((sigma.m * P).trace).re =
      ∑ y : a, (stateSpectralWeight sigma y : ℝ) *
        ∑ x : a,
          Complex.normSq
            ((star (rho.psd.isHermitian.eigenvectorUnitary : CMatrix a) *
                P * (sigma.psd.isHermitian.eigenvectorUnitary : CMatrix a)) x y) := by
  classical
  let Urho : Matrix.unitaryGroup a ℂ := rho.psd.isHermitian.eigenvectorUnitary
  let Usigma : Matrix.unitaryGroup a ℂ := sigma.psd.isHermitian.eigenvectorUnitary
  have htrace :=
    posSemidef_trace_mul_eq_eigenvalue_conjugate_diag_sum
      (M := sigma.m) (B := P) sigma.psd
  calc
    ((sigma.m * P).trace).re =
        ∑ y : a, (stateSpectralWeight sigma y : ℝ) *
          ((star (Usigma : CMatrix a) * P * (Usigma : CMatrix a)) y y).re := by
          simpa [Usigma, coe_stateSpectralWeight] using htrace
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
              ((star (rho.psd.isHermitian.eigenvectorUnitary : CMatrix a) *
                  P * (sigma.psd.isHermitian.eigenvectorUnitary : CMatrix a)) x y) := by
          rfl

/-- The Nussbaum--Szkola finite classical model
`p_xy = p_x |<psi_x|phi_y>|^2`,
`q_xy = q_y |<psi_x|phi_y>|^2`. -/
def nussbaumSzkolaModel (rho sigma : MState a) : ClassicalBinaryModel (a × a) where
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

/-- Splitting a common nonnegative factor out of a Chernoff-style weighted product:
`(p r)^s (q r)^{1-s} = p^s q^{1-s} r`. -/
theorem mul_rpow_mul_rpow_one_sub
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
`MState.petzRenyiCoefficient`, namely `Tr(ρ^s σ^(1-s))`
[Gour2024Resources, BookQRT.tex:15911-15949]. -/
theorem nussbaumSzkolaModel_petzChernoffCoefficient_eq
    (rho sigma : MState a) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (nussbaumSzkolaModel rho sigma).petzChernoffCoefficient s =
      rho.petzRenyiCoefficient sigma s := by
  classical
  let Urho : Matrix.unitaryGroup a ℂ := rho.psd.isHermitian.eigenvectorUnitary
  let Usigma : Matrix.unitaryGroup a ℂ := sigma.psd.isHermitian.eigenvectorUnitary
  have hrho :
      CFC.rpow rho.m s =
        (Urho : CMatrix a) *
          Matrix.diagonal (fun x => (((stateSpectralWeight rho x : ℝ) ^ s : ℝ) : ℂ)) *
            star (Urho : CMatrix a) := by
    simpa [Urho, coe_stateSpectralWeight] using
      cMatrix_rpow_eq_eigenbasis_diagonal rho.psd s
  have hsigma :
      CFC.rpow sigma.m (1 - s) =
        (Usigma : CMatrix a) *
          Matrix.diagonal
            (fun y => (((stateSpectralWeight sigma y : ℝ) ^ (1 - s) : ℝ) : ℂ)) *
            star (Usigma : CMatrix a) := by
    simpa [Usigma, coe_stateSpectralWeight] using
      cMatrix_rpow_eq_eigenbasis_diagonal sigma.psd (1 - s)
  have htrace :
      (rho.petzRenyiCoefficient sigma s : ℝ) =
        ∑ x : a, ∑ y : a,
          ((stateSpectralWeight rho x : ℝ) ^ s) *
            ((stateSpectralWeight sigma y : ℝ) ^ (1 - s)) *
              (nussbaumSzkolaOverlap rho sigma x y : ℝ) := by
    change ((CFC.rpow rho.m s * CFC.rpow sigma.m (1 - s)).trace).re = _
    rw [hrho, hsigma]
    simpa [Urho, Usigma, coe_nussbaumSzkolaOverlap, nussbaumSzkolaTransitionUnitary,
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
            mul_rpow_mul_rpow_one_sub _ _ _ hs0 hs1,
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
    (rho sigma : MState a) :
    (nussbaumSzkolaModel rho sigma).chernoffDistance =
      rho.chernoffDistance sigma := by
  unfold ClassicalBinaryModel.chernoffDistance MState.chernoffDistance
  apply iSup_congr
  intro s
  simp [ClassicalBinaryModel.chernoffExponent, MState.petzChernoffExponent,
    nussbaumSzkolaModel_petzChernoffCoefficient_eq rho sigma s.2.1 s.2.2]

/-- Product eigenbasis unitary for the product of the two marginals of a
bipartite state. -/
def productMarginalEigenvectorUnitary
    (rhoAB : MState (a × b)) : Matrix.unitaryGroup (a × b) ℂ :=
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoAB.traceRight.psd.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ :=
    rhoAB.traceLeft.psd.isHermitian.eigenvectorUnitary
  ⟨(UA : CMatrix a) ⊗ₖ (UB : CMatrix b),
    Matrix.kronecker_mem_unitary UA.2 UB.2⟩

/-- Transition from the eigenbasis of `rhoAB` to the product eigenbasis of its
marginals. -/
def productMarginalNussbaumSzkolaTransitionUnitary
    (rhoAB : MState (a × b)) : Matrix.unitaryGroup (a × b) ℂ :=
  rhoAB.psd.isHermitian.eigenvectorUnitary⁻¹ *
    productMarginalEigenvectorUnitary rhoAB

/-- Product-marginal Nussbaum--Szkola overlap
`|<rhoAB_x|rhoA_i tensor rhoB_j>|^2`. -/
def productMarginalNussbaumSzkolaOverlap
    (rhoAB : MState (a × b)) (x y : a × b) : NNReal :=
  ⟨Complex.normSq
    ((productMarginalNussbaumSzkolaTransitionUnitary rhoAB : CMatrix (a × b)) x y),
    Complex.normSq_nonneg _⟩

/-- The real value of a product-marginal overlap is the squared transition amplitude. -/
theorem coe_productMarginalNussbaumSzkolaOverlap
    (rhoAB : MState (a × b)) (x y : a × b) :
    ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) =
      Complex.normSq
        ((productMarginalNussbaumSzkolaTransitionUnitary rhoAB : CMatrix (a × b)) x y) := rfl

theorem productMarginalNussbaumSzkolaOverlap_row_sum
    (rhoAB : MState (a × b)) (x : a × b) :
    ∑ y : a × b, productMarginalNussbaumSzkolaOverlap rhoAB x y = 1 := by
  apply NNReal.eq
  simpa [coe_productMarginalNussbaumSzkolaOverlap] using
    unitary_row_normSq_sum
      (productMarginalNussbaumSzkolaTransitionUnitary rhoAB) x

theorem productMarginalNussbaumSzkolaOverlap_col_sum
    (rhoAB : MState (a × b)) (y : a × b) :
    ∑ x : a × b, productMarginalNussbaumSzkolaOverlap rhoAB x y = 1 := by
  apply NNReal.eq
  simpa [coe_productMarginalNussbaumSzkolaOverlap] using
    unitary_col_normSq_sum
      (productMarginalNussbaumSzkolaTransitionUnitary rhoAB) y

/-- Spectral weights of a product of the two marginals, expressed in the
explicit product marginal eigenbasis. -/
def productMarginalSpectralWeight
    (rhoAB : MState (a × b)) (y : a × b) : NNReal :=
  stateSpectralWeight rhoAB.traceRight y.1 *
    stateSpectralWeight rhoAB.traceLeft y.2

theorem productMarginalSpectralWeight_sum
    (rhoAB : MState (a × b)) :
    ∑ y : a × b, productMarginalSpectralWeight rhoAB y = 1 := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : a, ∑ y : b,
        stateSpectralWeight rhoAB.traceRight x *
          stateSpectralWeight rhoAB.traceLeft y)
        =
      ∑ x : a, stateSpectralWeight rhoAB.traceRight x *
        (∑ y : b, stateSpectralWeight rhoAB.traceLeft y) := by
        simp [Finset.mul_sum]
    _ = ∑ x : a, stateSpectralWeight rhoAB.traceRight x := by
        simp [stateSpectralWeight_sum]
    _ = 1 := stateSpectralWeight_sum rhoAB.traceRight

/-- The product of the two marginals is diagonalized by the explicit tensor
product of the marginal eigenbases. -/
theorem productMarginal_matrix_eq_productEigenbasis_diagonal
    (rhoAB : MState (a × b)) :
    (rhoAB.traceRight.prod rhoAB.traceLeft).m =
      (productMarginalEigenvectorUnitary rhoAB : CMatrix (a × b)) *
        Matrix.diagonal
          (fun y : a × b =>
            (((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) : ℂ)) *
        star (productMarginalEigenvectorUnitary rhoAB : CMatrix (a × b)) := by
  classical
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoAB.traceRight.psd.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ :=
    rhoAB.traceLeft.psd.isHermitian.eigenvectorUnitary
  have hA :
      rhoAB.traceRight.m =
        (UA : CMatrix a) *
          Matrix.diagonal
            (fun x : a => (((stateSpectralWeight rhoAB.traceRight x : NNReal) : ℝ) : ℂ)) *
          star (UA : CMatrix a) := by
    simpa [UA, coe_stateSpectralWeight, Function.comp_def,
      Unitary.conjStarAlgAut_apply]
      using rhoAB.traceRight.psd.isHermitian.spectral_theorem
  have hB :
      rhoAB.traceLeft.m =
        (UB : CMatrix b) *
          Matrix.diagonal
            (fun y : b => (((stateSpectralWeight rhoAB.traceLeft y : NNReal) : ℝ) : ℂ)) *
          star (UB : CMatrix b) := by
    simpa [UB, coe_stateSpectralWeight, Function.comp_def,
      Unitary.conjStarAlgAut_apply]
      using rhoAB.traceLeft.psd.isHermitian.spectral_theorem
  rw [MState.prod_m]
  change rhoAB.traceRight.m ⊗ₖ rhoAB.traceLeft.m =
    (productMarginalEigenvectorUnitary rhoAB : CMatrix (a × b)) *
      Matrix.diagonal
        (fun y : a × b =>
          (((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) : ℂ)) *
      star (productMarginalEigenvectorUnitary rhoAB : CMatrix (a × b))
  rw [hA, hB]
  simp [productMarginalEigenvectorUnitary, productMarginalSpectralWeight, UA, UB,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal,
    Matrix.mul_assoc]

/-- Product-marginal Nussbaum--Szkola model.  Its second spectral basis is the
explicit tensor-product eigenbasis of `rhoAB.traceRight.prod rhoAB.traceLeft`,
so the endpoint KL can be identified directly with entropy-form mutual
information. -/
def productMarginalNussbaumSzkolaModel
    (rhoAB : MState (a × b)) :
    ClassicalBinaryModel ((a × b) × (a × b)) where
  p xy :=
    stateSpectralWeight rhoAB xy.1 *
      productMarginalNussbaumSzkolaOverlap rhoAB xy.1 xy.2
  q xy :=
    productMarginalSpectralWeight rhoAB xy.2 *
      productMarginalNussbaumSzkolaOverlap rhoAB xy.1 xy.2
  p_sum := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ x : a × b, ∑ y : a × b,
          stateSpectralWeight rhoAB x *
            productMarginalNussbaumSzkolaOverlap rhoAB x y)
          =
        ∑ x : a × b, stateSpectralWeight rhoAB x *
          (∑ y : a × b, productMarginalNussbaumSzkolaOverlap rhoAB x y) := by
          simp [Finset.mul_sum]
      _ = ∑ x : a × b, stateSpectralWeight rhoAB x := by
          simp [productMarginalNussbaumSzkolaOverlap_row_sum]
      _ = 1 := stateSpectralWeight_sum rhoAB
  q_sum := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ x : a × b, ∑ y : a × b,
          productMarginalSpectralWeight rhoAB y *
            productMarginalNussbaumSzkolaOverlap rhoAB x y)
          =
        ∑ y : a × b, ∑ x : a × b,
          productMarginalSpectralWeight rhoAB y *
            productMarginalNussbaumSzkolaOverlap rhoAB x y := by
          rw [Finset.sum_comm]
      _ =
        ∑ y : a × b, productMarginalSpectralWeight rhoAB y *
          (∑ x : a × b, productMarginalNussbaumSzkolaOverlap rhoAB x y) := by
          simp [Finset.mul_sum]
      _ = ∑ y : a × b, productMarginalSpectralWeight rhoAB y := by
          simp [productMarginalNussbaumSzkolaOverlap_col_sum]
      _ = 1 := productMarginalSpectralWeight_sum rhoAB

/-- The product-marginal Nussbaum--Szkola `p` distribution is supported by
its `q` distribution. -/
theorem productMarginalNussbaumSzkolaModel_p_supportedBy_q
    (rhoAB : MState (a × b)) :
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
  · let Urho : Matrix.unitaryGroup (a × b) ℂ :=
      rhoAB.psd.isHermitian.eigenvectorUnitary
    let Uprod : Matrix.unitaryGroup (a × b) ℂ :=
      productMarginalEigenvectorUnitary rhoAB
    let sigma : MState (a × b) := rhoAB.traceRight.prod rhoAB.traceLeft
    let Dprod : CMatrix (a × b) :=
      Matrix.diagonal
        (fun i : a × b =>
          (((productMarginalSpectralWeight rhoAB i : NNReal) : ℝ) : ℂ))
    have hsigma_spec :
        sigma.m = (Uprod : CMatrix (a × b)) * Dprod *
          star (Uprod : CMatrix (a × b)) := by
      simpa [sigma, Uprod, Dprod] using
        productMarginal_matrix_eq_productEigenbasis_diagonal rhoAB
    have hsigma_mul :
        sigma.m * (Uprod : CMatrix (a × b)) =
          (Uprod : CMatrix (a × b)) * Dprod := by
      rw [hsigma_spec]
      calc
        ((Uprod : CMatrix (a × b)) * Dprod *
            star (Uprod : CMatrix (a × b))) *
            (Uprod : CMatrix (a × b))
            =
          (Uprod : CMatrix (a × b)) * Dprod *
            (star (Uprod : CMatrix (a × b)) *
              (Uprod : CMatrix (a × b))) := by
            noncomm_ring
        _ = (Uprod : CMatrix (a × b)) * Dprod := by
            rw [Unitary.coe_star_mul_self]
            simp
    have hsigma_col :
        ∀ k, (sigma.m * (Uprod : CMatrix (a × b))) k y = 0 := by
      intro k
      rw [hsigma_mul]
      simp [Dprod, Matrix.mul_apply, Matrix.diagonal, hweight_zero]
    let v : a × b → ℂ := fun i => (Uprod : CMatrix (a × b)) i y
    have hsigma_v : sigma.m.mulVec v = 0 := by
      ext k
      simpa [v, Matrix.mulVec, dotProduct, Matrix.mul_apply] using hsigma_col k
    have hrho_v : rhoAB.m.mulVec v = 0 :=
      rhoAB.matrix_supports_prod_marginals v (by simpa [sigma] using hsigma_v)
    have hrho_col :
        ∀ k, (rhoAB.m * (Uprod : CMatrix (a × b))) k y = 0 := by
      intro k
      have hk := congrFun hrho_v k
      simpa [v, Matrix.mulVec, dotProduct, Matrix.mul_apply] using hk
    have hleft :
        (star (Urho : CMatrix (a × b)) * rhoAB.m *
          (Uprod : CMatrix (a × b))) x y = 0 := by
      rw [Matrix.mul_assoc]
      simp [Matrix.mul_apply, hrho_col]
    let T : CMatrix (a × b) :=
      star (Urho : CMatrix (a × b)) * (Uprod : CMatrix (a × b))
    let Drho : CMatrix (a × b) :=
      Matrix.diagonal
        (fun i : a × b =>
          (((stateSpectralWeight rhoAB i : NNReal) : ℝ) : ℂ))
    have hrho_diag :
        rhoAB.m = (Urho : CMatrix (a × b)) * Drho *
          star (Urho : CMatrix (a × b)) := by
      simpa [Urho, Drho, Function.comp_def, coe_stateSpectralWeight,
        Unitary.conjStarAlgAut_apply]
        using rhoAB.psd.isHermitian.spectral_theorem
    have hleft_diag :
        (star (Urho : CMatrix (a × b)) * rhoAB.m *
          (Uprod : CMatrix (a × b))) x y =
          (((stateSpectralWeight rhoAB x : NNReal) : ℝ) : ℂ) * T x y := by
      have hmatrix :
          star (Urho : CMatrix (a × b)) * rhoAB.m *
            (Uprod : CMatrix (a × b)) =
              Drho * T := by
        rw [hrho_diag]
        dsimp [Drho, T]
        calc
          star (Urho : CMatrix (a × b)) *
              ((Urho : CMatrix (a × b)) * Drho *
                star (Urho : CMatrix (a × b))) *
                (Uprod : CMatrix (a × b))
              =
                (star (Urho : CMatrix (a × b)) *
                  (Urho : CMatrix (a × b))) *
                  (Drho * (star (Urho : CMatrix (a × b)) *
                    (Uprod : CMatrix (a × b)))) := by
                noncomm_ring
          _ = Drho *
                (star (Urho : CMatrix (a × b)) *
                  (Uprod : CMatrix (a × b)) ) := by
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
                CMatrix (a × b)) x y) = T x y := by
            simp [productMarginalNussbaumSzkolaTransitionUnitary, T, Urho, Uprod,
              Matrix.star_eq_conjTranspose]
          apply NNReal.eq
          change Complex.normSq
              ((productMarginalNussbaumSzkolaTransitionUnitary rhoAB :
                CMatrix (a × b)) x y) = 0
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
    (rhoAB : MState (a × b)) (y : a × b) :
    ∑ x : a × b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) =
      ((star (productMarginalEigenvectorUnitary rhoAB : CMatrix (a × b)) *
        rhoAB.m * (productMarginalEigenvectorUnitary rhoAB : CMatrix (a × b)))
          y y).re := by
  classical
  let Urho : Matrix.unitaryGroup (a × b) ℂ :=
    rhoAB.psd.isHermitian.eigenvectorUnitary
  let Uprod : Matrix.unitaryGroup (a × b) ℂ :=
    productMarginalEigenvectorUnitary rhoAB
  let D : CMatrix (a × b) :=
    Matrix.diagonal
      (fun x : a × b => (((stateSpectralWeight rhoAB x : NNReal) : ℝ) : ℂ))
  let T : CMatrix (a × b) :=
    star (Urho : CMatrix (a × b)) * (Uprod : CMatrix (a × b))
  have hrho :
      rhoAB.m = (Urho : CMatrix (a × b)) * D * star (Urho : CMatrix (a × b)) := by
    simpa [Urho, D, coe_stateSpectralWeight, Function.comp_def,
      Unitary.conjStarAlgAut_apply]
      using rhoAB.psd.isHermitian.spectral_theorem
  have hmatrix :
      star (Uprod : CMatrix (a × b)) * rhoAB.m *
          (Uprod : CMatrix (a × b)) =
        star T * D * T := by
    rw [hrho]
    dsimp [T]
    calc
      star (Uprod : CMatrix (a × b)) *
          ((Urho : CMatrix (a × b)) * D * star (Urho : CMatrix (a × b))) *
          (Uprod : CMatrix (a × b))
          =
        (star (Uprod : CMatrix (a × b)) * (Urho : CMatrix (a × b))) *
          D * (star (Urho : CMatrix (a × b)) * (Uprod : CMatrix (a × b))) := by
            noncomm_ring
      _ = star (star (Urho : CMatrix (a × b)) * (Uprod : CMatrix (a × b))) *
          D * (star (Urho : CMatrix (a × b)) * (Uprod : CMatrix (a × b))) := by
            simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have hentry := congrFun (congrFun hmatrix y) y
  have hre := congrArg Complex.re hentry
  have hdiag :
      ((star T * D * T) y y).re =
        ∑ x : a × b,
          ((stateSpectralWeight rhoAB x : NNReal) : ℝ) * Complex.normSq (T x y) := by
    simp [D, Matrix.mul_apply, Matrix.diagonal,
      Matrix.star_eq_conjTranspose, Complex.normSq_apply,
      mul_left_comm, mul_comm]
  change
    ∑ x : a × b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) =
      ((star (Uprod : CMatrix (a × b)) * rhoAB.m *
        (Uprod : CMatrix (a × b))) y y).re
  rw [hre]
  rw [hdiag]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  have hoverlap :
      ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) =
        Complex.normSq (T x y) := by
    change Complex.normSq
        ((productMarginalNussbaumSzkolaTransitionUnitary rhoAB : CMatrix (a × b)) x y) =
      Complex.normSq (T x y)
    congr 1
  rw [hoverlap]

/-- The first marginal of the product-marginal Nussbaum--Szkola `p`
distribution is the spectral distribution of `rhoAB.traceRight`. -/
theorem productMarginalNussbaumSzkolaOverlap_weighted_fst_sum
    (rhoAB : MState (a × b)) (i : a) :
    ∑ x : a × b, ∑ j : b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x (i, j) : NNReal) : ℝ) =
      ((stateSpectralWeight rhoAB.traceRight i : NNReal) : ℝ) := by
  classical
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoAB.traceRight.psd.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ :=
    rhoAB.traceLeft.psd.isHermitian.eigenvectorUnitary
  let Uprod : Matrix.unitaryGroup (a × b) ℂ :=
    productMarginalEigenvectorUnitary rhoAB
  let M : CMatrix (a × b) :=
    star (Uprod : CMatrix (a × b)) * rhoAB.m * (Uprod : CMatrix (a × b))
  have hdiag_sum :
      ∑ j : b, (M (i, j) (i, j)).re =
        ((stateSpectralWeight rhoAB.traceRight i : NNReal) : ℝ) := by
    have hpt :=
      traceRight_local_unitary_conj (a := a) (b := b)
        rhoAB.m UA UB
    have hUprod :
        (Uprod : CMatrix (a × b)) =
          (UA : CMatrix a) ⊗ₖ (UB : CMatrix b) := by
      rfl
    have hptM :
        Matrix.traceRight M =
          star (UA : CMatrix a) * rhoAB.traceRight.m * (UA : CMatrix a) := by
      simpa [M, Uprod, hUprod, MState.traceRight_m] using hpt
    have hdiag :
        star (UA : CMatrix a) * rhoAB.traceRight.m * (UA : CMatrix a) =
          Matrix.diagonal
            (fun k : a => (((stateSpectralWeight rhoAB.traceRight k : NNReal) : ℝ) : ℂ)) := by
      have hspec := rhoAB.traceRight.psd.isHermitian.spectral_theorem
      have hρA :
          rhoAB.traceRight.m =
            (UA : CMatrix a) *
              Matrix.diagonal
                (fun k : a =>
                  (((stateSpectralWeight rhoAB.traceRight k : NNReal) : ℝ) : ℂ)) *
              star (UA : CMatrix a) := by
        simpa [UA, coe_stateSpectralWeight, Function.comp_def,
          Unitary.conjStarAlgAut_apply] using hspec
      calc
        star (UA : CMatrix a) * rhoAB.traceRight.m * (UA : CMatrix a)
            = star (UA : CMatrix a) *
                ((UA : CMatrix a) *
                  Matrix.diagonal
                    (fun k : a =>
                      (((stateSpectralWeight rhoAB.traceRight k : NNReal) : ℝ) : ℂ)) *
                  star (UA : CMatrix a)) *
                (UA : CMatrix a) := by
                  rw [hρA]
        _ = (star (UA : CMatrix a) * (UA : CMatrix a)) *
              Matrix.diagonal
                (fun k : a =>
                  (((stateSpectralWeight rhoAB.traceRight k : NNReal) : ℝ) : ℂ)) *
              (star (UA : CMatrix a) * (UA : CMatrix a)) := by
                noncomm_ring
        _ = Matrix.diagonal
              (fun k : a =>
                (((stateSpectralWeight rhoAB.traceRight k : NNReal) : ℝ) : ℂ)) := by
              rw [Unitary.coe_star_mul_self]
              simp
    have hentry :
        (Matrix.traceRight M) i i =
          (Matrix.diagonal
            (fun k : a => (((stateSpectralWeight rhoAB.traceRight k : NNReal) : ℝ) : ℂ))
              : CMatrix a) i i := by
      rw [hptM, hdiag]
    have hre := congrArg Complex.re hentry
    simpa [Matrix.traceRight, Matrix.diagonal, M] using hre
  calc
    ∑ x : a × b, ∑ j : b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x (i, j) : NNReal) : ℝ)
        =
      ∑ j : b, ∑ x : a × b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x (i, j) : NNReal) : ℝ) := by
        rw [Finset.sum_comm]
    _ = ∑ j : b, (M (i, j) (i, j)).re := by
        refine Finset.sum_congr rfl ?_
        intro j _hj
        exact productMarginalNussbaumSzkolaOverlap_weighted_col_sum_eq_productBasis_diag
          rhoAB (i, j)
    _ = ((stateSpectralWeight rhoAB.traceRight i : NNReal) : ℝ) := hdiag_sum

/-- The second marginal of the product-marginal Nussbaum--Szkola `p`
distribution is the spectral distribution of `rhoAB.traceLeft`. -/
theorem productMarginalNussbaumSzkolaOverlap_weighted_snd_sum
    (rhoAB : MState (a × b)) (j : b) :
    ∑ x : a × b, ∑ i : a,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x (i, j) : NNReal) : ℝ) =
      ((stateSpectralWeight rhoAB.traceLeft j : NNReal) : ℝ) := by
  classical
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoAB.traceRight.psd.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ :=
    rhoAB.traceLeft.psd.isHermitian.eigenvectorUnitary
  let Uprod : Matrix.unitaryGroup (a × b) ℂ :=
    productMarginalEigenvectorUnitary rhoAB
  let M : CMatrix (a × b) :=
    star (Uprod : CMatrix (a × b)) * rhoAB.m * (Uprod : CMatrix (a × b))
  have hdiag_sum :
      ∑ i : a, (M (i, j) (i, j)).re =
        ((stateSpectralWeight rhoAB.traceLeft j : NNReal) : ℝ) := by
    have hpt :=
      traceLeft_local_unitary_conj (a := a) (b := b)
        rhoAB.m UA UB
    have hUprod :
        (Uprod : CMatrix (a × b)) =
          (UA : CMatrix a) ⊗ₖ (UB : CMatrix b) := by
      rfl
    have hptM :
        Matrix.traceLeft M =
          star (UB : CMatrix b) * rhoAB.traceLeft.m * (UB : CMatrix b) := by
      simpa [M, Uprod, hUprod, MState.traceLeft_m] using hpt
    have hdiag :
        star (UB : CMatrix b) * rhoAB.traceLeft.m * (UB : CMatrix b) =
          Matrix.diagonal
            (fun k : b => (((stateSpectralWeight rhoAB.traceLeft k : NNReal) : ℝ) : ℂ)) := by
      have hspec := rhoAB.traceLeft.psd.isHermitian.spectral_theorem
      have hρB :
          rhoAB.traceLeft.m =
            (UB : CMatrix b) *
              Matrix.diagonal
                (fun k : b =>
                  (((stateSpectralWeight rhoAB.traceLeft k : NNReal) : ℝ) : ℂ)) *
              star (UB : CMatrix b) := by
        simpa [UB, coe_stateSpectralWeight, Function.comp_def,
          Unitary.conjStarAlgAut_apply] using hspec
      calc
        star (UB : CMatrix b) * rhoAB.traceLeft.m * (UB : CMatrix b)
            = star (UB : CMatrix b) *
                ((UB : CMatrix b) *
                  Matrix.diagonal
                    (fun k : b =>
                      (((stateSpectralWeight rhoAB.traceLeft k : NNReal) : ℝ) : ℂ)) *
                  star (UB : CMatrix b)) *
                (UB : CMatrix b) := by
                  rw [hρB]
        _ = (star (UB : CMatrix b) * (UB : CMatrix b)) *
              Matrix.diagonal
                (fun k : b =>
                  (((stateSpectralWeight rhoAB.traceLeft k : NNReal) : ℝ) : ℂ)) *
              (star (UB : CMatrix b) * (UB : CMatrix b)) := by
                noncomm_ring
        _ = Matrix.diagonal
              (fun k : b =>
                (((stateSpectralWeight rhoAB.traceLeft k : NNReal) : ℝ) : ℂ)) := by
              rw [Unitary.coe_star_mul_self]
              simp
    have hentry :
        (Matrix.traceLeft M) j j =
          (Matrix.diagonal
            (fun k : b => (((stateSpectralWeight rhoAB.traceLeft k : NNReal) : ℝ) : ℂ))
              : CMatrix b) j j := by
      rw [hptM, hdiag]
    have hre := congrArg Complex.re hentry
    simpa [Matrix.traceLeft, Matrix.diagonal, M] using hre
  calc
    ∑ x : a × b, ∑ i : a,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x (i, j) : NNReal) : ℝ)
        =
      ∑ i : a, ∑ x : a × b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x (i, j) : NNReal) : ℝ) := by
        rw [Finset.sum_comm]
    _ = ∑ i : a, (M (i, j) (i, j)).re := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        exact productMarginalNussbaumSzkolaOverlap_weighted_col_sum_eq_productBasis_diag
          rhoAB (i, j)
    _ = ((stateSpectralWeight rhoAB.traceLeft j : NNReal) : ℝ) := hdiag_sum

/-- The log of the product-marginal spectral weight splits after multiplying by
the joint diagonal weight.  If one marginal eigenvalue is zero, the support
bridge makes the joint diagonal weight zero as well. -/
theorem productMarginalNussbaumSzkolaModel_weighted_log_product
    (rhoAB : MState (a × b)) (y : a × b) :
    (∑ x : a × b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ)) *
        Real.log ((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) =
      (∑ x : a × b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ)) *
        (Real.log ((stateSpectralWeight rhoAB.traceRight y.1 : NNReal) : ℝ) +
          Real.log ((stateSpectralWeight rhoAB.traceLeft y.2 : NNReal) : ℝ)) := by
  classical
  by_cases hmu : productMarginalSpectralWeight rhoAB y = 0
  · have hcoeff_zero :
        ∑ x : a × b,
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
  · have hA_ne : stateSpectralWeight rhoAB.traceRight y.1 ≠ 0 :=
      (mul_ne_zero_iff.mp (by simpa [productMarginalSpectralWeight] using hmu)).1
    have hB_ne : stateSpectralWeight rhoAB.traceLeft y.2 ≠ 0 :=
      (mul_ne_zero_iff.mp (by simpa [productMarginalSpectralWeight] using hmu)).2
    have hA_pos : 0 < ((stateSpectralWeight rhoAB.traceRight y.1 : NNReal) : ℝ) := by
      have hnn : (0 : NNReal) < stateSpectralWeight rhoAB.traceRight y.1 :=
        lt_of_le_of_ne (show (0 : NNReal) ≤ stateSpectralWeight rhoAB.traceRight y.1 from zero_le)
          (Ne.symm hA_ne)
      exact_mod_cast hnn
    have hB_pos : 0 < ((stateSpectralWeight rhoAB.traceLeft y.2 : NNReal) : ℝ) := by
      have hnn : (0 : NNReal) < stateSpectralWeight rhoAB.traceLeft y.2 :=
        lt_of_le_of_ne (show (0 : NNReal) ≤ stateSpectralWeight rhoAB.traceLeft y.2 from zero_le)
          (Ne.symm hB_ne)
      exact_mod_cast hnn
    rw [productMarginalSpectralWeight, NNReal.coe_mul]
    rw [Real.log_mul hA_pos.ne' hB_pos.ne']

end BinaryHypothesisTest

end QIT

namespace MState

/-- Entropy as the spectral-weight sum used by the Nussbaum--Szkola models. -/
theorem vonNeumann_eq_neg_sum_stateSpectralWeight (ρ : MState a) :
    ρ.vonNeumann =
      -∑ x : a, xlog2 ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) := by
  unfold MState.vonNeumann BinaryHypothesisTest.stateSpectralWeight
  congr 1

/-- Spectral log sums are the negative von Neumann entropy after dividing by
`log 2`. -/
theorem spectralWeight_mul_log_div_log_two_eq_neg_vonNeumann
    (ρ : MState a) :
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
    exact xlog2_mul_log2_self (NNReal.coe_nonneg _)
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

end MState
