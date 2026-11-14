/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Nonlocality.Bell
public import QIT.States.PosSqrt
public import QIT.Nonlocality.TwoQubit
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

/-!
# CHSH observable models

This module introduces a binary observable surface for Tsirelson-style CHSH
arguments.  It keeps the existing `CHSHBehavior` and `IsQuantum` APIs intact:
the bridge back to behavior-level probabilities is a separate construction.

The CHSH sign convention is the one already used by `QIT.Bell.CHSH`:
`false = +1` and `true = -1` [Brunner2013BellNonlocality,
ReviewALL.tex:142-152].  The observable setup matches the CHSH Bell-operator
discussion [Brunner2013BellNonlocality, ReviewALL.tex:508-517].
-/

@[expose] public section

open scoped ComplexOrder Kronecker MatrixOrder

namespace QIT
namespace Bell
namespace CHSH

universe u v

noncomputable section

/--
A finite-dimensional binary-observable CHSH model: a bipartite state and two
Hermitian square-one observables for each party.
-/
structure ObservableModel (HA : Type u) (HB : Type v)
    [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB] where
  /-- Shared bipartite state. -/
  rho : State (HA × HB)
  /-- Alice's two `±1` observables. -/
  alice : Fin 2 → CMatrix HA
  /-- Bob's two `±1` observables. -/
  bob : Fin 2 → CMatrix HB
  /-- Alice's observables are Hermitian. -/
  alice_isHermitian : ∀ x, (alice x).IsHermitian
  /-- Bob's observables are Hermitian. -/
  bob_isHermitian : ∀ y, (bob y).IsHermitian
  /-- Alice's observables square to identity. -/
  alice_square : ∀ x, alice x * alice x = 1
  /-- Bob's observables square to identity. -/
  bob_square : ∀ y, bob y * bob y = 1

namespace ObservableModel

variable {HA : Type u} {HB : Type v}
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

/-- Tensor-product observable `A_x ⊗ B_y` for one CHSH setting pair. -/
def jointObservable (M : ObservableModel HA HB) (x y : Fin 2) : CMatrix (HA × HB) :=
  Matrix.kronecker (M.alice x) (M.bob y)

/-- Observable-level correlator `E_xy = Tr(ρ (A_x ⊗ B_y))`, as a real number. -/
def correlator (M : ObservableModel HA HB) (x y : Fin 2) : ℝ :=
  ((M.rho.matrix * M.jointObservable x y).trace).re

/-- Observable-level CHSH value `E₀₀ + E₀₁ + E₁₀ - E₁₁`. -/
def value (M : ObservableModel HA HB) : ℝ :=
  M.correlator 0 0 + M.correlator 0 1 + M.correlator 1 0 - M.correlator 1 1

/-- The observable value unfolds to the same four-correlator CHSH formula as `CHSH.value`. -/
theorem value_eq_correlators (M : ObservableModel HA HB) :
    M.value =
      M.correlator 0 0 + M.correlator 0 1 + M.correlator 1 0 - M.correlator 1 1 :=
  rfl

/-- Alice's observable lifted to the bipartite product space. -/
def aliceLift (M : ObservableModel HA HB) (x : Fin 2) : CMatrix (HA × HB) :=
  Matrix.kronecker (M.alice x) (1 : CMatrix HB)

/-- Bob's observable lifted to the bipartite product space. -/
def bobLift (M : ObservableModel HA HB) (y : Fin 2) : CMatrix (HA × HB) :=
  Matrix.kronecker (1 : CMatrix HA) (M.bob y)

/-- The CHSH Bell operator `A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁`. -/
def chshOperator (M : ObservableModel HA HB) : CMatrix (HA × HB) :=
  M.aliceLift 0 * M.bobLift 0 + M.aliceLift 0 * M.bobLift 1 +
    M.aliceLift 1 * M.bobLift 0 - M.aliceLift 1 * M.bobLift 1

/-- The SOS scalar `1 / sqrt 2`, represented as `sqrt 2 / 2` for arithmetic. -/
def invSqrtTwo : ℝ :=
  Real.sqrt 2 / 2

/-- First Tsirelson sum-of-squares term. -/
def sosTerm0 (M : ObservableModel HA HB) : CMatrix (HA × HB) :=
  M.aliceLift 0 - invSqrtTwo • (M.bobLift 0 + M.bobLift 1)

/-- Second Tsirelson sum-of-squares term. -/
def sosTerm1 (M : ObservableModel HA HB) : CMatrix (HA × HB) :=
  M.aliceLift 1 - invSqrtTwo • (M.bobLift 0 - M.bobLift 1)

/-- Slack matrix `2 sqrt 2 · I - S`, where `S` is the CHSH operator. -/
def tsirelsonSlack (M : ObservableModel HA HB) : CMatrix (HA × HB) :=
  ((2 * Real.sqrt 2 : ℝ) : ℂ) • 1 - M.chshOperator

theorem invSqrtTwo_sq : invSqrtTwo ^ 2 = (1 / 2 : ℝ) := by
  have hsq : (Real.sqrt 2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  calc
    invSqrtTwo ^ 2 = ((Real.sqrt 2 : ℝ) / 2) ^ 2 := by rfl
    _ = (Real.sqrt 2 : ℝ) ^ 2 / 4 := by ring
    _ = 2 / 4 := by rw [hsq]
    _ = (1 / 2 : ℝ) := by norm_num

theorem invSqrtTwo_coeff :
    invSqrtTwo * 2 + invSqrtTwo ^ 3 * 4 = (Real.sqrt 2 : ℝ) * 2 := by
  have hsq : (Real.sqrt 2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  calc
    invSqrtTwo * 2 + invSqrtTwo ^ 3 * 4
        = Real.sqrt 2 + (Real.sqrt 2 : ℝ) ^ 3 / 2 := by
      simp [invSqrtTwo]
      ring
    _ = Real.sqrt 2 + Real.sqrt 2 * (Real.sqrt 2 : ℝ) ^ 2 / 2 := by ring
    _ = Real.sqrt 2 + Real.sqrt 2 * 2 / 2 := by rw [hsq]
    _ = (Real.sqrt 2 : ℝ) * 2 := by ring

theorem invSqrtTwo_nonneg : 0 ≤ invSqrtTwo := by
  unfold invSqrtTwo
  positivity

theorem aliceLift_mul_self (M : ObservableModel HA HB) (x : Fin 2) :
    M.aliceLift x * M.aliceLift x = 1 := by
  change (M.alice x ⊗ₖ (1 : CMatrix HB)) * (M.alice x ⊗ₖ (1 : CMatrix HB)) = 1
  rw [← Matrix.mul_kronecker_mul, M.alice_square x, Matrix.one_mul,
    Matrix.one_kronecker_one]

theorem bobLift_mul_self (M : ObservableModel HA HB) (y : Fin 2) :
    M.bobLift y * M.bobLift y = 1 := by
  change ((1 : CMatrix HA) ⊗ₖ M.bob y) * ((1 : CMatrix HA) ⊗ₖ M.bob y) = 1
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, M.bob_square y,
    Matrix.one_kronecker_one]

theorem aliceLift_mul_bobLift (M : ObservableModel HA HB) (x y : Fin 2) :
    M.aliceLift x * M.bobLift y = M.jointObservable x y := by
  change (M.alice x ⊗ₖ (1 : CMatrix HB)) * ((1 : CMatrix HA) ⊗ₖ M.bob y) =
        M.alice x ⊗ₖ M.bob y
  rw [← Matrix.mul_kronecker_mul]
  simp

theorem bobLift_mul_aliceLift (M : ObservableModel HA HB) (x y : Fin 2) :
    M.bobLift y * M.aliceLift x = M.jointObservable x y := by
  change ((1 : CMatrix HA) ⊗ₖ M.bob y) * (M.alice x ⊗ₖ (1 : CMatrix HB)) =
        M.alice x ⊗ₖ M.bob y
  rw [← Matrix.mul_kronecker_mul]
  simp

theorem aliceLift_comm_bobLift (M : ObservableModel HA HB) (x y : Fin 2) :
    M.aliceLift x * M.bobLift y = M.bobLift y * M.aliceLift x := by
  rw [aliceLift_mul_bobLift, bobLift_mul_aliceLift]

theorem aliceLift_isHermitian (M : ObservableModel HA HB) (x : Fin 2) :
    (M.aliceLift x).IsHermitian := by
  change Matrix.conjTranspose (M.alice x ⊗ₖ (1 : CMatrix HB)) =
    M.alice x ⊗ₖ (1 : CMatrix HB)
  rw [Matrix.conjTranspose_kronecker, M.alice_isHermitian x]
  simp

theorem bobLift_isHermitian (M : ObservableModel HA HB) (y : Fin 2) :
    (M.bobLift y).IsHermitian := by
  change Matrix.conjTranspose ((1 : CMatrix HA) ⊗ₖ M.bob y) =
    (1 : CMatrix HA) ⊗ₖ M.bob y
  rw [Matrix.conjTranspose_kronecker, M.bob_isHermitian y]
  simp

theorem sosTerm0_isHermitian (M : ObservableModel HA HB) :
    M.sosTerm0.IsHermitian := by
  rw [Matrix.IsHermitian, sosTerm0, Matrix.conjTranspose_sub]
  rw [M.aliceLift_isHermitian 0, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    M.bobLift_isHermitian 0,
    M.bobLift_isHermitian 1]
  simp

theorem sosTerm1_isHermitian (M : ObservableModel HA HB) :
    M.sosTerm1.IsHermitian := by
  rw [Matrix.IsHermitian, sosTerm1, Matrix.conjTranspose_sub]
  rw [M.aliceLift_isHermitian 1, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    M.bobLift_isHermitian 0,
    M.bobLift_isHermitian 1]
  simp

theorem value_eq_trace_chshOperator (M : ObservableModel HA HB) :
    M.value = ((M.rho.matrix * M.chshOperator).trace).re := by
  simp [value, correlator, chshOperator, aliceLift_mul_bobLift, Matrix.mul_add,
    Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]

theorem tsirelsonSlack_eq_sos (M : ObservableModel HA HB) :
    M.tsirelsonSlack =
      invSqrtTwo • (M.sosTerm0 * M.sosTerm0 + M.sosTerm1 * M.sosTerm1) := by
  let A0 := M.aliceLift 0
  let A1 := M.aliceLift 1
  let B0 := M.bobLift 0
  let B1 := M.bobLift 1
  have hA0sq : A0 * A0 = 1 := M.aliceLift_mul_self 0
  have hA1sq : A1 * A1 = 1 := M.aliceLift_mul_self 1
  have hB0sq : B0 * B0 = 1 := M.bobLift_mul_self 0
  have hB1sq : B1 * B1 = 1 := M.bobLift_mul_self 1
  have hA0B0 : A0 * B0 = B0 * A0 := M.aliceLift_comm_bobLift 0 0
  have hA0B1 : A0 * B1 = B1 * A0 := M.aliceLift_comm_bobLift 0 1
  have hA1B0 : A1 * B0 = B0 * A1 := M.aliceLift_comm_bobLift 1 0
  have hA1B1 : A1 * B1 = B1 * A1 := M.aliceLift_comm_bobLift 1 1
  change ((2 * Real.sqrt 2 : ℝ) : ℂ) • (1 : CMatrix (HA × HB)) -
      (A0 * B0 + A0 * B1 + A1 * B0 - A1 * B1) =
    invSqrtTwo • ((A0 - invSqrtTwo • (B0 + B1)) *
        (A0 - invSqrtTwo • (B0 + B1)) +
      (A1 - invSqrtTwo • (B0 - B1)) *
        (A1 - invSqrtTwo • (B0 - B1)))
  simp only [smul_add, smul_sub]
  simp only [sub_mul, mul_sub, add_mul, mul_add]
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [hA0sq, hA1sq, hB0sq, hB1sq]
  rw [← hA0B0, ← hA0B1, ← hA1B0, ← hA1B1]
  have hcsq : (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    norm_num
  have hccube : (((Real.sqrt 2 : ℝ) : ℂ) ^ 3) = ((Real.sqrt 2 : ℝ) : ℂ) * 2 := by
    rw [show (((Real.sqrt 2 : ℝ) : ℂ) ^ 3) =
        ((Real.sqrt 2 : ℝ) : ℂ) * (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) by ring, hcsq]
  ext i j
  simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, invSqrtTwo]
  ring_nf
  rw [hcsq, hccube]
  ring_nf

theorem sosTerm0_mul_self_posSemidef (M : ObservableModel HA HB) :
    (M.sosTerm0 * M.sosTerm0).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self M.sosTerm0
  rw [M.sosTerm0_isHermitian] at h
  exact h

theorem sosTerm1_mul_self_posSemidef (M : ObservableModel HA HB) :
    (M.sosTerm1 * M.sosTerm1).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self M.sosTerm1
  rw [M.sosTerm1_isHermitian] at h
  exact h

theorem tsirelsonSlack_posSemidef (M : ObservableModel HA HB) :
    M.tsirelsonSlack.PosSemidef := by
  rw [M.tsirelsonSlack_eq_sos]
  exact (Matrix.PosSemidef.add (M.sosTerm0_mul_self_posSemidef)
    (M.sosTerm1_mul_self_posSemidef)).smul invSqrtTwo_nonneg

theorem trace_mul_posSemidef_re_nonneg {a : Type u} [Fintype a] [DecidableEq a]
    (rho : State a) {H : CMatrix a}
    (hH : H.PosSemidef) :
    0 ≤ ((rho.matrix * H).trace).re := by
  have hpsd : (rho.sqrtMatrix * H * rho.sqrtMatrix).PosSemidef := by
    have h := hH.mul_mul_conjTranspose_same rho.sqrtMatrix
    rw [rho.sqrtMatrix_isHermitian] at h
    exact h
  have htrace : 0 ≤ (rho.sqrtMatrix * H * rho.sqrtMatrix).trace :=
    Matrix.PosSemidef.trace_nonneg hpsd
  have htrace_re : 0 ≤ ((rho.sqrtMatrix * H * rho.sqrtMatrix).trace).re := htrace.1
  have hEq : (rho.matrix * H).trace = (rho.sqrtMatrix * H * rho.sqrtMatrix).trace := by
    rw [← rho.sqrtMatrix_mul_self]
    calc
      ((rho.sqrtMatrix * rho.sqrtMatrix) * H).trace
          = (rho.sqrtMatrix * (rho.sqrtMatrix * H)).trace := by rw [Matrix.mul_assoc]
      _ = ((rho.sqrtMatrix * H) * rho.sqrtMatrix).trace := by rw [Matrix.trace_mul_comm]
      _ = (rho.sqrtMatrix * H * rho.sqrtMatrix).trace := by rw [Matrix.mul_assoc]
  rwa [hEq]

/-- Observable-level CHSH Tsirelson upper bound. -/
theorem value_le_two_mul_sqrt_two (M : ObservableModel HA HB) :
    M.value ≤ 2 * Real.sqrt 2 := by
  have hnonneg := trace_mul_posSemidef_re_nonneg M.rho M.tsirelsonSlack_posSemidef
  have hslack :
      ((M.rho.matrix * M.tsirelsonSlack).trace).re = 2 * Real.sqrt 2 - M.value := by
    rw [M.value_eq_trace_chshOperator]
    simp [tsirelsonSlack, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_smul,
      M.rho.trace_eq_one]
  rw [hslack] at hnonneg
  linarith

/-- Alice's two Pauli observables in the singlet CHSH strategy. -/
def singletAlice (x : Fin 2) : CMatrix Bool :=
  if x = 0 then TwoQubit.sigmaX else TwoQubit.sigmaZ

/-- Bob's two Pauli-direction observables in the singlet CHSH strategy. -/
def singletBob (y : Fin 2) : CMatrix Bool :=
  if y = 0 then
    (-TwoQubit.invSqrtTwo) • (TwoQubit.sigmaX + TwoQubit.sigmaZ)
  else
    TwoQubit.invSqrtTwo • (TwoQubit.sigmaZ - TwoQubit.sigmaX)

theorem singletAlice_isHermitian (x : Fin 2) :
    (singletAlice x).IsHermitian := by
  fin_cases x <;> simp [singletAlice, TwoQubit.sigmaX_isHermitian,
    TwoQubit.sigmaZ_isHermitian]

theorem singletBob_isHermitian (y : Fin 2) :
    (singletBob y).IsHermitian := by
  ext i j
  fin_cases y <;> cases i <;> cases j <;>
    simp [singletBob, TwoQubit.sigmaX, TwoQubit.sigmaZ, Matrix.conjTranspose]
  all_goals exact TwoQubit.star_invSqrtTwo

theorem singletAlice_square (x : Fin 2) :
    singletAlice x * singletAlice x = 1 := by
  fin_cases x <;> simp [singletAlice, TwoQubit.sigmaX_mul_self, TwoQubit.sigmaZ_mul_self]

theorem singletBob_square (y : Fin 2) :
    singletBob y * singletBob y = 1 := by
  ext i j
  fin_cases y <;> cases i <;> cases j <;>
    simp [singletBob, TwoQubit.sigmaX, TwoQubit.sigmaZ, Matrix.mul_apply,
      TwoQubit.invSqrtTwo_mul_self]
  all_goals norm_num

private theorem sqrt_two_cube_mul_quarter :
    (Real.sqrt 2 : ℝ) ^ 3 * (1 / 4) = Real.sqrt 2 * (1 / 2) := by
  have hsq : (Real.sqrt 2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  calc
    (Real.sqrt 2 : ℝ) ^ 3 * (1 / 4)
        = Real.sqrt 2 * ((Real.sqrt 2 : ℝ) ^ 2) * (1 / 4) := by ring
    _ = Real.sqrt 2 * 2 * (1 / 4) := by rw [hsq]
    _ = Real.sqrt 2 * (1 / 2) := by ring

private theorem sqrt_two_cube_mul_neg_quarter :
    (Real.sqrt 2 : ℝ) ^ 3 * (-1 / 4) = Real.sqrt 2 * (-1 / 2) := by
  rw [show (-1 / 4 : ℝ) = -(1 / 4) by norm_num, mul_neg,
    sqrt_two_cube_mul_quarter]
  ring

/-- Brunner's singlet strategy as a binary-observable CHSH model. -/
def singletObservableModel : ObservableModel Bool Bool where
  rho := TwoQubit.singletState
  alice := singletAlice
  bob := singletBob
  alice_isHermitian := singletAlice_isHermitian
  bob_isHermitian := singletBob_isHermitian
  alice_square := singletAlice_square
  bob_square := singletBob_square

theorem singletObservableModel_correlator_zero_zero :
    singletObservableModel.correlator 0 0 = Real.sqrt 2 / 2 := by
  norm_num [Fintype.sum_prod_type, singletObservableModel, correlator, jointObservable,
    singletAlice, singletBob,
    TwoQubit.singletState, TwoQubit.singletPureVector, TwoQubit.singletMatrix,
    rankOneMatrix, TwoQubit.singletAmp,
    TwoQubit.sigmaX, TwoQubit.sigmaZ, Matrix.vecMulVec_apply, Matrix.kronecker,
    Matrix.mul_apply, Matrix.trace, TwoQubit.invSqrtTwo, TwoQubit.star_invSqrtTwo]
  ring_nf
  exact sqrt_two_cube_mul_quarter

theorem singletObservableModel_correlator_zero_one :
    singletObservableModel.correlator 0 1 = Real.sqrt 2 / 2 := by
  norm_num [Fintype.sum_prod_type, singletObservableModel, correlator, jointObservable,
    singletAlice, singletBob,
    TwoQubit.singletState, TwoQubit.singletPureVector, TwoQubit.singletMatrix,
    rankOneMatrix, TwoQubit.singletAmp,
    TwoQubit.sigmaX, TwoQubit.sigmaZ, Matrix.vecMulVec_apply, Matrix.kronecker,
    Matrix.mul_apply, Matrix.trace, TwoQubit.invSqrtTwo, TwoQubit.star_invSqrtTwo]
  ring_nf
  exact sqrt_two_cube_mul_quarter

theorem singletObservableModel_correlator_one_zero :
    singletObservableModel.correlator 1 0 = Real.sqrt 2 / 2 := by
  norm_num [Fintype.sum_prod_type, singletObservableModel, correlator, jointObservable,
    singletAlice, singletBob,
    TwoQubit.singletState, TwoQubit.singletPureVector, TwoQubit.singletMatrix,
    rankOneMatrix, TwoQubit.singletAmp,
    TwoQubit.sigmaX, TwoQubit.sigmaZ, Matrix.vecMulVec_apply, Matrix.kronecker,
    Matrix.mul_apply, Matrix.trace, TwoQubit.invSqrtTwo, TwoQubit.star_invSqrtTwo]
  ring_nf
  exact sqrt_two_cube_mul_quarter

theorem singletObservableModel_correlator_one_one :
    singletObservableModel.correlator 1 1 = -(Real.sqrt 2 / 2) := by
  norm_num [Fintype.sum_prod_type, singletObservableModel, correlator, jointObservable,
    singletAlice, singletBob,
    TwoQubit.singletState, TwoQubit.singletPureVector, TwoQubit.singletMatrix,
    rankOneMatrix, TwoQubit.singletAmp,
    TwoQubit.sigmaX, TwoQubit.sigmaZ, Matrix.vecMulVec_apply, Matrix.kronecker,
    Matrix.mul_apply, Matrix.trace, TwoQubit.invSqrtTwo, TwoQubit.star_invSqrtTwo]
  ring_nf
  exact sqrt_two_cube_mul_neg_quarter

/-- The two-qubit singlet Pauli strategy attains CHSH value `2 * sqrt 2`. -/
theorem singletObservableModel_value :
    singletObservableModel.value = 2 * Real.sqrt 2 := by
  rw [value_eq_correlators, singletObservableModel_correlator_zero_zero,
    singletObservableModel_correlator_zero_one, singletObservableModel_correlator_one_zero,
    singletObservableModel_correlator_one_one]
  ring

end ObservableModel

/--
A finite-dimensional binary-contraction CHSH model.  This is the local bridge
surface for binary POVMs: the associated observables are Hermitian contractions
rather than necessarily square-one observables.
-/
structure ContractionModel (HA : Type u) (HB : Type v)
    [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB] where
  /-- Shared bipartite state. -/
  rho : State (HA × HB)
  /-- Alice's two Hermitian contraction observables. -/
  alice : Fin 2 → CMatrix HA
  /-- Bob's two Hermitian contraction observables. -/
  bob : Fin 2 → CMatrix HB
  /-- Alice's observables are Hermitian. -/
  alice_isHermitian : ∀ x, (alice x).IsHermitian
  /-- Bob's observables are Hermitian. -/
  bob_isHermitian : ∀ y, (bob y).IsHermitian
  /-- Alice's observables satisfy `A_x^2 ≤ I`. -/
  alice_contracts : ∀ x, (1 - alice x * alice x).PosSemidef
  /-- Bob's observables satisfy `B_y^2 ≤ I`. -/
  bob_contracts : ∀ y, (1 - bob y * bob y).PosSemidef

namespace ContractionModel

variable {HA : Type u} {HB : Type v}
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

/-- Tensor-product observable `A_x ⊗ B_y` for one CHSH setting pair. -/
def jointObservable (M : ContractionModel HA HB) (x y : Fin 2) : CMatrix (HA × HB) :=
  Matrix.kronecker (M.alice x) (M.bob y)

/-- Contraction-level correlator `E_xy = Tr(ρ (A_x ⊗ B_y))`. -/
def correlator (M : ContractionModel HA HB) (x y : Fin 2) : ℝ :=
  ((M.rho.matrix * M.jointObservable x y).trace).re

/-- Contraction-level CHSH value `E₀₀ + E₀₁ + E₁₀ - E₁₁`. -/
def value (M : ContractionModel HA HB) : ℝ :=
  M.correlator 0 0 + M.correlator 0 1 + M.correlator 1 0 - M.correlator 1 1

/-- The contraction value unfolds to the four-correlator CHSH formula. -/
theorem value_eq_correlators (M : ContractionModel HA HB) :
    M.value =
      M.correlator 0 0 + M.correlator 0 1 + M.correlator 1 0 - M.correlator 1 1 :=
  rfl

/-- Alice's contraction observable lifted to the bipartite product space. -/
def aliceLift (M : ContractionModel HA HB) (x : Fin 2) : CMatrix (HA × HB) :=
  Matrix.kronecker (M.alice x) (1 : CMatrix HB)

/-- Bob's contraction observable lifted to the bipartite product space. -/
def bobLift (M : ContractionModel HA HB) (y : Fin 2) : CMatrix (HA × HB) :=
  Matrix.kronecker (1 : CMatrix HA) (M.bob y)

/-- The CHSH Bell operator for a contraction model. -/
def chshOperator (M : ContractionModel HA HB) : CMatrix (HA × HB) :=
  M.aliceLift 0 * M.bobLift 0 + M.aliceLift 0 * M.bobLift 1 +
    M.aliceLift 1 * M.bobLift 0 - M.aliceLift 1 * M.bobLift 1

/-- First Tsirelson sum-of-squares term for contraction observables. -/
def sosTerm0 (M : ContractionModel HA HB) : CMatrix (HA × HB) :=
  M.aliceLift 0 - ObservableModel.invSqrtTwo • (M.bobLift 0 + M.bobLift 1)

/-- Second Tsirelson sum-of-squares term for contraction observables. -/
def sosTerm1 (M : ContractionModel HA HB) : CMatrix (HA × HB) :=
  M.aliceLift 1 - ObservableModel.invSqrtTwo • (M.bobLift 0 - M.bobLift 1)

/-- Slack matrix `2 sqrt 2 · I - S`, where `S` is the CHSH operator. -/
def tsirelsonSlack (M : ContractionModel HA HB) : CMatrix (HA × HB) :=
  ((2 * Real.sqrt 2 : ℝ) : ℂ) • 1 - M.chshOperator

/-- The positive certificate for the contraction Tsirelson slack. -/
def tsirelsonCertificate (M : ContractionModel HA HB) : CMatrix (HA × HB) :=
  M.sosTerm0 * M.sosTerm0 + M.sosTerm1 * M.sosTerm1 +
    (1 - M.aliceLift 0 * M.aliceLift 0) +
      (1 - M.aliceLift 1 * M.aliceLift 1) +
        (1 - M.bobLift 0 * M.bobLift 0) +
          (1 - M.bobLift 1 * M.bobLift 1)

theorem aliceLift_mul_bobLift (M : ContractionModel HA HB) (x y : Fin 2) :
    M.aliceLift x * M.bobLift y = M.jointObservable x y := by
  change (M.alice x ⊗ₖ (1 : CMatrix HB)) * ((1 : CMatrix HA) ⊗ₖ M.bob y) =
        M.alice x ⊗ₖ M.bob y
  rw [← Matrix.mul_kronecker_mul]
  simp

theorem bobLift_mul_aliceLift (M : ContractionModel HA HB) (x y : Fin 2) :
    M.bobLift y * M.aliceLift x = M.jointObservable x y := by
  change ((1 : CMatrix HA) ⊗ₖ M.bob y) * (M.alice x ⊗ₖ (1 : CMatrix HB)) =
        M.alice x ⊗ₖ M.bob y
  rw [← Matrix.mul_kronecker_mul]
  simp

theorem aliceLift_comm_bobLift (M : ContractionModel HA HB) (x y : Fin 2) :
    M.aliceLift x * M.bobLift y = M.bobLift y * M.aliceLift x := by
  rw [aliceLift_mul_bobLift, bobLift_mul_aliceLift]

theorem aliceLift_isHermitian (M : ContractionModel HA HB) (x : Fin 2) :
    (M.aliceLift x).IsHermitian := by
  change Matrix.conjTranspose (M.alice x ⊗ₖ (1 : CMatrix HB)) =
    M.alice x ⊗ₖ (1 : CMatrix HB)
  rw [Matrix.conjTranspose_kronecker, M.alice_isHermitian x]
  simp

theorem bobLift_isHermitian (M : ContractionModel HA HB) (y : Fin 2) :
    (M.bobLift y).IsHermitian := by
  change Matrix.conjTranspose ((1 : CMatrix HA) ⊗ₖ M.bob y) =
    (1 : CMatrix HA) ⊗ₖ M.bob y
  rw [Matrix.conjTranspose_kronecker, M.bob_isHermitian y]
  simp

theorem aliceLift_contracts (M : ContractionModel HA HB) (x : Fin 2) :
    (1 - M.aliceLift x * M.aliceLift x).PosSemidef := by
  have h :
      1 - M.aliceLift x * M.aliceLift x =
        Matrix.kronecker (1 - M.alice x * M.alice x) (1 : CMatrix HB) := by
    have hmul :
        M.aliceLift x * M.aliceLift x =
          Matrix.kronecker (M.alice x * M.alice x) ((1 : CMatrix HB) * 1) := by
      change (M.alice x ⊗ₖ (1 : CMatrix HB)) * (M.alice x ⊗ₖ (1 : CMatrix HB)) =
        (M.alice x * M.alice x) ⊗ₖ ((1 : CMatrix HB) * 1)
      rw [← Matrix.mul_kronecker_mul]
    rw [hmul]
    ext i j
    by_cases hHA : i.1 = j.1 <;> by_cases hHB : i.2 = j.2 <;>
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff,
        hHA, hHB]
  rw [h]
  exact (M.alice_contracts x).kronecker Matrix.PosSemidef.one

theorem bobLift_contracts (M : ContractionModel HA HB) (y : Fin 2) :
    (1 - M.bobLift y * M.bobLift y).PosSemidef := by
  have h :
      1 - M.bobLift y * M.bobLift y =
        Matrix.kronecker (1 : CMatrix HA) (1 - M.bob y * M.bob y) := by
    have hmul :
        M.bobLift y * M.bobLift y =
          Matrix.kronecker ((1 : CMatrix HA) * 1) (M.bob y * M.bob y) := by
      change ((1 : CMatrix HA) ⊗ₖ M.bob y) * ((1 : CMatrix HA) ⊗ₖ M.bob y) =
        ((1 : CMatrix HA) * 1) ⊗ₖ (M.bob y * M.bob y)
      rw [← Matrix.mul_kronecker_mul]
    rw [hmul]
    ext i j
    by_cases hHA : i.1 = j.1 <;> by_cases hHB : i.2 = j.2 <;>
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff,
        hHA, hHB]
  rw [h]
  exact Matrix.PosSemidef.one.kronecker (M.bob_contracts y)

theorem sosTerm0_isHermitian (M : ContractionModel HA HB) :
    M.sosTerm0.IsHermitian := by
  rw [Matrix.IsHermitian, sosTerm0, Matrix.conjTranspose_sub]
  rw [M.aliceLift_isHermitian 0, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    M.bobLift_isHermitian 0, M.bobLift_isHermitian 1]
  simp

theorem sosTerm1_isHermitian (M : ContractionModel HA HB) :
    M.sosTerm1.IsHermitian := by
  rw [Matrix.IsHermitian, sosTerm1, Matrix.conjTranspose_sub]
  rw [M.aliceLift_isHermitian 1, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    M.bobLift_isHermitian 0, M.bobLift_isHermitian 1]
  simp

theorem value_eq_trace_chshOperator (M : ContractionModel HA HB) :
    M.value = ((M.rho.matrix * M.chshOperator).trace).re := by
  simp [value, correlator, chshOperator, aliceLift_mul_bobLift, Matrix.mul_add,
    Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]

theorem tsirelsonSlack_eq_certificate (M : ContractionModel HA HB) :
    M.tsirelsonSlack = ObservableModel.invSqrtTwo • M.tsirelsonCertificate := by
  let A0 := M.aliceLift 0
  let A1 := M.aliceLift 1
  let B0 := M.bobLift 0
  let B1 := M.bobLift 1
  have hA0B0 : A0 * B0 = B0 * A0 := M.aliceLift_comm_bobLift 0 0
  have hA0B1 : A0 * B1 = B1 * A0 := M.aliceLift_comm_bobLift 0 1
  have hA1B0 : A1 * B0 = B0 * A1 := M.aliceLift_comm_bobLift 1 0
  have hA1B1 : A1 * B1 = B1 * A1 := M.aliceLift_comm_bobLift 1 1
  change ((2 * Real.sqrt 2 : ℝ) : ℂ) • (1 : CMatrix (HA × HB)) -
      (A0 * B0 + A0 * B1 + A1 * B0 - A1 * B1) =
    ObservableModel.invSqrtTwo •
      ((A0 - ObservableModel.invSqrtTwo • (B0 + B1)) *
          (A0 - ObservableModel.invSqrtTwo • (B0 + B1)) +
        (A1 - ObservableModel.invSqrtTwo • (B0 - B1)) *
          (A1 - ObservableModel.invSqrtTwo • (B0 - B1)) +
        (1 - A0 * A0) + (1 - A1 * A1) + (1 - B0 * B0) + (1 - B1 * B1))
  simp only [smul_add, smul_sub]
  simp only [sub_mul, mul_sub, add_mul, mul_add]
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [← hA0B0, ← hA0B1, ← hA1B0, ← hA1B1]
  have hcsq : (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    norm_num
  have hccube : (((Real.sqrt 2 : ℝ) : ℂ) ^ 3) = ((Real.sqrt 2 : ℝ) : ℂ) * 2 := by
    rw [show (((Real.sqrt 2 : ℝ) : ℂ) ^ 3) =
        ((Real.sqrt 2 : ℝ) : ℂ) * (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) by ring, hcsq]
  ext i j
  simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
    ObservableModel.invSqrtTwo]
  ring_nf
  rw [hcsq, hccube]
  ring_nf

theorem sosTerm0_mul_self_posSemidef (M : ContractionModel HA HB) :
    (M.sosTerm0 * M.sosTerm0).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self M.sosTerm0
  rw [M.sosTerm0_isHermitian] at h
  exact h

theorem sosTerm1_mul_self_posSemidef (M : ContractionModel HA HB) :
    (M.sosTerm1 * M.sosTerm1).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self M.sosTerm1
  rw [M.sosTerm1_isHermitian] at h
  exact h

theorem tsirelsonCertificate_posSemidef (M : ContractionModel HA HB) :
    M.tsirelsonCertificate.PosSemidef := by
  unfold tsirelsonCertificate
  exact (((((M.sosTerm0_mul_self_posSemidef.add M.sosTerm1_mul_self_posSemidef).add
    (M.aliceLift_contracts 0)).add (M.aliceLift_contracts 1)).add
      (M.bobLift_contracts 0)).add (M.bobLift_contracts 1))

theorem tsirelsonSlack_posSemidef (M : ContractionModel HA HB) :
    M.tsirelsonSlack.PosSemidef := by
  rw [M.tsirelsonSlack_eq_certificate]
  exact M.tsirelsonCertificate_posSemidef.smul ObservableModel.invSqrtTwo_nonneg

/-- Contraction-level CHSH Tsirelson upper bound. -/
theorem value_le_two_mul_sqrt_two (M : ContractionModel HA HB) :
    M.value ≤ 2 * Real.sqrt 2 := by
  have hnonneg := ObservableModel.trace_mul_posSemidef_re_nonneg M.rho M.tsirelsonSlack_posSemidef
  have hslack :
      ((M.rho.matrix * M.tsirelsonSlack).trace).re = 2 * Real.sqrt 2 - M.value := by
    rw [M.value_eq_trace_chshOperator]
    simp [tsirelsonSlack, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_smul,
      M.rho.trace_eq_one]
  rw [hslack] at hnonneg
  linarith

end ContractionModel

variable {a : Type u} [Fintype a] [DecidableEq a]

/--
The Hermitian `±1`-valued observable associated to a binary POVM under the
CHSH convention `false = +1`, `true = -1`.
-/
def _root_.QIT.POVM.binaryObservable (M : POVM Bool a) : CMatrix a :=
  M.effects false - M.effects true

theorem _root_.QIT.POVM.binary_sum_effects (M : POVM Bool a) :
    M.effects false + M.effects true = 1 := by
  simpa [Fintype.sum_bool, add_comm] using M.sum_eq_one

theorem _root_.QIT.POVM.effects_true_eq_one_sub_false (M : POVM Bool a) :
    M.effects true = 1 - M.effects false := by
  have h := M.binary_sum_effects
  rw [← h]
  abel

theorem _root_.QIT.POVM.binaryObservable_isHermitian (M : POVM Bool a) :
    M.binaryObservable.IsHermitian := by
  rw [Matrix.IsHermitian, POVM.binaryObservable, Matrix.conjTranspose_sub,
    (M.pos false).isHermitian, (M.pos true).isHermitian]

theorem _root_.QIT.POVM.effect_false_sub_square_nonneg (M : POVM Bool a) :
    (0 : CMatrix a) ≤ M.effects false - M.effects false * M.effects false := by
  let E := M.effects false
  have hE0 : (0 : CMatrix a) ≤ E := (M.pos false).nonneg
  have hE1 : E ≤ 1 := by
    rw [Matrix.le_iff]
    simpa [E, M.effects_true_eq_one_sub_false] using M.pos true
  have hEsa : IsSelfAdjoint E := IsSelfAdjoint.of_nonneg hE0
  have hE0' : (algebraMap ℝ (CMatrix a)) 0 ≤ E := by simpa using hE0
  have hspec0 : ∀ x ∈ spectrum ℝ E, (0 : ℝ) ≤ x := by
    simpa using (algebraMap_le_iff_le_spectrum (R := ℝ) (A := CMatrix a)
      (p := IsSelfAdjoint) (a := E) (r := (0 : ℝ)) (ha := hEsa)).mp hE0'
  have hspec1 : ∀ x ∈ spectrum ℝ E, x ≤ (1 : ℝ) := by
    simpa using (CFC.le_one_iff (R := ℝ) (A := CMatrix a)
      (p := IsSelfAdjoint) (a := E) (ha := hEsa)).mp hE1
  have hpos : 0 ≤ cfc (fun x : ℝ => x - x * x) E := by
    rw [cfc_nonneg_iff (R := ℝ) (A := CMatrix a) (p := IsSelfAdjoint)
      (a := E) (f := fun x : ℝ => x - x * x) (ha := hEsa)]
    intro x hx
    have hx0 := hspec0 x hx
    have hx1 := hspec1 x hx
    nlinarith
  have hcfceq : cfc (fun x : ℝ => x - x * x) E = E - E * E := by
    rw [cfc_sub (R := ℝ) (A := CMatrix a) (p := IsSelfAdjoint)
      (f := fun x : ℝ => x) (g := fun x : ℝ => x * x) (a := E)]
    rw [cfc_mul (R := ℝ) (A := CMatrix a) (p := IsSelfAdjoint)
      (f := fun x : ℝ => x) (g := fun x : ℝ => x) (a := E)]
    change cfc id E - cfc id E * cfc id E = E - E * E
    rw [cfc_id (R := ℝ) (A := CMatrix a) (p := IsSelfAdjoint) E]
  simpa [E, hcfceq] using hpos

theorem _root_.QIT.POVM.binaryObservable_contracts (M : POVM Bool a) :
    (1 - M.binaryObservable * M.binaryObservable).PosSemidef := by
  let E := M.effects false
  have htrue : M.effects true = 1 - E := by
    simpa [E] using M.effects_true_eq_one_sub_false
  have hquad : (E - E * E).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (M.effect_false_sub_square_nonneg)
  have hEq : 1 - M.binaryObservable * M.binaryObservable =
      (4 : ℝ) • (E - E * E) := by
    ext i j
    simp [POVM.binaryObservable, E, htrue, Matrix.mul_apply, Matrix.one_apply]
    ring_nf
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
      Finset.sum_ite_eq']
    rw [Finset.sum_mul]
    ring_nf
  rw [hEq]
  exact hquad.smul (by norm_num : (0 : ℝ) ≤ 4)

/-- The contraction model induced by the local binary POVMs of a CHSH quantum realization. -/
def _root_.QIT.Bell.QuantumRealization.toContractionModel :
    (R : QuantumRealization (Fin 2) (Fin 2) Bool Bool) →
      letI : Fintype R.HA := R.fintypeHA
      letI : DecidableEq R.HA := R.decidableEqHA
      letI : Fintype R.HB := R.fintypeHB
      letI : DecidableEq R.HB := R.decidableEqHB
      CHSH.ContractionModel R.HA R.HB := by
  intro R
  letI : Fintype R.HA := R.fintypeHA
  letI : DecidableEq R.HA := R.decidableEqHA
  letI : Fintype R.HB := R.fintypeHB
  letI : DecidableEq R.HB := R.decidableEqHB
  exact
    { rho := R.rho
      alice := fun x => (R.alice x).binaryObservable
      bob := fun y => (R.bob y).binaryObservable
      alice_isHermitian := fun x => (R.alice x).binaryObservable_isHermitian
      bob_isHermitian := fun y => (R.bob y).binaryObservable_isHermitian
      alice_contracts := fun x => (R.alice x).binaryObservable_contracts
      bob_contracts := fun y => (R.bob y).binaryObservable_contracts }

/-- Real CHSH correlator computed directly from a quantum realization's outcome probabilities. -/
def _root_.QIT.Bell.QuantumRealization.chshCorrelator
    (R : QuantumRealization (Fin 2) (Fin 2) Bool Bool) (x y : Fin 2) : ℝ :=
  ∑ ab : Bool × Bool,
    CHSH.outcomeSign ab.1 * CHSH.outcomeSign ab.2 * (R.prob ab.1 ab.2 x y : ℝ)

/-- CHSH value computed directly from a quantum realization's outcome probabilities. -/
def _root_.QIT.Bell.QuantumRealization.chshValue
    (R : QuantumRealization (Fin 2) (Fin 2) Bool Bool) : ℝ :=
  R.chshCorrelator 0 0 + R.chshCorrelator 0 1 +
    R.chshCorrelator 1 0 - R.chshCorrelator 1 1

theorem _root_.QIT.Bell.QuantumRealization.chshCorrelator_eq_toContractionModel_correlator
    (R : QuantumRealization (Fin 2) (Fin 2) Bool Bool)
    (x y : Fin 2) :
    letI : Fintype R.HA := R.fintypeHA
    letI : DecidableEq R.HA := R.decidableEqHA
    letI : Fintype R.HB := R.fintypeHB
    letI : DecidableEq R.HB := R.decidableEqHB
    R.chshCorrelator x y = (R.toContractionModel).correlator x y := by
  letI : Fintype R.HA := R.fintypeHA
  letI : DecidableEq R.HA := R.decidableEqHA
  letI : Fintype R.HB := R.fintypeHB
  letI : DecidableEq R.HB := R.decidableEqHB
  have htrace :
      ((R.rho.matrix *
            Matrix.kronecker ((R.alice x).effects false - (R.alice x).effects true)
              ((R.bob y).effects false - (R.bob y).effects true)).trace).re =
        ((R.rho.matrix *
            Matrix.kronecker ((R.alice x).effects false) ((R.bob y).effects false)).trace).re -
          ((R.rho.matrix *
            Matrix.kronecker ((R.alice x).effects false) ((R.bob y).effects true)).trace).re -
          ((R.rho.matrix *
            Matrix.kronecker ((R.alice x).effects true) ((R.bob y).effects false)).trace).re +
          ((R.rho.matrix *
            Matrix.kronecker ((R.alice x).effects true) ((R.bob y).effects true)).trace).re := by
    have hkr :
        Matrix.kronecker ((R.alice x).effects false - (R.alice x).effects true)
            ((R.bob y).effects false - (R.bob y).effects true) =
          Matrix.kronecker ((R.alice x).effects false) ((R.bob y).effects false) -
            Matrix.kronecker ((R.alice x).effects false) ((R.bob y).effects true) -
            Matrix.kronecker ((R.alice x).effects true) ((R.bob y).effects false) +
            Matrix.kronecker ((R.alice x).effects true) ((R.bob y).effects true) := by
      ext i j
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
      ring
    rw [hkr]
    simp [Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]
  simp only [Matrix.kronecker] at htrace
  unfold QuantumRealization.chshCorrelator CHSH.ContractionModel.correlator
    CHSH.ContractionModel.jointObservable QuantumRealization.toContractionModel
  simp [QuantumRealization.prob, POVM.prob_eq_trace_re, R.joint_effects,
    POVM.binaryObservable, CHSH.outcomeSign, Fintype.sum_prod_type]
  change _ =
    ((R.rho.matrix *
      Matrix.kronecker ((R.alice x).effects false - (R.alice x).effects true)
        ((R.bob y).effects false - (R.bob y).effects true)).trace).re
  simp only [Matrix.kronecker]
  rw [htrace]
  ring_nf

theorem _root_.QIT.Bell.QuantumRealization.chshValue_eq_toContractionModel_value :
    (R : QuantumRealization (Fin 2) (Fin 2) Bool Bool) →
    letI : Fintype R.HA := R.fintypeHA
    letI : DecidableEq R.HA := R.decidableEqHA
    letI : Fintype R.HB := R.fintypeHB
    letI : DecidableEq R.HB := R.decidableEqHB
    R.chshValue = (R.toContractionModel).value := by
  intro R
  letI : Fintype R.HA := R.fintypeHA
  letI : DecidableEq R.HA := R.decidableEqHA
  letI : Fintype R.HB := R.fintypeHB
  letI : DecidableEq R.HB := R.decidableEqHB
  simp [QuantumRealization.chshValue, CHSH.ContractionModel.value,
    R.chshCorrelator_eq_toContractionModel_correlator]

/-- A finite POVM-based CHSH quantum realization satisfies the Tsirelson bound. -/
theorem _root_.QIT.Bell.QuantumRealization.chshValue_le_two_mul_sqrt_two :
    (R : QuantumRealization (Fin 2) (Fin 2) Bool Bool) →
    R.chshValue ≤ 2 * Real.sqrt 2 := by
  intro R
  letI : Fintype R.HA := R.fintypeHA
  letI : DecidableEq R.HA := R.decidableEqHA
  letI : Fintype R.HB := R.fintypeHB
  letI : DecidableEq R.HB := R.decidableEqHB
  rw [R.chshValue_eq_toContractionModel_value]
  exact CHSH.ContractionModel.value_le_two_mul_sqrt_two R.toContractionModel

end
end CHSH
end Bell
end QIT
