/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Security.ExtractorTraceBridge
public import QIT.Util.BlockMatrix
public import QIT.Util.SDP.HermitianPSDTraceDuality
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Complex.Norm

/-!
# Quadratic bridge for direct extractor bounds

This module contains the finite matrix quadratic expression that appears in
Tomamichel's direct leftover-hash proof, together with the source-shaped bridge
from cq conditional min-entropy feasibility.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT.Security

universe uZ ue

noncomputable section

variable {Z : Type uZ} {e : Type ue}
variable [Fintype Z] [DecidableEq Z]
variable [Fintype e] [DecidableEq e]

omit [DecidableEq e] in
private theorem cMatrix_trace_re_le_of_le {X Y : CMatrix e} (hXY : X ≤ Y) :
    X.trace.re ≤ Y.trace.re := by
  rw [Matrix.le_iff] at hXY
  have htrace : 0 ≤ (Y - X).trace.re :=
    (Matrix.PosSemidef.trace_nonneg hXY).1
  have hcalc : (Y - X).trace.re = Y.trace.re - X.trace.re := by
    simp [Matrix.trace_sub]
  linarith

private theorem cMatrix_effect_mul_self_le_self {P : CMatrix e}
    (hPpos : P.PosSemidef) (hPle : P ≤ 1) :
    P * P ≤ P := by
  classical
  rw [Matrix.le_iff]
  let U : Matrix.unitaryGroup e ℂ := hPpos.1.eigenvectorUnitary
  let D : CMatrix e := Matrix.diagonal fun i => ((hPpos.1.eigenvalues i : ℝ) : ℂ)
  have hPdiag : P = (U : CMatrix e) * D * star (U : CMatrix e) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hPpos.1.spectral_theorem
  have hUstarU : star (U : CMatrix e) * (U : CMatrix e) = 1 := by
    simp [U]
  have hDle1 : ∀ i, hPpos.1.eigenvalues i ≤ 1 := by
    intro i
    have hsub : (1 - P).PosSemidef := by
      simpa [Matrix.le_iff] using hPle
    have hconj_eq :
        star (U : CMatrix e) * (1 - P) * (U : CMatrix e) = 1 - D := by
      rw [hPdiag]
      calc
        star (U : CMatrix e) * (1 - (U : CMatrix e) * D * star (U : CMatrix e)) *
            (U : CMatrix e) =
          (star (U : CMatrix e) * (U : CMatrix e)) -
            (star (U : CMatrix e) * (U : CMatrix e)) * D *
              (star (U : CMatrix e) * (U : CMatrix e)) := by
            noncomm_ring
        _ = 1 - D := by rw [hUstarU]; simp
    have hconj : (star (U : CMatrix e) * (1 - P) * (U : CMatrix e)).PosSemidef := by
      rw [Matrix.IsUnit.posSemidef_star_left_conjugate_iff (Unitary.isUnit_coe :
        IsUnit (U : CMatrix e))]
      exact hsub
    have hdiag_nonneg :
        0 ≤ ((1 - D) i i) :=
      (by
        rw [← hconj_eq]
        exact (Matrix.PosSemidef.diag_nonneg hconj (i := i)))
    have hdiag : ((1 - D) i i) = (1 : ℂ) - hPpos.1.eigenvalues i := by
      simp [D]
    have hreal : 0 ≤ (1 : ℝ) - hPpos.1.eigenvalues i := by
      have hcomplex : ((hPpos.1.eigenvalues i : ℂ) ≤ 1) := by
        simpa [hdiag, sub_nonneg] using hdiag_nonneg
      have hle : hPpos.1.eigenvalues i ≤ 1 := by
        exact_mod_cast hcomplex
      linarith
    linarith
  have hDsq_le_D : D * D ≤ D := by
    rw [Matrix.le_iff]
    rw [show D - D * D =
        Matrix.diagonal fun i =>
          (((hPpos.1.eigenvalues i - hPpos.1.eigenvalues i ^ 2 : ℝ)) : ℂ) by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [D, sub_eq_add_neg, pow_two]
      · simp [D, Matrix.diagonal, Matrix.mul_apply, hij]]
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    have hnonneg := hPpos.eigenvalues_nonneg i
    have hle := hDle1 i
    exact_mod_cast (by nlinarith [sq_nonneg (hPpos.1.eigenvalues i)])
  have hsub :
      P - P * P =
        (U : CMatrix e) * (D - D * D) * star (U : CMatrix e) := by
    rw [hPdiag]
    calc
      (U : CMatrix e) * D * star (U : CMatrix e) -
          ((U : CMatrix e) * D * star (U : CMatrix e)) *
            ((U : CMatrix e) * D * star (U : CMatrix e)) =
        (U : CMatrix e) * (D - D * (star (U : CMatrix e) * (U : CMatrix e)) * D) *
          star (U : CMatrix e) := by
          noncomm_ring
      _ = (U : CMatrix e) * (D - D * D) * star (U : CMatrix e) := by
          rw [hUstarU]
          simp
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (U : CMatrix e))]
  simpa [Matrix.le_iff] using hDsq_le_D

private theorem cMatrix_effect_trace_weight_le_one {P σ : CMatrix e}
    (hPpos : P.PosSemidef) (hPle : P ≤ 1) (hσ : σ.PosSemidef)
    (hσtr : σ.trace.re = 1) :
    ((P * σ * P).trace).re ≤ 1 := by
  have hP2le : P * P ≤ P := cMatrix_effect_mul_self_le_self hPpos hPle
  have htrace_le :
      ((σ * (P * P)).trace).re ≤ ((σ * P).trace).re :=
    QIT.cMatrix_trace_mul_le_of_le_posSemidef_left hσ hP2le
  have htrace_le_one :
      ((σ * P).trace).re ≤ σ.trace.re :=
    (QIT.cMatrix_trace_mul_le_of_le_posSemidef_left hσ hPle).trans_eq (by simp)
  have hcyc : (P * σ * P).trace = (σ * (P * P)).trace := by
    calc
      (P * σ * P).trace = ((P * σ) * P).trace := by rw [Matrix.mul_assoc]
      _ = (P * (P * σ)).trace := by rw [Matrix.trace_mul_comm]
      _ = ((P * P) * σ).trace := by rw [← Matrix.mul_assoc]
      _ = (σ * (P * P)).trace := by rw [Matrix.trace_mul_comm]
  rw [hcyc]
  linarith

private theorem cMatrix_trace_mul_effect_abs_sq_le_quadratic
    {R σ P : CMatrix e}
    (hR : R.IsHermitian) (hσ : σ.PosDef)
    (hPpos : P.PosSemidef) (hPle : P ≤ 1) (hσtr : σ.trace.re = 1) :
    Complex.normSq ((R * P).trace) ≤ ((σ⁻¹ * R * R).trace).re := by
  classical
  let M : CMatrix e := σ⁻¹
  have hM : M.PosDef := by simpa [M] using hσ.inv
  letI : NormedAddCommGroup (CMatrix e) := Matrix.toMatrixNormedAddCommGroup M hM
  letI : InnerProductSpace ℂ (CMatrix e) := Matrix.toMatrixInnerProductSpace M hM.posSemidef
  let x : CMatrix e := R
  let y : CMatrix e := P * σ
  have hcs := norm_inner_le_norm (𝕜 := ℂ) x y
  have hinner : inner ℂ x y = (R * P).trace := by
    dsimp [x, y, M]
    change ((P * σ) * σ⁻¹ * Matrix.conjTranspose R).trace = (R * P).trace
    have hdet : IsUnit σ.det := (Matrix.isUnit_iff_isUnit_det σ).mp hσ.isUnit
    calc
      ((P * σ) * σ⁻¹ * Matrix.conjTranspose R).trace =
          (P * (σ * σ⁻¹) * Matrix.conjTranspose R).trace := by noncomm_ring
      _ = (P * 1 * Matrix.conjTranspose R).trace := by rw [Matrix.mul_nonsing_inv σ hdet]
      _ = (P * R).trace := by simp [hR.eq]
      _ = (R * P).trace := by rw [Matrix.trace_mul_comm]
  have hxnorm : ‖x‖ ^ 2 = ((σ⁻¹ * R * R).trace).re := by
    rw [@norm_sq_eq_re_inner ℂ (CMatrix e) _ _ _ x]
    dsimp [x, M]
    change ((R * σ⁻¹ * Matrix.conjTranspose R).trace).re =
      ((σ⁻¹ * R * R).trace).re
    rw [hR.eq]
    congr 1
    calc
      (R * σ⁻¹ * R).trace = ((R * σ⁻¹) * R).trace := by rw [Matrix.mul_assoc]
      _ = (R * (R * σ⁻¹)).trace := by rw [Matrix.trace_mul_comm]
      _ = ((R * R) * σ⁻¹).trace := by rw [← Matrix.mul_assoc]
      _ = (σ⁻¹ * (R * R)).trace := by rw [Matrix.trace_mul_comm]
      _ = (σ⁻¹ * R * R).trace := by rw [← Matrix.mul_assoc]
  have hynorm : ‖y‖ ^ 2 = ((P * σ * P).trace).re := by
    rw [@norm_sq_eq_re_inner ℂ (CMatrix e) _ _ _ y]
    dsimp [y, M]
    change (((P * σ) * σ⁻¹ * Matrix.conjTranspose (P * σ)).trace).re =
      ((P * σ * P).trace).re
    have hdet : IsUnit σ.det := (Matrix.isUnit_iff_isUnit_det σ).mp hσ.isUnit
    calc
      (((P * σ) * σ⁻¹ * Matrix.conjTranspose (P * σ)).trace).re =
          ((P * (σ * σ⁻¹) * (Matrix.conjTranspose σ * Matrix.conjTranspose P)).trace).re := by
            rw [Matrix.conjTranspose_mul]
            congr 1
            noncomm_ring
      _ = ((P * 1 * (σ * P)).trace).re := by
            rw [Matrix.mul_nonsing_inv σ hdet, hσ.isHermitian.eq, hPpos.isHermitian.eq]
      _ = ((P * σ * P).trace).re := by simp [Matrix.mul_assoc]
  have hsq : Complex.normSq (inner ℂ x y) ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    calc
      ‖inner ℂ x y‖ ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hcs
      _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by ring
  have hq_nonneg : 0 ≤ ((σ⁻¹ * R * R).trace).re := by
    rw [← hxnorm]
    positivity
  have hweight :
      ((P * σ * P).trace).re ≤ 1 :=
    cMatrix_effect_trace_weight_le_one hPpos hPle hσ.posSemidef hσtr
  have hmul :
      ((σ⁻¹ * R * R).trace).re * ((P * σ * P).trace).re ≤
        ((σ⁻¹ * R * R).trace).re := by
    simpa using mul_le_mul_of_nonneg_left hweight hq_nonneg
  have hsq' :
      Complex.normSq ((R * P).trace) ≤
        ((σ⁻¹ * R * R).trace).re * ((P * σ * P).trace).re := by
    simpa [hinner, hxnorm, hynorm] using hsq
  exact hsq'.trans hmul

private theorem cMatrix_trace_mul_effect_re_le_sqrt_quadratic
    {R σ P : CMatrix e}
    (hR : R.IsHermitian) (hσ : σ.PosDef)
    (hPpos : P.PosSemidef) (hPle : P ≤ 1) (hσtr : σ.trace.re = 1) :
    ((R * P).trace).re ≤
      Real.sqrt ((σ⁻¹ * R * R).trace).re := by
  have habs_sq :=
    cMatrix_trace_mul_effect_abs_sq_le_quadratic hR hσ hPpos hPle hσtr
  have hq_nonneg : 0 ≤ ((σ⁻¹ * R * R).trace).re := by
    have h := cMatrix_trace_mul_effect_abs_sq_le_quadratic
      hR hσ hPpos hPle hσtr
    exact le_trans (Complex.normSq_nonneg _) h
  have habs_le :
      ‖((R * P).trace)‖ ≤
        Real.sqrt ((σ⁻¹ * R * R).trace).re := by
    have hsq_norm :
        ‖((R * P).trace)‖ ^ 2 ≤ ((σ⁻¹ * R * R).trace).re := by
      simpa [Complex.normSq_eq_norm_sq] using habs_sq
    exact Real.le_sqrt_of_sq_le hsq_norm
  exact le_trans (Complex.re_le_norm _) habs_le

private theorem cMatrix_inv_mul_self_trace_nonneg_of_hermitian_posDef
    {R σ : CMatrix e} (hR : R.IsHermitian) (hσ : σ.PosDef) :
    0 ≤ ((σ⁻¹ * R * R).trace).re := by
  have hpsd : (R * σ⁻¹ * R).PosSemidef := by
    have h := hσ.inv.posSemidef.mul_mul_conjTranspose_same R
    simpa [hR.eq, Matrix.mul_assoc] using h
  have htrace : 0 ≤ ((R * σ⁻¹ * R).trace).re :=
    (Matrix.PosSemidef.trace_nonneg hpsd).1
  have hcyc : (σ⁻¹ * R * R).trace = (R * σ⁻¹ * R).trace := by
    calc
      (σ⁻¹ * R * R).trace = ((σ⁻¹ * R) * R).trace := by rw [Matrix.mul_assoc]
      _ = (R * (σ⁻¹ * R)).trace := by rw [Matrix.trace_mul_comm]
      _ = (R * σ⁻¹ * R).trace := by rw [Matrix.mul_assoc]
  rwa [hcyc]

/-- CQ quadratic witness `∑_z tr(σ⁻¹ (p_z ρ_z) (p_z ρ_z))`. -/
def extractorCqQuadraticTerm (E : Ensemble Z e) (σ : State e) : ℝ :=
  ∑ z, ((σ.matrix⁻¹ * E.cqBlock z * E.cqBlock z).trace).re

omit [DecidableEq Z] in
@[simp]
theorem extractorCqQuadraticTerm_eq_sum (E : Ensemble Z e) (σ : State e) :
    extractorCqQuadraticTerm E σ =
      ∑ z, ((σ.matrix⁻¹ * E.cqBlock z * E.cqBlock z).trace).re :=
  rfl

theorem cMatrix_mul_inv_mul_self_le_smul_of_posSemidef_le_posDef
    {A σ : CMatrix e} {c : ℝ}
    (hA : A.PosSemidef) (hσ : σ.PosDef) (hc : 0 < c)
    (hAσ : A ≤ (c : ℂ) • σ) :
    A * σ⁻¹ * A ≤ (c : ℂ) • A := by
  classical
  rw [Matrix.le_iff]
  let C : CMatrix e := (c : ℂ) • σ
  have hcC : (0 : ℂ) < (c : ℂ) := by
    exact_mod_cast hc
  have hC : C.PosDef := by
    simpa [C] using hσ.smul hcC
  have hCminusA : (C - A).PosSemidef := by
    simpa [C, Matrix.le_iff] using hAσ
  have hblock :
      (Matrix.fromBlocks A A A C : CMatrix (Sum e e)).PosSemidef :=
    cMatrix_fromBlocks_self_le_posSemidef (e := e) hA hCminusA
  letI : Invertible C := hC.isUnit.invertible
  have hblock' :
      (Matrix.fromBlocks A A A.conjTranspose C : CMatrix (Sum e e)).PosSemidef := by
    simpa [hA.isHermitian.eq] using hblock
  have hschur :
      (A - A * C⁻¹ * A.conjTranspose).PosSemidef :=
    (Matrix.PosDef.fromBlocks₂₂ A A (D := C) hC).mp hblock'
  have hC_le :
      A * C⁻¹ * A ≤ A := by
    rw [Matrix.le_iff]
    simpa [hA.isHermitian.eq] using hschur
  have hcne : (c : ℂ) ≠ 0 := by
    exact_mod_cast hc.ne'
  letI : Invertible (c : ℂ) := invertibleOfNonzero hcne
  have hσdet : IsUnit σ.det := (Matrix.isUnit_iff_isUnit_det σ).mp hσ.isUnit
  have hCinv : C⁻¹ = ((c : ℂ)⁻¹) • σ⁻¹ := by
    calc
      C⁻¹ = (((c : ℂ) • σ))⁻¹ := by rfl
      _ = ⅟(c : ℂ) • σ⁻¹ := by
        simpa using Matrix.inv_smul σ (c : ℂ) hσdet
      _ = ((c : ℂ)⁻¹) • σ⁻¹ := by
        simp [invOf_eq_inv]
  have hinvScaled :
      ((c : ℂ)⁻¹) • (A * σ⁻¹ * A) ≤ A := by
    simpa [hCinv, Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul] using hC_le
  rw [Matrix.le_iff] at hinvScaled
  have hcNonneg : (0 : ℂ) ≤ (c : ℂ) := le_of_lt hcC
  have hscaled := hinvScaled.smul hcNonneg
  have hscale_eq :
      (c : ℂ) • (A - ((c : ℂ)⁻¹) • (A * σ⁻¹ * A)) =
        (c : ℂ) • A - A * σ⁻¹ * A := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hcne, one_smul]
  simpa [hscale_eq] using hscaled

theorem cMatrix_inv_mul_sq_trace_le_scaled_trace_of_le
    {A σ : CMatrix e} {c : ℝ}
    (hA : A.PosSemidef) (hσ : σ.PosDef) (hc : 0 < c)
    (hAσ : A ≤ (c : ℂ) • σ) :
    ((σ⁻¹ * A * A).trace).re ≤ c * A.trace.re := by
  classical
  have hle :
      A * σ⁻¹ * A ≤ (c : ℂ) • A :=
    cMatrix_mul_inv_mul_self_le_smul_of_posSemidef_le_posDef hA hσ hc hAσ
  have htrace_le := cMatrix_trace_re_le_of_le (e := e) hle
  have hcyc : (σ⁻¹ * A * A).trace = (A * σ⁻¹ * A).trace := by
    calc
      (σ⁻¹ * A * A).trace = ((σ⁻¹ * A) * A).trace := by rw [Matrix.mul_assoc]
      _ = (A * (σ⁻¹ * A)).trace := by rw [Matrix.trace_mul_comm]
      _ = (A * σ⁻¹ * A).trace := by rw [Matrix.mul_assoc]
  have hrhs : (((c : ℂ) • A).trace).re = c * A.trace.re := by
    simp [Matrix.trace_smul]
  simpa [hcyc, hrhs] using htrace_le

theorem extractorCqQuadratic_le_rpow_of_conditionalMinEntropyFeasible_posDef
    (E : Ensemble Z e) (σ : State e) (lam : ℝ)
    (hσ : σ.matrix.PosDef)
    (hmin : State.ConditionalMinEntropyFeasible (a := Z) E.cqState σ lam) :
    extractorCqQuadraticTerm E σ ≤ Real.rpow 2 (-lam) := by
  classical
  let c : ℝ := Real.rpow 2 (-lam)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hdual :
      E.cqDualFeasible ((Real.rpow 2 (-lam) : ℂ) • σ.matrix) :=
    Ensemble.cqDualFeasible_of_conditionalMinEntropyFeasible E σ lam hmin
  have hblock_psd : ∀ z, (E.cqBlock z).PosSemidef := by
    intro z
    rw [Ensemble.cqBlock_eq]
    exact (E.states z).pos.smul (by exact_mod_cast NNReal.coe_nonneg (E.probs z))
  have hterm : ∀ z,
      ((σ.matrix⁻¹ * E.cqBlock z * E.cqBlock z).trace).re ≤
        c * (E.cqBlock z).trace.re := by
    intro z
    simpa [c] using
      cMatrix_inv_mul_sq_trace_le_scaled_trace_of_le
        (e := e) (A := E.cqBlock z) (σ := σ.matrix) (c := c)
        (hblock_psd z) hσ hc (by simpa [c] using hdual.2 z)
  have hsum_le :
      ∑ z, ((σ.matrix⁻¹ * E.cqBlock z * E.cqBlock z).trace).re ≤
        ∑ z, c * (E.cqBlock z).trace.re :=
    Finset.sum_le_sum fun z _ => hterm z
  have htrace_sum : ∑ z, (E.cqBlock z).trace.re = 1 := by
    calc
      ∑ z, (E.cqBlock z).trace.re =
          ∑ z, ((E.probs z : ℂ) * (E.states z).matrix.trace).re := by
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [Ensemble.cqBlock_eq, Matrix.trace_smul]
            rfl
      _ = ∑ z, (E.probs z : ℝ) := by
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [(E.states z).trace_eq_one]
            simp
      _ = 1 := by
            exact_mod_cast E.weights_sum
  calc
    extractorCqQuadraticTerm E σ =
        ∑ z, ((σ.matrix⁻¹ * E.cqBlock z * E.cqBlock z).trace).re := rfl
    _ ≤ ∑ z, c * (E.cqBlock z).trace.re := hsum_le
    _ = c * ∑ z, (E.cqBlock z).trace.re := by rw [Finset.mul_sum]
    _ = c := by rw [htrace_sum, mul_one]
    _ = Real.rpow 2 (-lam) := rfl

namespace HashFamily

universe uF uS

variable {F : Type uF} {S : Type uS}
variable [Fintype F] [DecidableEq F] [Nonempty F]
variable [Fintype S] [DecidableEq S] [Nonempty S]

/-- The side-information block landing in output bucket `s` for seed `f`. -/
def extractorSeedOutputBucket (H : HashFamily F Z S) (E : Ensemble Z e)
    (f : F) (s : S) : CMatrix e :=
  ∑ z : Z, if H.hash f z = s then E.cqBlock z else 0

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] [Fintype S] [Nonempty S] in
@[simp]
theorem extractorSeedOutputBucket_eq_sum (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) (s : S) :
    H.extractorSeedOutputBucket E f s =
      ∑ z : Z, if H.hash f z = s then E.cqBlock z else 0 :=
  rfl

omit [DecidableEq F] [Nonempty F] [Fintype S] [Nonempty S] [DecidableEq Z] in
/-- The source-style output bucket is positive semidefinite. -/
theorem extractorSeedOutputBucket_posSemidef (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) (s : S) :
    (H.extractorSeedOutputBucket E f s).PosSemidef := by
  classical
  unfold extractorSeedOutputBucket
  refine Matrix.posSemidef_sum Finset.univ fun z _ => ?_
  by_cases hz : H.hash f z = s
  · simpa [hz] using Ensemble.cqBlock_posSemidef E z
  · simp [hz, Matrix.PosSemidef.zero]

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] [Fintype S] [Nonempty S] in
/-- Trace of one source-style output bucket. -/
theorem extractorSeedOutputBucket_trace_re (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) (s : S) :
    (H.extractorSeedOutputBucket E f s).trace.re =
      ∑ z : Z, if H.hash f z = s then (E.probs z : ℝ) else 0 := by
  classical
  unfold extractorSeedOutputBucket
  rw [Matrix.trace_sum]
  simp only [Complex.re_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : H.hash f z = s
  · have htrace_re : (E.states z).matrix.trace.re = 1 := by
      rw [(E.states z).trace_eq_one]
      simp
    simp [hz, Ensemble.cqBlock_eq, Matrix.trace_smul, htrace_re]
  · simp [hz]

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] [Fintype S] [Nonempty S] in
/-- One source-style output bucket has trace at most one. -/
theorem extractorSeedOutputBucket_trace_re_le_one (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) (s : S) :
    (H.extractorSeedOutputBucket E f s).trace.re ≤ 1 := by
  classical
  rw [H.extractorSeedOutputBucket_trace_re E f s]
  have hsum_le :
      (∑ z : Z, if H.hash f z = s then (E.probs z : ℝ) else 0) ≤
        ∑ z : Z, (E.probs z : ℝ) := by
    refine Finset.sum_le_sum fun z _ => ?_
    by_cases hz : H.hash f z = s
    · simp [hz]
    · exact by simp [hz, E.prob_nonneg z]
  have hsum : (∑ z : Z, (E.probs z : ℝ)) = 1 := by
    exact_mod_cast E.weights_sum
  exact hsum_le.trans_eq hsum

/--
The subnormalized side-information state in output bucket `s` when seed `f` is
applied.

[Tomamichel2015FiniteResources, apps.tex:256-292]
-/
def extractorSeedOutputBucketState (H : HashFamily F Z S) (E : Ensemble Z e)
    (f : F) (s : S) : SubnormalizedState e where
  matrix := H.extractorSeedOutputBucket E f s
  pos := H.extractorSeedOutputBucket_posSemidef E f s
  trace_le_one := H.extractorSeedOutputBucket_trace_re_le_one E f s

omit [DecidableEq F] [Nonempty F] [Fintype S] [Nonempty S] [DecidableEq Z] in
@[simp]
theorem extractorSeedOutputBucketState_matrix (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) (s : S) :
    (H.extractorSeedOutputBucketState E f s).matrix =
      H.extractorSeedOutputBucket E f s :=
  rfl

omit [DecidableEq F] [Nonempty F] [Fintype S] [Nonempty S] [DecidableEq Z] in
@[simp]
theorem extractorSeedOutputBucketState_trace_re (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) (s : S) :
    (H.extractorSeedOutputBucketState E f s).matrix.trace.re =
      ∑ z : Z, if H.hash f z = s then (E.probs z : ℝ) else 0 := by
  simpa using H.extractorSeedOutputBucket_trace_re E f s

/-- The total side-information block before hashing. -/
def extractorCqTotalBlock (_H : HashFamily F Z S) (E : Ensemble Z e) : CMatrix e :=
  ∑ z : Z, E.cqBlock z

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] [Fintype S] [DecidableEq S] [Nonempty S] in
@[simp]
theorem extractorCqTotalBlock_eq_sum (H : HashFamily F Z S) (E : Ensemble Z e) :
    H.extractorCqTotalBlock E = ∑ z : Z, E.cqBlock z :=
  rfl

/--
Centered output residual for one seed/output bucket:
`ρ_{E,s|f} - |S|⁻¹ ρ_E`.
-/
def extractorSeedCenteredResidual (H : HashFamily F Z S) (E : Ensemble Z e)
    (f : F) (s : S) : CMatrix e :=
  H.extractorSeedOutputBucket E f s -
    ((Fintype.card S : ℂ)⁻¹) • H.extractorCqTotalBlock E

private def centerCoeffR (H : HashFamily F Z S) (f : F) (s : S) (z : Z) : ℝ :=
  (if H.hash f z = s then 1 else 0) - (Fintype.card S : ℝ)⁻¹

private def centerCoeffC (H : HashFamily F Z S) (f : F) (s : S) (z : Z) : ℂ :=
  (if H.hash f z = s then 1 else 0) - (Fintype.card S : ℂ)⁻¹

omit [Fintype Z] [DecidableEq Z] [DecidableEq F] [Nonempty F] [Nonempty S] in
private theorem centerCoeffC_eq_ofReal (H : HashFamily F Z S)
    (f : F) (s : S) (z : Z) :
    H.centerCoeffC f s z = (H.centerCoeffR f s z : ℂ) := by
  unfold centerCoeffC centerCoeffR
  by_cases h : H.hash f z = s <;> simp [h]

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] [Fintype S] [Nonempty S] in
private theorem if_cqBlock_eq_indicator_smul
    (H : HashFamily F Z S) (E : Ensemble Z e) (f : F) (s : S) (z : Z) :
    (if H.hash f z = s then E.cqBlock z else 0) =
      ((if H.hash f z = s then (1 : ℂ) else 0) • E.cqBlock z) := by
  by_cases h : H.hash f z = s <;> simp [h]

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] [Nonempty S] in
private theorem extractorSeedCenteredResidual_eq_centerCoeff_sum
    (H : HashFamily F Z S) (E : Ensemble Z e) (f : F) (s : S) :
    H.extractorSeedCenteredResidual E f s =
      ∑ z : Z, H.centerCoeffC f s z • E.cqBlock z := by
  classical
  unfold extractorSeedCenteredResidual extractorSeedOutputBucket extractorCqTotalBlock centerCoeffC
  calc
    (∑ z : Z, if H.hash f z = s then E.cqBlock z else 0) -
        (Fintype.card S : ℂ)⁻¹ • ∑ z : Z, E.cqBlock z
        = (∑ z : Z, (if H.hash f z = s then (1 : ℂ) else 0) • E.cqBlock z) -
            ∑ z : Z, ((Fintype.card S : ℂ)⁻¹) • E.cqBlock z := by
            simp_rw [if_cqBlock_eq_indicator_smul]
            rw [Finset.smul_sum]
    _ = ∑ z : Z,
          ((if H.hash f z = s then (1 : ℂ) else 0) • E.cqBlock z -
            ((Fintype.card S : ℂ)⁻¹) • E.cqBlock z) := by
            rw [← Finset.sum_sub_distrib]
    _ = ∑ z : Z,
          (((if H.hash f z = s then (1 : ℂ) else 0) - (Fintype.card S : ℂ)⁻¹) •
            E.cqBlock z) := by
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [sub_smul]

omit [Fintype Z] [DecidableEq Z] [DecidableEq F] [Nonempty F] in
private theorem centerCoeff_pair_sum (H : HashFamily F Z S)
    (f : F) (z z' : Z) :
    (∑ s : S, H.centerCoeffR f s z * H.centerCoeffR f s z') =
      (if H.hash f z = H.hash f z' then (1 : ℝ) else 0) -
        (Fintype.card S : ℝ)⁻¹ := by
  classical
  let α : ℝ := (Fintype.card S : ℝ)⁻¹
  have hcard : (Fintype.card S : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum_indicator_left :
      (∑ s : S, (if H.hash f z = s then (1 : ℝ) else 0)) = 1 := by
    rw [Finset.sum_eq_single_of_mem (H.hash f z) (Finset.mem_univ _)]
    · simp
    · intro s _ hs
      have hne : H.hash f z ≠ s := fun h => hs h.symm
      simp [hne]
  have hsum_indicator_right :
      (∑ s : S, (if H.hash f z' = s then (1 : ℝ) else 0)) = 1 := by
    rw [Finset.sum_eq_single_of_mem (H.hash f z') (Finset.mem_univ _)]
    · simp
    · intro s _ hs
      have hne : H.hash f z' ≠ s := fun h => hs h.symm
      simp [hne]
  have hsum_pair :
      (∑ s : S,
        (if H.hash f z = s then (1 : ℝ) else 0) *
          (if H.hash f z' = s then (1 : ℝ) else 0)) =
        (if H.hash f z = H.hash f z' then (1 : ℝ) else 0) := by
    by_cases h : H.hash f z = H.hash f z'
    · rw [Finset.sum_eq_single_of_mem (H.hash f z) (Finset.mem_univ _)]
      · simp [h]
      · intro s _ hs
        have hne : H.hash f z ≠ s := fun hz => hs hz.symm
        simp [hne]
    · rw [Finset.sum_eq_single_of_mem (H.hash f z) (Finset.mem_univ _)]
      · have hsym : H.hash f z' ≠ H.hash f z := fun h' => h h'.symm
        simp [h, hsym]
      · intro s _ hs
        have hne : H.hash f z ≠ s := fun hz => hs hz.symm
        simp [hne]
  calc
    (∑ s : S, H.centerCoeffR f s z * H.centerCoeffR f s z') =
        ∑ s : S,
          ((if H.hash f z = s then (1 : ℝ) else 0) - α) *
            ((if H.hash f z' = s then (1 : ℝ) else 0) - α) := rfl
    _ = (∑ s : S,
          (if H.hash f z = s then (1 : ℝ) else 0) *
            (if H.hash f z' = s then (1 : ℝ) else 0)) -
        α * (∑ s : S, (if H.hash f z = s then (1 : ℝ) else 0)) -
        α * (∑ s : S, (if H.hash f z' = s then (1 : ℝ) else 0)) +
        (Fintype.card S : ℝ) * α * α := by
        simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring_nf
    _ = (if H.hash f z = H.hash f z' then (1 : ℝ) else 0) - α := by
        rw [hsum_pair, hsum_indicator_left, hsum_indicator_right]
        have hα : (Fintype.card S : ℝ) * α = 1 := by
          simp [α, hcard]
        rw [hα, one_mul]
        ring

omit [Fintype Z] [DecidableEq Z] [DecidableEq F] [Nonempty F] [Nonempty S] in
private theorem collisionProbability_eq_sum_collision
    (H : HashFamily F Z S) (z z' : Z) :
    H.collisionProbability z z' =
      ∑ f : F, (if H.hash f z = H.hash f z' then H.prob f else 0 : ℝ≥0) := by
  classical
  unfold collisionProbability collisionWeight
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases h : H.hash f z = H.hash f z'
  · rw [Finset.sum_eq_single_of_mem (H.hash f z) (Finset.mem_univ _)]
    · simp [h]
    · intro s _ hs
      have hne : H.hash f z ≠ s := fun hz => hs hz.symm
      simp [hne]
  · rw [Finset.sum_eq_single_of_mem (H.hash f z) (Finset.mem_univ _)]
    · have hsym : H.hash f z' ≠ H.hash f z := fun h' => h h'.symm
      simp [h, hsym]
    · intro s _ hs
      have hne : H.hash f z ≠ s := fun hz => hs hz.symm
      simp [hne]

omit [Fintype Z] [DecidableEq Z] [DecidableEq F] [Nonempty F] in
private theorem centerCoeff_pair_average_eq_collisionProbability
    (H : HashFamily F Z S) (z z' : Z) :
    (∑ f : F, (H.prob f : ℝ) *
      ∑ s : S, H.centerCoeffR f s z * H.centerCoeffR f s z') =
      (H.collisionProbability z z' : ℝ) - (Fintype.card S : ℝ)⁻¹ := by
  classical
  calc
    (∑ f : F, (H.prob f : ℝ) *
      ∑ s : S, H.centerCoeffR f s z * H.centerCoeffR f s z') =
        ∑ f : F, (H.prob f : ℝ) *
          ((if H.hash f z = H.hash f z' then (1 : ℝ) else 0) -
            (Fintype.card S : ℝ)⁻¹) := by
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [centerCoeff_pair_sum]
    _ = (∑ f : F, if H.hash f z = H.hash f z' then (H.prob f : ℝ) else 0) -
        ∑ f : F, (Fintype.card S : ℝ)⁻¹ * (H.prob f : ℝ) := by
        simp only [mul_sub, Finset.sum_sub_distrib]
        refine congrArg₂ HSub.hSub ?_ ?_
        · refine Finset.sum_congr rfl fun f _ => ?_
          by_cases h : H.hash f z = H.hash f z' <;> simp [h]
        · refine Finset.sum_congr rfl fun f _ => ?_
          ring
    _ = (∑ f : F, if H.hash f z = H.hash f z' then (H.prob f : ℝ) else 0) -
        (Fintype.card S : ℝ)⁻¹ * ∑ f : F, (H.prob f : ℝ) := by
        rw [Finset.mul_sum]
    _ = (H.collisionProbability z z' : ℝ) - (Fintype.card S : ℝ)⁻¹ := by
        rw [collisionProbability_eq_sum_collision]
        have hcast :
            ((∑ f : F,
                (if H.hash f z = H.hash f z' then H.prob f else 0 : ℝ≥0) : ℝ≥0) : ℝ) =
              ∑ f : F, if H.hash f z = H.hash f z' then (H.prob f : ℝ) else 0 := by
          simp only [NNReal.coe_sum]
          refine Finset.sum_congr rfl fun f _ => ?_
          by_cases h : H.hash f z = H.hash f z' <;> simp [h]
        rw [hcast]
        have hprob : (∑ f : F, (H.prob f : ℝ)) = 1 := by
          exact_mod_cast H.prob_sum
        rw [hprob, mul_one]

private def quad (σ : State e) (A B : CMatrix e) : ℝ :=
  ((σ.matrix⁻¹ * A * B).trace).re

omit [DecidableEq Z] in
private theorem quad_sum_smul_sum_smul_real (σ : State e)
    (A : Z → CMatrix e) (c d : Z → ℝ) :
    quad σ (∑ z : Z, (c z : ℂ) • A z) (∑ z' : Z, (d z' : ℂ) • A z') =
      ∑ z : Z, ∑ z' : Z, c z * d z' * quad σ (A z) (A z') := by
  unfold quad
  simp only [Matrix.trace_sum,
    Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  refine Finset.sum_congr rfl fun z' _ => ?_
  simp [Matrix.trace_smul, mul_assoc, mul_comm,
    mul_left_comm]

private theorem sum_reorder_four
    {F : Type uF} {S : Type uS} {Z : Type uZ}
    [Fintype F] [Fintype S] [Fintype Z]
    (p : F → ℝ) (a : F → S → Z → Z → ℝ) (q : Z → Z → ℝ) :
    (∑ f : F, p f * ∑ s : S, ∑ z : Z, ∑ z' : Z, a f s z z' * q z z') =
      ∑ z : Z, ∑ z' : Z, (∑ f : F, p f * ∑ s : S, a f s z z') * q z z' := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  conv_rhs =>
    rw [← Fintype.sum_prod_type']
    rw [← Fintype.sum_prod_type']
    rw [← Fintype.sum_prod_type']
  let e : (((F × S) × Z) × Z) ≃ (((Z × Z) × F) × S) := {
    toFun x := (((x.1.2, x.2), x.1.1.1), x.1.1.2)
    invFun y := (((y.1.2, y.2), y.1.1.1), y.1.1.2)
    left_inv x := by cases x with | mk x z' => cases x with | mk fs z => cases fs; rfl
    right_inv y := by cases y with | mk y s => cases y with | mk zz f => cases zz; rfl
  }
  refine Fintype.sum_equiv e _ _ ?_
  intro x
  simp [e, mul_comm, mul_left_comm]

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] [Nonempty S] in
@[simp]
theorem extractorSeedCenteredResidual_eq (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) (s : S) :
    H.extractorSeedCenteredResidual E f s =
      H.extractorSeedOutputBucket E f s -
        ((Fintype.card S : ℂ)⁻¹) • H.extractorCqTotalBlock E :=
  rfl

/-- Source-shaped centered quadratic witness for one seed. -/
def extractorSeedCenteredQuadraticTerm (H : HashFamily F Z S)
    (E : Ensemble Z e) (σ : State e) (f : F) : ℝ :=
  ∑ s : S,
    ((σ.matrix⁻¹ *
        H.extractorSeedCenteredResidual E f s *
          H.extractorSeedCenteredResidual E f s).trace).re

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] [Nonempty S] in
@[simp]
theorem extractorSeedCenteredQuadraticTerm_eq_sum (H : HashFamily F Z S)
    (E : Ensemble Z e) (σ : State e) (f : F) :
    H.extractorSeedCenteredQuadraticTerm E σ f =
      ∑ s : S,
        ((σ.matrix⁻¹ *
            H.extractorSeedCenteredResidual E f s *
              H.extractorSeedCenteredResidual E f s).trace).re :=
  rfl

private def outputBlock (M : CMatrix (S × e)) (s : S) : CMatrix e :=
  fun i j => M (s, i) (s, j)

omit [Fintype e] [DecidableEq e] [Fintype S] [DecidableEq S] [Nonempty S] in
private theorem outputBlock_posSemidef {M : CMatrix (S × e)}
    (hM : M.PosSemidef) (s : S) :
    (outputBlock (e := e) M s).PosSemidef := by
  simpa [outputBlock] using hM.submatrix (fun i : e => (s, i))

omit [Fintype e] [Fintype S] [Nonempty S] in
private theorem outputBlock_le_one {M : CMatrix (S × e)} (hM : M ≤ 1) (s : S) :
    outputBlock (e := e) M s ≤ 1 := by
  rw [Matrix.le_iff] at hM ⊢
  have h := hM.submatrix (fun i : e => (s, i))
  convert h using 1
  ext i j
  simp [outputBlock, Matrix.sub_apply, Matrix.one_apply]

omit [Fintype e] [DecidableEq e] [Fintype S] [DecidableEq S] [Nonempty S] in
private theorem outputBlock_isHermitian {M : CMatrix (S × e)}
    (hM : M.IsHermitian) (s : S) :
    (outputBlock (e := e) M s).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simpa [outputBlock, Matrix.conjTranspose] using
    congrFun (congrFun hM (s, i)) (s, j)

omit [DecidableEq e] [DecidableEq S] [Nonempty S] in
private theorem trace_mul_output_decomp_complex {D P : CMatrix (S × e)}
    (hoff : ∀ (s s' : S) (i j : e), s ≠ s' -> D (s, i) (s', j) = 0) :
    (D * P).trace =
      ∑ s : S, ((outputBlock (e := e) D s) * outputBlock P s).trace := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, outputBlock, Fintype.sum_prod_type]
  calc
    (∑ s : S, ∑ i : e, ∑ s' : S, ∑ j : e,
        D (s, i) (s', j) * P (s', j) (s, i)) =
      ∑ s : S, ∑ i : e, ∑ j : e,
        D (s, i) (s, j) * P (s, j) (s, i) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Finset.sum_eq_single_of_mem s (Finset.mem_univ _) (fun s' _ hs' => by
          have hne : s ≠ s' := fun h => hs' h.symm
          simp [hoff s s' i, hne])
    _ = ∑ s : S, ∑ i : e, ∑ j : e,
        D (s, i) (s, j) * P (s, j) (s, i) := rfl

omit [DecidableEq e] [DecidableEq S] [Nonempty S] in
private theorem trace_mul_output_decomp {D P : CMatrix (S × e)}
    (hoff : ∀ (s s' : S) (i j : e), s ≠ s' -> D (s, i) (s', j) = 0) :
    ((D * P).trace).re =
      ∑ s : S, (((outputBlock (e := e) D s) * outputBlock P s).trace).re := by
  rw [trace_mul_output_decomp_complex (S := S) (e := e) hoff]
  simp

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] [Fintype S] [Nonempty S] in
private theorem extractorSeedOutputMatrix_output_offdiag
    (H : HashFamily F Z S) (E : Ensemble Z e) (f : F)
    {s s' : S} {i j : e} (hss : s ≠ s') :
    extractorSeedOutputMatrix H E f (s, i) (s', j) = 0 := by
  unfold extractorSeedOutputMatrix
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  refine Finset.sum_eq_zero fun z _ => ?_
  have hsingle : Matrix.single (H.hash f z) (H.hash f z) (1 : ℂ) s s' = 0 := by
    rw [Matrix.single_apply]
    by_cases hs : H.hash f z = s
    · subst s
      simp [hss]
    · simp [hs]
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, hsingle]

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] [Nonempty S] in
private theorem extractorSeedSideInfoMatrix_eq_totalBlock
    (H : HashFamily F Z S) (E : Ensemble Z e) (f : F) :
    extractorSeedSideInfoMatrix H E f = H.extractorCqTotalBlock E := by
  ext i j
  unfold extractorSeedSideInfoMatrix extractorCqTotalBlock partialTraceA extractorSeedOutputMatrix
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  calc
    (∑ s : S, ∑ z : Z,
        (E.probs z) •
          (Matrix.kronecker
            (Matrix.single (H.hash f z) (H.hash f z) (1 : ℂ))
            (E.states z).matrix) (s, i) (s, j)) =
      ∑ z : Z, (E.probs z) • (E.states z).matrix i j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_eq_single_of_mem (H.hash f z) (Finset.mem_univ _)]
        · simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
        · intro s _ hs
          have hne : H.hash f z ≠ s := fun h => hs h.symm
          simp [Matrix.kronecker, Matrix.kroneckerMap_apply, hne]
    _ = (∑ z : Z, E.cqBlock z) i j := by
        rw [Matrix.sum_apply]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Ensemble.cqBlock_eq]
        simp [NNReal.smul_def]
    _ = ∑ z : Z, E.cqBlock z i j := by
        rw [Matrix.sum_apply]

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] in
private theorem extractorSeedIdealMatrix_output_offdiag
    (H : HashFamily F Z S) (E : Ensemble Z e) (f : F)
    {s s' : S} {i j : e} (hss : s ≠ s') :
    extractorSeedIdealMatrix H E f (s, i) (s', j) = 0 := by
  unfold extractorSeedIdealMatrix
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.diagonal, hss]

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] in
private theorem extractorSeedDiff_output_offdiag
    (H : HashFamily F Z S) (E : Ensemble Z e) (f : F)
    {s s' : S} {i j : e} (hss : s ≠ s') :
    (extractorSeedOutputMatrix H E f - extractorSeedIdealMatrix H E f)
        (s, i) (s', j) = 0 := by
  rw [Matrix.sub_apply, extractorSeedOutputMatrix_output_offdiag H E f hss,
    extractorSeedIdealMatrix_output_offdiag H E f hss]
  simp

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] in
private theorem outputBlock_seedDiff_eq_centeredResidual
    (H : HashFamily F Z S) (E : Ensemble Z e) (f : F) (s : S) :
    outputBlock (e := e)
        (extractorSeedOutputMatrix H E f - extractorSeedIdealMatrix H E f) s =
      H.extractorSeedCenteredResidual E f s := by
  ext i j
  unfold outputBlock extractorSeedCenteredResidual
  simp only [Matrix.sub_apply, Matrix.smul_apply]
  have hside := congrFun (congrFun (extractorSeedSideInfoMatrix_eq_totalBlock H E f) i) j
  have hout :
      extractorSeedOutputMatrix H E f (s, i) (s, j) =
        (H.extractorSeedOutputBucket E f s) i j := by
    unfold extractorSeedOutputMatrix extractorSeedOutputBucket
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Ensemble.cqBlock_eq]
    by_cases hz : H.hash f z = s
    · simp [hz, NNReal.smul_def]
    · simp [hz]
  have hideal :
      extractorSeedIdealMatrix H E f (s, i) (s, j) =
        (((Fintype.card S : ℂ)⁻¹) • H.extractorCqTotalBlock E) i j := by
    unfold extractorSeedIdealMatrix
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply]
    rw [hside]
    simp [uniformExtractorOutputState_matrix, uniformExtractorOutputProb, Matrix.diagonal]
  rw [hout, hideal]
  rfl

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] [Nonempty S] in
private theorem extractorSeedOutputMatrix_trace_local (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) :
    (extractorSeedOutputMatrix H E f).trace = 1 := by
  unfold extractorSeedOutputMatrix
  simp only [Matrix.trace_sum, Matrix.trace_smul]
  calc
    (∑ z : Z, (E.probs z) •
        (Matrix.kronecker (Matrix.single (H.hash f z) (H.hash f z) (1 : ℂ))
          (E.states z).matrix).trace) =
      ∑ z : Z, ((E.probs z : ℝ≥0) : ℂ) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        have htrace :
            (Matrix.kronecker (Matrix.single (H.hash f z) (H.hash f z) (1 : ℂ))
              (E.states z).matrix).trace = 1 := by
          simpa [Matrix.kronecker] using
            (Matrix.trace_kronecker
              (Matrix.single (H.hash f z) (H.hash f z) (1 : ℂ))
              (E.states z).matrix).trans
              (by rw [trace_single_one, if_pos rfl, (E.states z).trace_eq_one]; norm_num)
        rw [htrace]
        exact (Algebra.algebraMap_eq_smul_one _).symm
    _ = ↑(∑ z : Z, E.probs z) := by simp
    _ = 1 := by rw [E.weights_sum]; rfl

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] [Nonempty S] in
private theorem extractorSeedOutputMatrix_posSemidef_local (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) :
    (extractorSeedOutputMatrix H E f).PosSemidef := by
  unfold extractorSeedOutputMatrix
  exact Matrix.posSemidef_sum Finset.univ fun z _ =>
    (((posSemidef_single (H.hash f z)).kronecker (E.states z).pos).smul
      (NNReal.coe_nonneg (E.probs z)))

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] in
private theorem extractorSeedIdealMatrix_trace_local (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) :
    (extractorSeedIdealMatrix H E f).trace = 1 := by
  unfold extractorSeedIdealMatrix extractorSeedSideInfoMatrix
  rw [show (Matrix.kronecker (uniformExtractorOutputState (S := S)).matrix
      (partialTraceA (extractorSeedOutputMatrix H E f))).trace =
        (uniformExtractorOutputState (S := S)).matrix.trace *
          (partialTraceA (extractorSeedOutputMatrix H E f)).trace by
    simpa [Matrix.kronecker] using
      Matrix.trace_kronecker (uniformExtractorOutputState (S := S)).matrix
        (partialTraceA (extractorSeedOutputMatrix H E f))]
  rw [uniformExtractorOutputState_matrix]
  have hU : (Matrix.diagonal fun s : S => (uniformExtractorOutputProb (S := S) s : ℂ)).trace = 1 := by
    change (uniformExtractorOutputState (S := S)).matrix.trace = 1
    exact (uniformExtractorOutputState (S := S)).trace_eq_one
  rw [hU, partialTraceA_trace, extractorSeedOutputMatrix_trace_local H E f]
  norm_num

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] in
private theorem extractorSeedIdealMatrix_posSemidef_local (H : HashFamily F Z S)
    (E : Ensemble Z e) (f : F) :
    (extractorSeedIdealMatrix H E f).PosSemidef := by
  unfold extractorSeedIdealMatrix extractorSeedSideInfoMatrix
  exact (uniformExtractorOutputState (S := S)).pos.kronecker
    (partialTraceA_posSemidef (extractorSeedOutputMatrix_posSemidef_local H E f))

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] in
private theorem seedDiff_trace_zero_local (H : HashFamily F Z S) (E : Ensemble Z e) (f : F) :
    (extractorSeedOutputMatrix H E f - extractorSeedIdealMatrix H E f).trace = 0 := by
  rw [Matrix.trace_sub, extractorSeedOutputMatrix_trace_local H E f,
    extractorSeedIdealMatrix_trace_local H E f]
  norm_num

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] in
private theorem seedDiff_isHermitian_local (H : HashFamily F Z S) (E : Ensemble Z e) (f : F) :
    (extractorSeedOutputMatrix H E f - extractorSeedIdealMatrix H E f).IsHermitian :=
  (extractorSeedOutputMatrix_posSemidef_local H E f).isHermitian.sub
    (extractorSeedIdealMatrix_posSemidef_local H E f).isHermitian

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] in
private theorem normalizedTraceDistance_eq_posPart_trace_of_seedDiff_local
    (H : HashFamily F Z S) (E : Ensemble Z e) (f : F) :
    normalizedTraceDistance (extractorSeedOutputMatrix H E f) (extractorSeedIdealMatrix H E f) =
      (((extractorSeedOutputMatrix H E f - extractorSeedIdealMatrix H E f)⁺).trace).re := by
  let D : CMatrix (S × e) := extractorSeedOutputMatrix H E f - extractorSeedIdealMatrix H E f
  have hnorm := traceNorm_eq_two_posPart_trace_re_of_trace_zero D
    (by simpa [D] using seedDiff_isHermitian_local H E f)
    (by simpa [D] using seedDiff_trace_zero_local H E f)
  calc
    normalizedTraceDistance (extractorSeedOutputMatrix H E f) (extractorSeedIdealMatrix H E f) =
        (1 / 2 : ℝ) * traceNorm D := by rfl
    _ = (1 / 2 : ℝ) * (2 * (D⁺).trace.re) := by rw [hnorm]
    _ = (D⁺).trace.re := by ring

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] in
/-- Centered per-seed quadratic terms are nonnegative under a positive-definite reference state. -/
theorem extractorSeedCenteredQuadraticTerm_nonneg_of_posDef
    (H : HashFamily F Z S) (E : Ensemble Z e) (σ : State e) (f : F)
    (hσ : σ.matrix.PosDef) :
    0 ≤ H.extractorSeedCenteredQuadraticTerm E σ f := by
  unfold extractorSeedCenteredQuadraticTerm
  refine Finset.sum_nonneg fun s _ => ?_
  have hR :
      (H.extractorSeedCenteredResidual E f s).IsHermitian := by
    have hblock :=
      outputBlock_isHermitian (S := S) (e := e) (seedDiff_isHermitian_local H E f) s
    rw [← outputBlock_seedDiff_eq_centeredResidual H E f s]
    exact hblock
  exact cMatrix_inv_mul_self_trace_nonneg_of_hermitian_posDef hR hσ

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] in
private theorem posPart_trace_seedDiff_le_sum_centered_sqrt
    (H : HashFamily F Z S) (E : Ensemble Z e) (σ : State e) (f : F)
    (hσ : σ.matrix.PosDef) :
    (((extractorSeedOutputMatrix H E f - extractorSeedIdealMatrix H E f)⁺).trace).re ≤
      ∑ s : S, Real.sqrt (((σ.matrix⁻¹ *
        H.extractorSeedCenteredResidual E f s *
          H.extractorSeedCenteredResidual E f s).trace).re) := by
  classical
  let D : CMatrix (S × e) :=
    extractorSeedOutputMatrix H E f - extractorSeedIdealMatrix H E f
  have hD : D.IsHermitian := by
    simpa [D] using seedDiff_isHermitian_local H E f
  let P : CMatrix (S × e) := positiveSpectralProjector D hD
  have hscore : ((D * P).trace).re = (D⁺).trace.re := by
    simpa [P] using positiveSpectralProjector_score_eq_posPart_trace D hD
  calc
    (D⁺).trace.re = ((D * P).trace).re := hscore.symm
    _ = ∑ s : S, (((outputBlock (e := e) D s) * outputBlock P s).trace).re := by
      exact trace_mul_output_decomp (S := S) (e := e) (D := D) (P := P) (by
        intro s s' i j hss
        dsimp [D]
        simpa using extractorSeedDiff_output_offdiag H E f (s := s) (s' := s')
          (i := i) (j := j) hss)
    _ ≤ ∑ s : S, Real.sqrt (((σ.matrix⁻¹ *
        H.extractorSeedCenteredResidual E f s *
          H.extractorSeedCenteredResidual E f s).trace).re) := by
      refine Finset.sum_le_sum fun s _ => ?_
      have hblock : outputBlock (e := e) D s = H.extractorSeedCenteredResidual E f s := by
        dsimp [D]
        simpa using outputBlock_seedDiff_eq_centeredResidual H E f s
      rw [hblock]
      have hR :
          (H.extractorSeedCenteredResidual E f s).IsHermitian := by
        have hblockHerm := outputBlock_isHermitian (S := S) (e := e) hD s
        simpa [hblock] using hblockHerm
      have hPpos : (outputBlock (e := e) P s).PosSemidef :=
        outputBlock_posSemidef (S := S) (e := e)
          (positiveSpectralProjector_posSemidef D hD) s
      have hPle : outputBlock (e := e) P s ≤ 1 :=
        outputBlock_le_one (S := S) (e := e)
          (positiveSpectralProjector_le_one D hD) s
      have hσtr : σ.matrix.trace.re = 1 := by
        rw [σ.trace_eq_one]
        norm_num
      exact cMatrix_trace_mul_effect_re_le_sqrt_quadratic hR hσ hPpos hPle hσtr

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] in
/--
Per-seed Holder/Schatten bridge for the direct extractor proof route.

For a positive-definite side-information reference state, the per-seed
normalized trace distance is bounded by the square root of `|S|` times the
centered residual quadratic term.
-/
theorem extractorSeedTraceDistance_le_sqrt_card_mul_centeredQuadraticTerm_posDef
    (H : HashFamily F Z S) (E : Ensemble Z e) (σ : State e) (f : F)
    (hσ : σ.matrix.PosDef) :
    extractorSeedTraceDistance H E f ≤
      Real.sqrt ((Fintype.card S : ℝ) * H.extractorSeedCenteredQuadraticTerm E σ f) := by
  classical
  let q : S → ℝ := fun s =>
    ((σ.matrix⁻¹ *
      H.extractorSeedCenteredResidual E f s *
        H.extractorSeedCenteredResidual E f s).trace).re
  have hq : ∀ s, 0 ≤ q s := by
    intro s
    have hR :
        (H.extractorSeedCenteredResidual E f s).IsHermitian := by
      have hblock :=
        outputBlock_isHermitian (S := S) (e := e) (seedDiff_isHermitian_local H E f) s
      rw [← outputBlock_seedDiff_eq_centeredResidual H E f s]
      exact hblock
    simpa [q] using cMatrix_inv_mul_self_trace_nonneg_of_hermitian_posDef hR hσ
  have hpos_le :=
    posPart_trace_seedDiff_le_sum_centered_sqrt H E σ f hσ
  have hsum :
      (∑ s : S, Real.sqrt (q s)) ≤
        Real.sqrt ((Fintype.card S : ℝ) * ∑ s : S, q s) := by
    have hcauchy :=
      Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset S)
        (f := fun _ : S => (1 : ℝ)) (g := q)
        (by intro s; norm_num) hq
    have hleft :
        (∑ x ∈ (Finset.univ : Finset S), Real.sqrt (1 : ℝ) * Real.sqrt (q x)) =
          ∑ s : S, Real.sqrt (q s) := by simp
    have hright :
        Real.sqrt (∑ x ∈ (Finset.univ : Finset S), (1 : ℝ)) *
            Real.sqrt (∑ x ∈ (Finset.univ : Finset S), q x) =
          Real.sqrt ((Fintype.card S : ℝ) * ∑ s : S, q s) := by
        rw [Finset.sum_const, Finset.card_univ]
        rw [nsmul_eq_mul]
        simp only [mul_one]
        rw [Real.sqrt_mul (by positivity : 0 ≤ (Fintype.card S : ℝ))]
    simpa [hleft, hright] using hcauchy
  calc
    extractorSeedTraceDistance H E f =
        (((extractorSeedOutputMatrix H E f - extractorSeedIdealMatrix H E f)⁺).trace).re := by
          rw [extractorSeedTraceDistance,
            normalizedTraceDistance_eq_posPart_trace_of_seedDiff_local H E f]
    _ ≤ ∑ s : S, Real.sqrt (q s) := by
          simpa [q] using hpos_le
    _ ≤ Real.sqrt ((Fintype.card S : ℝ) * ∑ s : S, q s) := hsum
    _ = Real.sqrt ((Fintype.card S : ℝ) * H.extractorSeedCenteredQuadraticTerm E σ f) := by
          simp [q, extractorSeedCenteredQuadraticTerm]

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] [Nonempty S] in
private theorem extractorSeedCenteredQuadraticTerm_eq_coeff_sum
    (H : HashFamily F Z S) (E : Ensemble Z e) (σ : State e) (f : F) :
    H.extractorSeedCenteredQuadraticTerm E σ f =
      ∑ s : S, ∑ z : Z, ∑ z' : Z,
        H.centerCoeffR f s z * H.centerCoeffR f s z' *
          quad σ (E.cqBlock z) (E.cqBlock z') := by
  classical
  unfold extractorSeedCenteredQuadraticTerm
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [extractorSeedCenteredResidual_eq_centerCoeff_sum]
  simp_rw [centerCoeffC_eq_ofReal]
  simpa [quad] using
    quad_sum_smul_sum_smul_real (Z := Z) (e := e) σ
      (fun z => E.cqBlock z) (fun z => H.centerCoeffR f s z)
      (fun z => H.centerCoeffR f s z)

omit [DecidableEq Z] [DecidableEq F] [Nonempty F] in
private theorem extractorSeedCenteredQuadraticAverage_eq_pair_sum
    (H : HashFamily F Z S) (E : Ensemble Z e) (σ : State e) :
    extractorSeedQuadraticAverage H (fun f => H.extractorSeedCenteredQuadraticTerm E σ f) =
      ∑ z : Z, ∑ z' : Z,
        ((H.collisionProbability z z' : ℝ) - (Fintype.card S : ℝ)⁻¹) *
          quad σ (E.cqBlock z) (E.cqBlock z') := by
  classical
  unfold extractorSeedQuadraticAverage
  simp_rw [extractorSeedCenteredQuadraticTerm_eq_coeff_sum]
  rw [sum_reorder_four (p := fun f => (H.prob f : ℝ))
    (a := fun f s z z' => H.centerCoeffR f s z * H.centerCoeffR f s z')
    (q := fun z z' => quad σ (E.cqBlock z) (E.cqBlock z'))]
  refine Finset.sum_congr rfl fun z _ => ?_
  refine Finset.sum_congr rfl fun z' _ => ?_
  rw [centerCoeff_pair_average_eq_collisionProbability]

omit [DecidableEq Z] in
private theorem cqBlock_posSemidef (E : Ensemble Z e) (z : Z) :
    (E.cqBlock z).PosSemidef := by
  rw [Ensemble.cqBlock_eq]
  exact (E.states z).pos.smul (by exact_mod_cast NNReal.coe_nonneg (E.probs z))

omit [DecidableEq Z] in
private theorem quad_cqBlock_self_nonneg_of_posDef
    (E : Ensemble Z e) (σ : State e) (hσ : σ.matrix.PosDef) (z : Z) :
    0 ≤ quad σ (E.cqBlock z) (E.cqBlock z) := by
  classical
  let A : CMatrix e := E.cqBlock z
  have hA : A.PosSemidef := by
    simpa [A] using cqBlock_posSemidef (E := E) z
  have hpsd : (A * σ.matrix⁻¹ * A).PosSemidef := by
    have h := hσ.inv.posSemidef.mul_mul_conjTranspose_same A
    simpa [hA.isHermitian.eq, Matrix.mul_assoc] using h
  have htrace : 0 ≤ ((A * σ.matrix⁻¹ * A).trace).re :=
    (Matrix.PosSemidef.trace_nonneg hpsd).1
  have hcyc : (σ.matrix⁻¹ * A * A).trace = (A * σ.matrix⁻¹ * A).trace := by
    calc
      (σ.matrix⁻¹ * A * A).trace = ((σ.matrix⁻¹ * A) * A).trace := by
        rw [Matrix.mul_assoc]
      _ = (A * (σ.matrix⁻¹ * A)).trace := by rw [Matrix.trace_mul_comm]
      _ = (A * σ.matrix⁻¹ * A).trace := by rw [Matrix.mul_assoc]
  unfold quad
  change 0 ≤ ((σ.matrix⁻¹ * A * A).trace).re
  rw [hcyc]
  exact htrace

omit [DecidableEq F] [Nonempty F] in
/--
Collision-uniform centered residual collapse for the direct extractor route.

Under the exact off-diagonal collision probability `1 / |S|`, the seed average
of the centered residual quadratic keeps only diagonal cq-block terms.  The
remaining factor `1 - 1 / |S|` is at most `1`, and the diagonal terms are
nonnegative when the side-information reference state is positive definite.
-/
theorem extractorSeedCenteredQuadraticAverage_le_cqQuadratic_of_collisionUniform_posDef
    (H : HashFamily F Z S) (E : Ensemble Z e) (σ : State e)
    (hH : H.CollisionUniform) (hσ : σ.matrix.PosDef) :
    extractorSeedQuadraticAverage H (fun f => H.extractorSeedCenteredQuadraticTerm E σ f) ≤
      extractorCqQuadraticTerm E σ := by
  classical
  let α : ℝ := (Fintype.card S : ℝ)⁻¹
  have hcard_ge_one : (1 : ℝ) ≤ (Fintype.card S : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hα_le_one : α ≤ 1 := by
    exact inv_le_one_of_one_le₀ hcard_ge_one
  have hα_nonneg : 0 ≤ α := by
    positivity
  have hcollapsed :
      (∑ z : Z, ∑ z' : Z,
        ((H.collisionProbability z z' : ℝ) - α) *
          quad σ (E.cqBlock z) (E.cqBlock z')) =
        ∑ z : Z, (1 - α) * quad σ (E.cqBlock z) (E.cqBlock z) := by
    calc
      (∑ z : Z, ∑ z' : Z,
        ((H.collisionProbability z z' : ℝ) - α) *
          quad σ (E.cqBlock z) (E.cqBlock z')) =
          ∑ z : Z, ∑ z' : Z,
            (if z = z' then 1 - α else 0) *
              quad σ (E.cqBlock z) (E.cqBlock z') := by
          refine Finset.sum_congr rfl fun z _ => ?_
          refine Finset.sum_congr rfl fun z' _ => ?_
          by_cases hzz : z = z'
          · subst z'
            have hself : ((H.collisionProbability z z : ℝ) = 1) := by
              exact_mod_cast H.collisionProbability_self z
            rw [hself]
            simp
          · have hoff :
                (H.collisionProbability z z' : ℝ) = α := by
              have hnn := hH z z' hzz
              rw [hnn]
              simp [α]
            rw [hoff]
            simp [hzz]
      _ = ∑ z : Z, (1 - α) * quad σ (E.cqBlock z) (E.cqBlock z) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.sum_eq_single_of_mem z (Finset.mem_univ _)]
          · simp
          · intro z' _ hne
            have hne' : z ≠ z' := fun h => hne h.symm
            simp [hne']
  calc
    extractorSeedQuadraticAverage H (fun f => H.extractorSeedCenteredQuadraticTerm E σ f)
        = ∑ z : Z, ∑ z' : Z,
            ((H.collisionProbability z z' : ℝ) - α) *
              quad σ (E.cqBlock z) (E.cqBlock z') := by
          simpa [α] using extractorSeedCenteredQuadraticAverage_eq_pair_sum H E σ
    _ = ∑ z : Z, (1 - α) * quad σ (E.cqBlock z) (E.cqBlock z) := hcollapsed
    _ ≤ ∑ z : Z, quad σ (E.cqBlock z) (E.cqBlock z) := by
          refine Finset.sum_le_sum fun z _ => ?_
          have hq := quad_cqBlock_self_nonneg_of_posDef (E := E) (σ := σ) hσ z
          have hfactor : 1 - α ≤ 1 := by linarith
          nlinarith [mul_le_mul_of_nonneg_right hfactor hq]
    _ = extractorCqQuadraticTerm E σ := by
          simp [extractorCqQuadraticTerm, quad]

end HashFamily

end

end QIT.Security
