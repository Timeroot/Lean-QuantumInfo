/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Additivity.Basic

/-!
# Weighted Sion bridge for sandwiched EA additivity

This module is part of the Khatri--Wilde sandwiched-Renyi additivity proof
spine for entanglement-assisted classical communication.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Pointwise

namespace QIT

universe u1 v1 u2 v2

noncomputable section

namespace State

/-- Raw weighted matrix form of the KW Sion trace bracket
`Tr[(A_A ⊗ σ_B^{-p} ⊗ τ_C^p) R]`.

The reusable minimax theorem in `ConditionalRenyiMinimax` treats the special
case `A_A = I_A`.  The sandwiched mutual-information alternate expression in
KW `EA_capacity.tex:2020-2025` instead keeps the fixed marginal weight
`rho_A^((1 - alpha) / alpha)` on the `A` leg, so this definition records the
exact source-shaped bracket before the remaining fixed-weight Sion layer is
proved. -/
def abcWeightedSidePowerTraceRe
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (A : CMatrix a) (R : CMatrix (Prod (Prod a b) c))
    (σ : CMatrix b) (τ : CMatrix c) (p : ℝ) : ℝ :=
  ((Matrix.kronecker (Matrix.kronecker A (CFC.rpow σ (-p)))
      (CFC.rpow τ p) * R).trace).re

/-- The fixed-`A` KW trace bracket is nonnegative on PSD inputs. -/
theorem abcWeightedSidePowerTraceRe_nonneg
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    {A : CMatrix a} (hA : A.PosSemidef)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    {σ : CMatrix b} (hσ : σ.PosSemidef)
    {τ : CMatrix c} (hτ : τ.PosSemidef) (p : ℝ) :
    0 ≤ abcWeightedSidePowerTraceRe (a := a) A R σ τ p := by
  let S : CMatrix b := CFC.rpow σ (-p)
  let T : CMatrix c := CFC.rpow τ p
  have hS : S.PosSemidef := cMatrix_rpow_posSemidef (A := σ) (s := -p) hσ
  have hT : T.PosSemidef := cMatrix_rpow_posSemidef (A := τ) (s := p) hτ
  have hleft : (Matrix.kronecker A S).PosSemidef := hA.kronecker hS
  have hfull : (Matrix.kronecker (Matrix.kronecker A S) T).PosSemidef :=
    hleft.kronecker hT
  simpa [abcWeightedSidePowerTraceRe, S, T] using
    cMatrix_trace_mul_posSemidef_re_nonneg hfull hR

/-- The existing unweighted Sion bracket is the identity-weight instance of
the fixed-`A` bracket. -/
theorem abcWeightedSidePowerTraceRe_one
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (R : CMatrix (Prod (Prod a b) c)) (σ : CMatrix b) (τ : CMatrix c) (p : ℝ) :
    abcWeightedSidePowerTraceRe (a := a) (b := b) (c := c)
        (1 : CMatrix a) R σ τ p =
      abcSidePowerTraceRe (a := a) R σ τ p := by
  rfl

private theorem trace_weighted_kronecker_right_add_smul_add_smul_re
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [Fintype b] [Fintype c]
    (K : CMatrix (Prod a b)) (R : CMatrix (Prod (Prod a b) c))
    (T U V : CMatrix c) (s t : ℝ) :
    ((Matrix.kronecker K (T + (s • U + t • V)) * R).trace).re =
      ((Matrix.kronecker K T * R).trace).re +
        (s * ((Matrix.kronecker K U * R).trace).re +
          t * ((Matrix.kronecker K V * R).trace).re) := by
  unfold Matrix.kronecker
  rw [Matrix.kronecker_add K T (s • U + t • V)]
  rw [Matrix.kronecker_add K (s • U) (t • V)]
  rw [Matrix.kronecker_smul s K U, Matrix.kronecker_smul t K V]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.smul_re, smul_eq_mul]

private theorem trace_weighted_kronecker_middle_add_smul_add_smul_re
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [Fintype b] [Fintype c]
    (A : CMatrix a) (R : CMatrix (Prod (Prod a b) c)) (K : CMatrix c)
    (T U V : CMatrix b) (s t : ℝ) :
    ((Matrix.kronecker (Matrix.kronecker A (T + (s • U + t • V))) K *
          R).trace).re =
      ((Matrix.kronecker (Matrix.kronecker A T) K * R).trace).re +
        (s * ((Matrix.kronecker (Matrix.kronecker A U) K * R).trace).re +
          t * ((Matrix.kronecker (Matrix.kronecker A V) K * R).trace).re) := by
  unfold Matrix.kronecker
  rw [Matrix.kroneckerMap_add_right (fun x y : ℂ => x * y)
    (by intro x y z; exact mul_add x y z) A T (s • U + t • V)]
  rw [Matrix.kroneckerMap_add_left (fun x y : ℂ => x * y)
    (by intro x y z; exact add_mul x y z)
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) A T)
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) A (s • U + t • V))
    K]
  rw [Matrix.kroneckerMap_add_right (fun x y : ℂ => x * y)
    (by intro x y z; exact mul_add x y z) A (s • U) (t • V)]
  rw [Matrix.kroneckerMap_add_left (fun x y : ℂ => x * y)
    (by intro x y z; exact add_mul x y z)
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) A (s • U))
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) A (t • V))
    K]
  rw [Matrix.kroneckerMap_smul_right (fun x y : ℂ => x * y) s
    (by intro x y; exact mul_smul_comm s x y) A U]
  rw [Matrix.kroneckerMap_smul_right (fun x y : ℂ => x * y) t
    (by intro x y; exact mul_smul_comm t x y) A V]
  rw [Matrix.kroneckerMap_smul_left (fun x y : ℂ => x * y) s
    (by intro x y; exact smul_mul_assoc s x y)
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) A U) K]
  rw [Matrix.kroneckerMap_smul_left (fun x y : ℂ => x * y) t
    (by intro x y; exact smul_mul_assoc t x y)
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) A V) K]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.smul_re, smul_eq_mul]

private theorem trace_weighted_kronecker_right_continuous
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [Fintype b] [Fintype c]
    (K : CMatrix (Prod a b)) (R : CMatrix (Prod (Prod a b) c)) :
    Continuous fun T : CMatrix c => ((Matrix.kronecker K T * R).trace).re := by
  have hkr :
      Continuous fun T : CMatrix c => Matrix.kronecker K T := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply] using
        continuous_const.mul (continuous_id.matrix_elem x.2 y.2)
  exact Complex.continuous_re.comp
    (Continuous.matrix_trace (hkr.matrix_mul continuous_const))

private theorem trace_weighted_kronecker_middle_continuous
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [Fintype b] [Fintype c]
    (A : CMatrix a) (R : CMatrix (Prod (Prod a b) c)) (K : CMatrix c) :
    Continuous fun T : CMatrix b =>
      ((Matrix.kronecker (Matrix.kronecker A T) K * R).trace).re := by
  have hinner :
      Continuous fun T : CMatrix b => Matrix.kronecker A T := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply] using
        continuous_const.mul (continuous_id.matrix_elem x.2 y.2)
  have hkr :
      Continuous fun T : CMatrix b => Matrix.kronecker (Matrix.kronecker A T) K := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply] using
        ((hinner.matrix_elem x.1 y.1).mul continuous_const)
  exact Complex.continuous_re.comp
    (Continuous.matrix_trace (hkr.matrix_mul continuous_const))

/-- The fixed-`A` KW bracket is concave in the positive-power side variable. -/
theorem abcWeightedSidePowerTraceRe_concaveOn_tau
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    {A : CMatrix a} (hA : A.PosSemidef)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    {σ : CMatrix b} (hσ : σ.PosSemidef)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ConcaveOn ℝ ({τ : CMatrix c | τ.PosSemidef} : Set (CMatrix c))
      (fun τ : CMatrix c => abcWeightedSidePowerTraceRe (a := a) A R σ τ p) := by
  constructor
  · intro x hx y hy s t hs ht hst
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hx hs)
      (Matrix.PosSemidef.smul hy ht)
  · intro x hx y hy s t hs ht hst
    let S : CMatrix b := CFC.rpow σ (-p)
    let K : CMatrix (Prod a b) := Matrix.kronecker A S
    let T : CMatrix c := CFC.rpow (s • x + t • y) p
    let U : CMatrix c := CFC.rpow x p
    let V : CMatrix c := CFC.rpow y p
    let D : CMatrix c :=
      T + ((-s) • U + (-t) • V)
    have hpow :=
      (cMatrix_rpow_concaveOn_posSemidef_of_pos (a := c) hp0 hp1).2 hx hy hs ht hst
    have hdiff_nonneg :
        0 ≤ CFC.rpow (s • x + t • y) p -
          (s • CFC.rpow x p + t • CFC.rpow y p) := by
      exact sub_nonneg.mpr hpow
    have hD_nonneg : 0 ≤ D := by
      simpa [D, T, U, V, sub_eq_add_neg, neg_add_rev, add_comm, add_left_comm, add_assoc]
        using hdiff_nonneg
    have hD : D.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hD_nonneg
    have hS : S.PosSemidef :=
      cMatrix_rpow_posSemidef (A := σ) (s := -p) hσ
    have hleft : K.PosSemidef :=
      hA.kronecker hS
    have hfull : (Matrix.kronecker K D).PosSemidef :=
      hleft.kronecker hD
    have htrace := cMatrix_trace_mul_posSemidef_re_nonneg hfull hR
    change 0 ≤ ((Matrix.kronecker K D * R).trace).re at htrace
    have htrace' :
        0 ≤ abcWeightedSidePowerTraceRe (a := a) A R σ (s • x + t • y) p +
          (-s * abcWeightedSidePowerTraceRe (a := a) A R σ x p +
            -t * abcWeightedSidePowerTraceRe (a := a) A R σ y p) := by
      rw [trace_weighted_kronecker_right_add_smul_add_smul_re K R T U V (-s) (-t)]
        at htrace
      have hT :
          ((Matrix.kronecker K T * R).trace).re =
            abcWeightedSidePowerTraceRe (a := a) A R σ (s • x + t • y) p := by
        simp [abcWeightedSidePowerTraceRe, K, S, T]
      have hU :
          ((Matrix.kronecker K U * R).trace).re =
            abcWeightedSidePowerTraceRe (a := a) A R σ x p := by
        simp [abcWeightedSidePowerTraceRe, K, S, U]
      have hV :
          ((Matrix.kronecker K V * R).trace).re =
            abcWeightedSidePowerTraceRe (a := a) A R σ y p := by
        simp [abcWeightedSidePowerTraceRe, K, S, V]
      rw [hT, hU, hV] at htrace
      exact htrace
    have hle :
        s * abcWeightedSidePowerTraceRe (a := a) A R σ x p +
          t * abcWeightedSidePowerTraceRe (a := a) A R σ y p ≤
            abcWeightedSidePowerTraceRe (a := a) A R σ (s • x + t • y) p := by
      nlinarith
    simpa [smul_eq_mul] using hle

/-- The fixed-`A` KW bracket is quasiconcave in the positive-power side variable. -/
theorem abcWeightedSidePowerTraceRe_quasiconcaveOn_tau
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    {A : CMatrix a} (hA : A.PosSemidef)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    {σ : CMatrix b} (hσ : σ.PosSemidef)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    QuasiconcaveOn ℝ ({τ : CMatrix c | τ.PosSemidef} : Set (CMatrix c))
      (fun τ : CMatrix c => abcWeightedSidePowerTraceRe (a := a) A R σ τ p) :=
  (abcWeightedSidePowerTraceRe_concaveOn_tau (a := a) hA hR hσ hp0 hp1).quasiconcaveOn

/-- Continuity of the fixed-`A` KW bracket in the positive-power side variable. -/
theorem abcWeightedSidePowerTraceRe_continuousOn_tau_posSemidef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (A : CMatrix a) (R : CMatrix (Prod (Prod a b) c)) (σ : CMatrix b)
    {p : ℝ} (hp0 : 0 < p) :
    ContinuousOn
      (fun τ : CMatrix c => abcWeightedSidePowerTraceRe (a := a) A R σ τ p)
      ({τ : CMatrix c | τ.PosSemidef} : Set (CMatrix c)) := by
  let K : CMatrix (Prod a b) := Matrix.kronecker A (CFC.rpow σ (-p))
  have htrace := trace_weighted_kronecker_right_continuous (a := a) (b := b) K R
  have hpow := cMatrix_rpow_continuousOn_posSemidef_of_pos (a := c) hp0
  simpa [abcWeightedSidePowerTraceRe, K, Function.comp_def] using
    htrace.comp_continuousOn hpow

/-- Lower semicontinuity of the fixed-`A` KW bracket in the negative-power side
variable on the PSD cone. -/
theorem abcWeightedSidePowerTraceRe_lowerSemicontinuousOn_tau_posSemidef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (A : CMatrix a) (R : CMatrix (Prod (Prod a b) c)) (σ : CMatrix b)
    {p : ℝ} (hp0 : 0 < p) :
    LowerSemicontinuousOn
      (fun τ : CMatrix c => abcWeightedSidePowerTraceRe (a := a) A R σ τ p)
      ({τ : CMatrix c | τ.PosSemidef} : Set (CMatrix c)) :=
  ContinuousOn.lowerSemicontinuousOn
    (abcWeightedSidePowerTraceRe_continuousOn_tau_posSemidef (a := a) A R σ hp0)

/-- Upper semicontinuity of the fixed-`A` KW bracket in the positive-power side
variable on the PSD cone. -/
theorem abcWeightedSidePowerTraceRe_upperSemicontinuousOn_tau_posSemidef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (A : CMatrix a) (R : CMatrix (Prod (Prod a b) c)) (σ : CMatrix b)
    {p : ℝ} (hp0 : 0 < p) :
    UpperSemicontinuousOn
      (fun τ : CMatrix c => abcWeightedSidePowerTraceRe (a := a) A R σ τ p)
      ({τ : CMatrix c | τ.PosSemidef} : Set (CMatrix c)) :=
  ContinuousOn.upperSemicontinuousOn
    (abcWeightedSidePowerTraceRe_continuousOn_tau_posSemidef (a := a) A R σ hp0)

/-- The fixed-`A` KW bracket is convex in the negative-power side variable on
the positive-definite cone. -/
theorem abcWeightedSidePowerTraceRe_convexOn_sigma_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    {A : CMatrix a} (hA : A.PosSemidef)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    {τ : CMatrix c} (hτ : τ.PosSemidef)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ConvexOn ℝ ({σ : CMatrix b | σ.PosDef} : Set (CMatrix b))
      (fun σ : CMatrix b => abcWeightedSidePowerTraceRe (a := a) A R σ τ p) := by
  constructor
  · exact posDefMatrixSet_convex (a := b)
  · intro x hx y hy s t hs ht hst
    let S : CMatrix b := CFC.rpow (s • x + t • y) (-p)
    let U : CMatrix b := CFC.rpow x (-p)
    let V : CMatrix b := CFC.rpow y (-p)
    let T : CMatrix c := CFC.rpow τ p
    let D : CMatrix b := (-1 : ℝ) • S + (s • U + t • V)
    have hp_neg : -p ∈ Set.Icc (-1 : ℝ) 0 := by
      constructor <;> linarith
    have hpow :=
      (cMatrix_rpow_convexOn_posDef_of_mem_Icc_neg_one_zero (a := b) hp_neg).2
        hx hy hs ht hst
    have hdiff_nonneg :
        0 ≤ (s • CFC.rpow x (-p) + t • CFC.rpow y (-p)) -
          CFC.rpow (s • x + t • y) (-p) := by
      exact sub_nonneg.mpr hpow
    have hD_nonneg : 0 ≤ D := by
      simpa [D, S, U, V, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using hdiff_nonneg
    have hD : D.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hD_nonneg
    have hT : T.PosSemidef :=
      cMatrix_rpow_posSemidef (A := τ) (s := p) hτ
    have hleft : (Matrix.kronecker A D).PosSemidef :=
      hA.kronecker hD
    have hfull : (Matrix.kronecker (Matrix.kronecker A D) T).PosSemidef :=
      hleft.kronecker hT
    have htrace := cMatrix_trace_mul_posSemidef_re_nonneg hfull hR
    change 0 ≤
      ((Matrix.kronecker (Matrix.kronecker A D) T * R).trace).re at htrace
    have htrace' :
        0 ≤ -abcWeightedSidePowerTraceRe (a := a) A R (s • x + t • y) τ p +
          (s * abcWeightedSidePowerTraceRe (a := a) A R x τ p +
            t * abcWeightedSidePowerTraceRe (a := a) A R y τ p) := by
      rw [trace_weighted_kronecker_middle_add_smul_add_smul_re A R T
        ((-1 : ℝ) • S) U V s t] at htrace
      have hS :
          ((Matrix.kronecker (Matrix.kronecker A ((-1 : ℝ) • S)) T * R).trace).re =
            -abcWeightedSidePowerTraceRe (a := a) A R (s • x + t • y) τ p := by
        simp only [abcWeightedSidePowerTraceRe, S, T]
        unfold Matrix.kronecker
        rw [Matrix.kroneckerMap_smul_right (fun x y : ℂ => x * y) (-1 : ℝ)
          (by intro x y; exact mul_smul_comm (-1 : ℝ) x y) A
          (CFC.rpow (s • x + t • y) (-p))]
        rw [Matrix.kroneckerMap_smul_left (fun x y : ℂ => x * y) (-1 : ℝ)
          (by intro x y; exact smul_mul_assoc (-1 : ℝ) x y)
          (Matrix.kroneckerMap (fun x y : ℂ => x * y) A
            (CFC.rpow (s • x + t • y) (-p)))
          (CFC.rpow τ p)]
        rw [Matrix.smul_mul, Matrix.trace_smul]
        simp
      have hU :
          ((Matrix.kronecker (Matrix.kronecker A U) T * R).trace).re =
            abcWeightedSidePowerTraceRe (a := a) A R x τ p := by
        simp [abcWeightedSidePowerTraceRe, U, T]
      have hV :
          ((Matrix.kronecker (Matrix.kronecker A V) T * R).trace).re =
            abcWeightedSidePowerTraceRe (a := a) A R y τ p := by
        simp [abcWeightedSidePowerTraceRe, V, T]
      rw [hS, hU, hV] at htrace
      exact htrace
    have hle :
        abcWeightedSidePowerTraceRe (a := a) A R (s • x + t • y) τ p ≤
          s * abcWeightedSidePowerTraceRe (a := a) A R x τ p +
            t * abcWeightedSidePowerTraceRe (a := a) A R y τ p := by
      nlinarith
    simpa [smul_eq_mul] using hle

/-- The fixed-`A` KW bracket is quasiconvex in the negative-power side variable
on the positive-definite cone. -/
theorem abcWeightedSidePowerTraceRe_quasiconvexOn_sigma_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    {A : CMatrix a} (hA : A.PosSemidef)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    {τ : CMatrix c} (hτ : τ.PosSemidef)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    QuasiconvexOn ℝ ({σ : CMatrix b | σ.PosDef} : Set (CMatrix b))
      (fun σ : CMatrix b => abcWeightedSidePowerTraceRe (a := a) A R σ τ p) :=
  (abcWeightedSidePowerTraceRe_convexOn_sigma_posDef (a := a) hA hR hτ hp0 hp1)
    |>.quasiconvexOn

/-- Continuity of the fixed-`A` KW bracket in the negative-power side variable
on the positive-definite cone. -/
theorem abcWeightedSidePowerTraceRe_continuousOn_sigma_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (A : CMatrix a) (R : CMatrix (Prod (Prod a b) c)) (τ : CMatrix c) (p : ℝ) :
    ContinuousOn
      (fun σ : CMatrix b => abcWeightedSidePowerTraceRe (a := a) A R σ τ p)
      ({σ : CMatrix b | σ.PosDef} : Set (CMatrix b)) := by
  have htrace :=
    trace_weighted_kronecker_middle_continuous (a := a) (b := b) A R (CFC.rpow τ p)
  have hpow := cMatrix_rpow_continuousOn_posDef (a := b) (-p)
  simpa [abcWeightedSidePowerTraceRe, Function.comp_def] using
    htrace.comp_continuousOn hpow

/-- Lower semicontinuity of the fixed-`A` KW bracket in the negative-power side
variable on the positive-definite cone. -/
theorem abcWeightedSidePowerTraceRe_lowerSemicontinuousOn_sigma_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (A : CMatrix a) (R : CMatrix (Prod (Prod a b) c)) (τ : CMatrix c) (p : ℝ) :
    LowerSemicontinuousOn
      (fun σ : CMatrix b => abcWeightedSidePowerTraceRe (a := a) A R σ τ p)
      ({σ : CMatrix b | σ.PosDef} : Set (CMatrix b)) :=
  ContinuousOn.lowerSemicontinuousOn
    (abcWeightedSidePowerTraceRe_continuousOn_sigma_posDef (a := a) A R τ p)

/-- Upper semicontinuity of the fixed-`A` KW bracket in the negative-power side
variable on the positive-definite cone. -/
theorem abcWeightedSidePowerTraceRe_upperSemicontinuousOn_sigma_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (A : CMatrix a) (R : CMatrix (Prod (Prod a b) c)) (τ : CMatrix c) (p : ℝ) :
    UpperSemicontinuousOn
      (fun σ : CMatrix b => abcWeightedSidePowerTraceRe (a := a) A R σ τ p)
      ({σ : CMatrix b | σ.PosDef} : Set (CMatrix b)) :=
  ContinuousOn.upperSemicontinuousOn
    (abcWeightedSidePowerTraceRe_continuousOn_sigma_posDef (a := a) A R τ p)

/-- Source-faithful Sion minimax equality for the fixed-`A` KW trace bracket on
a compact full-support `sigma` domain.

This is the fixed-marginal-weight version needed for the sandwiched
mutual-information alternate expression in KW `EA_capacity.tex:2020-2025`. -/
theorem uniformlyPositiveDensityMatrixSet_sion_abcWeightedSidePowerTraceRe_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    {delta p : ℝ} (hdelta : 0 < delta)
    (hneB : (uniformlyPositiveDensityMatrixSet delta b).Nonempty)
    {A : CMatrix a} (hA : A.PosSemidef)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (⨅ σ ∈ uniformlyPositiveDensityMatrixSet delta b, ⨆ τ ∈ densityMatrixSet c,
        (abcWeightedSidePowerTraceRe (a := a) A R σ τ p : EReal)) =
      ⨆ τ ∈ densityMatrixSet c, ⨅ σ ∈ uniformlyPositiveDensityMatrixSet delta b,
        (abcWeightedSidePowerTraceRe (a := a) A R σ τ p : EReal) := by
  exact sion_iInf_iSup_eq_iSup_iInf
    hneB
    (uniformlyPositiveDensityMatrixSet_convex (a := b) (delta := delta))
    (uniformlyPositiveDensityMatrixSet_isCompact (a := b) (delta := delta))
    (fun τ hτ => by
      exact continuous_coe_real_ereal.comp_lowerSemicontinuousOn
        ((abcWeightedSidePowerTraceRe_lowerSemicontinuousOn_sigma_posDef
          (a := a) A R τ p).mono
          (uniformlyPositiveDensityMatrixSet_subset_posDef (a := b) hdelta))
        EReal.coe_strictMono.monotone)
    (fun τ hτ => by
      simpa [Function.comp_def] using
        (Convex.quasiconvexOn_restrict
          (abcWeightedSidePowerTraceRe_quasiconvexOn_sigma_posDef
            (a := a) hA hR hτ.1 hp0 hp1)
          (uniformlyPositiveDensityMatrixSet_subset_posDef (a := b) hdelta)
          (uniformlyPositiveDensityMatrixSet_convex (a := b) (delta := delta)))
            |>.monotone_comp EReal.coe_strictMono.monotone)
    (densityMatrixSet_convex (a := c))
    (fun σ hσ => by
      exact continuous_coe_real_ereal.comp_upperSemicontinuousOn
        ((abcWeightedSidePowerTraceRe_upperSemicontinuousOn_tau_posSemidef
          (a := a) A R σ hp0).mono
          (fun τ hτ => hτ.1))
        EReal.coe_strictMono.monotone)
    (fun σ hσ => by
      simpa [Function.comp_def] using
        (Convex.quasiconcaveOn_restrict
          (abcWeightedSidePowerTraceRe_quasiconcaveOn_tau
            (a := a) hA hR hσ.1.1 hp0 hp1)
          (fun τ hτ => hτ.1)
          (densityMatrixSet_convex (a := c))).monotone_comp
            EReal.coe_strictMono.monotone)

/-- Source-faithful Sion minimax equality for the fixed-`A` KW trace bracket
on the full-rank `sigma` domain.

Unlike the compact-cutoff lemma above, this uses the purifying-side density
matrices as Sion's compact variable and applies Sion to the negative saddle
function.  It is the no-cutoff exchange needed for the reverse half of the
state alternate-expression proof in KW `EA_capacity.tex:2018-2035`. -/
theorem fullRankDensityMatrixSet_sion_abcWeightedSidePowerTraceRe_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    {p : ℝ}
    {A : CMatrix a} (hA : A.PosSemidef)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (⨅ sigma : CMatrix b,
      ⨅ _hSigma : (fullRankDensityMatrixSet b) sigma,
        ⨆ tau : CMatrix c,
          ⨆ _hTau : (densityMatrixSet c) tau,
            (abcWeightedSidePowerTraceRe (a := a) A R sigma tau p : EReal)) =
      ⨆ tau : CMatrix c,
        ⨆ _hTau : (densityMatrixSet c) tau,
          ⨅ sigma : CMatrix b,
            ⨅ _hSigma : (fullRankDensityMatrixSet b) sigma,
              (abcWeightedSidePowerTraceRe (a := a) A R sigma tau p : EReal) := by
  let F : {sigma : CMatrix b // (fullRankDensityMatrixSet b) sigma} →
      {tau : CMatrix c // (densityMatrixSet c) tau} → EReal :=
    fun sigma tau =>
      (abcWeightedSidePowerTraceRe (a := a) A R sigma.1 tau.1 p : EReal)
  have hnegMem :
      (⨅ tau : CMatrix c,
        ⨅ _hTau : (densityMatrixSet c) tau,
          ⨆ sigma : CMatrix b,
            ⨆ _hSigma : (fullRankDensityMatrixSet b) sigma,
              -((abcWeightedSidePowerTraceRe (a := a) A R sigma tau p : EReal))) =
        ⨆ sigma : CMatrix b,
          ⨆ _hSigma : (fullRankDensityMatrixSet b) sigma,
            ⨅ tau : CMatrix c,
              ⨅ _hTau : (densityMatrixSet c) tau,
                -((abcWeightedSidePowerTraceRe (a := a) A R sigma tau p : EReal)) := by
    exact State.sion_iInf_iSup_eq_iSup_iInf
      (densityMatrixSet_nonempty (a := c))
      (densityMatrixSet_convex (a := c))
      (densityMatrixSet_isCompact (a := c))
      (fun sigma hSigma => by
        have hcontReal : ContinuousOn
            (fun tau : CMatrix c =>
              abcWeightedSidePowerTraceRe (a := a) A R sigma tau p)
            (densityMatrixSet c) :=
          (abcWeightedSidePowerTraceRe_continuousOn_tau_posSemidef
            (a := a) A R sigma hp0).mono (fun tau hTau => hTau.1)
        have hcontE : ContinuousOn
            (fun tau : CMatrix c =>
              (abcWeightedSidePowerTraceRe (a := a) A R sigma tau p : EReal))
            (densityMatrixSet c) :=
          continuous_coe_real_ereal.comp_continuousOn hcontReal
        exact ContinuousOn.lowerSemicontinuousOn
          (continuous_neg.comp_continuousOn hcontE))
      (fun sigma hSigma => by
        simpa [Function.comp_def] using
          (Convex.quasiconcaveOn_restrict
            (abcWeightedSidePowerTraceRe_quasiconcaveOn_tau
              (a := a) hA hR hSigma.1.posSemidef hp0 hp1)
            (fun tau hTau => hTau.1)
            (densityMatrixSet_convex (a := c))).antitone_comp
              antitone_ereal_neg_coe)
      (fullRankDensityMatrixSet_convex (a := b))
      (fun tau hTau => by
        have hcontReal : ContinuousOn
            (fun sigma : CMatrix b =>
              abcWeightedSidePowerTraceRe (a := a) A R sigma tau p)
            (fullRankDensityMatrixSet b) :=
          (abcWeightedSidePowerTraceRe_continuousOn_sigma_posDef
            (a := a) A R tau p).mono (fun sigma hSigma => hSigma.1)
        have hcontE : ContinuousOn
            (fun sigma : CMatrix b =>
              (abcWeightedSidePowerTraceRe (a := a) A R sigma tau p : EReal))
            (fullRankDensityMatrixSet b) :=
          continuous_coe_real_ereal.comp_continuousOn hcontReal
        exact ContinuousOn.upperSemicontinuousOn
          (continuous_neg.comp_continuousOn hcontE))
      (fun tau hTau => by
        simpa [Function.comp_def] using
          (Convex.quasiconvexOn_restrict
            (abcWeightedSidePowerTraceRe_quasiconvexOn_sigma_posDef
              (a := a) hA hR hTau.1 hp0 hp1)
            (fun sigma hSigma => hSigma.1)
            (fullRankDensityMatrixSet_convex (a := b))).antitone_comp
              antitone_ereal_neg_coe)
  have hnegSub :
      (⨅ tau : {tau : CMatrix c // (densityMatrixSet c) tau},
        ⨆ sigma : {sigma : CMatrix b // (fullRankDensityMatrixSet b) sigma},
          -F sigma tau) =
        ⨆ sigma : {sigma : CMatrix b // (fullRankDensityMatrixSet b) sigma},
          ⨅ tau : {tau : CMatrix c // (densityMatrixSet c) tau},
            -F sigma tau := by
    simpa [F, iInf_subtype', iSup_subtype'] using hnegMem
  have hsub := ereal_sion_from_neg F hnegSub
  simpa [F, iInf_subtype', iSup_subtype'] using hsub

end State

/-- KW high-`alpha` specialization of the fixed-`A` Sion exchange for the raw
alternate-expression trace bracket.

This is the fixed marginal-weight version of
`sandwichedAlpha_sion_abcSidePowerTraceRe_EReal`. -/
theorem sandwichedAlpha_sion_abcWeightedSidePowerTraceRe_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    {A : CMatrix a} (hA : A.PosSemidef)
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    (halpha : 1 < alpha) :
    (⨅ σ ∈ State.uniformlyPositiveDensityMatrixSet delta b,
        ⨆ τ ∈ State.densityMatrixSet c,
          (State.abcWeightedSidePowerTraceRe (a := a) A R σ τ
            ((alpha - 1) / alpha) : EReal)) =
      ⨆ τ ∈ State.densityMatrixSet c,
        ⨅ σ ∈ State.uniformlyPositiveDensityMatrixSet delta b,
          (State.abcWeightedSidePowerTraceRe (a := a) A R σ τ
            ((alpha - 1) / alpha) : EReal) := by
  have hp := sandwichedAlphaPrime_pos_lt_one halpha
  exact State.uniformlyPositiveDensityMatrixSet_sion_abcWeightedSidePowerTraceRe_EReal
    (a := a) (b := b) (c := c)
    hdelta_pos
    (State.uniformlyPositiveDensityMatrixSet_nonempty (a := b) hdelta_le)
    hA hR hp.1 (le_of_lt hp.2)
end

end QIT
