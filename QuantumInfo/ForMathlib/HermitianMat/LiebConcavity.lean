/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.Rpow
import QuantumInfo.ForMathlib.HermitianMat.Schatten
import Mathlib

/-!
# Lieb Concavity and Epstein's Theorem for Trace Functionals

This file proves the concavity of the trace functional
`σ ↦ Tr[(σ^s H σ^s)^p]` for `H ≥ 0`, `p ≥ 1`, and `2sp ≤ 1`,
which is a consequence of Epstein's generalization of Lieb's concavity theorem.

## Main results

* `HermitianMat.epstein_concavity` — Epstein's theorem: For `H ≥ 0`, `p ≥ 1`, `0 < s`,
  `2sp ≤ 1`, the map `σ ↦ Tr[(σ^s H σ^s)^p]` is concave on PSD matrices.

* `HermitianMat.trace_conj_rpow_concave` — For `α > 1`, the map
  `σ ↦ Tr[(H.conj (σ^s).mat)^p]` is concave on PSD matrices,
  where `s = (α-1)/(2α)` and `p = α/(α-1)`. This is the version used in the DPI proof.

## Proof strategy

The proof is structured via the following key steps:

1. **Trace identity** (`trace_conj_rpow_eq`): For PSD `σ` and `H`:
   `Tr[(σ^s H σ^s)^p] = Tr[(H^{1/2} σ^{2s} H^{1/2})^p]`
   This is proved using the SVD-like identity `Tr[(X†X)^p] = Tr[(XX†)^p]`.

2. **Operator concavity of rpow** (`rpow_operator_concave`): For `0 < s ≤ 1`,
   `σ ↦ σ^s` is operator concave on PSD matrices. This follows from the integral
   representation `A^s = (sin(πs)/π) ∫₀^∞ u^{s-1} A(A+uI)^{-1} du` and the
   operator concavity of each integrand.

3. **Trace monotonicity** (`inner_nonneg_of_nonneg`): For `H, A ≥ 0`, `⟪H, A⟫ ≥ 0`.

4. **Epstein's theorem for p = 1** (`epstein_concavity_p_one`):
   `σ ↦ Tr[H σ^{2s}] = ⟪H, σ^{2s}⟫` is concave for `2s ≤ 1` (from operator
   concavity + trace monotonicity).

5. **Epstein's theorem** (`epstein_concavity`): The general `p ≥ 1` case follows from
   Lieb's concavity theorem via complex interpolation or the Herglotz representation.

## References

* E.H. Lieb, "Convex trace functions and the Wigner-Yanase-Dyson conjecture", 1973.
* H. Epstein, "Remarks on two theorems of E. Lieb", 1973.
* E. Carlen, "Trace inequalities and quantum entropy", 2010.
* F. Hiai, D. Petz, "Introduction to Matrix Analysis and Applications", 2014.
-/

variable {d : Type*} [Fintype d] [DecidableEq d]

noncomputable section
open scoped Matrix ComplexOrder InnerProductSpace RealInnerProductSpace HermitianMat
open BigOperators

namespace HermitianMat

/-! ## Parameter arithmetic -/

/-- For `α > 1`, the exponent `s = (α-1)/(2α)` is positive. -/
lemma dpi_s_pos {α : ℝ} (hα : 1 < α) : 0 < (α - 1) / (2 * α) := by
  apply div_pos (by linarith) (by linarith)

/-- For `α > 1`, the exponent `s = (α-1)/(2α)` is less than `1/2`. -/
lemma dpi_s_lt_half {α : ℝ} (hα : 1 < α) : (α - 1) / (2 * α) < 1 / 2 := by
  have h2 : 0 < 2 * α := by linarith
  rw [div_lt_div_iff₀ h2 two_pos]
  linarith

/-- For `α > 1`, the exponent `s = (α-1)/(2α)` is at most `1/2`. -/
lemma dpi_s_le_half {α : ℝ} (hα : 1 < α) : (α - 1) / (2 * α) ≤ 1 / 2 :=
  le_of_lt (dpi_s_lt_half hα)

/-- For `α > 1`, the exponent `p = α/(α-1)` is greater than `1`. -/
lemma dpi_p_gt_one {α : ℝ} (hα : 1 < α) : 1 < α / (α - 1) := by
  rw [one_lt_div (by linarith : (0 : ℝ) < α - 1)]
  linarith

/-- For `α > 1`, the exponent `p = α/(α-1)` is positive. -/
lemma dpi_p_pos {α : ℝ} (hα : 1 < α) : 0 < α / (α - 1) :=
  lt_trans zero_lt_one (dpi_p_gt_one hα)

/-- The key identity: `2sp = 1` where `s = (α-1)/(2α)` and `p = α/(α-1)`. -/
lemma dpi_2sp_eq_one {α : ℝ} (hα : 1 < α) :
    2 * ((α - 1) / (2 * α)) * (α / (α - 1)) = 1 := by
  have h1 : α ≠ 0 := by linarith
  have h2 : α - 1 ≠ 0 := by linarith
  field_simp

/-! ## Convexity of the PSD cone -/

omit [Fintype d] in
/-- The set of PSD Hermitian matrices is convex. -/
theorem convex_psd : Convex ℝ {σ : HermitianMat d ℂ | 0 ≤ σ} := by
  intro x hx y hy a b ha hb _
  simp only [Set.mem_setOf_eq] at *
  exact convex_cone hx hy ha hb

/-! ## Trace identity: Tr[(σ^s H σ^s)^p] = Tr[(H^{1/2} σ^{2s} H^{1/2})^p]

This is the algebraic identity that connects the two forms of the trace functional.
It follows from the fact that for X = H^{1/2} σ^s:
- σ^s H σ^s = X†X  (since H = (H^{1/2})† H^{1/2} and σ^s is self-adjoint)
- H^{1/2} σ^{2s} H^{1/2} = XX†

And X†X and XX† have the same nonzero eigenvalues, hence Tr[(X†X)^p] = Tr[(XX†)^p].
-/

/-- For any square matrix, `Tr[(X†X)^p] = Tr[(XX†)^p]` for real `p > 0`.
  This follows from the fact that `X†X` and `XX†` have the same characteristic
  polynomial (`Matrix.charpoly_mul_comm`), hence the same eigenvalues. -/
lemma trace_rpow_XstarX_eq_XXstar (X : Matrix d d ℂ) {p : ℝ} (_hp : 0 < p) :
    let A : HermitianMat d ℂ :=
      ⟨X.conjTranspose * X, Matrix.isHermitian_conjTranspose_mul_self X⟩
    let B : HermitianMat d ℂ :=
      ⟨X * X.conjTranspose, Matrix.isHermitian_mul_conjTranspose_self X⟩
    (A ^ p).trace = (B ^ p).trace := by
  simp [HermitianMat.trace_rpow_eq_sum]
  have h_charpoly_eq : (X.conjTranspose * X).charpoly = (X * X.conjTranspose).charpoly :=
    Matrix.charpoly_mul_comm Xᴴ X
  rw [Matrix.IsHermitian.charpoly_eq, Matrix.IsHermitian.charpoly_eq] at h_charpoly_eq
  rotate_left
  · exact Matrix.isHermitian_mul_conjTranspose_self X
  · exact Matrix.isHermitian_conjTranspose_mul_self X
  apply_fun Polynomial.roots at h_charpoly_eq
  rw [Polynomial.roots_prod, Polynomial.roots_prod] at h_charpoly_eq
  · replace h_charpoly_eq := congr_arg Multiset.sum
      (congr_arg (Multiset.map (fun x : ℂ => x.re ^ p)) h_charpoly_eq)
    simp_all [Polynomial.roots_X_sub_C]
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _

/-- The trace identity: `Tr[(σ^s H σ^s)^p] = Tr[(H^{1/2} σ^{2s} H^{1/2})^p]`
  for PSD σ, H and p > 0.

  Uses the X†X/XX† eigenvalue identity with X = H^{1/2} · σ^s. -/
lemma trace_conj_rpow_eq (σ H : HermitianMat d ℂ) (hσ : 0 ≤ σ) (hH : 0 ≤ H)
    {s p : ℝ} (hs : 0 < s) (hp : 0 < p) :
    ((H.conj (σ ^ s).mat) ^ p).trace =
    (((σ ^ (2 * s)).conj H.sqrt.mat) ^ p).trace := by
  have h_trace_rpow : ∀ (X : Matrix d d ℂ),
      (let A : HermitianMat d ℂ :=
        ⟨X.conjTranspose * X, Matrix.isHermitian_conjTranspose_mul_self X⟩
       let B : HermitianMat d ℂ :=
        ⟨X * X.conjTranspose, Matrix.isHermitian_mul_conjTranspose_self X⟩
       (A ^ p).trace = (B ^ p).trace) := by
    grind only [trace_rpow_XstarX_eq_XXstar]
  convert h_trace_rpow (H.sqrt.mat * (σ ^ s).mat) using 1
  · congr! 2
    unfold conj; ext; simp [Matrix.mul_assoc, Matrix.conjTranspose_mul]
    simp [← Matrix.mul_assoc, ← HermitianMat.sqrt_sq hH]
  · have h_eq : (σ ^ (2 * s)).mat = (σ ^ s).mat * (σ ^ s).mat := by
      rw [two_mul, mat_rpow_add]
      · exact hσ
      · positivity
    simp [← mul_assoc, h_eq, conj]

/-! ## Operator concavity of rpow

The Löwner–Heinz theorem (`rpow_le_rpow_of_le`) gives operator monotonicity of
`σ ↦ σ^s` for `0 < s ≤ 1`. Operator concavity is a stronger statement that follows
from the integral representation of operator monotone functions.

The proof proceeds in stages:
1. `resolvent_inv_concave`: The resolvent `(A + u·1)⁻¹` satisfies operator convexity
   (from `inv_convex`), which gives pointwise concavity of the integral approximation.
2. `rpowApprox_concave`: The finite integral approximation `rpowApprox` satisfies the
   concavity inequality (by integrating the pointwise bound).
3. `rpow_operator_concave_posDef`: Passing to the limit gives operator concavity
   for positive definite matrices.
4. `rpow_operator_concave`: Extension to PSD by ε-perturbation and continuity.
-/

/-
A convex combination of positive definite matrices is positive definite.
-/
lemma posDef_convex_comb {A B : HermitianMat d ℂ}
    (hA : A.mat.PosDef) (hB : B.mat.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • A + b • B).mat.PosDef := by
  rcases lt_or_eq_of_le ha with ha | rfl <;> rcases lt_or_eq_of_le hb with hb | rfl;
  · convert Matrix.PosDef.add ?_ ?_ using 1;
    · infer_instance;
    · convert hA.smul ha;
    · convert hB.smul ?_ using 1;
      all_goals try infer_instance;
      exact hb;
  · aesop;
  · aesop;
  · norm_num at hab

/-
The resolvent satisfies operator convexity:
  `(a·A + b·B + u·1)⁻¹ ≤ a·(A + u·1)⁻¹ + b·(B + u·1)⁻¹`
  for positive definite A, B, u > 0, and a + b = 1.
  This is a direct consequence of `inv_convex`.
-/
lemma resolvent_inv_concave {A B : HermitianMat d ℂ}
    (hA : A.mat.PosDef) (hB : B.mat.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    {u : ℝ} (hu : 0 ≤ u) :
    (a • A + b • B + u • 1)⁻¹ ≤ a • (A + u • 1)⁻¹ + b • (B + u • 1)⁻¹ := by
  convert HermitianMat.inv_shift_convex _ _ _ _ _ u hu using 2;
  · exact hA;
  · exact hB;
  · exact ha;
  · exact hb;
  · exact hab

/-
The integrand of `rpowApprox` is integrable on `(0, T]` for PosDef matrices.
-/
lemma rpowApprox_integrand_integrableOn {A : HermitianMat d ℂ} (hA : A.mat.PosDef)
    {q : ℝ} (hq : 0 ≤ q) {T : ℝ} :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ q • ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (A + t • 1)⁻¹))
      (Set.Ioc 0 T) := by
  -- The function t ↦ t^q • ((1+t)⁻¹ • 1 - (A + t•1)⁻¹) is continuous on [0, T], hence integrable on (0, T].
  have h_cont : ContinuousOn (fun t : ℝ => t ^ q • ((1 + t)⁻¹ • 1 - (A + t • 1)⁻¹)) (Set.Icc 0 T) := by
    refine' ContinuousOn.smul _ _;
    · exact continuousOn_id.rpow_const fun x hx => Or.inr <| by linarith;
    · refine' ContinuousOn.sub ( ContinuousOn.smul ( ContinuousOn.inv₀ ( continuousOn_const.add continuousOn_id ) fun t ht => by linarith [ ht.1 ] ) continuousOn_const ) _;
      intro t ht;
      have h_inv_cont : ContinuousAt (fun t : ℝ => (A + t • 1)⁻¹) t := by
        have h_det_cont : ContinuousAt (fun t : ℝ => Matrix.det (A + t • 1 : Matrix d d ℂ)) t := by
          fun_prop
        have h_inv_cont : ContinuousAt (fun t : ℝ => (A + t • 1 : Matrix d d ℂ)⁻¹) t := by
          have h_det_ne_zero : Matrix.det (A + t • 1 : Matrix d d ℂ) ≠ 0 := by
            have h_det_ne_zero : ∀ t : ℝ, 0 ≤ t → Matrix.PosDef (A + t • 1 : Matrix d d ℂ) := by
              intro t ht;
              convert hA.add_posSemidef _ using 1;
              simp [ Matrix.PosSemidef ];
              simp [ Matrix.IsHermitian, Matrix.one_apply ];
              intro x; rw [ Finsupp.sum ] ; simp [ mul_comm, mul_left_comm ] ;
              exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp [ *, Complex.mul_conj, Complex.normSq_eq_norm_sq ] ; positivity;
            exact h_det_ne_zero t ht.1 |> fun h => h.det_pos.ne'
          simp_all [ Matrix.inv_def ];
          fun_prop (disch := solve_by_elim);
        rw [ ContinuousAt ] at *;
        rw [ tendsto_subtype_rng ] at *;
        convert h_inv_cont using 1;
      exact h_inv_cont.continuousWithinAt;
  exact h_cont.integrableOn_Icc.mono_set <| Set.Ioc_subset_Icc_self

set_option maxHeartbeats 1600000 in
/-- The finite resolvent integral approximation satisfies the concavity inequality
  for positive definite matrices. -/
lemma rpowApprox_concave {A B : HermitianMat d ℂ}
    (hA : A.mat.PosDef) (hB : B.mat.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    {q : ℝ} (hq : 0 ≤ q) {T : ℝ} (hT : 0 < T) :
    a • rpowApprox A q T + b • rpowApprox B q T ≤
    rpowApprox (a • A + b • B) q T := by
  have h_integral_mono : ∫ t in Set.Ioc 0 T, t ^ q • (a • ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (A + t • 1)⁻¹) + b • ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (B + t • 1)⁻¹)) ≤ ∫ t in Set.Ioc 0 T, t ^ q • ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (a • A + b • B + t • 1)⁻¹) := by
    refine' MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ioc fun t ht => smul_le_smul_of_nonneg_left _ ( Real.rpow_nonneg ht.1.le _ );
    · have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ q • ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (A + t • 1)⁻¹)) (Set.Ioc 0 T) ∧ MeasureTheory.IntegrableOn (fun t : ℝ => t ^ q • ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (B + t • 1)⁻¹)) (Set.Ioc 0 T) := by
        exact ⟨ rpowApprox_integrand_integrableOn hA hq, rpowApprox_integrand_integrableOn hB hq ⟩;
      simp_all [ smul_add, smul_sub, smul_smul ];
      refine' MeasureTheory.Integrable.add _ _;
      · convert h_integrable.1.smul a using 2 ; simp [  mul_comm, mul_left_comm ];
        module;
      · convert h_integrable.2.smul b using 2 ; norm_num ; ring_nf
        simp [ mul_assoc, mul_comm, smul_sub, smul_smul ];
    · convert rpowApprox_integrand_integrableOn _ _ using 1;
      · exact posDef_convex_comb hA hB ha hb hab;
      · exact hq;
    · -- Apply the resolvent inequality to each term individually.
      have h_resolvent : (a • A + b • B + t • 1)⁻¹ ≤ a • (A + t • 1)⁻¹ + b • (B + t • 1)⁻¹ := by
        convert resolvent_inv_concave hA hB ha hb hab ht.1.le using 1;
      simp_all [ ← eq_sub_iff_add_eq' ];
      convert sub_le_sub_left h_resolvent _ using 1 ; simp [ sub_smul, smul_sub ] ; abel_nf;
  convert h_integral_mono using 1 <;> simp [ intervalIntegral.integral_of_le hT.le, rpowApprox ];
  rw [ ← MeasureTheory.integral_smul, ← MeasureTheory.integral_smul, ← MeasureTheory.integral_add ];
  · simp only [smul_smul, mul_comm];
  · have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ q • ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (A + t • 1)⁻¹)) (Set.Ioc 0 T) := by
      convert rpowApprox_integrand_integrableOn hA hq using 1;
    exact MeasureTheory.Integrable.fun_smul_enorm a h_integrable;
  · have := @rpowApprox_integrand_integrableOn d _ _ B hB q hq T;
    exact MeasureTheory.Integrable.fun_smul_enorm b this

/-
For positive definite matrices and 0 < s < 1, rpow is operator concave.
-/
lemma rpow_operator_concave_posDef {A B : HermitianMat d ℂ}
    (hA : A.mat.PosDef) (hB : B.mat.PosDef)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t • A ^ s + (1 - t) • B ^ s ≤ (t • A + (1 - t) • B) ^ s := by
  by_cases h : 0 < rpowConst s;
  · have h_lim : Filter.Tendsto (fun T => rpowApprox A s T) Filter.atTop (nhds (rpowConst s • (A ^ s - 1))) ∧ Filter.Tendsto (fun T => rpowApprox B s T) Filter.atTop (nhds (rpowConst s • (B ^ s - 1))) ∧ Filter.Tendsto (fun T => rpowApprox (t • A + (1 - t) • B) s T) Filter.atTop (nhds (rpowConst s • ((t • A + (1 - t) • B) ^ s - 1))) := by
      refine' ⟨ tendsto_rpowApprox hA hs hs1, tendsto_rpowApprox hB hs hs1, tendsto_rpowApprox _ hs hs1 ⟩;
      apply posDef_convex_comb hA hB ht (sub_nonneg.mpr ht1) (by linarith);
    have h_lim : t • (rpowConst s • (A ^ s - 1)) + (1 - t) • (rpowConst s • (B ^ s - 1)) ≤ rpowConst s • ((t • A + (1 - t) • B) ^ s - 1) := by
      have h_lim : ∀ T > 0, t • rpowApprox A s T + (1 - t) • rpowApprox B s T ≤ rpowApprox (t • A + (1 - t) • B) s T := by
        intros T hT_pos
        apply rpowApprox_concave hA hB ht (sub_nonneg_of_le ht1) (by linarith) hs.le hT_pos;
      rename_i h;
      convert le_of_tendsto_of_tendsto ( Filter.Tendsto.add ( tendsto_const_nhds.smul h.1 ) ( tendsto_const_nhds.smul h.2.1 ) ) h.2.2 ( Filter.eventually_atTop.mpr ⟨ 1, fun T hT => h_lim T <| zero_lt_one.trans_le hT ⟩ ) using 1;
    have h_div : (1 / rpowConst s) • (t • (rpowConst s • (A ^ s - 1)) + (1 - t) • (rpowConst s • (B ^ s - 1))) ≤ (1 / rpowConst s) • (rpowConst s • ((t • A + (1 - t) • B) ^ s - 1)) := by
      convert smul_le_smul_of_nonneg_left h_lim ( one_div_nonneg.mpr h.le ) using 1;
    convert add_le_add_right h_div 1 using 1 <;> norm_num [ ← smul_assoc, h.ne' ];
    simp [ mul_comm, h.ne', smul_sub, sub_smul ];
    abel1;
  · exact False.elim <| h <| rpowConst_pos hs hs1

/-
**Operator concavity of rpow**: For `0 < s ≤ 1`, the map `σ ↦ σ^s` is operator concave
  on PSD matrices. That is, for PSD `σ₁`, `σ₂` and `t ∈ [0, 1]`:
  `(t σ₁ + (1-t) σ₂)^s ≥ t σ₁^s + (1-t) σ₂^s` in the Loewner order.

  This follows from the integral representation for `0 < s < 1`:
  `A^s = (sin(πs)/π) ∫₀^∞ u^{s-1} A(A + uI)^{-1} du`
  where each integrand `A(A+uI)^{-1}` is operator concave, and
  the case `s = 1` is trivial (identity).
-/
lemma rpow_operator_concave {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (σ₁ σ₂ : HermitianMat d ℂ) (hσ₁ : 0 ≤ σ₁) (hσ₂ : 0 ≤ σ₂)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t • σ₁ ^ s + (1 - t) • σ₂ ^ s ≤ (t • σ₁ + (1 - t) • σ₂) ^ s := by
  by_cases hs1 : s < 1;
  · -- Define σ₁ε = σ₁ + ε • 1 and σ₂ε = σ₂ + ε • 1.
    set σ₁ε : ℝ → HermitianMat d ℂ := fun ε => σ₁ + ε • 1
    set σ₂ε : ℝ → HermitianMat d ℂ := fun ε => σ₂ + ε • 1;
    -- For ε > 0, both σ₁ε and σ₂ε are positive definite.
    have h_pos_def : ∀ ε > 0, (σ₁ε ε).mat.PosDef ∧ (σ₂ε ε).mat.PosDef := by
      intro ε hε_pos
      have h_pos_def_σ₁ : (σ₁ + ε • 1).mat.PosDef := by
        convert posDef_of_posDef_le ( show ( ε • 1 : HermitianMat d ℂ ).mat.PosDef from ?_ ) ?_ using 1;
        · constructor <;> norm_num [ hε_pos ];
          · simp [ Matrix.IsHermitian, Matrix.conjTranspose_smul ];
          · simp [ Finsupp.sum, Matrix.one_apply ];
            intro x hx_ne; rw [ Finset.sum_congr rfl fun i hi => if_neg ( by contrapose! hx_ne; ext j; aesop ) ] ; simp [mul_comm, mul_left_comm ] ;
            simp [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
            exact_mod_cast Finset.sum_pos ( fun i hi => mul_pos hε_pos ( sq_pos_of_pos ( norm_pos_iff.mpr ( show x i ≠ 0 from by aesop ) ) ) ) ( Finset.nonempty_of_ne_empty ( by aesop ) );
        · exact le_add_of_nonneg_left hσ₁
      have h_pos_def_σ₂ : (σ₂ + ε • 1).mat.PosDef := by
        convert posDef_of_posDef_le ( show ( ε • 1 : HermitianMat d ℂ ).mat.PosDef from ?_ ) ?_ using 1;
        · convert Matrix.PosDef.smul ( show ( 1 : Matrix d d ℂ ).PosDef from ?_ ) hε_pos using 1;
          exact Matrix.PosDef.one;
        · exact le_add_of_nonneg_left hσ₂
      exact ⟨h_pos_def_σ₁, h_pos_def_σ₂⟩;
    -- By continuity of rpow (rpow_const_continuous) and continuity of the smul and add operations, as ε → 0⁺:
    have h_cont : Filter.Tendsto (fun ε : ℝ => σ₁ε ε ^ s) (nhdsWithin 0 (Set.Ioi 0)) (nhds (σ₁ ^ s)) ∧ Filter.Tendsto (fun ε : ℝ => σ₂ε ε ^ s) (nhdsWithin 0 (Set.Ioi 0)) (nhds (σ₂ ^ s)) ∧ Filter.Tendsto (fun ε : ℝ => (t • σ₁ε ε + (1 - t) • σ₂ε ε) ^ s) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((t • σ₁ + (1 - t) • σ₂) ^ s)) := by
      refine' ⟨ _, _, _ ⟩;
      · have h_cont : ContinuousOn (fun ε : ℝ => σ₁ε ε ^ s) (Set.Ici 0) := by
          fun_prop (disch := solve_by_elim);
        have := h_cont 0 ( by norm_num );
        convert this.tendsto.mono_left <| nhdsWithin_mono _ _ using 2 <;> aesop;
      · convert Filter.Tendsto.comp ( rpow_const_continuous hs.le |> Continuous.continuousAt ) ( show Filter.Tendsto ( fun ε : ℝ => σ₂ε ε ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) ( nhds ( σ₂ ) ) from ?_ ) using 2;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by aesop ) );
      · refine' tendsto_nhdsWithin_of_tendsto_nhds _;
        refine' ContinuousAt.tendsto _ |> fun h => h.trans _;
        · refine' ContinuousAt.comp ( _ : ContinuousAt ( fun x : HermitianMat d ℂ => x ^ s ) _ ) _;
          · exact ContinuousAt.comp ( rpow_const_continuous hs.le |> Continuous.continuousAt ) continuousAt_id;
          · fun_prop (disch := solve_by_elim);
        · simp +zetaDelta at *;
    -- By the properties of the limit, we can bring the limit inside the inequality.
    have h_limit : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0), t • (σ₁ε ε) ^ s + (1 - t) • (σ₂ε ε) ^ s ≤ (t • σ₁ε ε + (1 - t) • σ₂ε ε) ^ s := by
      filter_upwards [ self_mem_nhdsWithin ] with ε hε using rpow_operator_concave_posDef ( h_pos_def ε hε |>.1 ) ( h_pos_def ε hε |>.2 ) hs hs1 ht ht1;
    exact le_of_tendsto_of_tendsto ( Filter.Tendsto.add ( tendsto_const_nhds.smul h_cont.1 ) ( tendsto_const_nhds.smul h_cont.2.1 ) ) h_cont.2.2 h_limit;
  · norm_num [ show s = 1 by linarith ]

/-! ## Trace inner product monotonicity -/

/-
The inner product `⟪H, A⟫` is nonneg when both `H` and `A` are PSD.
-/
omit [DecidableEq d] in
lemma inner_nonneg_of_nonneg (H A : HermitianMat d ℂ) (hH : 0 ≤ H) (hA : 0 ≤ A) :
    0 ≤ ⟪H, A⟫_ℝ :=
  inner_ge_zero hH hA

/-
The inner product `⟪H, ·⟫` is monotone for `H ≥ 0`: if `A ≤ B` then `⟪H, A⟫ ≤ ⟪H, B⟫`.
-/
omit [DecidableEq d] in
lemma inner_le_inner_of_nonneg (H : HermitianMat d ℂ) (hH : 0 ≤ H)
    {A B : HermitianMat d ℂ} (hAB : A ≤ B) :
    ⟪H, A⟫_ℝ ≤ ⟪H, B⟫_ℝ := by
  rw [ ← sub_nonneg, ← inner_sub_right ];
  apply_rules [ inner_nonneg_of_nonneg ]
  exact mat_posSemidef_to_nonneg hAB

/-! ## Epstein's theorem: p = 1 case -/

/-
**Epstein's theorem, p = 1 case**: For `H ≥ 0` fixed and `0 < 2s ≤ 1`, the map
  `σ ↦ Tr[H σ^{2s}] = ⟪H, σ^{2s}⟫` is concave on PSD matrices.

  This follows from:
  - Operator concavity of `σ ↦ σ^{2s}` (since `2s ≤ 1`).
  - Monotonicity of `⟪H, ·⟫` for `H ≥ 0`.
-/
lemma epstein_concavity_p_one (H : HermitianMat d ℂ) (hH : 0 ≤ H)
    {s : ℝ} (hs : 0 < s) (hs2 : 2 * s ≤ 1) :
    ConcaveOn ℝ {σ : HermitianMat d ℂ | 0 ≤ σ}
      (fun σ ↦ ⟪H, σ ^ (2 * s)⟫_ℝ) := by
  refine' ⟨ convex_psd, _ ⟩;
  intro σ₁ hσ₁ σ₂ hσ₂ a b ha hb hab;
  convert inner_le_inner_of_nonneg H hH ( rpow_operator_concave ( show 0 < 2 * s by positivity ) hs2 σ₁ σ₂ hσ₁ hσ₂ a ha ( by linarith ) ) using 1;
  · simp [ ← hab, inner_add_right, inner_smul_right ];
  · rw [ ← hab, add_sub_cancel_left ]

/-! ## Epstein's theorem: general case -/

/-
For p = 1, `Tr[H.conj (σ^s).mat] = ⟪H, σ^{2s}⟫`, connecting to `epstein_concavity_p_one`.
-/
private lemma epstein_trace_eq_inner (H σ : HermitianMat d ℂ) (hσ : 0 ≤ σ)
    {s : ℝ} (hs : 0 < s) :
    ((H.conj (σ ^ s).mat) ^ (1 : ℝ)).trace = ⟪H, σ ^ (2 * s)⟫_ℝ := by
  rw [HermitianMat.rpow_one];
  unfold conj;
  simp [ two_mul, Matrix.mul_assoc, Matrix.trace_mul_comm ( σ ^ s |> HermitianMat.mat ), HermitianMat.trace ];
  -- By definition of $σ^s$, we know that $(σ^s)^2 = σ^{2s}$.
  have h_sq : (σ ^ s).mat * (σ ^ s).mat = (σ ^ (2 * s)).mat := by
    rw [ two_mul, HermitianMat.mat_rpow_add ];
    · exact hσ;
    · linarith;
  simp [ ← two_mul, h_sq, Inner.inner ]

/-! ## Helper lemmas for the p > 1 case

The proof of Epstein's theorem for `p > 1` is decomposed into:

1. **`trace_rpow_mono`**: Trace monotonicity of rpow for `p ≥ 1`:
   `0 ≤ A ≤ B → Tr[A^p] ≤ Tr[B^p]`.

2. **`lieb_concavity_2sp_eq_one`**: Lieb's concavity theorem for the critical case `2sp = 1`:
   `σ ↦ Tr[(σ^{1/(2p)} H σ^{1/(2p)})^p]` is concave on PSD matrices.

3. The general `2sp ≤ 1` case follows by composing operator concavity of `σ^t` (for `t ≤ 1`)
   with the monotone concave function from (2), using (1) for monotonicity.
-/

/-
For PSD `A`, `⟪A, A^(p-1)⟫ = Tr[A^p]` when `p ≥ 1`.
  This uses the fact that `A` commutes with `A^(p-1)` (both are functions of `A`
  via the CFC), so `A * A^(p-1) = A^p`.
-/
private lemma inner_self_rpow_eq_trace (A : HermitianMat d ℂ) (hA : 0 ≤ A)
    {p : ℝ} (hp : 1 ≤ p) :
    ⟪A, A ^ (p - 1)⟫_ℝ = (A ^ p).trace := by
  -- By definition of the inner product for Hermitian matrices, we have ⟪A, A^(p-1)⟫ = Re(Tr(A * (A^(p-1)))). Since A and A^(p-1) are both functions of A via the CFC, they commute. Moreover, A.mat * (A^(p-1)).mat = (A^p).mat by mat_rpow_add (with exponents 1 and p-1, which sum to p).
  have h_comm : A.mat * (A ^ (p - 1)).mat = (A ^ p).mat := by
    have h_comm : (A ^ (1 : ℝ)).mat * (A ^ (p - 1)).mat = (A ^ p).mat := by
      rw [ ← mat_rpow_add hA ];
      · rw [ add_sub_cancel ];
      · linarith;
    aesop;
  convert congr_arg RCLike.re ( congr_arg Matrix.trace h_comm ) using 1

/-
Trace monotonicity of rpow for `1 ≤ p ≤ 2`: uses Löwner-Heinz to get
  `A^(p-1) ≤ B^(p-1)` (since `p-1 ≤ 1`), then the inner product decomposition.
-/
private lemma trace_rpow_mono_le_two {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (hAB : A ≤ B)
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    (A ^ p).trace ≤ (B ^ p).trace := by
  -- Decompose: Tr[B^p] - Tr[A^p] = ⟪B-A, B^{p-1}⟫ + ⟪A, B^{p-1} - A^{p-1}⟫ ≥ 0.
  have h_decomp : (B ^ p).trace - (A ^ p).trace = ⟪B - A, B ^ (p - 1)⟫_ℝ + ⟪A, B ^ (p - 1) - A ^ (p - 1)⟫_ℝ := by
    have h_decomp : (B ^ p).trace = ⟪B, B ^ (p - 1)⟫_ℝ ∧ (A ^ p).trace = ⟪A, A ^ (p - 1)⟫_ℝ := by
      exact ⟨ by rw [ inner_self_rpow_eq_trace B ( show 0 ≤ B from le_trans hA hAB ) ( by linarith ) ], by rw [ inner_self_rpow_eq_trace A hA ( by linarith ) ] ⟩;
    simp [ h_decomp, inner_sub_left, inner_sub_right ];
  -- First term: $B - A \geq 0$ (hAB) and $B^{p-1} \geq 0$ (rpow_nonneg for PSD B, where B ≥ A ≥ 0).
  have h_first_term : 0 ≤ ⟪B - A, B ^ (p - 1)⟫_ℝ := by
    apply_rules [ inner_nonneg_of_nonneg ];
    · exact mat_posSemidef_to_nonneg hAB;
    · exact HermitianMat.rpow_nonneg ( by exact le_trans hA hAB );
  -- Second term: Since $0 < p-1 \le 1$ (from hp and hp2), by rpow_le_rpow_of_le: $A^{p-1} \le B^{p-1}$. So $B^{p-1} - A^{p-1} \ge 0$. And $A \ge 0$. So ⟪A, B^{p-1} - A^{p-1}⟫ \ge 0 by inner_ge_zero.
  have h_second_term : 0 ≤ ⟪A, B ^ (p - 1) - A ^ (p - 1)⟫_ℝ := by
    apply_rules [ inner_nonneg_of_nonneg, hA, sub_nonneg_of_le ];
    by_cases hp1 : p - 1 = 0;
    · aesop;
    · exact rpow_le_rpow_of_le hA hAB ( lt_of_le_of_ne ( by linarith ) ( Ne.symm hp1 ) ) ( by linarith );
  linarith

/-
Trace monotonicity of rpow: for `0 ≤ A ≤ B` and `p ≥ 1`, `Tr[A^p] ≤ Tr[B^p]`.

  **Proof**: For `p = 1`, this is trace monotonicity. For `p > 1`, use Young's inequality:
  1. `Tr[A^p] = ⟪A, A^(p-1)⟫` (by `inner_self_rpow_eq_trace`)
  2. `≤ ⟪B, A^(p-1)⟫` (since `A ≤ B` and `A^(p-1) ≥ 0`)
  3. `≤ Tr[B^p]/p + Tr[(A^(p-1))^q]/q` (by `trace_young`, with `q = p/(p-1)`)
  4. `= Tr[B^p]/p + Tr[A^p]/q` (since `(A^(p-1))^q = A^p`)
  Rearranging: `Tr[A^p]/p ≤ Tr[B^p]/p`, hence `Tr[A^p] ≤ Tr[B^p]`.
-/
lemma trace_rpow_mono {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (hAB : A ≤ B)
    {p : ℝ} (hp : 1 ≤ p) :
    (A ^ p).trace ≤ (B ^ p).trace := by
  by_cases hp' : 1 < p;
  · -- By Young's inequality:
    have h_young : ⟪B, A ^ (p - 1)⟫_ℝ ≤ (B ^ p).trace / p + ((A ^ (p - 1)) ^ (p / (p - 1))).trace / (p / (p - 1)) := by
      apply_rules [ HermitianMat.trace_young ];
      · exact le_trans hA hAB;
      · exact rpow_nonneg hA;
      · grind;
    -- By the properties of the trace and the inner product, we have:
    have h_trace_inner : (A ^ p).trace = ⟪A, A ^ (p - 1)⟫_ℝ := by
      rw [ ← inner_self_rpow_eq_trace A hA ( by linarith ) ]
    have h_trace_inner_B : ⟪A, A ^ (p - 1)⟫_ℝ ≤ ⟪B, A ^ (p - 1)⟫_ℝ := by
      convert inner_le_inner_of_nonneg ( A ^ ( p - 1 ) ) _ hAB using 1;
      · exact real_inner_comm (A ^ (p - 1)) A;
      · exact real_inner_comm (A ^ (p - 1)) B;
      · exact rpow_nonneg hA;
    have h_trace_inner_A : ((A ^ (p - 1)) ^ (p / (p - 1))).trace = (A ^ p).trace := by
      rw [ ← rpow_mul hA, mul_div_cancel₀ _ ( by linarith ) ];
    field_simp at *;
    nlinarith;
  · norm_num [ show p = 1 by linarith ];
    convert inner_le_inner_of_nonneg ( 1 : HermitianMat d ℂ ) ( by exact zero_le_one' (HermitianMat d ℂ) ) hAB using 1 <;> norm_num [ Matrix.trace_one ]

/-! ## Component lemmas for Lieb's concavity theorem

The proof of `lieb_concavity_2sp_eq_one` is decomposed into 5 major steps:

1. **Quadratic form concavity** (`rpow_quadform_concave`): For `0 < s ≤ 1` and
   a vector `v`, `σ ↦ v† σ^s v` is concave on PSD matrices.

2. **Trace convexity of rpow** (`trace_rpow_convex`): For `p ≥ 1`, the map
   `A ↦ Tr[A^p]` is convex on PSD matrices.

3. **Rank-one Lieb concavity** (`lieb_concavity_rank_one`): For a unit vector `v` and
   `p > 1`, the map `σ ↦ ⟨v, σ^{1/p} v⟩^p` is concave on PSD matrices.
   This is the rank-one case of Lieb's theorem.

4. **Positive definite core** (`lieb_concavity_posDef`): For `H ≥ 0`, `p > 1`, and
   positive definite `σ₁, σ₂`, the concavity inequality holds:
   `t·Tr[f(σ₁)] + (1-t)·Tr[f(σ₂)] ≤ Tr[f(t·σ₁ + (1-t)·σ₂)]`.
   This is the deep step, proved via complex interpolation (Hadamard three-lines theorem).

5. **Extension to PSD** (`lieb_concavity_psd_extension`): The positive definite result
   extends to PSD matrices by ε-perturbation and continuity.
-/

/-
**Step 1: Quadratic form concavity.**
  For `0 < s ≤ 1` and a vector `v`, the map `σ ↦ v† σ^s v` is concave on PSD matrices.
  This follows from operator concavity of `σ^s` (from `rpow_operator_concave`) plus
  the fact that the inner product `⟨v, A v⟩` is a monotone linear functional of `A`.
-/
lemma rpow_quadform_concave (v : d → ℂ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ConcaveOn ℝ {σ : HermitianMat d ℂ | 0 ≤ σ}
      (fun σ ↦ (dotProduct (star v) ((σ ^ s).mat.mulVec v)).re) := by
  have := @rpow_operator_concave;
  refine' ⟨ convex_psd, fun σ₁ hσ₁ σ₂ hσ₂ a b ha hb hab => _ ⟩;
  have := @this d _ _ s hs hs1 σ₁ σ₂ hσ₁ hσ₂ a ha ( by linarith );
  convert Complex.re_le_re ( show star v ⬝ᵥ ( a • σ₁ ^ s + ( 1 - a ) • σ₂ ^ s ).mat.mulVec v ≤ star v ⬝ᵥ ( ( a • σ₁ + ( 1 - a ) • σ₂ ) ^ s ).mat.mulVec v from ?_ ) using 1;
  · simp [ ← hab, Matrix.add_mulVec];
    simp [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm];
  · rw [ ← eq_sub_iff_add_eq' ] at hab ; aesop;
  · have h_inner : ∀ (A B : HermitianMat d ℂ), A ≤ B → star v ⬝ᵥ A.mat.mulVec v ≤ star v ⬝ᵥ B.mat.mulVec v := by
      intro A B hAB;
      have h_inner : ∀ (A : HermitianMat d ℂ), 0 ≤ A → star v ⬝ᵥ A.mat.mulVec v ≥ 0 := by
        intro A hA;
        have := hA.2;
        specialize this ( Finsupp.equivFunOnFinite.symm v ) ; simp_all [ Finsupp.sum_fintype, dotProduct ];
        simpa [ Matrix.mulVec, dotProduct, mul_assoc, Finset.mul_sum _ _ _ ] using this;
      have := h_inner ( B - A ) ( by simpa using hAB );
      simp_all [ Matrix.sub_mulVec, dotProduct_sub ];
    exact h_inner _ _ this

/-
**Step 2: Trace convexity of rpow.**
  For `p ≥ 1`, the map `A ↦ Tr[A^p]` is convex on PSD matrices.
  This follows from the decomposition `Tr[A^p] = ⟪A, A^{p-1}⟫` and the convexity
  of the eigenvalue map combined with the convexity of `x ↦ x^p`.
-/
lemma trace_rpow_convex {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ {A : HermitianMat d ℂ | 0 ≤ A}
      (fun A ↦ (A ^ p).trace) := by
  refine' ⟨ convex_psd, fun A _ B _ a b ha hb hab => _ ⟩;
  have := @rpow_operator_concave d;
  specialize this ( show 0 < 1 / p by positivity ) ( by rw [ div_le_iff₀ ] <;> linarith ) ( A ^ p ) ( B ^ p );
  specialize this ( by
    (expose_names; exact rpow_nonneg h) ) ( by
    (expose_names; exact rpow_nonneg h_1) ) a ha ( by linarith );
  have h_trace : (a • A + b • B) ≤ (a • A ^ p + b • B ^ p) ^ (1 / p) := by
    have h_trace : (A ^ p) ^ (1 / p) = A ∧ (B ^ p) ^ (1 / p) = B := by
      exact ⟨ by rw [ ← rpow_mul ( by assumption ) ] ; norm_num [ show p ≠ 0 by positivity ], by rw [ ← rpow_mul ( by assumption ) ] ; norm_num [ show p ≠ 0 by positivity ] ⟩;
    grind +splitImp only;
  have := @trace_rpow_mono d;
  specialize this ( show 0 ≤ a • A + b • B from ?_ ) h_trace ( show 1 ≤ p by linarith );
  · exact add_nonneg ( smul_nonneg ha ‹_› ) ( smul_nonneg hb ‹_› );
  · refine' le_trans this _;
    rw [ ← rpow_mul ] <;> norm_num [ show p ≠ 0 by positivity ];
    exact add_nonneg ( smul_nonneg ha ( by (expose_names; exact rpow_nonneg h) ) ) ( smul_nonneg hb ( by
    (expose_names; exact rpow_nonneg h_1) ) )

/-! ### Component lemmas for `lieb_concavity_rank_one`
The proof of the rank-one Lieb concavity theorem is decomposed into five steps:
1. **Nonnegativity** (`quadform_rpow_nonneg`): The quadratic form `⟨v, σ^s v⟩` is
   nonneg for PSD `σ`, ensuring `(·)^p` is well-defined.
2. **Self-adjoint identity** (`quadform_rpow_sq_identity`): For PSD `σ`,
   `v† σ^{1/p} v = (σ^{1/(2p)} v)† (σ^{1/(2p)} v)`, connecting to squared norms.
3. **Continuity** (`lieb_rank_one_functional_continuous`): The functional
   `σ ↦ ⟨v, σ^{1/p} v⟩^p` is continuous.
4. **Core inequality for positive definite matrices**
   (`lieb_rank_one_ineq_posDef`): The concavity inequality holds when
   `σ₁, σ₂` are positive definite. This is the deep step, proved via complex
   interpolation (Hadamard three-lines theorem).
5. **Extension to PSD** (`lieb_rank_one_psd_of_posDef`): The positive definite
   result extends to PSD matrices by ε-perturbation and continuity.
-/

/-- **Component 1: Quadratic form nonnegativity.**
  For PSD `σ` and `s > 0`, the quadratic form `(v† σ^s v).re` is nonneg.
  This is immediate from the PSD property of `σ^s`. -/
lemma quadform_rpow_nonneg (v : d → ℂ) (σ : HermitianMat d ℂ) (hσ : 0 ≤ σ)
    {s : ℝ} (_hs : 0 < s) :
    0 ≤ (dotProduct (star v) ((σ ^ s).mat.mulVec v)).re := by
  have hpsd := zero_le_iff.mp (rpow_nonneg hσ (p := s))
  have h_nonneg : 0 ≤ (star v ⬝ᵥ (σ ^ s).mat *ᵥ v) := by
    have h := hpsd.2 (Finsupp.equivFunOnFinite.symm v)
    simp [Finsupp.sum_fintype] at h
    simpa [Matrix.mulVec, dotProduct, mul_assoc, Finset.mul_sum] using h
  exact Complex.le_def.mp h_nonneg |>.1

/--
**Component 2: Self-adjoint quadratic form identity.**
  For PSD `σ`, `v† σ^{1/p} v = (σ^{1/(2p)} v)† (σ^{1/(2p)} v)`.
  This uses `σ^{1/p} = (σ^{1/(2p)})²` (from `mat_rpow_add`) and the fact that
  `σ^{1/(2p)}` is self-adjoint. The RHS is manifestly real and nonneg.
-/
lemma quadform_rpow_sq_identity (v : d → ℂ) (σ : HermitianMat d ℂ) (hσ : 0 ≤ σ)
    {p : ℝ} (hp : 1 < p) :
    dotProduct (star v) ((σ ^ (1 / p)).mat.mulVec v) =
    dotProduct (star ((σ ^ (1 / (2 * p))).mat.mulVec v))
      ((σ ^ (1 / (2 * p))).mat.mulVec v) := by
  -- By definition of exponentiation, we know that $(σ^{1/p}) = (σ^{1/(2p)})^2$.
  have h_exp : (σ ^ (1 / p : ℝ)).mat = (σ ^ (1 / (2 * p) : ℝ)).mat * (σ ^ (1 / (2 * p) : ℝ)).mat := by
    convert mat_rpow_add hσ ( show 1 / ( 2 * p ) + 1 / ( 2 * p ) ≠ 0 from by positivity ) using 1
    ring_nf;
  simp [ Matrix.dotProduct_mulVec];
  simp_all [ Matrix.star_mulVec,dotProduct_comm ]

/-- **Component 3: Continuity of the rank-one Lieb functional.**
  The map `σ ↦ (v† σ^{1/p} v).re ^ p` is continuous on all Hermitian matrices.
  Uses `rpow_const_continuous` for `σ ↦ σ^{1/p}` and continuity of the quadratic form. -/
lemma lieb_rank_one_functional_continuous (v : d → ℂ) {p : ℝ} (hp : 1 < p) :
    Continuous (fun σ : HermitianMat d ℂ ↦
      (dotProduct (star v) ((σ ^ (1 / p)).mat.mulVec v)).re ^ p) := by
  have h_mat_cont : Continuous (fun σ : HermitianMat d ℂ => (σ ^ (1/p : ℝ)).mat) :=
    continuous_subtype_val.comp (rpow_const_continuous (by positivity))
  have h_entry : ∀ i j, Continuous (fun σ : HermitianMat d ℂ => (σ ^ (1/p : ℝ)).mat i j) :=
    fun i j => (continuous_pi_iff.mp (continuous_pi_iff.mp h_mat_cont i) j)
  have h_mulvec_entry : ∀ i, Continuous
      (fun σ : HermitianMat d ℂ => ((σ ^ (1/p : ℝ)).mat.mulVec v) i) := by
    intro i; unfold Matrix.mulVec
    exact continuous_finset_sum _ fun j _ => (h_entry i j).mul continuous_const
  have h_dot : Continuous (fun σ : HermitianMat d ℂ =>
      dotProduct (star v) ((σ ^ (1/p : ℝ)).mat.mulVec v)) :=
    continuous_finset_sum _ fun i _ => continuous_const.mul (h_mulvec_entry i)
  exact (Complex.continuous_re.comp h_dot).rpow_const (fun x => Or.inr (by linarith))

/-! ### Decomposition of lieb_rank_one_ineq_posDef
The proof is decomposed into edge cases and a core inequality.
The core inequality is the genuinely deep step requiring complex interpolation. -/
/-
Edge case: when `v = 0`, all quadratic forms are zero, and the inequality is trivial.
-/
lemma lieb_rank_one_ineq_v_zero {p : ℝ} (hp : 1 < p)
    {σ₁ σ₂ : HermitianMat d ℂ}
    {t : ℝ} :
    t • (dotProduct (star (0 : d → ℂ)) ((σ₁ ^ (1 / p)).mat.mulVec 0)).re ^ p +
    (1 - t) • (dotProduct (star (0 : d → ℂ)) ((σ₂ ^ (1 / p)).mat.mulVec 0)).re ^ p ≤
    (dotProduct (star (0 : d → ℂ)) (((t • σ₁ + (1 - t) • σ₂) ^ (1 / p)).mat.mulVec 0)).re ^ p := by
  simp [ show p ≠ 0 by positivity ]

/-
Edge case: when `t = 0`, the inequality reduces to a trivial identity.
-/
lemma lieb_rank_one_ineq_t_zero (v : d → ℂ) {p : ℝ}
    {σ₁ σ₂ : HermitianMat d ℂ} :
    (0 : ℝ) • (dotProduct (star v) ((σ₁ ^ (1 / p)).mat.mulVec v)).re ^ p +
    (1 - (0 : ℝ)) • (dotProduct (star v) ((σ₂ ^ (1 / p)).mat.mulVec v)).re ^ p ≤
    (dotProduct (star v) ((((0 : ℝ) • σ₁ + (1 - (0 : ℝ)) • σ₂) ^ (1 / p)).mat.mulVec v)).re ^ p := by
  norm_num +zetaDelta at *

/-
Edge case: when `t = 1`, the inequality reduces to a trivial identity.
-/
lemma lieb_rank_one_ineq_t_one (v : d → ℂ) {p : ℝ} {σ₁ σ₂ : HermitianMat d ℂ} :
    (1 : ℝ) • (dotProduct (star v) ((σ₁ ^ (1 / p)).mat.mulVec v)).re ^ p +
    (1 - (1 : ℝ)) • (dotProduct (star v) ((σ₂ ^ (1 / p)).mat.mulVec v)).re ^ p ≤
    (dotProduct (star v) ((((1 : ℝ) • σ₁ + (1 - (1 : ℝ)) • σ₂) ^ (1 / p)).mat.mulVec v)).re ^ p := by
  aesop

/-! ### Rank-one trace identity
The following lemmas establish that for a rank-one PSD matrix `H = |v⟩⟨v|`,
the trace functional `Tr[(H.conj M)^p]` equals `(v† M² v)^p` when `M` is
self-adjoint. This connects `lieb_rank_one_ineq_core` to `lieb_concavity_posDef`. -/
/-- The rank-one HermitianMat formed from a vector `v`. This is `|v⟩⟨v|` as a
  Hermitian matrix, with entries `(rankOneHerm v) i j = v i * starRingEnd ℂ (v j)`. -/
def rankOneHerm (v : d → ℂ) : HermitianMat d ℂ :=
  ⟨Matrix.vecMulVec v (star v), by
    ext i j; simp [Matrix.vecMulVec_apply, mul_comm]⟩

omit [DecidableEq d] in
/--
`rankOneHerm v` is nonneg (PSD).
-/
lemma rankOneHerm_nonneg (v : d → ℂ) : 0 ≤ rankOneHerm v := by
  unfold rankOneHerm;
  refine' ⟨ _, fun x => _ ⟩;
  · ext; simp [ Matrix.vecMulVec, Matrix.conjTranspose ] ; ring!;
  · simp [ Matrix.vecMulVec, Finsupp.sum_fintype ];
    -- By Fubini's theorem, we can interchange the order of summation.
    have h_fubini : ∑ i, ∑ j, (starRingEnd ℂ (x i)) * (v i * (starRingEnd ℂ (v j))) * x j = (∑ i, (starRingEnd ℂ (x i)) * v i) * (∑ j, (starRingEnd ℂ (v j)) * x j) := by
      simp only [mul_left_comm, mul_comm, Finset.mul_sum];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
    rw [ h_fubini, mul_comm ];
    -- The product of a complex number and its conjugate is non-negative.
    have h_conj : ∀ (z : ℂ), 0 ≤ z * starRingEnd ℂ z := by
      simp [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
    convert h_conj ( ∑ j, ( starRingEnd ℂ ) ( v j ) * x j ) using 1 ; simp [ mul_comm ]

omit [DecidableEq d] in
/--
The conjugation of a rank-one matrix by a self-adjoint matrix gives another rank-one matrix:
  `(rankOneHerm v).conj M = rankOneHerm (M.mulVec v)` when `M` is self-adjoint.
  Since `M = (σ^{1/(2p)}).mat` is self-adjoint (Hermitian), `M† = M`, and:
  `M * vecMulVec v (star v) * M = vecMulVec (M v) (star (M v))`.
-/
lemma conj_rankOneHerm_eq (v : d → ℂ) (M : Matrix d d ℂ) :
    (rankOneHerm v).conj M = rankOneHerm (M.mulVec v) := by
  nontriviality;
  ext i;
  unfold conj;
  convert congr_arg ( fun x : ℂ => x ) ( show ( M * ( Matrix.vecMulVec v ( star v ) ) * M.conjTranspose ) i _ = ( Matrix.vecMulVec ( M.mulVec v ) ( star ( M.mulVec v ) ) ) i _ from ?_ ) using 1;
  simp [ Matrix.vecMulVec, Matrix.mul_apply, mul_comm, mul_left_comm, Finset.mul_sum _ _ _]
  simp [ Matrix.mulVec, dotProduct, mul_assoc, mul_comm, Finset.mul_sum _ _ _, Finset.sum_mul ]

set_option maxHeartbeats 800000 in
/--
The trace of `(rankOneHerm v)^p` equals `(v† v).re^p` for `p > 0`.
  For `p = 1`, this is just `‖v‖²`. For general `p`, the rank-one matrix
  has eigenvalue `‖v‖²` so its `p`-th power has eigenvalue `‖v‖^{2p}` and trace `‖v‖^{2p}`.
-/
lemma trace_rpow_rankOneHerm (v : d → ℂ) {p : ℝ} (hp : 0 < p) :
    ((rankOneHerm v) ^ p).trace = (dotProduct (star v) v).re ^ p := by
  have h_eigenvalues : ∃ (eigenvalues : d → ℝ), (rankOneHerm v).H.eigenvalues = eigenvalues ∧ (∑ i, eigenvalues i) = star v ⬝ᵥ v ∧ (∀ i, eigenvalues i ≥ 0) := by
    refine' ⟨ _, rfl, _, _ ⟩
    generalize_proofs at *;
    · have h_trace : Matrix.trace (Matrix.vecMulVec v (star v)) = star v ⬝ᵥ v := by
        simp [ Matrix.trace, Matrix.vecMulVec, dotProduct ];
        ac_rfl
      generalize_proofs at *; (
      have := Matrix.IsHermitian.spectral_theorem ( show Matrix.IsHermitian ( Matrix.vecMulVec v ( star v ) ) from by
                                                      ext i j; simp [ Matrix.vecMulVec] ; ring; )
      generalize_proofs at *; (
      replace this := congr_arg Matrix.trace this ; simp_all [ Matrix.trace ] ;
      simp [ Matrix.mul_apply, Matrix.diagonal ];
      simp [ mul_comm, mul_left_comm];
      simp [ ← mul_assoc, ← Finset.sum_mul, ← Finset.sum_comm ];
      simp [ ← sq, Complex.normSq_apply, Complex.mul_conj];
      have := OrthonormalBasis.orthonormal ( ‹Matrix.IsHermitian ( Matrix.vecMulVec v ( star v ) ) ›.eigenvectorBasis ) ; simp_all [ orthonormal_iff_ite ] ;
      simp_all [ Complex.ext_iff, inner ];
      norm_cast ; simp_all [ sq, Finset.sum_add_distrib ]));
    · intro i;
      grind only [eigenvalues_nonneg, rankOneHerm_nonneg];
  obtain ⟨eigenvalues, heigenvalues_eq, heigenvalues_sum, heigenvalues_nonneg⟩ := h_eigenvalues;
  have h_trace : (rankOneHerm v ^ p).trace = ∑ i, eigenvalues i ^ p := by
    convert trace_rpow_eq_sum ( rankOneHerm v ) p using 1;
    aesop;
  have h_rank_one : (rankOneHerm v).mat.rank ≤ 1 := by
    have h_rank_one : (Matrix.vecMulVec v (star v)).rank ≤ 1 := by
      have h_rank_one : ∀ (u v : d → ℂ), (Matrix.vecMulVec u v).rank ≤ 1 := by
        intro u v
        have h_rank_one : LinearMap.range (Matrix.mulVecLin (Matrix.vecMulVec u v)) ≤ Submodule.span ℂ {u} := by
          intro x hx
          obtain ⟨y, hy⟩ := hx
          generalize_proofs at *;
          exact hy ▸ Submodule.mem_span_singleton.mpr ⟨ ∑ i, y i * v i, by ext i; simp [ Matrix.vecMulVec, Matrix.mulVec, dotProduct, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ⟩
        generalize_proofs at *;
        exact le_trans ( Submodule.finrank_mono h_rank_one ) ( finrank_span_le_card _ ) |> le_trans <| by norm_num;
      exact h_rank_one v (star v);
    exact h_rank_one;
  have h_rank_one : ∑ i, (if eigenvalues i = 0 then 0 else 1) ≤ 1 := by
    have h_rank_one : Matrix.rank (Matrix.diagonal eigenvalues) ≤ 1 := by
      have h_rank_one : Matrix.rank (Matrix.diagonal eigenvalues) ≤ Matrix.rank (rankOneHerm v).mat := by
        have h_rank_one : ∃ (U : Matrix d d ℂ), U * U.conjTranspose = 1 ∧ (rankOneHerm v).mat = U * Matrix.diagonal (fun i => eigenvalues i : d → ℂ) * U.conjTranspose := by
          have := Matrix.IsHermitian.spectral_theorem ( rankOneHerm v ).H;
          refine' ⟨ _, _, _ ⟩;
          exact ( Matrix.IsHermitian.eigenvectorUnitary ( rankOneHerm v ).H ) |> fun x => x.val;
          · simp [ Matrix.IsHermitian.eigenvectorUnitary ];
          · convert this using 1;
            ext i j; simp [ Matrix.mul_apply, Matrix.diagonal_apply ] ;
            grind;
        obtain ⟨ U, hU₁, hU₂ ⟩ := h_rank_one;
        have h_rank_one : Matrix.rank (Matrix.diagonal (fun i => eigenvalues i : d → ℂ)) ≤ Matrix.rank (U * Matrix.diagonal (fun i => eigenvalues i : d → ℂ) * U.conjTranspose) := by
          have h_rank_one : Matrix.rank (Matrix.diagonal (fun i => eigenvalues i : d → ℂ)) ≤ Matrix.rank (U.conjTranspose * (U * Matrix.diagonal (fun i => eigenvalues i : d → ℂ) * U.conjTranspose) * U) := by
            simp [ ← mul_assoc ];
            simp [ Matrix.mul_assoc];
            rw [ ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_eq_one_comm.mp hU₁ ] ; norm_num;
          refine' le_trans h_rank_one _;
          exact Matrix.rank_mul_le_left _ _ |> le_trans <| Matrix.rank_mul_le_right _ _;
        convert h_rank_one using 1;
        · simp [ Matrix.rank_diagonal ];
        · exact hU₂ ▸ rfl;
      exact le_trans h_rank_one ‹_›;
    simp_all [ Matrix.rank_diagonal ];
    simp_all [ Finset.sum_ite ];
    rw [ Fintype.card_subtype ] at h_rank_one ; simp_all [ Finset.filter_not, Finset.card_sdiff ];
  cases h_rank_one.eq_or_lt <;> simp_all [ Finset.sum_ite ];
  · obtain ⟨ i, hi ⟩ := Finset.card_eq_one.mp ‹_›;
    simp_all [ Finset.ext_iff];
    rw [ ← heigenvalues_sum, Finset.sum_eq_single i ] <;> simp_all [ Complex.ext_iff ];
    · rw [ ← heigenvalues_sum.1, Finset.sum_eq_single i ] <;> simp_all
      exact fun j hj => Classical.not_not.1 fun h => hj <| hi j |>.1 h;
    · intro j hj; specialize hi j; simp_all
      rw [ heigenvalues_sum.2.symm, Real.zero_rpow ( by linarith ) ];
  · simp [ ← heigenvalues_sum, hp.ne' ]

/-
Key trace identity: For rank-one `H = |v⟩⟨v|` and self-adjoint PSD `σ`,
  `Tr[(H.conj (σ^{1/(2p)}).mat)^p] = ((v† σ^{1/p} v).re)^p`.
  **Proof:** Combine `conj_rankOneHerm_eq`, `trace_rpow_rankOneHerm`, and
  `quadform_rpow_sq_identity`.
-/
lemma trace_rpow_rankOne_conj (v : d → ℂ) (σ : HermitianMat d ℂ) (hσ : 0 ≤ σ)
    {p : ℝ} (hp : 1 < p) :
    (((rankOneHerm v).conj (σ ^ (1 / (2 * p))).mat) ^ p).trace =
    (dotProduct (star v) ((σ ^ (1 / p)).mat.mulVec v)).re ^ p := by
  -- Uses conj_rankOneHerm_eq, trace_rpow_rankOneHerm, and quadform_rpow_sq_identity
  -- Apply the identity `trace_rpow_rankOneHerm` to simplify the trace expression.
  have h_trace_rpow_rankOneHerm : ((rankOneHerm ((σ ^ (1 / (2 * p))).mat.mulVec v)) ^ p).trace = ((star ((σ ^ (1 / (2 * p))).mat.mulVec v) ⬝ᵥ ((σ ^ (1 / (2 * p))).mat.mulVec v)).re ^ p) := by
    convert trace_rpow_rankOneHerm _ _;
    positivity;
  convert h_trace_rpow_rankOneHerm using 2;
  · rw [ conj_rankOneHerm_eq ];
  · convert congr_arg Complex.re ( quadform_rpow_sq_identity v σ hσ hp ) using 1

/-- **Core concavity inequality** (strict interior case).
  For positive definite `σ₁, σ₂`, `0 < t < 1`, `v ≠ 0`, and `p > 1`:
  `t · (v† σ₁^{1/p} v)^p + (1-t) · (v† σ₂^{1/p} v)^p ≤ (v† (tσ₁+(1-t)σ₂)^{1/p} v)^p`.
  This follows from `lieb_concavity_posDef` applied to the rank-one PSD matrix
  `H = rankOneHerm v`, using `trace_rpow_rankOne_conj` to convert between
  the trace formulation and the quadratic form formulation.
  **Proof strategy (complex interpolation):**
  Let `C = t•σ₁ + (1-t)•σ₂` (positive definite). For `k ∈ {1, 2}`, define:
  `Fₖ(z) = (C^{z/(2p)} v)† σₖ^{1/p} (C^{z/(2p)} v)`
  where `C^{z/(2p)}` uses the complex matrix power (defined via the spectral
  decomposition `C = U D U†` as `C^w = U D^w U†` with `D^w = diag(dᵢ^w)`).
  Applying the Hadamard three-lines theorem gives the bound, which when
  combined with the rank-one trace identity yields the concavity inequality.
  **Alternative:** Derive directly from `lieb_concavity_posDef` using
  `trace_rpow_rankOne_conj` and `rankOneHerm_nonneg`. -/
lemma lieb_rank_one_ineq_core (v : d → ℂ) (hv : v ≠ 0) {p : ℝ} (hp : 1 < p)
    {σ₁ σ₂ : HermitianMat d ℂ} (hσ₁ : σ₁.mat.PosDef) (hσ₂ : σ₂.mat.PosDef)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    t • (dotProduct (star v) ((σ₁ ^ (1 / p)).mat.mulVec v)).re ^ p +
    (1 - t) • (dotProduct (star v) ((σ₂ ^ (1 / p)).mat.mulVec v)).re ^ p ≤
    (dotProduct (star v) (((t • σ₁ + (1 - t) • σ₂) ^ (1 / p)).mat.mulVec v)).re ^ p := by
  -- This can be proved via complex interpolation
  -- (Hadamard three-lines theorem).
  sorry

/-- **Component 4: Core concavity inequality for positive definite matrices.**
  For positive definite `σ₁, σ₂` and `0 ≤ t ≤ 1`, the rank-one Lieb concavity
  inequality holds:
  `t · (v† σ₁^{1/p} v)^p + (1-t) · (v† σ₂^{1/p} v)^p ≤ (v† (tσ₁+(1-t)σ₂)^{1/p} v)^p`.
  **Proof method**: This is the deep step. The proof uses complex interpolation:
  1. Define `F(z) = v† C^{z̄/(2p)} σ₁ C^{z/(2p)} v` where `C = tσ₁ + (1-t)σ₂`.
  2. `F` is analytic in the strip `{0 ≤ Re(z) ≤ 1}` (complex matrix powers are
     analytic for positive definite matrices).
  3. On `Re(z) = 0`: `C^{iy/(2p)}` is unitary, so `|F(iy)| ≤ v† σ₁ v`.
  4. On `Re(z) = 1`: `|F(1+iy)| ≤ v† C^{1/(2p)} σ₁ C^{1/(2p)} v`.
  5. The Hadamard three-lines theorem
     (`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`)
     interpolates these bounds, yielding the concavity inequality after raising
     to the `p`-th power and summing the symmetric bound for `σ₂`. -/
lemma lieb_rank_one_ineq_posDef (v : d → ℂ) {p : ℝ} (hp : 1 < p)
    {σ₁ σ₂ : HermitianMat d ℂ} (hσ₁ : σ₁.mat.PosDef) (hσ₂ : σ₂.mat.PosDef)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t • (dotProduct (star v) ((σ₁ ^ (1 / p)).mat.mulVec v)).re ^ p +
    (1 - t) • (dotProduct (star v) ((σ₂ ^ (1 / p)).mat.mulVec v)).re ^ p ≤
    (dotProduct (star v) (((t • σ₁ + (1 - t) • σ₂) ^ (1 / p)).mat.mulVec v)).re ^ p := by
  by_cases hv : v = 0
  · subst hv; exact lieb_rank_one_ineq_v_zero hp
  · rcases eq_or_lt_of_le ht with rfl | ht'
    · exact lieb_rank_one_ineq_t_zero v
    · rcases eq_or_lt_of_le ht1 with rfl | ht1'
      · exact lieb_rank_one_ineq_t_one v
      · exact lieb_rank_one_ineq_core v hv hp hσ₁ hσ₂ ht' ht1'

/-- **Component 5: Extension from positive definite to PSD.**
  The rank-one concavity inequality extends from positive definite to PSD
  matrices by ε-perturbation: replace `σ` by `σ + ε·I` (positive definite
  for `ε > 0`), apply `lieb_rank_one_ineq_posDef`, and take `ε → 0⁺`
  using `lieb_rank_one_functional_continuous`. -/
lemma lieb_rank_one_psd_of_posDef (v : d → ℂ) {p : ℝ} (hp : 1 < p)
    {σ₁ σ₂ : HermitianMat d ℂ} (hσ₁ : 0 ≤ σ₁) (hσ₂ : 0 ≤ σ₂)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t • (dotProduct (star v) ((σ₁ ^ (1 / p)).mat.mulVec v)).re ^ p +
    (1 - t) • (dotProduct (star v) ((σ₂ ^ (1 / p)).mat.mulVec v)).re ^ p ≤
    (dotProduct (star v) (((t • σ₁ + (1 - t) • σ₂) ^ (1 / p)).mat.mulVec v)).re ^ p := by
  -- ε-perturbation: σᵢ + εI is positive definite for ε > 0
  set f := (fun σ : HermitianMat d ℂ ↦
    (dotProduct (star v) ((σ ^ (1 / p)).mat.mulVec v)).re ^ p)
  -- Limits as ε → 0⁺
  have hf_cont := lieb_rank_one_functional_continuous v hp
  have h_lim₁ : Filter.Tendsto (fun ε : ℝ => f (σ₁ + ε • 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f σ₁)) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      (hf_cont.continuousAt.tendsto.comp <| Continuous.tendsto' (by continuity) _ _ (by simp))
  have h_lim₂ : Filter.Tendsto (fun ε : ℝ => f (σ₂ + ε • 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f σ₂)) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      (hf_cont.continuousAt.tendsto.comp <| Continuous.tendsto' (by continuity) _ _ (by simp))
  have h_lim₃ : Filter.Tendsto
      (fun ε : ℝ => f (t • (σ₁ + ε • 1) + (1 - t) • (σ₂ + ε • 1)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (f (t • σ₁ + (1 - t) • σ₂))) := by
    have h_eq : ∀ ε : ℝ, t • (σ₁ + ε • 1) + (1 - t) • (σ₂ + ε • 1) =
        (t • σ₁ + (1 - t) • σ₂) + ε • (1 : HermitianMat d ℂ) := by
      intro ε; simp only [smul_add, smul_smul]
      have : (t * ε) • (1 : HermitianMat d ℂ) + ((1 - t) * ε) • 1 = ε • 1 := by
        rw [← add_smul]; ring_nf
      calc t • σ₁ + (t * ε) • (1 : HermitianMat d ℂ) + ((1 - t) • σ₂ + ((1 - t) * ε) • 1)
          = t • σ₁ + (1 - t) • σ₂ +
            ((t * ε) • (1 : HermitianMat d ℂ) + ((1 - t) * ε) • 1) := by abel
        _ = t • σ₁ + (1 - t) • σ₂ + ε • 1 := by rw [this]
    simp_rw [h_eq]
    exact tendsto_nhdsWithin_of_tendsto_nhds
      (hf_cont.continuousAt.tendsto.comp <|
        Continuous.tendsto' (by continuity) _ _ (by simp))
  -- The inequality holds for σᵢ + εI (positive definite)
  have h_ineq : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      t • f (σ₁ + ε • 1) + (1 - t) • f (σ₂ + ε • 1) ≤
      f (t • (σ₁ + ε • 1) + (1 - t) • (σ₂ + ε • 1)) := by
    refine Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => ?_
    apply lieb_rank_one_ineq_posDef v hp _ _ ht ht1
    · have h_pd : (ε • (1 : HermitianMat d ℂ)).mat.PosDef := by
        rw [HermitianMat.mat_smul, HermitianMat.mat_one]
        exact Matrix.PosDef.one.smul hε.out
      exact posDef_of_posDef_le h_pd (le_add_of_nonneg_left hσ₁)
    · have h_pd : (ε • (1 : HermitianMat d ℂ)).mat.PosDef := by
        rw [HermitianMat.mat_smul, HermitianMat.mat_one]
        exact Matrix.PosDef.one.smul hε.out
      exact posDef_of_posDef_le h_pd (le_add_of_nonneg_left hσ₂)
  exact le_of_tendsto_of_tendsto
    (Filter.Tendsto.add (tendsto_const_nhds.mul h_lim₁) (tendsto_const_nhds.mul h_lim₂))
    h_lim₃ h_ineq

/-- **Rank-one Lieb concavity theorem.**
  For a vector `v` and `p > 1`, the map `σ ↦ ⟨v, σ^{1/p} v⟩^p` is concave on PSD matrices.
  This is the rank-one case of Lieb's concavity theorem.

  **Proof sketch (via complex interpolation):**
  For fixed PSD `σ₁, σ₂` and `t ∈ [0,1]`, define `σ_t = t σ₁ + (1-t) σ₂`.
  Consider `F(z) = ⟨v, σ₁^{z/p} σ_t^{(1-z)/p} v⟩` for `z` in the strip `0 ≤ Re(z) ≤ 1`.
  By the Hadamard three-lines theorem (`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`),
  `|F(t)| ≤ sup_{Re z = 0} |F(z)|^{1-t} · sup_{Re z = 1} |F(z)|^t`.
  On `Re(z) = 0`: `|F(iy)| ≤ ⟨v, σ_t^{1/p} v⟩` (unitary invariance of the spectral norm).
  On `Re(z) = 1`: `|F(1+iy)| ≤ ⟨v, σ₁^{1/p} v⟩` (similarly).
  Taking p-th powers and summing the symmetric bound for `σ₂` yields concavity. -/
lemma lieb_concavity_rank_one (v : d → ℂ) {p : ℝ} (hp : 1 < p) :
    ConcaveOn ℝ {σ : HermitianMat d ℂ | 0 ≤ σ}
      (fun σ ↦ (dotProduct (star v) ((σ ^ (1 / p)).mat.mulVec v)).re ^ p) := by
  refine ⟨convex_psd, fun σ₁ hσ₁ σ₂ hσ₂ a b ha hb hab => ?_⟩
  have hb1 : b = 1 - a := by linarith
  subst hb1
  exact lieb_rank_one_psd_of_posDef v hp hσ₁ hσ₂ ha (by linarith)

/-! ### Helper lemmas for `lieb_concavity_posDef`
The proof of `lieb_concavity_posDef` proceeds by:
1. **Unitary reduction** (`lieb_functional_eq_diagonal`): Using the spectral decomposition
   `H = (diagonal eigenvalues).conj U`, show that the trace functional with general H
   equals the same functional with diagonal H after a unitary change of basis on σ.
2. **Diagonal case** (`lieb_concavity_diagonal`): Prove the concavity for diagonal H.
   This is the core step. It can be further decomposed:
   a. For rank-one diagonal (single nonzero eigenvalue), reduce to `lieb_concavity_rank_one`.
   b. For general diagonal, use a sum decomposition.
-/

/--
Trace is invariant under unitary conjugation:
  `Tr[U A U†] = Tr[A]` for unitary `U`.
-/
lemma trace_conj_unitary (A : HermitianMat d ℂ) (U : Matrix.unitaryGroup d ℂ) :
    (A.conj U.val).trace = A.trace := by
  unfold HermitianMat.trace;
  erw [ Matrix.trace_mul_comm ] ; simp
  simp [ ← mul_assoc];
  rw [ show ( U : Matrix d d ℂ ) ᴴ * ( U : Matrix d d ℂ ) = 1 from ?_ ];
  · rw [ one_mul ];
  · exact U.2.1

/-- Trace of rpow is invariant under unitary conjugation:
  `Tr[(U A U†)^r] = Tr[A^r]` for unitary `U`. -/
lemma trace_rpow_conj_unitary (A : HermitianMat d ℂ) (U : Matrix.unitaryGroup d ℂ) {r : ℝ} :
    ((A.conj U.val) ^ r).trace = (A ^ r).trace := by
  rw [rpow_conj_unitary]
  exact trace_conj_unitary _ _

/--
Eigenvalues of a PSD matrix are nonneg.
-/
lemma eigenvalues_nonneg_of_psd (A : HermitianMat d ℂ) (hA : 0 ≤ A) :
    ∀ i, 0 ≤ A.H.eigenvalues i := by
  exact eigenvalues_nonneg hA

/--
PosDef is preserved under unitary conjugation.
-/
lemma posDef_conj_unitary {σ : HermitianMat d ℂ} (U : Matrix.unitaryGroup d ℂ)
    (hσ : σ.mat.PosDef) : (σ.conj U.val).mat.PosDef := by
  simp [  Matrix.mul_assoc ];
  convert hσ.conjTranspose_mul_mul_same _ using 1;
  rotate_left;
  exact inferInstance;
  exact U.val.conjTranspose;
  · exact Matrix.mulVec_injective_of_invertible _;
  · simp [ Matrix.mul_assoc ]

/-- Convex combinations are preserved under conjugation. -/
lemma conj_smul_add (σ₁ σ₂ : HermitianMat d ℂ) (t : ℝ) (B : Matrix d d ℂ) :
    (t • σ₁ + (1 - t) • σ₂).conj B = t • (σ₁.conj B) + (1 - t) • (σ₂.conj B) := by
  change (conjLinear ℝ B) (t • σ₁ + (1 - t) • σ₂) = t • (conjLinear ℝ B) σ₁ + (1 - t) • (conjLinear ℝ B) σ₂
  simp [map_add, map_smul]

/--
The Lieb trace functional expressed via spectral decomposition.
  For `H = (diagonal D).conj U` (spectral decomposition), the trace functional
  `Tr[(H.conj M)^p]` equals `Tr[((diagonal D).conj (τ^s))^p]` where `τ = σ.conj U†`.
  More precisely: `H.conj M = ((diagonal D).conj N).conj U` where `N = (τ^s).mat`
  and `τ = σ.conj U†`, so `Tr[(H.conj M)^p] = Tr[((diagonal D).conj N)^p]` by
  trace unitary invariance.
-/
lemma lieb_functional_eq_diagonal (σ H : HermitianMat d ℂ) {s p : ℝ} :
    ((H.conj (σ ^ s).mat) ^ p).trace =
    (((diagonal ℂ H.H.eigenvalues).conj
      ((σ.conj H.H.eigenvectorUnitary.val.conjTranspose) ^ s).mat) ^ p).trace := by
  -- Let's denote the eigenvector unitary matrix of H as U.
  set U := H.H.eigenvectorUnitary with hU;
  -- By definition of $U$, we know that $H = (diagonal D).conj U$.
  have hH : H = (diagonal ℂ H.H.eigenvalues).conj U := by
    convert eq_conj_diagonal H using 1;
  -- By definition of $U$, we know that $(σ^s).mat * U = U * ((σ.conj U†)^s).mat$.
  have h_conj : (σ ^ s).mat * U.val = U.val * ((σ.conj U.val.conjTranspose) ^ s).mat := by
    have h_conj : (σ.conj U.val.conjTranspose) ^ s = (σ ^ s).conj U.val.conjTranspose := by
      convert rpow_conj_unitary σ ( U⁻¹ ) s using 1;
    -- Since $U$ is unitary, we have $U * Uᴴ = 1$.
    have h_unitary : U.val * U.val.conjTranspose = 1 := by
      exact U.2.2;
    simp [ h_conj, mul_assoc];
    simp [ ← mul_assoc, h_unitary ];
  -- By definition of $U$, we know that $(σ^s).mat * U = U * ((σ.conj U†)^s).mat$, so we can rewrite the left-hand side.
  have h_lhs : ((conj ↑(σ ^ s)) H) = (conj U.val) ((conj ↑((σ.conj U.val.conjTranspose) ^ s)) (diagonal ℂ H.H.eigenvalues)) := by
    rw [ hH ];
    simp [ ← h_conj, conj_conj ];
    grind;
  rw [ h_lhs, HermitianMat.trace_rpow_conj_unitary ]

/-- **Lieb concavity for diagonal H**: Follows from
  restricted to positive definite matrices. -/
lemma lieb_concavity_diagonal (D : d → ℝ) (hD : ∀ i, 0 ≤ D i)
    {p : ℝ} (hp : 1 < p)
    {τ₁ τ₂ : HermitianMat d ℂ} (hτ₁ : τ₁.mat.PosDef) (hτ₂ : τ₂.mat.PosDef)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t • (((diagonal ℂ D).conj (τ₁ ^ (1 / (2 * p))).mat) ^ p).trace +
    (1 - t) • (((diagonal ℂ D).conj (τ₂ ^ (1 / (2 * p))).mat) ^ p).trace ≤
    (((diagonal ℂ D).conj ((t • τ₁ + (1 - t) • τ₂) ^ (1 / (2 * p))).mat) ^ p).trace := by
  sorry

/-- **Step 4: Positive definite core of Lieb's concavity.**
  For `H ≥ 0`, `p > 1`, and *positive definite* `σ₁, σ₂`, the concavity inequality:
  `t · Tr[(H.conj (σ₁^s))^p] + (1-t) · Tr[(H.conj (σ₂^s))^p] ≤ Tr[(H.conj ((tσ₁+(1-t)σ₂)^s))^p]`.

  **Proof sketch:**
  The argument reduces to showing that for any matrix `K` with `‖K‖_q ≤ 1`
  (where `q = p/(p-1)` is the conjugate exponent), the bilinear trace functional
  `Tr[K* (H^{1/2} σ^{1/p} H^{1/2})]` satisfies appropriate bounds under interpolation.
  This uses the three-lines theorem applied to the analytic function
  `F(z) = Tr[K* σ₁^{(1-z)/(2p)} H^{1/2} σ_t^{z/p} H^{1/2} σ₂^{(1-z)/(2p)}]`
  in the strip `0 ≤ Re(z) ≤ 1`, where `σ_t = t σ₁ + (1-t) σ₂`.
  On the boundary `Re(z) = 0`, the norm is bounded using Hölder's inequality and
  the Schatten `q`-norm of `K`. On `Re(z) = 1`, the norm is bounded by the
  individual trace values. The three-lines interpolation yields the concavity bound. -/
lemma lieb_concavity_posDef (H : HermitianMat d ℂ) (hH : 0 ≤ H)
    {p : ℝ} (hp : 1 < p)
    {σ₁ σ₂ : HermitianMat d ℂ} (hσ₁ : σ₁.mat.PosDef) (hσ₂ : σ₂.mat.PosDef)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t • ((H.conj (σ₁ ^ (1 / (2 * p))).mat) ^ p).trace +
    (1 - t) • ((H.conj (σ₂ ^ (1 / (2 * p))).mat) ^ p).trace ≤
    ((H.conj ((t • σ₁ + (1 - t) • σ₂) ^ (1 / (2 * p))).mat) ^ p).trace := by
  -- Step 1: Reduce to diagonal case via spectral decomposition.
  -- Use lieb_functional_eq_diagonal to express each trace functional
  -- in terms of diagonal eigenvalues and conjugated σ.
  rw [lieb_functional_eq_diagonal σ₁ H]
  rw [lieb_functional_eq_diagonal σ₂ H]
  rw [lieb_functional_eq_diagonal (t • σ₁ + (1 - t) • σ₂) H]
  -- Step 2: The change of basis σ ↦ τ = σ.conj U† preserves convex combinations.
  rw [conj_smul_add]
  -- Step 3: Apply the diagonal case with τᵢ = σᵢ.conj U†.
  set V : Matrix.unitaryGroup d ℂ := ⟨H.H.eigenvectorUnitary.val.conjTranspose, by
    constructor <;> {
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
      first | exact H.H.eigenvectorUnitary.prop.2 | exact H.H.eigenvectorUnitary.prop.1 }⟩
  exact lieb_concavity_diagonal _ (eigenvalues_nonneg_of_psd H hH) hp
    (posDef_conj_unitary V hσ₁) (posDef_conj_unitary V hσ₂) ht ht1

/-
**Step 5: Extension from positive definite to PSD.**
  The positive definite concavity result extends to PSD matrices via
  ε-perturbation: replace `σ` by `σ + ε·I` (which is positive definite for `ε > 0`),
  apply `lieb_concavity_posDef`, and take the limit as `ε → 0⁺` using
  the continuity of `σ ↦ ((H.conj (σ^s).mat)^p).trace` (from `rpow_const_continuous`).
-/
lemma lieb_concavity_psd_extension (H : HermitianMat d ℂ) (hH : 0 ≤ H)
    {p : ℝ} (hp : 1 < p)
    {σ₁ σ₂ : HermitianMat d ℂ} (hσ₁ : 0 ≤ σ₁) (hσ₂ : 0 ≤ σ₂)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t • ((H.conj (σ₁ ^ (1 / (2 * p))).mat) ^ p).trace +
    (1 - t) • ((H.conj (σ₂ ^ (1 / (2 * p))).mat) ^ p).trace ≤
    ((H.conj ((t • σ₁ + (1 - t) • σ₂) ^ (1 / (2 * p))).mat) ^ p).trace := by
  -- Apply the continuity of the trace function.
  have h_cont : Continuous (fun σ : HermitianMat d ℂ => ((H.conj (σ ^ (1 / (2 * p))).mat) ^ p).trace) := by
    -- Let's choose any two positive semidefinite matrices `σ₁` and `σ₂`.
    -- We'll use the fact that for any `ε > 0`, `σ₁ + εI` and `σ₂ + εI` are positive definite.
    have h_cont : Continuous (fun σ : HermitianMat d ℂ => ((H.conj (σ ^ (1 / (2 * p))).mat) ^ p).trace) := by
      have h_cont_rpow : Continuous (fun σ : HermitianMat d ℂ => σ ^ (1 / (2 * p))) := by
        exact rpow_const_continuous ( by positivity )
      have h_cont_conj : Continuous (fun σ : HermitianMat d ℂ => H.conj (σ ^ (1 / (2 * p))).mat) := by
        apply_rules [ Continuous.subtype_mk, Continuous.mul, continuous_const ];
        · exact Continuous.subtype_val h_cont_rpow;
        · fun_prop;
      have h_cont_rpow : Continuous (fun σ : HermitianMat d ℂ => ((H.conj (σ ^ (1 / (2 * p))).mat) ^ p)) := by
        convert ( HermitianMat.rpow_const_continuous ( show 0 ≤ p by positivity ) ) |> Continuous.comp <| h_cont_conj using 1;
      have h_cont_trace : Continuous (fun σ : HermitianMat d ℂ => σ.trace) := by
        simp [ HermitianMat.trace ];
        fun_prop;
      exact h_cont_trace.comp h_cont_rpow;
    exact h_cont;
  -- Apply the continuity of the trace function to the limit expression.
  have h_lim : Filter.Tendsto (fun ε : ℝ => ((H.conj ((σ₁ + ε • 1) ^ (1 / (2 * p))).mat) ^ p).trace) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((H.conj (σ₁ ^ (1 / (2 * p))).mat) ^ p).trace) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds ( h_cont.continuousAt.tendsto.comp <| Continuous.tendsto' ( by continuity ) _ _ <| by simp );
  have h_lim₂ : Filter.Tendsto (fun ε : ℝ => ((H.conj ((σ₂ + ε • 1) ^ (1 / (2 * p))).mat) ^ p).trace) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((H.conj (σ₂ ^ (1 / (2 * p))).mat) ^ p).trace) := by
    refine' h_cont.continuousAt.tendsto.comp _;
    exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by simp ) );
  have h_lim₃ : Filter.Tendsto (fun ε : ℝ => ((H.conj ((t • (σ₁ + ε • 1) + (1 - t) • (σ₂ + ε • 1)) ^ (1 / (2 * p))).mat) ^ p).trace) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((H.conj ((t • σ₁ + (1 - t) • σ₂) ^ (1 / (2 * p))).mat) ^ p).trace) := by
    convert h_cont.continuousAt.tendsto.comp _ using 2;
    refine' tendsto_nhdsWithin_of_tendsto_nhds _;
    refine' Continuous.tendsto' _ _ _ _ <;> norm_num;
    fun_prop;
  have h_lim_ineq : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), t • ((H.conj ((σ₁ + ε • 1) ^ (1 / (2 * p))).mat) ^ p).trace + (1 - t) • ((H.conj ((σ₂ + ε • 1) ^ (1 / (2 * p))).mat) ^ p).trace ≤ ((H.conj ((t • (σ₁ + ε • 1) + (1 - t) • (σ₂ + ε • 1)) ^ (1 / (2 * p))).mat) ^ p).trace := by
    refine' Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => _;
    apply_rules [ lieb_concavity_posDef ];
    · convert posDef_of_posDef_le ( show ( ε • 1 : HermitianMat d ℂ ).mat.PosDef from ?_ ) ?_ using 1;
      · simp [ Matrix.PosDef ]
        simp [ Matrix.IsHermitian, Matrix.one_apply ];
        intro x hx; simp [ Finsupp.sum ] ;
        rw [ Finset.sum_congr rfl fun i hi => if_neg ( by aesop ) ];
        simp [  mul_comm, mul_left_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq ];
        exact Finset.sum_pos ( fun i hi => mul_pos ( mod_cast hε ) ( sq_pos_of_pos ( mod_cast norm_pos_iff.mpr ( show x i ≠ 0 from by aesop ) ) ) ) ( by contrapose! hx; aesop );
      · exact le_add_of_nonneg_left hσ₁;
    · convert posDef_of_posDef_le ( show ( ε • 1 : HermitianMat d ℂ ).mat.PosDef from ?_ ) ?_ using 1;
      · simp [ Matrix.PosDef];
        simp [ Matrix.IsHermitian, Matrix.one_apply ];
        intro x hx; simp [ Finsupp.sum ] ;
        rw [ Finset.sum_congr rfl fun i hi => by rw [ if_neg ( by intro H; simp_all [ Finsupp.mem_support_iff ] ) ] ] ; simp [ mul_comm, mul_left_comm ];
        simp [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
        exact Finset.sum_pos ( fun i hi => mul_pos ( mod_cast hε ) ( sq_pos_of_pos ( mod_cast norm_pos_iff.mpr ( show x i ≠ 0 from by aesop ) ) ) ) ( by contrapose! hx; aesop );
      · exact le_add_of_nonneg_left hσ₂;
  exact le_of_tendsto_of_tendsto ( Filter.Tendsto.add ( tendsto_const_nhds.mul h_lim ) ( tendsto_const_nhds.mul h_lim₂ ) ) h_lim₃ h_lim_ineq

/-- **Lieb's concavity theorem** (critical case `2sp = 1`):
  For `H ≥ 0` and `p > 1`, the map `σ ↦ Tr[(σ^{1/(2p)} H σ^{1/(2p)})^p]`
  is concave on PSD matrices.

  This is equivalent to the concavity of `σ ↦ Tr[(H^{1/2} σ^{1/p} H^{1/2})^p]`
  (via the trace identity `trace_conj_rpow_eq`).

  The proof follows from `lieb_concavity_psd_extension` above, which is the
  pointwise concavity inequality, packaged into `ConcaveOn`.

  ## References
  * E.H. Lieb, "Convex trace functions and the Wigner-Yanase-Dyson conjecture", 1973.
  * H. Epstein, "Remarks on two theorems of E. Lieb", 1973. -/
lemma lieb_concavity_2sp_eq_one (H : HermitianMat d ℂ) (hH : 0 ≤ H)
    {p : ℝ} (hp : 1 < p) :
    ConcaveOn ℝ {σ : HermitianMat d ℂ | 0 ≤ σ}
      (fun σ ↦ ((H.conj (σ ^ (1 / (2 * p))).mat) ^ p).trace) := by
  refine ⟨convex_psd, fun σ₁ hσ₁ σ₂ hσ₂ a b ha hb hab => ?_⟩
  have hb1 : b = 1 - a := by linarith
  subst hb1
  exact lieb_concavity_psd_extension H hH hp hσ₁ hσ₂ ha (by linarith)

/-- **Epstein's theorem for p > 1**: For `H ≥ 0`, `p > 1`, `s > 0` with `2sp ≤ 1`,
  the map `σ ↦ Tr[(σ^s H σ^s)^p]` is concave on PSD matrices.

  The proof proceeds by reduction to the critical case `2sp = 1`:
  1. Set `t = 2sp ≤ 1` and observe `σ^s = (σ^t)^{1/(2p)}` (rpow identity).
  2. Define `g(τ) = Tr[(τ^{1/(2p)} H τ^{1/(2p)})^p]`, which is concave
     by `lieb_concavity_2sp_eq_one`.
  3. Show `g` is monotone increasing using `rpow_le_rpow_of_le` (Löwner-Heinz)
     + conjugation order preservation + `trace_rpow_mono`.
  4. Compose: `f(σ) = g(σ^t)` is concave since `σ ↦ σ^t` is operator concave
     (from `rpow_operator_concave`), `g` is concave, and `g` is monotone. -/

/-
The Lieb trace functional `g(τ) = Tr[(H.conj (τ^{1/(2p)}).mat)^p]` is monotone
  increasing on PSD matrices. Uses the trace identity to rewrite as
  `Tr[((τ^{1/p}).conj H.sqrt.mat)^p]`, then Löwner-Heinz + conj_mono + trace_rpow_mono.
-/
private lemma lieb_function_monotone (H : HermitianMat d ℂ) (hH : 0 ≤ H)
    {p : ℝ} (hp : 1 < p)
    {τ₁ τ₂ : HermitianMat d ℂ} (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 ≤ τ₂) (hle : τ₁ ≤ τ₂) :
    ((H.conj (τ₁ ^ (1 / (2 * p))).mat) ^ p).trace ≤
    ((H.conj (τ₂ ^ (1 / (2 * p))).mat) ^ p).trace := by
  rw [ trace_conj_rpow_eq, trace_conj_rpow_eq ];
  any_goals positivity;
  apply_rules [ trace_rpow_mono ];
  · apply_rules [ conj_nonneg, HermitianMat.rpow_nonneg ];
  · apply_rules [ conj_mono, rpow_le_rpow_of_le ];
    · positivity;
    · rw [ mul_div, div_le_iff₀ ] <;> linarith;
  · linarith

private lemma epstein_concavity_p_gt_one (H : HermitianMat d ℂ) (hH : 0 ≤ H)
    {s p : ℝ} (hs : 0 < s) (hp : 1 < p) (hsp : 2 * s * p ≤ 1) :
    ConcaveOn ℝ {σ : HermitianMat d ℂ | 0 ≤ σ}
      (fun σ ↦ ((H.conj (σ ^ s).mat) ^ p).trace) := by
  -- Apply the Lieb concavity result with $t = 2sp$.
  have h_lieb : ConcaveOn ℝ {σ : HermitianMat d ℂ | 0 ≤ σ} (fun σ => ((H.conj (σ ^ (1 / (2 * p))).mat) ^ p).trace) := by
    apply_rules [ lieb_concavity_2sp_eq_one ];
  have := h_lieb.2;
  refine' ⟨ convex_psd, _ ⟩;
  intro x hx y hy a b ha hb hab
  have h_rpow : (a • x + b • y) ^ (2 * s * p) ≥ a • x ^ (2 * s * p) + b • y ^ (2 * s * p) := by
    have := @rpow_operator_concave;
    simpa [ ← hab ] using this ( show 0 < 2 * s * p by positivity ) ( show 2 * s * p ≤ 1 by linarith ) x y hx hy a ha ( by linarith );
  convert this ( show 0 ≤ x ^ ( 2 * s * p ) from ?_ ) ( show 0 ≤ y ^ ( 2 * s * p ) from ?_ ) ha hb hab |> le_trans <| ?_ using 1;
  · simp [ ← rpow_mul ( show 0 ≤ _ from hx ), ← rpow_mul ( show 0 ≤ _ from hy ), mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans hp ) ];
  · exact rpow_nonneg hx;
  · exact rpow_nonneg hy;
  · convert lieb_function_monotone H hH hp _ _ h_rpow using 1;
    · rw [ ← rpow_mul ]
      ring_nf
      norm_num [ show p ≠ 0 by positivity ];
      exact add_nonneg ( smul_nonneg ha hx ) ( smul_nonneg hb hy );
    · refine' add_nonneg _ _;
      · refine' le_trans _ ( smul_le_smul_of_nonneg_left ( show 0 ≤ x ^ ( 2 * s * p ) from _ ) ha );
        · simp
        · exact rpow_nonneg hx;
      · refine' smul_nonneg hb _;
        exact rpow_nonneg hy;
    · apply_rules [ rpow_nonneg, hx, hy ];
      exact add_nonneg ( smul_nonneg ha hx ) ( smul_nonneg hb hy )

/-- **Epstein's theorem**: For `H ≥ 0` fixed, `p ≥ 1`, `s > 0` with `2sp ≤ 1`, the map
  `σ ↦ Tr[(σ^s H σ^s)^p]` is concave on PSD matrices.

  This is the deep content of Lieb's concavity theorem / Epstein's generalization.
  The proof combines the trace identity `trace_conj_rpow_eq` with complex interpolation
  or the Herglotz representation of operator monotone functions.

  When `p = 1`, this reduces to `epstein_concavity_p_one` (trace of operator concave function).
  For `p > 1`, the proof is genuinely harder and requires the full strength of
  Lieb's theorem or Epstein's original argument via the Herglotz representation. -/
theorem epstein_concavity (H : HermitianMat d ℂ) (hH : 0 ≤ H)
    {s p : ℝ} (hs : 0 < s) (hp : 1 ≤ p) (hsp : 2 * s * p ≤ 1) :
    ConcaveOn ℝ {σ : HermitianMat d ℂ | 0 ≤ σ}
      (fun σ ↦ ((H.conj (σ ^ s).mat) ^ p).trace) := by
  rcases eq_or_lt_of_le hp with rfl | hp'
  · -- p = 1 case: reduce to epstein_concavity_p_one
    have h2s : 2 * s ≤ 1 := by linarith [hsp]
    exact (epstein_concavity_p_one H hH hs h2s).congr fun σ hσ =>
      (epstein_trace_eq_inner H σ hσ hs).symm
  · -- p > 1 case: use the deep Lieb/Epstein theorem
    exact epstein_concavity_p_gt_one H hH hs hp' hsp

/-! ## Main result for DPI -/

/-- **Concavity of the trace functional for DPI**: For `α > 1`, `H ≥ 0`, the map
  `σ ↦ Tr[(σ^s H σ^s)^p]` is concave on PSD matrices,
  where `s = (α-1)/(2α)` and `p = α/(α-1)`.

  This is an instance of Epstein's theorem with `2sp = 1`. -/
theorem trace_conj_rpow_concave {α : ℝ} (hα : 1 < α)
    (H : HermitianMat d ℂ) (hH : 0 ≤ H) :
    ConcaveOn ℝ {σ : HermitianMat d ℂ | 0 ≤ σ}
      (fun σ ↦ ((H.conj (σ ^ ((α - 1) / (2 * α))).mat) ^ (α / (α - 1))).trace) := by
  exact epstein_concavity H hH (dpi_s_pos hα) (le_of_lt (dpi_p_gt_one hα))
    (le_of_eq (dpi_2sp_eq_one hα))

end HermitianMat
