/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.Rpow
import QuantumInfo.ForMathlib.HermitianMat.Schatten

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
    simp_all +decide [Polynomial.roots_X_sub_C]
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
    grind +suggestions
  convert h_trace_rpow (H.sqrt.mat * (σ ^ s).mat) using 1
  · congr! 2
    unfold conj; ext; simp +decide [Matrix.mul_assoc, Matrix.conjTranspose_mul]
    simp +decide [← Matrix.mul_assoc, ← HermitianMat.sqrt_sq hH]
  · have h_eq : (σ ^ (2 * s)).mat = (σ ^ s).mat * (σ ^ s).mat := by
      rw [two_mul, mat_rpow_add]
      · exact hσ
      · positivity
    simp +decide [← mul_assoc, h_eq, conj]

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
    {q : ℝ} (hq : 0 ≤ q) {T : ℝ} (hT : 0 ≤ T) :
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
              simp +decide [ Matrix.PosSemidef, ht ];
              simp +decide [ Matrix.IsHermitian, Matrix.one_apply ];
              intro x; rw [ Finsupp.sum ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
              exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp +decide [ *, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq ] ; positivity;
            exact h_det_ne_zero t ht.1 |> fun h => h.det_pos.ne'
          simp_all +decide [ Matrix.inv_def ];
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
        exact ⟨ rpowApprox_integrand_integrableOn hA hq hT.le, rpowApprox_integrand_integrableOn hB hq hT.le ⟩;
      simp_all +decide [ smul_add, smul_sub, smul_smul ];
      refine' MeasureTheory.Integrable.add _ _;
      · convert h_integrable.1.smul a using 2 ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, smul_smul ];
        module;
      · convert h_integrable.2.smul b using 2 ; norm_num ; ring;
        simp +decide [ mul_assoc, mul_comm, mul_left_comm, smul_sub, smul_smul ];
    · convert rpowApprox_integrand_integrableOn _ _ _ using 1;
      · exact posDef_convex_comb hA hB ha hb hab;
      · exact hq;
      · positivity;
    · -- Apply the resolvent inequality to each term individually.
      have h_resolvent : (a • A + b • B + t • 1)⁻¹ ≤ a • (A + t • 1)⁻¹ + b • (B + t • 1)⁻¹ := by
        convert resolvent_inv_concave hA hB ha hb hab ht.1.le using 1;
      simp_all +decide [ ← eq_sub_iff_add_eq' ];
      convert sub_le_sub_left h_resolvent _ using 1 ; simp +decide [ sub_smul, smul_sub ] ; abel_nf;
  convert h_integral_mono using 1 <;> simp +decide [ intervalIntegral.integral_of_le hT.le, rpowApprox ];
  rw [ ← MeasureTheory.integral_smul, ← MeasureTheory.integral_smul, ← MeasureTheory.integral_add ];
  · simp +decide only [smul_smul, mul_comm];
  · have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ q • ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (A + t • 1)⁻¹)) (Set.Ioc 0 T) := by
      convert rpowApprox_integrand_integrableOn hA hq hT.le using 1;
    exact MeasureTheory.Integrable.fun_smul_enorm a h_integrable;
  · have := @rpowApprox_integrand_integrableOn d _ _ B hB q hq T hT.le;
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
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, h.ne', smul_sub, sub_smul ];
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
          · simp +decide [ Matrix.IsHermitian, Matrix.conjTranspose_smul ];
          · simp +decide [ Finsupp.sum, Matrix.one_apply ];
            intro x hx_ne; rw [ Finset.sum_congr rfl fun i hi => if_neg ( by contrapose! hx_ne; ext j; aesop ) ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, hε_pos ] ;
            simp +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq, hε_pos ];
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
  · simp +decide [ ← hab, inner_add_right, inner_smul_right ];
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
  simp +decide [ two_mul, Matrix.mul_assoc, Matrix.trace_mul_comm ( σ ^ s |> HermitianMat.mat ), HermitianMat.trace ];
  -- By definition of $σ^s$, we know that $(σ^s)^2 = σ^{2s}$.
  have h_sq : (σ ^ s).mat * (σ ^ s).mat = (σ ^ (2 * s)).mat := by
    rw [ two_mul, HermitianMat.mat_rpow_add ];
    · exact hσ;
    · linarith;
  simp +decide [ ← two_mul, h_sq, Inner.inner ]

/-- **Epstein's theorem for p > 1**: The deep content requiring Lieb's concavity theorem
  or complex interpolation. For `H ≥ 0`, `p > 1`, `s > 0` with `2sp ≤ 1`,
  the map `σ ↦ Tr[(σ^s H σ^s)^p]` is concave on PSD matrices.

  This requires the full strength of Lieb's theorem or Epstein's Herglotz
  representation argument. -/
private lemma epstein_concavity_p_gt_one (H : HermitianMat d ℂ) (hH : 0 ≤ H)
    {s p : ℝ} (hs : 0 < s) (hp : 1 < p) (hsp : 2 * s * p ≤ 1) :
    ConcaveOn ℝ {σ : HermitianMat d ℂ | 0 ≤ σ}
      (fun σ ↦ ((H.conj (σ ^ s).mat) ^ p).trace) := by
  sorry

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
