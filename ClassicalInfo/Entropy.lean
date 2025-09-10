import ClassicalInfo.Distribution
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import ClassicalInfo.ForMathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! # Shannon entropy

Definitions and facts about the Shannon entropy function -x*ln(x), both on a single
variable and on a distribution.

There is significant overlap with `Real.negMulLog` and `Real.binEntropy` in Mathlib,
and probably these files could be combined in some form. -/

noncomputable section
open NNReal

variable {α : Type u} [Fintype α]

/-- The one-event entropy function, H₁(p) = -p*ln(p). Uses nits. -/
def H₁ : Prob → ℝ :=
  fun x ↦ Real.negMulLog x

/-- H₁ of 0 is zero.-/
@[simp]
def H₁_zero_eq_zero : H₁ 0 = 0 := by
  simp [H₁]

/-- H₁ of 1 is zero.-/
@[simp]
def H₁_one_eq_zero : H₁ 1 = 0 := by
  simp [H₁]

/-- Entropy is nonnegative. -/
theorem H₁_nonneg (p : Prob) : 0 ≤ H₁ p := by
  rw [H₁, Real.negMulLog, neg_mul, Left.nonneg_neg_iff]
  exact Real.mul_log_nonpos p.zero_le_coe p.coe_le_one

/-- Entropy is less than 1. -/
theorem H₁_le_1 (p : Prob) : H₁ p < 1 := by
  rw [H₁]
  by_cases h : p = 0
  · norm_num [h]
  · have hp0 : 0 < p := lt_of_le_of_ne' p.zero_le h
    have h₂ := Real.abs_log_mul_self_lt p hp0 p.coe_le_one
    rw [mul_comm, ← abs_neg, ← neg_mul] at h₂
    exact lt_of_abs_lt h₂

/-- Entropy is at most 1/e. -/
theorem H₁_le_exp_m1 (p : Prob) : H₁ p ≤ Real.exp (-1) :=
  Real.negMulLog_le_rexp_neg_one p.zero_le_coe

theorem H₁_concave : ∀ (x y : Prob), ∀ (p : Prob), p[H₁ x ↔ H₁ y] ≤ H₁ (p[x ↔ y]) := by
  intros x y p
  simp only [H₁, smul_eq_mul, Prob.coe_one_minus, Mixable.mix, Mixable.mix_ab, Mixable.mkT_instUniv,
    Prob.mkT_mixable, Prob.to_U_mixable, Mixable.to_U_instUniv, Prob.to_U_mixable]
  by_cases hxy : x = y
  · subst hxy
    ring_nf
    exact le_refl _
  by_cases hp : (p:ℝ) = 0
  · norm_num [hp]
  by_cases hp₁ : (p:ℝ) = 1
  · norm_num [hp₁]
  rw [← ne_eq] at hxy hp hp₁
  have := Real.strictConcaveOn_negMulLog.2
  replace := @this x ?_ y ?_ ?_ p (1 - p) ?_ ?_ (by linarith)
  · simp only [smul_eq_mul] at this
    apply le_of_lt
    convert this
  · simp only [Set.mem_Ici, Prob.zero_le_coe]
  · simp only [Set.mem_Ici, Prob.zero_le_coe]
  · simpa only [Prob.ne_iff]
  · exact lt_of_le_of_ne p.zero_le_coe hp.symm
  · linarith (config := {splitNe := true}) [p.coe_le_one]

/-- The Shannon entropy of a discrete distribution, H(X) = ∑ H₁(p_x). -/
def Hₛ (d : Distribution α) : ℝ :=
  Finset.sum Finset.univ (fun x ↦ H₁ (d.prob x))

/-- Shannon entropy of a distribution is nonnegative. -/
theorem Hₛ_nonneg (d : Distribution α) : 0 ≤ Hₛ d :=
  Finset.sum_nonneg' fun _ ↦ H₁_nonneg _

/-- Shannon entropy of a distribution is at most ln d. -/
theorem Hₛ_le_log_d (d : Distribution α) : Hₛ d ≤ Real.log (Finset.card Finset.univ (α := α)) := by
  --Thanks Aristotle
  by_cases h : Fintype.card α = 0
  · simp_all only [Finset.card_univ, CharP.cast_eq_zero, Real.log_zero]
    obtain ⟨val, property⟩ := d
    simp_all only [Distribution.funlike_apply, Hₛ]
    rw [ Fintype.card_eq_zero_iff ] at h
    aesop
  · -- Since the sum of the probabilities is 1, we can apply Jensen's inequality for the convex function $-x \log x$.
    have h_jensen : ∀ (p : α → ℝ), (∀ i, 0 ≤ p i ∧ p i ≤ 1) → (∑ i, p i = 1) → (∑ i, p i * Real.log (p i)) ≥ -Real.log (Fintype.card α) := by
      intros p hp hsum
      have h_jensen : (∑ i, p i * Real.log (p i)) ≥ -Real.log (Fintype.card α) := by
        have h_convex : ConvexOn ℝ (Set.Icc 0 1) (fun x => x * Real.log x) := by
          exact ( Real.convexOn_mul_log.subset ( Set.Icc_subset_Ici_self ) ( convex_Icc _ _ ) )
        -- By Jensen's inequality for the convex function $x \mapsto x \log x$, we have:
        have h_jensen : (∑ i, (1 / Fintype.card α : ℝ) • (p i * Real.log (p i))) ≥ ((∑ i, (1 / Fintype.card α : ℝ) • p i) * Real.log (∑ i, (1 / Fintype.card α : ℝ) • p i)) := by
          convert h_convex.map_sum_le _ _ _ <;> aesop;
        simp_all [← Finset.mul_sum];
        nlinarith [ inv_pos.mpr ( by positivity : 0 < ( Fintype.card α : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( Fintype.card α : ℝ ) ≠ 0 ) ];
      exact h_jensen;
    simp_all only [Finset.card_univ]
    obtain ⟨val, property⟩ := d
    simp_all only [Distribution.funlike_apply, Hₛ, H₁]
    simpa [ Real.negMulLog ] using neg_le_neg ( h_jensen _ ( fun i => ⟨ ( val i ) |>.2.1, ( val i ) |>.2.2 ⟩ ) property )

/-- The shannon entropy of a constant variable is zero. -/
@[simp]
theorem Hₛ_constant_eq_zero {i : α} : Hₛ (Distribution.constant i) = 0 := by
  simp [Hₛ, apply_ite]

/-- Shannon entropy of a uniform distribution is ln d. -/
theorem Hₛ_uniform [Nonempty α] :
    Hₛ (Distribution.uniform (α := α)) = Real.log (Finset.univ.card (α := α)) := by
  simp [Hₛ, Distribution.prob, H₁, Real.negMulLog]

/-- Shannon entropy of two-event distribution. -/
theorem Hₛ_coin (p : Prob) : Hₛ (Distribution.coin p) = Real.binEntropy p := by
  simp [Hₛ, H₁, Distribution.coin, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

--TODO:
-- * Shannon entropy is concave under mixing distributions.
-- * Shannon entropy as an expectation value
