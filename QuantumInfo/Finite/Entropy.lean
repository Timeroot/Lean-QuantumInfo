import QuantumInfo.Finite.Distribution

noncomputable section
open NNReal

variable {α : Type u} [Fintype α]

/-- The one-event entropy function, H₁(p) = -p*ln(p). Uses nits. -/
def H₁ : Prob → ℝ :=
  fun x ↦ -x * Real.log x

/-- H₁ of 0 is zero.-/
@[simp]
def H₁_zero_eq_zero : H₁ 0 = 0 := by
  norm_num [H₁]

/-- H₁ of 1 is zero.-/
@[simp]
def H₁_one_eq_zero : H₁ 1 = 0 := by
  norm_num [H₁]

/-- Entropy is nonnegative. -/
theorem H₁_pos (p : Prob) : 0 ≤ H₁ p := by
  rw [H₁, neg_mul, Left.nonneg_neg_iff]
  exact Real.mul_log_nonpos p.zero_le_coe p.coe_le_one

/-- Entropy is less than 1. -/
theorem H₁_le_1 (p : Prob) : H₁ p < 1 := by
  rw [H₁]
  by_cases h : 0 = p
  · subst h
    norm_num
  · rw [← ne_eq] at h
    have hp0 : 0 < p := lt_of_le_of_ne p.zero_le h
    have := Real.abs_log_mul_self_lt p hp0 p.coe_le_one
    rw [mul_comm, ← abs_neg, ← neg_mul] at this
    exact lt_of_abs_lt this

-- /-- TODO: Entropy is at most 1/e. -/
-- theorem H₁_le_exp_m1 (p : Prob) : H₁ p ≤ Real.exp (-1) := by
--   rw [H₁]
--   by_cases h : p = 0
--   · subst h
--     norm_num
--     exact Real.exp_nonneg (-1)
--   · sorry

theorem H₁_concave : ∀ x, ∀ y, ∀ (p : Prob), p.mix (H₁ x) (H₁ y) ≤ H₁ (p.mixP x y) := by
  intros x y p
  simp only [Prob.mix, Prob.val_eq_coe, H₁, smul_eq_mul, Prob.coe_one_minus, Prob.mixP, Prob.toReal_mk]
  by_cases hxy : x = y
  · subst hxy
    ring_nf
    linarith
  by_cases hp : (p:ℝ) = 0
  · rw [hp]
    norm_num
  by_cases hp₁ : (p:ℝ) = 1
  · rw [hp₁]
    norm_num
  rw [← ne_eq] at hxy hp hp₁
  have := Real.strictConcaveOn_negMulLog.2
  replace := @this x ?_ y ?_ ?_ p (1-p) ?_ ?_ (by linarith)
  simp only [smul_eq_mul, Real.negMulLog] at this
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

/-- The shannon entropy of a constant variable is zero. -/
@[simp]
theorem Hₛ_constant_eq_zero {i : α} : Hₛ (Distribution.constant i) = 0 := by
  simp [Hₛ, Distribution.constant_def', apply_ite]

--TODO:
-- * Shannon entropy is concave under mixing distributions.
-- * Shannon entropy is nonnegative and at most ln(d.card)/d
-- * Shannon entropy as an expectation value
