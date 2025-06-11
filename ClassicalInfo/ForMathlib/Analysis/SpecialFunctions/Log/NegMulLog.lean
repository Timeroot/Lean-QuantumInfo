import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

noncomputable section
open NNReal

theorem Real.negMulLog_monotoneOn : MonotoneOn Real.negMulLog (Set.Ioc (0 : ℝ) (Real.exp (-1))) := by
  apply monotoneOn_of_deriv_nonneg
  · exact convex_Ioc 0 (exp (-1))
  · apply Continuous.continuousOn
    exact continuous_negMulLog
  · apply DifferentiableOn.mono Real.differentiableOn_negMulLog
    simp only [interior_Ioc, Set.subset_compl_singleton_iff, Set.mem_Ioo, lt_self_iff_false, false_and,
      not_false_eq_true]
  -- Prove derivative positive
  intro x hx
  simp only [interior_Ioc, Set.mem_Ioo] at hx
  rw [deriv_negMulLog (by linarith), sub_nonneg]
  have := log_lt_log hx.left hx.right
  simp at this
  linarith

theorem Real.negMulLog_antitoneOn : AntitoneOn Real.negMulLog (Set.Ici (Real.exp (-1))) := by
  apply antitoneOn_of_deriv_nonpos
  · exact convex_Ici (Real.exp (-1))
  · apply Continuous.continuousOn
    exact continuous_negMulLog
  · apply DifferentiableOn.mono Real.differentiableOn_negMulLog
    simp only [Set.nonempty_Iio, interior_Ici', Set.subset_compl_singleton_iff, Set.mem_Ioi, not_lt]
    exact exp_nonneg (-1)
  intro x hx
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
  rw [deriv_negMulLog]
  simp only [tsub_le_iff_right, zero_add]
  have : log (Real.exp (-1)) < log x := log_lt_log (exp_pos (-1)) hx
  simp only [log_exp] at this
  linarith
  contrapose! hx
  subst hx
  positivity

-- TODO Generalize to all `x`
theorem Real.negMulLog_le_rexp_neg_one (x : ℝ) (hx : 0 < x) :
    Real.negMulLog x ≤ Real.exp (-1) := by
  -- Casework on the trichotomy of `x` being below, above, or equal to `1/e`.
  by_cases hp : x < Real.exp (-1)
  · have p_in_interval : x ∈ Set.Ioc (0 : ℝ) (Real.exp (-1)) := by
      simp only [Set.mem_Ioc]
      constructor
      · linarith
      · linarith
    have einv_in_interval : Real.exp (-1) ∈ Set.Ioc (0 : ℝ) (Real.exp (-1)) := by
      simp only [Set.mem_Ioc, le_refl, and_true]
      linarith
    have : x ≤ Real.exp (-1) := by
      linarith only [hp]
    have := Real.negMulLog_monotoneOn p_in_interval einv_in_interval this
    convert this using 1
    simp [Real.negMulLog]
  by_cases hp' : Real.exp (-1) < x
  · have p_in_interval : x ∈ Set.Ici (Real.exp (-1)) := by
      simp only [Set.mem_Ici]
      linarith
    have einv_in_interval : Real.exp (-1) ∈ Set.Ici (Real.exp (-1)) := by
      simp only [Set.mem_Ici, le_refl]
    have : Real.exp (-1) ≤ x := by
      linarith only [hp']
    have := Real.negMulLog_antitoneOn einv_in_interval p_in_interval this
    convert this using 1
    simp [Real.negMulLog]
  have : x = Real.exp (-1) := by
    linarith only [hp, hp']
  rw [this]
  simp [Real.negMulLog]
