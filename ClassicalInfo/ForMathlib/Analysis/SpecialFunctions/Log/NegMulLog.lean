import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

noncomputable section
open NNReal


theorem continuous_negMulLog : Continuous Real.negMulLog := by
  unfold Real.negMulLog
  have := Continuous.neg Real.continuous_mul_log
  convert Continuous.neg Real.continuous_mul_log using 1
  ext x
  ring

theorem Real.negMulLog_monotoneOn : MonotoneOn Real.negMulLog (Set.Ioc (0 : ℝ) (Real.exp (-1))) := by
  apply monotoneOn_of_deriv_nonneg
  · exact convex_Ioc 0 (exp (-1))
  · apply Continuous.continuousOn
    exact continuous_negMulLog
  · have := Real.differentiableOn_negMulLog
    apply DifferentiableOn.mono this
    aesop
  intro x hx
  simp at hx
  rw [deriv_negMulLog]
  simp
  have : log x < log (Real.exp (-1)) := by
    -- rw [Real.exp_neg]
    apply Real.log_lt_log
    exact hx.1
    exact hx.2
  simp at this
  linarith
  linarith

theorem Real.negMulLog_antitoneOn : AntitoneOn Real.negMulLog (Set.Ici (Real.exp (-1))) := by
  apply antitoneOn_of_deriv_nonpos
  · exact convex_Ici (Real.exp (-1))
  · apply Continuous.continuousOn
    exact continuous_negMulLog
  · have := Real.differentiableOn_negMulLog
    apply DifferentiableOn.mono this
    simp
    exact exp_nonneg (-1)
  intro x hx
  simp at hx
  rw [deriv_negMulLog]
  simp
  have : log (Real.exp (-1)) < log x := by
    -- rw [Real.exp_neg]
    apply Real.log_lt_log
    exact exp_pos (-1)
    exact hx
  simp at this
  linarith
  contrapose! hx
  subst hx
  positivity

-- TODO Generalize to all `x`
theorem Real.negMulLog_le_rexp_neg_one (x : ℝ) (hx : 0 < x) :
    Real.negMulLog x ≤ Real.exp (-1) := by
  -- Case on the trichotomy of `x` being below, above, or equal to `1/e`.
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
      linarith (config := {splitNe := true}) [hp]
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
      linarith (config := {splitNe := true}) [ hp']
    have := Real.negMulLog_antitoneOn einv_in_interval p_in_interval this
    convert this using 1
    simp [Real.negMulLog]
  have : x = Real.exp (-1) := by
    linarith (config := {splitNe := true}) [ hp, hp']
  rw [this]
  simp [Real.negMulLog]
