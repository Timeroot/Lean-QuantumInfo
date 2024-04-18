--COPIED FROM https://github.com/dupuisf/LFTCM2024TraceClass/blob/master/LFTCM2024TraceClass/Conway/CFC.lean

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.Module

namespace TraceClass

/-!
# Continuous functional calculus definitions

TODO: Merge these with the true CFC definitions coming from the other files.
-/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  [InnerProductSpace ℂ E]

/-- Absolute value of an operator, so |f| -/
def abs (f : E →L[ℂ] E) : E →L[ℂ] E := sorry

/-- Square of an operator, so f^2 -/
def sq (f : E →L[ℂ] E) : E →L[ℂ] E := sorry

/-- Square root of absolute value of an operator, so |f|^{1/2} -/
def sqrt_abs (f : E →L[ℂ] E) : E →L[ℂ] E := sorry

/-- Square root of absolute value is self-adjoint. -/
lemma adjoint_sqrt_abs (f : E →L[ℂ] E) :
  ContinuousLinearMap.adjoint (sqrt_abs f) = sqrt_abs f := by sorry

/-- Absolute value is self-adjoint. -/
lemma adjoint_abs (f : E →L[ℂ] E) :
  ContinuousLinearMap.adjoint (abs f) = abs f := by sorry

/-- Absolute value of adjoint is absolute value. -/
lemma abs_adjoint (f : E →L[ℂ] E) :
  abs (ContinuousLinearMap.adjoint f) = abs f := by sorry

/-- Square of absolute value is adjoint x f. -/
lemma sq_abs_eq_adjoint_self (f : E →L[ℂ] E) :
  sq (abs f) = (ContinuousLinearMap.adjoint f) * f := by sorry

/-- Abs of abs is abs -/
lemma abs_abs (f : E →L[ℂ] E) : abs (abs f) = abs f := sorry

/-- Square root of square is |f| -/
lemma sqrt_sq_eq_abs (f : E →L[ℂ] E) : sqrt_abs (sq (abs f)) = abs f := by sorry

/-- Abs * abs = adjoint x f -/
lemma abs_mul_abs (f : E →L[ℂ] E) (x : E) :
  (abs f) ((abs f) x) = (ContinuousLinearMap.adjoint f) (f x) := by sorry

/-- Norm of abs of vector is self norm  -/
lemma abs_vec_norm (f : E →L[ℂ] E) (x : E) : ‖(abs f) x‖^2 = ‖f x‖^2 := by
  rw [norm_sq_eq_inner (𝕜 := ℂ), norm_sq_eq_inner (𝕜 := ℂ)]
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rw [adjoint_abs, abs_mul_abs]
  rw [← ContinuousLinearMap.adjoint_inner_right]

lemma abs_vec_norm' (f : E →L[ℂ] E) (x : E) : ‖(abs f) x‖₊ = ‖f x‖₊ := by sorry

end

end TraceClass
