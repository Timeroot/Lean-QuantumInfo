import QuantumInfo.ForMathlib.Matrix

/-! Lieb's Inequality .. todo -/

variable {m n : Type*} [Fintype m] [Fintype n] {q r : ℝ}

noncomputable section
open ComplexOrder
open Classical

theorem LiebConcavity (K : Matrix m n ℂ) (hq : 0 ≤ q) (hr : 0 ≤ r) (hqr : q + r ≤ 1) :
    let F : (Matrix m m ℂ × Matrix n n ℂ) → ℝ :=
      fun (x,y) ↦ if h : x.PosSemidef ∧ y.PosSemidef then
        ((h.left.rpow_PosSemidef q).conjTranspose_mul_mul_same K).isHermitian.rinner
        (h.right.rpow_PosSemidef r).isHermitian
      else 0;
    ConvexOn ℝ {(x,y) | x.PosSemidef ∧ y.PosSemidef} F
    := by
  sorry
