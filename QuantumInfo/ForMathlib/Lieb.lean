/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat

/-! Lieb's Inequality .. todo -/

variable {m n : Type*} [Fintype m] [Fintype n] {q r : ℝ}

noncomputable section
open ComplexOrder
open Classical

theorem LiebConcavity (K : Matrix n m ℂ) (hq : 0 ≤ q) (hr : 0 ≤ r) (hqr : q + r ≤ 1) :
  let F : (HermitianMat m ℂ × HermitianMat n ℂ) → ℝ :=
      fun (x,y) ↦ ((x ^ q).conj K).inner (y ^ r);
    ConcaveOn ℝ .univ F := by
  sorry
