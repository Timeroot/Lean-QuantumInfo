/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Analysis.Subadditive

def Superadditive (u : ℕ → ℝ) : Prop :=
  ∀ m n, u (m + n) ≥ u m + u n

namespace Superadditive

variable {u : ℕ → ℝ} (h : Superadditive u)

include h in
theorem to_Subadditive : Subadditive (-u ·) :=
  (by dsimp; linarith [h · ·])

noncomputable def lim (_h : Superadditive u) :=
  sSup ((fun n : ℕ => u n / n) '' .Ici 1)

/-- Fekete's lemma for superadditive sequences: a superadditive sequence which is
  bounded above converges. -/
theorem tendsto_lim (hbdd : BddAbove (Set.range fun n => u n / n)) :
    Filter.Tendsto (fun n => u n / n) .atTop (nhds (h.lim)) := by
  have := h.to_Subadditive.tendsto_lim (hbdd.recOn
    (⟨-·, fun _ hx ↦ neg_le.mp <| ·
    (hx.recOn (⟨·, by rw [← ·, neg_div', neg_neg]⟩))⟩)
  )
  convert this.neg using 1
  · ext; rw [neg_div', neg_neg]
  · simp only [lim, Subadditive.lim, Real.sInf_def, neg_neg, nhds_eq_nhds_iff,
      ← Set.image_neg_eq_neg, Set.image_image, neg_div', neg_neg]

end Superadditive


namespace Subadditive

variable {u : ℕ → ℝ} (h : Subadditive u)

include h in
theorem to_Superadditive : Superadditive (-u ·) :=
  (by dsimp; linarith [h · ·])

end Subadditive
