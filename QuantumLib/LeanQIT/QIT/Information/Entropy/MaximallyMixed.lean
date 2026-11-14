/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy.EntropyTensorPower
public import QIT.States.MaximallyMixed

/-!
# Entropy of the maximally mixed state
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
open Matrix

namespace QIT

universe u

noncomputable section

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]

theorem vonNeumann_maximallyMixed [Nonempty a] :
    (maximallyMixed a).vonNeumann = log2 (Fintype.card a : ℝ) := by
  have hdiag :
      (maximallyMixed a).matrix =
        Matrix.diagonal (fun _ : a => (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [maximallyMixed]
    · simp [maximallyMixed, hij]
  rw [State.vonNeumann_eq_neg_sum_xlog2_of_diagonal _ _ hdiag]
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hcard_ne : (Fintype.card a : ℝ) ≠ 0 := ne_of_gt hcard_pos
  rw [Finset.sum_const, nsmul_eq_mul]
  simp only [xlog2, if_neg (inv_ne_zero hcard_ne), Finset.card_univ]
  unfold log2
  rw [Real.log_inv]
  field_simp [hcard_ne]

end State

end
end QIT
