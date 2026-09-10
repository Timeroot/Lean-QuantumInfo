/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Entropy.EntropyTensorPower
public import QuantumLib.QIT.States.MaximallyMixed

/-!
# Entropy of the maximally mixed state

The uniform state on a finite register has von Neumann entropy `log₂ d`, the largest value any
state on that register can take.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
open Matrix

noncomputable section
universe u

open QIT

namespace MState

variable {a : Type u} [Fintype a] [DecidableEq a]

theorem vonNeumann_uniform [Nonempty a] :
    (MState.uniform : MState a).vonNeumann = log2 (Fintype.card a : ℝ) := by
  have hdiag :
      (MState.uniform : MState a).m =
        Matrix.diagonal (fun _ : a => (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [MState.vonNeumann_eq_neg_sum_xlog2_of_diagonal _ _ hdiag]
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hcard_ne : (Fintype.card a : ℝ) ≠ 0 := ne_of_gt hcard_pos
  rw [Finset.sum_const, nsmul_eq_mul]
  simp only [xlog2, if_neg (inv_ne_zero hcard_ne), Finset.card_univ]
  unfold log2
  rw [Real.log_inv]
  field_simp [hcard_ne]

end MState
