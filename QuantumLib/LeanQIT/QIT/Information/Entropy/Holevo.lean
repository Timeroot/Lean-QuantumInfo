/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Classical.Ensemble
public import QIT.Information.Entropy.Entropy

/-!
# Holevo information

The Holevo information chi(E) of an ensemble and the dimension bound
chi <= log2(dim B).

[Wilde2011Qst, qit-notes.tex:19441-19448].
-/

@[expose] public section

namespace QIT

universe u v w

noncomputable section

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [Fintype a] [DecidableEq a]

namespace Ensemble

/-- The Holevo information chi(E) of an ensemble. -/
def holevoInformation (E : Ensemble ι a) : ℝ :=
  State.vonNeumann E.averageState
    - ∑ i, (E.probs i).toReal * State.vonNeumann (E.states i)

/-- The Holevo information is the entropy of the average state minus the
average entropy. -/
theorem holevoInformation_def (E : Ensemble ι a) :
    E.holevoInformation =
      State.vonNeumann E.averageState
        - ∑ i, (E.probs i).toReal * State.vonNeumann (E.states i) := by
  rfl

/-- Relabeling the finite classical index leaves Holevo information unchanged. -/
@[simp]
theorem relabelIndex_holevoInformation {κ : Type w} [Fintype κ]
    (E : Ensemble ι a) (e : κ ≃ ι) :
    (E.relabelIndex e).holevoInformation = E.holevoInformation := by
  rw [holevoInformation_def, holevoInformation_def, relabelIndex_averageState]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- Nonnegativity of Holevo information is equivalent to the entropy-concavity
inequality for a finite ensemble. -/
theorem holevoInformation_nonneg_iff_vonNeumann_average_ge_sum (E : Ensemble ι a) :
    0 ≤ E.holevoInformation ↔
      (∑ i, (E.probs i).toReal * State.vonNeumann (E.states i))
        ≤ State.vonNeumann E.averageState := by
  rw [holevoInformation_def]
  exact sub_nonneg

/-- The Holevo information is bounded by log2(dim B). -/
theorem holevo_le_log_card (E : Ensemble ι a) :
    E.holevoInformation ≤ log2 (Fintype.card a) := by
  have hnonneg_sum : 0
      ≤ ∑ i, (E.probs i).toReal * State.vonNeumann (E.states i) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (NNReal.coe_nonneg _) (State.vonNeumann_nonneg _)
  calc E.holevoInformation
      = State.vonNeumann E.averageState
          - ∑ i, (E.probs i).toReal * State.vonNeumann (E.states i) := rfl
    _ ≤ State.vonNeumann E.averageState := sub_le_self _ hnonneg_sum
    _ ≤ log2 (Fintype.card a) := State.vonNeumann_le_log_card E.averageState

end Ensemble

end

end QIT
