/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Classical.Ensemble
public import QuantumLib.QIT.Information.Entropy.Entropy

/-!
# Holevo information

The Holevo information chi(E) of an ensemble and the dimension bound
chi ≤ log2(dim B).

[Wilde2011Qst, qit-notes.tex:19441-19448].
-/

@[expose] public section

namespace MEnsemble

open QIT

universe u v w

noncomputable section

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [Fintype a] [DecidableEq a]

/-- The Holevo information chi(E) of an ensemble. -/
def holevoInformation (E : MEnsemble a ι) : ℝ :=
  MState.vonNeumann E.averageState
    - ∑ i, (E.probs i).toReal * MState.vonNeumann (E.states i)

/-- The Holevo information is the entropy of the average state minus the
average entropy. -/
theorem holevoInformation_def (E : MEnsemble a ι) :
    E.holevoInformation =
      MState.vonNeumann E.averageState
        - ∑ i, (E.probs i).toReal * MState.vonNeumann (E.states i) := by
  rfl

/-- Relabeling the finite classical index leaves Holevo information unchanged. -/
@[simp]
theorem relabelIndex_holevoInformation {κ : Type w} [Fintype κ]
    (E : MEnsemble a ι) (e : κ ≃ ι) :
    (E.relabelIndex e).holevoInformation = E.holevoInformation := by
  rw [holevoInformation_def, holevoInformation_def, relabelIndex_averageState]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- Nonnegativity of Holevo information is equivalent to the entropy-concavity
inequality for a finite ensemble. -/
theorem holevoInformation_nonneg_iff_vonNeumann_average_ge_sum (E : MEnsemble a ι) :
    0 ≤ E.holevoInformation ↔
      (∑ i, (E.probs i).toReal * MState.vonNeumann (E.states i))
        ≤ MState.vonNeumann E.averageState := by
  rw [holevoInformation_def]
  exact sub_nonneg

/-- The Holevo information is bounded by log2(dim B). -/
theorem holevo_le_log_card (E : MEnsemble a ι) :
    E.holevoInformation ≤ log2 (Fintype.card a) := by
  have hnonneg_sum : 0
      ≤ ∑ i, (E.probs i).toReal * MState.vonNeumann (E.states i) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (NNReal.coe_nonneg _) (MState.vonNeumann_nonneg _)
  calc E.holevoInformation
      = MState.vonNeumann E.averageState
          - ∑ i, (E.probs i).toReal * MState.vonNeumann (E.states i) := rfl
    _ ≤ MState.vonNeumann E.averageState := sub_le_self _ hnonneg_sum
    _ ≤ log2 (Fintype.card a) := MState.vonNeumann_le_log_card E.averageState

end

end MEnsemble
