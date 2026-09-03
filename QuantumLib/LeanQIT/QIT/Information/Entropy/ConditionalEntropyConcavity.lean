/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy.Holevo
public import QIT.Information.Entropy.StrongSubadditivity

/-!
# Concavity of conditional entropy

This module proves the conditional-entropy concavity corollary from
KhatriWilde2024Principles, `Chapters/entropies.tex`, Corollary*
`cor-QEI:cond-entr-concave`, Eq. `eq:QEI:concavity-cond-ent`, lines 733-742.
The proof follows the source route: build the classical-quantum state
`ρ_XAB = Σ_x p_x |x⟩⟨x| ⊗ ρ^x_AB`, reindex it as an `A-X-B` tripartite state,
apply strong subadditivity as `I(A;X|B) ≥ 0`, and expand the two cq entropies.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v w

noncomputable section

namespace Ensemble

variable {ι : Type u} {a : Type v} {b : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

/-- The ensemble obtained by taking the `B` marginal of every bipartite member. -/
def marginalBipartiteB (E : Ensemble ι (Prod a b)) : Ensemble ι b where
  probs := E.probs
  weights_sum := E.weights_sum
  states := fun x => (E.states x).marginalB

omit [DecidableEq ι] in
@[simp]
theorem marginalBipartiteB_probs (E : Ensemble ι (Prod a b)) :
    E.marginalBipartiteB.probs = E.probs := rfl

omit [DecidableEq ι] in
@[simp]
theorem marginalBipartiteB_states (E : Ensemble ι (Prod a b)) (x : ι) :
    E.marginalBipartiteB.states x = (E.states x).marginalB := rfl

omit [DecidableEq ι] in
/-- Taking the `B` marginal commutes with forming the ensemble average. -/
theorem marginalBipartiteB_averageState (E : Ensemble ι (Prod a b)) :
    E.marginalBipartiteB.averageState = E.averageState.marginalB := by
  apply State.ext
  ext b₁ b₂
  simp [marginalBipartiteB, Ensemble.averageState_matrix, State.marginalB,
    QIT.partialTraceA, Matrix.sum_apply, Finset.smul_sum]
  rw [Finset.sum_comm]

end Ensemble

namespace State

variable {ι : Type u} {a : Type v} {b : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

private theorem mutualInformation_nonneg_forEntropyConcavity (ρ : State (Prod a b)) :
    0 ≤ QIT.mutualInformation ρ := by
  have hDPI :=
    QIT.mutualInformation_dataProcessing_local_channels_ge ρ
      (terminalMeasureChannel a) (terminalMeasureChannel b)
  have hzero :
      QIT.mutualInformation
          (((terminalMeasureChannel a).prod (terminalMeasureChannel b)).applyState ρ) = 0 :=
    mutualInformation_punit_punit_eq_zero _
  linarith

/-- Reassociate a source cq state `X × (A × B)` as the tripartite state
`(A × X) × B` used by `I(A;X|B)`. -/
private def cqXABToAXBEquiv (ι : Type u) (a : Type v) (b : Type w) :
    Prod ι (Prod a b) ≃ Prod (Prod a ι) b where
  toFun x := ((x.2.1, x.1), x.2.2)
  invFun x := (x.1.2, (x.1.1, x.2))
  left_inv := by
    rintro ⟨x, a, b⟩
    rfl
  right_inv := by
    rintro ⟨⟨a, x⟩, b⟩
    rfl

/-- The source cq extension, re-associated as an `A-X-B` tripartite state. -/
private def cqAXBState (E : Ensemble ι (Prod a b)) :
    State (Prod (Prod a ι) b) :=
  E.cqState.reindex (cqXABToAXBEquiv ι a b)

private theorem cqAXBState_marginalAC (E : Ensemble ι (Prod a b)) :
    (cqAXBState E).marginalAC = E.averageState := by
  apply State.ext
  ext ab ab'
  simp [cqAXBState, cqXABToAXBEquiv, State.marginalAC, State.reindex,
    Ensemble.cqState_matrix, Ensemble.averageState_matrix, Matrix.sum_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.single_apply]

private theorem cqAXBState_marginalB (E : Ensemble ι (Prod a b)) :
    (cqAXBState E).marginalB = E.averageState.marginalB := by
  apply State.ext
  ext b₁ b₂
  simp [cqAXBState, cqXABToAXBEquiv, State.marginalB, State.reindex,
    Ensemble.cqState_matrix, Ensemble.averageState_matrix, Matrix.sum_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.single_apply,
    QIT.partialTraceA, Fintype.sum_prod_type]

private theorem cqAXBState_marginalBC_reindex (E : Ensemble ι (Prod a b)) :
    (cqAXBState E).marginalBC =
      E.marginalBipartiteB.cqState := by
  apply State.ext
  ext bx bx'
  rcases bx with ⟨x, b₁⟩
  rcases bx' with ⟨x', b₂⟩
  simp [cqAXBState, cqXABToAXBEquiv, State.marginalBC, State.reindex,
    Ensemble.cqState_matrix, Ensemble.marginalBipartiteB, State.marginalB,
    Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.single_apply, QIT.partialTraceA]
  by_cases h : x = x'
  · subst h
    simp [Finset.smul_sum]
  · have hzero : ∀ y : ι, ¬(y = x ∧ y = x') := by
      intro y hy
      exact h (hy.1.symm.trans hy.2)
    simp [hzero]

private theorem cqAXBState_vonNeumann (E : Ensemble ι (Prod a b)) :
    (cqAXBState E).vonNeumann = E.cqState.vonNeumann := by
  exact State.vonNeumann_reindex E.cqState (cqXABToAXBEquiv ι a b)

/-- Conditional von Neumann entropy is concave on finite ensembles of
bipartite states.  This is the `H(A|B)` half of KhatriWilde2024Principles,
`Chapters/entropies.tex`, Corollary* `cor-QEI:cond-entr-concave`,
Eq. `eq:QEI:concavity-cond-ent`, lines 733-742. -/
theorem conditionalEntropy_concave (E : Ensemble ι (Prod a b)) :
    (E.averageState).conditionalEntropy ≥
      ∑ x, (E.probs x : ℝ) * (E.states x).conditionalEntropy := by
  let ρAXB : State (Prod (Prod a ι) b) := cqAXBState E
  have hssa := State.condMutualInfoABGivenC_nonneg (ρ := ρAXB)
  have hAC : ρAXB.marginalAC = E.averageState := by
    simpa [ρAXB] using cqAXBState_marginalAC (E := E)
  have hB : ρAXB.marginalB = E.averageState.marginalB := by
    simpa [ρAXB] using cqAXBState_marginalB (E := E)
  have hBC : ρAXB.marginalBC =
      E.marginalBipartiteB.cqState := by
    simpa [ρAXB] using cqAXBState_marginalBC_reindex (E := E)
  have hwhole : ρAXB.vonNeumann = E.cqState.vonNeumann := by
    simpa [ρAXB] using cqAXBState_vonNeumann (E := E)
  rw [State.condMutualInfoABGivenC_eq, hAC, hB, hBC, hwhole] at hssa
  rw [State.conditionalEntropy_eq]
  have hmain :
      0 ≤ E.averageState.vonNeumann -
          E.averageState.marginalB.vonNeumann -
          ∑ x, (E.probs x : ℝ) *
            ((E.states x).vonNeumann - (E.states x).marginalB.vonNeumann) := by
    rw [cqState_vonNeumann E.marginalBipartiteB, cqState_vonNeumann E] at hssa
    simp [Ensemble.marginalBipartiteB] at hssa
    simp [mul_sub, Finset.sum_sub_distrib]
    ring_nf at hssa ⊢
    linarith
  have hsum :
      (∑ x, (E.probs x : ℝ) * (E.states x).conditionalEntropy) =
        ∑ x, (E.probs x : ℝ) *
          ((E.states x).vonNeumann - (E.states x).marginalB.vonNeumann) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [State.conditionalEntropy_eq]
  linarith

end State

namespace Ensemble

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype a] [DecidableEq a]

/-- The classical point mass `|x⟩⟨x|` as a density state. -/
private def classicalBasisState (x : ι) : State ι where
  matrix := Matrix.single x x (1 : ℂ)
  pos := posSemidef_single x
  trace_eq_one := by
    rw [trace_single_one, if_pos rfl]

/-- The ensemble of product states `|x⟩⟨x| ⊗ ρ_x` whose average is `E.cqState`. -/
private def cqProductEnsemble (E : Ensemble ι a) : Ensemble ι (Prod ι a) where
  probs := E.probs
  weights_sum := E.weights_sum
  states := fun x => (classicalBasisState x).prod (E.states x)

private theorem cqProductEnsemble_averageState (E : Ensemble ι a) :
    (cqProductEnsemble E).averageState = E.cqState := by
  apply State.ext
  ext xi xj
  rcases xi with ⟨x, i⟩
  rcases xj with ⟨y, j⟩
  simp [cqProductEnsemble, classicalBasisState, Ensemble.averageState_matrix,
    Ensemble.cqState_matrix, State.prod, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.sum_apply]

private theorem cqProductEnsemble_state_conditionalEntropy_nonneg
    (E : Ensemble ι a) (x : ι) :
    0 ≤ ((classicalBasisState x).prod (E.states x)).conditionalEntropy := by
  have hmarg :
      ((classicalBasisState x).prod (E.states x)).marginalB = E.states x := by
    apply State.ext
    exact State.partialTraceA_prod (classicalBasisState x) (E.states x)
  rw [State.conditionalEntropy_eq, hmarg, State.vonNeumann_prod]
  have hclassical : 0 ≤ (classicalBasisState x).vonNeumann :=
    State.vonNeumann_nonneg (classicalBasisState x)
  linarith

/-- Von Neumann entropy is concave on finite ensembles of states. -/
theorem vonNeumann_average_ge_sum (E : Ensemble ι a) :
    (∑ x, (E.probs x : ℝ) * (E.states x).vonNeumann) ≤
      E.averageState.vonNeumann := by
  have hI : 0 ≤ QIT.mutualInformation E.cqState :=
    State.mutualInformation_nonneg_forEntropyConcavity (ρ := E.cqState)
  rw [QIT.mutualInformation] at hI
  rw [cqState_marginalA_vonNeumann E] at hI
  rw [Ensemble.cqState_marginalB_eq_averageState E] at hI
  rw [cqState_vonNeumann E] at hI
  linarith

/-- Von Neumann entropy is bounded above by the Shannon entropy of the ensemble
weights plus the average member entropy. -/
theorem vonNeumann_average_le_shannon_add_sum (E : Ensemble ι a) :
    E.averageState.vonNeumann ≤
      -(∑ x, xlog2 ((E.probs x : ℝ))) +
        ∑ x, (E.probs x : ℝ) * (E.states x).vonNeumann := by
  let F : Ensemble ι (Prod ι a) := cqProductEnsemble E
  have hconc := State.conditionalEntropy_concave (E := F)
  have hsum_nonneg :
      0 ≤ ∑ x, (F.probs x : ℝ) * (F.states x).conditionalEntropy := by
    refine Finset.sum_nonneg ?_
    intro x _
    exact mul_nonneg (NNReal.coe_nonneg _) (by
      simpa [F, cqProductEnsemble] using
        cqProductEnsemble_state_conditionalEntropy_nonneg (E := E) x)
  have hcond_nonneg : 0 ≤ F.averageState.conditionalEntropy :=
    le_trans hsum_nonneg hconc
  have havg : F.averageState = E.cqState := by
    simpa [F] using cqProductEnsemble_averageState (E := E)
  have hcond :
      F.averageState.conditionalEntropy =
        E.cqState.vonNeumann - E.averageState.vonNeumann := by
    rw [State.conditionalEntropy_eq, havg, Ensemble.cqState_marginalB_eq_averageState]
  rw [hcond, cqState_vonNeumann E] at hcond_nonneg
  linarith

/-- Holevo information is bounded by the input alphabet size: χ(E)=I(X;B) ≤ H(X) ≤ log2|ι|. -/
theorem holevo_le_log_card_input (E : Ensemble ι a) :
    E.holevoInformation ≤ log2 (Fintype.card ι) := by
  calc E.holevoInformation
      = State.vonNeumann E.averageState
          - ∑ i, (E.probs i).toReal * State.vonNeumann (E.states i) := rfl
    _ ≤ -(∑ x, xlog2 ((E.probs x : ℝ))) := by
        linarith [vonNeumann_average_le_shannon_add_sum E]
    _ = State.vonNeumann E.cqState.marginalA := (cqState_marginalA_vonNeumann E).symm
    _ ≤ log2 (Fintype.card ι) := State.vonNeumann_le_log_card E.cqState.marginalA

/-- Full dimension bound: χ(E) ≤ log2(min{|ι|, |a|}) (Wilde, qit-notes.tex exercise ~19482). -/
theorem holevo_le_log_min_card (E : Ensemble ι a) :
    E.holevoInformation ≤ log2 (min (Fintype.card ι) (Fintype.card a)) := by
  have h1 := holevo_le_log_card_input E
  have h2 := holevo_le_log_card E
  rcases le_total (Fintype.card ι) (Fintype.card a) with hca | hca
  · rw [min_eq_left (by exact_mod_cast hca)]; exact h1
  · rw [min_eq_right (by exact_mod_cast hca)]; exact h2

end Ensemble

end

end QIT
