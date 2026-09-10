/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Entropy.Holevo
public import QuantumLib.QIT.Information.Entropy.StrongSubadditivity

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

noncomputable section
universe u v w

open QIT

namespace MEnsemble

variable {ι : Type u} {a : Type v} {b : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

/-- The ensemble obtained by taking the `B` marginal of every bipartite member. -/
def marginalBipartiteB (E : MEnsemble (a × b) ι) : MEnsemble b ι :=
  .ofProbs E.probs E.weights_sum (fun x => (E.states x).traceLeft)

omit [DecidableEq ι] in
@[simp]
theorem marginalBipartiteB_probs (E : MEnsemble (a × b) ι) :
    E.marginalBipartiteB.probs = E.probs := rfl

omit [DecidableEq ι] in
@[simp]
theorem marginalBipartiteB_states (E : MEnsemble (a × b) ι) (x : ι) :
    E.marginalBipartiteB.states x = (E.states x).traceLeft := rfl

omit [DecidableEq ι] in
/-- Taking the `B` marginal commutes with forming the ensemble average. -/
theorem marginalBipartiteB_averageState (E : MEnsemble (a × b) ι) :
    E.marginalBipartiteB.averageState = E.averageState.traceLeft := by
  apply MState.ext
  ext b₁ b₂
  simp [marginalBipartiteB, MEnsemble.averageState_matrix,
    Matrix.traceLeft, Matrix.sum_apply, Finset.smul_sum]
  rw [Finset.sum_comm]

end MEnsemble

namespace MState

variable {ι : Type u} {a : Type v} {b : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

/-- The source cq extension, re-associated as an `A-X-B` tripartite state. -/
private def cqAXBState (E : MEnsemble (a × b) ι) :
    MState ((a × ι) × b) :=
  E.cqState.reindex (prodABCToBACEquiv ι a b)

private theorem cqAXBState_marginalAC (E : MEnsemble (a × b) ι) :
    (cqAXBState E).marginalAC = E.averageState := by
  apply MState.ext
  ext ab ab'
  simp [cqAXBState, prodABCToBACEquiv, MState.marginalAC,
    MEnsemble.cqState_matrix, MEnsemble.averageState_matrix, Matrix.sum_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.single_apply]

private theorem cqAXBState_traceLeft (E : MEnsemble (a × b) ι) :
    (cqAXBState E).traceLeft = E.averageState.traceLeft := by
  apply MState.ext
  ext b₁ b₂
  simp [cqAXBState, prodABCToBACEquiv,
    MEnsemble.cqState_matrix, MEnsemble.averageState_matrix, Matrix.sum_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.single_apply,
    Matrix.traceLeft, Fintype.sum_prod_type]

private theorem cqAXBState_marginalBC_reindex (E : MEnsemble (a × b) ι) :
    (cqAXBState E).marginalBC =
      E.marginalBipartiteB.cqState := by
  apply MState.ext
  ext bx bx'
  rcases bx with ⟨x, b₁⟩
  rcases bx' with ⟨x', b₂⟩
  simp [cqAXBState, prodABCToBACEquiv, MState.marginalBC_matrix, MState.reindex_matrix,
    MEnsemble.cqState_matrix, MEnsemble.marginalBipartiteB,
    Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.single_apply, Matrix.traceLeft]
  by_cases h : x = x'
  · subst h
    simp [Finset.smul_sum]
  · have hzero : ∀ y : ι, ¬(y = x ∧ y = x') := by
      intro y hy
      exact h (hy.1.symm.trans hy.2)
    simp [hzero]

private theorem cqAXBState_vonNeumann (E : MEnsemble (a × b) ι) :
    (cqAXBState E).vonNeumann = E.cqState.vonNeumann := by
  exact MState.vonNeumann_reindex E.cqState (prodABCToBACEquiv ι a b)

/-- Conditional von Neumann entropy is concave on finite ensembles of
bipartite states.  This is the `H(A|B)` half of KhatriWilde2024Principles,
`Chapters/entropies.tex`, Corollary* `cor-QEI:cond-entr-concave`,
Eq. `eq:QEI:concavity-cond-ent`, lines 733-742. -/
theorem conditionalEntropy_concave (E : MEnsemble (a × b) ι) :
    (E.averageState).conditionalEntropy ≥
      ∑ x, (E.probs x : ℝ) * (E.states x).conditionalEntropy := by
  let ρAXB : MState ((a × ι) × b) := cqAXBState E
  have hssa := MState.condMutualInfoABGivenC_nonneg (ρ := ρAXB)
  have hAC : ρAXB.marginalAC = E.averageState := by
    simpa [ρAXB] using cqAXBState_marginalAC (E := E)
  have hB : ρAXB.traceLeft = E.averageState.traceLeft := by
    simpa [ρAXB] using cqAXBState_traceLeft (E := E)
  have hBC : ρAXB.marginalBC =
      E.marginalBipartiteB.cqState := by
    simpa [ρAXB] using cqAXBState_marginalBC_reindex (E := E)
  have hwhole : ρAXB.vonNeumann = E.cqState.vonNeumann := by
    simpa [ρAXB] using cqAXBState_vonNeumann (E := E)
  rw [MState.condMutualInfoABGivenC_eq, hAC, hB, hBC, hwhole] at hssa
  rw [MState.conditionalEntropy_eq]
  have hmain :
      0 ≤ E.averageState.vonNeumann -
          E.averageState.traceLeft.vonNeumann -
          ∑ x, (E.probs x : ℝ) *
            ((E.states x).vonNeumann - (E.states x).traceLeft.vonNeumann) := by
    rw [MState.cqState_vonNeumann E.marginalBipartiteB, MState.cqState_vonNeumann E] at hssa
    simp [MEnsemble.marginalBipartiteB] at hssa
    simp [mul_sub, Finset.sum_sub_distrib]
    ring_nf at hssa ⊢
    linarith
  have hsum :
      (∑ x, (E.probs x : ℝ) * (E.states x).conditionalEntropy) =
        ∑ x, (E.probs x : ℝ) *
          ((E.states x).vonNeumann - (E.states x).traceLeft.vonNeumann) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MState.conditionalEntropy_eq]
  linarith

end MState

namespace MEnsemble

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype a] [DecidableEq a]

/-- The classical point mass `|x⟩⟨x|` as a density state. -/
private def classicalBasisState (x : ι) : MState ι := .ofMatrix
  (matrix := Matrix.single x x (1 : ℂ))
  (pos := posSemidef_single x)
  (trace_eq_one := by
    rw [trace_single_one, if_pos rfl])

/-- The ensemble of product states `|x⟩⟨x| ⊗ ρ_x` whose average is `E.cqState`. -/
private def cqProductEnsemble (E : MEnsemble a ι) : MEnsemble (ι × a) ι :=
  .ofProbs E.probs E.weights_sum (fun x => (classicalBasisState x).prod (E.states x))

private theorem cqProductEnsemble_averageState (E : MEnsemble a ι) :
    (cqProductEnsemble E).averageState = E.cqState := by
  apply MState.ext
  ext xi xj
  rcases xi with ⟨x, i⟩
  rcases xj with ⟨y, j⟩
  simp [cqProductEnsemble, classicalBasisState, MEnsemble.averageState_matrix,
    MEnsemble.cqState_matrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.sum_apply]

private theorem cqProductEnsemble_state_conditionalEntropy_nonneg
    (E : MEnsemble a ι) (x : ι) :
    0 ≤ ((classicalBasisState x).prod (E.states x)).conditionalEntropy := by
  have hmarg :
      ((classicalBasisState x).prod (E.states x)).traceLeft = E.states x := by
    apply MState.ext
    rw [MState.traceLeft_m]
    exact MState.traceLeft_prod (classicalBasisState x) (E.states x)
  rw [MState.conditionalEntropy_eq, hmarg, MState.vonNeumann_prod]
  have hclassical : 0 ≤ (classicalBasisState x).vonNeumann :=
    MState.vonNeumann_nonneg (classicalBasisState x)
  linarith

/-- Von Neumann entropy is concave on finite ensembles of states. -/
theorem vonNeumann_average_ge_sum (E : MEnsemble a ι) :
    (∑ x, (E.probs x : ℝ) * (E.states x).vonNeumann) ≤
      E.averageState.vonNeumann := by
  have hI : 0 ≤ QIT.mutualInformation E.cqState :=
    MState.mutualInformation_nonneg (ρ := E.cqState)
  rw [QIT.mutualInformation] at hI
  rw [MState.cqState_traceRight_vonNeumann E] at hI
  rw [MEnsemble.cqState_traceLeft_eq_averageState E] at hI
  rw [MState.cqState_vonNeumann E] at hI
  linarith

/-- Von Neumann entropy is bounded above by the Shannon entropy of the ensemble
weights plus the average member entropy. -/
theorem vonNeumann_average_le_shannon_add_sum (E : MEnsemble a ι) :
    E.averageState.vonNeumann ≤
      -(∑ x, xlog2 ((E.probs x : ℝ))) +
        ∑ x, (E.probs x : ℝ) * (E.states x).vonNeumann := by
  let F : MEnsemble (ι × a) ι := cqProductEnsemble E
  have hconc := MState.conditionalEntropy_concave (E := F)
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
    rw [MState.conditionalEntropy_eq, havg, MEnsemble.cqState_traceLeft_eq_averageState]
  rw [hcond, MState.cqState_vonNeumann E] at hcond_nonneg
  linarith

/-- Holevo information is bounded by the input alphabet size: χ(E)=I(X;B) ≤ H(X) ≤ log2|ι|. -/
theorem holevo_le_log_card_input (E : MEnsemble a ι) :
    E.holevoInformation ≤ log2 (Fintype.card ι) := by
  calc E.holevoInformation
      = MState.vonNeumann E.averageState
          - ∑ i, (E.probs i).toReal * MState.vonNeumann (E.states i) := rfl
    _ ≤ -(∑ x, xlog2 ((E.probs x : ℝ))) := by
        linarith [vonNeumann_average_le_shannon_add_sum E]
    _ = MState.vonNeumann E.cqState.traceRight := (MState.cqState_traceRight_vonNeumann E).symm
    _ ≤ log2 (Fintype.card ι) := MState.vonNeumann_le_log_card E.cqState.traceRight

/-- Full dimension bound: χ(E) ≤ log2(min{|ι|, |a|}) (Wilde, qit-notes.tex exercise ~19482). -/
theorem holevo_le_log_min_card (E : MEnsemble a ι) :
    E.holevoInformation ≤ log2 (min (Fintype.card ι) (Fintype.card a)) := by
  have h1 := holevo_le_log_card_input E
  have h2 := holevo_le_log_card E
  rcases le_total (Fintype.card ι) (Fintype.card a) with hca | hca
  · rw [min_eq_left (by exact_mod_cast hca)]; exact h1
  · rw [min_eq_right (by exact_mod_cast hca)]; exact h2

end MEnsemble
