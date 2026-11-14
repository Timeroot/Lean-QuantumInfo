/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.Renyi
public import QIT.Information.Renyi.FrankLieb.DPI
public import QIT.Core.State
public import QIT.Classical.Bridge

/-! # State-level sandwiched-Renyi mutual information

This module provides the bipartite-state definitions and elementary order facts
for the sandwiched-Renyi mutual information used in the entanglement-assisted
classical communication strong-converse route.

Source alignment:
* [KhatriWilde2024Principles, Chapters/entropies.tex:8065-8074] defines the
  sandwiched-Renyi state and channel mutual information objectives.

The candidate, value set, and optimized-state API previously lived in
`QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Basic` and has been relocated
here so that the information layer can reason about these state-level
quantities without importing coding modules.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace State

/-- Candidate sandwiched-Renyi mutual information value for a fixed side
information state `sigmaB`:
`D~_alpha(rho_AB || rho_A tensor sigma_B)`.

This is the state-level candidate appearing before the `inf_sigmaB` in
Khatri--Wilde, `Chapters/entropies.tex:8069-8074`.  It uses the PSD-reference
extended-real divergence from `FrankLieb.lean`, so singular references follow
the source support convention instead of needing artificial full-rank
hypotheses. -/
def sandwichedRenyiMutualInformationCandidateE
    (rhoAB : State (Prod a b)) (sigmaB : State b) (alpha : ℝ) : EReal :=
  rhoAB.sandwichedRenyiPSDReferenceE
    (rhoAB.marginalA.prod sigmaB).matrix
    (rhoAB.marginalA.prod sigmaB).pos
    alpha

/-- Value set for the state sandwiched-Renyi mutual information
`I~_alpha(A;B)_rho`, before taking the infimum over side-information states. -/
def sandwichedRenyiMutualInformationEValueSet
    (rhoAB : State (Prod a b)) (alpha : ℝ) : Set EReal :=
  Set.range fun sigmaB : State b =>
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha

/-- Extended-real sandwiched-Renyi mutual information of a bipartite state:
`I~_alpha(A;B)_rho = inf_sigmaB D~_alpha(rho_AB || rho_A tensor sigma_B)`. -/
def sandwichedRenyiMutualInformationE
    (rhoAB : State (Prod a b)) (alpha : ℝ) : EReal :=
  sInf (rhoAB.sandwichedRenyiMutualInformationEValueSet alpha)

theorem sandwichedRenyiMutualInformationCandidateE_eq
    (rhoAB : State (Prod a b)) (sigmaB : State b) (alpha : ℝ) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
      rhoAB.sandwichedRenyiPSDReferenceE
        (rhoAB.marginalA.prod sigmaB).matrix
        (rhoAB.marginalA.prod sigmaB).pos
        alpha := by
  rfl

/-- On the full-rank high-`alpha` branch, the source-facing extended-real
candidate agrees with the repository's real-valued matrix-reference
sandwiched-Renyi divergence. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_reference_posDef
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    (hrho : rhoAB.matrix.PosDef) (hA : rhoAB.marginalA.matrix.PosDef)
    (hsigma : sigmaB.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
      (sandwichedRenyiReference rhoAB
        (rhoAB.marginalA.prod sigmaB).matrix
        hrho (State.prod_posDef hA hsigma)
        alpha (lt_trans zero_lt_one halpha) (ne_of_gt halpha) : EReal) := by
  rw [sandwichedRenyiMutualInformationCandidateE_eq]
  rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha]
  exact sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_reference_posDef
    rhoAB hrho (State.prod_posDef hA hsigma)
    alpha (lt_trans zero_lt_one halpha) (ne_of_gt halpha)

theorem sandwichedRenyiMutualInformationE_eq_sInf
    (rhoAB : State (Prod a b)) (alpha : ℝ) :
    rhoAB.sandwichedRenyiMutualInformationE alpha =
      sInf (rhoAB.sandwichedRenyiMutualInformationEValueSet alpha) := by
  rfl

theorem sandwichedRenyiMutualInformationCandidateE_mem_valueSet
    (rhoAB : State (Prod a b)) (sigmaB : State b) (alpha : ℝ) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha ∈
      rhoAB.sandwichedRenyiMutualInformationEValueSet alpha := by
  exact ⟨sigmaB, rfl⟩

theorem sandwichedRenyiMutualInformationE_le_candidate
    (rhoAB : State (Prod a b)) (sigmaB : State b) (alpha : ℝ) :
    rhoAB.sandwichedRenyiMutualInformationE alpha ≤
      rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha := by
  rw [sandwichedRenyiMutualInformationE_eq_sInf]
  exact sInf_le
    (rhoAB.sandwichedRenyiMutualInformationCandidateE_mem_valueSet sigmaB alpha)

/-- The side-information candidate set is nonempty whenever the side system is
inhabited.  This is the order-theoretic precondition for later `sInf` reasoning. -/
theorem sandwichedRenyiMutualInformationEValueSet_nonempty [Nonempty b]
    (rhoAB : State (Prod a b)) (alpha : ℝ) :
    (rhoAB.sandwichedRenyiMutualInformationEValueSet alpha).Nonempty := by
  classical
  let u : b → ℝ≥0 := fun _ => (Fintype.card b : ℝ≥0)⁻¹
  have husum : ∑ i, u i = 1 := by
    simp [u, Finset.sum_const, Fintype.card_ne_zero]
  let sigmaB : State b := Classical.diagonalState u husum
  exact ⟨rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha, ⟨sigmaB, rfl⟩⟩

end State

end

end QIT
