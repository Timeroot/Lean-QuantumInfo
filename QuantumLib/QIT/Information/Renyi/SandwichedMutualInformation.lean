/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Renyi.Renyi
public import QuantumLib.QIT.Information.Renyi.FrankLieb.DPI
public import QuantumLib.QIT.Core.State
public import QuantumLib.QIT.Classical.Bridge

/-! # MState-level sandwiched-Renyi mutual information

This module provides the bipartite-state definitions and elementary order facts
for the sandwiched-Renyi mutual information used in the entanglement-assisted
classical communication strong-converse route.

Source alignment:
* [KhatriWilde2024Principles, Chapters/entropies.tex:8065-8074] defines the
  sandwiched-Renyi state and channel mutual information objectives.

The candidate, value set, and optimized-state API lives here rather than with
the strong-converse route in `QIT.Coding.EntanglementAssisted.Renyi.Sandwiched`,
so that the information layer can reason about these state-level quantities
without importing coding modules.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

noncomputable section
universe u v
variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

open QIT

namespace MState

/-- Candidate sandwiched-Renyi mutual information value for a fixed side
information state `sigmaB`:
`D~_alpha(rho_AB || rho_A tensor sigma_B)`.

This is the state-level candidate appearing before the `inf_sigmaB` in
Khatri--Wilde, `Chapters/entropies.tex:8069-8074`.  It uses the PSD-reference
extended-real divergence from `FrankLieb.lean`, so singular references follow
the source support convention instead of needing artificial full-rank
hypotheses. -/
def sandwichedRenyiMutualInformationCandidateE
    (rhoAB : MState (a × b)) (sigmaB : MState b) (alpha : ℝ) : EReal :=
  rhoAB.sandwichedRenyiPSDReferenceE
    (rhoAB.traceRight.prod sigmaB).m
    (rhoAB.traceRight.prod sigmaB).psd
    alpha

/-- Value set for the state sandwiched-Renyi mutual information
`I~_alpha(A;B)_rho`, before taking the infimum over side-information states. -/
def sandwichedRenyiMutualInformationEValueSet
    (rhoAB : MState (a × b)) (alpha : ℝ) : Set EReal :=
  Set.range fun sigmaB : MState b =>
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha

/-- Extended-real sandwiched-Renyi mutual information of a bipartite state:
`I~_alpha(A;B)_rho = inf_sigmaB D~_alpha(rho_AB || rho_A tensor sigma_B)`. -/
def sandwichedRenyiMutualInformationE
    (rhoAB : MState (a × b)) (alpha : ℝ) : EReal :=
  sInf (rhoAB.sandwichedRenyiMutualInformationEValueSet alpha)

theorem sandwichedRenyiMutualInformationCandidateE_eq
    (rhoAB : MState (a × b)) (sigmaB : MState b) (alpha : ℝ) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
      rhoAB.sandwichedRenyiPSDReferenceE
        (rhoAB.traceRight.prod sigmaB).m
        (rhoAB.traceRight.prod sigmaB).psd
        alpha := by
  rfl

/-- On the full-rank high-`alpha` branch, the source-facing extended-real
candidate agrees with the repository's real-valued matrix-reference
sandwiched-Renyi divergence. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_coe_reference_posDef
    (rhoAB : MState (a × b)) (sigmaB : MState b)
    (hrho : rhoAB.m.PosDef) (hA : rhoAB.traceRight.m.PosDef)
    (hsigma : sigmaB.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
      (sandwichedRenyiReference rhoAB
        (rhoAB.traceRight.prod sigmaB).m
        hrho (MState.PosDef.kron hA hsigma)
        alpha (lt_trans zero_lt_one halpha) (ne_of_gt halpha) : EReal) := by
  rw [sandwichedRenyiMutualInformationCandidateE_eq]
  rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha]
  exact sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_reference_posDef
    rhoAB hrho (MState.PosDef.kron hA hsigma)
    alpha (lt_trans zero_lt_one halpha) (ne_of_gt halpha)

theorem sandwichedRenyiMutualInformationE_eq_sInf
    (rhoAB : MState (a × b)) (alpha : ℝ) :
    rhoAB.sandwichedRenyiMutualInformationE alpha =
      sInf (rhoAB.sandwichedRenyiMutualInformationEValueSet alpha) := by
  rfl

theorem sandwichedRenyiMutualInformationCandidateE_mem_valueSet
    (rhoAB : MState (a × b)) (sigmaB : MState b) (alpha : ℝ) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha ∈
      rhoAB.sandwichedRenyiMutualInformationEValueSet alpha := by
  exact ⟨sigmaB, rfl⟩

theorem sandwichedRenyiMutualInformationE_le_candidate
    (rhoAB : MState (a × b)) (sigmaB : MState b) (alpha : ℝ) :
    rhoAB.sandwichedRenyiMutualInformationE alpha ≤
      rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha := by
  rw [sandwichedRenyiMutualInformationE_eq_sInf]
  exact sInf_le
    (rhoAB.sandwichedRenyiMutualInformationCandidateE_mem_valueSet sigmaB alpha)

/-- The side-information candidate set is nonempty whenever the side system is
inhabited.  This is the order-theoretic precondition for later `sInf` reasoning. -/
theorem sandwichedRenyiMutualInformationEValueSet_nonempty [Nonempty b]
    (rhoAB : MState (a × b)) (alpha : ℝ) :
    (rhoAB.sandwichedRenyiMutualInformationEValueSet alpha).Nonempty := by
  classical
  let u : b → ℝ≥0 := fun _ => (Fintype.card b : ℝ≥0)⁻¹
  have husum : ∑ i, u i = 1 := by
    simp [u, Finset.sum_const, Fintype.card_ne_zero]
  let sigmaB : MState b := Classical.diagonalState u husum
  exact ⟨rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha, ⟨sigmaB, rfl⟩⟩

end MState
