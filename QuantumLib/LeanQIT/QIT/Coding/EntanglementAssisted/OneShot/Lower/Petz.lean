/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.PositionBasedCoding
public import QIT.Information.Renyi.Renyi

/-!
# Petz-Renyi one-shot lower-bound bridge

This module records the Petz--Renyi information surface used in the
Khatri--Wilde one-shot lower-bound theorem for entanglement-assisted classical
communication
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:679-721].

The source proof combines the hypothesis-testing one-shot lower bound with
the comparison

`D_H^epsilon(rho || sigma) >= D_alpha(rho || sigma)
  + alpha / (alpha - 1) * log2 (1 / epsilon)`

from
[KhatriWilde2024Principles, Chapters/entropies.tex:7037-7042].

This file does not pretend that comparison is already proved.  It provides the
barred Petz--Renyi channel quantity and proves the final algebraic
capacity-lower-bound bridge from the hypothesis-testing lower bound plus the
channel-level comparison hypothesis.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace State

/-- Non-optimized barred Petz--Renyi mutual information
`bar I_alpha(A;B)_rho = D_alpha(rho_AB || rho_A tensor rho_B)`.

The current `State.petzRenyi` kernel is a positive-definite API, so this
definition exposes the corresponding positivity witnesses explicitly. -/
def barPetzRenyiMutualInformation
    (rhoAB : State (Prod a b))
    (hρ : rhoAB.matrix.PosDef)
    (hA : rhoAB.marginalA.matrix.PosDef)
    (hB : rhoAB.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  rhoAB.petzRenyi (rhoAB.marginalA.prod rhoAB.marginalB)
    hρ (State.prod_posDef hA hB) α hα_pos hα_ne_one

theorem barPetzRenyiMutualInformation_eq
    (rhoAB : State (Prod a b))
    (hρ : rhoAB.matrix.PosDef)
    (hA : rhoAB.marginalA.matrix.PosDef)
    (hB : rhoAB.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    rhoAB.barPetzRenyiMutualInformation hρ hA hB α hα_pos hα_ne_one =
      rhoAB.petzRenyi (rhoAB.marginalA.prod rhoAB.marginalB)
        hρ (State.prod_posDef hA hB) α hα_pos hα_ne_one :=
  rfl

/-- PSD-domain barred Petz--Renyi mutual information
`bar I_alpha(A;B)_rho = D_alpha(rho_AB || rho_A tensor rho_B)` in the
`0 < alpha < 1` source branch.

Unlike the compatibility definition above, this one does not require positive
definiteness of `rho_AB` or its marginals. -/
def barPetzRenyiMutualInformationPSDFinite
    (rhoAB : State (Prod a b))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  rhoAB.petzRenyiPSDFinite (rhoAB.marginalA.prod rhoAB.marginalB)
    α hα_pos hα_ne_one

theorem barPetzRenyiMutualInformationPSDFinite_eq
    (rhoAB : State (Prod a b))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    rhoAB.barPetzRenyiMutualInformationPSDFinite α hα_pos hα_ne_one =
      rhoAB.petzRenyiPSDFinite (rhoAB.marginalA.prod rhoAB.marginalB)
        α hα_pos hα_ne_one :=
  rfl

/-- Canonical extended-real barred Petz--Renyi mutual information in the PSD
source range `0 < α < 1`. -/
noncomputable def barPetzRenyiMutualInformationPSD
    (rhoAB : State (Prod a b))
    (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1) : EReal :=
  rhoAB.petzRenyiPSD (rhoAB.marginalA.prod rhoAB.marginalB)
    α hα_pos hα_lt_one

theorem barPetzRenyiMutualInformationPSD_eq
    (rhoAB : State (Prod a b))
    (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    rhoAB.barPetzRenyiMutualInformationPSD α hα_pos hα_lt_one =
      rhoAB.petzRenyiPSD (rhoAB.marginalA.prod rhoAB.marginalB)
        α hα_pos hα_lt_one :=
  rfl

/-- The canonical barred PSD value is finite for a state paired with the
product of its marginals. -/
theorem barPetzRenyiMutualInformationPSD_eq_coe_finite
    (rhoAB : State (Prod a b))
    (alpha : ℝ) (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    rhoAB.barPetzRenyiMutualInformationPSD alpha halpha0 halpha1 =
      (rhoAB.barPetzRenyiMutualInformationPSDFinite
        alpha halpha0 (ne_of_lt halpha1) : EReal) := by
  unfold barPetzRenyiMutualInformationPSD barPetzRenyiMutualInformationPSDFinite
  apply rhoAB.petzRenyiPSD_eq_coe_finite_of_traceCoeff_pos
  exact rhoAB.petzRenyiPSDTraceCoeff_pos_of_support
    (rhoAB.marginalA.prod rhoAB.marginalB)
      (rhoAB.rpow_matrix_supports_prod_marginals halpha0)

end State

namespace Channel

variable (N : Channel a b)

/-- Barred Petz--Renyi mutual information of an input-reference pure state.

The positivity witnesses are explicit because the current Petz kernel is
positive-definite.  This is the state-level quantity appearing in
`bar I_alpha(N)` before taking the channel supremum. -/
def inputBarPetzRenyiMutualInformation
    (ψ : PureVector (Prod a a))
    (hω : (N.hypothesisTestingOutputState ψ).matrix.PosDef)
    (hR : (N.hypothesisTestingOutputState ψ).marginalA.matrix.PosDef)
    (hB : (N.hypothesisTestingOutputState ψ).marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  (N.hypothesisTestingOutputState ψ).barPetzRenyiMutualInformation
    hω hR hB α hα_pos hα_ne_one

/-- PSD-domain barred Petz--Renyi mutual information of an input-reference
pure state. -/
def inputBarPetzRenyiMutualInformationPSDFinite
    (ψ : PureVector (Prod a a))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  (N.hypothesisTestingOutputState ψ).barPetzRenyiMutualInformationPSDFinite
    α hα_pos hα_ne_one

/-- Canonical extended-real PSD barred Petz value for a fixed channel input. -/
noncomputable def inputBarPetzRenyiMutualInformationPSD
    (ψ : PureVector (Prod a a))
    (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1) : EReal :=
  (N.hypothesisTestingOutputState ψ).barPetzRenyiMutualInformationPSD
    α hα_pos hα_lt_one

/-- The canonical fixed-input barred PSD value is the coercion of its finite
real representative. -/
theorem inputBarPetzRenyiMutualInformationPSD_eq_coe_finite
    (ψ : PureVector (Prod a a))
    (alpha : ℝ) (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    N.inputBarPetzRenyiMutualInformationPSD ψ alpha halpha0 halpha1 =
      (N.inputBarPetzRenyiMutualInformationPSDFinite
        ψ alpha halpha0 (ne_of_lt halpha1) : EReal) := by
  exact State.barPetzRenyiMutualInformationPSD_eq_coe_finite
    (N.hypothesisTestingOutputState ψ) alpha halpha0 halpha1

/-- Value set for the barred channel Petz--Renyi quantity. -/
def barPetzRenyiMutualInformationValueSet
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : Set ℝ :=
  {value |
    ∃ ψ : PureVector (Prod a a),
      ∃ hω : (N.hypothesisTestingOutputState ψ).matrix.PosDef,
        ∃ hR : (N.hypothesisTestingOutputState ψ).marginalA.matrix.PosDef,
          ∃ hB : (N.hypothesisTestingOutputState ψ).marginalB.matrix.PosDef,
            value =
              N.inputBarPetzRenyiMutualInformation ψ hω hR hB
                α hα_pos hα_ne_one}

/-- Barred channel Petz--Renyi mutual information
`bar I_alpha(N) = sup_psi bar I_alpha(R;B)_{(id tensor N)(psi)}`.

This follows the Khatri--Wilde barred, non-optimized convention. -/
def barPetzRenyiMutualInformation
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  sSup (N.barPetzRenyiMutualInformationValueSet α hα_pos hα_ne_one)

/-- PSD-domain value set for the barred channel Petz--Renyi quantity. -/
def barPetzRenyiMutualInformationPSDFiniteValueSet
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : Set ℝ :=
  {value |
    ∃ ψ : PureVector (Prod a a),
      value = N.inputBarPetzRenyiMutualInformationPSDFinite ψ
        α hα_pos hα_ne_one}

/-- PSD-domain barred channel Petz--Renyi mutual information
`bar I_alpha(N) = sup_psi bar I_alpha(R;B)_{(id tensor N)(psi)}`. -/
def barPetzRenyiMutualInformationPSDFinite
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  sSup (N.barPetzRenyiMutualInformationPSDFiniteValueSet α hα_pos hα_ne_one)

theorem barPetzRenyiMutualInformation_eq_sSup
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    N.barPetzRenyiMutualInformation α hα_pos hα_ne_one =
      sSup (N.barPetzRenyiMutualInformationValueSet α hα_pos hα_ne_one) :=
  rfl

/-- Unfolding theorem for the PSD-domain barred channel Petz--Renyi quantity. -/
theorem barPetzRenyiMutualInformationPSDFinite_eq_sSup
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    N.barPetzRenyiMutualInformationPSDFinite α hα_pos hα_ne_one =
      sSup (N.barPetzRenyiMutualInformationPSDFiniteValueSet α hα_pos hα_ne_one) :=
  rfl

/-- Extended-real value set for the canonical PSD barred channel quantity. -/
noncomputable def barPetzRenyiMutualInformationPSDValueSet
    (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1) : Set EReal :=
  {value |
    ∃ ψ : PureVector (Prod a a),
      value = N.inputBarPetzRenyiMutualInformationPSD ψ α hα_pos hα_lt_one}

/-- Canonical PSD barred Petz--Renyi channel mutual information. -/
noncomputable def barPetzRenyiMutualInformationPSD
    (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1) : EReal :=
  sSup (N.barPetzRenyiMutualInformationPSDValueSet α hα_pos hα_lt_one)

theorem barPetzRenyiMutualInformationPSD_eq_sSup
    (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    N.barPetzRenyiMutualInformationPSD α hα_pos hα_lt_one =
      sSup (N.barPetzRenyiMutualInformationPSDValueSet α hα_pos hα_lt_one) :=
  rfl

/-- Channel-level hypothesis-testing/Petz comparison needed by the
Khatri--Wilde Petz one-shot lower-bound theorem.

The full proof of this predicate is the source proposition
`prop:ineq-hypo-renyi` lifted through the barred channel supremum. -/
def BarHypothesisTestingFiniteDominatesBarPetz
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : Prop :=
  N.barPetzRenyiMutualInformation α hα_pos hα_ne_one +
      α / (α - 1) * log2 (1 / ε) ≤
    N.barHypothesisTestingMutualInformationFinite ε

/-- Extended-real channel-level hypothesis-testing/Petz comparison.

This is the same source comparison as `BarHypothesisTestingFiniteDominatesBarPetz`,
but with the source-faithful extended-real `bar I_H^ε`.  It avoids imposing an
artificial real boundedness side condition on the hypothesis-testing supremum. -/
def BarHypothesisTestingDominatesBarPetz
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : Prop :=
  (N.barPetzRenyiMutualInformation α hα_pos hα_ne_one : EReal) +
      ((α / (α - 1) * log2 (1 / ε) : ℝ) : EReal) ≤
    N.barHypothesisTestingMutualInformation ε

/-- Extended-real channel-level hypothesis-testing/Petz comparison for the
PSD-domain barred Petz quantity. -/
def BarHypothesisTestingDominatesBarPetzPSDFinite
    (ε α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : Prop :=
  (N.barPetzRenyiMutualInformationPSDFinite α hα_pos hα_ne_one : EReal) +
      ((α / (α - 1) * log2 (1 / ε) : ℝ) : EReal) ≤
    N.barHypothesisTestingMutualInformation ε

/-- Canonical extended-real channel comparison for the PSD Petz branch. -/
def BarHypothesisTestingDominatesBarPetzPSD
    (ε α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1) : Prop :=
  N.barPetzRenyiMutualInformationPSD α hα_pos hα_lt_one +
      ((α / (α - 1) * log2 (1 / ε) : ℝ) : EReal) ≤
    N.barHypothesisTestingMutualInformation ε

/--
Algebraic bridge from the hypothesis-testing one-shot lower bound and the
channel-level `D_H`/Petz comparison to the Petz--Renyi one-shot lower bound.

This is the last line of Khatri--Wilde's proof of
`thm-eacc_one_shot_lower_bound`, with the still-to-be-proved comparison kept as
an explicit hypothesis.
-/
theorem oneShotEntanglementAssistedClassicalCapacityE_petzLowerBound_of_comparison
    {ε η α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hHT :
      ((N.barHypothesisTestingMutualInformationFinite (ε - η) -
          log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
        N.oneShotEntanglementAssistedClassicalCapacityE ε)
    (hcmp : N.BarHypothesisTestingFiniteDominatesBarPetz
        (ε - η) α hα_pos (ne_of_lt hα_lt_one)) :
    ((N.barPetzRenyiMutualInformation α hα_pos (ne_of_lt hα_lt_one) -
        α / (1 - α) * log2 (1 / (ε - η)) -
        log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  have hα_ne_one : α ≠ 1 := ne_of_lt hα_lt_one
  have hden :
      α / (α - 1) * log2 (1 / (ε - η)) =
        - (α / (1 - α) * log2 (1 / (ε - η))) := by
    have hsub : α - 1 = -(1 - α) := by ring
    rw [hsub]
    field_simp [sub_ne_zero.mpr hα_ne_one.symm]
  have hreal :
      N.barPetzRenyiMutualInformation α hα_pos hα_ne_one -
          α / (1 - α) * log2 (1 / (ε - η)) -
          log2 (4 * ε / η ^ 2) ≤
        N.barHypothesisTestingMutualInformationFinite (ε - η) -
          log2 (4 * ε / η ^ 2) := by
    unfold BarHypothesisTestingFiniteDominatesBarPetz at hcmp
    linarith
  exact (EReal.coe_le_coe_iff.mpr hreal).trans hHT

/--
Algebraic bridge from the source-faithful extended-real hypothesis-testing
one-shot lower bound and the channel-level real `D_H`/Petz comparison to the
Petz--Renyi one-shot lower bound.

The comparison theorem is still stated using the real-valued barred
hypothesis-testing information, while the hypothesis-testing lower bound is
stated with the source-faithful extended-real barred information.  The bridge
below inserts the canonical embedding `bar I_H ≤ bar I_H^E`.
-/
theorem oneShotEntanglementAssistedClassicalCapacityE_petzLowerBound_of_comparison_E
    [Nonempty (PureVector (Prod a a))]
    {ε η α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hHT :
      N.barHypothesisTestingMutualInformation (ε - η) -
          (log2 (4 * ε / η ^ 2) : EReal) ≤
        N.oneShotEntanglementAssistedClassicalCapacityE ε)
    (hcmp : N.BarHypothesisTestingFiniteDominatesBarPetz
        (ε - η) α hα_pos (ne_of_lt hα_lt_one)) :
    ((N.barPetzRenyiMutualInformation α hα_pos (ne_of_lt hα_lt_one) -
        α / (1 - α) * log2 (1 / (ε - η)) -
        log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  have hα_ne_one : α ≠ 1 := ne_of_lt hα_lt_one
  have hden :
      α / (α - 1) * log2 (1 / (ε - η)) =
        - (α / (1 - α) * log2 (1 / (ε - η))) := by
    have hsub : α - 1 = -(1 - α) := by ring
    rw [hsub]
    field_simp [sub_ne_zero.mpr hα_ne_one.symm]
  have hreal :
      N.barPetzRenyiMutualInformation α hα_pos hα_ne_one -
          α / (1 - α) * log2 (1 / (ε - η)) -
          log2 (4 * ε / η ^ 2) ≤
        N.barHypothesisTestingMutualInformationFinite (ε - η) -
          log2 (4 * ε / η ^ 2) := by
    unfold BarHypothesisTestingFiniteDominatesBarPetz at hcmp
    linarith
  have hrealE :
      ((N.barPetzRenyiMutualInformation α hα_pos hα_ne_one -
          α / (1 - α) * log2 (1 / (ε - η)) -
          log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
        (N.barHypothesisTestingMutualInformationFinite (ε - η) : EReal) -
          (log2 (4 * ε / η ^ 2) : EReal) := by
    simpa [EReal.coe_sub] using EReal.coe_le_coe_iff.mpr hreal
  exact hrealE.trans
    ((EReal.sub_le_sub
      (N.barHypothesisTestingMutualInformationFinite_le_E (ε - η)) le_rfl).trans hHT)

/--
Algebraic bridge from the extended-real hypothesis-testing one-shot lower
bound and the extended-real channel-level `D_H`/Petz comparison to the
Petz--Renyi one-shot lower bound.

This is the preferred bridge for the public one-shot lower-bound route because
it uses the source-faithful `bar I_H^ε` convention throughout.
-/
theorem oneShotEntanglementAssistedClassicalCapacityE_petzLowerBound_of_comparison_EReal
    {ε η α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hHT :
      N.barHypothesisTestingMutualInformation (ε - η) -
          (log2 (4 * ε / η ^ 2) : EReal) ≤
        N.oneShotEntanglementAssistedClassicalCapacityE ε)
    (hcmp : N.BarHypothesisTestingDominatesBarPetz
        (ε - η) α hα_pos (ne_of_lt hα_lt_one)) :
    ((N.barPetzRenyiMutualInformation α hα_pos (ne_of_lt hα_lt_one) -
        α / (1 - α) * log2 (1 / (ε - η)) -
        log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  have hα_ne_one : α ≠ 1 := ne_of_lt hα_lt_one
  have hden :
      α / (α - 1) * log2 (1 / (ε - η)) =
        - (α / (1 - α) * log2 (1 / (ε - η))) := by
    have hsub : α - 1 = -(1 - α) := by ring
    rw [hsub]
    field_simp [sub_ne_zero.mpr hα_ne_one.symm]
  have hleft :
      ((N.barPetzRenyiMutualInformation α hα_pos hα_ne_one -
          α / (1 - α) * log2 (1 / (ε - η)) -
          log2 (4 * ε / η ^ 2) : ℝ) : EReal) =
        (N.barPetzRenyiMutualInformation α hα_pos hα_ne_one : EReal) +
          ((α / (α - 1) * log2 (1 / (ε - η)) : ℝ) : EReal) -
            (log2 (4 * ε / η ^ 2) : EReal) := by
    have hreal :
        N.barPetzRenyiMutualInformation α hα_pos hα_ne_one -
            α / (1 - α) * log2 (1 / (ε - η)) -
            log2 (4 * ε / η ^ 2) =
          N.barPetzRenyiMutualInformation α hα_pos hα_ne_one +
            α / (α - 1) * log2 (1 / (ε - η)) -
              log2 (4 * ε / η ^ 2) := by
      rw [hden]
      ring
    rw [hreal]
    simp [EReal.coe_sub, EReal.coe_add]
  rw [hleft]
  exact (EReal.sub_le_sub hcmp le_rfl).trans hHT

/-- PSD-domain algebraic bridge from the extended-real hypothesis-testing
one-shot lower bound and the extended-real channel-level `D_H`/Petz
comparison to the Petz--Renyi one-shot lower bound. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_petzPSDFiniteLowerBound_of_comparison_EReal
    {ε η α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hHT :
      N.barHypothesisTestingMutualInformation (ε - η) -
          (log2 (4 * ε / η ^ 2) : EReal) ≤
        N.oneShotEntanglementAssistedClassicalCapacityE ε)
    (hcmp : N.BarHypothesisTestingDominatesBarPetzPSDFinite
        (ε - η) α hα_pos (ne_of_lt hα_lt_one)) :
    ((N.barPetzRenyiMutualInformationPSDFinite α hα_pos (ne_of_lt hα_lt_one) -
        α / (1 - α) * log2 (1 / (ε - η)) -
        log2 (4 * ε / η ^ 2) : ℝ) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  have hα_ne_one : α ≠ 1 := ne_of_lt hα_lt_one
  have hden :
      α / (α - 1) * log2 (1 / (ε - η)) =
        - (α / (1 - α) * log2 (1 / (ε - η))) := by
    have hsub : α - 1 = -(1 - α) := by ring
    rw [hsub]
    field_simp [sub_ne_zero.mpr hα_ne_one.symm]
  have hleft :
      ((N.barPetzRenyiMutualInformationPSDFinite α hα_pos hα_ne_one -
          α / (1 - α) * log2 (1 / (ε - η)) -
          log2 (4 * ε / η ^ 2) : ℝ) : EReal) =
        (N.barPetzRenyiMutualInformationPSDFinite α hα_pos hα_ne_one : EReal) +
          ((α / (α - 1) * log2 (1 / (ε - η)) : ℝ) : EReal) -
            (log2 (4 * ε / η ^ 2) : EReal) := by
    have hreal :
        N.barPetzRenyiMutualInformationPSDFinite α hα_pos hα_ne_one -
            α / (1 - α) * log2 (1 / (ε - η)) -
            log2 (4 * ε / η ^ 2) =
          N.barPetzRenyiMutualInformationPSDFinite α hα_pos hα_ne_one +
            α / (α - 1) * log2 (1 / (ε - η)) -
              log2 (4 * ε / η ^ 2) := by
      rw [hden]
      ring
    rw [hreal]
    simp [EReal.coe_sub, EReal.coe_add]
  rw [hleft]
  exact (EReal.sub_le_sub hcmp le_rfl).trans hHT

/-- Canonical extended-real algebraic bridge for the PSD Petz lower bound. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_petzPSDLowerBound_of_comparison_EReal
    {ε η α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hHT :
      N.barHypothesisTestingMutualInformation (ε - η) -
          (log2 (4 * ε / η ^ 2) : EReal) ≤
        N.oneShotEntanglementAssistedClassicalCapacityE ε)
    (hcmp : N.BarHypothesisTestingDominatesBarPetzPSD
        (ε - η) α hα_pos hα_lt_one) :
    N.barPetzRenyiMutualInformationPSD α hα_pos hα_lt_one -
          ((α / (1 - α) * log2 (1 / (ε - η)) : ℝ) : EReal) -
        (log2 (4 * ε / η ^ 2) : EReal) ≤
      N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  have hα_ne_one : α ≠ 1 := ne_of_lt hα_lt_one
  have hden :
      α / (α - 1) * log2 (1 / (ε - η)) =
        -(α / (1 - α) * log2 (1 / (ε - η))) := by
    have hsub : α - 1 = -(1 - α) := by ring
    rw [hsub]
    field_simp [sub_ne_zero.mpr hα_ne_one.symm]
  have hleft :
      N.barPetzRenyiMutualInformationPSD α hα_pos hα_lt_one -
          ((α / (1 - α) * log2 (1 / (ε - η)) : ℝ) : EReal) =
        N.barPetzRenyiMutualInformationPSD α hα_pos hα_lt_one +
          ((α / (α - 1) * log2 (1 / (ε - η)) : ℝ) : EReal) := by
    rw [hden]
    simp [sub_eq_add_neg]
  rw [hleft]
  exact (EReal.sub_le_sub hcmp le_rfl).trans hHT

end Channel

end

end QIT
