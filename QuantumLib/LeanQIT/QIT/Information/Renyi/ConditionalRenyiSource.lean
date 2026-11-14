/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.ConditionalRenyi
public import QIT.Information.Renyi.ConditionalPetzRenyi

/-!
# Source-shaped conditional Renyi entropy APIs

Semantic wrappers for Tomamichel's four conditional Renyi entropies
`H_α^↓`, `H_α^↑`, `H̃_α^↓`, and `H̃_α^↑`.

Source: Tomamichel2015FiniteResources, `cond.tex:87-98`.

This file is an API layer only. It does not prove data processing, duality,
uncertainty relations, optimizer existence, or compactness statements.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

open Matrix

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace State

/-- Source-shaped Petz conditional Renyi entropy `H_α^↓(A|B)_ρ`.

This fixes the reference side to the canonical marginal `ρ_B`, matching
Tomamichel2015FiniteResources, `cond.tex:87-98`. -/
def conditionalPetzRenyiDown (ρ : State (Prod a b))
    (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  ρ.conditionalPetzRenyiEntropyCandidateFullReference ρ.marginalB hρB
    α hα_pos hα_ne_one

@[simp]
theorem conditionalPetzRenyiDown_eq (ρ : State (Prod a b))
    (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalPetzRenyiDown hρB α hα_pos hα_ne_one =
      ρ.conditionalPetzRenyiEntropyCandidateFullReference ρ.marginalB hρB
        α hα_pos hα_ne_one :=
  rfl

/-- Candidate value set for the source-shaped Petz upward conditional Renyi
entropy `H_α^↑(A|B)_ρ`.

The supremum ranges over normalized full-rank side-information states, matching
Tomamichel2015FiniteResources, `cond.tex:87-98`. -/
def conditionalPetzRenyiUpValueSet (ρ : State (Prod a b))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : Set ℝ :=
  {h | ∃ σ : State b, ∃ hσ : σ.matrix.PosDef,
    h = ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α hα_pos hα_ne_one}

@[simp]
theorem conditionalPetzRenyiUpValueSet_eq (ρ : State (Prod a b))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalPetzRenyiUpValueSet α hα_pos hα_ne_one =
      {h | ∃ σ : State b, ∃ hσ : σ.matrix.PosDef,
        h = ρ.conditionalPetzRenyiEntropyCandidateFullReference
          σ hσ α hα_pos hα_ne_one} :=
  rfl

/-- Source-shaped Petz upward conditional Renyi entropy `H_α^↑(A|B)_ρ`.

This is the `sSup` over the full-rank side-reference value set from
Tomamichel2015FiniteResources, `cond.tex:87-98`. -/
def conditionalPetzRenyiUp (ρ : State (Prod a b))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  sSup (ρ.conditionalPetzRenyiUpValueSet α hα_pos hα_ne_one)

@[simp]
theorem conditionalPetzRenyiUp_eq (ρ : State (Prod a b))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalPetzRenyiUp α hα_pos hα_ne_one =
      sSup (ρ.conditionalPetzRenyiUpValueSet α hα_pos hα_ne_one) :=
  rfl

/-- Source-shaped sandwiched conditional Renyi entropy `H̃_α^↓(A|B)_ρ`.

This fixes the reference side to `I_A ⊗ ρ_B`, matching
Tomamichel2015FiniteResources, `cond.tex:87-98`. -/
def conditionalSandwichedRenyiDown (ρ : State (Prod a b))
    (hρ : ρ.matrix.PosDef) (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : ℝ :=
  - sandwichedRenyiReference ρ
      (identityTensorStateMatrix (a := a) ρ.marginalB) hρ
      (identityTensorStateMatrix_posDef_of_posDef (a := a) ρ.marginalB hρB)
      α hα_pos hα_ne_one

@[simp]
theorem conditionalSandwichedRenyiDown_eq (ρ : State (Prod a b))
    (hρ : ρ.matrix.PosDef) (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalSandwichedRenyiDown hρ hρB α hα_pos hα_ne_one =
      - sandwichedRenyiReference ρ
          (identityTensorStateMatrix (a := a) ρ.marginalB) hρ
          (identityTensorStateMatrix_posDef_of_posDef (a := a) ρ.marginalB hρB)
          α hα_pos hα_ne_one :=
  rfl

/-- Source-shaped sandwiched upward conditional Renyi entropy `H̃_α^↑(A|B)_ρ`.

Compatibility wrapper around the existing upward sandwiched API, preserving
`State.conditionalSandwichedRenyi`. -/
def conditionalSandwichedRenyiUp (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) : ℝ :=
  ρ.conditionalSandwichedRenyi hρ α hα hα_ne_one

@[simp]
theorem conditionalSandwichedRenyiUp_eq (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalSandwichedRenyiUp hρ α hα hα_ne_one =
      ρ.conditionalSandwichedRenyi hρ α hα hα_ne_one :=
  rfl

/-- Every full-rank side-information state contributes its Petz full-reference
candidate value to the upward Petz value set. -/
theorem conditionalPetzRenyiEntropyCandidateFullReference_mem_upValueSet
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α hα_pos hα_ne_one ∈
      ρ.conditionalPetzRenyiUpValueSet α hα_pos hα_ne_one :=
  ⟨σ, hσ, rfl⟩

/-- The upward Petz value set is nonempty on a nonempty conditioning system.

The witness is the full-rank uniform diagonal state on the conditioning
register. -/
theorem conditionalPetzRenyiUpValueSet_nonempty [Nonempty b]
    (ρ : State (Prod a b))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    (ρ.conditionalPetzRenyiUpValueSet α hα_pos hα_ne_one).Nonempty := by
  classical
  let u : b → ℝ≥0 := fun _ => (Fintype.card b : ℝ≥0)⁻¹
  have husum : ∑ i, u i = 1 := by
    simp [u, Finset.sum_const, Fintype.card_ne_zero]
  have hupos : ∀ i, 0 < (u i : ℝ) := by
    intro i
    have hcard_pos : 0 < (Fintype.card b : ℝ≥0) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i⟩)
    exact_mod_cast inv_pos.mpr hcard_pos
  let σ : State b := Classical.diagonalState u husum
  have hσ : σ.matrix.PosDef := by
    simpa [σ] using Classical.diagonalState_posDef u husum hupos
  exact
    ⟨ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α hα_pos hα_ne_one,
      ρ.conditionalPetzRenyiEntropyCandidateFullReference_mem_upValueSet
        σ hσ α hα_pos hα_ne_one⟩

/-- A uniform upper bound on all full-rank side-reference Petz candidates makes
the upward Petz value set bounded above. -/
theorem conditionalPetzRenyiUpValueSet_bddAbove_of_forall_candidate_le
    (ρ : State (Prod a b))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1)
    {C : ℝ}
    (hC : ∀ σ : State b, ∀ hσ : σ.matrix.PosDef,
      ρ.conditionalPetzRenyiEntropyCandidateFullReference
        σ hσ α hα_pos hα_ne_one ≤ C) :
    BddAbove (ρ.conditionalPetzRenyiUpValueSet α hα_pos hα_ne_one) := by
  refine ⟨C, ?_⟩
  intro x hx
  rcases hx with ⟨σ, hσ, rfl⟩
  exact hC σ hσ

/-- Petz full-reference candidates are bounded by the upward Petz entropy when
the value set is bounded above. -/
theorem conditionalPetzRenyiEntropyCandidateFullReference_le_conditionalPetzRenyiUp_of_bddAbove
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1)
    (hbdd : BddAbove (ρ.conditionalPetzRenyiUpValueSet α hα_pos hα_ne_one)) :
    ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α hα_pos hα_ne_one ≤
      ρ.conditionalPetzRenyiUp α hα_pos hα_ne_one := by
  rw [conditionalPetzRenyiUp_eq]
  exact le_csSup hbdd
    (ρ.conditionalPetzRenyiEntropyCandidateFullReference_mem_upValueSet
      σ hσ α hα_pos hα_ne_one)

/-- Upward Petz entropy upper bound from a pointwise candidate upper bound. -/
theorem conditionalPetzRenyiUp_le_of_forall_candidate_le [Nonempty b]
    (ρ : State (Prod a b))
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1)
    {C : ℝ}
    (hC : ∀ σ : State b, ∀ hσ : σ.matrix.PosDef,
      ρ.conditionalPetzRenyiEntropyCandidateFullReference
        σ hσ α hα_pos hα_ne_one ≤ C) :
    ρ.conditionalPetzRenyiUp α hα_pos hα_ne_one ≤ C := by
  rw [conditionalPetzRenyiUp_eq]
  refine csSup_le (ρ.conditionalPetzRenyiUpValueSet_nonempty α hα_pos hα_ne_one) ?_
  intro x hx
  rcases hx with ⟨σ, hσ, rfl⟩
  exact hC σ hσ

end State

end

end QIT
