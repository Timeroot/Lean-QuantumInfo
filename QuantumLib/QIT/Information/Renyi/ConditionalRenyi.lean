/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Renyi.Renyi

/-!
# Conditional upward sandwiched Renyi entropy

The one-shot conditional upward sandwiched Renyi entropy

  H̃^↑_α(A|B)_ρ = sup_{σ_B}  −D̃_α(ρ_AB ‖ I_A ⊗ σ_B)

in the repository bits convention, over the data-processing-valid range
`α ≥ 1/2` (`α ≠ 1`).

The second argument `I_A ⊗ σ_B` is subnormalized (trace `d_A`), so this kernel
works at the matrix level via `CFC.rpow` on the Kronecker product directly; it
does not require a `CFC.rpow` Kronecker factorization lemma. The supremum is
over full-rank (normalized, `PosDef`) side-information states `σ_B`.

Source: Tomamichel2015FiniteResources, `cond.tex` (the four conditional Renyi
entropies; the sandwiched data-processing range `α ∈ [1/2, ∞]`).

Optimizer existence, compactness, data processing, duality, and the entropic
uncertainty theorem are out of scope for this definition layer.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

open Matrix

noncomputable section
universe u v
variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

open QIT

namespace MState

/-- The per-side-information candidate `−D̃_α(ρ_AB ‖ I_A ⊗ σ_B)`.

Both witnesses are API preconditions aligning the statement with the
mathematical domain (positive-definite `ρ_AB` and `σ_B`); they are not needed
for `CFC.rpow` to typecheck, mirroring `MState.sandwichedRenyi`. -/
def conditionalSandwichedRenyiCandidate (ρ : MState (a × b)) (_hρ : ρ.m.PosDef)
    (σ : MState b) (_hσ : σ.m.PosDef) (α : ℝ) (_hα_pos : 0 < α)
    (_hα_ne_one : α ≠ 1) : ℝ :=
  let r := -(1 / (α - 1))
  let s := (1 - α) / (2 * α)
  let τ : CMatrix (a × b) := identityTensorStateMatrix (a := a) σ
  let M := CFC.rpow (CFC.rpow τ s * ρ.m * CFC.rpow τ s) α
  r * log2 M.trace.re

/-- Definition-level candidate value set for upward sandwiched conditional
Renyi entropy.

Keeping the set as a named object lets the later minimax/duality proof refer
to the exact `sSup` domain without repeatedly unfolding the definition. -/
def conditionalSandwichedRenyiValueSet (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) : Set ℝ :=
  {h | ∃ σ : MState b, ∃ hσ : σ.m.PosDef,
    h = conditionalSandwichedRenyiCandidate ρ hρ σ hσ α (by linarith) hα_ne_one}

@[simp]
theorem conditionalSandwichedRenyiValueSet_eq
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalSandwichedRenyiValueSet hρ α hα hα_ne_one =
      {h | ∃ σ : MState b, ∃ hσ : σ.m.PosDef,
        h = conditionalSandwichedRenyiCandidate ρ hρ σ hσ α
          (by linarith) hα_ne_one} :=
  rfl

/-- Conditional upward sandwiched Renyi entropy `H̃^↑_α(A|B)_ρ` as the supremum
over normalized full-rank side-information states `σ_B` of the candidate value.

At `α = 1` the sandwiched kernel degenerates and the value is the Umegaki
limit rather than a candidate supremum, so the API surface is `α ≥ 1/2`,
`α ≠ 1`. -/
def conditionalSandwichedRenyi (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) : ℝ :=
  sSup (ρ.conditionalSandwichedRenyiValueSet hρ α hα hα_ne_one)

@[simp]
theorem conditionalSandwichedRenyi_eq (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalSandwichedRenyi hρ α hα hα_ne_one =
      sSup (ρ.conditionalSandwichedRenyiValueSet hρ α hα hα_ne_one) :=
  rfl

/-- Every full-rank side-information state contributes its candidate value to
the upward conditional sandwiched Renyi value set. -/
theorem conditionalSandwichedRenyiCandidate_mem_valueSet
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (σ : MState b) (hσ : σ.m.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α (by linarith) hα_ne_one ∈
      ρ.conditionalSandwichedRenyiValueSet hρ α hα hα_ne_one :=
  ⟨σ, hσ, rfl⟩

/-- The upward conditional sandwiched Renyi candidate set is nonempty on a
nonempty conditioning system.

The witness is the full-rank uniform diagonal state on the conditioning
register. This is the basic order-theoretic precondition needed before applying
`sSup` rules in the conditional-duality/minimax route. -/
theorem conditionalSandwichedRenyiValueSet_nonempty [Nonempty b]
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) :
    (ρ.conditionalSandwichedRenyiValueSet hρ α hα hα_ne_one).Nonempty := by
  classical
  let u : b → ℝ≥0 := fun _ => (Fintype.card b : ℝ≥0)⁻¹
  have husum : ∑ i, u i = 1 := by
    simp [u, Finset.sum_const, Fintype.card_ne_zero]
  have hupos : ∀ i, 0 < (u i : ℝ) := by
    intro i
    have hcard_pos : 0 < (Fintype.card b : ℝ≥0) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i⟩)
    exact_mod_cast inv_pos.mpr hcard_pos
  let σ : MState b := Classical.diagonalState u husum
  have hσ : σ.m.PosDef := by
    simpa [σ] using Classical.diagonalState_posDef u husum hupos
  exact ⟨ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α (by linarith) hα_ne_one,
    ρ.conditionalSandwichedRenyiCandidate_mem_valueSet hρ σ hσ α hα hα_ne_one⟩

/-- A uniform upper bound on all full-rank side-information candidates makes
the conditional sandwiched Renyi value set bounded above. -/
theorem conditionalSandwichedRenyiValueSet_bddAbove_of_forall_candidate_le
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1)
    {C : ℝ}
    (hC : ∀ σ : MState b, ∀ hσ : σ.m.PosDef,
      ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α (by linarith) hα_ne_one ≤ C) :
    BddAbove (ρ.conditionalSandwichedRenyiValueSet hρ α hα hα_ne_one) := by
  refine ⟨C, ?_⟩
  intro x hx
  rcases hx with ⟨σ, hσ, rfl⟩
  exact hC σ hσ

/-- Candidate upper bound by the conditional entropy, assuming the value set
is bounded above.

This is the order-theoretic `sSup` handoff needed by the later Sion/minimax
route: once boundedness of the conditional candidate family is available, any
explicit optimizer candidate can be compared directly with
`conditionalSandwichedRenyi`. -/
theorem conditionalSandwichedRenyiCandidate_le_conditionalSandwichedRenyi_of_bddAbove
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (σ : MState b) (hσ : σ.m.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1)
    (hbdd : BddAbove (ρ.conditionalSandwichedRenyiValueSet hρ α hα hα_ne_one)) :
    ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α (by linarith) hα_ne_one ≤
      ρ.conditionalSandwichedRenyi hρ α hα hα_ne_one := by
  rw [conditionalSandwichedRenyi_eq]
  exact le_csSup hbdd
    (ρ.conditionalSandwichedRenyiCandidate_mem_valueSet hρ σ hσ α hα hα_ne_one)

/-- Conditional entropy upper bound from a pointwise candidate upper bound.

This is the companion `sSup` direction to
`conditionalSandwichedRenyiCandidate_le_conditionalSandwichedRenyi_of_bddAbove`.
Together they give the order-theoretic shell needed for the later Sion/minimax
argument: proving an inequality for every side-information candidate proves it
for the optimized conditional entropy. -/
theorem conditionalSandwichedRenyi_le_of_forall_candidate_le [Nonempty b]
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1)
    {C : ℝ}
    (hC : ∀ σ : MState b, ∀ hσ : σ.m.PosDef,
      ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α (by linarith) hα_ne_one ≤ C) :
    ρ.conditionalSandwichedRenyi hρ α hα hα_ne_one ≤ C := by
  rw [conditionalSandwichedRenyi_eq]
  refine csSup_le (ρ.conditionalSandwichedRenyiValueSet_nonempty hρ α hα hα_ne_one) ?_
  intro x hx
  rcases hx with ⟨σ, hσ, rfl⟩
  exact hC σ hσ

end MState
