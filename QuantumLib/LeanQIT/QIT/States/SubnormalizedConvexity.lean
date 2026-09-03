/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Geometry.FidelityConcavity
public import QIT.States.SubnormalizedTopology
public import Mathlib.Analysis.Convex.Basic

/-!
# Convexity of subnormalized purified-distance balls

This module formalizes the convexity part of the epsilon-ball properties in
Tomamichel2015FiniteResources, `calculus.tex:398-411`.  The source states the
property without a proof; the Lean proof uses normalized hat extensions and
fixed-left fidelity quasiconcavity.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix Set

namespace QIT

universe u

noncomputable section

namespace SubnormalizedState

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- A binary convex combination of subnormalized finite-dimensional states. -/
def convexCombination (t : ℝ) (ρ σ : SubnormalizedState a)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : SubnormalizedState a where
  matrix := ((t : ℂ) • ρ.matrix) + (((1 - t : ℝ) : ℂ) • σ.matrix)
  pos := by
    exact Matrix.PosSemidef.add
      (ρ.pos.smul (by exact_mod_cast ht0))
      (σ.pos.smul (by exact_mod_cast sub_nonneg.mpr ht1))
  trace_le_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
    rw [Algebra.smul_def, Algebra.smul_def]
    simp [Complex.mul_re, ρ.trace_im_zero, σ.trace_im_zero]
    nlinarith [ρ.trace_le_one, σ.trace_le_one]

@[simp]
theorem convexCombination_matrix (t : ℝ) (ρ σ : SubnormalizedState a)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (convexCombination t ρ σ ht0 ht1).matrix =
      ((t : ℂ) • ρ.matrix) + (((1 - t : ℝ) : ℂ) • σ.matrix) :=
  rfl

@[simp]
theorem convexCombination_trace_re (t : ℝ) (ρ σ : SubnormalizedState a)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (convexCombination t ρ σ ht0 ht1).matrix.trace.re =
      t * ρ.matrix.trace.re + (1 - t) * σ.matrix.trace.re := by
  rw [convexCombination_matrix, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
  rw [Algebra.smul_def, Algebra.smul_def]
  simp [Complex.mul_re, ρ.trace_im_zero, σ.trace_im_zero]

/-- Hat extension is affine on binary subnormalized-state combinations. -/
theorem hatExtension_convexCombination (t : ℝ) (ρ σ : SubnormalizedState a)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (convexCombination t ρ σ ht0 ht1).hatExtension =
      State.convexCombination t ρ.hatExtension σ.hatExtension ht0 ht1 := by
  apply State.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · cases i
    cases j
    simp [State.convexCombination, hatFailureMass]
    ring
  · simp [State.convexCombination]
  · simp [State.convexCombination]
  · simp [State.convexCombination, convexCombination]

/-- For fixed left input, generalized fidelity is quasiconcave in the right
subnormalized state. -/
theorem generalizedFidelity_convexCombination_right_ge_min
    (ρ σ τ : SubnormalizedState a) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    min (ρ.generalizedFidelity σ) (ρ.generalizedFidelity τ) ≤
      ρ.generalizedFidelity (convexCombination t σ τ ht0 ht1) := by
  rw [generalizedFidelity_eq_squaredFidelity_hatExtension,
    generalizedFidelity_eq_squaredFidelity_hatExtension,
    generalizedFidelity_eq_squaredFidelity_hatExtension,
    hatExtension_convexCombination,
    State.squaredFidelity_eq_fidelity_sq,
    State.squaredFidelity_eq_fidelity_sq,
    State.squaredFidelity_eq_fidelity_sq]
  let ρhat : State (Sum PUnit.{1} a) := ρ.hatExtension
  let σhat : State (Sum PUnit.{1} a) := σ.hatExtension
  let τhat : State (Sum PUnit.{1} a) := τ.hatExtension
  change min ((ρhat.fidelity σhat) ^ 2) ((ρhat.fidelity τhat) ^ 2) ≤
    (ρhat.fidelity (State.convexCombination t σhat τhat ht0 ht1)) ^ 2
  have hroot := State.fidelity_convexCombination_right_ge_min
    ρhat σhat τhat t ht0 ht1
  have hσ0 : 0 ≤ ρhat.fidelity σhat :=
    State.fidelity_nonneg _ _
  have hτ0 : 0 ≤ ρhat.fidelity τhat :=
    State.fidelity_nonneg _ _
  have hmix0 :
      0 ≤ ρhat.fidelity (State.convexCombination t σhat τhat ht0 ht1) :=
    State.fidelity_nonneg _ _
  by_cases hστ : ρhat.fidelity σhat ≤ ρhat.fidelity τhat
  · have hsq :
        (ρhat.fidelity σhat) ^ 2 ≤ (ρhat.fidelity τhat) ^ 2 := by
      nlinarith
    rw [min_eq_left hsq]
    rw [min_eq_left hστ] at hroot
    nlinarith
  · have hτσ : ρhat.fidelity τhat ≤ ρhat.fidelity σhat := le_of_not_ge hστ
    have hsq :
        (ρhat.fidelity τhat) ^ 2 ≤ (ρhat.fidelity σhat) ^ 2 := by
      nlinarith
    rw [min_eq_right hsq]
    rw [min_eq_right hτσ] at hroot
    nlinarith

/-- A binary convex combination of two states in the same purified-distance
ball remains in that ball. -/
theorem purifiedBall_convexCombination
    (ρ σ τ : SubnormalizedState a) (ε t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hσ : ρ.purifiedBall ε σ) (hτ : ρ.purifiedBall ε τ) :
    ρ.purifiedBall ε (convexCombination t σ τ ht0 ht1) := by
  rw [purifiedBall_eq, purifiedDistance_eq] at hσ hτ ⊢
  have hfid := generalizedFidelity_convexCombination_right_ge_min
    ρ σ τ t ht0 ht1
  by_cases hστ : ρ.generalizedFidelity σ ≤ ρ.generalizedFidelity τ
  · rw [min_eq_left hστ] at hfid
    exact (Real.sqrt_le_sqrt (sub_le_sub_left hfid 1)).trans hσ
  · have hτσ : ρ.generalizedFidelity τ ≤ ρ.generalizedFidelity σ :=
      le_of_not_ge hστ
    rw [min_eq_right hτσ] at hfid
    exact (Real.sqrt_le_sqrt (sub_le_sub_left hfid 1)).trans hτ

/-- Matrix realization of a purified-distance ball. -/
def purifiedBallMatrixSet (ρ : SubnormalizedState a) (ε : ℝ) : Set (CMatrix a) :=
  (fun σ : SubnormalizedState a => σ.matrix) ''
    {σ : SubnormalizedState a | ρ.purifiedBall ε σ}

/-- The matrix realization of a purified-distance ball is compact. -/
theorem purifiedBallMatrixSet_isCompact (ρ : SubnormalizedState a) (ε : ℝ) :
    IsCompact (purifiedBallMatrixSet ρ ε) := by
  simpa [purifiedBallMatrixSet] using
    (purifiedBall_isCompact ρ ε).image continuous_matrix

/-- The matrix realization of a purified-distance ball is convex. -/
theorem purifiedBallMatrixSet_convex (ρ : SubnormalizedState a) (ε : ℝ) :
    Convex ℝ (purifiedBallMatrixSet ρ ε) := by
  rw [convex_iff_add_mem]
  rintro M ⟨σ, hσ, rfl⟩ N ⟨τ, hτ, rfl⟩ x y hx hy hxy
  have hx1 : x ≤ 1 := by nlinarith
  let ω := convexCombination x σ τ hx hx1
  refine ⟨ω, purifiedBall_convexCombination ρ σ τ ε x hx hx1 hσ hτ, ?_⟩
  have hy_eq : y = 1 - x := by nlinarith
  subst y
  change ω.matrix = x • σ.matrix + (1 - x) • τ.matrix
  rw [show ω.matrix = (convexCombination x σ τ hx hx1).matrix by rfl]
  rw [convexCombination_matrix]
  ext i j
  simp

end SubnormalizedState

end

end QIT
