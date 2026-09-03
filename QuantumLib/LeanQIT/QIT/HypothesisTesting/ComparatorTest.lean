/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.HypothesisTesting.MutualInformation
public import QIT.Classical.Bridge
public import QIT.Util.SDP.HermitianPSDTraceDuality
public import Mathlib.Data.EReal.Basic

/-!
# Classical comparator tests

This module records the finite classical-register comparator test used in the
one-shot entanglement-assisted classical communication meta-converse
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:327-394].

The source argument tests equality of a uniformly distributed message register
and the decoded message register.  The comparator projection has type-II error
`1 / |M|` against `π_M ⊗ σ_{M'}` for every side state `σ_{M'}`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u

noncomputable section

variable {M : Type u} [Fintype M] [DecidableEq M]

/-- Uniform probability distribution on a finite nonempty message register. -/
def uniformMessageProb [Nonempty M] : M → ℝ≥0 :=
  fun _ => (Fintype.card M : ℝ≥0)⁻¹

omit [DecidableEq M] in
/-- The uniform message probabilities sum to one. -/
theorem uniformMessageProb_sum [Nonempty M] :
    (∑ m : M, uniformMessageProb (M := M) m) = 1 := by
  simp [uniformMessageProb, Finset.sum_const, Fintype.card_ne_zero]

/-- Uniform classical state on the message register. -/
def uniformMessageState [Nonempty M] : State M :=
  Classical.diagonalState (uniformMessageProb (M := M)) (uniformMessageProb_sum (M := M))

@[simp]
theorem uniformMessageState_matrix [Nonempty M] :
    (uniformMessageState (M := M)).matrix =
      Matrix.diagonal fun _ : M => ((Fintype.card M : ℝ≥0)⁻¹ : ℂ) :=
  by
    simp [uniformMessageState, Classical.diagonalState, uniformMessageProb]

/-- The equality-comparator effect on two message registers. -/
def comparatorEffect : CMatrix (Prod M M) :=
  Matrix.diagonal fun p : Prod M M => if p.1 = p.2 then (1 : ℂ) else 0

omit [Fintype M] in
@[simp]
theorem comparatorEffect_apply (p q : Prod M M) :
    comparatorEffect (M := M) p q =
      if p = q then (if p.1 = p.2 then (1 : ℂ) else 0) else 0 := by
  unfold comparatorEffect
  by_cases hpq : p = q
  · subst q
    simp
  · rw [Matrix.diagonal_apply_ne _ hpq]
    simp [hpq]

omit [Fintype M] in
/-- The comparator effect is positive semidefinite. -/
theorem comparatorEffect_posSemidef :
    (comparatorEffect (M := M)).PosSemidef := by
  exact Matrix.PosSemidef.diagonal fun p => by
    by_cases h : p.1 = p.2 <;> simp [h]

omit [Fintype M] in
/-- The complement of the comparator effect is positive semidefinite. -/
theorem comparatorEffect_compl_posSemidef :
    (1 - comparatorEffect (M := M)).PosSemidef := by
  convert Matrix.PosSemidef.diagonal
    (d := fun p : Prod M M => if p.1 = p.2 then (0 : ℂ) else 1)
    (fun p => by by_cases h : p.1 = p.2 <;> simp [h]) using 1
  ext p q
  by_cases hpq : p = q
  · subst q
    by_cases h : p.1 = p.2 <;> simp [comparatorEffect, h]
  · simp [comparatorEffect, hpq]

omit [Fintype M] in
/-- The comparator effect is bounded above by the identity. -/
theorem comparatorEffect_le_one :
    comparatorEffect (M := M) ≤ 1 := by
  simpa [Matrix.le_iff] using comparatorEffect_compl_posSemidef (M := M)

/-- The comparator has type-II trace `1 / |M|` against a uniform product state. -/
theorem comparatorEffect_uniform_prod_trace [Nonempty M] (σ : State M) :
    effectAcceptProbability ((uniformMessageState (M := M)).prod σ)
      (comparatorEffect (M := M)) = ((Fintype.card M : ℝ)⁻¹) := by
  unfold effectAcceptProbability
  rw [State.prod]
  simp only [Matrix.trace]
  calc
    (∑ p : Prod M M,
        (∑ q : Prod M M,
          (Matrix.kronecker (uniformMessageState (M := M)).matrix σ.matrix) p q *
            comparatorEffect (M := M) q p)).re =
        (∑ p : Prod M M,
          (Matrix.kronecker (uniformMessageState (M := M)).matrix σ.matrix) p p *
            comparatorEffect (M := M) p p).re := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro p _
          exact Finset.sum_eq_single_of_mem p (Finset.mem_univ p) (by
            intro q _ hq
            have hzero : comparatorEffect (M := M) q p = 0 := by
              unfold comparatorEffect
              exact Matrix.diagonal_apply_ne _ hq
            rw [hzero, mul_zero])
    _ = (∑ p : Prod M M,
          (if p.1 = p.2 then
            ((Fintype.card M : ℝ≥0)⁻¹ : ℂ) * σ.matrix p.2 p.2
          else 0)).re := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro p _
          by_cases h : p.1 = p.2
          · simp [Matrix.kronecker, Matrix.kroneckerMap_apply,
              uniformMessageState_matrix, comparatorEffect, h]
          · simp [Matrix.kronecker, Matrix.kroneckerMap_apply,
              uniformMessageState_matrix, comparatorEffect, h]
    _ = (∑ m₁ : M, ∑ m₂ : M,
          (if m₁ = m₂ then
            ((Fintype.card M : ℝ≥0)⁻¹ : ℂ) * σ.matrix m₂ m₂
          else 0)).re := by
          congr 1
          rw [Fintype.sum_prod_type]
    _ = (∑ m : M, ((Fintype.card M : ℝ≥0)⁻¹ : ℂ) * σ.matrix m m).re := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro m₁ _
          simp
    _ = ((Fintype.card M : ℝ)⁻¹ * σ.matrix.trace).re := by
          rw [Matrix.trace]
          simp only [Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro m _
          norm_num [NNReal.coe_inv, Complex.ofReal_inv]
    _ = ((Fintype.card M : ℝ)⁻¹) := by
          rw [σ.trace_eq_one]
          simp

namespace HypothesisTestingEffect

/-- Type-II error of a feasible effect is nonnegative. -/
theorem typeIIError_nonneg {ρ σ : State M} {ε : ℝ}
    (Λ : HypothesisTestingEffect ρ ε) :
    0 ≤ Λ.typeIIError σ := by
  unfold typeIIError effectTypeIIError effectAcceptProbability
  exact cMatrix_trace_mul_posSemidef_re_nonneg σ.pos Λ.pos

end HypothesisTestingEffect

namespace State

variable (ρ σ : State M) (ε : ℝ)

/-- Hypothesis-testing beta candidates are bounded below by zero. -/
theorem hypothesisTestingBetaCandidateSet_bddBelow :
    BddBelow (ρ.hypothesisTestingBetaCandidateSet σ ε) := by
  refine ⟨0, ?_⟩
  intro β hβ
  rcases hβ with ⟨Λ, rfl⟩
  exact Λ.typeIIError_nonneg

/-- Any feasible effect gives an upper bound on `β_ε`. -/
theorem hypothesisTestingBeta_le_of_effect
    (Λ : HypothesisTestingEffect ρ ε) :
    ρ.hypothesisTestingBeta σ ε ≤ Λ.typeIIError σ := by
  rw [hypothesisTestingBeta_eq_sInf]
  exact csInf_le (ρ.hypothesisTestingBetaCandidateSet_bddBelow σ ε) ⟨Λ, rfl⟩

/-- Monotonic transport from a positive beta upper bound into real-valued
hypothesis-testing relative entropy.

The positivity hypothesis is essential for the current real-valued encoding of
`D_H`; an extended-real API is needed to cover the source's `β = 0` case
without extra assumptions. -/
theorem neg_log2_le_hypothesisTestingRelativeEntropyFinite_of_beta_le
    {t : ℝ} (hβpos : 0 < ρ.hypothesisTestingBeta σ ε)
    (hle : ρ.hypothesisTestingBeta σ ε ≤ t) :
    -log2 t ≤ ρ.hypothesisTestingRelativeEntropyFinite σ ε := by
  have hlog :
      log2 (ρ.hypothesisTestingBeta σ ε) ≤ log2 t := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hβpos hle) (le_of_lt (Real.log_pos one_lt_two))
  rw [hypothesisTestingRelativeEntropyFinite_eq]
  exact neg_le_neg hlog

end State

omit [DecidableEq M] in
/-- `-log₂(1 / |M|) = log₂ |M|` for a nonempty finite message register. -/
theorem neg_log2_inv_card [Nonempty M] :
    -log2 ((Fintype.card M : ℝ)⁻¹) = log2 (Fintype.card M : ℝ) := by
  unfold log2
  rw [Real.log_inv]
  ring

/-- The comparator is feasible whenever the source comparator success
probability is at least `1 - ε`. -/
def comparatorHypothesisTestingEffect (ω : State (Prod M M)) (ε : ℝ)
    (hComparator : 1 - ε ≤ effectAcceptProbability ω (comparatorEffect (M := M))) :
    HypothesisTestingEffect ω ε where
  effect := comparatorEffect (M := M)
  pos := comparatorEffect_posSemidef (M := M)
  le_one := comparatorEffect_le_one (M := M)
  accept_ge := hComparator

@[simp]
theorem comparatorHypothesisTestingEffect_typeIIError [Nonempty M]
    (ω : State (Prod M M)) (ε : ℝ)
    (hComparator : 1 - ε ≤ effectAcceptProbability ω (comparatorEffect (M := M)))
    (σ : State M) :
    (comparatorHypothesisTestingEffect (M := M) ω ε hComparator).typeIIError
        ((uniformMessageState (M := M)).prod σ) =
      ((Fintype.card M : ℝ)⁻¹) := by
  unfold comparatorHypothesisTestingEffect HypothesisTestingEffect.typeIIError
    effectTypeIIError
  exact comparatorEffect_uniform_prod_trace (M := M) σ

/-- Comparator-test lower bound for optimized hypothesis-testing mutual
information, under the positive-beta side condition required by the current
real-valued `D_H` API.

This is the source comparator argument except for the `β = 0` branch, which
mathematically corresponds to an infinite hypothesis-testing relative entropy;
the extended-real theorem below records that convention without the positivity
side condition. -/
theorem comparator_hypothesisTestingMutualInformationFinite_lower_bound_of_beta_pos
    [Nonempty M] (ω : State (Prod M M)) (ε : ℝ)
    (hMarginalUniform : ω.marginalA = uniformMessageState (M := M))
    (hComparator : 1 - ε ≤ effectAcceptProbability ω (comparatorEffect (M := M)))
    (hBetaPos : ∀ σ : State M,
      0 < ω.hypothesisTestingBeta (ω.marginalA.prod σ) ε) :
    log2 (Fintype.card M : ℝ) ≤
      ω.hypothesisTestingMutualInformationFinite ε := by
  rw [State.hypothesisTestingMutualInformationFinite_eq_sInf]
  refine le_csInf ?hne ?hlower
  · refine ⟨ω.hypothesisTestingRelativeEntropyFinite
      (ω.marginalA.prod (uniformMessageState (M := M))) ε, ?_⟩
    exact ⟨uniformMessageState (M := M), rfl⟩
  · intro value hvalue
    rcases hvalue with ⟨σ, rfl⟩
    let Λ := comparatorHypothesisTestingEffect (M := M) ω ε hComparator
    have htype :
        Λ.typeIIError (ω.marginalA.prod σ) = ((Fintype.card M : ℝ)⁻¹) := by
      subst Λ
      rw [hMarginalUniform]
      exact comparatorHypothesisTestingEffect_typeIIError (M := M) ω ε hComparator σ
    have hβle :
        ω.hypothesisTestingBeta (ω.marginalA.prod σ) ε ≤
          ((Fintype.card M : ℝ)⁻¹) := by
      have hle := ω.hypothesisTestingBeta_le_of_effect (ω.marginalA.prod σ) ε Λ
      rw [htype] at hle
      exact hle
    have hrel :
        -log2 ((Fintype.card M : ℝ)⁻¹) ≤
          ω.hypothesisTestingRelativeEntropyFinite (ω.marginalA.prod σ) ε :=
      ω.neg_log2_le_hypothesisTestingRelativeEntropyFinite_of_beta_le
        (ω.marginalA.prod σ) ε (hBetaPos σ) hβle
    simpa [neg_log2_inv_card (M := M)] using hrel

/-- Extended-real comparator-test lower bound for hypothesis-testing mutual
information, with no full-rank or positive-beta side condition.

This is the source-shaped comparator lemma needed for the one-shot
entanglement-assisted meta-converse.  The `β = 0` case is handled by the
extended-real convention `D_H = ⊤`. -/
theorem comparator_hypothesisTestingMutualInformation_lower_bound
    [Nonempty M] (ω : State (Prod M M)) (ε : ℝ)
    (hMarginalUniform : ω.marginalA = uniformMessageState (M := M))
    (hComparator : 1 - ε ≤ effectAcceptProbability ω (comparatorEffect (M := M))) :
    (log2 (Fintype.card M : ℝ) : EReal) ≤
      ω.hypothesisTestingMutualInformation ε := by
  rw [State.hypothesisTestingMutualInformation_eq_sInf]
  refine le_csInf ?hne ?hlower
  · refine ⟨ω.hypothesisTestingRelativeEntropy
      (ω.marginalA.prod (uniformMessageState (M := M))) ε, ?_⟩
    exact ⟨uniformMessageState (M := M), rfl⟩
  · intro value hvalue
    rcases hvalue with ⟨σ, rfl⟩
    let Λ := comparatorHypothesisTestingEffect (M := M) ω ε hComparator
    have htype :
        Λ.typeIIError (ω.marginalA.prod σ) = ((Fintype.card M : ℝ)⁻¹) := by
      subst Λ
      rw [hMarginalUniform]
      exact comparatorHypothesisTestingEffect_typeIIError (M := M) ω ε hComparator σ
    have hβle :
        ω.hypothesisTestingBeta (ω.marginalA.prod σ) ε ≤
          ((Fintype.card M : ℝ)⁻¹) := by
      have hle := ω.hypothesisTestingBeta_le_of_effect (ω.marginalA.prod σ) ε Λ
      rw [htype] at hle
      exact hle
    by_cases hβzero :
        ω.hypothesisTestingBeta (ω.marginalA.prod σ) ε = 0
    · simp [State.hypothesisTestingRelativeEntropy, hβzero]
    · have hβnonneg :
          0 ≤ ω.hypothesisTestingBeta (ω.marginalA.prod σ) ε := by
        rw [State.hypothesisTestingBeta_eq_sInf]
        refine le_csInf ?hneβ ?hlowerβ
        · exact ⟨Λ.typeIIError (ω.marginalA.prod σ), ⟨Λ, rfl⟩⟩
        · intro β hβ
          rcases hβ with ⟨Λ', rfl⟩
          exact Λ'.typeIIError_nonneg
      have hβpos : 0 < ω.hypothesisTestingBeta (ω.marginalA.prod σ) ε :=
        lt_of_le_of_ne' hβnonneg hβzero
      have hrel :
          -log2 ((Fintype.card M : ℝ)⁻¹) ≤
            ω.hypothesisTestingRelativeEntropyFinite (ω.marginalA.prod σ) ε :=
        ω.neg_log2_le_hypothesisTestingRelativeEntropyFinite_of_beta_le
          (ω.marginalA.prod σ) ε hβpos hβle
      have hrel' :
          log2 (Fintype.card M : ℝ) ≤
            ω.hypothesisTestingRelativeEntropyFinite (ω.marginalA.prod σ) ε := by
        simpa [neg_log2_inv_card (M := M)] using hrel
      have hrelE :
          (log2 (Fintype.card M : ℝ) : EReal) ≤
            (ω.hypothesisTestingRelativeEntropyFinite
              (ω.marginalA.prod σ) ε : EReal) := by
        exact_mod_cast hrel'
      simpa [State.hypothesisTestingRelativeEntropy, hβzero] using hrelE

end

end QIT
