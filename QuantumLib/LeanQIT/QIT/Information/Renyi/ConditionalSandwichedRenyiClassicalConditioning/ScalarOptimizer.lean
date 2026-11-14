/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

import Mathlib.Algebra.Order.CompleteField
public import QIT.Information.Renyi.ConditionalRenyiClassical
public import QIT.Information.Renyi.SandwichedRenyiOptimizedUSC
public import QIT.Information.Renyi.ConditionalSandwichedRenyiDuality
public import QIT.Information.Renyi.ConditionalSandwichedRenyiAdditivity
public import QIT.Measurements.Projective
public import QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.BlockAlgebra
public import QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.LowAlphaQDecomposition

/-!
# scalar optimizer / component bridge

Responsibility layer of the sandwiched conditional Renyi classical-conditioning
source route.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Pointwise
open Matrix

namespace QIT

universe u v w

noncomputable section

variable {A : Type u} {B : Type v} {Y : Type w}
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable [Fintype Y] [DecidableEq Y]

namespace State

/-! ### Finite-support logarithmic form and scalar optimization -/

/-- The finite branch entropy associated with a positive sandwiched `Q` value. -/
def sandwichedFiniteBranchEntropy (Q : Y → ℝ) (α : ℝ) (y : Y) : ℝ :=
  (1 / (α - 1)) * log2 (Q y)

/- The source uses this identity after the block `Q` decomposition.  The
  hypothesis `hQ` is deliberately pointwise: it excludes only the
  undefined logarithm branch, while a zero classical weight still contributes
  exactly zero to the finite sum. -/
omit [DecidableEq Y] in
theorem sandwichedFiniteSupport_log_formula
    (p Q : Y → ℝ) (α : ℝ) (hα_ne_one : α ≠ 1)
    (_hp : ∀ y, 0 ≤ p y) (hQ : ∀ y, 0 < Q y) :
    (1 / (α - 1)) * log2 (∑ y, p y * Q y) =
      (1 / (α - 1)) * log2
        (∑ y, p y * Real.rpow 2
          ((α - 1) * sandwichedFiniteBranchEntropy Q α y)) := by
  apply congrArg (fun x : ℝ => (1 / (α - 1)) * log2 x)
  apply Finset.sum_congr rfl
  intro y hy
  unfold sandwichedFiniteBranchEntropy
  have hlog :
      (α - 1) * ((1 / (α - 1)) * log2 (Q y)) = log2 (Q y) := by
    field_simp [hα_ne_one]
  rw [hlog, QIT.rpow_two_log2_pos (hQ y)]

omit [DecidableEq Y] in
/-- The source finite-support logarithmic identity, rewritten in terms of the
normalized component conditional entropies. -/
theorem sandwichedDownComponentLogFormula
    (E : Ensemble Y (A × B)) (α : ℝ) (hα_ne_one : α ≠ 1) :
    (1 / (1 - α)) * log2
        (∑ y, (E.probs y : ℝ) *
          sandwichedRenyiQ (E.states y).matrix
            (identityTensorStateMatrix (a := A) (E.states y).marginalB)
            (E.states y).pos
            (identityTensorStateMatrix_posSemidef_of_state
              (a := A) (E.states y).marginalB) α) =
      (1 / (1 - α)) * log2
        (∑ y, (E.probs y : ℝ) * Real.rpow 2
          ((1 - α) * sandwichedDownComponentEntropy E y α)) := by
  let Q : Y → ℝ := fun y =>
    sandwichedRenyiQ (E.states y).matrix
      (identityTensorStateMatrix (a := A) (E.states y).marginalB)
      (E.states y).pos
      (identityTensorStateMatrix_posSemidef_of_state
        (a := A) (E.states y).marginalB) α
  have hp : ∀ y, 0 ≤ (E.probs y : ℝ) := by
    intro y
    exact_mod_cast NNReal.coe_nonneg (E.probs y)
  have hQ : ∀ y, 0 < Q y := by
    intro y
    exact sandwichedDownComponentQ_pos E y α
  have hsource := sandwichedFiniteSupport_log_formula
    (p := fun y => (E.probs y : ℝ)) (Q := Q)
    α hα_ne_one hp hQ
  have hexp : ∀ y,
      (α - 1) * sandwichedFiniteBranchEntropy Q α y =
        (1 - α) * sandwichedDownComponentEntropy E y α := by
    intro y
    unfold sandwichedFiniteBranchEntropy sandwichedDownComponentEntropy Q
    field_simp [hα_ne_one]
  have hsum :
      (∑ y, (E.probs y : ℝ) * Real.rpow 2
        ((α - 1) * sandwichedFiniteBranchEntropy Q α y)) =
      ∑ y, (E.probs y : ℝ) * Real.rpow 2
        ((1 - α) * sandwichedDownComponentEntropy E y α) := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [hexp y]
  have hneg := congrArg (fun x : ℝ => -x) hsource
  have hcoeff : -(1 / (α - 1)) = 1 / (1 - α) := by
    field_simp [hα_ne_one]
    ring
  change (1 / (1 - α)) * log2 (∑ y, (E.probs y : ℝ) * Q y) = _
  rw [hsum] at hneg
  calc
    (1 / (1 - α)) * log2 (∑ y, (E.probs y : ℝ) * Q y) =
        -(1 / (α - 1) * log2 (∑ y, (E.probs y : ℝ) * Q y)) := by
      rw [← neg_mul, hcoeff]
    _ = -(1 / (α - 1) * log2
        (∑ y, (E.probs y : ℝ) * Real.rpow 2
          ((1 - α) * sandwichedDownComponentEntropy E y α))) := hneg
    _ = (1 / (1 - α)) * log2
        (∑ y, (E.probs y : ℝ) * Real.rpow 2
          ((1 - α) * sandwichedDownComponentEntropy E y α)) := by
      rw [← neg_mul, hcoeff]

/-! The optimizer below is the scalar part of the source up-arrow proof. -/

/-! The finite-support optimizer is an instance of the following abstract
finite Minkowski-sum calculation. -/

private theorem real_csSup_add {s t : Set ℝ}
    (hs₀ : s.Nonempty) (hs₁ : BddAbove s)
    (ht₀ : t.Nonempty) (ht₁ : BddAbove t) :
    sSup (s + t) = sSup s + sSup t := by
  have hs₁' := hs₁
  have ht₁' := ht₁
  rcases hs₁' with ⟨u, hu⟩
  rcases ht₁' with ⟨v, hv⟩
  have hst₀ : (s + t).Nonempty := Set.Nonempty.image2 hs₀ ht₀
  have hst₁ : BddAbove (s + t) := by
    refine ⟨u + v, ?_⟩
    intro z hz
    rw [Set.mem_add] at hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    exact add_le_add (hu hx) (hv hy)
  apply le_antisymm
  · apply csSup_le hst₀
    intro z hz
    rw [Set.mem_add] at hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    exact add_le_add (le_csSup hs₁ hx) (le_csSup ht₁ hy)
  · have ht_bound : ∀ x ∈ s, sSup t ≤ sSup (s + t) - x := by
      intro x hx
      apply csSup_le ht₀
      intro y hy
      have hxy : x + y ≤ sSup (s + t) := by
        exact le_csSup hst₁ (Set.add_mem_add hx hy)
      linarith
    have hs_bound : sSup s ≤ sSup (s + t) - sSup t := by
      apply csSup_le hs₀
      intro x hx
      linarith [ht_bound x hx]
    linarith

def finiteSelectionSumSet {ι : Type*} (s : Finset ι) (S : ι → Set ℝ) : Set ℝ :=
  {x | ∃ f : ι → ℝ, (∀ i ∈ s, f i ∈ S i) ∧ x = ∑ i ∈ s, f i}

theorem finiteSelectionSumSet_insert {ι : Type*} [DecidableEq ι]
    (a : ι) (s : Finset ι) (S : ι → Set ℝ) (ha : a ∉ s) :
    finiteSelectionSumSet (insert a s) S =
      S a + finiteSelectionSumSet s S := by
  ext x
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [Finset.sum_insert ha]
    rw [Set.mem_add]
    refine ⟨f a, hf a (Finset.mem_insert_self a s), ∑ i ∈ s, f i, ?_, rfl⟩
    exact ⟨f, fun i hi => hf i (Finset.mem_insert_of_mem hi), rfl⟩
  · rw [Set.mem_add]
    rintro ⟨x, hx, y, ⟨f, hf, rfl⟩, rfl⟩
    let g : ι → ℝ := fun i => if i = a then x else f i
    refine ⟨g, ?_, ?_⟩
    · intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · simpa [g] using hx
      · have hia : i ≠ a := by
          intro hia
          exact ha (hia ▸ hi)
        simpa [g, hia] using hf i hi
    · rw [Finset.sum_insert ha]
      have hsum : (∑ i ∈ s, g i) = ∑ i ∈ s, f i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hia : i ≠ a := by
          intro hia
          exact ha (hia ▸ hi)
        simp [g, hia]
      simp [g, hsum]

theorem finiteSelectionSumSet_nonempty_bddAbove {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (S : ι → Set ℝ)
    (hne : ∀ i ∈ s, (S i).Nonempty)
    (hbd : ∀ i ∈ s, BddAbove (S i)) :
    (finiteSelectionSumSet s S).Nonempty ∧
      BddAbove (finiteSelectionSumSet s S) := by
  induction s using Finset.induction_on with
  | empty =>
      simp [finiteSelectionSumSet]
  | @insert a s ha ih =>
      rw [finiteSelectionSumSet_insert a s S ha]
      have hs := ih
        (fun i hi => hne i (Finset.mem_insert_of_mem hi))
        (fun i hi => hbd i (Finset.mem_insert_of_mem hi))
      constructor
      · exact Set.Nonempty.image2 (hne a (Finset.mem_insert_self a s)) hs.1
      · rcases hbd a (Finset.mem_insert_self a s) with ⟨u, hu⟩
        rcases hs.2 with ⟨v, hv⟩
        refine ⟨u + v, ?_⟩
        intro z hz
        rw [Set.mem_add] at hz
        rcases hz with ⟨x, hx, y, hy, rfl⟩
        exact add_le_add (hu hx) (hv hy)

theorem finiteSelectionSumSet_sSup {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (S : ι → Set ℝ)
    (hne : ∀ i ∈ s, (S i).Nonempty)
    (hbd : ∀ i ∈ s, BddAbove (S i)) :
    sSup (finiteSelectionSumSet s S) = ∑ i ∈ s, sSup (S i) := by
  induction s using Finset.induction_on with
  | empty =>
      simp [finiteSelectionSumSet]
  | @insert a s ha ih =>
      rw [finiteSelectionSumSet_insert a s S ha]
      have hs := finiteSelectionSumSet_nonempty_bddAbove s S
        (fun i hi => hne i (Finset.mem_insert_of_mem hi))
        (fun i hi => hbd i (Finset.mem_insert_of_mem hi))
      rw [real_csSup_add (hne a (Finset.mem_insert_self a s))
        (hbd a (Finset.mem_insert_self a s)) hs.1 hs.2]
      rw [ih (fun i hi => hne i (Finset.mem_insert_of_mem hi))
        (fun i hi => hbd i (Finset.mem_insert_of_mem hi))]
      rw [Finset.sum_insert ha]

/-- Unnormalised scalar weights in Tomamichel's upward optimization. -/
def sandwichedScalarOptimizerWeight (p h α : ℝ) : ℝ :=
  p * Real.rpow 2 (((1 - α) / α) * h)

def sandwichedScalarPower (r q : Y → ℝ) (α : ℝ) : ℝ :=
  ∑ y, (r y) ^ α * (q y) ^ (1 - α)

theorem sandwichedUpFixedReferenceBranchFormulaReal_eq_scalarPower
    (E : Ensemble Y (A × B)) (F : Ensemble Y B)
    (hF : (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedScalarPower
        (fun y => (E.probs y : ℝ) *
          Real.rpow 2 (((1 - α) / α) *
            sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one))
        (fun y => (F.probs y : ℝ)) α =
      ∑ y, (E.probs y : ℝ) ^ α * (F.probs y : ℝ) ^ (1 - α) *
        Real.rpow 2 ((1 - α) *
          sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one) := by
  classical
  unfold sandwichedScalarPower
  apply Finset.sum_congr rfl
  intro y hy
  have hp : 0 ≤ (E.probs y : ℝ) := by
    exact NNReal.coe_nonneg _
  have hq : 0 ≤ (F.probs y : ℝ) := by
    exact NNReal.coe_nonneg _
  have hbase : 0 ≤ Real.rpow 2 (((1 - α) / α) *
      sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one) :=
    Real.rpow_nonneg (by norm_num) _
  change ((E.probs y : ℝ) *
      Real.rpow 2 (((1 - α) / α) *
        sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one)) ^ α *
      (F.probs y : ℝ) ^ (1 - α) = _
  have hmul := Real.mul_rpow
    (x := (E.probs y : ℝ))
    (y := Real.rpow 2 (((1 - α) / α) *
      sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one))
    (z := α) hp hbase
  rw [hmul]
  have hpow :
      Real.rpow 2 (((1 - α) / α) *
        sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one) ^ α =
        Real.rpow 2 ((((1 - α) / α) *
          sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one) * α) := by
    exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
  rw [hpow]
  have hexp : ((1 - α) / α) *
      sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one * α =
      (1 - α) * sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one := by
    field_simp [hα_pos.ne']
  rw [hexp]
  ring

theorem sandwichedUpFixedReferenceBranchFormulaReal_eq_log_scalarPower
    (E : Ensemble Y (A × B)) (F : Ensemble Y B)
    (hF : (F.cqState.reindex (Equiv.prodComm Y B)).matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedUpFixedReferenceBranchFormulaReal E F α hF hα_pos hα_ne_one =
      (1 / (1 - α)) * log2
        (sandwichedScalarPower
          (fun y => (E.probs y : ℝ) *
            Real.rpow 2 (((1 - α) / α) *
              sandwichedFixedReferenceBranchValue E F y α hF hα_pos hα_ne_one))
          (fun y => (F.probs y : ℝ)) α) := by
  unfold sandwichedUpFixedReferenceBranchFormulaReal
  rw [sandwichedUpFixedReferenceBranchFormulaReal_eq_scalarPower
    E F hF α hα_pos hα_ne_one]

omit [DecidableEq Y] in
theorem sandwichedScalarPower_optimizer
    (r : Y → ℝ) (α : ℝ) (hr : ∀ y, 0 < r y)
    (_hα_pos : 0 < α) [Nonempty Y] :
    sandwichedScalarPower r
        (fun y => r y / ∑ z, r z) α =
      (∑ z, r z) ^ α := by
  classical
  let Z : ℝ := ∑ z, r z
  have hZ : 0 < Z := by
    dsimp [Z]
    apply Finset.sum_pos'
    · intro y hy
      exact le_of_lt (hr y)
    · let y : Y := Classical.choice (inferInstance : Nonempty Y)
      exact ⟨y, Finset.mem_univ y, hr y⟩
  unfold sandwichedScalarPower
  change ∑ y, r y ^ α * (r y / Z) ^ (1 - α) = Z ^ α
  calc
    ∑ y, r y ^ α * (r y / Z) ^ (1 - α) =
        ∑ y, r y / Z ^ (1 - α) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Real.div_rpow (le_of_lt (hr y)) (le_of_lt hZ)]
      have hpow : r y ^ α * r y ^ (1 - α) = r y := by
        rw [← Real.rpow_add (hr y)]
        have : α + (1 - α) = 1 := by ring
        rw [this, Real.rpow_one]
      field_simp [hZ.ne']
      rw [hpow]
    _ = Z / Z ^ (1 - α) := by rw [← Finset.sum_div]
    _ = Z ^ α := by
      have hdiv : Z / Z ^ (1 - α) = Z ^ (1 : ℝ) / Z ^ (1 - α) := by
        rw [Real.rpow_one]
      rw [hdiv, ← Real.rpow_sub hZ]
      congr 1
      ring

/-! The same optimizer remains exact when some weights vanish.  This is the
source convention needed for a classical register with zero-probability
branches: the normalized optimizer is zero on precisely those branches, and
no division by that probability is used. -/

omit [DecidableEq Y] in
theorem sandwichedScalarPower_optimizer_of_nonneg
    (r : Y → ℝ) (α : ℝ) (hr : ∀ y, 0 ≤ r y)
    (hR : 0 < ∑ y, r y) (hα_pos : 0 < α) :
    sandwichedScalarPower r
        (fun y => r y / ∑ z, r z) α =
      (∑ z, r z) ^ α := by
  classical
  let Z : ℝ := ∑ z, r z
  have hZ : 0 < Z := by simpa [Z] using hR
  unfold sandwichedScalarPower
  change ∑ y, r y ^ α * (r y / Z) ^ (1 - α) = Z ^ α
  calc
    ∑ y, r y ^ α * (r y / Z) ^ (1 - α) =
        ∑ y, r y / Z ^ (1 - α) := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hry : r y = 0
      · simp [hry, hα_pos.ne']
      · have hry_pos : 0 < r y := lt_of_le_of_ne (hr y) (Ne.symm hry)
        rw [Real.div_rpow hry_pos.le hZ.le]
        have hpow : r y ^ α * r y ^ (1 - α) = r y := by
          rw [← Real.rpow_add hry_pos]
          rw [show α + (1 - α) = 1 by ring, Real.rpow_one]
        field_simp [hZ.ne']
        rw [hpow]
    _ = Z / Z ^ (1 - α) := by rw [← Finset.sum_div]
    _ = Z ^ α := by
      have hdiv : Z / Z ^ (1 - α) = Z ^ (1 : ℝ) / Z ^ (1 - α) := by
        rw [Real.rpow_one]
      rw [hdiv, ← Real.rpow_sub hZ]
      congr 1
      ring

/-! The two inequalities below are the finite Holder/Jensen step in the
source optimizer.  They are stated with ordinary real `rpow`; consequently
the zero-probability branches are handled explicitly rather than by dividing
by a probability. -/

omit [DecidableEq Y] in
theorem sandwichedScalarPower_le_sum_rpow_of_nonneg
    (r q : Y → ℝ) (α : ℝ)
    (hr : ∀ y, 0 ≤ r y) (hq_pos : ∀ y, 0 < q y)
    (hq_sum : ∑ y, q y = 1)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    sandwichedScalarPower r q α ≤ (∑ y, r y) ^ α := by
  classical
  have hq : ∀ y, 0 ≤ q y := fun y => le_of_lt (hq_pos y)
  have hweighted_nonneg : ∀ y, 0 ≤ q y * (r y / q y) := by
    intro y
    exact mul_nonneg (hq y) (div_nonneg (hr y) (hq y))
  have hvalue_nonneg : ∀ y, 0 ≤ r y / q y := by
    intro y
    exact div_nonneg (hr y) (hq y)
  have hjensen :
      ∑ y, q y * (r y / q y) ^ α ≤
        (∑ y, q y * (r y / q y)) ^ α :=
    real_sum_weighted_rpow_le_rpow_weighted_sum
      (le_of_lt hα_pos) (le_of_lt hα_lt_one) hq hq_sum hvalue_nonneg
  have hterm :
      sandwichedScalarPower r q α =
        ∑ y, q y * (r y / q y) ^ α := by
    unfold sandwichedScalarPower
    apply Finset.sum_congr rfl
    intro y hy
    rw [Real.div_rpow (hr y) (hq y)]
    have hqpow : q y ^ α ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (hq_pos y) α)
    field_simp [ne_of_gt (hq_pos y), hqpow]
    calc
      r y ^ α * q y ^ (1 - α) * q y ^ α =
          r y ^ α * (q y ^ (1 - α) * q y ^ α) := by ring
      _ = r y ^ α * q y := by
        rw [← Real.rpow_add (hq_pos y)]
        rw [show (1 - α) + α = 1 by ring, Real.rpow_one]
  have hsum_le :
      (∑ y, q y * (r y / q y)) ≤ ∑ y, r y := by
    apply Finset.sum_le_sum
    intro y hy
    field_simp [ne_of_gt (hq_pos y)]
    exact le_rfl
  calc
    sandwichedScalarPower r q α =
        ∑ y, q y * (r y / q y) ^ α := hterm
    _ ≤ (∑ y, q y * (r y / q y)) ^ α := hjensen
    _ ≤ (∑ y, r y) ^ α := by
      exact Real.rpow_le_rpow
        (Finset.sum_nonneg fun y _ => hweighted_nonneg y)
        hsum_le (le_of_lt hα_pos)

omit [DecidableEq Y] in
theorem sum_rpow_le_sandwichedScalarPower_of_nonneg
    (r q : Y → ℝ) (α : ℝ)
    (hr : ∀ y, 0 ≤ r y) (hq : ∀ y, 0 ≤ q y)
    (hq_sum : ∑ y, q y = 1)
    (hzero : ∀ y, q y = 0 → r y = 0)
    (hα_gt_one : 1 < α) :
    (∑ y, r y) ^ α ≤ sandwichedScalarPower r q α := by
  classical
  have hweighted_nonneg : ∀ y, 0 ≤ q y * (r y / q y) := by
    intro y
    exact mul_nonneg (hq y) (div_nonneg (hr y) (hq y))
  have hvalue_nonneg : ∀ y, 0 ≤ r y / q y := by
    intro y
    exact div_nonneg (hr y) (hq y)
  have hsum_eq :
      (∑ y, q y * (r y / q y)) = ∑ y, r y := by
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hqy : q y = 0
    · simp [hqy, hzero y hqy]
    · have hqpos : 0 < q y := lt_of_le_of_ne (hq y) (Ne.symm hqy)
      field_simp [ne_of_gt hqpos]
  have hjensen :
      (∑ y, q y * (r y / q y)) ^ α ≤
        ∑ y, q y * (r y / q y) ^ α :=
    real_rpow_weighted_sum_le_sum_weighted_rpow
      (le_of_lt hα_gt_one) hq hq_sum hvalue_nonneg
  have hterm :
      sandwichedScalarPower r q α =
        ∑ y, q y * (r y / q y) ^ α := by
    unfold sandwichedScalarPower
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hqy : q y = 0
    · have hone : 1 - α ≠ 0 := by linarith
      simp [hqy, hone]
    · have hqpos : 0 < q y := lt_of_le_of_ne (hq y) (Ne.symm hqy)
      rw [Real.div_rpow (hr y) (hq y)]
      have hqpow : q y ^ α ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos hqpos α)
      field_simp [ne_of_gt hqpos, hqpow]
      calc
        r y ^ α * q y ^ (1 - α) * q y ^ α =
            r y ^ α * (q y ^ (1 - α) * q y ^ α) := by ring
        _ = r y ^ α * q y := by
          rw [← Real.rpow_add hqpos]
          rw [show (1 - α) + α = 1 by ring, Real.rpow_one]
  calc
    (∑ y, r y) ^ α =
        (∑ y, q y * (r y / q y)) ^ α := by rw [hsum_eq]
    _ ≤ ∑ y, q y * (r y / q y) ^ α := hjensen
    _ = sandwichedScalarPower r q α := hterm.symm

/-- Normalization of the source scalar optimizer. -/
def sandwichedScalarOptimizerDistribution (p h : Y → ℝ) (α : ℝ) (y : Y) : ℝ :=
  sandwichedScalarOptimizerWeight (p y) (h y) α /
    ∑ z, sandwichedScalarOptimizerWeight (p z) (h z) α

omit [DecidableEq Y] in
theorem sandwichedScalarPower_optimizer_weighted
    (p h : Y → ℝ) (α : ℝ) (hp : ∀ y, 0 < p y)
    (hα_pos : 0 < α) [Nonempty Y] :
    sandwichedScalarPower
        (fun y => sandwichedScalarOptimizerWeight (p y) (h y) α)
        (sandwichedScalarOptimizerDistribution p h α) α =
      (∑ y, sandwichedScalarOptimizerWeight (p y) (h y) α) ^ α := by
  unfold sandwichedScalarOptimizerDistribution
  exact sandwichedScalarPower_optimizer
    (fun y => sandwichedScalarOptimizerWeight (p y) (h y) α)
    α (by
      intro y
      unfold sandwichedScalarOptimizerWeight
      exact mul_pos (hp y) (Real.rpow_pos_of_pos (by norm_num) _)) hα_pos

omit [DecidableEq Y] in
theorem sandwichedScalarOptimizerDistribution_sum_one
    (p h : Y → ℝ) (α : ℝ)
    (hden : ∑ z, sandwichedScalarOptimizerWeight (p z) (h z) α ≠ 0) :
    ∑ y, sandwichedScalarOptimizerDistribution p h α y = 1 := by
  unfold sandwichedScalarOptimizerDistribution
  rw [← Finset.sum_div]
  exact div_self hden

omit [DecidableEq Y] in
theorem sandwichedScalarOptimizerDistribution_nonneg
    (p h : Y → ℝ) (α : ℝ)
    (hp : ∀ y, 0 ≤ p y) :
    ∀ y, 0 ≤ sandwichedScalarOptimizerDistribution p h α y := by
  intro y
  unfold sandwichedScalarOptimizerDistribution sandwichedScalarOptimizerWeight
  have hnum : 0 ≤ p y * Real.rpow 2 (((1 - α) / α) * h y) :=
    mul_nonneg (hp y) (Real.rpow_pos_of_pos (by norm_num) _).le
  have hden : 0 ≤ ∑ z, p z * Real.rpow 2 (((1 - α) / α) * h z) := by
    exact Finset.sum_nonneg fun z hz =>
      mul_nonneg (hp z) (Real.rpow_pos_of_pos (by norm_num) _).le
  exact div_nonneg hnum hden

omit [DecidableEq Y] in
theorem sandwichedScalarOptimizerDistribution_is_probability
    (p h : Y → ℝ) (α : ℝ)
    (hp : ∀ y, 0 ≤ p y)
    (hden : ∑ z, sandwichedScalarOptimizerWeight (p z) (h z) α ≠ 0) :
    (∀ y, 0 ≤ sandwichedScalarOptimizerDistribution p h α y) ∧
      ∑ y, sandwichedScalarOptimizerDistribution p h α y = 1 := by
  exact ⟨sandwichedScalarOptimizerDistribution_nonneg p h α hp,
    sandwichedScalarOptimizerDistribution_sum_one p h α hden⟩

omit [DecidableEq Y] in
theorem sandwichedScalarPower_uniformMix_tendsto
    [Nonempty Y] (r q : Y → ℝ) (α : ℝ) (hα_pos : 0 < α)
    (_hzero : ∀ y, r y = 0 → q y = 0)
    (hq_pos : ∀ y, r y ≠ 0 → 0 < q y) :
    Filter.Tendsto
      (fun δ : ℝ => sandwichedScalarPower r
        (fun y => (1 - δ) * q y + δ / (Fintype.card Y : ℝ)) α)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1))
      (nhds (sandwichedScalarPower r q α)) := by
  classical
  have hcard_pos : 0 < (Fintype.card Y : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty Y)
  have hq_tend : ∀ y, Filter.Tendsto
      (fun δ : ℝ => (1 - δ) * q y + δ / (Fintype.card Y : ℝ))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds (q y)) := by
    intro y
    have hcont : Continuous (fun δ : ℝ =>
        (1 - δ) * q y + δ / (Fintype.card Y : ℝ)) := by fun_prop
    simpa using hcont.continuousAt.mono_left
      (nhdsWithin_le_nhds :
        nhdsWithin (0 : ℝ) (Set.Ioo 0 1) ≤ nhds (0 : ℝ))
  have hterm : ∀ y, Filter.Tendsto
      (fun δ : ℝ => (r y) ^ α *
        ((1 - δ) * q y + δ / (Fintype.card Y : ℝ)) ^ (1 - α))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1))
      (nhds ((r y) ^ α * (q y) ^ (1 - α))) := by
    intro y
    by_cases hry : r y = 0
    · simp [hry, hα_pos.ne']
    · have hq : 0 < q y := hq_pos y hry
      have hp : Filter.Tendsto
          (fun δ : ℝ => ((1 - δ) * q y + δ / (Fintype.card Y : ℝ)) ^ (1 - α))
          (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds (q y ^ (1 - α))) :=
        (Real.continuousAt_rpow_const (q y) (1 - α) (Or.inl hq.ne')).tendsto.comp
          (hq_tend y)
      simpa using hp.const_mul (r y ^ α)
  unfold sandwichedScalarPower
  simpa using tendsto_finsetSum (Finset.univ : Finset Y)
    (fun y _ => hterm y)


end State

end

end QIT
