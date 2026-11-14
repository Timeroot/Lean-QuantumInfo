/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy.ConditionalEntropyConcavity
public import QIT.Information.Entropy.Entropy
public import QIT.Information.Entropy.MutualInformationDPI
public import QIT.States.TraceNorm.PositivePart
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import QIT.Information.Entropy.Log2Lemmas

/-!
# Alicki--Fannes--Winter continuity

This module contains the scalar entropy terms and finite-dimensional
conditional-entropy continuity theorem used by the
Alicki--Fannes--Winter bound.  The public theorem is source-shaped around the
normalized trace distance `1/2 ‖ρ - σ‖₁` and the modulus
`2 ε log₂ |A| + (1 + ε) h₂(ε / (1 + ε))`.
-/

@[expose] public section

namespace QIT

open Filter
open scoped ComplexOrder MatrixOrder NNReal

universe u v

noncomputable section

/-- Binary entropy in bits, with the repository's `0 log 0 = 0` convention. -/
def binaryEntropy (ε : ℝ) : ℝ :=
  -xlog2 ε - xlog2 (1 - ε)

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]
variable {b : Type v} [Fintype b] [DecidableEq b]

private def punitProdEquiv (α : Type v) : α ≃ Prod PUnit.{1} α where
  toFun x := (PUnit.unit, x)
  invFun x := x.2
  left_inv := by intro x; rfl
  right_inv := by rintro ⟨⟨⟩, x⟩; rfl

/-- The von Neumann entropy of a finite-dimensional pure state is zero. -/
theorem pureVector_vonNeumann_eq_zero
    {α : Type v} [Fintype α] [DecidableEq α] (Ψ : PureVector α) :
    Ψ.state.vonNeumann = 0 := by
  let Φ : PureVector (Prod PUnit.{1} α) := Ψ.reindex (punitProdEquiv α)
  have hmargA : Φ.state.marginalA.vonNeumann = 0 :=
    vonNeumann_punit_eq_zero Φ.state.marginalA
  have hmargB : Φ.state.marginalB = Ψ.state := by
    apply State.ext
    ext i j
    simp [Φ, State.marginalB, punitProdEquiv, QIT.partialTraceA]
  have hdual := pureVector_marginalA_vonNeumann_eq_marginalB Φ
  rw [hmargA, hmargB] at hdual
  exact hdual.symm

private def assocLeftEquiv (a : Type u) (b : Type v) (c : Type*) :
    Prod (Prod a b) c ≃ Prod a (Prod b c) where
  toFun x := (x.1.1, (x.1.2, x.2))
  invFun x := ((x.1, x.2.1), x.2.2)
  left_inv := by rintro ⟨⟨x, y⟩, z⟩; rfl
  right_inv := by rintro ⟨x, y, z⟩; rfl

private theorem pureVector_marginalBC_vonNeumann_eq_marginalA
    {c : Type*} [Fintype c] [DecidableEq c]
    (Ψ : PureVector (Prod (Prod a b) c)) :
    Ψ.state.marginalBC.vonNeumann = Ψ.state.marginalA.marginalA.vonNeumann := by
  let Φ : PureVector (Prod a (Prod b c)) := Ψ.reindex (assocLeftEquiv a b c)
  have hA : Φ.state.marginalA = Ψ.state.marginalA.marginalA := by
    apply State.ext
    ext i j
    simp [Φ, assocLeftEquiv, PureVector.reindex_state, State.reindex,
      State.marginalA, QIT.partialTraceB, Fintype.sum_prod_type]
  have hB : Φ.state.marginalB = Ψ.state.marginalBC := by
    apply State.ext
    ext i j
    simp [Φ, assocLeftEquiv, PureVector.reindex_state, State.reindex,
      State.marginalB, State.marginalBC, QIT.partialTraceA]
  have hdual := pureVector_marginalA_vonNeumann_eq_marginalB Φ
  rw [hA, hB] at hdual
  exact hdual.symm

/-- Conditional von Neumann entropy duality for complementary marginals of a
finite-dimensional pure tripartite state.

This is the von Neumann entropy duality used in TCR 2008, Theorem `thm:qaep`,
after the smooth min/max duality substitution. -/
theorem PureVector.conditionalEntropy_marginalAB_eq_neg_marginalAC
    {c : Type*} [Fintype c] [DecidableEq c]
    (Ψ : PureVector (Prod (Prod a b) c)) :
    Ψ.state.marginalAB.conditionalEntropy =
      -Ψ.state.marginalAC.conditionalEntropy := by
  classical
  let Ω : PureVector (Prod (Prod a c) b) :=
    Ψ.reindex
      { toFun := fun x => ((x.1.1, x.2), x.1.2)
        invFun := fun x => ((x.1.1, x.2), x.1.2)
        left_inv := by rintro ⟨⟨x, y⟩, z⟩; rfl
        right_inv := by rintro ⟨⟨x, z⟩, y⟩; rfl }
  have hAB_C : Ψ.state.marginalAB.vonNeumann = Ψ.state.marginalB.vonNeumann := by
    rw [State.marginalAB_eq_marginalA]
    exact pureVector_marginalA_vonNeumann_eq_marginalB Ψ
  have hAC_B : Ψ.state.marginalAC.vonNeumann = Ψ.state.marginalBOfABC.vonNeumann := by
    have hΩA : Ω.state.marginalA = Ψ.state.marginalAC := by
      apply State.ext
      ext i j
      simp [Ω, State.marginalAC_matrix, State.marginalA, State.reindex,
        PureVector.reindex_state, QIT.partialTraceB,
        PureVector.state_matrix, rankOneMatrix_apply]
    have hΩB : Ω.state.marginalB = Ψ.state.marginalBOfABC := by
      apply State.ext
      ext i j
      simp [Ω, State.marginalBOfABC, State.marginalB, State.reindex,
        PureVector.reindex_state, QIT.partialTraceA, QIT.partialTraceB,
        PureVector.state_matrix, rankOneMatrix_apply, Fintype.sum_prod_type]
    have hdual := pureVector_marginalA_vonNeumann_eq_marginalB Ω
    rwa [hΩA, hΩB] at hdual
  have hABmB : Ψ.state.marginalAB.marginalB = Ψ.state.marginalBOfABC := by
    rw [State.marginalBOfABC_eq, State.marginalAB_eq_marginalA]
  have hACmB : Ψ.state.marginalAC.marginalB = Ψ.state.marginalB := by
    apply State.ext
    ext i j
    simp [State.marginalAC_matrix, State.marginalB, QIT.partialTraceA,
      Fintype.sum_prod_type]
  rw [State.conditionalEntropy_eq, State.conditionalEntropy_eq]
  rw [hAB_C, hAC_B, hABmB, hACmB]
  ring

/-- Araki--Lieb half-inequality in conditional-entropy form:
`H(A|B)_τ ≥ -H(A)_τ`, equivalently `H(AB)_τ ≥ H(B)_τ - H(A)_τ`. -/
theorem conditionalEntropy_neg_marginalA_le (τ : State (Prod a b)) :
    -τ.marginalA.vonNeumann ≤ τ.conditionalEntropy := by
  let Ψ₀ : PureVector (Prod (Prod a b) (Prod a b)) :=
    τ.canonicalPurification.reindex (Equiv.prodComm (Prod a b) (Prod a b))
  have hAB : Ψ₀.state.marginalA = τ := by
    apply State.ext
    simpa [Ψ₀, State.marginalA, State.marginalB, PureVector.reindex_state,
      State.reindex, QIT.partialTraceA, QIT.partialTraceB,
      PureVector.state_matrix, rankOneMatrix_apply] using
      τ.canonicalPurification_purifies
  have hB : Ψ₀.state.marginalBOfABC = τ.marginalB := by
    rw [State.marginalBOfABC_eq, State.marginalAB_eq_marginalA, hAB]
  have hA : Ψ₀.state.marginalA.marginalA = τ.marginalA := by
    rw [hAB]
  have hwhole : Ψ₀.state.vonNeumann = 0 := pureVector_vonNeumann_eq_zero Ψ₀
  have hBC :
      Ψ₀.state.marginalBC.vonNeumann = τ.marginalA.vonNeumann := by
    rw [pureVector_marginalBC_vonNeumann_eq_marginalA Ψ₀, hA]
  have hssa := State.condMutualInfo_nonneg (ρ := Ψ₀.state)
  rw [State.condMutualInfo_eq, State.marginalAB_eq_marginalA, hAB, hB, hBC, hwhole] at hssa
  rw [conditionalEntropy_eq]
  linarith

theorem mutualInformation_nonneg (ρ : State (Prod a b)) :
    0 ≤ QIT.mutualInformation ρ := by
  have hDPI :=
    QIT.mutualInformation_dataProcessing_local_channels_ge ρ
      (terminalMeasureChannel a) (terminalMeasureChannel b)
  have hzero :
      QIT.mutualInformation
          (((terminalMeasureChannel a).prod (terminalMeasureChannel b)).applyState ρ) = 0 :=
    mutualInformation_punit_punit_eq_zero _
  linarith

/-- Quantum mutual information dimension bound: `I(A;B)_τ ≤ 2 log dim A`.

This is the dimension bound for the quantum mutual information used in the
Schumacher converse [Wilde2011Qst, qit-notes.tex:31610-31690]. It follows from
the Araki--Lieb half-inequality `H(AB)_τ ≥ H(B)_τ - H(A)_τ` (available here as
`conditionalEntropy_neg_marginalA_le`) together with `H(A)_τ ≤ log dim A`:
`I(A;B) = H(A) + H(B) - H(AB) ≤ 2 H(A) ≤ 2 log dim A`. -/
theorem mutualInformation_le_two_log_card_left (τ : State (Prod a b)) :
    QIT.mutualInformation τ ≤ 2 * log2 (Fintype.card a) := by
  have hAraki : -τ.marginalA.vonNeumann ≤ τ.conditionalEntropy :=
    conditionalEntropy_neg_marginalA_le τ
  have hA : τ.marginalA.vonNeumann ≤ log2 (Fintype.card a) :=
    vonNeumann_le_log_card τ.marginalA
  rw [QIT.mutualInformation]
  rw [conditionalEntropy_eq] at hAraki
  linarith

/-- Quantum mutual information dimension bound (right system): `I(A;B)_τ ≤ 2 log dim B`,
symmetric to `mutualInformation_le_two_log_card_left`.

This is the right/marginalB version of the dimension bound for the quantum
mutual information.  It follows by applying the left bound
`mutualInformation_le_two_log_card_left` to the `prodComm`-reindexed state:
mutual information is invariant under swapping the bipartition, since the
marginalA and marginalB terms exchange and the von Neumann entropy is
reindex-invariant. -/
theorem mutualInformation_le_two_log_card_right (τ : State (Prod a b)) :
    QIT.mutualInformation τ ≤ 2 * log2 (Fintype.card b) := by
  have hstA : (τ.reindex (Equiv.prodComm a b)).marginalA = τ.marginalB := by
    apply State.ext
    ext (i i' : b)
    rfl
  have hstB : (τ.reindex (Equiv.prodComm a b)).marginalB = τ.marginalA := by
    apply State.ext
    ext (i i' : a)
    rfl
  have hmA :
      vonNeumann (τ.reindex (Equiv.prodComm a b)).marginalA =
        vonNeumann τ.marginalB :=
    congrArg State.vonNeumann hstA
  have hmB :
      vonNeumann (τ.reindex (Equiv.prodComm a b)).marginalB =
        vonNeumann τ.marginalA :=
    congrArg State.vonNeumann hstB
  have hmi_swap :
      QIT.mutualInformation (τ.reindex (Equiv.prodComm a b)) =
        QIT.mutualInformation τ := by
    rw [QIT.mutualInformation, QIT.mutualInformation, hmA, hmB,
      State.vonNeumann_reindex]
    ring
  rw [← hmi_swap]
  exact mutualInformation_le_two_log_card_left (τ.reindex (Equiv.prodComm a b))

/-- Conditional entropy is bounded above by the logarithm of the left
system dimension. -/
theorem conditionalEntropy_le_log_card_left (τ : State (Prod a b)) :
    τ.conditionalEntropy ≤ log2 (Fintype.card a) := by
  have hI : 0 ≤ QIT.mutualInformation τ := mutualInformation_nonneg τ
  have hA : τ.marginalA.vonNeumann ≤ log2 (Fintype.card a) :=
    vonNeumann_le_log_card τ.marginalA
  rw [QIT.mutualInformation] at hI
  rw [conditionalEntropy_eq]
  linarith

/-- Conditional entropy is bounded below by minus the logarithm of the left
system dimension.  This is the lower half of the finite-dimensional
dimension sandwich used at the end of Winter's AFW proof. -/
theorem conditionalEntropy_neg_log_card_left_le (τ : State (Prod a b)) :
    -log2 (Fintype.card a) ≤ τ.conditionalEntropy := by
  have hAraki : -τ.marginalA.vonNeumann ≤ τ.conditionalEntropy :=
    conditionalEntropy_neg_marginalA_le τ
  have hA : τ.marginalA.vonNeumann ≤ log2 (Fintype.card a) :=
    vonNeumann_le_log_card τ.marginalA
  linarith

private theorem binaryWeights_sum (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.toNNReal (1 - p) + Real.toNNReal p = 1 := by
  apply Subtype.ext
  simp [Real.toNNReal_of_nonneg hp0, Real.toNNReal_of_nonneg (sub_nonneg.mpr hp1)]

/-- Binary convex mixture `(1 - p)ρ + pτ` of two states. -/
def binaryMix (p : ℝ) (ρ τ : State a) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : State a where
  matrix := (Real.toNNReal (1 - p)) • ρ.matrix + (Real.toNNReal p) • τ.matrix
  pos := by
    exact Matrix.PosSemidef.add
      (ρ.pos.smul (NNReal.coe_nonneg _))
      (τ.pos.smul (NNReal.coe_nonneg _))
  trace_eq_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      ρ.trace_eq_one, τ.trace_eq_one]
    rw [NNReal.smul_def, NNReal.smul_def]
    simp [Algebra.smul_def, Real.toNNReal_of_nonneg hp0,
      Real.toNNReal_of_nonneg (sub_nonneg.mpr hp1)]

@[simp]
theorem binaryMix_matrix (p : ℝ) (ρ τ : State a) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binaryMix p ρ τ hp0 hp1).matrix =
      (Real.toNNReal (1 - p)) • ρ.matrix + (Real.toNNReal p) • τ.matrix :=
  rfl

/-- The two-point ensemble with weights `(1-p,p)`. -/
private def binaryEnsemble (p : ℝ) (ρ τ : State a) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Ensemble Bool a where
  probs := fun b => if b then Real.toNNReal p else Real.toNNReal (1 - p)
  weights_sum := by
    apply Subtype.ext
    simp [Real.toNNReal_of_nonneg hp0, Real.toNNReal_of_nonneg (sub_nonneg.mpr hp1)]
  states := fun b => if b then τ else ρ

private theorem binaryEnsemble_averageState (p : ℝ) (ρ τ : State a)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binaryEnsemble p ρ τ hp0 hp1).averageState =
      binaryMix p ρ τ hp0 hp1 := by
  apply State.ext
  rw [Ensemble.averageState_matrix, binaryMix_matrix]
  ext i j
  simp [binaryEnsemble, Matrix.add_apply, add_comm]

private theorem binaryEnsemble_shannon_eq_binaryEntropy (p : ℝ)
    (ρ τ : State a) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    -(∑ x : Bool, xlog2 (((binaryEnsemble p ρ τ hp0 hp1).probs x : ℝ))) =
      binaryEntropy p := by
  simp [binaryEnsemble, Real.toNNReal_of_nonneg hp0,
    Real.toNNReal_of_nonneg (sub_nonneg.mpr hp1), add_comm]
  rw [binaryEntropy]
  ring

/-- Binary conditional entropy is not too concave: mixing costs at most the
binary Shannon entropy of the mixing weight. -/
theorem conditionalEntropy_binaryMix_le
    (p : ℝ) (ρ τ : State (Prod a b)) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binaryMix p ρ τ hp0 hp1).conditionalEntropy ≤
      binaryEntropy p + (1 - p) * ρ.conditionalEntropy + p * τ.conditionalEntropy := by
  let E : Ensemble Bool (Prod a b) := binaryEnsemble p ρ τ hp0 hp1
  have havg : E.averageState = binaryMix p ρ τ hp0 hp1 := by
    simpa [E] using binaryEnsemble_averageState p ρ τ hp0 hp1
  have hAB := Ensemble.vonNeumann_average_le_shannon_add_sum E
  have hB := Ensemble.vonNeumann_average_ge_sum E.marginalBipartiteB
  have hBavg : E.marginalBipartiteB.averageState = E.averageState.marginalB :=
    Ensemble.marginalBipartiteB_averageState E
  have hAB' :
      (binaryMix p ρ τ hp0 hp1).vonNeumann ≤
        binaryEntropy p + (1 - p) * ρ.vonNeumann + p * τ.vonNeumann := by
    have hsh := binaryEnsemble_shannon_eq_binaryEntropy (p := p) ρ τ hp0 hp1
    have hAB0 :
        (binaryMix p ρ τ hp0 hp1).vonNeumann ≤
          -(∑ x : Bool, xlog2 (((E : Ensemble Bool (Prod a b)).probs x : ℝ))) +
            ((1 - p) * ρ.vonNeumann + p * τ.vonNeumann) := by
      rw [← havg]
      simpa [E, binaryEnsemble, Real.toNNReal_of_nonneg hp0,
        Real.toNNReal_of_nonneg (sub_nonneg.mpr hp1), add_comm, add_left_comm, add_assoc]
        using hAB
    rw [hsh] at hAB0
    linarith
  have hB' :
      (1 - p) * ρ.marginalB.vonNeumann + p * τ.marginalB.vonNeumann ≤
        (binaryMix p ρ τ hp0 hp1).marginalB.vonNeumann := by
    rw [← havg, ← hBavg]
    simpa [E, binaryEnsemble, Real.toNNReal_of_nonneg hp0,
      Real.toNNReal_of_nonneg (sub_nonneg.mpr hp1), add_comm, add_left_comm, add_assoc]
      using hB
  rw [conditionalEntropy_eq, conditionalEntropy_eq, conditionalEntropy_eq]
  linarith

/-- Binary specialization of concavity of conditional entropy. -/
theorem conditionalEntropy_binaryMix_ge
    (p : ℝ) (ρ τ : State (Prod a b)) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * ρ.conditionalEntropy + p * τ.conditionalEntropy ≤
      (binaryMix p ρ τ hp0 hp1).conditionalEntropy := by
  let E : Ensemble Bool (Prod a b) := binaryEnsemble p ρ τ hp0 hp1
  have hconc := State.conditionalEntropy_concave (E := E)
  have havg : E.averageState = binaryMix p ρ τ hp0 hp1 := by
    simpa [E] using binaryEnsemble_averageState p ρ τ hp0 hp1
  rw [havg] at hconc
  simpa [E, binaryEnsemble, Real.toNNReal_of_nonneg hp0,
    Real.toNNReal_of_nonneg (sub_nonneg.mpr hp1), add_comm, add_left_comm, add_assoc]
    using hconc

end State

/-- Scalar right-hand side in Winter's Alicki--Fannes--Winter bound:
`2 ε log₂ d + (1 + ε) h₂(ε / (1 + ε))`. -/
def afwContinuityModulus (d : ℕ) (ε : ℝ) : ℝ :=
  2 * ε * log2 (d : ℝ) +
    (1 + ε) * binaryEntropy (ε / (1 + ε))

@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy, xlog2, log2_one]

@[simp] theorem binaryEntropy_one : binaryEntropy 1 = 0 := by
  simp [binaryEntropy, xlog2, log2_one]

theorem binaryEntropy_eq_neg_xlog2_sub_xlog2 (ε : ℝ) :
    binaryEntropy ε = -xlog2 ε - xlog2 (1 - ε) := rfl

theorem tendsto_xlog2_nhdsWithin_zero_right :
    Tendsto xlog2 (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hneg :
      Tendsto (fun x : ℝ => -Real.negMulLog x / Real.log 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    exact
      by
        simpa [Real.negMulLog] using
          (((Real.continuous_negMulLog.tendsto 0).neg.div_const (Real.log 2)).mono_left
            nhdsWithin_le_nhds)
  refine hneg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxne : x ≠ 0 := ne_of_gt hx
  simp [xlog2, log2, Real.negMulLog, hxne, div_eq_mul_inv]
  ring

theorem tendsto_binaryEntropy_nhdsWithin_zero_right :
    Tendsto binaryEntropy (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hx := tendsto_xlog2_nhdsWithin_zero_right
  have hone :
      Tendsto (fun x : ℝ => xlog2 (1 - x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hcont : ContinuousAt (fun x : ℝ => xlog2 (1 - x)) 0 := by
      rw [show (fun x : ℝ => xlog2 (1 - x)) =
          (fun x : ℝ => -Real.negMulLog (1 - x) / Real.log 2) by
        funext x
        by_cases hx : 1 - x = 0
        · simp [xlog2, Real.negMulLog, hx]
        · simp [xlog2, log2, Real.negMulLog, hx, div_eq_mul_inv]
          ring]
      exact ((Real.continuous_negMulLog.continuousAt.comp
        ((continuousAt_const.sub continuousAt_id))).neg.div_const (Real.log 2))
    simpa [xlog2, log2_one] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  simpa [binaryEntropy] using hx.neg.sub hone

theorem tendsto_afwContinuityModulus_nhdsWithin_zero_right (d : ℕ) :
    Tendsto (afwContinuityModulus d)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hlin :
      Tendsto (fun ε : ℝ => 2 * ε * log2 (d : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hidWithin :
        Tendsto (fun ε : ℝ => ε)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
      tendsto_id
    have hid0 :
        Tendsto (fun ε : ℝ => ε)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
      (tendsto_nhdsWithin_iff.mp hidWithin).1
    simpa using (hid0.const_mul (2 : ℝ)).mul_const (log2 (d : ℝ))
  have harg0 :
      Tendsto (fun ε : ℝ => ε / (1 + ε))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hcont : ContinuousAt (fun ε : ℝ => ε / (1 + ε)) 0 :=
      continuousAt_id.div (continuousAt_const.add continuousAt_id) (by norm_num)
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have harg_pos :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ε / (1 + ε) ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : 0 < ε := by simpa using hε
    exact div_pos hεpos (by linarith)
  have harg :
      Tendsto (fun ε : ℝ => ε / (1 + ε))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨harg0, harg_pos⟩
  have hbin :
      Tendsto (fun ε : ℝ => binaryEntropy (ε / (1 + ε)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_binaryEntropy_nhdsWithin_zero_right.comp harg
  have hscale :
      Tendsto (fun ε : ℝ => (1 + ε) * binaryEntropy (ε / (1 + ε)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 * 0)) :=
    by
      have hidWithin :
          Tendsto (fun ε : ℝ => ε)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
        tendsto_id
      have hid0 :
          Tendsto (fun ε : ℝ => ε)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
        (tendsto_nhdsWithin_iff.mp hidWithin).1
      simpa using (hid0.const_add (1 : ℝ)).mul hbin
  simpa [afwContinuityModulus] using hlin.add hscale

theorem afwContinuityModulus_eq (d : ℕ) (ε : ℝ) :
    afwContinuityModulus d ε =
      2 * ε * log2 (d : ℝ) +
        (1 + ε) * binaryEntropy (ε / (1 + ε)) := rfl

theorem xlog2_nonpos_of_nonneg_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    xlog2 x ≤ 0 := by
  by_cases hx : x = 0
  · simp [xlog2, hx]
  · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    have hlog2le : log2 x ≤ 0 := by
      unfold log2
      exact div_nonpos_of_nonpos_of_nonneg
        (Real.log_nonpos hx0 hx1) (le_of_lt (Real.log_pos one_lt_two))
    simpa [xlog2, hx] using
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hxpos) hlog2le

theorem binaryEntropy_nonneg {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    0 ≤ binaryEntropy ε := by
  have hleft : 0 ≤ -xlog2 ε :=
    neg_nonneg.mpr (xlog2_nonpos_of_nonneg_of_le_one hε0 hε1)
  have hone0 : 0 ≤ 1 - ε := sub_nonneg.mpr hε1
  have hone1 : 1 - ε ≤ 1 := by linarith
  have hright : 0 ≤ -xlog2 (1 - ε) :=
    neg_nonneg.mpr (xlog2_nonpos_of_nonneg_of_le_one hone0 hone1)
  unfold binaryEntropy
  linarith

theorem afw_binaryEntropy_argument_nonneg {ε : ℝ} (hε0 : 0 ≤ ε) :
    0 ≤ ε / (1 + ε) := by
  exact div_nonneg hε0 (by linarith)

theorem afw_binaryEntropy_argument_le_one {ε : ℝ} (hε0 : 0 ≤ ε) :
    ε / (1 + ε) ≤ 1 := by
  have hden : 0 < 1 + ε := by linarith
  rw [div_le_one hden]
  linarith

theorem binaryEntropy_afw_argument_nonneg {ε : ℝ} (hε0 : 0 ≤ ε) :
    0 ≤ binaryEntropy (ε / (1 + ε)) :=
  binaryEntropy_nonneg (afw_binaryEntropy_argument_nonneg hε0)
    (afw_binaryEntropy_argument_le_one hε0)

theorem afw_binaryEntropy_scaled_eq {ε : ℝ} (hε0 : 0 ≤ ε) :
    (1 + ε) * binaryEntropy (ε / (1 + ε)) =
      -xlog2 ε + xlog2 (1 + ε) := by
  by_cases hε : ε = 0
  · simp [hε, binaryEntropy, xlog2, log2_one]
  have hεpos : 0 < ε := lt_of_le_of_ne hε0 (Ne.symm hε)
  have honepos : 0 < 1 + ε := by linarith
  have harg_ne : ε / (1 + ε) ≠ 0 := by positivity
  have hone_sub_eq : 1 - ε / (1 + ε) = (1 + ε)⁻¹ := by
    field_simp [honepos.ne']
    ring
  have hone_sub_ne : 1 - ε / (1 + ε) ≠ 0 := by
    rw [hone_sub_eq]
    exact inv_ne_zero honepos.ne'
  have hlog_arg :
      log2 (ε / (1 + ε)) = log2 ε - log2 (1 + ε) := by
    unfold log2
    rw [Real.log_div hεpos.ne' honepos.ne']
    ring
  have hlog_inv :
      log2 (1 - ε / (1 + ε)) = -log2 (1 + ε) := by
    rw [hone_sub_eq]
    unfold log2
    rw [Real.log_inv]
    ring
  simp [binaryEntropy, xlog2, harg_ne, hone_sub_ne, hε, honepos.ne',
    hlog_arg, hlog_inv]
  field_simp [honepos.ne']
  ring_nf

theorem log2_nat_cast_nonneg (d : ℕ) : 0 ≤ log2 (d : ℝ) := by
  rcases d with _ | d
  · simp [log2]
  · unfold log2
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast Nat.succ_pos d))
      (le_of_lt (Real.log_pos one_lt_two))

theorem afwContinuityModulus_nonneg {d : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) :
    0 ≤ afwContinuityModulus d ε := by
  have hfirst : 0 ≤ 2 * ε * log2 (d : ℝ) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hε0) (log2_nat_cast_nonneg d)
  have hsecond : 0 ≤ (1 + ε) * binaryEntropy (ε / (1 + ε)) := by
    exact mul_nonneg (by linarith) (binaryEntropy_afw_argument_nonneg hε0)
  unfold afwContinuityModulus
  linarith

theorem afwContinuityModulus_mono_card {d e : ℕ} {ε : ℝ}
    (hde : d ≤ e) (hε0 : 0 ≤ ε) :
    afwContinuityModulus d ε ≤ afwContinuityModulus e ε := by
  have hlog : log2 (d : ℝ) ≤ log2 (e : ℝ) := by
    rcases d with _ | d
    · simp [log2]
      exact log2_nat_cast_nonneg e
    · unfold log2
      exact div_le_div_of_nonneg_right
        (Real.log_le_log (by exact_mod_cast Nat.succ_pos d) (by exact_mod_cast hde))
        (le_of_lt (Real.log_pos one_lt_two))
  unfold afwContinuityModulus
  gcongr

private theorem afw_scaledLog_hasDerivAt {ε : ℝ} (hεpos : 0 < ε) :
    HasDerivAt (fun t : ℝ => -(t * log2 t) + (1 + t) * log2 (1 + t))
      (log2 (1 + ε) - log2 ε) ε := by
  have hleft : HasDerivAt (fun t : ℝ => t * log2 t) (log2 ε + 1 / Real.log 2) ε := by
    have hlog2 : HasDerivAt log2 (ε⁻¹ / Real.log 2) ε := by
      unfold log2
      exact (Real.hasDerivAt_log hεpos.ne').div_const _
    have h := (hasDerivAt_id ε).mul hlog2
    convert h using 1
    simp [div_eq_mul_inv, hεpos.ne']
  have hright : HasDerivAt (fun t : ℝ => (1 + t) * log2 (1 + t))
      (log2 (1 + ε) + 1 / Real.log 2) ε := by
    have honepos : 0 < 1 + ε := by linarith
    have harg : HasDerivAt (fun t : ℝ => 1 + t) 1 ε := by
      simpa using (hasDerivAt_const (x := ε) (c := (1 : ℝ))).add (hasDerivAt_id ε)
    have hlog2 : HasDerivAt (fun t : ℝ => log2 (1 + t)) ((1 + ε)⁻¹ / Real.log 2) ε := by
      unfold log2
      simpa [Function.comp_def, one_mul] using
        ((Real.hasDerivAt_log honepos.ne').comp ε harg).div_const (Real.log 2)
    have h := harg.mul hlog2
    convert h using 1
    simp [div_eq_mul_inv, honepos.ne']
  convert hleft.neg.add hright using 1
  ring

private theorem afw_scaledLog_mono_of_pos {δ ε : ℝ} (hδpos : 0 < δ) (hδε : δ ≤ ε) :
    -(δ * log2 δ) + (1 + δ) * log2 (1 + δ) ≤
      -(ε * log2 ε) + (1 + ε) * log2 (1 + ε) := by
  let f := fun t : ℝ => -(t * log2 t) + (1 + t) * log2 (1 + t)
  have hmono : MonotoneOn f (Set.Icc δ ε) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun x => log2 (1 + x) - log2 x) (convex_Icc δ ε) ?_ ?_ ?_
    · intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hδpos hx.1
      exact (afw_scaledLog_hasDerivAt hxpos).continuousAt.continuousWithinAt
    · intro x hx
      have hxI : x ∈ Set.Ioo δ ε := by simpa [interior_Icc] using hx
      have hxpos : 0 < x := lt_trans hδpos hxI.1
      exact (afw_scaledLog_hasDerivAt hxpos).hasDerivWithinAt
    · intro x hx
      have hxI : x ∈ Set.Ioo δ ε := by simpa [interior_Icc] using hx
      have hxpos : 0 < x := lt_trans hδpos hxI.1
      exact sub_nonneg.mpr (by
        unfold log2
        exact div_le_div_of_nonneg_right (Real.log_le_log hxpos (by linarith))
          (le_of_lt (Real.log_pos one_lt_two)))
  exact hmono ⟨le_rfl, hδε⟩ ⟨hδε, le_rfl⟩ hδε

theorem afwContinuityModulus_mono_epsilon {d : ℕ} {δ ε : ℝ}
    (hδ0 : 0 ≤ δ) (hδε : δ ≤ ε) :
    afwContinuityModulus d δ ≤ afwContinuityModulus d ε := by
  have hε0 : 0 ≤ ε := hδ0.trans hδε
  have hfirst : 2 * δ * log2 (d : ℝ) ≤ 2 * ε * log2 (d : ℝ) := by
    gcongr
    exact log2_nat_cast_nonneg d
  have hsecond :
      (1 + δ) * binaryEntropy (δ / (1 + δ)) ≤
        (1 + ε) * binaryEntropy (ε / (1 + ε)) := by
    by_cases hδ : δ = 0
    · subst δ
      simp only [zero_div, binaryEntropy_zero, mul_zero]
      exact mul_nonneg (show 0 ≤ 1 + ε by linarith) (binaryEntropy_afw_argument_nonneg hε0)
    · have hδpos : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hδ)
      have hεpos : 0 < ε := lt_of_lt_of_le hδpos hδε
      rw [afw_binaryEntropy_scaled_eq hδ0, afw_binaryEntropy_scaled_eq hε0]
      simpa [xlog2, hδ, (ne_of_gt hδpos), (ne_of_gt (by linarith : 0 < 1 + δ)),
        (ne_of_gt hεpos), (ne_of_gt (by linarith : 0 < 1 + ε))] using
        afw_scaledLog_mono_of_pos hδpos hδε
  unfold afwContinuityModulus
  linarith

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]
variable {b : Type v} [Fintype b] [DecidableEq b]

private theorem afw_one_sub_weight_eq {δ : ℝ} (hδ0 : 0 ≤ δ) :
    1 - δ / (1 + δ) = (1 + δ)⁻¹ := by
  have hden : 1 + δ ≠ 0 := by linarith
  field_simp [hden]
  ring

private theorem afw_common_state_eq
    (ρ σ : State (Prod a b)) (hδ : 0 < ρ.normalizedTraceDistance σ) :
    binaryMix (ρ.normalizedTraceDistance σ / (1 + ρ.normalizedTraceDistance σ))
        σ (ρ.traceDistancePosPartState σ hδ)
        (afw_binaryEntropy_argument_nonneg hδ.le)
        (afw_binaryEntropy_argument_le_one hδ.le) =
      binaryMix (ρ.normalizedTraceDistance σ / (1 + ρ.normalizedTraceDistance σ))
        ρ (ρ.traceDistanceNegPartState σ hδ)
        (afw_binaryEntropy_argument_nonneg hδ.le)
        (afw_binaryEntropy_argument_le_one hδ.le) := by
  let δ : ℝ := ρ.normalizedTraceDistance σ
  have hδ0 : 0 ≤ δ := hδ.le
  have hδpos : 0 < δ := hδ
  have hδden : 1 + δ ≠ 0 := by linarith
  have hp0 : 0 ≤ δ / (1 + δ) := afw_binaryEntropy_argument_nonneg hδ0
  have hp1 : δ / (1 + δ) ≤ 1 := afw_binaryEntropy_argument_le_one hδ0
  have honep0 : 0 ≤ 1 - δ / (1 + δ) := sub_nonneg.mpr hp1
  have hcommon :=
    State.sigma_add_normalizedTraceDistance_smul_traceDistancePosPartState_eq ρ σ hδ
  change σ.matrix + ((δ : ℝ) : ℂ) • (ρ.traceDistancePosPartState σ hδ).matrix =
    ρ.matrix + ((δ : ℝ) : ℂ) • (ρ.traceDistanceNegPartState σ hδ).matrix at hcommon
  apply State.ext
  rw [binaryMix_matrix, binaryMix_matrix]
  change
    (Real.toNNReal (1 - δ / (1 + δ))) • σ.matrix +
        (Real.toNNReal (δ / (1 + δ))) • (ρ.traceDistancePosPartState σ hδ).matrix =
      (Real.toNNReal (1 - δ / (1 + δ))) • ρ.matrix +
        (Real.toNNReal (δ / (1 + δ))) • (ρ.traceDistanceNegPartState σ hδ).matrix
  ext i j
  have hentry := congrFun (congrFun hcommon i) j
  simp only [Matrix.add_apply] at hentry ⊢
  rw [NNReal.smul_def, NNReal.smul_def, NNReal.smul_def, NNReal.smul_def]
  simp [Algebra.smul_def, Real.toNNReal_of_nonneg hp0,
    Real.toNNReal_of_nonneg honep0] at hentry ⊢
  have hδdenC : (1 + (δ : ℂ)) ≠ 0 := by
    simpa [Complex.ofReal_add] using
      (Complex.ofReal_ne_zero.mpr hδden : ((1 + δ : ℝ) : ℂ) ≠ 0)
  field_simp [hδdenC]
  simpa [mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
    mul_assoc] using hentry

private theorem conditionalEntropy_sub_le_afwModulus
    (ρ σ : State (Prod a b)) :
    σ.conditionalEntropy - ρ.conditionalEntropy ≤
      afwContinuityModulus (Fintype.card a) (ρ.normalizedTraceDistance σ) := by
  let δ : ℝ := ρ.normalizedTraceDistance σ
  have hδ0 : 0 ≤ δ := State.normalizedTraceDistance_nonneg ρ σ
  by_cases hδzero : δ = 0
  · have hρσ : ρ = σ := by
      exact State.eq_of_normalizedTraceDistance_eq_zero (rho := ρ) (sigma := σ) hδzero
    subst σ
    have hmod : 0 ≤ afwContinuityModulus (Fintype.card a) 0 :=
      afwContinuityModulus_nonneg (d := Fintype.card a) (ε := 0) (by norm_num)
    simpa [δ] using hmod
  · have hδpos : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hδzero)
    let p : ℝ := δ / (1 + δ)
    have hp0 : 0 ≤ p := afw_binaryEntropy_argument_nonneg hδ0
    have hp1 : p ≤ 1 := afw_binaryEntropy_argument_le_one hδ0
    let Δ : State (Prod a b) := ρ.traceDistancePosPartState σ hδpos
    let Δ' : State (Prod a b) := ρ.traceDistanceNegPartState σ hδpos
    let ω : State (Prod a b) := binaryMix p σ Δ hp0 hp1
    have hω :
        ω = binaryMix p ρ Δ' hp0 hp1 := by
      simpa [ω, Δ, Δ', p, δ] using afw_common_state_eq ρ σ hδpos
    have hlower :
        (1 - p) * σ.conditionalEntropy + p * Δ.conditionalEntropy ≤
          ω.conditionalEntropy := by
      simpa [ω] using conditionalEntropy_binaryMix_ge p σ Δ hp0 hp1
    have hupper :
        ω.conditionalEntropy ≤
          binaryEntropy p + (1 - p) * ρ.conditionalEntropy +
            p * Δ'.conditionalEntropy := by
      rw [hω]
      simpa using conditionalEntropy_binaryMix_le p ρ Δ' hp0 hp1
    have hcombine :
        (1 - p) * σ.conditionalEntropy + p * Δ.conditionalEntropy ≤
          binaryEntropy p + (1 - p) * ρ.conditionalEntropy +
            p * Δ'.conditionalEntropy :=
      le_trans hlower hupper
    have hscale_nonneg : 0 ≤ 1 + δ := by linarith
    have hmul := mul_le_mul_of_nonneg_left hcombine hscale_nonneg
    have hp_scale : (1 + δ) * p = δ := by
      have hden : 1 + δ ≠ 0 := by linarith
      dsimp [p]
      field_simp [hden]
    have hone_scale : (1 + δ) * (1 - p) = 1 := by
      calc
        (1 + δ) * (1 - p) = (1 + δ) - (1 + δ) * p := by ring
        _ = 1 := by rw [hp_scale]; ring
    have hleft_scale :
        (1 + δ) * ((1 - p) * σ.conditionalEntropy + p * Δ.conditionalEntropy) =
          σ.conditionalEntropy + δ * Δ.conditionalEntropy := by
      rw [mul_add, ← mul_assoc, ← mul_assoc, hone_scale, hp_scale]
      ring
    have hright_scale :
        (1 + δ) *
            (binaryEntropy p + (1 - p) * ρ.conditionalEntropy +
              p * Δ'.conditionalEntropy) =
          (1 + δ) * binaryEntropy p + ρ.conditionalEntropy +
            δ * Δ'.conditionalEntropy := by
      rw [mul_add, mul_add, ← mul_assoc (1 + δ) (1 - p),
        ← mul_assoc (1 + δ) p, hone_scale, hp_scale]
      ring
    rw [hleft_scale, hright_scale] at hmul
    have hdiff :
        σ.conditionalEntropy - ρ.conditionalEntropy ≤
          δ * (Δ'.conditionalEntropy - Δ.conditionalEntropy) +
            (1 + δ) * binaryEntropy p := by
      linarith
    have hΔupper : Δ'.conditionalEntropy ≤ log2 (Fintype.card a) :=
      conditionalEntropy_le_log_card_left Δ'
    have hΔlower : -log2 (Fintype.card a) ≤ Δ.conditionalEntropy :=
      conditionalEntropy_neg_log_card_left_le Δ
    have hΔdiff :
        Δ'.conditionalEntropy - Δ.conditionalEntropy ≤
          2 * log2 (Fintype.card a) := by
      linarith
    have hδdiff :
        δ * (Δ'.conditionalEntropy - Δ.conditionalEntropy) ≤
          δ * (2 * log2 (Fintype.card a)) := by
      exact mul_le_mul_of_nonneg_left hΔdiff hδ0
    unfold afwContinuityModulus
    change σ.conditionalEntropy - ρ.conditionalEntropy ≤
      2 * δ * log2 (Fintype.card a : ℝ) +
        (1 + δ) * binaryEntropy (δ / (1 + δ))
    nlinarith

/-- Alicki--Fannes--Winter continuity bound at the exact normalized trace
distance.  This follows Winter's positive/negative trace-distance split and
then sandwiches the two auxiliary conditional entropies by `± log |A|`. -/
theorem conditionalEntropy_dist_le_afwModulus
    (ρ σ : State (Prod a b)) :
    |ρ.conditionalEntropy - σ.conditionalEntropy| ≤
      afwContinuityModulus (Fintype.card a) (ρ.normalizedTraceDistance σ) := by
  rw [abs_sub_le_iff]
  constructor
  · have h := conditionalEntropy_sub_le_afwModulus σ ρ
    rwa [State.normalizedTraceDistance_comm σ ρ] at h
  · exact conditionalEntropy_sub_le_afwModulus ρ σ

/-- Source-shaped Alicki--Fannes--Winter continuity bound with an external
error parameter `ε`.  Nonnegativity of `ε` is forced by
`normalizedTraceDistance_nonneg` and `hεdist`, so no extra hypothesis is
needed. -/
theorem alickiFannesWinter_conditionalEntropy
    (ρ σ : State (Prod a b)) (ε : ℝ)
    (hεdist : ρ.normalizedTraceDistance σ ≤ ε) :
    |ρ.conditionalEntropy - σ.conditionalEntropy| ≤
      afwContinuityModulus (Fintype.card a) ε := by
  exact (conditionalEntropy_dist_le_afwModulus ρ σ).trans
    (afwContinuityModulus_mono_epsilon
      (State.normalizedTraceDistance_nonneg ρ σ) hεdist)

end State

end

end QIT
