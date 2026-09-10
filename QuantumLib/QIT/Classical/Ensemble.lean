/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Classical.Distribution
public import QuantumLib.QIT.Core.State
public import QuantumLib.QIT.Util.Matrix
public import QuantumInfo.States.Ensemble
public import Mathlib.Data.NNReal.Basic

/-!
# Finite ensembles of states

A finite indexed ensemble pairs a probability distribution over a finite
index type with a density state at each index. The average (mean) state is
the convex combination of the member states weighted by the distribution,
instantiating the convex-set construction for density states in the source
material [Tomamichel2015FiniteResources, prelim.tex:431-431].

`MEnsemble` stores its weights as a `ProbDistribution`, whose values are the
reals in `[0, 1]`. `MEnsemble.probs` reads the same weights as nonnegative
reals, which is the form the convex combinations work with, and
`MEnsemble.ofProbs` builds an ensemble from them.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace MEnsemble

open QIT

universe u v w

noncomputable section

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [Fintype a] [DecidableEq a]

/-- The weight an ensemble gives each index, as a nonnegative real. -/
def probs (E : MEnsemble a ι) (i : ι) : ℝ≥0 :=
  E.distr.nnprob i

theorem coe_probs (E : MEnsemble a ι) (i : ι) : (E.probs i : ℝ) = E.distr i :=
  rfl

@[simp]
theorem distr_nnprob (E : MEnsemble a ι) (i : ι) : E.distr.nnprob i = E.probs i :=
  rfl

/-- The weights of a finite ensemble sum to one. -/
theorem weights_sum (E : MEnsemble a ι) : (∑ i, E.probs i) = 1 :=
  E.distr.sum_nnprob

/-- The ensemble with the given weights and member states. -/
@[reducible]
def ofProbs (p : ι → ℝ≥0) (hp : (∑ i, p i) = 1) (s : ι → MState a) : MEnsemble a ι where
  var := s
  distr := ProbDistribution.ofNNReal p hp

@[simp]
theorem ofProbs_distr (p : ι → ℝ≥0) (hp : (∑ i, p i) = 1) (s : ι → MState a) :
    (ofProbs p hp s).distr = ProbDistribution.ofNNReal p hp :=
  rfl

@[simp]
theorem ofProbs_probs (p : ι → ℝ≥0) (hp : (∑ i, p i) = 1) (s : ι → MState a) :
    (ofProbs p hp s).probs = p :=
  rfl

@[simp]
theorem ofProbs_states (p : ι → ℝ≥0) (hp : (∑ i, p i) = 1) (s : ι → MState a) :
    (ofProbs p hp s).states = s :=
  rfl

/-- Two ensembles with the same weights and the same member states are equal. -/
@[ext]
theorem ext_probs {E F : MEnsemble a ι} (hp : E.probs = F.probs) (hs : E.states = F.states) :
    E = F := by
  obtain ⟨sE, ⟨pE, hE⟩⟩ := E
  obtain ⟨sF, ⟨pF, hF⟩⟩ := F
  congr 1
  refine Subtype.ext (funext fun i => Prob.ext ?_)
  exact congrArg (fun q : ℝ≥0 => (q : ℝ)) (congrFun hp i)

/-- Relabel a finite ensemble along an equivalence of its classical index type. -/
def relabelIndex {κ : Type w} [Fintype κ]
    (E : MEnsemble a ι) (e : κ ≃ ι) : MEnsemble a κ :=
  ofProbs (fun k => E.probs (e k))
    (by
      calc
        ∑ k, E.probs (e k) = ∑ i, E.probs i :=
          Fintype.sum_equiv e _ _ (fun _ => rfl)
        _ = 1 := E.weights_sum)
    (fun k => E.states (e k))

@[simp]
theorem relabelIndex_probs {κ : Type w} [Fintype κ]
    (E : MEnsemble a ι) (e : κ ≃ ι) (k : κ) :
    (E.relabelIndex e).probs k = E.probs (e k) :=
  rfl

@[simp]
theorem relabelIndex_states {κ : Type w} [Fintype κ]
    (E : MEnsemble a ι) (e : κ ≃ ι) (k : κ) :
    (E.relabelIndex e).states k = E.states (e k) :=
  rfl

/-- Ensemble probabilities are nonnegative when read as real numbers. -/
theorem prob_nonneg (E : MEnsemble a ι) (i : ι) : 0 ≤ (E.probs i : ℝ) :=
  NNReal.coe_nonneg (E.probs i)

/-- Every probability weight in a finite normalized ensemble is at most one. -/
theorem prob_le_one [DecidableEq ι] (E : MEnsemble a ι) (i : ι) :
    (E.probs i : ℝ) ≤ 1 :=
  (E.distr i).2.2

/-- The average (mean) state of an ensemble, the convex combination weighted by `probs`. -/
def averageState (E : MEnsemble a ι) : MState a :=
  Ensemble.mix E

/-- The average state's matrix is the weighted sum of the member matrices. -/
@[simp]
theorem averageState_matrix (E : MEnsemble a ι) :
    E.averageState.m = ∑ i, (E.probs i) • (E.states i).m := by
  rw [averageState, Ensemble.mix_of]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (E.probs i : ℝ) • (E.states i).m = E.probs i • (E.states i).m
  rw [NNReal.smul_def]

/-- Relabeling the classical index of an ensemble preserves its average state. -/
@[simp]
theorem relabelIndex_averageState {κ : Type w} [Fintype κ]
    (E : MEnsemble a ι) (e : κ ≃ ι) :
    (E.relabelIndex e).averageState = E.averageState := by
  apply MState.ext
  rw [averageState_matrix, averageState_matrix]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- If every member state equals `σ`, the average is `σ`. -/
theorem averageState_of_constant (E : MEnsemble a ι) (σ : MState a)
    (h : ∀ i, E.states i = σ) : E.averageState = σ := by
  apply MState.ext
  rw [averageState_matrix,
      Finset.sum_congr rfl fun i _ => by rw [h i],
      ← Finset.sum_smul,
      E.weights_sum, one_smul]

/-- A single-element ensemble averages to its sole state. -/
theorem averageState_singleton [DecidableEq ι]
    (E : MEnsemble a ι) (hcard : Fintype.card ι = 1) (i : ι) :
    E.averageState = E.states i := by
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hcard
  have hxi : x = i := (hx i).symm
  have hunique : ∀ j, j = i := fun j => (hx j).trans hxi
  have huniv : (Finset.univ : Finset ι) = {i} := by
    ext j
    simp [hunique j]
  have hwt : E.probs i = 1 := by
    have hsum : ∑ j, E.probs j = E.probs i := by
      rw [huniv]
      simp
    exact hsum.symm.trans E.weights_sum
  apply MState.ext
  rw [averageState_matrix, huniv, Finset.sum_singleton, hwt, one_smul]

end

end MEnsemble
