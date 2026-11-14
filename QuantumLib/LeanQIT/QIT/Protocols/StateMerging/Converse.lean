/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Protocols.LOCC.ReferenceLift
public import QIT.Protocols.StateMerging.Core
public import QIT.Protocols.StateMerging.DistanceAveraging
public import QIT.Information.Entropy.EntropyTensorPower
public import QIT.Information.Entropy.MaximallyMixed
public import QIT.Information.Fannes
public import QIT.Asymptotic.AEP
import QIT.OneShot.SmoothNormalizedExtension

/-!
# Converse for quantum state merging

This module follows the Horodecki--Oppenheim--Winter converse in
`swlong.6.2.tex:1071-1139`.  It first exposes the pure input and target vectors
underlying the operational state-merging protocol and regroups the untouched
reference with Alice, as required by the LOCC entanglement argument.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

open Filter

universe u v w x y z p q ua ua' ub ub' ux

noncomputable section

/-- Entropy of the canonical maximally mixed ebit marginal. -/
private theorem sum_sum_sum_mul_eq_mul_sum_sum_sum
    {A K R : Type*} [Fintype A] [Fintype K] [Fintype R]
    (f : A → R → ℂ) (g : K → ℂ) :
    (∑ a : A, ∑ k : K, ∑ r : R, f a r * g k) =
      (∑ a : A, ∑ r : R, f a r) * ∑ k : K, g k := by
  calc
    (∑ a : A, ∑ k : K, ∑ r : R, f a r * g k) =
        ∑ a : A, ∑ k : K, (∑ r : R, f a r) * g k := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
    _ = ∑ a : A, (∑ r : R, f a r) * ∑ k : K, g k := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    _ = (∑ a : A, ∑ r : R, f a r) * ∑ k : K, g k := by
      rw [Finset.sum_mul]

private theorem sum_sum_mul_eq_mul_sum
    {K R : Type*} [Fintype K] [Fintype R]
    (f : R → ℂ) (g : K → ℂ) :
    (∑ k : K, ∑ r : R, f r * g k) = (∑ r : R, f r) * ∑ k : K, g k := by
  calc
    (∑ k : K, ∑ r : R, f r * g k) =
        ∑ k : K, (∑ r : R, f r) * g k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
    _ = (∑ r : R, f r) * ∑ k : K, g k := by
      rw [Finset.mul_sum]

private theorem log2_mul_of_pos {x y : Real} (hx : 0 < x) (hy : 0 < y) :
    log2 (x * y) = log2 x + log2 y := by
  unfold log2
  rw [Real.log_mul hx.ne' hy.ne']
  ring

private theorem squaredFidelity_reindex
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (rho sigma : State A) (e : A ≃ B) :
    (rho.reindex e).squaredFidelity (sigma.reindex e) = rho.squaredFidelity sigma := by
  rw [State.squaredFidelity_eq_fidelity_sq, State.squaredFidelity_eq_fidelity_sq,
    SmoothNormalizedExtension.State.fidelity_reindex]

namespace OneWayLOCC

variable {A : Type ua} {A' : Type ua'} {B : Type ub} {B' : Type ub'} {X : Type ux}
variable [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
variable [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype X]

/-- Fannes continuity applied to one physical positive LOCC branch and a pure target. -/
theorem finalNormalizedBranch_entanglement_sub_target_le_howFannes
    (L : OneWayLOCC A A' B B' X) (input : PureVector (Prod A B))
    (target : PureVector (Prod A' B')) (j : L.jointPositiveSupport input) :
    |(L.finalNormalizedBranch input j).entanglementEntropy - target.entanglementEntropy| ≤
      log2 (Fintype.card B' : Real) *
        howFannesEta
          ((L.finalNormalizedBranch input j).state.marginalB.traceNormDistance
            target.state.marginalB) := by
  exact State.vonNeumann_dist_le_howFannes
    (L.finalNormalizedBranch input j).state.marginalB target.state.marginalB

/-- Jensen-averaged Fannes continuity for the physical positive branches of a
finite one-way LOCC protocol. -/
theorem sum_jointPositiveBranchProbability_mul_abs_entanglement_sub_target_le
    (L : OneWayLOCC A A' B B' X) (input : PureVector (Prod A B))
    (target : PureVector (Prod A' B')) :
    (∑ j : L.jointPositiveSupport input,
      (L.jointPositiveBranchProbability input j : Real) *
        |(L.finalNormalizedBranch input j).entanglementEntropy -
          target.entanglementEntropy|) ≤
      log2 (Fintype.card B' : Real) *
        howFannesEta
          (∑ j : L.jointPositiveSupport input,
            (L.jointPositiveBranchProbability input j : Real) *
              (L.finalNormalizedBranch input j).state.marginalB.traceNormDistance
                target.state.marginalB) := by
  have hq := L.sum_jointPositiveBranchProbability_eq_one input
  have hpointSum :
      (∑ j : L.jointPositiveSupport input,
        (L.jointPositiveBranchProbability input j : Real) *
          |(L.finalNormalizedBranch input j).entanglementEntropy -
            target.entanglementEntropy|) ≤
        log2 (Fintype.card B' : Real) *
          ∑ j : L.jointPositiveSupport input,
            (L.jointPositiveBranchProbability input j : Real) *
              howFannesEta
                ((L.finalNormalizedBranch input j).state.marginalB.traceNormDistance
                  target.state.marginalB) := by
    calc
      (∑ j : L.jointPositiveSupport input,
          (L.jointPositiveBranchProbability input j : Real) *
            |(L.finalNormalizedBranch input j).entanglementEntropy -
              target.entanglementEntropy|) ≤
          ∑ j : L.jointPositiveSupport input,
            (L.jointPositiveBranchProbability input j : Real) *
              (log2 (Fintype.card B' : Real) *
                howFannesEta
                  ((L.finalNormalizedBranch input j).state.marginalB.traceNormDistance
                    target.state.marginalB)) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left
          (L.finalNormalizedBranch_entanglement_sub_target_le_howFannes input target j)
          (NNReal.coe_nonneg _)
      _ = log2 (Fintype.card B' : Real) *
          ∑ j : L.jointPositiveSupport input,
            (L.jointPositiveBranchProbability input j : Real) *
              howFannesEta
                ((L.finalNormalizedBranch input j).state.marginalB.traceNormDistance
                  target.state.marginalB) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hjensen := howFannesEta_weighted_le
    (fun j : L.jointPositiveSupport input => L.jointPositiveBranchProbability input j)
    (fun j => (L.finalNormalizedBranch input j).state.marginalB.traceNormDistance
      target.state.marginalB)
    hq (fun j => State.traceNormDistance_nonneg _ _)
  exact hpointSum.trans
    (mul_le_mul_of_nonneg_left hjensen (log2_nat_cast_nonneg _))

end OneWayLOCC

/-- Regroup `((Alice, Bob), Reference)` as `((Alice, Reference), Bob)` for the
HOW converse bipartition. -/
def stateMergingConverseInputEquiv
    (A : Type u) (B : Type v) (R : Type w) :
    Prod (Prod A B) R ≃ Prod (Prod A R) B where
  toFun t := ((t.1.1, t.2), t.1.2)
  invFun t := ((t.1.1, t.2), t.1.2)
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

/-- Regroup the reference-lifted LOCC output `((Alice, Reference), Bob)` back
to the operational order `((Alice, Bob), Reference)`. -/
def stateMergingConverseOutputEquiv
    (A : Type u) (B : Type v) (R : Type w) :
    Prod (Prod A R) B ≃ Prod (Prod A B) R where
  toFun t := ((t.1.1, t.2), t.1.2)
  invFun t := ((t.1.1, t.2), t.1.2)
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

/-- Moving the reference from Alice's side back to the outer output register
does not change Bob's marginal. -/
theorem State.reindex_stateMergingConverseOutputEquiv_symm_marginalB
    {A B R : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (rho : State (Prod (Prod A B) R)) :
    (rho.reindex (stateMergingConverseOutputEquiv A B R).symm).marginalB =
      rho.marginalA.marginalB := by
  apply State.ext
  rw [State.marginalB_matrix, State.marginalB_matrix, State.marginalA_matrix,
    State.reindex_matrix]
  ext i j
  change
    (∑ ar : Prod A R,
      rho.matrix ((ar.1, i), ar.2) ((ar.1, j), ar.2)) =
      ∑ a : A, ∑ r : R, rho.matrix ((a, i), r) ((a, j), r)
  rw [Fintype.sum_prod_type]

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable {psi : PureVector (Prod (Prod a b) r)} {n : ℕ}
variable {kA : Type x} {kB : Type y} {lA : Type z} {lB : Type p}
variable {outcome : Type q}
variable [Fintype kA] [DecidableEq kA] [Nonempty kA]
variable [Fintype kB] [DecidableEq kB]
variable [Fintype lA] [DecidableEq lA] [Nonempty lA]
variable [Fintype lB] [DecidableEq lB]
variable [Fintype outcome] [DecidableEq outcome] [Nonempty outcome]

/-- The grouped `A^n B^n` marginal of the state-merging source is the
bipartite tensor power of the one-copy `AB` marginal. -/
theorem stateMergingBlockSource_marginalA_eq_tensorPower
    (psi : PureVector (Prod (Prod a b) r)) (n : ℕ) :
    (stateMergingBlockSource psi n).state.marginalA =
      psi.state.marginalA.tensorPowerBipartite n := by
  simpa [stateMergingBlockSource, fqswTensorPowerTripartiteEquiv,
    PureVector.tensorPowerTripartiteGrouped,
    PureVector.tensorPowerTripartiteGroupedEquiv, PureVector.reindex_state,
    PureVector.tensorPower_state] using
    PureVector.tensorPowerTripartiteGrouped_marginalAB
      (a := a) (b := b) (c := r) psi n

/-- The grouped `A^n R^n` marginal of the state-merging source is the
bipartite tensor power of the one-copy `AR` marginal.  This is the source
identification used by the smooth-min-entropy converse. -/
theorem stateMergingBlockSource_marginalAC_eq_tensorPower
    (psi : PureVector (Prod (Prod a b) r)) (n : ℕ) :
    (stateMergingBlockSource psi n).state.marginalAC =
      psi.state.marginalAC.tensorPowerBipartite n := by
  simpa [stateMergingBlockSource, fqswTensorPowerTripartiteEquiv,
    PureVector.tensorPowerTripartiteGrouped,
    PureVector.tensorPowerTripartiteGroupedEquiv, PureVector.reindex_state,
    PureVector.tensorPower_state] using
    PureVector.tensorPowerTripartiteGrouped_marginalAC
      (a := a) (b := b) (c := r) psi n

/-- The `B^n` marginal of the grouped state-merging source is the tensor
power of the one-copy `B` marginal. -/
theorem stateMergingBlockSource_marginalB_eq_tensorPower
    (psi : PureVector (Prod (Prod a b) r)) (n : ℕ) :
    (stateMergingBlockSource psi n).state.marginalA.marginalB =
      psi.state.marginalA.marginalB.tensorPower n := by
  rw [stateMergingBlockSource_marginalA_eq_tensorPower]
  simpa using State.tensorPowerBipartite_marginalB
    (rho := psi.state.marginalA) n

namespace StateMergingBlockProtocol

local instance stateMergingConverseOutputDecidableEq :
    DecidableEq
      (Prod
        (Prod lA (Prod (Prod (TensorPower a n) (TensorPower b n)) lB))
        (TensorPower r n)) :=
  @instDecidableEqProd _ _
    (@instDecidableEqProd _ _ inferInstance
      (@instDecidableEqProd _ _
        (@instDecidableEqProd _ _
          (tensorPowerDecidableEq n) (tensorPowerDecidableEq n))
        inferInstance))
    (tensorPowerDecidableEq n)

variable (C : StateMergingBlockProtocol psi n kA kB lA lB outcome)

/-- The normalized pure vector underlying the physical state-merging input. -/
def initialPureVector :
    PureVector
      (Prod
        (Prod (Prod (TensorPower a n) kA) (Prod (TensorPower b n) kB))
        (TensorPower r n)) :=
  ((stateMergingBlockSource psi n).prod
      (PureVector.maximallyEntangled C.inputEbitPairing)).reindex
    (stateMergingInputEquiv
      (TensorPower a n) (TensorPower b n) (TensorPower r n) kA kB)

@[simp]
theorem initialPureVector_state : C.initialPureVector.state = C.initialState := by
  rw [initialPureVector, initialState, PureVector.reindex_state, PureVector.prod_state]
  rfl

/-- The input pure vector under the converse bipartition
`(Alice, Reference) | Bob`. -/
def converseInputPureVector :
    PureVector
      (Prod
        (Prod (Prod (TensorPower a n) kA) (TensorPower r n))
        (Prod (TensorPower b n) kB)) :=
  C.initialPureVector.reindex
    (stateMergingConverseInputEquiv
      (Prod (TensorPower a n) kA)
      (Prod (TensorPower b n) kB)
      (TensorPower r n))

/-- The physical state-merging one-way LOCC operation lifted by the untouched
IID reference and grouped with Alice for the HOW converse. -/
def converseLOCC :
    OneWayLOCC
      (Prod (Prod (TensorPower a n) kA) (TensorPower r n))
      (Prod lA (TensorPower r n))
      (Prod (TensorPower b n) kB)
      (Prod (Prod (TensorPower a n) (TensorPower b n)) lB)
      outcome :=
  C.locc.prodIdRight (R := TensorPower r n)

/-- The lifted LOCC output is the operational output with the untouched
reference regrouped onto Alice's side. -/
theorem converseLOCC_applyState :
    C.converseLOCC.toChannel.applyState C.converseInputPureVector.state =
      C.outputState.reindex
        (stateMergingConverseOutputEquiv
          lA (Prod (Prod (TensorPower a n) (TensorPower b n)) lB)
          (TensorPower r n)).symm := by
  have h := OneWayLOCC.prodIdRight_applyState_reindex_pure
    (R := TensorPower r n) C.locc C.initialPureVector
  calc
    C.converseLOCC.toChannel.applyState C.converseInputPureVector.state =
        (C.locc.prodIdRight (R := TensorPower r n)).toChannel.applyState
          (C.initialPureVector.state.reindex
            (loccReferenceRegroupEquiv
              (Prod (TensorPower a n) kA)
              (Prod (TensorPower b n) kB)
              (TensorPower r n))) := by
      rw [converseLOCC, converseInputPureVector, PureVector.reindex_state]
      rfl
    _ = ((C.locc.toChannel.prod (Channel.idChannel (TensorPower r n))).applyState
          C.initialPureVector.state).reindex
          (loccReferenceRegroupEquiv
            lA (Prod (Prod (TensorPower a n) (TensorPower b n)) lB)
            (TensorPower r n)) := h
    _ = C.outputState.reindex
        (stateMergingConverseOutputEquiv
          lA (Prod (Prod (TensorPower a n) (TensorPower b n)) lB)
          (TensorPower r n)).symm := by
      rw [initialPureVector_state]
      rfl

/-- Bob's marginal of the regrouped converse input is the product of the IID
source `B` marginal and Bob's input-ebit marginal. -/
theorem converseInputPureVector_marginalB :
    C.converseInputPureVector.state.marginalB =
      (stateMergingBlockSource psi n).state.marginalA.marginalB.prod
        (State.maximallyEntangled C.inputEbitPairing).marginalB := by
  apply State.ext
  ext i j
  simp [converseInputPureVector, initialPureVector,
    stateMergingConverseInputEquiv, stateMergingInputEquiv,
    PureVector.reindex_state, PureVector.prod_state, State.reindex,
    State.prod, State.marginalA, State.marginalB, partialTraceA, partialTraceB,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  simpa only [PureVector.maximallyEntangled_amp] using
    (sum_sum_sum_mul_eq_mul_sum_sum_sum
      (fun x x_2 =>
        (stateMergingBlockSource psi n).amp ((x, i.1), x_2) *
          star ((stateMergingBlockSource psi n).amp ((x, j.1), x_2)))
      (fun x_1 =>
        (PureVector.maximallyEntangled C.inputEbitPairing).amp (x_1, i.2) *
          star ((PureVector.maximallyEntangled C.inputEbitPairing).amp (x_1, j.2))))

/-- HOW input-entanglement identity `E_in = n S(B) + log K`. -/
theorem initialBobEntanglement :
    C.converseInputPureVector.entanglementEntropy =
      n * psi.state.marginalA.marginalB.vonNeumann +
        log2 (Fintype.card kA : ℝ) := by
  rw [PureVector.entanglementEntropy, C.converseInputPureVector_marginalB]
  calc
    ((stateMergingBlockSource psi n).state.marginalA.marginalB.prod
        (State.maximallyEntangled C.inputEbitPairing).marginalB).vonNeumann =
        (stateMergingBlockSource psi n).state.marginalA.marginalB.vonNeumann +
          (State.maximallyEntangled C.inputEbitPairing).marginalB.vonNeumann := by
      rw [State.vonNeumann_prod]
    _ = n * psi.state.marginalA.marginalB.vonNeumann +
          (State.maximallyEntangled C.inputEbitPairing).marginalB.vonNeumann := by
      rw [stateMergingBlockSource_marginalB_eq_tensorPower,
        State.vonNeumann_tensorPower]
    _ = n * psi.state.marginalA.marginalB.vonNeumann +
          (PureVector.maximallyEntangled C.inputEbitPairing).state.marginalB.vonNeumann := by
      rfl
    _ = n * psi.state.marginalA.marginalB.vonNeumann +
          log2 (Fintype.card kA : ℝ) := by
      rw [← State.pureVector_marginalA_vonNeumann_eq_marginalB
        (PureVector.maximallyEntangled C.inputEbitPairing),
        PureVector.maximallyEntangled_marginalA,
        State.vonNeumann_maximallyMixed]

/-- The normalized pure vector underlying the ideal state-merging target. -/
def targetPureVector :
    PureVector
      (Prod
        (Prod lA (Prod (Prod (TensorPower a n) (TensorPower b n)) lB))
        (TensorPower r n)) :=
  ((stateMergingBlockSource psi n).prod
      (PureVector.maximallyEntangled C.outputEbitPairing)).reindex
    (stateMergingTargetEquiv
      (TensorPower a n) (TensorPower b n) (TensorPower r n) lA lB)

@[simp]
theorem targetPureVector_state : C.targetPureVector.state = C.targetState := by
  rw [targetPureVector, targetState, PureVector.reindex_state, PureVector.prod_state]
  rfl

/-- Tracing the ideal target down to Bob gives the product of the transferred
IID source and Bob's output-ebit marginal. -/
theorem targetPureVector_marginalA_marginalB :
    C.targetPureVector.state.marginalA.marginalB =
      (stateMergingBlockSource psi n).state.marginalA.prod
        (State.maximallyEntangled C.outputEbitPairing).marginalB := by
  apply State.ext
  ext i j
  simp [targetPureVector, stateMergingTargetEquiv, PureVector.reindex_state,
    PureVector.prod_state, State.reindex, State.prod, State.marginalA,
    State.marginalB, partialTraceA, partialTraceB, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  simpa only [PureVector.maximallyEntangled_amp] using
    (sum_sum_mul_eq_mul_sum
      (fun x =>
        (stateMergingBlockSource psi n).amp (i.1, x) *
          star ((stateMergingBlockSource psi n).amp (j.1, x)))
      (fun x =>
        (PureVector.maximallyEntangled C.outputEbitPairing).amp (x, i.2) *
          star ((PureVector.maximallyEntangled C.outputEbitPairing).amp (x, j.2))))

/-- The ideal target in the output order of the reference-lifted LOCC channel. -/
def converseTargetPureVector :
    PureVector
      (Prod
        (Prod lA (TensorPower r n))
        (Prod (Prod (TensorPower a n) (TensorPower b n)) lB)) :=
  C.targetPureVector.reindex
    (stateMergingConverseOutputEquiv
      lA (Prod (Prod (TensorPower a n) (TensorPower b n)) lB)
      (TensorPower r n)).symm

@[simp]
theorem converseTargetPureVector_state :
    C.converseTargetPureVector.state =
      C.targetState.reindex
        (stateMergingConverseOutputEquiv
          lA (Prod (Prod (TensorPower a n) (TensorPower b n)) lB)
          (TensorPower r n)).symm := by
  simp [converseTargetPureVector, targetPureVector_state, PureVector.reindex_state]

/-- The fidelity deficit of the lifted HOW output is exactly the protocol's
computed fidelity error. -/
theorem converseLOCC_fidelityError :
    1 - (C.converseLOCC.toChannel.applyState C.converseInputPureVector.state).squaredFidelity
        C.converseTargetPureVector.state =
      C.fidelityError := by
  rw [C.converseLOCC_applyState, C.converseTargetPureVector_state,
    squaredFidelity_reindex]
  rfl

/-- Bob's marginal of the regrouped ideal target. -/
theorem converseTargetPureVector_marginalB :
    C.converseTargetPureVector.state.marginalB =
      (stateMergingBlockSource psi n).state.marginalA.prod
        (State.maximallyEntangled C.outputEbitPairing).marginalB := by
  rw [converseTargetPureVector, PureVector.reindex_state,
    State.reindex_stateMergingConverseOutputEquiv_symm_marginalB]
  exact C.targetPureVector_marginalA_marginalB

/-- Entanglement of the ideal target is `n S(AB) + log L`. -/
theorem targetBobEntanglement :
    C.converseTargetPureVector.entanglementEntropy =
      n * psi.state.marginalA.vonNeumann + log2 (Fintype.card lA : ℝ) := by
  rw [PureVector.entanglementEntropy, C.converseTargetPureVector_marginalB]
  calc
    ((stateMergingBlockSource psi n).state.marginalA.prod
        (State.maximallyEntangled C.outputEbitPairing).marginalB).vonNeumann =
        (stateMergingBlockSource psi n).state.marginalA.vonNeumann +
          (State.maximallyEntangled C.outputEbitPairing).marginalB.vonNeumann := by
      rw [State.vonNeumann_prod]
    _ = n * psi.state.marginalA.vonNeumann +
          (State.maximallyEntangled C.outputEbitPairing).marginalB.vonNeumann := by
      rw [stateMergingBlockSource_marginalA_eq_tensorPower]
      change
        ((psi.state.marginalA.tensorPower n).reindex
            (tensorPowerProdEquiv a b n)).vonNeumann +
          (State.maximallyEntangled C.outputEbitPairing).marginalB.vonNeumann =
        n * psi.state.marginalA.vonNeumann +
          (State.maximallyEntangled C.outputEbitPairing).marginalB.vonNeumann
      rw [State.vonNeumann_reindex, State.vonNeumann_tensorPower]
    _ = n * psi.state.marginalA.vonNeumann +
          (PureVector.maximallyEntangled C.outputEbitPairing).state.marginalB.vonNeumann := by
      rfl
    _ = n * psi.state.marginalA.vonNeumann + log2 (Fintype.card lA : ℝ) := by
      rw [← State.pureVector_marginalA_vonNeumann_eq_marginalB
        (PureVector.maximallyEntangled C.outputEbitPairing),
        PureVector.maximallyEntangled_marginalA,
        State.vonNeumann_maximallyMixed]

include C

/-- The Bob output dimension in HOW's Fannes term is
`log L + n log d_A + n log d_B`. -/
theorem log2_converseBobOutput_card :
    log2
        (Fintype.card
          (Prod (Prod (TensorPower a n) (TensorPower b n)) lB) : Real) =
      n * log2 (Fintype.card a : Real) +
        n * log2 (Fintype.card b : Real) +
          log2 (Fintype.card lA : Real) := by
  letI : Nonempty a := ⟨(Classical.choice psi.state.nonempty).1.1⟩
  letI : Nonempty b := ⟨(Classical.choice psi.state.nonempty).1.2⟩
  letI : Nonempty lB := ⟨C.outputEbitPairing (Classical.choice inferInstance)⟩
  have ha : 0 < (Fintype.card (TensorPower a n) : Real) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hb : 0 < (Fintype.card (TensorPower b n) : Real) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hl : 0 < (Fintype.card lB : Real) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hcardL : Fintype.card lB = Fintype.card lA :=
    Fintype.card_congr C.outputEbitPairing.symm
  rw [Fintype.card_prod, Fintype.card_prod, Nat.cast_mul, Nat.cast_mul,
    log2_mul_of_pos (mul_pos ha hb) hl, log2_mul_of_pos ha hb,
    State.log2_tensorPower_card, State.log2_tensorPower_card, hcardL]

/-- The physical positive branches of the lifted protocol obey HOW's averaged
Bob-marginal trace-distance bound. -/
theorem converseLOCC_average_marginalB_traceNormDistance_le :
    (∑ j : C.converseLOCC.jointPositiveSupport C.converseInputPureVector,
      (C.converseLOCC.jointPositiveBranchProbability C.converseInputPureVector j : Real) *
        (C.converseLOCC.finalNormalizedBranch C.converseInputPureVector j).state.marginalB.traceNormDistance
          C.converseTargetPureVector.state.marginalB) ≤
      2 * Real.sqrt C.fidelityError := by
  have h :=
    C.converseLOCC.sum_jointPositiveBranchProbability_mul_marginalB_traceNormDistance_le
      C.converseInputPureVector C.converseTargetPureVector
  rw [C.converseLOCC_fidelityError] at h
  exact h

/-- Applying HOW's Fannes modulus branchwise and Jensen's inequality controls
the average output-entanglement deviation from the ideal target. -/
theorem converseLOCC_average_abs_entanglement_sub_target_le :
    (∑ j : C.converseLOCC.jointPositiveSupport C.converseInputPureVector,
      (C.converseLOCC.jointPositiveBranchProbability C.converseInputPureVector j : Real) *
        |(C.converseLOCC.finalNormalizedBranch C.converseInputPureVector j).entanglementEntropy -
          C.converseTargetPureVector.entanglementEntropy|) ≤
      log2
          (Fintype.card
            (Prod (Prod (TensorPower a n) (TensorPower b n)) lB) : Real) *
        howFannesEta (2 * Real.sqrt C.fidelityError) := by
  have hgeneric :=
    C.converseLOCC.sum_jointPositiveBranchProbability_mul_abs_entanglement_sub_target_le
      C.converseInputPureVector C.converseTargetPureVector
  have hmono := howFannesEta_mono
    (Finset.sum_nonneg fun j _ =>
      mul_nonneg (NNReal.coe_nonneg _) (State.traceNormDistance_nonneg _ _))
    C.converseLOCC_average_marginalB_traceNormDistance_le
  exact hgeneric.trans
    (mul_le_mul_of_nonneg_left hmono (log2_nat_cast_nonneg _))

/-- HOW's unnormalized finite-block converse inequality, before division by
the positive block length. -/
theorem conditionalEntropy_predivision_le_netEntanglementNumerator :
    (n : Real) * psi.state.marginalA.conditionalEntropy -
        (log2 (Fintype.card lA : Real) +
          (n : Real) * log2 (Fintype.card a : Real) +
          (n : Real) * log2 (Fintype.card b : Real)) *
          howFannesEta (2 * Real.sqrt C.fidelityError) ≤
      log2 (Fintype.card kA : Real) - log2 (Fintype.card lA : Real) := by
  let L := C.converseLOCC
  let input := C.converseInputPureVector
  let target := C.converseTargetPureVector
  let q : L.jointPositiveSupport input → NNReal :=
    fun j => L.jointPositiveBranchProbability input j
  have hqReal : ∑ j, (q j : Real) = 1 := by
    have hq := L.sum_jointPositiveBranchProbability_eq_one input
    simpa [q, NNReal.coe_sum, NNReal.coe_one] using
      congrArg (fun x : NNReal => (x : Real)) hq
  have hpoint (j : L.jointPositiveSupport input) :
      target.entanglementEntropy -
          |(L.finalNormalizedBranch input j).entanglementEntropy -
            target.entanglementEntropy| ≤
        (L.finalNormalizedBranch input j).entanglementEntropy := by
    have h := neg_abs_le
      ((L.finalNormalizedBranch input j).entanglementEntropy -
        target.entanglementEntropy)
    linarith
  have htargetSum :
      (∑ j, (q j : Real) * target.entanglementEntropy) =
        target.entanglementEntropy := by
    calc
      (∑ j, (q j : Real) * target.entanglementEntropy) =
          target.entanglementEntropy * ∑ j, (q j : Real) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = target.entanglementEntropy := by rw [hqReal, mul_one]
  have hlower :
      target.entanglementEntropy -
          (∑ j, (q j : Real) *
            |(L.finalNormalizedBranch input j).entanglementEntropy -
              target.entanglementEntropy|) ≤
        L.refinedBranchAverageEntanglement input := by
    rw [OneWayLOCC.refinedBranchAverageEntanglement]
    calc
      target.entanglementEntropy -
          (∑ j, (q j : Real) *
            |(L.finalNormalizedBranch input j).entanglementEntropy -
              target.entanglementEntropy|) =
          ∑ j, (q j : Real) *
            (target.entanglementEntropy -
              |(L.finalNormalizedBranch input j).entanglementEntropy -
                target.entanglementEntropy|) := by
        symm
        calc
          (∑ j, (q j : Real) *
              (target.entanglementEntropy -
                |(L.finalNormalizedBranch input j).entanglementEntropy -
                  target.entanglementEntropy|)) =
              ∑ j, ((q j : Real) * target.entanglementEntropy -
                (q j : Real) *
                  |(L.finalNormalizedBranch input j).entanglementEntropy -
                    target.entanglementEntropy|) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = (∑ j, (q j : Real) * target.entanglementEntropy) -
              ∑ j, (q j : Real) *
                |(L.finalNormalizedBranch input j).entanglementEntropy -
                  target.entanglementEntropy| := by rw [Finset.sum_sub_distrib]
          _ = target.entanglementEntropy -
              ∑ j, (q j : Real) *
                |(L.finalNormalizedBranch input j).entanglementEntropy -
                  target.entanglementEntropy| := by rw [htargetSum]
      _ ≤ ∑ j, (q j : Real) *
          (L.finalNormalizedBranch input j).entanglementEntropy := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hpoint j) (NNReal.coe_nonneg _)
      _ = ∑ j : L.jointPositiveSupport input,
          (L.jointPositiveBranchProbability input j : Real) *
            (L.finalNormalizedBranch input j).entanglementEntropy := by rfl
  have hdeviation := C.converseLOCC_average_abs_entanglement_sub_target_le
  have hmonotone := L.average_pure_entanglement_le input
  have hchain :
      target.entanglementEntropy -
          log2
              (Fintype.card
                (Prod (Prod (TensorPower a n) (TensorPower b n)) lB) : Real) *
            howFannesEta (2 * Real.sqrt C.fidelityError) ≤
        input.entanglementEntropy := by
    linarith
  rw [show target.entanglementEntropy =
      n * psi.state.marginalA.vonNeumann + log2 (Fintype.card lA : Real) by
        exact C.targetBobEntanglement,
    show input.entanglementEntropy =
      n * psi.state.marginalA.marginalB.vonNeumann +
        log2 (Fintype.card kA : Real) by exact C.initialBobEntanglement,
    C.log2_converseBobOutput_card] at hchain
  rw [State.conditionalEntropy_eq]
  linarith

private theorem how_predivision_to_netEntanglementRate
    (H eta outputEbitExponent logDimA logDimB : Real)
    (hn : 0 < n) (heta : 0 <= eta)
    (houtput :
      log2 (Fintype.card lA : Real) <= outputEbitExponent * (n : Real))
    (hpre :
      (n : Real) * H -
          (log2 (Fintype.card lA : Real) +
            (n : Real) * logDimA + (n : Real) * logDimB) * eta <=
        log2 (Fintype.card kA : Real) - log2 (Fintype.card lA : Real)) :
    H - (outputEbitExponent + logDimA + logDimB) * eta <=
      C.netEntanglementRate := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hscaled := mul_le_mul_of_nonneg_right houtput heta
  rw [netEntanglementRate, if_neg hn_ne, le_div_iff₀ hnR]
  nlinarith

/-- HOW's finite-block converse bound in the protocol's normalized net-rate
coordinates.  The only size input is the uniform exponential bound on the
output ebit rank that is part of asymptotic state-merging achievability. -/
theorem conditionalEntropy_sub_howRemainder_le_netEntanglementRate
    (outputEbitExponent : Real) (hn : 0 < n)
    (houtput :
      log2 (Fintype.card lA : Real) ≤ outputEbitExponent * (n : Real)) :
    psi.state.marginalA.conditionalEntropy -
        (outputEbitExponent + log2 (Fintype.card a : Real) +
          log2 (Fintype.card b : Real)) *
          howFannesEta (2 * Real.sqrt C.fidelityError) ≤
      C.netEntanglementRate := by
  exact how_predivision_to_netEntanglementRate
    C
    psi.state.marginalA.conditionalEntropy
    (howFannesEta (2 * Real.sqrt C.fidelityError))
    outputEbitExponent
    (log2 (Fintype.card a : Real))
    (log2 (Fintype.card b : Real))
    hn
    (howFannesEta_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg C.fidelityError)))
    houtput
    C.conditionalEntropy_predivision_le_netEntanglementNumerator

omit C

end StateMergingBlockProtocol

namespace PureVector

/-- The original HOW/Fannes converse for the explicitly exponent-restricted
achievable-rate predicate.  The canonical unrestricted converse is proved
separately by the dimension-independent smooth-min-entropy route. -/
theorem conditionalEntropy_le_of_isAchievableStateMergingRateWithOutputEbitExponent
    (psi : PureVector (Prod (Prod a b) r)) (R : Real)
    (hR :
      IsAchievableStateMergingRateWithOutputEbitExponent.{u, v, w, x, y, z, p, q}
        psi R) :
    psi.state.marginalA.conditionalEntropy ≤ R := by
  by_contra hcontra
  push Not at hcontra
  obtain ⟨outputEbitExponent, houtputEbitExponent, hR⟩ := hR
  let H := psi.state.marginalA.conditionalEntropy
  let slack := (H - R) / 3
  let coefficient := outputEbitExponent + log2 (Fintype.card a : Real) +
    log2 (Fintype.card b : Real)
  have hslack : 0 < slack := by
    dsimp only [slack, H]
    linarith
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    exact add_nonneg
      (add_nonneg houtputEbitExponent (log2_nat_cast_nonneg _))
      (log2_nat_cast_nonneg _)
  have hlimit :
      Tendsto (fun t : Real => coefficient * howFannesEta t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul tendsto_howFannesEta_nhdsWithin_zero_right)
  have heventually : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      coefficient * howFannesEta t < slack := by
    have hball : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
        coefficient * howFannesEta t ∈ Metric.ball (0 : Real) slack :=
      hlimit.eventually (Metric.ball_mem_nhds _ hslack)
    filter_upwards [hball] with t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    exact lt_of_le_of_lt (le_abs_self _) ht
  have hmem : {t : Real | coefficient * howFannesEta t < slack} ∈
      nhdsWithin 0 (Set.Ioi 0) := heventually
  rw [Metric.mem_nhdsWithin_iff] at hmem
  obtain ⟨radius, hradius, hradiusSub⟩ := hmem
  let t₀ := min radius 1 / 2
  have ht₀ : 0 < t₀ := by
    dsimp only [t₀]
    exact div_pos (lt_min hradius (by norm_num)) (by norm_num)
  have ht₀Radius : t₀ < radius := by
    dsimp only [t₀]
    nlinarith [min_le_left radius 1]
  have ht₀Small : coefficient * howFannesEta t₀ < slack := by
    apply hradiusSub
    constructor
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht₀]
      exact ht₀Radius
    · exact ht₀
  let epsilon := (t₀ / 2) ^ 2
  have hepsilon : 0 < epsilon := sq_pos_of_pos (div_pos ht₀ (by norm_num))
  obtain ⟨N, hN, hcodes⟩ := hR slack hslack epsilon hepsilon
  obtain ⟨kA, kAFintype, kADecidableEq, kANonempty,
    kB, kBFintype, kBDecidableEq,
    lA, lAFintype, lADecidableEq, lANonempty,
    lB, lBFintype, lBDecidableEq,
    outcome, outcomeFintype, outcomeDecidableEq, outcomeNonempty,
    C, hrate, herror, houtput⟩ := hcodes N le_rfl
  letI : Fintype kA := kAFintype
  letI : DecidableEq kA := kADecidableEq
  letI : Nonempty kA := kANonempty
  letI : Fintype kB := kBFintype
  letI : DecidableEq kB := kBDecidableEq
  letI : Fintype lA := lAFintype
  letI : DecidableEq lA := lADecidableEq
  letI : Nonempty lA := lANonempty
  letI : Fintype lB := lBFintype
  letI : DecidableEq lB := lBDecidableEq
  letI : Fintype outcome := outcomeFintype
  letI : DecidableEq outcome := outcomeDecidableEq
  letI : Nonempty outcome := outcomeNonempty
  have hNPositive : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hsqrtEpsilon : Real.sqrt epsilon = t₀ / 2 := by
    dsimp only [epsilon]
    exact Real.sqrt_sq (le_of_lt (div_pos ht₀ (by norm_num)))
  have hargument : 2 * Real.sqrt C.fidelityError ≤ t₀ := by
    have hsqrt := Real.sqrt_le_sqrt herror
    rw [hsqrtEpsilon] at hsqrt
    linarith
  have heta :
      howFannesEta (2 * Real.sqrt C.fidelityError) ≤ howFannesEta t₀ :=
    howFannesEta_mono
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg C.fidelityError)) hargument
  have hremainder :
      coefficient * howFannesEta (2 * Real.sqrt C.fidelityError) < slack :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left heta hcoefficient) ht₀Small
  have hfinite :=
    C.conditionalEntropy_sub_howRemainder_le_netEntanglementRate
      outputEbitExponent hNPositive houtput
  dsimp only [H, coefficient] at hfinite hremainder
  dsimp only [slack, H] at hrate hremainder ⊢
  linarith

end PureVector

end

end QIT
