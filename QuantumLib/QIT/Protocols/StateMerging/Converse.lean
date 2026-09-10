/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Protocols.LOCC.ReferenceLift
public import QuantumLib.QIT.Protocols.StateMerging.Core
public import QuantumLib.QIT.Protocols.StateMerging.DistanceAveraging
public import QuantumLib.QIT.Information.Entropy.EntropyTensorPower
public import QuantumLib.QIT.Information.Entropy.MaximallyMixed
public import QuantumLib.QIT.Information.Fannes
public import QuantumLib.QIT.Asymptotic.AEP
import QuantumLib.QIT.OneShot.SmoothNormalizedExtension

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

/-- A double sum whose summand factors as `f r * g k` splits into a product of
sums. -/
private theorem sum_sum_mul_eq_mul_sum
    {K R : Type*} [Fintype K] [Fintype R]
    (f : R → ℂ) (g : K → ℂ) :
    (∑ k : K, ∑ r : R, f r * g k) = (∑ r : R, f r) * ∑ k : K, g k := by
  rw [Finset.sum_comm, ← Fintype.sum_mul_sum]

/-- The same factorization with an extra outer index carried by the left
factor. -/
private theorem sum_sum_sum_mul_eq_mul_sum_sum_sum
    {A K R : Type*} [Fintype A] [Fintype K] [Fintype R]
    (f : A → R → ℂ) (g : K → ℂ) :
    (∑ a : A, ∑ k : K, ∑ r : R, f a r * g k) =
      (∑ a : A, ∑ r : R, f a r) * ∑ k : K, g k := by
  simp_rw [sum_sum_mul_eq_mul_sum]
  rw [← Finset.sum_mul]

namespace OneWayLOCC

variable {A : Type ua} {A' : Type ua'} {B : Type ub} {B' : Type ub'} {X : Type ux}
variable [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
variable [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype X]

/-- Fannes continuity applied to one physical positive LOCC branch and a pure target. -/
theorem finalNormalizedBranch_entanglement_sub_target_le_howFannes
    (L : OneWayLOCC A A' B B' X) (input : Ket (A × B))
    (target : Ket (A' × B')) (j : L.jointPositiveSupport input) :
    |(L.finalNormalizedBranch input j).entanglementEntropy - target.entanglementEntropy| ≤
      log2 (Fintype.card B' : ℝ) *
        howFannesEta
          ((L.finalNormalizedBranch input j).state.traceLeft.traceNormDistance
            target.state.traceLeft) := by
  exact MState.vonNeumann_dist_le_howFannes
    (L.finalNormalizedBranch input j).state.traceLeft target.state.traceLeft

/-- Jensen-averaged Fannes continuity for the physical positive branches of a
finite one-way LOCC protocol. -/
theorem sum_jointPositiveBranchProbability_mul_abs_entanglement_sub_target_le
    (L : OneWayLOCC A A' B B' X) (input : Ket (A × B))
    (target : Ket (A' × B')) :
    (∑ j : L.jointPositiveSupport input,
      (L.jointPositiveBranchProbability input j : ℝ) *
        |(L.finalNormalizedBranch input j).entanglementEntropy -
          target.entanglementEntropy|) ≤
      log2 (Fintype.card B' : ℝ) *
        howFannesEta
          (∑ j : L.jointPositiveSupport input,
            (L.jointPositiveBranchProbability input j : ℝ) *
              (L.finalNormalizedBranch input j).state.traceLeft.traceNormDistance
                target.state.traceLeft) := by
  have hq := L.sum_jointPositiveBranchProbability_eq_one input
  have hpointSum :
      (∑ j : L.jointPositiveSupport input,
        (L.jointPositiveBranchProbability input j : ℝ) *
          |(L.finalNormalizedBranch input j).entanglementEntropy -
            target.entanglementEntropy|) ≤
        log2 (Fintype.card B' : ℝ) *
          ∑ j : L.jointPositiveSupport input,
            (L.jointPositiveBranchProbability input j : ℝ) *
              howFannesEta
                ((L.finalNormalizedBranch input j).state.traceLeft.traceNormDistance
                  target.state.traceLeft) := by
    calc
      (∑ j : L.jointPositiveSupport input,
          (L.jointPositiveBranchProbability input j : ℝ) *
            |(L.finalNormalizedBranch input j).entanglementEntropy -
              target.entanglementEntropy|) ≤
          ∑ j : L.jointPositiveSupport input,
            (L.jointPositiveBranchProbability input j : ℝ) *
              (log2 (Fintype.card B' : ℝ) *
                howFannesEta
                  ((L.finalNormalizedBranch input j).state.traceLeft.traceNormDistance
                    target.state.traceLeft)) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left
          (L.finalNormalizedBranch_entanglement_sub_target_le_howFannes input target j)
          (NNReal.coe_nonneg _)
      _ = log2 (Fintype.card B' : ℝ) *
          ∑ j : L.jointPositiveSupport input,
            (L.jointPositiveBranchProbability input j : ℝ) *
              howFannesEta
                ((L.finalNormalizedBranch input j).state.traceLeft.traceNormDistance
                  target.state.traceLeft) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hjensen := howFannesEta_weighted_le
    (fun j : L.jointPositiveSupport input => L.jointPositiveBranchProbability input j)
    (fun j => (L.finalNormalizedBranch input j).state.traceLeft.traceNormDistance
      target.state.traceLeft)
    hq (fun j => MState.traceNormDistance_nonneg _ _)
  exact hpointSum.trans
    (mul_le_mul_of_nonneg_left hjensen (log2_nat_cast_nonneg _))

end OneWayLOCC

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable {psi : Ket ((a × b) × r)} {n : ℕ}
variable {kA : Type x} {kB : Type y} {lA : Type z} {lB : Type p}
variable {outcome : Type q}
variable [Fintype kA] [DecidableEq kA] [Nonempty kA]
variable [Fintype kB] [DecidableEq kB]
variable [Fintype lA] [DecidableEq lA] [Nonempty lA]
variable [Fintype lB] [DecidableEq lB]
variable [Fintype outcome] [DecidableEq outcome] [Nonempty outcome]

/-- The grouped `A^n B^n` marginal of the state-merging source is the
bipartite tensor power of the one-copy `AB` marginal. -/
theorem stateMergingBlockSource_traceRight_eq_tensorPower
    (psi : Ket ((a × b) × r)) (n : ℕ) :
    (stateMergingBlockSource psi n).state.traceRight =
      psi.state.traceRight.tensorPowerBipartite n := by
  simpa [stateMergingBlockSource, tensorPowerProdProdEquiv,
    Ket.tensorPowerTripartiteGrouped, Ket.reindex_state,
    Ket.tensorPower_state] using
    Ket.tensorPowerTripartiteGrouped_marginalAB
      (a := a) (b := b) (c := r) psi n

/-- The grouped `A^n R^n` marginal of the state-merging source is the
bipartite tensor power of the one-copy `AR` marginal.  This is the source
identification used by the smooth-min-entropy converse. -/
theorem stateMergingBlockSource_marginalAC_eq_tensorPower
    (psi : Ket ((a × b) × r)) (n : ℕ) :
    (stateMergingBlockSource psi n).state.marginalAC =
      psi.state.marginalAC.tensorPowerBipartite n := by
  simpa [stateMergingBlockSource, tensorPowerProdProdEquiv,
    Ket.tensorPowerTripartiteGrouped, Ket.reindex_state,
    Ket.tensorPower_state] using
    Ket.tensorPowerTripartiteGrouped_marginalAC
      (a := a) (b := b) (c := r) psi n

/-- The `B^n` marginal of the grouped state-merging source is the tensor
power of the one-copy `B` marginal. -/
theorem stateMergingBlockSource_traceLeft_eq_tensorPower
    (psi : Ket ((a × b) × r)) (n : ℕ) :
    (stateMergingBlockSource psi n).state.traceRight.traceLeft =
      psi.state.traceRight.traceLeft.tensorPower n := by
  rw [stateMergingBlockSource_traceRight_eq_tensorPower]
  simpa using MState.tensorPowerBipartite_traceLeft
    (rho := psi.state.traceRight) n

namespace StateMergingBlockProtocol

/-- Decidable equality on the protocol's output register, assembled from the
factor instances so that it is definitionally the product instance. -/
local instance stateMergingConverseOutputDecidableEq :
    DecidableEq
      ((lA × ((TensorPower a n × TensorPower b n) × lB)) ×
        TensorPower r n) :=
  @instDecidableEqProd _ _
    (@instDecidableEqProd _ _ inferInstance
      (@instDecidableEqProd _ _
        (@instDecidableEqProd _ _
          (tensorPowerDecidableEq n) (tensorPowerDecidableEq n))
        inferInstance))
    (tensorPowerDecidableEq n)

variable (C : StateMergingBlockProtocol psi n kA kB lA lB outcome)

/-- The normalized ket underlying the physical state-merging input. -/
def initialKet :
    Ket
      (((TensorPower a n × kA) × (TensorPower b n × kB)) ×
        TensorPower r n) :=
  ((stateMergingBlockSource psi n).prod
      (Ket.maximallyEntangled C.inputEbitPairing)).reindex
    (stateMergingInputEquiv
      (TensorPower a n) (TensorPower b n) (TensorPower r n) kA kB)

@[simp]
theorem initialKet_state : C.initialKet.state = C.initialState := by
  rw [initialKet, initialState, Ket.reindex_state, Ket.prod_state]
  rfl

/-- The input ket under the converse bipartition
`(Alice, Reference) | Bob`. -/
def converseInputKet :
    Ket
      (((TensorPower a n × kA) × TensorPower r n) ×
        (TensorPower b n × kB)) :=
  C.initialKet.reindex
    (prodABCToACBEquiv
      (TensorPower a n × kA)
      (TensorPower b n × kB)
      (TensorPower r n))

/-- The physical state-merging one-way LOCC operation lifted by the untouched
IID reference and grouped with Alice for the HOW converse. -/
def converseLOCC :
    OneWayLOCC
      ((TensorPower a n × kA) × TensorPower r n)
      (lA × TensorPower r n)
      (TensorPower b n × kB)
      ((TensorPower a n × TensorPower b n) × lB)
      outcome :=
  C.locc.prodIdRight (R := TensorPower r n)

set_option maxRecDepth 4000 in
/-- The lifted LOCC output is the operational output with the untouched
reference regrouped onto Alice's side. -/
theorem converseLOCC_applyState :
    C.converseLOCC.toChannel C.converseInputKet.state =
      C.outputState.reindex
        (prodABCToACBEquiv
          lA ((TensorPower a n × TensorPower b n) × lB)
          (TensorPower r n)) := by
  have h := OneWayLOCC.prodIdRight_applyState_reindex_pure
    (R := TensorPower r n) C.locc C.initialKet
  calc
    C.converseLOCC.toChannel C.converseInputKet.state =
        (C.locc.prodIdRight (R := TensorPower r n)).toChannel
          (C.initialKet.state.reindex
            (prodABCToACBEquiv
              (TensorPower a n × kA)
              (TensorPower b n × kB)
              (TensorPower r n))) := by
      rw [converseLOCC, converseInputKet, Ket.reindex_state]
    _ = MState.reindex ((C.locc.toChannel.prod (CPTPOp.id (dIn := TensorPower r n)))
          C.initialKet.state)
          (prodABCToACBEquiv
            lA ((TensorPower a n × TensorPower b n) × lB)
            (TensorPower r n)) := h
    _ = C.outputState.reindex
        (prodABCToACBEquiv
          lA ((TensorPower a n × TensorPower b n) × lB)
          (TensorPower r n)) := by
      rw [initialKet_state]
      rfl

/-- Bob's marginal of the regrouped converse input is the product of the IID
source `B` marginal and Bob's input-ebit marginal. -/
theorem converseInputKet_traceLeft :
    C.converseInputKet.state.traceLeft =
      (stateMergingBlockSource psi n).state.traceRight.traceLeft.prod
        (MState.maximallyEntangled C.inputEbitPairing).traceLeft := by
  apply MState.ext
  ext i j
  simp [converseInputKet, initialKet,
    prodABCToACBEquiv, stateMergingInputEquiv,
    Ket.reindex_state, Ket.prod_state,
    Matrix.traceLeft, Matrix.traceRight,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  simpa only [Ket.maximallyEntangled_vec, starRingEnd_apply] using
    (sum_sum_sum_mul_eq_mul_sum_sum_sum
      (fun x x_2 =>
        (stateMergingBlockSource psi n).vec ((x, i.1), x_2) *
          star ((stateMergingBlockSource psi n).vec ((x, j.1), x_2)))
      (fun x_1 =>
        (Ket.maximallyEntangled C.inputEbitPairing).vec (x_1, i.2) *
          star ((Ket.maximallyEntangled C.inputEbitPairing).vec (x_1, j.2))))

/-- HOW input-entanglement identity `E_in = n S(B) + log K`. -/
theorem initialBobEntanglement :
    C.converseInputKet.entanglementEntropy =
      n * psi.state.traceRight.traceLeft.vonNeumann +
        log2 (Fintype.card kA : ℝ) := by
  rw [Ket.entanglementEntropy, C.converseInputKet_traceLeft]
  calc
    ((stateMergingBlockSource psi n).state.traceRight.traceLeft.prod
        (MState.maximallyEntangled C.inputEbitPairing).traceLeft).vonNeumann =
        (stateMergingBlockSource psi n).state.traceRight.traceLeft.vonNeumann +
          (MState.maximallyEntangled C.inputEbitPairing).traceLeft.vonNeumann := by
      rw [MState.vonNeumann_prod]
    _ = n * psi.state.traceRight.traceLeft.vonNeumann +
          (MState.maximallyEntangled C.inputEbitPairing).traceLeft.vonNeumann := by
      rw [stateMergingBlockSource_traceLeft_eq_tensorPower,
        MState.vonNeumann_tensorPower]
    _ = n * psi.state.traceRight.traceLeft.vonNeumann +
          (Ket.maximallyEntangled C.inputEbitPairing).state.traceLeft.vonNeumann := by
      rfl
    _ = n * psi.state.traceRight.traceLeft.vonNeumann +
          log2 (Fintype.card kA : ℝ) := by
      rw [← MState.ket_traceRight_vonNeumann_eq_traceLeft
        (Ket.maximallyEntangled C.inputEbitPairing),
        Ket.maximallyEntangled_traceRight,
        MState.vonNeumann_uniform]

/-- The normalized ket underlying the ideal state-merging target. -/
def targetKet :
    Ket
      ((lA × ((TensorPower a n × TensorPower b n) × lB)) ×
        TensorPower r n) :=
  ((stateMergingBlockSource psi n).prod
      (Ket.maximallyEntangled C.outputEbitPairing)).reindex
    (stateMergingTargetEquiv
      (TensorPower a n) (TensorPower b n) (TensorPower r n) lA lB)

@[simp]
theorem targetKet_state : C.targetKet.state = C.targetState := by
  rw [targetKet, targetState, Ket.reindex_state, Ket.prod_state]
  rfl

/-- Tracing the ideal target down to Bob gives the product of the transferred
IID source and Bob's output-ebit marginal. -/
theorem targetKet_traceRight_traceLeft :
    C.targetKet.state.traceRight.traceLeft =
      (stateMergingBlockSource psi n).state.traceRight.prod
        (MState.maximallyEntangled C.outputEbitPairing).traceLeft := by
  apply MState.ext
  ext i j
  simp [targetKet, stateMergingTargetEquiv, Ket.reindex_state,
    Ket.prod_state,
    Matrix.traceLeft, Matrix.traceRight, Matrix.kroneckerMap_apply]
  simpa only [Ket.maximallyEntangled_vec, starRingEnd_apply] using
    (sum_sum_mul_eq_mul_sum
      (fun x =>
        (stateMergingBlockSource psi n).vec (i.1, x) *
          star ((stateMergingBlockSource psi n).vec (j.1, x)))
      (fun x =>
        (Ket.maximallyEntangled C.outputEbitPairing).vec (x, i.2) *
          star ((Ket.maximallyEntangled C.outputEbitPairing).vec (x, j.2))))

/-- The ideal target in the output order of the reference-lifted LOCC channel. -/
def converseTargetKet :
    Ket
      ((lA × TensorPower r n) ×
        ((TensorPower a n × TensorPower b n) × lB)) :=
  C.targetKet.reindex
    (prodABCToACBEquiv
      lA ((TensorPower a n × TensorPower b n) × lB)
      (TensorPower r n))

@[simp]
theorem converseTargetKet_state :
    C.converseTargetKet.state =
      C.targetState.reindex
        (prodABCToACBEquiv
          lA ((TensorPower a n × TensorPower b n) × lB)
          (TensorPower r n)) := by
  simp [converseTargetKet, targetKet_state, Ket.reindex_state]

/-- The fidelity deficit of the lifted HOW output is exactly the protocol's
computed fidelity error. -/
theorem converseLOCC_fidelityError :
    1 - MState.squaredFidelity (C.converseLOCC.toChannel C.converseInputKet.state)
        C.converseTargetKet.state =
      C.fidelityError := by
  rw [C.converseLOCC_applyState, C.converseTargetKet_state,
    MState.squaredFidelity_reindex]
  rfl

/-- Bob's marginal of the regrouped ideal target. -/
theorem converseTargetKet_traceLeft :
    C.converseTargetKet.state.traceLeft =
      (stateMergingBlockSource psi n).state.traceRight.prod
        (MState.maximallyEntangled C.outputEbitPairing).traceLeft := by
  rw [converseTargetKet, Ket.reindex_state, MState.prodABCToACB_traceLeft,
    MState.marginalBOfABC_eq, MState.marginalAB_eq_traceRight]
  exact C.targetKet_traceRight_traceLeft

/-- Entanglement of the ideal target is `n S(AB) + log L`. -/
theorem targetBobEntanglement :
    C.converseTargetKet.entanglementEntropy =
      n * psi.state.traceRight.vonNeumann + log2 (Fintype.card lA : ℝ) := by
  rw [Ket.entanglementEntropy, C.converseTargetKet_traceLeft]
  calc
    ((stateMergingBlockSource psi n).state.traceRight.prod
        (MState.maximallyEntangled C.outputEbitPairing).traceLeft).vonNeumann =
        (stateMergingBlockSource psi n).state.traceRight.vonNeumann +
          (MState.maximallyEntangled C.outputEbitPairing).traceLeft.vonNeumann := by
      rw [MState.vonNeumann_prod]
    _ = n * psi.state.traceRight.vonNeumann +
          (MState.maximallyEntangled C.outputEbitPairing).traceLeft.vonNeumann := by
      rw [stateMergingBlockSource_traceRight_eq_tensorPower]
      change
        ((psi.state.traceRight.tensorPower n).reindex
            (tensorPowerProdEquiv a b n)).vonNeumann +
          (MState.maximallyEntangled C.outputEbitPairing).traceLeft.vonNeumann =
        n * psi.state.traceRight.vonNeumann +
          (MState.maximallyEntangled C.outputEbitPairing).traceLeft.vonNeumann
      rw [MState.vonNeumann_reindex, MState.vonNeumann_tensorPower]
    _ = n * psi.state.traceRight.vonNeumann +
          (Ket.maximallyEntangled C.outputEbitPairing).state.traceLeft.vonNeumann := by
      rfl
    _ = n * psi.state.traceRight.vonNeumann + log2 (Fintype.card lA : ℝ) := by
      rw [← MState.ket_traceRight_vonNeumann_eq_traceLeft
        (Ket.maximallyEntangled C.outputEbitPairing),
        Ket.maximallyEntangled_traceRight,
        MState.vonNeumann_uniform]

include C

/-- The Bob output dimension in HOW's Fannes term is
`log L + n log d_A + n log d_B`. -/
theorem log2_converseBobOutput_card :
    log2
        (Fintype.card
          ((TensorPower a n × TensorPower b n) × lB) : ℝ) =
      n * log2 (Fintype.card a : ℝ) +
        n * log2 (Fintype.card b : ℝ) +
          log2 (Fintype.card lA : ℝ) := by
  let : Nonempty a := ⟨(Classical.choice psi.state.nonempty).1.1⟩
  let : Nonempty b := ⟨(Classical.choice psi.state.nonempty).1.2⟩
  let : Nonempty lB := ⟨C.outputEbitPairing (Classical.choice inferInstance)⟩
  have ha : 0 < (Fintype.card (TensorPower a n) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hb : 0 < (Fintype.card (TensorPower b n) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hl : 0 < (Fintype.card lB : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hcardL : Fintype.card lB = Fintype.card lA :=
    Fintype.card_congr C.outputEbitPairing.symm
  rw [Fintype.card_prod, Fintype.card_prod, Nat.cast_mul, Nat.cast_mul,
    log2_mul (mul_pos ha hb).ne' hl.ne', log2_mul ha.ne' hb.ne',
    MState.log2_tensorPower_card, MState.log2_tensorPower_card, hcardL]

set_option maxRecDepth 4000 in
/-- The physical positive branches of the lifted protocol obey HOW's averaged
Bob-marginal trace-distance bound. -/
theorem converseLOCC_average_traceLeft_traceNormDistance_le :
    (∑ j : C.converseLOCC.jointPositiveSupport C.converseInputKet,
      (C.converseLOCC.jointPositiveBranchProbability C.converseInputKet j : ℝ) *
        (C.converseLOCC.finalNormalizedBranch C.converseInputKet j).state.traceLeft.traceNormDistance
          C.converseTargetKet.state.traceLeft) ≤
      2 * Real.sqrt C.fidelityError := by
  have h :=
    C.converseLOCC.sum_jointPositiveBranchProbability_mul_traceLeft_traceNormDistance_le
      C.converseInputKet C.converseTargetKet
  rw [C.converseLOCC_fidelityError] at h
  exact h

/-- Applying HOW's Fannes modulus branchwise and Jensen's inequality controls
the average output-entanglement deviation from the ideal target. -/
theorem converseLOCC_average_abs_entanglement_sub_target_le :
    (∑ j : C.converseLOCC.jointPositiveSupport C.converseInputKet,
      (C.converseLOCC.jointPositiveBranchProbability C.converseInputKet j : ℝ) *
        |(C.converseLOCC.finalNormalizedBranch C.converseInputKet j).entanglementEntropy -
          C.converseTargetKet.entanglementEntropy|) ≤
      log2
          (Fintype.card
            ((TensorPower a n × TensorPower b n) × lB) : ℝ) *
        howFannesEta (2 * Real.sqrt C.fidelityError) := by
  have hgeneric :=
    C.converseLOCC.sum_jointPositiveBranchProbability_mul_abs_entanglement_sub_target_le
      C.converseInputKet C.converseTargetKet
  have hmono := howFannesEta_mono
    (Finset.sum_nonneg fun j _ =>
      mul_nonneg (NNReal.coe_nonneg _) (MState.traceNormDistance_nonneg _ _))
    C.converseLOCC_average_traceLeft_traceNormDistance_le
  exact hgeneric.trans
    (mul_le_mul_of_nonneg_left hmono (log2_nat_cast_nonneg _))

/-- HOW's unnormalized finite-block converse inequality, before division by
the positive block length. -/
theorem conditionalEntropy_predivision_le_netEntanglementNumerator :
    (n : ℝ) * psi.state.traceRight.conditionalEntropy -
        (log2 (Fintype.card lA : ℝ) +
          (n : ℝ) * log2 (Fintype.card a : ℝ) +
          (n : ℝ) * log2 (Fintype.card b : ℝ)) *
          howFannesEta (2 * Real.sqrt C.fidelityError) ≤
      log2 (Fintype.card kA : ℝ) - log2 (Fintype.card lA : ℝ) := by
  let L := C.converseLOCC
  let input := C.converseInputKet
  let target := C.converseTargetKet
  let q : L.jointPositiveSupport input → NNReal :=
    fun j => L.jointPositiveBranchProbability input j
  have hqReal : ∑ j, (q j : ℝ) = 1 := by
    have hq := L.sum_jointPositiveBranchProbability_eq_one input
    simpa [q, NNReal.coe_sum, NNReal.coe_one] using
      congrArg (fun x : NNReal => (x : ℝ)) hq
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
      (∑ j, (q j : ℝ) * target.entanglementEntropy) =
        target.entanglementEntropy := by
    calc
      (∑ j, (q j : ℝ) * target.entanglementEntropy) =
          target.entanglementEntropy * ∑ j, (q j : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = target.entanglementEntropy := by rw [hqReal, mul_one]
  have hlower :
      target.entanglementEntropy -
          (∑ j, (q j : ℝ) *
            |(L.finalNormalizedBranch input j).entanglementEntropy -
              target.entanglementEntropy|) ≤
        L.refinedBranchAverageEntanglement input := by
    rw [OneWayLOCC.refinedBranchAverageEntanglement]
    calc
      target.entanglementEntropy -
          (∑ j, (q j : ℝ) *
            |(L.finalNormalizedBranch input j).entanglementEntropy -
              target.entanglementEntropy|) =
          ∑ j, (q j : ℝ) *
            (target.entanglementEntropy -
              |(L.finalNormalizedBranch input j).entanglementEntropy -
                target.entanglementEntropy|) := by
        symm
        calc
          (∑ j, (q j : ℝ) *
              (target.entanglementEntropy -
                |(L.finalNormalizedBranch input j).entanglementEntropy -
                  target.entanglementEntropy|)) =
              ∑ j, ((q j : ℝ) * target.entanglementEntropy -
                (q j : ℝ) *
                  |(L.finalNormalizedBranch input j).entanglementEntropy -
                    target.entanglementEntropy|) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = (∑ j, (q j : ℝ) * target.entanglementEntropy) -
              ∑ j, (q j : ℝ) *
                |(L.finalNormalizedBranch input j).entanglementEntropy -
                  target.entanglementEntropy| := by rw [Finset.sum_sub_distrib]
          _ = target.entanglementEntropy -
              ∑ j, (q j : ℝ) *
                |(L.finalNormalizedBranch input j).entanglementEntropy -
                  target.entanglementEntropy| := by rw [htargetSum]
      _ ≤ ∑ j, (q j : ℝ) *
          (L.finalNormalizedBranch input j).entanglementEntropy := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hpoint j) (NNReal.coe_nonneg _)
      _ = ∑ j : L.jointPositiveSupport input,
          (L.jointPositiveBranchProbability input j : ℝ) *
            (L.finalNormalizedBranch input j).entanglementEntropy := by rfl
  have hdeviation := C.converseLOCC_average_abs_entanglement_sub_target_le
  have hmonotone := L.average_pure_entanglement_le input
  have hchain :
      target.entanglementEntropy -
          log2
              (Fintype.card
                ((TensorPower a n × TensorPower b n) × lB) : ℝ) *
            howFannesEta (2 * Real.sqrt C.fidelityError) ≤
        input.entanglementEntropy := by
    linarith
  rw [show target.entanglementEntropy =
      n * psi.state.traceRight.vonNeumann + log2 (Fintype.card lA : ℝ) by
        exact C.targetBobEntanglement,
    show input.entanglementEntropy =
      n * psi.state.traceRight.traceLeft.vonNeumann +
        log2 (Fintype.card kA : ℝ) by exact C.initialBobEntanglement,
    C.log2_converseBobOutput_card] at hchain
  rw [MState.conditionalEntropy_eq]
  linarith

omit [DecidableEq r] in
private theorem how_predivision_to_netEntanglementRate
    (H eta outputEbitExponent logDimA logDimB : ℝ)
    (hn : 0 < n) (heta : 0 ≤ eta)
    (houtput :
      log2 (Fintype.card lA : ℝ) ≤ outputEbitExponent * (n : ℝ))
    (hpre :
      (n : ℝ) * H -
          (log2 (Fintype.card lA : ℝ) +
            (n : ℝ) * logDimA + (n : ℝ) * logDimB) * eta ≤
        log2 (Fintype.card kA : ℝ) - log2 (Fintype.card lA : ℝ)) :
    H - (outputEbitExponent + logDimA + logDimB) * eta ≤
      C.netEntanglementRate := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hscaled := mul_le_mul_of_nonneg_right houtput heta
  rw [netEntanglementRate, if_neg hn_ne, le_div_iff₀ hnR]
  nlinarith

/-- HOW's finite-block converse bound in the protocol's normalized net-rate
coordinates.  The only size input is the uniform exponential bound on the
output ebit rank that is part of asymptotic state-merging achievability. -/
theorem conditionalEntropy_sub_howRemainder_le_netEntanglementRate
    (outputEbitExponent : ℝ) (hn : 0 < n)
    (houtput :
      log2 (Fintype.card lA : ℝ) ≤ outputEbitExponent * (n : ℝ)) :
    psi.state.traceRight.conditionalEntropy -
        (outputEbitExponent + log2 (Fintype.card a : ℝ) +
          log2 (Fintype.card b : ℝ)) *
          howFannesEta (2 * Real.sqrt C.fidelityError) ≤
      C.netEntanglementRate := by
  exact how_predivision_to_netEntanglementRate
    C
    psi.state.traceRight.conditionalEntropy
    (howFannesEta (2 * Real.sqrt C.fidelityError))
    outputEbitExponent
    (log2 (Fintype.card a : ℝ))
    (log2 (Fintype.card b : ℝ))
    hn
    (howFannesEta_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg C.fidelityError)))
    houtput
    C.conditionalEntropy_predivision_le_netEntanglementNumerator

omit C

end StateMergingBlockProtocol

end
end QIT

namespace Ket

noncomputable section

open QIT
open Filter
universe u v w x y z p q ua ua' ub ub' ux
variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable {psi : Ket ((a × b) × r)} {n : ℕ}
variable {kA : Type x} {kB : Type y} {lA : Type z} {lB : Type p}
variable {outcome : Type q}
variable [Fintype kA] [DecidableEq kA] [Nonempty kA]
variable [Fintype kB] [DecidableEq kB]
variable [Fintype lA] [DecidableEq lA] [Nonempty lA]
variable [Fintype lB] [DecidableEq lB]
variable [Fintype outcome] [DecidableEq outcome] [Nonempty outcome]

/-- The original HOW/Fannes converse for the explicitly exponent-restricted
achievable-rate predicate.  The canonical unrestricted converse is proved
separately by the dimension-independent smooth-min-entropy route. -/
theorem conditionalEntropy_le_of_isAchievableStateMergingRateWithOutputEbitExponent
    (psi : Ket ((a × b) × r)) (R : ℝ)
    (hR :
      IsAchievableStateMergingRateWithOutputEbitExponent.{u, v, w, x, y, z, p, q}
        psi R) :
    psi.state.traceRight.conditionalEntropy ≤ R := by
  by_contra hcontra
  push Not at hcontra
  obtain ⟨outputEbitExponent, houtputEbitExponent, hR⟩ := hR
  let H := psi.state.traceRight.conditionalEntropy
  let slack := (H - R) / 3
  let coefficient := outputEbitExponent + log2 (Fintype.card a : ℝ) +
    log2 (Fintype.card b : ℝ)
  have hslack : 0 < slack := by
    dsimp only [slack, H]
    linarith
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    exact add_nonneg
      (add_nonneg houtputEbitExponent (log2_nat_cast_nonneg _))
      (log2_nat_cast_nonneg _)
  have hlimit :
      Tendsto (fun t : ℝ => coefficient * howFannesEta t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul tendsto_howFannesEta_nhdsWithin_zero_right)
  have heventually : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      coefficient * howFannesEta t < slack := by
    have hball : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
        coefficient * howFannesEta t ∈ Metric.ball (0 : ℝ) slack :=
      hlimit.eventually (Metric.ball_mem_nhds _ hslack)
    filter_upwards [hball] with t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    exact lt_of_le_of_lt (le_abs_self _) ht
  have hmem : {t : ℝ | coefficient * howFannesEta t < slack} ∈
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
  let : Fintype kA := kAFintype
  let : DecidableEq kA := kADecidableEq
  let : Nonempty kA := kANonempty
  let : Fintype kB := kBFintype
  let : DecidableEq kB := kBDecidableEq
  let : Fintype lA := lAFintype
  let : DecidableEq lA := lADecidableEq
  let : Nonempty lA := lANonempty
  let : Fintype lB := lBFintype
  let : DecidableEq lB := lBDecidableEq
  let : Fintype outcome := outcomeFintype
  let : DecidableEq outcome := outcomeDecidableEq
  let : Nonempty outcome := outcomeNonempty
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

end

end Ket

namespace QIT
noncomputable section

open Filter
universe u v w x y z p q ua ua' ub ub' ux
variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable {psi : Ket ((a × b) × r)} {n : ℕ}
variable {kA : Type x} {kB : Type y} {lA : Type z} {lB : Type p}
variable {outcome : Type q}
variable [Fintype kA] [DecidableEq kA] [Nonempty kA]
variable [Fintype kB] [DecidableEq kB]
variable [Fintype lA] [DecidableEq lA] [Nonempty lA]
variable [Fintype lB] [DecidableEq lB]
variable [Fintype outcome] [DecidableEq outcome] [Nonempty outcome]

end

end QIT
