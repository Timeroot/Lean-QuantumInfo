/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Protocols.StateMerging.Converse
public import QuantumLib.QIT.Protocols.LOCC.SmoothConditionalMinEntropy
public import QuantumLib.QIT.OneShot.SmoothEndpoint.Duality
public import QuantumLib.QIT.Protocols.LOCC.Construction
public import QuantumLib.QIT.Core.System
import QuantumLib.QIT.OneShot.SmoothNormalizedExtension

/-!
# Alice's recorded outcomes in the state-merging converse

This module implements the cq-record step in Berta's smooth-min-entropy
converse (`diploma_thesis_berta_08_v1.tex`, lines 730--735, 810--815, and
891--901).  The classical record contains exactly Alice's refined local
instrument outcome.  Bob's conditional channel is trace preserving and is
therefore summed out nonselectively; its Kraus refinement is not exposed as
part of the classical record.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

universe u v w x y z p q

noncomputable section

namespace MEnsemble

open QIT

variable {i : Type u} {s : Type v}
variable [Fintype i] [DecidableEq i] [Fintype s] [DecidableEq s]

/-- The normalized trace distance between cq states with the same classical
distribution is the corresponding weighted branch average. -/
private theorem cqState_normalizedTraceDistance_eq_sum_of_same_probs
    (E F : MEnsemble s i) (hprobs : ∀ j, F.probs j = E.probs j) :
    E.cqState.normalizedTraceDistance F.cqState =
      ∑ j, (E.probs j : ℝ) *
        (E.states j).normalizedTraceDistance (F.states j) := by
  classical
  simp only [MState.normalizedTraceDistance, QIT.normalizedTraceDistance,
    QIT.traceNormDistance]
  rw [Classical.cqState_eq_blockDiagonal, Classical.cqState_eq_blockDiagonal]
  have hF :
      Classical.blockDiagonal (fun j =>
          ((F.probs j : ℝ) : ℂ) • (F.states j).m) =
        Classical.blockDiagonal (fun j =>
          ((E.probs j : ℝ) : ℂ) • (F.states j).m) := by
    congr 1
    funext j
    rw [hprobs j]
  rw [hF, ← Classical.blockDiagonal_sub]
  have hblocks :
      (fun j => ((E.probs j : ℝ) : ℂ) • (E.states j).m -
          ((E.probs j : ℝ) : ℂ) • (F.states j).m) =
        fun j => ((E.probs j : ℝ) : ℂ) •
          ((E.states j).m - (F.states j).m) := by
    funext j
    rw [smul_sub]
  rw [hblocks, Classical.traceNorm_blockDiagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [traceNorm_real_smul_eq (NNReal.coe_nonneg (E.probs j))]
  ring

omit [DecidableEq i] in
/-- Squared fidelity with a pure target is affine over a state ensemble. -/
private theorem sum_prob_mul_squaredFidelity_eq_averageState
    (E : MEnsemble s i) (target : Ket s) :
    (∑ j, (E.probs j : ℝ) * (E.states j).squaredFidelity target.state) =
      E.averageState.squaredFidelity target.state := by
  rw [MState.squaredFidelity_pure_right_eq_trace E.averageState target]
  calc
    (∑ j, (E.probs j : ℝ) * (E.states j).squaredFidelity target.state) =
        ∑ j, (((E.probs j : ℂ) *
          (((E.states j).m * target.state.m).trace)).re) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [MState.squaredFidelity_pure_right_eq_trace]
      simp [Complex.mul_re]
    _ = (((∑ j, (E.probs j : ℂ) • (E.states j).m) *
          target.state.m).trace).re := by
      simp [Finset.sum_mul, Matrix.trace_sum, Matrix.trace_smul, Complex.mul_re]
    _ = ((E.averageState.m * target.state.m).trace).re := by
      simp [NNReal.smul_def]

omit [DecidableEq i] in
/-- Jensen's square-root estimate for an arbitrary finite state ensemble. -/
private theorem sum_prob_mul_sqrt_one_sub_squaredFidelity_le
    (E : MEnsemble s i) (target : Ket s) :
    (∑ j, (E.probs j : ℝ) *
      Real.sqrt (1 - (E.states j).squaredFidelity target.state)) ≤
      Real.sqrt (1 - E.averageState.squaredFidelity target.state) := by
  classical
  let deficit : i → ℝ :=
    fun j ↦ 1 - (E.states j).squaredFidelity target.state
  have hdeficit : ∀ j, deficit j ∈ Set.Ici (0 : ℝ) := by
    intro j
    exact sub_nonneg.mpr (MState.squaredFidelity_le_one _ _)
  have hsum : (∑ j, (E.probs j : ℝ)) = 1 := by
    simpa only [NNReal.coe_sum, NNReal.coe_one] using
      congrArg (fun x : NNReal ↦ (x : ℝ)) E.weights_sum
  have hjensen := Real.strictConcaveOn_sqrt.concaveOn.le_map_sum
    (t := Finset.univ) (w := fun j ↦ (E.probs j : ℝ)) (p := deficit)
    (fun j _ ↦ NNReal.coe_nonneg (E.probs j)) hsum
    (fun j _ ↦ hdeficit j)
  have havg : (∑ j, (E.probs j : ℝ) * deficit j) =
      1 - ∑ j, (E.probs j : ℝ) *
        (E.states j).squaredFidelity target.state := by
    calc
      (∑ j, (E.probs j : ℝ) * deficit j) =
          ∑ j, ((E.probs j : ℝ) - (E.probs j : ℝ) *
            (E.states j).squaredFidelity target.state) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp [deficit]
        ring
      _ = (∑ j, (E.probs j : ℝ)) -
          ∑ j, (E.probs j : ℝ) *
            (E.states j).squaredFidelity target.state := by
        rw [Finset.sum_sub_distrib]
      _ = 1 - ∑ j, (E.probs j : ℝ) *
          (E.states j).squaredFidelity target.state := by rw [hsum]
  have hjensen' :
      (∑ j, (E.probs j : ℝ) * Real.sqrt (deficit j)) ≤
        Real.sqrt (∑ j, (E.probs j : ℝ) * deficit j) := by
    simpa only [Function.comp_apply, smul_eq_mul] using hjensen
  rw [havg, E.sum_prob_mul_squaredFidelity_eq_averageState target] at hjensen'
  simpa only [deficit] using hjensen'

omit [DecidableEq i] in
/-- The average trace distance of a state ensemble from a pure target is
controlled by the fidelity of its average state. -/
private theorem sum_prob_mul_traceNormDistance_le_pure
    (E : MEnsemble s i) (target : Ket s) :
    (∑ j, (E.probs j : ℝ) * (E.states j).traceNormDistance target.state) ≤
      2 * Real.sqrt
        (1 - E.averageState.squaredFidelity target.state) := by
  have hfdg (j : i) :
      (E.states j).traceNormDistance target.state ≤
        2 * Real.sqrt (1 - (E.states j).squaredFidelity target.state) := by
    have h := MState.fuchs_van_de_graaf_upper (E.states j) target.state
    simpa [MState.normalizedTraceDistance, QIT.normalizedTraceDistance] using
      mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 2 by norm_num)
  calc
    (∑ j, (E.probs j : ℝ) * (E.states j).traceNormDistance target.state) ≤
        ∑ j, (E.probs j : ℝ) *
          (2 * Real.sqrt (1 - (E.states j).squaredFidelity target.state)) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hfdg j) (NNReal.coe_nonneg _)
    _ = 2 * ∑ j, (E.probs j : ℝ) *
        Real.sqrt (1 - (E.states j).squaredFidelity target.state) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ 2 * Real.sqrt
        (1 - E.averageState.squaredFidelity target.state) :=
      mul_le_mul_of_nonneg_left
        (E.sum_prob_mul_sqrt_one_sub_squaredFidelity_le target) (by norm_num)

end MEnsemble

namespace QIT

/-- Reassociation commutes with three independent matrix maps. -/
private theorem prodAssoc_kron_naturality
    {A : Type u} {R : Type v} {B : Type w}
    {A' : Type x} {R' : Type y} {B' : Type z}
    [Fintype A] [DecidableEq A] [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A'] [Fintype R'] [DecidableEq R']
    [Fintype B'] [DecidableEq B']
    (PhiA : MatrixMap A A') (PhiR : MatrixMap R R')
    (PhiB : MatrixMap B B') :
    (MatrixMap.kron PhiA (MatrixMap.kron PhiR PhiB)).comp
        (CPTPOp.reindex (Equiv.prodAssoc A R B)).map =
      (CPTPOp.reindex (Equiv.prodAssoc A' R' B')).map.comp
        (MatrixMap.kron (MatrixMap.kron PhiA PhiR) PhiB) := by
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single
    ((MatrixMap.kron PhiA (MatrixMap.kron PhiR PhiB)).comp
      (CPTPOp.reindex (Equiv.prodAssoc A R B)).map) X]
  rw [MatrixMap.map_eq_sum_single
    ((CPTPOp.reindex (Equiv.prodAssoc A' R' B')).map.comp
      (MatrixMap.kron (MatrixMap.kron PhiA PhiR) PhiB)) X]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [LinearMap.comp_apply]
  rw [CPTPOp.reindex_map_single]
  rw [show Matrix.single (Equiv.prodAssoc A R B i)
      (Equiv.prodAssoc A R B j) (1 : ℂ) =
        Matrix.kronecker
          (Matrix.single i.1.1 j.1.1 (1 : ℂ))
          (Matrix.single (i.1.2, i.2) (j.1.2, j.2) (1 : ℂ)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  simp only [Matrix.kronecker]
  rw [MatrixMap.kron_map_of_kron_state]
  rw [show Matrix.single (i.1.2, i.2) (j.1.2, j.2) (1 : ℂ) =
        Matrix.kronecker
          (Matrix.single i.1.2 j.1.2 (1 : ℂ))
          (Matrix.single i.2 j.2 (1 : ℂ)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  simp only [Matrix.kronecker]
  rw [MatrixMap.kron_map_of_kron_state]
  rw [show Matrix.single i j (1 : ℂ) =
        Matrix.kronecker
          (Matrix.single i.1 j.1 (1 : ℂ))
          (Matrix.single i.2 j.2 (1 : ℂ)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  simp only [Matrix.kronecker]
  rw [MatrixMap.kron_map_of_kron_state]
  rw [show Matrix.single i.1 j.1 (1 : ℂ) =
        Matrix.kronecker
          (Matrix.single i.1.1 j.1.1 (1 : ℂ))
          (Matrix.single i.1.2 j.1.2 (1 : ℂ)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  simp only [Matrix.kronecker]
  rw [MatrixMap.kron_map_of_kron_state, CPTPOp.reindex_map]
  ext k l
  simp [mul_assoc]

private theorem kron_idChannel_idChannel_eq_idChannel_map
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] :
    MatrixMap.kron (CPTPOp.id (dIn := A)).map (CPTPOp.id (dIn := B)).map =
      (CPTPOp.id (dIn := A × B)).map := by
  simp only [CPTPOp.id_map]
  rw [MatrixMap.kron_id_id]

private theorem sum_rankOne_localPostAmplitude_eq_kron_ofKraus
    {A : Type u} {A' : Type v} {B : Type w} {K : Type x}
    [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype K]
    (kraus : K → Matrix A' A ℂ) (amp : A × B → ℂ) :
    (∑ k : K,
        rankOneMatrix (fun out : A' × B =>
          ∑ a : A, kraus k out.1 a * amp (a, out.2))) =
      MatrixMap.kron (MatrixMap.ofKraus kraus) (CPTPOp.id (dIn := B)).map
        (rankOneMatrix amp) := by
  classical
  ext i j
  rw [MatrixMap.kron_idChannel_apply_slice]
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply, rankOneMatrix_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

private theorem FiniteInstrument.sum_rankOne_postAmplitude_fixedOutcome
    {A : Type u} {A' : Type v} {B : Type w} {X : Type x}
    [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype X]
    (M : FiniteInstrument A A' X) (psi : Ket (A × B)) (result : X) :
    (∑ k : A × A', rankOneMatrix (M.postAmplitude psi (result, k))) =
      MatrixMap.kron (M.branch result) (CPTPOp.id (dIn := B)).map
        psi.state.m := by
  rw [← (M.branchTraceNonincreasingCP result).ofKraus_kraus]
  simp only [Ket.state_matrix]
  exact sum_rankOne_localPostAmplitude_eq_kron_ofKraus
    (M.branchTraceNonincreasingCP result).kraus psi.vec

private theorem traceNormDistance_traceRight_le
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (rho sigma : MState (A × B)) :
    rho.traceRight.traceNormDistance sigma.traceRight ≤ rho.traceNormDistance sigma := by
  simp only [MState.traceNormDistance, QIT.traceNormDistance, MState.traceRight_m]
  rw [← Matrix.traceRight_sub]
  exact traceNorm_traceRight_le_matrix (rho.m - sigma.m)

namespace OneWayLOCC

variable {A : Type u} {A' : Type v} {B B' X : Type*}
variable [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
variable [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype X]

/-- The physical output conditioned only on Alice's refined local outcome;
Bob's complete channel is applied nonselectively. -/
def aliceConditionedOutputState
    (L : OneWayLOCC A A' B B' X) (input : Ket (A × B))
    (i : L.aliceInstrument.positiveSupport input) : MState (A' × B') :=
  ((CPTPOp.id (dIn := A')).prod (L.bobChannel i.1.1))
    (L.aliceInstrument.normalizedBranch input i).state

/-- Averaging the Alice-conditioned, nonselective Bob outputs recovers the
realized one-way LOCC output. -/
theorem sum_alicePositiveBranchWeight_smul_conditionedOutputState_matrix
    (L : OneWayLOCC A A' B B' X) (input : Ket (A × B)) :
    (∑ i : L.aliceInstrument.positiveSupport input,
      L.aliceInstrument.branchWeight input i.1 •
        (L.aliceConditionedOutputState input i).m) =
      L.toChannel.map input.state.m := by
  classical
  let f : L.aliceInstrument.refinedBranchIndex → CMatrix (A' × B') :=
    fun i ↦ ((CPTPOp.id (dIn := A')).prod (L.bobChannel i.1)).map
      (rankOneMatrix (L.aliceInstrument.postAmplitude input i))
  have hsupport :
      (∑ i : L.aliceInstrument.positiveSupport input, f i.1) =
        ∑ i : L.aliceInstrument.refinedBranchIndex, f i := by
    conv_rhs =>
      rw [← Fintype.sum_subtype_add_sum_subtype
        (fun i : L.aliceInstrument.refinedBranchIndex ↦
          0 < L.aliceInstrument.branchWeight input i) f]
    have hzero :
        (∑ i : {i : L.aliceInstrument.refinedBranchIndex //
            ¬ 0 < L.aliceInstrument.branchWeight input i}, f i.1) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hweight : L.aliceInstrument.branchWeight input i.1 = 0 :=
        le_antisymm (not_lt.mp i.2) bot_le
      simp [f, L.aliceInstrument.rankOne_postAmplitude_eq_zero_of_branchWeight_eq_zero
        input i.1 hweight]
    rw [hzero, add_zero]
  calc
    (∑ i : L.aliceInstrument.positiveSupport input,
        L.aliceInstrument.branchWeight input i.1 •
          (L.aliceConditionedOutputState input i).m) =
        ∑ i : L.aliceInstrument.positiveSupport input, f i.1 := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [f]
      simp only [aliceConditionedOutputState, CPTPOp.mat_coe_eq_apply_mat]
      change ((L.aliceInstrument.branchWeight input i.1 : ℂ) •
          ((CPTPOp.id (dIn := A')).prod (L.bobChannel i.1.1)).map
            (L.aliceInstrument.normalizedBranch input i).state.m) =
        ((CPTPOp.id (dIn := A')).prod (L.bobChannel i.1.1)).map
          (rankOneMatrix (L.aliceInstrument.postAmplitude input i.1))
      rw [← map_smul]
      congr 1
      rw [← L.aliceInstrument.branchWeight_smul_normalizedBranch_state_matrix input i]
      ext p q
      simp [NNReal.smul_def, Complex.real_smul]
    _ = ∑ i : L.aliceInstrument.refinedBranchIndex, f i := hsupport
    _ = ∑ result : X, ∑ k : A × A', f (result, k) := by
      simp only [FiniteInstrument.refinedBranchIndex, Fintype.sum_prod_type]
    _ = ∑ result : X,
        ((CPTPOp.id (dIn := A')).prod (L.bobChannel result)).map
          (∑ k : A × A',
            rankOneMatrix (L.aliceInstrument.postAmplitude input (result, k))) := by
      apply Finset.sum_congr rfl
      intro result _
      rw [map_sum]
    _ = ∑ result : X,
        ((CPTPOp.id (dIn := A')).prod (L.bobChannel result)).map
          (MatrixMap.kron (L.aliceInstrument.branch result)
            (CPTPOp.id (dIn := B)).map input.state.m) := by
      apply Finset.sum_congr rfl
      intro result _
      rw [L.aliceInstrument.sum_rankOne_postAmplitude_fixedOutcome input result]
    _ = ∑ result : X,
        MatrixMap.kron (L.aliceInstrument.branch result)
          (L.bobChannel result).map input.state.m := by
      apply Finset.sum_congr rfl
      intro result _
      calc
        ((CPTPOp.id (dIn := A')).prod (L.bobChannel result)).map
            (MatrixMap.kron (L.aliceInstrument.branch result)
              (CPTPOp.id (dIn := B)).map input.state.m) =
            MatrixMap.kron
              ((CPTPOp.id (dIn := A')).map.comp
                (L.aliceInstrument.branch result))
              ((L.bobChannel result).map.comp (CPTPOp.id (dIn := B)).map)
              input.state.m := by
          rw [CPTPOp.prod_map]
          exact MatrixMap.kron_comp_apply_general
            (CPTPOp.id (dIn := A')).map (L.bobChannel result).map
            (L.aliceInstrument.branch result) (CPTPOp.id (dIn := B)).map
            input.state.m
        _ = MatrixMap.kron (L.aliceInstrument.branch result)
            (L.bobChannel result).map input.state.m := by
          rw [CPTPOp.id_map (dIn := A'),
            CPTPOp.id_map (dIn := B)]
          simp only [LinearMap.id_comp, LinearMap.comp_id]
    _ = L.toChannel.map input.state.m := by
      rw [L.toChannel_map, LinearMap.sum_apply]

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

namespace StateMergingBlockProtocol

/-- Decidable equality on the local-converse output register, assembled from the
factor instances so that it is definitionally the product instance. -/
local instance localConverseOutputDecidableEq :
    DecidableEq
      (lA ×
        (TensorPower r n ×
          ((TensorPower a n × TensorPower b n) × lB))) :=
  @instDecidableEqProd _ _ inferInstance
    (@instDecidableEqProd _ _
      (tensorPowerDecidableEq (a := r) n)
      (@instDecidableEqProd _ _
        (@instDecidableEqProd _ _
          (tensorPowerDecidableEq (a := a) n)
          (tensorPowerDecidableEq (a := b) n))
        inferInstance))

variable (C : StateMergingBlockProtocol psi n kA kB lA lB outcome)

/-- The physical converse input regrouped as `A (R B)`, so the original
Alice instrument acts only on `A` and the untouched reference remains part of
the purifying side. -/
def localConverseInputKet :
    Ket
      ((TensorPower a n × kA) ×
        (TensorPower r n × (TensorPower b n × kB))) :=
  C.converseInputKet.reindex
    (Equiv.prodAssoc
      (TensorPower a n × kA)
      (TensorPower r n)
      (TensorPower b n × kB))

@[simp]
theorem localConverseInputKet_reindex_symm :
    C.localConverseInputKet.reindex
        (Equiv.prodAssoc
          (TensorPower a n × kA)
          (TensorPower r n)
          (TensorPower b n × kB)).symm =
      C.converseInputKet := by
  apply Ket.ext_vec
  funext i
  rfl

/-- The same physical one-way LOCC map in the local grouping
`A | (R B)`.  Alice's instrument is exactly the protocol's original local
instrument; the reference identity is carried only by Bob's channel. -/
def localConverseLOCC :
    OneWayLOCC
      (TensorPower a n × kA)
      lA
      (TensorPower r n × (TensorPower b n × kB))
      (TensorPower r n ×
        ((TensorPower a n × TensorPower b n) × lB))
      outcome :=
  OneWayLOCC.ofFiniteInstrument C.locc.aliceInstrument
    (fun result ↦
      (CPTPOp.id (dIn := TensorPower r n)).prod (C.locc.bobChannel result))

/-- The ideal target in the local grouping `L_A | (R^n B')`. -/
def localConverseTargetKet :
    Ket
      (lA ×
        (TensorPower r n ×
          ((TensorPower a n × TensorPower b n) × lB))) :=
  C.converseTargetKet.reindex
    (Equiv.prodAssoc lA (TensorPower r n)
      ((TensorPower a n × TensorPower b n) × lB))

/-- Reassociation identifies the local physical output with the existing
reference-lifted converse output. -/
theorem localConverseLOCC_applyState :
    C.localConverseLOCC.toChannel C.localConverseInputKet.state =
      MState.reindex (C.converseLOCC.toChannel C.converseInputKet.state)
        (Equiv.prodAssoc lA (TensorPower r n)
          ((TensorPower a n × TensorPower b n) × lB)) := by
  apply MState.ext
  simp only [CPTPOp.mat_coe_eq_apply_mat, MState.reindex_matrix]
  rw [← CPTPOp.reindex_map
    (Equiv.prodAssoc lA (TensorPower r n)
      ((TensorPower a n × TensorPower b n) × lB))
    (C.converseLOCC.toChannel.map C.converseInputKet.state.m)]
  simp only [localConverseLOCC, OneWayLOCC.ofFiniteInstrument,
    localConverseInputKet, Ket.reindex_state, converseLOCC,
    OneWayLOCC.prodIdRight, OneWayLOCC.toChannel_map,
    FiniteInstrument.prodIdRight_branch, CPTPOp.prod_map, MState.reindex_matrix,
    LinearMap.sum_apply, map_sum]
  rw [← CPTPOp.reindex_map
    (Equiv.prodAssoc (TensorPower a n × kA) (TensorPower r n)
      (TensorPower b n × kB))
    C.converseInputKet.state.m]
  apply Finset.sum_congr rfl
  intro result _
  have h := LinearMap.congr_fun
    (prodAssoc_kron_naturality
      (C.locc.aliceInstrument.branch result)
      (CPTPOp.id (dIn := TensorPower r n)).map
      (C.locc.bobChannel result).map)
    C.converseInputKet.state.m
  simp only [LinearMap.comp_apply] at h
  with_reducible exact h

/-- The locally grouped protocol has exactly the block protocol's computed
fidelity deficit. -/
theorem localConverseLOCC_fidelityError :
    1 - MState.squaredFidelity
        (C.localConverseLOCC.toChannel C.localConverseInputKet.state)
        C.localConverseTargetKet.state = C.fidelityError := by
  rw [C.localConverseLOCC_applyState]
  simp only [localConverseTargetKet, Ket.reindex_state,
    MState.squaredFidelity_reindex]
  exact C.converseLOCC_fidelityError

/-- Source-faithful refined Alice outcomes before the reference lift. -/
abbrev originalRecordedOutcomeIndex :=
  C.locc.aliceInstrument.positiveSupport C.localConverseInputKet

/-- Instrument outcomes are only assumed finite, so equality is decided classically. -/
local instance originalRecordedOutcomeIndexDecidableEq :
    DecidableEq C.originalRecordedOutcomeIndex :=
  Classical.decEq _

/-- The state after Bob's complete conditional channel on one original
positive Alice branch.  Bob's Kraus outcomes are summed nonselectively. -/
def originalAlicePostBobBranchState
    (i : C.originalRecordedOutcomeIndex) :
    MState
      ((lA × TensorPower r n) ×
        ((TensorPower a n × TensorPower b n) × lB)) :=
  ((CPTPOp.id (dIn := lA × TensorPower r n)).prod
      (C.locc.bobChannel i.1.1))
    ((C.locc.aliceInstrument.normalizedBranch
      C.localConverseInputKet i).state.reindex
        (Equiv.prodAssoc lA (TensorPower r n)
          (TensorPower b n × kB)).symm)

/-- Reassociating one original Alice branch identifies its nonselective Bob
output with the corresponding branch of the locally grouped LOCC map. -/
theorem originalAlicePostBobBranchState_reindex
    (i : C.originalRecordedOutcomeIndex) :
    (C.originalAlicePostBobBranchState i).reindex
        (Equiv.prodAssoc lA (TensorPower r n)
          ((TensorPower a n × TensorPower b n) × lB)) =
      C.localConverseLOCC.aliceConditionedOutputState
        C.localConverseInputKet i := by
  apply MState.ext
  simp only [originalAlicePostBobBranchState,
    OneWayLOCC.aliceConditionedOutputState, localConverseLOCC,
    OneWayLOCC.ofFiniteInstrument, CPTPOp.mat_coe_eq_apply_mat,
    MState.reindex_matrix, CPTPOp.prod_map]
  let rho :=
    (C.locc.aliceInstrument.normalizedBranch
      C.localConverseInputKet i).state
  rw [← CPTPOp.reindex_map
    (Equiv.prodAssoc lA (TensorPower r n)
      ((TensorPower a n × TensorPower b n) × lB))]
  rw [← CPTPOp.reindex_map
    (Equiv.prodAssoc lA (TensorPower r n)
      (TensorPower b n × kB)).symm]
  rw [← kron_idChannel_idChannel_eq_idChannel_map
    (A := lA) (B := TensorPower r n)]
  have h := LinearMap.congr_fun
    (prodAssoc_kron_naturality
      (CPTPOp.id (dIn := lA)).map
      (CPTPOp.id (dIn := TensorPower r n)).map
      (C.locc.bobChannel i.1.1).map)
    ((CPTPOp.reindex
      (Equiv.prodAssoc lA (TensorPower r n)
        (TensorPower b n × kB)).symm).map rho.m)
  simp only [LinearMap.comp_apply] at h
  simp only [CPTPOp.reindex_map_symm_map] at h
  with_reducible exact h.symm

/-- Bob's trace-preserving conditional channel leaves the retained Alice
register and untouched reference marginal unchanged. -/
theorem originalAlicePostBobBranchState_traceRight
    (i : C.originalRecordedOutcomeIndex) :
    (C.originalAlicePostBobBranchState i).traceRight =
      C.locc.aliceInstrument.positiveBranchSourceReferenceState
        C.localConverseInputKet i := by
  rw [originalAlicePostBobBranchState,
    MState.traceRight_applyState_id_prod]
  rfl

/-- Original Alice branches after Bob is summed out, with the physical
Alice branch weights. -/
def originalAlicePostBobEnsemble :
    MEnsemble ((lA × TensorPower r n) ×
        ((TensorPower a n × TensorPower b n) × lB)) C.originalRecordedOutcomeIndex :=
  .ofProbs
    (fun i => C.locc.aliceInstrument.branchWeight
      C.localConverseInputKet i.1)
    (C.locc.aliceInstrument.sum_positiveSupport_branchWeight_eq_one
      C.localConverseInputKet)
    (fun i => C.originalAlicePostBobBranchState i)

/-- The nonselective average over original Alice outcomes is the existing
physical converse output. -/
theorem originalAlicePostBobEnsemble_averageState :
    C.originalAlicePostBobEnsemble.averageState =
      C.converseLOCC.toChannel C.converseInputKet.state := by
  have hlocal :
      C.originalAlicePostBobEnsemble.averageState.reindex
          (Equiv.prodAssoc lA (TensorPower r n)
            ((TensorPower a n × TensorPower b n) × lB)) =
        C.localConverseLOCC.toChannel
          C.localConverseInputKet.state := by
    apply MState.ext
    simp only [MState.reindex_matrix, CPTPOp.mat_coe_eq_apply_mat]
    rw [← CPTPOp.reindex_map
      (Equiv.prodAssoc lA (TensorPower r n)
        ((TensorPower a n × TensorPower b n) × lB))]
    change (CPTPOp.reindex
        (Equiv.prodAssoc lA (TensorPower r n)
          ((TensorPower a n × TensorPower b n) × lB))).map
        C.originalAlicePostBobEnsemble.averageState.m =
      C.localConverseLOCC.toChannel.map C.localConverseInputKet.state.m
    rw [MEnsemble.averageState_matrix, map_sum]
    calc
      (∑ i : C.originalRecordedOutcomeIndex,
          (CPTPOp.reindex
            (Equiv.prodAssoc lA (TensorPower r n)
              ((TensorPower a n × TensorPower b n) × lB))).map
            (C.originalAlicePostBobEnsemble.probs i •
              (C.originalAlicePostBobEnsemble.states i).m)) =
          ∑ i : C.originalRecordedOutcomeIndex,
            C.localConverseLOCC.aliceInstrument.branchWeight
                C.localConverseInputKet i.1 •
              (C.localConverseLOCC.aliceConditionedOutputState
                C.localConverseInputKet i).m := by
        apply Finset.sum_congr rfl
        intro i _
        rw [LinearMap.map_smul_of_tower, CPTPOp.reindex_map]
        simp only [originalAlicePostBobEnsemble]
        rw [← MState.reindex_matrix, C.originalAlicePostBobBranchState_reindex i]
        ext j k
        simp [NNReal.smul_def, Matrix.smul_apply, Complex.real_smul,
          localConverseLOCC, OneWayLOCC.ofFiniteInstrument]
      _ = C.localConverseLOCC.toChannel.map
          C.localConverseInputKet.state.m :=
        C.localConverseLOCC.sum_alicePositiveBranchWeight_smul_conditionedOutputState_matrix
          C.localConverseInputKet
  rw [C.localConverseLOCC_applyState] at hlocal
  have hcancel : ∀ ρ : MState ((lA × TensorPower r n) ×
        ((TensorPower a n × TensorPower b n) × lB)),
      (ρ.reindex (Equiv.prodAssoc lA (TensorPower r n)
            ((TensorPower a n × TensorPower b n) × lB))).reindex
          (Equiv.prodAssoc lA (TensorPower r n)
            ((TensorPower a n × TensorPower b n) × lB)).symm = ρ := by
    intro ρ
    simpa using ρ.reindex_symm_reindex
      (Equiv.prodAssoc lA (TensorPower r n)
        ((TensorPower a n × TensorPower b n) × lB)).symm
  have h := congrArg
    (fun rho ↦ rho.reindex
      (Equiv.prodAssoc lA (TensorPower r n)
        ((TensorPower a n × TensorPower b n) × lB)).symm)
    hlocal
  simpa [hcancel] using h

/-- Berta's physical recorded state on `L_A | (R^n X_A)`, built from the
original Alice instrument rather than the canonical Kraus refinement of its
reference lift. -/
def originalRecordedOutcomeState :
    MState
      (lA × (TensorPower r n × C.originalRecordedOutcomeIndex)) :=
  C.locc.aliceInstrument.recordedSourceReferenceState
    C.localConverseInputKet

/-- The ideal target on Alice's retained ebit half and the untouched
reference is the product of the maximally mixed ebit marginal and the source
reference marginal. -/
theorem converseTargetKet_traceRight_eq_uniform_prod :
    C.converseTargetKet.state.traceRight =
      (MState.uniform : MState lA).prod
        (stateMergingBlockSource psi n).state.traceLeft := by
  apply MState.ext
  ext i j
  simp [converseTargetKet, targetKet,
    prodABCToACBEquiv, stateMergingTargetEquiv,
    Matrix.traceLeft,
    Matrix.traceRight, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type]
  have hebit :
      (∑ k : lB,
        (Ket.maximallyEntangled C.outputEbitPairing).vec (i.1, k) *
          star ((Ket.maximallyEntangled C.outputEbitPairing).vec (j.1, k))) =
        (Fintype.card lA : ℂ)⁻¹ * (1 : CMatrix lA) i.1 j.1 := by
    have h := congrArg (fun rho : MState lA => rho.m i.1 j.1)
      (Ket.maximallyEntangled_traceRight C.outputEbitPairing)
    simpa [Matrix.traceRight, Ket.state,
      rankOneMatrix_apply] using h
  calc
    (∑ x, ∑ y, ∑ k,
        (stateMergingBlockSource psi n).vec ((x, y), i.2) *
            (Ket.maximallyEntangled C.outputEbitPairing).vec (i.1, k) *
          (star ((stateMergingBlockSource psi n).vec ((x, y), j.2)) *
            star ((Ket.maximallyEntangled C.outputEbitPairing).vec (j.1, k)))) =
        (∑ x, ∑ y, ∑ k,
          (stateMergingBlockSource psi n).vec ((x, y), i.2) *
              star ((stateMergingBlockSource psi n).vec ((x, y), j.2)) *
            ((Ket.maximallyEntangled C.outputEbitPairing).vec (i.1, k) *
              star ((Ket.maximallyEntangled C.outputEbitPairing).vec (j.1, k)))) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
        Finset.sum_congr rfl fun k _ => ?_
      ring
    _ =
        (∑ k : lB,
          (Ket.maximallyEntangled C.outputEbitPairing).vec (i.1, k) *
            star ((Ket.maximallyEntangled C.outputEbitPairing).vec (j.1, k))) *
          (∑ x, ∑ y,
            (stateMergingBlockSource psi n).vec ((x, y), i.2) *
              star ((stateMergingBlockSource psi n).vec ((x, y), j.2))) := by
      exact sum_sum_sum_mul_right
        (fun x y =>
          (stateMergingBlockSource psi n).vec ((x, y), i.2) *
            star ((stateMergingBlockSource psi n).vec ((x, y), j.2)))
        (fun k =>
          (Ket.maximallyEntangled C.outputEbitPairing).vec (i.1, k) *
            star ((Ket.maximallyEntangled C.outputEbitPairing).vec (j.1, k)))
    _ = (Fintype.card lA : ℂ)⁻¹ * (1 : CMatrix lA) i.1 j.1 *
          ∑ x, ∑ y,
            (stateMergingBlockSource psi n).vec ((x, y), i.2) *
              star ((stateMergingBlockSource psi n).vec ((x, y), j.2)) := by
      rw [hebit]

/-- Alice's positive refined local-instrument outcomes.  Bob's Kraus index is
deliberately absent from this source-faithful Berta record. -/
abbrev recordedOutcomeIndex :=
  C.originalRecordedOutcomeIndex

/-- Instrument outcomes are only assumed finite, so equality is decided classically. -/
local instance recordedOutcomeIndexDecidableEq :
    DecidableEq C.recordedOutcomeIndex :=
  Classical.decEq _

/-- Physical post-Alice states on `L_A R^n`, with Alice's operational branch
probabilities. -/
def recordedOutcomeEnsemble :
    MEnsemble (lA × TensorPower r n) C.recordedOutcomeIndex :=
  .ofProbs
    (fun i =>
      C.locc.aliceInstrument.branchWeight C.localConverseInputKet i.1)
    (C.locc.aliceInstrument.sum_positiveSupport_branchWeight_eq_one
      C.localConverseInputKet)
    (fun i =>
      C.locc.aliceInstrument.positiveBranchSourceReferenceState
        C.localConverseInputKet i)

/-- The ideal `L_A R^n` branch, repeated with the same Alice-outcome
distribution as the physical ensemble. -/
def idealRecordedOutcomeEnsemble :
    MEnsemble (lA × TensorPower r n) C.recordedOutcomeIndex :=
  .ofProbs
    (fun i =>
      C.locc.aliceInstrument.branchWeight C.localConverseInputKet i.1)
    (C.locc.aliceInstrument.sum_positiveSupport_branchWeight_eq_one
      C.localConverseInputKet)
    (fun _ =>
      (MState.uniform : MState lA).prod
        (stateMergingBlockSource psi n).state.traceLeft)

/-- Alice's physical cq record, reordered onto `L_A (R^n X_A)`. -/
def recordedOutcomeState :
    MState (lA × (TensorPower r n × C.recordedOutcomeIndex)) :=
  C.recordedOutcomeEnsemble.cqState.reindex
    (prodABCToBCAEquiv
      C.recordedOutcomeIndex lA (TensorPower r n))

/-- The same-weight ideal cq record on `L_A (R^n X_A)`. -/
def idealRecordedOutcomeState :
    MState (lA × (TensorPower r n × C.recordedOutcomeIndex)) :=
  C.idealRecordedOutcomeEnsemble.cqState.reindex
    (prodABCToBCAEquiv
      C.recordedOutcomeIndex lA (TensorPower r n))

/-- The ideal side-information ensemble on the untouched reference. -/
def idealRecordedConditioningEnsemble :
    MEnsemble (TensorPower r n) C.recordedOutcomeIndex :=
  .ofProbs
    (fun i =>
      C.locc.aliceInstrument.branchWeight C.localConverseInputKet i.1)
    (C.locc.aliceInstrument.sum_positiveSupport_branchWeight_eq_one
      C.localConverseInputKet)
    (fun _ => (stateMergingBlockSource psi n).state.traceLeft)

/-- The ideal conditioning state on `R^n X_A`. -/
def idealRecordedConditioningState :
    MState (TensorPower r n × C.recordedOutcomeIndex) :=
  C.idealRecordedConditioningEnsemble.cqState.reindex
    (Equiv.prodComm C.recordedOutcomeIndex (TensorPower r n))

@[simp]
theorem idealRecordedOutcomeEnsemble_states_eq_target
    (i : C.recordedOutcomeIndex) :
    C.idealRecordedOutcomeEnsemble.states i =
      C.converseTargetKet.state.traceRight := by
  exact C.converseTargetKet_traceRight_eq_uniform_prod.symm

/-- The ideal Alice-record state is a uniform retained-ebit register
independent of the untouched reference and Alice's classical outcome. -/
theorem idealRecordedOutcomeState_eq_uniform_prod :
    C.idealRecordedOutcomeState =
      (MState.uniform : MState lA).prod C.idealRecordedConditioningState := by
  apply MState.ext
  ext i j
  simp [idealRecordedOutcomeState, idealRecordedConditioningState,
    idealRecordedOutcomeEnsemble, idealRecordedConditioningEnsemble,
    prodABCToBCAEquiv, Equiv.prodComm,
    MEnsemble.cqState, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp [NNReal.smul_def, mul_assoc, mul_comm]

/-- Berta's ideal cq endpoint: the retained ebit half is uniform and
independent of `R^n X_A`, so its conditional min-entropy is `log₂ |L_A|`. -/
theorem idealRecordedOutcomeState_conditionalMinEntropy :
    C.idealRecordedOutcomeState.conditionalMinEntropy =
      log2 (Fintype.card lA : ℝ) := by
  rw [C.idealRecordedOutcomeState_eq_uniform_prod]
  exact MState.conditionalMinEntropy_uniform_prod
    C.idealRecordedConditioningState

@[simp]
theorem idealRecordedOutcomeEnsemble_probs (i : C.recordedOutcomeIndex) :
    C.idealRecordedOutcomeEnsemble.probs i = C.recordedOutcomeEnsemble.probs i := by
  simp only [idealRecordedOutcomeEnsemble, recordedOutcomeEnsemble, MEnsemble.ofProbs_probs]

/-- Alice's recorded physical state is within `sqrt fidelityError` in
normalized trace distance of the same-weight ideal record. -/
theorem recordedOutcomeState_normalizedTraceDistance_le_sqrt_fidelityError :
    C.recordedOutcomeState.normalizedTraceDistance C.idealRecordedOutcomeState ≤
      Real.sqrt C.fidelityError := by
  rw [recordedOutcomeState, idealRecordedOutcomeState,
    MState.normalizedTraceDistance_reindex_equiv]
  rw [MEnsemble.cqState_normalizedTraceDistance_eq_sum_of_same_probs
    C.recordedOutcomeEnsemble C.idealRecordedOutcomeEnsemble
    C.idealRecordedOutcomeEnsemble_probs]
  have hfull :=
    C.originalAlicePostBobEnsemble.sum_prob_mul_traceNormDistance_le_pure
      C.converseTargetKet
  rw [C.originalAlicePostBobEnsemble_averageState,
    C.converseLOCC_fidelityError] at hfull
  have havg :
      (∑ i : C.recordedOutcomeIndex,
        (C.locc.aliceInstrument.branchWeight
          C.localConverseInputKet i.1 : ℝ) *
          (C.locc.aliceInstrument.positiveBranchSourceReferenceState
            C.localConverseInputKet i).traceNormDistance
              C.converseTargetKet.state.traceRight) ≤
        2 * Real.sqrt C.fidelityError := by
    calc
      (∑ i : C.recordedOutcomeIndex,
          (C.locc.aliceInstrument.branchWeight
            C.localConverseInputKet i.1 : ℝ) *
            (C.locc.aliceInstrument.positiveBranchSourceReferenceState
              C.localConverseInputKet i).traceNormDistance
                C.converseTargetKet.state.traceRight) =
          ∑ i : C.recordedOutcomeIndex,
            (C.originalAlicePostBobEnsemble.probs i : ℝ) *
              (C.originalAlicePostBobEnsemble.states i).traceRight.traceNormDistance
                C.converseTargetKet.state.traceRight := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [originalAlicePostBobEnsemble, MEnsemble.ofProbs_probs,
          MEnsemble.ofProbs_states]
        rw [C.originalAlicePostBobBranchState_traceRight i]
      _ ≤ ∑ i : C.recordedOutcomeIndex,
          (C.originalAlicePostBobEnsemble.probs i : ℝ) *
            (C.originalAlicePostBobEnsemble.states i).traceNormDistance
              C.converseTargetKet.state := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (traceNormDistance_traceRight_le _ _) (NNReal.coe_nonneg _)
      _ ≤ 2 * Real.sqrt C.fidelityError := hfull
  calc
    (∑ i : C.recordedOutcomeIndex,
        (C.recordedOutcomeEnsemble.probs i : ℝ) *
          (C.recordedOutcomeEnsemble.states i).normalizedTraceDistance
            (C.idealRecordedOutcomeEnsemble.states i)) =
        (1 / 2 : ℝ) *
          ∑ i : C.recordedOutcomeIndex,
            (C.locc.aliceInstrument.branchWeight
                C.localConverseInputKet i.1 : ℝ) *
              (C.locc.aliceInstrument.positiveBranchSourceReferenceState
                C.localConverseInputKet i).traceNormDistance
                  C.converseTargetKet.state.traceRight := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [recordedOutcomeEnsemble, MEnsemble.ofProbs_probs,
        MEnsemble.ofProbs_states,
        C.idealRecordedOutcomeEnsemble_states_eq_target,
        MState.normalizedTraceDistance, QIT.normalizedTraceDistance,
        MState.traceNormDistance]
      ring
    _ ≤ (1 / 2 : ℝ) * (2 * Real.sqrt C.fidelityError) :=
      mul_le_mul_of_nonneg_left havg (by norm_num)
    _ = Real.sqrt C.fidelityError := by ring

/-- The canonical purified-distance smoothing statement corresponding to the
recorded trace-distance estimate.  The metrics are related explicitly by the
repository's Fuchs--van de Graaf bridge. -/
theorem recordedOutcomeState_purifiedBall :
    C.recordedOutcomeState.purifiedBall
        (Real.sqrt
          (2 * Real.sqrt C.fidelityError - (Real.sqrt C.fidelityError) ^ 2))
      C.idealRecordedOutcomeState := by
  let : DecidableEq (TensorPower a n) := tensorPowerDecidableEq n
  let : DecidableEq (TensorPower b n) := tensorPowerDecidableEq n
  let : DecidableEq (TensorPower r n) := tensorPowerDecidableEq n
  rw [MState.purifiedBall_eq]
  apply MState.purifiedDistance_le_sqrt_two_mul_sub_sq_of_normalizedTraceDistance_le
  · apply Real.sqrt_le_one.mpr
    unfold fidelityError
    have hnonneg := MState.squaredFidelity_nonneg C.outputState C.targetState
    linarith
  · exact C.recordedOutcomeState_normalizedTraceDistance_le_sqrt_fidelityError

end StateMergingBlockProtocol

end QIT

end
