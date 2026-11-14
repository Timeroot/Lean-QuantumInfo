/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Protocols.StateMerging.Converse
public import QIT.Protocols.LOCC.SmoothConditionalMinEntropy
public import QIT.OneShot.SmoothEndpoint.Duality
public import QIT.Protocols.LOCC.Construction
public import QIT.Core.System
import QIT.OneShot.SmoothNormalizedExtension

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

namespace QIT

universe u v w x y z p q

noncomputable section

namespace Ensemble

variable {i : Type u} {s : Type v}
variable [Fintype i] [DecidableEq i] [Fintype s] [DecidableEq s]

/-- The normalized trace distance between cq states with the same classical
distribution is the corresponding weighted branch average. -/
private theorem cqState_normalizedTraceDistance_eq_sum_of_same_probs
    (E F : Ensemble i s) (hprobs : ∀ j, F.probs j = E.probs j) :
    E.cqState.normalizedTraceDistance F.cqState =
      ∑ j, (E.probs j : ℝ) *
        (E.states j).normalizedTraceDistance (F.states j) := by
  classical
  simp only [State.normalizedTraceDistance, QIT.normalizedTraceDistance,
    QIT.traceNormDistance]
  rw [Classical.cqState_eq_blockDiagonal, Classical.cqState_eq_blockDiagonal]
  have hF :
      Classical.blockDiagonal (fun j =>
          ((F.probs j : ℝ) : ℂ) • (F.states j).matrix) =
        Classical.blockDiagonal (fun j =>
          ((E.probs j : ℝ) : ℂ) • (F.states j).matrix) := by
    congr 1
    funext j
    rw [hprobs j]
  rw [hF, ← Classical.blockDiagonal_sub]
  have hblocks :
      (fun j => ((E.probs j : ℝ) : ℂ) • (E.states j).matrix -
          ((E.probs j : ℝ) : ℂ) • (F.states j).matrix) =
        fun j => ((E.probs j : ℝ) : ℂ) •
          ((E.states j).matrix - (F.states j).matrix) := by
    funext j
    rw [smul_sub]
  rw [hblocks, Classical.traceNorm_blockDiagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [traceNorm_real_smul_eq (NNReal.coe_nonneg (E.probs j))]
  ring

omit [DecidableEq i] in
/-- Trace-norm convexity for the average of a finite ensemble. -/
private theorem averageState_traceNormDistance_le_sum
    (E : Ensemble i s) (target : State s) :
    E.averageState.traceNormDistance target ≤
      ∑ j, (E.probs j : ℝ) * (E.states j).traceNormDistance target := by
  classical
  change traceNorm (E.averageState.matrix - target.matrix) ≤
    ∑ j, (E.probs j : ℝ) * traceNorm ((E.states j).matrix - target.matrix)
  have hsub :
      E.averageState.matrix - target.matrix =
        ∑ j, (E.probs j) • ((E.states j).matrix - target.matrix) := by
    calc
      E.averageState.matrix - target.matrix =
          (∑ j, (E.probs j) • (E.states j).matrix) -
            ∑ j, (E.probs j) • target.matrix := by
        rw [E.averageState_matrix, ← Finset.sum_smul, E.weights_sum, one_smul]
      _ = ∑ j, ((E.probs j) • (E.states j).matrix -
          (E.probs j) • target.matrix) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ j, (E.probs j) • ((E.states j).matrix - target.matrix) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_sub]
  rw [hsub]
  calc
    traceNorm
        (∑ j, (E.probs j) •
          ((E.states j).matrix - target.matrix)) ≤
        ∑ j, traceNorm
          ((E.probs j) •
            ((E.states j).matrix - target.matrix)) := by
      simpa using traceNorm_sum_le_sum_traceNorm
        (s := Finset.univ)
        (f := fun j => (E.probs j) •
          ((E.states j).matrix - target.matrix))
    _ = ∑ j, (E.probs j : ℝ) *
        traceNorm ((E.states j).matrix - target.matrix) := by
      apply Finset.sum_congr rfl
      intro j _
      change traceNorm (((E.probs j : ℝ) : ℂ) •
          ((E.states j).matrix - target.matrix)) =
        (E.probs j : ℝ) * traceNorm ((E.states j).matrix - target.matrix)
      rw [traceNorm_real_smul_eq (NNReal.coe_nonneg (E.probs j))]

omit [DecidableEq i] in
/-- Squared fidelity with a pure target is affine over a state ensemble. -/
private theorem sum_prob_mul_squaredFidelity_eq_averageState
    (E : Ensemble i s) (target : PureVector s) :
    (∑ j, (E.probs j : ℝ) * (E.states j).squaredFidelity target.state) =
      E.averageState.squaredFidelity target.state := by
  rw [State.squaredFidelity_pure_right_eq_trace E.averageState target]
  calc
    (∑ j, (E.probs j : ℝ) * (E.states j).squaredFidelity target.state) =
        ∑ j, (((E.probs j : ℂ) *
          (((E.states j).matrix * target.state.matrix).trace)).re) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [State.squaredFidelity_pure_right_eq_trace]
      simp [Complex.mul_re]
    _ = (((∑ j, (E.probs j : ℂ) • (E.states j).matrix) *
          target.state.matrix).trace).re := by
      simp [Finset.sum_mul, Matrix.trace_sum, Matrix.trace_smul, Complex.mul_re]
    _ = ((E.averageState.matrix * target.state.matrix).trace).re := by
      simp [NNReal.smul_def]

omit [DecidableEq i] in
/-- Jensen's square-root estimate for an arbitrary finite state ensemble. -/
private theorem sum_prob_mul_sqrt_one_sub_squaredFidelity_le
    (E : Ensemble i s) (target : PureVector s) :
    (∑ j, (E.probs j : ℝ) *
      Real.sqrt (1 - (E.states j).squaredFidelity target.state)) ≤
      Real.sqrt (1 - E.averageState.squaredFidelity target.state) := by
  classical
  let deficit : i → ℝ :=
    fun j ↦ 1 - (E.states j).squaredFidelity target.state
  have hdeficit : ∀ j, deficit j ∈ Set.Ici (0 : ℝ) := by
    intro j
    exact sub_nonneg.mpr (State.squaredFidelity_le_one _ _)
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
    (E : Ensemble i s) (target : PureVector s) :
    (∑ j, (E.probs j : ℝ) * (E.states j).traceNormDistance target.state) ≤
      2 * Real.sqrt
        (1 - E.averageState.squaredFidelity target.state) := by
  have hfdg (j : i) :
      (E.states j).traceNormDistance target.state ≤
        2 * Real.sqrt (1 - (E.states j).squaredFidelity target.state) := by
    have h := State.fuchs_van_de_graaf_upper (E.states j) target.state
    simpa [State.normalizedTraceDistance, QIT.normalizedTraceDistance] using
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

end Ensemble

private theorem normalizedTraceDistance_reindex_equiv
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (rho sigma : State A) (e : A ≃ B) :
    (rho.reindex e).normalizedTraceDistance (sigma.reindex e) =
      rho.normalizedTraceDistance sigma := by
  change (1 / 2 : ℝ) *
      traceNorm
        (rho.matrix.submatrix e.symm e.symm - sigma.matrix.submatrix e.symm e.symm) =
    (1 / 2 : ℝ) * traceNorm (rho.matrix - sigma.matrix)
  have hsub :
      rho.matrix.submatrix e.symm e.symm - sigma.matrix.submatrix e.symm e.symm =
        (rho.matrix - sigma.matrix).submatrix e.symm e.symm := by
    ext a b
    rfl
  rw [hsub, traceNorm_submatrix_equiv]

private theorem squaredFidelity_reindex_equiv
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (rho sigma : State A) (e : A ≃ B) :
    (rho.reindex e).squaredFidelity (sigma.reindex e) =
      rho.squaredFidelity sigma := by
  rw [State.squaredFidelity_eq_fidelity_sq, State.squaredFidelity_eq_fidelity_sq,
    SmoothNormalizedExtension.State.fidelity_reindex]

private theorem reindexChannel_map
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (X : CMatrix A) :
    (Channel.reindex e).map X = X.submatrix e.symm e.symm := by
  ext i j
  simp [Channel.reindex, MatrixMap.ofReferenceIsometry_apply,
    ReferenceIsometry.ofEquiv, Matrix.mul_apply]
  rw [Finset.sum_eq_single (e.symm j)]
  · rw [Finset.sum_eq_single (e.symm i)]
    · simp
    · intro x _ hx
      have hne : i ≠ e x := by
        intro hi
        apply hx
        simp [hi]
      simp [hne]
    · simp
  · intro x _ hx
    have hne : j ≠ e x := by
      intro hj
      apply hx
      simp [hj]
    simp [hne]
  · simp

private theorem reindexChannel_map_single
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (i j : A) :
    (Channel.reindex e).map (Matrix.single i j (1 : ℂ)) =
      Matrix.single (e i) (e j) (1 : ℂ) := by
  rw [reindexChannel_map]
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.single_apply]
  have hx : i = e.symm x ↔ e i = x := by
    constructor
    · intro h
      rw [h, e.apply_symm_apply]
    · intro h
      apply e.injective
      rw [e.apply_symm_apply, h]
  have hy : j = e.symm y ↔ e j = y := by
    constructor
    · intro h
      rw [h, e.apply_symm_apply]
    · intro h
      apply e.injective
      rw [e.apply_symm_apply, h]
  simp only [hx, hy]

private theorem reindexChannel_map_symm_map
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (X : CMatrix B) :
    (Channel.reindex e).map ((Channel.reindex e.symm).map X) = X := by
  rw [reindexChannel_map, reindexChannel_map]
  ext i j
  simp

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
        (Channel.reindex (Equiv.prodAssoc A R B)).map =
      (Channel.reindex (Equiv.prodAssoc A' R' B')).map.comp
        (MatrixMap.kron (MatrixMap.kron PhiA PhiR) PhiB) := by
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single
    ((MatrixMap.kron PhiA (MatrixMap.kron PhiR PhiB)).comp
      (Channel.reindex (Equiv.prodAssoc A R B)).map) X]
  rw [MatrixMap.map_eq_sum_single
    ((Channel.reindex (Equiv.prodAssoc A' R' B')).map.comp
      (MatrixMap.kron (MatrixMap.kron PhiA PhiR) PhiB)) X]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  change MatrixMap.kron PhiA (MatrixMap.kron PhiR PhiB)
      ((Channel.reindex (Equiv.prodAssoc A R B)).map
        (Matrix.single i j (1 : ℂ))) =
    (Channel.reindex (Equiv.prodAssoc A' R' B')).map
      (MatrixMap.kron (MatrixMap.kron PhiA PhiR) PhiB
        (Matrix.single i j (1 : ℂ)))
  rw [reindexChannel_map_single]
  rw [show Matrix.single (Equiv.prodAssoc A R B i)
      (Equiv.prodAssoc A R B j) (1 : ℂ) =
        Matrix.kronecker
          (Matrix.single i.1.1 j.1.1 (1 : ℂ))
          (Matrix.single (i.1.2, i.2) (j.1.2, j.2) (1 : ℂ)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_apply_kronecker]
  rw [show Matrix.single (i.1.2, i.2) (j.1.2, j.2) (1 : ℂ) =
        Matrix.kronecker
          (Matrix.single i.1.2 j.1.2 (1 : ℂ))
          (Matrix.single i.2 j.2 (1 : ℂ)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_apply_kronecker]
  rw [show Matrix.single i j (1 : ℂ) =
        Matrix.kronecker
          (Matrix.single i.1 j.1 (1 : ℂ))
          (Matrix.single i.2 j.2 (1 : ℂ)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_apply_kronecker]
  rw [show Matrix.single i.1 j.1 (1 : ℂ) =
        Matrix.kronecker
          (Matrix.single i.1.1 j.1.1 (1 : ℂ))
          (Matrix.single i.1.2 j.1.2 (1 : ℂ)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_apply_kronecker, reindexChannel_map]
  ext k l
  simp [Matrix.kronecker, mul_assoc]

private theorem kron_idChannel_idChannel_eq_idChannel_map
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] :
    MatrixMap.kron (Channel.idChannel A).map (Channel.idChannel B).map =
      (Channel.idChannel (Prod A B)).map := by
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single
    (MatrixMap.kron (Channel.idChannel A).map (Channel.idChannel B).map) X]
  rw [MatrixMap.map_eq_sum_single (Channel.idChannel (Prod A B)).map X]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [show Matrix.single i j (1 : ℂ) =
      Matrix.kronecker (Matrix.single i.1 j.1 (1 : ℂ))
        (Matrix.single i.2 j.2 (1 : ℂ)) by
    exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_apply_kronecker]
  rw [Channel.idChannel_map_eq_linearMap_id (α := A),
    Channel.idChannel_map_eq_linearMap_id (α := B),
    Channel.idChannel_map_eq_linearMap_id (α := Prod A B)]
  rfl

private theorem sum_rankOne_localPostAmplitude_eq_kron_ofKraus
    {A : Type u} {A' : Type v} {B : Type w} {K : Type x}
    [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype K]
    (kraus : K → Matrix A' A ℂ) (amp : Prod A B → ℂ) :
    (∑ k : K,
        rankOneMatrix (fun out : Prod A' B =>
          ∑ a : A, kraus k out.1 a * amp (a, out.2))) =
      MatrixMap.kron (MatrixMap.ofKraus kraus) (Channel.idChannel B).map
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
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A B)) (result : X) :
    (∑ k : A × A', rankOneMatrix (M.postAmplitude psi (result, k))) =
      MatrixMap.kron (M.branch result) (Channel.idChannel B).map
        psi.state.matrix := by
  rw [← (M.branchTraceNonincreasingCP result).ofKraus_kraus]
  simpa [FiniteInstrument.postAmplitude, FiniteInstrument.refinedKraus,
    PureVector.state_matrix] using
    (sum_rankOne_localPostAmplitude_eq_kron_ofKraus
      (M.branchTraceNonincreasingCP result).kraus psi.amp)

private theorem traceNormDistance_marginalA_le
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (rho sigma : State (Prod A B)) :
    rho.marginalA.traceNormDistance sigma.marginalA ≤ rho.traceNormDistance sigma := by
  change traceNorm
      (partialTraceB (a := A) (b := B) rho.matrix -
        partialTraceB (a := A) (b := B) sigma.matrix) ≤
    traceNorm (rho.matrix - sigma.matrix)
  rw [← partialTraceB_sub]
  exact traceNorm_partialTraceB_le_matrix (rho.matrix - sigma.matrix)

private theorem sum_sum_sum_mul_right
    {I : Type u} {K : Type v} {J : Type w}
    [Fintype I] [Fintype K] [Fintype J]
    (f : I → K → ℂ) (g : J → ℂ) :
    (∑ i, ∑ k, ∑ j, f i k * g j) =
      (∑ j, g j) * (∑ i, ∑ k, f i k) := by
  calc
    (∑ i, ∑ k, ∑ j, f i k * g j) =
        ∑ i, ∑ k, f i k * ∑ j, g j := by
      simp [Finset.mul_sum]
    _ = (∑ i, ∑ k, f i k) * ∑ j, g j := by
      simp [Finset.sum_mul]
    _ = (∑ j, g j) * (∑ i, ∑ k, f i k) := by ring

namespace OneWayLOCC

variable {A : Type u} {A' : Type v} {B B' X : Type*}
variable [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
variable [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype X]

/-- The physical output conditioned only on Alice's refined local outcome;
Bob's complete channel is applied nonselectively. -/
def aliceConditionedOutputState
    (L : OneWayLOCC A A' B B' X) (input : PureVector (Prod A B))
    (i : L.aliceInstrument.positiveSupport input) : State (Prod A' B') :=
  ((Channel.idChannel A').prod (L.bobChannel i.1.1)).applyState
    (L.aliceInstrument.normalizedBranch input i).state

/-- Averaging the Alice-conditioned, nonselective Bob outputs recovers the
realized one-way LOCC output. -/
theorem sum_alicePositiveBranchWeight_smul_conditionedOutputState_matrix
    (L : OneWayLOCC A A' B B' X) (input : PureVector (Prod A B)) :
    (∑ i : L.aliceInstrument.positiveSupport input,
      L.aliceInstrument.branchWeight input i.1 •
        (L.aliceConditionedOutputState input i).matrix) =
      L.toChannel.map input.state.matrix := by
  classical
  let f : L.aliceInstrument.refinedBranchIndex → CMatrix (Prod A' B') :=
    fun i ↦ ((Channel.idChannel A').prod (L.bobChannel i.1)).map
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
          (L.aliceConditionedOutputState input i).matrix) =
        ∑ i : L.aliceInstrument.positiveSupport input, f i.1 := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [f]
      change ((L.aliceInstrument.branchWeight input i.1 : ℂ) •
          ((Channel.idChannel A').prod (L.bobChannel i.1.1)).map
            (L.aliceInstrument.normalizedBranch input i).state.matrix) =
        ((Channel.idChannel A').prod (L.bobChannel i.1.1)).map
          (rankOneMatrix (L.aliceInstrument.postAmplitude input i.1))
      rw [← map_smul]
      congr 1
      simpa only [NNReal.smul_def] using
        L.aliceInstrument.branchWeight_smul_normalizedBranch_state_matrix input i
    _ = ∑ i : L.aliceInstrument.refinedBranchIndex, f i := hsupport
    _ = ∑ result : X, ∑ k : A × A', f (result, k) := by
      simp only [FiniteInstrument.refinedBranchIndex, Fintype.sum_prod_type]
    _ = ∑ result : X,
        ((Channel.idChannel A').prod (L.bobChannel result)).map
          (∑ k : A × A',
            rankOneMatrix (L.aliceInstrument.postAmplitude input (result, k))) := by
      apply Finset.sum_congr rfl
      intro result _
      rw [map_sum]
    _ = ∑ result : X,
        ((Channel.idChannel A').prod (L.bobChannel result)).map
          (MatrixMap.kron (L.aliceInstrument.branch result)
            (Channel.idChannel B).map input.state.matrix) := by
      apply Finset.sum_congr rfl
      intro result _
      rw [L.aliceInstrument.sum_rankOne_postAmplitude_fixedOutcome input result]
    _ = ∑ result : X,
        MatrixMap.kron (L.aliceInstrument.branch result)
          (L.bobChannel result).map input.state.matrix := by
      apply Finset.sum_congr rfl
      intro result _
      calc
        ((Channel.idChannel A').prod (L.bobChannel result)).map
            (MatrixMap.kron (L.aliceInstrument.branch result)
              (Channel.idChannel B).map input.state.matrix) =
            MatrixMap.kron
              ((Channel.idChannel A').map.comp
                (L.aliceInstrument.branch result))
              ((L.bobChannel result).map.comp (Channel.idChannel B).map)
              input.state.matrix := by
          exact MatrixMap.kron_comp_apply_general
            (Channel.idChannel A').map (L.bobChannel result).map
            (L.aliceInstrument.branch result) (Channel.idChannel B).map
            input.state.matrix
        _ = MatrixMap.kron (L.aliceInstrument.branch result)
            (L.bobChannel result).map input.state.matrix := by
          rw [Channel.idChannel_map_eq_linearMap_id (α := A'),
            Channel.idChannel_map_eq_linearMap_id (α := B)]
          simp only [LinearMap.id_comp, LinearMap.comp_id]
    _ = L.toChannel.map input.state.matrix := by
      rw [L.toChannel_map, LinearMap.sum_apply]

end OneWayLOCC

/-- Reorder Alice's recorded cq state so that the retained `L_A` register is
the source and the untouched reference together with Alice's local outcome is
the conditioning system. -/
def stateMergingRecordedOutcomeEquiv
    (J : Type u) (L : Type v) (R : Type w) :
    Prod J (Prod L R) ≃ Prod L (Prod R J) where
  toFun t := (t.2.1, (t.2.2, t.1))
  invFun t := (t.2.2, (t.1, t.2.1))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

/-- Reorder the untouched reference and Alice's local outcome. -/
def stateMergingRecordedConditioningEquiv
    (J : Type u) (R : Type v) : Prod J R ≃ Prod R J :=
  Equiv.prodComm J R

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

namespace StateMergingBlockProtocol

local instance localConverseOutputDecidableEq :
    DecidableEq
      (Prod lA
        (Prod (TensorPower r n)
          (Prod (Prod (TensorPower a n) (TensorPower b n)) lB))) :=
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
def localConverseInputPureVector :
    PureVector
      (Prod (Prod (TensorPower a n) kA)
        (Prod (TensorPower r n) (Prod (TensorPower b n) kB))) :=
  C.converseInputPureVector.reindex
    (Equiv.prodAssoc
      (Prod (TensorPower a n) kA)
      (TensorPower r n)
      (Prod (TensorPower b n) kB))

@[simp]
theorem localConverseInputPureVector_reindex_symm :
    C.localConverseInputPureVector.reindex
        (Equiv.prodAssoc
          (Prod (TensorPower a n) kA)
          (TensorPower r n)
          (Prod (TensorPower b n) kB)).symm =
      C.converseInputPureVector := by
  apply PureVector.ext_amp
  funext i
  rfl

/-- The same physical one-way LOCC map in the local grouping
`A | (R B)`.  Alice's instrument is exactly the protocol's original local
instrument; the reference identity is carried only by Bob's channel. -/
def localConverseLOCC :
    OneWayLOCC
      (Prod (TensorPower a n) kA)
      lA
      (Prod (TensorPower r n) (Prod (TensorPower b n) kB))
      (Prod (TensorPower r n)
        (Prod (Prod (TensorPower a n) (TensorPower b n)) lB))
      outcome :=
  OneWayLOCC.ofFiniteInstrument C.locc.aliceInstrument
    (fun result ↦
      (Channel.idChannel (TensorPower r n)).prod (C.locc.bobChannel result))

/-- The ideal target in the local grouping `L_A | (R^n B')`. -/
def localConverseTargetPureVector :
    PureVector
      (Prod lA
        (Prod (TensorPower r n)
          (Prod (Prod (TensorPower a n) (TensorPower b n)) lB))) :=
  C.converseTargetPureVector.reindex
    (Equiv.prodAssoc lA (TensorPower r n)
      (Prod (Prod (TensorPower a n) (TensorPower b n)) lB))

/-- Reassociation identifies the local physical output with the existing
reference-lifted converse output. -/
theorem localConverseLOCC_applyState :
    C.localConverseLOCC.toChannel.applyState C.localConverseInputPureVector.state =
      (C.converseLOCC.toChannel.applyState C.converseInputPureVector.state).reindex
        (Equiv.prodAssoc lA (TensorPower r n)
          (Prod (Prod (TensorPower a n) (TensorPower b n)) lB)) := by
  apply State.ext
  simp only [Channel.applyState, State.reindex]
  rw [← reindexChannel_map
    (Equiv.prodAssoc lA (TensorPower r n)
      (Prod (Prod (TensorPower a n) (TensorPower b n)) lB))
    (C.converseLOCC.toChannel.map C.converseInputPureVector.state.matrix)]
  simp only [localConverseLOCC, OneWayLOCC.ofFiniteInstrument,
    localConverseInputPureVector, PureVector.reindex_state, converseLOCC,
    OneWayLOCC.prodIdRight, OneWayLOCC.toChannel_map,
    FiniteInstrument.prodIdRight_branch, Channel.prod, State.reindex,
    LinearMap.sum_apply, map_sum]
  rw [← reindexChannel_map
    (Equiv.prodAssoc (Prod (TensorPower a n) kA) (TensorPower r n)
      (Prod (TensorPower b n) kB))
    C.converseInputPureVector.state.matrix]
  apply Finset.sum_congr rfl
  intro result _
  exact LinearMap.congr_fun
    (prodAssoc_kron_naturality
      (C.locc.aliceInstrument.branch result)
      (Channel.idChannel (TensorPower r n)).map
      (C.locc.bobChannel result).map)
    C.converseInputPureVector.state.matrix

/-- The locally grouped protocol has exactly the block protocol's computed
fidelity deficit. -/
theorem localConverseLOCC_fidelityError :
    1 - (C.localConverseLOCC.toChannel.applyState
        C.localConverseInputPureVector.state).squaredFidelity
          C.localConverseTargetPureVector.state = C.fidelityError := by
  rw [C.localConverseLOCC_applyState]
  simp only [localConverseTargetPureVector, PureVector.reindex_state,
    squaredFidelity_reindex_equiv]
  exact C.converseLOCC_fidelityError

/-- Source-faithful refined Alice outcomes before the reference lift. -/
abbrev originalRecordedOutcomeIndex :=
  C.locc.aliceInstrument.positiveSupport C.localConverseInputPureVector

local instance originalRecordedOutcomeIndexDecidableEq :
    DecidableEq C.originalRecordedOutcomeIndex :=
  Classical.decEq _

/-- The state after Bob's complete conditional channel on one original
positive Alice branch.  Bob's Kraus outcomes are summed nonselectively. -/
def originalAlicePostBobBranchState
    (i : C.originalRecordedOutcomeIndex) :
    State
      (Prod (Prod lA (TensorPower r n))
        (Prod (Prod (TensorPower a n) (TensorPower b n)) lB)) :=
  ((Channel.idChannel (Prod lA (TensorPower r n))).prod
      (C.locc.bobChannel i.1.1)).applyState
    ((C.locc.aliceInstrument.normalizedBranch
      C.localConverseInputPureVector i).state.reindex
        (sourceReferenceRegroupEquiv lA (TensorPower r n)
          (Prod (TensorPower b n) kB)))

/-- Reassociating one original Alice branch identifies its nonselective Bob
output with the corresponding branch of the locally grouped LOCC map. -/
theorem originalAlicePostBobBranchState_reindex
    (i : C.originalRecordedOutcomeIndex) :
    (C.originalAlicePostBobBranchState i).reindex
        (Equiv.prodAssoc lA (TensorPower r n)
          (Prod (Prod (TensorPower a n) (TensorPower b n)) lB)) =
      C.localConverseLOCC.aliceConditionedOutputState
        C.localConverseInputPureVector i := by
  apply State.ext
  simp only [originalAlicePostBobBranchState,
    OneWayLOCC.aliceConditionedOutputState, localConverseLOCC,
    Channel.applyState, State.reindex]
  let rho :=
    (C.locc.aliceInstrument.normalizedBranch
      C.localConverseInputPureVector i).state
  rw [← reindexChannel_map
    (Equiv.prodAssoc lA (TensorPower r n)
      (Prod (Prod (TensorPower a n) (TensorPower b n)) lB))]
  rw [show sourceReferenceRegroupEquiv lA (TensorPower r n)
      (Prod (TensorPower b n) kB) =
        (Equiv.prodAssoc lA (TensorPower r n)
          (Prod (TensorPower b n) kB)).symm by rfl]
  rw [← reindexChannel_map
    (Equiv.prodAssoc lA (TensorPower r n)
      (Prod (TensorPower b n) kB)).symm]
  change (Channel.reindex
      (Equiv.prodAssoc lA (TensorPower r n)
        (Prod (Prod (TensorPower a n) (TensorPower b n)) lB))).map
      (MatrixMap.kron (Channel.idChannel (Prod lA (TensorPower r n))).map
        (C.locc.bobChannel i.1.1).map
        ((Channel.reindex
          (Equiv.prodAssoc lA (TensorPower r n)
            (Prod (TensorPower b n) kB)).symm).map rho.matrix)) =
    MatrixMap.kron (Channel.idChannel lA).map
      (MatrixMap.kron (Channel.idChannel (TensorPower r n)).map
        (C.locc.bobChannel i.1.1).map) rho.matrix
  rw [← kron_idChannel_idChannel_eq_idChannel_map
    (A := lA) (B := TensorPower r n)]
  have h := LinearMap.congr_fun
    (prodAssoc_kron_naturality
      (Channel.idChannel lA).map
      (Channel.idChannel (TensorPower r n)).map
      (C.locc.bobChannel i.1.1).map)
    ((Channel.reindex
      (Equiv.prodAssoc lA (TensorPower r n)
        (Prod (TensorPower b n) kB)).symm).map rho.matrix)
  simp only [LinearMap.comp_apply] at h
  rw [reindexChannel_map_symm_map] at h
  exact h.symm

/-- Bob's trace-preserving conditional channel leaves the retained Alice
register and untouched reference marginal unchanged. -/
theorem originalAlicePostBobBranchState_marginalA
    (i : C.originalRecordedOutcomeIndex) :
    (C.originalAlicePostBobBranchState i).marginalA =
      C.locc.aliceInstrument.positiveBranchSourceReferenceState
        C.localConverseInputPureVector i := by
  rw [originalAlicePostBobBranchState,
    State.marginalA_applyState_id_prod]
  rfl

/-- Original Alice branches after Bob is summed out, with the physical
Alice branch weights. -/
def originalAlicePostBobEnsemble :
    Ensemble C.originalRecordedOutcomeIndex
      (Prod (Prod lA (TensorPower r n))
        (Prod (Prod (TensorPower a n) (TensorPower b n)) lB)) where
  probs i := C.locc.aliceInstrument.branchWeight
    C.localConverseInputPureVector i.1
  weights_sum := C.locc.aliceInstrument.sum_positiveSupport_branchWeight_eq_one
    C.localConverseInputPureVector
  states i := C.originalAlicePostBobBranchState i

/-- The nonselective average over original Alice outcomes is the existing
physical converse output. -/
theorem originalAlicePostBobEnsemble_averageState :
    C.originalAlicePostBobEnsemble.averageState =
      C.converseLOCC.toChannel.applyState C.converseInputPureVector.state := by
  have hlocal :
      C.originalAlicePostBobEnsemble.averageState.reindex
          (Equiv.prodAssoc lA (TensorPower r n)
            (Prod (Prod (TensorPower a n) (TensorPower b n)) lB)) =
        C.localConverseLOCC.toChannel.applyState
          C.localConverseInputPureVector.state := by
    apply State.ext
    simp only [State.reindex, Channel.applyState]
    rw [← reindexChannel_map
      (Equiv.prodAssoc lA (TensorPower r n)
        (Prod (Prod (TensorPower a n) (TensorPower b n)) lB))]
    change (Channel.reindex
        (Equiv.prodAssoc lA (TensorPower r n)
          (Prod (Prod (TensorPower a n) (TensorPower b n)) lB))).map
        C.originalAlicePostBobEnsemble.averageState.matrix =
      C.localConverseLOCC.toChannel.map C.localConverseInputPureVector.state.matrix
    rw [Ensemble.averageState_matrix, map_sum]
    calc
      (∑ i : C.originalRecordedOutcomeIndex,
          (Channel.reindex
            (Equiv.prodAssoc lA (TensorPower r n)
              (Prod (Prod (TensorPower a n) (TensorPower b n)) lB))).map
            (C.originalAlicePostBobEnsemble.probs i •
              (C.originalAlicePostBobEnsemble.states i).matrix)) =
          ∑ i : C.originalRecordedOutcomeIndex,
            C.localConverseLOCC.aliceInstrument.branchWeight
                C.localConverseInputPureVector i.1 •
              (C.localConverseLOCC.aliceConditionedOutputState
                C.localConverseInputPureVector i).matrix := by
        apply Finset.sum_congr rfl
        intro i _
        rw [LinearMap.map_smul_of_tower, reindexChannel_map]
        simp only [originalAlicePostBobEnsemble]
        change (C.locc.aliceInstrument.branchWeight
              C.localConverseInputPureVector i.1 : Complex) •
            ((C.originalAlicePostBobBranchState i).reindex
              (Equiv.prodAssoc lA (TensorPower r n)
                (Prod (Prod (TensorPower a n) (TensorPower b n)) lB))).matrix = _
        rw [C.originalAlicePostBobBranchState_reindex i]
        ext j k
        simp [NNReal.smul_def, Matrix.smul_apply, Complex.real_smul,
          localConverseLOCC, OneWayLOCC.ofFiniteInstrument]
      _ = C.localConverseLOCC.toChannel.map
          C.localConverseInputPureVector.state.matrix :=
        C.localConverseLOCC.sum_alicePositiveBranchWeight_smul_conditionedOutputState_matrix
          C.localConverseInputPureVector
  rw [C.localConverseLOCC_applyState] at hlocal
  have h := congrArg
    (fun rho ↦ rho.reindex
      (Equiv.prodAssoc lA (TensorPower r n)
        (Prod (Prod (TensorPower a n) (TensorPower b n)) lB)).symm)
    hlocal
  simpa [State.reindex_symm_reindex] using h

/-- Berta's physical recorded state on `L_A | (R^n X_A)`, built from the
original Alice instrument rather than the canonical Kraus refinement of its
reference lift. -/
def originalRecordedOutcomeState :
    State
      (Prod lA (Prod (TensorPower r n) C.originalRecordedOutcomeIndex)) :=
  C.locc.aliceInstrument.recordedSourceReferenceState
    C.localConverseInputPureVector

/-- The ideal target on Alice's retained ebit half and the untouched
reference is the product of the maximally mixed ebit marginal and the source
reference marginal. -/
theorem converseTargetPureVector_marginalA_eq_maximallyMixed_prod :
    C.converseTargetPureVector.state.marginalA =
      (State.maximallyMixed lA).prod
        (stateMergingBlockSource psi n).state.marginalB := by
  apply State.ext
  ext i j
  simp [converseTargetPureVector, targetPureVector,
    stateMergingConverseOutputEquiv, stateMergingTargetEquiv,
    PureVector.reindex_state, PureVector.prod_state, State.reindex, State.prod,
    State.maximallyMixed, State.marginalA, State.marginalB, partialTraceA,
    partialTraceB, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type]
  have hebit :
      (∑ k : lB,
        (PureVector.maximallyEntangled C.outputEbitPairing).amp (i.1, k) *
          star ((PureVector.maximallyEntangled C.outputEbitPairing).amp (j.1, k))) =
        (Fintype.card lA : ℂ)⁻¹ * (1 : CMatrix lA) i.1 j.1 := by
    have h := congrArg (fun rho : State lA => rho.matrix i.1 j.1)
      (PureVector.maximallyEntangled_marginalA C.outputEbitPairing)
    simpa [State.marginalA, partialTraceB, PureVector.state,
      rankOneMatrix_apply, State.maximallyMixed] using h
  calc
    (∑ x, ∑ y, ∑ k,
        (stateMergingBlockSource psi n).amp ((x, y), i.2) *
            star ((stateMergingBlockSource psi n).amp ((x, y), j.2)) *
          ((PureVector.maximallyEntangled C.outputEbitPairing).amp (i.1, k) *
            star ((PureVector.maximallyEntangled C.outputEbitPairing).amp (j.1, k)))) =
        (∑ k : lB,
          (PureVector.maximallyEntangled C.outputEbitPairing).amp (i.1, k) *
            star ((PureVector.maximallyEntangled C.outputEbitPairing).amp (j.1, k))) *
          (∑ x, ∑ y,
            (stateMergingBlockSource psi n).amp ((x, y), i.2) *
              star ((stateMergingBlockSource psi n).amp ((x, y), j.2))) := by
      exact sum_sum_sum_mul_right
        (fun x y =>
          (stateMergingBlockSource psi n).amp ((x, y), i.2) *
            star ((stateMergingBlockSource psi n).amp ((x, y), j.2)))
        (fun k =>
          (PureVector.maximallyEntangled C.outputEbitPairing).amp (i.1, k) *
            star ((PureVector.maximallyEntangled C.outputEbitPairing).amp (j.1, k)))
    _ = (Fintype.card lA : ℂ)⁻¹ * (1 : CMatrix lA) i.1 j.1 *
          ∑ x, ∑ y,
            (stateMergingBlockSource psi n).amp ((x, y), i.2) *
              star ((stateMergingBlockSource psi n).amp ((x, y), j.2)) := by
      rw [hebit]

/-- Alice's positive refined local-instrument outcomes.  Bob's Kraus index is
deliberately absent from this source-faithful Berta record. -/
abbrev recordedOutcomeIndex :=
  C.originalRecordedOutcomeIndex

local instance recordedOutcomeIndexDecidableEq :
    DecidableEq C.recordedOutcomeIndex :=
  Classical.decEq _

/-- Physical post-Alice states on `L_A R^n`, with Alice's operational branch
probabilities. -/
def recordedOutcomeEnsemble :
    Ensemble C.recordedOutcomeIndex (Prod lA (TensorPower r n)) where
  probs i :=
    C.locc.aliceInstrument.branchWeight C.localConverseInputPureVector i.1
  weights_sum :=
    C.locc.aliceInstrument.sum_positiveSupport_branchWeight_eq_one
      C.localConverseInputPureVector
  states i :=
    C.locc.aliceInstrument.positiveBranchSourceReferenceState
      C.localConverseInputPureVector i

/-- The ideal `L_A R^n` branch, repeated with the same Alice-outcome
distribution as the physical ensemble. -/
def idealRecordedOutcomeEnsemble :
    Ensemble C.recordedOutcomeIndex (Prod lA (TensorPower r n)) where
  probs i :=
    C.locc.aliceInstrument.branchWeight C.localConverseInputPureVector i.1
  weights_sum :=
    C.locc.aliceInstrument.sum_positiveSupport_branchWeight_eq_one
      C.localConverseInputPureVector
  states _ :=
    (State.maximallyMixed lA).prod
      (stateMergingBlockSource psi n).state.marginalB

/-- Alice's physical cq record, reordered onto `L_A (R^n X_A)`. -/
def recordedOutcomeState :
    State (Prod lA (Prod (TensorPower r n) C.recordedOutcomeIndex)) :=
  C.recordedOutcomeEnsemble.cqState.reindex
    (stateMergingRecordedOutcomeEquiv
      C.recordedOutcomeIndex lA (TensorPower r n))

/-- The same-weight ideal cq record on `L_A (R^n X_A)`. -/
def idealRecordedOutcomeState :
    State (Prod lA (Prod (TensorPower r n) C.recordedOutcomeIndex)) :=
  C.idealRecordedOutcomeEnsemble.cqState.reindex
    (stateMergingRecordedOutcomeEquiv
      C.recordedOutcomeIndex lA (TensorPower r n))

/-- The ideal side-information ensemble on the untouched reference. -/
def idealRecordedConditioningEnsemble :
    Ensemble C.recordedOutcomeIndex (TensorPower r n) where
  probs i :=
    C.locc.aliceInstrument.branchWeight C.localConverseInputPureVector i.1
  weights_sum :=
    C.locc.aliceInstrument.sum_positiveSupport_branchWeight_eq_one
      C.localConverseInputPureVector
  states _ := (stateMergingBlockSource psi n).state.marginalB

/-- The ideal conditioning state on `R^n X_A`. -/
def idealRecordedConditioningState :
    State (Prod (TensorPower r n) C.recordedOutcomeIndex) :=
  C.idealRecordedConditioningEnsemble.cqState.reindex
    (stateMergingRecordedConditioningEquiv
      C.recordedOutcomeIndex (TensorPower r n))

@[simp]
theorem idealRecordedOutcomeEnsemble_states_eq_target
    (i : C.recordedOutcomeIndex) :
    C.idealRecordedOutcomeEnsemble.states i =
      C.converseTargetPureVector.state.marginalA := by
  exact C.converseTargetPureVector_marginalA_eq_maximallyMixed_prod.symm

/-- The ideal Alice-record state is a uniform retained-ebit register
independent of the untouched reference and Alice's classical outcome. -/
theorem idealRecordedOutcomeState_eq_maximallyMixed_prod :
    C.idealRecordedOutcomeState =
      (State.maximallyMixed lA).prod C.idealRecordedConditioningState := by
  apply State.ext
  ext i j
  simp [idealRecordedOutcomeState, idealRecordedConditioningState,
    idealRecordedOutcomeEnsemble, idealRecordedConditioningEnsemble,
    stateMergingRecordedOutcomeEquiv, stateMergingRecordedConditioningEquiv,
    Ensemble.cqState, State.reindex, State.prod, Matrix.kronecker,
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
  rw [C.idealRecordedOutcomeState_eq_maximallyMixed_prod]
  exact State.conditionalMinEntropy_maximallyMixed_prod
    C.idealRecordedConditioningState

@[simp]
theorem idealRecordedOutcomeEnsemble_probs (i : C.recordedOutcomeIndex) :
    C.idealRecordedOutcomeEnsemble.probs i = C.recordedOutcomeEnsemble.probs i :=
  rfl

/-- Alice's recorded physical state is within `sqrt fidelityError` in
normalized trace distance of the same-weight ideal record. -/
theorem recordedOutcomeState_normalizedTraceDistance_le_sqrt_fidelityError :
    C.recordedOutcomeState.normalizedTraceDistance C.idealRecordedOutcomeState ≤
      Real.sqrt C.fidelityError := by
  rw [recordedOutcomeState, idealRecordedOutcomeState,
    normalizedTraceDistance_reindex_equiv]
  rw [Ensemble.cqState_normalizedTraceDistance_eq_sum_of_same_probs
    C.recordedOutcomeEnsemble C.idealRecordedOutcomeEnsemble
    C.idealRecordedOutcomeEnsemble_probs]
  have hfull :=
    C.originalAlicePostBobEnsemble.sum_prob_mul_traceNormDistance_le_pure
      C.converseTargetPureVector
  rw [C.originalAlicePostBobEnsemble_averageState,
    C.converseLOCC_fidelityError] at hfull
  have havg :
      (∑ i : C.recordedOutcomeIndex,
        (C.locc.aliceInstrument.branchWeight
          C.localConverseInputPureVector i.1 : ℝ) *
          (C.locc.aliceInstrument.positiveBranchSourceReferenceState
            C.localConverseInputPureVector i).traceNormDistance
              C.converseTargetPureVector.state.marginalA) ≤
        2 * Real.sqrt C.fidelityError := by
    calc
      (∑ i : C.recordedOutcomeIndex,
          (C.locc.aliceInstrument.branchWeight
            C.localConverseInputPureVector i.1 : ℝ) *
            (C.locc.aliceInstrument.positiveBranchSourceReferenceState
              C.localConverseInputPureVector i).traceNormDistance
                C.converseTargetPureVector.state.marginalA) =
          ∑ i : C.recordedOutcomeIndex,
            (C.originalAlicePostBobEnsemble.probs i : ℝ) *
              (C.originalAlicePostBobEnsemble.states i).marginalA.traceNormDistance
                C.converseTargetPureVector.state.marginalA := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [originalAlicePostBobEnsemble]
        rw [C.originalAlicePostBobBranchState_marginalA i]
      _ ≤ ∑ i : C.recordedOutcomeIndex,
          (C.originalAlicePostBobEnsemble.probs i : ℝ) *
            (C.originalAlicePostBobEnsemble.states i).traceNormDistance
              C.converseTargetPureVector.state := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (traceNormDistance_marginalA_le _ _) (NNReal.coe_nonneg _)
      _ ≤ 2 * Real.sqrt C.fidelityError := hfull
  calc
    (∑ i : C.recordedOutcomeIndex,
        (C.recordedOutcomeEnsemble.probs i : ℝ) *
          (C.recordedOutcomeEnsemble.states i).normalizedTraceDistance
            (C.idealRecordedOutcomeEnsemble.states i)) =
        (1 / 2 : ℝ) *
          ∑ i : C.recordedOutcomeIndex,
            (C.locc.aliceInstrument.branchWeight
                C.localConverseInputPureVector i.1 : ℝ) *
              (C.locc.aliceInstrument.positiveBranchSourceReferenceState
                C.localConverseInputPureVector i).traceNormDistance
                  C.converseTargetPureVector.state.marginalA := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [recordedOutcomeEnsemble,
        C.idealRecordedOutcomeEnsemble_states_eq_target,
        State.normalizedTraceDistance, QIT.normalizedTraceDistance,
        State.traceNormDistance]
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
  letI : DecidableEq (TensorPower a n) := tensorPowerDecidableEq n
  letI : DecidableEq (TensorPower b n) := tensorPowerDecidableEq n
  letI : DecidableEq (TensorPower r n) := tensorPowerDecidableEq n
  rw [State.purifiedBall_eq]
  apply State.purifiedDistance_le_sqrt_two_mul_sub_sq_of_normalizedTraceDistance_le
  · apply Real.sqrt_le_one.mpr
    unfold fidelityError
    have hnonneg := State.squaredFidelity_nonneg C.outputState C.targetState
    linarith
  · exact C.recordedOutcomeState_normalizedTraceDistance_le_sqrt_fidelityError

end StateMergingBlockProtocol

end

end QIT
