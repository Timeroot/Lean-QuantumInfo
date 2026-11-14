/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy.PureEntanglement
public import QIT.Protocols.LOCC.InstrumentEntanglement

/-!
# Pure-state entanglement under finite one-way LOCC

This module formalizes the average pure-state entanglement monotonicity used
in the Horodecki--Oppenheim--Winter state-merging converse
[`horodecki-oppenheim-winter-2005-state-merging:m8-state-merging-converse-proof-route`,
`swlong.6.2.tex:1071-1139`]. Branches are obtained from the Kraus families of
the physical instrument and conditional channels; no output ensemble is
supplied independently of the protocol.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y

noncomputable section

namespace Channel

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

/-- Regard a channel as a finite instrument with one classical outcome. -/
def asSingletonInstrument (N : Channel a b) : FiniteInstrument a b Unit where
  branch _ := N.map
  branchTraceNonincreasingCP _ := N.traceNonincreasingCP_map
  total := N
  sum_branch_eq_total := by simp

end Channel

namespace OneWayLOCC

variable {A : Type u} {A' : Type v}
variable {B : Type w} {B' : Type x} {R : Type y}
variable [Fintype A] [DecidableEq A]
variable [Fintype A'] [DecidableEq A']
variable [Fintype B] [DecidableEq B]
variable [Fintype B'] [DecidableEq B']
variable [Fintype R]

/-- The chosen Kraus operator for Bob's conditional channel. -/
def bobRefinedKraus (L : OneWayLOCC A A' B B' R) (r : R) (k : B × B') :
    Matrix B' B ℂ :=
  ((L.bobChannel r).traceNonincreasingCP_map).kraus k

/-- A joint branch records Alice's outcome and Kraus index, followed by Bob's
conditional Kraus index. -/
abbrev jointBranchIndex (L : OneWayLOCC A A' B B' R) :=
  L.aliceInstrument.refinedBranchIndex × (B × B')

/-- Unnormalized final amplitude on one joint Alice--Bob Kraus branch. -/
def jointPostAmplitude
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (j : L.jointBranchIndex) : Prod A' B' → ℂ :=
  fun x => ∑ a : A, ∑ b : B,
    L.aliceInstrument.refinedKraus j.1 x.1 a *
      L.bobRefinedKraus j.1.1 j.2 x.2 b * psi.amp (a, b)

/-- Probability of a joint Kraus branch. -/
def jointBranchProbability
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (j : L.jointBranchIndex) : NNReal :=
  ⟨(rankOneMatrix (L.jointPostAmplitude psi j)).trace.re,
    (Matrix.PosSemidef.trace_nonneg
      (rankOneMatrix_pos (L.jointPostAmplitude psi j))).1⟩

@[simp]
theorem jointBranchProbability_coe
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (j : L.jointBranchIndex) :
    (L.jointBranchProbability psi j : ℝ) =
      (rankOneMatrix (L.jointPostAmplitude psi j)).trace.re :=
  rfl

theorem jointBranchProbability_nonneg
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (j : L.jointBranchIndex) :
    0 ≤ (L.jointBranchProbability psi j : ℝ) :=
  NNReal.coe_nonneg _

/-- Summing every unnormalized joint pure branch recovers the realized LOCC channel. -/
theorem sum_rankOne_jointPostAmplitude_eq_toChannel
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B)) :
    (∑ j : L.jointBranchIndex, rankOneMatrix (L.jointPostAmplitude psi j)) =
      L.toChannel.map psi.state.matrix := by
  classical
  calc
    (∑ j : L.jointBranchIndex, rankOneMatrix (L.jointPostAmplitude psi j)) =
        ∑ r : R, ∑ kA : A × A', ∑ kB : B × B',
          rankOneMatrix (fun x : Prod A' B' =>
            ∑ a : A, ∑ b : B,
              (L.aliceInstrument.branchTraceNonincreasingCP r).kraus kA x.1 a *
                L.bobRefinedKraus r kB x.2 b * psi.amp (a, b)) := by
      simp only [jointBranchIndex, FiniteInstrument.refinedBranchIndex,
        Fintype.sum_prod_type]
      rfl
    _ = ∑ r : R,
        MatrixMap.kron
          (MatrixMap.ofKraus
            (L.aliceInstrument.branchTraceNonincreasingCP r).kraus)
          (MatrixMap.ofKraus (L.bobRefinedKraus r)) psi.state.matrix := by
      apply Finset.sum_congr rfl
      intro r _
      simpa [Fintype.sum_prod_type, PureVector.state_matrix] using
        (FiniteInstrument.sum_rankOne_bilocalPostAmplitude_eq_kron_ofKraus
          (A := A) (A' := A') (B := B') (R := B)
          (L.aliceInstrument.branchTraceNonincreasingCP r).kraus
          (L.bobRefinedKraus r) psi.amp)
    _ = ∑ r : R,
        MatrixMap.kron (L.aliceInstrument.branch r) (L.bobChannel r).map
          psi.state.matrix := by
      apply Finset.sum_congr rfl
      intro r _
      rw [(L.aliceInstrument.branchTraceNonincreasingCP r).ofKraus_kraus]
      rw [show MatrixMap.ofKraus (L.bobRefinedKraus r) =
          (L.bobChannel r).map by
        exact (L.bobChannel r).traceNonincreasingCP_map.ofKraus_kraus]
    _ = L.toChannel.map psi.state.matrix := by
      rw [L.toChannel_map]
      rw [LinearMap.sum_apply]

/-- Joint branch probabilities have total mass one. -/
theorem sum_jointBranchProbability_eq_one
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B)) :
    (∑ j : L.jointBranchIndex, L.jointBranchProbability psi j) = 1 := by
  classical
  apply NNReal.eq
  simp only [NNReal.coe_sum, jointBranchProbability_coe, NNReal.coe_one]
  have htrace := L.toChannel.tracePreserving psi.state.matrix
  calc
    (∑ j : L.jointBranchIndex,
        (rankOneMatrix (L.jointPostAmplitude psi j)).trace.re) =
        ((∑ j : L.jointBranchIndex,
          rankOneMatrix (L.jointPostAmplitude psi j)).trace).re := by
      simp [Matrix.trace_sum]
    _ = (L.toChannel.map psi.state.matrix).trace.re := by
      rw [L.sum_rankOne_jointPostAmplitude_eq_toChannel psi]
    _ = psi.state.matrix.trace.re := congrArg Complex.re htrace
    _ = 1 := by rw [psi.state.trace_eq_one]; norm_num

/-- Physical joint branches on which direct pure-state normalization is valid. -/
abbrev physicalJointPositiveSupport
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B)) :=
  { j : L.jointBranchIndex // 0 < L.jointBranchProbability psi j }

/-- A zero-probability joint branch has an identically zero rank-one state. -/
theorem rankOne_jointPostAmplitude_eq_zero_of_probability_eq_zero
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (j : L.jointBranchIndex) (hj : L.jointBranchProbability psi j = 0) :
    rankOneMatrix (L.jointPostAmplitude psi j) = 0 := by
  apply (Matrix.PosSemidef.trace_eq_zero_iff
    (rankOneMatrix_pos (L.jointPostAmplitude psi j))).mp
  have hre : (rankOneMatrix (L.jointPostAmplitude psi j)).trace.re = 0 := by
    have hcoe := congrArg (fun p : NNReal => (p : ℝ)) hj
    simpa using hcoe
  apply Complex.ext
  · simpa using hre
  · simpa using
      (Matrix.PosSemidef.trace_nonneg
        (rankOneMatrix_pos (L.jointPostAmplitude psi j))).2.symm

/-- The directly normalized pure state on a positive-probability physical branch. -/
def physicalFinalNormalizedBranch
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (j : L.physicalJointPositiveSupport psi) : PureVector (Prod A' B') :=
  PureVector.normalize (L.jointPostAmplitude psi j.1) (by
    have hj : 0 < (L.jointBranchProbability psi j.1 : ℝ) := by
      exact_mod_cast j.2
    simpa using hj)

@[simp]
theorem physicalFinalNormalizedBranch_state_matrix
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (j : L.physicalJointPositiveSupport psi) :
    (L.physicalFinalNormalizedBranch psi j).state.matrix =
      ((((L.jointBranchProbability psi j.1 : ℝ)⁻¹ : ℝ) : ℂ) •
        rankOneMatrix (L.jointPostAmplitude psi j.1)) := by
  rw [physicalFinalNormalizedBranch, PureVector.normalize_state_matrix]
  rfl

/-- Swap an Alice-instrument branch so Bob's conditional channel acts on the first factor. -/
def bobBranchInput
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (i : L.aliceInstrument.positiveSupport psi) : PureVector (Prod B A') :=
  (L.aliceInstrument.normalizedBranch psi i).reindex (Equiv.prodComm A' B)

/-- Positive branches of the sequential Alice-then-Bob Kraus refinement.
The dependent index records that Bob's branch belongs to the channel selected
by Alice's physical outcome. -/
abbrev jointPositiveSupport
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B)) :=
  Σ i : L.aliceInstrument.positiveSupport psi,
    ((L.bobChannel i.1.1).asSingletonInstrument).positiveSupport
      (L.bobBranchInput psi i)

/-- The full physical joint Kraus index underlying a positive sequential branch. -/
def jointPositivePhysicalIndex
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (j : L.jointPositiveSupport psi) : L.jointBranchIndex :=
  (j.1.1, j.2.1.2)

/-- Probability of a positive sequential Alice--Bob branch. -/
def jointPositiveBranchProbability
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (j : L.jointPositiveSupport psi) : NNReal :=
  L.aliceInstrument.branchWeight psi j.1.1 *
    ((L.bobChannel j.1.1.1).asSingletonInstrument).branchWeight
      (L.bobBranchInput psi j.1) j.2.1

/-- Final normalized pure output of a positive sequential joint branch. -/
def finalNormalizedBranch
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (j : L.jointPositiveSupport psi) : PureVector (Prod A' B') :=
  (((L.bobChannel j.1.1.1).asSingletonInstrument).normalizedBranch
    (L.bobBranchInput psi j.1) j.2).reindex (Equiv.prodComm B' A')

private theorem nnreal_smul_rankOneMatrix_sqrt_inv
    {ι : Type*} (p : NNReal) (hp : 0 < p) (v : ι → ℂ) :
    p • rankOneMatrix
        (fun x => (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) * v x) =
      rankOneMatrix v := by
  have hp_real : 0 < (p : ℝ) := by
    exact_mod_cast hp
  have hsqrt_ne : Real.sqrt (p : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hp_real)
  have hreal :
      (p : ℝ) * (Real.sqrt (p : ℝ))⁻¹ *
          (Real.sqrt (p : ℝ))⁻¹ = 1 := by
    field_simp [hsqrt_ne]
    rw [Real.sq_sqrt hp_real.le]
  have hcomplex :
      (p : ℂ) * (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) *
          (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) = 1 := by
    exact_mod_cast hreal
  ext x y
  simp only [rankOneMatrix_apply]
  change (p : ℂ) *
      (((((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) * v x) *
        star ((((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) * v y)) =
    v x * star (v y)
  calc
    _ = ((p : ℂ) * (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) *
          (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ)) *
        (v x * star (v y)) := by
      simp [mul_assoc, mul_left_comm, mul_comm]
    _ = v x * star (v y) := by rw [hcomplex, one_mul]

private theorem nnreal_smul_inv_smul_matrix
    {ι : Type*} (p : NNReal) (hp : 0 < p) (M : Matrix ι ι ℂ) :
    p • ((((p : ℝ)⁻¹ : ℝ) : ℂ) • M) = M := by
  have hp_real : 0 < (p : ℝ) := by
    exact_mod_cast hp
  have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_real
  have hreal : (p : ℝ) * (p : ℝ)⁻¹ = 1 :=
    mul_inv_cancel₀ hp_ne
  have hcomplex :
      (p : ℂ) * (((p : ℝ)⁻¹ : ℝ) : ℂ) = 1 := by
    exact_mod_cast hreal
  ext x y
  simp only [Matrix.smul_apply]
  change (p : ℂ) * ((((p : ℝ)⁻¹ : ℝ) : ℂ) * M x y) = M x y
  rw [← mul_assoc, hcomplex, one_mul]

private theorem bobPostAmplitude_reindex_eq_scaled_jointPostAmplitude
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (j : L.jointPositiveSupport psi) :
    (fun z : Prod A' B' =>
      ((L.bobChannel j.1.1.1).asSingletonInstrument).postAmplitude
        (L.bobBranchInput psi j.1) j.2.1 (z.2, z.1)) =
      fun z =>
        (((Real.sqrt
          (L.aliceInstrument.branchWeight psi j.1.1 : ℝ))⁻¹ : ℝ) : ℂ) *
          L.jointPostAmplitude psi (L.jointPositivePhysicalIndex psi j) z := by
  classical
  funext z
  simp only [FiniteInstrument.postAmplitude, FiniteInstrument.refinedKraus,
    Channel.asSingletonInstrument, bobBranchInput, PureVector.reindex_amp,
    FiniteInstrument.normalizedBranch, PureVector.normalize, jointPostAmplitude,
    bobRefinedKraus, jointPositivePhysicalIndex, Equiv.prodComm_symm,
    Equiv.prodComm_apply, FiniteInstrument.branchWeight_coe, Prod.swap_prod_mk]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem bobBranchWeight_smul_finalNormalizedBranch_state_matrix
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (j : L.jointPositiveSupport psi) :
    ((L.bobChannel j.1.1.1).asSingletonInstrument).branchWeight
        (L.bobBranchInput psi j.1) j.2.1 •
        (L.finalNormalizedBranch psi j).state.matrix =
      rankOneMatrix (fun z : Prod A' B' =>
        ((L.bobChannel j.1.1.1).asSingletonInstrument).postAmplitude
          (L.bobBranchInput psi j.1) j.2.1 (z.2, z.1)) := by
  have hBob :=
    FiniteInstrument.branchWeight_smul_normalizedBranch_state_matrix
      ((L.bobChannel j.1.1.1).asSingletonInstrument)
      (L.bobBranchInput psi j.1) j.2
  ext z w
  have hentry := congrFun (congrFun hBob (z.2, z.1)) (w.2, w.1)
  simpa [finalNormalizedBranch, PureVector.state_matrix, rankOneMatrix_apply] using hentry

/-- Weighting a positive sequential branch recovers its physical joint Kraus branch. -/
theorem jointPositiveBranchProbability_smul_finalNormalizedBranch_state_matrix
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (j : L.jointPositiveSupport psi) :
    L.jointPositiveBranchProbability psi j •
        (L.finalNormalizedBranch psi j).state.matrix =
      rankOneMatrix
        (L.jointPostAmplitude psi (L.jointPositivePhysicalIndex psi j)) := by
  rw [jointPositiveBranchProbability, mul_smul]
  rw [bobBranchWeight_smul_finalNormalizedBranch_state_matrix]
  rw [bobPostAmplitude_reindex_eq_scaled_jointPostAmplitude]
  exact nnreal_smul_rankOneMatrix_sqrt_inv
    (L.aliceInstrument.branchWeight psi j.1.1) j.1.2
    (L.jointPostAmplitude psi (L.jointPositivePhysicalIndex psi j))

/-- The sequential product probability is the probability of its physical joint branch. -/
theorem jointPositiveBranchProbability_eq_jointBranchProbability
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (j : L.jointPositiveSupport psi) :
    L.jointPositiveBranchProbability psi j =
      L.jointBranchProbability psi (L.jointPositivePhysicalIndex psi j) := by
  apply NNReal.eq
  have htrace := congrArg Matrix.trace
    (L.jointPositiveBranchProbability_smul_finalNormalizedBranch_state_matrix psi j)
  rw [Matrix.trace_smul, (L.finalNormalizedBranch psi j).state.trace_eq_one] at htrace
  have hre := congrArg Complex.re htrace
  simpa [NNReal.smul_def] using hre

/-- A positive sequential branch regarded as a positive physical joint branch. -/
def jointPositiveToPhysicalSupport
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B)) :
    L.jointPositiveSupport psi → L.physicalJointPositiveSupport psi :=
  fun j => ⟨L.jointPositivePhysicalIndex psi j, by
    rw [← L.jointPositiveBranchProbability_eq_jointBranchProbability psi j]
    exact mul_pos j.1.2 j.2.2⟩

/-- Distinct public dependent branches have distinct full physical Kraus indices. -/
theorem jointPositivePhysicalIndex_injective
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B)) :
    Function.Injective (L.jointPositivePhysicalIndex psi) := by
  intro j k h
  rcases j with ⟨i, bi⟩
  rcases k with ⟨i', bi'⟩
  simp only [jointPositivePhysicalIndex] at h
  have hi : i = i' := by
    apply Subtype.ext
    exact congrArg Prod.fst h
  subst i'
  have hbi : bi = bi' := by
    apply Subtype.ext
    exact Prod.ext (Subsingleton.elim _ _)
      (congrArg (fun q : L.jointBranchIndex => q.2) h)
  subst bi'
  rfl

/-- Weighting a normalized positive physical branch recovers its joint rank-one state. -/
theorem jointBranchProbability_smul_physicalFinalNormalizedBranch_state_matrix
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (j : L.physicalJointPositiveSupport psi) :
    L.jointBranchProbability psi j.1 •
        (L.physicalFinalNormalizedBranch psi j).state.matrix =
      rankOneMatrix (L.jointPostAmplitude psi j.1) := by
  rw [L.physicalFinalNormalizedBranch_state_matrix psi j]
  exact nnreal_smul_inv_smul_matrix
    (L.jointBranchProbability psi j.1) j.2
    (rankOneMatrix (L.jointPostAmplitude psi j.1))

/-- Public and physical normalization give the same state on the mapped branch. -/
theorem finalNormalizedBranch_state_matrix_eq_physical
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (j : L.jointPositiveSupport psi) :
    (L.finalNormalizedBranch psi j).state.matrix =
      (L.physicalFinalNormalizedBranch psi
        (L.jointPositiveToPhysicalSupport psi j)).state.matrix := by
  have hPublic :=
    L.jointPositiveBranchProbability_smul_finalNormalizedBranch_state_matrix psi j
  have hPhysical :=
    L.jointBranchProbability_smul_physicalFinalNormalizedBranch_state_matrix psi
      (L.jointPositiveToPhysicalSupport psi j)
  simp only [jointPositiveToPhysicalSupport] at hPhysical
  rw [← L.jointPositiveBranchProbability_eq_jointBranchProbability psi j] at hPhysical
  have hweighted :
      L.jointPositiveBranchProbability psi j •
          (L.finalNormalizedBranch psi j).state.matrix =
        L.jointPositiveBranchProbability psi j •
          (L.physicalFinalNormalizedBranch psi
            (L.jointPositiveToPhysicalSupport psi j)).state.matrix :=
    hPublic.trans hPhysical.symm
  have hp : 0 < L.jointPositiveBranchProbability psi j :=
    mul_pos j.1.2 j.2.2
  have hp_real : 0 < (L.jointPositiveBranchProbability psi j : ℝ) := by
    exact_mod_cast hp
  have hp_complex : (L.jointPositiveBranchProbability psi j : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hp_real
  ext x y
  have hentry := congrFun (congrFun hweighted x) y
  simp only [Matrix.smul_apply] at hentry
  change (L.jointPositiveBranchProbability psi j : ℂ) *
      (L.finalNormalizedBranch psi j).state.matrix x y =
    (L.jointPositiveBranchProbability psi j : ℂ) *
      (L.physicalFinalNormalizedBranch psi
        (L.jointPositiveToPhysicalSupport psi j)).state.matrix x y at hentry
  exact mul_left_cancel₀ hp_complex hentry

/-- The positive sequential joint branches carry total probability one. -/
theorem sum_jointPositiveBranchProbability_eq_one
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B)) :
    (∑ j : L.jointPositiveSupport psi, L.jointPositiveBranchProbability psi j) = 1 := by
  classical
  rw [Fintype.sum_sigma]
  simp only [jointPositiveBranchProbability]
  calc
    (∑ i : L.aliceInstrument.positiveSupport psi,
        ∑ k : ((L.bobChannel i.1.1).asSingletonInstrument).positiveSupport
            (L.bobBranchInput psi i),
          L.aliceInstrument.branchWeight psi i.1 *
            ((L.bobChannel i.1.1).asSingletonInstrument).branchWeight
              (L.bobBranchInput psi i) k.1) =
        ∑ i : L.aliceInstrument.positiveSupport psi,
          L.aliceInstrument.branchWeight psi i.1 *
            (∑ k : ((L.bobChannel i.1.1).asSingletonInstrument).positiveSupport
                (L.bobBranchInput psi i),
              ((L.bobChannel i.1.1).asSingletonInstrument).branchWeight
                (L.bobBranchInput psi i) k.1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ i : L.aliceInstrument.positiveSupport psi,
        L.aliceInstrument.branchWeight psi i.1 := by
      apply Finset.sum_congr rfl
      intro i _
      have hBob := FiniteInstrument.sum_positiveSupport_branchWeight_eq_one
        ((L.bobChannel i.1.1).asSingletonInstrument) (L.bobBranchInput psi i)
      rw [hBob, mul_one]
    _ = 1 := L.aliceInstrument.sum_positiveSupport_branchWeight_eq_one psi

/-- The public positive branch ensemble averages to the realized LOCC output state. -/
theorem sum_jointPositiveBranchProbability_smul_finalNormalizedBranch_state_matrix
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B)) :
    (∑ j : L.jointPositiveSupport psi,
        L.jointPositiveBranchProbability psi j •
          (L.finalNormalizedBranch psi j).state.matrix) =
      L.toChannel.map psi.state.matrix := by
  classical
  let f : L.jointPositiveSupport psi → L.jointBranchIndex :=
    L.jointPositivePhysicalIndex psi
  have hf : Function.Injective f :=
    L.jointPositivePhysicalIndex_injective psi
  letI : Fintype {q : L.jointBranchIndex // q ∈ Set.range f} :=
    Subtype.fintype fun q => q ∈ Set.range f
  have hRangeProbability :
      (∑ q : {q : L.jointBranchIndex // q ∈ Set.range f},
        L.jointBranchProbability psi q.1) = 1 := by
    calc
      (∑ q : {q : L.jointBranchIndex // q ∈ Set.range f},
          L.jointBranchProbability psi q.1) =
          ∑ j : L.jointPositiveSupport psi,
            L.jointBranchProbability psi (f j) := by
        symm
        exact Fintype.sum_equiv
          (Equiv.ofInjective f hf : L.jointPositiveSupport psi ≃
            {q : L.jointBranchIndex // q ∈ Set.range f}) _ _ (fun _ => rfl)
      _ = ∑ j : L.jointPositiveSupport psi,
          L.jointPositiveBranchProbability psi j := by
        apply Finset.sum_congr rfl
        intro j _
        simpa [f] using
          (L.jointPositiveBranchProbability_eq_jointBranchProbability psi j).symm
      _ = 1 := L.sum_jointPositiveBranchProbability_eq_one psi
  have hFullProbability := L.sum_jointBranchProbability_eq_one psi
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun q : L.jointBranchIndex => q ∈ Set.range f)
    (fun q => L.jointBranchProbability psi q)] at hFullProbability
  change (∑ q : {q : L.jointBranchIndex // q ∈ Set.range f},
      L.jointBranchProbability psi q.1) +
      (∑ q : {q : L.jointBranchIndex // q ∉ Set.range f},
        L.jointBranchProbability psi q.1) = 1 at hFullProbability
  have hComplementProbability :
      (∑ q : {q : L.jointBranchIndex // q ∉ Set.range f},
        L.jointBranchProbability psi q.1) = 0 := by
    rw [hRangeProbability] at hFullProbability
    have hadd :
        (1 : NNReal) +
            (∑ q : {q : L.jointBranchIndex // q ∉ Set.range f},
              L.jointBranchProbability psi q.1) = 1 + 0 := by
      simpa only [add_zero] using hFullProbability
    exact add_left_cancel hadd
  have hComplementProbabilityZero :
      (fun q : {q : L.jointBranchIndex // q ∉ Set.range f} =>
        L.jointBranchProbability psi q.1) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg (fun _ => bot_le)).mp
      hComplementProbability
  have hComplementMatrix :
      (∑ q : {q : L.jointBranchIndex // q ∉ Set.range f},
        rankOneMatrix (L.jointPostAmplitude psi q.1)) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    exact L.rankOne_jointPostAmplitude_eq_zero_of_probability_eq_zero psi q.1
      (congrFun hComplementProbabilityZero q)
  calc
    (∑ j : L.jointPositiveSupport psi,
        L.jointPositiveBranchProbability psi j •
          (L.finalNormalizedBranch psi j).state.matrix) =
        ∑ j : L.jointPositiveSupport psi,
          rankOneMatrix (L.jointPostAmplitude psi (f j)) := by
      apply Finset.sum_congr rfl
      intro j _
      simpa [f] using
        L.jointPositiveBranchProbability_smul_finalNormalizedBranch_state_matrix psi j
    _ = ∑ q : {q : L.jointBranchIndex // q ∈ Set.range f},
        rankOneMatrix (L.jointPostAmplitude psi q.1) := by
      exact Fintype.sum_equiv
        (Equiv.ofInjective f hf : L.jointPositiveSupport psi ≃
          {q : L.jointBranchIndex // q ∈ Set.range f}) _ _ (fun _ => rfl)
    _ = ∑ q : L.jointBranchIndex,
        rankOneMatrix (L.jointPostAmplitude psi q) := by
      conv_rhs =>
        rw [← Fintype.sum_subtype_add_sum_subtype
          (fun q : L.jointBranchIndex => q ∈ Set.range f)
          (fun q => rankOneMatrix (L.jointPostAmplitude psi q))]
      change (∑ q : {q : L.jointBranchIndex // q ∈ Set.range f},
          rankOneMatrix (L.jointPostAmplitude psi q.1)) =
        (∑ q : {q : L.jointBranchIndex // q ∈ Set.range f},
          rankOneMatrix (L.jointPostAmplitude psi q.1)) +
          ∑ q : {q : L.jointBranchIndex // q ∉ Set.range f},
            rankOneMatrix (L.jointPostAmplitude psi q.1)
      rw [hComplementMatrix, add_zero]
    _ = L.toChannel.map psi.state.matrix :=
      L.sum_rankOne_jointPostAmplitude_eq_toChannel psi

/-- Average entanglement after refining Bob's conditional channel at one Alice branch. -/
def bobRefinedBranchAverageEntanglement
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (i : L.aliceInstrument.positiveSupport psi) : Real :=
  ((L.bobChannel i.1.1).asSingletonInstrument).refinedBranchAverageEntanglement
    (L.bobBranchInput psi i)

/-- Average pure-state entanglement of the canonical Alice--Bob Kraus refinement. -/
def refinedBranchAverageEntanglement
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B)) : Real :=
  ∑ j : L.jointPositiveSupport psi,
    (L.jointPositiveBranchProbability psi j : Real) *
      (L.finalNormalizedBranch psi j).entanglementEntropy

theorem refinedBranchAverageEntanglement_eq_sequential
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B)) :
    L.refinedBranchAverageEntanglement psi =
      ∑ i : L.aliceInstrument.positiveSupport psi,
        (L.aliceInstrument.branchWeight psi i.1 : Real) *
          L.bobRefinedBranchAverageEntanglement psi i := by
  classical
  rw [refinedBranchAverageEntanglement, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [bobRefinedBranchAverageEntanglement,
    FiniteInstrument.refinedBranchAverageEntanglement]
  simp only [jointPositiveBranchProbability, NNReal.coe_mul, finalNormalizedBranch]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [PureVector.entanglementEntropy_reindex_prodComm]
  simp only [PureVector.entanglementEntropy, mul_assoc]

theorem bobRefinedBranchAverageEntanglement_le
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B))
    (i : L.aliceInstrument.positiveSupport psi) :
    L.bobRefinedBranchAverageEntanglement psi i ≤
      (L.aliceInstrument.normalizedBranch psi i).entanglementEntropy := by
  have h :=
    ((L.bobChannel i.1.1).asSingletonInstrument).average_pure_entanglement_le
      (L.bobBranchInput psi i)
  calc
    L.bobRefinedBranchAverageEntanglement psi i ≤
        (L.bobBranchInput psi i).entanglementEntropy := by
      simpa [bobRefinedBranchAverageEntanglement, PureVector.entanglementEntropy] using h
    _ = (L.aliceInstrument.normalizedBranch psi i).entanglementEntropy := by
      exact PureVector.entanglementEntropy_reindex_prodComm
        (L.aliceInstrument.normalizedBranch psi i)

/-- Finite one-way LOCC cannot increase the average entropy of entanglement
of a bipartite pure state. -/
theorem average_pure_entanglement_le
    (L : OneWayLOCC A A' B B' R) (psi : PureVector (Prod A B)) :
    L.refinedBranchAverageEntanglement psi ≤ psi.entanglementEntropy := by
  classical
  rw [L.refinedBranchAverageEntanglement_eq_sequential psi]
  calc
    (∑ i : L.aliceInstrument.positiveSupport psi,
          (L.aliceInstrument.branchWeight psi i.1 : Real) *
            L.bobRefinedBranchAverageEntanglement psi i) ≤
        ∑ i : L.aliceInstrument.positiveSupport psi,
          (L.aliceInstrument.branchWeight psi i.1 : Real) *
            (L.aliceInstrument.normalizedBranch psi i).entanglementEntropy := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (L.bobRefinedBranchAverageEntanglement_le psi i) (NNReal.coe_nonneg _)
    _ = L.aliceInstrument.refinedBranchAverageEntanglement psi := by
      rfl
    _ ≤ psi.entanglementEntropy := by
      simpa [PureVector.entanglementEntropy] using
        L.aliceInstrument.average_pure_entanglement_le psi

end OneWayLOCC

end

end QIT
