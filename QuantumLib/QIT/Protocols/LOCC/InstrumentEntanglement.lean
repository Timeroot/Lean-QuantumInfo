/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Entropy.ConditionalEntropyConcavity
public import QuantumLib.QIT.Protocols.LOCC.Core

/-!
# Pure-state entanglement under finite instruments

This module refines every outcome of a finite instrument by its chosen Kraus
family.  Positive-weight refined branches are normalized as kets; zero
branches are retained in the algebraic completeness sum but are never normalized.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y

noncomputable section

namespace FiniteInstrument

variable {A : Type u} {A' : Type v} {B : Type w} {R : Type x}
variable [Fintype A] [DecidableEq A]
variable [Fintype A'] [DecidableEq A']
variable [Fintype B] [DecidableEq B]
variable [Fintype R]

/-- An instrument outcome refined by the canonical chosen Kraus index. -/
abbrev refinedBranchIndex (_M : FiniteInstrument A A' R) := R × (A × A')

/-- The chosen Kraus operator at a refined instrument branch. -/
def refinedKraus (M : FiniteInstrument A A' R) (i : M.refinedBranchIndex) :
    Matrix A' A ℂ :=
  (M.branchTraceNonincreasingCP i.1).kraus i.2

/-- Unnormalized output amplitudes after one refined Kraus branch acts on Alice. -/
def postAmplitude (M : FiniteInstrument A A' R) (ψ : Ket (A × B))
    (i : M.refinedBranchIndex) : A' × B → ℂ :=
  fun x => ∑ a : A, M.refinedKraus i x.1 a * ψ.vec (a, x.2)

/-- Probability weight of a refined branch, represented as a nonnegative real. -/
def branchWeight (M : FiniteInstrument A A' R) (ψ : Ket (A × B))
    (i : M.refinedBranchIndex) : NNReal :=
  ⟨(rankOneMatrix (M.postAmplitude ψ i)).trace.re,
    (Matrix.PosSemidef.trace_nonneg (rankOneMatrix_pos (M.postAmplitude ψ i))).1⟩

omit [DecidableEq B] in
@[simp]
theorem branchWeight_coe (M : FiniteInstrument A A' R) (ψ : Ket (A × B))
    (i : M.refinedBranchIndex) :
    (M.branchWeight ψ i : ℝ) = (rankOneMatrix (M.postAmplitude ψ i)).trace.re :=
  rfl

omit [DecidableEq B] in
theorem branchWeight_nonneg (M : FiniteInstrument A A' R)
    (ψ : Ket (A × B)) (i : M.refinedBranchIndex) :
    0 ≤ (M.branchWeight ψ i : ℝ) :=
  NNReal.coe_nonneg _

/-- Aggregating all chosen outcome-Kraus families recovers the total channel. -/
theorem ofKraus_refinedKraus_eq_total (M : FiniteInstrument A A' R) :
    MatrixMap.ofKraus M.refinedKraus = M.total.map := by
  classical
  calc
    MatrixMap.ofKraus M.refinedKraus =
        ∑ r : R, MatrixMap.ofKraus (M.branchTraceNonincreasingCP r).kraus := by
      apply LinearMap.ext
      intro X
      ext i j
      simp [MatrixMap.ofKraus, refinedKraus, Fintype.sum_prod_type]
    _ = ∑ r : R, M.branch r := by
      apply Finset.sum_congr rfl
      intro r _
      exact (M.branchTraceNonincreasingCP r).ofKraus_kraus
    _ = M.total.map := M.sum_branch_eq_total

private theorem sum_rankOne_localPostAmplitude_eq_kron_ofKraus
    {κ : Type y} [Fintype κ] (K : κ → Matrix A' A ℂ) (v : A × B → ℂ) :
    (∑ k : κ,
        rankOneMatrix (fun x : A' × B => ∑ a : A, K k x.1 a * v (a, x.2))) =
      MatrixMap.kron (MatrixMap.ofKraus K) (CPTPOp.id (dIn := B)).map
        (rankOneMatrix v) := by
  classical
  ext x y
  rw [MatrixMap.kron_idChannel_apply_slice]
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply, rankOneMatrix_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

private theorem sum_rankOne_rightPostAmplitude_eq_kron_ofKraus
    {κ : Type y} [Fintype κ] [DecidableEq R]
    (K : κ → Matrix B R ℂ) (v : A' × R → ℂ) :
    (∑ k : κ,
        rankOneMatrix (fun x : A' × B =>
          ∑ r : R, K k x.2 r * v (x.1, r))) =
      MatrixMap.kron (CPTPOp.id (dIn := A')).map (MatrixMap.ofKraus K)
        (rankOneMatrix v) := by
  classical
  ext x z
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply, rankOneMatrix_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- The product of two finite Kraus refinements expands a bipartite pure
input into the corresponding sum of unnormalized rank-one branches. -/
theorem sum_rankOne_bilocalPostAmplitude_eq_kron_ofKraus
    {κA : Type y} {κB : Type*} [Fintype κA] [Fintype κB] [DecidableEq R]
    (KA : κA → Matrix A' A ℂ) (KB : κB → Matrix B R ℂ)
    (v : A × R → ℂ) :
    (∑ k : κA × κB,
        rankOneMatrix (fun x : A' × B =>
          ∑ a : A, ∑ r : R,
            KA k.1 x.1 a * KB k.2 x.2 r * v (a, r))) =
      MatrixMap.kron (MatrixMap.ofKraus KA) (MatrixMap.ofKraus KB)
        (rankOneMatrix v) := by
  classical
  let localPostAmplitude : κA → A' × R → ℂ :=
    fun k x => ∑ a : A, KA k x.1 a * v (a, x.2)
  calc
    (∑ k : κA × κB,
        rankOneMatrix (fun x : A' × B =>
          ∑ a : A, ∑ r : R,
            KA k.1 x.1 a * KB k.2 x.2 r * v (a, r))) =
        ∑ kA : κA, ∑ kB : κB,
          rankOneMatrix (fun x : A' × B =>
            ∑ r : R, KB kB x.2 r * localPostAmplitude kA (x.1, r)) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro kA _
      apply Finset.sum_congr rfl
      intro kB _
      apply congrArg rankOneMatrix
      funext x
      simp only [localPostAmplitude, Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      simp only [mul_assoc, mul_left_comm]
    _ = ∑ kA : κA,
        MatrixMap.kron (CPTPOp.id (dIn := A')).map (MatrixMap.ofKraus KB)
          (rankOneMatrix (localPostAmplitude kA)) := by
      apply Finset.sum_congr rfl
      intro kA _
      exact sum_rankOne_rightPostAmplitude_eq_kron_ofKraus
        (A' := A') (R := R) KB (localPostAmplitude kA)
    _ = MatrixMap.kron (CPTPOp.id (dIn := A')).map (MatrixMap.ofKraus KB)
        (∑ kA : κA, rankOneMatrix (localPostAmplitude kA)) := by
      rw [map_sum]
    _ = MatrixMap.kron (CPTPOp.id (dIn := A')).map (MatrixMap.ofKraus KB)
        (MatrixMap.kron (MatrixMap.ofKraus KA) (CPTPOp.id (dIn := R)).map
          (rankOneMatrix v)) := by
      rw [show (∑ kA : κA, rankOneMatrix (localPostAmplitude kA)) =
          MatrixMap.kron (MatrixMap.ofKraus KA) (CPTPOp.id (dIn := R)).map
            (rankOneMatrix v) by
        simpa [localPostAmplitude] using
          (sum_rankOne_localPostAmplitude_eq_kron_ofKraus
            (B := R) KA v)]
    _ = MatrixMap.kron (MatrixMap.ofKraus KA) (MatrixMap.ofKraus KB)
        (rankOneMatrix v) := by
      calc
        MatrixMap.kron (CPTPOp.id (dIn := A')).map (MatrixMap.ofKraus KB)
            (MatrixMap.kron (MatrixMap.ofKraus KA) (CPTPOp.id (dIn := R)).map
              (rankOneMatrix v)) =
            MatrixMap.kron
              ((CPTPOp.id (dIn := A')).map.comp (MatrixMap.ofKraus KA))
              ((MatrixMap.ofKraus KB).comp (CPTPOp.id (dIn := R)).map)
              (rankOneMatrix v) :=
          MatrixMap.kron_comp_apply_general
            (α := A') (β := A') (γ := R) (δ := B) (η := A) (θ := R)
            (CPTPOp.id (dIn := A')).map (MatrixMap.ofKraus KB)
            (MatrixMap.ofKraus KA) (CPTPOp.id (dIn := R)).map (rankOneMatrix v)
        _ = MatrixMap.kron (MatrixMap.ofKraus KA) (MatrixMap.ofKraus KB)
            (rankOneMatrix v) := by
          rw [CPTPOp.id_map (dIn := A'),
            CPTPOp.id_map (dIn := R)]
          simp only [LinearMap.id_comp, LinearMap.comp_id]

/-- The sum of unnormalized refined pure branches is the total local channel action. -/
theorem sum_rankOne_postAmplitude_eq_totalAction
    (M : FiniteInstrument A A' R) (ψ : Ket (A × B)) :
    (∑ i : M.refinedBranchIndex, rankOneMatrix (M.postAmplitude ψ i)) =
      MatrixMap.kron M.total.map (CPTPOp.id (dIn := B)).map ψ.state.m := by
  rw [← M.ofKraus_refinedKraus_eq_total, Ket.state_matrix]
  exact sum_rankOne_localPostAmplitude_eq_kron_ofKraus (B := B) M.refinedKraus ψ.vec

/-- Refined branch weights form a probability distribution. -/
theorem sum_branchWeight_eq_one
    (M : FiniteInstrument A A' R) (ψ : Ket (A × B)) :
    (∑ i : M.refinedBranchIndex, M.branchWeight ψ i) = 1 := by
  classical
  apply NNReal.eq
  simp only [NNReal.coe_sum, branchWeight_coe, NNReal.coe_one]
  have htrace := MatrixMap.IsTracePreserving.kron M.total.map_TP (CPTPOp.id (dIn := B)).map_TP ψ.state.m
  calc
    (∑ i : M.refinedBranchIndex,
        (rankOneMatrix (M.postAmplitude ψ i)).trace.re) =
        ((∑ i : M.refinedBranchIndex,
          rankOneMatrix (M.postAmplitude ψ i)).trace).re := by
      simp [Matrix.trace_sum]
    _ = (MatrixMap.kron M.total.map (CPTPOp.id (dIn := B)).map
          ψ.state.m).trace.re := by
      rw [M.sum_rankOne_postAmplitude_eq_totalAction ψ]
    _ = ψ.state.m.trace.re := congrArg Complex.re htrace
    _ = 1 := by rw [ψ.state.tr']; norm_num

/-- Refined branches on which normalization is mathematically valid. -/
abbrev positiveSupport (M : FiniteInstrument A A' R) (ψ : Ket (A × B)) :=
  { i : M.refinedBranchIndex // 0 < M.branchWeight ψ i }

/-- The normalized pure output on a strictly positive refined branch. -/
def normalizedBranch (M : FiniteInstrument A A' R) (ψ : Ket (A × B))
    (i : M.positiveSupport ψ) : Ket (A' × B) :=
  Ket.normalizeRankOne (M.postAmplitude ψ i.1) (by
    have hi : 0 < (M.branchWeight ψ i.1 : ℝ) := by
      exact_mod_cast i.2
    simpa using hi)

theorem normalizedBranch_state_matrix
    (M : FiniteInstrument A A' R) (ψ : Ket (A × B))
    (i : M.positiveSupport ψ) :
    (M.normalizedBranch ψ i).state.m =
      ((((M.branchWeight ψ i.1 : ℝ)⁻¹ : ℝ) : ℂ) •
        rankOneMatrix (M.postAmplitude ψ i.1)) := by
  rw [normalizedBranch, Ket.normalizeRankOne_state_matrix]
  rfl

/-- Weighting a normalized positive branch recovers its unnormalized rank-one state. -/
theorem branchWeight_smul_normalizedBranch_state_matrix
    (M : FiniteInstrument A A' R) (ψ : Ket (A × B))
    (i : M.positiveSupport ψ) :
    M.branchWeight ψ i.1 • (M.normalizedBranch ψ i).state.m =
      rankOneMatrix (M.postAmplitude ψ i.1) := by
  rw [M.normalizedBranch_state_matrix ψ i]
  have hi : 0 < (M.branchWeight ψ i.1 : ℝ) := by
    exact_mod_cast i.2
  have hine : (M.branchWeight ψ i.1 : ℝ) ≠ 0 := ne_of_gt hi
  have hreal :
      (M.branchWeight ψ i.1 : ℝ) * (M.branchWeight ψ i.1 : ℝ)⁻¹ = 1 :=
    mul_inv_cancel₀ hine
  have hcomplex :
      (M.branchWeight ψ i.1 : ℂ) *
          (((M.branchWeight ψ i.1 : ℝ)⁻¹ : ℝ) : ℂ) = 1 := by
    exact_mod_cast hreal
  ext x y
  simp only [Matrix.smul_apply]
  change (M.branchWeight ψ i.1 : ℂ) *
      ((((M.branchWeight ψ i.1 : ℝ)⁻¹ : ℝ) : ℂ) *
        rankOneMatrix (M.postAmplitude ψ i.1) x y) =
    rankOneMatrix (M.postAmplitude ψ i.1) x y
  rw [← mul_assoc, hcomplex, one_mul]

omit [DecidableEq B] in
/-- A zero-weight refined branch has an identically zero unnormalized state. -/
theorem rankOne_postAmplitude_eq_zero_of_branchWeight_eq_zero
    (M : FiniteInstrument A A' R) (ψ : Ket (A × B))
    (i : M.refinedBranchIndex) (hi : M.branchWeight ψ i = 0) :
    rankOneMatrix (M.postAmplitude ψ i) = 0 := by
  apply (Matrix.PosSemidef.trace_eq_zero_iff
    (rankOneMatrix_pos (M.postAmplitude ψ i))).mp
  have hre : (rankOneMatrix (M.postAmplitude ψ i)).trace.re = 0 := by
    have hcoe := congrArg (fun p : NNReal => (p : ℝ)) hi
    simpa using hcoe
  apply Complex.ext
  · simpa using hre
  · simpa using
      (Matrix.PosSemidef.trace_nonneg
        (rankOneMatrix_pos (M.postAmplitude ψ i))).2.symm

/-- Restricting the branch weights to positive support preserves their total mass. -/
theorem sum_positiveSupport_branchWeight_eq_one
    (M : FiniteInstrument A A' R) (ψ : Ket (A × B)) :
    (∑ i : M.positiveSupport ψ, M.branchWeight ψ i.1) = 1 := by
  classical
  rw [← M.sum_branchWeight_eq_one ψ]
  conv_rhs =>
    rw [← Fintype.sum_subtype_add_sum_subtype
      (fun i : M.refinedBranchIndex => 0 < M.branchWeight ψ i)
      (fun i => M.branchWeight ψ i)]
  have hzero :
      (∑ i : { i : M.refinedBranchIndex // ¬ 0 < M.branchWeight ψ i },
        M.branchWeight ψ i.1) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact le_antisymm (not_lt.mp i.2) bot_le
  rw [hzero, add_zero]

/-- The full refined branch sum has the same remote marginal as the input state. -/
theorem sum_remoteBranchMatrix_eq_inputMarginal
    (M : FiniteInstrument A A' R) (ψ : Ket (A × B)) :
    (∑ i : M.refinedBranchIndex,
        Matrix.traceLeft
          (rankOneMatrix (M.postAmplitude ψ i))) =
      ψ.state.traceLeft.m := by
  classical
  calc
    (∑ i : M.refinedBranchIndex,
        Matrix.traceLeft
          (rankOneMatrix (M.postAmplitude ψ i))) =
        Matrix.traceLeft
          (∑ i : M.refinedBranchIndex,
            rankOneMatrix (M.postAmplitude ψ i)) := by
      ext b b'
      simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.sum_apply]
      rw [Finset.sum_comm]
    _ = Matrix.traceLeft
        (MatrixMap.kron M.total.map (CPTPOp.id (dIn := B)).map
          ψ.state.m) := by
      rw [M.sum_rankOne_postAmplitude_eq_totalAction ψ]
    _ = Matrix.traceLeft ψ.state.m :=
      MatrixMap.traceLeft_kron_idChannel_of_tracePreserving
        M.total.map M.total.map_TP ψ.state.m
    _ = ψ.state.traceLeft.m := (MState.traceLeft_m ψ.state).symm

omit [DecidableEq B] in
/-- Zero branches contribute no remote subnormalized state. -/
theorem remoteBranchMatrix_eq_zero_of_not_positive
    (M : FiniteInstrument A A' R) (ψ : Ket (A × B))
    (i : M.refinedBranchIndex) (hi : ¬ 0 < M.branchWeight ψ i) :
    Matrix.traceLeft
        (rankOneMatrix (M.postAmplitude ψ i)) = 0 := by
  have hweight : M.branchWeight ψ i = 0 :=
    le_antisymm (not_lt.mp hi) bot_le
  rw [M.rankOne_postAmplitude_eq_zero_of_branchWeight_eq_zero ψ i hweight]
  ext b b'
  simp [Matrix.traceLeft]

omit [DecidableEq B] in
/-- Positive support carries the entire remote subnormalized-state sum. -/
theorem sum_positiveSupport_remoteBranchMatrix_eq_sum
    (M : FiniteInstrument A A' R) (ψ : Ket (A × B)) :
    (∑ i : M.positiveSupport ψ,
        Matrix.traceLeft
          (rankOneMatrix (M.postAmplitude ψ i.1))) =
      ∑ i : M.refinedBranchIndex,
        Matrix.traceLeft
          (rankOneMatrix (M.postAmplitude ψ i)) := by
  classical
  conv_rhs =>
    rw [← Fintype.sum_subtype_add_sum_subtype
      (fun i : M.refinedBranchIndex => 0 < M.branchWeight ψ i)
      (fun i => Matrix.traceLeft
        (rankOneMatrix (M.postAmplitude ψ i)))]
  have hzero :
      (∑ i : { i : M.refinedBranchIndex // ¬ 0 < M.branchWeight ψ i },
        Matrix.traceLeft
          (rankOneMatrix (M.postAmplitude ψ i.1))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact M.remoteBranchMatrix_eq_zero_of_not_positive ψ i.1 i.2
  rw [hzero, add_zero]

/-- A weighted normalized remote marginal is its unnormalized branch marginal. -/
theorem branchWeight_smul_normalizedBranch_traceLeft_matrix
    (M : FiniteInstrument A A' R) (ψ : Ket (A × B))
    (i : M.positiveSupport ψ) :
    M.branchWeight ψ i.1 • (M.normalizedBranch ψ i).state.traceLeft.m =
      Matrix.traceLeft
        (rankOneMatrix (M.postAmplitude ψ i.1)) := by
  have hmatrix := M.branchWeight_smul_normalizedBranch_state_matrix ψ i
  ext b b'
  simp only [MState.traceLeft_m, Matrix.traceLeft, Matrix.of_apply, Matrix.smul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a' _
  have hentry := congrFun (congrFun hmatrix (a', b)) (a', b')
  simpa only [Matrix.smul_apply] using hentry

/-- Remote marginals of the normalized positive branches, with canonical weights. -/
def remoteMarginalEnsemble
    (M : FiniteInstrument A A' R) (ψ : Ket (A × B)) :
    MEnsemble B (M.positiveSupport ψ) :=
  .ofProbs
    (fun i => M.branchWeight ψ i.1)
    (M.sum_positiveSupport_branchWeight_eq_one ψ)
    (fun i => (M.normalizedBranch ψ i).state.traceLeft)

/-- The canonical remote marginal ensemble averages exactly to the input remote marginal. -/
theorem remoteMarginalEnsemble_averageState
    (M : FiniteInstrument A A' R) (ψ : Ket (A × B)) :
    (M.remoteMarginalEnsemble ψ).averageState = ψ.state.traceLeft := by
  classical
  apply MState.ext
  rw [MEnsemble.averageState_matrix]
  change (∑ i : M.positiveSupport ψ,
      M.branchWeight ψ i.1 •
        (M.normalizedBranch ψ i).state.traceLeft.m) =
    ψ.state.traceLeft.m
  calc
    (∑ i : M.positiveSupport ψ,
        M.branchWeight ψ i.1 •
          (M.normalizedBranch ψ i).state.traceLeft.m) =
        ∑ i : M.positiveSupport ψ,
          Matrix.traceLeft
            (rankOneMatrix (M.postAmplitude ψ i.1)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact M.branchWeight_smul_normalizedBranch_traceLeft_matrix ψ i
    _ = ∑ i : M.refinedBranchIndex,
        Matrix.traceLeft
          (rankOneMatrix (M.postAmplitude ψ i)) :=
      M.sum_positiveSupport_remoteBranchMatrix_eq_sum ψ
    _ = ψ.state.traceLeft.m :=
      M.sum_remoteBranchMatrix_eq_inputMarginal ψ

/-- Probability-weighted remote entropy of the normalized refined pure branches. -/
def refinedBranchAverageEntanglement
    (M : FiniteInstrument A A' R) (ψ : Ket (A × B)) : ℝ :=
  ∑ i : M.positiveSupport ψ,
    (M.branchWeight ψ i.1 : ℝ) *
      (M.normalizedBranch ψ i).state.traceLeft.vonNeumann

/-- A finite local instrument cannot increase average pure-state entanglement. -/
theorem average_pure_entanglement_le
    (M : FiniteInstrument A A' R) (ψ : Ket (A × B)) :
    M.refinedBranchAverageEntanglement ψ ≤ ψ.state.traceLeft.vonNeumann := by
  classical
  have h := MEnsemble.vonNeumann_average_ge_sum (M.remoteMarginalEnsemble ψ)
  rw [M.remoteMarginalEnsemble_averageState ψ] at h
  simpa [refinedBranchAverageEntanglement, remoteMarginalEnsemble] using h

end FiniteInstrument

end

end QIT
