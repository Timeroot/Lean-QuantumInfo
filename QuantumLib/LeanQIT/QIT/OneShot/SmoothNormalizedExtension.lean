/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.SmoothAttainment
public import QIT.States.TraceNorm.BlockMatrix

/-!
# Normalized extensions for smooth conditional min-entropy

This module follows Tomamichel's normalized-extension construction from
`calculus.tex:525-554`.  A subnormalized optimizer is placed in one summand of
an enlarged source register, while its missing trace is diluted over an
orthogonal source summand.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QIT

universe u v w

noncomputable section

namespace SmoothNormalizedExtension

/-- Distribute a direct sum of two joint systems over their common right
factor. -/
def sourceSumEquiv (extra : Type w) (a : Type u) (b : Type v) :
    Sum (Prod extra b) (Prod a b) ≃ Prod (Sum extra a) b where
  toFun
    | Sum.inl eb => (Sum.inl eb.1, eb.2)
    | Sum.inr ab => (Sum.inr ab.1, ab.2)
  invFun
    | (Sum.inl e, y) => Sum.inl (e, y)
    | (Sum.inr x, y) => Sum.inr (x, y)
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨x | x, y⟩ <;> rfl

private theorem submatrix_equiv_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A B : CMatrix κ) :
    (A * B).submatrix e e = A.submatrix e e * B.submatrix e e := by
  classical
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  exact (Fintype.sum_equiv e
    (fun x => A (e i) (e x) * B (e x) (e j))
    (fun y => A (e i) y * B y (e j))
    (by simp)).symm

/-- Positive square roots commute with relabeling along a finite equivalence. -/
theorem psdSqrt_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
    {M : CMatrix ι} (hM : M.PosSemidef) :
    psdSqrt (M.submatrix e.symm e.symm) =
      (psdSqrt M).submatrix e.symm e.symm := by
  let S : CMatrix κ := (psdSqrt M).submatrix e.symm e.symm
  have hSpos : S.PosSemidef := (psdSqrt_pos M).submatrix e.symm
  have hSsq : S * S = M.submatrix e.symm e.symm := by
    dsimp [S]
    rw [← submatrix_equiv_mul e.symm, psdSqrt_mul_self_of_posSemidef hM]
  simpa [psdSqrt, S] using
    (CFC.sqrt_unique (a := M.submatrix e.symm e.symm) (b := S)
      hSsq hSpos.nonneg)

/-- Root fidelity is invariant under a simultaneous finite basis relabeling. -/
theorem State.fidelity_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (ρ σ : State ι) (e : ι ≃ κ) :
    (ρ.reindex e).fidelity (σ.reindex e) = ρ.fidelity σ := by
  rw [State.fidelity, State.fidelity]
  change traceNorm
      (psdSqrt (ρ.reindex e).matrix * psdSqrt (σ.reindex e).matrix) =
    traceNorm (psdSqrt ρ.matrix * psdSqrt σ.matrix)
  rw [State.reindex_matrix, State.reindex_matrix]
  rw [psdSqrt_submatrix_equiv e ρ.pos, psdSqrt_submatrix_equiv e σ.pos]
  rw [← submatrix_equiv_mul e.symm]
  exact traceNorm_submatrix_equiv e.symm (psdSqrt ρ.matrix * psdSqrt σ.matrix)

/-- The direct-sum state before distributing the common side-information
factor over the enlarged source register. -/
def blockExtensionCoarseState
    {extra : Type w} {a : Type u} {b : Type v}
    [Fintype extra] [DecidableEq extra] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (ρ : SubnormalizedState (Prod a b)) (failure : State (Prod extra b)) :
    State (Sum (Prod extra b) (Prod a b)) :=
  let q := 1 - ρ.matrix.trace.re
  {
    matrix := Matrix.fromBlocks (q • failure.matrix) 0 0 ρ.matrix
    pos := Matrix.fromBlocks_diagonal_posSemidef
      (Matrix.PosSemidef.smul failure.pos (sub_nonneg.mpr ρ.trace_le_one)) ρ.pos
    trace_eq_one := by
      rw [Matrix.trace_fromBlocks_diagonal, Matrix.trace_smul, failure.trace_eq_one]
      apply Complex.ext
      · simp [q]
      · simpa using ρ.trace_im_zero
  }

/-- The direct-sum normalized extension with an arbitrary normalized failure
state on the orthogonal source summand. -/
def blockExtensionState
    {extra : Type w} {a : Type u} {b : Type v}
    [Fintype extra] [DecidableEq extra] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (ρ : SubnormalizedState (Prod a b)) (failure : State (Prod extra b)) :
    State (Prod (Sum extra a) b) :=
  (blockExtensionCoarseState ρ failure).reindex (sourceSumEquiv extra a b)

@[simp]
theorem blockExtensionCoarseState_matrix
    {extra : Type w} {a : Type u} {b : Type v}
    [Fintype extra] [DecidableEq extra] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (ρ : SubnormalizedState (Prod a b)) (failure : State (Prod extra b)) :
    (blockExtensionCoarseState ρ failure).matrix =
      Matrix.fromBlocks ((1 - ρ.matrix.trace.re) • failure.matrix) 0 0 ρ.matrix :=
  rfl

@[simp]
theorem blockExtensionState_matrix
    {extra : Type w} {a : Type u} {b : Type v}
    [Fintype extra] [DecidableEq extra] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (ρ : SubnormalizedState (Prod a b)) (failure : State (Prod extra b)) :
    (blockExtensionState ρ failure).matrix =
      (Matrix.fromBlocks
        ((1 - ρ.matrix.trace.re) • failure.matrix) 0 0 ρ.matrix).submatrix
          (sourceSumEquiv extra a b).symm (sourceSumEquiv extra a b).symm :=
  rfl

/-- Adding missing trace in an orthogonal source summand does not alter root
fidelity against a normalized center. -/
theorem blockExtensionState_fidelity
    {extra : Type w} {a : Type u} {b : Type v}
    [Fintype extra] [DecidableEq extra] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (ρ : State (Prod a b)) (σ : SubnormalizedState (Prod a b))
    (failure : State (Prod extra b)) :
    (blockExtensionState ρ.toSubnormalized failure).fidelity
        (blockExtensionState σ failure) =
      traceNorm (ρ.sqrtMatrix * psdSqrt σ.matrix) := by
  rw [blockExtensionState, blockExtensionState]
  rw [State.fidelity_reindex]
  rw [State.fidelity]
  change traceNorm
      (psdSqrt (blockExtensionCoarseState ρ.toSubnormalized failure).matrix *
        psdSqrt (blockExtensionCoarseState σ failure).matrix) = _
  rw [blockExtensionCoarseState_matrix, blockExtensionCoarseState_matrix]
  have hq : 0 ≤ 1 - σ.matrix.trace.re := sub_nonneg.mpr σ.trace_le_one
  rw [show 1 - ρ.toSubnormalized.matrix.trace.re = 0 by
    rw [State.toSubnormalized_trace]
    norm_num]
  simp only [zero_smul]
  rw [State.toSubnormalized_matrix]
  rw [Matrix.fromBlocks_diagonal_psdSqrt Matrix.PosSemidef.zero ρ.pos]
  rw [Matrix.fromBlocks_diagonal_psdSqrt
    (Matrix.PosSemidef.smul failure.pos hq) σ.pos]
  rw [Matrix.fromBlocks_multiply]
  simp only [psdSqrt_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [Matrix.traceNorm_fromBlocks_diagonal]
  simp [State.sqrtMatrix]

/-- The direct-sum extension preserves purified distance from a normalized
center, even when the candidate on the original summand is subnormalized. -/
theorem blockExtensionState_purifiedDistance
    {extra : Type w} {a : Type u} {b : Type v}
    [Fintype extra] [DecidableEq extra] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (ρ : State (Prod a b)) (σ : SubnormalizedState (Prod a b))
    (failure : State (Prod extra b)) :
    (blockExtensionState ρ.toSubnormalized failure).purifiedDistance
        (blockExtensionState σ failure) =
      ρ.toSubnormalized.purifiedDistance σ := by
  rw [State.purifiedDistance_eq, SubnormalizedState.purifiedDistance_eq]
  rw [State.squaredFidelity_eq_fidelity_sq]
  rw [blockExtensionState_fidelity]
  rw [SubnormalizedState.generalizedFidelity_eq]
  rw [State.toSubnormalized_matrix, ρ.trace_re_eq_one]
  simp [State.sqrtMatrix]

/-- A candidate in the original subnormalized purified-distance ball remains
in the same ball after the source direct-sum normalized extension. -/
theorem blockExtensionState_purifiedBall
    {extra : Type w} {a : Type u} {b : Type v}
    [Fintype extra] [DecidableEq extra] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (ρ : State (Prod a b)) (σ : SubnormalizedState (Prod a b))
    (failure : State (Prod extra b)) {ε : ℝ}
    (hball : ρ.toSubnormalized.purifiedBall ε σ) :
    (blockExtensionState ρ.toSubnormalized failure).purifiedBall ε
      (blockExtensionState σ failure) := by
  rw [State.purifiedBall_eq]
  rw [blockExtensionState_purifiedDistance]
  exact hball

/-- For a normalized center, the direct-sum extension is exactly the existing
right-summand source isometry, viewed in the subnormalized state space. -/
theorem blockExtensionState_toSubnormalized_center
    {extra : Type w} {a : Type u} {b : Type v}
    [Fintype extra] [DecidableEq extra] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (ρ : State (Prod a b)) (failure : State (Prod extra b)) :
    (blockExtensionState ρ.toSubnormalized failure).toSubnormalized =
      ρ.toSubnormalized.sourceIsometryApply
        (ReferenceIsometry.sumInr extra a) := by
  apply SubnormalizedState.ext
  ext i j
  rcases i with ⟨i, ib⟩
  rcases j with ⟨j, jb⟩
  cases i <;> cases j <;>
    simp [blockExtensionState_matrix, sourceSumEquiv,
      SubnormalizedState.sourceIsometryApply_matrix,
      ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
      ReferenceIsometry.sumInr, Matrix.mul_apply, ρ.trace_re_eq_one]

/-- If the extra source dimension dilutes the missing trace below the optimal
conditional-min scale, the direct-sum extension is feasible for the same side
operator. -/
theorem blockExtensionState_scaleFeasible
    {extra : Type w} {a : Type u} {b : Type v}
    [Fintype extra] [DecidableEq extra] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Nonempty extra]
    (ρ : SubnormalizedState (Prod a b)) (T : CMatrix b) (σ : State b)
    (hT : SubnormalizedState.ConditionalMinEntropyScaleFeasible (a := a) ρ T)
    (hnormalize : ((T.trace.re : ℂ) • σ.matrix) = T)
    (hdim : 1 - ρ.matrix.trace.re ≤ (Fintype.card extra : ℝ) * T.trace.re) :
    State.ConditionalMinEntropyScaleFeasible (a := Sum extra a)
      (blockExtensionState ρ ((State.maximallyMixed extra).prod σ)) T := by
  constructor
  · exact hT.1
  · rw [Matrix.le_iff]
    let failure : State (Prod extra b) := (State.maximallyMixed extra).prod σ
    let topDiff : CMatrix (Prod extra b) :=
      Matrix.kronecker (1 : CMatrix extra) T -
        (1 - ρ.matrix.trace.re) • failure.matrix
    let bottomDiff : CMatrix (Prod a b) :=
      Matrix.kronecker (1 : CMatrix a) T - ρ.matrix
    have hfailure :
        State.identityTensorStateMatrix (a := extra) σ =
          ((Fintype.card extra : ℝ) : ℂ) • failure.matrix := by
      simpa [failure] using
        State.identityTensorStateMatrix_eq_card_smul_maximallyMixed_prod
          (a := extra) σ
    have htop_eq :
        topDiff =
          ((Fintype.card extra : ℝ) * T.trace.re -
              (1 - ρ.matrix.trace.re)) • failure.matrix := by
      dsimp [topDiff]
      calc
        Matrix.kronecker (1 : CMatrix extra) T -
              (1 - ρ.matrix.trace.re) • failure.matrix =
            Matrix.kronecker (1 : CMatrix extra)
                ((T.trace.re : ℂ) • σ.matrix) -
              (1 - ρ.matrix.trace.re) • failure.matrix := by rw [hnormalize]
        _ = (T.trace.re : ℂ) • State.identityTensorStateMatrix (a := extra) σ -
              (1 - ρ.matrix.trace.re) • failure.matrix := by
              congr 1
              ext i j
              simp [State.identityTensorStateMatrix, Matrix.kronecker,
                Matrix.kroneckerMap_apply]
              ring
        _ = ((Fintype.card extra : ℝ) * T.trace.re -
              (1 - ρ.matrix.trace.re)) • failure.matrix := by
              rw [hfailure]
              module
    have htop : topDiff.PosSemidef := by
      rw [htop_eq]
      exact Matrix.PosSemidef.smul failure.pos (sub_nonneg.mpr hdim)
    have hbottom : bottomDiff.PosSemidef := by
      simpa [bottomDiff, Matrix.le_iff] using hT.2
    have hcoarse :
        (Matrix.fromBlocks topDiff 0 0 bottomDiff :
          CMatrix (Sum (Prod extra b) (Prod a b))).PosSemidef :=
      Matrix.fromBlocks_diagonal_posSemidef htop hbottom
    have hmatrix :
        Matrix.kronecker (1 : CMatrix (Sum extra a)) T -
            (blockExtensionState ρ failure).matrix =
          (Matrix.fromBlocks topDiff 0 0 bottomDiff).submatrix
            (sourceSumEquiv extra a b).symm (sourceSumEquiv extra a b).symm := by
      ext i j
      rcases i with ⟨i, ib⟩
      rcases j with ⟨j, jb⟩
      cases i <;> cases j <;>
        simp [blockExtensionState_matrix, sourceSumEquiv, topDiff, bottomDiff,
          failure, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.one_apply]
    rw [hmatrix]
    exact hcoarse.submatrix (sourceSumEquiv extra a b).symm

/-- Tomamichel's normalized-extension lemma for smooth conditional
min-entropy.  The theorem returns an optimal side operator and a normalized
state on an explicitly enlarged source system. -/
theorem exists_normalizedExtension_smoothConditionalMinEntropy
    {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    ∃ (n : ℕ) (Tmin : CMatrix b) (σB : State b)
      (ρhat : State (Prod (Sum (Fin (n + 1)) a) b)),
      0 < Tmin.trace.re ∧
        ((Tmin.trace.re : ℂ) • σB.matrix) = Tmin ∧
          State.ConditionalMinEntropyScaleFeasible
            (a := Sum (Fin (n + 1)) a) ρhat Tmin ∧
            (ρ.toSubnormalized.sourceIsometryApply
              (ReferenceIsometry.sumInr (Fin (n + 1)) a)).purifiedBall
                ε ρhat.toSubnormalized ∧
              ρhat.conditionalMinEntropy = -log2 Tmin.trace.re ∧
              ρhat.conditionalMinEntropy =
                ρ.smoothConditionalMinEntropy ε hε0 hε1 := by
  have hεsub : ε < Real.sqrt ρ.toSubnormalized.matrix.trace.re :=
    ρ.epsilon_lt_sqrt_toSubnormalized_trace hε1
  rcases ρ.toSubnormalized.smoothConditionalMinEntropy_exists_scale_optimizer
      (a := a) hε0 hεsub with
    ⟨ρmin, Tmin, hρmin, hρmin_ball, hTmin_feas, hscale_eq, hsmooth_eq, _hoptimizer⟩
  have hρmin_trace_pos : 0 < ρmin.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      ρ.toSubnormalized ρmin hεsub hρmin_ball
  have hTmin_trace_pos : 0 < Tmin.trace.re := by
    have hscale_pos :=
      ρmin.conditionalMinEntropyScale_pos_of_trace_pos (a := a) hρmin_trace_pos
    rwa [hscale_eq] at hscale_pos
  let σB : State b :=
    State.ofPosSemidefTracePos Tmin hTmin_feas.1 hTmin_trace_pos
  have hnormalize : ((Tmin.trace.re : ℂ) • σB.matrix) = Tmin := by
    exact State.smul_ofPosSemidefTracePos_matrix
      Tmin hTmin_feas.1 hTmin_trace_pos
  let n : ℕ := Nat.ceil (Tmin.trace.re)⁻¹
  let extra := Fin (n + 1)
  let failure : State (Prod extra b) := (State.maximallyMixed extra).prod σB
  let ρhat : State (Prod (Sum extra a) b) :=
    blockExtensionState ρmin failure
  have hdim :
      1 - ρmin.matrix.trace.re ≤ (Fintype.card extra : ℝ) * Tmin.trace.re := by
    have hmissing : 1 - ρmin.matrix.trace.re ≤ 1 := by
      linarith [ρmin.trace_nonneg]
    have hinv_le :
        (Tmin.trace.re)⁻¹ ≤ (Nat.ceil (Tmin.trace.re)⁻¹ : ℝ) :=
      Nat.le_ceil _
    have hceil_le_extra :
        (Nat.ceil (Tmin.trace.re)⁻¹ : ℝ) ≤ Fintype.card extra := by
      simp [extra, n]
    have hone_le : 1 ≤ (Fintype.card extra : ℝ) * Tmin.trace.re := by
      have hmul := mul_le_mul_of_nonneg_right
        (hinv_le.trans hceil_le_extra) hTmin_trace_pos.le
      field_simp [hTmin_trace_pos.ne'] at hmul
      simpa [mul_comm] using hmul
    exact hmissing.trans hone_le
  have hρhat_feas :
      State.ConditionalMinEntropyScaleFeasible
        (a := Sum extra a) ρhat Tmin := by
    exact blockExtensionState_scaleFeasible ρmin Tmin σB hTmin_feas hnormalize hdim
  have hball_state :
      (blockExtensionState ρ.toSubnormalized failure).purifiedBall ε ρhat := by
    exact blockExtensionState_purifiedBall ρ ρmin failure hρmin_ball
  have hball_sub :
      (ρ.toSubnormalized.sourceIsometryApply
        (ReferenceIsometry.sumInr extra a)).purifiedBall ε ρhat.toSubnormalized := by
    have h :=
      (State.purifiedBall_iff_toSubnormalized_purifiedBall
        (blockExtensionState ρ.toSubnormalized failure) ρhat ε).mp hball_state
    rwa [blockExtensionState_toSubnormalized_center] at h
  have hscale_hat_le :
      ρhat.conditionalMinEntropyScale (a := Sum extra a) ≤ Tmin.trace.re := by
    rw [State.conditionalMinEntropyScale_eq_sInf_scaleValueSet]
    have hbdd :
        BddBelow (ρhat.conditionalMinEntropyScaleValueSet (a := Sum extra a)) := by
      rw [ρhat.conditionalMinEntropyScaleValueSet_eq_normalizedScaleValueSet
        (a := Sum extra a)]
      exact ρhat.conditionalMinEntropyNormalizedScaleValueSet_bddBelow
        (a := Sum extra a)
    exact csInf_le hbdd ⟨Tmin, hρhat_feas, rfl⟩
  have hmin_lower : ρmin.conditionalMinEntropyRaw ≤ ρhat.conditionalMinEntropy := by
    rw [ρmin.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a) hρmin_trace_pos]
    rw [ρhat.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty
      (a := Sum extra a)]
    rw [hscale_eq]
    unfold log2
    exact neg_le_neg (div_le_div_of_nonneg_right
      (Real.log_le_log
        (ρhat.conditionalMinEntropyScale_eq_normalizedScale (a := Sum extra a) ▸
          ρhat.conditionalMinEntropyNormalizedScale_inf_pos (a := Sum extra a))
        hscale_hat_le)
      (le_of_lt (Real.log_pos one_lt_two)))
  have hmin_upper : ρhat.conditionalMinEntropy ≤ ρmin.conditionalMinEntropyRaw := by
    have hcand :
        SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw
          (a := Sum extra a)
          (ρ.toSubnormalized.sourceIsometryApply
            (ReferenceIsometry.sumInr extra a)) ε
          ρhat.conditionalMinEntropy :=
      ⟨ρhat.toSubnormalized, hball_sub,
        (State.toSubnormalized_conditionalMinEntropyRaw_eq ρhat).symm⟩
    have hle :=
      SubnormalizedState.le_smoothConditionalMinEntropy_of_candidate_of_lt_sqrt_trace
        (a := Sum extra a) hε0 (by
          rwa [SubnormalizedState.sourceIsometryApply_trace_re]) hcand
    rw [ρ.toSubnormalized.smoothConditionalMinEntropy_sourceIsometryApply
      (a := a) (ReferenceIsometry.sumInr extra a) hε0 hεsub] at hle
    rw [hsmooth_eq] at hle
    exact hle
  refine ⟨n, Tmin, σB, ρhat, hTmin_trace_pos, hnormalize, ?_, hball_sub, ?_, ?_⟩
  · simpa [extra, n] using hρhat_feas
  · calc
      ρhat.conditionalMinEntropy = ρmin.conditionalMinEntropyRaw :=
        le_antisymm hmin_upper hmin_lower
      _ = -log2 Tmin.trace.re := by
        rw [ρmin.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
          (a := a) hρmin_trace_pos, hscale_eq]
  · rw [State.smoothConditionalMinEntropy_eq_toSubnormalized]
    rw [hsmooth_eq]
    exact le_antisymm hmin_upper hmin_lower

/-- Concrete block form of right-summand source padding. -/
theorem sourceIsometryApply_sumInr_matrix
    {extra : Type w} {a : Type u} {b : Type v}
    [Fintype extra] [DecidableEq extra] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (ρ : SubnormalizedState (Prod a b)) :
    (ρ.sourceIsometryApply (ReferenceIsometry.sumInr extra a)).matrix =
      (Matrix.fromBlocks (0 : CMatrix (Prod extra b)) 0 0 ρ.matrix).submatrix
        (sourceSumEquiv extra a b).symm (sourceSumEquiv extra a b).symm := by
  ext i j
  rcases i with ⟨i, ib⟩
  rcases j with ⟨j, jb⟩
  cases i <;> cases j <;>
    simp [SubnormalizedState.sourceIsometryApply_matrix, sourceSumEquiv,
      ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
      ReferenceIsometry.sumInr, Matrix.mul_apply]

/-- The source identity tensor is block diagonal under the direct-sum/product
equivalence. -/
theorem identityTensorStateMatrix_sourceSumEquiv
    {extra : Type w} {a : Type u} {b : Type v}
    [Fintype extra] [DecidableEq extra] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (σ : SubnormalizedState b) :
    SubnormalizedState.identityTensorStateMatrix (a := Sum extra a) σ =
      (Matrix.fromBlocks
        (SubnormalizedState.identityTensorStateMatrix (a := extra) σ) 0 0
        (SubnormalizedState.identityTensorStateMatrix (a := a) σ)).submatrix
          (sourceSumEquiv extra a b).symm (sourceSumEquiv extra a b).symm := by
  ext i j
  rcases i with ⟨i, ib⟩
  rcases j with ⟨j, jb⟩
  cases i <;> cases j <;>
    simp [sourceSumEquiv, SubnormalizedState.identityTensorStateMatrix,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- The raw max-entropy trace-norm factor is invariant under concrete
right-summand padding of the source register. -/
theorem traceNorm_sourceIsometryApply_sumInr_mul_sqrt_identityTensorStateMatrix
    {extra : Type w} {a : Type u} {b : Type v}
    [Fintype extra] [DecidableEq extra] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) :
    traceNorm
        (psdSqrt
            (ρ.sourceIsometryApply (ReferenceIsometry.sumInr extra a)).matrix *
          psdSqrt
            (SubnormalizedState.identityTensorStateMatrix (a := Sum extra a) σ)) =
      traceNorm
        (psdSqrt ρ.matrix *
          psdSqrt (SubnormalizedState.identityTensorStateMatrix (a := a) σ)) := by
  let e := sourceSumEquiv extra a b
  let topSide := SubnormalizedState.identityTensorStateMatrix (a := extra) σ
  let bottomSide := SubnormalizedState.identityTensorStateMatrix (a := a) σ
  rw [sourceIsometryApply_sumInr_matrix, identityTensorStateMatrix_sourceSumEquiv]
  rw [psdSqrt_submatrix_equiv e
    (Matrix.fromBlocks_diagonal_posSemidef Matrix.PosSemidef.zero ρ.pos)]
  rw [psdSqrt_submatrix_equiv e
    (Matrix.fromBlocks_diagonal_posSemidef
      (SubnormalizedState.identityTensorStateMatrix_posSemidef (a := extra) σ)
      (SubnormalizedState.identityTensorStateMatrix_posSemidef (a := a) σ))]
  rw [← submatrix_equiv_mul e.symm]
  rw [traceNorm_submatrix_equiv e.symm]
  rw [Matrix.fromBlocks_diagonal_psdSqrt Matrix.PosSemidef.zero ρ.pos]
  rw [Matrix.fromBlocks_diagonal_psdSqrt
    (SubnormalizedState.identityTensorStateMatrix_posSemidef (a := extra) σ)
    (SubnormalizedState.identityTensorStateMatrix_posSemidef (a := a) σ)]
  rw [Matrix.fromBlocks_multiply]
  simp only [psdSqrt_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [Matrix.traceNorm_fromBlocks_diagonal]
  simp

/-- Unsmoothed subnormalized conditional max-entropy is invariant under the
concrete source padding used by the normalized-extension proof. -/
theorem conditionalMaxEntropyRaw_sourceIsometryApply_sumInr
    {extra : Type w} {a : Type u} {b : Type v}
    [Fintype extra] [DecidableEq extra] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (ρ : SubnormalizedState (Prod a b)) :
    (ρ.sourceIsometryApply
      (ReferenceIsometry.sumInr extra a)).conditionalMaxEntropyRaw =
        ρ.conditionalMaxEntropyRaw := by
  rw [SubnormalizedState.conditionalMaxEntropyRaw_eq,
    SubnormalizedState.conditionalMaxEntropyRaw_eq]
  congr 1
  ext h
  constructor
  · rintro ⟨σ, hpos, rfl⟩
    refine ⟨σ, ?_, ?_⟩
    · simpa only [traceNorm_sourceIsometryApply_sumInr_mul_sqrt_identityTensorStateMatrix]
        using hpos
    · unfold SubnormalizedState.conditionalMaxEntropyFidelityCandidate
      rw [traceNorm_sourceIsometryApply_sumInr_mul_sqrt_identityTensorStateMatrix]
  · rintro ⟨σ, hpos, rfl⟩
    refine ⟨σ, ?_, ?_⟩
    · simpa only [traceNorm_sourceIsometryApply_sumInr_mul_sqrt_identityTensorStateMatrix]
        using hpos
    · unfold SubnormalizedState.conditionalMaxEntropyFidelityCandidate
      rw [traceNorm_sourceIsometryApply_sumInr_mul_sqrt_identityTensorStateMatrix]

end SmoothNormalizedExtension

end

end QIT
