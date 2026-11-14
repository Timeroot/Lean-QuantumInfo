/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.SmoothAttainment
public import QIT.OneShot.SmoothEndpoint
public import QIT.Information.Renyi.RenyiDPI.Domain

set_option maxHeartbeats 1000000

/-!
# Support restriction for smooth conditional entropies

This module contains the dimension-preserving support filter used in the
support-restriction argument for smooth conditional min- and max-entropy.
The optimizer theorems are proved below the elementary filter API so that the
matrix support statement remains independent of compression index types.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Pointwise

open Matrix

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace SubnormalizedState

/-- The spectral support projector of a positive semidefinite matrix. -/
def supportProjector (M : CMatrix a) (hM : M.PosSemidef) : CMatrix a :=
  psdInvSqrt M hM.isHermitian * M * psdInvSqrt M hM.isHermitian

@[simp]
theorem supportProjector_apply (M : CMatrix a) (hM : M.PosSemidef) :
    supportProjector M hM =
      psdInvSqrt M hM.isHermitian * M * psdInvSqrt M hM.isHermitian :=
  rfl

/-- The product support projector associated with a bipartite state. -/
def bipartiteSupportProjector (ρ : SubnormalizedState (Prod a b)) :
    CMatrix (Prod a b) :=
  Matrix.kronecker
    (supportProjector ρ.marginalA.matrix ρ.marginalA.pos)
    (supportProjector ρ.marginalB.matrix ρ.marginalB.pos)

/-- The one-Kraus support filter on a bipartite matrix. -/
def supportFilter (ρ : SubnormalizedState (Prod a b)) :
    MatrixMap (Prod a b) (Prod a b) :=
  MatrixMap.ofKraus (fun _ : Unit => bipartiteSupportProjector ρ)

@[simp]
theorem supportFilter_apply (ρ : SubnormalizedState (Prod a b))
    (X : CMatrix (Prod a b)) :
    supportFilter ρ X =
      bipartiteSupportProjector ρ * X *
        Matrix.conjTranspose (bipartiteSupportProjector ρ) := by
  simp [supportFilter, MatrixMap.ofKraus]

theorem supportFilter_completelyPositive
    (ρ : SubnormalizedState (Prod a b)) :
    MatrixMap.IsCompletelyPositive (supportFilter ρ) := by
  exact MatrixMap.ofKraus_isCompletelyPositive _

/- The order estimate for the product support projector is kept as a local
   lemma.  It is the only algebraic input needed to construct the TNI map. -/
theorem bipartiteSupportProjector_posSemidef
    (ρ : SubnormalizedState (Prod a b)) :
    (bipartiteSupportProjector ρ).PosSemidef := by
  apply Matrix.PosSemidef.kronecker
  · exact psdInvSqrt_support_posSemidef ρ.marginalA.pos
  · exact psdInvSqrt_support_posSemidef ρ.marginalB.pos

theorem supportFilter_traceNonincreasing
    (ρ : SubnormalizedState (Prod a b)) :
    MatrixMap.IsTraceNonincreasing (supportFilter ρ) := by
  intro X hX
  have hP : (bipartiteSupportProjector ρ).PosSemidef :=
    bipartiteSupportProjector_posSemidef ρ
  have hPle : bipartiteSupportProjector ρ ≤ (1 : CMatrix (Prod a b)) := by
    let PA : CMatrix a := supportProjector ρ.marginalA.matrix ρ.marginalA.pos
    let PB : CMatrix b := supportProjector ρ.marginalB.matrix ρ.marginalB.pos
    have hPA : PA.PosSemidef := by
      exact psdInvSqrt_support_posSemidef ρ.marginalA.pos
    have hPB : PB.PosSemidef := by
      exact psdInvSqrt_support_posSemidef ρ.marginalB.pos
    have hPAle : PA ≤ (1 : CMatrix a) := by
      exact psdInvSqrt_support_le_one ρ.marginalA.pos
    have hPBle : PB ≤ (1 : CMatrix b) := by
      exact psdInvSqrt_support_le_one ρ.marginalB.pos
    have hleft : ((1 : CMatrix a) - PA).PosSemidef := Matrix.le_iff.mp hPAle
    have hright : ((1 : CMatrix b) - PB).PosSemidef := Matrix.le_iff.mp hPBle
    have hdecomp :
        (1 : CMatrix (Prod a b)) - Matrix.kronecker PA PB =
          Matrix.kronecker ((1 : CMatrix a) - PA) PB +
            Matrix.kronecker (1 : CMatrix a) ((1 : CMatrix b) - PB) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.kronecker, Matrix.kroneckerMap_apply, sub_eq_add_neg]
        ring
      · by_cases h1 : i.1 = j.1
        · have h2 : i.2 ≠ j.2 := by
            intro h2
            exact hij (Prod.ext h1 h2)
          simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
            h1, h2, hij]
          ring
        · have hp : i ≠ j := hij
          simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
            h1, hp]
    rw [show bipartiteSupportProjector ρ = Matrix.kronecker PA PB by rfl]
    rw [Matrix.le_iff]
    rw [hdecomp]
    exact (hleft.kronecker hPB).add (Matrix.PosSemidef.one.kronecker hright)
  have hdiff :
      ((1 : CMatrix (Prod a b)) - bipartiteSupportProjector ρ).PosSemidef :=
    Matrix.le_iff.mp hPle
  have hnonneg := cMatrix_trace_mul_posSemidef_re_nonneg hX hdiff
  have htrace :
      (X * ((1 : CMatrix (Prod a b)) - bipartiteSupportProjector ρ)).trace.re =
        X.trace.re -
          (X * bipartiteSupportProjector ρ).trace.re := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    rw [Matrix.mul_one]
  have hPherm : (bipartiteSupportProjector ρ).IsHermitian := by
    exact hP.isHermitian
  have hPid : bipartiteSupportProjector ρ * bipartiteSupportProjector ρ =
      bipartiteSupportProjector ρ := by
    let PA : CMatrix a := supportProjector ρ.marginalA.matrix ρ.marginalA.pos
    let PB : CMatrix b := supportProjector ρ.marginalB.matrix ρ.marginalB.pos
    have hPAid : PA * PA = PA := by
      exact psdInvSqrt_support_idempotent ρ.marginalA.pos
    have hPBid : PB * PB = PB := by
      exact psdInvSqrt_support_idempotent ρ.marginalB.pos
    change Matrix.kronecker PA PB * Matrix.kronecker PA PB =
      Matrix.kronecker PA PB
    calc
      Matrix.kronecker PA PB * Matrix.kronecker PA PB =
          Matrix.kronecker (PA * PA) (PB * PB) := by
            exact (Matrix.mul_kronecker_mul PA PA PB PB).symm
      _ = Matrix.kronecker PA PB := by rw [hPAid, hPBid]
  have hout :
      (supportFilter ρ X).trace.re =
        (X * bipartiteSupportProjector ρ).trace.re := by
    rw [supportFilter_apply, Matrix.trace_mul_cycle]
    rw [hPherm.eq]
    rw [hPid]
    exact congrArg Complex.re (Matrix.trace_mul_comm _ _)
  rw [hout]
  linarith

theorem supportFilter_traceNonincreasingCP
    (ρ : SubnormalizedState (Prod a b)) :
    MatrixMap.TraceNonincreasingCP (supportFilter ρ) := by
  exact ⟨supportFilter_completelyPositive ρ,
    supportFilter_traceNonincreasing ρ⟩

/-- Applying the support filter gives a state on the original ambient space. -/
def supportFilterState (ρ τ : SubnormalizedState (Prod a b)) :
    SubnormalizedState (Prod a b) :=
  τ.applyTraceNonincreasingCP (supportFilter ρ)
    (supportFilter_traceNonincreasingCP ρ)

@[simp]
theorem supportFilterState_matrix (ρ τ : SubnormalizedState (Prod a b)) :
    (supportFilterState ρ τ).matrix =
      bipartiteSupportProjector ρ * τ.matrix *
        Matrix.conjTranspose (bipartiteSupportProjector ρ) := by
  change supportFilter ρ τ.matrix = _
  exact supportFilter_apply ρ τ.matrix

theorem supportFilterState_purifiedBall
    {ρ τ : SubnormalizedState (Prod a b)} {ε : ℝ}
    (hfix : supportFilterState ρ ρ = ρ)
    (hball : ρ.purifiedBall ε τ) :
    ρ.purifiedBall ε (supportFilterState ρ τ) := by
  have hball' := SubnormalizedState.purifiedBall_of_traceNonincreasingCP
    (ρ := ρ) (σ := τ) (ε := ε) (supportFilter ρ)
    (supportFilter_traceNonincreasingCP ρ) hball
  change (supportFilterState ρ ρ).purifiedBall ε
    (supportFilterState ρ τ) at hball'
  rw [hfix] at hball'
  exact hball'

theorem bipartiteSupport_center_support
    (ρ : SubnormalizedState (Prod a b)) :
    Matrix.Supports ρ.matrix
      (ρ.marginalA.prod ρ.marginalB).matrix := by
  by_cases htr : ρ.matrix.trace.re = 0
  · have hzero : ρ.matrix = 0 := by
      apply (Matrix.PosSemidef.trace_eq_zero_iff ρ.pos).mp
      apply Complex.ext
      · exact htr
      · exact ρ.trace_im_zero
    rw [hzero]
    exact Matrix.Supports.zero_left _
  · let ρn : State (Prod a b) := ρ.normalize htr
    have hnorm := ρn.matrix_supports_prod_marginals
    intro v hv
    have hA : ρn.marginalA.matrix =
        (ρ.matrix.trace.re)⁻¹ • ρ.marginalA.matrix := by
      dsimp [ρn]
      ext i j
      simp [QIT.partialTraceB, Matrix.smul_apply, Finset.mul_sum]
    have hB : ρn.marginalB.matrix =
        (ρ.matrix.trace.re)⁻¹ • ρ.marginalB.matrix := by
      dsimp [ρn]
      ext i j
      simp [QIT.partialTraceA, Matrix.smul_apply, Finset.mul_sum]
    have hprod : (ρn.marginalA.prod ρn.marginalB).matrix =
        (ρ.matrix.trace.re)⁻¹ ^ 2 •
          (ρ.marginalA.prod ρ.marginalB).matrix := by
      change Matrix.kronecker ρn.marginalA.matrix ρn.marginalB.matrix =
        (ρ.matrix.trace.re)⁻¹ ^ 2 •
          Matrix.kronecker ρ.marginalA.matrix ρ.marginalB.matrix
      rw [hA, hB]
      ext x y
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply]
      ring
    have hvn : (ρn.marginalA.prod ρn.marginalB).matrix.mulVec v = 0 := by
      rw [hprod]
      simp [Matrix.smul_mulVec, hv]
    have hmn := hnorm v hvn
    rw [SubnormalizedState.normalize_matrix] at hmn
    rw [Matrix.smul_mulVec] at hmn
    exact (smul_eq_zero.mp hmn).resolve_left (inv_ne_zero htr)

private theorem fixes_of_supports_projector
    {M P : CMatrix (Prod a b)} (hM : M.PosSemidef)
    (hP : P.PosSemidef) (hPid : P * P = P)
    (hSupport : Matrix.Supports M P) : P * M = M ∧ M * P = M := by
  have hPcomp : P * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hPid]
    abel
  have hMcomp : M * (1 - P) = 0 := by
    ext i j
    have hv := hSupport (fun k => (1 - P) k j) (by
      ext i'
      change ∑ k, P i' k * (1 - P) k j = 0
      simpa [Matrix.mul_apply] using congrFun (congrFun hPcomp i') j )
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hv i
  have hright : M * P = M := by
    calc
      M * P = M * (1 - (1 - P)) := by noncomm_ring
      _ = M := by rw [Matrix.mul_sub, hMcomp, Matrix.mul_one]; abel
  have hleft : P * M = M := by
    have hconj := congrArg Matrix.conjTranspose hright
    simpa [Matrix.conjTranspose_mul, hP.isHermitian.eq, hM.isHermitian.eq]
      using hconj
  exact ⟨hleft, hright⟩

theorem supportFilterState_center (ρ : SubnormalizedState (Prod a b)) :
    supportFilterState ρ ρ = ρ := by
  apply SubnormalizedState.ext
  have hcenter := bipartiteSupport_center_support ρ
  let NA : CMatrix a := ρ.marginalA.matrix
  let NB : CMatrix b := ρ.marginalB.matrix
  let PA : CMatrix a := supportProjector NA ρ.marginalA.pos
  let PB : CMatrix b := supportProjector NB ρ.marginalB.pos
  have hNA : NA * PA = NA := by
    exact (supportProjector_fixes_of_supports (M := NA) (N := NA)
      ρ.marginalA.pos ρ.marginalA.pos (Matrix.Supports.refl NA)).2
  have hNB : NB * PB = NB := by
    exact (supportProjector_fixes_of_supports (M := NB) (N := NB)
      ρ.marginalB.pos ρ.marginalB.pos (Matrix.Supports.refl NB)).2
  have hNP : Matrix.kronecker NA NB * Matrix.kronecker PA PB =
      Matrix.kronecker NA NB := by
    calc
      Matrix.kronecker NA NB * Matrix.kronecker PA PB =
          Matrix.kronecker (NA * PA) (NB * PB) := by
            exact (Matrix.mul_kronecker_mul NA PA NB PB).symm
      _ = Matrix.kronecker NA NB := by rw [hNA, hNB]
  have hNPsupport : Matrix.Supports (Matrix.kronecker NA NB)
      (Matrix.kronecker PA PB) :=
    Matrix.Supports.of_mul_right_eq_self hNP
  have hρP : Matrix.Supports ρ.matrix (Matrix.kronecker PA PB) := by
    exact hcenter.trans hNPsupport
  have hP : (Matrix.kronecker PA PB).PosSemidef :=
    (ρ.marginalA.pos |> psdInvSqrt_support_posSemidef).kronecker
      (ρ.marginalB.pos |> psdInvSqrt_support_posSemidef)
  have hPid : Matrix.kronecker PA PB * Matrix.kronecker PA PB =
      Matrix.kronecker PA PB := by
    have hPAid : PA * PA = PA := by
      exact psdInvSqrt_support_idempotent ρ.marginalA.pos
    have hPBid : PB * PB = PB := by
      exact psdInvSqrt_support_idempotent ρ.marginalB.pos
    calc
      Matrix.kronecker PA PB * Matrix.kronecker PA PB =
          Matrix.kronecker (PA * PA) (PB * PB) := by
            exact (Matrix.mul_kronecker_mul PA PA PB PB).symm
      _ = Matrix.kronecker PA PB := by
        rw [hPAid, hPBid]
  have hfix := fixes_of_supports_projector ρ.pos hP hPid hρP
  rw [supportFilterState_matrix]
  change bipartiteSupportProjector ρ * ρ.matrix *
      Matrix.conjTranspose (bipartiteSupportProjector ρ) = ρ.matrix
  rw [show bipartiteSupportProjector ρ = Matrix.kronecker PA PB by rfl,
    (hP.isHermitian).eq, hfix.1, hfix.2]

theorem supportFilterState_supports_projector
    (ρ τ : SubnormalizedState (Prod a b)) :
    Matrix.Supports (supportFilterState ρ τ).matrix
      (bipartiteSupportProjector ρ) := by
  apply Matrix.Supports.of_mul_right_eq_self
  rw [supportFilterState_matrix]
  have hP := bipartiteSupportProjector_posSemidef ρ
  have hPid : bipartiteSupportProjector ρ * bipartiteSupportProjector ρ =
      bipartiteSupportProjector ρ := by
    let PA : CMatrix a := supportProjector ρ.marginalA.matrix ρ.marginalA.pos
    let PB : CMatrix b := supportProjector ρ.marginalB.matrix ρ.marginalB.pos
    have hPA : PA * PA = PA := psdInvSqrt_support_idempotent ρ.marginalA.pos
    have hPB : PB * PB = PB := psdInvSqrt_support_idempotent ρ.marginalB.pos
    change Matrix.kronecker PA PB * Matrix.kronecker PA PB = _
    calc
      Matrix.kronecker PA PB * Matrix.kronecker PA PB =
          Matrix.kronecker (PA * PA) (PB * PB) := by
            exact (Matrix.mul_kronecker_mul PA PA PB PB).symm
      _ = Matrix.kronecker PA PB := by rw [hPA, hPB]
  have hPherm := hP.isHermitian
  rw [Matrix.mul_assoc, hPherm.eq, hPid]

private theorem supportFilter_side_trace_le
    {T : CMatrix b} (hT : T.PosSemidef)
    (ρ : SubnormalizedState (Prod a b)) :
    ((supportProjector ρ.marginalB.matrix ρ.marginalB.pos * T *
      supportProjector ρ.marginalB.matrix ρ.marginalB.pos).trace).re ≤
      T.trace.re := by
  let PB : CMatrix b := supportProjector ρ.marginalB.matrix ρ.marginalB.pos
  have hPle : PB ≤ (1 : CMatrix b) := psdInvSqrt_support_le_one ρ.marginalB.pos
  have hdiff : ((1 : CMatrix b) - PB).PosSemidef := Matrix.le_iff.mp hPle
  have hnonneg := cMatrix_trace_mul_posSemidef_re_nonneg hT hdiff
  have hPid : PB * PB = PB := psdInvSqrt_support_idempotent ρ.marginalB.pos
  have hPherm : PB.IsHermitian := psdInvSqrt_support_isHermitian ρ.marginalB.pos
  have hout : (PB * T * PB).trace.re = (T * PB).trace.re := by
    rw [Matrix.trace_mul_cycle, hPid]
    exact congrArg Complex.re (Matrix.trace_mul_comm _ _)
  rw [hout]
  have htrace : (T * ((1 : CMatrix b) - PB)).trace.re =
      T.trace.re - (T * PB).trace.re := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, Matrix.mul_one]
  linarith

private theorem transpose_referenceIsometry_matrix_mem_unitary
    (V : ReferenceIsometry a a) :
    Matrix.transpose V.matrix ∈ Matrix.unitaryGroup a ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  have h := congrFun (congrFun V.isometry j) i
  simpa [Matrix.mul_apply, Matrix.conjTranspose, Matrix.transpose, Matrix.one_apply,
    Finset.mul_sum, mul_comm, eq_comm] using h

private theorem supportRestriction_psdSqrt_projector_factor
    (E A : CMatrix a) (hA : A.PosSemidef)
    (hEherm : E.IsHermitian) :
    ∃ U : Matrix.unitaryGroup a ℂ,
      psdSqrt (E * A * E) = E * psdSqrt A * (U : CMatrix a) := by
  have hEA : (E * A * E).PosSemidef := by
    have h := hA.conjTranspose_mul_mul_same E
    rw [hEherm.eq] at h
    simpa [Matrix.mul_assoc] using h
  let X : CMatrix a := E * psdSqrt A
  let S : CMatrix a := psdSqrt (E * A * E)
  have hSsq : S * Matrix.conjTranspose S = E * A * E := by
    dsimp [S]
    rw [psdSqrt_isHermitian (E * A * E), psdSqrt_mul_self_of_posSemidef hEA]
  have hXgram : X * Matrix.conjTranspose X = E * A * E := by
    dsimp [X]
    rw [Matrix.conjTranspose_mul, hEherm.eq, psdSqrt_isHermitian A]
    calc
      E * psdSqrt A * (psdSqrt A * E) =
          E * (psdSqrt A * psdSqrt A) * E := by simp [Matrix.mul_assoc]
      _ = E * A * E := by rw [psdSqrt_mul_self_of_posSemidef hA]
  obtain ⟨V, hV⟩ :=
    ReferenceIsometry.exists_eq_mul_transpose_of_mul_conjTranspose_eq
      (A := X) (B := S) (by rw [hXgram, hSsq]) (Nat.le_refl _)
  let U : Matrix.unitaryGroup a ℂ :=
    ⟨Matrix.transpose V.matrix, transpose_referenceIsometry_matrix_mem_unitary V⟩
  refine ⟨U, ?_⟩
  simpa [X, S, U] using hV

private theorem supportRestriction_traceNorm_psdSqrt_mul_psdSqrt_eq_trace_psdSqrt_sandwich
    (A B : CMatrix a) (hA : A.PosSemidef) :
    traceNorm (psdSqrt A * psdSqrt B) =
      (psdSqrt (psdSqrt B * A * psdSqrt B)).trace.re := by
  rw [← traceNorm_conjTranspose (psdSqrt A * psdSqrt B)]
  rw [Matrix.conjTranspose_mul, psdSqrt_isHermitian A,
    psdSqrt_isHermitian B]
  rw [traceNorm_eq_trace_psdSqrt_mul_conjTranspose]
  rw [Matrix.conjTranspose_mul, psdSqrt_isHermitian A,
    psdSqrt_isHermitian B]
  have hinside :
      psdSqrt B * psdSqrt A * (psdSqrt A * psdSqrt B) =
        psdSqrt B * A * psdSqrt B := by
    calc
      psdSqrt B * psdSqrt A * (psdSqrt A * psdSqrt B) =
          psdSqrt B * (psdSqrt A * psdSqrt A) * psdSqrt B := by
            simp [Matrix.mul_assoc]
      _ = psdSqrt B * A * psdSqrt B := by
            rw [psdSqrt_mul_self_of_posSemidef hA]
  rw [hinside]

private theorem supportRestriction_trace_psdSqrt_projector_compression_le
    (P X : CMatrix a) (hX : X.PosSemidef)
    (hPherm : P.IsHermitian)
    (hPle : Matrix.conjTranspose P * P ≤ (1 : CMatrix a)) :
    (psdSqrt (P * X * P)).trace.re ≤ (psdSqrt X).trace.re := by
  obtain ⟨U, hU⟩ := supportRestriction_psdSqrt_projector_factor P X hX hPherm
  have hnorm : traceNorm (psdSqrt (P * X * P)) ≤ traceNorm (psdSqrt X) := by
    rw [hU]
    have hUunit : Matrix.conjTranspose (U : CMatrix a) * (U : CMatrix a) = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using
        (Unitary.coe_star_mul_self U : star (U : CMatrix a) * (U : CMatrix a) = 1)
    calc
      traceNorm (P * psdSqrt X * (U : CMatrix a)) ≤
          traceNorm (P * psdSqrt X) :=
        MatrixMap.traceNorm_mul_contraction_le (P * psdSqrt X)
          (U : CMatrix a) hUunit.le
      _ = traceNorm (Matrix.conjTranspose (P * psdSqrt X)) := by
        rw [traceNorm_conjTranspose]
      _ = traceNorm (psdSqrt X * P) := by
        rw [Matrix.conjTranspose_mul, hPherm.eq, psdSqrt_isHermitian X]
      _ ≤ traceNorm (psdSqrt X) :=
        MatrixMap.traceNorm_mul_contraction_le (psdSqrt X) P hPle
  have hleft : traceNorm (psdSqrt (P * X * P)) =
      (psdSqrt (P * X * P)).trace.re := by
    rw [traceNorm_eq_trace_psdSqrt_mul_conjTranspose]
    have hsq : psdSqrt (P * X * P) *
        Matrix.conjTranspose (psdSqrt (P * X * P)) = P * X * P := by
      rw [psdSqrt_isHermitian (P * X * P),
        psdSqrt_mul_self_of_posSemidef (by
          simpa [hPherm.eq, Matrix.mul_assoc] using hX.conjTranspose_mul_mul_same P)]
    rw [hsq]
  have hright : traceNorm (psdSqrt X) = (psdSqrt X).trace.re := by
    rw [traceNorm_eq_trace_psdSqrt_mul_conjTranspose]
    have hsq : psdSqrt X * Matrix.conjTranspose (psdSqrt X) = X := by
      rw [psdSqrt_isHermitian X, psdSqrt_mul_self_of_posSemidef hX]
    rw [hsq]
  rw [← hleft, ← hright]
  exact hnorm

private theorem supportRestriction_candidate_compression_le
    (A P R : CMatrix a)
    (hA : A.PosSemidef)
    (hPherm : P.IsHermitian)
    (hPle : Matrix.conjTranspose P * P ≤ (1 : CMatrix a))
    (hcomm : P * psdSqrt R = psdSqrt R * P) :
    traceNorm (psdSqrt (P * A * P) * psdSqrt R) ≤
      traceNorm (psdSqrt A * psdSqrt R) := by
  have hsand : psdSqrt R * (P * A * P) * psdSqrt R =
      P * (psdSqrt R * A * psdSqrt R) * P := by
    calc
      psdSqrt R * (P * A * P) * psdSqrt R =
          (psdSqrt R * P) * A * (P * psdSqrt R) := by simp [Matrix.mul_assoc]
      _ = (P * psdSqrt R) * A * (psdSqrt R * P) := by
        rw [hcomm.symm, hcomm]
      _ = P * (psdSqrt R * A * psdSqrt R) * P := by simp [Matrix.mul_assoc]
  calc
    traceNorm (psdSqrt (P * A * P) * psdSqrt R) =
        (psdSqrt (psdSqrt R * (P * A * P) * psdSqrt R)).trace.re :=
      supportRestriction_traceNorm_psdSqrt_mul_psdSqrt_eq_trace_psdSqrt_sandwich
        (P * A * P) R (by
          simpa [hPherm.eq, Matrix.mul_assoc] using hA.conjTranspose_mul_mul_same P)
    _ = (psdSqrt (P * (psdSqrt R * A * psdSqrt R) * P)).trace.re := by rw [hsand]
    _ ≤ (psdSqrt (psdSqrt R * A * psdSqrt R)).trace.re := by
      apply supportRestriction_trace_psdSqrt_projector_compression_le
      · have h := hA.conjTranspose_mul_mul_same (psdSqrt R)
        rw [psdSqrt_isHermitian R] at h
        simpa [Matrix.mul_assoc] using h
      · exact hPherm
      · exact hPle
    _ = traceNorm (psdSqrt A * psdSqrt R) :=
      (supportRestriction_traceNorm_psdSqrt_mul_psdSqrt_eq_trace_psdSqrt_sandwich
        A R hA).symm

private theorem supportRestriction_candidate_side_compression_eq
    (A R E : CMatrix a) (hR : R.PosSemidef)
    (hER : (E * R * E).PosSemidef)
    (hleft : psdSqrt A * E = psdSqrt A)
    (hright : E * psdSqrt A = psdSqrt A) :
    traceNorm (psdSqrt A * psdSqrt R) =
      traceNorm (psdSqrt A * psdSqrt (E * R * E)) := by
  have hsand : psdSqrt A * R * psdSqrt A =
      psdSqrt A * (E * R * E) * psdSqrt A := by
    calc
      psdSqrt A * R * psdSqrt A =
          (psdSqrt A * E) * R * (E * psdSqrt A) := by rw [hleft, hright]
      _ = psdSqrt A * (E * R * E) * psdSqrt A := by simp [Matrix.mul_assoc]
  calc
    traceNorm (psdSqrt A * psdSqrt R) =
        traceNorm (psdSqrt R * psdSqrt A) := by
      rw [← traceNorm_conjTranspose]
      rw [Matrix.conjTranspose_mul, (psdSqrt_isHermitian R).eq,
        (psdSqrt_isHermitian A).eq]
    _ = (psdSqrt (psdSqrt A * R * psdSqrt A)).trace.re :=
      supportRestriction_traceNorm_psdSqrt_mul_psdSqrt_eq_trace_psdSqrt_sandwich
        R A hR
    _ = (psdSqrt (psdSqrt A * (E * R * E) * psdSqrt A)).trace.re := by rw [hsand]
    _ = traceNorm (psdSqrt (E * R * E) * psdSqrt A) :=
      (supportRestriction_traceNorm_psdSqrt_mul_psdSqrt_eq_trace_psdSqrt_sandwich
        (E * R * E) A hER).symm
    _ = traceNorm (psdSqrt A * psdSqrt (E * R * E)) := by
      rw [← traceNorm_conjTranspose]
      rw [Matrix.conjTranspose_mul, (psdSqrt_isHermitian A).eq,
        (psdSqrt_isHermitian (E * R * E)).eq]

private theorem supportRestriction_projector_complement_posSemidef
    (P : CMatrix a) (hP : P.PosSemidef) (hPid : P * P = P) :
    ((1 : CMatrix a) - P).PosSemidef := by
  have h1P_herm : ((1 : CMatrix a) - P).IsHermitian :=
    (Matrix.isHermitian_one).sub hP.isHermitian
  have h1P_conj : Matrix.conjTranspose ((1 : CMatrix a) - P) = 1 - P :=
    h1P_herm.eq
  have h1P_sq : ((1 : CMatrix a) - P) * (1 - P) = 1 - P := by
    have e : ((1 : CMatrix a) - P) * (1 - P) = 1 - P - P + P * P := by
      noncomm_ring
    rw [e, hPid]
    abel
  have hkey : (1 : CMatrix a) - P =
      Matrix.conjTranspose ((1 : CMatrix a) - P) * (1 - P) := by
    rw [h1P_conj, h1P_sq]
  rw [hkey]
  exact Matrix.posSemidef_conjTranspose_mul_self (1 - P)

private def sideSupportFilter (ρ : SubnormalizedState (Prod a b)) :
    MatrixMap b b :=
  MatrixMap.ofKraus (fun _ : Unit =>
    supportProjector ρ.marginalB.matrix ρ.marginalB.pos)

private theorem sideSupportFilter_traceNonincreasingCP
    (ρ : SubnormalizedState (Prod a b)) :
    MatrixMap.TraceNonincreasingCP (sideSupportFilter ρ) := by
  let Q : CMatrix b := supportProjector ρ.marginalB.matrix ρ.marginalB.pos
  have hQpos : Q.PosSemidef := psdInvSqrt_support_posSemidef ρ.marginalB.pos
  have hQle : Q ≤ (1 : CMatrix b) := psdInvSqrt_support_le_one ρ.marginalB.pos
  have hQid : Q * Q = Q := psdInvSqrt_support_idempotent ρ.marginalB.pos
  have hQherm : Q.IsHermitian := psdInvSqrt_support_isHermitian ρ.marginalB.pos
  refine ⟨MatrixMap.ofKraus_isCompletelyPositive _, ?_⟩
  intro X hX
  have hineq : (Q * X * Matrix.conjTranspose Q).trace.re ≤ X.trace.re := by
    have hdiff : ((1 : CMatrix b) - Q).PosSemidef := Matrix.le_iff.mp hQle
    have hnonneg := cMatrix_trace_mul_posSemidef_re_nonneg hX hdiff
    have hout : (Q * X * Matrix.conjTranspose Q).trace.re = (X * Q).trace.re := by
      rw [hQherm.eq, Matrix.trace_mul_cycle, hQid]
      exact congrArg Complex.re (Matrix.trace_mul_comm _ _)
    rw [hout]
    have htrace : (X * ((1 : CMatrix b) - Q)).trace.re =
        X.trace.re - (X * Q).trace.re := by
      rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, Matrix.mul_one]
    linarith
  simpa [sideSupportFilter, MatrixMap.ofKraus, Q] using hineq

private def sideSupportState
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) :
    SubnormalizedState b :=
  σ.applyTraceNonincreasingCP (sideSupportFilter ρ)
    (sideSupportFilter_traceNonincreasingCP ρ)

@[simp]
private theorem sideSupportState_matrix
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) :
    (sideSupportState ρ σ).matrix =
      supportProjector ρ.marginalB.matrix ρ.marginalB.pos * σ.matrix *
        Matrix.conjTranspose (supportProjector ρ.marginalB.matrix ρ.marginalB.pos) := by
  change sideSupportFilter ρ σ.matrix = _
  simp [sideSupportFilter, MatrixMap.ofKraus]

private theorem supportFilter_conditionalMaxEntropyExponentCandidate_le
    (ρ τ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) :
    (supportFilterState ρ τ).conditionalMaxEntropyExponentCandidate σ ≤
      τ.conditionalMaxEntropyExponentCandidate (sideSupportState ρ σ) := by
  let PA : CMatrix a := supportProjector ρ.marginalA.matrix ρ.marginalA.pos
  let PB : CMatrix b := supportProjector ρ.marginalB.matrix ρ.marginalB.pos
  let P : CMatrix (Prod a b) := bipartiteSupportProjector ρ
  let Q : CMatrix b := PB
  let R : CMatrix (Prod a b) :=
    identityTensorStateMatrix (a := a) (sideSupportState ρ σ)
  have hPA : PA.PosSemidef := psdInvSqrt_support_posSemidef ρ.marginalA.pos
  have hPB : PB.PosSemidef := psdInvSqrt_support_posSemidef ρ.marginalB.pos
  have hP : P.PosSemidef := hPA.kronecker hPB
  have hPherm : P.IsHermitian := hP.isHermitian
  have hPid : P * P = P := by
    have hPAid : PA * PA = PA := psdInvSqrt_support_idempotent ρ.marginalA.pos
    have hPBid : PB * PB = PB := psdInvSqrt_support_idempotent ρ.marginalB.pos
    change Matrix.kronecker PA PB * Matrix.kronecker PA PB = Matrix.kronecker PA PB
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul, hPAid, hPBid]
  have hPle : Matrix.conjTranspose P * P ≤ (1 : CMatrix (Prod a b)) := by
    have hPone : P ≤ (1 : CMatrix (Prod a b)) :=
      Matrix.le_iff.mpr (supportRestriction_projector_complement_posSemidef P hP hPid)
    rw [hPherm.eq, hPid]
    exact hPone
  have hPBherm : PB.IsHermitian := psdInvSqrt_support_isHermitian ρ.marginalB.pos
  have hPBid : PB * PB = PB := psdInvSqrt_support_idempotent ρ.marginalB.pos
  have hσp : (sideSupportState ρ σ).matrix = PB * σ.matrix * PB := by
    rw [sideSupportState_matrix, hPBherm.eq]
  obtain ⟨Uσ, hUσ⟩ := supportRestriction_psdSqrt_projector_factor
    PB σ.matrix (by exact σ.pos) hPBherm
  have hσsqrt_left : PB * psdSqrt (sideSupportState ρ σ).matrix =
      psdSqrt (sideSupportState ρ σ).matrix := by
    rw [hσp, hUσ]
    calc
      PB * (PB * psdSqrt σ.matrix * (Uσ : CMatrix b)) =
          (PB * PB) * psdSqrt σ.matrix * (Uσ : CMatrix b) := by
            simp [Matrix.mul_assoc]
      _ = PB * psdSqrt σ.matrix * (Uσ : CMatrix b) := by rw [hPBid]
  have hσsqrt_right : psdSqrt (sideSupportState ρ σ).matrix * PB =
      psdSqrt (sideSupportState ρ σ).matrix := by
    have h := congrArg Matrix.conjTranspose hσsqrt_left
    have hs := (psdSqrt_isHermitian (sideSupportState ρ σ).matrix).eq
    rw [Matrix.conjTranspose_mul, hs, hPBherm.eq] at h
    exact h
  have hR : R.PosSemidef := by
    exact identityTensorStateMatrix_posSemidef (a := a) (sideSupportState ρ σ)
  have hsqrtR : psdSqrt R =
      Matrix.kronecker (1 : CMatrix a)
        (psdSqrt (sideSupportState ρ σ).matrix) := by
    change psdSqrt (Matrix.kronecker (1 : CMatrix a)
        (sideSupportState ρ σ).matrix) = _
    rw [psdSqrt_kronecker Matrix.PosSemidef.one
      (sideSupportState ρ σ).pos]
    have hone : psdSqrt (1 : CMatrix a) = (1 : CMatrix a) := by
      simpa using (psdSqrt_real_smul_one (a := a) (r := 1) (by norm_num))
    rw [hone]
  have hcomm : P * psdSqrt R = psdSqrt R * P := by
    dsimp [P]
    calc
      Matrix.kronecker PA PB * psdSqrt R =
          Matrix.kronecker PA PB *
            Matrix.kronecker (1 : CMatrix a)
              (psdSqrt (sideSupportState ρ σ).matrix) := by rw [hsqrtR]
      _ = Matrix.kronecker (PA * (1 : CMatrix a))
          (PB * psdSqrt (sideSupportState ρ σ).matrix) := by
            simp only [Matrix.kronecker]
            rw [← Matrix.mul_kronecker_mul]
      _ = Matrix.kronecker PA (psdSqrt (sideSupportState ρ σ).matrix) := by
            rw [Matrix.mul_one, hσsqrt_left]
      _ = Matrix.kronecker ((1 : CMatrix a) * PA)
          (psdSqrt (sideSupportState ρ σ).matrix * PB) := by
            rw [one_mul, hσsqrt_right]
      _ = Matrix.kronecker (1 : CMatrix a)
          (psdSqrt (sideSupportState ρ σ).matrix) *
            Matrix.kronecker PA PB := by
            simp only [Matrix.kronecker]
            rw [← Matrix.mul_kronecker_mul]
      _ = psdSqrt R * P := by
        change Matrix.kronecker (1 : CMatrix a)
            (psdSqrt (sideSupportState ρ σ).matrix) *
              Matrix.kronecker PA PB =
          psdSqrt R * Matrix.kronecker PA PB
        rw [hsqrtR]
  let A0 : SubnormalizedState (Prod a b) := supportFilterState ρ τ
  let E : CMatrix (Prod a b) := Matrix.kronecker (1 : CMatrix a) PB
  let R0 : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  have hER : E * R0 * E = R := by
    dsimp [E, R0, R, identityTensorStateMatrix]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    rw [hσp]
    simp only [ mul_one]
  have hEP : E * P = P := by
    change Matrix.kronecker (1 : CMatrix a) PB * Matrix.kronecker PA PB =
      Matrix.kronecker PA PB
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul]
    rw [one_mul, hPBid]
  have hPE : P * E = P := by
    change Matrix.kronecker PA PB * Matrix.kronecker (1 : CMatrix a) PB =
      Matrix.kronecker PA PB
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul]
    rw [Matrix.mul_one, hPBid]
  have hAstate : A0.matrix = P * τ.matrix * P := by
    dsimp [A0]
    rw [supportFilterState_matrix, hPherm.eq]
  obtain ⟨UA, hUA⟩ := supportRestriction_psdSqrt_projector_factor
    P A0.matrix A0.pos hPherm
  have hAfix : P * A0.matrix * P = A0.matrix := by
    rw [hAstate]
    calc
      P * (P * τ.matrix * P) * P = (P * P) * τ.matrix * (P * P) := by
        simp [Matrix.mul_assoc]
      _ = P * τ.matrix * P := by rw [hPid]
  have hAleftP : P * psdSqrt A0.matrix = psdSqrt A0.matrix := by
    have hUA' := hUA
    rw [hAfix] at hUA'
    calc
      P * psdSqrt A0.matrix =
          P * (P * psdSqrt A0.matrix * (UA : CMatrix (Prod a b))) := by
            exact congrArg (fun X : CMatrix (Prod a b) => P * X) hUA'
      _ = P * psdSqrt A0.matrix * (UA : CMatrix (Prod a b)) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc P P, hPid]
      _ = psdSqrt A0.matrix := hUA'.symm
  have hArightP : psdSqrt A0.matrix * P = psdSqrt A0.matrix := by
    have h := congrArg Matrix.conjTranspose hAleftP
    rw [Matrix.conjTranspose_mul, (psdSqrt_isHermitian A0.matrix).eq,
      hPherm.eq] at h
    exact h
  have hAleftE : E * psdSqrt A0.matrix = psdSqrt A0.matrix := by
    calc
      E * psdSqrt A0.matrix = E * (P * psdSqrt A0.matrix) := by rw [hAleftP]
      _ = (E * P) * psdSqrt A0.matrix := by simp [Matrix.mul_assoc]
      _ = psdSqrt A0.matrix := by rw [hEP, hAleftP]
  have hEherm : E.IsHermitian :=
    (Matrix.PosSemidef.one.kronecker hPB).isHermitian
  have hArightE : psdSqrt A0.matrix * E = psdSqrt A0.matrix := by
    have h := congrArg Matrix.conjTranspose hAleftE
    rw [Matrix.conjTranspose_mul, (psdSqrt_isHermitian A0.matrix).eq] at h
    rw [hEherm.eq] at h
    exact h
  have hside :
      traceNorm (psdSqrt A0.matrix * psdSqrt R0) =
        traceNorm (psdSqrt A0.matrix * psdSqrt R) := by
    calc
      traceNorm (psdSqrt A0.matrix * psdSqrt R0) =
          traceNorm (psdSqrt A0.matrix * psdSqrt (E * R0 * E)) :=
        supportRestriction_candidate_side_compression_eq
          A0.matrix R0 E
          (identityTensorStateMatrix_posSemidef (a := a) σ)
          (by rw [hER]; exact hR) hArightE hAleftE
      _ = traceNorm (psdSqrt A0.matrix * psdSqrt R) := by rw [hER]
  have htrace :
      traceNorm (psdSqrt (supportFilterState ρ τ).matrix * psdSqrt R) ≤
        traceNorm (psdSqrt τ.matrix * psdSqrt R) := by
    have hstate : (supportFilterState ρ τ).matrix = P * τ.matrix * P := hAstate
    rw [hstate]
    exact supportRestriction_candidate_compression_le τ.matrix P R τ.pos hPherm hPle hcomm
  have htrace0 :
      traceNorm (psdSqrt (supportFilterState ρ τ).matrix * psdSqrt R0) ≤
        traceNorm (psdSqrt τ.matrix * psdSqrt R) := by
    calc
      traceNorm (psdSqrt (supportFilterState ρ τ).matrix * psdSqrt R0) =
          traceNorm (psdSqrt A0.matrix * psdSqrt R0) := by rfl
      _ = traceNorm (psdSqrt A0.matrix * psdSqrt R) := hside
      _ ≤ traceNorm (psdSqrt τ.matrix * psdSqrt R) := htrace
  unfold conditionalMaxEntropyExponentCandidate
  simpa [R] using
    (sq_le_sq₀ (traceNorm_nonneg _) (traceNorm_nonneg _)).2 htrace0

theorem conditionalMinEntropyScaleFeasible_supportFilter
    {τ : SubnormalizedState (Prod a b)} {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) τ T)
    (ρ : SubnormalizedState (Prod a b)) :
    ConditionalMinEntropyScaleFeasible (a := a) (supportFilterState ρ τ)
      (supportProjector ρ.marginalB.matrix ρ.marginalB.pos * T *
        supportProjector ρ.marginalB.matrix ρ.marginalB.pos) := by
  let PA : CMatrix a := supportProjector ρ.marginalA.matrix ρ.marginalA.pos
  let PB : CMatrix b := supportProjector ρ.marginalB.matrix ρ.marginalB.pos
  let P : CMatrix (Prod a b) := bipartiteSupportProjector ρ
  let T' : CMatrix b := PB * T * PB
  have hPA : PA.PosSemidef := psdInvSqrt_support_posSemidef ρ.marginalA.pos
  have hPB : PB.PosSemidef := psdInvSqrt_support_posSemidef ρ.marginalB.pos
  have hPAle : PA ≤ (1 : CMatrix a) := psdInvSqrt_support_le_one ρ.marginalA.pos
  have hQ : T'.PosSemidef := by
    change (PB * T * PB).PosSemidef
    have h := hT.1.conjTranspose_mul_mul_same PB
    rw [hPB.isHermitian.eq] at h
    exact h
  constructor
  · exact hQ
  · have hsand := hT.2.conjTranspose_mul_mul_same P
    have hPherm : P.IsHermitian := (hPA.kronecker hPB).isHermitian
    rw [hPherm.eq] at hsand
    have hPAid : PA * PA = PA := psdInvSqrt_support_idempotent ρ.marginalA.pos
    have hPBid : PB * PB = PB := psdInvSqrt_support_idempotent ρ.marginalB.pos
    have hPITP :
        P * Matrix.kronecker (1 : CMatrix a) T * P =
          Matrix.kronecker PA T' := by
      rw [show P = Matrix.kronecker PA PB by rfl]
      simp only [Matrix.kronecker]
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
      simp [T', hPAid]
    have hdiff :
        (Matrix.kronecker (1 : CMatrix a) T' -
          (supportFilterState ρ τ).matrix).PosSemidef := by
      have hstate :
          (supportFilterState ρ τ).matrix =
            P * τ.matrix * Matrix.conjTranspose P := by
        rw [supportFilterState_matrix]
      rw [hstate]
      rw [hPherm.eq]
      rw [show P = Matrix.kronecker PA PB by rfl] at hsand
      have hdecomp :
          Matrix.kronecker (1 : CMatrix a) T' -
              P * τ.matrix * P =
            (P * (Matrix.kronecker (1 : CMatrix a) T - τ.matrix) *
                P) +
              Matrix.kronecker ((1 : CMatrix a) - PA) T' := by
        have hsplit : Matrix.kronecker (1 : CMatrix a) T' =
            Matrix.kronecker PA T' +
              Matrix.kronecker ((1 : CMatrix a) - PA) T' := by
          ext x y
          simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
          ring
        calc
          Matrix.kronecker (1 : CMatrix a) T' - P * τ.matrix * P =
              (Matrix.kronecker PA T' +
                Matrix.kronecker ((1 : CMatrix a) - PA) T') -
                  P * τ.matrix * P := by rw [← hsplit]
          _ = (P * Matrix.kronecker (1 : CMatrix a) T * P -
                P * τ.matrix * P) +
                  Matrix.kronecker ((1 : CMatrix a) - PA) T' := by
                rw [hPITP]
                abel
          _ = P * (Matrix.kronecker (1 : CMatrix a) T - τ.matrix) * P +
                Matrix.kronecker ((1 : CMatrix a) - PA) T' := by
                rw [mul_sub, sub_mul]
      rw [hdecomp]
      have hrest :
          (Matrix.kronecker ((1 : CMatrix a) - PA) T').PosSemidef :=
        (Matrix.le_iff.mp hPAle).kronecker hQ
      have hadd :
          (P * (Matrix.kronecker (1 : CMatrix a) T - τ.matrix) * P +
            Matrix.kronecker ((1 : CMatrix a) - PA) T').PosSemidef :=
        Matrix.PosSemidef.add hsand hrest
      exact hadd
    exact (Matrix.le_iff).mpr hdiff

theorem conditionalMinEntropyScale_supportFilter_le
    (ρ τ : SubnormalizedState (Prod a b)) :
    (supportFilterState ρ τ).conditionalMinEntropyScale (a := a) ≤
      τ.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf (τ.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
  intro t ht
  rcases ht with ⟨T, hT, rfl⟩
  have hbdd :=
      (supportFilterState ρ τ).conditionalMinEntropyScaleValueSet_bddBelow
        (a := a)
  exact le_trans
    (csInf_le hbdd ⟨_, conditionalMinEntropyScaleFeasible_supportFilter hT ρ, rfl⟩)
    (supportFilter_side_trace_le hT.1 ρ)

theorem conditionalMinEntropyRaw_le_supportFilter_of_trace_pos
    [Nonempty a] [Nonempty b]
    (ρ τ : SubnormalizedState (Prod a b)) (hτ : 0 < τ.matrix.trace.re)
    (hfilter : 0 < (supportFilterState ρ τ).matrix.trace.re) :
    τ.conditionalMinEntropyRaw ≤
      (supportFilterState ρ τ).conditionalMinEntropyRaw := by
  rw [τ.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos (a := a) hτ,
    (supportFilterState ρ τ).conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := a) hfilter]
  have hscale := conditionalMinEntropyScale_supportFilter_le ρ τ
  have hpos := (supportFilterState ρ τ).conditionalMinEntropyScale_pos_of_trace_pos
    (a := a) hfilter
  have hlog : log2 ((supportFilterState ρ τ).conditionalMinEntropyScale (a := a)) ≤
      log2 (τ.conditionalMinEntropyScale (a := a)) := by
    unfold log2
    exact div_le_div_of_nonneg_right (Real.log_le_log hpos hscale)
      (le_of_lt (Real.log_pos one_lt_two))
  exact neg_le_neg hlog

theorem smoothConditionalMinEntropy_exists_support_optimizer
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε : ℝ}
    (hε_nonneg : 0 ≤ ε) (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    ∃ ρmin : SubnormalizedState (Prod a b),
      ∃ hρmin : ρmin.matrix ≠ 0,
      ρ.purifiedBall ε ρmin ∧
        ρ.smoothConditionalMinEntropy ε hε_nonneg hε =
          ρmin.conditionalMinEntropyFinite hρmin ∧
        (∀ ρ' : SubnormalizedState (Prod a b),
          ∀ hρ' : ρ'.matrix ≠ 0, ρ.purifiedBall ε ρ' →
            ρ'.conditionalMinEntropyFinite hρ' ≤
              ρmin.conditionalMinEntropyFinite hρmin) ∧
        Matrix.Supports ρmin.matrix (bipartiteSupportProjector ρ) := by
  rcases ρ.smoothConditionalMinEntropy_exists_scale_optimizer
      (a := a) hε_nonneg hε with
    ⟨ρmin, _Tmin, hρmin, hball, _hfeas, _hscale, hsmooth, hopt⟩
  let ρproj := supportFilterState ρ ρmin
  have hballproj : ρ.purifiedBall ε ρproj := by
    exact supportFilterState_purifiedBall (supportFilterState_center ρ) hball
  have htrmin : 0 < ρmin.matrix.trace.re :=
    ρ.purifiedBall_trace_pos_of_lt_sqrt_trace ρmin hε hball
  have htrproj : 0 < ρproj.matrix.trace.re :=
    ρ.purifiedBall_trace_pos_of_lt_sqrt_trace ρproj hε hballproj
  have hρproj : ρproj.matrix ≠ 0 := by
    intro hzero
    rw [hzero] at htrproj
    simp at htrproj
  have hge : ρmin.conditionalMinEntropyRaw ≤ ρproj.conditionalMinEntropyRaw := by
    exact conditionalMinEntropyRaw_le_supportFilter_of_trace_pos
      ρ ρmin htrmin htrproj
  have hle : ρproj.conditionalMinEntropyRaw ≤ ρmin.conditionalMinEntropyRaw :=
    hopt ρproj hρproj hballproj
  have heq : ρproj.conditionalMinEntropyRaw = ρmin.conditionalMinEntropyRaw :=
    le_antisymm hle hge
  refine ⟨ρproj, hρproj, hballproj, hsmooth.trans heq.symm, ?_, ?_⟩
  · intro ρ' hρ' hρ'ball
    calc
      ρ'.conditionalMinEntropyFinite hρ' ≤
          ρmin.conditionalMinEntropyFinite hρmin := hopt ρ' hρ' hρ'ball
      _ = ρproj.conditionalMinEntropyFinite hρproj := heq.symm
  · exact supportFilterState_supports_projector ρ ρmin

theorem supportFilter_conditionalMaxEntropyRaw_le
    [Nonempty a] [Nonempty b]
    (ρ τ : SubnormalizedState (Prod a b))
    (hτ : 0 < τ.matrix.trace.re)
    (hfilter : 0 < (supportFilterState ρ τ).matrix.trace.re) :
    (supportFilterState ρ τ).conditionalMaxEntropyRaw ≤
      τ.conditionalMaxEntropyRaw := by
  let τproj : SubnormalizedState (Prod a b) := supportFilterState ρ τ
  have hne_τ :
      (τ.conditionalMaxEntropyPositiveExponentValueSet (a := a)).Nonempty :=
    τ.conditionalMaxEntropyPositiveExponentValueSet_nonempty_of_trace_pos
      (a := a) hτ
  have hne_proj :
      (τproj.conditionalMaxEntropyPositiveExponentValueSet (a := a)).Nonempty :=
    τproj.conditionalMaxEntropyPositiveExponentValueSet_nonempty_of_trace_pos
      (a := a) hfilter
  have hbdd_τ :
      BddAbove (τ.conditionalMaxEntropyPositiveExponentValueSet (a := a)) :=
    τ.conditionalMaxEntropyPositiveExponentValueSet_bddAbove_of_trace_pos
      (a := a) hτ
  have hbdd_proj :
      BddAbove (τproj.conditionalMaxEntropyPositiveExponentValueSet (a := a)) :=
    τproj.conditionalMaxEntropyPositiveExponentValueSet_bddAbove_of_trace_pos
      (a := a) hfilter
  have hexp :
      τproj.conditionalMaxEntropyPositiveExponent (a := a) ≤
        τ.conditionalMaxEntropyPositiveExponent (a := a) := by
    rw [conditionalMaxEntropyPositiveExponent_eq,
      conditionalMaxEntropyPositiveExponent_eq]
    refine csSup_le hne_proj ?_
    intro x hx
    rcases hx with ⟨σ, hσpos, rfl⟩
    have hcand := supportFilter_conditionalMaxEntropyExponentCandidate_le
      (a := a) (b := b) ρ τ σ
    have hσproj_mem :
        τ.conditionalMaxEntropyExponentCandidate (a := a)
            (sideSupportState ρ σ) ∈
          τ.conditionalMaxEntropyPositiveExponentValueSet (a := a) := by
      refine ⟨sideSupportState ρ σ, lt_of_lt_of_le hσpos hcand, rfl⟩
    exact le_trans hcand (le_csSup hbdd_τ hσproj_mem)
  have hproj_exp_pos :
      0 < τproj.conditionalMaxEntropyPositiveExponent (a := a) := by
    rcases hne_proj with ⟨x, hx⟩
    have hxpos : 0 < x := by
      rcases hx with ⟨σ, hσpos, rfl⟩
      exact hσpos
    exact lt_of_lt_of_le hxpos (by
      rw [conditionalMaxEntropyPositiveExponent_eq]
      exact le_csSup hbdd_proj hx)
  rw [conditionalMaxEntropy_eq_positive,
    conditionalMaxEntropy_eq_positive,
    conditionalMaxEntropyPositive_eq_log2_positiveExponent
      (a := a) τproj hne_proj hbdd_proj,
    conditionalMaxEntropyPositive_eq_log2_positiveExponent
      (a := a) τ hne_τ hbdd_τ]
  unfold log2
  exact div_le_div_of_nonneg_right
    (Real.log_le_log hproj_exp_pos hexp)
    (le_of_lt (Real.log_pos one_lt_two))

theorem smoothConditionalMaxEntropy_exists_support_optimizer
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε : ℝ}
    (hε_nonneg : 0 ≤ ε) (hε : ε < Real.sqrt ρ.matrix.trace.re)
    :
    ∃ ρmax : SubnormalizedState (Prod a b),
      ∃ hρmax : ρmax.matrix ≠ 0,
      ρ.purifiedBall ε ρmax ∧
        ρ.smoothConditionalMaxEntropy ε hε_nonneg hε =
          ρmax.conditionalMaxEntropyFinite hρmax ∧
        (∀ ρ' : SubnormalizedState (Prod a b),
          ∀ hρ' : ρ'.matrix ≠ 0, ρ.purifiedBall ε ρ' →
            ρmax.conditionalMaxEntropyFinite hρmax ≤
              ρ'.conditionalMaxEntropyFinite hρ') ∧
        Matrix.Supports ρmax.matrix (bipartiteSupportProjector ρ) := by
  rcases ρ.smoothConditionalMaxEntropy_exists_optimizer
      (a := a) (b := b) hε_nonneg hε with
    ⟨ρmax, hρmax, hball, hsmooth, hopt⟩
  let ρproj := supportFilterState ρ ρmax
  have hballproj : ρ.purifiedBall ε ρproj := by
    exact supportFilterState_purifiedBall (supportFilterState_center ρ) hball
  have htrmax : 0 < ρmax.matrix.trace.re :=
    ρ.purifiedBall_trace_pos_of_lt_sqrt_trace ρmax hε hball
  have htrproj : 0 < ρproj.matrix.trace.re :=
    ρ.purifiedBall_trace_pos_of_lt_sqrt_trace ρproj hε hballproj
  have hρproj : ρproj.matrix ≠ 0 := by
    intro hzero
    rw [hzero] at htrproj
    simp at htrproj
  have hle : ρproj.conditionalMaxEntropyRaw ≤ ρmax.conditionalMaxEntropyRaw := by
    exact supportFilter_conditionalMaxEntropyRaw_le ρ ρmax htrmax htrproj
  have hge : ρmax.conditionalMaxEntropyRaw ≤ ρproj.conditionalMaxEntropyRaw :=
    hopt ρproj hρproj hballproj
  have heq : ρproj.conditionalMaxEntropyRaw = ρmax.conditionalMaxEntropyRaw :=
    le_antisymm hle hge
  refine ⟨ρproj, hρproj, hballproj, hsmooth.trans heq.symm, ?_, ?_⟩
  · intro ρ' hρ' hρ'ball
    change ρproj.conditionalMaxEntropyRaw ≤ ρ'.conditionalMaxEntropyRaw
    rw [heq]
    exact hopt ρ' hρ' hρ'ball
  · exact supportFilterState_supports_projector ρ ρmax

theorem smoothConditionalMinMaxEntropy_exists_support_optimizers
    [Nonempty a] [Nonempty b]
    (ρ : SubnormalizedState (Prod a b)) {ε : ℝ}
    (hε_nonneg : 0 ≤ ε) (hε : ε < Real.sqrt ρ.matrix.trace.re)
    :
    ∃ ρmin ρmax : SubnormalizedState (Prod a b),
      ∃ (hρmin : ρmin.matrix ≠ 0) (hρmax : ρmax.matrix ≠ 0),
      ρ.purifiedBall ε ρmin ∧ ρ.purifiedBall ε ρmax ∧
        ρ.smoothConditionalMinEntropy ε hε_nonneg hε =
          ρmin.conditionalMinEntropyFinite hρmin ∧
        ρ.smoothConditionalMaxEntropy ε hε_nonneg hε =
          ρmax.conditionalMaxEntropyFinite hρmax ∧
        Matrix.Supports ρmin.matrix (bipartiteSupportProjector ρ) ∧
        Matrix.Supports ρmax.matrix (bipartiteSupportProjector ρ) := by
  rcases smoothConditionalMinEntropy_exists_support_optimizer
      (a := a) (b := b) ρ hε_nonneg hε with
    ⟨ρmin, hρmin, hminball, hmineq, hminopt, hminsupport⟩
  rcases smoothConditionalMaxEntropy_exists_support_optimizer
      (a := a) (b := b) ρ hε_nonneg hε with
    ⟨ρmax, hρmax, hmaxball, hmaxeq, hmaxopt, hmaxsupport⟩
  exact ⟨ρmin, ρmax, hρmin, hρmax, hminball, hmaxball, hmineq, hmaxeq,
    hminsupport, hmaxsupport⟩

end SubnormalizedState

end

end QIT
