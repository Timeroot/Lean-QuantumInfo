/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Geometry.Fidelity
public import QIT.Core.Channel
public import QIT.States.Purification.Canonical
public import QIT.States.Purification.Equivalence
public import QIT.States.Purification.ReferenceUnitary
public import QIT.States.TraceNorm.Variational
public import Mathlib.Data.Fintype.EquivFin

/-!
# Uhlmann theorem for canonical purifications

This module proves the canonical-purification Uhlmann route registered from
[Wilde2011Qst, qit-notes.tex:15060-15093] and the overlap-to-trace calculation
from [Wilde2011Qst, qit-notes.tex:15114-15127].  It uses the local
`State.squaredFidelity` convention and the trace-norm variational bridge from
`QIT.States.TraceNorm.Variational`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u
universe v
universe w

noncomputable section

namespace ReferenceIsometry

variable {r₁ : Type u} {r₂ : Type v} {a : Type*}
variable [Fintype r₁] [DecidableEq r₁]
variable [Fintype r₂] [DecidableEq r₂]
variable [Fintype a] [DecidableEq a]

/-- A reference-side isometry preserves pure-vector overlaps. -/
theorem overlap_applyPureVector (V : ReferenceIsometry r₁ r₂)
    (Ψ Φ : PureVector (Prod r₁ a)) :
    (V.applyPureVector Ψ).overlap (V.applyPureVector Φ) = Ψ.overlap Φ := by
  classical
  have hsum :
      (∑ k : r₂, ∑ z : a, ∑ i : r₁, ∑ j : r₁,
        V.matrix k j *
          (Φ.amp (j, z) * (star (V.matrix k i) * star (Ψ.amp (i, z))))) =
        ∑ i : r₁, ∑ z : a, Φ.amp (i, z) * star (Ψ.amp (i, z)) := by
    let F : r₂ → a → ℂ := fun k z =>
      ∑ i : r₁, ∑ j : r₁,
        V.matrix k j *
          (Φ.amp (j, z) * (star (V.matrix k i) * star (Ψ.amp (i, z))))
    change (∑ k : r₂, ∑ z : a, F k z) =
      ∑ i : r₁, ∑ z : a, Φ.amp (i, z) * star (Ψ.amp (i, z))
    rw [show (∑ k : r₂, ∑ z : a, F k z) = ∑ z : a, ∑ k : r₂, F k z by
      simpa using (Finset.sum_comm :
        (∑ k : r₂, ∑ z : a, F k z) = ∑ z : a, ∑ k : r₂, F k z)]
    rw [show (∑ i : r₁, ∑ z : a, Φ.amp (i, z) * star (Ψ.amp (i, z))) =
        ∑ z : a, ∑ i : r₁, Φ.amp (i, z) * star (Ψ.amp (i, z)) by
      simpa using (Finset.sum_comm :
        (∑ i : r₁, ∑ z : a, Φ.amp (i, z) * star (Ψ.amp (i, z))) =
          ∑ z : a, ∑ i : r₁, Φ.amp (i, z) * star (Ψ.amp (i, z)))]
    refine Finset.sum_congr rfl ?_
    intro z _
    let G : r₂ → r₁ → ℂ := fun k i =>
      ∑ j : r₁,
        V.matrix k j *
          (Φ.amp (j, z) * (star (V.matrix k i) * star (Ψ.amp (i, z))))
    change (∑ k : r₂, ∑ i : r₁, G k i) =
      ∑ i : r₁, Φ.amp (i, z) * star (Ψ.amp (i, z))
    rw [show (∑ k : r₂, ∑ i : r₁, G k i) = ∑ i : r₁, ∑ k : r₂, G k i by
      simpa using (Finset.sum_comm :
        (∑ k : r₂, ∑ i : r₁, G k i) = ∑ i : r₁, ∑ k : r₂, G k i)]
    refine Finset.sum_congr rfl ?_
    intro i _
    let H : r₂ → r₁ → ℂ := fun k j =>
      V.matrix k j *
        (Φ.amp (j, z) * (star (V.matrix k i) * star (Ψ.amp (i, z))))
    change (∑ k : r₂, ∑ j : r₁, H k j) =
      Φ.amp (i, z) * star (Ψ.amp (i, z))
    rw [show (∑ k : r₂, ∑ j : r₁, H k j) = ∑ j : r₁, ∑ k : r₂, H k j by
      simpa using (Finset.sum_comm :
        (∑ k : r₂, ∑ j : r₁, H k j) = ∑ j : r₁, ∑ k : r₂, H k j)]
    rw [Finset.sum_eq_single i]
    · have hfactor :
          (∑ k : r₂,
            V.matrix k i *
              (Φ.amp (i, z) * (star (V.matrix k i) * star (Ψ.amp (i, z))))) =
            (∑ k : r₂, V.matrix k i * star (V.matrix k i)) *
              (Φ.amp (i, z) * star (Ψ.amp (i, z))) := by
        calc
          (∑ k : r₂,
            V.matrix k i *
              (Φ.amp (i, z) * (star (V.matrix k i) * star (Ψ.amp (i, z))))) =
              ∑ k : r₂,
                (V.matrix k i * star (V.matrix k i)) *
                  (Φ.amp (i, z) * star (Ψ.amp (i, z))) := by
                refine Finset.sum_congr rfl ?_
                intro k _
                ring
          _ = (∑ k : r₂, V.matrix k i * star (V.matrix k i)) *
              (Φ.amp (i, z) * star (Ψ.amp (i, z))) := by
                rw [Finset.sum_mul]
      change
        (∑ k : r₂,
          V.matrix k i *
            (Φ.amp (i, z) * (star (V.matrix k i) * star (Ψ.amp (i, z))))) =
          Φ.amp (i, z) * star (Ψ.amp (i, z))
      rw [hfactor, V.sum_mul_star i i]
      simp
    · intro j _ hj
      have hfactor :
          (∑ k : r₂,
            V.matrix k j *
              (Φ.amp (j, z) * (star (V.matrix k i) * star (Ψ.amp (i, z))))) =
            (∑ k : r₂, V.matrix k j * star (V.matrix k i)) *
              (Φ.amp (j, z) * star (Ψ.amp (i, z))) := by
        calc
          (∑ k : r₂,
            V.matrix k j *
              (Φ.amp (j, z) * (star (V.matrix k i) * star (Ψ.amp (i, z))))) =
              ∑ k : r₂,
                (V.matrix k j * star (V.matrix k i)) *
                  (Φ.amp (j, z) * star (Ψ.amp (i, z))) := by
                refine Finset.sum_congr rfl ?_
                intro k _
                ring
          _ = (∑ k : r₂, V.matrix k j * star (V.matrix k i)) *
              (Φ.amp (j, z) * star (Ψ.amp (i, z))) := by
                rw [Finset.sum_mul]
      change
        (∑ k : r₂,
          V.matrix k j *
            (Φ.amp (j, z) * (star (V.matrix k i) * star (Ψ.amp (i, z))))) = 0
      rw [hfactor, V.sum_mul_star j i]
      simp [hj]
    · intro hi
      simp at hi
  simp [PureVector.overlap, ReferenceIsometry.applyPureVector_amp,
    ReferenceIsometry.applyAmp, Matrix.mulVec, dotProduct, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_comm]
  conv_lhs =>
    rw [← Finset.univ_product_univ]
    rw [Finset.sum_product]
  conv_rhs =>
    rw [← Finset.univ_product_univ]
    rw [Finset.sum_product]
  exact hsum

/-- A reference-side isometry preserves squared pure-vector overlaps. -/
theorem overlapSq_applyPureVector (V : ReferenceIsometry r₁ r₂)
    (Ψ Φ : PureVector (Prod r₁ a)) :
    (V.applyPureVector Ψ).overlapSq (V.applyPureVector Φ) = Ψ.overlapSq Φ := by
  rw [PureVector.overlapSq_eq_normSq, PureVector.overlapSq_eq_normSq,
    V.overlap_applyPureVector Ψ Φ]

end ReferenceIsometry

namespace MatrixMap

variable {κ : Type w}
variable [Fintype κ] [DecidableEq κ]
variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Stinespring isometry associated to a trace-preserving Kraus family. -/
def krausStinespringIsometry (K : κ → Matrix b a ℂ)
    (hTP : IsTracePreserving (ofKraus K)) : ReferenceIsometry a (Prod b κ) where
  matrix := fun yx x => K yx.2 yx.1 x
  isometry := by
    have hone := krausAdjoint_one_of_tracePreserving K hTP
    ext i j
    have hentry := congrFun (congrFun hone i) j
    simp only [krausAdjoint, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply] at hentry
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simpa [mul_comm] using hentry

/-- Tracing the Stinespring environment recovers the original Kraus map. -/
theorem partialTraceB_krausStinespringIsometry
    (K : κ → Matrix b a ℂ) (hTP : IsTracePreserving (ofKraus K)) (X : CMatrix a) :
    partialTraceB (a := b) (b := κ)
      ((krausStinespringIsometry K hTP).matrix * X *
        Matrix.conjTranspose (krausStinespringIsometry K hTP).matrix) =
      ofKraus K X := by
  ext y y'
  simp [partialTraceB, ofKraus, krausStinespringIsometry, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, mul_assoc]

/-- The output marginal of the Stinespring lift is the original Kraus-map
output. -/
theorem marginalA_marginalB_applyPureVectorRight_krausStinespringIsometry
    {r : Type _} [Fintype r] [DecidableEq r]
    (K : κ → Matrix b a ℂ) (hTP : IsTracePreserving (ofKraus K))
    {Ψ : PureVector (Prod r a)} {ρ : State a} (hΨ : Ψ.Purifies ρ) :
    ((krausStinespringIsometry K hTP).applyPureVectorRight Ψ).state.marginalB.marginalA.matrix =
      ofKraus K ρ.matrix := by
  let V := krausStinespringIsometry K hTP
  change
    partialTraceB (a := b) (b := κ)
      (partialTraceA (a := r) (b := Prod b κ)
        ((V.applyPureVectorRight Ψ).state.matrix)) =
      ofKraus K ρ.matrix
  rw [V.rankOne_applyPureVectorRight]
  rw [V.partialTraceA_applyMatrixRight]
  rw [hΨ]
  exact partialTraceB_krausStinespringIsometry K hTP ρ.matrix

end MatrixMap

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- The canonical-purification overlap after a reference unitary is the trace
of `√ρ * √σ * Uᵀ`. -/
theorem canonicalPurification_overlap_applyReferenceUnitary_eq_trace
    (ρ σ : State a) (U : ReferenceUnitary a) :
    ρ.canonicalPurification.overlap (U.applyPureVector σ.canonicalPurification) =
      (ρ.sqrtMatrix * σ.sqrtMatrix * Matrix.transpose U.matrix).trace := by
  classical
  simp [PureVector.overlap, State.canonicalPurification, State.canonicalPurificationAmp,
    ReferenceUnitary.applyPureVector, ReferenceUnitary.toReferenceIsometry,
    ReferenceIsometry.applyPureVector, ReferenceIsometry.applyAmp, Matrix.trace,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose, Finset.mul_sum, mul_assoc,
    ρ.sqrtMatrix_isHermitian.apply]
  conv_lhs =>
    rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [mul_comm]

/-- Squared canonical-purification overlaps unfold to the squared trace
expression used by the trace-norm variational bridge. -/
theorem canonicalPurification_overlapSq_applyReferenceUnitary_eq_normSq_trace
    (ρ σ : State a) (U : ReferenceUnitary a) :
    ρ.canonicalPurification.overlapSq (U.applyPureVector σ.canonicalPurification) =
      Complex.normSq ((ρ.sqrtMatrix * σ.sqrtMatrix * Matrix.transpose U.matrix).trace) := by
  rw [PureVector.overlapSq_eq_normSq]
  rw [canonicalPurification_overlap_applyReferenceUnitary_eq_trace]

/-- Canonical-purification form of Uhlmann's theorem: squared fidelity is
attained by some reference unitary and bounds every reference-unitary overlap. -/
theorem exists_referenceUnitary_canonicalPurification_overlapSq_eq_squaredFidelity
    (ρ σ : State a) :
    ∃ U : ReferenceUnitary a,
      ρ.squaredFidelity σ =
        ρ.canonicalPurification.overlapSq (U.applyPureVector σ.canonicalPurification) ∧
      ∀ V : ReferenceUnitary a,
        ρ.canonicalPurification.overlapSq (V.applyPureVector σ.canonicalPurification) ≤
      ρ.squaredFidelity σ := by
  classical
  obtain ⟨U, hU⟩ :=
    traceNorm_variational_exists_referenceUnitary_sq (ρ.sqrtMatrix * σ.sqrtMatrix)
  refine ⟨U, ?_, ?_⟩
  · rw [canonicalPurification_overlapSq_applyReferenceUnitary_eq_normSq_trace, hU,
      State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq]
  · intro V
    rw [canonicalPurification_overlapSq_applyReferenceUnitary_eq_normSq_trace,
      State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq]
    exact traceNorm_variational_referenceUnitary_sq_le (ρ.sqrtMatrix * σ.sqrtMatrix) V

end State

namespace PureVector

variable {r : Type v} {a : Type u}
variable [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]

theorem overlap_eq_trace_conjTranspose_amplitudeMatrix_mul
    (Ψ Φ : PureVector (Prod r a)) :
    Ψ.overlap Φ = (Matrix.conjTranspose Ψ.amplitudeMatrix * Φ.amplitudeMatrix).trace := by
  classical
  simp [PureVector.overlap, PureVector.amplitudeMatrix, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose, mul_comm]
  conv_lhs =>
    rw [← Finset.univ_product_univ]
    rw [Finset.sum_product]

/-- Relabeling both pure vectors preserves their overlap. -/
theorem overlap_reindex {β : Type w} [Fintype β] [DecidableEq β]
    (Ψ Φ : PureVector a) (e : a ≃ β) :
    (Ψ.reindex e).overlap (Φ.reindex e) = Ψ.overlap Φ := by
  classical
  simpa [PureVector.overlap] using
    Fintype.sum_equiv e.symm
    (fun j : β => star (Ψ.amp (e.symm j)) * Φ.amp (e.symm j))
    (fun i : a => star (Ψ.amp i) * Φ.amp i)
    (by intro j; simp)

/-- Relabeling both pure vectors preserves squared overlap. -/
theorem overlapSq_reindex {β : Type w} [Fintype β] [DecidableEq β]
    (Ψ Φ : PureVector a) (e : a ≃ β) :
    (Ψ.reindex e).overlapSq (Φ.reindex e) = Ψ.overlapSq Φ := by
  rw [PureVector.overlapSq_eq_normSq, PureVector.overlapSq_eq_normSq,
    overlap_reindex]

/-- A bipartite pure vector purifies its target marginal. -/
theorem purifies_marginalB (Ψ : PureVector (Prod r a)) :
    Ψ.Purifies Ψ.state.marginalB := by
  rw [PureVector.purifies_iff, State.marginalB_matrix]

def marginalAReferenceEquiv (r a b : Type*) :
    Prod r (Prod a b) ≃ Prod (Prod r b) a where
  toFun x := ((x.1, x.2.2), x.2.1)
  invFun x := (x.1.1, (x.2, x.1.2))
  left_inv x := by
    cases x with
    | mk i xb =>
      cases xb
      rfl
  right_inv x := by
    cases x with
    | mk ib j =>
      cases ib
      rfl

def marginalBReferenceEquiv (r a b : Type*) :
    Prod r (Prod a b) ≃ Prod (Prod r a) b where
  toFun x := ((x.1, x.2.1), x.2.2)
  invFun x := (x.1.1, (x.1.2, x.2))
  left_inv x := by
    cases x with
    | mk i xb =>
      cases xb
      rfl
  right_inv x := by
    cases x with
    | mk ia j =>
      cases ia
      rfl

/-- Reassociating a purification of `ρAB` as `(reference × B) × A`
purifies the `A` marginal. -/
theorem reindex_marginalAReferenceEquiv_purifies_marginalA
    {b : Type w} [Fintype b] [DecidableEq b]
    {Ψ : PureVector (Prod r (Prod a b))} {ρ : State (Prod a b)}
    (hΨ : Ψ.Purifies ρ) :
    (Ψ.reindex (marginalAReferenceEquiv r a b)).Purifies ρ.marginalA := by
  rw [PureVector.purifies_iff]
  rw [State.marginalA_matrix, ← hΨ]
  ext x y
  simp [PureVector.reindex_state, State.reindex, partialTraceA,
    partialTraceB, PureVector.state_matrix, rankOneMatrix_apply, marginalAReferenceEquiv]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- Reassociating a purification of `ρAB` as `(reference × A) × B`
purifies the `B` marginal. -/
theorem reindex_marginalBReferenceEquiv_purifies_marginalB
    {b : Type w} [Fintype b] [DecidableEq b]
    {Ψ : PureVector (Prod r (Prod a b))} {ρ : State (Prod a b)}
    (hΨ : Ψ.Purifies ρ) :
    (Ψ.reindex (marginalBReferenceEquiv r a b)).Purifies ρ.marginalB := by
  rw [PureVector.purifies_iff]
  rw [State.marginalB_matrix, ← hΨ]
  ext x y
  simp [PureVector.reindex_state, State.reindex, partialTraceA,
    PureVector.state_matrix, rankOneMatrix_apply, marginalBReferenceEquiv]
  rw [Finset.sum_comm]
  rw [Fintype.sum_prod_type]

/-- A purification amplitude factors through the positive square root of the
purified state when the reference register is at least as large as the target. -/
theorem exists_referenceIsometry_amplitudeMatrix_eq_sqrtMatrix_mul_transpose
    {Ψ : PureVector (Prod r a)} {ρ : State a}
    (hΨ : Ψ.Purifies ρ) (hcard : Fintype.card a ≤ Fintype.card r) :
    ∃ V : ReferenceIsometry a r,
      Ψ.amplitudeMatrix = ρ.sqrtMatrix * Matrix.transpose V.matrix := by
  classical
  have hGram :
      ρ.sqrtMatrix * Matrix.conjTranspose ρ.sqrtMatrix =
        Ψ.amplitudeMatrix * Matrix.conjTranspose Ψ.amplitudeMatrix := by
    calc
      ρ.sqrtMatrix * Matrix.conjTranspose ρ.sqrtMatrix = ρ.sqrtMatrix * ρ.sqrtMatrix := by
        rw [ρ.sqrtMatrix_isHermitian.eq]
      _ = ρ.matrix := ρ.sqrtMatrix_mul_self
      _ = Ψ.amplitudeMatrix * Matrix.conjTranspose Ψ.amplitudeMatrix := by
        rw [← purifies_amplitudeMatrix_mul_conjTranspose_eq hΨ]
  exact ReferenceIsometry.exists_eq_mul_transpose_of_mul_conjTranspose_eq
    ρ.sqrtMatrix Ψ.amplitudeMatrix hGram hcard

private theorem referenceIsometry_transpose_mul_conjTranspose
    (V : ReferenceIsometry a r) :
    Matrix.transpose V.matrix * Matrix.conjTranspose (Matrix.transpose V.matrix) =
      (1 : CMatrix a) := by
  ext i j
  have h := V.sum_mul_star i j
  simpa [Matrix.mul_apply, Matrix.transpose, Matrix.conjTranspose, Matrix.one_apply,
    eq_comm, mul_comm] using h

private theorem referenceIsometry_transpose_cross_contraction
    (V W : ReferenceIsometry a r) :
    Matrix.conjTranspose
        (Matrix.transpose W.matrix * Matrix.conjTranspose (Matrix.transpose V.matrix)) *
        (Matrix.transpose W.matrix * Matrix.conjTranspose (Matrix.transpose V.matrix))
      ≤ (1 : CMatrix a) := by
  classical
  let TV : Matrix a r ℂ := Matrix.transpose V.matrix
  let TW : Matrix a r ℂ := Matrix.transpose W.matrix
  have hTV : TV * Matrix.conjTranspose TV = (1 : CMatrix a) := by
    simpa [TV] using referenceIsometry_transpose_mul_conjTranspose V
  have hTW : TW * Matrix.conjTranspose TW = (1 : CMatrix a) := by
    simpa [TW] using referenceIsometry_transpose_mul_conjTranspose W
  have hproj_le : Matrix.conjTranspose TW * TW ≤ (1 : CMatrix r) := by
    have hP : (Matrix.conjTranspose TW * TW).PosSemidef :=
      Matrix.posSemidef_conjTranspose_mul_self TW
    have hdiff_pos : ((1 : CMatrix r) - Matrix.conjTranspose TW * TW).PosSemidef := by
      have hidem :
          (Matrix.conjTranspose TW * TW) * (Matrix.conjTranspose TW * TW) =
            Matrix.conjTranspose TW * TW := by
        calc
          (Matrix.conjTranspose TW * TW) * (Matrix.conjTranspose TW * TW) =
              Matrix.conjTranspose TW * (TW * Matrix.conjTranspose TW) * TW := by
            simp [Matrix.mul_assoc]
          _ = Matrix.conjTranspose TW * (1 : CMatrix a) * TW := by
            rw [hTW]
          _ = Matrix.conjTranspose TW * TW := by
            simp
      exact MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent
        (Matrix.conjTranspose TW * TW) hP hidem
    exact sub_nonneg.mp (Matrix.nonneg_iff_posSemidef.mpr hdiff_pos)
  have hconj :
      TV * (Matrix.conjTranspose TW * TW) * Matrix.conjTranspose TV ≤
        TV * (1 : CMatrix r) * Matrix.conjTranspose TV := by
    have hnon : 0 ≤ (1 : CMatrix r) - Matrix.conjTranspose TW * TW :=
      sub_nonneg.mpr hproj_le
    have hpos :
        0 ≤ TV * ((1 : CMatrix r) - Matrix.conjTranspose TW * TW) *
            Matrix.conjTranspose TV := by
      have h :=
        (Matrix.nonneg_iff_posSemidef.mp hnon).conjTranspose_mul_mul_same
          (Matrix.conjTranspose TV)
      simpa [Matrix.conjTranspose_conjTranspose] using
        (Matrix.nonneg_iff_posSemidef.mpr h)
    have hdiff :
        TV * ((1 : CMatrix r) - Matrix.conjTranspose TW * TW) *
            Matrix.conjTranspose TV =
          TV * (1 : CMatrix r) * Matrix.conjTranspose TV -
            TV * (Matrix.conjTranspose TW * TW) * Matrix.conjTranspose TV := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
    exact sub_nonneg.mp (by simpa [hdiff] using hpos)
  have hK :
      Matrix.conjTranspose (TW * Matrix.conjTranspose TV) *
          (TW * Matrix.conjTranspose TV) =
        TV * (Matrix.conjTranspose TW * TW) * Matrix.conjTranspose TV := by
    simp [TV, TW, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hK]
  calc
    TV * (Matrix.conjTranspose TW * TW) * Matrix.conjTranspose TV ≤
        TV * (1 : CMatrix r) * Matrix.conjTranspose TV := hconj
    _ = 1 := by
      simp [hTV]

/-- Any two purifications on a sufficiently large common reference have squared
overlap bounded by the squared fidelity of their target states.

This is the "only if" side of Uhlmann's variational characterization, stated
for arbitrary purifications rather than only canonical purifications. -/
theorem overlapSq_le_squaredFidelity_of_purifies_of_card_le
    {Ψ Φ : PureVector (Prod r a)} {ρ σ : State a}
    (hΨ : Ψ.Purifies ρ) (hΦ : Φ.Purifies σ)
    (hcard : Fintype.card a ≤ Fintype.card r) :
    Ψ.overlapSq Φ ≤ ρ.squaredFidelity σ := by
  classical
  obtain ⟨V, hV⟩ :=
    exists_referenceIsometry_amplitudeMatrix_eq_sqrtMatrix_mul_transpose hΨ hcard
  obtain ⟨W, hW⟩ :=
    exists_referenceIsometry_amplitudeMatrix_eq_sqrtMatrix_mul_transpose hΦ hcard
  let K : CMatrix a :=
    Matrix.transpose W.matrix * Matrix.conjTranspose (Matrix.transpose V.matrix)
  have hK : Matrix.conjTranspose K * K ≤ (1 : CMatrix a) := by
    simpa [K] using referenceIsometry_transpose_cross_contraction V W
  have hoverlap :
      Ψ.overlap Φ = ((ρ.sqrtMatrix * σ.sqrtMatrix) * K).trace := by
    calc
      Ψ.overlap Φ =
          (Matrix.conjTranspose Ψ.amplitudeMatrix * Φ.amplitudeMatrix).trace := by
        rw [overlap_eq_trace_conjTranspose_amplitudeMatrix_mul]
      _ =
          (Matrix.conjTranspose (ρ.sqrtMatrix * Matrix.transpose V.matrix) *
              (σ.sqrtMatrix * Matrix.transpose W.matrix)).trace := by
        rw [hV, hW]
      _ =
          (Matrix.conjTranspose (Matrix.transpose V.matrix) *
              (ρ.sqrtMatrix * σ.sqrtMatrix) * Matrix.transpose W.matrix).trace := by
        simp [Matrix.conjTranspose_mul, ρ.sqrtMatrix_isHermitian.eq,
          Matrix.mul_assoc]
      _ =
          ((ρ.sqrtMatrix * σ.sqrtMatrix) * Matrix.transpose W.matrix *
              Matrix.conjTranspose (Matrix.transpose V.matrix)).trace := by
        calc
          (Matrix.conjTranspose (Matrix.transpose V.matrix) *
              (ρ.sqrtMatrix * σ.sqrtMatrix) * Matrix.transpose W.matrix).trace =
              (Matrix.conjTranspose (Matrix.transpose V.matrix) *
                ((ρ.sqrtMatrix * σ.sqrtMatrix) * Matrix.transpose W.matrix)).trace := by
            simp [Matrix.mul_assoc]
          _ =
              (((ρ.sqrtMatrix * σ.sqrtMatrix) * Matrix.transpose W.matrix) *
                Matrix.conjTranspose (Matrix.transpose V.matrix)).trace := by
            exact Matrix.trace_mul_comm _ _
          _ =
              ((ρ.sqrtMatrix * σ.sqrtMatrix) * Matrix.transpose W.matrix *
                Matrix.conjTranspose (Matrix.transpose V.matrix)).trace := by
            simp [Matrix.mul_assoc]
      _ = ((ρ.sqrtMatrix * σ.sqrtMatrix) * K).trace := by
        simp [K, Matrix.mul_assoc]
  have habs :
      Complex.abs (Ψ.overlap Φ) ≤ traceNorm (ρ.sqrtMatrix * σ.sqrtMatrix) := by
    rw [hoverlap]
    exact traceNorm_variational_contraction_abs_trace_le
      (ρ.sqrtMatrix * σ.sqrtMatrix) K hK
  rw [PureVector.overlapSq_eq_normSq,
    State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq]
  exact complex_normSq_le_sq_of_abs_le habs

/-- Any two purifications have squared overlap bounded by the squared fidelity
of their target states.

This removes the auxiliary large-reference side condition by padding the
reference register with a right-summand embedding before applying the large
reference version. -/
theorem overlapSq_le_squaredFidelity_of_purifies
    {Ψ Φ : PureVector (Prod r a)} {ρ σ : State a}
    (hΨ : Ψ.Purifies ρ) (hΦ : Φ.Purifies σ) :
    Ψ.overlapSq Φ ≤ ρ.squaredFidelity σ := by
  classical
  let V := ReferenceIsometry.sumInr a r
  have hΨ' : (V.applyPureVector Ψ).Purifies ρ := V.applyPureVector_purifies hΨ
  have hΦ' : (V.applyPureVector Φ).Purifies σ := V.applyPureVector_purifies hΦ
  have hcard : Fintype.card a ≤ Fintype.card (Sum a r) := by
    simp [Fintype.card_sum]
  have hbound :=
    overlapSq_le_squaredFidelity_of_purifies_of_card_le hΨ' hΦ' hcard
  rwa [V.overlapSq_applyPureVector Ψ Φ] at hbound

/-- The absolute overlap of two purifications is bounded by the root fidelity
of their target states. -/
theorem abs_overlap_le_fidelity
    {Ψ Φ : PureVector (Prod r a)} {ρ σ : State a}
    (hΨ : Ψ.Purifies ρ) (hΦ : Φ.Purifies σ) :
    Complex.abs (Ψ.overlap Φ) ≤ ρ.fidelity σ := by
  have hsq := overlapSq_le_squaredFidelity_of_purifies hΨ hΦ
  rw [PureVector.overlapSq_eq_normSq, State.squaredFidelity_eq_fidelity_sq] at hsq
  have hleft_nonneg : 0 ≤ Complex.abs (Ψ.overlap Φ) := norm_nonneg _
  have hfid_nonneg : 0 ≤ ρ.fidelity σ := State.fidelity_nonneg ρ σ
  rw [Complex.normSq_eq_norm_sq] at hsq
  exact (sq_le_sq₀ hleft_nonneg hfid_nonneg).mp hsq

/-- Build a pure vector from an amplitude matrix whose Gram trace is one.

The matrix is indexed by target rows and reference columns, matching
`PureVector.amplitudeMatrix`. -/
def ofAmplitudeMatrix {r : Type u} {α : Type v}
    [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    (A : Matrix α r ℂ) (htrace : (A * Matrix.conjTranspose A).trace = 1) :
    PureVector (Prod r α) where
  amp := fun x => A x.2 x.1
  trace_rankOne_eq_one := by
    classical
    calc
      (rankOneMatrix (fun x : Prod r α => A x.2 x.1)).trace =
          ∑ x : Prod r α, A x.2 x.1 * star (A x.2 x.1) := by
            simp [Matrix.trace, rankOneMatrix_apply]
      _ = ∑ i : α, ∑ j : r, A i j * star (A i j) := by
            rw [Fintype.sum_prod_type]
            rw [Finset.sum_comm]
      _ = (A * Matrix.conjTranspose A).trace := by
            simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]
      _ = 1 := htrace

@[simp]
theorem ofAmplitudeMatrix_amplitudeMatrix {r : Type u} {α : Type v}
    [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    (A : Matrix α r ℂ) (htrace : (A * Matrix.conjTranspose A).trace = 1) :
    (ofAmplitudeMatrix A htrace).amplitudeMatrix = A := by
  ext x i
  rfl

/-- The pure vector built from an amplitude matrix purifies the state whose
matrix is the amplitude Gram. -/
theorem ofAmplitudeMatrix_purifies {r : Type u} {α : Type v}
    [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    {A : Matrix α r ℂ} {ρ : State α}
    (hgram : A * Matrix.conjTranspose A = ρ.matrix)
    (htrace : (A * Matrix.conjTranspose A).trace = 1) :
    (ofAmplitudeMatrix A htrace).Purifies ρ := by
  rw [PureVector.purifies_iff]
  rw [PureVector.state_matrix]
  rw [PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose]
  simpa [ofAmplitudeMatrix_amplitudeMatrix] using hgram

/-- Uhlmann extension theorem for an arbitrary sufficiently large reference
register: given a purification `Ψ` of `ρ` on reference `r`, every target state
`σ` has a purification on the same reference whose squared overlap with `Ψ`
attains `ρ.squaredFidelity σ`.

This is the normalized finite-dimensional form of the source Uhlmann extension
step [Tomamichel2015FiniteResources, metric.tex:314-327]. -/
theorem exists_purification_with_overlapSq_eq_squaredFidelity
    {Ψ : PureVector (Prod r a)} {ρ σ : State a}
    (hΨ : Ψ.Purifies ρ) (hcard : Fintype.card a ≤ Fintype.card r) :
    ∃ Φ : PureVector (Prod r a),
      Φ.Purifies σ ∧ Ψ.overlapSq Φ = ρ.squaredFidelity σ := by
  classical
  obtain ⟨U, hUeq, _hUle⟩ :=
    State.exists_referenceUnitary_canonicalPurification_overlapSq_eq_squaredFidelity ρ σ
  let Θ : PureVector (Prod a a) := U.applyPureVector σ.canonicalPurification
  have hΘ : Θ.Purifies σ := by
    simpa [Θ] using
      U.toReferenceIsometry.applyPureVector_purifies σ.canonicalPurification_purifies
  obtain ⟨V, hV⟩ :=
    exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state
      ρ.canonicalPurification_purifies hΨ hcard
  refine ⟨V.applyPureVector Θ, ?_, ?_⟩
  · exact V.applyPureVector_purifies hΘ
  · rw [hV, V.overlapSq_applyPureVector ρ.canonicalPurification Θ]
    exact hUeq.symm

end PureVector

namespace ReferenceIsometry

variable {r₁ : Type u} {r₂ : Type v} {a : Type w}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
variable [Fintype a] [DecidableEq a]

/-- A right-reference-side isometry preserves squared pure-vector overlaps. -/
theorem overlapSq_applyPureVectorRight (V : ReferenceIsometry r₁ r₂)
    (Ψ Φ : PureVector (Prod a r₁)) :
    (V.applyPureVectorRight Ψ).overlapSq (V.applyPureVectorRight Φ) =
      Ψ.overlapSq Φ := by
  rw [ReferenceIsometry.applyPureVectorRight, ReferenceIsometry.applyPureVectorRight]
  rw [PureVector.overlapSq_reindex]
  rw [V.overlapSq_applyPureVector]
  rw [PureVector.overlapSq_reindex]

end ReferenceIsometry

namespace State

variable {r : Type v}
variable [Fintype r] [DecidableEq r]
variable {a : Type u}
variable [Fintype a] [DecidableEq a]

/-- Every finite-dimensional state has a purification on any reference register
whose cardinality is at least the target cardinality. -/
theorem exists_purification_on_reference_of_card_le
    (ρ : State a) (hcard : Fintype.card a ≤ Fintype.card r) :
    ∃ Ψ : PureVector (Prod r a), Ψ.Purifies ρ := by
  classical
  let emb : a ↪ r := Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
  let V : ReferenceIsometry a r := {
    matrix := fun x i => if x = emb i then 1 else 0
    isometry := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij
        rw [Finset.sum_eq_single (emb i)]
        · simp
        · intro y _ hy
          simp [hy]
        · simp
      · rw [Finset.sum_eq_zero]
        · simp [hij]
        · intro y _
          by_cases hyj : y = emb j
          · subst hyj
            have hne : emb j ≠ emb i := fun h => hij ((emb.injective h).symm)
            simp [hne]
          · simp [hyj] }
  refine ⟨V.applyPureVector ρ.canonicalPurification, ?_⟩
  exact V.applyPureVector_purifies ρ.canonicalPurification_purifies

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

omit [DecidableEq a] [DecidableEq b] in
private theorem card_le_prod_prod_right [Nonempty b] :
    Fintype.card a ≤ Fintype.card (Prod (Prod a b) b) := by
  have hbpos : 0 < Fintype.card b := Fintype.card_pos_iff.mpr inferInstance
  have h1 : Fintype.card a ≤ Fintype.card a * Fintype.card b :=
    Nat.le_mul_of_pos_right (Fintype.card a) hbpos
  have h2 : Fintype.card a * Fintype.card b ≤
      (Fintype.card a * Fintype.card b) * Fintype.card b :=
    Nat.le_mul_of_pos_right (Fintype.card a * Fintype.card b) hbpos
  simpa [Fintype.card_prod, Nat.mul_assoc] using h1.trans h2

omit [DecidableEq a] [DecidableEq b] in
private theorem card_le_prod_prod_left [Nonempty a] :
    Fintype.card b ≤ Fintype.card (Prod (Prod a b) a) := by
  have hapos : 0 < Fintype.card a := Fintype.card_pos_iff.mpr inferInstance
  have h1 : Fintype.card b ≤ Fintype.card b * Fintype.card a :=
    Nat.le_mul_of_pos_right (Fintype.card b) hapos
  have h2 : Fintype.card b * Fintype.card a ≤
      (Fintype.card b * Fintype.card a) * Fintype.card a :=
    Nat.le_mul_of_pos_right (Fintype.card b * Fintype.card a) hapos
  calc
    Fintype.card b ≤ Fintype.card b * Fintype.card a := h1
    _ ≤ (Fintype.card b * Fintype.card a) * Fintype.card a := h2
    _ = Fintype.card (Prod (Prod a b) a) := by
      simp [Fintype.card_prod, Nat.mul_comm]

/-- Squared fidelity cannot decrease when tracing out the second subsystem. -/
theorem squaredFidelity_le_marginalA_squaredFidelity [Nonempty b]
    (ρ σ : State (Prod a b)) :
    ρ.squaredFidelity σ ≤ ρ.marginalA.squaredFidelity σ.marginalA := by
  classical
  obtain ⟨U, hUeq, _hUle⟩ :=
    State.exists_referenceUnitary_canonicalPurification_overlapSq_eq_squaredFidelity ρ σ
  let Ψ : PureVector (Prod (Prod a b) (Prod a b)) := ρ.canonicalPurification
  let Φ : PureVector (Prod (Prod a b) (Prod a b)) :=
    U.applyPureVector σ.canonicalPurification
  let e := PureVector.marginalAReferenceEquiv (Prod a b) a b
  have hΨ : Ψ.Purifies ρ := by
    simpa [Ψ] using ρ.canonicalPurification_purifies
  have hΦ : Φ.Purifies σ := by
    simpa [Φ] using
      U.toReferenceIsometry.applyPureVector_purifies σ.canonicalPurification_purifies
  have hΨA : (Ψ.reindex e).Purifies ρ.marginalA := by
    simpa [e] using
      PureVector.reindex_marginalAReferenceEquiv_purifies_marginalA hΨ
  have hΦA : (Φ.reindex e).Purifies σ.marginalA := by
    simpa [e] using
      PureVector.reindex_marginalAReferenceEquiv_purifies_marginalA hΦ
  have hcard : Fintype.card a ≤ Fintype.card (Prod (Prod a b) b) := by
    simpa using card_le_prod_prod_right (a := a) (b := b)
  have hbound :=
    PureVector.overlapSq_le_squaredFidelity_of_purifies_of_card_le
      hΨA hΦA hcard
  rw [PureVector.overlapSq_reindex] at hbound
  rw [← hUeq] at hbound
  simpa [Ψ, Φ] using hbound

/-- Squared fidelity cannot decrease when tracing out the first subsystem. -/
theorem squaredFidelity_le_marginalB_squaredFidelity [Nonempty a]
    (ρ σ : State (Prod a b)) :
    ρ.squaredFidelity σ ≤ ρ.marginalB.squaredFidelity σ.marginalB := by
  classical
  obtain ⟨U, hUeq, _hUle⟩ :=
    State.exists_referenceUnitary_canonicalPurification_overlapSq_eq_squaredFidelity ρ σ
  let Ψ : PureVector (Prod (Prod a b) (Prod a b)) := ρ.canonicalPurification
  let Φ : PureVector (Prod (Prod a b) (Prod a b)) :=
    U.applyPureVector σ.canonicalPurification
  let e := PureVector.marginalBReferenceEquiv (Prod a b) a b
  have hΨ : Ψ.Purifies ρ := by
    simpa [Ψ] using ρ.canonicalPurification_purifies
  have hΦ : Φ.Purifies σ := by
    simpa [Φ] using
      U.toReferenceIsometry.applyPureVector_purifies σ.canonicalPurification_purifies
  have hΨB : (Ψ.reindex e).Purifies ρ.marginalB := by
    simpa [e] using
      PureVector.reindex_marginalBReferenceEquiv_purifies_marginalB hΨ
  have hΦB : (Φ.reindex e).Purifies σ.marginalB := by
    simpa [e] using
      PureVector.reindex_marginalBReferenceEquiv_purifies_marginalB hΦ
  have hcard : Fintype.card b ≤ Fintype.card (Prod (Prod a b) a) := by
    simpa using card_le_prod_prod_left (a := a) (b := b)
  have hbound :=
    PureVector.overlapSq_le_squaredFidelity_of_purifies_of_card_le
      hΨB hΦB hcard
  rw [PureVector.overlapSq_reindex] at hbound
  rw [← hUeq] at hbound
  simpa [Ψ, Φ] using hbound

/-- Squared fidelity cannot decrease under a finite-dimensional channel. -/
theorem squaredFidelity_le_applyState_squaredFidelity
    (Φ : Channel a b) (ρ σ : State a) :
    ρ.squaredFidelity σ ≤
      (Φ.applyState ρ).squaredFidelity (Φ.applyState σ) := by
  classical
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  have hTPK : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  let V := MatrixMap.krausStinespringIsometry K hTPK
  obtain ⟨U, hUeq, _hUle⟩ :=
    State.exists_referenceUnitary_canonicalPurification_overlapSq_eq_squaredFidelity ρ σ
  let Ψ : PureVector (Prod a a) := ρ.canonicalPurification
  let Θ : PureVector (Prod a a) := U.applyPureVector σ.canonicalPurification
  let Ψout : PureVector (Prod a (Prod b (a × b))) := V.applyPureVectorRight Ψ
  let Θout : PureVector (Prod a (Prod b (a × b))) := V.applyPureVectorRight Θ
  let τρ : State (Prod b (a × b)) := Ψout.state.marginalB
  let τσ : State (Prod b (a × b)) := Θout.state.marginalB
  have hΨpur : Ψ.Purifies ρ := by
    simpa [Ψ] using ρ.canonicalPurification_purifies
  have hΘpur : Θ.Purifies σ := by
    simpa [Θ] using
      U.toReferenceIsometry.applyPureVector_purifies σ.canonicalPurification_purifies
  have hΨoutpur : Ψout.Purifies τρ := by
    simp [Ψout, τρ]
  have hΘoutpur : Θout.Purifies τσ := by
    simp [Θout, τσ]
  have hoverlap_bound : Ψout.overlapSq Θout ≤ τρ.squaredFidelity τσ :=
    PureVector.overlapSq_le_squaredFidelity_of_purifies hΨoutpur hΘoutpur
  have hoverlap_pres : Ψout.overlapSq Θout = Ψ.overlapSq Θ := by
    simpa [Ψout, Θout, V] using V.overlapSq_applyPureVectorRight Ψ Θ
  haveI : Nonempty (a × b) :=
    ⟨(Classical.choice ρ.nonempty, Classical.choice (Φ.applyState ρ).nonempty)⟩
  have htrace_env : τρ.squaredFidelity τσ ≤
      τρ.marginalA.squaredFidelity τσ.marginalA :=
    State.squaredFidelity_le_marginalA_squaredFidelity τρ τσ
  have hτρm : τρ.marginalA = Φ.applyState ρ := by
    apply State.ext
    calc
      τρ.marginalA.matrix = MatrixMap.ofKraus K ρ.matrix := by
        simpa [τρ, Ψout, V] using
          MatrixMap.marginalA_marginalB_applyPureVectorRight_krausStinespringIsometry
            K hTPK hΨpur
      _ = (Φ.applyState ρ).matrix := by
        simp [Channel.applyState, hK]
  have hτσm : τσ.marginalA = Φ.applyState σ := by
    apply State.ext
    calc
      τσ.marginalA.matrix = MatrixMap.ofKraus K σ.matrix := by
        simpa [τσ, Θout, V] using
          MatrixMap.marginalA_marginalB_applyPureVectorRight_krausStinespringIsometry
            K hTPK hΘpur
      _ = (Φ.applyState σ).matrix := by
        simp [Channel.applyState, hK]
  calc
    ρ.squaredFidelity σ = Ψ.overlapSq Θ := by
      simpa [Ψ, Θ] using hUeq
    _ = Ψout.overlapSq Θout := hoverlap_pres.symm
    _ ≤ τρ.squaredFidelity τσ := hoverlap_bound
    _ ≤ τρ.marginalA.squaredFidelity τσ.marginalA := htrace_env
    _ = (Φ.applyState ρ).squaredFidelity (Φ.applyState σ) := by
      rw [hτρm, hτσm]

end State

end

end QIT
