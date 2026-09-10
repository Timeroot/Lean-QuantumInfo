/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.HypothesisTesting.ComparatorTest
public import QuantumLib.QIT.Channels.Diamond
public import QuantumLib.QIT.States.Purification.Equivalence
public import QuantumLib.QIT.States.Purification.Canonical
import QuantumLib.QIT.States.Purification.Uhlmann
public import QuantumLib.QIT.States.Purification.ReferenceIsometry

/-!
# Hypothesis-testing data processing

This module proves the finite-dimensional effect-pullback route for
hypothesis-testing relative entropy and optimized hypothesis-testing mutual
information data processing.  The route is the one used in the one-shot
entanglement-assisted classical communication meta-converse
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:327-394].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

noncomputable section
universe u v w x y

open QIT

namespace QIT

namespace ReferenceIsometry

variable {a : Type u}
variable [Fintype a] [DecidableEq a]
variable {r₁ : Type x} {r₂ : Type y}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]

theorem applyMatrix_sub (V : ReferenceIsometry r₁ r₂)
    (X Y : CMatrix (r₁ × a)) :
    V.applyMatrix (X - Y) = V.applyMatrix X - V.applyMatrix Y := by
  rw [← MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft V (X - Y)]
  rw [map_sub]
  rw [MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft V X]
  rw [MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft V Y]

omit [DecidableEq a] [DecidableEq r₁] in theorem targetBlock_mul (X Y : CMatrix (r₁ × a)) (i j : a) :
    targetBlock (X * Y) i j =
      ∑ k : a, targetBlock X i k * targetBlock Y k j := by
  ext x y
  change (X * Y) (x, i) (y, j) =
    (∑ k : a, targetBlock X i k * targetBlock Y k j) x y
  rw [Matrix.mul_apply, ← Finset.univ_product_univ, Finset.sum_product,
    Finset.sum_comm]
  rw [Matrix.sum_apply]
  simp [targetBlock, Matrix.mul_apply]

omit [DecidableEq a] in theorem applyMatrix_mul (V : ReferenceIsometry r₁ r₂)
    (X Y : CMatrix (r₁ × a)) :
    V.applyMatrix X * V.applyMatrix Y = V.applyMatrix (X * Y) := by
  ext p q
  calc
    (V.applyMatrix X * V.applyMatrix Y) p q =
        (∑ k : a,
          ((V.matrix * targetBlock X p.2 k * Matrix.conjTranspose V.matrix) *
            (V.matrix * targetBlock Y k q.2 * Matrix.conjTranspose V.matrix)) p.1 q.1) := by
      change (∑ j : r₂ × a, V.applyMatrix X p j * V.applyMatrix Y j q) =
        (∑ k : a,
          ((V.matrix * targetBlock X p.2 k * Matrix.conjTranspose V.matrix) *
            (V.matrix * targetBlock Y k q.2 * Matrix.conjTranspose V.matrix)) p.1 q.1)
      rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]
      simp [applyMatrix, Matrix.mul_apply]
    _ =
        (∑ k : a,
          (V.matrix * (targetBlock X p.2 k * targetBlock Y k q.2) *
            Matrix.conjTranspose V.matrix) p.1 q.1) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [V.matrix_mul_conjTranspose_mul_matrix]
    _ = (V.matrix *
          (∑ k : a, targetBlock X p.2 k * targetBlock Y k q.2) *
            Matrix.conjTranspose V.matrix) p.1 q.1 := by
      have hsum :
          V.matrix *
              (∑ k : a, targetBlock X p.2 k * targetBlock Y k q.2) *
              Matrix.conjTranspose V.matrix =
            ∑ k : a,
              V.matrix * (targetBlock X p.2 k * targetBlock Y k q.2) *
                Matrix.conjTranspose V.matrix := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
      have hentry := congrFun (congrFun hsum p.1) q.1
      simpa [Matrix.sum_apply] using hentry.symm
    _ = V.applyMatrix (X * Y) p q := by
      rw [← targetBlock_mul X Y p.2 q.2]
      rfl

theorem applyMatrix_one_idempotent (V : ReferenceIsometry r₁ r₂) :
    V.applyMatrix (1 : CMatrix (r₁ × a)) *
      V.applyMatrix (1 : CMatrix (r₁ × a)) =
        V.applyMatrix (1 : CMatrix (r₁ × a)) := by
  rw [V.applyMatrix_mul, Matrix.mul_one]

theorem one_sub_applyMatrix_one_posSemidef (V : ReferenceIsometry r₁ r₂) :
    (1 - V.applyMatrix (1 : CMatrix (r₁ × a))).PosSemidef := by
  exact MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent
    (V.applyMatrix (1 : CMatrix (r₁ × a)))
    (V.applyMatrix_posSemidef Matrix.PosSemidef.one)
    (V.applyMatrix_one_idempotent (a := a))

theorem applyMatrix_le_one_of_le_one (V : ReferenceIsometry r₁ r₂)
    {E : CMatrix (r₁ × a)} (hE : E ≤ 1) :
    V.applyMatrix E ≤ 1 := by
  rw [Matrix.le_iff]
  have hEsub : (1 - E).PosSemidef := by
    simpa [Matrix.le_iff] using hE
  have himageSub :
      (V.applyMatrix ((1 : CMatrix (r₁ × a)) - E)).PosSemidef :=
    V.applyMatrix_posSemidef hEsub
  have hdecomp :
      (1 : CMatrix (r₂ × a)) - V.applyMatrix E =
        (1 - V.applyMatrix (1 : CMatrix (r₁ × a))) +
          V.applyMatrix ((1 : CMatrix (r₁ × a)) - E) := by
    rw [V.applyMatrix_sub]
    abel
  rw [hdecomp]
  exact Matrix.PosSemidef.add
    (V.one_sub_applyMatrix_one_posSemidef (a := a)) himageSub

omit [DecidableEq a] in theorem trace_applyMatrix_mul_applyMatrix (V : ReferenceIsometry r₁ r₂)
    (X Y : CMatrix (r₁ × a)) :
    ((V.applyMatrix X * V.applyMatrix Y).trace) = (X * Y).trace := by
  rw [V.applyMatrix_mul, V.trace_applyMatrix]

end ReferenceIsometry

end QIT
end

noncomputable section

namespace CPTPOp

open QIT

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem effectAcceptProbability_applyState_dualEffect
    (Φ : CPTPMap a b) (ρ : MState a) (E : CMatrix b) :
    effectAcceptProbability (Φ ρ) E =
      effectAcceptProbability ρ (Φ.dualEffect E) := by
  unfold effectAcceptProbability
  rw [Φ.applyState_dualEffect_trace ρ E]

/-- Pull back a feasible output hypothesis-testing effect along a channel. -/
def pullbackHypothesisTestingEffect
    (Φ : CPTPMap a b) (ρ : MState a) (ε : ℝ)
    (Λ : HypothesisTestingEffect (Φ ρ) ε) :
    HypothesisTestingEffect ρ ε where
  effect := Φ.dualEffect Λ.effect
  pos := Φ.dualEffect_posSemidef Λ.pos
  le_one := Φ.dualEffect_le_one_of_le_one Λ.le_one
  accept_ge := by
    rw [← Φ.effectAcceptProbability_applyState_dualEffect ρ Λ.effect]
    exact Λ.accept_ge

theorem pullbackHypothesisTestingEffect_typeIIError
    (Φ : CPTPMap a b) (ρ σ : MState a) (ε : ℝ)
    (Λ : HypothesisTestingEffect (Φ ρ) ε) :
    (Φ.pullbackHypothesisTestingEffect ρ ε Λ).typeIIError σ =
      Λ.typeIIError (Φ σ) := by
  unfold pullbackHypothesisTestingEffect HypothesisTestingEffect.typeIIError
    effectTypeIIError
  rw [← Φ.effectAcceptProbability_applyState_dualEffect σ Λ.effect]

end CPTPOp

end

noncomputable section

namespace QIT

open QIT

namespace ReferenceIsometry

variable {a : Type u}
variable [Fintype a] [DecidableEq a]
variable {r₁ : Type x} {r₂ : Type y}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]

/-- Push a feasible hypothesis-testing effect forward along a reference
isometry.  This is the effect-side reverse of channel pullback, valid because
an isometry embeds the whole tested subspace and preserves the trace pairing on
the image. -/
def pushForwardHypothesisTestingEffect
    (V : ReferenceIsometry r₁ r₂) (ρ : MState (r₁ × a)) (ε : ℝ)
    (Λ : HypothesisTestingEffect ρ ε) :
    HypothesisTestingEffect
      (((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := a))) ρ) ε where
  effect := V.applyMatrix Λ.effect
  pos := V.applyMatrix_posSemidef Λ.pos
  le_one := V.applyMatrix_le_one_of_le_one Λ.le_one
  accept_ge := by
    simp only [effectAcceptProbability, CPTPOp.ofReferenceIsometry_prod_id_applyState_matrix,
      V.trace_applyMatrix_mul_applyMatrix]
    exact Λ.accept_ge

theorem pushForwardHypothesisTestingEffect_typeIIError
    (V : ReferenceIsometry r₁ r₂) (ρ σ : MState (r₁ × a)) (ε : ℝ)
    (Λ : HypothesisTestingEffect ρ ε) :
    (V.pushForwardHypothesisTestingEffect ρ ε Λ).typeIIError
      (((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := a))) σ) =
      Λ.typeIIError σ := by
  simp only [pushForwardHypothesisTestingEffect, HypothesisTestingEffect.typeIIError,
    effectTypeIIError, effectAcceptProbability,
    CPTPOp.ofReferenceIsometry_prod_id_applyState_matrix,
    V.trace_applyMatrix_mul_applyMatrix]

end ReferenceIsometry

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

private theorem trace_reindex_mul_reindex
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (X Y : CMatrix α) :
    ((X.submatrix e.symm e.symm * Y.submatrix e.symm e.symm).trace) =
      (X * Y).trace := by
  rw [Matrix.trace, Matrix.trace]
  change (∑ i : β, ∑ j : β,
      X (e.symm i) (e.symm j) * Y (e.symm j) (e.symm i)) =
    ∑ i : α, ∑ j : α, X i j * Y j i
  trans ∑ i : α, ∑ j : β, X i (e.symm j) * Y (e.symm j) i
  · exact Fintype.sum_equiv e.symm
      (fun i : β => ∑ j : β,
        X (e.symm i) (e.symm j) * Y (e.symm j) (e.symm i))
      (fun i : α => ∑ j : β, X i (e.symm j) * Y (e.symm j) i)
      (by intro i; rfl)
  · refine Finset.sum_congr rfl ?_
    intro i _
    exact Fintype.sum_equiv e.symm
      (fun j : β => X i (e.symm j) * Y (e.symm j) i)
      (fun j : α => X i j * Y j i)
      (by intro j; rfl)

private theorem submatrix_one_equiv
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) :
    (1 : CMatrix α).submatrix e.symm e.symm = (1 : CMatrix β) := by
  ext i j
  simp [Matrix.one_apply]

private theorem submatrix_sub_equiv
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (X Y : CMatrix α) :
    (X - Y).submatrix e.symm e.symm =
      X.submatrix e.symm e.symm - Y.submatrix e.symm e.symm := by
  ext i j
  rfl

namespace HypothesisTestingEffect

variable {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
variable [Fintype β] [DecidableEq β]
variable {ρ σ : MState α} {ε : ℝ}

/-- Relabel a feasible hypothesis-testing effect along a finite basis
equivalence. -/
def reindex (Λ : HypothesisTestingEffect ρ ε) (e : α ≃ β) :
    HypothesisTestingEffect (ρ.reindex e) ε where
  effect := Λ.effect.submatrix e.symm e.symm
  pos := Λ.pos.submatrix e.symm
  le_one := by
    have hle_one := Λ.le_one
    rw [Matrix.le_iff] at hle_one ⊢
    simpa [submatrix_sub_equiv e (1 : CMatrix α) Λ.effect,
      submatrix_one_equiv e] using hle_one.submatrix e.symm
  accept_ge := by
    simp only [effectAcceptProbability, MState.reindex_matrix]
    rw [trace_reindex_mul_reindex e ρ.m Λ.effect]
    exact Λ.accept_ge

theorem reindex_typeIIError (Λ : HypothesisTestingEffect ρ ε)
    (e : α ≃ β) :
    (Λ.reindex e).typeIIError (σ.reindex e) = Λ.typeIIError σ := by
  unfold HypothesisTestingEffect.typeIIError effectTypeIIError effectAcceptProbability
  rw [MState.reindex_matrix]
  change (((σ.m.submatrix e.symm e.symm) *
      (Λ.effect.submatrix e.symm e.symm)).trace).re =
    ((σ.m * Λ.effect).trace).re
  rw [trace_reindex_mul_reindex e σ.m Λ.effect]

end HypothesisTestingEffect

end QIT

namespace MState

open QIT

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

theorem hypothesisTestingBeta_reindex_le
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ρ σ : MState α) (ε : ℝ) (hε : 0 ≤ ε) (e : α ≃ β) :
    (ρ.reindex e).hypothesisTestingBeta (σ.reindex e) ε ≤
      ρ.hypothesisTestingBeta σ ε := by
  change (ρ.reindex e).hypothesisTestingBeta (σ.reindex e) ε ≤
    sInf (ρ.hypothesisTestingBetaCandidateSet σ ε)
  refine le_csInf (ρ.hypothesisTestingBetaCandidateSet_nonempty_of_nonneg σ ε hε) ?_
  intro β hβ
  rcases hβ with ⟨Λ, rfl⟩
  have hle :=
    MState.hypothesisTestingBeta_le_of_effect
      (ρ.reindex e) (σ.reindex e) ε (Λ.reindex e)
  rw [HypothesisTestingEffect.reindex_typeIIError Λ e] at hle
  exact hle

theorem hypothesisTestingBeta_le_reindex
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ρ σ : MState α) (ε : ℝ) (hε : 0 ≤ ε) (e : α ≃ β) :
    ρ.hypothesisTestingBeta σ ε ≤
      (ρ.reindex e).hypothesisTestingBeta (σ.reindex e) ε := by
  have h :=
    hypothesisTestingBeta_reindex_le (ρ.reindex e) (σ.reindex e) ε hε e.symm
  simpa [MState.reindex_reindex_symm] using h

theorem hypothesisTestingBeta_reindex
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ρ σ : MState α) (ε : ℝ) (hε : 0 ≤ ε) (e : α ≃ β) :
    (ρ.reindex e).hypothesisTestingBeta (σ.reindex e) ε =
      ρ.hypothesisTestingBeta σ ε :=
  le_antisymm (hypothesisTestingBeta_reindex_le ρ σ ε hε e)
    (hypothesisTestingBeta_le_reindex ρ σ ε hε e)

theorem hypothesisTestingRelativeEntropyFinite_reindex
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ρ σ : MState α) (ε : ℝ) (hε : 0 ≤ ε) (e : α ≃ β) :
    (ρ.reindex e).hypothesisTestingRelativeEntropyFinite (σ.reindex e) ε =
      ρ.hypothesisTestingRelativeEntropyFinite σ ε := by
  rw [hypothesisTestingRelativeEntropyFinite_eq, hypothesisTestingRelativeEntropyFinite_eq,
    hypothesisTestingBeta_reindex ρ σ ε hε e]

theorem hypothesisTestingRelativeEntropy_reindex
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ρ σ : MState α) (ε : ℝ) (hε : 0 ≤ ε) (e : α ≃ β) :
    (ρ.reindex e).hypothesisTestingRelativeEntropy (σ.reindex e) ε =
      ρ.hypothesisTestingRelativeEntropy σ ε := by
  have hβ := hypothesisTestingBeta_reindex ρ σ ε hε e
  by_cases hzero : ρ.hypothesisTestingBeta σ ε = 0
  · have hzero' :
        (ρ.reindex e).hypothesisTestingBeta (σ.reindex e) ε = 0 := by
      simpa [hβ] using hzero
    simp [hypothesisTestingRelativeEntropy, hzero, hzero']
  · have hzero' :
        (ρ.reindex e).hypothesisTestingBeta (σ.reindex e) ε ≠ 0 := by
      simpa [hβ] using hzero
    simp [hypothesisTestingRelativeEntropy, hzero, hzero',
      hypothesisTestingRelativeEntropyFinite_reindex ρ σ ε hε e]

private theorem prod_reindex_prodCongr_forHypothesisTestingDPI
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (ρ : MState α) (σ : MState γ) (e : α ≃ β) (f : γ ≃ δ) :
    (ρ.prod σ).reindex (Equiv.prodCongr e f) =
      (ρ.reindex e).prod (σ.reindex f) := by
  apply MState.ext
  ext i j
  simp

theorem hypothesisTestingMutualInformation_reindex_prodCongr_le
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (ρ : MState (α × γ)) (ε : ℝ) (hε : 0 ≤ ε)
    (e : α ≃ β) (f : γ ≃ δ) :
    (ρ.reindex (Equiv.prodCongr e f)).hypothesisTestingMutualInformation ε ≤
      ρ.hypothesisTestingMutualInformation ε := by
  let ρ' : MState (β × δ) := ρ.reindex (Equiv.prodCongr e f)
  rw [hypothesisTestingMutualInformation_eq_sInf]
  refine le_sInf ?_
  intro value hvalue
  rcases hvalue with ⟨σB, rfl⟩
  have houtMem :
      ρ'.hypothesisTestingRelativeEntropy
          (ρ'.traceRight.prod (σB.reindex f)) ε ∈
        hypothesisTestingMutualInformationCandidateSet (a := β) (b := δ) ρ' ε := by
    exact ⟨σB.reindex f, rfl⟩
  have houtLe :
      ρ'.hypothesisTestingMutualInformation ε ≤
        ρ'.hypothesisTestingRelativeEntropy
          (ρ'.traceRight.prod (σB.reindex f)) ε := by
    rw [hypothesisTestingMutualInformation_eq_sInf]
    exact sInf_le houtMem
  have hmarg : ρ'.traceRight = ρ.traceRight.reindex e := by
    simpa [ρ'] using MState.traceRight_reindex_prodCongr ρ e f
  have hprod :
      ρ'.traceRight.prod (σB.reindex f) =
        (ρ.traceRight.prod σB).reindex (Equiv.prodCongr e f) := by
    rw [hmarg]
    exact (prod_reindex_prodCongr_forHypothesisTestingDPI
      ρ.traceRight σB e f).symm
  have hD :
      ρ'.hypothesisTestingRelativeEntropy
          ((ρ.traceRight.prod σB).reindex (Equiv.prodCongr e f)) ε =
        ρ.hypothesisTestingRelativeEntropy (ρ.traceRight.prod σB) ε := by
    simpa [ρ'] using
      hypothesisTestingRelativeEntropy_reindex ρ (ρ.traceRight.prod σB) ε hε
        (Equiv.prodCongr e f)
  exact houtLe.trans (by simpa [hprod] using le_of_eq hD)

theorem hypothesisTestingMutualInformation_reindex_prodCongr
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (ρ : MState (α × γ)) (ε : ℝ) (hε : 0 ≤ ε)
    (e : α ≃ β) (f : γ ≃ δ) :
    (ρ.reindex (Equiv.prodCongr e f)).hypothesisTestingMutualInformation ε =
      ρ.hypothesisTestingMutualInformation ε := by
  let ρ' : MState (β × δ) := ρ.reindex (Equiv.prodCongr e f)
  have hforward :
      ρ'.hypothesisTestingMutualInformation ε ≤
        ρ.hypothesisTestingMutualInformation ε := by
    simpa [ρ'] using hypothesisTestingMutualInformation_reindex_prodCongr_le
      ρ ε hε e f
  have hback :
      ρ.hypothesisTestingMutualInformation ε ≤
        ρ'.hypothesisTestingMutualInformation ε := by
    have h :=
      hypothesisTestingMutualInformation_reindex_prodCongr_le
        ρ' ε hε e.symm f.symm
    have hreindex : ρ'.reindex (Equiv.prodCongr e.symm f.symm) = ρ := by
      apply MState.ext
      ext i j
      rcases i with ⟨iα, iγ⟩
      rcases j with ⟨jα, jγ⟩
      simp [ρ']
    simpa [hreindex] using h
  exact le_antisymm hforward hback

/-- Canonical purification of a mixed input-reference state, re-associated so
that the original reference remains part of the reference register and the
channel input is the target register. -/
def purifiedInputForHypothesisTestingDPI
    {r : Type u} {a : Type v} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a] (ρ : MState (r × a)) :
    Ket (((r × a) × r) × a) :=
  ρ.canonicalPurification.reindex (Equiv.prodAssoc (r × a) r a).symm

theorem traceOut_purifiedInputForHypothesisTestingDPI
    {r : Type u} {a : Type v} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a] (ρ : MState (r × a)) :
    ((CPTPOp.traceOutLeft (r × a) r).prod
        (CPTPOp.id (dIn := a)))
        (ρ.purifiedInputForHypothesisTestingDPI.state) = ρ := by
  apply MState.ext
  rw [CPTPOp.mat_coe_eq_apply_mat, CPTPOp.prod_map]
  ext x y
  rcases x with ⟨xr, xa⟩
  rcases y with ⟨yr, ya⟩
  rw [MatrixMap.kron_idChannel_apply_slice, CPTPOp.traceOutLeft_map]
  change
    (Matrix.traceLeft
      (fun i j =>
        ρ.purifiedInputForHypothesisTestingDPI.state.m (i, xa) (j, ya)))
        xr yr =
      ρ.m (xr, xa) (yr, ya)
  change
    (∑ p : r × a,
      ρ.purifiedInputForHypothesisTestingDPI.state.m ((p, xr), xa) ((p, yr), ya)) =
      ρ.m (xr, xa) (yr, ya)
  have hentry :=
    congrFun (congrFun (MState.canonicalPurification_matrix ρ) (xr, xa)) (yr, ya)
  rw [← hentry]
  simp [Matrix.traceLeft, purifiedInputForHypothesisTestingDPI,
    Ket.reindex_state, Ket.state_matrix,
    MState.canonicalPurification]

theorem hypothesisTestingBeta_applyReferenceIsometry_le
    {r₁ : Type x} {r₂ : Type y} [Fintype r₁] [DecidableEq r₁]
    [Fintype r₂] [DecidableEq r₂]
    (V : ReferenceIsometry r₁ r₂) (ρ σ : MState (r₁ × a))
    (ε : ℝ) (hε : 0 ≤ ε) :
    MState.hypothesisTestingBeta
        (((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := a))) ρ)
        (((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := a))) σ)
        ε ≤
      ρ.hypothesisTestingBeta σ ε := by
  change
    MState.hypothesisTestingBeta
        (((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := a))) ρ)
        (((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := a))) σ)
        ε ≤
      sInf (ρ.hypothesisTestingBetaCandidateSet σ ε)
  refine le_csInf (ρ.hypothesisTestingBetaCandidateSet_nonempty_of_nonneg σ ε hε) ?_
  intro β hβ
  rcases hβ with ⟨Λ, rfl⟩
  have hle :=
    MState.hypothesisTestingBeta_le_of_effect
        (((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := a))) ρ)
        (((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := a))) σ)
        ε
        (V.pushForwardHypothesisTestingEffect ρ ε Λ)
  rw [ReferenceIsometry.pushForwardHypothesisTestingEffect_typeIIError V ρ σ ε Λ] at hle
  exact hle

theorem hypothesisTestingRelativeEntropy_le_applyReferenceIsometry
    {r₁ : Type x} {r₂ : Type y} [Fintype r₁] [DecidableEq r₁]
    [Fintype r₂] [DecidableEq r₂]
    (V : ReferenceIsometry r₁ r₂) (ρ σ : MState (r₁ × a))
    (ε : ℝ) (hε : 0 ≤ ε) :
    ρ.hypothesisTestingRelativeEntropy σ ε ≤
      MState.hypothesisTestingRelativeEntropy
        (((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := a))) ρ)
        (((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := a))) σ)
        ε := by
  let ρ' : MState (r₂ × a) :=
    ((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := a))) ρ
  let σ' : MState (r₂ × a) :=
    ((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := a))) σ
  have hβle : ρ'.hypothesisTestingBeta σ' ε ≤ ρ.hypothesisTestingBeta σ ε := by
    exact hypothesisTestingBeta_applyReferenceIsometry_le V ρ σ ε hε
  by_cases hβin_zero : ρ.hypothesisTestingBeta σ ε = 0
  · have hβout_nonneg : 0 ≤ ρ'.hypothesisTestingBeta σ' ε :=
      ρ'.hypothesisTestingBeta_nonneg σ' ε hε
    have hβout_zero : ρ'.hypothesisTestingBeta σ' ε = 0 :=
      le_antisymm (by simpa [hβin_zero] using hβle) hβout_nonneg
    simp [hypothesisTestingRelativeEntropy, hβin_zero, hβout_zero, ρ', σ']
  · have hβin_nonneg := ρ.hypothesisTestingBeta_nonneg σ ε hε
    have hβin_pos : 0 < ρ.hypothesisTestingBeta σ ε :=
      lt_of_le_of_ne' hβin_nonneg hβin_zero
    by_cases hβout_zero : ρ'.hypothesisTestingBeta σ' ε = 0
    · simp [hypothesisTestingRelativeEntropy, hβin_zero, hβout_zero, ρ', σ']
    · have hβout_nonneg : 0 ≤ ρ'.hypothesisTestingBeta σ' ε :=
        ρ'.hypothesisTestingBeta_nonneg σ' ε hε
      have hβout_pos : 0 < ρ'.hypothesisTestingBeta σ' ε :=
        lt_of_le_of_ne' hβout_nonneg hβout_zero
      have hlog :
          log2 (ρ'.hypothesisTestingBeta σ' ε) ≤
            log2 (ρ.hypothesisTestingBeta σ ε) := by
        unfold log2
        exact div_le_div_of_nonneg_right
          (Real.log_le_log hβout_pos hβle)
          (le_of_lt (Real.log_pos one_lt_two))
      have hrel :
          ρ.hypothesisTestingRelativeEntropyFinite σ ε ≤
            ρ'.hypothesisTestingRelativeEntropyFinite σ' ε := by
        rw [hypothesisTestingRelativeEntropyFinite_eq, hypothesisTestingRelativeEntropyFinite_eq]
        exact neg_le_neg hlog
      have hrelE :
          (ρ.hypothesisTestingRelativeEntropyFinite σ ε : EReal) ≤
            (ρ'.hypothesisTestingRelativeEntropyFinite σ' ε : EReal) := by
        exact_mod_cast hrel
      simpa [hypothesisTestingRelativeEntropy, hβin_zero, hβout_zero, ρ', σ']
        using hrelE

theorem hypothesisTestingBeta_le_applyState
    (Φ : CPTPMap a b) (ρ σ : MState a) (ε : ℝ) (hε : 0 ≤ ε) :
    ρ.hypothesisTestingBeta σ ε ≤
      MState.hypothesisTestingBeta (Φ ρ) (Φ σ) ε := by
  rw [hypothesisTestingBeta_eq_sInf]
  refine le_csInf
    (MState.hypothesisTestingBetaCandidateSet_nonempty_of_nonneg (Φ ρ)
      (Φ σ) ε hε) ?_
  intro β hβ
  rcases hβ with ⟨Λ, rfl⟩
  have hle :=
    ρ.hypothesisTestingBeta_le_of_effect σ ε
      (Φ.pullbackHypothesisTestingEffect ρ ε Λ)
  rw [Φ.pullbackHypothesisTestingEffect_typeIIError ρ σ ε Λ] at hle
  exact hle

theorem hypothesisTestingRelativeEntropy_applyState_le
    (Φ : CPTPMap a b) (ρ σ : MState a) (ε : ℝ) (hε : 0 ≤ ε) :
    MState.hypothesisTestingRelativeEntropy (Φ ρ) (Φ σ) ε ≤
      ρ.hypothesisTestingRelativeEntropy σ ε := by
  have hβle := ρ.hypothesisTestingBeta_le_applyState Φ σ ε hε
  by_cases hβin_zero : ρ.hypothesisTestingBeta σ ε = 0
  · simp [hypothesisTestingRelativeEntropy, hβin_zero]
  · have hβin_nonneg := ρ.hypothesisTestingBeta_nonneg σ ε hε
    have hβin_pos : 0 < ρ.hypothesisTestingBeta σ ε :=
      lt_of_le_of_ne' hβin_nonneg hβin_zero
    have hβout_pos :
        0 < MState.hypothesisTestingBeta (Φ ρ) (Φ σ) ε :=
      lt_of_lt_of_le hβin_pos hβle
    have hβout_zero :
        MState.hypothesisTestingBeta (Φ ρ) (Φ σ) ε ≠ 0 :=
      ne_of_gt hβout_pos
    have hlog :
        log2 (ρ.hypothesisTestingBeta σ ε) ≤
          log2 (MState.hypothesisTestingBeta (Φ ρ) (Φ σ) ε) := by
      unfold log2
      exact div_le_div_of_nonneg_right
        (Real.log_le_log hβin_pos hβle) (le_of_lt (Real.log_pos one_lt_two))
    have hrel :
        MState.hypothesisTestingRelativeEntropyFinite (Φ ρ) (Φ σ) ε ≤
          ρ.hypothesisTestingRelativeEntropyFinite σ ε := by
      rw [hypothesisTestingRelativeEntropyFinite_eq, hypothesisTestingRelativeEntropyFinite_eq]
      exact neg_le_neg hlog
    have hrelE :
        (MState.hypothesisTestingRelativeEntropyFinite (Φ ρ)
          (Φ σ) ε : EReal) ≤
            (ρ.hypothesisTestingRelativeEntropyFinite σ ε : EReal) := by
      exact_mod_cast hrel
    simpa [hypothesisTestingRelativeEntropy, hβin_zero, hβout_zero] using hrelE

/-- Optimized extended-real hypothesis-testing mutual information does not
decrease when the first/reference register is embedded by an isometry. -/
theorem hypothesisTestingMutualInformation_le_applyReferenceIsometry
    {r₁ : Type x} {r₂ : Type y} [Fintype r₁] [DecidableEq r₁]
    [Fintype r₂] [DecidableEq r₂]
    (V : ReferenceIsometry r₁ r₂) (ρ : MState (r₁ × a))
    (ε : ℝ) (hε : 0 ≤ ε) :
    ρ.hypothesisTestingMutualInformation ε ≤
      MState.hypothesisTestingMutualInformation
        (((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := a))) ρ)
        ε := by
  let ρ' : MState (r₂ × a) :=
    ((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := a))) ρ
  rw [hypothesisTestingMutualInformation_eq_sInf]
  refine le_sInf ?_
  intro value hvalue
  rcases hvalue with ⟨σA, rfl⟩
  have hinMem :
      ρ.hypothesisTestingRelativeEntropy (ρ.traceRight.prod σA) ε ∈
        hypothesisTestingMutualInformationCandidateSet (a := r₁) (b := a) ρ ε := by
    exact ⟨σA, rfl⟩
  have hinLe :
      ρ.hypothesisTestingMutualInformation ε ≤
        ρ.hypothesisTestingRelativeEntropy (ρ.traceRight.prod σA) ε := by
    rw [hypothesisTestingMutualInformation_eq_sInf]
    exact sInf_le hinMem
  have hprod :
      ρ'.traceRight.prod σA =
        ((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := a)))
          (ρ.traceRight.prod σA) := by
    simp [ρ', traceRight_applyState_prod_id]
  have hD :
      ρ.hypothesisTestingRelativeEntropy (ρ.traceRight.prod σA) ε ≤
        ρ'.hypothesisTestingRelativeEntropy (ρ'.traceRight.prod σA) ε := by
    simpa [ρ', hprod] using
      hypothesisTestingRelativeEntropy_le_applyReferenceIsometry
        V ρ (ρ.traceRight.prod σA) ε hε
  exact hinLe.trans hD

/-- Optimized hypothesis-testing mutual information is monotone under local
post-processing on the second register, in the extended-real convention. -/
theorem hypothesisTestingMutualInformation_dataProcessing_right
    (ρ : MState (a × b)) (D : CPTPMap b c) (ε : ℝ) (hε : 0 ≤ ε) :
    MState.hypothesisTestingMutualInformation (((CPTPOp.id (dIn := a)).prod D) ρ) ε ≤
      ρ.hypothesisTestingMutualInformation ε := by
  let ρ' : MState (a × c) := ((CPTPOp.id (dIn := a)).prod D) ρ
  rw [hypothesisTestingMutualInformation_eq_sInf]
  refine le_sInf ?_
  intro value hvalue
  rcases hvalue with ⟨σB, rfl⟩
  have hρAmarg : ρ'.traceRight = ρ.traceRight := by
    exact traceRight_applyState_id_prod ρ D
  have hprod :
      ρ'.traceRight.prod (D σB) =
        ((CPTPOp.id (dIn := a)).prod D) (ρ.traceRight.prod σB) := by
    rw [hρAmarg]
    exact (MState.applyState_id_prod_prod ρ.traceRight σB D).symm
  have houtMem :
      ρ'.hypothesisTestingRelativeEntropy
          (ρ'.traceRight.prod (D σB)) ε ∈
        hypothesisTestingMutualInformationCandidateSet (a := a) (b := c) ρ' ε := by
    exact ⟨D σB, rfl⟩
  have houtLe :
      ρ'.hypothesisTestingMutualInformation ε ≤
        ρ'.hypothesisTestingRelativeEntropy
          (ρ'.traceRight.prod (D σB)) ε := by
    rw [hypothesisTestingMutualInformation_eq_sInf]
    exact sInf_le houtMem
  have hDPI :
      ρ'.hypothesisTestingRelativeEntropy
          (((CPTPOp.id (dIn := a)).prod D) (ρ.traceRight.prod σB)) ε ≤
        ρ.hypothesisTestingRelativeEntropy (ρ.traceRight.prod σB) ε := by
    exact hypothesisTestingRelativeEntropy_applyState_le
      ((CPTPOp.id (dIn := a)).prod D) ρ (ρ.traceRight.prod σB) ε hε
  exact houtLe.trans (by simpa [hprod] using hDPI)

/-- Optimized hypothesis-testing mutual information is monotone under local
post-processing on the first register, in the extended-real convention. -/
theorem hypothesisTestingMutualInformation_dataProcessing_left
    (ρ : MState (a × b)) (D : CPTPMap a c) (ε : ℝ) (hε : 0 ≤ ε) :
    MState.hypothesisTestingMutualInformation ((D.prod (CPTPOp.id (dIn := b))) ρ) ε ≤
      ρ.hypothesisTestingMutualInformation ε := by
  let ρ' : MState (c × b) := (D.prod (CPTPOp.id (dIn := b))) ρ
  rw [hypothesisTestingMutualInformation_eq_sInf]
  refine le_sInf ?_
  intro value hvalue
  rcases hvalue with ⟨σB, rfl⟩
  have hρAmarg : ρ'.traceRight = D ρ.traceRight := by
    apply MState.ext
    simp only [ρ', MState.traceRight_m, CPTPOp.mat_coe_eq_apply_mat,
      CPTPOp.prod_map]
    change Matrix.traceRight
        (MatrixMap.kron D.map (CPTPOp.id (dIn := b)).map ρ.m) =
      D.map (Matrix.traceRight ρ.m)
    ext i i'
    simp only [Matrix.traceRight, Matrix.of_apply]
    let S : b → CMatrix a := fun j => Matrix.of fun x x' => ρ.m (x, j) (x', j)
    have hsum :
        (fun x x' => ∑ j : b, ρ.m (x, j) (x', j)) =
          ∑ j : b, S j := by
      ext x x'
      simp only [Matrix.sum_apply]
      rfl
    change (∑ j : b,
        MatrixMap.kron D.map (CPTPOp.id (dIn := b)).map ρ.m (i, j) (i', j)) =
      D.map (fun x x' => ∑ j : b, ρ.m (x, j) (x', j)) i i'
    rw [hsum, map_sum]
    simp only [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact MatrixMap.kron_idChannel_apply_slice (a := a) (b := c) (r := b)
      (Φ := D.map) (X := ρ.m) (br := (i, j)) (br' := (i', j))
  have hprod :
      ρ'.traceRight.prod σB =
        (D.prod (CPTPOp.id (dIn := b))) (ρ.traceRight.prod σB) := by
    rw [hρAmarg]
    exact (MState.applyState_prod_id_prod ρ.traceRight σB D).symm
  have houtMem :
      ρ'.hypothesisTestingRelativeEntropy (ρ'.traceRight.prod σB) ε ∈
        hypothesisTestingMutualInformationCandidateSet (a := c) (b := b) ρ' ε := by
    exact ⟨σB, rfl⟩
  have houtLe :
      ρ'.hypothesisTestingMutualInformation ε ≤
        ρ'.hypothesisTestingRelativeEntropy (ρ'.traceRight.prod σB) ε := by
    rw [hypothesisTestingMutualInformation_eq_sInf]
    exact sInf_le houtMem
  have hDPI :
      ρ'.hypothesisTestingRelativeEntropy
          ((D.prod (CPTPOp.id (dIn := b))) (ρ.traceRight.prod σB)) ε ≤
        ρ.hypothesisTestingRelativeEntropy (ρ.traceRight.prod σB) ε := by
    exact hypothesisTestingRelativeEntropy_applyState_le
      (D.prod (CPTPOp.id (dIn := b))) ρ (ρ.traceRight.prod σB) ε hε
  exact houtLe.trans (by simpa [hprod] using hDPI)

/-- Repartition `(M × E) × B` as `M × (B × E)`, moving side information
from the reference block to the output block while preserving the message
register as the first factor. -/
def messageOutputSideInfoEquiv
    (m e b : Type*) : ((m × e) × b) ≃ (m × (b × e)) :=
  (Equiv.prodAssoc m e b).trans
    (Equiv.prodCongr (Equiv.refl m) (Equiv.prodComm e b))

private theorem traceRight_reindex_messageOutputSideInfoEquiv
    {m e b : Type*} [Fintype m] [DecidableEq m]
    [Fintype e] [DecidableEq e] [Fintype b] [DecidableEq b]
    (θ : MState ((m × e) × b)) :
    (θ.reindex (messageOutputSideInfoEquiv m e b)).traceRight =
      θ.traceRight.traceRight := by
  apply MState.ext
  ext i j
  simp only [MState.traceRight_m, MState.reindex_matrix]
  change
    (∑ x : b × e, θ.m
      ((messageOutputSideInfoEquiv m e b).symm (i, x))
      ((messageOutputSideInfoEquiv m e b).symm (j, x))) =
    ∑ x : e, Matrix.traceRight θ.m (i, x) (j, x)
  rw [Fintype.sum_prod_type]
  simp [messageOutputSideInfoEquiv, Matrix.traceRight]
  rw [Finset.sum_comm]

private theorem product_reference_reindex_messageOutputSideInfoEquiv
    {m e b : Type*} [Fintype m] [DecidableEq m]
    [Fintype e] [DecidableEq e] [Fintype b] [DecidableEq b]
    (θME : MState (m × e)) (σB : MState b)
    (hprod : θME = θME.traceRight.prod θME.traceLeft) :
    (θME.prod σB).reindex (messageOutputSideInfoEquiv m e b) =
      θME.traceRight.prod (σB.prod θME.traceLeft) := by
  apply MState.ext
  ext x y
  rcases x with ⟨xm, xb, xe⟩
  rcases y with ⟨ym, yb, ye⟩
  have hentry :=
    congrFun (congrFun (congrArg DensityOp.m hprod) (xm, xe)) (ym, ye)
  simp [MState.reindex_matrix, messageOutputSideInfoEquiv, hentry, mul_assoc, mul_comm]

theorem hypothesisTestingMutualInformation_repartition_le_of_traceRight_eq_prod
    {m e b : Type*} [Fintype m] [DecidableEq m]
    [Fintype e] [DecidableEq e] [Fintype b] [DecidableEq b]
    (θ : MState ((m × e) × b)) (ε : ℝ) (hε : 0 ≤ ε)
    (hprod : θ.traceRight = θ.traceRight.traceRight.prod θ.traceRight.traceLeft) :
    ((θ.reindex (messageOutputSideInfoEquiv m e b)).hypothesisTestingMutualInformation ε) ≤
      θ.hypothesisTestingMutualInformation ε := by
  let θ' : MState (m × (b × e)) :=
    θ.reindex (messageOutputSideInfoEquiv m e b)
  rw [hypothesisTestingMutualInformation_eq_sInf]
  refine le_sInf ?_
  intro value hvalue
  rcases hvalue with ⟨σB, rfl⟩
  let σBE : MState (b × e) := σB.prod θ.traceRight.traceLeft
  have houtMem :
      θ'.hypothesisTestingRelativeEntropy (θ'.traceRight.prod σBE) ε ∈
        hypothesisTestingMutualInformationCandidateSet
          (a := m) (b := b × e) θ' ε := by
    exact ⟨σBE, rfl⟩
  have houtLe :
      θ'.hypothesisTestingMutualInformation ε ≤
        θ'.hypothesisTestingRelativeEntropy (θ'.traceRight.prod σBE) ε := by
    rw [hypothesisTestingMutualInformation_eq_sInf]
    exact sInf_le houtMem
  have hmarg : θ'.traceRight = θ.traceRight.traceRight := by
    simpa [θ'] using traceRight_reindex_messageOutputSideInfoEquiv θ
  have hprodState :
      θ'.traceRight.prod σBE =
        (θ.traceRight.prod σB).reindex (messageOutputSideInfoEquiv m e b) := by
    rw [hmarg]
    exact (product_reference_reindex_messageOutputSideInfoEquiv
      θ.traceRight σB hprod).symm
  have hD :
      θ'.hypothesisTestingRelativeEntropy
          ((θ.traceRight.prod σB).reindex (messageOutputSideInfoEquiv m e b)) ε =
        θ.hypothesisTestingRelativeEntropy (θ.traceRight.prod σB) ε := by
    simpa [θ'] using
      hypothesisTestingRelativeEntropy_reindex θ (θ.traceRight.prod σB) ε hε
        (messageOutputSideInfoEquiv m e b)
  exact houtLe.trans (by simpa [hprodState] using le_of_eq hD)

end MState

end

noncomputable section

namespace CPTPOp

open QIT

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

/-- If a bipartite state is obtained from a channel output by local
post-processing on the output register, then its optimized extended-real
hypothesis-testing mutual information is bounded by the channel quantity.

This is the reusable channel-optimization bridge for converse arguments once a
protocol-specific construction has represented the relevant state as a
post-processed output for a pure input with the canonical input-copy reference. -/
theorem hypothesisTestingMutualInformation_postprocess_output_le_channel
    (N : CPTPMap a b) (D : CPTPMap b c) (ψ : Ket (a × a))
    (ε : ℝ) (hε : 0 ≤ ε) :
    MState.hypothesisTestingMutualInformation (((CPTPOp.id (dIn := a)).prod D)
        (N.hypothesisTestingOutputState ψ)) ε ≤
      N.hypothesisTestingMutualInformation ε := by
  exact (MState.hypothesisTestingMutualInformation_dataProcessing_right
    (N.hypothesisTestingOutputState ψ) D ε hε).trans
      (N.inputHypothesisTestingMutualInformation_le_channel ε ψ)

/-- Equality-shaped version of
`hypothesisTestingMutualInformation_postprocess_output_le_channel`, useful when
the protocol state has first been identified with a post-processed channel
output. -/
theorem hypothesisTestingMutualInformation_le_channel_of_eq_postprocess_output
    (N : CPTPMap a b) (D : CPTPMap b c) (ψ : Ket (a × a))
    (ω : MState (a × c)) (ε : ℝ) (hε : 0 ≤ ε)
    (hω : ω =
      ((CPTPOp.id (dIn := a)).prod D)
        (N.hypothesisTestingOutputState ψ)) :
    ω.hypothesisTestingMutualInformation ε ≤
      N.hypothesisTestingMutualInformation ε := by
  rw [hω]
  exact N.hypothesisTestingMutualInformation_postprocess_output_le_channel D ψ ε hε

variable {r₁ : Type x} {r₂ : Type y}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]

/-- A reference isometry commutes with applying the communication channel on
the target/input register. -/
theorem hypothesisTestingOutputState_applyReferenceIsometry
    (N : CPTPMap a b) (V : ReferenceIsometry r₁ r₂)
    (ψ : Ket (r₁ × a)) :
    N.hypothesisTestingOutputState (V.applyKet ψ) =
      ((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := b)))
        (N.hypothesisTestingOutputState ψ) := by
  apply MState.ext
  rw [CPTPOp.hypothesisTestingOutputState_matrix, CPTPOp.mat_coe_eq_apply_mat,
    CPTPOp.hypothesisTestingOutputState_matrix, CPTPOp.prod_map]
  change MatrixMap.kron (CPTPOp.id (dIn := r₂)).map N.map
      (V.applyKet ψ).state.m =
    MatrixMap.kron (CPTPOp.ofReferenceIsometry V).map
      (CPTPOp.id (dIn := b)).map
      (MatrixMap.kron (CPTPOp.id (dIn := r₁)).map N.map ψ.state.m)
  have hVstate :
      (V.applyKet ψ).state.m =
        V.applyMatrix ψ.state.m := by
    rw [Ket.state_matrix, Ket.state_matrix]
    exact V.rankOne_applyAmp ψ.vec
  rw [hVstate]
  rw [CPTPOp.ofReferenceIsometry_map]
  rw [MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft]
  exact MatrixMap.kron_idChannel_left_apply_applyMatrix N.map V ψ.state.m

/-- Arbitrary-reference pure inputs whose reference system contains an
input-copy reference are bounded by the channel extended-real
hypothesis-testing mutual information. -/
theorem inputHypothesisTestingMutualInformation_le_channel_of_card_le
    (N : CPTPMap a b) {r : Type w} [Fintype r] [DecidableEq r]
    (ψ : Ket (r × a)) (ε : ℝ) (hε : 0 ≤ ε)
    (hcard : Fintype.card a ≤ Fintype.card r) :
    N.inputHypothesisTestingMutualInformation ψ ε ≤
      N.hypothesisTestingMutualInformation ε := by
  let φ : Ket (a × a) := ψ.state.traceLeft.canonicalPurification
  have hφ : φ.Purifies ψ.state.traceLeft := by
    exact ψ.state.traceLeft.canonicalPurification_purifies
  have hψ : ψ.Purifies ψ.state.traceLeft :=
    ψ.purifies_traceLeft
  rcases Ket.exists_referenceIsometry_applyKet_eq_of_purifies_same_state
      hφ hψ hcard with ⟨V, hV⟩
  have hout :
      N.hypothesisTestingOutputState ψ =
        ((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := b)))
          (N.hypothesisTestingOutputState φ) := by
    rw [hV]
    exact N.hypothesisTestingOutputState_applyReferenceIsometry V φ
  rw [inputHypothesisTestingMutualInformation, hout]
  exact (MState.hypothesisTestingMutualInformation_dataProcessing_left
      (N.hypothesisTestingOutputState φ) (CPTPOp.ofReferenceIsometry V) ε hε).trans
    (N.inputHypothesisTestingMutualInformation_le_channel ε φ)

/-- Arbitrary-reference pure inputs are bounded by the channel optimized
extended-real hypothesis-testing mutual information.  The proof pads the
reference by an isometric embedding, uses the sufficiently-large-reference
purification bridge, and transports the hypothesis-testing mutual information
back along the isometry. -/
theorem inputHypothesisTestingMutualInformation_le_channel_of_arbitrary_reference
    (N : CPTPMap a b) {r : Type w} [Fintype r] [DecidableEq r]
    (ψ : Ket (r × a)) (ε : ℝ) (hε : 0 ≤ ε) :
    N.inputHypothesisTestingMutualInformation ψ ε ≤
      N.hypothesisTestingMutualInformation ε := by
  let V : ReferenceIsometry r (a ⊕ r) :=
    ReferenceIsometry.sumInr a r
  let ψ' : Ket ((a ⊕ r) × a) := V.applyKet ψ
  have hlarge : Fintype.card a ≤ Fintype.card (a ⊕ r) := by
    rw [Fintype.card_sum]
    exact Nat.le_add_right _ _
  have hleft :
      N.inputHypothesisTestingMutualInformation ψ ε ≤
        N.inputHypothesisTestingMutualInformation ψ' ε := by
    unfold inputHypothesisTestingMutualInformation
    rw [N.hypothesisTestingOutputState_applyReferenceIsometry V ψ]
    exact MState.hypothesisTestingMutualInformation_le_applyReferenceIsometry
      V (N.hypothesisTestingOutputState ψ) ε hε
  have hright :
      N.inputHypothesisTestingMutualInformation ψ' ε ≤
        N.hypothesisTestingMutualInformation ε := by
    exact N.inputHypothesisTestingMutualInformation_le_channel_of_card_le
      ψ' ε hε hlarge
  exact hleft.trans hright

/-- A pure channel output remains bounded by the channel optimized
extended-real hypothesis-testing mutual information after arbitrary local
post-processing on the reference register.

This is the source-shaped bridge used by meta-converse arguments: once a
protocol state is identified as a reference-side post-processing of a pure
input-reference channel output, data processing reduces it to the channel
quantity `I_H^ε(N)`.
-/
theorem hypothesisTestingMutualInformation_referencePostprocess_output_le_channel
    (N : CPTPMap a b) {r : Type w} [Fintype r] [DecidableEq r]
    {s : Type x} [Fintype s] [DecidableEq s]
    (D : CPTPMap r s) (ψ : Ket (r × a)) (ε : ℝ) (hε : 0 ≤ ε) :
    (MState.hypothesisTestingMutualInformation ((D.prod (CPTPOp.id (dIn := b)))
        (N.hypothesisTestingOutputState ψ)) ε) ≤
      N.hypothesisTestingMutualInformation ε := by
  exact (MState.hypothesisTestingMutualInformation_dataProcessing_left
      (N.hypothesisTestingOutputState ψ) D ε hε).trans
    (N.inputHypothesisTestingMutualInformation_le_channel_of_arbitrary_reference ψ ε hε)

/-- Equality-shaped version of
`hypothesisTestingMutualInformation_referencePostprocess_output_le_channel`,
for protocol constructions that first identify the tested state with a
reference-side post-processing of a pure channel output. -/
theorem hypothesisTestingMutualInformation_le_channel_of_eq_referencePostprocess_output
    (N : CPTPMap a b) {r : Type w} [Fintype r] [DecidableEq r]
    {s : Type x} [Fintype s] [DecidableEq s]
    (D : CPTPMap r s) (ψ : Ket (r × a)) (ω : MState (s × b))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hω : ω =
      (D.prod (CPTPOp.id (dIn := b))) (N.hypothesisTestingOutputState ψ)) :
    ω.hypothesisTestingMutualInformation ε ≤
      N.hypothesisTestingMutualInformation ε := by
  rw [hω]
  exact N.hypothesisTestingMutualInformation_referencePostprocess_output_le_channel
    D ψ ε hε

set_option maxRecDepth 4000 in
/-- Mixed input-reference states are also bounded by the channel optimized
extended-real hypothesis-testing mutual information.

The proof purifies the mixed input-reference state, traces out the extra
purifying reference after the channel use, and then applies reference-side data
processing together with the arbitrary-reference pure-input optimization
bridge. -/
theorem mixedInputOutput_hypothesisTestingMutualInformation_le_channel
    (N : CPTPMap a b) {r : Type w} [Fintype r] [DecidableEq r]
    (ρ : MState (r × a)) (ε : ℝ) (hε : 0 ≤ ε) :
    MState.hypothesisTestingMutualInformation (((CPTPOp.id (dIn := r)).prod N) ρ) ε ≤
      N.hypothesisTestingMutualInformation ε := by
  let ψ : Ket (((r × a) × r) × a) :=
    ρ.purifiedInputForHypothesisTestingDPI
  let D : CPTPMap ((r × a) × r) r :=
    CPTPOp.traceOutLeft (r × a) r
  have hstate :
      (D.prod (CPTPOp.id (dIn := b))) (N.hypothesisTestingOutputState ψ) =
        ((CPTPOp.id (dIn := r)).prod N) ρ := by
    calc
      (D.prod (CPTPOp.id (dIn := b))) (N.hypothesisTestingOutputState ψ) =
        (D.prod (CPTPOp.id (dIn := b)))
          (((CPTPOp.id (dIn := (r × a) × r)).prod N) ψ.state) := by
          simp only [CPTPOp.hypothesisTestingOutputState]
      _ = ((CPTPOp.id (dIn := r)).prod N)
          (((D.prod (CPTPOp.id (dIn := a))) ψ.state)) := by
          exact CPTPOp.traceOutLeft_prod_id_applyState_id_prod
            (p := r × a) (r := r) (a := a) (b := b) N ψ.state
      _ = ((CPTPOp.id (dIn := r)).prod N) ρ := by
          rw [MState.traceOut_purifiedInputForHypothesisTestingDPI]
  rw [← hstate]
  exact N.hypothesisTestingMutualInformation_referencePostprocess_output_le_channel
    D ψ ε hε

end CPTPOp

end
