/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.HypothesisTesting.ComparatorTest
public import QIT.Channels.Diamond
public import QIT.States.Purification.Equivalence
public import QIT.States.Purification.Canonical
import QIT.States.Purification.Uhlmann
public import QIT.States.Purification.ReferenceIsometry

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

namespace QIT

universe u v w x y

noncomputable section

namespace ReferenceIsometry

variable {a : Type u}
variable [Fintype a] [DecidableEq a]
variable {r₁ : Type x} {r₂ : Type y}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]

theorem applyMatrix_sub (V : ReferenceIsometry r₁ r₂)
    (X Y : CMatrix (Prod r₁ a)) :
    V.applyMatrix (X - Y) = V.applyMatrix X - V.applyMatrix Y := by
  rw [← MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft V (X - Y)]
  rw [map_sub]
  rw [MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft V X]
  rw [MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft V Y]

theorem applyMatrix_posSemidef (V : ReferenceIsometry r₁ r₂)
    {X : CMatrix (Prod r₁ a)} (hX : X.PosSemidef) :
    (V.applyMatrix X).PosSemidef := by
  have hCP :
      MatrixMap.IsCompletelyPositive
        (MatrixMap.kron (MatrixMap.ofReferenceIsometry V)
          (Channel.idChannel a).map) := by
    exact MatrixMap.isCompletelyPositive_kron
      (MatrixMap.ofReferenceIsometry V) (Channel.idChannel a).map
      (MatrixMap.ofReferenceIsometry_isCompletelyPositive V)
      (Channel.idChannel a).completelyPositive
  have hpos :=
    MatrixMap.isCompletelyPositive_mapsPositive
      (MatrixMap.kron (MatrixMap.ofReferenceIsometry V)
        (Channel.idChannel a).map) hCP X hX
  simpa [MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft V X]
    using hpos

omit [DecidableEq a] [DecidableEq r₁] in theorem targetBlock_mul (X Y : CMatrix (Prod r₁ a)) (i j : a) :
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
    (X Y : CMatrix (Prod r₁ a)) :
    V.applyMatrix X * V.applyMatrix Y = V.applyMatrix (X * Y) := by
  ext p q
  calc
    (V.applyMatrix X * V.applyMatrix Y) p q =
        (∑ k : a,
          ((V.matrix * targetBlock X p.2 k * Matrix.conjTranspose V.matrix) *
            (V.matrix * targetBlock Y k q.2 * Matrix.conjTranspose V.matrix)) p.1 q.1) := by
      change (∑ j : Prod r₂ a, V.applyMatrix X p j * V.applyMatrix Y j q) =
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
    V.applyMatrix (1 : CMatrix (Prod r₁ a)) *
      V.applyMatrix (1 : CMatrix (Prod r₁ a)) =
        V.applyMatrix (1 : CMatrix (Prod r₁ a)) := by
  rw [V.applyMatrix_mul, Matrix.mul_one]

theorem one_sub_applyMatrix_one_posSemidef (V : ReferenceIsometry r₁ r₂) :
    (1 - V.applyMatrix (1 : CMatrix (Prod r₁ a))).PosSemidef := by
  exact MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent
    (V.applyMatrix (1 : CMatrix (Prod r₁ a)))
    (V.applyMatrix_posSemidef Matrix.PosSemidef.one)
    (V.applyMatrix_one_idempotent (a := a))

theorem applyMatrix_le_one_of_le_one (V : ReferenceIsometry r₁ r₂)
    {E : CMatrix (Prod r₁ a)} (hE : E ≤ 1) :
    V.applyMatrix E ≤ 1 := by
  rw [Matrix.le_iff]
  have hEsub : (1 - E).PosSemidef := by
    simpa [Matrix.le_iff] using hE
  have himageSub :
      (V.applyMatrix ((1 : CMatrix (Prod r₁ a)) - E)).PosSemidef :=
    V.applyMatrix_posSemidef hEsub
  have hdecomp :
      (1 : CMatrix (Prod r₂ a)) - V.applyMatrix E =
        (1 - V.applyMatrix (1 : CMatrix (Prod r₁ a))) +
          V.applyMatrix ((1 : CMatrix (Prod r₁ a)) - E) := by
    rw [V.applyMatrix_sub]
    abel
  rw [hdecomp]
  exact Matrix.PosSemidef.add
    (V.one_sub_applyMatrix_one_posSemidef (a := a)) himageSub

omit [DecidableEq a] in theorem trace_applyMatrix_mul_applyMatrix (V : ReferenceIsometry r₁ r₂)
    (X Y : CMatrix (Prod r₁ a)) :
    ((V.applyMatrix X * V.applyMatrix Y).trace) = (X * Y).trace := by
  rw [V.applyMatrix_mul, V.trace_applyMatrix]

end ReferenceIsometry

namespace Channel

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem effectAcceptProbability_applyState_dualEffect
    (Φ : Channel a b) (ρ : State a) (E : CMatrix b) :
    effectAcceptProbability (Φ.applyState ρ) E =
      effectAcceptProbability ρ (Φ.dualEffect E) := by
  unfold effectAcceptProbability
  rw [Φ.applyState_dualEffect_trace ρ E]

/-- Pull back a feasible output hypothesis-testing effect along a channel. -/
def pullbackHypothesisTestingEffect
    (Φ : Channel a b) (ρ : State a) (ε : ℝ)
    (Λ : HypothesisTestingEffect (Φ.applyState ρ) ε) :
    HypothesisTestingEffect ρ ε where
  effect := Φ.dualEffect Λ.effect
  pos := Φ.dualEffect_posSemidef Λ.pos
  le_one := Φ.dualEffect_le_one_of_le_one Λ.le_one
  accept_ge := by
    rw [← Φ.effectAcceptProbability_applyState_dualEffect ρ Λ.effect]
    exact Λ.accept_ge

@[simp]
theorem pullbackHypothesisTestingEffect_typeIIError
    (Φ : Channel a b) (ρ σ : State a) (ε : ℝ)
    (Λ : HypothesisTestingEffect (Φ.applyState ρ) ε) :
    (Φ.pullbackHypothesisTestingEffect ρ ε Λ).typeIIError σ =
      Λ.typeIIError (Φ.applyState σ) := by
  unfold pullbackHypothesisTestingEffect HypothesisTestingEffect.typeIIError
    effectTypeIIError
  rw [← Φ.effectAcceptProbability_applyState_dualEffect σ Λ.effect]

end Channel

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
    (V : ReferenceIsometry r₁ r₂) (ρ : State (Prod r₁ a)) (ε : ℝ)
    (Λ : HypothesisTestingEffect ρ ε) :
    HypothesisTestingEffect
      (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState ρ) ε where
  effect := V.applyMatrix Λ.effect
  pos := V.applyMatrix_posSemidef Λ.pos
  le_one := V.applyMatrix_le_one_of_le_one Λ.le_one
  accept_ge := by
    simpa [effectAcceptProbability, Channel.ofReferenceIsometry_prod_id_applyState_matrix,
      V.trace_applyMatrix_mul_applyMatrix] using Λ.accept_ge

@[simp]
theorem pushForwardHypothesisTestingEffect_typeIIError
    (V : ReferenceIsometry r₁ r₂) (ρ σ : State (Prod r₁ a)) (ε : ℝ)
    (Λ : HypothesisTestingEffect ρ ε) :
    (V.pushForwardHypothesisTestingEffect ρ ε Λ).typeIIError
      (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState σ) =
      Λ.typeIIError σ := by
  simp [pushForwardHypothesisTestingEffect, HypothesisTestingEffect.typeIIError,
    effectTypeIIError, effectAcceptProbability,
    Channel.ofReferenceIsometry_prod_id_applyState_matrix,
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
variable {ρ σ : State α} {ε : ℝ}

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
    change 1 - ε ≤
      (((ρ.matrix.submatrix e.symm e.symm) *
        (Λ.effect.submatrix e.symm e.symm)).trace).re
    rw [trace_reindex_mul_reindex e ρ.matrix Λ.effect]
    exact Λ.accept_ge

@[simp]
theorem reindex_typeIIError (Λ : HypothesisTestingEffect ρ ε)
    (e : α ≃ β) :
    (Λ.reindex e).typeIIError (σ.reindex e) = Λ.typeIIError σ := by
  unfold HypothesisTestingEffect.typeIIError effectTypeIIError effectAcceptProbability
  change (((σ.matrix.submatrix e.symm e.symm) *
      (Λ.effect.submatrix e.symm e.symm)).trace).re =
    ((σ.matrix * Λ.effect).trace).re
  rw [trace_reindex_mul_reindex e σ.matrix Λ.effect]

end HypothesisTestingEffect

namespace State

private theorem reindex_symm_reindex_forHypothesisTestingDPI
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (ρ : State α) (e : α ≃ β) :
    (ρ.reindex e).reindex e.symm = ρ := by
  apply State.ext
  ext i j
  simp [State.reindex]

theorem hypothesisTestingBeta_nonneg_of_epsilon_nonneg
    (ρ σ : State a) (ε : ℝ) (hε : 0 ≤ ε) :
    0 ≤ ρ.hypothesisTestingBeta σ ε := by
  rw [hypothesisTestingBeta_eq_sInf]
  refine le_csInf (ρ.hypothesisTestingBetaCandidateSet_nonempty_of_nonneg σ ε hε) ?_
  intro β hβ
  rcases hβ with ⟨Λ, rfl⟩
  exact Λ.typeIIError_nonneg

theorem hypothesisTestingBeta_reindex_le
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ρ σ : State α) (ε : ℝ) (hε : 0 ≤ ε) (e : α ≃ β) :
    (ρ.reindex e).hypothesisTestingBeta (σ.reindex e) ε ≤
      ρ.hypothesisTestingBeta σ ε := by
  change (ρ.reindex e).hypothesisTestingBeta (σ.reindex e) ε ≤
    sInf (ρ.hypothesisTestingBetaCandidateSet σ ε)
  refine le_csInf (ρ.hypothesisTestingBetaCandidateSet_nonempty_of_nonneg σ ε hε) ?_
  intro β hβ
  rcases hβ with ⟨Λ, rfl⟩
  have hle :=
    State.hypothesisTestingBeta_le_of_effect
      (ρ.reindex e) (σ.reindex e) ε (Λ.reindex e)
  rw [HypothesisTestingEffect.reindex_typeIIError Λ e] at hle
  exact hle

theorem hypothesisTestingBeta_le_reindex
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ρ σ : State α) (ε : ℝ) (hε : 0 ≤ ε) (e : α ≃ β) :
    ρ.hypothesisTestingBeta σ ε ≤
      (ρ.reindex e).hypothesisTestingBeta (σ.reindex e) ε := by
  have h :=
    hypothesisTestingBeta_reindex_le (ρ.reindex e) (σ.reindex e) ε hε e.symm
  simpa [reindex_symm_reindex_forHypothesisTestingDPI] using h

theorem hypothesisTestingBeta_reindex
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ρ σ : State α) (ε : ℝ) (hε : 0 ≤ ε) (e : α ≃ β) :
    (ρ.reindex e).hypothesisTestingBeta (σ.reindex e) ε =
      ρ.hypothesisTestingBeta σ ε :=
  le_antisymm (hypothesisTestingBeta_reindex_le ρ σ ε hε e)
    (hypothesisTestingBeta_le_reindex ρ σ ε hε e)

theorem hypothesisTestingRelativeEntropyFinite_reindex
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ρ σ : State α) (ε : ℝ) (hε : 0 ≤ ε) (e : α ≃ β) :
    (ρ.reindex e).hypothesisTestingRelativeEntropyFinite (σ.reindex e) ε =
      ρ.hypothesisTestingRelativeEntropyFinite σ ε := by
  rw [hypothesisTestingRelativeEntropyFinite_eq, hypothesisTestingRelativeEntropyFinite_eq,
    hypothesisTestingBeta_reindex ρ σ ε hε e]

theorem hypothesisTestingRelativeEntropy_reindex
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ρ σ : State α) (ε : ℝ) (hε : 0 ≤ ε) (e : α ≃ β) :
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
    (ρ : State α) (σ : State γ) (e : α ≃ β) (f : γ ≃ δ) :
    (ρ.prod σ).reindex (Equiv.prodCongr e f) =
      (ρ.reindex e).prod (σ.reindex f) := by
  apply State.ext
  ext i j
  simp [State.reindex, State.prod, Matrix.kronecker]

theorem hypothesisTestingMutualInformation_reindex_prodCongr_le
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (ρ : State (Prod α γ)) (ε : ℝ) (hε : 0 ≤ ε)
    (e : α ≃ β) (f : γ ≃ δ) :
    (ρ.reindex (Equiv.prodCongr e f)).hypothesisTestingMutualInformation ε ≤
      ρ.hypothesisTestingMutualInformation ε := by
  let ρ' : State (Prod β δ) := ρ.reindex (Equiv.prodCongr e f)
  rw [hypothesisTestingMutualInformation_eq_sInf]
  refine le_sInf ?_
  intro value hvalue
  rcases hvalue with ⟨σB, rfl⟩
  have houtMem :
      ρ'.hypothesisTestingRelativeEntropy
          (ρ'.marginalA.prod (σB.reindex f)) ε ∈
        hypothesisTestingMutualInformationCandidateSet (a := β) (b := δ) ρ' ε := by
    exact ⟨σB.reindex f, rfl⟩
  have houtLe :
      ρ'.hypothesisTestingMutualInformation ε ≤
        ρ'.hypothesisTestingRelativeEntropy
          (ρ'.marginalA.prod (σB.reindex f)) ε := by
    rw [hypothesisTestingMutualInformation_eq_sInf]
    exact sInf_le houtMem
  have hmarg : ρ'.marginalA = ρ.marginalA.reindex e := by
    simpa [ρ'] using State.marginalA_reindex_prodCongr ρ e f
  have hprod :
      ρ'.marginalA.prod (σB.reindex f) =
        (ρ.marginalA.prod σB).reindex (Equiv.prodCongr e f) := by
    rw [hmarg]
    exact (prod_reindex_prodCongr_forHypothesisTestingDPI
      ρ.marginalA σB e f).symm
  have hD :
      ρ'.hypothesisTestingRelativeEntropy
          ((ρ.marginalA.prod σB).reindex (Equiv.prodCongr e f)) ε =
        ρ.hypothesisTestingRelativeEntropy (ρ.marginalA.prod σB) ε := by
    simpa [ρ'] using
      hypothesisTestingRelativeEntropy_reindex ρ (ρ.marginalA.prod σB) ε hε
        (Equiv.prodCongr e f)
  exact houtLe.trans (by simpa [hprod] using le_of_eq hD)

theorem hypothesisTestingMutualInformation_reindex_prodCongr
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (ρ : State (Prod α γ)) (ε : ℝ) (hε : 0 ≤ ε)
    (e : α ≃ β) (f : γ ≃ δ) :
    (ρ.reindex (Equiv.prodCongr e f)).hypothesisTestingMutualInformation ε =
      ρ.hypothesisTestingMutualInformation ε := by
  let ρ' : State (Prod β δ) := ρ.reindex (Equiv.prodCongr e f)
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
      apply State.ext
      ext i j
      rcases i with ⟨iα, iγ⟩
      rcases j with ⟨jα, jγ⟩
      simp [ρ', State.reindex]
    simpa [hreindex] using h
  exact le_antisymm hforward hback

/-- Canonical purification of a mixed input-reference state, re-associated so
that the original reference remains part of the reference register and the
channel input is the target register. -/
def purifiedInputForHypothesisTestingDPI
    {r : Type u} {a : Type v} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a] (ρ : State (Prod r a)) :
    PureVector (Prod (Prod (Prod r a) r) a) :=
  ρ.canonicalPurification.reindex (Equiv.prodAssoc (Prod r a) r a).symm

theorem traceOut_purifiedInputForHypothesisTestingDPI
    {r : Type u} {a : Type v} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a] (ρ : State (Prod r a)) :
    ((Channel.traceOutLeft (Prod r a) r).prod
        (Channel.idChannel a)).applyState
        (ρ.purifiedInputForHypothesisTestingDPI.state) = ρ := by
  apply State.ext
  ext x y
  rcases x with ⟨xr, xa⟩
  rcases y with ⟨yr, ya⟩
  change
    (MatrixMap.kron
        (Channel.traceOutLeft (Prod r a) r).map
        (Channel.idChannel a).map
        ρ.purifiedInputForHypothesisTestingDPI.state.matrix) (xr, xa) (yr, ya) =
      ρ.matrix (xr, xa) (yr, ya)
  rw [MatrixMap.kron_idChannel_apply_slice]
  change
    (QIT.partialTraceA (a := Prod r a) (b := r)
      (fun i j =>
        ρ.purifiedInputForHypothesisTestingDPI.state.matrix (i, xa) (j, ya)))
        xr yr =
      ρ.matrix (xr, xa) (yr, ya)
  change
    (∑ p : Prod r a,
      ρ.purifiedInputForHypothesisTestingDPI.state.matrix ((p, xr), xa) ((p, yr), ya)) =
      ρ.matrix (xr, xa) (yr, ya)
  have hentry :=
    congrFun (congrFun (State.canonicalPurification_matrix ρ) (xr, xa)) (yr, ya)
  rw [← hentry]
  simp [QIT.partialTraceA, purifiedInputForHypothesisTestingDPI,
    PureVector.reindex_state, State.reindex, PureVector.state_matrix,
    State.canonicalPurification]

theorem hypothesisTestingBeta_applyReferenceIsometry_le
    {r₁ : Type x} {r₂ : Type y} [Fintype r₁] [DecidableEq r₁]
    [Fintype r₂] [DecidableEq r₂]
    (V : ReferenceIsometry r₁ r₂) (ρ σ : State (Prod r₁ a))
    (ε : ℝ) (hε : 0 ≤ ε) :
    State.hypothesisTestingBeta
        (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState ρ)
        (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState σ)
        ε ≤
      ρ.hypothesisTestingBeta σ ε := by
  change
    State.hypothesisTestingBeta
        (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState ρ)
        (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState σ)
        ε ≤
      sInf (ρ.hypothesisTestingBetaCandidateSet σ ε)
  refine le_csInf (ρ.hypothesisTestingBetaCandidateSet_nonempty_of_nonneg σ ε hε) ?_
  intro β hβ
  rcases hβ with ⟨Λ, rfl⟩
  have hle :=
    State.hypothesisTestingBeta_le_of_effect
        (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState ρ)
        (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState σ)
        ε
        (V.pushForwardHypothesisTestingEffect ρ ε Λ)
  rw [ReferenceIsometry.pushForwardHypothesisTestingEffect_typeIIError V ρ σ ε Λ] at hle
  exact hle

theorem hypothesisTestingRelativeEntropy_le_applyReferenceIsometry
    {r₁ : Type x} {r₂ : Type y} [Fintype r₁] [DecidableEq r₁]
    [Fintype r₂] [DecidableEq r₂]
    (V : ReferenceIsometry r₁ r₂) (ρ σ : State (Prod r₁ a))
    (ε : ℝ) (hε : 0 ≤ ε) :
    ρ.hypothesisTestingRelativeEntropy σ ε ≤
      State.hypothesisTestingRelativeEntropy
        (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState ρ)
        (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState σ)
        ε := by
  let ρ' : State (Prod r₂ a) :=
    ((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState ρ
  let σ' : State (Prod r₂ a) :=
    ((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState σ
  have hβle : ρ'.hypothesisTestingBeta σ' ε ≤ ρ.hypothesisTestingBeta σ ε := by
    exact hypothesisTestingBeta_applyReferenceIsometry_le V ρ σ ε hε
  by_cases hβin_zero : ρ.hypothesisTestingBeta σ ε = 0
  · have hβout_nonneg : 0 ≤ ρ'.hypothesisTestingBeta σ' ε :=
      ρ'.hypothesisTestingBeta_nonneg_of_epsilon_nonneg σ' ε hε
    have hβout_zero : ρ'.hypothesisTestingBeta σ' ε = 0 :=
      le_antisymm (by simpa [hβin_zero] using hβle) hβout_nonneg
    simp [hypothesisTestingRelativeEntropy, hβin_zero, hβout_zero, ρ', σ']
  · have hβin_nonneg := ρ.hypothesisTestingBeta_nonneg_of_epsilon_nonneg σ ε hε
    have hβin_pos : 0 < ρ.hypothesisTestingBeta σ ε :=
      lt_of_le_of_ne' hβin_nonneg hβin_zero
    by_cases hβout_zero : ρ'.hypothesisTestingBeta σ' ε = 0
    · simp [hypothesisTestingRelativeEntropy, hβin_zero, hβout_zero, ρ', σ']
    · have hβout_nonneg : 0 ≤ ρ'.hypothesisTestingBeta σ' ε :=
        ρ'.hypothesisTestingBeta_nonneg_of_epsilon_nonneg σ' ε hε
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
    (Φ : Channel a b) (ρ σ : State a) (ε : ℝ) (hε : 0 ≤ ε) :
    ρ.hypothesisTestingBeta σ ε ≤
      (Φ.applyState ρ).hypothesisTestingBeta (Φ.applyState σ) ε := by
  rw [hypothesisTestingBeta_eq_sInf]
  refine le_csInf
    ((Φ.applyState ρ).hypothesisTestingBetaCandidateSet_nonempty_of_nonneg
      (Φ.applyState σ) ε hε) ?_
  intro β hβ
  rcases hβ with ⟨Λ, rfl⟩
  have hle :=
    ρ.hypothesisTestingBeta_le_of_effect σ ε
      (Φ.pullbackHypothesisTestingEffect ρ ε Λ)
  rw [Φ.pullbackHypothesisTestingEffect_typeIIError ρ σ ε Λ] at hle
  exact hle

theorem hypothesisTestingRelativeEntropy_applyState_le
    (Φ : Channel a b) (ρ σ : State a) (ε : ℝ) (hε : 0 ≤ ε) :
    (Φ.applyState ρ).hypothesisTestingRelativeEntropy (Φ.applyState σ) ε ≤
      ρ.hypothesisTestingRelativeEntropy σ ε := by
  have hβle := ρ.hypothesisTestingBeta_le_applyState Φ σ ε hε
  by_cases hβin_zero : ρ.hypothesisTestingBeta σ ε = 0
  · simp [hypothesisTestingRelativeEntropy, hβin_zero]
  · have hβin_nonneg := ρ.hypothesisTestingBeta_nonneg_of_epsilon_nonneg σ ε hε
    have hβin_pos : 0 < ρ.hypothesisTestingBeta σ ε :=
      lt_of_le_of_ne' hβin_nonneg hβin_zero
    have hβout_pos :
        0 < (Φ.applyState ρ).hypothesisTestingBeta (Φ.applyState σ) ε :=
      lt_of_lt_of_le hβin_pos hβle
    have hβout_zero :
        (Φ.applyState ρ).hypothesisTestingBeta (Φ.applyState σ) ε ≠ 0 :=
      ne_of_gt hβout_pos
    have hlog :
        log2 (ρ.hypothesisTestingBeta σ ε) ≤
          log2 ((Φ.applyState ρ).hypothesisTestingBeta (Φ.applyState σ) ε) := by
      unfold log2
      exact div_le_div_of_nonneg_right
        (Real.log_le_log hβin_pos hβle) (le_of_lt (Real.log_pos one_lt_two))
    have hrel :
        (Φ.applyState ρ).hypothesisTestingRelativeEntropyFinite (Φ.applyState σ) ε ≤
          ρ.hypothesisTestingRelativeEntropyFinite σ ε := by
      rw [hypothesisTestingRelativeEntropyFinite_eq, hypothesisTestingRelativeEntropyFinite_eq]
      exact neg_le_neg hlog
    have hrelE :
        ((Φ.applyState ρ).hypothesisTestingRelativeEntropyFinite
          (Φ.applyState σ) ε : EReal) ≤
            (ρ.hypothesisTestingRelativeEntropyFinite σ ε : EReal) := by
      exact_mod_cast hrel
    simpa [hypothesisTestingRelativeEntropy, hβin_zero, hβout_zero] using hrelE

/-- Optimized extended-real hypothesis-testing mutual information does not
decrease when the first/reference register is embedded by an isometry. -/
theorem hypothesisTestingMutualInformation_le_applyReferenceIsometry
    {r₁ : Type x} {r₂ : Type y} [Fintype r₁] [DecidableEq r₁]
    [Fintype r₂] [DecidableEq r₂]
    (V : ReferenceIsometry r₁ r₂) (ρ : State (Prod r₁ a))
    (ε : ℝ) (hε : 0 ≤ ε) :
    ρ.hypothesisTestingMutualInformation ε ≤
      State.hypothesisTestingMutualInformation
        (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState ρ)
        ε := by
  let ρ' : State (Prod r₂ a) :=
    ((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState ρ
  rw [hypothesisTestingMutualInformation_eq_sInf]
  refine le_sInf ?_
  intro value hvalue
  rcases hvalue with ⟨σA, rfl⟩
  have hinMem :
      ρ.hypothesisTestingRelativeEntropy (ρ.marginalA.prod σA) ε ∈
        hypothesisTestingMutualInformationCandidateSet (a := r₁) (b := a) ρ ε := by
    exact ⟨σA, rfl⟩
  have hinLe :
      ρ.hypothesisTestingMutualInformation ε ≤
        ρ.hypothesisTestingRelativeEntropy (ρ.marginalA.prod σA) ε := by
    rw [hypothesisTestingMutualInformation_eq_sInf]
    exact sInf_le hinMem
  have hprod :
      ρ'.marginalA.prod σA =
        ((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState
          (ρ.marginalA.prod σA) := by
    simpa [ρ', marginalA_applyState_prod_id] using
      (State.applyState_prod_id_prod ρ.marginalA σA (Channel.ofReferenceIsometry V)).symm
  have hD :
      ρ.hypothesisTestingRelativeEntropy (ρ.marginalA.prod σA) ε ≤
        ρ'.hypothesisTestingRelativeEntropy (ρ'.marginalA.prod σA) ε := by
    simpa [ρ', hprod] using
      hypothesisTestingRelativeEntropy_le_applyReferenceIsometry
        V ρ (ρ.marginalA.prod σA) ε hε
  exact hinLe.trans hD

/-- Optimized hypothesis-testing mutual information is monotone under local
post-processing on the second register, in the extended-real convention. -/
theorem hypothesisTestingMutualInformation_dataProcessing_right
    (ρ : State (Prod a b)) (D : Channel b c) (ε : ℝ) (hε : 0 ≤ ε) :
    (((Channel.idChannel a).prod D).applyState ρ).hypothesisTestingMutualInformation ε ≤
      ρ.hypothesisTestingMutualInformation ε := by
  let ρ' : State (Prod a c) := ((Channel.idChannel a).prod D).applyState ρ
  rw [hypothesisTestingMutualInformation_eq_sInf]
  refine le_sInf ?_
  intro value hvalue
  rcases hvalue with ⟨σB, rfl⟩
  have hρAmarg : ρ'.marginalA = ρ.marginalA := by
    exact marginalA_applyState_id_prod ρ D
  have hprod :
      ρ'.marginalA.prod (D.applyState σB) =
        ((Channel.idChannel a).prod D).applyState (ρ.marginalA.prod σB) := by
    rw [hρAmarg]
    exact (State.applyState_id_prod_prod ρ.marginalA σB D).symm
  have houtMem :
      ρ'.hypothesisTestingRelativeEntropy
          (ρ'.marginalA.prod (D.applyState σB)) ε ∈
        hypothesisTestingMutualInformationCandidateSet (a := a) (b := c) ρ' ε := by
    exact ⟨D.applyState σB, rfl⟩
  have houtLe :
      ρ'.hypothesisTestingMutualInformation ε ≤
        ρ'.hypothesisTestingRelativeEntropy
          (ρ'.marginalA.prod (D.applyState σB)) ε := by
    rw [hypothesisTestingMutualInformation_eq_sInf]
    exact sInf_le houtMem
  have hDPI :
      ρ'.hypothesisTestingRelativeEntropy
          (((Channel.idChannel a).prod D).applyState (ρ.marginalA.prod σB)) ε ≤
        ρ.hypothesisTestingRelativeEntropy (ρ.marginalA.prod σB) ε := by
    exact hypothesisTestingRelativeEntropy_applyState_le
      ((Channel.idChannel a).prod D) ρ (ρ.marginalA.prod σB) ε hε
  exact houtLe.trans (by simpa [hprod] using hDPI)

/-- Optimized hypothesis-testing mutual information is monotone under local
post-processing on the first register, in the extended-real convention. -/
theorem hypothesisTestingMutualInformation_dataProcessing_left
    (ρ : State (Prod a b)) (D : Channel a c) (ε : ℝ) (hε : 0 ≤ ε) :
    ((D.prod (Channel.idChannel b)).applyState ρ).hypothesisTestingMutualInformation ε ≤
      ρ.hypothesisTestingMutualInformation ε := by
  let ρ' : State (Prod c b) := (D.prod (Channel.idChannel b)).applyState ρ
  rw [hypothesisTestingMutualInformation_eq_sInf]
  refine le_sInf ?_
  intro value hvalue
  rcases hvalue with ⟨σB, rfl⟩
  have hρAmarg : ρ'.marginalA = D.applyState ρ.marginalA := by
    apply State.ext
    change partialTraceB (a := c) (b := b)
        (MatrixMap.kron D.map (Channel.idChannel b).map ρ.matrix) =
      D.map (partialTraceB (a := a) (b := b) ρ.matrix)
    ext i i'
    simp only [partialTraceB]
    let S : b → CMatrix a := fun j => fun x x' => ρ.matrix (x, j) (x', j)
    have hsum :
        (fun x x' => ∑ j : b, ρ.matrix (x, j) (x', j)) =
          ∑ j : b, S j := by
      ext x x'
      change (∑ j : b, ρ.matrix (x, j) (x', j)) =
        (∑ j : b, S j) x x'
      simp only [Matrix.sum_apply]
      rfl
    change (∑ j : b,
        MatrixMap.kron D.map (Channel.idChannel b).map ρ.matrix (i, j) (i', j)) =
      D.map (fun x x' => ∑ j : b, ρ.matrix (x, j) (x', j)) i i'
    rw [hsum, map_sum]
    simp only [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simpa [S] using
      (MatrixMap.kron_idChannel_apply_slice (a := a) (b := c) (r := b)
        (Φ := D.map) (X := ρ.matrix) (br := (i, j)) (br' := (i', j)))
  have hprod :
      ρ'.marginalA.prod σB =
        (D.prod (Channel.idChannel b)).applyState (ρ.marginalA.prod σB) := by
    rw [hρAmarg]
    exact (State.applyState_prod_id_prod ρ.marginalA σB D).symm
  have houtMem :
      ρ'.hypothesisTestingRelativeEntropy (ρ'.marginalA.prod σB) ε ∈
        hypothesisTestingMutualInformationCandidateSet (a := c) (b := b) ρ' ε := by
    exact ⟨σB, rfl⟩
  have houtLe :
      ρ'.hypothesisTestingMutualInformation ε ≤
        ρ'.hypothesisTestingRelativeEntropy (ρ'.marginalA.prod σB) ε := by
    rw [hypothesisTestingMutualInformation_eq_sInf]
    exact sInf_le houtMem
  have hDPI :
      ρ'.hypothesisTestingRelativeEntropy
          ((D.prod (Channel.idChannel b)).applyState (ρ.marginalA.prod σB)) ε ≤
        ρ.hypothesisTestingRelativeEntropy (ρ.marginalA.prod σB) ε := by
    exact hypothesisTestingRelativeEntropy_applyState_le
      (D.prod (Channel.idChannel b)) ρ (ρ.marginalA.prod σB) ε hε
  exact houtLe.trans (by simpa [hprod] using hDPI)

/-- Repartition `(M × E) × B` as `M × (B × E)`, moving side information
from the reference block to the output block while preserving the message
register as the first factor. -/
def messageOutputSideInfoEquiv
    (m e b : Type*) : Prod (Prod m e) b ≃ Prod m (Prod b e) :=
  (Equiv.prodAssoc m e b).trans
    (Equiv.prodCongr (Equiv.refl m) (Equiv.prodComm e b))

private theorem marginalA_reindex_messageOutputSideInfoEquiv
    {m e b : Type*} [Fintype m] [DecidableEq m]
    [Fintype e] [DecidableEq e] [Fintype b] [DecidableEq b]
    (θ : State (Prod (Prod m e) b)) :
    (θ.reindex (messageOutputSideInfoEquiv m e b)).marginalA =
      θ.marginalA.marginalA := by
  apply State.ext
  ext i j
  simp only [State.marginalA_matrix, State.reindex_matrix]
  change
    (∑ x : Prod b e, θ.matrix
      ((messageOutputSideInfoEquiv m e b).symm (i, x))
      ((messageOutputSideInfoEquiv m e b).symm (j, x))) =
    ∑ x : e, θ.marginalA.matrix (i, x) (j, x)
  rw [Fintype.sum_prod_type]
  simp [messageOutputSideInfoEquiv, State.marginalA, partialTraceB]
  rw [Finset.sum_comm]

private theorem product_reference_reindex_messageOutputSideInfoEquiv
    {m e b : Type*} [Fintype m] [DecidableEq m]
    [Fintype e] [DecidableEq e] [Fintype b] [DecidableEq b]
    (θME : State (Prod m e)) (σB : State b)
    (hprod : θME = θME.marginalA.prod θME.marginalB) :
    (θME.prod σB).reindex (messageOutputSideInfoEquiv m e b) =
      θME.marginalA.prod (σB.prod θME.marginalB) := by
  apply State.ext
  ext x y
  rcases x with ⟨xm, xb, xe⟩
  rcases y with ⟨ym, yb, ye⟩
  have hentry :=
    congrFun (congrFun (congrArg State.matrix hprod) (xm, xe)) (ym, ye)
  simp [State.reindex, State.prod, Matrix.kronecker,
    messageOutputSideInfoEquiv, hentry, mul_assoc, mul_left_comm, mul_comm]

theorem hypothesisTestingMutualInformation_repartition_le_of_marginalA_eq_prod
    {m e b : Type*} [Fintype m] [DecidableEq m]
    [Fintype e] [DecidableEq e] [Fintype b] [DecidableEq b]
    (θ : State (Prod (Prod m e) b)) (ε : ℝ) (hε : 0 ≤ ε)
    (hprod : θ.marginalA = θ.marginalA.marginalA.prod θ.marginalA.marginalB) :
    ((θ.reindex (messageOutputSideInfoEquiv m e b)).hypothesisTestingMutualInformation ε) ≤
      θ.hypothesisTestingMutualInformation ε := by
  let θ' : State (Prod m (Prod b e)) :=
    θ.reindex (messageOutputSideInfoEquiv m e b)
  rw [hypothesisTestingMutualInformation_eq_sInf]
  refine le_sInf ?_
  intro value hvalue
  rcases hvalue with ⟨σB, rfl⟩
  let σBE : State (Prod b e) := σB.prod θ.marginalA.marginalB
  have houtMem :
      θ'.hypothesisTestingRelativeEntropy (θ'.marginalA.prod σBE) ε ∈
        hypothesisTestingMutualInformationCandidateSet
          (a := m) (b := Prod b e) θ' ε := by
    exact ⟨σBE, rfl⟩
  have houtLe :
      θ'.hypothesisTestingMutualInformation ε ≤
        θ'.hypothesisTestingRelativeEntropy (θ'.marginalA.prod σBE) ε := by
    rw [hypothesisTestingMutualInformation_eq_sInf]
    exact sInf_le houtMem
  have hmarg : θ'.marginalA = θ.marginalA.marginalA := by
    simpa [θ'] using marginalA_reindex_messageOutputSideInfoEquiv θ
  have hprodState :
      θ'.marginalA.prod σBE =
        (θ.marginalA.prod σB).reindex (messageOutputSideInfoEquiv m e b) := by
    rw [hmarg]
    exact (product_reference_reindex_messageOutputSideInfoEquiv
      θ.marginalA σB hprod).symm
  have hD :
      θ'.hypothesisTestingRelativeEntropy
          ((θ.marginalA.prod σB).reindex (messageOutputSideInfoEquiv m e b)) ε =
        θ.hypothesisTestingRelativeEntropy (θ.marginalA.prod σB) ε := by
    simpa [θ'] using
      hypothesisTestingRelativeEntropy_reindex θ (θ.marginalA.prod σB) ε hε
        (messageOutputSideInfoEquiv m e b)
  exact houtLe.trans (by simpa [hprodState] using le_of_eq hD)

end State

namespace Channel

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
    (N : Channel a b) (D : Channel b c) (ψ : PureVector (Prod a a))
    (ε : ℝ) (hε : 0 ≤ ε) :
    (((Channel.idChannel a).prod D).applyState
        (N.hypothesisTestingOutputState ψ)).hypothesisTestingMutualInformation ε ≤
      N.hypothesisTestingMutualInformation ε := by
  exact (State.hypothesisTestingMutualInformation_dataProcessing_right
    (N.hypothesisTestingOutputState ψ) D ε hε).trans
      (N.inputHypothesisTestingMutualInformation_le_channel ε ψ)

/-- Equality-shaped version of
`hypothesisTestingMutualInformation_postprocess_output_le_channel`, useful when
the protocol state has first been identified with a post-processed channel
output. -/
theorem hypothesisTestingMutualInformation_le_channel_of_eq_postprocess_output
    (N : Channel a b) (D : Channel b c) (ψ : PureVector (Prod a a))
    (ω : State (Prod a c)) (ε : ℝ) (hε : 0 ≤ ε)
    (hω : ω =
      ((Channel.idChannel a).prod D).applyState
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
    (N : Channel a b) (V : ReferenceIsometry r₁ r₂)
    (ψ : PureVector (Prod r₁ a)) :
    N.hypothesisTestingOutputState (V.applyPureVector ψ) =
      ((Channel.ofReferenceIsometry V).prod (Channel.idChannel b)).applyState
        (N.hypothesisTestingOutputState ψ) := by
  apply State.ext
  change MatrixMap.kron (Channel.idChannel r₂).map N.map
      (V.applyPureVector ψ).state.matrix =
    MatrixMap.kron (Channel.ofReferenceIsometry V).map
      (Channel.idChannel b).map
      (MatrixMap.kron (Channel.idChannel r₁).map N.map ψ.state.matrix)
  have hVstate :
      (V.applyPureVector ψ).state.matrix =
        V.applyMatrix ψ.state.matrix := by
    rw [PureVector.state_matrix, PureVector.state_matrix]
    exact V.rankOne_applyAmp ψ.amp
  rw [hVstate]
  rw [Channel.ofReferenceIsometry_map]
  rw [MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft]
  exact MatrixMap.kron_idChannel_left_apply_applyMatrix N.map V ψ.state.matrix

/-- Arbitrary-reference pure inputs whose reference system contains an
input-copy reference are bounded by the channel extended-real
hypothesis-testing mutual information. -/
theorem inputHypothesisTestingMutualInformation_le_channel_of_card_le
    (N : Channel a b) {r : Type w} [Fintype r] [DecidableEq r]
    (ψ : PureVector (Prod r a)) (ε : ℝ) (hε : 0 ≤ ε)
    (hcard : Fintype.card a ≤ Fintype.card r) :
    N.inputHypothesisTestingMutualInformation ψ ε ≤
      N.hypothesisTestingMutualInformation ε := by
  let φ : PureVector (Prod a a) := ψ.state.marginalB.canonicalPurification
  have hφ : φ.Purifies ψ.state.marginalB := by
    exact ψ.state.marginalB.canonicalPurification_purifies
  have hψ : ψ.Purifies ψ.state.marginalB :=
    ψ.purifies_marginalB
  rcases PureVector.exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state
      hφ hψ hcard with ⟨V, hV⟩
  have hout :
      N.hypothesisTestingOutputState ψ =
        ((Channel.ofReferenceIsometry V).prod (Channel.idChannel b)).applyState
          (N.hypothesisTestingOutputState φ) := by
    rw [hV]
    exact N.hypothesisTestingOutputState_applyReferenceIsometry V φ
  rw [inputHypothesisTestingMutualInformation, hout]
  exact (State.hypothesisTestingMutualInformation_dataProcessing_left
      (N.hypothesisTestingOutputState φ) (Channel.ofReferenceIsometry V) ε hε).trans
    (N.inputHypothesisTestingMutualInformation_le_channel ε φ)

/-- Arbitrary-reference pure inputs are bounded by the channel optimized
extended-real hypothesis-testing mutual information.  The proof pads the
reference by an isometric embedding, uses the sufficiently-large-reference
purification bridge, and transports the hypothesis-testing mutual information
back along the isometry. -/
theorem inputHypothesisTestingMutualInformation_le_channel_of_arbitrary_reference
    (N : Channel a b) {r : Type w} [Fintype r] [DecidableEq r]
    (ψ : PureVector (Prod r a)) (ε : ℝ) (hε : 0 ≤ ε) :
    N.inputHypothesisTestingMutualInformation ψ ε ≤
      N.hypothesisTestingMutualInformation ε := by
  let V : ReferenceIsometry r (Sum a r) :=
    ReferenceIsometry.sumInr a r
  let ψ' : PureVector (Prod (Sum a r) a) := V.applyPureVector ψ
  have hlarge : Fintype.card a ≤ Fintype.card (Sum a r) := by
    rw [Fintype.card_sum]
    exact Nat.le_add_right _ _
  have hleft :
      N.inputHypothesisTestingMutualInformation ψ ε ≤
        N.inputHypothesisTestingMutualInformation ψ' ε := by
    unfold inputHypothesisTestingMutualInformation
    rw [N.hypothesisTestingOutputState_applyReferenceIsometry V ψ]
    exact State.hypothesisTestingMutualInformation_le_applyReferenceIsometry
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
    (N : Channel a b) {r : Type w} [Fintype r] [DecidableEq r]
    {s : Type x} [Fintype s] [DecidableEq s]
    (D : Channel r s) (ψ : PureVector (Prod r a)) (ε : ℝ) (hε : 0 ≤ ε) :
    (((D.prod (Channel.idChannel b)).applyState
        (N.hypothesisTestingOutputState ψ)).hypothesisTestingMutualInformation ε) ≤
      N.hypothesisTestingMutualInformation ε := by
  exact (State.hypothesisTestingMutualInformation_dataProcessing_left
      (N.hypothesisTestingOutputState ψ) D ε hε).trans
    (N.inputHypothesisTestingMutualInformation_le_channel_of_arbitrary_reference ψ ε hε)

/-- Equality-shaped version of
`hypothesisTestingMutualInformation_referencePostprocess_output_le_channel`,
for protocol constructions that first identify the tested state with a
reference-side post-processing of a pure channel output. -/
theorem hypothesisTestingMutualInformation_le_channel_of_eq_referencePostprocess_output
    (N : Channel a b) {r : Type w} [Fintype r] [DecidableEq r]
    {s : Type x} [Fintype s] [DecidableEq s]
    (D : Channel r s) (ψ : PureVector (Prod r a)) (ω : State (Prod s b))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hω : ω =
      (D.prod (Channel.idChannel b)).applyState (N.hypothesisTestingOutputState ψ)) :
    ω.hypothesisTestingMutualInformation ε ≤
      N.hypothesisTestingMutualInformation ε := by
  rw [hω]
  exact N.hypothesisTestingMutualInformation_referencePostprocess_output_le_channel
    D ψ ε hε

/-- Mixed input-reference states are also bounded by the channel optimized
extended-real hypothesis-testing mutual information.

The proof purifies the mixed input-reference state, traces out the extra
purifying reference after the channel use, and then applies reference-side data
processing together with the arbitrary-reference pure-input optimization
bridge. -/
theorem mixedInputOutput_hypothesisTestingMutualInformation_le_channel
    (N : Channel a b) {r : Type w} [Fintype r] [DecidableEq r]
    (ρ : State (Prod r a)) (ε : ℝ) (hε : 0 ≤ ε) :
    (((Channel.idChannel r).prod N).applyState ρ).hypothesisTestingMutualInformation ε ≤
      N.hypothesisTestingMutualInformation ε := by
  let ψ : PureVector (Prod (Prod (Prod r a) r) a) :=
    ρ.purifiedInputForHypothesisTestingDPI
  let D : Channel (Prod (Prod r a) r) r :=
    Channel.traceOutLeft (Prod r a) r
  have hstate :
      (D.prod (Channel.idChannel b)).applyState (N.hypothesisTestingOutputState ψ) =
        ((Channel.idChannel r).prod N).applyState ρ := by
    calc
      (D.prod (Channel.idChannel b)).applyState (N.hypothesisTestingOutputState ψ) =
        (D.prod (Channel.idChannel b)).applyState
          (((Channel.idChannel (Prod (Prod r a) r)).prod N).applyState ψ.state) := rfl
      _ = ((Channel.idChannel r).prod N).applyState
          (((D.prod (Channel.idChannel a)).applyState ψ.state)) := by
          exact Channel.traceOutLeft_prod_id_applyState_id_prod
            (p := Prod r a) (r := r) N ψ.state
      _ = ((Channel.idChannel r).prod N).applyState ρ := by
          rw [State.traceOut_purifiedInputForHypothesisTestingDPI]
  rw [← hstate]
  exact N.hypothesisTestingMutualInformation_referencePostprocess_output_le_channel
    D ψ ε hε

end Channel

end

end QIT
