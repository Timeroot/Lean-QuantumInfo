/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Symmetry.DeFinetti.Domination

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal
open MeasureTheory

namespace QIT

universe u v w x

noncomputable section

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [Fintype a] [DecidableEq a]

local instance deFinettiTwirlingCMatrixContinuousENorm
    {α : Type v} [Fintype α] [DecidableEq α] :
    ContinuousENorm (CMatrix α) :=
  SeminormedAddGroup.toContinuousENorm

/-- CKR post-selection reference state on `H^n × H^n`.

The source theorem evaluates `Δ ⊗ id` on a purification/reference extension of
`τ_{H^n}`.  The library source-facing input is the enlarged symmetric reference
on `(H × H)^n`, transported across the standard identification
`(H × H)^n ≃ H^n × H^n`.  This name intentionally avoids presenting the bare
normalized symmetric projection on `H^n` as the full CKR mixed reference. -/
abbrev ckrPostSelectionReferenceState [Nonempty a] (n : ℕ) :
    State (Prod (TensorPower a n) (TensorPower a n)) :=
  (State.symmetricProjectionReferenceState (a := Prod a a) n).reindex
    (tensorPowerProdEquiv a a n)

@[simp]
theorem ckrPostSelectionReferenceState_matrix [Nonempty a] (n : ℕ) :
    (ckrPostSelectionReferenceState (a := a) n).matrix =
      (State.symmetricProjectionReferenceState (a := Prod a a) n).matrix.submatrix
        (tensorPowerProdEquiv a a n).symm
        (tensorPowerProdEquiv a a n).symm :=
  rfl

theorem ckrPostSelectionReferenceState_trace_eq_one [Nonempty a] (n : ℕ) :
    (ckrPostSelectionReferenceState (a := a) n).matrix.trace = 1 :=
  (ckrPostSelectionReferenceState (a := a) n).trace_eq_one

/-- Compatibility bridge for the older local post-selection reference name.
Source-facing statements should prefer `ckrPostSelectionReferenceState`. -/
abbrev postSelectionReferenceState [Nonempty a] (n : ℕ) :
    State (Prod (TensorPower a n) (TensorPower a n)) :=
  ckrPostSelectionReferenceState (a := a) n

@[simp]
theorem postSelectionReferenceState_matrix [Nonempty a] (n : ℕ) :
    (postSelectionReferenceState (a := a) n).matrix =
      (State.symmetricProjectionReferenceState (a := Prod a a) n).matrix.submatrix
        (tensorPowerProdEquiv a a n).symm
        (tensorPowerProdEquiv a a n).symm :=
  rfl

theorem postSelectionReferenceState_trace_eq_one [Nonempty a] (n : ℕ) :
    (postSelectionReferenceState (a := a) n).matrix.trace = 1 :=
  ckrPostSelectionReferenceState_trace_eq_one (a := a) n

/-- Entrywise action of a tensor-factor permutation on the left input register,
with the reference register left unchanged. -/
theorem permutationChannel_prod_id_map_apply {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (π : Equiv.Perm (Fin n)) (X : CMatrix (Prod (TensorPower a n) r))
    (x y : Prod (TensorPower a n) r) :
    (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).map X) x y =
      X (permEquiv (a := a) n π x.1, x.2)
        (permEquiv (a := a) n π y.1, y.2) := by
  change MatrixMap.kron (permutationChannel (a := a) n π).map
    (Channel.idChannel r).map X x y = _
  rw [MatrixMap.kron_idChannel_apply_slice]
  rw [permutationChannel_map_apply]

/-- Partial trace over the reference register commutes with a tensor-factor
permutation on the input register. -/
theorem partialTraceB_permutation_prod_id_map {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (π : Equiv.Perm (Fin n)) (X : CMatrix (Prod (TensorPower a n) r)) :
    partialTraceB (a := TensorPower a n) (b := r)
        (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).map X) =
      (permutationChannel (a := a) n π).map
        (partialTraceB (a := TensorPower a n) (b := r) X) := by
  ext x y
  simp only [partialTraceB]
  rw [permutationChannel_map_apply]
  refine Finset.sum_congr rfl fun rr _ => ?_
  rw [permutationChannel_prod_id_map_apply]

namespace State

/-- Average an input-reference state over permutations of the input tensor
factors, leaving the reference register unchanged. -/
def inputPermutationTwirling {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    State (Prod (TensorPower a n) r) where
  matrix := (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
    ∑ π : Equiv.Perm (Fin n),
      (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix
  pos := by
    have hcR : 0 ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ :=
      inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (Equiv.Perm (Fin n))))
    have hcC : 0 ≤ (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast hcR
    exact (Matrix.posSemidef_sum Finset.univ fun π _ =>
      (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).pos).smul hcC
  trace_eq_one := by
    simp only [Matrix.trace_smul, Matrix.trace_sum]
    calc
      ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
          ∑ π : Equiv.Perm (Fin n),
            ((((permutationChannel (a := a) n π).prod
              (Channel.idChannel r)).applyState ω).matrix).trace) =
          (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) *
            (Fintype.card (Equiv.Perm (Fin n)) : ℂ) := by
            simp [State.trace_eq_one, Finset.sum_const, nsmul_eq_mul]
      _ = 1 := by
            norm_num [Nat.cast_ne_zero.mpr (Fintype.card_ne_zero :
              Fintype.card (Equiv.Perm (Fin n)) ≠ 0)]

/-- Input permutation twirling is invariant under further input permutations. -/
theorem inputPermutationTwirling_apply_permutation {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) (τ : Equiv.Perm (Fin n)) :
    ((permutationChannel (a := a) n τ).prod (Channel.idChannel r)).applyState
        (ω.inputPermutationTwirling (a := a) (r := r)) =
      ω.inputPermutationTwirling (a := a) (r := r) := by
  apply State.ext
  ext x y
  dsimp [inputPermutationTwirling]
  simp only [Channel.applyState]
  change MatrixMap.kron (permutationChannel (a := a) n τ).map (Channel.idChannel r).map
      ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
        ∑ σ : Equiv.Perm (Fin n),
          (((permutationChannel (a := a) n σ).prod (Channel.idChannel r)).applyState ω).matrix) x y =
    ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
        ∑ σ : Equiv.Perm (Fin n),
          (((permutationChannel (a := a) n σ).prod (Channel.idChannel r)).applyState ω).matrix) x y
  rw [map_smul, map_sum]
  simp only [Matrix.smul_apply, Matrix.sum_apply]
  congr 1
  refine Fintype.sum_equiv
    { toFun := fun σ : Equiv.Perm (Fin n) => σ * τ,
      invFun := fun σ => σ * τ⁻¹,
      left_inv := by intro σ; simp [mul_assoc],
      right_inv := by intro σ; simp [mul_assoc] }
    (fun σ => (MatrixMap.kron (permutationChannel (a := a) n τ).map
      (Channel.idChannel r).map
      (((permutationChannel (a := a) n σ).prod (Channel.idChannel r)).applyState ω).matrix) x y)
    (fun σ => (((permutationChannel (a := a) n σ).prod
      (Channel.idChannel r)).applyState ω).matrix x y) ?_
  intro σ
  cases x with
  | mk xA xr =>
  cases y with
  | mk yA yr =>
    simp only [Channel.applyState]
    rw [MatrixMap.kron_idChannel_apply_slice]
    rw [permutationChannel_map_apply]
    simp only [permutationChannel_prod_id_map_apply]
    change ω.matrix (σ • (τ • xA), xr) (σ • (τ • yA), yr) =
      ω.matrix ((σ * τ) • xA, xr) ((σ * τ) • yA, yr)
    rw [← mul_smul, ← mul_smul]

/-- The input marginal of an input-permutation-twirled state is permutation
invariant. -/
theorem inputPermutationTwirling_marginalA_isPermutationInvariant
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    (ω.inputPermutationTwirling (a := a) (r := r)).marginalA.IsPermutationInvariant
      (a := a) := by
  intro τ
  apply State.ext
  have hwhole := inputPermutationTwirling_apply_permutation (a := a) (r := r) ω τ
  have hm := congrArg
    (fun ρ : State (Prod (TensorPower a n) r) => ρ.marginalA.matrix) hwhole
  change partialTraceB
      (((permutationChannel (a := a) n τ).prod (Channel.idChannel r)).map
        (ω.inputPermutationTwirling (a := a) (r := r)).matrix) =
    (ω.inputPermutationTwirling (a := a) (r := r)).marginalA.matrix at hm
  rw [partialTraceB_permutation_prod_id_map] at hm
  exact hm

/-- Reindex the canonical purification of an input-reference state into
input-first form, with the original reference and the purifying environment
bundled as the new reference register. -/
def extensionPurificationInputEquiv {r : Type w} {n : ℕ} :
    Equiv (Prod (Prod (TensorPower a n) r) (Prod (TensorPower a n) r))
      (Prod (TensorPower a n) (Prod r (Prod (TensorPower a n) r))) where
  toFun x := (x.2.1, (x.2.2, x.1))
  invFun x := (x.2.2, (x.1, x.2.1))
  left_inv := by intro x; cases x with | mk e t => cases e; cases t; rfl
  right_inv := by intro x; cases x with | mk xa xrE => cases xrE; rfl

/-- Canonical pure extension of a mixed input-reference state, oriented with
the channel input as the first factor. -/
def inputReferenceCanonicalExtension {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    PureVector (Prod (TensorPower a n) (Prod r (Prod (TensorPower a n) r))) :=
  ω.canonicalPurification.reindex
    (extensionPurificationInputEquiv (a := a) (r := r) (n := n))

/-- Output-side counterpart of `extensionPurificationInputEquiv` after a
channel has acted on the input tensor power. -/
def extensionPurificationOutputEquiv {r : Type w} {b : Type x} {n : ℕ} :
    Equiv (Prod (Prod (TensorPower a n) r) (Prod b r))
      (Prod b (Prod r (Prod (TensorPower a n) r))) where
  toFun x := (x.2.1, (x.2.2, x.1))
  invFun x := (x.2.2, (x.1, x.2.1))
  left_inv := by intro x; cases x with | mk e t => cases e; cases t; rfl
  right_inv := by intro x; cases x with | mk xb xrE => cases xrE; rfl

/-- Canonical purification of a tensor-power state, reindexed as a state on
`(H × H)^n`.  This is the symmetric-lift input used by the CKR post-selection
reduction. -/
def canonicalTensorPowerPurificationState {n : ℕ} (ρ : State (TensorPower a n)) :
    State (TensorPower (Prod a a) n) :=
  ρ.canonicalPurification.state.reindex (tensorPowerProdEquiv a a n).symm

/-- Amplitude of `canonicalTensorPowerPurificationState`. -/
def canonicalTensorPowerPurificationAmp {n : ℕ} (ρ : State (TensorPower a n)) :
    TensorPower (Prod a a) n → ℂ :=
  fun x => ρ.canonicalPurification.amp ((tensorPowerProdEquiv a a n) x)

/-- Canonical purification of a tensor-power state with the purified system in
the first factor after reindexing as `H^n × H^n`.  This orientation matches the
finite diamond-distance convention where the channel acts on the first factor. -/
def inputCanonicalTensorPowerPurificationState {n : ℕ} (ρ : State (TensorPower a n)) :
    State (TensorPower (Prod a a) n) :=
  ρ.canonicalPurification.state.reindex
    ((Equiv.prodComm (TensorPower a n) (TensorPower a n)).trans
      (tensorPowerProdEquiv a a n).symm)

/-- Amplitude of `inputCanonicalTensorPowerPurificationState`. -/
def inputCanonicalTensorPowerPurificationAmp {n : ℕ} (ρ : State (TensorPower a n)) :
    TensorPower (Prod a a) n → ℂ :=
  fun x => ρ.sqrtMatrix ((tensorPowerProdEquiv a a n x).1)
    ((tensorPowerProdEquiv a a n x).2)

@[simp]
theorem canonicalTensorPowerPurificationState_matrix {n : ℕ}
    (ρ : State (TensorPower a n)) :
    ρ.canonicalTensorPowerPurificationState.matrix =
      rankOneMatrix ρ.canonicalTensorPowerPurificationAmp := by
  ext x y
  simp [canonicalTensorPowerPurificationState, canonicalTensorPowerPurificationAmp,
    State.reindex_matrix, PureVector.state_matrix, rankOneMatrix_apply]

@[simp]
theorem inputCanonicalTensorPowerPurificationState_matrix {n : ℕ}
    (ρ : State (TensorPower a n)) :
    ρ.inputCanonicalTensorPowerPurificationState.matrix =
      rankOneMatrix ρ.inputCanonicalTensorPowerPurificationAmp := by
  ext x y
  simp [inputCanonicalTensorPowerPurificationState, inputCanonicalTensorPowerPurificationAmp,
    State.reindex_matrix, PureVector.state_matrix, rankOneMatrix_apply,
    State.canonicalPurification, State.canonicalPurificationAmp]

/-- Reindexing the tensor-power canonical purification back to
`H^n × H^n` recovers the library's ordinary canonical purification. -/
theorem canonicalTensorPowerPurificationState_reindex_tensorPowerProdEquiv {n : ℕ}
    (ρ : State (TensorPower a n)) :
    ρ.canonicalTensorPowerPurificationState.reindex (tensorPowerProdEquiv a a n) =
      ρ.canonicalPurification.state := by
  apply State.ext
  ext x y
  simp [canonicalTensorPowerPurificationState, State.reindex]

/-- Reindexing the input-first tensor-power canonical purification back to
`H^n × H^n` gives the ordinary canonical purification with its two factors
swapped. -/
theorem inputCanonicalTensorPowerPurificationState_reindex_tensorPowerProdEquiv {n : ℕ}
    (ρ : State (TensorPower a n)) :
    ρ.inputCanonicalTensorPowerPurificationState.reindex (tensorPowerProdEquiv a a n) =
      ρ.canonicalPurification.state.reindex
        (Equiv.prodComm (TensorPower a n) (TensorPower a n)) := by
  apply State.ext
  ext x y
  simp [inputCanonicalTensorPowerPurificationState, State.reindex]

/-- The right marginal of the tensor-power canonical purification, after
reindexing as `H^n × H^n`, is the purified input state. -/
theorem canonicalTensorPowerPurificationState_reindex_marginalB {n : ℕ}
    (ρ : State (TensorPower a n)) :
    (ρ.canonicalTensorPowerPurificationState.reindex
        (tensorPowerProdEquiv a a n)).marginalB = ρ := by
  rw [canonicalTensorPowerPurificationState_reindex_tensorPowerProdEquiv]
  apply State.ext
  change partialTraceA (a := TensorPower a n) (b := TensorPower a n)
      ρ.canonicalPurification.state.matrix = ρ.matrix
  exact PureVector.partialTraceA_state_matrix_eq_of_purifies
    ρ.canonicalPurification_purifies

/-- The first marginal of the input-first tensor-power canonical purification,
after reindexing as `H^n × H^n`, is the purified input state. -/
theorem inputCanonicalTensorPowerPurificationState_reindex_marginalA {n : ℕ}
    (ρ : State (TensorPower a n)) :
    (ρ.inputCanonicalTensorPowerPurificationState.reindex
        (tensorPowerProdEquiv a a n)).marginalA = ρ := by
  rw [inputCanonicalTensorPowerPurificationState_reindex_tensorPowerProdEquiv]
  apply State.ext
  ext i j
  change partialTraceB (a := TensorPower a n) (b := TensorPower a n)
      ((ρ.canonicalPurification.state.reindex
        (Equiv.prodComm (TensorPower a n) (TensorPower a n))).matrix) i j =
    ρ.matrix i j
  simp [partialTraceB, State.reindex, State.canonicalPurification,
    State.canonicalPurificationAmp, PureVector.state_matrix, rankOneMatrix_apply]
  rw [← ρ.sqrtMatrix_mul_self]
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := congrArg star (ρ.sqrtMatrix_isHermitian.apply j x)
  simpa using (congrArg (fun z => ρ.sqrtMatrix i x * z) h).symm

end State

end

end QIT
