/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Symmetry.DeFinetti.Domination
public import QuantumLib.QIT.Util.MatrixInstances

/-!
# Permutation twirling and tensor-power purifications

The symmetry-averaging half of the de Finetti development.

`MState.inputPermutationTwirling` averages a state on `TensorPower a n × r` over the `n!`
permutations of the input tensor factors, leaving the reference register `r` untouched.  The
average is fixed by any further permutation, so its input marginal is permutation invariant, which
is the hypothesis the domination and post-selection bounds are stated under.

The rest of the module moves states between the two ways of writing a doubled tensor power,
`TensorPower (a × a) n` and `TensorPower a n × TensorPower a n`, along `tensorPowerProdEquiv`.
`ckrPostSelectionReferenceState` is the normalized symmetric-projection reference on the former
read as a state on the latter, and `canonicalTensorPowerPurificationState` and its `input` variant
are the canonical purification of a tensor-power state read the other way, in the two register
orders the post-selection argument uses; each comes with its amplitude, its rank-one matrix, and
the marginal that recovers the state purified.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal QIT.MatrixL2
open MeasureTheory

noncomputable section
universe u v w x
variable {ι : Type u} {a : Type v}
variable [Fintype ι] [Fintype a] [DecidableEq a]

open QIT

namespace QIT

/-- CKR post-selection reference state on `H^n × H^n`.

The source theorem evaluates `Δ ⊗ id` on a purification/reference extension of
`τ_{H^n}`.  The library source-facing input is the enlarged symmetric reference
on `(H × H)^n`, transported across the standard identification
`(H × H)^n ≃ H^n × H^n`.  This name intentionally avoids presenting the bare
normalized symmetric projection on `H^n` as the full CKR mixed reference. -/
abbrev ckrPostSelectionReferenceState [Nonempty a] (n : ℕ) :
    MState (TensorPower a n × TensorPower a n) :=
  (MState.symmetricProjectionReferenceState (a := a × a) n).reindex
    (tensorPowerProdEquiv a a n)

theorem ckrPostSelectionReferenceState_matrix [Nonempty a] (n : ℕ) :
    (ckrPostSelectionReferenceState (a := a) n).m =
      (MState.symmetricProjectionReferenceState (a := a × a) n).m.submatrix
        (tensorPowerProdEquiv a a n).symm
        (tensorPowerProdEquiv a a n).symm :=
  MState.reindex_matrix _ _

theorem ckrPostSelectionReferenceState_trace_eq_one [Nonempty a] (n : ℕ) :
    (ckrPostSelectionReferenceState (a := a) n).m.trace = 1 :=
  (ckrPostSelectionReferenceState (a := a) n).tr'

/-- Entrywise action of a tensor-factor permutation on the left input register,
with the reference register left unchanged. -/
theorem permutationChannel_prod_id_map_apply {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (π : Equiv.Perm (Fin n)) (X : CMatrix (TensorPower a n × r))
    (x y : TensorPower a n × r) :
    (((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))).map X) x y =
      X (permEquiv (a := a) n π x.1, x.2)
        (permEquiv (a := a) n π y.1, y.2) := by
  rw [CPTPOp.prod_map,
    MatrixMap.kron_idChannel_apply_slice]
  rw [permutationChannel_map_apply]
  simp only [Matrix.of_apply]

/-- Partial trace over the reference register commutes with a tensor-factor
permutation on the input register. -/
theorem traceRight_permutation_prod_id_map {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (π : Equiv.Perm (Fin n)) (X : CMatrix (TensorPower a n × r)) :
    Matrix.traceRight
        (((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))).map X) =
      (permutationChannel (a := a) n π).map
        (Matrix.traceRight X) := by
  ext x y
  simp only [Matrix.traceRight, Matrix.of_apply]
  rw [permutationChannel_map_apply]
  refine Finset.sum_congr rfl fun rr _ => ?_
  rw [permutationChannel_prod_id_map_apply]

end QIT

namespace MState

/-- Average an input-reference state over permutations of the input tensor
factors, leaving the reference register unchanged. -/
def inputPermutationTwirling {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : MState (TensorPower a n × r)) :
    MState (TensorPower a n × r) := .ofMatrix
  (matrix := (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
    ∑ π : Equiv.Perm (Fin n),
      (((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m)
  (pos := by
    have hcR : 0 ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ :=
      inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (Equiv.Perm (Fin n))))
    have hcC : 0 ≤ (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast hcR
    exact (Matrix.posSemidef_sum Finset.univ fun π _ =>
      (((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).psd).smul hcC)
  (trace_eq_one := by
    simp only [Matrix.trace_smul, Matrix.trace_sum]
    calc
      ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
          ∑ π : Equiv.Perm (Fin n),
            ((((permutationChannel (a := a) n π).prod
              (CPTPOp.id (dIn := r))) ω).m).trace) =
          (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) *
            (Fintype.card (Equiv.Perm (Fin n)) : ℂ) := by
            simp only [DensityOp.tr']
            simp
      _ = 1 := by
            norm_num [Nat.cast_ne_zero.mpr (Fintype.card_ne_zero :
              Fintype.card (Equiv.Perm (Fin n)) ≠ 0)])

@[simp]
theorem inputPermutationTwirling_matrix {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : MState (TensorPower a n × r)) :
    (ω.inputPermutationTwirling (a := a) (r := r)).m =
      (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
        ∑ π : Equiv.Perm (Fin n),
          (((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m :=
  MState.matrix_ofMatrix _ _ _

/-- Input permutation twirling is invariant under further input permutations. -/
theorem inputPermutationTwirling_apply_permutation {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : MState (TensorPower a n × r)) (τ : Equiv.Perm (Fin n)) :
    ((permutationChannel (a := a) n τ).prod (CPTPOp.id (dIn := r)))
        (ω.inputPermutationTwirling (a := a) (r := r)) =
      ω.inputPermutationTwirling (a := a) (r := r) := by
  apply MState.ext
  rw [CPTPOp.mat_coe_eq_apply_mat, inputPermutationTwirling_matrix, map_smul, map_sum,
    CPTPOp.prod_map]
  ext x y
  simp only [Matrix.smul_apply, Matrix.sum_apply]
  congr 1
  refine Fintype.sum_equiv
    { toFun := fun σ : Equiv.Perm (Fin n) => σ * τ,
      invFun := fun σ => σ * τ⁻¹,
      left_inv := by intro σ; simp [mul_assoc],
      right_inv := by intro σ; simp [mul_assoc] }
    (fun σ => (MatrixMap.kron (permutationChannel (a := a) n τ).map
      (CPTPOp.id (dIn := r)).map
      (((permutationChannel (a := a) n σ).prod (CPTPOp.id (dIn := r))) ω).m) x y)
    (fun σ => (((permutationChannel (a := a) n σ).prod
      (CPTPOp.id (dIn := r))) ω).m x y) ?_
  intro σ
  cases x with
  | mk xA xr =>
  cases y with
  | mk yA yr =>
    simp only [CPTPOp.mat_coe_eq_apply_mat]
    rw [MatrixMap.kron_idChannel_apply_slice]
    rw [permutationChannel_map_apply]
    simp only [permutationChannel_prod_id_map_apply]
    change ω.m (σ • (τ • xA), xr) (σ • (τ • yA), yr) =
      ω.m ((σ * τ) • xA, xr) ((σ * τ) • yA, yr)
    rw [← mul_smul, ← mul_smul]

/-- The input marginal of an input-permutation-twirled state is permutation
invariant. -/
theorem inputPermutationTwirling_traceRight_isPermutationInvariant
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : MState (TensorPower a n × r)) :
    (ω.inputPermutationTwirling (a := a) (r := r)).traceRight.IsPermutationInvariant
      (a := a) := by
  intro τ
  apply MState.ext
  have hwhole := inputPermutationTwirling_apply_permutation (a := a) (r := r) ω τ
  have hm := congrArg
    (fun ρ : MState (TensorPower a n × r) => ρ.traceRight.m) hwhole
  simp only [MState.traceRight_m, CPTPOp.mat_coe_eq_apply_mat] at hm ⊢
  rwa [traceRight_permutation_prod_id_map] at hm

/-- Reindex the canonical purification of an input-reference state into
input-first form, with the original reference and the purifying environment
bundled as the new reference register. -/
def extensionPurificationInputEquiv {r : Type w} {n : ℕ} :
    Equiv ((TensorPower a n × r) × (TensorPower a n × r))
      (TensorPower a n × (r × (TensorPower a n × r))) where
  toFun x := (x.2.1, (x.2.2, x.1))
  invFun x := (x.2.2, (x.1, x.2.1))
  left_inv := by intro x; cases x with | mk e t => cases e; cases t; rfl
  right_inv := by intro x; cases x with | mk xa xrE => cases xrE; rfl

/-- Canonical pure extension of a mixed input-reference state, oriented with
the channel input as the first factor. -/
def inputReferenceCanonicalExtension {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : MState (TensorPower a n × r)) :
    Ket (TensorPower a n × (r × (TensorPower a n × r))) :=
  ω.canonicalPurification.reindex
    (extensionPurificationInputEquiv (a := a) (r := r) (n := n))

/-- Output-side counterpart of `extensionPurificationInputEquiv` after a
channel has acted on the input tensor power. -/
def extensionPurificationOutputEquiv {r : Type w} {b : Type x} {n : ℕ} :
    Equiv ((TensorPower a n × r) × (b × r))
      (b × (r × (TensorPower a n × r))) where
  toFun x := (x.2.1, (x.2.2, x.1))
  invFun x := (x.2.2, (x.1, x.2.1))
  left_inv := by intro x; cases x with | mk e t => cases e; cases t; rfl
  right_inv := by intro x; cases x with | mk xb xrE => cases xrE; rfl

/-- Canonical purification of a tensor-power state, reindexed as a state on
`(H × H)^n`.  This is the symmetric-lift input used by the CKR post-selection
reduction. -/
def canonicalTensorPowerPurificationState {n : ℕ} (ρ : MState (TensorPower a n)) :
    MState (TensorPower (a × a) n) :=
  ρ.canonicalPurification.state.reindex (tensorPowerProdEquiv a a n).symm

/-- Amplitude of `canonicalTensorPowerPurificationState`. -/
def canonicalTensorPowerPurificationAmp {n : ℕ} (ρ : MState (TensorPower a n)) :
    TensorPower (a × a) n → ℂ :=
  fun x => ρ.canonicalPurification.vec ((tensorPowerProdEquiv a a n) x)

/-- Canonical purification of a tensor-power state with the purified system in
the first factor after reindexing as `H^n × H^n`.  This orientation matches the
finite diamond-distance convention where the channel acts on the first factor. -/
def inputCanonicalTensorPowerPurificationState {n : ℕ} (ρ : MState (TensorPower a n)) :
    MState (TensorPower (a × a) n) :=
  ρ.canonicalPurification.state.reindex
    ((Equiv.prodComm (TensorPower a n) (TensorPower a n)).trans
      (tensorPowerProdEquiv a a n).symm)

/-- Amplitude of `inputCanonicalTensorPowerPurificationState`. -/
def inputCanonicalTensorPowerPurificationAmp {n : ℕ} (ρ : MState (TensorPower a n)) :
    TensorPower (a × a) n → ℂ :=
  fun x => ρ.sqrtMatrix ((tensorPowerProdEquiv a a n x).1)
    ((tensorPowerProdEquiv a a n x).2)

@[simp]
theorem canonicalTensorPowerPurificationState_matrix {n : ℕ}
    (ρ : MState (TensorPower a n)) :
    ρ.canonicalTensorPowerPurificationState.m =
      rankOneMatrix ρ.canonicalTensorPowerPurificationAmp := by
  ext x y
  simp [canonicalTensorPowerPurificationState, canonicalTensorPowerPurificationAmp,
    MState.reindex_matrix, Ket.state_matrix, rankOneMatrix_apply]

@[simp]
theorem inputCanonicalTensorPowerPurificationState_matrix {n : ℕ}
    (ρ : MState (TensorPower a n)) :
    ρ.inputCanonicalTensorPowerPurificationState.m =
      rankOneMatrix ρ.inputCanonicalTensorPowerPurificationAmp := by
  ext x y
  simp [inputCanonicalTensorPowerPurificationState, inputCanonicalTensorPowerPurificationAmp,
    MState.reindex_matrix, Ket.state_matrix, rankOneMatrix_apply,
    MState.canonicalPurification, MState.canonicalPurificationAmp]

/-- Reindexing the tensor-power canonical purification back to
`H^n × H^n` recovers the library's ordinary canonical purification. -/
theorem canonicalTensorPowerPurificationState_reindex_tensorPowerProdEquiv {n : ℕ}
    (ρ : MState (TensorPower a n)) :
    ρ.canonicalTensorPowerPurificationState.reindex (tensorPowerProdEquiv a a n) =
      ρ.canonicalPurification.state := by
  apply MState.ext
  ext x y
  simp [canonicalTensorPowerPurificationState]

/-- Reindexing the input-first tensor-power canonical purification back to
`H^n × H^n` gives the ordinary canonical purification with its two factors
swapped. -/
theorem inputCanonicalTensorPowerPurificationState_reindex_tensorPowerProdEquiv {n : ℕ}
    (ρ : MState (TensorPower a n)) :
    ρ.inputCanonicalTensorPowerPurificationState.reindex (tensorPowerProdEquiv a a n) =
      ρ.canonicalPurification.state.reindex
        (Equiv.prodComm (TensorPower a n) (TensorPower a n)) := by
  apply MState.ext
  ext x y
  simp [inputCanonicalTensorPowerPurificationState]

/-- The right marginal of the tensor-power canonical purification, after
reindexing as `H^n × H^n`, is the purified input state. -/
theorem canonicalTensorPowerPurificationState_reindex_traceLeft {n : ℕ}
    (ρ : MState (TensorPower a n)) :
    (ρ.canonicalTensorPowerPurificationState.reindex
        (tensorPowerProdEquiv a a n)).traceLeft = ρ := by
  rw [canonicalTensorPowerPurificationState_reindex_tensorPowerProdEquiv]
  apply MState.ext
  rw [MState.traceLeft_m]
  exact Ket.traceLeft_state_matrix_eq_of_purifies
    ρ.canonicalPurification_purifies

/-- The first marginal of the input-first tensor-power canonical purification,
after reindexing as `H^n × H^n`, is the purified input state. -/
theorem inputCanonicalTensorPowerPurificationState_reindex_traceRight {n : ℕ}
    (ρ : MState (TensorPower a n)) :
    (ρ.inputCanonicalTensorPowerPurificationState.reindex
        (tensorPowerProdEquiv a a n)).traceRight = ρ := by
  rw [inputCanonicalTensorPowerPurificationState_reindex_tensorPowerProdEquiv]
  apply MState.ext
  rw [MState.traceRight_m]
  ext i j
  simp [Matrix.traceRight, MState.reindex_matrix, MState.canonicalPurification,
    MState.canonicalPurificationAmp, Ket.state_matrix, rankOneMatrix_apply]
  rw [← ρ.sqrtMatrix_mul_self]
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := congrArg star (ρ.sqrtMatrix_isHermitian.apply j x)
  simpa using (congrArg (fun z => ρ.sqrtMatrix i x * z) h).symm

end MState
