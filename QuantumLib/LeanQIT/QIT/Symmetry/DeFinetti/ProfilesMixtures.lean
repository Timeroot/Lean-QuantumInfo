/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Symmetry.SymmetricSubspace
public import QIT.Symmetry.TensorPowerSplit
public import QIT.Symmetry.UnitaryTwirl
public import QIT.Classical.Ensemble
public import QIT.Classical.CQState
public import QIT.Channels.Diamond
public import QIT.States.Purification.Canonical
public import QIT.States.Purification.Equivalence
public import QIT.States.Schatten
public import QIT.States.Subnormalized
public import QIT.States.TraceNorm.PositivePart
public import QIT.Util.SDP.HermitianPSDTraceDuality
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal
open MeasureTheory

namespace QIT

universe u v w x

noncomputable section

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [Fintype a] [DecidableEq a]

local instance deFinettiCMatrixContinuousENorm {α : Type v} [Fintype α] [DecidableEq α] :
    ContinuousENorm (CMatrix α) :=
  SeminormedAddGroup.toContinuousENorm

namespace TensorPower

omit [Fintype a] [DecidableEq a] in
/-- A nonempty base alphabet gives a nonempty tensor-power basis at every
block length. -/
protected theorem nonempty [Nonempty a] :
    (n : ℕ) → Nonempty (TensorPower a n)
  | 0 => ⟨⟨⟩⟩
  | n + 1 =>
      let hn := TensorPower.nonempty n
      ⟨(Classical.choice ‹Nonempty a›, Classical.choice hn)⟩

end TensorPower

instance tensorPowerNonempty [Nonempty a] (n : ℕ) : Nonempty (TensorPower a n) :=
  TensorPower.nonempty (a := a) n

namespace TensorPowerProfile

/-- A nonempty base alphabet gives at least one realized tensor-power profile. -/
protected theorem nonempty [Nonempty a] (n : ℕ) : Nonempty (TensorPowerProfile a n) := by
  let x : TensorPower a n := Classical.choice (TensorPower.nonempty n)
  exact ⟨⟨tensorPowerTypeProfile (a := a) n x,
    tensorPowerTypeProfile_mem_profiles (a := a) n x⟩⟩

theorem card_ne_zero [Nonempty a] (n : ℕ) :
    Fintype.card (TensorPowerProfile a n) ≠ 0 :=
  letI : Nonempty (TensorPowerProfile a n) := TensorPowerProfile.nonempty (a := a) n
  Fintype.card_ne_zero

theorem card_pos [Nonempty a] (n : ℕ) :
    0 < Fintype.card (TensorPowerProfile a n) :=
  Nat.pos_of_ne_zero (TensorPowerProfile.card_ne_zero (a := a) n)

end TensorPowerProfile

/-- Source-shaped split of a tensor power into retained `n` systems and traced
`k` systems.  The coordinate-level split is the shared
`QIT.TensorPower.takeDropEquiv` API. -/
def tensorPowerTakeDropEquiv (a : Type v) [Fintype a] [DecidableEq a]
    (n k : ℕ) :
    TensorPower a (n + k) ≃ Prod (TensorPower a n) (TensorPower a k) :=
  TensorPower.takeDropEquiv a n k

/-- Embed a permutation of the last `k` tensor positions into a permutation of
`Fin (n+k)` that fixes the first `n` positions. -/
def finRightPerm (n k : ℕ) (σ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (n + k)) :=
  ((finSumFinEquiv (m := n) (n := k)).symm.trans
    (Equiv.sumCongr (Equiv.refl (Fin n)) σ)).trans
      (finSumFinEquiv (m := n) (n := k))

@[simp]
theorem finRightPerm_castAdd (n k : ℕ) (σ : Equiv.Perm (Fin k)) (i : Fin n) :
    finRightPerm n k σ (Fin.castAdd k i) = Fin.castAdd k i := by
  simp [finRightPerm, finSumFinEquiv_apply_left]

@[simp]
theorem finRightPerm_natAdd (n k : ℕ) (σ : Equiv.Perm (Fin k)) (j : Fin k) :
    finRightPerm n k σ (Fin.natAdd n j) = Fin.natAdd n (σ j) := by
  simp [finRightPerm, finSumFinEquiv_apply_right]

@[simp]
theorem finRightPerm_symm_castAdd (n k : ℕ) (σ : Equiv.Perm (Fin k)) (i : Fin n) :
    (finRightPerm n k σ).symm (Fin.castAdd k i) = Fin.castAdd k i := by
  apply (finRightPerm n k σ).injective
  simp

@[simp]
theorem finRightPerm_symm_natAdd (n k : ℕ) (σ : Equiv.Perm (Fin k)) (j : Fin k) :
    (finRightPerm n k σ).symm (Fin.natAdd n j) = Fin.natAdd n (σ.symm j) := by
  apply (finRightPerm n k σ).injective
  simp

@[simp]
theorem tensorPowerTakeDropEquiv_fst_apply (n k : ℕ)
    (x : TensorPower a (n + k)) (i : Fin n) :
    tensorPowerEquiv n ((tensorPowerTakeDropEquiv a n k x).1) i =
      tensorPowerEquiv (n + k) x (Fin.castAdd k i) := by
  simp [tensorPowerTakeDropEquiv, TensorPower.takeDropEquiv, TensorPower.finTakeDropEquiv]

@[simp]
theorem tensorPowerTakeDropEquiv_snd_apply (n k : ℕ)
    (x : TensorPower a (n + k)) (j : Fin k) :
    tensorPowerEquiv k ((tensorPowerTakeDropEquiv a n k x).2) j =
      tensorPowerEquiv (n + k) x (Fin.natAdd n j) := by
  simp [tensorPowerTakeDropEquiv, TensorPower.takeDropEquiv, TensorPower.finTakeDropEquiv]

/-- Under the `n|k` split, a permutation embedded in the last `k` positions
acts only on the dropped/right tensor factor. -/
theorem tensorPowerTakeDropEquiv_permEquiv_right (n k : ℕ)
    (σ : Equiv.Perm (Fin k)) (x : TensorPower a (n + k)) :
    tensorPowerTakeDropEquiv a n k
        (permEquiv (a := a) (n + k) (finRightPerm n k σ) x) =
      ((tensorPowerTakeDropEquiv a n k x).1,
        permEquiv (a := a) k σ ((tensorPowerTakeDropEquiv a n k x).2)) := by
  apply Prod.ext
  · apply (tensorPowerEquiv (a := a) n).injective
    funext i
    rw [tensorPowerTakeDropEquiv_fst_apply]
    rw [tensorPowerTakeDropEquiv_fst_apply]
    rw [tensorPowerEquiv_permEquiv]
    simp
  · apply (tensorPowerEquiv (a := a) k).injective
    funext j
    rw [tensorPowerTakeDropEquiv_snd_apply]
    rw [tensorPowerEquiv_permEquiv]
    simp [tensorPowerEquiv_permEquiv, tensorPowerTakeDropEquiv_snd_apply]

theorem tensorPowerTakeDropEquiv_symm_prod_permEquiv_right (n k : ℕ)
    (σ : Equiv.Perm (Fin k)) (x : TensorPower a n) (y : TensorPower a k) :
    (tensorPowerTakeDropEquiv a n k).symm
        (x, permEquiv (a := a) k σ y) =
      permEquiv (a := a) (n + k) (finRightPerm n k σ)
        ((tensorPowerTakeDropEquiv a n k).symm (x, y)) := by
  apply (tensorPowerTakeDropEquiv a n k).injective
  simp [tensorPowerTakeDropEquiv_permEquiv_right]

/-- A globally symmetric vector remains symmetric in the right block after the
`n|k` split and after fixing the left block. -/
theorem rightBlock_mem_symmetric_of_global_mem_symmetric (n k : ℕ)
    {f : TensorPower a (n + k) → ℂ}
    (hf : f ∈ symmetricSubspace (a := a) (n + k))
    (x : TensorPower a n) :
    (fun y : TensorPower a k =>
      f ((tensorPowerTakeDropEquiv a n k).symm (x, y))) ∈
        symmetricSubspace (a := a) k := by
  rw [mem_symmetric]
  intro σ
  ext y
  have hglobal := congrFun (hf (finRightPerm n k σ))
    ((tensorPowerTakeDropEquiv a n k).symm (x, y))
  simpa [Function.comp_apply,
    tensorPowerTakeDropEquiv_symm_prod_permEquiv_right] using hglobal

private theorem kronecker_one_mulVec_apply {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (P : CMatrix β) (φ : Prod α β → ℂ) (x : Prod α β) :
    (Matrix.kronecker (1 : CMatrix α) P).mulVec φ x =
      P.mulVec (fun y : β => φ (x.1, y)) x.2 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [Fintype.sum_prod_type]
  simp [Matrix.one_apply]

/-- Matrix-vector form of `rightBlock_mem_symmetric_of_global_mem_symmetric`:
after splitting `n+k` tensor factors into `n|k`, the projector onto the
symmetric subspace of the right block fixes any globally symmetric vector. -/
theorem kronecker_one_symmetricProjection_mulVec_split_of_global_mem_symmetric
    (n k : ℕ) {f : TensorPower a (n + k) → ℂ}
    (hf : f ∈ symmetricSubspace (a := a) (n + k)) :
    (Matrix.kronecker (1 : CMatrix (TensorPower a n))
        (symmetricProjectionMatrix (a := a) k)).mulVec
      (fun x : Prod (TensorPower a n) (TensorPower a k) =>
        f ((tensorPowerTakeDropEquiv a n k).symm x)) =
      (fun x : Prod (TensorPower a n) (TensorPower a k) =>
        f ((tensorPowerTakeDropEquiv a n k).symm x)) := by
  ext x
  have hright :=
    (mem_symmetric_iff_symmetricProjectionMatrix_mulVec_eq_self
      (a := a) k
      (fun y : TensorPower a k =>
        f ((tensorPowerTakeDropEquiv a n k).symm (x.1, y)))).mp
      (rightBlock_mem_symmetric_of_global_mem_symmetric (a := a) n k hf x.1)
  have happ := congrFun hright x.2
  rw [kronecker_one_mulVec_apply]
  exact happ

/-- The right-block symmetric projector absorbs the globally symmetric
projector after the `n|k` reindexing. -/
theorem kronecker_one_symmetricProjection_mul_reindexed_symmetricProjection
    (n k : ℕ) :
    Matrix.kronecker (1 : CMatrix (TensorPower a n))
        (symmetricProjectionMatrix (a := a) k) *
      (symmetricProjectionMatrix (a := a) (n + k)).submatrix
        (tensorPowerTakeDropEquiv a n k).symm
        (tensorPowerTakeDropEquiv a n k).symm =
      (symmetricProjectionMatrix (a := a) (n + k)).submatrix
        (tensorPowerTakeDropEquiv a n k).symm
        (tensorPowerTakeDropEquiv a n k).symm := by
  ext x y
  let f : TensorPower a (n + k) → ℂ :=
    fun z => symmetricProjectionMatrix (a := a) (n + k) z
      ((tensorPowerTakeDropEquiv a n k).symm y)
  have hf : f ∈ symmetricSubspace (a := a) (n + k) := by
    change (fun z => symmetricProjection (a := a) (n + k)
      (tensorPowerBasisDelta (a := a)
        ((tensorPowerTakeDropEquiv a n k).symm y)) z) ∈
        symmetricSubspace (a := a) (n + k)
    exact symmetricProjection_mem (a := a) (n + k)
      (tensorPowerBasisDelta (a := a)
        ((tensorPowerTakeDropEquiv a n k).symm y))
  have hvec :=
    congrFun
      (kronecker_one_symmetricProjection_mulVec_split_of_global_mem_symmetric
        (a := a) n k hf) x
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, f] using hvec

/-- Splitting a tensor power at `m|0` leaves the retained component unchanged,
up to the definitional `m+0` reindexing. -/
theorem tensorPowerTakeDropEquiv_zero_fst (m : ℕ)
    (x : TensorPower a (m + 0)) :
    ((tensorPowerTakeDropEquiv a m 0) x).1 =
      (Equiv.cast (by simp) x : TensorPower a m) := by
  apply (tensorPowerEquiv (a := a) m).injective
  funext i
  rw [tensorPowerTakeDropEquiv_fst_apply]
  simp

private theorem fin_prod_univ_add {M : Type _} [CommMonoid M] (n k : ℕ)
    (f : Fin (n + k) → M) :
    (∏ i : Fin (n + k), f i) =
      (∏ i : Fin n, f (Fin.castAdd k i)) *
        (∏ j : Fin k, f (Fin.natAdd n j)) := by
  calc
    (∏ i : Fin (n + k), f i) =
        ∏ s : Sum (Fin n) (Fin k), f (finSumFinEquiv s) := by
          refine (Finset.prod_equiv finSumFinEquiv ?_ ?_).symm
          · intro s
            simp
          · intro s hs
            rfl
    _ = (∏ i : Fin n, f (Fin.castAdd k i)) *
          (∏ j : Fin k, f (Fin.natAdd n j)) := by
          simp [Fintype.prod_sum_type, finSumFinEquiv_apply_left,
            finSumFinEquiv_apply_right]

/-- Under the source `n|k` split, a tensor-power unitary factors as the
Kronecker product of its retained and traced-block tensor powers. -/
theorem unitaryTensorPowerMatrix_takeDrop_submatrix
    (n k : ℕ) (U : Matrix.unitaryGroup a ℂ) :
    (unitaryTensorPowerMatrix U (n + k) : CMatrix (TensorPower a (n + k))).submatrix
        (tensorPowerTakeDropEquiv a n k).symm
        (tensorPowerTakeDropEquiv a n k).symm =
      Matrix.kronecker
        (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n))
        (unitaryTensorPowerMatrix U k : CMatrix (TensorPower a k)) := by
  ext x y
  rw [Matrix.submatrix_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [unitaryTensorPowerMatrix_apply_eq_fin_prod,
    unitaryTensorPowerMatrix_apply_eq_fin_prod,
    unitaryTensorPowerMatrix_apply_eq_fin_prod]
  rw [fin_prod_univ_add]
  have hx_left : ∀ i : Fin n,
      tensorPowerEquiv (n + k) ((tensorPowerTakeDropEquiv a n k).symm x)
          (Fin.castAdd k i) =
        tensorPowerEquiv n x.1 i := by
    intro i
    have h := tensorPowerTakeDropEquiv_fst_apply (a := a) n k
      ((tensorPowerTakeDropEquiv a n k).symm x) i
    simpa using h.symm
  have hy_left : ∀ i : Fin n,
      tensorPowerEquiv (n + k) ((tensorPowerTakeDropEquiv a n k).symm y)
          (Fin.castAdd k i) =
        tensorPowerEquiv n y.1 i := by
    intro i
    have h := tensorPowerTakeDropEquiv_fst_apply (a := a) n k
      ((tensorPowerTakeDropEquiv a n k).symm y) i
    simpa using h.symm
  have hx_right : ∀ j : Fin k,
      tensorPowerEquiv (n + k) ((tensorPowerTakeDropEquiv a n k).symm x)
          (Fin.natAdd n j) =
        tensorPowerEquiv k x.2 j := by
    intro j
    have h := tensorPowerTakeDropEquiv_snd_apply (a := a) n k
      ((tensorPowerTakeDropEquiv a n k).symm x) j
    simpa using h.symm
  have hy_right : ∀ j : Fin k,
      tensorPowerEquiv (n + k) ((tensorPowerTakeDropEquiv a n k).symm y)
          (Fin.natAdd n j) =
        tensorPowerEquiv k y.2 j := by
    intro j
    have h := tensorPowerTakeDropEquiv_snd_apply (a := a) n k
      ((tensorPowerTakeDropEquiv a n k).symm y) j
    simpa using h.symm
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hx_left i, hy_left i]
  · apply Finset.prod_congr rfl
    intro j hj
    rw [hx_right j, hy_right j]

namespace PureVector

variable {b : Type w} [Fintype b] [DecidableEq b]

/-- Renner's rank-one-projector version of an `m`-IID vector, in the typed
`m+r` tensor-power form. It says that after some permutation, the rank-one
state of `ψ` is a product of `ν^⊗m` and an arbitrary residual pure state.
This is the finite Lean form of the definition preceding
Theorem `thm:main` [Renner2007Symmetry, sub.tex:608-611]. -/
def IsRennerMIIDIn {m r : ℕ} (ψ : PureVector (TensorPower a (m + r)))
    (ν : PureVector a) : Prop :=
  ∃ σ : Equiv.Perm (Fin (m + r)), ∃ η : PureVector (TensorPower a r),
    ψ.state =
      (((ν.tensorPower m).prod η).reindex
        (tensorPowerTakeDropEquiv a m r).symm).state.reindex
          (permEquiv (a := a) (m + r) σ).symm

/-- The pure IID tensor power is Renner `m`-IID with zero residual part. -/
theorem tensorPower_isRennerMIIDIn_zero (ν : PureVector a) (m : ℕ) :
    (ν.tensorPower m).IsRennerMIIDIn (a := a) (m := m) (r := 0) ν := by
  refine ⟨1, ν.tensorPower 0, ?_⟩
  apply State.ext
  ext x y
  simp [State.reindex_matrix, PureVector.state_matrix, rankOneMatrix_apply, PureVector.prod_amp]
  have hx : x = ((tensorPowerTakeDropEquiv a m 0) x).1 :=
    (tensorPowerTakeDropEquiv_zero_fst (a := a) m x).symm
  have hy : y = ((tensorPowerTakeDropEquiv a m 0) y).1 :=
    (tensorPowerTakeDropEquiv_zero_fst (a := a) m y).symm
  conv_lhs => rw [hx, hy]

end PureVector

namespace State

/-- Reindexing by an equivalence inverse and then by the equivalence returns
the original state. -/
theorem reindex_symm_reindex {α : Type u} {β : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ : State β) (e : α ≃ β) :
    (ρ.reindex e.symm).reindex e = ρ := by
  apply State.ext
  ext i j
  simp [State.reindex]

/-- Product-state marginal on the left subsystem. -/
theorem marginalA_prod {α : Type u} {β : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ : State α) (σ : State β) :
    (ρ.prod σ).marginalA = ρ := by
  apply State.ext
  exact State.partialTraceB_prod ρ σ

/-- IID tensor powers factor across the `n|k` tensor-power split. -/
theorem tensorPower_reindex_takeDrop (ρ : State a) (n k : ℕ) :
    (ρ.tensorPower (n + k)).reindex (tensorPowerTakeDropEquiv a n k) =
      (ρ.tensorPower n).prod (ρ.tensorPower k) := by
  apply State.ext
  ext x y
  simp only [State.reindex_matrix, Matrix.submatrix_apply]
  rw [State.tensorPower_matrix_apply, State.prod]
  change
    (∏ i : Fin (n + k),
        ρ.matrix
          (tensorPowerEquiv (n + k) ((tensorPowerTakeDropEquiv a n k).symm x) i)
          (tensorPowerEquiv (n + k) ((tensorPowerTakeDropEquiv a n k).symm y) i)) =
      (ρ.tensorPower n).matrix x.1 y.1 * (ρ.tensorPower k).matrix x.2 y.2
  rw [fin_prod_univ_add n k]
  rw [State.tensorPower_matrix_apply ρ n, State.tensorPower_matrix_apply ρ k]
  have hleft :
      (∏ i : Fin n,
          ρ.matrix
            (tensorPowerEquiv (n + k) ((tensorPowerTakeDropEquiv a n k).symm x)
              (Fin.castAdd k i))
            (tensorPowerEquiv (n + k) ((tensorPowerTakeDropEquiv a n k).symm y)
              (Fin.castAdd k i))) =
        ∏ i : Fin n, ρ.matrix (tensorPowerEquiv n x.1 i) (tensorPowerEquiv n y.1 i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hx := tensorPowerTakeDropEquiv_fst_apply (a := a) n k
      ((tensorPowerTakeDropEquiv a n k).symm x) i
    have hy := tensorPowerTakeDropEquiv_fst_apply (a := a) n k
      ((tensorPowerTakeDropEquiv a n k).symm y) i
    simp at hx hy
    rw [← hx, ← hy]
  have hright :
      (∏ j : Fin k,
          ρ.matrix
            (tensorPowerEquiv (n + k) ((tensorPowerTakeDropEquiv a n k).symm x)
              (Fin.natAdd n j))
            (tensorPowerEquiv (n + k) ((tensorPowerTakeDropEquiv a n k).symm y)
              (Fin.natAdd n j))) =
        ∏ j : Fin k, ρ.matrix (tensorPowerEquiv k x.2 j) (tensorPowerEquiv k y.2 j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hx := tensorPowerTakeDropEquiv_snd_apply (a := a) n k
      ((tensorPowerTakeDropEquiv a n k).symm x) j
    have hy := tensorPowerTakeDropEquiv_snd_apply (a := a) n k
      ((tensorPowerTakeDropEquiv a n k).symm y) j
    simp at hx hy
    rw [← hx, ← hy]
  rw [hleft, hright]

/-- Trace out the last `k` tensor factors of a state on `a^(n+k)`, using the
project tensor-power convention. -/
def traceOutLastK {n k : ℕ} (ρ : State (TensorPower a (n + k))) :
    State (TensorPower a n) :=
  (ρ.reindex (tensorPowerTakeDropEquiv a n k)).marginalA

@[simp]
theorem traceOutLastK_matrix {n k : ℕ} (ρ : State (TensorPower a (n + k))) :
    (ρ.traceOutLastK (a := a) (n := n) (k := k)).matrix =
      partialTraceB (a := TensorPower a n) (b := TensorPower a k)
        ((ρ.reindex (tensorPowerTakeDropEquiv a n k)).matrix) := rfl

/-- Tracing out the last `k` factors of a product state written across the
`n|k` split returns the retained state. -/
theorem traceOutLastK_reindex_split_prod {n k : ℕ}
    (ρ : State (TensorPower a n)) (σ : State (TensorPower a k)) :
    traceOutLastK (a := a) (n := n) (k := k)
        ((ρ.prod σ).reindex (tensorPowerTakeDropEquiv a n k).symm) = ρ := by
  simp [traceOutLastK, State.reindex_symm_reindex, State.marginalA_prod]

/-- Tracing out the final `k` systems of an IID tensor power leaves the retained
`n`-fold IID tensor power. -/
theorem traceOutLastK_tensorPower (ρ : State a) (n k : ℕ) :
    traceOutLastK (a := a) (n := n) (k := k) (ρ.tensorPower (n + k)) =
      ρ.tensorPower n := by
  simp [traceOutLastK, State.tensorPower_reindex_takeDrop, State.marginalA_prod]

/-- Tracing out the residual factor of a split product pure state preserves the
rank-one retained component. -/
theorem traceOutLastK_pure_prod {n k : ℕ}
    (ψ : PureVector (TensorPower a n)) (η : PureVector (TensorPower a k)) :
    traceOutLastK (a := a) (n := n) (k := k)
        (((ψ.prod η).state).reindex (tensorPowerTakeDropEquiv a n k).symm) =
      ψ.state := by
  rw [PureVector.prod_state, traceOutLastK_reindex_split_prod]

/-- A rank-one state whose pure vector is Renner `m`-IID in the prototype `ν`. -/
def IsRankOneRennerMIIDIn {m r : ℕ} (ρ : State (TensorPower a (m + r)))
    (ν : PureVector a) : Prop :=
  ∃ ψ : PureVector (TensorPower a (m + r)),
    ψ.IsRennerMIIDIn (a := a) (m := m) (r := r) ν ∧ ρ = ψ.state

end State

/-- The subspace spanned by Renner `m`-IID pure vectors with prototype `ν`.

This is the finite-dimensional support space behind Renner's projector
`P_id^{n,r}` [Renner2007Symmetry, sub.tex:833-852]. -/
def RennerMIIDSubspace (a : Type v) [Fintype a] [DecidableEq a]
    (m r : ℕ) (ν : PureVector a) :
    Submodule ℂ (EuclideanSpace ℂ (TensorPower a (m + r))) :=
  Submodule.span ℂ
    {v : EuclideanSpace ℂ (TensorPower a (m + r)) |
      ∃ ψ : PureVector (TensorPower a (m + r)),
        ψ.IsRennerMIIDIn (a := a) (m := m) (r := r) ν ∧
          v = WithLp.toLp 2 ψ.amp}

@[simp]
theorem pureVector_mem_RennerMIIDSubspace {m r : ℕ} {ν : PureVector a}
    {ψ : PureVector (TensorPower a (m + r))}
    (hψ : ψ.IsRennerMIIDIn (a := a) (m := m) (r := r) ν) :
    WithLp.toLp 2 ψ.amp ∈ RennerMIIDSubspace a m r ν := by
  exact Submodule.subset_span ⟨ψ, hψ, rfl⟩

/-- Orthogonal projector onto the Renner m-IID support subspace, represented
as a matrix in the tensor-power computational basis. -/
def rennerMIIDProjectorFor (m r : ℕ) (ν : PureVector a) :
    CMatrix (TensorPower a (m + r)) :=
  Matrix.toEuclideanLin.symm
    ((RennerMIIDSubspace a m r ν).starProjection.toLinearMap)

@[simp]
theorem rennerMIIDProjectorFor_toEuclideanLin (m r : ℕ) (ν : PureVector a) :
    (rennerMIIDProjectorFor (a := a) m r ν).toEuclideanLin =
      (RennerMIIDSubspace a m r ν).starProjection.toLinearMap := by
  simp [rennerMIIDProjectorFor]

/-- Source-facing notation for Renner's fixed/base projector `P_id^{m,r}`. -/
def rennerMIIDProjectorId (m r : ℕ) (ν : PureVector a) :
    CMatrix (TensorPower a (m + r)) :=
  rennerMIIDProjectorFor (a := a) m r ν

/-- Source-facing notation for Renner's rotated projector
`P_U^{m,r} = U^⊗(m+r) P_id^{m,r} (U†)^⊗(m+r)`. -/
def rennerMIIDProjector (m r : ℕ) (ν : PureVector a)
    (U : Matrix.unitaryGroup a ℂ) : CMatrix (TensorPower a (m + r)) :=
  (unitaryTensorPowerMatrix U (m + r) : CMatrix (TensorPower a (m + r))) *
    rennerMIIDProjectorId (a := a) m r ν *
      star (unitaryTensorPowerMatrix U (m + r) : CMatrix (TensorPower a (m + r)))

theorem rennerMIIDProjector_covariant (m r : ℕ) (ν : PureVector a)
    (U : Matrix.unitaryGroup a ℂ) :
    rennerMIIDProjector (a := a) m r ν U =
      (unitaryTensorPowerMatrix U (m + r) : CMatrix (TensorPower a (m + r))) *
        rennerMIIDProjectorId (a := a) m r ν *
          star (unitaryTensorPowerMatrix U (m + r) :
            CMatrix (TensorPower a (m + r))) := rfl

/-- A state is supported in the Renner m-IID span when its matrix is dominated
by the corresponding orthogonal projector. -/
def State.SupportedOnRennerMIIDSubspace {m r : ℕ}
    (ρ : State (TensorPower a (m + r))) (ν : PureVector a) : Prop :=
  ρ.matrix ≤ rennerMIIDProjectorFor (a := a) m r ν

/-- A finite source-shaped mixture of IID tensor-power states.

This is the finite expression layer used by de Finetti/post-selection routes:
an index distribution chooses a single-system state, then emits its `n`-fold
tensor power. The actual de Finetti representation theorem is deliberately
not stated here. -/
structure FiniteIidMixture (ι : Type u) (a : Type v) [Fintype ι]
    [Fintype a] [DecidableEq a] (n : ℕ) where
  /-- Nonnegative weights over the finite mixture index. -/
  probs : ι → ℝ≥0
  /-- The weights form a probability distribution. -/
  weights_sum : (∑ i, probs i) = 1
  /-- The single-system state attached to each mixture index. -/
  states : ι → State a

namespace FiniteIidMixture

variable {n : ℕ} (M : FiniteIidMixture ι a n)

/-- The ensemble of tensor-power states induced by a finite IID mixture. -/
def tensorPowerEnsemble : Ensemble ι (TensorPower a n) where
  probs := M.probs
  weights_sum := M.weights_sum
  states := fun i => (M.states i).tensorPower n

/-- The finite mixture state `∑ᵢ pᵢ ρᵢ^⊗n`. -/
def state : State (TensorPower a n) :=
  M.tensorPowerEnsemble.averageState

/-- The finite IID mixture state is the average state of its tensor-power
ensemble. -/
theorem state_eq_averageState :
    M.state = M.tensorPowerEnsemble.averageState := rfl

@[simp]
theorem tensorPowerEnsemble_probs (i : ι) :
    M.tensorPowerEnsemble.probs i = M.probs i := rfl

@[simp]
theorem tensorPowerEnsemble_states (i : ι) :
    M.tensorPowerEnsemble.states i = (M.states i).tensorPower n := rfl

/-- Matrix form of the finite IID mixture state. -/
@[simp]
theorem state_matrix :
    M.state.matrix =
      ∑ i, (M.probs i) • ((M.states i).tensorPower n).matrix := by
  rfl

/-- A finite IID mixture is fixed by every tensor-factor permutation channel. -/
theorem permutationChannel_apply_state (σ : Equiv.Perm (Fin n)) :
    (permutationChannel (a := a) n σ).applyState M.state = M.state := by
  apply State.ext
  change (permutationChannel (a := a) n σ).map M.state.matrix = M.state.matrix
  rw [M.state_matrix, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (permutationChannel (a := a) n σ).map
      ((M.probs i : ℂ) • ((M.states i).tensorPower n).matrix) =
    (M.probs i : ℂ) • ((M.states i).tensorPower n).matrix
  rw [map_smul]
  have hi := congrArg State.matrix
    (State.permutationChannel_apply_tensorPower (a := a) (M.states i) n σ)
  exact congrArg ((M.probs i : ℂ) • ·) hi

/-- A finite IID mixture state is permutation invariant. -/
theorem state_isPermutationInvariant :
    M.state.IsPermutationInvariant (a := a) := by
  intro σ
  exact M.permutationChannel_apply_state σ

/-- Twirling a finite IID mixture state leaves it unchanged. -/
theorem permutationTwirling_state :
    M.state.permutationTwirling (a := a) = M.state :=
  State.permutationTwirling_apply_of_isPermutationInvariant
    (a := a) M.state_isPermutationInvariant

/-- The one-point IID mixture attached to a single state. -/
def onePoint (ρ : State a) (n : ℕ) : FiniteIidMixture PUnit a n where
  probs := fun _ => 1
  weights_sum := by simp
  states := fun _ => ρ

/-- A one-point IID mixture is exactly the corresponding tensor-power state. -/
theorem onePoint_state (ρ : State a) (n : ℕ) :
    (onePoint (a := a) ρ n).state = ρ.tensorPower n := by
  rw [state]
  exact Ensemble.averageState_of_constant
    ((onePoint (a := a) ρ n).tensorPowerEnsemble) (ρ.tensorPower n)
    (fun i => by cases i; rfl)

end FiniteIidMixture

/-- A finite weighted mixture of pure-state projectors.

This is the finite Lean substitute layer for the source integral over
rank-one projectors in Renner's de Finetti theorem
[Renner2007Symmetry, sub.tex:618-633]. -/
structure FinitePureStateMixture (ι : Type u) (a : Type v) [Fintype ι]
    [Fintype a] [DecidableEq a] where
  /-- Nonnegative weights over the finite mixture index. -/
  probs : ι → ℝ≥0
  /-- The weights form a probability distribution. -/
  weights_sum : (∑ i, probs i) = 1
  /-- The pure vector attached to each mixture index. -/
  vectors : ι → PureVector a

namespace FinitePureStateMixture

variable (M : FinitePureStateMixture ι a)

/-- The state ensemble induced by a finite pure-state mixture. -/
def toEnsemble : Ensemble ι a where
  probs := M.probs
  weights_sum := M.weights_sum
  states := fun i => (M.vectors i).state

/-- The barycentric state `∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|`. -/
def state : State a :=
  M.toEnsemble.averageState

/-- Matrix form of the finite pure-state barycenter. -/
@[simp]
theorem state_matrix :
    M.state.matrix = ∑ i, (M.probs i) • (M.vectors i).state.matrix := by
  rfl

/-- View a finite pure-state mixture as a finite IID mixture after taking
one-system pure states as density states. -/
def toFiniteIidMixture (n : ℕ) : FiniteIidMixture ι a n where
  probs := M.probs
  weights_sum := M.weights_sum
  states := fun i => (M.vectors i).state

/-- The tensor-power barycenter generated by this pure-state mixture. -/
def tensorPowerState (n : ℕ) : State (TensorPower a n) :=
  (M.toFiniteIidMixture n).state

/-- Tensor-power pure mixtures are exactly the existing `FiniteIidMixture`
construction applied to the corresponding rank-one states. -/
theorem tensorPower_state_eq_finiteIidMixture_state (n : ℕ) :
    M.tensorPowerState n = (M.toFiniteIidMixture n).state := rfl

/-- Matrix form of the tensor-power barycenter. -/
@[simp]
theorem tensorPowerState_matrix (n : ℕ) :
    (M.tensorPowerState n).matrix =
      ∑ i, (M.probs i) • ((M.vectors i).state.tensorPower n).matrix := by
  rfl

end FinitePureStateMixture

/-- A finite mixture whose pure components satisfy Renner's rank-one
`m`-IID-in-`ν` condition.

The source theorem uses a measure over one-dimensional projectors `ν` and
density operators supported on the span of `m`-IID vectors in `ν`. This finite
wrapper records the rank-one/vector-level component support that the later
Renner approximation theorem can average. -/
structure FiniteRennerMIIDMixture (ι : Type u) (a : Type v) [Fintype ι]
    [Fintype a] [DecidableEq a] (m r : ℕ) where
  /-- Nonnegative weights over the finite mixture index. -/
  probs : ι → ℝ≥0
  /-- The weights form a probability distribution. -/
  weights_sum : (∑ i, probs i) = 1
  /-- Pure components on `a^(m+r)`. -/
  vectors : ι → PureVector (TensorPower a (m + r))
  /-- The single-system pure vector `ν` witnessing the component's `m`-IID part. -/
  bases : ι → PureVector a
  /-- Each component is Renner `m`-IID in its corresponding rank-one projector. -/
  renner_miid : ∀ i, (vectors i).IsRennerMIIDIn (a := a) (m := m) (r := r) (bases i)

namespace FiniteRennerMIIDMixture

variable {m r : ℕ} (M : FiniteRennerMIIDMixture ι a m r)

/-- Forget the Renner support witnesses and retain the finite pure-state
barycenter. -/
def toFinitePureStateMixture :
    FinitePureStateMixture ι (TensorPower a (m + r)) where
  probs := M.probs
  weights_sum := M.weights_sum
  vectors := M.vectors

/-- The finite barycenter of Renner `m`-IID pure components. -/
def state : State (TensorPower a (m + r)) :=
  M.toFinitePureStateMixture.state

/-- Matrix form of the finite Renner `m`-IID barycenter. -/
@[simp]
theorem state_matrix :
    M.state.matrix = ∑ i, (M.probs i) • (M.vectors i).state.matrix := by
  rfl

/-- Each component state satisfies the rank-one Renner `m`-IID wrapper from
the nested partial-trace API. -/
theorem component_isRankOneRennerMIIDIn (i : ι) :
    (M.vectors i).state.IsRankOneRennerMIIDIn (a := a) (m := m) (r := r)
      (M.bases i) := by
  exact ⟨M.vectors i, M.renner_miid i, rfl⟩

end FiniteRennerMIIDMixture

end

end QIT
