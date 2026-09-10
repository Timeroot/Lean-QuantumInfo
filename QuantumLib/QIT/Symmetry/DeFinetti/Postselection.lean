/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Symmetry.DeFinetti.RennerProjectors
public import QuantumLib.QIT.Util.MatrixInstances

/-!
# The Christandl--König--Renner post-selection theorem

`postSelection_diamondTraceDistance_le_profile_count`: if the difference of two channels on
`TensorPower a n` is covariant under permutations of the tensor factors
(`PostSelectionCovariantDifference`), then their diamond trace distance is at most
`Fintype.card (TensorPowerProfile (a × a) n)` times the action of that difference on the single
state `ckrPostSelectionPurifiedReferenceState n`.  `postSelection_diamondTraceDistance_le_choose`
is the same bound with the factor as the binomial `(n + (Fintype.card a) ^ 2 - 1).choose n`.  A
permutation-covariant comparison over all reference systems therefore reduces, at polynomial cost,
to one fixed input.

The reduction runs in three steps.

* *Purify.*  A mixed input-reference state is controlled by the canonical purification of the whole
  input-reference system, since the mixed action is a partial trace of the pure one and partial
  trace contracts trace norm; a pure input-reference state is in turn controlled by the canonical
  purification of its input marginal, by the reference-isometry adapter in `RennerProjectors`.
* *Symmetrize.*  Covariance makes the action invariant under permuting the input factors, so it is
  unchanged by `MState.inputPermutationLabelExtension`, the twirl `1/n! ∑_π (π ⊗ id)(ω) ⊗ |π⟩⟨π|`
  that records the applied permutation in a classical register.  That extension has a permutation
  invariant input marginal, and its action is a block-diagonal trace-norm sum — which is what the
  `Classical.blockDiagonal` lemmas in the first half of the file compute.
* *Extract.*  A permutation-invariant input marginal makes the purification symmetric, so the
  profile isometry `ckrProfileIsometryMatrix` compresses it onto the profile register.  Reading
  that compression as the trace-nonincreasing CP map `ckrProfileCoordinateEffect` and commuting the
  channel difference past it produces the CKR reference state and the profile-count factor.

The last section is about the symmetric-support hypothesis itself.
`MState.symmetricProjectionNormalizedState` renormalizes the sandwich `P_sym ρ P_sym`, which is
supported on the symmetric subspace by construction and hence dominated by
`symmetricProjectionReferenceState`, and the closing lemmas derive matrix domination and finite-IID
domination from a bound assumed on every tensor power.
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

private theorem dropRightUnitMatrix_kron_id_traceEffectToUnit_apply
    {α β : Type u} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {E : CMatrix β} (hE : E.PosSemidef)
    (X : CMatrix (α × β)) (x y : α) :
    dropRightUnitMatrix
        ((MatrixMap.kron (CPTPOp.id (dIn := α)).map (MatrixMap.traceEffectToUnit E)) X)
        x y =
      ∑ p : β, ∑ q : β, X (x, p) (y, q) * E q p := by
  classical
  show MatrixMap.kron (CPTPOp.id (dIn := α)).map (MatrixMap.traceEffectToUnit E) X
      (x, PUnit.unit) (y, PUnit.unit) = _
  rw [MatrixMap.kron_idChannel_left_apply_slice,
    MatrixMap.traceEffectToUnit_apply_of_posSemidef hE]
  simp [Matrix.trace, Matrix.mul_apply]

private theorem matrixMap_trace_weight_commute
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (Δ : MatrixMap α β) (A : γ → γ → CMatrix α) (E : CMatrix γ)
    (x y : β) :
    ((Matrix.of fun j j' => Δ (A j j') x y) * E).trace =
      Δ (fun i i' => ((Matrix.of fun j j' => A j j' i i') * E).trace) x y := by
  simp [Matrix.trace, Matrix.mul_apply]
  have hmap :
      Δ (fun i i' => ∑ j : γ, ∑ j' : γ, A j j' i i' * E j' j) =
        ∑ j : γ, ∑ j' : γ, E j' j • Δ (A j j') := by
    have hfun : (fun i i' => ∑ j : γ, ∑ j' : γ, A j j' i i' * E j' j) =
        ∑ j : γ, ∑ j' : γ, E j' j • A j j' := by
      ext i i'
      simp [Matrix.sum_apply, Matrix.smul_apply, mul_comm]
    rw [hfun]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [map_smul]
  have happ := congrFun (congrFun hmap x) y
  rw [happ]
  simp [Matrix.sum_apply, Matrix.smul_apply, mul_comm]

private def assocRightMatrix
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (X : CMatrix (α × (β × γ))) : CMatrix ((α × β) × γ) :=
  X.submatrix (Equiv.prodAssoc α β γ) (Equiv.prodAssoc α β γ)

private theorem traceNorm_assocRightMatrix
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (X : CMatrix (α × (β × γ))) :
    traceNorm (assocRightMatrix X) = traceNorm X := by
  simpa [assocRightMatrix] using
    (traceNorm_submatrix_equiv (Equiv.prodAssoc α β γ) X)

private theorem assocRightMatrix_isHermitian
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    {X : CMatrix (α × (β × γ))} (hX : X.IsHermitian) :
    (assocRightMatrix X).IsHermitian := by
  simpa [assocRightMatrix] using hX.submatrix (Equiv.prodAssoc α β γ)

private theorem trace_assocRightMatrix
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (X : CMatrix (α × (β × γ))) :
    (assocRightMatrix X).trace = X.trace := by
  rw [assocRightMatrix]
  rw [Matrix.trace]
  rw [Matrix.trace]
  exact Fintype.sum_equiv (Equiv.prodAssoc α β γ)
    (fun x : (α × β) × γ =>
      X (Equiv.prodAssoc α β γ x) (Equiv.prodAssoc α β γ x))
    (fun y : α × (β × γ) => X y y)
    (by intro x; rfl)

private theorem dropRightUnitMatrix_action_traceEffectToUnit_commute
    {b : Type w} [Fintype b] [DecidableEq b]
    [Nonempty a] {n : ℕ}
    (Δ : MatrixMap (TensorPower a n) b)
    {E : CMatrix (ckrPurifyingRegister a n)} (hE : E.PosSemidef) :
    dropRightUnitMatrix
      ((MatrixMap.kron (CPTPOp.id (dIn := b × QIT.TensorPower a n)).map
          (MatrixMap.traceEffectToUnit E))
        (assocRightMatrix
          ((MatrixMap.kron Δ
              (CPTPOp.id (dIn := QIT.TensorPower a n × ckrPurifyingRegister a n)).map)
            (ckrPostSelectionPurifiedReferenceState (a := a) n).m))) =
    MatrixMap.kron Δ (CPTPOp.id (dIn := TensorPower a n)).map
      ((dropRightUnitMatrix
          ((MatrixMap.kron
              (CPTPOp.id (dIn := TensorPower (a × a) n)).map
              (MatrixMap.traceEffectToUnit E))
            (ckrPurifiedReferenceState (a := a) n).m)).submatrix
        (tensorPowerProdEquiv a a n).symm (tensorPowerProdEquiv a a n).symm) := by
  ext br br'
  simp [-CPTPOp.id_map, assocRightMatrix, dropRightUnitMatrix,
    MatrixMap.kron_idChannel_apply_slice, MatrixMap.kron_idChannel_left_apply_slice,
    MatrixMap.traceEffectToUnit_apply_of_posSemidef hE,
    ckrPostSelectionPurifiedReferenceState, ckrPostSelectionPurifiedReferenceStatePair]
  exact matrixMap_trace_weight_commute Δ
    (fun j j' => fun i i' =>
      (ckrPurifiedReferenceVector (a := a) n).vec
        ((tensorPowerProdEquiv a a n).symm (i, br.2), j) *
      star ((ckrPurifiedReferenceVector (a := a) n).vec
        ((tensorPowerProdEquiv a a n).symm (i', br'.2), j')))
    E br.1 br'.1

end QIT

namespace MState

variable {n : ℕ}

/-- Reindex the CKR permutation-label extension from label-first block form to
the input-first convention used by `ancillaNormalizedTraceAction`. -/
def inputPermutationLabelEquiv {r : Type w} {n : ℕ} :
    Equiv (Equiv.Perm (Fin n) × (TensorPower a n × r))
      (TensorPower a n × (r × Equiv.Perm (Fin n))) where
  toFun x := (x.2.1, x.2.2, x.1)
  invFun x := (x.2.2, x.1, x.2.1)
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; cases x with | mk xA xrπ => cases xrπ; rfl

private theorem classical_blockDiagonal_posSemidef {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (blocks : ι → CMatrix β) (hblocks : ∀ i, (blocks i).PosSemidef) :
    (Classical.blockDiagonal blocks).PosSemidef := by
  classical
  unfold Classical.blockDiagonal
  exact Matrix.posSemidef_sum Finset.univ fun i _ =>
    (posSemidef_single i).kronecker (hblocks i)

private theorem classical_blockDiagonal_trace {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (blocks : ι → CMatrix β) :
    (Classical.blockDiagonal blocks).trace = ∑ i, (blocks i).trace := by
  classical
  unfold Classical.blockDiagonal
  simp only [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.trace, Matrix.kronecker, Matrix.single]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hj
    have hji : ¬ i = j := fun hij => hj hij.symm
    simp [hji]

private theorem trace_mul_block_decomp_complex {ι : Type w} {β : Type x}
    [Fintype ι] [Fintype β]
    {H P : CMatrix (ι × β)}
    (hoff : ∀ (i j : ι) (x y : β), i ≠ j → H (i, x) (j, y) = 0) :
    (H * P).trace = ∑ i : ι, ((Classical.block H i i) * Classical.block P i i).trace := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Classical.block, Fintype.sum_prod_type]
  calc
    (∑ i : ι, ∑ x : β, ∑ j : ι, ∑ y : β,
        H (i, x) (j, y) * P (j, y) (i, x)) =
      ∑ i : ι, ∑ x : β, ∑ y : β,
        H (i, x) (i, y) * P (i, y) (i, x) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun j _ hji => by
          have hij : i ≠ j := fun h => hji h.symm
          simp [hoff i j x, hij])]
    _ = ∑ i : ι, ∑ x : β, ∑ y : β,
        H (i, x) (i, y) * P (i, y) (i, x) := rfl

private theorem trace_mul_block_decomp {ι : Type w} {β : Type x}
    [Fintype ι] [Fintype β]
    {H P : CMatrix (ι × β)}
    (hoff : ∀ (i j : ι) (x y : β), i ≠ j → H (i, x) (j, y) = 0) :
    ((H * P).trace).re =
      ∑ i : ι, ((((Classical.block H i i) * Classical.block P i i).trace).re) := by
  rw [trace_mul_block_decomp_complex (H := H) (P := P) hoff]
  simp

private theorem classical_block_posSemidef {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {M : CMatrix (ι × β)} (hM : M.PosSemidef) (i : ι) :
    (Classical.block M i i).PosSemidef := by
  exact hM.submatrix (fun x : β => (i, x))

private theorem classical_block_le_one {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {M : CMatrix (ι × β)} (hM : M ≤ 1) (i : ι) :
    Classical.block M i i ≤ 1 := by
  rw [Matrix.le_iff] at hM ⊢
  have h := hM.submatrix (fun x : β => (i, x))
  convert h using 1
  ext x y
  simp [Classical.block, Matrix.sub_apply, Matrix.one_apply]

private theorem classical_blockDiagonal_offdiag {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (blocks : ι → CMatrix β) {i j : ι} (hij : i ≠ j) (x y : β) :
    Classical.blockDiagonal blocks (i, x) (j, y) = 0 := by
  have h := congrFun (congrFun (Classical.blockDiagonal_block_ne blocks hij) x) y
  simpa [Classical.block] using h

private theorem classical_blockDiagonal_block_self_apply {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (blocks : ι → CMatrix β) (i : ι) (x y : β) :
    Classical.blockDiagonal blocks (i, x) (i, y) = blocks i x y := by
  have h := congrFun (congrFun (Classical.blockDiagonal_block_self blocks i) x) y
  simpa [Classical.block] using h

private theorem classical_blockDiagonal_isHermitian {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (blocks : ι → CMatrix β) (hblocks : ∀ i, (blocks i).IsHermitian) :
    (Classical.blockDiagonal blocks).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext x y
  rcases x with ⟨xi, xb⟩
  rcases y with ⟨yi, yb⟩
  change star (Classical.blockDiagonal blocks (yi, yb) (xi, xb)) =
    Classical.blockDiagonal blocks (xi, xb) (yi, yb)
  by_cases hxy : xi = yi
  · subst hxy
    rw [classical_blockDiagonal_block_self_apply, classical_blockDiagonal_block_self_apply]
    simpa [Matrix.IsHermitian, Matrix.conjTranspose] using congrFun (congrFun (hblocks xi) xb) yb
  · have hyx : yi ≠ xi := fun h => hxy h.symm
    rw [classical_blockDiagonal_offdiag blocks hyx, classical_blockDiagonal_offdiag blocks hxy]
    simp

private theorem posPart_trace_blockDiagonal_le_sum {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (blocks : ι → CMatrix β)
    (hblocks : ∀ i, (blocks i).IsHermitian) :
    (((Classical.blockDiagonal blocks)⁺).trace).re ≤ ∑ i : ι, (((blocks i)⁺).trace).re := by
  classical
  let H : CMatrix (ι × β) := Classical.blockDiagonal blocks
  have hH : H.IsHermitian := classical_blockDiagonal_isHermitian blocks hblocks
  let P : CMatrix (ι × β) := positiveSpectralProjector H hH
  have hscore : ((H * P).trace).re = (H⁺).trace.re := by
    simpa [P] using positiveSpectralProjector_score_eq_posPart_trace H hH
  rw [← hscore]
  rw [trace_mul_block_decomp (H := H) (P := P) (by
    intro i j x y hij
    exact classical_blockDiagonal_offdiag blocks hij x y)]
  refine Finset.sum_le_sum fun i _ => ?_
  have hblockH : Classical.block H i i = blocks i := by
    dsimp [H]
    exact Classical.blockDiagonal_block_self blocks i
  rw [hblockH]
  exact hermitian_trace_mul_effect_le_posPart_trace (blocks i) (Classical.block P i i)
    (hblocks i) (classical_block_posSemidef (positiveSpectralProjector_posSemidef H hH) i)
    (classical_block_le_one (positiveSpectralProjector_le_one H hH) i)

private theorem classical_blockDiagonal_le_one {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (blocks : ι → CMatrix β) (hblocks : ∀ i, blocks i ≤ 1) :
    Classical.blockDiagonal blocks ≤ 1 := by
  rw [Matrix.le_iff]
  have hcomp :
      (1 : CMatrix (ι × β)) - Classical.blockDiagonal blocks =
        Classical.blockDiagonal (fun i => (1 : CMatrix β) - blocks i) := by
    ext x y
    rcases x with ⟨xi, xb⟩
    rcases y with ⟨yi, yb⟩
    by_cases hxy : xi = yi
    · subst hxy
      change (1 : CMatrix (ι × β)) (xi, xb) (xi, yb) -
          Classical.blockDiagonal blocks (xi, xb) (xi, yb) =
        Classical.blockDiagonal (fun i => (1 : CMatrix β) - blocks i) (xi, xb) (xi, yb)
      rw [classical_blockDiagonal_block_self_apply blocks xi xb yb]
      rw [classical_blockDiagonal_block_self_apply
        (fun i => (1 : CMatrix β) - blocks i) xi xb yb]
      simp [Matrix.sub_apply, Matrix.one_apply]
    · have hpair : (xi, xb) ≠ (yi, yb) := by
        intro h
        exact hxy (Prod.ext_iff.mp h).1
      change (1 : CMatrix (ι × β)) (xi, xb) (yi, yb) -
          Classical.blockDiagonal blocks (xi, xb) (yi, yb) =
        Classical.blockDiagonal (fun i => (1 : CMatrix β) - blocks i) (xi, xb) (yi, yb)
      rw [classical_blockDiagonal_offdiag blocks hxy xb yb]
      rw [classical_blockDiagonal_offdiag (fun i => (1 : CMatrix β) - blocks i) hxy xb yb]
      simp [hpair]
  rw [hcomp]
  exact classical_blockDiagonal_posSemidef (fun i => (1 : CMatrix β) - blocks i) (fun i => by
    rw [← Matrix.le_iff]
    exact hblocks i)

private theorem sum_posPart_trace_le_blockDiagonal {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (blocks : ι → CMatrix β)
    (hblocks : ∀ i, (blocks i).IsHermitian) :
    (∑ i : ι, (((blocks i)⁺).trace).re) ≤
      (((Classical.blockDiagonal blocks)⁺).trace).re := by
  classical
  let H : CMatrix (ι × β) := Classical.blockDiagonal blocks
  have hH : H.IsHermitian := classical_blockDiagonal_isHermitian blocks hblocks
  let P : CMatrix (ι × β) :=
    Classical.blockDiagonal (fun i : ι => positiveSpectralProjector (blocks i) (hblocks i))
  have hPpos : P.PosSemidef := by
    dsimp [P]
    exact classical_blockDiagonal_posSemidef _
      (fun i => positiveSpectralProjector_posSemidef (blocks i) (hblocks i))
  have hPle : P ≤ 1 := by
    dsimp [P]
    exact classical_blockDiagonal_le_one _
      (fun i => positiveSpectralProjector_le_one (blocks i) (hblocks i))
  have htrace :
      ((H * P).trace).re =
        ∑ i : ι, ((((blocks i) * positiveSpectralProjector (blocks i) (hblocks i)).trace).re) := by
    simpa [H, P] using trace_mul_block_decomp
      (H := H) (P := P) (by
        intro i j x y hij
        dsimp [H]
        exact classical_blockDiagonal_offdiag blocks hij x y)
  calc
    (∑ i : ι, (((blocks i)⁺).trace).re) =
        ∑ i : ι, ((((blocks i) * positiveSpectralProjector (blocks i) (hblocks i)).trace).re) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact (positiveSpectralProjector_score_eq_posPart_trace (blocks i) (hblocks i)).symm
    _ = ((H * P).trace).re := htrace.symm
    _ ≤ ((H⁺).trace).re := by
      exact hermitian_trace_mul_effect_le_posPart_trace H P hH hPpos hPle

private theorem traceNorm_classical_blockDiagonal_eq_sum {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (blocks : ι → CMatrix β)
    (hblocks : ∀ i, (blocks i).IsHermitian) (htr : ∀ i, (blocks i).trace = 0) :
    traceNorm (Classical.blockDiagonal blocks) = ∑ i : ι, traceNorm (blocks i) := by
  classical
  let H : CMatrix (ι × β) := Classical.blockDiagonal blocks
  have hH : H.IsHermitian := classical_blockDiagonal_isHermitian blocks hblocks
  have hHtr : H.trace = 0 := by
    have htrace : H.trace = ∑ i : ι, (blocks i).trace := by
      dsimp [H]
      exact classical_blockDiagonal_trace blocks
    rw [htrace]
    simp [htr]
  have hnormH := traceNorm_eq_two_posPart_trace_re_of_trace_zero H hH hHtr
  have hnormBlocks :
      (∑ i : ι, traceNorm (blocks i)) =
        ∑ i : ι, 2 * (((blocks i)⁺).trace).re := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact traceNorm_eq_two_posPart_trace_re_of_trace_zero (blocks i) (hblocks i) (htr i)
  rw [hnormH, hnormBlocks, ← Finset.mul_sum]
  congr 1
  exact le_antisymm
    (posPart_trace_blockDiagonal_le_sum blocks hblocks)
    (sum_posPart_trace_le_blockDiagonal blocks hblocks)

/-- CKR permutation-labelled extension
`1/n! ∑π (π ⊗ id)(ω) ⊗ |π⟩⟨π|`, reindexed so the channel input remains the
left factor.  Its input marginal is the ordinary input permutation twirl. -/
def inputPermutationLabelExtension {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : MState (TensorPower a n × r)) :
    MState (TensorPower a n × (r × Equiv.Perm (Fin n))) := .ofMatrix
  (matrix :=
    (Classical.blockDiagonal (fun π : Equiv.Perm (Fin n) =>
      ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
        (((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m))
      ).submatrix
        (inputPermutationLabelEquiv (a := a) (r := r) (n := n)).symm
        (inputPermutationLabelEquiv (a := a) (r := r) (n := n)).symm)
  (pos := by
    classical
    apply Matrix.PosSemidef.submatrix
    apply classical_blockDiagonal_posSemidef
    intro π
    have hcR : 0 ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ :=
      inv_nonneg.mpr (Nat.cast_nonneg _)
    have hcC : 0 ≤ ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ)) := by
      exact_mod_cast hcR
    exact ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).psd).smul hcC)
  (trace_eq_one := by
    classical
    rw [Matrix.trace_submatrix]
    rw [classical_blockDiagonal_trace]
    simp only [Matrix.trace_smul, DensityOp.tr', Finset.sum_const, nsmul_eq_mul]
    have hcard_ne : (Fintype.card (Equiv.Perm (Fin n)) : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero :
        Fintype.card (Equiv.Perm (Fin n)) ≠ 0)
    have hcard_neR : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero :
        Fintype.card (Equiv.Perm (Fin n)) ≠ 0)
    simp only [smul_eq_mul, mul_one] at *
    change (Fintype.card (Equiv.Perm (Fin n)) : ℂ) *
        (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) = 1
    norm_num [hcard_ne])

@[simp]
theorem inputPermutationLabelExtension_matrix {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : MState (TensorPower a n × r)) :
    (ω.inputPermutationLabelExtension (a := a) (r := r)).m =
      (Classical.blockDiagonal (fun π : Equiv.Perm (Fin n) =>
        ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
          (((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m))
        ).submatrix
          (inputPermutationLabelEquiv (a := a) (r := r) (n := n)).symm
          (inputPermutationLabelEquiv (a := a) (r := r) (n := n)).symm :=
  MState.matrix_ofMatrix _ _ _

private theorem inputPermutationLabelExtension_slice_same
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : MState (TensorPower a n × r))
    (π : Equiv.Perm (Fin n)) (i i' : TensorPower a n) (j j' : r) :
    (ω.inputPermutationLabelExtension (a := a) (r := r)).m
      (i, (j, π)) (i', (j', π)) =
      ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) *
        (((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m
          (i, j) (i', j')) := by
  rw [MState.inputPermutationLabelExtension_matrix]
  simp only [MState.inputPermutationLabelEquiv, Classical.blockDiagonal, Matrix.submatrix_apply,
    Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.single,
    Matrix.smul_apply, Equiv.coe_fn_symm_mk]
  rw [Finset.sum_eq_single π]
  · simp
  · intro σ _ hσ
    have hne : σ ≠ π := hσ
    simp [hne]
  · intro hnot
    simp at hnot

private theorem inputPermutationLabelExtension_slice_ne
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : MState (TensorPower a n × r))
    {π σ : Equiv.Perm (Fin n)} (hπσ : π ≠ σ)
    (i i' : TensorPower a n) (j j' : r) :
    (ω.inputPermutationLabelExtension (a := a) (r := r)).m
      (i, (j, π)) (i', (j', σ)) = 0 := by
  rw [MState.inputPermutationLabelExtension_matrix]
  simp only [MState.inputPermutationLabelEquiv, Classical.blockDiagonal, Matrix.submatrix_apply,
    Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.single,
    Matrix.smul_apply, Equiv.coe_fn_symm_mk]
  refine Finset.sum_eq_zero fun τ _ => ?_
  by_cases hτπ : τ = π
  · subst hτπ
    simp [hπσ]
  · simp [hτπ]

/-- The input marginal of the permutation-labelled extension is the ordinary
input permutation twirl. -/
theorem inputPermutationLabelExtension_traceRight_eq_inputPermutationTwirling_traceRight
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : MState (TensorPower a n × r)) :
    (ω.inputPermutationLabelExtension (a := a) (r := r)).traceRight =
      (ω.inputPermutationTwirling (a := a) (r := r)).traceRight := by
  apply MState.ext
  rw [MState.traceRight_m, MState.traceRight_m]
  ext i i'
  simp only [Matrix.traceRight, Matrix.of_apply]
  rw [Fintype.sum_prod_type]
  simp only [inputPermutationLabelExtension_slice_same]
  simp [MState.inputPermutationTwirling, Matrix.smul_apply, Matrix.sum_apply,
    Finset.mul_sum]

/-- The input marginal of the permutation-labelled extension is permutation
invariant. -/
theorem inputPermutationLabelExtension_traceRight_isPermutationInvariant
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : MState (TensorPower a n × r)) :
    (ω.inputPermutationLabelExtension (a := a) (r := r)).traceRight.IsPermutationInvariant
      (a := a) := by
  rw [inputPermutationLabelExtension_traceRight_eq_inputPermutationTwirling_traceRight]
  exact inputPermutationTwirling_traceRight_isPermutationInvariant (a := a) (r := r) ω

private def outputPermutationLabelEquiv {r : Type w} {b : Type x} {n : ℕ} :
    Equiv (b × (r × Equiv.Perm (Fin n)))
      (Equiv.Perm (Fin n) × (b × r)) where
  toFun x := (x.2.2, x.1, x.2.1)
  invFun x := (x.2.1, x.2.2, x.1)
  left_inv := by intro x; cases x with | mk xb xrπ => cases xrπ; rfl
  right_inv := by intro x; cases x with | mk xπ xbr => cases xbr; rfl

private theorem inputPermutationLabelExtension_action_block_same
    {r : Type w} [Fintype r] [DecidableEq r]
    {b : Type x} [Fintype b] [DecidableEq b]
    {n : ℕ} (Δ : MatrixMap (TensorPower a n) b)
    (ω : MState (TensorPower a n × r)) (π : Equiv.Perm (Fin n)) :
    MatrixMap.blockCompression (β := b × r) π
      ((MatrixMap.kron Δ (CPTPOp.id (dIn := r × Equiv.Perm (Fin n))).map
        (ω.inputPermutationLabelExtension (a := a) (r := r)).m).submatrix
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm) =
      (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
        MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map
          ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m) := by
  ext br br'
  rcases br with ⟨bo, rr⟩
  rcases br' with ⟨bo', rr'⟩
  let c : ℂ := (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ)
  let X : CMatrix (TensorPower a n) := Matrix.of fun i i' =>
    (((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m
      (i, rr) (i', rr')
  have hslice :
      (Matrix.of fun i i' =>
        (ω.inputPermutationLabelExtension (a := a) (r := r)).m
          (i, (rr, π)) (i', (rr', π))) = c • X := by
    ext i i'
    exact inputPermutationLabelExtension_slice_same
      (a := a) (r := r) (n := n) ω π i i' rr rr'
  have hlhs :
      MatrixMap.blockCompression (β := b × r) π
          ((MatrixMap.kron Δ (CPTPOp.id (dIn := r × Equiv.Perm (Fin n))).map
            (ω.inputPermutationLabelExtension (a := a) (r := r)).m).submatrix
              (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm
              (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm)
          (bo, rr) (bo', rr') =
        Δ (Matrix.of fun i i' =>
          (ω.inputPermutationLabelExtension (a := a) (r := r)).m
            (i, (rr, π)) (i', (rr', π))) bo bo' :=
    MatrixMap.kron_idChannel_apply_slice (r := r × Equiv.Perm (Fin n)) Δ
      (ω.inputPermutationLabelExtension (a := a) (r := r)).m (bo, (rr, π)) (bo', (rr', π))
  have hrhs :
      ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
          MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map
            ((((permutationChannel (a := a) n π).prod
              (CPTPOp.id (dIn := r))) ω).m))
          (bo, rr) (bo', rr') = c • Δ X bo bo' :=
    congrArg (fun z => c • z)
      (MatrixMap.kron_idChannel_apply_slice (r := r) Δ
        ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m)
        (bo, rr) (bo', rr'))
  rw [hlhs, hrhs, hslice, LinearMap.map_smul]
  rfl

private theorem inputPermutationLabelExtension_action_block_ne
    {r : Type w} [Fintype r] [DecidableEq r]
    {b : Type x} [Fintype b] [DecidableEq b]
    {n : ℕ} (Δ : MatrixMap (TensorPower a n) b)
    (ω : MState (TensorPower a n × r)) {π σ : Equiv.Perm (Fin n)}
    (hπσ : π ≠ σ) (br br' : b × r) :
    ((MatrixMap.kron Δ (CPTPOp.id (dIn := r × Equiv.Perm (Fin n))).map
        (ω.inputPermutationLabelExtension (a := a) (r := r)).m).submatrix
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm)
        (π, br) (σ, br') = 0 := by
  rcases br with ⟨bo, rr⟩
  rcases br' with ⟨bo', rr'⟩
  simp only [Matrix.submatrix_apply]
  rw [MatrixMap.kron_idChannel_apply_slice]
  change Δ
      (fun i i' =>
        (ω.inputPermutationLabelExtension (a := a) (r := r)).m
          (i, (rr, π)) (i', (rr', σ))) bo bo' = 0
  have hslice :
      (fun i i' =>
        (ω.inputPermutationLabelExtension (a := a) (r := r)).m
          (i, (rr, π)) (i', (rr', σ))) = 0 := by
    ext i i'
    exact inputPermutationLabelExtension_slice_ne
      (a := a) (r := r) (n := n) ω hπσ i i' rr rr'
  rw [hslice]
  exact congrFun (congrFun (map_zero Δ) bo) bo'

private theorem inputPermutationLabelExtension_action_reindexed_eq_blockDiagonal
    {r : Type w} [Fintype r] [DecidableEq r]
    {b : Type x} [Fintype b] [DecidableEq b]
    {n : ℕ} (Δ : MatrixMap (TensorPower a n) b)
    (ω : MState (TensorPower a n × r)) :
    ((MatrixMap.kron Δ (CPTPOp.id (dIn := r × Equiv.Perm (Fin n))).map
        (ω.inputPermutationLabelExtension (a := a) (r := r)).m).submatrix
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm) =
      Classical.blockDiagonal (fun π : Equiv.Perm (Fin n) =>
        (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
          MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map
            ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m)) := by
  ext x y
  rcases x with ⟨π, br⟩
  rcases y with ⟨σ, br'⟩
  by_cases hπσ : π = σ
  · subst hπσ
    have hblock := congrFun (congrFun
      (inputPermutationLabelExtension_action_block_same
        (a := a) (r := r) (b := b) Δ ω π) br) br'
    have hself := classical_blockDiagonal_block_self_apply
      (fun π : Equiv.Perm (Fin n) =>
        (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
          MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map
            ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m))
      π br br'
    exact hblock.trans hself.symm
  · rw [inputPermutationLabelExtension_action_block_ne
      (a := a) (r := r) (b := b) Δ ω hπσ br br']
    rw [classical_blockDiagonal_offdiag
      (fun π : Equiv.Perm (Fin n) =>
        (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
          MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map
            ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m))
      hπσ br br']

private theorem cMatrix_isHermitian_real_smul {β : Type x} [Fintype β] [DecidableEq β]
    {c : ℝ} {M : CMatrix β} (hM : M.IsHermitian) :
    (((c : ℂ) • M) : CMatrix β).IsHermitian := by
  exact hM.smul (by simp [IsSelfAdjoint])

private theorem inputPermutationLabelExtension_channelDifference_action_traceNorm_eq_sum
    {r : Type w} [Fintype r] [DecidableEq r]
    {b : Type x} [Fintype b] [DecidableEq b]
    {n : ℕ} (Φ Ψ : CPTPMap (TensorPower a n) b)
    (ω : MState (TensorPower a n × r)) :
    traceNorm
      (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ)
        (CPTPOp.id (dIn := r × Equiv.Perm (Fin n))).map
        (ω.inputPermutationLabelExtension (a := a) (r := r)).m) =
      ∑ π : Equiv.Perm (Fin n),
        traceNorm
          (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℂ) •
            MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (CPTPOp.id (dIn := r)).map
              ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m)) := by
  classical
  let Δ : MatrixMap (TensorPower a n) b := MatrixMap.channelDifference Φ Ψ
  let M : CMatrix (b × (r × Equiv.Perm (Fin n))) :=
    MatrixMap.kron Δ (CPTPOp.id (dIn := r × Equiv.Perm (Fin n))).map
      (ω.inputPermutationLabelExtension (a := a) (r := r)).m
  let blocks : Equiv.Perm (Fin n) → CMatrix (b × r) := fun π =>
    (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℂ) •
      MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map
        ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m))
  have hEq :
      M.submatrix (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm =
        Classical.blockDiagonal blocks := by
    simpa [M, blocks, Δ] using
      inputPermutationLabelExtension_action_reindexed_eq_blockDiagonal
        (a := a) (r := r) (b := b) Δ ω
  have hblocks : ∀ π, (blocks π).IsHermitian := by
    intro π
    simpa [blocks, Δ] using cMatrix_isHermitian_real_smul
      (c := (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹)
      (M := MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (CPTPOp.id (dIn := r)).map
        ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m))
      (MatrixMap.channelDifference_kron_id_apply_isHermitian
      (a := TensorPower a n) (b := b) (r := r) Φ Ψ
      (((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω))
  have htr : ∀ π, (blocks π).trace = 0 := by
    intro π
    have hzero := MatrixMap.channelDifference_kron_id_apply_trace_eq_zero
      (a := TensorPower a n) (b := b) (r := r) Φ Ψ
      (((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω)
    dsimp [blocks, Δ]
    rw [Matrix.trace_smul, hzero, smul_zero]
  calc
    traceNorm M =
        traceNorm
          (M.submatrix (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm
            (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm) := by
          rw [traceNorm_submatrix_equiv]
    _ = traceNorm (Classical.blockDiagonal blocks) := by rw [hEq]
    _ = ∑ π : Equiv.Perm (Fin n), traceNorm (blocks π) :=
          traceNorm_classical_blockDiagonal_eq_sum blocks hblocks htr
    _ = ∑ π : Equiv.Perm (Fin n),
        traceNorm
          (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℂ) •
            MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (CPTPOp.id (dIn := r)).map
              ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m)) := by
          rfl

/-- Profile-coordinate compression of a state by the normalized symmetric
profile isometry. -/
def ckrProfileCoordinateMatrix
    (ρ : MState (TensorPower (a × a) n)) :
    CMatrix (ckrPurifyingRegister a n) :=
  (ckrProfileIsometryMatrix a n).conjTranspose * ρ.m *
    ckrProfileIsometryMatrix a n

/-- CKR extraction effect.  The transpose matches the convention of
`MatrixMap.traceEffectToUnit`, whose scalar action on a matrix unit is
`X ↦ Tr(XE)`. -/
def ckrProfileCoordinateEffect
    (ρ : MState (TensorPower (a × a) n)) :
    CMatrix (ckrPurifyingRegister a n) :=
  (ρ.ckrProfileCoordinateMatrix (a := a)).transpose

theorem ckrProfileCoordinateMatrix_posSemidef
    (ρ : MState (TensorPower (a × a) n)) :
    (ρ.ckrProfileCoordinateMatrix (a := a)).PosSemidef := by
  exact ρ.psd.conjTranspose_mul_mul_same (ckrProfileIsometryMatrix a n)

theorem ckrProfileCoordinateEffect_posSemidef
    (ρ : MState (TensorPower (a × a) n)) :
    (ρ.ckrProfileCoordinateEffect (a := a)).PosSemidef := by
  exact (ρ.ckrProfileCoordinateMatrix_posSemidef (a := a)).transpose

theorem ckrProfileCoordinateMatrix_le_one [Nonempty a]
    (ρ : MState (TensorPower (a × a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a × a)) :
    ρ.ckrProfileCoordinateMatrix (a := a) ≤ 1 := by
  dsimp [SupportedOnSymmetricSubspace] at hρ
  rw [Matrix.le_iff] at hρ ⊢
  let U := ckrProfileIsometryMatrix a n
  have hconj : (U.conjTranspose *
      (symmetricProjectionMatrix (a := a × a) n - ρ.m) * U).PosSemidef :=
    hρ.conjTranspose_mul_mul_same U
  have heq :
      (1 : CMatrix (ckrPurifyingRegister a n)) - ρ.ckrProfileCoordinateMatrix (a := a) =
        U.conjTranspose *
          (symmetricProjectionMatrix (a := a × a) n - ρ.m) * U := by
    calc
      1 - ρ.ckrProfileCoordinateMatrix (a := a) =
          (U.conjTranspose * symmetricProjectionMatrix (a := a × a) n * U) -
            (U.conjTranspose * ρ.m * U) := by
            dsimp [ckrProfileCoordinateMatrix, U]
            rw [← ckrProfileIsometryMatrix_mul_conjTranspose (a := a) n]
            rw [← Matrix.mul_assoc, ckrProfileIsometryMatrix_conjTranspose_mul (a := a) n,
              Matrix.one_mul, Matrix.mul_assoc,
              ckrProfileIsometryMatrix_conjTranspose_mul (a := a) n]
      _ = U.conjTranspose *
          (symmetricProjectionMatrix (a := a × a) n - ρ.m) * U := by
            rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [heq]
  exact hconj

theorem ckrProfileCoordinateEffect_le_one [Nonempty a]
    (ρ : MState (TensorPower (a × a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a × a)) :
    ρ.ckrProfileCoordinateEffect (a := a) ≤ 1 := by
  have hC := ρ.ckrProfileCoordinateMatrix_le_one (a := a) hρ
  rw [Matrix.le_iff] at hC
  rw [Matrix.le_iff]
  dsimp [ckrProfileCoordinateEffect]
  have heq :
      (1 : CMatrix (ckrPurifyingRegister a n)) -
          (ρ.ckrProfileCoordinateMatrix (a := a)).transpose =
        ((1 : CMatrix (ckrPurifyingRegister a n)) -
          ρ.ckrProfileCoordinateMatrix (a := a)).transpose := by
    rw [Matrix.transpose_sub, Matrix.transpose_one]
  rw [heq]
  exact hC.transpose

theorem ckrProfileCoordinateEffect_traceNonincreasingCP [Nonempty a]
    (ρ : MState (TensorPower (a × a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a × a)) :
    MatrixMap.TraceNonincreasingCP
      (MatrixMap.traceEffectToUnit (ρ.ckrProfileCoordinateEffect (a := a))) :=
  MatrixMap.traceEffectToUnit_traceNonincreasingCP
    (ρ.ckrProfileCoordinateEffect_posSemidef (a := a))
    (ρ.ckrProfileCoordinateEffect_le_one (a := a) hρ)

omit [Fintype a] [DecidableEq a] in
private theorem cMatrix_eq_zero_of_posSemidef_and_neg_posSemidef
    {A : CMatrix (TensorPower (a × a) n)}
    (hA : A.PosSemidef) (hneg : (-A).PosSemidef) :
    A = 0 := by
  have h0A : (0 : CMatrix (TensorPower (a × a) n)) ≤ A := by
    rw [Matrix.le_iff]
    simpa using hA
  have hA0 : A ≤ (0 : CMatrix (TensorPower (a × a) n)) := by
    rw [Matrix.le_iff]
    simpa using hneg
  exact le_antisymm hA0 h0A

private theorem symmetricProjection_supported_fixed [Nonempty a]
    (ρ : MState (TensorPower (a × a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a × a)) :
    symmetricProjectionMatrix (a := a × a) n * ρ.m *
        symmetricProjectionMatrix (a := a × a) n = ρ.m := by
  classical
  let P : CMatrix (TensorPower (a × a) n) :=
    symmetricProjectionMatrix (a := a × a) n
  let Q : CMatrix (TensorPower (a × a) n) := 1 - P
  have hPidem : P * P = P := by
    simpa [P] using symmetricProjectionMatrix_idempotent (a := a × a) n
  have hPherm : P.IsHermitian := by
    simpa [P] using symmetricProjectionMatrix_isHermitian (a := a × a) n
  have hQherm : Q.IsHermitian := by
    dsimp [Q]
    exact symmetricProjectionMatrix_complement_isHermitian (a := a × a) n
  have hQP : Q * P = 0 := by
    calc
      Q * P = (1 - P) * P := rfl
      _ = P - P * P := by rw [Matrix.sub_mul, Matrix.one_mul]
      _ = 0 := by rw [hPidem, sub_self]
  have hPQ : P * Q = 0 := by
    calc
      P * Q = P * (1 - P) := rfl
      _ = P - P * P := by rw [Matrix.mul_sub, Matrix.mul_one]
      _ = 0 := by rw [hPidem, sub_self]
  have hdiff : (P - ρ.m).PosSemidef := by
    dsimp [SupportedOnSymmetricSubspace, P] at hρ
    rwa [Matrix.le_iff] at hρ
  have hQrhoQ_pos : (Q * ρ.m * Q).PosSemidef := by
    have h := ρ.psd.conjTranspose_mul_mul_same Q
    simpa [hQherm.eq] using h
  have hQdiffQ_pos : (Q * (P - ρ.m) * Q).PosSemidef := by
    have h := hdiff.conjTranspose_mul_mul_same Q
    simpa [hQherm.eq] using h
  have hQdiffQ_eq_neg :
      Q * (P - ρ.m) * Q = -(Q * ρ.m * Q) := by
    have hleft : Q * (P - ρ.m) = Q * P - Q * ρ.m := by
      rw [Matrix.mul_sub]
    calc
      Q * (P - ρ.m) * Q =
          (Q * P - Q * ρ.m) * Q := by rw [hleft]
      _ = Q * P * Q - Q * ρ.m * Q := by rw [Matrix.sub_mul]
      _ = 0 - Q * ρ.m * Q := by rw [hQP, Matrix.zero_mul]
      _ = -(Q * ρ.m * Q) := by rw [zero_sub]
  have hQrhoQ_zero : Q * ρ.m * Q = 0 :=
    cMatrix_eq_zero_of_posSemidef_and_neg_posSemidef
      hQrhoQ_pos (by simpa [hQdiffQ_eq_neg] using hQdiffQ_pos)
  let S : CMatrix (TensorPower (a × a) n) := psdSqrt ρ.m
  have hSsq : S * S = ρ.m := by
    simpa [S] using psdSqrt_mul_self_of_posSemidef ρ.psd
  have hSherm : S.IsHermitian := by
    simpa [S] using psdSqrt_isHermitian ρ.m
  have hSQ_conj_self :
      (S * Q).conjTranspose * (S * Q) = 0 := by
    calc
      (S * Q).conjTranspose * (S * Q) =
          Q * S * (S * Q) := by
          rw [Matrix.conjTranspose_mul, hQherm.eq, hSherm.eq]
      _ = Q * ρ.m * Q := by
          calc
            Q * S * (S * Q) = (Q * S * S) * Q := by
              rw [← Matrix.mul_assoc]
            _ = Q * (S * S) * Q := by
              rw [Matrix.mul_assoc Q S S]
            _ = Q * ρ.m * Q := by rw [hSsq]
      _ = 0 := hQrhoQ_zero
  have hSQ : S * Q = 0 := by
    have htrace : ((S * Q).conjTranspose * (S * Q)).trace = 0 := by
      rw [hSQ_conj_self, Matrix.trace_zero]
    exact (Matrix.trace_conjTranspose_mul_self_eq_zero_iff).mp htrace
  have hρQ : ρ.m * Q = 0 := by
    rw [← hSsq, Matrix.mul_assoc, hSQ, Matrix.mul_zero]
  have hQρ : Q * ρ.m = 0 := by
    rw [← Matrix.conjTranspose_eq_zero]
    calc
      (Q * ρ.m).conjTranspose =
          ρ.m.conjTranspose * Q.conjTranspose := by rw [Matrix.conjTranspose_mul]
      _ = ρ.m * Q := by rw [ρ.psd.isHermitian.eq, hQherm.eq]
      _ = 0 := hρQ
  have hPρ : P * ρ.m = ρ.m := by
    calc
      P * ρ.m = (1 - Q) * ρ.m := by simp [Q, sub_sub_cancel]
      _ = ρ.m - Q * ρ.m := by rw [Matrix.sub_mul, Matrix.one_mul]
      _ = ρ.m := by rw [hQρ, sub_zero]
  have hρP : ρ.m * P = ρ.m := by
    calc
      ρ.m * P = ρ.m * (1 - Q) := by simp [Q, sub_sub_cancel]
      _ = ρ.m - ρ.m * Q := by rw [Matrix.mul_sub, Matrix.mul_one]
      _ = ρ.m := by rw [hρQ, sub_zero]
  calc
    symmetricProjectionMatrix (a := a × a) n * ρ.m *
        symmetricProjectionMatrix (a := a × a) n =
        P * ρ.m * P := rfl
    _ = ρ.m * P := by rw [hPρ]
    _ = ρ.m := hρP

private theorem ckrProfileCoordinate_reconstruct_of_projection_fixed [Nonempty a]
    (ρ : MState (TensorPower (a × a) n))
    (hfixed :
      symmetricProjectionMatrix (a := a × a) n * ρ.m *
          symmetricProjectionMatrix (a := a × a) n = ρ.m) :
    ckrProfileIsometryMatrix a n *
        ρ.ckrProfileCoordinateMatrix (a := a) *
        (ckrProfileIsometryMatrix a n).conjTranspose =
      ρ.m := by
  calc
    ckrProfileIsometryMatrix a n *
        ρ.ckrProfileCoordinateMatrix (a := a) *
        (ckrProfileIsometryMatrix a n).conjTranspose =
        ckrProfileIsometryMatrix a n *
          ((ckrProfileIsometryMatrix a n).conjTranspose * ρ.m *
            ckrProfileIsometryMatrix a n) *
          (ckrProfileIsometryMatrix a n).conjTranspose := by
          rfl
    _ =
        (ckrProfileIsometryMatrix a n *
            (ckrProfileIsometryMatrix a n).conjTranspose) *
          ρ.m *
          (ckrProfileIsometryMatrix a n *
            (ckrProfileIsometryMatrix a n).conjTranspose) := by
          simp [Matrix.mul_assoc]
    _ =
        symmetricProjectionMatrix (a := a × a) n * ρ.m *
          symmetricProjectionMatrix (a := a × a) n := by
          rw [ckrProfileIsometryMatrix_mul_conjTranspose]
    _ = ρ.m := hfixed

private theorem dropRightUnitMatrix_ckrExtraction_eq_profile_reconstruction [Nonempty a]
    (ρ : MState (TensorPower (a × a) n)) :
    dropRightUnitMatrix
        ((MatrixMap.kron
            (CPTPOp.id (dIn := TensorPower (a × a) n)).map
            (MatrixMap.traceEffectToUnit (ρ.ckrProfileCoordinateEffect (a := a)))
          (ckrPurifiedReferenceState (a := a) n).m)) =
      (((Fintype.card (ckrPurifyingRegister a n) : ℝ)⁻¹ : ℂ) •
        (ckrProfileIsometryMatrix a n *
          ρ.ckrProfileCoordinateMatrix (a := a) *
          (ckrProfileIsometryMatrix a n).conjTranspose)) := by
  classical
  let U := ckrProfileIsometryMatrix a n
  let C := ρ.ckrProfileCoordinateMatrix (a := a)
  let E := ρ.ckrProfileCoordinateEffect (a := a)
  let g : ℂ := (Fintype.card (ckrPurifyingRegister a n) : ℂ)
  let c : ℂ := (Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ)⁻¹
  have hcstar : star c = c := by
    simp [c]
  have hc2 : c * c = g⁻¹ := by
    simpa [c, g] using inv_sqrt_profile_count_mul_inv_sqrt_profile_count (a := a) n
  have hEpos : E.PosSemidef := by
    simpa [E] using ρ.ckrProfileCoordinateEffect_posSemidef (a := a)
  ext x y
  calc
    dropRightUnitMatrix
        ((MatrixMap.kron
            (CPTPOp.id (dIn := TensorPower (a × a) n)).map
            (MatrixMap.traceEffectToUnit E)
          (ckrPurifiedReferenceState (a := a) n).m)) x y =
        ∑ p : ckrPurifyingRegister a n,
          ∑ q : ckrPurifyingRegister a n,
            (c * U x p * star (c * U y q)) * E q p := by
          rw [dropRightUnitMatrix_kron_id_traceEffectToUnit_apply hEpos]
          refine Finset.sum_congr rfl fun p _ => ?_
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [ckrPurifiedReferenceState_matrix, rankOneMatrix_apply]
          rfl
    _ =
        g⁻¹ * (∑ p : ckrPurifyingRegister a n,
          ∑ q : ckrPurifyingRegister a n,
            U x p * C p q * star (U y q)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          calc
            c * U x p * star (c * U y q) * C p q =
                c * U x p * (star (U y q) * star c) * C p q := by
                rw [star_mul]
            _ = (c * c) * (U x p * C p q * star (U y q)) := by
                rw [hcstar]
                ring
            _ = g⁻¹ * (U x p * C p q * star (U y q)) := by
                rw [hc2]
    _ =
        (((Fintype.card (ckrPurifyingRegister a n) : ℝ)⁻¹ : ℂ) •
          (U * C * U.conjTranspose)) x y := by
          have hgcast :
              (((Fintype.card (ckrPurifyingRegister a n) : ℝ)⁻¹ : ℂ) = g⁻¹) := by
            simp [g]
          rw [Matrix.smul_apply, hgcast]
          congr 1
          rw [Finset.sum_comm]
          simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
            Finset.sum_mul, mul_assoc]

/-- CKR `extractpart` with the exact profile-count factor.

Every state supported on the symmetric subspace of `(H ⊗ H)^n` is recovered
from the CKR purified reference state by applying a trace-nonincreasing CP
effect map on the profile purifying register.  The scalar factor is the exact
number of tensor-power profiles, i.e. the rank of the symmetric projection in
the profile basis. -/
theorem ckr_extractpart_profile_count [Nonempty a]
    {n : ℕ} (ρ : MState (TensorPower (a × a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a × a)) :
    ∃ T : MatrixMap (ckrPurifyingRegister a n) PUnit,
      T.TraceNonincreasingCP ∧
        ρ.m =
          ((Fintype.card (TensorPowerProfile (a × a) n) : ℝ) : ℂ) •
            dropRightUnitMatrix
              ((MatrixMap.kron
                  (CPTPOp.id (dIn := TensorPower (a × a) n)).map T)
                (ckrPurifiedReferenceState (a := a) n).m) := by
  classical
  let T : MatrixMap (ckrPurifyingRegister a n) PUnit :=
    MatrixMap.traceEffectToUnit (ρ.ckrProfileCoordinateEffect (a := a))
  refine ⟨T, ?_, ?_⟩
  · simpa [T] using ρ.ckrProfileCoordinateEffect_traceNonincreasingCP
      (a := a) hρ
  · have hdrop :=
      dropRightUnitMatrix_ckrExtraction_eq_profile_reconstruction (a := a) ρ
    have hfixed := symmetricProjection_supported_fixed (a := a) ρ hρ
    have hrec :=
      ckrProfileCoordinate_reconstruct_of_projection_fixed (a := a) ρ hfixed
    have hdropρ :
        dropRightUnitMatrix
            ((MatrixMap.kron
                (CPTPOp.id (dIn := TensorPower (a × a) n)).map T)
              (ckrPurifiedReferenceState (a := a) n).m) =
          (((Fintype.card (TensorPowerProfile (a × a) n) : ℝ)⁻¹ : ℂ) •
            ρ.m) := by
      simpa [T, ckrPurifyingRegister, hrec] using hdrop
    rw [hdropρ]
    symm
    have hcard_ne :
        (Fintype.card (TensorPowerProfile (a × a) n) : ℂ) ≠ 0 := by
      exact_mod_cast TensorPowerProfile.card_ne_zero (a := a × a) n
    calc
      (Fintype.card (TensorPowerProfile (a × a) n) : ℂ) •
          ((Fintype.card (TensorPowerProfile (a × a) n) : ℂ)⁻¹ •
            ρ.m) =
          ((Fintype.card (TensorPowerProfile (a × a) n) : ℂ) *
              (Fintype.card (TensorPowerProfile (a × a) n) : ℂ)⁻¹) •
            ρ.m := by
            rw [smul_smul]
      _ = ρ.m := by rw [mul_inv_cancel₀ hcard_ne, one_smul]

/-- CKR `extractpart` with the binomial symmetric-dimension factor. -/
theorem ckr_extractpart_choose [Nonempty a]
    {n : ℕ} (ρ : MState (TensorPower (a × a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a × a)) :
    ∃ T : MatrixMap (ckrPurifyingRegister a n) PUnit,
      T.TraceNonincreasingCP ∧
        ρ.m =
          ((Nat.choose (n + Fintype.card (a × a) - 1) n : ℝ) : ℂ) •
            dropRightUnitMatrix
              ((MatrixMap.kron
                  (CPTPOp.id (dIn := TensorPower (a × a) n)).map T)
                (ckrPurifiedReferenceState (a := a) n).m) := by
  classical
  obtain ⟨T, hT, hEq⟩ :=
    ρ.ckr_extractpart_profile_count (a := a) hρ
  refine ⟨T, hT, ?_⟩
  simpa [tensorPowerProfile_card_eq_choose (a := a × a) n] using hEq

/-- Concrete `traceEffectToUnit` form of CKR `extractpart`.

This is the witness used in `ckr_extractpart_profile_count`, exposed so the
post-selection assembly can commute a channel-difference action past the
explicit extraction map. -/
theorem ckr_extractpart_profile_count_traceEffect [Nonempty a]
    {n : ℕ} (ρ : MState (TensorPower (a × a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a × a)) :
    ρ.m =
      ((Fintype.card (TensorPowerProfile (a × a) n) : ℝ) : ℂ) •
        dropRightUnitMatrix
          ((MatrixMap.kron
              (CPTPOp.id (dIn := TensorPower (a × a) n)).map
              (MatrixMap.traceEffectToUnit (ρ.ckrProfileCoordinateEffect (a := a))))
            (ckrPurifiedReferenceState (a := a) n).m) := by
  classical
  let T : MatrixMap (ckrPurifyingRegister a n) PUnit :=
    MatrixMap.traceEffectToUnit (ρ.ckrProfileCoordinateEffect (a := a))
  have hdrop :=
    dropRightUnitMatrix_ckrExtraction_eq_profile_reconstruction (a := a) ρ
  have hfixed := symmetricProjection_supported_fixed (a := a) ρ hρ
  have hrec :=
    ckrProfileCoordinate_reconstruct_of_projection_fixed (a := a) ρ hfixed
  have hdropρ :
      dropRightUnitMatrix
          ((MatrixMap.kron
              (CPTPOp.id (dIn := TensorPower (a × a) n)).map T)
            (ckrPurifiedReferenceState (a := a) n).m) =
        (((Fintype.card (TensorPowerProfile (a × a) n) : ℝ)⁻¹ : ℂ) •
          ρ.m) := by
    simpa [T, ckrPurifyingRegister, hrec] using hdrop
  rw [hdropρ]
  symm
  have hcard_ne :
      (Fintype.card (TensorPowerProfile (a × a) n) : ℂ) ≠ 0 := by
    exact_mod_cast TensorPowerProfile.card_ne_zero (a := a × a) n
  calc
    (Fintype.card (TensorPowerProfile (a × a) n) : ℂ) •
        ((Fintype.card (TensorPowerProfile (a × a) n) : ℂ)⁻¹ •
          ρ.m) =
        ((Fintype.card (TensorPowerProfile (a × a) n) : ℂ) *
            (Fintype.card (TensorPowerProfile (a × a) n) : ℂ)⁻¹) •
          ρ.m := by
          rw [smul_smul]
    _ = ρ.m := by rw [mul_inv_cancel₀ hcard_ne, one_smul]

end MState

namespace QIT

namespace MatrixMap

theorem ancillaNormalizedTraceAction_le_spectralPure_sum
    {a : Type v} {b : Type w} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (Δ : MatrixMap a b) (ω : MState (a × a)) :
    Δ.ancillaNormalizedTraceAction ω ≤
      ∑ i : a × a,
        ω.psd.isHermitian.eigenvalues i *
          Δ.ancillaNormalizedTraceAction (ω.spectralKet i).state := by
  dsimp [ancillaNormalizedTraceAction, normalizedTraceAction]
  have hmatrix := ω.matrix_eq_sum_spectralKet
  have hmap : MatrixMap.kron Δ (CPTPOp.id (dIn := a)).map ω.m =
      ∑ i : a × a,
        ((ω.psd.isHermitian.eigenvalues i : ℝ) : ℂ) •
          MatrixMap.kron Δ (CPTPOp.id (dIn := a)).map
            (ω.spectralKet i).state.m := by
    conv_lhs => rw [hmatrix]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
  rw [hmap]
  have hsum := traceNorm_sum_le_sum_traceNorm
    (Finset.univ : Finset (a × a))
    (fun i => ((ω.psd.isHermitian.eigenvalues i : ℝ) : ℂ) •
      MatrixMap.kron Δ (CPTPOp.id (dIn := a)).map (ω.spectralKet i).state.m)
  have hterms :
      (∑ i : a × a,
        traceNorm (((ω.psd.isHermitian.eigenvalues i : ℝ) : ℂ) •
          MatrixMap.kron Δ (CPTPOp.id (dIn := a)).map
            (ω.spectralKet i).state.m)) ≤
        ∑ i : a × a,
          ω.psd.isHermitian.eigenvalues i *
            traceNorm (MatrixMap.kron Δ (CPTPOp.id (dIn := a)).map
              (ω.spectralKet i).state.m) := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact traceNorm_real_smul_le (ω.psd.eigenvalues_nonneg i) _
  calc
    (1 / 2 : ℝ) * traceNorm
        (∑ i : a × a,
          ((ω.psd.isHermitian.eigenvalues i : ℝ) : ℂ) •
            MatrixMap.kron Δ (CPTPOp.id (dIn := a)).map
              (ω.spectralKet i).state.m)
        ≤ (1 / 2 : ℝ) *
          (∑ i : a × a,
            traceNorm (((ω.psd.isHermitian.eigenvalues i : ℝ) : ℂ) •
              MatrixMap.kron Δ (CPTPOp.id (dIn := a)).map
                (ω.spectralKet i).state.m)) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
          (∑ i : a × a,
            ω.psd.isHermitian.eigenvalues i *
              traceNorm (MatrixMap.kron Δ (CPTPOp.id (dIn := a)).map
                (ω.spectralKet i).state.m)) :=
          mul_le_mul_of_nonneg_left hterms (by norm_num)
    _ = ∑ i : a × a,
          ω.psd.isHermitian.eigenvalues i *
            ((1 / 2 : ℝ) * traceNorm (MatrixMap.kron Δ (CPTPOp.id (dIn := a)).map
              (ω.spectralKet i).state.m)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring

/-- Convexity bridge for the source-shaped diamond distance: it suffices to
bound the finite-reference action on pure input-reference states. -/
theorem ancillaNormalizedTraceAction_le_of_forall_pure_bound
    {a : Type v} {b : Type w} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (Δ : MatrixMap a b) (ω : MState (a × a)) {B : ℝ}
    (h : ∀ Ω : Ket (a × a), Δ.ancillaNormalizedTraceAction Ω.state ≤ B) :
    Δ.ancillaNormalizedTraceAction ω ≤ B := by
  calc
    Δ.ancillaNormalizedTraceAction ω ≤
        ∑ i : a × a,
          ω.psd.isHermitian.eigenvalues i *
            Δ.ancillaNormalizedTraceAction (ω.spectralKet i).state :=
          Δ.ancillaNormalizedTraceAction_le_spectralPure_sum ω
    _ ≤ ∑ i : a × a, ω.psd.isHermitian.eigenvalues i * B := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_left (h (ω.spectralKet i))
            (ω.psd.eigenvalues_nonneg i)
    _ = B := by
          rw [← Finset.sum_mul]
          rw [ω.sum_eigenvalues_eq_one]
          simp

variable {n : ℕ}
variable {b : Type w} [Fintype b] [DecidableEq b]

/-- CKR post-selection covariance for a matrix-map difference.

For every tensor-factor permutation `π`, the source assumes a CPTP map `Kπ`
such that `Δ ∘ π = Kπ ∘ Δ`.  The predicate is stated at matrix level using the
project's finite permutation channel. -/
def PostSelectionCovariant (Δ : MatrixMap (QIT.TensorPower a n) b) : Prop :=
  ∀ π : Equiv.Perm (Fin n), ∃ Kπ : CPTPMap b b,
    ∀ X : CMatrix (QIT.TensorPower a n),
      Δ ((permutationChannel (a := a) n π).map X) = Kπ.map (Δ X)

/-- Tensoring a post-selection covariant map with an identity reference keeps
the covariance equation at the finite-ancilla level. -/
theorem postSelectionCovariant_kron_permutation_eq
    {r : Type x} [Fintype r] [DecidableEq r]
    (Δ : MatrixMap (QIT.TensorPower a n) b)
    (hcov : Δ.PostSelectionCovariant (a := a) (n := n))
    (π : Equiv.Perm (Fin n)) (X : CMatrix (QIT.TensorPower a n × r)) :
    ∃ Kπ : CPTPMap b b,
      MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map
          (((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))).map X) =
        (Kπ.prod (CPTPOp.id (dIn := r))).map
          (MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map X) := by
  obtain ⟨Kπ, hKπ⟩ := hcov π
  refine ⟨Kπ, ?_⟩
  simp only [CPTPOp.prod_map]
  ext br br'
  rw [MatrixMap.kron_idChannel_apply_slice]
  rw [MatrixMap.kron_idChannel_apply_slice]
  have hslice_perm :
      (Matrix.of fun i i' =>
          MatrixMap.kron (permutationChannel (a := a) n π).map
            (CPTPOp.id (dIn := r)).map X (i, br.2) (i', br'.2)) =
        (permutationChannel (a := a) n π).map
          (Matrix.of fun i i' => X (i, br.2) (i', br'.2)) := by
    ext i i'
    exact MatrixMap.kron_idChannel_apply_slice (permutationChannel (a := a) n π).map X
      (i, br.2) (i', br'.2)
  have hslice_delta :
      (Matrix.of fun i i' =>
          MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map X (i, br.2) (i', br'.2)) =
        Δ (Matrix.of fun i i' => X (i, br.2) (i', br'.2)) := by
    ext i i'
    exact MatrixMap.kron_idChannel_apply_slice Δ X (i, br.2) (i', br'.2)
  rw [hslice_perm, hKπ, hslice_delta]

end MatrixMap

end QIT
end

noncomputable section

namespace CPTPOp

open QIT

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [Fintype a] [DecidableEq a]

variable {n : ℕ}
variable {b : Type w} [Fintype b] [DecidableEq b]

/-- CKR post-selection covariance for the difference of two channels. -/
def PostSelectionCovariantDifference (Φ Ψ : CPTPMap (QIT.TensorPower a n) b) : Prop :=
  MatrixMap.PostSelectionCovariant (a := a) (n := n) (b := b)
    (MatrixMap.channelDifference (a := QIT.TensorPower a n) (b := b) Φ Ψ)

/-- Under CKR post-selection covariance, applying a tensor-factor permutation
to the input-reference state cannot increase the channel-difference normalized
trace action. -/
theorem postSelectionCovariantDifference_ancillaAction_permutation_le
    {r : Type x} [Fintype r] [DecidableEq r]
    (Φ Ψ : CPTPMap (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ)
    (π : Equiv.Perm (Fin n)) (ω : MState (QIT.TensorPower a n × r)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω) ≤
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω := by
  obtain ⟨Kπ, hEq⟩ :=
    MatrixMap.postSelectionCovariant_kron_permutation_eq (a := a) (b := b) (r := r)
      (MatrixMap.channelDifference Φ Ψ) hcov π ω.m
  dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction]
  rw [CPTPOp.mat_coe_eq_apply_mat, hEq]
  have hH := MatrixMap.channelDifference_kron_id_apply_isHermitian
    (a := QIT.TensorPower a n) (b := b) (r := r) Φ Ψ ω
  have htr := MatrixMap.channelDifference_kron_id_apply_trace_eq_zero
    (a := QIT.TensorPower a n) (b := b) (r := r) Φ Ψ ω
  have hle := MatrixMap.traceNorm_apply_le_of_traceNonincreasingCP
    (CPTPOp.traceNonincreasingCP_kron_id (r := r) Kπ) hH htr
  exact mul_le_mul_of_nonneg_left (by simpa [CPTPOp.prod] using hle) (by norm_num)

/-- Applying a tensor-factor permutation and then its inverse on the input
register leaves an input-reference state unchanged. -/
private theorem inputPermutation_inv_apply_permutation
    {r : Type x} [Fintype r] [DecidableEq r]
    (π : Equiv.Perm (Fin n)) (ω : MState (QIT.TensorPower a n × r)) :
    ((permutationChannel (a := a) n π⁻¹).prod (CPTPOp.id (dIn := r)))
        (((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω) =
      ω := by
  apply MState.ext
  rw [CPTPOp.mat_coe_eq_apply_mat, CPTPOp.mat_coe_eq_apply_mat]
  ext x y
  rw [permutationChannel_prod_id_map_apply]
  rw [permutationChannel_prod_id_map_apply]
  cases x with
  | mk xA xr =>
  cases y with
  | mk yA yr =>
    change ω.m (π • (π⁻¹ • xA), xr) (π • (π⁻¹ • yA), yr) =
      ω.m (xA, xr) (yA, yr)
    rw [← mul_smul, ← mul_smul]
    simp

/-- Under CKR post-selection covariance, applying a tensor-factor permutation
to the input-reference state preserves the channel-difference normalized trace
action.  One inequality is contraction through the covariance map; the reverse
uses the inverse permutation. -/
theorem postSelectionCovariantDifference_ancillaAction_permutation_eq
    {r : Type x} [Fintype r] [DecidableEq r]
    (Φ Ψ : CPTPMap (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ)
    (π : Equiv.Perm (Fin n)) (ω : MState (QIT.TensorPower a n × r)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω) =
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω := by
  apply le_antisymm
  · exact postSelectionCovariantDifference_ancillaAction_permutation_le
      (a := a) (b := b) (r := r) Φ Ψ hcov π ω
  · have hle := postSelectionCovariantDifference_ancillaAction_permutation_le
      (a := a) (b := b) (r := r) Φ Ψ hcov π⁻¹
      (((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω)
    simpa [inputPermutation_inv_apply_permutation (a := a) (r := r) π ω] using hle

private theorem postSelectionCovariantDifference_labelExtension_action_eq
    {r : Type x} [Fintype r] [DecidableEq r]
    (Φ Ψ : CPTPMap (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ)
    (ω : MState (QIT.TensorPower a n × r)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (ω.inputPermutationLabelExtension (a := a) (r := r)) =
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω := by
  classical
  let Δ : MatrixMap (QIT.TensorPower a n) b := MatrixMap.channelDifference Φ Ψ
  let c : ℝ := (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹
  have hc : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  have hcard_ne : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (Equiv.Perm (Fin n)) ≠ 0)
  dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction]
  rw [MState.inputPermutationLabelExtension_channelDifference_action_traceNorm_eq_sum
    (a := a) (r := r) (b := b) Φ Ψ ω]
  have hterms :
      (∑ π : Equiv.Perm (Fin n),
        traceNorm
          ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ •
            MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map
              ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m))) =
        ∑ π : Equiv.Perm (Fin n),
          c * traceNorm
            (MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map
              ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m)) := by
    refine Finset.sum_congr rfl fun π _ => ?_
    simpa [c] using traceNorm_real_smul_eq
      (a := b × r) (c := c) hc
      (MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map
        ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m))
  change (1 / 2 : ℝ) *
      (∑ π : Equiv.Perm (Fin n),
        traceNorm
          ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ •
            MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map
              ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m))) =
    (1 / 2 : ℝ) * traceNorm
      (MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map ω.m)
  rw [hterms]
  have hpermTrace :
      ∀ π : Equiv.Perm (Fin n),
        traceNorm
          (MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map
            ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m)) =
        traceNorm
          (MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map ω.m) := by
    intro π
    have h := postSelectionCovariantDifference_ancillaAction_permutation_eq
      (a := a) (b := b) (r := r) Φ Ψ hcov π ω
    dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction, Δ] at h
    nlinarith
  calc
    (1 / 2 : ℝ) *
        (∑ π : Equiv.Perm (Fin n),
          c * traceNorm
            (MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map
              ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m)) ) =
        (1 / 2 : ℝ) *
          (∑ π : Equiv.Perm (Fin n),
            c * traceNorm
              (MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map ω.m)) := by
          refine congrArg (fun z : ℝ => (1 / 2 : ℝ) * z) ?_
          refine Finset.sum_congr rfl fun π _ => ?_
          rw [hpermTrace π]
    _ = (1 / 2 : ℝ) * traceNorm
          (MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map ω.m) := by
          simp [c, Finset.sum_const, nsmul_eq_mul, hcard_ne]

/-- A mixed input-reference state is controlled by the canonical pure extension
obtained by purifying the whole input-reference system.  The proof is the
finite-dimensional data-processing step: the mixed action is the partial trace
of the pure-extension action, and partial trace contracts trace norm. -/
private theorem inputReferenceAction_le_canonicalExtension
    {r : Type x} [Fintype r] [DecidableEq r]
    (Φ Ψ : CPTPMap (QIT.TensorPower a n) b)
    (ω : MState (QIT.TensorPower a n × r)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω ≤
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (ω.inputReferenceCanonicalExtension (a := a) (r := r)).state := by
  classical
  let Δ : MatrixMap (QIT.TensorPower a n) b := MatrixMap.channelDifference Φ Ψ
  let E := (QIT.TensorPower a n × r)
  let Y : CMatrix (E × (b × r)) :=
    MatrixMap.kron (CPTPOp.id (dIn := E)).map
      (MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map)
      ω.canonicalPurification.state.m
  let Z : CMatrix (b × (r × E)) :=
    MatrixMap.kron Δ (CPTPOp.id (dIn := r × E)).map
      (ω.inputReferenceCanonicalExtension (a := a) (r := r)).state.m
  have hpt :
      Matrix.traceLeft Y =
        MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map ω.m := by
    calc
      Matrix.traceLeft Y =
          MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map
            (Matrix.traceLeft
              ω.canonicalPurification.state.m) := by
            simp only [Y]
            rw [MatrixMap.traceLeft_kron_idChannel_left]
      _ = MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map ω.m := by
            have hp : Matrix.traceLeft
                ω.canonicalPurification.state.m = ω.m := by
              exact Ket.traceLeft_state_matrix_eq_of_purifies
                ω.canonicalPurification_purifies
            rw [hp]
  have hreindex :
      Z =
        Y.submatrix
          (MState.extensionPurificationOutputEquiv (a := a) (r := r) (b := b) (n := n)).symm
          (MState.extensionPurificationOutputEquiv (a := a) (r := r) (b := b) (n := n)).symm := by
    ext x y
    simp [-CPTPOp.id_map, Z, Y, MState.inputReferenceCanonicalExtension,
      MState.extensionPurificationInputEquiv, MState.extensionPurificationOutputEquiv,
      Ket.reindex_state,
      MatrixMap.kron_idChannel_apply_slice, MatrixMap.kron_idChannel_left_apply_slice]
  have htraceY : traceNorm Y = traceNorm Z := by
    rw [hreindex]
    symm
    exact traceNorm_submatrix_equiv
      (MState.extensionPurificationOutputEquiv (a := a) (r := r) (b := b) (n := n)).symm
      Y
  dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction]
  change (1 / 2 : ℝ) * traceNorm
      (MatrixMap.kron Δ (CPTPOp.id (dIn := r)).map ω.m) ≤
    (1 / 2 : ℝ) * traceNorm Z
  rw [← hpt]
  calc
    (1 / 2 : ℝ) * traceNorm (Matrix.traceLeft Y)
        ≤ (1 / 2 : ℝ) * traceNorm Y :=
          mul_le_mul_of_nonneg_left
            (traceNorm_traceLeft_le_matrix (a := E) (b := b × r) Y)
            (by norm_num)
    _ = (1 / 2 : ℝ) * traceNorm Z := by rw [htraceY]

/-- The input marginal of the canonical pure extension of an input-reference
state is the original input marginal. -/
private theorem inputReferenceCanonicalExtension_traceRight
    {r : Type x} [Fintype r] [DecidableEq r]
    (ω : MState (QIT.TensorPower a n × r)) :
    (ω.inputReferenceCanonicalExtension (a := a) (r := r)).state.traceRight =
      ω.traceRight := by
  apply MState.ext
  rw [MState.traceRight_m, MState.traceRight_m]
  have hp : Matrix.traceLeft
      ω.canonicalPurification.state.m = ω.m := by
    exact Ket.traceLeft_state_matrix_eq_of_purifies
      ω.canonicalPurification_purifies
  simp only [MState.inputReferenceCanonicalExtension, Ket.reindex_state,
    MState.reindex_matrix]
  ext i j
  simp only [Matrix.traceRight, Matrix.of_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun xr _ => ?_
  have hpij := congrFun (congrFun hp (i, xr)) (j, xr)
  simpa [Matrix.traceLeft, MState.extensionPurificationInputEquiv] using hpij

/-- Averaging an input-reference state over input tensor-factor permutations
does not increase the post-selection covariant channel-difference action. -/
theorem postSelectionCovariantDifference_ancillaAction_inputPermutationTwirling_le
    {r : Type x} [Fintype r] [DecidableEq r]
    (Φ Ψ : CPTPMap (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ)
    (ω : MState (QIT.TensorPower a n × r)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (ω.inputPermutationTwirling (a := a) (r := r)) ≤
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω := by
  classical
  let c : ℝ := (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr (Nat.cast_nonneg _)
  dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction]
  rw [MState.inputPermutationTwirling_matrix, map_smul, map_sum]
  have hsmul : traceNorm (((c : ℂ) • ∑ π : Equiv.Perm (Fin n),
      MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (CPTPOp.id (dIn := r)).map
        ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m))) ≤
      c * traceNorm (∑ π : Equiv.Perm (Fin n),
      MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (CPTPOp.id (dIn := r)).map
        ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m)) :=
    traceNorm_real_smul_le hc _
  have hsum := traceNorm_sum_le_sum_traceNorm (Finset.univ : Finset (Equiv.Perm (Fin n)))
    (fun π => MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (CPTPOp.id (dIn := r)).map
      ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m))
  have hterms : (∑ π : Equiv.Perm (Fin n), traceNorm
      (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (CPTPOp.id (dIn := r)).map
        ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m)) ≤
      ∑ π : Equiv.Perm (Fin n), traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (CPTPOp.id (dIn := r)).map ω.m)) := by
    refine Finset.sum_le_sum fun π _ => ?_
    have h := postSelectionCovariantDifference_ancillaAction_permutation_le
      (a := a) (b := b) (r := r) Φ Ψ hcov π ω
    dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction] at h
    nlinarith [h]
  have hcard_ne : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin n)) ≠ 0)
  calc
    (1 / 2 : ℝ) * traceNorm
      ((c : ℂ) • ∑ π : Equiv.Perm (Fin n),
        MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (CPTPOp.id (dIn := r)).map
          ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m))
        ≤ (1 / 2 : ℝ) * (c * traceNorm (∑ π : Equiv.Perm (Fin n),
        MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (CPTPOp.id (dIn := r)).map
          ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m))) :=
          mul_le_mul_of_nonneg_left hsmul (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (c * (∑ π : Equiv.Perm (Fin n), traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (CPTPOp.id (dIn := r)).map
          ((((permutationChannel (a := a) n π).prod (CPTPOp.id (dIn := r))) ω).m)))) := by
          gcongr
    _ ≤ (1 / 2 : ℝ) * (c * (∑ π : Equiv.Perm (Fin n), traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (CPTPOp.id (dIn := r)).map ω.m))) := by
          gcongr
    _ = (1 / 2 : ℝ) * traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (CPTPOp.id (dIn := r)).map ω.m) := by
          simp [c, Finset.sum_const, nsmul_eq_mul, hcard_ne]

/-- Supported symmetric input-reference states are controlled by the CKR
purified post-selection reference action, with the exact profile-count factor.

This is the extractpart-to-action bridge: it applies the concrete
trace-effect extraction map from CKR `extractpart`, commutes the
channel-difference action past that extraction, and then uses
trace-nonincreasing CP contraction. -/
private theorem postSelection_supportedInputReferenceAction_le_profile_count_purified
    [Nonempty a] (Φ Ψ : CPTPMap (QIT.TensorPower a n) b)
    (ρ : MState (QIT.TensorPower (a × a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a × a)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (ρ.reindex (tensorPowerProdEquiv a a n)) ≤
      (Fintype.card (TensorPowerProfile (a × a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (ckrPostSelectionPurifiedReferenceState (a := a) n) := by
  classical
  let Δ : MatrixMap (QIT.TensorPower a n) b := MatrixMap.channelDifference Φ Ψ
  let gR : ℝ := Fintype.card (TensorPowerProfile (a × a) n)
  let E : CMatrix (ckrPurifyingRegister a n) :=
    ρ.ckrProfileCoordinateEffect (a := a)
  let T : MatrixMap (ckrPurifyingRegister a n) PUnit.{1} :=
    MatrixMap.traceEffectToUnit E
  let H0 : CMatrix (b × (QIT.TensorPower a n × ckrPurifyingRegister a n)) :=
    (MatrixMap.kron Δ
      (CPTPOp.id (dIn := QIT.TensorPower a n × ckrPurifyingRegister a n)).map)
      (ckrPostSelectionPurifiedReferenceState (a := a) n).m
  let H : CMatrix ((b × QIT.TensorPower a n) × ckrPurifyingRegister a n) :=
    assocRightMatrix H0
  have hEpos : E.PosSemidef := by
    simpa [E] using ρ.ckrProfileCoordinateEffect_posSemidef (a := a)
  have hT : T.TraceNonincreasingCP := by
    simpa [T, E] using
      ρ.ckrProfileCoordinateEffect_traceNonincreasingCP (a := a) hρ
  have hExtract := ρ.ckr_extractpart_profile_count_traceEffect (a := a) hρ
  have hActionEq :
      MatrixMap.kron Δ (CPTPOp.id (dIn := QIT.TensorPower a n)).map
          (ρ.reindex (tensorPowerProdEquiv a a n)).m =
        (gR : ℂ) •
          dropRightUnitMatrix
            ((MatrixMap.kron (CPTPOp.id (dIn := b × QIT.TensorPower a n)).map T) H) := by
    have hReindex :
        (ρ.reindex (tensorPowerProdEquiv a a n)).m =
          (gR : ℂ) •
            (dropRightUnitMatrix
              ((MatrixMap.kron
                  (CPTPOp.id (dIn := QIT.TensorPower (a × a) n)).map T)
                (ckrPurifiedReferenceState (a := a) n).m)).submatrix
              (tensorPowerProdEquiv a a n).symm
              (tensorPowerProdEquiv a a n).symm := by
      rw [MState.reindex_matrix, hExtract]
      ext i j
      simp [Matrix.smul_apply, gR, T, E]
      left
      rfl
    rw [hReindex, map_smul]
    congr 1
    simpa [Δ, T, E, H, H0] using
      (dropRightUnitMatrix_action_traceEffectToUnit_commute
        (a := a) (n := n) (b := b) Δ (E := E) hEpos).symm
  have hH0Herm : H0.IsHermitian := by
    simpa [H0, Δ] using
      MatrixMap.channelDifference_kron_id_apply_isHermitian
        (a := QIT.TensorPower a n) (b := b)
        (r := QIT.TensorPower a n × ckrPurifyingRegister a n)
        Φ Ψ (ckrPostSelectionPurifiedReferenceState (a := a) n)
  have hH0tr : H0.trace = 0 := by
    simpa [H0, Δ] using
      MatrixMap.channelDifference_kron_id_apply_trace_eq_zero
        (a := QIT.TensorPower a n) (b := b)
        (r := QIT.TensorPower a n × ckrPurifyingRegister a n)
        Φ Ψ (ckrPostSelectionPurifiedReferenceState (a := a) n)
  have hHHerm : H.IsHermitian := by
    simpa [H] using assocRightMatrix_isHermitian hH0Herm
  have hHtr : H.trace = 0 := by
    simpa [H, hH0tr] using trace_assocRightMatrix H0
  have hContract :
      traceNorm
          (dropRightUnitMatrix
            ((MatrixMap.kron (CPTPOp.id (dIn := b × QIT.TensorPower a n)).map T) H)) ≤
        traceNorm H :=
    traceNorm_dropRightUnitMatrix_kron_id_le_of_traceNonincreasingCP
      (α := b × QIT.TensorPower a n) (β := ckrPurifyingRegister a n)
      hT hHHerm hHtr
  have hg_nonneg : 0 ≤ gR := by
    dsimp [gR]
    exact Nat.cast_nonneg _
  dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction]
  change (1 / 2 : ℝ) *
      traceNorm
        (MatrixMap.kron Δ (CPTPOp.id (dIn := QIT.TensorPower a n)).map
          (ρ.reindex (tensorPowerProdEquiv a a n)).m) ≤
    gR * ((1 / 2 : ℝ) * traceNorm H0)
  rw [hActionEq]
  calc
    (1 / 2 : ℝ) *
        traceNorm ((gR : ℂ) •
          dropRightUnitMatrix
            ((MatrixMap.kron (CPTPOp.id (dIn := b × QIT.TensorPower a n)).map T) H))
        ≤ (1 / 2 : ℝ) *
            (gR * traceNorm
              (dropRightUnitMatrix
                ((MatrixMap.kron (CPTPOp.id (dIn := b × QIT.TensorPower a n)).map T) H))) :=
          mul_le_mul_of_nonneg_left
            (traceNorm_real_smul_le hg_nonneg _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (gR * traceNorm H) := by
          gcongr
    _ = gR * ((1 / 2 : ℝ) * traceNorm H0) := by
          rw [traceNorm_assocRightMatrix H0]
          ring

/-- Pure input-reference states whose input marginal is permutation-invariant
are controlled by the CKR purified post-selection reference action.  The only
remaining step for the full CKR diamond theorem is the source's reduction from
arbitrary pure inputs to this invariant-marginal situation. -/
theorem postSelection_pureInputReferenceAction_le_profile_count_of_traceRight_invariant
    [Nonempty a] (Φ Ψ : CPTPMap (QIT.TensorPower a n) b)
    (Ω : Ket (QIT.TensorPower a n × QIT.TensorPower a n))
    (hInv : Ω.state.traceRight.IsPermutationInvariant (a := a)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction Ω.state ≤
      (Fintype.card (TensorPowerProfile (a × a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (ckrPostSelectionPurifiedReferenceState (a := a) n) := by
  have hcanon :=
    Ω.channelDifference_normalizedAction_le_canonicalOfMarginalA Φ Ψ
  have hsup :=
    postSelection_supportedInputReferenceAction_le_profile_count_purified
      (a := a) (n := n) (b := b) Φ Ψ
      Ω.state.traceRight.inputCanonicalTensorPowerPurificationState
      (MState.inputCanonicalTensorPowerPurification_supported_of_invariant
        (a := a) hInv)
  calc
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction Ω.state ≤
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (Ω.state.traceRight.canonicalPurification.reindex
            (Equiv.prodComm (QIT.TensorPower a n) (QIT.TensorPower a n))).state :=
          hcanon
    _ ≤ (Fintype.card (TensorPowerProfile (a × a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (ckrPostSelectionPurifiedReferenceState (a := a) n) := by
          rw [Ket.reindex_state,
            ← MState.inputCanonicalTensorPowerPurificationState_reindex_tensorPowerProdEquiv]
          exact hsup

private theorem inputReferenceAction_le_profile_count_of_invariantMarginal
    [Nonempty a] {r : Type x} [Fintype r] [DecidableEq r] [Nonempty r]
    (Φ Ψ : CPTPMap (QIT.TensorPower a n) b)
    (ω : MState (QIT.TensorPower a n × r))
    (hInv : ω.traceRight.IsPermutationInvariant (a := a)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω ≤
      (Fintype.card (TensorPowerProfile (a × a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (ckrPostSelectionPurifiedReferenceState (a := a) n) := by
  classical
  let Ω : Ket
      (QIT.TensorPower a n ×
        (r × (QIT.TensorPower a n × r))) :=
    ω.inputReferenceCanonicalExtension (a := a) (r := r)
  have hExt :=
    inputReferenceAction_le_canonicalExtension (a := a) (n := n) (b := b)
      (r := r) Φ Ψ ω
  have hcard :
      Fintype.card (QIT.TensorPower a n) ≤
        Fintype.card (r × (QIT.TensorPower a n × r)) := by
    have hrpos : 0 < Fintype.card r := Fintype.card_pos_iff.mpr inferInstance
    have hmulpos : 0 < Fintype.card r * Fintype.card r := Nat.mul_pos hrpos hrpos
    have hbase :
        Fintype.card (QIT.TensorPower a n) ≤
          Fintype.card (QIT.TensorPower a n) * (Fintype.card r * Fintype.card r) :=
      Nat.le_mul_of_pos_right _ hmulpos
    simpa [Fintype.card_prod, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      using hbase
  have hCan :=
    Ω.channelDifference_normalizedAction_le_canonicalOfMarginalA_of_card_le
      Φ Ψ hcard
  have hCan' :
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction Ω.state ≤
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (ω.traceRight.canonicalPurification.reindex
            (Equiv.prodComm (QIT.TensorPower a n) (QIT.TensorPower a n))).state := by
    simpa [Ω, inputReferenceCanonicalExtension_traceRight (a := a) (n := n) (r := r) ω]
      using hCan
  have hPureInv :
      MState.IsPermutationInvariant
        (((ω.traceRight.canonicalPurification.reindex
          (Equiv.prodComm (QIT.TensorPower a n) (QIT.TensorPower a n))).state).traceRight)
        (a := a) := by
    rw [MState.canonicalPurification_reindex_prodComm_traceRight]
    exact hInv
  have hPure :=
    postSelection_pureInputReferenceAction_le_profile_count_of_traceRight_invariant
      (a := a) (n := n) (b := b) Φ Ψ
      (ω.traceRight.canonicalPurification.reindex
        (Equiv.prodComm (QIT.TensorPower a n) (QIT.TensorPower a n))) hPureInv
  exact hExt.trans (hCan'.trans hPure)

private theorem postSelection_labelExtensionAction_le_profile_count
    [Nonempty a] {r : Type x} [Fintype r] [DecidableEq r] [Nonempty r]
    (Φ Ψ : CPTPMap (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ)
    (ω : MState (QIT.TensorPower a n × r)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω ≤
      (Fintype.card (TensorPowerProfile (a × a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (ckrPostSelectionPurifiedReferenceState (a := a) n) := by
  have hlabel :=
    postSelectionCovariantDifference_labelExtension_action_eq
      (a := a) (n := n) (b := b) (r := r) Φ Ψ hcov ω
  have hbound :=
    inputReferenceAction_le_profile_count_of_invariantMarginal
      (a := a) (n := n) (b := b)
      (r := r × Equiv.Perm (Fin n)) Φ Ψ
      (ω.inputPermutationLabelExtension (a := a) (r := r))
      (MState.inputPermutationLabelExtension_traceRight_isPermutationInvariant
        (a := a) (r := r) ω)
  exact hlabel ▸ hbound

/-- CKR mixed input-reference reduction: under post-selection covariance, every
input-reference state is bounded by the purified post-selection reference
action with the exact profile-count factor. -/
theorem postSelection_inputReferenceAction_le_profile_count
    [Nonempty a] (Φ Ψ : CPTPMap (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ)
    (ω : MState (QIT.TensorPower a n × QIT.TensorPower a n)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω ≤
      (Fintype.card (TensorPowerProfile (a × a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (ckrPostSelectionPurifiedReferenceState (a := a) n) := by
  classical
  let _ : Nonempty (QIT.TensorPower a n) := QIT.tensorPower_nonempty_of_nonempty (α := a) n
  exact postSelection_labelExtensionAction_le_profile_count
    (a := a) (n := n) (b := b)
    (r := QIT.TensorPower a n) Φ Ψ hcov ω

/-- CKR finite-dimensional post-selection theorem in source-shaped diamond
trace-distance form, with the exact profile-count factor. -/
theorem postSelection_diamondTraceDistance_le_profile_count
    [Nonempty a] (Φ Ψ : CPTPMap (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ) :
    Φ.diamondTraceDistance Ψ ≤
      (Fintype.card (TensorPowerProfile (a × a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (ckrPostSelectionPurifiedReferenceState (a := a) n) := by
  classical
  refine CPTPOp.diamondTraceDistance_le_of_inputReferenceBound
    (a := QIT.TensorPower a n) (b := b) (Φ := Φ) (Ψ := Ψ)
    (ε := (Fintype.card (TensorPowerProfile (a × a) n) : ℝ) *
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (ckrPostSelectionPurifiedReferenceState (a := a) n)) ?_
  intro ω
  rw [CPTPOp.ancillaChannelTraceDistance_eq_channelDifferenceAction]
  exact postSelection_inputReferenceAction_le_profile_count
    (a := a) (n := n) (b := b) Φ Ψ hcov ω

/-- CKR post-selection theorem with the equivalent binomial symmetric-dimension
factor. -/
theorem postSelection_diamondTraceDistance_le_choose
    [Nonempty a] (Φ Ψ : CPTPMap (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ) :
    Φ.diamondTraceDistance Ψ ≤
      (Nat.choose (n + Fintype.card (a × a) - 1) n : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (ckrPostSelectionPurifiedReferenceState (a := a) n) := by
  simpa [tensorPowerProfile_card_eq_choose (a := a × a) n] using
    postSelection_diamondTraceDistance_le_profile_count
      (a := a) (n := n) (b := b) Φ Ψ hcov

/-- To bound the source-shaped finite-dimensional diamond trace distance it is
enough to bound the channel-difference action on pure input-reference states.
This packages the spectral decomposition and convexity bridge for later CKR
post-selection assembly. -/
theorem diamondTraceDistance_le_of_pureInputReferenceBound [Nonempty a]
    {Φ Ψ : CPTPMap a b} {ε : ℝ}
    (h : ∀ Ω : Ket (a × a),
      MatrixMap.ancillaNormalizedTraceAction (MatrixMap.channelDifference Φ Ψ) Ω.state ≤ ε) :
    Φ.diamondTraceDistance Ψ ≤ ε := by
  refine CPTPOp.diamondTraceDistance_le_of_inputReferenceBound (a := a) (b := b)
    (Φ := Φ) (Ψ := Ψ) (ε := ε) ?_
  intro ω
  rw [CPTPOp.ancillaChannelTraceDistance_eq_channelDifferenceAction]
  exact MatrixMap.ancillaNormalizedTraceAction_le_of_forall_pure_bound
    (MatrixMap.channelDifference Φ Ψ) ω h

end CPTPOp

end

noncomputable section

namespace QIT

open QIT

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [Fintype a] [DecidableEq a]

namespace SubnormalizedState

variable {n : ℕ}

/-- A subnormalized state is supported on the symmetric tensor-power subspace
when its matrix is bounded by the symmetric projection. -/
def SupportedOnSymmetricSubspace (ρ : SubnormalizedState (TensorPower a n)) : Prop :=
  ρ.matrix ≤ symmetricProjectionMatrix (a := a) n

theorem supportedOnSymmetricSubspace_iff
    (ρ : SubnormalizedState (TensorPower a n)) :
    ρ.SupportedOnSymmetricSubspace (a := a) ↔
      ρ.matrix ≤ symmetricProjectionMatrix (a := a) n := by
  rfl

end SubnormalizedState

end QIT

namespace MState

open QIT

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [Fintype a] [DecidableEq a]
variable {n : ℕ}

/-- Project a tensor-power state onto the symmetric subspace on both sides:
`P_sym ρ P_sym`. This matrix is generally subnormalized. -/
def symmetricProjectionSandwichMatrix (ρ : MState (TensorPower a n)) :
    CMatrix (TensorPower a n) :=
  symmetricProjectionMatrix (a := a) n * ρ.m * symmetricProjectionMatrix (a := a) n

@[simp]
theorem symmetricProjectionSandwichMatrix_eq (ρ : MState (TensorPower a n)) :
    ρ.symmetricProjectionSandwichMatrix (a := a) =
      symmetricProjectionMatrix (a := a) n * ρ.m *
        symmetricProjectionMatrix (a := a) n := rfl

/-- The symmetric projection sandwich `P_sym ρ P_sym` is positive semidefinite. -/
theorem symmetricProjectionSandwichMatrix_posSemidef
    (ρ : MState (TensorPower a n)) :
    (ρ.symmetricProjectionSandwichMatrix (a := a)).PosSemidef := by
  have h := ρ.psd.conjTranspose_mul_mul_same (symmetricProjectionMatrix (a := a) n)
  simpa [symmetricProjectionSandwichMatrix, symmetricProjectionMatrix_conjTranspose]
    using h

/-- The trace of `P_sym ρ P_sym` is at most one. -/
theorem symmetricProjectionSandwichMatrix_trace_re_le_one
    (ρ : MState (TensorPower a n)) :
    ((ρ.symmetricProjectionSandwichMatrix (a := a)).trace).re ≤ 1 := by
  let P : CMatrix (TensorPower a n) := symmetricProjectionMatrix (a := a) n
  have htrace_le' :
      ((ρ.m * P).trace).re ≤ ((ρ.m * 1).trace).re :=
    cMatrix_trace_mul_le_of_le_posSemidef_left ρ.psd
      (symmetricProjectionMatrix_le_one (a := a) n)
  have htrace_le : ((ρ.m * P).trace).re ≤ ρ.m.trace.re := by
    simpa [P, Matrix.mul_one] using htrace_le'
  have hcyc :
      (ρ.symmetricProjectionSandwichMatrix (a := a)).trace = (ρ.m * P).trace := by
    calc
      (ρ.symmetricProjectionSandwichMatrix (a := a)).trace =
          (P * ρ.m * P).trace := rfl
      _ = (ρ.m * (P * P)).trace := by
          calc
            (P * ρ.m * P).trace = ((P * ρ.m) * P).trace := by
              rw [Matrix.mul_assoc]
            _ = (P * (P * ρ.m)).trace := by rw [Matrix.trace_mul_comm]
            _ = ((P * P) * ρ.m).trace := by rw [← Matrix.mul_assoc]
            _ = (ρ.m * (P * P)).trace := by rw [Matrix.trace_mul_comm]
      _ = (ρ.m * P).trace := by
          rw [show P * P = P by
            exact symmetricProjectionMatrix_idempotent (a := a) n]
  rw [hcyc]
  rw [ρ.tr'] at htrace_le
  norm_num at htrace_le
  exact htrace_le

/-- The projected matrix `P_sym ρ P_sym` is bounded by `P_sym`; equivalently,
the projected subnormalized state is automatically supported in the symmetric
subspace. -/
theorem symmetricProjectionSandwichMatrix_le_symmetricProjection
    (ρ : MState (TensorPower a n)) :
    ρ.symmetricProjectionSandwichMatrix (a := a) ≤
      symmetricProjectionMatrix (a := a) n := by
  let P : CMatrix (TensorPower a n) := symmetricProjectionMatrix (a := a) n
  have hconj : P.conjTranspose * ρ.m * P ≤ P.conjTranspose * 1 * P :=
    star_left_conjugate_le_conjugate (matrix_le_one ρ) P
  simpa [symmetricProjectionSandwichMatrix, P, symmetricProjectionMatrix_conjTranspose,
    symmetricProjectionMatrix_idempotent, Matrix.mul_assoc] using hconj

/-- The symmetric projection sandwich as a subnormalized state. -/
def symmetricProjectionSandwichSubnormalizedState
    (ρ : MState (TensorPower a n)) :
    SubnormalizedState (TensorPower a n) where
  matrix := ρ.symmetricProjectionSandwichMatrix (a := a)
  pos := ρ.symmetricProjectionSandwichMatrix_posSemidef (a := a)
  trace_le_one := ρ.symmetricProjectionSandwichMatrix_trace_re_le_one (a := a)

@[simp]
theorem symmetricProjectionSandwichSubnormalizedState_matrix
    (ρ : MState (TensorPower a n)) :
    (ρ.symmetricProjectionSandwichSubnormalizedState (a := a)).matrix =
      ρ.symmetricProjectionSandwichMatrix (a := a) := rfl

/-- The symmetric projection sandwich subnormalized state is supported on the
symmetric tensor-power subspace. -/
theorem symmetricProjectionSandwichSubnormalizedState_supportedOnSymmetricSubspace
    (ρ : MState (TensorPower a n)) :
    SubnormalizedState.SupportedOnSymmetricSubspace
      (a := a) (ρ.symmetricProjectionSandwichSubnormalizedState (a := a)) :=
  ρ.symmetricProjectionSandwichMatrix_le_symmetricProjection (a := a)

private theorem symmetricProjectionSandwichMatrix_fixed
    (ρ : MState (TensorPower a n)) :
    symmetricProjectionMatrix (a := a) n *
        ρ.symmetricProjectionSandwichMatrix (a := a) *
        symmetricProjectionMatrix (a := a) n =
      ρ.symmetricProjectionSandwichMatrix (a := a) := by
  let P : CMatrix (TensorPower a n) := symmetricProjectionMatrix (a := a) n
  calc
    P * ρ.symmetricProjectionSandwichMatrix (a := a) * P =
        P * (P * ρ.m * P) * P := rfl
    _ = P * ρ.m * P := by
        have hP2 : P * P = P := symmetricProjectionMatrix_idempotent (a := a) n
        calc
          P * (P * ρ.m * P) * P = (P * P) * ρ.m * (P * P) := by
            noncomm_ring
          _ = P * ρ.m * P := by rw [hP2]

private theorem supportedOnSymmetricSubspace_of_projection_fixed
    (ρ : MState (TensorPower a n))
    (hfixed : symmetricProjectionMatrix (a := a) n * ρ.m *
        symmetricProjectionMatrix (a := a) n = ρ.m) :
    ρ.SupportedOnSymmetricSubspace (a := a) := by
  let P : CMatrix (TensorPower a n) := symmetricProjectionMatrix (a := a) n
  have hconj : P.conjTranspose * ρ.m * P ≤ P.conjTranspose * 1 * P :=
    star_left_conjugate_le_conjugate (matrix_le_one ρ) P
  simpa [SupportedOnSymmetricSubspace, P, symmetricProjectionMatrix_conjTranspose,
    symmetricProjectionMatrix_idempotent, Matrix.mul_assoc, hfixed] using hconj

/-- Normalize the symmetric projection sandwich when its trace is positive. -/
def symmetricProjectionNormalizedState
    (ρ : MState (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re) :
    MState (TensorPower a n) := .ofMatrix
  (matrix := (((ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)⁻¹ : ℂ) •
    ρ.symmetricProjectionSandwichMatrix (a := a))
  (pos := (ρ.symmetricProjectionSandwichMatrix_posSemidef (a := a)).smul
    (by exact_mod_cast inv_nonneg.mpr htrace.le))
  (trace_eq_one := by
    rw [Matrix.trace_smul]
    have htrace_im :
        (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.im = 0 :=
      (Matrix.PosSemidef.trace_nonneg
        (ρ.symmetricProjectionSandwichMatrix_posSemidef (a := a))).2.symm
    have htrace_complex :
        (ρ.symmetricProjectionSandwichMatrix (a := a)).trace =
          ((ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using htrace_im
    rw [htrace_complex]
    let t : ℝ := (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re
    have ht_ne : t ≠ 0 := ne_of_gt htrace
    change ((t : ℂ)⁻¹ • (t : ℂ)) = 1
    rw [Algebra.smul_def]
    have htc_ne : (t : ℂ) ≠ 0 := by exact_mod_cast ht_ne
    simpa using inv_mul_cancel₀ htc_ne)

@[simp]
theorem symmetricProjectionNormalizedState_matrix
    (ρ : MState (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re) :
    (ρ.symmetricProjectionNormalizedState (a := a) htrace).m =
      (((ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)⁻¹ : ℂ) •
        ρ.symmetricProjectionSandwichMatrix (a := a) :=
  MState.matrix_ofMatrix _ _ _

/-- The normalized symmetric projection state is supported on the symmetric
tensor-power subspace. -/
theorem symmetricProjectionNormalizedState_supportedOnSymmetricSubspace
    (ρ : MState (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re) :
    MState.SupportedOnSymmetricSubspace
      (a := a) (ρ.symmetricProjectionNormalizedState (a := a) htrace) := by
  apply supportedOnSymmetricSubspace_of_projection_fixed
  rw [symmetricProjectionNormalizedState_matrix]
  calc
    symmetricProjectionMatrix (a := a) n *
        ((((ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)⁻¹ : ℂ) •
          ρ.symmetricProjectionSandwichMatrix (a := a)) *
        symmetricProjectionMatrix (a := a) n =
        (((ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)⁻¹ : ℂ) •
          (symmetricProjectionMatrix (a := a) n *
            ρ.symmetricProjectionSandwichMatrix (a := a) *
            symmetricProjectionMatrix (a := a) n) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = (((ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)⁻¹ : ℂ) •
          ρ.symmetricProjectionSandwichMatrix (a := a) := by
          rw [symmetricProjectionSandwichMatrix_fixed]

/-- The normalized symmetric projection state can be used directly in the
exact profile-count post-selection domination theorem. -/
theorem matrixDominatedBy_symmetricProjectionReferenceState_of_symmetricProjectionNormalizedState
    [Nonempty a] (ρ : MState (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re) :
    (ρ.symmetricProjectionNormalizedState (a := a) htrace).MatrixDominatedBy
      (Fintype.card (TensorPowerProfile a n) : ℝ)
      (symmetricProjectionReferenceState (a := a) n) :=
  matrixDominatedBy_symmetricProjectionReferenceState_of_supported
    (a := a)
    (ρ.symmetricProjectionNormalizedState_supportedOnSymmetricSubspace
      (a := a) htrace)

/-- Polynomial-factor post-selection domination for the normalized symmetric
projection state. -/
theorem matrixDominatedBy_symmetricProjectionReferenceState_pow_succ_of_symmetricProjectionNormalizedState
    [Nonempty a] (ρ : MState (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re) :
    (ρ.symmetricProjectionNormalizedState (a := a) htrace).MatrixDominatedBy
      ((n + 1) ^ Fintype.card a : ℝ)
      (symmetricProjectionReferenceState (a := a) n) :=
  matrixDominatedBy_symmetricProjectionReferenceState_pow_succ_of_supported
    (a := a)
    (ρ.symmetricProjectionNormalizedState_supportedOnSymmetricSubspace
      (a := a) htrace)

/-- Exact profile-count channel-output post-selection domination for the
normalized symmetric projection state. -/
theorem matrixDominatedBy_applyChannel_symmetricProjectionReferenceState_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : MState (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : CPTPMap (TensorPower a n) b) :
    MState.MatrixDominatedBy (Φ (ρ.symmetricProjectionNormalizedState (a := a) htrace))
      (Fintype.card (TensorPowerProfile a n) : ℝ)
      (Φ (symmetricProjectionReferenceState (a := a) n)) :=
  matrixDominatedBy_applyChannel Φ
    (ρ.matrixDominatedBy_symmetricProjectionReferenceState_of_symmetricProjectionNormalizedState
      (a := a) htrace)

/-- Polynomial-factor channel-output post-selection domination for the
normalized symmetric projection state. -/
theorem matrixDominatedBy_applyChannel_symmetricProjectionReferenceState_pow_succ_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : MState (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : CPTPMap (TensorPower a n) b) :
    MState.MatrixDominatedBy (Φ (ρ.symmetricProjectionNormalizedState (a := a) htrace))
      ((n + 1) ^ Fintype.card a : ℝ)
      (Φ (symmetricProjectionReferenceState (a := a) n)) :=
  matrixDominatedBy_applyChannel Φ
    (ρ.matrixDominatedBy_symmetricProjectionReferenceState_pow_succ_of_symmetricProjectionNormalizedState
      (a := a) htrace)

/-- Polynomial-factor trace-distance post-selection theorem with the
constructed normalized projection state as input. -/
theorem stateLevelPostSelectionTraceDistanceBound_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : MState (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : CPTPMap (TensorPower a n) b) :
    ChannelOutputTraceDistanceBound Φ
      (ρ.symmetricProjectionNormalizedState (a := a) htrace)
      (symmetricProjectionReferenceState (a := a) n)
      (((n + 1) ^ Fintype.card a : ℝ) - 1) :=
  channelOutputTraceDistanceBound_of_matrixDominatedBy Φ
    (ρ.matrixDominatedBy_symmetricProjectionReferenceState_pow_succ_of_symmetricProjectionNormalizedState
      (a := a) htrace)

/-- Exact profile-count trace-distance post-selection theorem with the
constructed normalized projection state as input. -/
theorem stateLevelPostSelectionTraceDistanceBound_profile_count_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : MState (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : CPTPMap (TensorPower a n) b) :
    ChannelOutputTraceDistanceBound Φ
      (ρ.symmetricProjectionNormalizedState (a := a) htrace)
      (symmetricProjectionReferenceState (a := a) n)
      ((Fintype.card (TensorPowerProfile a n) : ℝ) - 1) :=
  channelOutputTraceDistanceBound_of_matrixDominatedBy Φ
    (ρ.matrixDominatedBy_symmetricProjectionReferenceState_of_symmetricProjectionNormalizedState
      (a := a) htrace)

/-- Difference-matrix form of the polynomial post-selection domination theorem
for the constructed normalized projection state. -/
theorem stateLevelPostSelectionDifference_posSemidef_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : MState (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : CPTPMap (TensorPower a n) b) :
    ((((n + 1) ^ Fintype.card a : ℝ) : ℂ) •
        (Φ (symmetricProjectionReferenceState (a := a) n)).m -
      (Φ (ρ.symmetricProjectionNormalizedState (a := a) htrace)).m).PosSemidef := by
  have h :=
    ρ.matrixDominatedBy_applyChannel_symmetricProjectionReferenceState_pow_succ_of_symmetricProjectionNormalizedState
      (a := a) htrace Φ
  dsimp [MatrixDominatedBy] at h
  rwa [Matrix.le_iff] at h

/-- Difference-matrix form of the exact profile-count post-selection domination
theorem for the constructed normalized projection state. -/
theorem stateLevelPostSelectionDifference_profile_count_posSemidef_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : MState (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : CPTPMap (TensorPower a n) b) :
    (((Fintype.card (TensorPowerProfile a n) : ℝ) : ℂ) •
        (Φ (symmetricProjectionReferenceState (a := a) n)).m -
      (Φ (ρ.symmetricProjectionNormalizedState (a := a) htrace)).m).PosSemidef := by
  have h :=
    ρ.matrixDominatedBy_applyChannel_symmetricProjectionReferenceState_of_symmetricProjectionNormalizedState
      (a := a) htrace Φ
  dsimp [MatrixDominatedBy] at h
  rwa [Matrix.le_iff] at h

end MState

namespace QIT

namespace FiniteIidMixture

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [Fintype a] [DecidableEq a]
variable {n : ℕ} (M : FiniteIidMixture ι a n)

/-- A finite IID mixture state is dominated by itself with factor `1`. -/
theorem state_isDominatedBy_self :
    M.state.IsDominatedByFiniteIidMixture 1 M :=
  MState.matrixDominatedBy_refl M.state

/-- A finite IID mixture state is dominated by itself with any factor at least
`1`. -/
theorem state_isDominatedBy_self_mono_factor {c : ℝ} (hc : 1 ≤ c) :
    M.state.IsDominatedByFiniteIidMixture c M :=
  MState.isDominatedByFiniteIidMixture_mono_factor
    (M.state_isDominatedBy_self) hc

/-- Matrix form of the image of a finite IID mixture under a channel. -/
theorem applyChannel_state_matrix {b : Type w} [Fintype b] [DecidableEq b]
    (Φ : CPTPMap (TensorPower a n) b) :
    (Φ M.state).m =
      ∑ i, (M.probs i) • (Φ ((M.states i).tensorPower n)).m := by
  simp only [CPTPOp.mat_coe_eq_apply_mat]
  rw [M.state_matrix, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change Φ.map ((M.probs i : ℂ) • ((M.states i).tensorPower n).m) =
    (M.probs i : ℂ) • Φ.map ((M.states i).tensorPower n).m
  rw [map_smul]

/-- If every tensor-power component of a finite IID mixture is dominated by the
same target state with the same factor, then the whole mixture is dominated by
that target with the same factor. -/
theorem matrixDominatedBy_of_forall_tensorPower (τ : MState (TensorPower a n)) (c : ℝ)
    (h : ∀ i, ((M.states i).tensorPower n).MatrixDominatedBy c τ) :
    M.state.MatrixDominatedBy c τ := by
  dsimp [MState.MatrixDominatedBy] at h ⊢
  change (((c : ℂ) • τ.m) - M.state.m).PosSemidef
  rw [M.state_matrix]
  have hsum_coeff :
      (∑ i, (M.probs i) • ((c : ℂ) • τ.m)) = (c : ℂ) • τ.m := by
    rw [← Finset.sum_smul]
    rw [M.weights_sum, one_smul]
  have hrewrite :
      ((c : ℂ) • τ.m) -
          (∑ i, (M.probs i) • ((M.states i).tensorPower n).m) =
        ∑ i, (M.probs i) •
          (((c : ℂ) • τ.m) - ((M.states i).tensorPower n).m) := by
    calc
      ((c : ℂ) • τ.m) -
          (∑ i, (M.probs i) • ((M.states i).tensorPower n).m) =
          (∑ i, (M.probs i) • ((c : ℂ) • τ.m)) -
            (∑ i, (M.probs i) • ((M.states i).tensorPower n).m) := by
            rw [hsum_coeff]
      _ = ∑ i, ((M.probs i) • ((c : ℂ) • τ.m) -
            (M.probs i) • ((M.states i).tensorPower n).m) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ i, (M.probs i) •
          (((c : ℂ) • τ.m) - ((M.states i).tensorPower n).m) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [smul_sub]
  rw [hrewrite]
  exact Matrix.posSemidef_sum Finset.univ fun i _ =>
    (h i).smul (NNReal.coe_nonneg (M.probs i))

/-- If each channel image of a tensor-power component is dominated by the same
target state with the same factor, then the channel image of the whole finite
IID mixture is dominated by that target. -/
theorem applyChannel_matrixDominatedBy_of_forall_tensorPower
    {b : Type w} [Fintype b] [DecidableEq b]
    (Φ : CPTPMap (TensorPower a n) b) (τ : MState b) (c : ℝ)
    (h : ∀ i, MState.MatrixDominatedBy (Φ ((M.states i).tensorPower n)) c τ) :
    MState.MatrixDominatedBy (Φ M.state) c τ := by
  dsimp [MState.MatrixDominatedBy] at h ⊢
  change (((c : ℂ) • τ.m) - (Φ M.state).m).PosSemidef
  rw [M.applyChannel_state_matrix Φ]
  have hsum_coeff :
      (∑ i, (M.probs i) • ((c : ℂ) • τ.m)) = (c : ℂ) • τ.m := by
    rw [← Finset.sum_smul]
    rw [M.weights_sum, one_smul]
  have hrewrite :
      ((c : ℂ) • τ.m) -
          (∑ i, (M.probs i) • (Φ ((M.states i).tensorPower n)).m) =
        ∑ i, (M.probs i) •
          (((c : ℂ) • τ.m) -
            (Φ ((M.states i).tensorPower n)).m) := by
    calc
      ((c : ℂ) • τ.m) -
          (∑ i, (M.probs i) • (Φ ((M.states i).tensorPower n)).m) =
          (∑ i, (M.probs i) • ((c : ℂ) • τ.m)) -
            (∑ i, (M.probs i) • (Φ ((M.states i).tensorPower n)).m) := by
            rw [hsum_coeff]
      _ = ∑ i, ((M.probs i) • ((c : ℂ) • τ.m) -
            (M.probs i) • (Φ ((M.states i).tensorPower n)).m) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ i, (M.probs i) •
          (((c : ℂ) • τ.m) -
            (Φ ((M.states i).tensorPower n)).m) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [smul_sub]
  rw [hrewrite]
  exact Matrix.posSemidef_sum Finset.univ fun i _ =>
    (h i).smul (NNReal.coe_nonneg (M.probs i))

/-- If each channel image of a tensor-power component is dominated by the same
output finite IID mixture, then the channel image of the whole finite IID
mixture is dominated by that output mixture. -/
theorem applyChannel_isDominatedByFiniteIidMixture_of_forall_tensorPower
    {κ : Type x} {b : Type w} [Fintype κ] [Fintype b] [DecidableEq b]
    (Φ : CPTPMap (TensorPower a n) (TensorPower b n))
    (N : FiniteIidMixture κ b n) (c : ℝ)
    (h : ∀ i, MState.IsDominatedByFiniteIidMixture (Φ ((M.states i).tensorPower n)) c N) :
    MState.IsDominatedByFiniteIidMixture (Φ M.state) c N :=
  M.applyChannel_matrixDominatedBy_of_forall_tensorPower Φ N.state c h

/-- If every tensor-power component of a finite IID mixture is dominated by the
same finite IID mixture, then the averaged mixture is dominated by it as well. -/
theorem isDominatedByFiniteIidMixture_of_forall_tensorPower
    (N : FiniteIidMixture ι a n) (c : ℝ)
    (h : ∀ i, ((M.states i).tensorPower n).IsDominatedByFiniteIidMixture c N) :
    M.state.IsDominatedByFiniteIidMixture c N :=
  M.matrixDominatedBy_of_forall_tensorPower N.state c h

/-- Componentwise domination by a finite IID mixture can be composed with
matrix domination of the target mixture state. -/
theorem matrixDominatedBy_trans_of_forall_tensorPower
    (N : FiniteIidMixture ι a n) (τ : MState (TensorPower a n)) {c d : ℝ}
    (hc : 0 ≤ c)
    (h : ∀ i, ((M.states i).tensorPower n).IsDominatedByFiniteIidMixture c N)
    (hNτ : N.state.MatrixDominatedBy d τ) :
    M.state.MatrixDominatedBy (c * d) τ :=
  MState.matrixDominatedBy_trans hc
    (M.isDominatedByFiniteIidMixture_of_forall_tensorPower N c h) hNτ

end FiniteIidMixture

end QIT
