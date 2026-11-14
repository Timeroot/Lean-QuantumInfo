/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Symmetry.DeFinetti.RennerProjectors

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal
open MeasureTheory

namespace QIT

universe u v w x

noncomputable section

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [Fintype a] [DecidableEq a]

local instance deFinettiPostselectionCMatrixContinuousENorm
    {α : Type v} [Fintype α] [DecidableEq α] :
    ContinuousENorm (CMatrix α) :=
  SeminormedAddGroup.toContinuousENorm

private theorem idChannel_map_eq_self
    {α : Type u} [Fintype α] [DecidableEq α] (X : CMatrix α) :
    (Channel.idChannel α).map X = X := by
  simp [Channel.idChannel, MatrixMap.ofKraus]

private theorem traceEffectToUnit_single_apply
    {α : Type u} [Fintype α] [DecidableEq α]
    {E : CMatrix α} (hE : E.PosSemidef) (p q : α) :
    MatrixMap.traceEffectToUnit E (Matrix.single p q (1 : ℂ))
        PUnit.unit PUnit.unit = E q p := by
  have h := MatrixMap.traceEffectToUnit_apply_of_posSemidef (a := α)
    (E := E) (X := Matrix.single p q (1 : ℂ)) hE
  have happ := congrFun (congrFun h PUnit.unit) PUnit.unit
  calc
    MatrixMap.traceEffectToUnit E (Matrix.single p q (1 : ℂ))
        PUnit.unit PUnit.unit =
        ((Matrix.single p q (1 : ℂ) * E).trace) := happ
    _ = E q p := by
          rw [Matrix.trace]
          change
            (∑ x : α, (Matrix.single p q (1 : ℂ) * E) x x) = E q p
          rw [Finset.sum_eq_single p]
          · simp [Matrix.mul_apply, Matrix.single]
          · intro r _ hr
            have hpr : p ≠ r := by exact hr.symm
            simp [Matrix.mul_apply, Matrix.single, hpr]
          · intro hp
            simp at hp

private theorem kron_id_traceEffectToUnit_raw_sum
    {α β : Type u} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {E : CMatrix β} (hE : E.PosSemidef)
    (X : CMatrix (Prod α β)) (x y : α) :
    (∑ p : β, ∑ q : β, ∑ i : α, ∑ i' : α,
        X (i, p) (i', q) * Matrix.single i i' (1 : ℂ) x y *
          MatrixMap.traceEffectToUnit E (Matrix.single p q (1 : ℂ))
            PUnit.unit PUnit.unit) =
      ∑ p : β, ∑ q : β, X (x, p) (y, q) * E q p := by
  classical
  have hT :
      ∀ p q : β,
        MatrixMap.traceEffectToUnit E (Matrix.single p q (1 : ℂ))
            PUnit.unit PUnit.unit = E q p := by
    intro p q
    exact traceEffectToUnit_single_apply (E := E) hE p q
  calc
    (∑ p : β, ∑ q : β, ∑ i : α, ∑ i' : α,
        X (i, p) (i', q) * Matrix.single i i' (1 : ℂ) x y *
          MatrixMap.traceEffectToUnit E (Matrix.single p q (1 : ℂ))
            PUnit.unit PUnit.unit) =
        ∑ p : β, ∑ q : β,
          X (x, p) (y, q) *
            MatrixMap.traceEffectToUnit E (Matrix.single p q (1 : ℂ))
              PUnit.unit PUnit.unit := by
          refine Finset.sum_congr rfl fun p _ => ?_
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_eq_single x]
          · rw [Finset.sum_eq_single y]
            · rw [Matrix.single_apply_same]
              ring
            · intro y' _ hy'
              rw [Matrix.single_apply_of_col_ne x x hy' (1 : ℂ)]
              ring
            · intro hnot_mem
              simp at hnot_mem
          · intro x' _ hx'
            apply Finset.sum_eq_zero
            intro y' _
            rw [Matrix.single_apply_of_row_ne hx' y' y (1 : ℂ)]
            ring
          · intro hnot_mem
            simp at hnot_mem
    _ = ∑ p : β, ∑ q : β, X (x, p) (y, q) * E q p := by
          refine Finset.sum_congr rfl fun p _ => ?_
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [hT p q]

private theorem dropRightUnitMatrix_kron_id_traceEffectToUnit_apply
    {α β : Type u} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {E : CMatrix β} (hE : E.PosSemidef)
    (X : CMatrix (Prod α β)) (x y : α) :
    dropRightUnitMatrix
        ((MatrixMap.kron (Channel.idChannel α).map (MatrixMap.traceEffectToUnit E)) X)
        x y =
      ∑ p : β, ∑ q : β, X (x, p) (y, q) * E q p := by
  classical
  simpa only [dropRightUnitMatrix, MatrixMap.kron, idChannel_map_eq_self] using
    kron_id_traceEffectToUnit_raw_sum (E := E) hE X x y

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
    (X : CMatrix (Prod α (Prod β γ))) : CMatrix (Prod (Prod α β) γ) :=
  X.submatrix (Equiv.prodAssoc α β γ) (Equiv.prodAssoc α β γ)

private theorem traceNorm_assocRightMatrix
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (X : CMatrix (Prod α (Prod β γ))) :
    traceNorm (assocRightMatrix X) = traceNorm X := by
  simpa [assocRightMatrix] using
    (traceNorm_submatrix_equiv (Equiv.prodAssoc α β γ) X)

private theorem assocRightMatrix_isHermitian
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    {X : CMatrix (Prod α (Prod β γ))} (hX : X.IsHermitian) :
    (assocRightMatrix X).IsHermitian := by
  simpa [assocRightMatrix] using hX.submatrix (Equiv.prodAssoc α β γ)

private theorem trace_assocRightMatrix
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (X : CMatrix (Prod α (Prod β γ))) :
    (assocRightMatrix X).trace = X.trace := by
  rw [assocRightMatrix]
  rw [Matrix.trace]
  rw [Matrix.trace]
  exact Fintype.sum_equiv (Equiv.prodAssoc α β γ)
    (fun x : Prod (Prod α β) γ =>
      X (Equiv.prodAssoc α β γ x) (Equiv.prodAssoc α β γ x))
    (fun y : Prod α (Prod β γ) => X y y)
    (by intro x; rfl)

private theorem dropRightUnitMatrix_action_traceEffectToUnit_commute
    {b : Type w} [Fintype b] [DecidableEq b]
    [Nonempty a] {n : ℕ}
    (Δ : MatrixMap (TensorPower a n) b)
    {E : CMatrix (ckrPurifyingRegister a n)} (hE : E.PosSemidef) :
    dropRightUnitMatrix
      ((MatrixMap.kron (Channel.idChannel (Prod b (QIT.TensorPower a n))).map
          (MatrixMap.traceEffectToUnit E))
        (assocRightMatrix
          ((MatrixMap.kron Δ
              (Channel.idChannel (Prod (QIT.TensorPower a n) (ckrPurifyingRegister a n))).map)
            (ckrPostSelectionPurifiedReferenceState (a := a) n).matrix))) =
    MatrixMap.kron Δ (Channel.idChannel (TensorPower a n)).map
      ((dropRightUnitMatrix
          ((MatrixMap.kron
              (Channel.idChannel (TensorPower (Prod a a) n)).map
              (MatrixMap.traceEffectToUnit E))
            (ckrPurifiedReferenceState (a := a) n).matrix)).submatrix
        (tensorPowerProdEquiv a a n).symm (tensorPowerProdEquiv a a n).symm) := by
  ext br br'
  simp [assocRightMatrix, dropRightUnitMatrix, MatrixMap.kron_idChannel_apply_slice,
    MatrixMap.kron_idChannel_left_apply_slice,
    MatrixMap.traceEffectToUnit_apply_of_posSemidef hE]
  exact matrixMap_trace_weight_commute Δ
    (fun j j' => fun i i' =>
      (ckrPurifiedReferenceVector (a := a) n).amp
        ((tensorPowerProdEquiv a a n).symm (i, br.2), j) *
      star ((ckrPurifiedReferenceVector (a := a) n).amp
        ((tensorPowerProdEquiv a a n).symm (i', br'.2), j')))
    E br.1 br'.1

namespace State

variable {n : ℕ}

/-- Reindex the CKR permutation-label extension from label-first block form to
the input-first convention used by `ancillaNormalizedTraceAction`. -/
def inputPermutationLabelEquiv {r : Type w} {n : ℕ} :
    Equiv (Prod (Equiv.Perm (Fin n)) (Prod (TensorPower a n) r))
      (Prod (TensorPower a n) (Prod r (Equiv.Perm (Fin n)))) where
  toFun x := (x.2.1, x.2.2, x.1)
  invFun x := (x.2.2, x.1, x.2.1)
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; cases x with | mk xA xrπ => cases xrπ; rfl

private theorem trace_submatrix_equiv_local {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M : CMatrix κ) :
    (M.submatrix e e).trace = M.trace := by
  classical
  unfold Matrix.trace
  exact Fintype.sum_equiv e (fun i => M (e i) (e i)) (fun k => M k k) (by simp)

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
    {H P : CMatrix (Prod ι β)}
    (hoff : ∀ (i j : ι) (x y : β), i ≠ j -> H (i, x) (j, y) = 0) :
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
    {H P : CMatrix (Prod ι β)}
    (hoff : ∀ (i j : ι) (x y : β), i ≠ j -> H (i, x) (j, y) = 0) :
    ((H * P).trace).re =
      ∑ i : ι, ((((Classical.block H i i) * Classical.block P i i).trace).re) := by
  rw [trace_mul_block_decomp_complex (H := H) (P := P) hoff]
  simp

private theorem classical_block_posSemidef {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {M : CMatrix (Prod ι β)} (hM : M.PosSemidef) (i : ι) :
    (Classical.block M i i).PosSemidef := by
  simpa [Classical.block] using hM.submatrix (fun x : β => (i, x))

private theorem classical_block_le_one {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {M : CMatrix (Prod ι β)} (hM : M ≤ 1) (i : ι) :
    Classical.block M i i ≤ 1 := by
  rw [Matrix.le_iff] at hM ⊢
  have h := hM.submatrix (fun x : β => (i, x))
  convert h using 1
  ext x y
  simp [Classical.block, Matrix.sub_apply, Matrix.one_apply]

private theorem classical_block_isHermitian {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {M : CMatrix (Prod ι β)} (hM : M.IsHermitian) (i : ι) :
    (Classical.block M i i).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext x y
  simpa [Classical.block, Matrix.conjTranspose] using congrFun (congrFun hM (i, x)) (i, y)

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
  let H : CMatrix (Prod ι β) := Classical.blockDiagonal blocks
  have hH : H.IsHermitian := classical_blockDiagonal_isHermitian blocks hblocks
  let P : CMatrix (Prod ι β) := positiveSpectralProjector H hH
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
      (1 : CMatrix (Prod ι β)) - Classical.blockDiagonal blocks =
        Classical.blockDiagonal (fun i => (1 : CMatrix β) - blocks i) := by
    ext x y
    rcases x with ⟨xi, xb⟩
    rcases y with ⟨yi, yb⟩
    by_cases hxy : xi = yi
    · subst hxy
      change (1 : CMatrix (Prod ι β)) (xi, xb) (xi, yb) -
          Classical.blockDiagonal blocks (xi, xb) (xi, yb) =
        Classical.blockDiagonal (fun i => (1 : CMatrix β) - blocks i) (xi, xb) (xi, yb)
      rw [classical_blockDiagonal_block_self_apply blocks xi xb yb]
      rw [classical_blockDiagonal_block_self_apply
        (fun i => (1 : CMatrix β) - blocks i) xi xb yb]
      simp [Matrix.sub_apply, Matrix.one_apply]
    · have hpair : (xi, xb) ≠ (yi, yb) := by
        intro h
        exact hxy (Prod.ext_iff.mp h).1
      change (1 : CMatrix (Prod ι β)) (xi, xb) (yi, yb) -
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
  let H : CMatrix (Prod ι β) := Classical.blockDiagonal blocks
  have hH : H.IsHermitian := classical_blockDiagonal_isHermitian blocks hblocks
  let P : CMatrix (Prod ι β) :=
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
  let H : CMatrix (Prod ι β) := Classical.blockDiagonal blocks
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
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    State (Prod (TensorPower a n) (Prod r (Equiv.Perm (Fin n)))) where
  matrix :=
    (Classical.blockDiagonal (fun π : Equiv.Perm (Fin n) =>
      ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
        (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))
      ).submatrix
        (inputPermutationLabelEquiv (a := a) (r := r) (n := n)).symm
        (inputPermutationLabelEquiv (a := a) (r := r) (n := n)).symm
  pos := by
    classical
    apply Matrix.PosSemidef.submatrix
    apply classical_blockDiagonal_posSemidef
    intro π
    have hcR : 0 ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ :=
      inv_nonneg.mpr (Nat.cast_nonneg _)
    have hcC : 0 ≤ ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ)) := by
      exact_mod_cast hcR
    exact ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).pos).smul hcC
  trace_eq_one := by
    classical
    rw [trace_submatrix_equiv_local]
    rw [classical_blockDiagonal_trace]
    simp only [Matrix.trace_smul, State.trace_eq_one, Finset.sum_const, nsmul_eq_mul]
    have hcard_ne : (Fintype.card (Equiv.Perm (Fin n)) : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero :
        Fintype.card (Equiv.Perm (Fin n)) ≠ 0)
    have hcard_neR : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero :
        Fintype.card (Equiv.Perm (Fin n)) ≠ 0)
    simp only [smul_eq_mul, mul_one] at *
    change (Fintype.card (Equiv.Perm (Fin n)) : ℂ) *
        (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) = 1
    norm_num [hcard_ne]

private theorem inputPermutationLabelExtension_slice_same
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r))
    (π : Equiv.Perm (Fin n)) (i i' : TensorPower a n) (j j' : r) :
    (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix
      (i, (j, π)) (i', (j', π)) =
      ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) *
        (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix
          (i, j) (i', j')) := by
  dsimp [State.inputPermutationLabelExtension]
  simp only [State.inputPermutationLabelEquiv, Classical.blockDiagonal, Matrix.sum_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.single, Matrix.smul_apply]
  rw [Finset.sum_eq_single π]
  · simp
  · intro σ _ hσ
    have hne : σ ≠ π := hσ
    simp [hne]
  · intro hnot
    simp at hnot

private theorem inputPermutationLabelExtension_slice_ne
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r))
    {π σ : Equiv.Perm (Fin n)} (hπσ : π ≠ σ)
    (i i' : TensorPower a n) (j j' : r) :
    (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix
      (i, (j, π)) (i', (j', σ)) = 0 := by
  dsimp [State.inputPermutationLabelExtension]
  simp only [State.inputPermutationLabelEquiv, Classical.blockDiagonal, Matrix.sum_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.single, Matrix.smul_apply]
  refine Finset.sum_eq_zero fun τ _ => ?_
  by_cases hτπ : τ = π
  · subst hτπ
    simp [hπσ]
  · simp [hτπ]

/-- The input marginal of the permutation-labelled extension is the ordinary
input permutation twirl. -/
theorem inputPermutationLabelExtension_marginalA_eq_inputPermutationTwirling_marginalA
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    (ω.inputPermutationLabelExtension (a := a) (r := r)).marginalA =
      (ω.inputPermutationTwirling (a := a) (r := r)).marginalA := by
  apply State.ext
  ext i i'
  simp only [State.marginalA, partialTraceB]
  rw [Fintype.sum_prod_type]
  simp only [inputPermutationLabelExtension_slice_same]
  simp [State.inputPermutationTwirling, Matrix.smul_apply, Matrix.sum_apply,
    Finset.mul_sum]

/-- The input marginal of the permutation-labelled extension is permutation
invariant. -/
theorem inputPermutationLabelExtension_marginalA_isPermutationInvariant
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    (ω.inputPermutationLabelExtension (a := a) (r := r)).marginalA.IsPermutationInvariant
      (a := a) := by
  rw [inputPermutationLabelExtension_marginalA_eq_inputPermutationTwirling_marginalA]
  exact inputPermutationTwirling_marginalA_isPermutationInvariant (a := a) (r := r) ω

private def outputPermutationLabelEquiv {r : Type w} {b : Type x} {n : ℕ} :
    Equiv (Prod b (Prod r (Equiv.Perm (Fin n))))
      (Prod (Equiv.Perm (Fin n)) (Prod b r)) where
  toFun x := (x.2.2, x.1, x.2.1)
  invFun x := (x.2.1, x.2.2, x.1)
  left_inv := by intro x; cases x with | mk xb xrπ => cases xrπ; rfl
  right_inv := by intro x; cases x with | mk xπ xbr => cases xbr; rfl

private theorem inputPermutationLabelExtension_action_block_same
    {r : Type w} [Fintype r] [DecidableEq r]
    {b : Type x} [Fintype b] [DecidableEq b]
    {n : ℕ} (Δ : MatrixMap (TensorPower a n) b)
    (ω : State (Prod (TensorPower a n) r)) (π : Equiv.Perm (Fin n)) :
    MatrixMap.blockCompression (β := Prod b r) π
      ((MatrixMap.kron Δ (Channel.idChannel (Prod r (Equiv.Perm (Fin n)))).map
        (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix).submatrix
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm) =
      (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
        MatrixMap.kron Δ (Channel.idChannel r).map
          ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix) := by
  ext br br'
  rcases br with ⟨bo, rr⟩
  rcases br' with ⟨bo', rr'⟩
  simp only [MatrixMap.blockCompression_apply, Matrix.submatrix_apply, Matrix.smul_apply]
  rw [MatrixMap.kron_idChannel_apply_slice]
  rw [MatrixMap.kron_idChannel_apply_slice]
  change Δ
      (fun i i' =>
        (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix
          (i, (rr, π)) (i', (rr', π))) bo bo' =
    ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
      Δ (fun i i' =>
        (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix
          (i, rr) (i', rr'))) bo bo'
  have hslice :
      (fun i i' =>
        (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix
          (i, (rr, π)) (i', (rr', π))) =
        (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
          (fun i i' =>
            (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix
              (i, rr) (i', rr')) := by
    ext i i'
    exact inputPermutationLabelExtension_slice_same
      (a := a) (r := r) (n := n) ω π i i' rr rr'
  rw [hslice]
  let c : ℂ := (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ)
  let X : CMatrix (TensorPower a n) := fun i i' =>
    (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix
      (i, rr) (i', rr')
  have hlin : Δ (c • X) = c • Δ X := LinearMap.map_smul Δ c X
  change Δ (c • X) bo bo' = (c • Δ X) bo bo'
  exact congrFun (congrFun hlin bo) bo'

private theorem inputPermutationLabelExtension_action_block_ne
    {r : Type w} [Fintype r] [DecidableEq r]
    {b : Type x} [Fintype b] [DecidableEq b]
    {n : ℕ} (Δ : MatrixMap (TensorPower a n) b)
    (ω : State (Prod (TensorPower a n) r)) {π σ : Equiv.Perm (Fin n)}
    (hπσ : π ≠ σ) (br br' : Prod b r) :
    ((MatrixMap.kron Δ (Channel.idChannel (Prod r (Equiv.Perm (Fin n)))).map
        (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix).submatrix
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm)
        (π, br) (σ, br') = 0 := by
  rcases br with ⟨bo, rr⟩
  rcases br' with ⟨bo', rr'⟩
  simp only [Matrix.submatrix_apply]
  rw [MatrixMap.kron_idChannel_apply_slice]
  change Δ
      (fun i i' =>
        (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix
          (i, (rr, π)) (i', (rr', σ))) bo bo' = 0
  have hslice :
      (fun i i' =>
        (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix
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
    (ω : State (Prod (TensorPower a n) r)) :
    ((MatrixMap.kron Δ (Channel.idChannel (Prod r (Equiv.Perm (Fin n)))).map
        (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix).submatrix
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm) =
      Classical.blockDiagonal (fun π : Equiv.Perm (Fin n) =>
        (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
          MatrixMap.kron Δ (Channel.idChannel r).map
            ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix)) := by
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
          MatrixMap.kron Δ (Channel.idChannel r).map
            ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))
      π br br'
    exact hblock.trans hself.symm
  · rw [inputPermutationLabelExtension_action_block_ne
      (a := a) (r := r) (b := b) Δ ω hπσ br br']
    rw [classical_blockDiagonal_offdiag
      (fun π : Equiv.Perm (Fin n) =>
        (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
          MatrixMap.kron Δ (Channel.idChannel r).map
            ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))
      hπσ br br']

private theorem cMatrix_isHermitian_real_smul {β : Type x} [Fintype β] [DecidableEq β]
    {c : ℝ} {M : CMatrix β} (hM : M.IsHermitian) :
    (((c : ℂ) • M) : CMatrix β).IsHermitian := by
  exact hM.smul (by simp [IsSelfAdjoint])

private theorem inputPermutationLabelExtension_channelDifference_action_traceNorm_eq_sum
    {r : Type w} [Fintype r] [DecidableEq r]
    {b : Type x} [Fintype b] [DecidableEq b]
    {n : ℕ} (Φ Ψ : Channel (TensorPower a n) b)
    (ω : State (Prod (TensorPower a n) r)) :
    traceNorm
      (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ)
        (Channel.idChannel (Prod r (Equiv.Perm (Fin n)))).map
        (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix) =
      ∑ π : Equiv.Perm (Fin n),
        traceNorm
          (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℂ) •
            MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
              ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix)) := by
  classical
  let Δ : MatrixMap (TensorPower a n) b := MatrixMap.channelDifference Φ Ψ
  let M : CMatrix (Prod b (Prod r (Equiv.Perm (Fin n)))) :=
    MatrixMap.kron Δ (Channel.idChannel (Prod r (Equiv.Perm (Fin n)))).map
      (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix
  let blocks : Equiv.Perm (Fin n) → CMatrix (Prod b r) := fun π =>
    (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℂ) •
      MatrixMap.kron Δ (Channel.idChannel r).map
        ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))
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
      (M := MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
        ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))
      (MatrixMap.channelDifference_kron_id_apply_isHermitian
      (a := TensorPower a n) (b := b) (r := r) Φ Ψ
      (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω))
  have htr : ∀ π, (blocks π).trace = 0 := by
    intro π
    dsimp [blocks, Δ]
    rw [Matrix.trace_smul]
    simp [MatrixMap.channelDifference_kron_id_apply_trace_eq_zero
      (a := TensorPower a n) (b := b) (r := r) Φ Ψ
      (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω)]
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
            MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
              ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix)) := by
          rfl

/-- Profile-coordinate compression of a state by the normalized symmetric
profile isometry. -/
def ckrProfileCoordinateMatrix
    (ρ : State (TensorPower (Prod a a) n)) :
    CMatrix (ckrPurifyingRegister a n) :=
  (ckrProfileIsometryMatrix a n).conjTranspose * ρ.matrix *
    ckrProfileIsometryMatrix a n

/-- CKR extraction effect.  The transpose matches the convention of
`MatrixMap.traceEffectToUnit`, whose scalar action on a matrix unit is
`X ↦ Tr(XE)`. -/
def ckrProfileCoordinateEffect
    (ρ : State (TensorPower (Prod a a) n)) :
    CMatrix (ckrPurifyingRegister a n) :=
  (ρ.ckrProfileCoordinateMatrix (a := a)).transpose

theorem ckrProfileCoordinateMatrix_posSemidef
    (ρ : State (TensorPower (Prod a a) n)) :
    (ρ.ckrProfileCoordinateMatrix (a := a)).PosSemidef := by
  exact ρ.pos.conjTranspose_mul_mul_same (ckrProfileIsometryMatrix a n)

theorem ckrProfileCoordinateEffect_posSemidef
    (ρ : State (TensorPower (Prod a a) n)) :
    (ρ.ckrProfileCoordinateEffect (a := a)).PosSemidef := by
  exact (ρ.ckrProfileCoordinateMatrix_posSemidef (a := a)).transpose

theorem ckrProfileCoordinateMatrix_le_one [Nonempty a]
    (ρ : State (TensorPower (Prod a a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := Prod a a)) :
    ρ.ckrProfileCoordinateMatrix (a := a) ≤ 1 := by
  dsimp [SupportedOnSymmetricSubspace] at hρ
  rw [Matrix.le_iff] at hρ ⊢
  let U := ckrProfileIsometryMatrix a n
  have hconj : (U.conjTranspose *
      (symmetricProjectionMatrix (a := Prod a a) n - ρ.matrix) * U).PosSemidef :=
    hρ.conjTranspose_mul_mul_same U
  convert hconj using 1
  calc
    1 - ρ.ckrProfileCoordinateMatrix (a := a) =
        (U.conjTranspose * symmetricProjectionMatrix (a := Prod a a) n * U) -
          (U.conjTranspose * ρ.matrix * U) := by
          dsimp [ckrProfileCoordinateMatrix, U]
          rw [← ckrProfileIsometryMatrix_mul_conjTranspose (a := a) n]
          rw [← Matrix.mul_assoc, ckrProfileIsometryMatrix_conjTranspose_mul (a := a) n,
            Matrix.one_mul, Matrix.mul_assoc,
            ckrProfileIsometryMatrix_conjTranspose_mul (a := a) n]
    _ = U.conjTranspose *
        (symmetricProjectionMatrix (a := Prod a a) n - ρ.matrix) * U := by
          rw [Matrix.mul_sub, Matrix.sub_mul]

theorem ckrProfileCoordinateEffect_le_one [Nonempty a]
    (ρ : State (TensorPower (Prod a a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := Prod a a)) :
    ρ.ckrProfileCoordinateEffect (a := a) ≤ 1 := by
  have hC := ρ.ckrProfileCoordinateMatrix_le_one (a := a) hρ
  rw [Matrix.le_iff] at hC
  rw [Matrix.le_iff]
  dsimp [ckrProfileCoordinateEffect]
  convert hC.transpose using 1
  rw [Matrix.transpose_sub, Matrix.transpose_one]

theorem ckrProfileCoordinateEffect_traceNonincreasingCP [Nonempty a]
    (ρ : State (TensorPower (Prod a a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := Prod a a)) :
    MatrixMap.TraceNonincreasingCP
      (MatrixMap.traceEffectToUnit (ρ.ckrProfileCoordinateEffect (a := a))) :=
  MatrixMap.traceEffectToUnit_traceNonincreasingCP
    (ρ.ckrProfileCoordinateEffect_posSemidef (a := a))
    (ρ.ckrProfileCoordinateEffect_le_one (a := a) hρ)

omit [Fintype a] [DecidableEq a] in
private theorem cMatrix_eq_zero_of_posSemidef_and_neg_posSemidef
    {A : CMatrix (TensorPower (Prod a a) n)}
    (hA : A.PosSemidef) (hneg : (-A).PosSemidef) :
    A = 0 := by
  have h0A : (0 : CMatrix (TensorPower (Prod a a) n)) ≤ A := by
    rw [Matrix.le_iff]
    simpa using hA
  have hA0 : A ≤ (0 : CMatrix (TensorPower (Prod a a) n)) := by
    rw [Matrix.le_iff]
    simpa using hneg
  exact le_antisymm hA0 h0A

private theorem symmetricProjection_supported_fixed [Nonempty a]
    (ρ : State (TensorPower (Prod a a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := Prod a a)) :
    symmetricProjectionMatrix (a := Prod a a) n * ρ.matrix *
        symmetricProjectionMatrix (a := Prod a a) n = ρ.matrix := by
  classical
  let P : CMatrix (TensorPower (Prod a a) n) :=
    symmetricProjectionMatrix (a := Prod a a) n
  let Q : CMatrix (TensorPower (Prod a a) n) := 1 - P
  have hPidem : P * P = P := by
    simpa [P] using symmetricProjectionMatrix_idempotent (a := Prod a a) n
  have hPherm : P.IsHermitian := by
    simpa [P] using symmetricProjectionMatrix_isHermitian (a := Prod a a) n
  have hQherm : Q.IsHermitian := by
    dsimp [Q]
    exact symmetricProjectionMatrix_complement_isHermitian (a := Prod a a) n
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
  have hdiff : (P - ρ.matrix).PosSemidef := by
    dsimp [SupportedOnSymmetricSubspace, P] at hρ
    rwa [Matrix.le_iff] at hρ
  have hQrhoQ_pos : (Q * ρ.matrix * Q).PosSemidef := by
    have h := ρ.pos.conjTranspose_mul_mul_same Q
    simpa [hQherm.eq] using h
  have hQdiffQ_pos : (Q * (P - ρ.matrix) * Q).PosSemidef := by
    have h := hdiff.conjTranspose_mul_mul_same Q
    simpa [hQherm.eq] using h
  have hQdiffQ_eq_neg :
      Q * (P - ρ.matrix) * Q = -(Q * ρ.matrix * Q) := by
    have hleft : Q * (P - ρ.matrix) = Q * P - Q * ρ.matrix := by
      rw [Matrix.mul_sub]
    calc
      Q * (P - ρ.matrix) * Q =
          (Q * P - Q * ρ.matrix) * Q := by rw [hleft]
      _ = Q * P * Q - Q * ρ.matrix * Q := by rw [Matrix.sub_mul]
      _ = 0 - Q * ρ.matrix * Q := by rw [hQP, Matrix.zero_mul]
      _ = -(Q * ρ.matrix * Q) := by rw [zero_sub]
  have hQrhoQ_zero : Q * ρ.matrix * Q = 0 :=
    cMatrix_eq_zero_of_posSemidef_and_neg_posSemidef
      hQrhoQ_pos (by simpa [hQdiffQ_eq_neg] using hQdiffQ_pos)
  let S : CMatrix (TensorPower (Prod a a) n) := psdSqrt ρ.matrix
  have hSsq : S * S = ρ.matrix := by
    simpa [S] using psdSqrt_mul_self_of_posSemidef ρ.pos
  have hSherm : S.IsHermitian := by
    simpa [S] using psdSqrt_isHermitian ρ.matrix
  have hSQ_conj_self :
      (S * Q).conjTranspose * (S * Q) = 0 := by
    calc
      (S * Q).conjTranspose * (S * Q) =
          Q * S * (S * Q) := by
          rw [Matrix.conjTranspose_mul, hQherm.eq, hSherm.eq]
      _ = Q * ρ.matrix * Q := by
          calc
            Q * S * (S * Q) = (Q * S * S) * Q := by
              rw [← Matrix.mul_assoc]
            _ = Q * (S * S) * Q := by
              rw [Matrix.mul_assoc Q S S]
            _ = Q * ρ.matrix * Q := by rw [hSsq]
      _ = 0 := hQrhoQ_zero
  have hSQ : S * Q = 0 := by
    have htrace : ((S * Q).conjTranspose * (S * Q)).trace = 0 := by
      rw [hSQ_conj_self, Matrix.trace_zero]
    exact (Matrix.trace_conjTranspose_mul_self_eq_zero_iff).mp htrace
  have hρQ : ρ.matrix * Q = 0 := by
    rw [← hSsq, Matrix.mul_assoc, hSQ, Matrix.mul_zero]
  have hQρ : Q * ρ.matrix = 0 := by
    rw [← Matrix.conjTranspose_eq_zero]
    calc
      (Q * ρ.matrix).conjTranspose =
          ρ.matrix.conjTranspose * Q.conjTranspose := by rw [Matrix.conjTranspose_mul]
      _ = ρ.matrix * Q := by rw [ρ.pos.isHermitian.eq, hQherm.eq]
      _ = 0 := hρQ
  have hPρ : P * ρ.matrix = ρ.matrix := by
    calc
      P * ρ.matrix = (1 - Q) * ρ.matrix := by simp [Q, sub_sub_cancel]
      _ = ρ.matrix - Q * ρ.matrix := by rw [Matrix.sub_mul, Matrix.one_mul]
      _ = ρ.matrix := by rw [hQρ, sub_zero]
  have hρP : ρ.matrix * P = ρ.matrix := by
    calc
      ρ.matrix * P = ρ.matrix * (1 - Q) := by simp [Q, sub_sub_cancel]
      _ = ρ.matrix - ρ.matrix * Q := by rw [Matrix.mul_sub, Matrix.mul_one]
      _ = ρ.matrix := by rw [hρQ, sub_zero]
  calc
    symmetricProjectionMatrix (a := Prod a a) n * ρ.matrix *
        symmetricProjectionMatrix (a := Prod a a) n =
        P * ρ.matrix * P := rfl
    _ = ρ.matrix * P := by rw [hPρ]
    _ = ρ.matrix := hρP

private theorem ckrProfileCoordinate_reconstruct_of_projection_fixed [Nonempty a]
    (ρ : State (TensorPower (Prod a a) n))
    (hfixed :
      symmetricProjectionMatrix (a := Prod a a) n * ρ.matrix *
          symmetricProjectionMatrix (a := Prod a a) n = ρ.matrix) :
    ckrProfileIsometryMatrix a n *
        ρ.ckrProfileCoordinateMatrix (a := a) *
        (ckrProfileIsometryMatrix a n).conjTranspose =
      ρ.matrix := by
  calc
    ckrProfileIsometryMatrix a n *
        ρ.ckrProfileCoordinateMatrix (a := a) *
        (ckrProfileIsometryMatrix a n).conjTranspose =
        ckrProfileIsometryMatrix a n *
          ((ckrProfileIsometryMatrix a n).conjTranspose * ρ.matrix *
            ckrProfileIsometryMatrix a n) *
          (ckrProfileIsometryMatrix a n).conjTranspose := by
          rfl
    _ =
        (ckrProfileIsometryMatrix a n *
            (ckrProfileIsometryMatrix a n).conjTranspose) *
          ρ.matrix *
          (ckrProfileIsometryMatrix a n *
            (ckrProfileIsometryMatrix a n).conjTranspose) := by
          simp [Matrix.mul_assoc]
    _ =
        symmetricProjectionMatrix (a := Prod a a) n * ρ.matrix *
          symmetricProjectionMatrix (a := Prod a a) n := by
          rw [ckrProfileIsometryMatrix_mul_conjTranspose]
    _ = ρ.matrix := hfixed

private theorem inv_sqrt_profile_count_mul_inv_sqrt_profile_count
    [Nonempty a] (n : ℕ) :
    ((Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ)⁻¹) *
        ((Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ)⁻¹) =
      ((Fintype.card (ckrPurifyingRegister a n) : ℂ)⁻¹) := by
  have hpos : 0 < (Fintype.card (ckrPurifyingRegister a n) : ℝ) := by
    exact_mod_cast TensorPowerProfile.card_pos (a := Prod a a) n
  have hsqrt_sq :
      (Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ) *
          (Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ) =
        (Fintype.card (ckrPurifyingRegister a n) : ℂ) := by
    norm_cast
    simp
  rw [← mul_inv_rev, hsqrt_sq]

private theorem dropRightUnitMatrix_ckrExtraction_eq_profile_reconstruction [Nonempty a]
    (ρ : State (TensorPower (Prod a a) n)) :
    dropRightUnitMatrix
        ((MatrixMap.kron
            (Channel.idChannel (TensorPower (Prod a a) n)).map
            (MatrixMap.traceEffectToUnit (ρ.ckrProfileCoordinateEffect (a := a)))
          (ckrPurifiedReferenceState (a := a) n).matrix)) =
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
            (Channel.idChannel (TensorPower (Prod a a) n)).map
            (MatrixMap.traceEffectToUnit E)
          (ckrPurifiedReferenceState (a := a) n).matrix)) x y =
        ∑ p : ckrPurifyingRegister a n,
          ∑ q : ckrPurifyingRegister a n,
            (c * U x p * star (c * U y q)) * E q p := by
          rw [dropRightUnitMatrix_kron_id_traceEffectToUnit_apply hEpos]
          refine Finset.sum_congr rfl fun p _ => ?_
          refine Finset.sum_congr rfl fun q _ => ?_
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
    {n : ℕ} (ρ : State (TensorPower (Prod a a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := Prod a a)) :
    ∃ T : MatrixMap (ckrPurifyingRegister a n) PUnit,
      T.TraceNonincreasingCP ∧
        ρ.matrix =
          ((Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) : ℂ) •
            dropRightUnitMatrix
              ((MatrixMap.kron
                  (Channel.idChannel (TensorPower (Prod a a) n)).map T)
                (ckrPurifiedReferenceState (a := a) n).matrix) := by
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
                (Channel.idChannel (TensorPower (Prod a a) n)).map T)
              (ckrPurifiedReferenceState (a := a) n).matrix) =
          (((Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ)⁻¹ : ℂ) •
            ρ.matrix) := by
      simpa [T, ckrPurifyingRegister, hrec] using hdrop
    rw [hdropρ]
    symm
    have hcard_ne :
        (Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ) ≠ 0 := by
      exact_mod_cast TensorPowerProfile.card_ne_zero (a := Prod a a) n
    calc
      (Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ) •
          ((Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ)⁻¹ •
            ρ.matrix) =
          ((Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ) *
              (Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ)⁻¹) •
            ρ.matrix := by
            rw [smul_smul]
      _ = ρ.matrix := by rw [mul_inv_cancel₀ hcard_ne, one_smul]

/-- CKR `extractpart` with the binomial symmetric-dimension factor. -/
theorem ckr_extractpart_choose [Nonempty a]
    {n : ℕ} (ρ : State (TensorPower (Prod a a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := Prod a a)) :
    ∃ T : MatrixMap (ckrPurifyingRegister a n) PUnit,
      T.TraceNonincreasingCP ∧
        ρ.matrix =
          ((Nat.choose (n + Fintype.card (Prod a a) - 1) n : ℝ) : ℂ) •
            dropRightUnitMatrix
              ((MatrixMap.kron
                  (Channel.idChannel (TensorPower (Prod a a) n)).map T)
                (ckrPurifiedReferenceState (a := a) n).matrix) := by
  classical
  obtain ⟨T, hT, hEq⟩ :=
    ρ.ckr_extractpart_profile_count (a := a) hρ
  refine ⟨T, hT, ?_⟩
  simpa [tensorPowerProfile_card_eq_choose (a := Prod a a) n] using hEq

/-- Concrete `traceEffectToUnit` form of CKR `extractpart`.

This is the witness used in `ckr_extractpart_profile_count`, exposed so the
post-selection assembly can commute a channel-difference action past the
explicit extraction map. -/
theorem ckr_extractpart_profile_count_traceEffect [Nonempty a]
    {n : ℕ} (ρ : State (TensorPower (Prod a a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := Prod a a)) :
    ρ.matrix =
      ((Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) : ℂ) •
        dropRightUnitMatrix
          ((MatrixMap.kron
              (Channel.idChannel (TensorPower (Prod a a) n)).map
              (MatrixMap.traceEffectToUnit (ρ.ckrProfileCoordinateEffect (a := a))))
            (ckrPurifiedReferenceState (a := a) n).matrix) := by
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
              (Channel.idChannel (TensorPower (Prod a a) n)).map T)
            (ckrPurifiedReferenceState (a := a) n).matrix) =
        (((Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ)⁻¹ : ℂ) •
          ρ.matrix) := by
    simpa [T, ckrPurifyingRegister, hrec] using hdrop
  rw [hdropρ]
  symm
  have hcard_ne :
      (Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ) ≠ 0 := by
    exact_mod_cast TensorPowerProfile.card_ne_zero (a := Prod a a) n
  calc
    (Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ) •
        ((Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ)⁻¹ •
          ρ.matrix) =
        ((Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ) *
            (Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ)⁻¹) •
          ρ.matrix := by
          rw [smul_smul]
    _ = ρ.matrix := by rw [mul_inv_cancel₀ hcard_ne, one_smul]

end State

namespace MatrixMap

theorem ancillaNormalizedTraceAction_le_spectralPure_sum
    {a : Type v} {b : Type w} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (Δ : MatrixMap a b) (ω : State (Prod a a)) :
    Δ.ancillaNormalizedTraceAction ω ≤
      ∑ i : Prod a a,
        ω.pos.isHermitian.eigenvalues i *
          Δ.ancillaNormalizedTraceAction (ω.spectralPureVector i).state := by
  dsimp [ancillaNormalizedTraceAction, normalizedTraceAction]
  have hmatrix := ω.matrix_eq_sum_spectralPureVector
  have hmap : MatrixMap.kron Δ (Channel.idChannel a).map ω.matrix =
      ∑ i : Prod a a,
        ((ω.pos.isHermitian.eigenvalues i : ℝ) : ℂ) •
          MatrixMap.kron Δ (Channel.idChannel a).map
            (ω.spectralPureVector i).state.matrix := by
    conv_lhs => rw [hmatrix]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
  rw [hmap]
  have hsum := traceNorm_sum_le_sum_traceNorm
    (Finset.univ : Finset (Prod a a))
    (fun i => ((ω.pos.isHermitian.eigenvalues i : ℝ) : ℂ) •
      MatrixMap.kron Δ (Channel.idChannel a).map (ω.spectralPureVector i).state.matrix)
  have hterms :
      (∑ i : Prod a a,
        traceNorm (((ω.pos.isHermitian.eigenvalues i : ℝ) : ℂ) •
          MatrixMap.kron Δ (Channel.idChannel a).map
            (ω.spectralPureVector i).state.matrix)) ≤
        ∑ i : Prod a a,
          ω.pos.isHermitian.eigenvalues i *
            traceNorm (MatrixMap.kron Δ (Channel.idChannel a).map
              (ω.spectralPureVector i).state.matrix) := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact traceNorm_real_smul_le (ω.pos.eigenvalues_nonneg i) _
  calc
    (1 / 2 : ℝ) * traceNorm
        (∑ i : Prod a a,
          ((ω.pos.isHermitian.eigenvalues i : ℝ) : ℂ) •
            MatrixMap.kron Δ (Channel.idChannel a).map
              (ω.spectralPureVector i).state.matrix)
        ≤ (1 / 2 : ℝ) *
          (∑ i : Prod a a,
            traceNorm (((ω.pos.isHermitian.eigenvalues i : ℝ) : ℂ) •
              MatrixMap.kron Δ (Channel.idChannel a).map
                (ω.spectralPureVector i).state.matrix)) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
          (∑ i : Prod a a,
            ω.pos.isHermitian.eigenvalues i *
              traceNorm (MatrixMap.kron Δ (Channel.idChannel a).map
                (ω.spectralPureVector i).state.matrix)) :=
          mul_le_mul_of_nonneg_left hterms (by norm_num)
    _ = ∑ i : Prod a a,
          ω.pos.isHermitian.eigenvalues i *
            ((1 / 2 : ℝ) * traceNorm (MatrixMap.kron Δ (Channel.idChannel a).map
              (ω.spectralPureVector i).state.matrix)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring

/-- Convexity bridge for the source-shaped diamond distance: it suffices to
bound the finite-reference action on pure input-reference states. -/
theorem ancillaNormalizedTraceAction_le_of_forall_pure_bound
    {a : Type v} {b : Type w} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (Δ : MatrixMap a b) (ω : State (Prod a a)) {B : ℝ}
    (h : ∀ Ω : PureVector (Prod a a), Δ.ancillaNormalizedTraceAction Ω.state ≤ B) :
    Δ.ancillaNormalizedTraceAction ω ≤ B := by
  calc
    Δ.ancillaNormalizedTraceAction ω ≤
        ∑ i : Prod a a,
          ω.pos.isHermitian.eigenvalues i *
            Δ.ancillaNormalizedTraceAction (ω.spectralPureVector i).state :=
          Δ.ancillaNormalizedTraceAction_le_spectralPure_sum ω
    _ ≤ ∑ i : Prod a a, ω.pos.isHermitian.eigenvalues i * B := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_left (h (ω.spectralPureVector i))
            (ω.pos.eigenvalues_nonneg i)
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
  ∀ π : Equiv.Perm (Fin n), ∃ Kπ : Channel b b,
    ∀ X : CMatrix (QIT.TensorPower a n),
      Δ ((permutationChannel (a := a) n π).map X) = Kπ.map (Δ X)

/-- Tensoring a post-selection covariant map with an identity reference keeps
the covariance equation at the finite-ancilla level. -/
theorem postSelectionCovariant_kron_permutation_eq
    {r : Type x} [Fintype r] [DecidableEq r]
    (Δ : MatrixMap (QIT.TensorPower a n) b)
    (hcov : Δ.PostSelectionCovariant (a := a) (n := n))
    (π : Equiv.Perm (Fin n)) (X : CMatrix (Prod (QIT.TensorPower a n) r)) :
    ∃ Kπ : Channel b b,
      MatrixMap.kron Δ (Channel.idChannel r).map
          (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).map X) =
        (Kπ.prod (Channel.idChannel r)).map
          (MatrixMap.kron Δ (Channel.idChannel r).map X) := by
  obtain ⟨Kπ, hKπ⟩ := hcov π
  refine ⟨Kπ, ?_⟩
  change MatrixMap.kron Δ (Channel.idChannel r).map
      (MatrixMap.kron (permutationChannel (a := a) n π).map
        (Channel.idChannel r).map X) =
    MatrixMap.kron Kπ.map (Channel.idChannel r).map
      (MatrixMap.kron Δ (Channel.idChannel r).map X)
  ext br br'
  rw [MatrixMap.kron_idChannel_apply_slice]
  rw [MatrixMap.kron_idChannel_apply_slice]
  have hslice_perm :
      (fun i i' =>
          MatrixMap.kron (permutationChannel (a := a) n π).map
            (Channel.idChannel r).map X (i, br.2) (i', br'.2)) =
        (permutationChannel (a := a) n π).map
          (fun i i' => X (i, br.2) (i', br'.2)) := by
    ext i i'
    rw [MatrixMap.kron_idChannel_apply_slice]
  have hslice_delta :
      (fun i i' =>
          MatrixMap.kron Δ (Channel.idChannel r).map X (i, br.2) (i', br'.2)) =
        Δ (fun i i' => X (i, br.2) (i', br'.2)) := by
    ext i i'
    rw [MatrixMap.kron_idChannel_apply_slice]
  rw [hslice_perm, hKπ, hslice_delta]

end MatrixMap

namespace Channel

variable {n : ℕ}
variable {b : Type w} [Fintype b] [DecidableEq b]

/-- CKR post-selection covariance for the difference of two channels. -/
def PostSelectionCovariantDifference (Φ Ψ : Channel (QIT.TensorPower a n) b) : Prop :=
  MatrixMap.PostSelectionCovariant (a := a) (n := n) (b := b)
    (MatrixMap.channelDifference (a := QIT.TensorPower a n) (b := b) Φ Ψ)

/-- Under CKR post-selection covariance, applying a tensor-factor permutation
to the input-reference state cannot increase the channel-difference normalized
trace action. -/
theorem postSelectionCovariantDifference_ancillaAction_permutation_le
    {r : Type x} [Fintype r] [DecidableEq r]
    (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ)
    (π : Equiv.Perm (Fin n)) (ω : State (Prod (QIT.TensorPower a n) r)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω) ≤
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω := by
  obtain ⟨Kπ, hEq⟩ :=
    MatrixMap.postSelectionCovariant_kron_permutation_eq (a := a) (b := b) (r := r)
      (MatrixMap.channelDifference Φ Ψ) hcov π ω.matrix
  dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction]
  rw [Channel.applyState, hEq]
  have hH := MatrixMap.channelDifference_kron_id_apply_isHermitian
    (a := QIT.TensorPower a n) (b := b) (r := r) Φ Ψ ω
  have htr := MatrixMap.channelDifference_kron_id_apply_trace_eq_zero
    (a := QIT.TensorPower a n) (b := b) (r := r) Φ Ψ ω
  have hle := MatrixMap.traceNorm_apply_le_of_traceNonincreasingCP
    (Channel.traceNonincreasingCP_kron_id (r := r) Kπ) hH htr
  exact mul_le_mul_of_nonneg_left (by simpa [Channel.prod] using hle) (by norm_num)

/-- Applying a tensor-factor permutation and then its inverse on the input
register leaves an input-reference state unchanged. -/
private theorem inputPermutation_inv_apply_permutation
    {r : Type x} [Fintype r] [DecidableEq r]
    (π : Equiv.Perm (Fin n)) (ω : State (Prod (QIT.TensorPower a n) r)) :
    ((permutationChannel (a := a) n π⁻¹).prod (Channel.idChannel r)).applyState
        (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω) =
      ω := by
  apply State.ext
  ext x y
  simp only [Channel.applyState]
  rw [permutationChannel_prod_id_map_apply]
  rw [permutationChannel_prod_id_map_apply]
  cases x with
  | mk xA xr =>
  cases y with
  | mk yA yr =>
    change ω.matrix (π • (π⁻¹ • xA), xr) (π • (π⁻¹ • yA), yr) =
      ω.matrix (xA, xr) (yA, yr)
    rw [← mul_smul, ← mul_smul]
    simp

/-- Under CKR post-selection covariance, applying a tensor-factor permutation
to the input-reference state preserves the channel-difference normalized trace
action.  One inequality is contraction through the covariance map; the reverse
uses the inverse permutation. -/
theorem postSelectionCovariantDifference_ancillaAction_permutation_eq
    {r : Type x} [Fintype r] [DecidableEq r]
    (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ)
    (π : Equiv.Perm (Fin n)) (ω : State (Prod (QIT.TensorPower a n) r)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω) =
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω := by
  apply le_antisymm
  · exact postSelectionCovariantDifference_ancillaAction_permutation_le
      (a := a) (b := b) (r := r) Φ Ψ hcov π ω
  · have hle := postSelectionCovariantDifference_ancillaAction_permutation_le
      (a := a) (b := b) (r := r) Φ Ψ hcov π⁻¹
      (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω)
    simpa [inputPermutation_inv_apply_permutation (a := a) (r := r) π ω] using hle

private theorem postSelectionCovariantDifference_labelExtension_action_eq
    {r : Type x} [Fintype r] [DecidableEq r]
    (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ)
    (ω : State (Prod (QIT.TensorPower a n) r)) :
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
  rw [State.inputPermutationLabelExtension_channelDifference_action_traceNorm_eq_sum
    (a := a) (r := r) (b := b) Φ Ψ ω]
  have hterms :
      (∑ π : Equiv.Perm (Fin n),
        traceNorm
          ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ •
            MatrixMap.kron Δ (Channel.idChannel r).map
              ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))) =
        ∑ π : Equiv.Perm (Fin n),
          c * traceNorm
            (MatrixMap.kron Δ (Channel.idChannel r).map
              ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix)) := by
    refine Finset.sum_congr rfl fun π _ => ?_
    simpa [c] using traceNorm_real_smul_eq
      (a := Prod b r) (c := c) hc
      (MatrixMap.kron Δ (Channel.idChannel r).map
        ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))
  change (1 / 2 : ℝ) *
      (∑ π : Equiv.Perm (Fin n),
        traceNorm
          ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ •
            MatrixMap.kron Δ (Channel.idChannel r).map
              ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))) =
    (1 / 2 : ℝ) * traceNorm
      (MatrixMap.kron Δ (Channel.idChannel r).map ω.matrix)
  rw [hterms]
  have hpermTrace :
      ∀ π : Equiv.Perm (Fin n),
        traceNorm
          (MatrixMap.kron Δ (Channel.idChannel r).map
            ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix)) =
        traceNorm
          (MatrixMap.kron Δ (Channel.idChannel r).map ω.matrix) := by
    intro π
    have h := postSelectionCovariantDifference_ancillaAction_permutation_eq
      (a := a) (b := b) (r := r) Φ Ψ hcov π ω
    dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction, Δ] at h
    nlinarith
  calc
    (1 / 2 : ℝ) *
        (∑ π : Equiv.Perm (Fin n),
          c * traceNorm
            (MatrixMap.kron Δ (Channel.idChannel r).map
              ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix)) ) =
        (1 / 2 : ℝ) *
          (∑ π : Equiv.Perm (Fin n),
            c * traceNorm
              (MatrixMap.kron Δ (Channel.idChannel r).map ω.matrix)) := by
          congr 1
          refine Finset.sum_congr rfl fun π _ => ?_
          rw [hpermTrace π]
    _ = (1 / 2 : ℝ) * traceNorm
          (MatrixMap.kron Δ (Channel.idChannel r).map ω.matrix) := by
          simp [c, Finset.sum_const, nsmul_eq_mul, hcard_ne]

/-- A mixed input-reference state is controlled by the canonical pure extension
obtained by purifying the whole input-reference system.  The proof is the
finite-dimensional data-processing step: the mixed action is the partial trace
of the pure-extension action, and partial trace contracts trace norm. -/
private theorem inputReferenceAction_le_canonicalExtension
    {r : Type x} [Fintype r] [DecidableEq r]
    (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (ω : State (Prod (QIT.TensorPower a n) r)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω ≤
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (ω.inputReferenceCanonicalExtension (a := a) (r := r)).state := by
  classical
  let Δ : MatrixMap (QIT.TensorPower a n) b := MatrixMap.channelDifference Φ Ψ
  let E := Prod (QIT.TensorPower a n) r
  let Y : CMatrix (Prod E (Prod b r)) :=
    MatrixMap.kron (Channel.idChannel E).map
      (MatrixMap.kron Δ (Channel.idChannel r).map)
      ω.canonicalPurification.state.matrix
  let Z : CMatrix (Prod b (Prod r E)) :=
    MatrixMap.kron Δ (Channel.idChannel (Prod r E)).map
      (ω.inputReferenceCanonicalExtension (a := a) (r := r)).state.matrix
  have hpt :
      partialTraceA (a := E) (b := Prod b r) Y =
        MatrixMap.kron Δ (Channel.idChannel r).map ω.matrix := by
    calc
      partialTraceA (a := E) (b := Prod b r) Y =
          MatrixMap.kron Δ (Channel.idChannel r).map
            (partialTraceA (a := E) (b := E)
              ω.canonicalPurification.state.matrix) := by
            simpa [Y, E] using
              MatrixMap.partialTraceA_kron_idChannel_left
                (a := E) (c := E) (d := Prod b r)
                (MatrixMap.kron Δ (Channel.idChannel r).map)
                ω.canonicalPurification.state.matrix
      _ = MatrixMap.kron Δ (Channel.idChannel r).map ω.matrix := by
            have hp : partialTraceA (a := E) (b := E)
                ω.canonicalPurification.state.matrix = ω.matrix := by
              exact PureVector.partialTraceA_state_matrix_eq_of_purifies
                ω.canonicalPurification_purifies
            rw [hp]
  have hreindex :
      Z =
        Y.submatrix
          (State.extensionPurificationOutputEquiv (a := a) (r := r) (b := b) (n := n)).symm
          (State.extensionPurificationOutputEquiv (a := a) (r := r) (b := b) (n := n)).symm := by
    ext x y
    simp [Z, Y, State.inputReferenceCanonicalExtension,
      State.extensionPurificationInputEquiv, State.extensionPurificationOutputEquiv,
      PureVector.reindex_state, State.reindex,
      MatrixMap.kron_idChannel_apply_slice, MatrixMap.kron_idChannel_left_apply_slice]
  have htraceY : traceNorm Y = traceNorm Z := by
    rw [hreindex]
    symm
    exact traceNorm_submatrix_equiv
      (State.extensionPurificationOutputEquiv (a := a) (r := r) (b := b) (n := n)).symm
      Y
  dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction]
  change (1 / 2 : ℝ) * traceNorm
      (MatrixMap.kron Δ (Channel.idChannel r).map ω.matrix) ≤
    (1 / 2 : ℝ) * traceNorm Z
  rw [← hpt]
  calc
    (1 / 2 : ℝ) * traceNorm (partialTraceA (a := E) (b := Prod b r) Y)
        ≤ (1 / 2 : ℝ) * traceNorm Y :=
          mul_le_mul_of_nonneg_left
            (traceNorm_partialTraceA_le_matrix (a := E) (b := Prod b r) Y)
            (by norm_num)
    _ = (1 / 2 : ℝ) * traceNorm Z := by rw [htraceY]

/-- The input marginal of the canonical pure extension of an input-reference
state is the original input marginal. -/
private theorem inputReferenceCanonicalExtension_marginalA
    {r : Type x} [Fintype r] [DecidableEq r]
    (ω : State (Prod (QIT.TensorPower a n) r)) :
    (ω.inputReferenceCanonicalExtension (a := a) (r := r)).state.marginalA =
      ω.marginalA := by
  apply State.ext
  ext i j
  have hp : partialTraceA (a := Prod (QIT.TensorPower a n) r)
      (b := Prod (QIT.TensorPower a n) r)
      ω.canonicalPurification.state.matrix = ω.matrix := by
    exact PureVector.partialTraceA_state_matrix_eq_of_purifies
      ω.canonicalPurification_purifies
  simp only [State.inputReferenceCanonicalExtension, State.marginalA, partialTraceB,
    PureVector.reindex_state, State.reindex, PureVector.state_matrix]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun xr _ => ?_
  have hpij := congrFun (congrFun hp (i, xr)) (j, xr)
  simpa [partialTraceA, State.extensionPurificationInputEquiv] using hpij

/-- Swapping the canonical purification puts the purified system in the input
position, whose marginal is the original state. -/
private theorem canonicalPurification_reindex_prodComm_marginalA
    {α : Type v} [Fintype α] [DecidableEq α] (ρ : State α) :
    (ρ.canonicalPurification.reindex (Equiv.prodComm α α)).state.marginalA = ρ := by
  apply State.ext
  ext i j
  have hp : partialTraceA (a := α) (b := α)
      ρ.canonicalPurification.state.matrix = ρ.matrix := by
    exact PureVector.partialTraceA_state_matrix_eq_of_purifies
      ρ.canonicalPurification_purifies
  have hpij := congrFun (congrFun hp i) j
  simpa [State.marginalA, partialTraceB, partialTraceA,
    PureVector.reindex_state, State.reindex] using hpij

/-- Averaging an input-reference state over input tensor-factor permutations
does not increase the post-selection covariant channel-difference action. -/
theorem postSelectionCovariantDifference_ancillaAction_inputPermutationTwirling_le
    {r : Type x} [Fintype r] [DecidableEq r]
    (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ)
    (ω : State (Prod (QIT.TensorPower a n) r)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (ω.inputPermutationTwirling (a := a) (r := r)) ≤
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω := by
  classical
  let c : ℝ := (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr (Nat.cast_nonneg _)
  dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction]
  change (1 / 2 : ℝ) * traceNorm
      (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
        (((c : ℂ) • ∑ π : Equiv.Perm (Fin n),
          (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))) ≤
    (1 / 2 : ℝ) * traceNorm
      (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map ω.matrix)
  rw [map_smul, map_sum]
  have hsmul : traceNorm (((c : ℂ) • ∑ π : Equiv.Perm (Fin n),
      MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
        ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))) ≤
      c * traceNorm (∑ π : Equiv.Perm (Fin n),
      MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
        ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix)) :=
    traceNorm_real_smul_le hc _
  have hsum := traceNorm_sum_le_sum_traceNorm (Finset.univ : Finset (Equiv.Perm (Fin n)))
    (fun π => MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
      ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))
  have hterms : (∑ π : Equiv.Perm (Fin n), traceNorm
      (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
        ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix)) ≤
      ∑ π : Equiv.Perm (Fin n), traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map ω.matrix)) := by
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
        MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
          ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))
        ≤ (1 / 2 : ℝ) * (c * traceNorm (∑ π : Equiv.Perm (Fin n),
        MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
          ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))) :=
          mul_le_mul_of_nonneg_left hsmul (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (c * (∑ π : Equiv.Perm (Fin n), traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
          ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix)))) := by
          gcongr
    _ ≤ (1 / 2 : ℝ) * (c * (∑ π : Equiv.Perm (Fin n), traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map ω.matrix))) := by
          gcongr
    _ = (1 / 2 : ℝ) * traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map ω.matrix) := by
          simp [c, Finset.sum_const, nsmul_eq_mul, hcard_ne]

/-- Supported symmetric input-reference states are controlled by the CKR
purified post-selection reference action, with the exact profile-count factor.

This is the extractpart-to-action bridge: it applies the concrete
trace-effect extraction map from CKR `extractpart`, commutes the
channel-difference action past that extraction, and then uses
trace-nonincreasing CP contraction. -/
private theorem postSelection_supportedInputReferenceAction_le_profile_count_purified
    [Nonempty a] (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (ρ : State (QIT.TensorPower (Prod a a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := Prod a a)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (ρ.reindex (tensorPowerProdEquiv a a n)) ≤
      (Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (ckrPostSelectionPurifiedReferenceState (a := a) n) := by
  classical
  let Δ : MatrixMap (QIT.TensorPower a n) b := MatrixMap.channelDifference Φ Ψ
  let gR : ℝ := Fintype.card (TensorPowerProfile (Prod a a) n)
  let E : CMatrix (ckrPurifyingRegister a n) :=
    ρ.ckrProfileCoordinateEffect (a := a)
  let T : MatrixMap (ckrPurifyingRegister a n) PUnit.{1} :=
    MatrixMap.traceEffectToUnit E
  let H0 : CMatrix (Prod b (Prod (QIT.TensorPower a n) (ckrPurifyingRegister a n))) :=
    (MatrixMap.kron Δ
      (Channel.idChannel (Prod (QIT.TensorPower a n) (ckrPurifyingRegister a n))).map)
      (ckrPostSelectionPurifiedReferenceState (a := a) n).matrix
  let H : CMatrix (Prod (Prod b (QIT.TensorPower a n)) (ckrPurifyingRegister a n)) :=
    assocRightMatrix H0
  have hEpos : E.PosSemidef := by
    simpa [E] using ρ.ckrProfileCoordinateEffect_posSemidef (a := a)
  have hT : T.TraceNonincreasingCP := by
    simpa [T, E] using
      ρ.ckrProfileCoordinateEffect_traceNonincreasingCP (a := a) hρ
  have hExtract := ρ.ckr_extractpart_profile_count_traceEffect (a := a) hρ
  have hActionEq :
      MatrixMap.kron Δ (Channel.idChannel (QIT.TensorPower a n)).map
          (ρ.reindex (tensorPowerProdEquiv a a n)).matrix =
        (gR : ℂ) •
          dropRightUnitMatrix
            ((MatrixMap.kron (Channel.idChannel (Prod b (QIT.TensorPower a n))).map T) H) := by
    have hReindex :
        (ρ.reindex (tensorPowerProdEquiv a a n)).matrix =
          (gR : ℂ) •
            (dropRightUnitMatrix
              ((MatrixMap.kron
                  (Channel.idChannel (QIT.TensorPower (Prod a a) n)).map T)
                (ckrPurifiedReferenceState (a := a) n).matrix)).submatrix
              (tensorPowerProdEquiv a a n).symm
              (tensorPowerProdEquiv a a n).symm := by
      rw [State.reindex_matrix, hExtract]
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
        (r := Prod (QIT.TensorPower a n) (ckrPurifyingRegister a n))
        Φ Ψ (ckrPostSelectionPurifiedReferenceState (a := a) n)
  have hH0tr : H0.trace = 0 := by
    simpa [H0, Δ] using
      MatrixMap.channelDifference_kron_id_apply_trace_eq_zero
        (a := QIT.TensorPower a n) (b := b)
        (r := Prod (QIT.TensorPower a n) (ckrPurifyingRegister a n))
        Φ Ψ (ckrPostSelectionPurifiedReferenceState (a := a) n)
  have hHHerm : H.IsHermitian := by
    simpa [H] using assocRightMatrix_isHermitian hH0Herm
  have hHtr : H.trace = 0 := by
    simpa [H, hH0tr] using trace_assocRightMatrix H0
  have hContract :
      traceNorm
          (dropRightUnitMatrix
            ((MatrixMap.kron (Channel.idChannel (Prod b (QIT.TensorPower a n))).map T) H)) ≤
        traceNorm H :=
    traceNorm_dropRightUnitMatrix_kron_id_le_of_traceNonincreasingCP
      (α := Prod b (QIT.TensorPower a n)) (β := ckrPurifyingRegister a n)
      hT hHHerm hHtr
  have hg_nonneg : 0 ≤ gR := by
    dsimp [gR]
    exact Nat.cast_nonneg _
  dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction]
  change (1 / 2 : ℝ) *
      traceNorm
        (MatrixMap.kron Δ (Channel.idChannel (QIT.TensorPower a n)).map
          (ρ.reindex (tensorPowerProdEquiv a a n)).matrix) ≤
    gR * ((1 / 2 : ℝ) * traceNorm H0)
  rw [hActionEq]
  calc
    (1 / 2 : ℝ) *
        traceNorm ((gR : ℂ) •
          dropRightUnitMatrix
            ((MatrixMap.kron (Channel.idChannel (Prod b (QIT.TensorPower a n))).map T) H))
        ≤ (1 / 2 : ℝ) *
            (gR * traceNorm
              (dropRightUnitMatrix
                ((MatrixMap.kron (Channel.idChannel (Prod b (QIT.TensorPower a n))).map T) H))) :=
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
theorem postSelection_pureInputReferenceAction_le_profile_count_of_marginalA_invariant
    [Nonempty a] (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (Ω : PureVector (Prod (QIT.TensorPower a n) (QIT.TensorPower a n)))
    (hInv : Ω.state.marginalA.IsPermutationInvariant (a := a)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction Ω.state ≤
      (Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (ckrPostSelectionPurifiedReferenceState (a := a) n) := by
  have hcanon :=
    Ω.channelDifference_normalizedAction_le_canonicalOfMarginalA Φ Ψ
  have hsup :=
    postSelection_supportedInputReferenceAction_le_profile_count_purified
      (a := a) (n := n) (b := b) Φ Ψ
      Ω.state.marginalA.inputCanonicalTensorPowerPurificationState
      (State.inputCanonicalTensorPowerPurification_supported_of_invariant
        (a := a) hInv)
  calc
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction Ω.state ≤
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (Ω.state.marginalA.canonicalPurification.state.reindex
            (Equiv.prodComm (QIT.TensorPower a n) (QIT.TensorPower a n))) :=
          hcanon
    _ ≤ (Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (ckrPostSelectionPurifiedReferenceState (a := a) n) := by
          simpa [State.inputCanonicalTensorPowerPurificationState_reindex_tensorPowerProdEquiv]
            using hsup

private theorem inputReferenceAction_le_profile_count_of_invariantMarginal
    [Nonempty a] {r : Type x} [Fintype r] [DecidableEq r] [Nonempty r]
    (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (ω : State (Prod (QIT.TensorPower a n) r))
    (hInv : ω.marginalA.IsPermutationInvariant (a := a)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω ≤
      (Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (ckrPostSelectionPurifiedReferenceState (a := a) n) := by
  classical
  let Ω : PureVector
      (Prod (QIT.TensorPower a n)
        (Prod r (Prod (QIT.TensorPower a n) r))) :=
    ω.inputReferenceCanonicalExtension (a := a) (r := r)
  have hExt :=
    inputReferenceAction_le_canonicalExtension (a := a) (n := n) (b := b)
      (r := r) Φ Ψ ω
  have hcard :
      Fintype.card (QIT.TensorPower a n) ≤
        Fintype.card (Prod r (Prod (QIT.TensorPower a n) r)) := by
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
          (ω.marginalA.canonicalPurification.reindex
            (Equiv.prodComm (QIT.TensorPower a n) (QIT.TensorPower a n))).state := by
    simpa [Ω, inputReferenceCanonicalExtension_marginalA (a := a) (n := n) (r := r) ω]
      using hCan
  have hPureInv :
      State.IsPermutationInvariant
        (((ω.marginalA.canonicalPurification.reindex
          (Equiv.prodComm (QIT.TensorPower a n) (QIT.TensorPower a n))).state).marginalA)
        (a := a) := by
    rw [canonicalPurification_reindex_prodComm_marginalA]
    exact hInv
  have hPure :=
    postSelection_pureInputReferenceAction_le_profile_count_of_marginalA_invariant
      (a := a) (n := n) (b := b) Φ Ψ
      (ω.marginalA.canonicalPurification.reindex
        (Equiv.prodComm (QIT.TensorPower a n) (QIT.TensorPower a n))) hPureInv
  exact hExt.trans (hCan'.trans hPure)

private theorem postSelection_labelExtensionAction_le_profile_count
    [Nonempty a] {r : Type x} [Fintype r] [DecidableEq r] [Nonempty r]
    (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ)
    (ω : State (Prod (QIT.TensorPower a n) r)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω ≤
      (Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (ckrPostSelectionPurifiedReferenceState (a := a) n) := by
  have hlabel :=
    postSelectionCovariantDifference_labelExtension_action_eq
      (a := a) (n := n) (b := b) (r := r) Φ Ψ hcov ω
  have hbound :=
    inputReferenceAction_le_profile_count_of_invariantMarginal
      (a := a) (n := n) (b := b)
      (r := Prod r (Equiv.Perm (Fin n))) Φ Ψ
      (ω.inputPermutationLabelExtension (a := a) (r := r))
      (State.inputPermutationLabelExtension_marginalA_isPermutationInvariant
        (a := a) (r := r) ω)
  exact hlabel ▸ hbound

/-- CKR mixed input-reference reduction: under post-selection covariance, every
input-reference state is bounded by the purified post-selection reference
action with the exact profile-count factor. -/
theorem postSelection_inputReferenceAction_le_profile_count
    [Nonempty a] (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ)
    (ω : State (Prod (QIT.TensorPower a n) (QIT.TensorPower a n))) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω ≤
      (Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (ckrPostSelectionPurifiedReferenceState (a := a) n) := by
  classical
  letI : Nonempty (QIT.TensorPower a n) := QIT.TensorPower.nonempty (a := a) n
  exact postSelection_labelExtensionAction_le_profile_count
    (a := a) (n := n) (b := b)
    (r := QIT.TensorPower a n) Φ Ψ hcov ω

/-- CKR finite-dimensional post-selection theorem in source-shaped diamond
trace-distance form, with the exact profile-count factor. -/
theorem postSelection_diamondTraceDistance_le_profile_count
    [Nonempty a] (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ) :
    Φ.diamondTraceDistance Ψ ≤
      (Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (ckrPostSelectionPurifiedReferenceState (a := a) n) := by
  classical
  refine Channel.diamondTraceDistance_le_of_inputReferenceBound
    (a := QIT.TensorPower a n) (b := b) (Φ := Φ) (Ψ := Ψ)
    (ε := (Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) *
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (ckrPostSelectionPurifiedReferenceState (a := a) n)) ?_
  intro ω
  rw [Channel.ancillaChannelTraceDistance_eq_channelDifferenceAction]
  exact postSelection_inputReferenceAction_le_profile_count
    (a := a) (n := n) (b := b) Φ Ψ hcov ω

/-- CKR post-selection theorem with the equivalent binomial symmetric-dimension
factor. -/
theorem postSelection_diamondTraceDistance_le_choose
    [Nonempty a] (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ) :
    Φ.diamondTraceDistance Ψ ≤
      (Nat.choose (n + Fintype.card (Prod a a) - 1) n : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (ckrPostSelectionPurifiedReferenceState (a := a) n) := by
  simpa [tensorPowerProfile_card_eq_choose (a := Prod a a) n] using
    postSelection_diamondTraceDistance_le_profile_count
      (a := a) (n := n) (b := b) Φ Ψ hcov

/-- To bound the source-shaped finite-dimensional diamond trace distance it is
enough to bound the channel-difference action on pure input-reference states.
This packages the spectral decomposition and convexity bridge for later CKR
post-selection assembly. -/
theorem diamondTraceDistance_le_of_pureInputReferenceBound [Nonempty a]
    {Φ Ψ : Channel a b} {ε : ℝ}
    (h : ∀ Ω : PureVector (Prod a a),
      MatrixMap.ancillaNormalizedTraceAction (MatrixMap.channelDifference Φ Ψ) Ω.state ≤ ε) :
    Φ.diamondTraceDistance Ψ ≤ ε := by
  refine Channel.diamondTraceDistance_le_of_inputReferenceBound (a := a) (b := b)
    (Φ := Φ) (Ψ := Ψ) (ε := ε) ?_
  intro ω
  rw [Channel.ancillaChannelTraceDistance_eq_channelDifferenceAction]
  exact MatrixMap.ancillaNormalizedTraceAction_le_of_forall_pure_bound
    (MatrixMap.channelDifference Φ Ψ) ω h

end Channel

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

namespace State

variable {n : ℕ}

/-- Project a tensor-power state onto the symmetric subspace on both sides:
`P_sym ρ P_sym`. This matrix is generally subnormalized. -/
def symmetricProjectionSandwichMatrix (ρ : State (TensorPower a n)) :
    CMatrix (TensorPower a n) :=
  symmetricProjectionMatrix (a := a) n * ρ.matrix * symmetricProjectionMatrix (a := a) n

@[simp]
theorem symmetricProjectionSandwichMatrix_eq (ρ : State (TensorPower a n)) :
    ρ.symmetricProjectionSandwichMatrix (a := a) =
      symmetricProjectionMatrix (a := a) n * ρ.matrix *
        symmetricProjectionMatrix (a := a) n := rfl

/-- The symmetric projection sandwich `P_sym ρ P_sym` is positive semidefinite. -/
theorem symmetricProjectionSandwichMatrix_posSemidef
    (ρ : State (TensorPower a n)) :
    (ρ.symmetricProjectionSandwichMatrix (a := a)).PosSemidef := by
  have h := ρ.pos.conjTranspose_mul_mul_same (symmetricProjectionMatrix (a := a) n)
  simpa [symmetricProjectionSandwichMatrix, symmetricProjectionMatrix_conjTranspose]
    using h

/-- The trace of `P_sym ρ P_sym` is at most one. -/
theorem symmetricProjectionSandwichMatrix_trace_re_le_one
    (ρ : State (TensorPower a n)) :
    ((ρ.symmetricProjectionSandwichMatrix (a := a)).trace).re ≤ 1 := by
  let P : CMatrix (TensorPower a n) := symmetricProjectionMatrix (a := a) n
  have htrace_le' :
      ((ρ.matrix * P).trace).re ≤ ((ρ.matrix * 1).trace).re :=
    cMatrix_trace_mul_le_of_le_posSemidef_left ρ.pos
      (symmetricProjectionMatrix_le_one (a := a) n)
  have htrace_le : ((ρ.matrix * P).trace).re ≤ ρ.matrix.trace.re := by
    simpa [P, Matrix.mul_one] using htrace_le'
  have hcyc :
      (ρ.symmetricProjectionSandwichMatrix (a := a)).trace = (ρ.matrix * P).trace := by
    calc
      (ρ.symmetricProjectionSandwichMatrix (a := a)).trace =
          (P * ρ.matrix * P).trace := rfl
      _ = (ρ.matrix * (P * P)).trace := by
          calc
            (P * ρ.matrix * P).trace = ((P * ρ.matrix) * P).trace := by
              rw [Matrix.mul_assoc]
            _ = (P * (P * ρ.matrix)).trace := by rw [Matrix.trace_mul_comm]
            _ = ((P * P) * ρ.matrix).trace := by rw [← Matrix.mul_assoc]
            _ = (ρ.matrix * (P * P)).trace := by rw [Matrix.trace_mul_comm]
      _ = (ρ.matrix * P).trace := by
          rw [show P * P = P by
            exact symmetricProjectionMatrix_idempotent (a := a) n]
  rw [hcyc]
  rw [ρ.trace_eq_one] at htrace_le
  norm_num at htrace_le
  exact htrace_le

private theorem matrix_le_one (ρ : State a) :
    ρ.matrix ≤ 1 := by
  classical
  rw [Matrix.le_iff]
  let U : Matrix.unitaryGroup a ℂ := ρ.pos.1.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => ((ρ.pos.1.eigenvalues i : ℝ) : ℂ)
  have hdiag : ρ.matrix = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using ρ.pos.1.spectral_theorem
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 := by
    simp [U]
  have heig_sum : ∑ i, ρ.pos.1.eigenvalues i = 1 := by
    have hc : (∑ i, ((ρ.pos.1.eigenvalues i : ℝ) : ℂ)) = 1 := by
      exact ρ.pos.1.trace_eq_sum_eigenvalues.symm.trans ρ.trace_eq_one
    exact Complex.ofReal_injective (by simpa using hc)
  have heig_le_one : ∀ i, ρ.pos.1.eigenvalues i ≤ 1 := by
    intro i
    have hnonneg (j : a) : 0 ≤ ρ.pos.1.eigenvalues j :=
      ρ.pos.eigenvalues_nonneg j
    calc ρ.pos.1.eigenvalues i
        ≤ ρ.pos.1.eigenvalues i +
            ∑ j ∈ Finset.univ.erase i, ρ.pos.1.eigenvalues j :=
          le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hnonneg j))
      _ = ∑ j, ρ.pos.1.eigenvalues j := by
          rw [add_comm]
          exact Finset.sum_erase_add (s := Finset.univ)
            (f := fun j => ρ.pos.1.eigenvalues j) (Finset.mem_univ i)
      _ = 1 := heig_sum
  have hsub :
      1 - ρ.matrix = (U : CMatrix a) * (1 - D) * star (U : CMatrix a) := by
    rw [hdiag]
    have hUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
      simp
    calc
      1 - (U : CMatrix a) * D * star (U : CMatrix a) =
          (U : CMatrix a) * 1 * star (U : CMatrix a) -
            (U : CMatrix a) * D * star (U : CMatrix a) := by
            rw [Matrix.mul_one, hUstar]
      _ = (U : CMatrix a) * (1 - D) * star (U : CMatrix a) := by
            noncomm_ring
  have hdiag_sub :
      (1 : CMatrix a) - D =
        Matrix.diagonal fun i => (((1 : ℝ) - ρ.pos.1.eigenvalues i : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [D]
    · simp [D, Matrix.diagonal, hij]
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (U : CMatrix a))]
  rw [hdiag_sub]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  have hnonneg : 0 ≤ (1 : ℝ) - ρ.pos.1.eigenvalues i := by
    exact sub_nonneg.mpr (heig_le_one i)
  exact_mod_cast hnonneg

/-- The projected matrix `P_sym ρ P_sym` is bounded by `P_sym`; equivalently,
the projected subnormalized state is automatically supported in the symmetric
subspace. -/
theorem symmetricProjectionSandwichMatrix_le_symmetricProjection
    (ρ : State (TensorPower a n)) :
    ρ.symmetricProjectionSandwichMatrix (a := a) ≤
      symmetricProjectionMatrix (a := a) n := by
  let P : CMatrix (TensorPower a n) := symmetricProjectionMatrix (a := a) n
  have hconj : P.conjTranspose * ρ.matrix * P ≤ P.conjTranspose * 1 * P :=
    star_left_conjugate_le_conjugate (matrix_le_one ρ) P
  simpa [symmetricProjectionSandwichMatrix, P, symmetricProjectionMatrix_conjTranspose,
    symmetricProjectionMatrix_idempotent, Matrix.mul_assoc] using hconj

/-- The symmetric projection sandwich as a subnormalized state. -/
def symmetricProjectionSandwichSubnormalizedState
    (ρ : State (TensorPower a n)) :
    SubnormalizedState (TensorPower a n) where
  matrix := ρ.symmetricProjectionSandwichMatrix (a := a)
  pos := ρ.symmetricProjectionSandwichMatrix_posSemidef (a := a)
  trace_le_one := ρ.symmetricProjectionSandwichMatrix_trace_re_le_one (a := a)

@[simp]
theorem symmetricProjectionSandwichSubnormalizedState_matrix
    (ρ : State (TensorPower a n)) :
    (ρ.symmetricProjectionSandwichSubnormalizedState (a := a)).matrix =
      ρ.symmetricProjectionSandwichMatrix (a := a) := rfl

/-- The symmetric projection sandwich subnormalized state is supported on the
symmetric tensor-power subspace. -/
theorem symmetricProjectionSandwichSubnormalizedState_supportedOnSymmetricSubspace
    (ρ : State (TensorPower a n)) :
    SubnormalizedState.SupportedOnSymmetricSubspace
      (a := a) (ρ.symmetricProjectionSandwichSubnormalizedState (a := a)) :=
  ρ.symmetricProjectionSandwichMatrix_le_symmetricProjection (a := a)

private theorem symmetricProjectionSandwichMatrix_fixed
    (ρ : State (TensorPower a n)) :
    symmetricProjectionMatrix (a := a) n *
        ρ.symmetricProjectionSandwichMatrix (a := a) *
        symmetricProjectionMatrix (a := a) n =
      ρ.symmetricProjectionSandwichMatrix (a := a) := by
  let P : CMatrix (TensorPower a n) := symmetricProjectionMatrix (a := a) n
  calc
    P * ρ.symmetricProjectionSandwichMatrix (a := a) * P =
        P * (P * ρ.matrix * P) * P := rfl
    _ = P * ρ.matrix * P := by
        have hP2 : P * P = P := symmetricProjectionMatrix_idempotent (a := a) n
        calc
          P * (P * ρ.matrix * P) * P = (P * P) * ρ.matrix * (P * P) := by
            noncomm_ring
          _ = P * ρ.matrix * P := by rw [hP2]

private theorem supportedOnSymmetricSubspace_of_projection_fixed
    (ρ : State (TensorPower a n))
    (hfixed : symmetricProjectionMatrix (a := a) n * ρ.matrix *
        symmetricProjectionMatrix (a := a) n = ρ.matrix) :
    ρ.SupportedOnSymmetricSubspace (a := a) := by
  let P : CMatrix (TensorPower a n) := symmetricProjectionMatrix (a := a) n
  have hconj : P.conjTranspose * ρ.matrix * P ≤ P.conjTranspose * 1 * P :=
    star_left_conjugate_le_conjugate (matrix_le_one ρ) P
  simpa [SupportedOnSymmetricSubspace, P, symmetricProjectionMatrix_conjTranspose,
    symmetricProjectionMatrix_idempotent, Matrix.mul_assoc, hfixed] using hconj

/-- Normalize the symmetric projection sandwich when its trace is positive. -/
def symmetricProjectionNormalizedState
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re) :
    State (TensorPower a n) where
  matrix := (((ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)⁻¹ : ℂ) •
    ρ.symmetricProjectionSandwichMatrix (a := a)
  pos := (ρ.symmetricProjectionSandwichMatrix_posSemidef (a := a)).smul
    (by exact_mod_cast inv_nonneg.mpr htrace.le)
  trace_eq_one := by
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
    simpa using inv_mul_cancel₀ htc_ne

@[simp]
theorem symmetricProjectionNormalizedState_matrix
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re) :
    (ρ.symmetricProjectionNormalizedState (a := a) htrace).matrix =
      (((ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)⁻¹ : ℂ) •
        ρ.symmetricProjectionSandwichMatrix (a := a) := rfl

/-- The normalized symmetric projection state is supported on the symmetric
tensor-power subspace. -/
theorem symmetricProjectionNormalizedState_supportedOnSymmetricSubspace
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re) :
    State.SupportedOnSymmetricSubspace
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
    [Nonempty a] (ρ : State (TensorPower a n))
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
    [Nonempty a] (ρ : State (TensorPower a n))
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
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : Channel (TensorPower a n) b) :
    (Φ.applyState (ρ.symmetricProjectionNormalizedState (a := a) htrace)).MatrixDominatedBy
      (Fintype.card (TensorPowerProfile a n) : ℝ)
      (Φ.applyState (symmetricProjectionReferenceState (a := a) n)) :=
  matrixDominatedBy_applyChannel Φ
    (ρ.matrixDominatedBy_symmetricProjectionReferenceState_of_symmetricProjectionNormalizedState
      (a := a) htrace)

/-- Polynomial-factor channel-output post-selection domination for the
normalized symmetric projection state. -/
theorem matrixDominatedBy_applyChannel_symmetricProjectionReferenceState_pow_succ_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : Channel (TensorPower a n) b) :
    (Φ.applyState (ρ.symmetricProjectionNormalizedState (a := a) htrace)).MatrixDominatedBy
      ((n + 1) ^ Fintype.card a : ℝ)
      (Φ.applyState (symmetricProjectionReferenceState (a := a) n)) :=
  matrixDominatedBy_applyChannel Φ
    (ρ.matrixDominatedBy_symmetricProjectionReferenceState_pow_succ_of_symmetricProjectionNormalizedState
      (a := a) htrace)

/-- State-level post-selection theorem with the constructed normalized
projection state as input. This removes the need to supply a separate support
hypothesis. -/
theorem stateLevelPostSelectionBound_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : Channel (TensorPower a n) b) :
    (Φ.applyState (ρ.symmetricProjectionNormalizedState (a := a) htrace)).MatrixDominatedBy
      ((n + 1) ^ Fintype.card a : ℝ)
      (Φ.applyState (symmetricProjectionReferenceState (a := a) n)) :=
  ρ.matrixDominatedBy_applyChannel_symmetricProjectionReferenceState_pow_succ_of_symmetricProjectionNormalizedState
    (a := a) htrace Φ

/-- Exact profile-count state-level post-selection theorem with the constructed
normalized projection state as input. -/
theorem stateLevelPostSelectionBound_profile_count_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : Channel (TensorPower a n) b) :
    (Φ.applyState (ρ.symmetricProjectionNormalizedState (a := a) htrace)).MatrixDominatedBy
      (Fintype.card (TensorPowerProfile a n) : ℝ)
      (Φ.applyState (symmetricProjectionReferenceState (a := a) n)) :=
  ρ.matrixDominatedBy_applyChannel_symmetricProjectionReferenceState_of_symmetricProjectionNormalizedState
    (a := a) htrace Φ

/-- Polynomial-factor trace-distance post-selection theorem with the
constructed normalized projection state as input. -/
theorem stateLevelPostSelectionTraceDistanceBound_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : Channel (TensorPower a n) b) :
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
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : Channel (TensorPower a n) b) :
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
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : Channel (TensorPower a n) b) :
    ((((n + 1) ^ Fintype.card a : ℝ) : ℂ) •
        (Φ.applyState (symmetricProjectionReferenceState (a := a) n)).matrix -
      (Φ.applyState (ρ.symmetricProjectionNormalizedState (a := a) htrace)).matrix).PosSemidef := by
  have h :=
    ρ.stateLevelPostSelectionBound_of_symmetricProjectionNormalizedState
      (a := a) htrace Φ
  dsimp [MatrixDominatedBy] at h
  rwa [Matrix.le_iff] at h

/-- Difference-matrix form of the exact profile-count post-selection domination
theorem for the constructed normalized projection state. -/
theorem stateLevelPostSelectionDifference_profile_count_posSemidef_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : Channel (TensorPower a n) b) :
    (((Fintype.card (TensorPowerProfile a n) : ℝ) : ℂ) •
        (Φ.applyState (symmetricProjectionReferenceState (a := a) n)).matrix -
      (Φ.applyState (ρ.symmetricProjectionNormalizedState (a := a) htrace)).matrix).PosSemidef := by
  have h :=
    ρ.stateLevelPostSelectionBound_profile_count_of_symmetricProjectionNormalizedState
      (a := a) htrace Φ
  dsimp [MatrixDominatedBy] at h
  rwa [Matrix.le_iff] at h

end State

namespace FiniteIidMixture

variable {n : ℕ} (M : FiniteIidMixture ι a n)

/-- A finite IID mixture state is dominated by itself with factor `1`. -/
theorem state_isDominatedBy_self :
    M.state.IsDominatedByFiniteIidMixture 1 M :=
  State.matrixDominatedBy_refl M.state

/-- A finite IID mixture state is dominated by itself with any factor at least
`1`. -/
theorem state_isDominatedBy_self_mono_factor {c : ℝ} (hc : 1 ≤ c) :
    M.state.IsDominatedByFiniteIidMixture c M :=
  State.isDominatedByFiniteIidMixture_mono_factor
    (M.state_isDominatedBy_self) hc

/-- Matrix form of the image of a finite IID mixture under a channel. -/
theorem applyChannel_state_matrix {b : Type w} [Fintype b] [DecidableEq b]
    (Φ : Channel (TensorPower a n) b) :
    (Φ.applyState M.state).matrix =
      ∑ i, (M.probs i) • (Φ.applyState ((M.states i).tensorPower n)).matrix := by
  change Φ.map M.state.matrix =
    ∑ i, (M.probs i) • Φ.map ((M.states i).tensorPower n).matrix
  rw [M.state_matrix, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change Φ.map ((M.probs i : ℂ) • ((M.states i).tensorPower n).matrix) =
    (M.probs i : ℂ) • Φ.map ((M.states i).tensorPower n).matrix
  rw [map_smul]

/-- If every tensor-power component of a finite IID mixture is dominated by the
same target state with the same factor, then the whole mixture is dominated by
that target with the same factor. -/
theorem matrixDominatedBy_of_forall_tensorPower (τ : State (TensorPower a n)) (c : ℝ)
    (h : ∀ i, ((M.states i).tensorPower n).MatrixDominatedBy c τ) :
    M.state.MatrixDominatedBy c τ := by
  dsimp [State.MatrixDominatedBy] at h ⊢
  change (((c : ℂ) • τ.matrix) - M.state.matrix).PosSemidef
  rw [M.state_matrix]
  have hsum_coeff :
      (∑ i, (M.probs i) • ((c : ℂ) • τ.matrix)) = (c : ℂ) • τ.matrix := by
    rw [← Finset.sum_smul]
    rw [M.weights_sum, one_smul]
  have hrewrite :
      ((c : ℂ) • τ.matrix) -
          (∑ i, (M.probs i) • ((M.states i).tensorPower n).matrix) =
        ∑ i, (M.probs i) •
          (((c : ℂ) • τ.matrix) - ((M.states i).tensorPower n).matrix) := by
    calc
      ((c : ℂ) • τ.matrix) -
          (∑ i, (M.probs i) • ((M.states i).tensorPower n).matrix) =
          (∑ i, (M.probs i) • ((c : ℂ) • τ.matrix)) -
            (∑ i, (M.probs i) • ((M.states i).tensorPower n).matrix) := by
            rw [hsum_coeff]
      _ = ∑ i, ((M.probs i) • ((c : ℂ) • τ.matrix) -
            (M.probs i) • ((M.states i).tensorPower n).matrix) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ i, (M.probs i) •
          (((c : ℂ) • τ.matrix) - ((M.states i).tensorPower n).matrix) := by
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
    (Φ : Channel (TensorPower a n) b) (τ : State b) (c : ℝ)
    (h : ∀ i, (Φ.applyState ((M.states i).tensorPower n)).MatrixDominatedBy c τ) :
    (Φ.applyState M.state).MatrixDominatedBy c τ := by
  dsimp [State.MatrixDominatedBy] at h ⊢
  change (((c : ℂ) • τ.matrix) - (Φ.applyState M.state).matrix).PosSemidef
  rw [M.applyChannel_state_matrix Φ]
  have hsum_coeff :
      (∑ i, (M.probs i) • ((c : ℂ) • τ.matrix)) = (c : ℂ) • τ.matrix := by
    rw [← Finset.sum_smul]
    rw [M.weights_sum, one_smul]
  have hrewrite :
      ((c : ℂ) • τ.matrix) -
          (∑ i, (M.probs i) • (Φ.applyState ((M.states i).tensorPower n)).matrix) =
        ∑ i, (M.probs i) •
          (((c : ℂ) • τ.matrix) -
            (Φ.applyState ((M.states i).tensorPower n)).matrix) := by
    calc
      ((c : ℂ) • τ.matrix) -
          (∑ i, (M.probs i) • (Φ.applyState ((M.states i).tensorPower n)).matrix) =
          (∑ i, (M.probs i) • ((c : ℂ) • τ.matrix)) -
            (∑ i, (M.probs i) • (Φ.applyState ((M.states i).tensorPower n)).matrix) := by
            rw [hsum_coeff]
      _ = ∑ i, ((M.probs i) • ((c : ℂ) • τ.matrix) -
            (M.probs i) • (Φ.applyState ((M.states i).tensorPower n)).matrix) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ i, (M.probs i) •
          (((c : ℂ) • τ.matrix) -
            (Φ.applyState ((M.states i).tensorPower n)).matrix) := by
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
    (Φ : Channel (TensorPower a n) (TensorPower b n))
    (N : FiniteIidMixture κ b n) (c : ℝ)
    (h : ∀ i, (Φ.applyState ((M.states i).tensorPower n)).IsDominatedByFiniteIidMixture c N) :
    (Φ.applyState M.state).IsDominatedByFiniteIidMixture c N :=
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
    (N : FiniteIidMixture ι a n) (τ : State (TensorPower a n)) {c d : ℝ}
    (hc : 0 ≤ c)
    (h : ∀ i, ((M.states i).tensorPower n).IsDominatedByFiniteIidMixture c N)
    (hNτ : N.state.MatrixDominatedBy d τ) :
    M.state.MatrixDominatedBy (c * d) τ :=
  State.matrixDominatedBy_trans hc
    (M.isDominatedByFiniteIidMixture_of_forall_tensorPower N c h) hNτ

end FiniteIidMixture

end

end QIT
