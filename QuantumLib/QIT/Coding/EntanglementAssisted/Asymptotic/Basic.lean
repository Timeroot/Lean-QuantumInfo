/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Coding.EntanglementAssisted.OneShot.Lower.Petz
public import QuantumLib.QIT.Coding.EntanglementAssisted.OneShot.WeakConverse
public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Petz.Additivity
public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Petz.Limit
public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Additivity.ChannelProduct
public import QuantumLib.QIT.HypothesisTesting.PetzComparison
public import QuantumLib.QIT.Information.Entropy.EntropyTensorPower
public import QuantumLib.QIT.Information.AlickiFannesWinter
import QuantumLib.QIT.Util.TensorPower

/-!
# Asymptotic basic helpers

This module is part of the entanglement-assisted classical communication
asymptotic proof spine.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Topology
open Filter

noncomputable section
universe u v w x y
variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

open QIT

namespace QIT

namespace PetzRenyiAlpha

/-- The left-to-one filter on the source range `0 < alpha < 1` is nontrivial:
every one-sided neighborhood of `1` contains an admissible Renyi parameter. -/
theorem leftToOne_neBot : Filter.NeBot PetzRenyiAlpha.leftToOne := by
  unfold PetzRenyiAlpha.leftToOne
  refine Filter.comap_neBot ?_
  intro t ht
  have hflt :
      (t ∩ Set.Iio (1 : ℝ)) ∩ Set.Ioi (0 : ℝ) ∈
        nhdsWithin (1 : ℝ) (Set.Iio 1) := by
    exact Filter.inter_mem
      (Filter.inter_mem ht self_mem_nhdsWithin)
      (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds zero_lt_one))
  have : Filter.NeBot (nhdsWithin (1 : ℝ) (Set.Iio 1)) :=
    nhdsWithin_Iio_neBot (α := ℝ) (a := 1) (b := 1) le_rfl
  rcases Filter.nonempty_of_mem hflt with ⟨x, hx⟩
  refine ⟨⟨x, ?_⟩, ?_⟩
  · exact ⟨hx.2, hx.1.2⟩
  · exact hx.1.1

end PetzRenyiAlpha

namespace MatrixMap

variable {α : Type u} {β : Type v} {γ : Type w}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Fintype γ] [DecidableEq γ]

/-- Relabel the output basis of a finite matrix map. -/
def outputReindex (Phi : MatrixMap α β) (e : β ≃ γ) : MatrixMap α γ where
  toFun X := Matrix.reindex e e (Phi X)
  map_add' X Y := by
    ext i j
    simp [Matrix.reindex_apply]
  map_smul' c X := by
    ext i j
    simp [Matrix.reindex_apply]

@[simp]
theorem outputReindex_apply (Phi : MatrixMap α β) (e : β ≃ γ) (X : CMatrix α) (i j : γ) :
    Phi.outputReindex e X i j = Phi X (e.symm i) (e.symm j) :=
  rfl

theorem outputReindex_isCompletelyPositive
    (Phi : MatrixMap α β) (e : β ≃ γ)
    (hPhi : MatrixMap.IsCompletelyPositive Phi) :
    MatrixMap.IsCompletelyPositive (Phi.outputReindex e) := by
  rw [MatrixMap.isCompletelyPositive_iff_choi]
  have hchoi :
      MatrixMap.choi (Phi.outputReindex e) =
        (MatrixMap.choi Phi).submatrix
          (fun x : α × γ => (x.1, e.symm x.2))
          (fun x : α × γ => (x.1, e.symm x.2)) := by
    ext x y
    rfl
  rw [hchoi]
  exact ((MatrixMap.isCompletelyPositive_iff_choi _).mp hPhi).submatrix _

theorem outputReindex_isTracePreserving
    (Phi : MatrixMap α β) (e : β ≃ γ)
    (hPhi : MatrixMap.IsTracePreserving Phi) :
    MatrixMap.IsTracePreserving (Phi.outputReindex e) := by
  intro X
  change (Matrix.reindex e e (Phi X)).trace = X.trace
  rw [cMatrix_trace_reindex e, hPhi X]

theorem outputReindex_mapsPositive
    (Phi : MatrixMap α β) (e : β ≃ γ)
    (hPhi : ∀ X : CMatrix α, X.PosSemidef → (Phi X).PosSemidef) :
    ∀ X : CMatrix α, X.PosSemidef → ((Phi.outputReindex e) X).PosSemidef := by
  intro X hX
  change (Matrix.reindex e e (Phi X)).PosSemidef
  exact (hPhi X hX).submatrix e.symm

end MatrixMap

namespace MatrixMap

/-- Right-slice form of the Kronecker product of matrix maps.  It views
`(Φ ⊗ Ψ)(X)` as first applying `Φ` to each right-index slice of `X`, then
applying `Ψ` to the resulting right-index matrix. -/
theorem kron_apply_slice_right
    {a₀ : Type u} {b₀ : Type v} {a₁ : Type w} {b₁ : Type x}
    [Fintype a₀] [DecidableEq a₀] [Fintype b₀] [DecidableEq b₀]
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    (Φ : MatrixMap a₀ b₀) (Ψ : MatrixMap a₁ b₁) (X : CMatrix (a₀ × a₁))
    (x₀ y₀ : b₀) (x₁ y₁ : b₁) :
    MatrixMap.kron Φ Ψ X (x₀, x₁) (y₀, y₁) =
      Ψ (fun j j' => Φ (fun i i' => X (i, j) (i', j')) x₀ y₀) x₁ y₁ := by
  rw [MatrixMap.kron_apply]
  rw [map_eq_sum_single Ψ
    (fun j j' => Φ (fun i i' => X (i, j) (i', j')) x₀ y₀)]
  simp only [Matrix.sum_apply]
  have hΦ : ∀ j j',
      Φ (fun i i' => X (i, j) (i', j')) x₀ y₀ =
        ∑ i : a₀, ∑ i' : a₀,
          X (i, j) (i', j') * Φ (Matrix.single i i' (1 : ℂ)) x₀ y₀ := by
    intro j j'
    have h := congrFun
      (congrFun (map_eq_sum_single Φ (fun i i' => X (i, j) (i', j'))) x₀)
      y₀
    simpa [Matrix.sum_apply] using h
  simp_rw [hΦ]
  simp [Finset.sum_mul, mul_assoc]

/-- Relabelling the output of the left factor of a Kronecker product of matrix maps relabels the
left component of the output index. -/
theorem kron_outputReindex_left
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {ε : Type y}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    [Fintype δ] [DecidableEq δ] [Fintype ε] [DecidableEq ε]
    (Φ : MatrixMap α β) (Ψ : MatrixMap δ ε) (e : β ≃ γ) (X : CMatrix (α × δ)) :
    MatrixMap.kron (Φ.outputReindex e) Ψ X =
      (MatrixMap.kron Φ Ψ X).submatrix
        (Equiv.prodCongr e (Equiv.refl ε)).symm (Equiv.prodCongr e (Equiv.refl ε)).symm := by
  ext p q
  rw [Matrix.submatrix_apply, MatrixMap.kron_apply, MatrixMap.kron_apply]
  simp only [outputReindex_apply, Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id_eq]

end MatrixMap

end QIT
end

noncomputable section

namespace CPTPOp

open QIT

variable {α : Type u} {β : Type v} {γ : Type w}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Fintype γ] [DecidableEq γ]

/-- Relabel the output basis of a finite-dimensional channel. -/
def outputReindex (Phi : CPTPMap α β) (e : β ≃ γ) : CPTPMap α γ :=
  CPTPOp.ofMat
    (Phi.map.outputReindex e)
    (MatrixMap.outputReindex_isCompletelyPositive Phi.map e Phi.map_cp)
    (MatrixMap.outputReindex_isTracePreserving Phi.map e Phi.map_TP)

@[simp]
theorem outputReindex_applyState (Phi : CPTPMap α β) (ρ : MState α) (e : β ≃ γ) :
    (Phi.outputReindex e) ρ = MState.reindex (Phi ρ) e := by
  apply MState.ext
  simp only [CPTPOp.mat_coe_eq_apply_mat, MState.reindex_matrix, outputReindex,
    CPTPOp.map_ofMat]
  rfl

end CPTPOp

end

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

open QIT

namespace QIT

theorem cMatrix_rpow_reindex_nonneg {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (A : CMatrix α) (hA : A.PosSemidef)
    {s : ℝ} (hs0 : 0 ≤ s) :
    CFC.rpow (Matrix.reindex e e A) s =
      Matrix.reindex e e (CFC.rpow A s) := by
  change (Matrix.reindex e e A) ^ s = Matrix.reindex e e (A ^ s)
  have hmap_nonneg : 0 ≤ Matrix.reindex e e A := by
    exact Matrix.nonneg_iff_posSemidef.mpr (hA.submatrix e.symm)
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  rw [CFC.rpow_eq_cfc_real (a := Matrix.reindex e e A) (y := s) hmap_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s) hA_nonneg]
  simpa [cMatrixReindexStarAlgEquiv, Matrix.coe_reindexAlgEquiv] using
    (StarAlgHomClass.map_cfc
      (cMatrixReindexStarAlgEquiv e)
      (fun x : ℝ => x ^ s) A
      (hf := (Real.continuous_rpow_const hs0).continuousOn)
      (hφ := by
        change Continuous (Matrix.reindex e e : CMatrix α → CMatrix β)
        fun_prop)).symm

end QIT

namespace MState

/-- Re-associate a product-channel output so that the second channel is the
right-local channel with reference `(R × B₁)`. -/
theorem applyState_id_prod_prod_assoc_symm
    {r : Type u} {a₁ : Type v} {b₁ : Type w} {a₂ : Type x} {b₂ : Type y}
    [Fintype r] [DecidableEq r]
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (N₁ : CPTPMap a₁ b₁) (N₂ : CPTPMap a₂ b₂)
    (ρ : MState (r × (a₁ × a₂))) :
    MState.reindex (((CPTPOp.id (dIn := r)).prod (N₁.prod N₂)) ρ)
        (Equiv.prodAssoc r b₁ b₂).symm =
      (((CPTPOp.id (dIn := r × b₁)).prod N₂)
        (MState.reindex ((((CPTPOp.id (dIn := r)).prod (N₁.prod (CPTPOp.id (dIn := a₂)))) ρ))
          (Equiv.prodAssoc r b₁ a₂).symm)) := by
  apply MState.ext
  ext x y
  rcases x with ⟨xRB1, xB2⟩
  rcases y with ⟨yRB1, yB2⟩
  rcases xRB1 with ⟨xR, xB1⟩
  rcases yRB1 with ⟨yR, yB1⟩
  simp only [CPTPOp.mat_coe_eq_apply_mat, CPTPOp.prod_map,
    MState.reindex_matrix, Matrix.submatrix_apply]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  simp [Equiv.prodAssoc, -CPTPOp.id_map]
  simp_rw [MatrixMap.kron_idChannel_left_apply_slice]
  change MatrixMap.kron N₁.map N₂.map
      (Matrix.of fun j j' => ρ.m (xR, j) (yR, j'))
      (xB1, xB2) (yB1, yB2) =
    N₂.map
      (Matrix.of fun j j' =>
        (MatrixMap.kron N₁.map (CPTPOp.id (dIn := a₂)).map
          (Matrix.of fun z z' => ρ.m (xR, z) (yR, z')))
          (xB1, j) (yB1, j'))
      xB2 yB2
  have hslice :
      (Matrix.of fun j j' =>
        (MatrixMap.kron N₁.map (CPTPOp.id (dIn := a₂)).map
          (Matrix.of fun z z' => ρ.m (xR, z) (yR, z')))
          (xB1, j) (yB1, j')) =
        (Matrix.of fun j j' =>
          N₁.map (Matrix.of fun i i' => ρ.m (xR, (i, j)) (yR, (i', j'))) xB1 yB1) := by
    ext j j'
    simp only [Matrix.of_apply]
    rw [MatrixMap.kron_idChannel_apply_slice]
    rfl
  rw [hslice]
  exact MatrixMap.kron_apply_slice_right
    N₁.map N₂.map (Matrix.of fun j j' => ρ.m (xR, j) (yR, j'))
    xB1 yB1 xB2 yB2

/-- The `(R × B₁)` marginal of the partially processed state is the output of
`N₁` on the corresponding mixed `(R × A₁)` input. -/
theorem partialProductOutput_marginalAB
    {r : Type u} {a₁ : Type v} {b₁ : Type w} {a₂ : Type x}
    [Fintype r] [DecidableEq r]
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂]
    (N₁ : CPTPMap a₁ b₁) (ρ : MState (r × (a₁ × a₂))) :
    ((MState.reindex ((((CPTPOp.id (dIn := r)).prod (N₁.prod (CPTPOp.id (dIn := a₂)))) ρ))
          (Equiv.prodAssoc r b₁ a₂).symm).marginalAB) =
      ((CPTPOp.id (dIn := r)).prod N₁)
        ((ρ.reindex (Equiv.prodAssoc r a₁ a₂).symm).marginalAB) := by
  apply MState.ext
  ext x y
  rcases x with ⟨xR, xB1⟩
  rcases y with ⟨yR, yB1⟩
  simp only [MState.marginalAB_eq_traceRight, MState.traceRight_m, Matrix.traceRight,
    Matrix.of_apply, MState.reindex_matrix, CPTPOp.mat_coe_eq_apply_mat, CPTPOp.prod_map]
  simp [Equiv.prodAssoc, -CPTPOp.id_map]
  simp_rw [MatrixMap.kron_idChannel_left_apply_slice]
  change
    (∑ x_1 : a₂,
      (MatrixMap.kron N₁.map (CPTPOp.id (dIn := a₂)).map
        (Matrix.of fun j j' => ρ.m (xR, j) (yR, j')))
        (xB1, x_1) (yB1, x_1)) =
      N₁.map
        (Matrix.of fun j j' => ∑ x_1 : a₂, ρ.m (xR, (j, x_1)) (yR, (j', x_1)))
        xB1 yB1
  simp_rw [MatrixMap.kron_idChannel_apply_slice]
  have hsum :=
    congrFun
      (congrFun
        (map_sum N₁.map
          (fun x_1 : a₂ => Matrix.of fun i i' =>
            ρ.m (xR, (i, x_1)) (yR, (i', x_1)))
          Finset.univ)
        xB1)
      yB1
  simp only [Matrix.sum_apply] at hsum
  have hmatrix :
      (Matrix.of fun j j' => ∑ x_1 : a₂, ρ.m (xR, (j, x_1)) (yR, (j', x_1))) =
        (∑ x_1 : a₂, Matrix.of fun i i' => ρ.m (xR, (i, x_1)) (yR, (i', x_1))) := by
    ext j j'
    simp [Matrix.sum_apply, Matrix.of_apply]
  rw [hmatrix]
  exact hsum.symm

theorem mutualInformation_bipartiteProduct
    {a₁ : Type u} {b₁ : Type v} {a₂ : Type w} {b₂ : Type x}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ : MState (a₁ × b₁)) (σ : MState (a₂ × b₂)) :
    mutualInformation (ρ.bipartiteProduct σ) =
      mutualInformation ρ + mutualInformation σ := by
  unfold mutualInformation
  rw [MState.bipartiteProduct_traceRight, MState.bipartiteProduct_traceLeft]
  rw [MState.vonNeumann_prod, MState.vonNeumann_prod]
  unfold MState.bipartiteProduct
  rw [MState.vonNeumann_reindex, MState.vonNeumann_prod]
  ring

/-- Chain-rule form used for the channel mutual-information additivity upper
bound:
`I(R;B₁B₂) = I(R;B₁) + I(RB₁;B₂) - I(B₁;B₂)`.

The state is stored as `(R × B₁) × B₂`; the left side re-associates it as
`R × (B₁ × B₂)`.
This follows the source route in Khatri--Wilde,
`Chapters/EA_capacity.tex`, lines 1080-1086. -/
theorem mutualInformation_assoc_chain
    {r : Type u} {b₁ : Type v} {b₂ : Type w}
    [Fintype r] [DecidableEq r] [Fintype b₁] [DecidableEq b₁]
    [Fintype b₂] [DecidableEq b₂]
    (ρ : MState ((r × b₁) × b₂)) :
    mutualInformation (ρ.reindex (Equiv.prodAssoc r b₁ b₂)) =
      mutualInformation ρ.marginalAB + mutualInformation ρ -
        mutualInformation ρ.marginalBC := by
  unfold mutualInformation
  have hA :
      (ρ.reindex (Equiv.prodAssoc r b₁ b₂)).traceRight =
        ρ.marginalAB.traceRight := by
    apply MState.ext
    ext x y
    simp [MState.reindex_matrix, MState.marginalAB_eq_traceRight,
      Matrix.traceRight, Equiv.prodAssoc, Fintype.sum_prod_type]
  have hB :
      (ρ.reindex (Equiv.prodAssoc r b₁ b₂)).traceLeft =
        ρ.marginalBC := by
    apply MState.ext
    ext x y
    simp [MState.reindex_matrix, MState.marginalBC_matrix,
      Matrix.traceLeft, Equiv.prodAssoc]
  rw [hA, hB, MState.vonNeumann_reindex]
  rw [MState.marginalAB_eq_traceRight]
  rw [MState.marginalBC_traceRight_eq_marginalBOfABC,
    MState.marginalBC_traceLeft_eq_traceLeft]
  rw [MState.marginalBOfABC_eq, MState.marginalAB_eq_traceRight]
  ring

/-- Chain-rule upper bound obtained from
`I(R;B₁B₂) = I(R;B₁) + I(RB₁;B₂) - I(B₁;B₂)` and nonnegativity of
mutual information. -/
theorem mutualInformation_assoc_le
    {r : Type u} {b₁ : Type v} {b₂ : Type w}
    [Fintype r] [DecidableEq r] [Fintype b₁] [DecidableEq b₁]
    [Fintype b₂] [DecidableEq b₂]
    (ρ : MState ((r × b₁) × b₂)) :
    mutualInformation (ρ.reindex (Equiv.prodAssoc r b₁ b₂)) ≤
      mutualInformation ρ.marginalAB + mutualInformation ρ := by
  rw [MState.mutualInformation_assoc_chain]
  have hnonneg : 0 ≤ mutualInformation ρ.marginalBC :=
    MState.mutualInformation_nonneg ρ.marginalBC
  linarith

/-- Mutual information is additive on IID bipartite tensor powers:
`I(A^n;B^n)_{ρ^{⊗n}} = n I(A;B)_ρ`. -/
theorem mutualInformation_tensorPowerBipartite (ρ : MState (a × b)) (n : ℕ) :
    mutualInformation (ρ.tensorPowerBipartite n) =
      (n : ℝ) * mutualInformation ρ := by
  unfold mutualInformation
  rw [ρ.tensorPowerBipartite_traceRight n,
    ρ.tensorPowerBipartite_traceLeft n]
  rw [MState.vonNeumann_tensorPower,
    MState.vonNeumann_tensorPower,
    show vonNeumann (ρ.tensorPowerBipartite n) =
      vonNeumann ((ρ.tensorPower n).reindex (tensorPowerProdEquiv a b n)) from rfl,
    MState.vonNeumann_reindex,
    MState.vonNeumann_tensorPower]
  ring

/-- PSD-domain Petz--Renyi divergence is invariant under simultaneous finite
basis relabeling in the source range `0 ≤ alpha ≤ 1`. -/
theorem petzRenyiPSDFinite_reindex {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ σ : MState α) (e : α ≃ β)
    (alphaR : ℝ) (halpha_pos : 0 < alphaR) (halpha_lt_one : alphaR < 1) :
    (ρ.reindex e).petzRenyiPSDFinite (σ.reindex e)
        alphaR halpha_pos (ne_of_lt halpha_lt_one) =
      ρ.petzRenyiPSDFinite σ alphaR halpha_pos (ne_of_lt halpha_lt_one) := by
  unfold MState.petzRenyiPSDFinite
  have halpha_nonneg : 0 ≤ alphaR := le_of_lt halpha_pos
  have hone_sub_nonneg : 0 ≤ 1 - alphaR := sub_nonneg.mpr (le_of_lt halpha_lt_one)
  rw [MState.reindex_matrix, MState.reindex_matrix]
  change (1 / (alphaR - 1)) *
      log2 (((CFC.rpow (Matrix.reindex e e ρ.m) alphaR *
        CFC.rpow (Matrix.reindex e e σ.m) (1 - alphaR)).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow ρ.m alphaR *
        CFC.rpow σ.m (1 - alphaR)).trace).re)
  rw [cMatrix_rpow_reindex_nonneg e ρ.m ρ.psd halpha_nonneg]
  rw [cMatrix_rpow_reindex_nonneg e σ.m σ.psd hone_sub_nonneg]
  change (1 / (alphaR - 1)) *
      log2 ((((Matrix.reindexAlgEquiv ℂ ℂ e) (CFC.rpow ρ.m alphaR) *
        (Matrix.reindexAlgEquiv ℂ ℂ e)
          (CFC.rpow σ.m (1 - alphaR))).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow ρ.m alphaR *
        CFC.rpow σ.m (1 - alphaR)).trace).re)
  rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ e)
    (CFC.rpow ρ.m alphaR) (CFC.rpow σ.m (1 - alphaR))]
  change (1 / (alphaR - 1)) *
      log2 (((Matrix.reindex e e
        (CFC.rpow ρ.m alphaR *
          CFC.rpow σ.m (1 - alphaR))).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow ρ.m alphaR *
        CFC.rpow σ.m (1 - alphaR)).trace).re)
  rw [cMatrix_trace_reindex e]

/-- The product-marginal Petz coefficient is strictly positive in the source
range `0 < alpha < 1`, because the product-marginal Nussbaum--Szkola model has
nonempty common support. -/
theorem petzRenyiCoefficient_productMarginal_pos
    (ρ : MState (a × b)) {alphaR : ℝ}
    (halpha_pos : 0 < alphaR) (halpha_lt_one : alphaR < 1) :
    0 < ρ.petzRenyiCoefficient (ρ.traceRight.prod ρ.traceLeft) alphaR := by
  classical
  let M := BinaryHypothesisTest.productMarginalNussbaumSzkolaModel ρ
  have hpq : M.pDistribution.SupportedBy M.q := by
    simpa [M] using
      BinaryHypothesisTest.productMarginalNussbaumSzkolaModel_p_supportedBy_q ρ
  have hcommon :
      Nonempty M.commonSupport :=
    BinaryHypothesisTest.ClassicalBinaryModel.commonSupport_nonempty_of_p_supportedBy_q
      (M := M) hpq
  have hpart_pos : 0 < M.chernoffPartitionNNReal alphaR :=
    BinaryHypothesisTest.ClassicalBinaryModel.chernoffPartitionNNReal_pos_of_commonSupport_nonempty
      (M := M) hcommon alphaR
  have hpart :
      M.chernoffPartitionNNReal alphaR = M.petzChernoffCoefficient alphaR :=
    BinaryHypothesisTest.ClassicalBinaryModel.chernoffPartitionNNReal_eq_petzChernoffCoefficient_of_mem_Ioo
      (M := M) halpha_pos halpha_lt_one
  have hcoeff :
      M.petzChernoffCoefficient alphaR =
        ρ.petzRenyiCoefficient (ρ.traceRight.prod ρ.traceLeft) alphaR := by
    simpa [M] using
      BinaryHypothesisTest.productMarginalNussbaumSzkolaModel_petzChernoffCoefficient_eq
        ρ (le_of_lt halpha_pos) (le_of_lt halpha_lt_one)
  simpa [hpart, hcoeff] using hpart_pos

/-- PSD-domain Petz--Renyi divergence is additive on IID tensor powers when
the base coefficient is positive. -/
theorem petzRenyiPSDFinite_tensorPower
    {α : Type u} [Fintype α] [DecidableEq α] (ρ σ : MState α)
    {alphaR : ℝ} (halpha_pos : 0 < alphaR) (halpha_lt_one : alphaR < 1)
    (hcoeff : 0 < ρ.petzRenyiCoefficient σ alphaR) (n : ℕ) :
    (ρ.tensorPower n).petzRenyiPSDFinite (σ.tensorPower n)
        alphaR halpha_pos (ne_of_lt halpha_lt_one) =
      (n : ℝ) * ρ.petzRenyiPSDFinite σ alphaR halpha_pos (ne_of_lt halpha_lt_one) := by
  unfold MState.petzRenyiPSDFinite
  have htrace_tensor :
      ((CFC.rpow (ρ.tensorPower n).m alphaR *
          CFC.rpow (σ.tensorPower n).m (1 - alphaR)).trace).re =
        ((ρ.petzRenyiCoefficient σ alphaR : ℝ) ^ n) := by
    have htrace :
        ((CFC.rpow (ρ.tensorPower n).m alphaR *
            CFC.rpow (σ.tensorPower n).m (1 - alphaR)).trace).re =
          (((ρ.tensorPower n).petzRenyiCoefficient (σ.tensorPower n) alphaR : ℝ)) := by
      have h := MState.petzRenyiCoefficient_trace_eq
        (ρ.tensorPower n) (σ.tensorPower n) alphaR
      have hre := congrArg Complex.re h
      simpa using hre.symm
    have hcoeff_tensor :
        (((ρ.tensorPower n).petzRenyiCoefficient
            (σ.tensorPower n) alphaR : ℝ) =
          ((ρ.petzRenyiCoefficient σ alphaR : ℝ) ^ n)) := by
      exact_mod_cast MState.petzRenyiCoefficient_tensorPower ρ σ alphaR n
    rw [htrace, hcoeff_tensor]
  have htrace_base :
      ((CFC.rpow ρ.m alphaR *
          CFC.rpow σ.m (1 - alphaR)).trace).re =
        (ρ.petzRenyiCoefficient σ alphaR : ℝ) := by
    have h := MState.petzRenyiCoefficient_trace_eq ρ σ alphaR
    have hre := congrArg Complex.re h
    simpa using hre.symm
  change (1 / (alphaR - 1)) *
      log2 ((CFC.rpow (ρ.tensorPower n).m alphaR *
        CFC.rpow (σ.tensorPower n).m (1 - alphaR)).trace).re =
    (n : ℝ) *
      ((1 / (alphaR - 1)) *
        log2 ((CFC.rpow ρ.m alphaR *
          CFC.rpow σ.m (1 - alphaR)).trace).re)
  rw [htrace_tensor, htrace_base]
  have hcoeff_real_pos : 0 < (ρ.petzRenyiCoefficient σ alphaR : ℝ) := by
    exact_mod_cast hcoeff
  rw [log2_pow (ρ.petzRenyiCoefficient σ alphaR : ℝ) n]
  ring

/-- PSD-domain barred Petz--Renyi mutual information is additive on IID
bipartite tensor powers. -/
theorem barPetzRenyiMutualInformationPSDFinite_tensorPowerBipartite
    (ρ : MState (a × b)) {alphaR : ℝ}
    (halpha_pos : 0 < alphaR) (halpha_lt_one : alphaR < 1) (n : ℕ) :
    (ρ.tensorPowerBipartite n).barPetzRenyiMutualInformationPSDFinite
        alphaR halpha_pos (ne_of_lt halpha_lt_one) =
      (n : ℝ) *
        ρ.barPetzRenyiMutualInformationPSDFinite
          alphaR halpha_pos (ne_of_lt halpha_lt_one) := by
  have hcomp :
      (ρ.tensorPowerBipartite n).traceRight.prod
          (ρ.tensorPowerBipartite n).traceLeft =
        (ρ.traceRight.prod ρ.traceLeft).tensorPowerBipartite n := by
    calc
      (ρ.tensorPowerBipartite n).traceRight.prod
          (ρ.tensorPowerBipartite n).traceLeft =
        (ρ.traceRight.tensorPower n).prod
          (ρ.traceLeft.tensorPower n) := by
          rw [ρ.tensorPowerBipartite_traceRight n,
            ρ.tensorPowerBipartite_traceLeft n]
      _ = (ρ.traceRight.prod ρ.traceLeft).tensorPowerBipartite n :=
          (MState.prod_tensorPowerBipartite ρ.traceRight ρ.traceLeft n).symm
  unfold MState.barPetzRenyiMutualInformationPSDFinite
  calc
    (ρ.tensorPowerBipartite n).petzRenyiPSDFinite
        ((ρ.tensorPowerBipartite n).traceRight.prod
          (ρ.tensorPowerBipartite n).traceLeft)
        alphaR halpha_pos (ne_of_lt halpha_lt_one) =
      (ρ.tensorPowerBipartite n).petzRenyiPSDFinite
        ((ρ.traceRight.prod ρ.traceLeft).tensorPowerBipartite n)
        alphaR halpha_pos (ne_of_lt halpha_lt_one) := by
        unfold MState.petzRenyiPSDFinite
        rw [congrArg DensityOp.m hcomp]
    _ =
      (n : ℝ) *
        ρ.petzRenyiPSDFinite (ρ.traceRight.prod ρ.traceLeft)
          alphaR halpha_pos (ne_of_lt halpha_lt_one) := by
        change
          ((ρ.tensorPower n).reindex (tensorPowerProdEquiv a b n)).petzRenyiPSDFinite
            (((ρ.traceRight.prod ρ.traceLeft).tensorPower n).reindex
              (tensorPowerProdEquiv a b n))
            alphaR halpha_pos (ne_of_lt halpha_lt_one) =
          (n : ℝ) *
            ρ.petzRenyiPSDFinite (ρ.traceRight.prod ρ.traceLeft)
              alphaR halpha_pos (ne_of_lt halpha_lt_one)
        rw [MState.petzRenyiPSDFinite_reindex
          (ρ.tensorPower n)
          ((ρ.traceRight.prod ρ.traceLeft).tensorPower n)
          (tensorPowerProdEquiv a b n)
          alphaR halpha_pos halpha_lt_one]
        exact MState.petzRenyiPSDFinite_tensorPower ρ
          (ρ.traceRight.prod ρ.traceLeft)
          halpha_pos halpha_lt_one
          (MState.petzRenyiCoefficient_productMarginal_pos
            ρ halpha_pos halpha_lt_one)
          n

end MState
