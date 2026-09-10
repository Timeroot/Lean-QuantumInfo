/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Classical.CQState
public import QuantumLib.QIT.Core.Channel

/-!
# cq states under local quantum channels

Small reusable matrix identities for applying a quantum channel to the
quantum register of a classical-quantum state.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w

noncomputable section

/-- Applying a right-local channel to a cq state applies the channel to each
quantum block. -/
theorem applyState_id_prod_cqState_matrix
    {ι : Type u} {c : Type v} {d : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c]
    [Fintype d] [DecidableEq d]
    (E : MEnsemble c ι) (D : CPTPMap c d) :
    (((CPTPOp.id (dIn := ι)).prod D) E.cqState).m =
      ∑ i : ι, (E.probs i : ℂ) •
        Matrix.kronecker (Matrix.single i i (1 : ℂ)) (D (E.states i)).m := by
  rw [CPTPOp.mat_coe_eq_apply_mat, CPTPOp.prod_map,
    MEnsemble.cqState_matrix]
  change MatrixMap.kron (CPTPOp.id (dIn := ι)).map D.map
      (∑ i : ι, (E.probs i : ℂ) •
        Matrix.kronecker (Matrix.single i i (1 : ℂ)) (E.states i).m) = _
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul]
  simp only [Matrix.kronecker]
  rw [MatrixMap.kron_map_of_kron_state]
  simp [CPTPOp.mat_coe_eq_apply_mat, CPTPOp.id_map]

/-- Applying a left-local classical preparation channel to a cq state prepares
the output state selected by each classical block and leaves the quantum block
unchanged. -/
theorem applyState_prepare_prod_id_cqState_matrix
    {ι : Type u} {c : Type v} {d : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c]
    [Fintype d] [DecidableEq d]
    (E : MEnsemble c ι) (ρ : ι → MState d) :
    (((CPTPOp.prepare ρ).prod (CPTPOp.id (dIn := c))) E.cqState).m =
      ∑ i : ι, (E.probs i : ℂ) •
        Matrix.kronecker (ρ i).m (E.states i).m := by
  rw [CPTPOp.mat_coe_eq_apply_mat, CPTPOp.prod_map,
    MEnsemble.cqState_matrix]
  change MatrixMap.kron (CPTPOp.prepare ρ).map (CPTPOp.id (dIn := c)).map
      (∑ i : ι, (E.probs i : ℂ) •
        Matrix.kronecker (Matrix.single i i (1 : ℂ)) (E.states i).m) = _
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul]
  simp only [Matrix.kronecker]
  rw [MatrixMap.kron_map_of_kron_state]
  rw [CPTPOp.prepare_map_single_eq]
  simp [CPTPOp.id_map]

end

end QIT
