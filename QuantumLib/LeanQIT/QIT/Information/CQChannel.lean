/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Classical.CQState
public import QIT.Core.Channel

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
    (E : Ensemble ι c) (D : Channel c d) :
    (((Channel.idChannel ι).prod D).applyState E.cqState).matrix =
      ∑ i : ι, (E.probs i : ℂ) •
        Matrix.kronecker (Matrix.single i i (1 : ℂ)) (D.applyState (E.states i)).matrix := by
  change MatrixMap.kron (Channel.idChannel ι).map D.map E.cqState.matrix = _
  rw [Ensemble.cqState_matrix]
  change MatrixMap.kron (Channel.idChannel ι).map D.map
      (∑ i : ι, (E.probs i : ℂ) •
        Matrix.kronecker (Matrix.single i i (1 : ℂ)) (E.states i).matrix) = _
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul, MatrixMap.kron_apply_kronecker]
  simp [Channel.applyState, Channel.idChannel, MatrixMap.ofKraus]

/-- Applying a left-local classical preparation channel to a cq state prepares
the output state selected by each classical block and leaves the quantum block
unchanged. -/
theorem applyState_prepare_prod_id_cqState_matrix
    {ι : Type u} {c : Type v} {d : Type w}
    [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c]
    [Fintype d] [DecidableEq d]
    (E : Ensemble ι c) (ρ : ι → State d) :
    (((Channel.prepare ρ).prod (Channel.idChannel c)).applyState E.cqState).matrix =
      ∑ i : ι, (E.probs i : ℂ) •
        Matrix.kronecker (ρ i).matrix (E.states i).matrix := by
  change MatrixMap.kron (Channel.prepare ρ).map (Channel.idChannel c).map
      E.cqState.matrix = _
  rw [Ensemble.cqState_matrix]
  change MatrixMap.kron (Channel.prepare ρ).map (Channel.idChannel c).map
      (∑ i : ι, (E.probs i : ℂ) •
        Matrix.kronecker (Matrix.single i i (1 : ℂ)) (E.states i).matrix) = _
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul, MatrixMap.kron_apply_kronecker]
  rw [Channel.prepare_map_single_eq]
  simp [Channel.idChannel, MatrixMap.ofKraus]

end

end QIT
