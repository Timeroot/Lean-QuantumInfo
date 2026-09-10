/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Coding.EntanglementAssisted.Asymptotic.Basic

/-!
# Protocol lifting and rate normalization

This module is part of the entanglement-assisted classical communication
asymptotic proof spine.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Topology
open Filter

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace EntanglementAssistedClassicalCode

variable {N : CPTPMap a b} {n : ℕ}
variable {M : Type u} [Fintype M] [DecidableEq M] [Nonempty M]
variable {EA : Type x} [Fintype EA] [DecidableEq EA]
variable {EB : Type y} [Fintype EB] [DecidableEq EB]

omit [DecidableEq a] in
/-- Rate normalization for a nonzero `n`-use entanglement-assisted code. -/
theorem rate_eq_log_card_div (C : EntanglementAssistedClassicalCode N n M EA EB)
    (hn : n ≠ 0) :
    C.rate = log2 (Fintype.card M : ℝ) / (n : ℝ) := by
  unfold rate messageRate
  simp [hn]

omit [DecidableEq a] in
/-- If the message set has logarithmic size at least `n * R`, then the
normalized `n`-use code rate is at least `R`. -/
theorem rate_ge_of_mul_le_log_card
    (C : EntanglementAssistedClassicalCode N n M EA EB)
    {R : ℝ} (hn_pos : 0 < n)
    (hlog : (n : ℝ) * R ≤ log2 (Fintype.card M : ℝ)) :
    R ≤ C.rate := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn_pos
  rw [C.rate_eq_log_card_div hn_ne]
  have hn_real_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  exact (le_div_iff₀ hn_real_pos).mpr (by simpa [mul_comm] using hlog)

omit [DecidableEq a] in
/-- If the message set has logarithmic size at most `n * B`, then the
normalized `n`-use code rate is at most `B`. -/
theorem rate_le_of_log_card_le_mul
    (C : EntanglementAssistedClassicalCode N n M EA EB)
    {B : ℝ} (hn_pos : 0 < n)
    (hlog : log2 (Fintype.card M : ℝ) ≤ (n : ℝ) * B) :
    C.rate ≤ B := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn_pos
  rw [C.rate_eq_log_card_div hn_ne]
  have hn_real_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  exact (div_le_iff₀ hn_real_pos).mpr (by simpa [mul_comm] using hlog)

/-- Interpret a one-shot code for the block channel `N^{⊗n}` as an `n`-use
code for `N`, dropping the terminal unit register of the one-fold tensor power. -/
def liftBlockOneShot
    (C : EntanglementAssistedClassicalCode (N.tensorPower n) 1 M EA EB) :
    EntanglementAssistedClassicalCode N n M EA EB where
  sharedState := C.sharedState
  encoder m :=
    (C.encoder m).outputReindex (tensorPowerOneEquiv (QIT.TensorPower a n))
  decoder :=
    C.decoder.reindex
      (Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower b n)) (Equiv.refl EB))

/-- Interpret an `n`-use code for `N` as a one-shot code for the block channel
`N^{⊗n}`, adding the terminal unit register of the one-fold tensor power.

This is the converse-direction block-code bridge used to lift one-shot upper
bounds to `n`-use asymptotic upper bounds. -/
def asBlockOneShot
    (C : EntanglementAssistedClassicalCode N n M EA EB) :
    EntanglementAssistedClassicalCode (N.tensorPower n) 1 M EA EB where
  sharedState := C.sharedState
  encoder m :=
    (C.encoder m).outputReindex (tensorPowerOneEquiv (QIT.TensorPower a n)).symm
  decoder :=
    C.decoder.reindex
      (Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower b n)) (Equiv.refl EB)).symm

/-- The lifted `n`-use code has normalized rate at least `R` when the block
one-shot code has rate at least `n * R`. -/
theorem liftBlockOneShot_rate_ge_of_mul_le_rate
    (C : EntanglementAssistedClassicalCode (N.tensorPower n) 1 M EA EB)
    {R : ℝ} (hn_pos : 0 < n) (hR : (n : ℝ) * R ≤ C.rate) :
    R ≤ C.liftBlockOneShot.rate := by
  apply C.liftBlockOneShot.rate_ge_of_mul_le_log_card hn_pos
  simpa using hR

/-- Channel-input states of the lifted block code are just the block one-shot
input states with the one-fold tensor-power register removed. -/
theorem liftBlockOneShot_channelInputState
    (C : EntanglementAssistedClassicalCode (N.tensorPower n) 1 M EA EB)
    (m : M) :
    C.liftBlockOneShot.channelInputState m =
      (C.channelInputState m).reindex
        (Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower a n)) (Equiv.refl EB)) := by
  apply MState.ext
  simp only [channelInputState, CPTPOp.mat_coe_eq_apply_mat, MState.reindex_matrix,
    liftBlockOneShot, CPTPOp.prod_map,
    CPTPOp.outputReindex, CPTPOp.map_ofMat]
  rw [MatrixMap.kron_outputReindex_left]

set_option maxRecDepth 4000 in
/-- Applying a one-fold tensor-power channel and then dropping the terminal unit
register agrees with dropping the unit input register first and applying the
underlying channel. -/
theorem applyState_tensorPower_one_prod_id_reindex
    {q : Type u} {r : Type v} {s : Type x}
    [Fintype q] [DecidableEq q] [Fintype r] [DecidableEq r]
    [Fintype s] [DecidableEq s]
    (D : CPTPMap q r) (ρ : MState (QIT.TensorPower q 1 × s)) :
    (D.prod (CPTPOp.id (dIn := s)))
        (ρ.reindex (Equiv.prodCongr (tensorPowerOneEquiv q) (Equiv.refl s))) =
      MState.reindex ((((D.tensorPower 1).prod (CPTPOp.id (dIn := s))) ρ))
        (Equiv.prodCongr (tensorPowerOneEquiv r) (Equiv.refl s)) := by
  apply MState.ext
  ext x y
  rcases x with ⟨xr, xs⟩
  rcases y with ⟨yr, ys⟩
  simp only [CPTPOp.mat_coe_eq_apply_mat, MState.reindex_matrix, CPTPOp.prod_map]
  change
    MatrixMap.kron D.map (CPTPOp.id (dIn := s)).map
        (Matrix.of fun z z' =>
          ρ.m ((z.1, PUnit.unit), z.2) ((z'.1, PUnit.unit), z'.2))
        (xr, xs) (yr, ys) =
      MatrixMap.kron (D.tensorPower 1).map (CPTPOp.id (dIn := s)).map
        ρ.m ((xr, PUnit.unit), xs) ((yr, PUnit.unit), ys)
  rw [MatrixMap.kron_idChannel_apply_slice]
  rw [MatrixMap.kron_idChannel_apply_slice]
  rw [CPTPOp.tensorPower_succ]
  change _ = (D.prod (D.tensorPower 0)).map _ _ _
  simp only [CPTPOp.prod_map]
  rw [CPTPOp.tensorPower_zero]
  change
    D.map
        (Matrix.of fun z z' =>
          ρ.m ((z, PUnit.unit), xs) ((z', PUnit.unit), ys)) xr yr =
      MatrixMap.kron D.map (CPTPOp.unit).map
        (Matrix.of fun z z' => ρ.m (z, xs) (z', ys))
        (xr, PUnit.unit) (yr, PUnit.unit)
  rw [CPTPOp.unit_map]
  refine Eq.trans ?_ (MatrixMap.kron_unit_apply_slice D.map _ _ _).symm
  rfl

/-- Output states of the lifted block code are the block one-shot output states
with the one-fold tensor-power register removed. -/
theorem liftBlockOneShot_outputState
    (C : EntanglementAssistedClassicalCode (N.tensorPower n) 1 M EA EB)
    (m : M) :
    C.liftBlockOneShot.outputState m =
      (C.outputState m).reindex
        (Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower b n)) (Equiv.refl EB)) := by
  rw [EntanglementAssistedClassicalCode.outputState]
  rw [C.liftBlockOneShot_channelInputState m]
  exact applyState_tensorPower_one_prod_id_reindex (N.tensorPower n) (C.channelInputState m)

/-- Lifting a one-shot block code preserves each message success probability. -/
theorem liftBlockOneShot_successProbability
    (C : EntanglementAssistedClassicalCode (N.tensorPower n) 1 M EA EB)
    (m : M) :
    C.liftBlockOneShot.successProbability m = C.successProbability m := by
  unfold successProbability
  rw [C.liftBlockOneShot_outputState m]
  exact POVM.prob_reindex_state C.decoder (C.outputState m)
    (Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower b n)) (Equiv.refl EB)) m

/-- Lifting a reliable one-shot block code gives a reliable `n`-use code. -/
theorem liftBlockOneShot_maxErrorAtMost
    (C : EntanglementAssistedClassicalCode (N.tensorPower n) 1 M EA EB)
    {ε : ℝ} (hC : C.maxErrorAtMost ε) :
    C.liftBlockOneShot.maxErrorAtMost ε := by
  intro m
  unfold error
  rw [C.liftBlockOneShot_successProbability m]
  exact hC m

/-- The block one-shot view has the same logarithmic rate as the message set. -/
theorem asBlockOneShot_rate
    (C : EntanglementAssistedClassicalCode N n M EA EB) :
    C.asBlockOneShot.rate = log2 (Fintype.card M : ℝ) :=
  C.asBlockOneShot.rate_one

/-- Channel-input states of the block one-shot view are just the `n`-use input
states with an added one-fold tensor-power unit register. -/
theorem asBlockOneShot_channelInputState
    (C : EntanglementAssistedClassicalCode N n M EA EB)
    (m : M) :
    C.asBlockOneShot.channelInputState m =
      (C.channelInputState m).reindex
        (Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower a n)) (Equiv.refl EB)).symm := by
  apply MState.ext
  simp only [channelInputState, CPTPOp.mat_coe_eq_apply_mat, MState.reindex_matrix,
    asBlockOneShot, CPTPOp.prod_map,
    CPTPOp.outputReindex, CPTPOp.map_ofMat]
  rw [MatrixMap.kron_outputReindex_left]
  rfl

/-- Output states of the block one-shot view are the original `n`-use output
states with an added one-fold tensor-power unit register. -/
theorem asBlockOneShot_outputState
    (C : EntanglementAssistedClassicalCode N n M EA EB)
    (m : M) :
    C.asBlockOneShot.outputState m =
      (C.outputState m).reindex
        (Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower b n)) (Equiv.refl EB)).symm := by
  let ein :=
    Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower a n)) (Equiv.refl EB)
  let eout :=
    Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower b n)) (Equiv.refl EB)
  have h :=
    applyState_tensorPower_one_prod_id_reindex
      (N.tensorPower n) (C.asBlockOneShot.channelInputState m)
  rw [C.asBlockOneShot_channelInputState m] at h
  have hinput :
      (((C.channelInputState m).reindex ein.symm).reindex ein) =
        C.channelInputState m := by
    exact MState.reindex_reindex_symm (C.channelInputState m) ein.symm
  rw [hinput] at h
  have hout :
      C.outputState m =
        (C.asBlockOneShot.outputState m).reindex eout := by
    simpa [EntanglementAssistedClassicalCode.outputState, eout,
      C.asBlockOneShot_channelInputState m] using h
  change C.asBlockOneShot.outputState m = (C.outputState m).reindex eout.symm
  calc
    C.asBlockOneShot.outputState m =
        ((C.asBlockOneShot.outputState m).reindex eout).reindex eout.symm := by
      rw [MState.reindex_reindex_symm]
    _ = (C.outputState m).reindex eout.symm := by
      rw [← hout]

/-- The block one-shot view preserves each message success probability. -/
theorem asBlockOneShot_successProbability
    (C : EntanglementAssistedClassicalCode N n M EA EB)
    (m : M) :
    C.asBlockOneShot.successProbability m = C.successProbability m := by
  unfold successProbability
  rw [C.asBlockOneShot_outputState m]
  exact (POVM.prob_reindex_state C.decoder (C.outputState m)
    (Equiv.prodCongr (tensorPowerOneEquiv (QIT.TensorPower b n)) (Equiv.refl EB)).symm
    m)

/-- Reinterpreting an `n`-use reliable code as a one-shot block-code preserves
the maximal error bound. -/
theorem asBlockOneShot_maxErrorAtMost
    (C : EntanglementAssistedClassicalCode N n M EA EB)
    {ε : ℝ} (hC : C.maxErrorAtMost ε) :
    C.asBlockOneShot.maxErrorAtMost ε := by
  intro m
  unfold error
  rw [C.asBlockOneShot_successProbability m]
  exact hC m

end EntanglementAssistedClassicalCode

end

end QIT
