/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Entropy.MutualInformationDPI

/-!
# Strong subadditivity of quantum entropy

This module proves finite-dimensional strong subadditivity in the conditional
mutual information form [KhatriWilde2024Principles, Chapters/entropies.tex:705-711].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

noncomputable section
universe u v w

open QIT

namespace MState

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

/-- Source-shaped conditional mutual information
`I(A;B|C)_ρ = H(AC)_ρ + H(BC)_ρ - H(C)_ρ - H(ABC)_ρ`
for a left-associated tripartite state `ρ : MState ((A × B) × C)`. -/
def condMutualInfoABGivenC (ρ : MState ((a × b) × c)) : ℝ :=
  vonNeumann ρ.marginalAC + vonNeumann ρ.marginalBC
    - vonNeumann ρ.traceLeft - vonNeumann ρ

@[simp]
theorem condMutualInfoABGivenC_eq (ρ : MState ((a × b) × c)) :
    ρ.condMutualInfoABGivenC =
      vonNeumann ρ.marginalAC + vonNeumann ρ.marginalBC
        - vonNeumann ρ.traceLeft - vonNeumann ρ := rfl

/-- Applying the channel `Tr_A ⊗ id_C` to a left-associated tripartite state
returns the `BC` marginal. -/
theorem applyState_traceOutLeft_prod_idChannel_eq_marginalBC
    (ρ : MState ((a × b) × c)) :
    (((CPTPOp.traceOutLeft a b).prod (CPTPOp.id (dIn := c))) ρ) =
      ρ.marginalBC := by
  apply MState.ext
  rw [CPTPOp.mat_coe_eq_apply_mat, CPTPOp.prod_map]
  ext bc bc'
  rw [MatrixMap.kron_idChannel_apply_slice]
  simp [CPTPOp.traceOutLeft, MatrixMap.traceLeft, Matrix.traceLeft,
    MState.marginalBC_matrix]

/-- The `B` marginal computed from `ρ_BC` agrees with the direct tripartite
`B` marginal. -/
theorem marginalBC_traceRight_eq_marginalBOfABC
    (ρ : MState ((a × b) × c)) :
    ρ.marginalBC.traceRight = ρ.marginalBOfABC := by
  let Φ : CPTPMap (a × b) b := CPTPOp.traceOutLeft a b
  let Ψ : CPTPMap c c := CPTPOp.id (dIn := c)
  let ω : MState (b × c) := (Φ.prod Ψ) ρ
  have hω : ω = ρ.marginalBC := by
    simpa [ω, Φ, Ψ] using
      MState.applyState_traceOutLeft_prod_idChannel_eq_marginalBC (ρ := ρ)
  calc
    ρ.marginalBC.traceRight = ω.traceRight := by rw [hω]
    _ = Φ ρ.traceRight := by
      exact MState.traceRight_applyState_prod ρ Φ Ψ
    _ = ρ.marginalBOfABC := by
      simp [Φ, MState.marginalAB_eq_traceRight, MState.marginalBOfABC_eq]

/-- The `C` marginal computed from `ρ_BC` agrees with the direct tripartite
`C` marginal. -/
theorem marginalBC_traceLeft_eq_traceLeft
    (ρ : MState ((a × b) × c)) :
    ρ.marginalBC.traceLeft = ρ.traceLeft := by
  let Φ : CPTPMap (a × b) b := CPTPOp.traceOutLeft a b
  let Ψ : CPTPMap c c := CPTPOp.id (dIn := c)
  let ω : MState (b × c) := (Φ.prod Ψ) ρ
  have hω : ω = ρ.marginalBC := by
    simpa [ω, Φ, Ψ] using
      MState.applyState_traceOutLeft_prod_idChannel_eq_marginalBC (ρ := ρ)
  calc
    ρ.marginalBC.traceLeft = ω.traceLeft := by rw [hω]
    _ = Ψ ρ.traceLeft := by
      exact MState.traceLeft_applyState_prod ρ Φ Ψ
    _ = ρ.traceLeft := by
      simp [Ψ]

/-- Strong subadditivity of finite-dimensional quantum entropy:
conditional mutual information is nonnegative. -/
theorem condMutualInfo_nonneg (ρ : MState ((a × b) × c)) :
    0 ≤ ρ.condMutualInfo := by
  let Φ : CPTPMap (a × b) b := CPTPOp.traceOutLeft a b
  let Ψ : CPTPMap c c := CPTPOp.id (dIn := c)
  have hDPI :=
    mutualInformation_dataProcessing_local_channels_ge (ρ := ρ) Φ Ψ
  have hOut :
      (Φ.prod Ψ) ρ = ρ.marginalBC := by
    simpa [Φ, Ψ] using
      MState.applyState_traceOutLeft_prod_idChannel_eq_marginalBC (ρ := ρ)
  have hMI :
      mutualInformation ρ ≥ mutualInformation ρ.marginalBC := by
    simpa [hOut] using hDPI
  rw [mutualInformation, mutualInformation,
    MState.marginalBC_traceRight_eq_marginalBOfABC,
    MState.marginalBC_traceLeft_eq_traceLeft] at hMI
  rw [MState.condMutualInfo_eq]
  change 0 ≤
    ρ.traceRight.vonNeumann + ρ.marginalBC.vonNeumann -
      ρ.marginalBOfABC.vonNeumann - ρ.vonNeumann
  linarith

/-- Strong subadditivity in the source convention:
`I(A;B|C)_ρ` is nonnegative for every finite-dimensional tripartite state. -/
theorem condMutualInfoABGivenC_nonneg (ρ : MState ((a × b) × c)) :
    0 ≤ ρ.condMutualInfoABGivenC := by
  let ρacb : MState ((a × c) × b) :=
    ρ.reindex (prodABCToACBEquiv a b c)
  have h := MState.condMutualInfo_nonneg (ρ := ρacb)
  rw [MState.condMutualInfo_eq,
    MState.prodABCToACB_marginalAB,
    MState.prodABCToACB_marginalBC,
    MState.prodABCToACB_marginalBOfABC,
    MState.vonNeumann_reindex] at h
  rw [MState.condMutualInfoABGivenC_eq]
  simpa [ρacb, MState.vonNeumann_reindex] using h

end MState
