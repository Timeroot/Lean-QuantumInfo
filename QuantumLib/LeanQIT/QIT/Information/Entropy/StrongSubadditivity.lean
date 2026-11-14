/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy.MutualInformationDPI

/-!
# Strong subadditivity of quantum entropy

This module proves finite-dimensional strong subadditivity in the conditional
mutual information form [KhatriWilde2024Principles, Chapters/entropies.tex:705-711].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w

noncomputable section

namespace State

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

private def abcToAcbEquiv (a : Type u) (b : Type v) (c : Type w) :
    Prod (Prod a b) c ≃ Prod (Prod a c) b where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv := by
    rintro ⟨⟨i, j⟩, k⟩
    rfl
  right_inv := by
    rintro ⟨⟨i, k⟩, j⟩
    rfl

/-- Source-shaped conditional mutual information
`I(A;B|C)_ρ = H(AC)_ρ + H(BC)_ρ - H(C)_ρ - H(ABC)_ρ`
for a left-associated tripartite state `ρ : State ((A × B) × C)`. -/
def condMutualInfoABGivenC (ρ : State (Prod (Prod a b) c)) : ℝ :=
  vonNeumann ρ.marginalAC + vonNeumann ρ.marginalBC
    - vonNeumann ρ.marginalB - vonNeumann ρ

@[simp]
theorem condMutualInfoABGivenC_eq (ρ : State (Prod (Prod a b) c)) :
    ρ.condMutualInfoABGivenC =
      vonNeumann ρ.marginalAC + vonNeumann ρ.marginalBC
        - vonNeumann ρ.marginalB - vonNeumann ρ := rfl

/-- Applying the channel `Tr_A ⊗ id_C` to a left-associated tripartite state
returns the `BC` marginal. -/
theorem applyState_traceOutLeft_prod_idChannel_eq_marginalBC
    (ρ : State (Prod (Prod a b) c)) :
    (((Channel.traceOutLeft a b).prod (Channel.idChannel c)).applyState ρ) =
      ρ.marginalBC := by
  apply State.ext
  ext bc bc'
  change
    MatrixMap.kron (Channel.traceOutLeft a b).map (Channel.idChannel c).map
        ρ.matrix bc bc' =
      ρ.marginalBC.matrix bc bc'
  rw [MatrixMap.kron_idChannel_apply_slice]
  simp [Channel.traceOutLeft, MatrixMap.partialTraceA, QIT.partialTraceA,
    State.marginalBC]

@[simp]
theorem applyState_idChannel (ρ : State a) :
    (Channel.idChannel a).applyState ρ = ρ := by
  apply State.ext
  change (Channel.idChannel a).map ρ.matrix = ρ.matrix
  simp [Channel.idChannel, MatrixMap.ofKraus]

/-- The `B` marginal computed from `ρ_BC` agrees with the direct tripartite
`B` marginal. -/
theorem marginalBC_marginalA_eq_marginalBOfABC
    (ρ : State (Prod (Prod a b) c)) :
    ρ.marginalBC.marginalA = ρ.marginalBOfABC := by
  let Φ : Channel (Prod a b) b := Channel.traceOutLeft a b
  let Ψ : Channel c c := Channel.idChannel c
  let ω : State (Prod b c) := (Φ.prod Ψ).applyState ρ
  have hω : ω = ρ.marginalBC := by
    simpa [ω, Φ, Ψ] using
      State.applyState_traceOutLeft_prod_idChannel_eq_marginalBC (ρ := ρ)
  calc
    ρ.marginalBC.marginalA = ω.marginalA := by rw [hω]
    _ = Φ.applyState ρ.marginalA := by
      exact State.marginalA_applyState_prod ρ Φ Ψ
    _ = ρ.marginalBOfABC := by
      simp [Φ, State.marginalAB_eq_marginalA, State.marginalBOfABC_eq]

/-- The `C` marginal computed from `ρ_BC` agrees with the direct tripartite
`C` marginal. -/
theorem marginalBC_marginalB_eq_marginalB
    (ρ : State (Prod (Prod a b) c)) :
    ρ.marginalBC.marginalB = ρ.marginalB := by
  let Φ : Channel (Prod a b) b := Channel.traceOutLeft a b
  let Ψ : Channel c c := Channel.idChannel c
  let ω : State (Prod b c) := (Φ.prod Ψ).applyState ρ
  have hω : ω = ρ.marginalBC := by
    simpa [ω, Φ, Ψ] using
      State.applyState_traceOutLeft_prod_idChannel_eq_marginalBC (ρ := ρ)
  calc
    ρ.marginalBC.marginalB = ω.marginalB := by rw [hω]
    _ = Ψ.applyState ρ.marginalB := by
      exact State.marginalB_applyState_prod ρ Φ Ψ
    _ = ρ.marginalB := by
      simp [Ψ]

/-- Strong subadditivity of finite-dimensional quantum entropy:
conditional mutual information is nonnegative. -/
theorem condMutualInfo_nonneg (ρ : State (Prod (Prod a b) c)) :
    0 ≤ ρ.condMutualInfo := by
  let Φ : Channel (Prod a b) b := Channel.traceOutLeft a b
  let Ψ : Channel c c := Channel.idChannel c
  have hDPI :=
    mutualInformation_dataProcessing_local_channels_ge (ρ := ρ) Φ Ψ
  have hOut :
      (Φ.prod Ψ).applyState ρ = ρ.marginalBC := by
    simpa [Φ, Ψ] using
      State.applyState_traceOutLeft_prod_idChannel_eq_marginalBC (ρ := ρ)
  have hMI :
      mutualInformation ρ ≥ mutualInformation ρ.marginalBC := by
    simpa [hOut] using hDPI
  rw [mutualInformation, mutualInformation,
    State.marginalBC_marginalA_eq_marginalBOfABC,
    State.marginalBC_marginalB_eq_marginalB] at hMI
  rw [State.condMutualInfo_eq]
  change 0 ≤
    ρ.marginalA.vonNeumann + ρ.marginalBC.vonNeumann -
      ρ.marginalBOfABC.vonNeumann - ρ.vonNeumann
  linarith

private theorem marginalAB_reindex_abcToAcbEquiv
    (ρ : State (Prod (Prod a b) c)) :
    (ρ.reindex (abcToAcbEquiv a b c)).marginalAB = ρ.marginalAC := by
  apply State.ext
  ext ac ac'
  simp [State.marginalAB, State.marginalA, State.marginalAC, State.reindex,
    abcToAcbEquiv, QIT.partialTraceB]

private theorem marginalBC_reindex_abcToAcbEquiv
    (ρ : State (Prod (Prod a b) c)) :
    (ρ.reindex (abcToAcbEquiv a b c)).marginalBC =
      ρ.marginalBC.reindex (Equiv.prodComm b c) := by
  apply State.ext
  ext cb cb'
  simp [State.marginalBC, State.reindex, abcToAcbEquiv, Equiv.prodComm]

private theorem marginalBOfABC_reindex_abcToAcbEquiv
    (ρ : State (Prod (Prod a b) c)) :
    (ρ.reindex (abcToAcbEquiv a b c)).marginalBOfABC = ρ.marginalB := by
  apply State.ext
  ext k k'
  simp [State.marginalBOfABC, State.marginalAB, State.marginalA, State.marginalB,
    State.reindex, abcToAcbEquiv, QIT.partialTraceA, QIT.partialTraceB,
    Fintype.sum_prod_type]

/-- Strong subadditivity in the source convention:
`I(A;B|C)_ρ` is nonnegative for every finite-dimensional tripartite state. -/
theorem condMutualInfoABGivenC_nonneg (ρ : State (Prod (Prod a b) c)) :
    0 ≤ ρ.condMutualInfoABGivenC := by
  let ρacb : State (Prod (Prod a c) b) :=
    ρ.reindex (abcToAcbEquiv a b c)
  have h := State.condMutualInfo_nonneg (ρ := ρacb)
  rw [State.condMutualInfo_eq,
    State.marginalAB_reindex_abcToAcbEquiv,
    State.marginalBC_reindex_abcToAcbEquiv,
    State.marginalBOfABC_reindex_abcToAcbEquiv,
    State.vonNeumann_reindex] at h
  rw [State.condMutualInfoABGivenC_eq]
  simpa [ρacb, State.vonNeumann_reindex] using h

end State

end

end QIT
