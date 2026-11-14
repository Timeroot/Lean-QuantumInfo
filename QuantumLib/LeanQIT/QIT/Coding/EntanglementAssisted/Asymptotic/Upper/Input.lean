/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Asymptotic.SandwichedTensorPower
public import QIT.Coding.EntanglementAssisted.Asymptotic.ProtocolLifting
public import QIT.Coding.EntanglementAssisted.OneShot.Upper
public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Converse
public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Limit

/-!
# Asymptotic upper-bound input structures

This module is part of the entanglement-assisted classical communication
asymptotic proof spine.  It was split out mechanically from the historical
`EntanglementAssistedAsymptotic` files; theorem statements and proof routes are
unchanged.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Topology
open Filter

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace Channel

variable (N : Channel a b)

/-- Source-shaped input expected from the Khatri--Wilde sandwiched-Renyi
asymptotic upper-bound route.

This version uses the source error range `ε ∈ [0, 1)`, which is the range in
the one-shot upper bounds [KhatriWilde2024Principles,
Chapters/EA_capacity.tex:411-427] and in the strong-converse argument
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:990-1331]. -/
structure EntanglementAssistedSourceAsymptoticUpperInput where
  logCard_upper :
    ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 ≤ ε → ε < 1 →
      ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
        ∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M],
          ∀ (EA : Type u) [Fintype EA] [DecidableEq EA],
            ∀ (EB : Type u) [Fintype EB] [DecidableEq EB],
              ∀ C : EntanglementAssistedClassicalCode N n M EA EB,
                C.maxErrorAtMost ε →
                  log2 (Fintype.card M : ℝ) ≤
                    (n : ℝ) * (N.entanglementAssistedInformation + η)

/-- Convert the Khatri--Wilde block-channel sandwiched-Renyi estimate into the
source-shaped asymptotic upper-bound input.

The hypothesis is the exact handoff expected from the sandwiched-Renyi
additivity plus `α → 1` limit route in
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:990-1331]: for every
slack and every source error `ε ∈ [0, 1)`, some `α > 1` eventually makes the
one-shot sandwiched upper bound for the block channel `N^{⊗n}` no larger than
`n * (I(N) + η)`.  The proof only reinterprets an `n`-use code as a one-shot
code for the block channel and then applies the already-proved one-shot
Khatri--Wilde upper bound. -/
theorem entanglementAssisted_sourceAsymptoticUpperInput_of_blockSandwichedBounds
    [Nonempty a]
    (hblock :
      ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 ≤ ε → ε < 1 →
        ∃ alpha : ℝ, 1 < alpha ∧
          ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
            (N.tensorPower n).sandwichedRenyiMutualInformationE alpha +
                ((alpha / (alpha - 1) * log2 (1 / (1 - ε)) : ℝ) : EReal) ≤
              ((n : ℝ) * (N.entanglementAssistedInformation + η) : EReal)) :
    N.EntanglementAssistedSourceAsymptoticUpperInput where
  logCard_upper := by
    intro η hη ε hε_nonneg hε_lt_one
    obtain ⟨alpha, halpha, N0, hN0⟩ :=
      hblock η hη ε hε_nonneg hε_lt_one
    refine ⟨N0, ?_⟩
    intro n hn M _hMfin _hMdec _hMnonempty EA _hEAfin _hEAdec EB _hEBfin _hEBdec C hC
    have hblockCode :
        (log2 (Fintype.card M : ℝ) : EReal) ≤
          (N.tensorPower n).sandwichedRenyiMutualInformationE alpha +
            ((alpha / (alpha - 1) * log2 (1 / (1 - ε)) : ℝ) : EReal) :=
      (C.asBlockOneShot).log_card_le_channel_sandwichedRenyiMutualInformationE_add
        hε_nonneg hε_lt_one halpha (C.asBlockOneShot_maxErrorAtMost hC)
    have hE :
        (log2 (Fintype.card M : ℝ) : EReal) ≤
          ((n : ℝ) * (N.entanglementAssistedInformation + η) : EReal) :=
      hblockCode.trans (hN0 n hn)
    exact EReal.coe_le_coe_iff.mp hE

/-- Source-shaped asymptotic upper-bound input from the completed
sandwiched-Renyi additivity and `α → 1+` limit route.

This uses the Khatri--Wilde alpha-to-one channel limit
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:1869-1907] in the
strong-converse asymptotic step: choose `α > 1` close enough to one so that the
optimized sandwiched channel quantity is within half the requested slack of
`I(N)`, then choose the blocklength large enough that the one-shot error penalty
divided by `n` is within the other half.  The block-channel sandwiched quantity
is reduced using the tensor-power additivity theorem. -/
theorem entanglementAssisted_sourceAsymptoticUpperInput_of_sandwichedLimit
    [Nonempty a] [Nonempty b] :
    N.EntanglementAssistedSourceAsymptoticUpperInput := by
  refine N.entanglementAssisted_sourceAsymptoticUpperInput_of_blockSandwichedBounds ?_
  intro η hη ε hε_nonneg hε_lt_one
  let δ : ℝ := η / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have htarget_lt :
      (N.entanglementAssistedInformation : EReal) <
        ((N.entanglementAssistedInformation + δ : ℝ) : EReal) := by
    exact EReal.coe_lt_coe_iff.mpr (by dsimp [δ]; linarith)
  have hlim := N.sandwichedRenyiMutualInformationE_tendsto_information
  have hα_eventually :
      ∀ᶠ alpha in State.relativeEntropyHighAlphaRightToOne,
        N.sandwichedRenyiMutualInformationE alpha.1 <
          ((N.entanglementAssistedInformation + δ : ℝ) : EReal) := by
    exact (tendsto_order.mp hlim).2
      ((N.entanglementAssistedInformation + δ : ℝ) : EReal) htarget_lt
  haveI : Filter.NeBot State.relativeEntropyHighAlphaRightToOne :=
    State.relativeEntropyHighAlphaRightToOne_neBot
  obtain ⟨alpha, hα_lt⟩ := hα_eventually.exists
  refine ⟨alpha.1, alpha.2, ?_⟩
  let penalty : ℝ :=
    alpha.1 / (alpha.1 - 1) * log2 (1 / (1 - ε))
  have hpenalty_tendsto :
      Tendsto (fun n : ℕ => penalty / (n : ℝ)) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpenalty_eventually :
      ∀ᶠ n : ℕ in atTop, penalty / (n : ℝ) < δ := by
    exact hpenalty_tendsto.eventually (eventually_lt_nhds hδ_pos)
  obtain ⟨Npen, hNpen⟩ := Filter.eventually_atTop.mp hpenalty_eventually
  refine ⟨max 1 Npen, ?_⟩
  intro n hn
  have hn_pos : 0 < n :=
    lt_of_lt_of_le (by norm_num : 0 < 1) (le_trans (Nat.le_max_left 1 Npen) hn)
  have hn_pen : n ≥ Npen :=
    le_trans (Nat.le_max_right 1 Npen) hn
  have hnR_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos
  have hpen_div : penalty / (n : ℝ) < δ := hNpen n hn_pen
  have hpen_le : penalty ≤ (n : ℝ) * δ := by
    simpa [mul_comm] using le_of_lt ((div_lt_iff₀ hnR_pos).mp hpen_div)
  let X : EReal := N.sandwichedRenyiMutualInformationE alpha.1
  let Y : ℝ := N.entanglementAssistedInformation + δ
  have hX_le : X ≤ (Y : EReal) := le_of_lt hα_lt
  have hn_nonneg_E : (0 : EReal) ≤ ((n : ℝ) : EReal) := by
    exact EReal.coe_nonneg.mpr (le_of_lt hnR_pos)
  have hmul_le : ((n : ℝ) : EReal) * X ≤ ((n : ℝ) : EReal) * (Y : EReal) := by
    exact mul_le_mul_of_nonneg_left hX_le hn_nonneg_E
  have htensor :
      (N.tensorPower n).sandwichedRenyiMutualInformationE alpha.1 =
        ((n : ℝ) : EReal) * X := by
    dsimp [X]
    simpa using N.sandwichedRenyiMutualInformationE_tensorPower_eq_n_mul alpha.2 n
  have hreal_tail :
      (n : ℝ) * Y + (n : ℝ) * δ =
        (n : ℝ) * (N.entanglementAssistedInformation + η) := by
    dsimp [Y, δ]
    ring
  calc
    (N.tensorPower n).sandwichedRenyiMutualInformationE alpha.1 +
          ((alpha.1 / (alpha.1 - 1) * log2 (1 / (1 - ε)) : ℝ) : EReal)
        = ((n : ℝ) : EReal) * X + (penalty : EReal) := by
            simp [htensor, penalty]
    _ ≤ ((n : ℝ) : EReal) * (Y : EReal) + (penalty : EReal) := by
            exact add_le_add hmul_le le_rfl
    _ ≤ ((n : ℝ) : EReal) * (Y : EReal) + (((n : ℝ) * δ : ℝ) : EReal) := by
            exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hpen_le)
    _ = ((n : ℝ) * (N.entanglementAssistedInformation + η) : EReal) := by
            rw [← EReal.coe_mul, ← EReal.coe_add, hreal_tail]
            simp [EReal.coe_mul, EReal.coe_add]

end Channel

end

end QIT
