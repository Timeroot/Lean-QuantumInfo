/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.OneShot.WeakConverse
public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Converse

/-!
# One-shot upper bounds for entanglement-assisted classical communication

This module records the public-node assembly of the Khatri--Wilde one-shot
upper bounds for entanglement-assisted classical communication.

Source alignment:
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:411-427] states the
  weak-converse and sandwiched-Renyi one-shot upper bounds:
  `C_EA^epsilon(N) <= (I(N) + h_2(epsilon)) / (1 - epsilon)` and
  `C_EA^epsilon(N) <= I~_alpha(N) +
    alpha / (alpha - 1) * log2 (1 / (1 - epsilon))`.

The two proof ingredients are supplied by
`QIT.Coding.EntanglementAssisted.OneShot.WeakConverse` and
`QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Converse`; this file packages
them into one source-shaped theorem for the public catalog node.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace Channel

variable (N : Channel a b)

/-- Extended-real sandwiched-Renyi one-shot converse bound. -/
def entanglementAssistedSandwichedOneShotConverseBoundE
    (epsilon alpha : ℝ) : EReal :=
  N.sandwichedRenyiMutualInformationE alpha +
    ((alpha / (alpha - 1) * log2 (1 / (1 - epsilon)) : ℝ) : EReal)

/-- The weak-converse bound upper-bounds every one-shot reliable
entanglement-assisted classical code. -/
theorem entanglementAssistedWeakConverseBoundE_isOneShotUpperBound
    [Nonempty a] {epsilon : ℝ}
    (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_lt_one : epsilon < 1) :
    N.IsOneShotEntanglementAssistedClassicalCapacityUpperBoundE epsilon
      (N.entanglementAssistedWeakConverseBound epsilon : EReal) := by
  intro M _hM _hMeq _hMne EA _hEA _hEAeq EB _hEB _hEBeq C hC
  rw [EntanglementAssistedClassicalCode.rate_one C]
  exact C.log_card_le_channel_entanglementAssistedWeakConverseBoundE
    hepsilon_nonneg hepsilon_lt_one hC

/-- The sandwiched-Renyi bound upper-bounds every one-shot reliable
entanglement-assisted classical code. -/
theorem entanglementAssistedSandwichedOneShotConverseBoundE_isOneShotUpperBound
    [Nonempty a] {epsilon alpha : ℝ}
    (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_lt_one : epsilon < 1)
    (halpha : 1 < alpha) :
    N.IsOneShotEntanglementAssistedClassicalCapacityUpperBoundE epsilon
      (N.entanglementAssistedSandwichedOneShotConverseBoundE epsilon alpha) := by
  intro M _hM _hMeq _hMne EA _hEA _hEAeq EB _hEB _hEBeq C hC
  rw [EntanglementAssistedClassicalCode.rate_one C]
  exact C.log_card_le_channel_sandwichedRenyiMutualInformationE_add
    hepsilon_nonneg hepsilon_lt_one halpha hC

/-- Khatri--Wilde one-shot upper bounds for entanglement-assisted classical
communication.

This theorem packages both source inequalities at the public-node level:
the weak-converse bound, the sandwiched-Renyi strong-converse bound, and their
capacity consequences. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_upperBounds
    [Nonempty a] {epsilon alpha : ℝ}
    (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_lt_one : epsilon < 1)
    (halpha : 1 < alpha) :
    N.IsOneShotEntanglementAssistedClassicalCapacityUpperBoundE epsilon
        (N.entanglementAssistedWeakConverseBound epsilon : EReal) ∧
      N.IsOneShotEntanglementAssistedClassicalCapacityUpperBoundE epsilon
        (N.entanglementAssistedSandwichedOneShotConverseBoundE epsilon alpha) ∧
      N.oneShotEntanglementAssistedClassicalCapacityE epsilon ≤
        (N.entanglementAssistedWeakConverseBound epsilon : EReal) ∧
      N.oneShotEntanglementAssistedClassicalCapacityE epsilon ≤
        N.entanglementAssistedSandwichedOneShotConverseBoundE epsilon alpha := by
  constructor
  · exact N.entanglementAssistedWeakConverseBoundE_isOneShotUpperBound
      hepsilon_nonneg hepsilon_lt_one
  constructor
  · exact N.entanglementAssistedSandwichedOneShotConverseBoundE_isOneShotUpperBound
      hepsilon_nonneg hepsilon_lt_one halpha
  constructor
  · exact N.oneShotEntanglementAssistedClassicalCapacityE_le_weakConverseBound
      hepsilon_nonneg hepsilon_lt_one
  · simpa [entanglementAssistedSandwichedOneShotConverseBoundE] using
      N.oneShotEntanglementAssistedClassicalCapacityE_le_sandwichedRenyiMutualInformationE_add
        hepsilon_nonneg hepsilon_lt_one halpha

end Channel

end

end QIT
