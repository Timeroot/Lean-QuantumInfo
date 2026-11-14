/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.OneShot.Converse
public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Basic

/-!
# Sandwiched-Renyi one-shot EA converse

This module assembles the Khatri--Wilde one-shot strong-converse upper-bound
conversion for entanglement-assisted classical communication.

Source alignment:
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:411-427] derives
  `C_EA^epsilon(N) <= I~_alpha(N) +
    alpha / (alpha - 1) * log2(1 / (1 - epsilon))` for `alpha > 1`.

The proof combines the one-shot hypothesis-testing meta-converse with the
channel lift of `prop:sandwich-to-htre`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace EntanglementAssistedClassicalCode

variable {N : Channel a b}
variable {M : Type w} [Fintype M] [DecidableEq M] [Nonempty M]
variable {EA : Type x} [Fintype EA] [DecidableEq EA]
variable {EB : Type y} [Fintype EB] [DecidableEq EB]

/-- Per-code sandwiched-Renyi one-shot strong-converse upper bound.

This is the code-level form of
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:411-427]. -/
theorem log_card_le_channel_sandwichedRenyiMutualInformationE_add
    [Nonempty a]
    (C : EntanglementAssistedClassicalCode N 1 M EA EB)
    {epsilon alpha : ℝ}
    (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_lt_one : epsilon < 1)
    (halpha : 1 < alpha) (hC : C.maxErrorAtMost epsilon) :
    (log2 (Fintype.card M : ℝ) : EReal) ≤
      N.sandwichedRenyiMutualInformationE alpha +
        ((alpha / (alpha - 1) * log2 (1 / (1 - epsilon)) : ℝ) : EReal) :=
  (C.log_card_le_channel_hypothesisTestingMutualInformation
    hepsilon_nonneg hC).trans
    (N.hypothesisTestingMutualInformation_le_sandwichedRenyiMutualInformationE_add
      hepsilon_nonneg hepsilon_lt_one halpha)

end EntanglementAssistedClassicalCode

namespace Channel

variable (N : Channel a b)

/-- One-shot entanglement-assisted capacity is upper bounded by the
sandwiched-Renyi channel mutual information plus the Khatri--Wilde
strong-converse penalty. -/
theorem oneShotEntanglementAssistedClassicalCapacityE_le_sandwichedRenyiMutualInformationE_add
    [Nonempty a] {epsilon alpha : ℝ}
    (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_lt_one : epsilon < 1)
    (halpha : 1 < alpha) :
    N.oneShotEntanglementAssistedClassicalCapacityE epsilon ≤
      N.sandwichedRenyiMutualInformationE alpha +
        ((alpha / (alpha - 1) * log2 (1 / (1 - epsilon)) : ℝ) : EReal) :=
  (N.oneShotEntanglementAssistedClassicalCapacityE_le_hypothesisTestingMutualInformation
    hepsilon_nonneg).trans
    (N.hypothesisTestingMutualInformation_le_sandwichedRenyiMutualInformationE_add
      hepsilon_nonneg hepsilon_lt_one halpha)

end Channel

end

end QIT
