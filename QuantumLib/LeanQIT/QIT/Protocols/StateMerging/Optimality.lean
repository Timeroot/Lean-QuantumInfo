/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Protocols.StateMerging.SmoothMinConverse
public import QIT.Protocols.StateMerging.Direct

/-!
# Optimal entanglement cost of quantum state merging

This module assembles the concrete ADHW FQSW-plus-teleportation direct
construction with Berta's dimension-independent smooth-min-entropy converse
for the unrestricted Horodecki--Oppenheim--Winter rate domain. The resulting
optimal net entanglement cost is the conditional entropy, including its
negative (net entanglement generation) regime.

Source: HOW `swlong.6.2.tex:545-625`, the ADHW child protocol route
`fqsw.tex:402-420`, and Berta's one-shot/asymptotic converse
`diploma_thesis_berta_08_v1.tex:729-798,840-902,910-942`.
-/

@[expose] public section

namespace QIT

universe u v w x y

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

namespace PureVector

/-- The conditional entropy is the least achievable standard state-merging
net entanglement rate.  The membership half is the concrete ADHW
FQSW-plus-teleportation construction; minimality follows from Berta's
dimension-independent smooth-min-entropy converse on the HOW rate domain. -/
theorem conditionalEntropy_isLeast_stateMergingRates
    (psi : PureVector (Prod (Prod a b) r)) :
    IsLeast
      {R : Real |
        IsAchievableStateMergingRate.{u, v, w, x, x, y, y, x} psi R}
      psi.state.marginalA.conditionalEntropy :=
  ⟨stateMerging_direct_achievable_at_conditionalEntropy psi,
    fun R hR => conditionalEntropy_le_of_isAchievableStateMergingRate psi R hR⟩

/-- **Optimal state-merging cost.**  For every finite-dimensional pure
tripartite source, the infimum net entanglement cost of standard one-way-LOCC
state merging equals `H(A|B)` of the source. -/
theorem stateMergingCost_eq_conditionalEntropy
    (psi : PureVector (Prod (Prod a b) r)) :
    stateMergingCost.{u, v, w, x, x, y, y, x} psi =
      psi.state.marginalA.conditionalEntropy := by
  let S : Set Real :=
    {R | IsAchievableStateMergingRate.{u, v, w, x, x, y, y, x} psi R}
  have hleast := conditionalEntropy_isLeast_stateMergingRates.{u, v, w, x, y} psi
  have hnonempty : S.Nonempty := ⟨psi.state.marginalA.conditionalEntropy, hleast.1⟩
  have hbddBelow : BddBelow S := ⟨psi.state.marginalA.conditionalEntropy, hleast.2⟩
  apply le_antisymm
  · exact csInf_le hbddBelow hleast.1
  · exact le_csInf hnonempty hleast.2

/-- Positive conditional entropy means that optimal state merging consumes
net entanglement. -/
theorem stateMergingCost_pos_of_conditionalEntropy_pos
    (psi : PureVector (Prod (Prod a b) r))
    (h : 0 < psi.state.marginalA.conditionalEntropy) :
    0 < stateMergingCost.{u, v, w, x, x, y, y, x} psi := by
  rwa [stateMergingCost_eq_conditionalEntropy.{u, v, w, x, y} psi]

/-- Zero conditional entropy gives zero optimal net entanglement cost. -/
theorem stateMergingCost_eq_zero_of_conditionalEntropy_eq_zero
    (psi : PureVector (Prod (Prod a b) r))
    (h : psi.state.marginalA.conditionalEntropy = 0) :
    stateMergingCost.{u, v, w, x, x, y, y, x} psi = 0 := by
  rw [stateMergingCost_eq_conditionalEntropy.{u, v, w, x, y} psi, h]

/-- Negative conditional entropy means that optimal state merging generates
net entanglement. -/
theorem stateMergingCost_neg_of_conditionalEntropy_neg
    (psi : PureVector (Prod (Prod a b) r))
    (h : psi.state.marginalA.conditionalEntropy < 0) :
    stateMergingCost.{u, v, w, x, x, y, y, x} psi < 0 := by
  rwa [stateMergingCost_eq_conditionalEntropy.{u, v, w, x, y} psi]

end PureVector

end QIT
