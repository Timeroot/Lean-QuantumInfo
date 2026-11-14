/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.ConditionalRenyi

/-!
# Sandwiched Renyi DPI statement surface

Planning-only statement surface for the sandwiched Renyi data-processing
inequality at general channel arity.  This `Prop`-valued target is consumed by
local reduction theorems.  The completed public PSD-reference sandwiched Renyi
DPI theorem is
`QIT.State.sandwichedRenyiPSDReferenceE_dataProcessing_channel_ge_of_half_le_lt_one_or_one_lt`
in `QIT.Information.Renyi.FrankLieb.DPI`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

namespace State
namespace RenyiDPI
namespace Statement

/-- Full-rank state-level sandwiched Renyi data-processing statement with a
general input-output channel `Φ : Channel a b`.

This is still weaker than the public source theorem for `sandwiched-renyi-dpi`:
the source statement allows a positive semidefinite reference operator `σ`, while
this local surface keeps the current full-rank `State + PosDef` domain. -/
def sandwichedRenyi_dataProcessing_channel_statement (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) : Prop :=
  sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ α (by linarith) hα_ne_one ≤
    sandwichedRenyi ρ σ hρ hσ α (by linarith) hα_ne_one

end Statement
end RenyiDPI
end State

end

end QIT
