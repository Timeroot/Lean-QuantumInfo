/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Renyi.ConditionalRenyi

/-!
# Sandwiched Renyi DPI statement surface

Planning-only statement surface for the sandwiched Renyi data-processing
inequality at general channel arity.  This `Prop`-valued target is consumed by
local reduction theorems.  The completed public PSD-reference sandwiched Renyi
DPI theorem is
`MState.sandwichedRenyiPSDReferenceE_dataProcessing_channel_ge_of_half_le_lt_one_or_one_lt`
in `QIT.Information.Renyi.FrankLieb.DPI`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

noncomputable section
universe u v w
variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

open QIT

namespace MState
namespace RenyiDPI
namespace Statement

/-- Full-rank state-level sandwiched Renyi data-processing statement with a
general input-output channel `Φ : CPTPMap a b`.

This is still weaker than the public source theorem for `sandwiched-renyi-dpi`:
the source statement allows a positive semidefinite reference operator `σ`, while
this local surface keeps the current full-rank `MState + PosDef` domain. -/
def sandwichedRenyi_dataProcessing_channel_statement (ρ σ : MState a) (Φ : CPTPMap a b)
    (hρ : ρ.m.PosDef) (hσ : σ.m.PosDef)
    (hρΦ : (Φ ρ).m.PosDef) (hσΦ : (Φ σ).m.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) : Prop :=
  sandwichedRenyi (Φ ρ) (Φ σ) hρΦ hσΦ α (by linarith) hα_ne_one ≤
    sandwichedRenyi ρ σ hρ hσ α (by linarith) hα_ne_one

end Statement
end RenyiDPI
end MState
