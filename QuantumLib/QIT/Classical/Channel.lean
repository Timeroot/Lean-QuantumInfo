/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Classical.Distribution
public import QuantumInfo.ClassicalInfo.Channel

/-!
# Nonnegative-real transition weights of a discrete memoryless channel

`DMChannel` stores the output distribution of each input symbol as a
`ProbDistribution`, whose weights live in `Prob`. The typicality and coding
arguments need those weights as nonnegative reals, so `DMChannel.nnprob` reads
them through `ProbDistribution.nnprob` and `DMChannel.ofNNReal` builds a channel
from a transition matrix of nonnegative reals.
-/

@[expose] public section

open scoped BigOperators NNReal

namespace DMChannel

universe u v

variable {α : Type u} {β : Type v} [Fintype β]

/-- The weight a channel gives an output symbol, as a nonnegative real. -/
def nnprob (K : DMChannel α β) (x : α) (z : β) : ℝ≥0 :=
  (K.symb_dist x).nnprob z

theorem coe_nnprob (K : DMChannel α β) (x : α) (z : β) :
    (K.nnprob x z : ℝ) = K.symb_dist x z :=
  rfl

/-- The nonnegative-real weights of each output distribution sum to one. -/
theorem sum_nnprob (K : DMChannel α β) (x : α) : ∑ z, K.nnprob x z = 1 :=
  (K.symb_dist x).sum_nnprob

theorem nnprob_le_one (K : DMChannel α β) (x : α) (z : β) : K.nnprob x z ≤ 1 :=
  (K.symb_dist x).nnprob_le_one z

/-- The channel with the given nonnegative-real transition weights. -/
@[reducible]
def ofNNReal (f : α → β → ℝ≥0) (hf : ∀ x, ∑ z, f x z = 1) : DMChannel α β :=
  ⟨fun x => .ofNNReal (f x) (hf x)⟩

@[simp]
theorem nnprob_ofNNReal (f : α → β → ℝ≥0) (hf : ∀ x, ∑ z, f x z = 1) :
    (ofNNReal f hf).nnprob = f :=
  rfl

end DMChannel
