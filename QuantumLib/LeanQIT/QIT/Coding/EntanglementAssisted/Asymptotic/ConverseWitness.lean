/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Asymptotic.ProtocolLifting

/-!
# Asymptotic converse witness normalization

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

/-- Source-consistent converse witness family from eventual `n`-use
log-cardinality upper bounds.

This is the rate-normalization layer for the Khatri--Wilde asymptotic upper
bound and strong-converse route, using the source error range
`ε ∈ [0, 1)` from the one-shot upper bounds.  The output is a strict rate
estimate, matching the operational strong-converse interface. -/
theorem entanglementAssisted_sourceConverseWitnessFamily_of_logCardUpperBounds
    (h :
      ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 ≤ ε → ε < 1 →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          ∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M],
            ∀ (EA : Type u) [Fintype EA] [DecidableEq EA],
              ∀ (EB : Type u) [Fintype EB] [DecidableEq EB],
                ∀ C : EntanglementAssistedClassicalCode N n M EA EB,
                  C.maxErrorAtMost ε →
                    log2 (Fintype.card M : ℝ) ≤
                      (n : ℝ) * (N.entanglementAssistedInformation + η)) :
    EntanglementAssistedSourceConverseWitnessFamily N where
  rate_lt := by
    intro η hη ε hε_nonneg hε_lt_one
    have hhalf : 0 < η / 2 := half_pos hη
    obtain ⟨N0, hN0⟩ := h (η / 2) hhalf ε hε_nonneg hε_lt_one
    refine ⟨max 1 N0, ?_⟩
    intro n hn M _hMfin _hMdec _hMnonempty EA _hEAfin _hEAdec EB _hEBfin _hEBdec C hC
    have hn_pos : 0 < n :=
      lt_of_lt_of_le (by norm_num : 0 < 1) (le_trans (Nat.le_max_left 1 N0) hn)
    have hnN0 : n ≥ N0 :=
      le_trans (Nat.le_max_right 1 N0) hn
    have hrate_le :
        C.rate ≤ N.entanglementAssistedInformation + η / 2 :=
      C.rate_le_of_log_card_le_mul hn_pos (hN0 n hnN0 M EA EB C hC)
    have hstrict :
        N.entanglementAssistedInformation + η / 2 <
          N.entanglementAssistedInformation + η := by
      linarith
    exact lt_of_le_of_lt hrate_le hstrict

end Channel

end

end QIT
