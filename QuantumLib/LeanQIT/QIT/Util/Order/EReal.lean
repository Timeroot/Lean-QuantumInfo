/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Extended-real order utilities

Small coercion lemmas for finite real optimization problems viewed in `EReal`.
-/

@[expose] public section

namespace QIT

/-- Coercion from a bounded-above real objective to `EReal` preserves its supremum. -/
theorem ereal_sSup_range_coe_eq_coe_real_sSup
    {ι : Type*} [Nonempty ι] (f : ι → ℝ)
    (hf : BddAbove (Set.range f)) :
    sSup (Set.range fun i : ι => (f i : EReal)) =
      ((sSup (Set.range f) : ℝ) : EReal) := by
  let S : Set (WithTop ℝ) := Set.range fun i : ι => ((f i : ℝ) : WithTop ℝ)
  have hS_nonempty : S.Nonempty := Set.range_nonempty _
  have hS_bdd : BddAbove S := ⟨⊤, by intro y _hy; exact le_top⟩
  have htop : sSup S = ((sSup (Set.range f) : ℝ) : WithTop ℝ) := by
    have h := WithTop.coe_sSup' (s := Set.range f) hf
    have himage : ((fun a : ℝ => (a : WithTop ℝ)) '' Set.range f) = S := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨f i, ⟨i, rfl⟩, rfl⟩
    rw [himage] at h
    exact h.symm
  have hbot := WithBot.coe_sSup' (s := S) hS_nonempty hS_bdd
  have hrange : (Set.range fun i : ι => (f i : EReal)) =
      ((fun a : WithTop ℝ => (a : WithBot (WithTop ℝ))) '' S) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(f i : WithTop ℝ), ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [hrange]
  calc
    sSup ((fun a : WithTop ℝ => (a : WithBot (WithTop ℝ))) '' S) =
        ((sSup S : WithTop ℝ) : WithBot (WithTop ℝ)) := hbot.symm
    _ = (((sSup (Set.range f) : ℝ) : WithTop ℝ) : WithBot (WithTop ℝ)) := by
      rw [htop]

end QIT
