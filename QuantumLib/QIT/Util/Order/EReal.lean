/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Extended-real order utilities

Small coercion and negation lemmas for finite real optimization problems
viewed in `EReal`, including the transfer of a Sion minimax equality between a
saddle function and its negative.
-/

@[expose] public section

namespace QIT

/-- Negation changes an extended-real infimum into the corresponding supremum.

This order-theoretic bridge is used when applying Sion to the negative of a
trace bracket and then returning to the original bracket. -/
theorem ereal_neg_iInf_eq_iSup_neg {ι : Sort _} (f : ι → EReal) :
    -(⨅ i, f i) = ⨆ i, -f i := by
  have h := OrderIso.map_iInf EReal.negOrderIso f
  change OrderDual.ofDual (EReal.negOrderIso (⨅ i, f i)) = _
  rw [h]
  rfl

/-- Negation changes an extended-real supremum into the corresponding
infimum. -/
theorem ereal_neg_iSup_eq_iInf_neg {ι : Sort _} (f : ι → EReal) :
    -(⨆ i, f i) = ⨅ i, -f i := by
  have h := OrderIso.map_iSup EReal.negOrderIso f
  change OrderDual.ofDual (EReal.negOrderIso (⨆ i, f i)) = _
  rw [h]
  rfl

/-- Convert a Sion equality proved for the negative saddle function back to
the source `inf sup = sup inf` equality for the original function. -/
theorem ereal_sion_from_neg
    {ι κ : Sort _} (F : ι → κ → EReal)
    (h :
      (⨅ k : κ, ⨆ i : ι, -F i k) =
        ⨆ i : ι, ⨅ k : κ, -F i k) :
    (⨅ i : ι, ⨆ k : κ, F i k) =
      ⨆ k : κ, ⨅ i : ι, F i k := by
  have hneg := congrArg Neg.neg h
  rw [ereal_neg_iInf_eq_iSup_neg, ereal_neg_iSup_eq_iInf_neg] at hneg
  simp_rw [ereal_neg_iSup_eq_iInf_neg, ereal_neg_iInf_eq_iSup_neg, neg_neg] at hneg
  exact hneg.symm

/-- The scalar map `x ↦ -(x : EReal)` is antitone. -/
theorem antitone_ereal_neg_coe : Antitone (fun x : ℝ => -((x : EReal))) := by
  intro x y hxy
  exact EReal.neg_le_neg_iff.mpr (EReal.coe_le_coe_iff.mpr hxy)

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

/-- Coercion from a bounded-below real objective to `EReal` preserves its infimum. -/
theorem ereal_sInf_range_coe_eq_coe_real_sInf
    {ι : Type*} [Nonempty ι] (f : ι → ℝ)
    (hf : BddBelow (Set.range f)) :
    sInf (Set.range fun i : ι => (f i : EReal)) =
      ((sInf (Set.range f) : ℝ) : EReal) := by
  let S : Set (WithTop ℝ) := Set.range fun i : ι => ((f i : ℝ) : WithTop ℝ)
  have hS_bdd : BddBelow S := by
    rcases hf with ⟨lb, hlb⟩
    refine ⟨(lb : WithTop ℝ), ?_⟩
    rintro y ⟨i, rfl⟩
    exact WithTop.coe_le_coe.mpr (hlb ⟨i, rfl⟩)
  have htop : sInf S = ((sInf (Set.range f) : ℝ) : WithTop ℝ) := by
    have h := WithTop.coe_sInf' (s := Set.range f) (Set.range_nonempty f) hf
    have himage : ((fun a : ℝ => (a : WithTop ℝ)) '' Set.range f) = S := by
      ext y
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨f i, ⟨i, rfl⟩, rfl⟩
    rw [himage] at h
    exact h.symm
  have hbot := WithBot.coe_sInf' (s := S) hS_bdd
  have hrange : (Set.range fun i : ι => (f i : EReal)) =
      ((fun a : WithTop ℝ => (a : WithBot (WithTop ℝ))) '' S) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(f i : WithTop ℝ), ⟨i, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [hrange]
  calc
    sInf ((fun a : WithTop ℝ => (a : WithBot (WithTop ℝ))) '' S) =
        ((sInf S : WithTop ℝ) : WithBot (WithTop ℝ)) := hbot.symm
    _ = (((sInf (Set.range f) : ℝ) : WithTop ℝ) : WithBot (WithTop ℝ)) := by
      rw [htop]

end QIT
