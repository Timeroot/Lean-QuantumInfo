/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.CompletePartialOrder

--Can this be rewritten more generally? For `finiteness` to work, I don't know how.
--PR'ed in #33105
@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem ite_eq_top {α : Type*} [Top α] (h : Prop) [Decidable h] {x y : α} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    (if h then x else y) ≠ ⊤ := by
  split <;> assumption

section subtype_val_iSup

variable {ι α : Type*} [i : Nonempty ι] [ConditionallyCompleteLattice α]
  {f : ι → α} {a b : α} [Fact (a ≤ b)]

/- This isn't marked as `simp` because rewriting from a sup over a `CompleteLattice` into a
`ConditionallyCompleteLattice` would, pretty often, be undesirable. -/
theorem subtype_val_iSup (h : ∀ i, f i ∈ Set.Icc a b) :
    (⨆ i, (⟨f i, h i⟩ : ↑(Set.Icc a b))).val = ⨆ i, f i := by
  simp only [iSup, sSup, Set.range_eq_empty_iff, not_isEmpty_of_nonempty, reduceDIte]
  congr 1; ext1
  simp

theorem subtype_val_iSup' (h : ∀ i, f i ∈ Set.Icc a b) :
    ⨆ i, (⟨f i, h i⟩ : ↑(Set.Icc a b)) =
      ⟨⨆ i, f i, ⟨(h i.some).1.trans (le_ciSup ⟨b, by intro; grind⟩ _), ciSup_le (h ·|>.2)⟩⟩ := by
  rw [Subtype.eq_iff, subtype_val_iSup]

/- This isn't marked as `simp` because rewriting from a sup over a `CompleteLattice` into a
`ConditionallyCompleteLattice` would, pretty often, be undesirable. -/
theorem subtype_val_iInf (h : ∀ i, f i ∈ Set.Icc a b) :
    (⨅ i, (⟨f i, h i⟩ : ↑(Set.Icc a b))).val = ⨅ i, f i := by
  simp only [iInf, sInf, Set.range_eq_empty_iff, not_isEmpty_of_nonempty, reduceDIte]
  congr 1; ext1
  simp

theorem subtype_val_iInf' (h : ∀ i, f i ∈ Set.Icc a b) :
    ⨅ i, (⟨f i, h i⟩ : ↑(Set.Icc a b)) =
      ⟨⨅ i, f i, ⟨le_ciInf (h ·|>.1), (ciInf_le ⟨a, by intro; grind⟩ _).trans (h i.some).2⟩⟩ := by
  rw [Subtype.eq_iff, subtype_val_iInf]

end subtype_val_iSup

--PR'ed in #33106
@[simp]
theorem Real.log_comp_exp : log ∘ exp = _root_.id := by
  ext
  simp

open scoped ENNReal Topology in
/-- Analogous to `bdd_le_mul_tendsto_zero`, for `ENNReal` (which otherwise lacks a continuous
multiplication function). The product of a sequence that tends to zero with any bounded sequence
also tends to zero. -/
protected lemma ENNReal.bdd_le_mul_tendsto_zero
  {α : Type*} {l : Filter α} {f g : α → ℝ≥0∞} {b : ℝ≥0∞} (hb : b ≠ ⊤)
  (hf : l.Tendsto f (𝓝 0)) (hg : ∀ᶠ (x : α) in l, g x ≤ b) :
    l.Tendsto (fun x ↦ f x * g x) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero] at hf ⊢
  intro ε hεpos
  by_cases hb_pos : 0 < b
  · filter_upwards [hf (ε / b) (by simp [hb, hεpos.ne']), hg] with x hx₁ hx₂
    grw [hx₁, hx₂, ENNReal.div_mul_cancel hb_pos.ne' hb]
  · filter_upwards [hg] with x hx
    grind [not_lt, nonpos_iff_eq_zero, mul_zero, zero_le]

--PULLOUT: Belongs in Mathlib/Algebra/Order/Group/Pointwise/CompleteLattice.lean
-- (after appropriately generalizing to MulPosMono)
open scoped Pointwise in
theorem csInf_mul_nonneg {s t : Set ℝ}
  (hs₀ : s.Nonempty) (hs₁ : ∀ x ∈ s, 0 ≤ x) (ht₀ : t.Nonempty) (ht₁ : ∀ x ∈ t, 0 ≤ x) :
    sInf (s * t) = sInf s * sInf t := by
  apply le_antisymm
  · set a := sInf s
    set b := sInf t
    have h_eps : ∀ ε > 0, ∃ x ∈ s, x < a + ε ∧ ∃ y ∈ t, y < b + ε := by
      intro ε ε_pos
      obtain ⟨x, hx₁, hx₂⟩ := exists_lt_of_csInf_lt hs₀ (lt_add_of_pos_right a ε_pos)
      obtain ⟨y, hy₁, hy₂⟩ := exists_lt_of_csInf_lt ht₀ (lt_add_of_pos_right b ε_pos)
      exact ⟨x, hx₁, hx₂, y, hy₁, hy₂⟩
    have h_prod_eps : ∀ ε > 0, ∃ x ∈ s, ∃ y ∈ t, x * y < (a + ε) * (b + ε) := by
      intro ε hε
      obtain ⟨x, hx₁, hx₂, y, hy₁, hy₂⟩ := h_eps ε hε
      exact ⟨x, hx₁, y, hy₁, by nlinarith [hs₁ x hx₁, ht₁ y hy₁]⟩
    have h_lim : Filter.Tendsto (fun ε => (a + ε) * (b + ε)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (a * b)) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by continuity) _ _ (by norm_num))
    apply le_of_tendsto_of_tendsto tendsto_const_nhds h_lim
    filter_upwards [self_mem_nhdsWithin] with ε hε
    specialize h_prod_eps ε hε
    choose x hx y hy using h_prod_eps
    refine le_trans ?_ hy.right.le
    refine csInf_le ⟨0, ?_⟩ ?_
    · rintro x ⟨u, hu, v, hv, rfl⟩
      exact mul_nonneg (hs₁ u hu) (ht₁ v hv)
    · exact ⟨_, hx, _, hy.left, rfl⟩
  · apply le_csInf (hs₀.mul ht₀)
    rintro _ ⟨x, hx, y, hy, rfl⟩
    apply mul_le_mul
    · exact csInf_le ⟨0, hs₁⟩ hx
    · exact csInf_le ⟨0, ht₁⟩ hy
    · exact Real.sInf_nonneg ht₁
    · exact hs₁ x hx
