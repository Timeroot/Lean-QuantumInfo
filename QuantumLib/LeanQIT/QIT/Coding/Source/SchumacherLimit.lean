/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Source.Schumacher
public import QIT.Coding.Source.SchumacherConverse
public import QIT.Coding.Source.SchumacherDirect

/-!
# Schumacher data-compression limit equality

The operational quantum data-compression limit of an i.i.d. quantum source `ρ`
equals its von Neumann entropy `S(ρ)` [Wilde2011Qst, qit-notes.tex:31275-31690].
This combines the direct achievability (`SchumacherDirect`) and the converse
(`SchumacherConverse`): `S(ρ)` is the least achievable Schumacher compression
rate, so the optimal (infimum) rate is exactly `S(ρ)`.
-/

@[expose] public section

namespace QIT

open scoped Real

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

namespace State

/-- The optimal (infimum) achievable Schumacher compression rate. -/
noncomputable def schumacherCompressionRate (ρ : State a) : ℝ :=
  sInf {R : ℝ | ρ.IsAchievableSchumacherRate R}

/-- The von Neumann entropy is the least achievable Schumacher compression rate.

`S(ρ)` is itself achievable (`schumacher_direct_achievable`) and every
achievable rate is at least `S(ρ)` (`schumacher_converse`). -/
theorem schumacherRate_isLeast_achievableRates (ρ : State a) :
    IsLeast {R : ℝ | ρ.IsAchievableSchumacherRate R} ρ.schumacherRate :=
  ⟨schumacher_direct_achievable ρ, fun _R hR => schumacher_converse ρ _ hR⟩

/-- **Schumacher quantum data-compression limit equality.** The optimal
asymptotic compression rate of an i.i.d. quantum source with density operator
`ρ` equals its von Neumann entropy `S(ρ)` [Wilde2011Qst, qit-notes.tex:31275-31690]. -/
theorem schumacher_data_compression_limit (ρ : State a) :
    ρ.schumacherCompressionRate = ρ.schumacherRate := by
  set S : Set ℝ := {R | ρ.IsAchievableSchumacherRate R} with hSdef
  have hleast := ρ.schumacherRate_isLeast_achievableRates
  have hne : S.Nonempty := ⟨ρ.schumacherRate, hleast.1⟩
  have hbdd : BddBelow S := ⟨ρ.schumacherRate, hleast.2⟩
  -- `sInf S ≤ S(ρ)` because `S(ρ) ∈ S`.
  have h1 : sInf S ≤ ρ.schumacherRate := csInf_le hbdd hleast.1
  -- `S(ρ) ≤ sInf S` because `S(ρ)` is a lower bound of the nonempty set `S`.
  have h2 : ρ.schumacherRate ≤ sInf S := le_csInf hne hleast.2
  exact le_antisymm h1 h2

end State

end

end QIT
