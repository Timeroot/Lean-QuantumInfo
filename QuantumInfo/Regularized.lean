/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.Superadditive
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.MonotoneConvergence

/-! Definition of "Regularized quantities" as are common in information theory,
from one-shot versions, and good properties coming from Fekete's lemma.
-/

variable {T : Type*} [ConditionallyCompleteLattice T]

/-- An `InfRegularized` value is the lim sup of value at each natural number, but requires
 a proof of lower- and upper-bounds to be defined. -/
noncomputable def InfRegularized (fn : ℕ → T) {lb ub : T}
    (_ : ∀ n, lb ≤ fn n) (_ : ∀ n, fn n ≤ ub) : T :=
  Filter.atTop.liminf fn

/-- A `SupRegularized` value is the lim sup of value at each natural number, but requires
 a proof of lower- and upper-bounds to be defined. -/
noncomputable def SupRegularized (fn : ℕ → T) {lb ub : T}
    (_ : ∀ n, lb ≤ fn n) (_ : ∀ n, fn n ≤ ub) : T :=
  Filter.atTop.limsup fn

namespace InfRegularized

variable {fn : ℕ → T} {_lb _ub : T} {hl : ∀ n, _lb ≤ fn n} {hu : ∀ n, fn n ≤ _ub}

/-- The `InfRegularized` value is also lower bounded. -/
theorem lb : _lb ≤ InfRegularized fn hl hu := by
  sorry

/-- The `InfRegularized` value is also upper bounded. -/
theorem ub : InfRegularized fn hl hu ≤ _ub := by
  sorry

/-- For `Antitone` functions, the `InfRegularized` is the supremum of values. -/
theorem anti_inf (h : Antitone fn) :
    InfRegularized fn hl hu = sInf (Set.range fn) := by
  sorry

/-- For `Antitone` functions, the `InfRegularized` is lower bounded by
  any particular value. -/
theorem anti_ub (h : Antitone fn) : ∀ n, InfRegularized fn hl hu ≤ fn n := by
  sorry

end InfRegularized

namespace SupRegularized

variable {fn : ℕ → T} {_lb _ub : T} {hl : ∀ n, _lb ≤ fn n} {hu : ∀ n, fn n ≤ _ub}

/-- The `SupRegularized` value is also lower bounded. -/
theorem lb : _lb ≤ SupRegularized fn hl hu := by
  sorry

/-- The `SupRegularized` value is also upper bounded. -/
theorem ub : SupRegularized fn hl hu ≤ _ub := by
  sorry

/-- For `Monotone` functions, the `SupRegularized` is the supremum of values. -/
theorem mono_sup (h : Monotone fn) :
    SupRegularized fn hl hu = sSup { fn n | n : ℕ} := by
  sorry

/-- For `Monotone` functions, the `SupRegularized` is lower bounded by
  any particular value. -/
theorem mono_lb (h : Monotone fn) : ∀ n, fn n ≤ SupRegularized fn hl hu := by
  sorry

end SupRegularized

section real

variable {fn : ℕ → ℝ} {_lb _ub : ℝ} {hl : ∀ n, _lb ≤ fn n} {hu : ∀ n, fn n ≤ _ub}

theorem InfRegularized.to_SupRegularized : InfRegularized fn hl hu = -SupRegularized (-fn ·)
    (lb := -_ub) (ub := -_lb) (neg_le_neg_iff.mpr <| hu ·) (neg_le_neg_iff.mpr <| hl ·) := by
  sorry

theorem SupRegularized.to_InfRegularized : SupRegularized fn hl hu = -InfRegularized (-fn ·)
    (lb := -_ub) (ub := -_lb) (neg_le_neg_iff.mpr <| hu ·) (neg_le_neg_iff.mpr <| hl ·) := by
  sorry

/-- For `Antitone` functions, the value `Filter.Tendsto` the `InfRegularized` value. -/
theorem InfRegularized.anti_tendsto (h : Antitone fn) :
    Filter.Tendsto fn .atTop (nhds (InfRegularized fn hl hu)) := by
  convert tendsto_atTop_ciInf h ⟨_lb, fun _ ⟨a,b⟩ ↦ b ▸ hl a⟩
  rw [InfRegularized.anti_inf h, iInf.eq_1]


variable {f₁ : ℕ → ℝ} {_lb _ub : ℝ} {hl : ∀ n, _lb ≤ fn n} {hu : ∀ n, fn n ≤ _ub}

theorem InfRegularized.of_Subadditive (hf : Subadditive (fun n ↦ fn n * n))
    :
    hf.lim = InfRegularized fn hl hu := by
  have h₁ := hf.tendsto_lim (by
    use min 0 _lb
    rw [mem_lowerBounds]
    rintro x ⟨y,(rfl : _ / _ = _)⟩
    rcases y with (_|n)
    · simp
    · rw [inf_le_iff]
      convert Or.inr (hl (n+1))
      field_simp
  )
  apply tendsto_nhds_unique h₁
  have := InfRegularized.anti_tendsto (fn := fn) (hl := hl) (hu := hu) (sorry)
  sorry
