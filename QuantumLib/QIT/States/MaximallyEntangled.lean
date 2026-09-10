/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Core.Pure
public import QuantumLib.QIT.States.MaximallyMixed

/-!
# Canonical maximally entangled states

The canonical bipartite ket and its normalized state are defined from
a finite basis equivalence.  Their marginal identities are foundation-level
facts, independent of any communication protocol.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
open Matrix

noncomputable section
universe u v

open QIT

namespace Ket

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Nonempty a] [Fintype b] [DecidableEq b]

/-- The normalized vector with equal amplitudes on the graph of `pairing`. -/
def maximallyEntangled (pairing : a ≃ b) : Ket (a × b) :=
  Ket.ofRankOne
    (fun x => if pairing x.1 = x.2 then ((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹) else 0) <| by
    rw [rankOneMatrix_trace]
    have hcard_pos : 0 < (Fintype.card a : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    have hsqrt_ne : Real.sqrt (Fintype.card a : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 hcard_pos)
    calc
      (fun x : a × b =>
          (if pairing x.1 = x.2 then ((Real.sqrt (Fintype.card a : ℝ))⁻¹ : ℂ) else 0)) ⬝ᵥ
          (fun x : a × b =>
            star (if pairing x.1 = x.2 then
              ((Real.sqrt (Fintype.card a : ℝ))⁻¹ : ℂ) else 0)) =
          ∑ i : a, ∑ j : b,
            (if pairing i = j then
              (((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹) *
                (((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹))) else 0) := by
        simp [dotProduct, Fintype.sum_prod_type]
      _ = ∑ i : a,
            (((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹) *
              (((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_eq_single (pairing i)]
        · simp
        · intro j _ hj
          have hne : pairing i ≠ j := fun h => hj h.symm
          simp [hne]
        · simp
      _ = (Fintype.card a : ℂ) *
            (((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹) *
              (((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹))) := by
        simp
      _ = 1 := by
        have hsqrtC_ne : (Real.sqrt (Fintype.card a : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast hsqrt_ne
        field_simp [hsqrtC_ne]
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow]
        exact congrArg Complex.ofReal (Real.sq_sqrt hcard_pos.le).symm

omit [DecidableEq a] in
theorem maximallyEntangled_vec (pairing : a ≃ b) (x : a × b) :
    (maximallyEntangled pairing).vec x =
      if pairing x.1 = x.2 then
        ((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹)
      else 0 :=
  rfl

theorem maximallyEntangled_matrix (pairing : a ≃ b) :
    (maximallyEntangled pairing).state.m =
      rankOneMatrix (maximallyEntangled pairing).vec := by
  rw [state_matrix]

end Ket

namespace MState

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Nonempty a] [Fintype b] [DecidableEq b]

/-- The normalized state associated with the canonical maximally entangled
ket. -/
def maximallyEntangled (pairing : a ≃ b) : MState (a × b) :=
  (Ket.maximallyEntangled pairing).state

@[simp]
theorem maximallyEntangled_matrix (pairing : a ≃ b) :
    (maximallyEntangled pairing).m =
      (Ket.maximallyEntangled pairing).state.m :=
  rfl

end MState

namespace Ket

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Nonempty a] [Fintype b] [DecidableEq b]

/-- The first marginal of the canonical maximally entangled vector is
maximally mixed. -/
theorem maximallyEntangled_traceRight (pairing : a ≃ b) :
    (maximallyEntangled pairing).state.traceRight =
      (MState.uniform : MState a) := by
  apply MState.ext
  ext x y
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hsqrt_ne : (Real.sqrt (Fintype.card a : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hcard_pos))
  have hcoef :
      ((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹ *
          star ((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹)) =
        (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [star_inv₀]
    simp
    field_simp [hsqrt_ne]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow]
    exact congrArg Complex.ofReal (Real.sq_sqrt hcard_pos.le).symm
  have hcoef' :
      ((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹ *
          ((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹)) =
        (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) := by
    simpa using hcoef
  by_cases hxy : x = y
  · subst y
    simp [Matrix.traceRight, Ket.state,
      maximallyEntangled, hcoef']
  · have hyx : ¬ y = x := fun h => hxy h.symm
    simp [Matrix.traceRight, Ket.state,
      maximallyEntangled, hxy, hyx]

/-- The second marginal of the canonical maximally entangled vector is
maximally mixed. -/
theorem maximallyEntangled_traceLeft (pairing : a ≃ b) [Nonempty b] :
    (maximallyEntangled pairing).state.traceLeft =
      (MState.uniform : MState b) := by
  apply MState.ext
  ext x y
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hsqrt_ne : (Real.sqrt (Fintype.card a : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hcard_pos))
  have hcoef :
      ((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹ *
          star ((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹)) =
        (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [star_inv₀]
    simp
    field_simp [hsqrt_ne]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow]
    exact congrArg Complex.ofReal (Real.sq_sqrt hcard_pos.le).symm
  have hcoef' :
      ((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹ *
          ((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹)) =
        (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) := by
    simpa using hcoef
  by_cases hxy : x = y
  · subst y
    simp [Matrix.traceLeft, Ket.state,
      maximallyEntangled]
    rw [Finset.sum_eq_single (pairing.symm x)]
    · simp [pairing.apply_symm_apply]
      rw [hcoef']
      norm_num
      rw [Fintype.card_congr pairing]
    · intro j _ hj
      have hne : pairing j ≠ x := fun h =>
        hj (pairing.injective (h.trans (pairing.apply_symm_apply x).symm))
      simp [hne]
    · simp
  · have hyx : ¬ y = x := fun h => hxy h.symm
    simp [Matrix.traceLeft, Ket.state,
      maximallyEntangled]
    rw [Finset.sum_eq_single (pairing.symm x)]
    · simp [hxy]
    · intro j _ hj
      have hne : pairing j ≠ x := fun h =>
        hj (pairing.injective (h.trans (pairing.apply_symm_apply x).symm))
      simp [hne]
    · simp

end Ket
