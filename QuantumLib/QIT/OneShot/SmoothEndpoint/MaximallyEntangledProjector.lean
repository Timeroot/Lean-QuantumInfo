/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.OneShot.SmoothEndpoint.Order
public import QuantumLib.QIT.States.MaximallyEntangled

/-!
# The maximally entangled projector across a middle register

`MState.maximallyEntangledProjectorWithMiddle b` is the canonical maximally entangled projector on
the two outer copies of `a` in `(a × b) × a`, tensored with the identity on the middle register
`b`.  Its entries are `(Fintype.card a)⁻¹` on the index pairs the projector selects and zero
elsewhere, so pairing it against an observable `O` collapses the trace to a triple sum of entries
of `O`: `trace_maximallyEntangledProjectorWithMiddle_mul` and
`trace_mul_maximallyEntangledProjectorWithMiddle` are that identity on either side.  Those are what
the SDP duality argument for the smooth endpoint quantities uses it for.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker
open Matrix

noncomputable section
universe u v

open QIT

namespace MState

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

omit [DecidableEq a] in
private theorem maximallyEntangledProjectorWithMiddle_coeff [Nonempty a] :
    (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) =
      ((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹) *
        star ((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹) := by
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hsqrt_ne : (Real.sqrt (Fintype.card a : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hcard_pos))
  rw [star_inv₀]
  simp
  field_simp [hsqrt_ne]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow]
  exact congrArg Complex.ofReal (Real.sq_sqrt hcard_pos.le)

/-- The maximally-entangled projector on the outer `A` registers, tensored
with the identity on the middle `B` register.

On `(A × B) × A`, this is the normalized canonical maximally entangled
projector `|Ω⟩⟨Ω|_{AA'}` tensored with `I_B`, then reindexed into the endpoint
register order. -/
def maximallyEntangledProjectorWithMiddle [Nonempty a] (b : Type v) [Fintype b]
    [DecidableEq b] :
    CMatrix ((a × b) × a) :=
  Matrix.reindex
    (prodABCToACBEquiv a a b)
    (prodABCToACBEquiv a a b)
    ((MState.maximallyEntangled (Equiv.refl a)).m ⊗ₖ (1 : CMatrix b))

@[simp]
theorem maximallyEntangledProjectorWithMiddle_apply [Nonempty a]
    {b : Type v} [Fintype b] [DecidableEq b] (x y : (a × b) × a) :
    maximallyEntangledProjectorWithMiddle (a := a) b x y =
      if x.1.2 = y.1.2 ∧ x.1.1 = x.2 ∧ y.1.1 = y.2 then
        (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ)
      else
        0 := by
  have hentry :
      maximallyEntangledProjectorWithMiddle (a := a) b x y =
        (MState.maximallyEntangled (Equiv.refl a)).m (x.1.1, x.2) (y.1.1, y.2) *
          (1 : CMatrix b) x.1.2 y.1.2 := by
    simp [maximallyEntangledProjectorWithMiddle, prodABCToACBEquiv,
      Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [hentry]
  by_cases hb : x.1.2 = y.1.2
  · by_cases hx : x.1.1 = x.2
    · by_cases hy : y.1.1 = y.2
      · rw [maximallyEntangledProjectorWithMiddle_coeff (a := a)]
        simp [MState.maximallyEntangled, Ket.maximallyEntangled, Ket.state,
          rankOneMatrix_apply, Matrix.one_apply, hb, hx, hy]
      · simp [MState.maximallyEntangled, Ket.maximallyEntangled, Ket.state,
          rankOneMatrix_apply, hb, hx, hy]
    · simp [MState.maximallyEntangled, Ket.maximallyEntangled, Ket.state,
        rankOneMatrix_apply, hb, hx]
  · simp [MState.maximallyEntangled, Ket.maximallyEntangled, Ket.state,
      rankOneMatrix_apply, hb]

theorem maximallyEntangledProjectorWithMiddle_posSemidef [Nonempty a] :
    (maximallyEntangledProjectorWithMiddle (a := a) b).PosSemidef := by
  simpa [maximallyEntangledProjectorWithMiddle, Matrix.reindex_apply] using
    (((MState.maximallyEntangled (Equiv.refl a)).psd).kronecker Matrix.PosSemidef.one).submatrix
      (prodABCToACBEquiv a a b).symm

private theorem sum_projector_delta_state_full {α : Type*} {β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (r : ℂ) (f : α → β → α → α → β → α → ℂ) :
    (∑ x : α, ∑ y : β, ∑ u : α, ∑ z : α, ∑ v : β, ∑ w : α,
      if y = v ∧ x = u ∧ z = w then r * f x y u z v w else 0) =
      r * (∑ x : α, ∑ z : α, ∑ y : β, f x y x z y z) := by
  calc
    (∑ x : α, ∑ y : β, ∑ u : α, ∑ z : α, ∑ v : β, ∑ w : α,
      if y = v ∧ x = u ∧ z = w then r * f x y u z v w else 0) =
        ∑ x : α, ∑ y : β, ∑ z : α, r * f x y x z y z := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      calc
        (∑ u : α, ∑ z : α, ∑ v : β, ∑ w : α,
          if y = v ∧ x = u ∧ z = w then r * f x y u z v w else 0) =
            ∑ z : α, ∑ u : α, ∑ v : β, ∑ w : α,
              if y = v ∧ x = u ∧ z = w then r * f x y u z v w else 0 := by
          rw [Finset.sum_comm]
        _ = ∑ z : α, r * f x y x z y z := by
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.sum_eq_single x]
          · rw [Finset.sum_eq_single y]
            · rw [Finset.sum_eq_single z]
              · simp
              · intro w _ hw
                have hzw : z ≠ w := hw.symm
                simp [hzw]
              · intro hnot
                simp at hnot
            · intro v _ hv
              have hyv : y ≠ v := hv.symm
              simp [hyv]
            · intro hnot
              simp at hnot
          · intro u _ hu
            have hxu : x ≠ u := hu.symm
            simp [hxu]
          · intro hnot
            simp at hnot
    _ = ∑ x : α, ∑ z : α, ∑ y : β, r * f x y x z y z := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = r * (∑ x : α, ∑ z : α, ∑ y : β, f x y x z y z) := by
      simp [Finset.mul_sum]

private theorem sum_projector_delta_state_full_right {α : Type*} {β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (r : ℂ) (f : α → β → α → α → β → α → ℂ) :
    (∑ x : α, ∑ y : β, ∑ u : α, ∑ z : α, ∑ v : β, ∑ w : α,
      if z = w ∧ v = y ∧ x = u then r * f x y u z v w else 0) =
      r * (∑ x : α, ∑ z : α, ∑ y : β, f x y x z y z) := by
  calc
    (∑ x : α, ∑ y : β, ∑ u : α, ∑ z : α, ∑ v : β, ∑ w : α,
      if z = w ∧ v = y ∧ x = u then r * f x y u z v w else 0) =
        ∑ x : α, ∑ y : β, ∑ z : α, r * f x y x z y z := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      calc
        (∑ u : α, ∑ z : α, ∑ v : β, ∑ w : α,
          if z = w ∧ v = y ∧ x = u then r * f x y u z v w else 0) =
            ∑ z : α, ∑ u : α, ∑ v : β, ∑ w : α,
              if z = w ∧ v = y ∧ x = u then r * f x y u z v w else 0 := by
          rw [Finset.sum_comm]
        _ = ∑ z : α, r * f x y x z y z := by
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.sum_eq_single x]
          · rw [Finset.sum_eq_single y]
            · rw [Finset.sum_eq_single z]
              · simp
              · intro w _ hw
                have hzw : z ≠ w := hw.symm
                simp [hzw]
              · intro hnot
                simp at hnot
            · intro v _ hv
              simp [hv]
            · intro hnot
              simp at hnot
          · intro u _ hu
            have hxu : x ≠ u := hu.symm
            simp [hxu]
          · intro hnot
            simp at hnot
    _ = ∑ x : α, ∑ z : α, ∑ y : β, r * f x y x z y z := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = r * (∑ x : α, ∑ z : α, ∑ y : β, f x y x z y z) := by
      simp [Finset.mul_sum]

theorem trace_maximallyEntangledProjectorWithMiddle_mul [Nonempty a]
    (O : CMatrix ((a × b) × a)) :
    (((maximallyEntangledProjectorWithMiddle (a := a) b) * O).trace) =
      (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) *
        (∑ i : a, ∑ i' : a, ∑ j : b, O ((i', j), i') ((i, j), i)) := by
  classical
  simpa [Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type] using
    sum_projector_delta_state_full
      (α := a) (β := b)
      ((((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ))
      (fun x y u z v w => O ((z, v), w) ((x, y), u))

theorem trace_mul_maximallyEntangledProjectorWithMiddle [Nonempty a]
    (O : CMatrix ((a × b) × a)) :
    ((O * (maximallyEntangledProjectorWithMiddle (a := a) b)).trace) =
      (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) *
        (∑ i : a, ∑ i' : a, ∑ j : b, O ((i, j), i) ((i', j), i')) := by
  classical
  simpa [Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, mul_comm,
    and_assoc, and_left_comm, and_comm] using
    sum_projector_delta_state_full_right
      (α := a) (β := b)
      ((((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ))
      (fun x y u z v w => O ((x, y), u) ((z, v), w))

end MState
