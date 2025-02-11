import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Finprod

/- Other facts that belong in Mathlib that don't fit nicely
anywhere else. -/

open BigOperators

namespace Finset

variable [CommMonoid β]

-- in #21524
/-- Cyclically permute 3 nested instances of `Finset.prod`. -/
@[to_additive]
theorem prod_comm_3 {s : Finset γ} {t : Finset α} {u : Finset δ} {f : γ → α → δ → β} :
    (∏ x ∈ s, ∏ y ∈ t, ∏ z ∈ u, f x y z) = ∏ z ∈ u, ∏ x ∈ s, ∏ y ∈ t, f x y z := by
  simp_rw [prod_comm (s := t), prod_comm (s := s)]

end Finset
