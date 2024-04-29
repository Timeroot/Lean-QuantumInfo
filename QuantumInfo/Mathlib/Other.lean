import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Finprod

/- Other facts that belong in Mathlib that don't fit nicely
anywhere else. -/

open BigOperators

namespace Finset

variable [CommMonoid β]

/-- Cyclically permute 3 nested instances of `Finset.sum`. -/
@[to_additive]
theorem prod_comm_3 {s : Finset γ} {t : Finset α} {u : Finset δ} {f : γ → α → δ → β} :
    (∏ x in s, ∏ y in t, ∏ z in u, f x y z) = ∏ z in u, ∏ x in s, ∏ y in t, f x y z := by
  nth_rewrite 2 [prod_comm]
  congr 1
  funext
  exact prod_comm

end Finset
