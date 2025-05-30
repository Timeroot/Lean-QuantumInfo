import QuantumInfo.ForMathlib.HermitianMat.Basic

import Mathlib.Analysis.Convex.Contractible

/-!
Theorems about `HermitianMat`s that have to do with the topological structure. Pretty much everything here will
assume these are matrices over ℂ, but changes to upgrade this to other types are welcome.
-/

namespace HermitianMat
open ComplexOrder

variable {d : Type*} [Fintype d]

--Using `#guard_msgs(drop info) in #synth` to check that certain instances already exist here

#guard_msgs(drop info) in
#synth ContinuousAdd (HermitianMat d ℂ)

instance ContinuousSMul : ContinuousSMul ℝ (HermitianMat d ℂ) := by
  sorry

instance OrderedSMul : OrderedSMul ℝ (HermitianMat d ℂ) := by
  sorry

#guard_msgs(drop info) in
#synth ContractibleSpace (HermitianMat d ℂ)

/-- The PSD matrices that are `≤ 1` are a compact set. More generally, this is true of any closed interval,
but stating that is a bit different because of how numerals are treated. The `0` and `1` here are already
directly matrices, putting in an `(a : ℝ) ≤ m ∧ m ≤ (b : ℝ)` involves casts. But that theorem should follow
easily from this.
-/
theorem unitInterval_IsCompact [DecidableEq d] : IsCompact {m : HermitianMat d ℂ | 0 ≤ m ∧ m ≤ 1} := by
  sorry

@[fun_prop] --fun_prop can actually prove this, should I leave this on or not?
theorem inner_bilinForm_Continuous (A : HermitianMat d ℂ) : Continuous ⇑(HermitianMat.inner_BilinForm A) :=
  LinearMap.continuous_of_finiteDimensional _

@[fun_prop]
theorem inner_continuous (A : HermitianMat d ℂ) : Continuous (A.inner) := by
  exact inner_bilinForm_Continuous A
