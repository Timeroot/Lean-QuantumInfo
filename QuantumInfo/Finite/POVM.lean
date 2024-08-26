import QuantumInfo.Finite.CPTPMap

/-! # Positive Operator-Valued Measures

A Positive Operator-Valued Measures, or POVM, is the most general notion of a quantum "measurement":
a collection of positive semidefinite (PSD) operators that sum to the identity. These induce a distribution,
`POVM.measure`, of measurement outcomes; and they induce a CPTP map, `POVM.measurement_map`, which changes the state
but adds learned information.

Developing this theory is important if one wants to discuss classical information across quantum channels, as POVMs
are the route to get back to classical information (a `Distribution` of outcomes).

TODO: They can also evolve under CPTP maps themselves (the Heisenberg picture of quantum evolution), they might commute
with each other or not, they might be projective or not.
-/
open BigOperators
open ComplexOrder
open Matrix
noncomputable section

/-- A POVM is a (finite) collection of PSD matrices on the same Hilbert space
 that sum to the identity. Here `X` indexes the matrices, and `d` is the space
 dimension.

 Applied to an `MState` on that on that space with
 `POVM.measure`, this produces a distribution of outcomes indexed by the same
 type as the collection.

 This measurement action can be composed with `MState.of_classical`, in which
 case it is equal to a CPTP map `measurement_map`. -/
structure POVM (X : Type*) (d : Type*) [Fintype X] [Fintype d] [DecidableEq d] where
  mats : X → Matrix d d ℂ
  pos : ∀ x, (mats x).PosSemidef
  normalized : ∑ x, mats x = (1 : Matrix d d ℂ)

namespace POVM

variable {X : Type*} {d : Type*} [Fintype X] [Fintype d] [DecidableEq d] [DecidableEq X]

/-- The act of measuring is a quantum channel, that maps a `d`-dimensional quantum
state to an `d × X`-dimensional quantum-classical state. -/
def measurement_map (Λ : POVM X d) : CPTPMap d (d × X) where
  map := open Kronecker in {
    toFun := fun ρ ↦ ∑ (i : X), (Λ.mats i).inner ρ • (Λ.mats i ⊗ₖ 1)
    map_add' := by simp [Matrix.inner, mul_add, trace_add, add_smul, Finset.sum_add_distrib]
    map_smul' := by simp [Matrix.inner, MulAction.mul_smul, Finset.smul_sum]
  }
  trace_preserving := sorry
  completely_pos := sorry

/-- A POVM leads to a distribution of outcomes on any given mixed state ρ. -/
def measure (Λ : POVM X d) (ρ : MState d) : Distribution X where
  val := fun x ↦ ⟨((Λ.mats x).inner ρ.m).re,
    ⟨And.left $ Complex.nonneg_iff.1 $ (Λ.pos x).inner_ge_zero ρ.pos,
    by
    -- That each observation probability is at most 1.
    -- ρ.m.inner (∑ y, Λ.mats y) = ρ.m.inner 1 = ρ.m.trace = 1
    -- ρ.m.inner (∑ y ≠ x, Λ.mats y) = ρ.m.inner (sum of PSD) ≥ 0
    -- ρ.m.inner x = ρ.m.inner (∑ y, Λ.mats y) - ρ.m.inner (∑ y ≠ x, Λ.mats y) ≤ 1 - 0 ≤ 1
    sorry
    ⟩⟩
  property := by
    simp [← Complex.re_sum, Matrix.inner, ← trace_sum,
    ← Finset.sum_mul, ← conjTranspose_sum, Λ.normalized, ρ.tr]

/-- The quantum-classical `POVM.measurement_map`, gives a marginal on the right equal to `POVM.measure`.-/
theorem measure_eq_measurement_map (Λ : POVM X d) (ρ : MState d) :
    (Λ.measurement_map ρ).traceLeft = MState.ofClassical (Λ.measure ρ) :=
  sorry

end POVM
