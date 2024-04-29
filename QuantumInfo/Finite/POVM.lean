import QuantumInfo.Finite.CPTPMap

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

variable {X : Type*} {d : Type*} [Fintype X] [Fintype d] [DecidableEq d]

/-- The act of measuring is a quantum channel, that maps a `d`-dimensional quantum
state to an `d × X`-dimensional quantum-classical state. -/
def measurement_map (Λ : POVM X d) : CPTPMap d (d × X) :=
  CPTPMap.CPTP_of_choi_PSD_Tr (M := sorry) (sorry) (sorry)

/-- A POVM leads to a distribution of outcomes on any given mixed state ρ. -/
def measure (Λ : POVM X d) (ρ : MState d) : Distribution X where
  val := fun x ↦ ⟨ρ.m.inner (Λ.mats x),
    sorry⟩--use Matrix.PosSemidef.inner_ge_zero and inner_le_mul_trace
  property := sorry

/-- The quantum-classical `POVM.measurement_map`, gives a marginal on the right equal to `POVM.measure`.-/
theorem measure_eq_measurement_map (Λ : POVM X d) (ρ : MState d) :
    (Λ.measurement_map ρ).trace_left = MState.ofClassical (Λ.measure ρ) :=
  sorry

end POVM
