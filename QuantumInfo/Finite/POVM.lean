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
noncomputable section
open BigOperators
open ComplexOrder
open Matrix

/-- A POVM is a (finite) collection of PSD matrices on the same Hilbert space
 that sum to the identity. Here `X` indexes the matrices, and `d` is the space
 dimension.

 Applied to an `MState` on that on that space with
 `POVM.measure`, this produces a distribution of outcomes indexed by the same
 type as the collection.

 This measurement action can be composed with `MState.of_classical`, in which
 case it is equal to a CPTP map `measurement_map`. -/
structure POVM (X : Type*) (d : Type*) [Fintype X] [Fintype d] [DecidableEq d] where
  mats : X → HermitianMat d ℂ
  zero_le : ∀ x, 0 ≤ (mats x)
  normalized : ∑ x, mats x = 1

namespace POVM

variable {X : Type*} {d : Type*} [Fintype X] [Fintype d] [DecidableEq d] [DecidableEq X]

/-- The act of measuring is a quantum channel, that maps a `d`-dimensional quantum
state to an `d × X`-dimensional quantum-classical state. -/
def measurement_map (Λ : POVM X d) : CPTPMap d (d × X) where
  toLinearMap :=
    ∑ (x : X), open Kronecker in {
      toFun := fun ρ ↦ ((((Λ.mats x) ^ (1/2:ℝ)).toMat * ρ * ((Λ.mats x)^(1/2:ℝ)).toMat) ⊗ₖ Matrix.single x x 1)
      map_add' := by simp [mul_add, add_mul, Matrix.kroneckerMap_add_left]
      map_smul' := by simp [Matrix.smul_kronecker]
    }
  cp :=
    sorry
    -- apply Finset.sum_induction
    -- · exact fun _ _ ha ↦ ha.add
    -- · exact MatrixMap.IsCompletelyPositive.zero _ _
    -- · intro x _
    --   let M₁ : MatrixMap d d ℂ := ⟨⟨
    --     fun ρ ↦ ((Λ.mats x) ^ (1/2:ℝ)).toMat * ρ * ((Λ.mats x)^(1/2:ℝ)).toMat,
    --     by simp [mul_add, add_mul]⟩,
    --     by simp⟩
    --   let M₂ : MatrixMap d (d × X) ℂ := ⟨⟨
    --     fun ρ ↦ (ρ.kronecker (Matrix.stdBasisMatrix x x 1)),
    --     by simp [mul_add, add_mul, Matrix.kroneckerMap_add_left]⟩,
    --     by simp [Matrix.smul_kronecker]⟩
    --   set M₃ := LinearMap.comp M₂ M₁ with hM₃
    --   simp only [M₁, M₂, LinearMap.comp, kronecker, LinearMap.coe_mk, AddHom.coe_mk] at hM₃
    --   unfold Function.comp at hM₃
    --   rw [← hM₃]
    --   apply MatrixMap.IsCompletelyPositive.comp
    --   · intro n ρ h
    --     sorry
    --   · apply MatrixMap.IsCompletelyPositive.kron_kronecker_const
    --     convert (Matrix.PosSemidef.stdBasisMatrix_iff_eq x x (zero_lt_one' ℂ)).2 rfl
  TP := by
    intro x
    rw [LinearMap.sum_apply, trace_sum]
    dsimp
    simp only [Matrix.trace_kronecker, Matrix.trace_mul_cycle (B := x),
      Matrix.trace_single_eq_same, mul_one]
    rw [← trace_sum, ← Finset.sum_mul]
    congr
    convert one_mul x
    rw [show (1 : Matrix d d ℂ) = (1 : HermitianMat d ℂ).toMat by rfl, ← Λ.normalized]
    push_cast
    congr! with i _
    sorry -- x ^ (1/2) * x ^ (1/2) = x when x is a PSD HermitiatMat

/-- A POVM leads to a distribution of outcomes on any given mixed state ρ. -/
def measure (Λ : POVM X d) (ρ : MState d) : Distribution X where
  val := fun x ↦ ⟨(Λ.mats x).inner ρ.M,
    ⟨HermitianMat.inner_ge_zero (Λ.zero_le x) ρ.zero_le,
    by
    -- That each observation probability is at most 1.
    -- Should follow from the fact they're nonnegative (above) and sum to 1 (below);
    -- so maybe we want a different Distribution constructor for that?
    sorry
    ⟩⟩
  property := by
    simp [HermitianMat.inner_eq_re_trace, ← Complex.re_sum, ← trace_sum, ← Finset.sum_mul,
      ← AddSubgroup.val_finset_sum, ← HermitianMat.val_eq_coe, Λ.normalized, ρ.tr]

/-- The quantum-classical `POVM.measurement_map`, gives a marginal on the right equal to `POVM.measure`.-/
theorem measure_eq_measurement_map (Λ : POVM X d) (ρ : MState d) :
    (Λ.measurement_map ρ).traceLeft = MState.ofClassical (Λ.measure ρ) :=
  sorry

/-- The action of measuring a state with the POVM `Λ`, discarding the resulting state, and keeping
the mixed state recording the outcome. This resulting state is purely diagonal, as given in
`POVM.measureDiscard_apply`. -/
noncomputable def measureDiscard (Λ : POVM X d) : CPTPMap d X :=
  CPTPMap.traceLeft ∘ₘ Λ.measurement_map

theorem measureDiscard_apply (Λ : POVM X d) (ρ : MState d) :
    Λ.measureDiscard ρ = MState.ofClassical (Λ.measure ρ) := by
  sorry

end POVM
