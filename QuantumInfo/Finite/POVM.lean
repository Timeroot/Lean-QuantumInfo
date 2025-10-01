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
def measurementMap (Λ : POVM X d) : CPTPMap d (d × X) where
  toLinearMap :=
    ∑ (x : X), open Kronecker in {
      toFun := fun ρ ↦ ((((Λ.mats x) ^ (1/2:ℝ)).toMat * ρ * ((Λ.mats x)^(1/2:ℝ)).toMat) ⊗ₖ Matrix.single x x 1)
      map_add' := by simp [mul_add, add_mul, Matrix.kroneckerMap_add_left]
      map_smul' := by simp [Matrix.smul_kronecker]
    }
  cp := by
    apply Finset.sum_induction
    · exact fun _ _ ha ↦ ha.add
    · exact MatrixMap.IsCompletelyPositive.zero _ _
    · intro x _
      --Note: this map M₁ would do as well as an object on its own, it's "measure and forget the result".
      let M₁ : MatrixMap d d ℂ := ⟨⟨
        fun ρ ↦ ((Λ.mats x) ^ (1/2:ℝ)).toMat * ρ * ((Λ.mats x)^(1/2:ℝ)).toMat,
        by simp [mul_add, add_mul]⟩,
        by simp⟩
      let M₂ : MatrixMap d (d × X) ℂ := ⟨⟨
        fun ρ ↦ (ρ.kronecker (Matrix.single x x 1)),
        by simp [add_mul, Matrix.kroneckerMap_add_left]⟩,
        by simp [Matrix.smul_kronecker]⟩
      set M₃ := LinearMap.comp M₂ M₁ with hM₃
      simp only [M₁, M₂, LinearMap.comp, kronecker, LinearMap.coe_mk, AddHom.coe_mk] at hM₃
      unfold Function.comp at hM₃
      rw [← hM₃]
      apply MatrixMap.IsCompletelyPositive.comp
      · dsimp [M₁]
        conv =>
          enter [1, 1, 1, ρ, 2]
          rw [← HermitianMat.conjTranspose_toMat]
        exact MatrixMap.IsCompletelyPositive.conj_isCompletelyPositive (Λ.mats x ^ (1 / 2)).toMat
      · apply MatrixMap.IsCompletelyPositive.kron_kronecker_const
        exact (Matrix.PosSemidef.stdBasisMatrix_iff_eq x x (zero_lt_one' ℂ)).2 rfl
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
    exact HermitianMat.pow_half_mul (Λ.zero_le i)

open Kronecker in
theorem measurementMap_apply_matrix (Λ : POVM X d) (m : Matrix d d ℂ) :
  Λ.measurementMap.map m =  ∑ x : X,
    ((((Λ.mats x) ^ (1/2:ℝ)).toMat * m * ((Λ.mats x)^(1/2:ℝ)).toMat) ⊗ₖ Matrix.single x x 1) := by
  dsimp [measurementMap, HPMap.map]
  rw [LinearMap.sum_apply]
  rfl

open HermitianMat in
theorem measurementMap_apply_hermitianMat (Λ : POVM X d) (m : HermitianMat d ℂ) :
  Λ.measurementMap.toHPMap m = ∑ x : X,
    --TODO: Something like `HermitianMat.single` to make this better
    ((m.conj ((Λ.mats x)^(1/2:ℝ)).toMat : HermitianMat d ℂ) ⊗ₖ .diagonal (fun y ↦ ite (x = y) 1 0)) := by
  ext1
  convert Λ.measurementMap_apply_matrix m.toMat
  simp [HermitianMat.conj]
  congr!
  ext i j
  simp only [HermitianMat.diagonal, mk_toMat, diagonal_apply, single, of_apply]
  split_ifs <;> (try grind) <;> norm_num

/-- A POVM leads to a distribution of outcomes on any given mixed state ρ. -/
def measure (Λ : POVM X d) (ρ : MState d) : Distribution X := .mk'
    (f := fun x ↦ (Λ.mats x).inner ρ.M)
    (h₁ := fun x ↦ HermitianMat.inner_ge_zero (Λ.zero_le x) ρ.zero_le)
    (hN := by
      simp [HermitianMat.inner_eq_re_trace, ← Complex.re_sum, ← trace_sum, ← Finset.sum_mul,
      ← AddSubgroup.val_finset_sum, ← HermitianMat.val_eq_coe, Λ.normalized])

/-- The quantum-classical `POVM.measurement_map`, gives a marginal on the right equal to `POVM.measure`.-/
theorem traceLeft_measurementMap_eq_measure (Λ : POVM X d) (ρ : MState d) :
    (Λ.measurementMap ρ).traceLeft = MState.ofClassical (Λ.measure ρ) := by
  open Kronecker in
  ext i j
  rcases ρ with ⟨⟨ρ, ρH⟩, hρ0, hρ1⟩
  change (Matrix.traceLeft (Λ.measurementMap.map ρ)) i j = _
  rw [measurementMap_apply_matrix]
  --TODO: a lemma for Matrix.traceLeft (∑ x, _) = ∑ x, (Matrix.traceLeft _)
  simp_rw [Matrix.traceLeft, Matrix.of_apply, Matrix.sum_apply]
  rw [Finset.sum_comm]
  simp only [kroneckerMap_apply, MState.coe_ofClassical]
  simp only [single, of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  simp only [HermitianMat.diagonal, HermitianMat.mk_toMat, diagonal_apply]
  symm; split
  · subst j
    simp only [measure, Distribution.mk', Distribution.funlike_apply, and_self, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    change _ = Matrix.trace _
    rw [Matrix.trace_mul_cycle, HermitianMat.pow_half_mul (Λ.zero_le i)]
    exact HermitianMat.inner_eq_trace_rc _ _
  · conv => enter [2, 2, x]; rw [if_neg (by grind)]
    simp

/-- The action of measuring a state with the POVM `Λ`, discarding the resulting state, and keeping
the mixed state recording the outcome. This resulting state is purely diagonal, as given in
`POVM.measureDiscard_apply`. -/
noncomputable def measureDiscard (Λ : POVM X d) : CPTPMap d X :=
  CPTPMap.traceLeft ∘ₘ Λ.measurementMap

theorem measureDiscard_apply (Λ : POVM X d) (ρ : MState d) :
    Λ.measureDiscard ρ = MState.ofClassical (Λ.measure ρ) := by
  simp [measureDiscard, traceLeft_measurementMap_eq_measure]

/-- The action of measuring a state with the POVM `Λ`, forgetting the measurement outcome, and
keeping the disturbed state. -/
noncomputable def measureForget (Λ : POVM X d) : CPTPMap d d :=
  CPTPMap.traceRight ∘ₘ Λ.measurementMap

proof_wanted measureForget_eq_kraus (Λ : POVM X d) :
    Λ.measureForget = CPTPMap.of_kraus_CPTPMap (fun i ↦ (Λ.mats i) ^ (1/2 : ℝ)) (by
      simpa [-one_div, fun x ↦ HermitianMat.pow_half_mul (Λ.zero_le x), HermitianMat.ext_iff]
        using Λ.normalized
    )

end POVM
