/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Asymptotic.FixedSmoothMinEntropy.ThresholdProjector
import QIT.Util.TensorPower

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker NNReal
open Filter

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
namespace State
/-! ## Finite-AEP assembly core -/

/-! ### Full-rank regularization setup for arbitrary finite states -/

/-- Matrix path that regularizes an arbitrary finite bipartite state by adding
white noise on `AB`.

For `0 < η ≤ 1`, the associated state below is positive definite, and as
`η → 0+` this matrix tends back to `ρ.matrix`.  This is the reusable
regularization surface needed before taking the positive-definite finite-AEP
core to arbitrary states. -/
def finiteAEPFullRankRegularizationMatrix
    (ρ : State (Prod a b)) (η : ℝ) : CMatrix (Prod a b) :=
  (((1 - η : ℝ) : ℂ) • ρ.matrix) +
    ((((η / (Fintype.card (Prod a b) : ℝ) : ℝ)) : ℂ) •
      (1 : CMatrix (Prod a b)))

/-- The fixed direction from `ρ` toward the maximally mixed state used by the
white-noise regularization. -/
def finiteAEPFullRankRegularizationDirection
    (ρ : State (Prod a b)) : CMatrix (Prod a b) :=
  ((((1 / (Fintype.card (Prod a b) : ℝ) : ℝ) : ℂ) •
    (1 : CMatrix (Prod a b))) - ρ.matrix)

/-- The normalized state associated with
`finiteAEPFullRankRegularizationMatrix` when the regularization weight lies in
the probability interval. -/
def finiteAEPFullRankRegularization
    (ρ : State (Prod a b)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    State (Prod a b) where
  matrix := finiteAEPFullRankRegularizationMatrix ρ η
  pos := by
    unfold finiteAEPFullRankRegularizationMatrix
    have hleft : (0 : ℂ) ≤ (((1 - η : ℝ) : ℂ)) := by
      exact_mod_cast sub_nonneg.mpr hη1
    have hright : (0 : ℂ) ≤ (((η / (Fintype.card (Prod a b) : ℝ) : ℝ) : ℂ)) := by
      exact_mod_cast div_nonneg hη0 (by positivity : (0 : ℝ) ≤ Fintype.card (Prod a b))
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul ρ.pos hleft)
      (Matrix.PosSemidef.smul Matrix.PosSemidef.one hright)
  trace_eq_one := by
    letI : Nonempty (Prod a b) := ρ.nonempty
    have hcardR : (Fintype.card (Prod a b) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card (Prod a b) ≠ 0))
    have hscalar :
        (1 - η) + (η / (Fintype.card (Prod a b) : ℝ)) *
            (Fintype.card (Prod a b) : ℝ) = 1 := by
      field_simp [hcardR]
      ring
    unfold finiteAEPFullRankRegularizationMatrix
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, ρ.trace_eq_one,
      Matrix.trace_one]
    simpa [smul_eq_mul] using congrArg (fun x : ℝ => (x : ℂ)) hscalar

@[simp]
theorem finiteAEPFullRankRegularization_matrix
    (ρ : State (Prod a b)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).matrix =
      finiteAEPFullRankRegularizationMatrix ρ η :=
  rfl

/-- The full-rank white-noise regularization differs from the original state
by `η` times a fixed matrix. -/
theorem finiteAEPFullRankRegularization_matrix_sub
    (ρ : State (Prod a b)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).matrix - ρ.matrix =
      ((η : ℂ) • ρ.finiteAEPFullRankRegularizationDirection) := by
  ext i j
  simp [finiteAEPFullRankRegularization_matrix,
    finiteAEPFullRankRegularizationMatrix, finiteAEPFullRankRegularizationDirection,
    Matrix.one_apply]
  by_cases hij : i = j
  · simp [hij]
    ring_nf
  · simp [hij]
    ring_nf

/-- The normalized trace distance from the white-noise regularization to the
original state is at most linear in the regularization weight. -/
theorem finiteAEPFullRankRegularization_normalizedTraceDistance_le
    (ρ : State (Prod a b)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).normalizedTraceDistance ρ ≤
      η * (1 / 2 : ℝ) *
        traceNorm ρ.finiteAEPFullRankRegularizationDirection := by
  rw [State.normalizedTraceDistance_eq_matrix, QIT.normalizedTraceDistance_eq,
    QIT.traceNormDistance]
  rw [finiteAEPFullRankRegularization_matrix_sub ρ η hη0 hη1]
  have hnorm := traceNorm_real_smul_le (a := Prod a b) hη0
    ρ.finiteAEPFullRankRegularizationDirection
  nlinarith

/-- The purified distance from the white-noise regularization to the original
state is controlled by the square root of the regularization weight. -/
theorem finiteAEPFullRankRegularization_purifiedDistance_le
    (ρ : State (Prod a b)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).purifiedDistance ρ ≤
      Real.sqrt
        (η *
          traceNorm ρ.finiteAEPFullRankRegularizationDirection) := by
  have hP :=
    purifiedDistance_le_sqrt_two_mul_normalizedTraceDistance
      (ρ.finiteAEPFullRankRegularization η hη0 hη1) ρ
  have hD := ρ.finiteAEPFullRankRegularization_normalizedTraceDistance_le η hη0 hη1
  have htrace_nonneg :
      0 ≤ traceNorm ρ.finiteAEPFullRankRegularizationDirection :=
    traceNorm_nonneg _
  refine le_trans hP (Real.sqrt_le_sqrt ?_)
  nlinarith

private theorem cMatrix_real_smul_one_posDef_forFiniteAEP
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℝ} (hr : 0 < r) :
    (r • (1 : CMatrix ι)).PosDef := by
  rw [show r • (1 : CMatrix ι) = Matrix.diagonal (fun _ : ι => (r : ℂ)) by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]]
  rw [Matrix.posDef_diagonal_iff]
  intro i
  exact_mod_cast hr

/-- Positive regularization weight makes the white-noise regularization
positive definite, even when the original state is singular. -/
theorem finiteAEPFullRankRegularization_posDef
    (ρ : State (Prod a b)) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hηpos : 0 < η) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).matrix.PosDef := by
  letI : Nonempty (Prod a b) := ρ.nonempty
  unfold finiteAEPFullRankRegularization finiteAEPFullRankRegularizationMatrix
  have hleft : (0 : ℂ) ≤ (((1 - η : ℝ) : ℂ)) := by
    exact_mod_cast sub_nonneg.mpr hη1
  have hright : 0 < η / (Fintype.card (Prod a b) : ℝ) := by
    exact div_pos hηpos (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Prod a b)))
  exact Matrix.PosDef.posSemidef_add
    (Matrix.PosSemidef.smul ρ.pos hleft)
    (cMatrix_real_smul_one_posDef_forFiniteAEP hright)

private theorem partialTraceA_one_forFiniteAEP
    (a : Type u) (b : Type v) [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] :
    partialTraceA (a := a) (b := b) (1 : CMatrix (Prod a b)) =
      ((Fintype.card a : ℂ) • (1 : CMatrix b)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [partialTraceA]
  · simp [partialTraceA, hij]

private theorem finiteAEPFullRankRegularization_whiteNoise_marginalB_scalar
    (ρ : State (Prod a b)) (η : ℝ) :
    ((η / (Fintype.card (Prod a b) : ℝ) : ℝ) *
        (Fintype.card a : ℝ)) =
      η / (Fintype.card b : ℝ) := by
  letI : Nonempty (Prod a b) := ρ.nonempty
  letI : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  letI : Nonempty b := ⟨(Classical.choice ρ.nonempty).2⟩
  have ha : (Fintype.card a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card a ≠ 0))
  have hb : (Fintype.card b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card b ≠ 0))
  have hprod :
      (Fintype.card (Prod a b) : ℝ) =
        (Fintype.card a : ℝ) * (Fintype.card b : ℝ) := by
    exact_mod_cast (Fintype.card_prod a b)
  rw [hprod]
  field_simp [ha, hb]

/-- The `B` marginal of the white-noise regularization is the matching
white-noise regularization of `ρ_B`. -/
theorem finiteAEPFullRankRegularization_marginalB_matrix
    (ρ : State (Prod a b)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).marginalB.matrix =
      (((1 - η : ℝ) : ℂ) • ρ.marginalB.matrix) +
        ((((η / (Fintype.card b : ℝ) : ℝ)) : ℂ) • (1 : CMatrix b)) := by
  unfold finiteAEPFullRankRegularization
  simp only [State.marginalB_matrix]
  unfold finiteAEPFullRankRegularizationMatrix
  rw [partialTraceA_add, partialTraceA_smul, partialTraceA_smul,
    partialTraceA_one_forFiniteAEP]
  rw [smul_smul]
  have hscalar :
      (((η / (Fintype.card (Prod a b) : ℝ) : ℝ) : ℂ) *
          (Fintype.card a : ℂ)) =
        (((η / (Fintype.card b : ℝ) : ℝ) : ℂ)) := by
    exact_mod_cast
      finiteAEPFullRankRegularization_whiteNoise_marginalB_scalar
        (a := a) (b := b) ρ η
  rw [hscalar]

/-- The `B` marginal of the regularized state is positive definite for every
positive regularization weight. -/
theorem finiteAEPFullRankRegularization_marginalB_posDef
    (ρ : State (Prod a b)) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hηpos : 0 < η) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).marginalB.matrix.PosDef := by
  letI : Nonempty b := ⟨(Classical.choice ρ.nonempty).2⟩
  rw [finiteAEPFullRankRegularization_marginalB_matrix]
  have hleft : (0 : ℂ) ≤ (((1 - η : ℝ) : ℂ)) := by
    exact_mod_cast sub_nonneg.mpr hη1
  have hright : 0 < η / (Fintype.card b : ℝ) := by
    exact div_pos hηpos (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card b))
  exact Matrix.PosDef.posSemidef_add
    (Matrix.PosSemidef.smul ρ.marginalB.pos hleft)
    (cMatrix_real_smul_one_posDef_forFiniteAEP hright)

/-- The full-rank regularization matrix tends back to the original state
matrix as the noise weight tends to zero through positive probabilities. -/
theorem finiteAEPFullRankRegularizationMatrix_tendsto_zero
    (ρ : State (Prod a b)) :
    Filter.Tendsto (fun η : ℝ => finiteAEPFullRankRegularizationMatrix ρ η)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ.matrix) := by
  have hcont : Continuous fun η : ℝ =>
      finiteAEPFullRankRegularizationMatrix ρ η := by
    unfold finiteAEPFullRankRegularizationMatrix
    fun_prop
  have h0 : finiteAEPFullRankRegularizationMatrix ρ 0 = ρ.matrix := by
    simp [finiteAEPFullRankRegularizationMatrix]
  simpa [h0] using
    (hcont.continuousWithinAt (x := (0 : ℝ)) (s := Set.Ioo (0 : ℝ) 1)).tendsto

/-- The expanded `B`-marginal white-noise regularization matrix tends back to
the original `B` marginal as the noise weight tends to zero through positive
probabilities. -/
theorem finiteAEPFullRankRegularization_marginalB_matrix_path_tendsto_zero
    (ρ : State (Prod a b)) :
    Filter.Tendsto
      (fun η : ℝ =>
        (((1 - η : ℝ) : ℂ) • ρ.marginalB.matrix) +
          ((((η / (Fintype.card b : ℝ) : ℝ)) : ℂ) • (1 : CMatrix b)))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ.marginalB.matrix) := by
  have hcont : Continuous fun η : ℝ =>
      (((1 - η : ℝ) : ℂ) • ρ.marginalB.matrix) +
        ((((η / (Fintype.card b : ℝ) : ℝ)) : ℂ) • (1 : CMatrix b)) := by
    fun_prop
  have h0 :
      (((1 - (0 : ℝ) : ℝ) : ℂ) • ρ.marginalB.matrix) +
          ((((0 / (Fintype.card b : ℝ) : ℝ)) : ℂ) • (1 : CMatrix b)) =
        ρ.marginalB.matrix := by
    simp
  simpa [h0] using
    (hcont.continuousWithinAt (x := (0 : ℝ)) (s := Set.Ioo (0 : ℝ) 1)).tendsto

/-- The `B` marginal matrix of the full-rank regularized state tends back to
the original `B` marginal matrix as the noise weight tends to zero through
`η ∈ (0, 1)`.

Outside the interval the displayed path is filled in with the limiting matrix,
so it is a total function on `ℝ`; on the `nhdsWithin` filter it is eventually
equal to the actual regularized marginal. -/
theorem finiteAEPFullRankRegularization_marginalB_matrix_tendsto_zero
    (ρ : State (Prod a b)) :
    Filter.Tendsto
      (fun η : ℝ =>
        if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          (ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le).marginalB.matrix
        else
          ρ.marginalB.matrix)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ.marginalB.matrix) := by
  refine Filter.Tendsto.congr' ?_
    (finiteAEPFullRankRegularization_marginalB_matrix_path_tendsto_zero ρ)
  filter_upwards [self_mem_nhdsWithin] with η hη
  rw [dif_pos hη]
  exact
    (finiteAEPFullRankRegularization_marginalB_matrix
      (a := a) (b := b) ρ η hη.1.le hη.2.le).symm

/-- The full-rank regularized state tends back to the original state as the
noise weight tends to zero through `η ∈ (0, 1)`.

Outside the interval the displayed path is filled in with the limiting state,
so it is a total function on `ℝ`; on the `nhdsWithin` filter it is eventually
equal to the actual regularized state. -/
theorem finiteAEPFullRankRegularization_tendsto_zero
    (ρ : State (Prod a b)) :
    Filter.Tendsto
      (fun η : ℝ =>
        if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
        else
          ρ)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ) := by
  rw [Filter.tendsto_iff_comap]
  rw [nhds_induced]
  rw [Filter.comap_comap]
  rw [← Filter.tendsto_iff_comap]
  refine Filter.Tendsto.congr' ?_ (finiteAEPFullRankRegularizationMatrix_tendsto_zero ρ)
  filter_upwards [self_mem_nhdsWithin] with η hη
  change ρ.finiteAEPFullRankRegularizationMatrix η =
    (if hη' : η ∈ Set.Ioo (0 : ℝ) 1 then
      ρ.finiteAEPFullRankRegularization η hη'.1.le hη'.2.le
    else ρ).matrix
  rw [dif_pos hη]
  rfl

/-- Conditional entropy is continuous along the full-rank white-noise
regularization path. -/
theorem finiteAEPFullRankRegularization_conditionalEntropy_tendsto_zero
    (ρ : State (Prod a b)) :
    Filter.Tendsto
      (fun η : ℝ =>
        (if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
        else
          ρ).conditionalEntropy)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ.conditionalEntropy) :=
  State.conditionalEntropy_continuous.tendsto ρ |>.comp
    (finiteAEPFullRankRegularization_tendsto_zero ρ)

/-- Fixed tensor powers are continuous as maps of the input density state. -/
theorem tensorPower_matrix_continuous (n : ℕ) :
    Continuous (fun ρ : State a => (ρ.tensorPower n).matrix) := by
  induction n with
  | zero =>
      change Continuous fun _ : State a => (1 : CMatrix PUnit)
      fun_prop
  | succ n ih =>
      change Continuous fun ρ : State a => (ρ.prod (ρ.tensorPower n)).matrix
      refine continuous_pi ?_
      intro i
      refine continuous_pi ?_
      intro j
      cases i with
      | mk i0 it =>
        cases j with
        | mk j0 jt =>
          simp [State.prod, Matrix.kronecker, Matrix.kroneckerMap_apply]
          exact ((continuous_apply j0).comp
              ((continuous_apply i0).comp State.continuous_matrix)).mul
            ((continuous_apply jt).comp ((continuous_apply it).comp ih))

/-- Fixed tensor powers are continuous at the state level. -/
theorem tensorPower_continuous (n : ℕ) :
    Continuous (fun ρ : State a => ρ.tensorPower n) := by
  rw [continuous_induced_rng]
  exact tensorPower_matrix_continuous (a := a) n

/-- Fixed bipartite tensor powers are continuous as matrix-valued maps of the
input density state. -/
theorem tensorPowerBipartite_matrix_continuous (n : ℕ) :
    Continuous (fun ρ : State (Prod a b) => (ρ.tensorPowerBipartite n).matrix) := by
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro j
  simp [State.tensorPowerBipartite]
  exact (continuous_apply ((tensorPowerProdEquiv a b n).symm j)).comp
    ((continuous_apply ((tensorPowerProdEquiv a b n).symm i)).comp
      (tensorPower_matrix_continuous (a := Prod a b) n))

/-- Fixed bipartite tensor powers are continuous at the state level. -/
theorem tensorPowerBipartite_continuous (n : ℕ) :
    Continuous (fun ρ : State (Prod a b) => ρ.tensorPowerBipartite n) := by
  rw [continuous_induced_rng]
  exact tensorPowerBipartite_matrix_continuous (a := a) (b := b) n

/-- Bipartite tensor powers of the full-rank white-noise regularization tend
back to the tensor power of the original state. -/
theorem finiteAEPFullRankRegularization_tensorPowerBipartite_tendsto_zero
    (ρ : State (Prod a b)) (n : ℕ) :
    Filter.Tendsto
      (fun η : ℝ =>
        (if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
        else
          ρ).tensorPowerBipartite n)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1))
      (nhds (ρ.tensorPowerBipartite n)) :=
  (tensorPowerBipartite_continuous (a := a) (b := b) n).tendsto ρ |>.comp
    (finiteAEPFullRankRegularization_tendsto_zero ρ)

/-- Bipartite tensor powers of the full-rank regularization approach the
original tensor power in normalized trace distance. -/
theorem finiteAEPFullRankRegularization_tensorPowerBipartite_normalizedTraceDistance_tendsto_zero
    (ρ : State (Prod a b)) (n : ℕ) :
    Filter.Tendsto
      (fun η : ℝ =>
        ((if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
        else
          ρ).tensorPowerBipartite n).normalizedTraceDistance
            (ρ.tensorPowerBipartite n))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds 0) := by
  have hcont :=
    finiteAEP_normalizedTraceDistance_continuous_left
      (a := TensorPower a n) (b := TensorPower b n) (ρ.tensorPowerBipartite n)
  simpa using hcont.tendsto (ρ.tensorPowerBipartite n) |>.comp
    (finiteAEPFullRankRegularization_tensorPowerBipartite_tendsto_zero ρ n)

/-- Bipartite tensor powers of the full-rank regularization approach the
original tensor power in purified distance. -/
theorem finiteAEPFullRankRegularization_tensorPowerBipartite_purifiedDistance_tendsto_zero
    (ρ : State (Prod a b)) (n : ℕ) :
    Filter.Tendsto
      (fun η : ℝ =>
        ((if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
        else
          ρ).tensorPowerBipartite n).purifiedDistance
            (ρ.tensorPowerBipartite n))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds 0) := by
  have hD :=
    finiteAEPFullRankRegularization_tensorPowerBipartite_normalizedTraceDistance_tendsto_zero
      (a := a) (b := b) ρ n
  refine squeeze_zero
    (f := fun η : ℝ =>
      ((if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
        ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
      else
        ρ).tensorPowerBipartite n).purifiedDistance
          (ρ.tensorPowerBipartite n))
    (g := fun η : ℝ =>
      Real.sqrt
        (2 *
          (((if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
            ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
          else
            ρ).tensorPowerBipartite n).normalizedTraceDistance
              (ρ.tensorPowerBipartite n))))
    (fun η => ?_) (fun η => ?_) ?_
  · simp [State.purifiedDistance_eq]
  · exact purifiedDistance_le_sqrt_two_mul_normalizedTraceDistance
      (((if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
        ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
      else
        ρ).tensorPowerBipartite n))
      (ρ.tensorPowerBipartite n)
  · simpa using (hD.const_mul (2 : ℝ)).sqrt

/-- The same convergence after viewing normalized states as subnormalized
states, matching the smoothing-ball center-migration API. -/
theorem finiteAEPFullRankRegularization_tensorPowerBipartite_toSubnormalized_purifiedDistance_tendsto_zero
    (ρ : State (Prod a b)) (n : ℕ) :
    Filter.Tendsto
      (fun η : ℝ =>
        (((if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
        else
          ρ).tensorPowerBipartite n).toSubnormalized).purifiedDistance
            (ρ.tensorPowerBipartite n).toSubnormalized)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds 0) := by
  refine Filter.Tendsto.congr' ?_
    (finiteAEPFullRankRegularization_tensorPowerBipartite_purifiedDistance_tendsto_zero
      (a := a) (b := b) ρ n)
  filter_upwards with η
  rw [State.toSubnormalized_purifiedDistance_eq]

/-- Eventually the regularized tensor power lies in any prescribed
subnormalized purified-distance ball around the original tensor power. -/
theorem finiteAEPFullRankRegularization_tensorPowerBipartite_toSubnormalized_purifiedDistance_eventually_le
    (ρ : State (Prod a b)) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioo 0 1),
      (((if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
        ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
      else
        ρ).tensorPowerBipartite n).toSubnormalized).purifiedDistance
          (ρ.tensorPowerBipartite n).toSubnormalized ≤ δ := by
  have h :=
    finiteAEPFullRankRegularization_tensorPowerBipartite_toSubnormalized_purifiedDistance_tendsto_zero
      (a := a) (b := b) ρ n
  have hlt :
      ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioo 0 1),
        (((if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
        else
          ρ).tensorPowerBipartite n).toSubnormalized).purifiedDistance
            (ρ.tensorPowerBipartite n).toSubnormalized < δ :=
    h.eventually (Iio_mem_nhds hδ)
  filter_upwards [hlt] with η hη
  exact le_of_lt hη

/-- Transfer an unnormalized finite-AEP lower bound from a full-rank
regularized tensor-power center back to the original center.

The scalar comparison hypothesis isolates the remaining regularization
analysis: once the regularized conditional-entropy and eta penalty are shown
to dominate the target right-hand side, center migration supplies the smooth
min-entropy part. -/
theorem finiteAEPFullRankRegularization_tensorLowerBound_transfer
    (ρ : State (Prod a b)) (n : ℕ)
    {ξ ε δ targetL regL : ℝ} (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hε_nonneg : 0 ≤ ε)
    (hεδ_nonneg : 0 ≤ ε + δ) (hεδ_lt : ε + δ < 1)
    (hcenter :
      ((ρ.finiteAEPFullRankRegularization ξ hξ.1.le hξ.2.le).tensorPowerBipartite n).toSubnormalized.purifiedDistance
        (ρ.tensorPowerBipartite n).toSubnormalized ≤ δ)
    (hreg :
      regL ≤
        (ρ.finiteAEPFullRankRegularization ξ hξ.1.le hξ.2.le).tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw ε n)
    (hscalar : targetL ≤ regL) :
    targetL ≤ ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw (ε + δ) n := by
  exact le_trans hscalar
    (tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_lower_bound_of_center_migration
      (ρ := ρ)
      (η := ρ.finiteAEPFullRankRegularization ξ hξ.1.le hξ.2.le)
      (n := n) hε_nonneg hεδ_nonneg hεδ_lt hcenter hreg)

/-- Package an unnormalized tensor-power lower bound into the public finite-N
AEP statement surface with an explicit source parameter `η`.

This is the arbitrary-state assembly shell: subsequent support/regularization
work only has to provide the displayed tensor lower bound for each admissible
positive smoothing parameter and blocklength. -/
theorem finiteNAEP_statement_of_explicitEta_tensorLowerBound
    (ρ : State (Prod a b)) (ε η : ℝ) (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1) (n : ℕ)
    (hcore :
      ∀ (_hε_pos : 0 < ε)
        (_hn : 0 < n)
        (_hn_ge : (8 / 5 : ℝ) * log2 (2 / ε ^ 2) ≤ (n : ℝ)),
        ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy
            ε n hε_nonneg hε_lt ≥
          (n : ℝ) * ρ.conditionalEntropy -
            finiteAEPDelta ε η * Real.sqrt (n : ℝ)) :
    QIT.finiteNAEP_statement ρ ε η n hε_nonneg hε_lt := by
  intro hε_pos hn_ge
  have hM : 0 < log2 (2 / ε ^ 2) :=
    finiteAEP_log2_two_div_sq_pos hε_pos hε_lt
  have hnR : 0 < (n : ℝ) := by
    exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 8 / 5) hM) hn_ge
  have hn : 0 < n := by exact_mod_cast hnR
  have hbound := hcore hε_pos hn hn_ge
  exact
    finiteAEP_normalized_rate_of_tensor_lower_bound
      (S := ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy
        ε n hε_nonneg hε_lt)
      (H := ρ.conditionalEntropy)
      (δ := QIT.finiteAEPDelta ε η)
      (n := n) hn hbound

/-- Positive-definite fixed-reference finite-AEP core with subnormalized
smooth-min witnesses.

This is the assembly form that matches the source-shaped `GρG†` construction:
the one-shot smooth-min/Petz bridge produces a subnormalized nearby witness,
while the alpha-to-von-Neumann estimate is the positive-definite core from
`AlphaEntropyContinuity`. -/
theorem relativeFiniteAEP_core_posDef_of_smoothMinPetzBound_subnormalized
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (_hε_pos : 0 < ε)
    (hα_gt : 1 < α) (_hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)))
    (hsmoothMinPetz :
      ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
          ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε ≥
      ρ.conditionalEntropyRelative hρ σ hσ -
        4 * (α - 1) *
          (log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  have hpetz :
      ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        ρ.conditionalEntropyRelative hρ σ hσ -
          4 * (α - 1) *
            (log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)) ^ 2 :=
    conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef
      (ρ := ρ) hρ (σ := σ) hσ α hα_gt hα_lt
  linarith

/-- Full-reference finite-AEP one-copy core for arbitrary left states and a
positive-definite reference.

This combines the source-aligned smooth-min lower bound (`thm:entropy-ineq`)
with the support-indexed alpha-to-von-Neumann bound (`lemma:alpha-bound`) in the
full-rank-reference branch. -/
theorem relativeFiniteAEP_core_fullReference
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.conditionalAlphaConvergenceParameterTrace σ))) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε ≥
      ρ.conditionalEntropyRelativeFullReference σ hσ -
        4 * (α - 1) *
          (log2 (ρ.conditionalAlphaConvergenceParameterTrace σ)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  have hsmooth :
      ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
          ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε :=
    ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_fullReference
      σ hσ ε α hε_pos hε_lt hα_gt hα_le_two
  have hpetz :
      ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        ρ.conditionalEntropyRelativeFullReference σ hσ -
          4 * (α - 1) *
            (log2 (ρ.conditionalAlphaConvergenceParameterTrace σ)) ^ 2 :=
    conditionalPetzRenyiEntropyCandidateFullReference_alpha_bound
      (ρ := ρ) (σ := σ) hσ α hα_gt hα_lt
  linarith

/-- Positive-definite fixed-reference finite-AEP core from the source-shaped
`GρG†` smooth-min construction, reducing the remaining one-shot estimate to
the single Petz positive-part trace bound. -/
theorem relativeFiniteAEP_core_posDef_of_fixedPetzSmoothMinG_petzTrace
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)))
    (hpetz :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      (ρ.fixedPetzThresholdPositivePart σ lam).trace.re ≤
        lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm σ α) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε ≥
      ρ.conditionalEntropyRelative hρ σ hσ -
        4 * (α - 1) *
          (log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  exact
    ρ.relativeFiniteAEP_core_posDef_of_smoothMinPetzBound_subnormalized
      hρ σ hσ ε α hε_pos hα_gt hα_le_two hα_lt
      (ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_petzTrace
        hρ σ hσ ε α hε_pos hε_lt hα_gt hα_le_two hpetz)

/-- Positive-definite fixed-reference finite-AEP core from the source-shaped
`GρG†` smooth-min construction, exposing the remaining noncommutative source
step as the Petz effect-variational inequality. -/
theorem relativeFiniteAEP_core_posDef_of_fixedPetzSmoothMinG_effectVariational
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)))
    (hvar :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational ρ.matrix
        (identityTensorStateMatrix (a := a) σ) lam α) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε ≥
      ρ.conditionalEntropyRelative hρ σ hσ -
        4 * (α - 1) *
          (log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  exact
    ρ.relativeFiniteAEP_core_posDef_of_smoothMinPetzBound_subnormalized
      hρ σ hσ ε α hε_pos hα_gt hα_le_two hα_lt
      (ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_effectVariational
        hρ σ hσ ε α hε_pos hε_lt hα_gt hα_le_two hvar)

/-- Positive-definite fixed-reference finite-AEP core from the source-shaped
`GρG†` smooth-min construction, exposing the remaining noncommutative source
step as the Hilbert-Schmidt kernel dephasing monotonicity inequality. -/
theorem relativeFiniteAEP_core_posDef_of_fixedPetzSmoothMinG_kernelDephaseMonotone
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)))
    (hkernel :
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ σ hσ ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) σ).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one)
        ).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceKernelDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) σ) U α) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε ≥
      ρ.conditionalEntropyRelative hρ σ hσ -
        4 * (α - 1) *
          (log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  exact
    ρ.relativeFiniteAEP_core_posDef_of_smoothMinPetzBound_subnormalized
      hρ σ hσ ε α hε_pos hα_gt hα_le_two hα_lt
      (ρ.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_kernelDephaseMonotone
        hρ σ hσ ε α hε_pos hε_lt hα_gt hα_le_two hkernel)

/-- Canonical positive-definite finite-AEP core for the public side reference
`σ = ρ_B`, still exposing the Petz positive-part trace estimate.

This is only a specialization of the fixed-reference core above.  The
positive-definiteness of `ρ_B` and the Petz trace bound remain assumptions. -/
theorem finiteAEP_core_posDef_of_fixedPetzSmoothMinG_petzTrace
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB)))
    (hpetz :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ ρ.marginalB hρB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      (ρ.fixedPetzThresholdPositivePart ρ.marginalB lam).trace.re ≤
        lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm ρ.marginalB α) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized ρ.marginalB.toSubnormalized ε ≥
      ρ.conditionalEntropy -
        4 * (α - 1) *
          (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  have hcore :=
    ρ.relativeFiniteAEP_core_posDef_of_fixedPetzSmoothMinG_petzTrace
      hρ ρ.marginalB hρB ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [finiteAEPEta_eq] using hα_lt) hpetz
  rw [ρ.conditionalEntropyRelative_to_conditionalEntropy hρ hρB] at hcore
  simpa [finiteAEPEta_eq] using hcore

/-- Canonical positive-definite finite-AEP core for the public side reference
`σ = ρ_B`, with the remaining source step expressed as the Petz
effect-variational inequality. -/
theorem finiteAEP_core_posDef_of_fixedPetzSmoothMinG_effectVariational
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB)))
    (hvar :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ ρ.marginalB hρB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational ρ.matrix
        (identityTensorStateMatrix (a := a) ρ.marginalB) lam α) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized ρ.marginalB.toSubnormalized ε ≥
      ρ.conditionalEntropy -
        4 * (α - 1) *
          (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  have hcore :=
    ρ.relativeFiniteAEP_core_posDef_of_fixedPetzSmoothMinG_effectVariational
      hρ ρ.marginalB hρB ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [finiteAEPEta_eq] using hα_lt) hvar
  rw [ρ.conditionalEntropyRelative_to_conditionalEntropy hρ hρB] at hcore
  simpa [finiteAEPEta_eq] using hcore

/-- Canonical positive-definite finite-AEP core for the public side reference
`σ = ρ_B`, with the remaining source step expressed as the Hilbert-Schmidt
kernel dephasing monotonicity inequality. -/
theorem finiteAEP_core_posDef_of_fixedPetzSmoothMinG_kernelDephaseMonotone
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB)))
    (hkernel :
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ ρ.marginalB hρB ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) ρ.marginalB).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) ρ.marginalB hρB
      let H : CMatrix (Prod a b) :=
        ρ.matrix - lam • identityTensorStateMatrix (a := a) ρ.marginalB
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρ.petzSmoothMinThresholdScale_pos hρ ρ.marginalB hρB ε α hα_pos hα_ne_one)
        ).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceKernelDephaseMonotone ρ.matrix
        (identityTensorStateMatrix (a := a) ρ.marginalB) U α) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized ρ.marginalB.toSubnormalized ε ≥
      ρ.conditionalEntropy -
        4 * (α - 1) *
          (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  have hcore :=
    ρ.relativeFiniteAEP_core_posDef_of_fixedPetzSmoothMinG_kernelDephaseMonotone
      hρ ρ.marginalB hρB ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [finiteAEPEta_eq] using hα_lt) hkernel
  rw [ρ.conditionalEntropyRelative_to_conditionalEntropy hρ hρB] at hcore
  simpa [finiteAEPEta_eq] using hcore

/-- Optimized scalar-choice finite-AEP core with explicit tensor-power
bookkeeping assumptions.

The state `ρn` is intentionally arbitrary: downstream tensor-power work should
instantiate it with `ρ_AB^{⊗ n}` and prove the displayed entropy and eta-growth
hypotheses.  The Petz positive-part trace estimate is still explicit. -/
theorem finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_petzTrace
    (ρn : State (Prod a b)) (hρn : ρn.matrix.PosDef)
    (hρnB : ρn.marginalB.matrix.PosDef)
    (ε η α H : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hL : 0 < log2 η)
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρn.finiteAEPEta hρn hρnB)))
    (hentropy_tensor : ρn.conditionalEntropy = (n : ℝ) * H)
    (heta_tensor :
      (log2 (ρn.finiteAEPEta hρn hρnB)) ^ 2 ≤
        (n : ℝ) * (log2 η) ^ 2)
    (hpetz :
      let hα_gt : 1 < α := by
        rw [hα_opt]
        have hden :
            0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
          exact mul_pos (mul_pos (by norm_num) hL)
            (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
        have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
          Real.sqrt_pos.mpr hM
        have hfrac :
            0 <
              Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) :=
          div_pos hnum hden
        linarith
      let lam : ℝ :=
        ρn.petzSmoothMinThresholdScale hρn ρn.marginalB hρnB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      (ρn.fixedPetzThresholdPositivePart ρn.marginalB lam).trace.re ≤
        lam ^ (1 - α) * ρn.conditionalPetzRenyiTraceTerm ρn.marginalB α) :
    ρn.smoothConditionalMinEntropyFixedSubnormalized ρn.marginalB.toSubnormalized ε ≥
      (n : ℝ) * H - QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
  subst α
  have hden :
      0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
    Real.sqrt_pos.mpr hM
  have hfrac :
      0 <
        Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)) :=
    div_pos hnum hden
  have hα_gt :
      1 <
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)) := by
    linarith
  have hcore :
      ρn.smoothConditionalMinEntropyFixedSubnormalized
          ρn.marginalB.toSubnormalized ε ≥
        ρn.conditionalEntropy -
          4 *
              (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                    (2 * log2 η * Real.sqrt (n : ℝ)) -
                  1) *
              (log2 (ρn.finiteAEPEta hρn hρnB)) ^ 2 -
            (1 /
                (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                    (2 * log2 η * Real.sqrt (n : ℝ)) -
                  1)) *
              log2 (2 / ε ^ 2) := by
    exact
      ρn.finiteAEP_core_posDef_of_fixedPetzSmoothMinG_petzTrace
        hρn hρnB ε
        (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
        hε_pos hε_lt hα_gt hα_le_two hα_lt hpetz
  rw [hentropy_tensor] at hcore
  have hcoeff_nonneg :
      0 ≤
        4 *
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) -
            1) := by
    nlinarith
  have hquad :
      4 *
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) -
            1) *
          (log2 (ρn.finiteAEPEta hρn hρnB)) ^ 2 ≤
        4 *
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) -
            1) *
          ((n : ℝ) * (log2 η) ^ 2) :=
    mul_le_mul_of_nonneg_left heta_tensor hcoeff_nonneg
  have hscalar :
      4 *
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) -
            1) *
          (n : ℝ) *
          (log2 η) ^ 2 +
        (1 /
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) -
              1)) *
          log2 (2 / ε ^ 2) =
          QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      QIT.finiteAEP_penalty_optimized_eq ε η (n := n) hM hL hn
  have hpenalty :
      4 *
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) -
            1) *
          (log2 (ρn.finiteAEPEta hρn hρnB)) ^ 2 +
        (1 /
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) -
              1)) *
          log2 (2 / ε ^ 2) ≤
        QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
    calc
      4 *
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) -
              1) *
            (log2 (ρn.finiteAEPEta hρn hρnB)) ^ 2 +
          (1 /
              (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                  (2 * log2 η * Real.sqrt (n : ℝ)) -
                1)) *
            log2 (2 / ε ^ 2) ≤
          4 *
              (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                  (2 * log2 η * Real.sqrt (n : ℝ)) -
                1) *
              ((n : ℝ) * (log2 η) ^ 2) +
            (1 /
                (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                    (2 * log2 η * Real.sqrt (n : ℝ)) -
                  1)) *
              log2 (2 / ε ^ 2) := by
        linarith
      _ =
          4 *
              (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                  (2 * log2 η * Real.sqrt (n : ℝ)) -
                1) *
              (n : ℝ) *
              (log2 η) ^ 2 +
            (1 /
                (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                    (2 * log2 η * Real.sqrt (n : ℝ)) -
                  1)) *
              log2 (2 / ε ^ 2) := by
        ring
      _ = QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := hscalar
  linarith

/-- Optimized scalar-choice finite-AEP core with the remaining source step
expressed as the Petz effect-variational inequality. -/
theorem finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational
    (ρn : State (Prod a b)) (hρn : ρn.matrix.PosDef)
    (hρnB : ρn.marginalB.matrix.PosDef)
    (ε η α H : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hL : 0 < log2 η)
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρn.finiteAEPEta hρn hρnB)))
    (hentropy_tensor : ρn.conditionalEntropy = (n : ℝ) * H)
    (heta_tensor :
      (log2 (ρn.finiteAEPEta hρn hρnB)) ^ 2 ≤
        (n : ℝ) * (log2 η) ^ 2)
    (hvar :
      let hα_gt : 1 < α := by
        rw [hα_opt]
        have hden :
            0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
          exact mul_pos (mul_pos (by norm_num) hL)
            (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
        have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
          Real.sqrt_pos.mpr hM
        have hfrac :
            0 <
              Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) :=
          div_pos hnum hden
        linarith
      let lam : ℝ :=
        ρn.petzSmoothMinThresholdScale hρn ρn.marginalB hρnB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational ρn.matrix
        (identityTensorStateMatrix (a := a) ρn.marginalB) lam α) :
    ρn.smoothConditionalMinEntropyFixedSubnormalized ρn.marginalB.toSubnormalized ε ≥
      (n : ℝ) * H - QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
  have hα_gt : 1 < α := by
    rw [hα_opt]
    have hden :
        0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
      exact mul_pos (mul_pos (by norm_num) hL)
        (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
    have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
      Real.sqrt_pos.mpr hM
    have hfrac :
        0 <
          Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 η * Real.sqrt (n : ℝ)) :=
      div_pos hnum hden
    linarith
  let lam : ℝ :=
    ρn.petzSmoothMinThresholdScale hρn ρn.marginalB hρnB ε α
      (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
  have hlam : 0 < lam := by
    simpa [lam] using
      ρn.petzSmoothMinThresholdScale_pos hρn ρn.marginalB hρnB ε α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
  have hvar_lam :
      cMatrixPetzTraceEffectVariational ρn.matrix
        (identityTensorStateMatrix (a := a) ρn.marginalB) lam α := by
    simpa [lam, hα_gt] using hvar
  have hpetz :
      (ρn.fixedPetzThresholdPositivePart ρn.marginalB lam).trace.re ≤
        lam ^ (1 - α) * ρn.conditionalPetzRenyiTraceTerm ρn.marginalB α :=
    ρn.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_effect_variational
      hρn ρn.marginalB hρnB hlam hα_gt hα_le_two hvar_lam
  exact
    ρn.finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_petzTrace
      hρn hρnB ε η α H hM hL hn hα_opt hε_pos hε_lt hα_le_two hα_lt
      hentropy_tensor heta_tensor
      (by simpa [lam, hα_gt] using hpetz)

/-- Optimized scalar-choice finite-AEP core with the remaining source step
expressed as Petz monotonicity under the threshold-eigenbasis dephasing map.

This is the same assembly as
`finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational`, but
it isolates the noncommutative Appendix input as the source-shaped
`cMatrixPetzTraceUnitaryDephaseMonotone` predicate instead of the stronger
effect-variational package. -/
theorem finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_unitaryDephaseMonotone
    (ρn : State (Prod a b)) (hρn : ρn.matrix.PosDef)
    (hρnB : ρn.marginalB.matrix.PosDef)
    (ε η α H : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hL : 0 < log2 η)
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρn.finiteAEPEta hρn hρnB)))
    (hentropy_tensor : ρn.conditionalEntropy = (n : ℝ) * H)
    (heta_tensor :
      (log2 (ρn.finiteAEPEta hρn hρnB)) ^ 2 ≤
        (n : ℝ) * (log2 η) ^ 2)
    (hmono :
      let hα_gt : 1 < α := by
        rw [hα_opt]
        have hden :
            0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
          exact mul_pos (mul_pos (by norm_num) hL)
            (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
        have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
          Real.sqrt_pos.mpr hM
        have hfrac :
            0 <
              Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) :=
          div_pos hnum hden
        linarith
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        ρn.petzSmoothMinThresholdScale hρn ρn.marginalB hρnB ε α hα_pos
          hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) ρn.marginalB).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) ρn.marginalB hρnB
      let Hmat : CMatrix (Prod a b) :=
        ρn.matrix - lam • identityTensorStateMatrix (a := a) ρn.marginalB
      let hH : Hmat.IsHermitian :=
        hρn.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρn.petzSmoothMinThresholdScale_pos hρn ρn.marginalB hρnB ε α
            hα_pos hα_ne_one)).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρn.matrix
        (identityTensorStateMatrix (a := a) ρn.marginalB) U α) :
    ρn.smoothConditionalMinEntropyFixedSubnormalized ρn.marginalB.toSubnormalized ε ≥
      (n : ℝ) * H - QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
  have hα_gt : 1 < α := by
    rw [hα_opt]
    have hden :
        0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
      exact mul_pos (mul_pos (by norm_num) hL)
        (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
    have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
      Real.sqrt_pos.mpr hM
    have hfrac :
        0 <
          Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 η * Real.sqrt (n : ℝ)) :=
      div_pos hnum hden
    linarith
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let lam : ℝ :=
    ρn.petzSmoothMinThresholdScale hρn ρn.marginalB hρnB ε α hα_pos hα_ne_one
  have hlam : 0 < lam := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρn.petzSmoothMinThresholdScale_pos hρn ρn.marginalB hρnB ε α
        hα_pos hα_ne_one
  have hmono_lam :
      let hB : (identityTensorStateMatrix (a := a) ρn.marginalB).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) ρn.marginalB hρnB
      let Hmat : CMatrix (Prod a b) :=
        ρn.matrix - lam • identityTensorStateMatrix (a := a) ρn.marginalB
      let hH : Hmat.IsHermitian :=
        hρn.isHermitian.sub ((Matrix.PosDef.smul hB hlam).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρn.matrix
        (identityTensorStateMatrix (a := a) ρn.marginalB) U α := by
    simpa [lam, hα_gt, hα_pos, hα_ne_one, hlam] using hmono
  have hpetz :
      (ρn.fixedPetzThresholdPositivePart ρn.marginalB lam).trace.re ≤
        lam ^ (1 - α) * ρn.conditionalPetzRenyiTraceTerm ρn.marginalB α :=
    ρn.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_unitaryDephaseMonotone
      hρn ρn.marginalB hρnB hlam hα_gt hα_le_two hmono_lam
  exact
    ρn.finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_petzTrace
      hρn hρnB ε η α H hM hL hn hα_opt hε_pos hε_lt hα_le_two hα_lt
      hentropy_tensor heta_tensor
      (by simpa [lam, hα_gt, hα_pos, hα_ne_one] using hpetz)

theorem tensorPowerBipartite_posDef_forFiniteAEP
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef) (n : ℕ) :
    (ρ.tensorPowerBipartite n).matrix.PosDef :=
  State.tensorPowerBipartite_posDef_forAEP ρ hρ n

theorem tensorPowerBipartite_marginalB_posDef_forFiniteAEP
    (ρ : State (Prod a b)) (_hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef) (n : ℕ) :
    (ρ.tensorPowerBipartite n).marginalB.matrix.PosDef :=
  State.tensorPowerBipartite_marginalB_posDef_forAEP ρ _hρ hρB n

theorem tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP
    (ρ : State (Prod a b))
    (hρB : ρ.marginalB.matrix.PosDef) (n : ℕ) :
    (ρ.tensorPowerBipartite n).marginalB.matrix.PosDef := by
  rw [State.tensorPowerBipartite_marginalB ρ n]
  exact State.tensorPower_posDef hρB n

theorem tensorPowerBipartite_succ_grouped
    (ρ : State (Prod a b)) (n : ℕ) :
    ρ.tensorPowerBipartite (n + 1) =
      (ρ.prod (ρ.tensorPowerBipartite n)).reindex
        (conditionalPetzRenyiProductGroupingEquiv
          a b (TensorPower a n) (TensorPower b n)) := by
  ext x y
  rcases x with ⟨⟨xA, xsA⟩, ⟨xB, xsB⟩⟩
  rcases y with ⟨⟨yA, ysA⟩, ⟨yB, ysB⟩⟩
  simp [State.tensorPowerBipartite, State.tensorPower_succ,
    conditionalPetzRenyiProductGroupingEquiv, tensorPowerProdEquiv,
    State.prod, State.reindex, Matrix.kronecker, Matrix.kroneckerMap_apply]

theorem tensorPowerBipartite_succ_grouped_marginalB
    (ρ : State (Prod a b)) (n : ℕ) :
    (((ρ.prod (ρ.tensorPowerBipartite n)).reindex
        (conditionalPetzRenyiProductGroupingEquiv
          a b (TensorPower a n) (TensorPower b n))).marginalB) =
      ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB := by
  ext x y
  rcases x with ⟨xB, xsB⟩
  rcases y with ⟨yB, ysB⟩
  simp [State.marginalB, partialTraceA, State.prod, State.reindex,
    conditionalPetzRenyiProductGroupingEquiv, Matrix.kronecker,
        Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Applying two right-reference isometries before taking a product state is
the same as applying their product isometry after the standard regrouping. -/
theorem conditioningIsometryApply_prod_reindex_grouped
    {a' : Type*} {c : Type*} {bPlus : Type*} {cPlus : Type*}
    [Fintype a'] [DecidableEq a'] [Fintype c] [DecidableEq c]
    [Fintype bPlus] [DecidableEq bPlus] [Fintype cPlus] [DecidableEq cPlus]
    (ρ : State (Prod a b)) (σ : State (Prod a' c))
    (V : ReferenceIsometry b bPlus) (W : ReferenceIsometry c cPlus) :
    ((ρ.conditioningIsometryApply V).prod (σ.conditioningIsometryApply W)).reindex
        (conditionalPetzRenyiProductGroupingEquiv a bPlus a' cPlus) =
      State.conditioningIsometryApply
        ((ρ.prod σ).reindex (conditionalPetzRenyiProductGroupingEquiv a b a' c))
        (V.prod W) := by
  apply State.ext
  ext x y
  rcases x with ⟨⟨xA, xA'⟩, ⟨xB, xC⟩⟩
  rcases y with ⟨⟨yA, yA'⟩, ⟨yB, yC⟩⟩
  simp [State.prod, State.reindex, State.conditioningIsometryApply_matrix,
    ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
    ReferenceIsometry.prod, conditionalPetzRenyiProductGroupingEquiv,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.mul_apply,
    Matrix.conjTranspose, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum]
  conv_lhs =>
    enter [2, z]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, z, 2, w]
    rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℂ) (s₁ := (Finset.univ : Finset b)) rfl ?_
  intro z _
  refine Finset.sum_congr (M := ℂ) (s₁ := (Finset.univ : Finset c)) rfl ?_
  intro zc _
  refine Finset.sum_congr (M := ℂ) (s₁ := (Finset.univ : Finset b)) rfl ?_
  intro zb _
  refine Finset.sum_congr (M := ℂ) (s₁ := (Finset.univ : Finset c)) rfl ?_
  intro zw _
  ring_nf

/-- Tensor powers commute with applying a right-reference isometry to the
conditioning register, using the tensor-power product isometry on `B^n`. -/
theorem conditioningIsometryApply_tensorPowerBipartite
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (ρ : State (Prod a b)) (V : ReferenceIsometry b bPlus) :
    ∀ n : ℕ,
      (ρ.conditioningIsometryApply V).tensorPowerBipartite n =
        (ρ.tensorPowerBipartite n).conditioningIsometryApply (V.tensorPower n)
  | 0 => by
      apply State.ext
      ext x y
      rcases x with ⟨xA, xB⟩
      rcases y with ⟨yA, yB⟩
      cases xA
      cases xB
      cases yA
      cases yB
      simp [State.tensorPowerBipartite, State.tensorPower, State.reindex,
        State.conditioningIsometryApply_matrix, ReferenceIsometry.applyMatrixRight,
        ReferenceIsometry.rightBlock, ReferenceIsometry.tensorPower,
        Matrix.mul_apply, Matrix.conjTranspose, TensorPower, tensorPowerProdEquiv]
      rfl
  | n + 1 => by
      have ih := conditioningIsometryApply_tensorPowerBipartite ρ V n
      rw [State.tensorPowerBipartite_succ_grouped]
      rw [ih]
      rw [conditioningIsometryApply_prod_reindex_grouped]
      rw [← State.tensorPowerBipartite_succ_grouped]
      rfl

/-- Embedding normalized states as subnormalized states commutes with applying
a right-reference isometry. -/
theorem toSubnormalized_conditioningIsometryApply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (ρ : State (Prod a b)) (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).toSubnormalized =
      ρ.toSubnormalized.conditioningIsometryApply V := by
  apply SubnormalizedState.ext
  rw [State.toSubnormalized_matrix]
  rw [SubnormalizedState.conditioningIsometryApply_matrix]
  rw [State.conditioningIsometryApply_matrix]
  rfl

theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_succ_of_regroupedCandidate
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : ℕ)
    (hregroup :
      (ρ.tensorPowerBipartite (n + 1)).conditionalPetzRenyiEntropyCandidate
          (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ (n + 1))
          (ρ.tensorPowerBipartite (n + 1)).marginalB
          (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB (n + 1))
          α hα_pos hα_ne_one =
        (((ρ.prod (ρ.tensorPowerBipartite n)).reindex
            (conditionalPetzRenyiProductGroupingEquiv
              a b (TensorPower a n) (TensorPower b n))).conditionalPetzRenyiEntropyCandidate
            (State.reindex_posDef_of_posDef
              (ρ.prod (ρ.tensorPowerBipartite n))
              (State.prod_posDef hρ
                (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n))
              (conditionalPetzRenyiProductGroupingEquiv
                a b (TensorPower a n) (TensorPower b n)))
            (ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB)
            (State.prod_posDef hρB
              (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n))
            α hα_pos hα_ne_one)) :
    (ρ.tensorPowerBipartite (n + 1)).conditionalPetzRenyiEntropyCandidate
        (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ (n + 1))
        (ρ.tensorPowerBipartite (n + 1)).marginalB
        (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB (n + 1))
        α hα_pos hα_ne_one =
      ρ.conditionalPetzRenyiEntropyCandidate
          hρ ρ.marginalB hρB α hα_pos hα_ne_one +
        (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
          (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
          (ρ.tensorPowerBipartite n).marginalB
          (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
          α hα_pos hα_ne_one := by
  have hprod :=
    conditionalPetzRenyiEntropyCandidate_prod_grouped_posDef
      (ρ₁ := ρ) (σ₁ := ρ.marginalB)
      (ρ₂ := ρ.tensorPowerBipartite n)
      (σ₂ := (ρ.tensorPowerBipartite n).marginalB)
      hρ hρB
      (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
      (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
      α hα_pos hα_ne_one
  exact hregroup.trans hprod

theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_succ
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : ℕ) :
    (ρ.tensorPowerBipartite (n + 1)).conditionalPetzRenyiEntropyCandidate
        (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ (n + 1))
        (ρ.tensorPowerBipartite (n + 1)).marginalB
        (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB (n + 1))
        α hα_pos hα_ne_one =
      ρ.conditionalPetzRenyiEntropyCandidate
          hρ ρ.marginalB hρB α hα_pos hα_ne_one +
        (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
          (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
          (ρ.tensorPowerBipartite n).marginalB
          (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
          α hα_pos hα_ne_one := by
  refine
    tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_succ_of_regroupedCandidate
      ρ hρ hρB α hα_pos hα_ne_one n ?_
  let τ : State (Prod (Prod a (TensorPower a n)) (Prod b (TensorPower b n))) :=
    (ρ.prod (ρ.tensorPowerBipartite n)).reindex
      (conditionalPetzRenyiProductGroupingEquiv
        a b (TensorPower a n) (TensorPower b n))
  have hτ :
      ρ.tensorPowerBipartite (n + 1) = τ :=
    tensorPowerBipartite_succ_grouped ρ n
  have hτB :
      τ.marginalB = ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB := by
    simpa [τ] using tensorPowerBipartite_succ_grouped_marginalB ρ n
  have hτ_matrix :
      (ρ.tensorPowerBipartite (n + 1)).matrix = τ.matrix :=
    congrArg State.matrix hτ
  have hτ_matrix' :
      Matrix.submatrix (ρ.tensorPower (n + 1)).matrix
          (tensorPowerProdEquiv a b (n + 1)).symm
          (tensorPowerProdEquiv a b (n + 1)).symm =
        Matrix.submatrix (ρ.prod (ρ.tensorPowerBipartite n)).matrix
          (conditionalPetzRenyiProductGroupingEquiv
            a b (TensorPower a n) (TensorPower b n)).symm
          (conditionalPetzRenyiProductGroupingEquiv
            a b (TensorPower a n) (TensorPower b n)).symm := by
    simpa [State.tensorPowerBipartite_matrix, τ, State.reindex_matrix] using hτ_matrix
  have hτB_matrix :
      (ρ.tensorPowerBipartite (n + 1)).marginalB.matrix =
        (ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB).matrix := by
    simpa [← hτ] using congrArg State.matrix hτB
  have hτB_ref :
      identityTensorStateMatrix (a := TensorPower a (n + 1))
          (ρ.tensorPowerBipartite (n + 1)).marginalB =
        identityTensorStateMatrix (a := Prod a (TensorPower a n))
          (ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB) := by
    ext i j
    by_cases hij : i.1 = j.1
    · simp [identityTensorStateMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.one_apply, hij]
      exact congrFun (congrFun hτB_matrix i.2) j.2
    · simp [identityTensorStateMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.one_apply, hij]
      intro h
      exact False.elim (hij h)
  dsimp [conditionalPetzRenyiEntropyCandidate, conditionalPetzRenyiTraceTerm]
  rw [hτ_matrix', hτB_ref]
  rfl

theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidateFullReference_succ
    (ρ : State (Prod a b)) (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : ℕ) :
    (ρ.tensorPowerBipartite (n + 1)).conditionalPetzRenyiEntropyCandidateFullReference
        (ρ.tensorPowerBipartite (n + 1)).marginalB
        (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB (n + 1))
        α hα_pos hα_ne_one =
      ρ.conditionalPetzRenyiEntropyCandidateFullReference
          ρ.marginalB hρB α hα_pos hα_ne_one +
        (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidateFullReference
          (ρ.tensorPowerBipartite n).marginalB
          (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB n)
          α hα_pos hα_ne_one := by
  let τ : State (Prod (Prod a (TensorPower a n)) (Prod b (TensorPower b n))) :=
    (ρ.prod (ρ.tensorPowerBipartite n)).reindex
      (conditionalPetzRenyiProductGroupingEquiv
        a b (TensorPower a n) (TensorPower b n))
  have hτ :
      ρ.tensorPowerBipartite (n + 1) = τ :=
    tensorPowerBipartite_succ_grouped ρ n
  have hτB :
      τ.marginalB = ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB := by
    simpa [τ] using tensorPowerBipartite_succ_grouped_marginalB ρ n
  have hregroup :
      (ρ.tensorPowerBipartite (n + 1)).conditionalPetzRenyiEntropyCandidateFullReference
          (ρ.tensorPowerBipartite (n + 1)).marginalB
          (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB (n + 1))
          α hα_pos hα_ne_one =
        τ.conditionalPetzRenyiEntropyCandidateFullReference
          (ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB)
          (State.prod_posDef hρB
            (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB n))
          α hα_pos hα_ne_one := by
    have hτ_matrix :
        (ρ.tensorPowerBipartite (n + 1)).matrix = τ.matrix :=
      congrArg State.matrix hτ
    have hτ_matrix' :
        Matrix.submatrix (ρ.tensorPower (n + 1)).matrix
            (tensorPowerProdEquiv a b (n + 1)).symm
            (tensorPowerProdEquiv a b (n + 1)).symm =
          Matrix.submatrix (ρ.prod (ρ.tensorPowerBipartite n)).matrix
            (conditionalPetzRenyiProductGroupingEquiv
              a b (TensorPower a n) (TensorPower b n)).symm
            (conditionalPetzRenyiProductGroupingEquiv
              a b (TensorPower a n) (TensorPower b n)).symm := by
      simpa [State.tensorPowerBipartite_matrix, τ, State.reindex_matrix] using hτ_matrix
    have hτ_matrix_def :
        τ.matrix =
          Matrix.submatrix (ρ.prod (ρ.tensorPowerBipartite n)).matrix
            (conditionalPetzRenyiProductGroupingEquiv
              a b (TensorPower a n) (TensorPower b n)).symm
            (conditionalPetzRenyiProductGroupingEquiv
              a b (TensorPower a n) (TensorPower b n)).symm := by
      simp [τ, State.reindex_matrix]
    have hτB_matrix :
        (ρ.tensorPowerBipartite (n + 1)).marginalB.matrix =
          (ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB).matrix := by
      simpa [← hτ] using congrArg State.matrix hτB
    have hτB_ref :
        identityTensorStateMatrix (a := TensorPower a (n + 1))
            (ρ.tensorPowerBipartite (n + 1)).marginalB =
          identityTensorStateMatrix (a := Prod a (TensorPower a n))
            (ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB) := by
      ext i j
      by_cases hij : i.1 = j.1
      · simp [identityTensorStateMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
          Matrix.one_apply, hij]
        exact congrFun (congrFun hτB_matrix i.2) j.2
      · simp [identityTensorStateMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
          Matrix.one_apply, hij]
        intro h
        exact False.elim (hij h)
    dsimp [conditionalPetzRenyiEntropyCandidateFullReference, conditionalPetzRenyiTraceTerm]
    rw [hτ_matrix', hτB_ref, hτ_matrix_def]
    rfl
  have hprod :=
    conditionalPetzRenyiEntropyCandidateFullReference_prod_grouped
      (ρ₁ := ρ) (σ₁ := ρ.marginalB)
      (ρ₂ := ρ.tensorPowerBipartite n)
      (σ₂ := (ρ.tensorPowerBipartite n).marginalB)
      hρB
      (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB n)
      α hα_pos hα_ne_one
  exact hregroup.trans hprod

theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_zero
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    (ρ.tensorPowerBipartite 0).conditionalPetzRenyiEntropyCandidate
        (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ 0)
        (ρ.tensorPowerBipartite 0).marginalB
        (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB 0)
        α hα_pos hα_ne_one = 0 := by
  have hmat :
      (ρ.tensorPowerBipartite 0).matrix =
        (1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) := by
    ext x y
    rcases x with ⟨xA, xB⟩
    rcases y with ⟨yA, yB⟩
    cases xA
    cases xB
    cases yA
    cases yB
    simp [State.tensorPowerBipartite, State.tensorPower, State.reindex,
      State.unit, TensorPower, tensorPowerProdEquiv]
  have hBmat :
      (ρ.tensorPowerBipartite 0).marginalB.matrix =
        (1 : CMatrix (TensorPower b 0)) := by
    ext x y
    cases x
    cases y
    change partialTraceA (a := TensorPower a 0) (b := TensorPower b 0)
        (ρ.tensorPowerBipartite 0).matrix PUnit.unit PUnit.unit =
      (1 : CMatrix (TensorPower b 0)) PUnit.unit PUnit.unit
    rw [hmat]
    simp [partialTraceA, TensorPower]
    change (1 : ℂ) = 1
    norm_num
  have href :
      identityTensorStateMatrix (a := TensorPower a 0)
          (ρ.tensorPowerBipartite 0).marginalB =
        (1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) := by
    ext x y
    rcases x with ⟨xA, xB⟩
    rcases y with ⟨yA, yB⟩
    cases xA
    cases xB
    cases yA
    cases yB
    change
      (Matrix.kronecker (1 : CMatrix (TensorPower a 0))
          (ρ.tensorPowerBipartite 0).marginalB.matrix)
        (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit) =
        (1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0)))
          (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit)
    rw [hBmat]
    simp [TensorPower, Matrix.kronecker, Matrix.kroneckerMap_apply]
    change (1 : ℂ) * 1 = 1
    norm_num
  unfold conditionalPetzRenyiEntropyCandidate
  rw [hmat, href]
  dsimp only
  change 1 / (1 - α) *
      log2 ((((1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) ^ α) *
        ((1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) ^ (1 - α))).trace.re) =
    0
  rw [show ((1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) ^ α) = 1 by
      exact CFC.one_rpow,
    show ((1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) ^ (1 - α)) = 1 by
      exact CFC.one_rpow,
    one_mul, Matrix.trace_one]
  have hcard : Fintype.card (Prod (TensorPower a 0) (TensorPower b 0)) = 1 := by
    change Fintype.card (PUnit × PUnit) = 1
    simp
  simp [hcard, log2]

theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidateFullReference_zero
    (ρ : State (Prod a b)) (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    (ρ.tensorPowerBipartite 0).conditionalPetzRenyiEntropyCandidateFullReference
        (ρ.tensorPowerBipartite 0).marginalB
        (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB 0)
        α hα_pos hα_ne_one = 0 := by
  have hmat :
      (ρ.tensorPowerBipartite 0).matrix =
        (1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) := by
    ext x y
    rcases x with ⟨xA, xB⟩
    rcases y with ⟨yA, yB⟩
    cases xA
    cases xB
    cases yA
    cases yB
    simp [State.tensorPowerBipartite, State.tensorPower, State.reindex,
      State.unit, TensorPower, tensorPowerProdEquiv]
  have hBmat :
      (ρ.tensorPowerBipartite 0).marginalB.matrix =
        (1 : CMatrix (TensorPower b 0)) := by
    ext x y
    cases x
    cases y
    change partialTraceA (a := TensorPower a 0) (b := TensorPower b 0)
        (ρ.tensorPowerBipartite 0).matrix PUnit.unit PUnit.unit =
      (1 : CMatrix (TensorPower b 0)) PUnit.unit PUnit.unit
    rw [hmat]
    simp [partialTraceA, TensorPower]
    change (1 : ℂ) = 1
    norm_num
  have href :
      identityTensorStateMatrix (a := TensorPower a 0)
          (ρ.tensorPowerBipartite 0).marginalB =
        (1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) := by
    ext x y
    rcases x with ⟨xA, xB⟩
    rcases y with ⟨yA, yB⟩
    cases xA
    cases xB
    cases yA
    cases yB
    change
      (Matrix.kronecker (1 : CMatrix (TensorPower a 0))
          (ρ.tensorPowerBipartite 0).marginalB.matrix)
        (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit) =
        (1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0)))
          (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit)
    rw [hBmat]
    simp [TensorPower, Matrix.kronecker, Matrix.kroneckerMap_apply]
    change (1 : ℂ) * 1 = 1
    norm_num
  unfold conditionalPetzRenyiEntropyCandidateFullReference conditionalPetzRenyiTraceTerm
  rw [hmat, href]
  change 1 / (1 - α) *
      log2 ((((1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) ^ α) *
        ((1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) ^ (1 - α))).trace.re) =
    0
  rw [show ((1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) ^ α) = 1 by
      exact CFC.one_rpow,
    show ((1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) ^ (1 - α)) = 1 by
      exact CFC.one_rpow,
    one_mul, Matrix.trace_one]
  have hcard : Fintype.card (Prod (TensorPower a 0) (TensorPower b 0)) = 1 := by
    change Fintype.card (PUnit × PUnit) = 1
    simp
  simp [hcard, log2]

/-- Conditional Petz alpha-entropy candidate is additive on bipartite tensor
powers relative to the corresponding tensor-power marginal reference. -/
theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_additive
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : ℕ) :
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
        (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
        (ρ.tensorPowerBipartite n).marginalB
        (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
        α hα_pos hα_ne_one =
      (n : ℝ) *
        ρ.conditionalPetzRenyiEntropyCandidate
          hρ ρ.marginalB hρB α hα_pos hα_ne_one := by
  induction n with
  | zero =>
      rw [tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_zero
        ρ hρ hρB α hα_pos hα_ne_one]
      simp
  | succ n ih =>
      rw [tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_succ
        ρ hρ hρB α hα_pos hα_ne_one n]
      rw [ih]
      rw [Nat.cast_add, Nat.cast_one]
      ring

/-- Full-reference conditional Petz alpha-entropy candidate is additive on
bipartite tensor powers relative to the corresponding tensor-power marginal
reference, without requiring the left state to be full-rank. -/
theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidateFullReference_additive
    (ρ : State (Prod a b)) (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : ℕ) :
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidateFullReference
        (ρ.tensorPowerBipartite n).marginalB
        (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB n)
        α hα_pos hα_ne_one =
      (n : ℝ) *
        ρ.conditionalPetzRenyiEntropyCandidateFullReference
          ρ.marginalB hρB α hα_pos hα_ne_one := by
  induction n with
  | zero =>
      rw [tensorPowerBipartite_conditionalPetzRenyiEntropyCandidateFullReference_zero
        ρ hρB α hα_pos hα_ne_one]
      simp
  | succ n ih =>
      rw [tensorPowerBipartite_conditionalPetzRenyiEntropyCandidateFullReference_succ
        ρ hρB α hα_pos hα_ne_one n]
      rw [ih]
      rw [Nat.cast_add, Nat.cast_one]
      ring

/-- Tensor-power alpha-to-von-Neumann lower bound using single-copy eta and
conditional Petz alpha-entropy additivity.

This is the source-shaped route for TCR finite AEP: apply the one-copy
alpha-bound and then use additivity of the fixed-reference conditional Petz
candidate, instead of bounding the tensor-power convergence parameter. -/
theorem tensorPower_conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) {n : ℕ}
    (hα_gt : 1 < α)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB))) :
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
        (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
        (ρ.tensorPowerBipartite n).marginalB
        (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
        α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
      (n : ℝ) * ρ.conditionalEntropy -
        4 * (α - 1) * (n : ℝ) *
          (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  have hsingle :
      ρ.conditionalPetzRenyiEntropyCandidate
          hρ ρ.marginalB hρB α hα_pos hα_ne_one ≥
        ρ.conditionalEntropy -
          4 * (α - 1) * (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 := by
    have h :=
      conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef
        (ρ := ρ) hρ (σ := ρ.marginalB) hρB α hα_gt
        (by simpa [finiteAEPEta_eq] using hα_lt)
    rw [ρ.conditionalEntropyRelative_to_conditionalEntropy hρ hρB] at h
    simpa [finiteAEPEta_eq, hα_pos, hα_ne_one] using h
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hmul :
      (n : ℝ) *
          (ρ.conditionalEntropy -
            4 * (α - 1) * (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2) ≤
        (n : ℝ) *
          ρ.conditionalPetzRenyiEntropyCandidate
            hρ ρ.marginalB hρB α hα_pos hα_ne_one :=
    mul_le_mul_of_nonneg_left hsingle hn_nonneg
  calc
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
        (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
        (ρ.tensorPowerBipartite n).marginalB
        (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
        α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
        = (n : ℝ) *
            ρ.conditionalPetzRenyiEntropyCandidate
              hρ ρ.marginalB hρB α hα_pos hα_ne_one := by
          simpa [hα_pos, hα_ne_one] using
            tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_additive
              ρ hρ hρB α hα_pos hα_ne_one n
    _ ≥
        (n : ℝ) *
          (ρ.conditionalEntropy -
            4 * (α - 1) * (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2) := hmul
    _ =
        (n : ℝ) * ρ.conditionalEntropy -
          4 * (α - 1) * (n : ℝ) *
            (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 := by
          ring

/-- Full-reference tensor-power alpha-to-von-Neumann lower bound using the
single-copy trace eta.

This is the arbitrary-left-state analogue of
`tensorPower_conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef`: the
joint tensor-power state is not assumed full-rank, while the canonical side
reference is propagated as a full-rank marginal reference. -/
theorem tensorPower_conditionalPetzRenyiEntropyCandidateFullReference_alpha_bound
    (ρ : State (Prod a b))
    (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) {n : ℕ}
    (hα_gt : 1 < α)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 ρ.finiteAEPEtaTrace)) :
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidateFullReference
        (ρ.tensorPowerBipartite n).marginalB
        (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB n)
        α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
      (n : ℝ) * ρ.conditionalEntropy -
        4 * (α - 1) * (n : ℝ) *
          (log2 ρ.finiteAEPEtaTrace) ^ 2 := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  have hsingle :
      ρ.conditionalPetzRenyiEntropyCandidateFullReference
          ρ.marginalB hρB α hα_pos hα_ne_one ≥
        ρ.conditionalEntropy -
          4 * (α - 1) * (log2 ρ.finiteAEPEtaTrace) ^ 2 := by
    have h :=
      conditionalPetzRenyiEntropyCandidateFullReference_alpha_bound
        (ρ := ρ) (σ := ρ.marginalB) hρB α hα_gt
        (by simpa [finiteAEPEtaTrace] using hα_lt)
    rw [ρ.conditionalEntropyRelativeFullReference_to_conditionalEntropy hρB] at h
    simpa [finiteAEPEtaTrace, hα_pos, hα_ne_one] using h
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hmul :
      (n : ℝ) *
          (ρ.conditionalEntropy -
            4 * (α - 1) * (log2 ρ.finiteAEPEtaTrace) ^ 2) ≤
        (n : ℝ) *
          ρ.conditionalPetzRenyiEntropyCandidateFullReference
            ρ.marginalB hρB α hα_pos hα_ne_one :=
    mul_le_mul_of_nonneg_left hsingle hn_nonneg
  calc
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidateFullReference
        (ρ.tensorPowerBipartite n).marginalB
        (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB n)
        α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
        = (n : ℝ) *
            ρ.conditionalPetzRenyiEntropyCandidateFullReference
              ρ.marginalB hρB α hα_pos hα_ne_one := by
          simpa [hα_pos, hα_ne_one] using
            tensorPowerBipartite_conditionalPetzRenyiEntropyCandidateFullReference_additive
              ρ hρB α hα_pos hα_ne_one n
    _ ≥
        (n : ℝ) *
          (ρ.conditionalEntropy -
            4 * (α - 1) * (log2 ρ.finiteAEPEtaTrace) ^ 2) := hmul
    _ =
        (n : ℝ) * ρ.conditionalEntropy -
          4 * (α - 1) * (n : ℝ) *
            (log2 ρ.finiteAEPEtaTrace) ^ 2 := by
          ring

/-- Optimized scalar-choice fixed-reference finite-AEP core from a
full-reference tensor/source-shaped Petz alpha lower bound.

The left state is arbitrary.  The only reference-side hypothesis is that the
fixed side reference is full-rank, which is enough for the full-reference
smooth-min/Petz lower bound. -/
theorem finiteAEP_core_fullReference_optimized_petzAlphaBound
    (ρn : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε η α H : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hL : 0 < log2 η)
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hpetz_alpha :
      ρn.conditionalPetzRenyiEntropyCandidateFullReference
          σ hσ α
          (by
            rw [hα_opt]
            have hden :
                0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
              exact mul_pos (mul_pos (by norm_num) hL)
                (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
            have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
              Real.sqrt_pos.mpr hM
            have hfrac :
                0 <
                  Real.sqrt (log2 (2 / ε ^ 2)) /
                    (2 * log2 η * Real.sqrt (n : ℝ)) :=
              div_pos hnum hden
            linarith)
          (by
            have hα_gt : 1 < α := by
              rw [hα_opt]
              have hden :
                  0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
                exact mul_pos (mul_pos (by norm_num) hL)
                  (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
              have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
                Real.sqrt_pos.mpr hM
              have hfrac :
                  0 <
                    Real.sqrt (log2 (2 / ε ^ 2)) /
                      (2 * log2 η * Real.sqrt (n : ℝ)) :=
                div_pos hnum hden
              linarith
            exact (ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * H - 4 * (α - 1) * (n : ℝ) * (log2 η) ^ 2) :
    ρn.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε ≥
      (n : ℝ) * H - QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
  subst α
  have hden :
      0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
    Real.sqrt_pos.mpr hM
  have hfrac :
      0 <
        Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)) :=
    div_pos hnum hden
  have hα_gt :
      1 <
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)) := by
    linarith
  have hsmooth :
      ρn.conditionalPetzRenyiEntropyCandidateFullReference σ hσ
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 η * Real.sqrt (n : ℝ)))
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
        (1 /
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) - 1)) *
          log2 (2 / ε ^ 2) ≤
        ρn.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε := by
    exact
      ρn.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_fullReference
        σ hσ ε
        (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
        hε_pos hε_lt hα_gt hα_le_two
  have hpetz_alpha' :
      ρn.conditionalPetzRenyiEntropyCandidateFullReference σ hσ
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 η * Real.sqrt (n : ℝ)))
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * H -
          4 *
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) - 1) *
            (n : ℝ) * (log2 η) ^ 2 := by
    simpa [hα_gt] using hpetz_alpha
  have hscalar :
      4 *
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) -
            1) *
          (n : ℝ) *
          (log2 η) ^ 2 +
        (1 /
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) -
              1)) *
          log2 (2 / ε ^ 2) =
          QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      QIT.finiteAEP_penalty_optimized_eq ε η (n := n) hM hL hn
  calc
    ρn.smoothConditionalMinEntropyFixedSubnormalized σ.toSubnormalized ε ≥
      (n : ℝ) * H -
        (4 *
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) -
              1) *
            (n : ℝ) *
            (log2 η) ^ 2 +
          (1 /
              (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                  (2 * log2 η * Real.sqrt (n : ℝ)) -
                1)) *
            log2 (2 / ε ^ 2)) := by
        linarith
    _ = (n : ℝ) * H - QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
        rw [hscalar]

/-- Tensor-power optimized finite-AEP core for arbitrary left state and
full-rank canonical marginal reference.

This is the full-reference source route: smooth-min is bounded by the
full-reference Petz candidate, while the Petz alpha term is tensorized by
additivity and the one-copy trace eta. -/
theorem tensorPowerFiniteAEP_core_fullReference_optimized_additivePetz
    (ρ : State (Prod a b))
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 ρ.finiteAEPEtaTrace * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 ρ.finiteAEPEtaTrace)) :
    (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
        (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε ρ.finiteAEPEtaTrace *
          Real.sqrt (n : ℝ) := by
  have hη3 : 3 ≤ ρ.finiteAEPEtaTrace := by
    simpa [finiteAEPEtaTrace] using
      conditionalAlphaConvergenceParameterTrace_ge_three
        (ρ := ρ) (σ := ρ.marginalB) hρB
  have hL : 0 < log2 ρ.finiteAEPEtaTrace := by
    unfold log2
    exact div_pos
      (Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hη3))
      (Real.log_pos one_lt_two)
  have hα_gt : 1 < α := by
    rw [hα_opt]
    have hden :
        0 < 2 * log2 ρ.finiteAEPEtaTrace * Real.sqrt (n : ℝ) := by
      exact mul_pos (mul_pos (by norm_num) hL)
        (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
    have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
      Real.sqrt_pos.mpr hM
    have hfrac :
        0 <
          Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 ρ.finiteAEPEtaTrace * Real.sqrt (n : ℝ)) :=
      div_pos hnum hden
    linarith
  have hpetz_alpha :
      (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidateFullReference
          (ρ.tensorPowerBipartite n).marginalB
          (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB n)
          α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * ρ.conditionalEntropy -
          4 * (α - 1) * (n : ℝ) *
            (log2 ρ.finiteAEPEtaTrace) ^ 2 :=
    ρ.tensorPower_conditionalPetzRenyiEntropyCandidateFullReference_alpha_bound
      hρB α hα_gt hα_lt
  exact
    (ρ.tensorPowerBipartite n).finiteAEP_core_fullReference_optimized_petzAlphaBound
      (ρ.tensorPowerBipartite n).marginalB
      (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB n)
      ε ρ.finiteAEPEtaTrace α ρ.conditionalEntropy hM hL hn hα_opt
      hε_pos hε_lt hα_le_two hpetz_alpha

/-- Tensor-power optimized finite-AEP core for optimized subnormalized smooth
min-entropy, using only a full-rank canonical marginal reference. -/
theorem tensorPowerFiniteAEP_core_fullReference_optimized_subnormalizedSmooth_additivePetz
    (ρ : State (Prod a b))
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 ρ.finiteAEPEtaTrace * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 ρ.finiteAEPEtaTrace)) :
    ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_pos.le hε_lt ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε ρ.finiteAEPEtaTrace *
          Real.sqrt (n : ℝ) := by
  have hfixedCore :
      (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
          (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε ≥
        (n : ℝ) * ρ.conditionalEntropy -
          QIT.finiteAEPDelta ε ρ.finiteAEPEtaTrace *
            Real.sqrt (n : ℝ) :=
    ρ.tensorPowerFiniteAEP_core_fullReference_optimized_additivePetz
      hρB ε α hM hn hα_opt hε_pos hε_lt hα_le_two hα_lt
  have hbridge :
      (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
          (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε ≤
        ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_pos.le hε_lt :=
    (ρ.tensorPowerBipartite n)
      |>.smoothConditionalMinEntropyFixedSubnormalized_le_subnormalizedSmoothConditionalMinEntropy
        (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε
        hε_pos.le hε_lt
        (fun ρ' _hball =>
          SubnormalizedState.conditionalMinEntropyFixed_feasibleSet_nonempty_of_posDef_reference
            (a := TensorPower a n) ρ' (ρ.tensorPowerBipartite n).marginalB
            (tensorPowerBipartite_marginalB_posDef_fullReference_forFiniteAEP ρ hρB n))
  exact le_trans hfixedCore hbridge

/-- Optimized scalar-choice finite-AEP core from a tensor/source-shaped Petz
alpha-bound.

Compared with
`finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational`, this
assembly lemma does not assume a tensor-power eta growth estimate.  It only
needs the already tensorized alpha-to-von-Neumann lower bound with the
single-copy eta parameter. -/
theorem finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational_petzAlphaBound
    (ρn : State (Prod a b)) (hρn : ρn.matrix.PosDef)
    (hρnB : ρn.marginalB.matrix.PosDef)
    (ε η α H : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hL : 0 < log2 η)
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hpetz_alpha :
      ρn.conditionalPetzRenyiEntropyCandidate
          hρn ρn.marginalB hρnB α
          (by
            rw [hα_opt]
            have hden :
                0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
              exact mul_pos (mul_pos (by norm_num) hL)
                (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
            have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
              Real.sqrt_pos.mpr hM
            have hfrac :
                0 <
                  Real.sqrt (log2 (2 / ε ^ 2)) /
                    (2 * log2 η * Real.sqrt (n : ℝ)) :=
              div_pos hnum hden
            linarith)
          (by
            have hα_gt : 1 < α := by
              rw [hα_opt]
              have hden :
                  0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
                exact mul_pos (mul_pos (by norm_num) hL)
                  (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
              have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
                Real.sqrt_pos.mpr hM
              have hfrac :
                  0 <
                    Real.sqrt (log2 (2 / ε ^ 2)) /
                      (2 * log2 η * Real.sqrt (n : ℝ)) :=
                div_pos hnum hden
              linarith
            exact (ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * H - 4 * (α - 1) * (n : ℝ) * (log2 η) ^ 2)
    (hvar :
      let hα_gt : 1 < α := by
        rw [hα_opt]
        have hden :
            0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
          exact mul_pos (mul_pos (by norm_num) hL)
            (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
        have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
          Real.sqrt_pos.mpr hM
        have hfrac :
            0 <
              Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) :=
          div_pos hnum hden
        linarith
      let lam : ℝ :=
        ρn.petzSmoothMinThresholdScale hρn ρn.marginalB hρnB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational ρn.matrix
        (identityTensorStateMatrix (a := a) ρn.marginalB) lam α) :
    ρn.smoothConditionalMinEntropyFixedSubnormalized ρn.marginalB.toSubnormalized ε ≥
      (n : ℝ) * H - QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
  subst α
  have hden :
      0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
    Real.sqrt_pos.mpr hM
  have hfrac :
      0 <
        Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)) :=
    div_pos hnum hden
  have hα_gt :
      1 <
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)) := by
    linarith
  have hsmooth :
      (ρn.conditionalPetzRenyiEntropyCandidate
          hρn ρn.marginalB hρnB
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 η * Real.sqrt (n : ℝ)))
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)) -
        (1 /
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) - 1)) *
          log2 (2 / ε ^ 2) ≤
        ρn.smoothConditionalMinEntropyFixedSubnormalized
          ρn.marginalB.toSubnormalized ε := by
    exact
      ρn.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_effectVariational
        hρn ρn.marginalB hρnB ε
        (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
        hε_pos hε_lt hα_gt hα_le_two
        (by simpa [hα_gt] using hvar)
  have hpetz_alpha' :
      ρn.conditionalPetzRenyiEntropyCandidate
          hρn ρn.marginalB hρnB
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 η * Real.sqrt (n : ℝ)))
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * H -
          4 *
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) - 1) *
            (n : ℝ) * (log2 η) ^ 2 := by
    simpa [hα_gt] using hpetz_alpha
  have hscalar :
      4 *
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) -
            1) *
          (n : ℝ) *
          (log2 η) ^ 2 +
        (1 /
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) -
              1)) *
          log2 (2 / ε ^ 2) =
          QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      QIT.finiteAEP_penalty_optimized_eq ε η (n := n) hM hL hn
  calc
    ρn.smoothConditionalMinEntropyFixedSubnormalized
        ρn.marginalB.toSubnormalized ε ≥
      (n : ℝ) * H -
        (4 *
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) -
              1) *
            (n : ℝ) *
            (log2 η) ^ 2 +
          (1 /
              (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                  (2 * log2 η * Real.sqrt (n : ℝ)) -
                1)) *
            log2 (2 / ε ^ 2)) := by
        linarith
    _ = (n : ℝ) * H - QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
        rw [hscalar]

/-- Optimized scalar-choice finite-AEP core from a tensor/source-shaped Petz
alpha lower bound, with the one-shot source step isolated as threshold-basis
Petz dephasing monotonicity.

This is the `cMatrixPetzTraceUnitaryDephaseMonotone` version of
`finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational_petzAlphaBound`.
It keeps the remaining noncommutative Appendix input at the dephasing
monotonicity level, without asking callers to provide the stronger
effect-variational package. -/
theorem finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_unitaryDephaseMonotone_petzAlphaBound
    (ρn : State (Prod a b)) (hρn : ρn.matrix.PosDef)
    (hρnB : ρn.marginalB.matrix.PosDef)
    (ε η α H : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hL : 0 < log2 η)
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hpetz_alpha :
      ρn.conditionalPetzRenyiEntropyCandidate
          hρn ρn.marginalB hρnB α
          (by
            rw [hα_opt]
            have hden :
                0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
              exact mul_pos (mul_pos (by norm_num) hL)
                (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
            have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
              Real.sqrt_pos.mpr hM
            have hfrac :
                0 <
                  Real.sqrt (log2 (2 / ε ^ 2)) /
                    (2 * log2 η * Real.sqrt (n : ℝ)) :=
              div_pos hnum hden
            linarith)
          (by
            have hα_gt : 1 < α := by
              rw [hα_opt]
              have hden :
                  0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
                exact mul_pos (mul_pos (by norm_num) hL)
                  (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
              have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
                Real.sqrt_pos.mpr hM
              have hfrac :
                  0 <
                    Real.sqrt (log2 (2 / ε ^ 2)) /
                      (2 * log2 η * Real.sqrt (n : ℝ)) :=
                div_pos hnum hden
              linarith
            exact (ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * H - 4 * (α - 1) * (n : ℝ) * (log2 η) ^ 2)
    (hmono :
      let hα_gt : 1 < α := by
        rw [hα_opt]
        have hden :
            0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
          exact mul_pos (mul_pos (by norm_num) hL)
            (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
        have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
          Real.sqrt_pos.mpr hM
        have hfrac :
            0 <
              Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) :=
          div_pos hnum hden
        linarith
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        ρn.petzSmoothMinThresholdScale hρn ρn.marginalB hρnB ε α hα_pos
          hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) ρn.marginalB).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) ρn.marginalB hρnB
      let Hmat : CMatrix (Prod a b) :=
        ρn.matrix - lam • identityTensorStateMatrix (a := a) ρn.marginalB
      let hH : Hmat.IsHermitian :=
        hρn.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρn.petzSmoothMinThresholdScale_pos hρn ρn.marginalB hρnB ε α
            hα_pos hα_ne_one)).isHermitian)
      let U : Matrix.unitaryGroup (Prod a b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρn.matrix
        (identityTensorStateMatrix (a := a) ρn.marginalB) U α) :
    ρn.smoothConditionalMinEntropyFixedSubnormalized ρn.marginalB.toSubnormalized ε ≥
      (n : ℝ) * H - QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
  subst α
  have hden :
      0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
    Real.sqrt_pos.mpr hM
  have hfrac :
      0 <
        Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)) :=
    div_pos hnum hden
  have hα_gt :
      1 <
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)) := by
    linarith
  have hsmooth :
      (ρn.conditionalPetzRenyiEntropyCandidate
          hρn ρn.marginalB hρnB
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 η * Real.sqrt (n : ℝ)))
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)) -
        (1 /
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) - 1)) *
          log2 (2 / ε ^ 2) ≤
        ρn.smoothConditionalMinEntropyFixedSubnormalized
          ρn.marginalB.toSubnormalized ε := by
    exact
      ρn.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_unitaryDephaseMonotone
        hρn ρn.marginalB hρnB ε
        (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
        hε_pos hε_lt hα_gt hα_le_two
        (by simpa [hα_gt] using hmono)
  have hpetz_alpha' :
      ρn.conditionalPetzRenyiEntropyCandidate
          hρn ρn.marginalB hρnB
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 η * Real.sqrt (n : ℝ)))
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * H -
          4 *
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) - 1) *
            (n : ℝ) * (log2 η) ^ 2 := by
    simpa [hα_gt] using hpetz_alpha
  have hscalar :
      4 *
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) -
            1) *
          (n : ℝ) *
          (log2 η) ^ 2 +
        (1 /
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) -
              1)) *
          log2 (2 / ε ^ 2) =
          QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      QIT.finiteAEP_penalty_optimized_eq ε η (n := n) hM hL hn
  calc
    ρn.smoothConditionalMinEntropyFixedSubnormalized
        ρn.marginalB.toSubnormalized ε ≥
      (n : ℝ) * H -
        (4 *
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) -
              1) *
            (n : ℝ) *
            (log2 η) ^ 2 +
          (1 /
              (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
                  (2 * log2 η * Real.sqrt (n : ℝ)) -
                1)) *
            log2 (2 / ε ^ 2)) := by
        linarith
    _ = (n : ℝ) * H - QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
        rw [hscalar]

/-- Tensor-power optimized finite-AEP core using conditional Petz alpha-entropy
additivity and the single-copy eta parameter.

The remaining assumption is the one-shot Petz dephasing monotonicity in the
threshold eigenbasis for the tensor-power state.  This is the narrow
source-shaped replacement for the `hvar` assumption in
`tensorPowerFiniteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational_additivePetz`. -/
theorem tensorPowerFiniteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_unitaryDephaseMonotone_additivePetz
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB)))
    (hmono :
      let hρn : (ρ.tensorPowerBipartite n).matrix.PosDef :=
        tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n
      let hρnB : (ρ.tensorPowerBipartite n).marginalB.matrix.PosDef :=
        tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n
      let hα_gt : 1 < α := by
        rw [hα_opt]
        have hL : 0 < log2 (ρ.finiteAEPEta hρ hρB) :=
          ρ.log2_finiteAEPEta_pos hρ hρB
        have hden :
            0 < 2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ) := by
          exact mul_pos (mul_pos (by norm_num) hL)
            (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
        have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
          Real.sqrt_pos.mpr hM
        have hfrac :
            0 <
              Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)) :=
          div_pos hnum hden
        linarith
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        (ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale
          hρn (ρ.tensorPowerBipartite n).marginalB hρnB ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).marginalB).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).marginalB hρnB
      let Hmat : CMatrix (Prod (TensorPower a n) (TensorPower b n)) :=
        (ρ.tensorPowerBipartite n).matrix -
          lam • identityTensorStateMatrix (a := TensorPower a n)
            (ρ.tensorPowerBipartite n).marginalB
      let hH : Hmat.IsHermitian :=
        hρn.isHermitian.sub ((Matrix.PosDef.smul hB
          ((ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale_pos
            hρn (ρ.tensorPowerBipartite n).marginalB hρnB ε α hα_pos hα_ne_one)
        ).isHermitian)
      let U : Matrix.unitaryGroup (Prod (TensorPower a n) (TensorPower b n)) ℂ :=
        hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone (ρ.tensorPowerBipartite n).matrix
        (identityTensorStateMatrix (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).marginalB) U α) :
    (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
        (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB) *
          Real.sqrt (n : ℝ) := by
  have hL : 0 < log2 (ρ.finiteAEPEta hρ hρB) :=
    ρ.log2_finiteAEPEta_pos hρ hρB
  have hα_gt : 1 < α := by
    rw [hα_opt]
    have hden :
        0 < 2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ) := by
      exact mul_pos (mul_pos (by norm_num) hL)
        (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
    have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
      Real.sqrt_pos.mpr hM
    have hfrac :
        0 <
          Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)) :=
      div_pos hnum hden
    linarith
  have hpetz_alpha :
      (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
          (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
          (ρ.tensorPowerBipartite n).marginalB
          (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
          α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * ρ.conditionalEntropy -
          4 * (α - 1) * (n : ℝ) *
            (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 :=
    ρ.tensorPower_conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef
      hρ hρB α hα_gt hα_lt
  exact
    (ρ.tensorPowerBipartite n).finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_unitaryDephaseMonotone_petzAlphaBound
      (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
      (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
      ε (ρ.finiteAEPEta hρ hρB) α ρ.conditionalEntropy hM hL hn hα_opt
      hε_pos hε_lt hα_le_two hpetz_alpha hmono

/-- Tensor-power optimized finite-AEP core for the optimized subnormalized
smooth min-entropy around the embedded normalized tensor-power state.

This combines the fixed-reference tensor-power AEP core with the order bridge
from fixed-reference subnormalized smoothing to optimized subnormalized
smoothing.  The fixed-reference feasible-set nonemptiness is supplied by the
positive-definite tensor-power marginal, so the remaining source-shaped
assumption is Petz dephasing monotonicity in the threshold eigenbasis. -/
theorem tensorPowerFiniteAEP_core_posDef_optimized_subnormalizedSmooth_of_unitaryDephaseMonotone_additivePetz
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB)))
    (hmono :
      let hρn : (ρ.tensorPowerBipartite n).matrix.PosDef :=
        tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n
      let hρnB : (ρ.tensorPowerBipartite n).marginalB.matrix.PosDef :=
        tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n
      let hα_gt : 1 < α := by
        rw [hα_opt]
        have hL : 0 < log2 (ρ.finiteAEPEta hρ hρB) :=
          ρ.log2_finiteAEPEta_pos hρ hρB
        have hden :
            0 < 2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ) := by
          exact mul_pos (mul_pos (by norm_num) hL)
            (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
        have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
          Real.sqrt_pos.mpr hM
        have hfrac :
            0 <
              Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)) :=
          div_pos hnum hden
        linarith
      let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
      let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
      let lam : ℝ :=
        (ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale
          hρn (ρ.tensorPowerBipartite n).marginalB hρnB ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).marginalB).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).marginalB hρnB
      let Hmat : CMatrix (Prod (TensorPower a n) (TensorPower b n)) :=
        (ρ.tensorPowerBipartite n).matrix -
          lam • identityTensorStateMatrix (a := TensorPower a n)
            (ρ.tensorPowerBipartite n).marginalB
      let hH : Hmat.IsHermitian :=
        hρn.isHermitian.sub ((Matrix.PosDef.smul hB
          ((ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale_pos
            hρn (ρ.tensorPowerBipartite n).marginalB hρnB ε α hα_pos hα_ne_one)
        ).isHermitian)
      let U : Matrix.unitaryGroup (Prod (TensorPower a n) (TensorPower b n)) ℂ :=
        hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone (ρ.tensorPowerBipartite n).matrix
        (identityTensorStateMatrix (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).marginalB) U α) :
    ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_pos.le hε_lt ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB) *
          Real.sqrt (n : ℝ) := by
  have hfixedCore :
      (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
          (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε ≥
        (n : ℝ) * ρ.conditionalEntropy -
          QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB) *
            Real.sqrt (n : ℝ) :=
    ρ.tensorPowerFiniteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_unitaryDephaseMonotone_additivePetz
      hρ hρB ε α hM hn hα_opt hε_pos hε_lt hα_le_two hα_lt hmono
  have hbridge :
      (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
          (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε ≤
        ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_pos.le hε_lt :=
    (ρ.tensorPowerBipartite n)
      |>.smoothConditionalMinEntropyFixedSubnormalized_le_subnormalizedSmoothConditionalMinEntropy
        (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε
        hε_pos.le hε_lt
        (fun ρ' _hball =>
          SubnormalizedState.conditionalMinEntropyFixed_feasibleSet_nonempty_of_posDef_reference
            (a := TensorPower a n) ρ' (ρ.tensorPowerBipartite n).marginalB
            (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n))
  exact le_trans hfixedCore hbridge

/-- Tensor-power optimized finite-AEP core from a global finite-uniform Petz
joint-convexity input on the tensor-power matrix dimension.

The remaining hypothesis `hjoint` is the precise noncommutative
perspective/joint-convexity theorem still needed for the source proof route.
All tensor-power bookkeeping, alpha-continuity, scalar optimization, and
subnormalized smoothing bridges are discharged here. -/
theorem tensorPowerFiniteAEP_core_posDef_optimized_subnormalizedSmooth_of_uniformJointConvex_all_additivePetz
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB)))
    (hjoint :
      ∀ {κ : Type (max u v)} [Fintype κ] [Nonempty κ],
        (Aκ Bκ : κ → CMatrix (Prod (TensorPower a n) (TensorPower b n))) →
          cMatrixPetzTraceUniformJointConvex Aκ Bκ α) :
    ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_pos.le hε_lt ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB) *
          Real.sqrt (n : ℝ) := by
  refine
    ρ.tensorPowerFiniteAEP_core_posDef_optimized_subnormalizedSmooth_of_unitaryDephaseMonotone_additivePetz
      hρ hρB ε α hM hn hα_opt hε_pos hε_lt hα_le_two hα_lt ?_
  dsimp
  let hρn : (ρ.tensorPowerBipartite n).matrix.PosDef :=
    tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n
  let hρnB : (ρ.tensorPowerBipartite n).marginalB.matrix.PosDef :=
    tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n
  let hα_gt : 1 < α := by
    rw [hα_opt]
    have hL : 0 < log2 (ρ.finiteAEPEta hρ hρB) :=
      ρ.log2_finiteAEPEta_pos hρ hρB
    have hden :
        0 < 2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ) := by
      exact mul_pos (mul_pos (by norm_num) hL)
        (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
    have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
      Real.sqrt_pos.mpr hM
    have hfrac :
        0 <
          Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)) :=
      div_pos hnum hden
    linarith
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  let lam : ℝ :=
    (ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale
      hρn (ρ.tensorPowerBipartite n).marginalB hρnB ε α hα_pos hα_ne_one
  let hB : (identityTensorStateMatrix (a := TensorPower a n)
      (ρ.tensorPowerBipartite n).marginalB).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := TensorPower a n)
      (ρ.tensorPowerBipartite n).marginalB hρnB
  let Hmat : CMatrix (Prod (TensorPower a n) (TensorPower b n)) :=
    (ρ.tensorPowerBipartite n).matrix -
      lam • identityTensorStateMatrix (a := TensorPower a n)
        (ρ.tensorPowerBipartite n).marginalB
  let hH : Hmat.IsHermitian :=
    hρn.isHermitian.sub ((Matrix.PosDef.smul hB
      ((ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale_pos
        hρn (ρ.tensorPowerBipartite n).marginalB hρnB ε α hα_pos hα_ne_one)
    ).isHermitian)
  let U : Matrix.unitaryGroup (Prod (TensorPower a n) (TensorPower b n)) ℂ :=
    hH.eigenvectorUnitary
  exact cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex_all
    (ρ.tensorPowerBipartite n).matrix
    (identityTensorStateMatrix (a := TensorPower a n)
      (ρ.tensorPowerBipartite n).marginalB)
    hρn.posSemidef hB U hα_gt hα_le_two hjoint

/-- Tensor-power optimized finite-AEP core with the Petz joint-convexity input
discharged by the finite-dimensional rpow perspective theorem. -/
theorem tensorPowerFiniteAEP_core_posDef_optimized_subnormalizedSmooth_of_rpow_perspective_additivePetz
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB))) :
    ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_pos.le hε_lt ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB) *
          Real.sqrt (n : ℝ) := by
  refine
    ρ.tensorPowerFiniteAEP_core_posDef_optimized_subnormalizedSmooth_of_uniformJointConvex_all_additivePetz
      hρ hρB ε α hM hn hα_opt hε_pos hε_lt hα_le_two hα_lt ?_
  intro κ _ _ Aκ Bκ
  exact cMatrixPetzTraceUniformJointConvex_of_rpow_perspective_one_two Aκ Bκ

/-- Positive-definite finite-N AEP statement from the remaining universal Petz
joint-convexity input.

This theorem connects the source-aligned public statement surface to the
proved tensor-power core.  The only analytic input still left explicit is the
finite-uniform joint convexity of the Petz trace on the tensor-power matrix
dimension; the optimized alpha choice, source blocklength condition, and
normalization by `n` are all discharged here. -/
theorem finiteNAEP_statement_posDef_of_uniformJointConvex_all
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε : ℝ) (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1) (n : ℕ)
    (hjoint :
      ∀ {κ : Type (max u v)} [Fintype κ] [Nonempty κ],
        (Aκ Bκ : κ → CMatrix (Prod (TensorPower a n) (TensorPower b n))) →
          cMatrixPetzTraceUniformJointConvex Aκ Bκ
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)))) :
    QIT.finiteNAEP_statement ρ ε (ρ.finiteAEPEta hρ hρB) n hε_nonneg hε_lt := by
  intro hε_pos hn_ge
  let α : ℝ :=
    1 + Real.sqrt (log2 (2 / ε ^ 2)) /
      (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ))
  have hM : 0 < log2 (2 / ε ^ 2) :=
    finiteAEP_log2_two_div_sq_pos hε_pos hε_lt
  have hM_nonneg : 0 ≤ log2 (2 / ε ^ 2) := le_of_lt hM
  have hL : 0 < log2 (ρ.finiteAEPEta hρ hρB) :=
    ρ.log2_finiteAEPEta_pos hρ hρB
  have hη3 : 3 ≤ ρ.finiteAEPEta hρ hρB :=
    ρ.three_le_finiteAEPEta hρ hρB
  have hnR : 0 < (n : ℝ) := by
    exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 8 / 5) hM) hn_ge
  have hn : 0 < n := by exact_mod_cast hnR
  have hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)) := rfl
  have hα_le_two : α ≤ 2 := by
    simpa [α] using
      finiteAEP_alpha_le_two_of_n_ge ε (ρ.finiteAEPEta hρ hρB)
        hM_nonneg hL hη3 hn hn_ge
  have hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB)) := by
    simpa [α] using
      finiteAEP_alpha_window_of_n_ge ε (ρ.finiteAEPEta hρ hρB)
        hM_nonneg hL hn hn_ge
  have hcore :
      ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_pos.le hε_lt ≥
        (n : ℝ) * ρ.conditionalEntropy -
          QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB) *
            Real.sqrt (n : ℝ) :=
    have hjointAlpha :
        ∀ {κ : Type (max u v)} [Fintype κ] [Nonempty κ],
          (Aκ Bκ : κ → CMatrix (Prod (TensorPower a n) (TensorPower b n))) →
            cMatrixPetzTraceUniformJointConvex Aκ Bκ α := by
      intro κ _ _ Aκ Bκ
      simpa [α] using hjoint (κ := κ) Aκ Bκ
    ρ.tensorPowerFiniteAEP_core_posDef_optimized_subnormalizedSmooth_of_uniformJointConvex_all_additivePetz
      hρ hρB ε α hM hn hα_opt hε_pos hε_lt hα_le_two hα_lt hjointAlpha
  simpa [State.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_eq] using
    finiteAEP_normalized_rate_of_tensor_lower_bound
      (S := ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_pos.le hε_lt)
      (H := ρ.conditionalEntropy)
      (δ := QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB))
      (n := n) hn hcore

/-- Finite-N AEP statement using only the full-rank marginal reference and the
trace-term eta parameter. -/
theorem finiteNAEP_statement_traceEta_of_marginal_posDef
    (ρ : State (Prod a b))
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε : ℝ) (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1) (n : ℕ) :
    QIT.finiteNAEP_statement ρ ε ρ.finiteAEPEtaTrace n hε_nonneg hε_lt := by
  intro hε_pos hn_ge
  let α : ℝ :=
    1 + Real.sqrt (log2 (2 / ε ^ 2)) /
      (2 * log2 ρ.finiteAEPEtaTrace * Real.sqrt (n : ℝ))
  have hM : 0 < log2 (2 / ε ^ 2) :=
    finiteAEP_log2_two_div_sq_pos hε_pos hε_lt
  have hM_nonneg : 0 ≤ log2 (2 / ε ^ 2) := le_of_lt hM
  have hη3 : 3 ≤ ρ.finiteAEPEtaTrace := by
    simpa [finiteAEPEtaTrace] using
      conditionalAlphaConvergenceParameterTrace_ge_three
        (ρ := ρ) (σ := ρ.marginalB) hρB
  have hL : 0 < log2 ρ.finiteAEPEtaTrace := by
    unfold log2
    exact div_pos
      (Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hη3))
      (Real.log_pos one_lt_two)
  have hnR : 0 < (n : ℝ) := by
    exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 8 / 5) hM) hn_ge
  have hn : 0 < n := by exact_mod_cast hnR
  have hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 ρ.finiteAEPEtaTrace * Real.sqrt (n : ℝ)) := rfl
  have hα_le_two : α ≤ 2 := by
    simpa [α] using
      finiteAEP_alpha_le_two_of_n_ge ε ρ.finiteAEPEtaTrace
        hM_nonneg hL hη3 hn hn_ge
  have hα_lt :
      α < 1 + log2 3 /
        (4 * log2 ρ.finiteAEPEtaTrace) := by
    simpa [α] using
      finiteAEP_alpha_window_of_n_ge ε ρ.finiteAEPEtaTrace
        hM_nonneg hL hn hn_ge
  have hcore :
      ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_pos.le hε_lt ≥
        (n : ℝ) * ρ.conditionalEntropy -
          QIT.finiteAEPDelta ε ρ.finiteAEPEtaTrace *
            Real.sqrt (n : ℝ) :=
    ρ.tensorPowerFiniteAEP_core_fullReference_optimized_subnormalizedSmooth_additivePetz
      hρB ε α hM hn hα_opt hε_pos hε_lt hα_le_two hα_lt
  simpa [State.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_eq] using
    finiteAEP_normalized_rate_of_tensor_lower_bound
      (S := ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_pos.le hε_lt)
      (H := ρ.conditionalEntropy)
      (δ := QIT.finiteAEPDelta ε ρ.finiteAEPEtaTrace)
      (n := n) hn hcore

/-- Tensor-power subnormalized smooth min-entropy is unchanged by compressing
the conditioning register to the support of the canonical marginal and applying
the tensor-power support isometry back, with the same smoothing radius. -/
theorem tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_conditioningSupportCompressedState
    (ρ : State (Prod a b)) (ε : ℝ) (hε0 : 0 ≤ ε) (hε_lt : ε < 1) (n : ℕ) :
    ρ.conditioningSupportCompressedState.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw ε n =
      ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw ε n := by
  let ρc := ρ.conditioningSupportCompressedState
  let V : ReferenceIsometry (psdSupportIndex ρ.marginalB.matrix ρ.marginalB.pos) b :=
    psdSupportReferenceIsometry ρ.marginalB.matrix ρ.marginalB.pos
  haveI : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  haveI : Nonempty b := ⟨(Classical.choice ρ.nonempty).2⟩
  haveI : Nonempty (psdSupportIndex ρ.marginalB.matrix ρ.marginalB.pos) :=
    ⟨(Classical.choice ρc.nonempty).2⟩
  haveI : Nonempty (TensorPower a n) := tensorPower_nonempty_of_nonempty n
  haveI : Nonempty (TensorPower b n) := tensorPower_nonempty_of_nonempty n
  haveI :
      Nonempty (TensorPower (psdSupportIndex ρ.marginalB.matrix ρ.marginalB.pos) n) :=
    tensorPower_nonempty_of_nonempty n
  have hε_sqrt :
      ε < Real.sqrt ((ρc.tensorPowerBipartite n).toSubnormalized.matrix.trace.re) := by
    rw [State.toSubnormalized_trace]
    norm_num
    exact hε_lt
  have hsmooth :=
    SubnormalizedState.smoothConditionalMinEntropy_conditioningIsometryApply
      (a := TensorPower a n)
      (ρ := (ρc.tensorPowerBipartite n).toSubnormalized)
      (V := V.tensorPower n) hε0 hε_sqrt
  have htensorState :
      (ρc.tensorPowerBipartite n).conditioningIsometryApply (V.tensorPower n) =
        ρ.tensorPowerBipartite n := by
    calc
      (ρc.tensorPowerBipartite n).conditioningIsometryApply (V.tensorPower n) =
          (ρc.conditioningIsometryApply V).tensorPowerBipartite n := by
            rw [State.conditioningIsometryApply_tensorPowerBipartite]
      _ = ρ.tensorPowerBipartite n := by
            rw [show ρc.conditioningIsometryApply V = ρ from by
              simpa [ρc, V] using
                State.conditioningSupportCompressedState_conditioningIsometryApply (ρ := ρ)]
  have hsubState :
      (ρc.tensorPowerBipartite n).toSubnormalized.conditioningIsometryApply
          (V.tensorPower n) =
        (ρ.tensorPowerBipartite n).toSubnormalized := by
    rw [← State.toSubnormalized_conditioningIsometryApply]
    rw [htensorState]
  rw [State.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_eq,
    State.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_eq]
  rw [← hsubState]
  exact hsmooth.symm

/-- Canonical finite-domain support-compression invariance for the tensor-power
smooth conditional min-entropy. -/
theorem tensorPowerSubnormalizedSmoothConditionalMinEntropy_conditioningSupportCompressedState
    (ρ : State (Prod a b)) (ε : ℝ) (hε0 : 0 ≤ ε) (hε_lt : ε < 1) (n : ℕ) :
    ρ.conditioningSupportCompressedState.tensorPowerSubnormalizedSmoothConditionalMinEntropy
        ε n hε0 hε_lt =
      ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε0 hε_lt := by
  change
    ρ.conditioningSupportCompressedState.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw
        ε n =
      ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw ε n
  exact tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_conditioningSupportCompressedState
    ρ ε hε0 hε_lt n

/-- Arbitrary-state finite-N AEP with the trace-term eta parameter, obtained
from the full-rank-marginal theorem by support compression of the conditioning
register. -/
theorem finiteNAEP_statement_traceEta
    (ρ : State (Prod a b)) (ε : ℝ) (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1) (n : ℕ) :
    QIT.finiteNAEP_statement ρ ε ρ.finiteAEPEtaTrace n hε_nonneg hε_lt := by
  let ρc := ρ.conditioningSupportCompressedState
  have hcompressed :
      QIT.finiteNAEP_statement ρc ε ρc.finiteAEPEtaTrace n hε_nonneg hε_lt :=
    finiteNAEP_statement_traceEta_of_marginal_posDef
      (ρ := ρc) (State.conditioningSupportCompressedState_marginalB_posDef ρ)
      ε hε_nonneg hε_lt n
  intro hε_pos hn_ge
  have hε0 : 0 ≤ ε := le_of_lt hε_pos
  have hbound := hcompressed hε_pos hn_ge
  change
    (1 / (n : ℝ)) *
        ρc.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw ε n ≥
      ρc.conditionalEntropy -
        finiteAEPDelta ε ρc.finiteAEPEtaTrace / Real.sqrt (n : ℝ) at hbound
  change
    (1 / (n : ℝ)) * ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw ε n ≥
      ρ.conditionalEntropy -
        finiteAEPDelta ε ρ.finiteAEPEtaTrace / Real.sqrt (n : ℝ)
  rw [← State.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_conditioningSupportCompressedState
    ρ ε hε0 hε_lt n]
  rw [← State.conditionalEntropy_conditioningSupportCompressedState ρ]
  rw [← State.finiteAEPEtaTrace_conditioningSupportCompressedState ρ]
  exact hbound

/-- The finite-N AEP theorem supplies the lower half of the source proof of
the asymptotic fully quantum AEP.

This is the Lean version of the first step in TCR 2008, proof of
`thm:qaep`: after the final tolerance is fixed, for all sufficiently small
positive smoothing radii and sufficiently large blocklengths, the normalized
smooth-min rate is at least `H(A|B)_ρ` up to that tolerance. -/
theorem SmoothMinRateLowerFromFiniteNAEP_traceEta
    (ρ : State (Prod a b)) :
    ρ.SmoothMinRateLowerFromFiniteNAEP := by
  intro γ hγ
  have hε_pos :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε := by
    exact self_mem_nhdsWithin
  have hε_lt_one :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < 1 := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hε_pos, hε_lt_one] with ε hε_pos hε_lt_one
  intro hε_nonneg hε_lt_domain
  have hdelta_tend :
      Tendsto
        (fun n : ℕ => QIT.finiteAEPDelta ε ρ.finiteAEPEtaTrace / Real.sqrt (n : ℝ))
        atTop (nhds 0) :=
    QIT.finiteAEPDelta_div_sqrt_tendsto_zero ε ρ.finiteAEPEtaTrace
  have hdelta_small :
      ∀ᶠ n : ℕ in atTop,
        QIT.finiteAEPDelta ε ρ.finiteAEPEtaTrace / Real.sqrt (n : ℝ) < γ := by
    exact hdelta_tend.eventually (Iio_mem_nhds hγ)
  have hn_ge :
      ∀ᶠ n : ℕ in atTop,
        (8 / 5 : ℝ) * log2 (2 / ε ^ 2) ≤ (n : ℝ) := by
    refine eventually_atTop.2 ⟨Nat.ceil ((8 / 5 : ℝ) * log2 (2 / ε ^ 2)), ?_⟩
    intro n hn
    exact (Nat.le_ceil ((8 / 5 : ℝ) * log2 (2 / ε ^ 2))).trans
      (by exact_mod_cast hn)
  filter_upwards [hdelta_small, hn_ge] with n hdelta_small hn_ge
  have hfinite := finiteNAEP_statement_traceEta
    ρ ε hε_nonneg hε_lt_domain n hε_pos hn_ge
  change ρ.conditionalEntropy - γ ≤
    (1 / (n : ℝ)) *
      ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy
        ε n hε_nonneg hε_lt_domain
  linarith

/-- AFW continuity supplies the upper half of the source proof of TCR
`thm:qaep`.

The endpoint ordering `H_min ≤ H` is the only order input needed by
`AEP.lean`; the preceding support-log residual and padding lemmas prove it for
the optimized conditional min-entropy without a full-rank assumption. -/
theorem SmoothMinRateUpperFromContinuity.afw
    (ρ : State (Prod a b)) :
    ρ.SmoothMinRateUpperFromContinuity :=
  State.SmoothMinRateUpperFromContinuity.afw_of_tensorPower_ordering ρ
    (by
      intro n τ
      exact τ.conditionalMinEntropy_le_conditionalEntropy)

/-- Source-aligned min-entropy half of the asymptotic AEP, with the finite-N
lower bound discharged by the finite-AEP theorem and the AFW/Fannes upper
handoff left explicit. -/
theorem asymptoticAEPMin_statement_of_traceEta_and_continuity
    (ρ : State (Prod a b))
    (hupper : ρ.SmoothMinRateUpperFromContinuity) :
    SourceFiniteDomainTwoStageLimitTo
      (fun ε hε_nonneg hε_lt_one n =>
        ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRate
          ε n hε_nonneg hε_lt_one)
      ρ.conditionalEntropy :=
  ρ.asymptoticAEPMin_statement_of_finiteNAEP_and_continuity
    (ρ.SmoothMinRateLowerFromFiniteNAEP_traceEta) hupper

/-- Smooth min/max duality supplies the source max-entropy half of TCR
`thm:qaep` once the min-entropy half is available on every finite complement. -/
theorem SmoothMaxRateFromMinDuality.smoothDuality
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
    ρ.SmoothMaxRateFromMinDuality := by
  refine State.SmoothMaxRateFromMinDuality.of_all_min ρ ?_
  intro c _ _ _ σ
  exact σ.asymptoticAEPMin_statement_of_traceEta_and_continuity
    (State.SmoothMinRateUpperFromContinuity.afw σ)

/-- Source-aligned assembly theorem for the asymptotic fully quantum AEP.

The finite-N lower half is supplied by the finite-AEP theorem.  The remaining
two inputs are exactly the source proof's later ingredients: ordering plus
AFW/Fannes continuity for the min upper half, and smooth min/max plus von
Neumann duality for the max half. -/
theorem asymptoticAEPTwoStage_statement_of_traceEta_continuity_and_duality
    (ρ : State (Prod a b))
    (hupper : ρ.SmoothMinRateUpperFromContinuity)
    (hmax : ρ.SmoothMaxRateFromMinDuality) :
    QIT.asymptoticAEPTwoStage_statement ρ :=
  ρ.asymptoticAEPTwoStage_statement_of_min_and_max_duality
    (ρ.asymptoticAEPMin_statement_of_traceEta_and_continuity hupper) hmax

/-- Fully quantum asymptotic equipartition property, TCR 2008 `thm:qaep`.

The proof follows the source route: finite-N AEP gives the smooth-min lower
limit, AFW continuity and `H_min ≤ H` give the smooth-min upper limit, and
smooth min/max duality plus conditional-entropy duality gives the max-entropy
limit. -/
theorem fullyQuantumAsymptoticEquipartitionProperty_twoStage
    (ρ : State (Prod a b)) :
    QIT.asymptoticAEPTwoStage_statement ρ := by
  letI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  letI : Nonempty b := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  exact ρ.asymptoticAEPTwoStage_statement_of_traceEta_continuity_and_duality
    (State.SmoothMinRateUpperFromContinuity.afw ρ)
    (State.SmoothMaxRateFromMinDuality.smoothDuality ρ)

/-- Positive-definite finite-N AEP statement with Petz joint convexity
discharged by the finite-dimensional rpow perspective theorem. -/
theorem finiteNAEP_statement_posDef_of_rpow_perspective_one_two
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε : ℝ) (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1) (n : ℕ) :
    QIT.finiteNAEP_statement ρ ε (ρ.finiteAEPEta hρ hρB) n hε_nonneg hε_lt :=
  ρ.finiteNAEP_statement_posDef_of_uniformJointConvex_all
    hρ hρB ε hε_nonneg hε_lt n
    (fun {κ} [Fintype κ] [Nonempty κ]
        (Aκ Bκ : κ → CMatrix (Prod (TensorPower a n) (TensorPower b n))) =>
      cMatrixPetzTraceUniformJointConvex_of_rpow_perspective_one_two Aκ Bκ)

/-- Explicit-`η` spelling of the positive-definite finite-N AEP theorem.

This keeps the public statement parameter separate from the current
positive-definite implementation of the source convergence parameter. -/
theorem finiteNAEP_statement_posDef_explicitEta_of_rpow_perspective_one_two
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (η ε : ℝ) (hη : η = ρ.finiteAEPEta hρ hρB)
    (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1) (n : ℕ) :
    QIT.finiteNAEP_statement ρ ε η n hε_nonneg hε_lt := by
  subst η
  exact ρ.finiteNAEP_statement_posDef_of_rpow_perspective_one_two
    hρ hρB ε hε_nonneg hε_lt n

/-- Positive-definite finite-N AEP using the arbitrary-state trace-term eta
spelling of `Upsilon(A|B)_{rho|rho}`. -/
theorem finiteNAEP_statement_posDef_traceEta_of_rpow_perspective_one_two
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε : ℝ) (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1) (n : ℕ) :
    QIT.finiteNAEP_statement ρ ε ρ.finiteAEPEtaTrace n hε_nonneg hε_lt := by
  rw [← ρ.finiteAEPEta_eq_trace hρ hρB]
  exact ρ.finiteNAEP_statement_posDef_of_rpow_perspective_one_two
    hρ hρB ε hε_nonneg hε_lt n

/-- Tensor-power optimized finite-AEP core using conditional Petz alpha-entropy
additivity and the single-copy eta parameter.

The remaining assumptions are the single-copy alpha window and the one-shot
Petz effect-variational inequality.  No tensor-power eta square bound is
assumed. -/
theorem tensorPowerFiniteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational_additivePetz
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε α : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB)))
    (hvar :
      let hρn : (ρ.tensorPowerBipartite n).matrix.PosDef :=
        tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n
      let hρnB : (ρ.tensorPowerBipartite n).marginalB.matrix.PosDef :=
        tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n
      let hα_gt : 1 < α := by
        rw [hα_opt]
        have hL : 0 < log2 (ρ.finiteAEPEta hρ hρB) :=
          ρ.log2_finiteAEPEta_pos hρ hρB
        have hden :
            0 < 2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ) := by
          exact mul_pos (mul_pos (by norm_num) hL)
            (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
        have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
          Real.sqrt_pos.mpr hM
        have hfrac :
            0 <
              Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)) :=
          div_pos hnum hden
        linarith
      let lam : ℝ :=
        (ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale
          hρn (ρ.tensorPowerBipartite n).marginalB hρnB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational (ρ.tensorPowerBipartite n).matrix
        (identityTensorStateMatrix (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).marginalB) lam α) :
    (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
        (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB) *
          Real.sqrt (n : ℝ) := by
  have hL : 0 < log2 (ρ.finiteAEPEta hρ hρB) :=
    ρ.log2_finiteAEPEta_pos hρ hρB
  have hα_gt : 1 < α := by
    rw [hα_opt]
    have hden :
        0 < 2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ) := by
      exact mul_pos (mul_pos (by norm_num) hL)
        (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
    have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
      Real.sqrt_pos.mpr hM
    have hfrac :
        0 <
          Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 (ρ.finiteAEPEta hρ hρB) * Real.sqrt (n : ℝ)) :=
      div_pos hnum hden
    linarith
  have hpetz_alpha :
      (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
          (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
          (ρ.tensorPowerBipartite n).marginalB
          (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
          α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * ρ.conditionalEntropy -
          4 * (α - 1) * (n : ℝ) *
            (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 :=
    ρ.tensorPower_conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef
      hρ hρB α hα_gt hα_lt
  exact
    (ρ.tensorPowerBipartite n).finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational_petzAlphaBound
      (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
      (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
      ε (ρ.finiteAEPEta hρ hρB) α ρ.conditionalEntropy hM hL hn hα_opt
      hε_pos hε_lt hα_le_two hpetz_alpha hvar

/-- Tensor-power instantiation of the optimized positive-definite finite-AEP
core.

This theorem discharges the tensor-power positive-definiteness bookkeeping for
`ρ_AB^{⊗ n}`, its `B^n` marginal, and conditional entropy additivity.  The eta
growth, alpha-window, and Petz effect-variational inputs remain explicit. -/
theorem tensorPowerFiniteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (ε η α : ℝ) {n : ℕ}
    (hM : 0 < log2 (2 / ε ^ 2))
    (hL : 0 < log2 η)
    (hn : 0 < n)
    (hα_opt :
      α =
        1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 ((ρ.tensorPowerBipartite n).finiteAEPEta
          (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
          (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n))))
    (heta_tensor :
      (log2 ((ρ.tensorPowerBipartite n).finiteAEPEta
        (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
        (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n))) ^ 2 ≤
          (n : ℝ) * (log2 η) ^ 2)
    (hvar :
      let hρn : (ρ.tensorPowerBipartite n).matrix.PosDef :=
        tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n
      let hρnB : (ρ.tensorPowerBipartite n).marginalB.matrix.PosDef :=
        tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n
      let hα_gt : 1 < α := by
        rw [hα_opt]
        have hden :
            0 < 2 * log2 η * Real.sqrt (n : ℝ) := by
          exact mul_pos (mul_pos (by norm_num) hL)
            (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
        have hnum : 0 < Real.sqrt (log2 (2 / ε ^ 2)) :=
          Real.sqrt_pos.mpr hM
        have hfrac :
            0 <
              Real.sqrt (log2 (2 / ε ^ 2)) /
                (2 * log2 η * Real.sqrt (n : ℝ)) :=
          div_pos hnum hden
        linarith
      let lam : ℝ :=
        (ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale
          hρn (ρ.tensorPowerBipartite n).marginalB hρnB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational (ρ.tensorPowerBipartite n).matrix
        (identityTensorStateMatrix (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).marginalB) lam α) :
    (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
        (ρ.tensorPowerBipartite n).marginalB.toSubnormalized ε ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
  exact
    (ρ.tensorPowerBipartite n).finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational
      (tensorPowerBipartite_posDef_forFiniteAEP ρ hρ n)
      (tensorPowerBipartite_marginalB_posDef_forFiniteAEP ρ hρ hρB n)
      ε η α ρ.conditionalEntropy hM hL hn hα_opt hε_pos hε_lt hα_le_two hα_lt
      (State.tensorPowerBipartite_conditionalEntropy ρ n) heta_tensor hvar

/-- Honest positive-definite fixed-reference finite-AEP core.

This combines the TCR alpha-to-von-Neumann estimate already proved in
`conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef` with an explicit
one-shot smooth-min/Petz lower-bound hypothesis.  That hypothesis is precisely
the missing fixed-reference analogue of TCR 2008 `thm:entropy-ineq`, lines
630--633; this theorem does not claim that bridge as proved. -/
theorem relativeFiniteAEP_core_posDef_of_smoothMinPetzBound
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (_hε_pos : 0 < ε)
    (hα_gt : 1 < α) (_hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)))
    (hsmoothMinPetz :
      ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) ≤
          ρ.smoothConditionalMinEntropyFixed σ ε) :
    ρ.smoothConditionalMinEntropyFixed σ ε ≥
      ρ.conditionalEntropyRelative hρ σ hσ -
        4 * (α - 1) *
          (log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  have hpetz :
      ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        ρ.conditionalEntropyRelative hρ σ hσ -
          4 * (α - 1) *
            (log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)) ^ 2 :=
    conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef
      (ρ := ρ) hρ (σ := σ) hσ α hα_gt hα_lt
  linarith

/-- Positive-definite fixed-reference finite-AEP core from a concrete
Petz-threshold operator-order smoothed witness.

Compared with `relativeFiniteAEP_core_posDef_of_smoothMinPetzBound`, this
removes the broad smooth-min/Petz lower-bound hypothesis and leaves the smaller
source construction: find `ρ'` in the purified ball below the fixed-reference
Petz threshold scale. -/
theorem relativeFiniteAEP_core_posDef_of_petz_feasible_witness
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε)
    (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)))
    (hconstruct :
      ∃ ρ' : State (Prod a b), ρ.purifiedBall ε ρ' ∧
        ρ'.matrix ≤
          ((ρ.petzSmoothMinThresholdScale hρ σ hσ ε α
            (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) : ℝ) : ℂ) •
            identityTensorStateMatrix (a := a) σ) :
    ρ.smoothConditionalMinEntropyFixed σ ε ≥
      ρ.conditionalEntropyRelative hρ σ hσ -
        4 * (α - 1) *
          (log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  rcases hconstruct with ⟨ρ', hball, hbound⟩
  exact relativeFiniteAEP_core_posDef_of_smoothMinPetzBound
    (ρ := ρ) hρ (σ := σ) hσ ε α hε_pos hα_gt hα_le_two hα_lt
    (smoothConditionalMinEntropyFixed_lower_bound_of_petz_operator_bound
      (ρ := ρ) hρ (σ := σ) hσ ε α hε_pos hε_lt hα_gt hα_le_two
      ρ' hball hbound)

end State
end

end QIT
