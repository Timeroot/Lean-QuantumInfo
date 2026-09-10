/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Asymptotic.FixedSmoothMinEntropy.ThresholdProjector
import QuantumLib.QIT.Util.TensorPower

/-!
# From the one-shot Petz bound to the fully quantum AEP

The one-shot bound of `ThresholdProjector.lean` becomes an asymptotic statement once it is applied
to `ρ_AB^{⊗n}` with the reference `σ_B^{⊗n}` and the Rényi parameter is optimized.  Additivity is
what makes this work: `tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_additive` shows
the fixed-reference Petz candidate is `n` times the single-copy one, so the one-shot bound reads

`n H↑_α(A|B) - log₂(2/ε²)/(α-1) ≤ H_min^ε(Aⁿ|Bⁿ)`,

and feeding in the linear lower bound `H↑_α ≥ H(A|B) - 4(α-1)(log₂ η)²` at
`α = 1 + √(log₂(2/ε²)) / (2 log₂ η √n)` balances the two error terms into `-δ(ε,η)√n`.  That is
`finiteNAEP_statement`, proved here first for positive definite states and then in general.

Two regularizations remove the rank hypotheses.  White noise
`finiteAEPFullRankRegularization ρ η = (1-η)ρ + (η/d)·I` makes the joint state positive definite,
and both the purified distance to `ρ` and the change in conditional entropy vanish as `η → 0`, so a
bound proved for every `η > 0` passes to the limit; this is packaged as
`finiteAEPFullRankRegularization_tensorLowerBound_transfer`, which also has to commute the
regularization with the tensor power.  The conditioning register instead gets compressed to the
support of `ρ_B`, since none of the quantities involved sees the kernel.

The last section cashes in the finite-`N` theorem.  It supplies the lower half of the smooth-min
rate; AFW continuity together with `H_min ≤ H` supplies the upper half; and smooth min/max duality
against conditional-entropy duality converts the min statement into the max one.  Assembling the
three gives `fullyQuantumAsymptoticEquipartitionProperty_twoStage`
[TomamichelColbeckRenner2008Fqaep, thm:qaep].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker NNReal
open Filter

noncomputable section
universe u v w
variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

open QIT

namespace MState
/-! ## Finite-AEP assembly core -/

/-! ### Full-rank regularization setup for arbitrary finite states -/

/-- Matrix path that regularizes an arbitrary finite bipartite state by adding
white noise on `AB`.

For `0 < η ≤ 1`, the associated state below is positive definite, and as
`η → 0+` this matrix tends back to `ρ.m`.  This is the reusable
regularization surface needed before taking the positive-definite finite-AEP
core to arbitrary states. -/
def finiteAEPFullRankRegularizationMatrix
    (ρ : MState (a × b)) (η : ℝ) : CMatrix (a × b) :=
  (((1 - η : ℝ) : ℂ) • ρ.m) +
    ((((η / (Fintype.card (a × b) : ℝ) : ℝ)) : ℂ) •
      (1 : CMatrix (a × b)))

/-- The fixed direction from `ρ` toward the maximally mixed state used by the
white-noise regularization. -/
def finiteAEPFullRankRegularizationDirection
    (ρ : MState (a × b)) : CMatrix (a × b) :=
  ((((1 / (Fintype.card (a × b) : ℝ) : ℝ) : ℂ) •
    (1 : CMatrix (a × b))) - ρ.m)

/-- The normalized state associated with
`finiteAEPFullRankRegularizationMatrix` when the regularization weight lies in
the probability interval. -/
def finiteAEPFullRankRegularization
    (ρ : MState (a × b)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    MState (a × b) := .ofMatrix
  (matrix := finiteAEPFullRankRegularizationMatrix ρ η)
  (pos := by
    unfold finiteAEPFullRankRegularizationMatrix
    have hleft : (0 : ℂ) ≤ (((1 - η : ℝ) : ℂ)) := by
      exact_mod_cast sub_nonneg.mpr hη1
    have hright : (0 : ℂ) ≤ (((η / (Fintype.card (a × b) : ℝ) : ℝ) : ℂ)) := by
      exact_mod_cast div_nonneg hη0 (by positivity : (0 : ℝ) ≤ Fintype.card (a × b))
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul ρ.psd hleft)
      (Matrix.PosSemidef.smul Matrix.PosSemidef.one hright))
  (trace_eq_one := by
    let : Nonempty (a × b) := ρ.nonempty
    have hcardR : (Fintype.card (a × b) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card (a × b) ≠ 0))
    have hscalar :
        (1 - η) + (η / (Fintype.card (a × b) : ℝ)) *
            (Fintype.card (a × b) : ℝ) = 1 := by
      field_simp [hcardR]
      ring
    unfold finiteAEPFullRankRegularizationMatrix
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, ρ.tr',
      Matrix.trace_one]
    simpa [smul_eq_mul] using congrArg (fun x : ℝ => (x : ℂ)) hscalar)

@[simp]
theorem finiteAEPFullRankRegularization_matrix
    (ρ : MState (a × b)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).m =
      finiteAEPFullRankRegularizationMatrix ρ η :=
  MState.matrix_ofMatrix _ _ _

/-- The full-rank white-noise regularization differs from the original state
by `η` times a fixed matrix. -/
theorem finiteAEPFullRankRegularization_matrix_sub
    (ρ : MState (a × b)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).m - ρ.m =
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
    (ρ : MState (a × b)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).normalizedTraceDistance ρ ≤
      η * (1 / 2 : ℝ) *
        traceNorm ρ.finiteAEPFullRankRegularizationDirection := by
  rw [MState.normalizedTraceDistance_eq_matrix, QIT.normalizedTraceDistance_eq,
    QIT.traceNormDistance]
  rw [finiteAEPFullRankRegularization_matrix_sub ρ η hη0 hη1]
  have hnorm := traceNorm_real_smul_le (a := a × b) hη0
    ρ.finiteAEPFullRankRegularizationDirection
  nlinarith

/-- The purified distance from the white-noise regularization to the original
state is controlled by the square root of the regularization weight. -/
theorem finiteAEPFullRankRegularization_purifiedDistance_le
    (ρ : MState (a × b)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
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

/-- Positive regularization weight makes the white-noise regularization
positive definite, even when the original state is singular. -/
theorem finiteAEPFullRankRegularization_posDef
    (ρ : MState (a × b)) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hηpos : 0 < η) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).m.PosDef := by
  let : Nonempty (a × b) := ρ.nonempty
  rw [finiteAEPFullRankRegularization_matrix]
  unfold finiteAEPFullRankRegularizationMatrix
  have hleft : (0 : ℂ) ≤ (((1 - η : ℝ) : ℂ)) := by
    exact_mod_cast sub_nonneg.mpr hη1
  have hright : 0 < η / (Fintype.card (a × b) : ℝ) := by
    exact div_pos hηpos (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (a × b)))
  exact Matrix.PosDef.posSemidef_add
    (Matrix.PosSemidef.smul ρ.psd hleft)
    (cMatrix_real_smul_one_posDef hright)

private theorem traceLeft_one_forFiniteAEP
    (a : Type u) (b : Type v) [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] :
    Matrix.traceLeft (1 : CMatrix (a × b)) =
      ((Fintype.card a : ℂ) • (1 : CMatrix b)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.traceLeft]
  · simp [Matrix.traceLeft, hij]

private theorem finiteAEPFullRankRegularization_whiteNoise_traceLeft_scalar
    (ρ : MState (a × b)) (η : ℝ) :
    ((η / (Fintype.card (a × b) : ℝ) : ℝ) *
        (Fintype.card a : ℝ)) =
      η / (Fintype.card b : ℝ) := by
  let : Nonempty (a × b) := ρ.nonempty
  let : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  let : Nonempty b := ⟨(Classical.choice ρ.nonempty).2⟩
  have ha : (Fintype.card a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card a ≠ 0))
  have hb : (Fintype.card b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card b ≠ 0))
  have hprod :
      (Fintype.card (a × b) : ℝ) =
        (Fintype.card a : ℝ) * (Fintype.card b : ℝ) := by
    exact_mod_cast (Fintype.card_prod a b)
  rw [hprod]
  field_simp [ha, hb]

/-- The `B` marginal of the white-noise regularization is the matching
white-noise regularization of `ρ_B`. -/
theorem finiteAEPFullRankRegularization_traceLeft_matrix
    (ρ : MState (a × b)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).traceLeft.m =
      (((1 - η : ℝ) : ℂ) • ρ.traceLeft.m) +
        ((((η / (Fintype.card b : ℝ) : ℝ)) : ℂ) • (1 : CMatrix b)) := by
  simp only [MState.traceLeft_m, finiteAEPFullRankRegularization_matrix]
  unfold finiteAEPFullRankRegularizationMatrix
  rw [Matrix.traceLeft_add, Matrix.traceLeft_smul, Matrix.traceLeft_smul,
    traceLeft_one_forFiniteAEP]
  rw [smul_smul]
  have hscalar :
      (((η / (Fintype.card (a × b) : ℝ) : ℝ) : ℂ) *
          (Fintype.card a : ℂ)) =
        (((η / (Fintype.card b : ℝ) : ℝ) : ℂ)) := by
    exact_mod_cast
      finiteAEPFullRankRegularization_whiteNoise_traceLeft_scalar
        (a := a) (b := b) ρ η
  rw [hscalar]

/-- The `B` marginal of the regularized state is positive definite for every
positive regularization weight. -/
theorem finiteAEPFullRankRegularization_traceLeft_posDef
    (ρ : MState (a × b)) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hηpos : 0 < η) :
    (ρ.finiteAEPFullRankRegularization η hη0 hη1).traceLeft.m.PosDef := by
  let : Nonempty b := ⟨(Classical.choice ρ.nonempty).2⟩
  rw [finiteAEPFullRankRegularization_traceLeft_matrix]
  have hleft : (0 : ℂ) ≤ (((1 - η : ℝ) : ℂ)) := by
    exact_mod_cast sub_nonneg.mpr hη1
  have hright : 0 < η / (Fintype.card b : ℝ) := by
    exact div_pos hηpos (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card b))
  exact Matrix.PosDef.posSemidef_add
    (Matrix.PosSemidef.smul ρ.traceLeft.psd hleft)
    (cMatrix_real_smul_one_posDef hright)

/-- The full-rank regularization matrix tends back to the original state
matrix as the noise weight tends to zero through positive probabilities. -/
theorem finiteAEPFullRankRegularizationMatrix_tendsto_zero
    (ρ : MState (a × b)) :
    Filter.Tendsto (fun η : ℝ => finiteAEPFullRankRegularizationMatrix ρ η)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ.m) := by
  have hcont : Continuous fun η : ℝ =>
      finiteAEPFullRankRegularizationMatrix ρ η := by
    unfold finiteAEPFullRankRegularizationMatrix
    fun_prop
  have h0 : finiteAEPFullRankRegularizationMatrix ρ 0 = ρ.m := by
    simp [finiteAEPFullRankRegularizationMatrix]
  simpa [h0] using
    (hcont.continuousWithinAt (x := (0 : ℝ)) (s := Set.Ioo (0 : ℝ) 1)).tendsto

/-- The expanded `B`-marginal white-noise regularization matrix tends back to
the original `B` marginal as the noise weight tends to zero through positive
probabilities. -/
theorem finiteAEPFullRankRegularization_traceLeft_matrix_path_tendsto_zero
    (ρ : MState (a × b)) :
    Filter.Tendsto
      (fun η : ℝ =>
        (((1 - η : ℝ) : ℂ) • ρ.traceLeft.m) +
          ((((η / (Fintype.card b : ℝ) : ℝ)) : ℂ) • (1 : CMatrix b)))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ.traceLeft.m) := by
  have hcont : Continuous fun η : ℝ =>
      (((1 - η : ℝ) : ℂ) • ρ.traceLeft.m) +
        ((((η / (Fintype.card b : ℝ) : ℝ)) : ℂ) • (1 : CMatrix b)) := by
    fun_prop
  have h0 :
      (((1 - (0 : ℝ) : ℝ) : ℂ) • ρ.traceLeft.m) +
          ((((0 / (Fintype.card b : ℝ) : ℝ)) : ℂ) • (1 : CMatrix b)) =
        ρ.traceLeft.m := by
    simp
  simpa [h0] using
    (hcont.continuousWithinAt (x := (0 : ℝ)) (s := Set.Ioo (0 : ℝ) 1)).tendsto

/-- The `B` marginal matrix of the full-rank regularized state tends back to
the original `B` marginal matrix as the noise weight tends to zero through
`η ∈ (0, 1)`.

Outside the interval the displayed path is filled in with the limiting matrix,
so it is a total function on `ℝ`; on the `nhdsWithin` filter it is eventually
equal to the actual regularized marginal. -/
theorem finiteAEPFullRankRegularization_traceLeft_matrix_tendsto_zero
    (ρ : MState (a × b)) :
    Filter.Tendsto
      (fun η : ℝ =>
        if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          (ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le).traceLeft.m
        else
          ρ.traceLeft.m)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ.traceLeft.m) := by
  refine Filter.Tendsto.congr' ?_
    (finiteAEPFullRankRegularization_traceLeft_matrix_path_tendsto_zero ρ)
  filter_upwards [self_mem_nhdsWithin] with η hη
  rw [dif_pos hη]
  exact
    (finiteAEPFullRankRegularization_traceLeft_matrix
      (a := a) (b := b) ρ η hη.1.le hη.2.le).symm

/-- The full-rank regularized state tends back to the original state as the
noise weight tends to zero through `η ∈ (0, 1)`.

Outside the interval the displayed path is filled in with the limiting state,
so it is a total function on `ℝ`; on the `nhdsWithin` filter it is eventually
equal to the actual regularized state. -/
theorem finiteAEPFullRankRegularization_tendsto_zero
    (ρ : MState (a × b)) :
    Filter.Tendsto
      (fun η : ℝ =>
        if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
        else
          ρ)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ) := by
  refine tendsto_of_tendsto_m ?_
  refine Filter.Tendsto.congr' ?_ (finiteAEPFullRankRegularizationMatrix_tendsto_zero ρ)
  filter_upwards [self_mem_nhdsWithin] with η hη
  change ρ.finiteAEPFullRankRegularizationMatrix η =
    (if hη' : η ∈ Set.Ioo (0 : ℝ) 1 then
      ρ.finiteAEPFullRankRegularization η hη'.1.le hη'.2.le
    else ρ).m
  rw [dif_pos hη, finiteAEPFullRankRegularization_matrix]

/-- Conditional entropy is continuous along the full-rank white-noise
regularization path. -/
theorem finiteAEPFullRankRegularization_conditionalEntropy_tendsto_zero
    (ρ : MState (a × b)) :
    Filter.Tendsto
      (fun η : ℝ =>
        (if hη : η ∈ Set.Ioo (0 : ℝ) 1 then
          ρ.finiteAEPFullRankRegularization η hη.1.le hη.2.le
        else
          ρ).conditionalEntropy)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ.conditionalEntropy) :=
  MState.conditionalEntropy_continuous.tendsto ρ |>.comp
    (finiteAEPFullRankRegularization_tendsto_zero ρ)

/-- Fixed tensor powers are continuous as maps of the input density state. -/
theorem tensorPower_matrix_continuous (n : ℕ) :
    Continuous (fun ρ : MState a => (ρ.tensorPower n).m) := by
  induction n with
  | zero =>
      simp only [MState.tensorPower_zero_matrix]
      fun_prop
  | succ n ih =>
      change Continuous fun ρ : MState a => (ρ.prod (ρ.tensorPower n)).m
      refine continuous_pi ?_
      intro i
      refine continuous_pi ?_
      intro j
      cases i with
      | mk i0 it =>
        cases j with
        | mk j0 jt =>
          simp [Matrix.kroneckerMap_apply]
          exact ((continuous_apply j0).comp
              ((continuous_apply i0).comp MState.continuous_matrix)).mul
            ((continuous_apply jt).comp ((continuous_apply it).comp ih))

/-- Fixed tensor powers are continuous at the state level. -/
theorem tensorPower_continuous (n : ℕ) :
    Continuous (fun ρ : MState a => ρ.tensorPower n) :=
  continuous_of_continuous_m (tensorPower_matrix_continuous (a := a) n)

/-- Fixed bipartite tensor powers are continuous as matrix-valued maps of the
input density state. -/
theorem tensorPowerBipartite_matrix_continuous (n : ℕ) :
    Continuous (fun ρ : MState (a × b) => (ρ.tensorPowerBipartite n).m) := by
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro j
  simp [MState.tensorPowerBipartite]
  exact (continuous_apply ((tensorPowerProdEquiv a b n).symm j)).comp
    ((continuous_apply ((tensorPowerProdEquiv a b n).symm i)).comp
      (tensorPower_matrix_continuous (a := a × b) n))

/-- Fixed bipartite tensor powers are continuous at the state level. -/
theorem tensorPowerBipartite_continuous (n : ℕ) :
    Continuous (fun ρ : MState (a × b) => ρ.tensorPowerBipartite n) :=
  continuous_of_continuous_m (tensorPowerBipartite_matrix_continuous (a := a) (b := b) n)

/-- Bipartite tensor powers of the full-rank white-noise regularization tend
back to the tensor power of the original state. -/
theorem finiteAEPFullRankRegularization_tensorPowerBipartite_tendsto_zero
    (ρ : MState (a × b)) (n : ℕ) :
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
    (ρ : MState (a × b)) (n : ℕ) :
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
  simpa [Function.comp_def] using hcont.tendsto (ρ.tensorPowerBipartite n) |>.comp
    (finiteAEPFullRankRegularization_tensorPowerBipartite_tendsto_zero ρ n)

/-- Bipartite tensor powers of the full-rank regularization approach the
original tensor power in purified distance. -/
theorem finiteAEPFullRankRegularization_tensorPowerBipartite_purifiedDistance_tendsto_zero
    (ρ : MState (a × b)) (n : ℕ) :
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
  · simp [MState.purifiedDistance_eq]
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
    (ρ : MState (a × b)) (n : ℕ) :
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
  rw [MState.toSubnormalized_purifiedDistance_eq]

/-- Eventually the regularized tensor power lies in any prescribed
subnormalized purified-distance ball around the original tensor power. -/
theorem finiteAEPFullRankRegularization_tensorPowerBipartite_toSubnormalized_purifiedDistance_eventually_le
    (ρ : MState (a × b)) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
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
    (ρ : MState (a × b)) (n : ℕ)
    {ξ ε δ targetL regL : ℝ} (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hε_nonneg : 0 ≤ ε)
    (hεδ_nonneg : 0 ≤ ε + δ) (hεδ_lt : ε + δ < 1)
    (hcenter :
      ((ρ.finiteAEPFullRankRegularization ξ hξ.1.le hξ.2.le).tensorPowerBipartite
          n).toSubnormalized.purifiedDistance
        (ρ.tensorPowerBipartite n).toSubnormalized ≤ δ)
    (hreg :
      regL ≤
        (ρ.finiteAEPFullRankRegularization ξ hξ.1.le
          hξ.2.le).tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw ε n)
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
    (ρ : MState (a × b)) (ε η : ℝ) (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1) (n : ℕ)
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
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (σ : MState b) (hσ : σ.m.PosDef)
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
    (ρ : MState (a × b))
    (σ : MState b) (hσ : σ.m.PosDef)
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
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (σ : MState b) (hσ : σ.m.PosDef)
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
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (σ : MState b) (hσ : σ.m.PosDef)
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
      cMatrixPetzTraceEffectVariational ρ.m
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
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (σ : MState b) (hσ : σ.m.PosDef)
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
      let H : CMatrix (a × b) :=
        ρ.m - lam • identityTensorStateMatrix (a := a) σ
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρ.petzSmoothMinThresholdScale_pos hρ σ hσ ε α hα_pos hα_ne_one)
        ).isHermitian)
      let U : Matrix.unitaryGroup (a × b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceKernelDephaseMonotone ρ.m
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
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (hρB : ρ.traceLeft.m.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB)))
    (hpetz :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ ρ.traceLeft hρB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      (ρ.fixedPetzThresholdPositivePart ρ.traceLeft lam).trace.re ≤
        lam ^ (1 - α) * ρ.conditionalPetzRenyiTraceTerm ρ.traceLeft α) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized ρ.traceLeft.toSubnormalized ε ≥
      ρ.conditionalEntropy -
        4 * (α - 1) *
          (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  have hcore :=
    ρ.relativeFiniteAEP_core_posDef_of_fixedPetzSmoothMinG_petzTrace
      hρ ρ.traceLeft hρB ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [finiteAEPEta_eq] using hα_lt) hpetz
  rw [ρ.conditionalEntropyRelative_to_conditionalEntropy hρ hρB] at hcore
  simpa [finiteAEPEta_eq] using hcore

/-- Canonical positive-definite finite-AEP core for the public side reference
`σ = ρ_B`, with the remaining source step expressed as the Petz
effect-variational inequality. -/
theorem finiteAEP_core_posDef_of_fixedPetzSmoothMinG_effectVariational
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (hρB : ρ.traceLeft.m.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB)))
    (hvar :
      let lam : ℝ :=
        ρ.petzSmoothMinThresholdScale hρ ρ.traceLeft hρB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational ρ.m
        (identityTensorStateMatrix (a := a) ρ.traceLeft) lam α) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized ρ.traceLeft.toSubnormalized ε ≥
      ρ.conditionalEntropy -
        4 * (α - 1) *
          (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  have hcore :=
    ρ.relativeFiniteAEP_core_posDef_of_fixedPetzSmoothMinG_effectVariational
      hρ ρ.traceLeft hρB ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [finiteAEPEta_eq] using hα_lt) hvar
  rw [ρ.conditionalEntropyRelative_to_conditionalEntropy hρ hρB] at hcore
  simpa [finiteAEPEta_eq] using hcore

/-- Canonical positive-definite finite-AEP core for the public side reference
`σ = ρ_B`, with the remaining source step expressed as the Hilbert-Schmidt
kernel dephasing monotonicity inequality. -/
theorem finiteAEP_core_posDef_of_fixedPetzSmoothMinG_kernelDephaseMonotone
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (hρB : ρ.traceLeft.m.PosDef)
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
        ρ.petzSmoothMinThresholdScale hρ ρ.traceLeft hρB ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) ρ.traceLeft).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) ρ.traceLeft hρB
      let H : CMatrix (a × b) :=
        ρ.m - lam • identityTensorStateMatrix (a := a) ρ.traceLeft
      let hH : H.IsHermitian :=
        hρ.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρ.petzSmoothMinThresholdScale_pos hρ ρ.traceLeft hρB ε α hα_pos hα_ne_one)
        ).isHermitian)
      let U : Matrix.unitaryGroup (a × b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceKernelDephaseMonotone ρ.m
        (identityTensorStateMatrix (a := a) ρ.traceLeft) U α) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized ρ.traceLeft.toSubnormalized ε ≥
      ρ.conditionalEntropy -
        4 * (α - 1) *
          (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 -
        (1 / (α - 1)) * log2 (2 / ε ^ 2) := by
  have hcore :=
    ρ.relativeFiniteAEP_core_posDef_of_fixedPetzSmoothMinG_kernelDephaseMonotone
      hρ ρ.traceLeft hρB ε α hε_pos hε_lt hα_gt hα_le_two
      (by simpa [finiteAEPEta_eq] using hα_lt) hkernel
  rw [ρ.conditionalEntropyRelative_to_conditionalEntropy hρ hρB] at hcore
  simpa [finiteAEPEta_eq] using hcore

/-- Optimized scalar-choice finite-AEP core with explicit tensor-power
bookkeeping assumptions.

The state `ρn` is intentionally arbitrary: downstream tensor-power work should
instantiate it with `ρ_AB^{⊗ n}` and prove the displayed entropy and eta-growth
hypotheses.  The Petz positive-part trace estimate is still explicit. -/
theorem finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_petzTrace
    (ρn : MState (a × b)) (hρn : ρn.m.PosDef)
    (hρnB : ρn.traceLeft.m.PosDef)
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
        ρn.petzSmoothMinThresholdScale hρn ρn.traceLeft hρnB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      (ρn.fixedPetzThresholdPositivePart ρn.traceLeft lam).trace.re ≤
        lam ^ (1 - α) * ρn.conditionalPetzRenyiTraceTerm ρn.traceLeft α) :
    ρn.smoothConditionalMinEntropyFixedSubnormalized ρn.traceLeft.toSubnormalized ε ≥
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
          ρn.traceLeft.toSubnormalized ε ≥
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
    (ρn : MState (a × b)) (hρn : ρn.m.PosDef)
    (hρnB : ρn.traceLeft.m.PosDef)
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
        ρn.petzSmoothMinThresholdScale hρn ρn.traceLeft hρnB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational ρn.m
        (identityTensorStateMatrix (a := a) ρn.traceLeft) lam α) :
    ρn.smoothConditionalMinEntropyFixedSubnormalized ρn.traceLeft.toSubnormalized ε ≥
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
    ρn.petzSmoothMinThresholdScale hρn ρn.traceLeft hρnB ε α
      (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
  have hlam : 0 < lam := by
    simpa [lam] using
      ρn.petzSmoothMinThresholdScale_pos hρn ρn.traceLeft hρnB ε α
        (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
  have hvar_lam :
      cMatrixPetzTraceEffectVariational ρn.m
        (identityTensorStateMatrix (a := a) ρn.traceLeft) lam α := by
    simpa [lam, hα_gt] using hvar
  have hpetz :
      (ρn.fixedPetzThresholdPositivePart ρn.traceLeft lam).trace.re ≤
        lam ^ (1 - α) * ρn.conditionalPetzRenyiTraceTerm ρn.traceLeft α :=
    ρn.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_effect_variational
      hρn ρn.traceLeft hρnB hlam hα_gt hα_le_two hvar_lam
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
    (ρn : MState (a × b)) (hρn : ρn.m.PosDef)
    (hρnB : ρn.traceLeft.m.PosDef)
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
        ρn.petzSmoothMinThresholdScale hρn ρn.traceLeft hρnB ε α hα_pos
          hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) ρn.traceLeft).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) ρn.traceLeft hρnB
      let Hmat : CMatrix (a × b) :=
        ρn.m - lam • identityTensorStateMatrix (a := a) ρn.traceLeft
      let hH : Hmat.IsHermitian :=
        hρn.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρn.petzSmoothMinThresholdScale_pos hρn ρn.traceLeft hρnB ε α
            hα_pos hα_ne_one)).isHermitian)
      let U : Matrix.unitaryGroup (a × b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρn.m
        (identityTensorStateMatrix (a := a) ρn.traceLeft) U α) :
    ρn.smoothConditionalMinEntropyFixedSubnormalized ρn.traceLeft.toSubnormalized ε ≥
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
    ρn.petzSmoothMinThresholdScale hρn ρn.traceLeft hρnB ε α hα_pos hα_ne_one
  have hlam : 0 < lam := by
    simpa [lam, hα_pos, hα_ne_one] using
      ρn.petzSmoothMinThresholdScale_pos hρn ρn.traceLeft hρnB ε α
        hα_pos hα_ne_one
  have hmono_lam :
      let hB : (identityTensorStateMatrix (a := a) ρn.traceLeft).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) ρn.traceLeft hρnB
      let Hmat : CMatrix (a × b) :=
        ρn.m - lam • identityTensorStateMatrix (a := a) ρn.traceLeft
      let hH : Hmat.IsHermitian :=
        hρn.isHermitian.sub ((Matrix.PosDef.smul hB hlam).isHermitian)
      let U : Matrix.unitaryGroup (a × b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρn.m
        (identityTensorStateMatrix (a := a) ρn.traceLeft) U α := by
    simpa [lam, hα_gt, hα_pos, hα_ne_one, hlam] using hmono
  have hpetz :
      (ρn.fixedPetzThresholdPositivePart ρn.traceLeft lam).trace.re ≤
        lam ^ (1 - α) * ρn.conditionalPetzRenyiTraceTerm ρn.traceLeft α :=
    ρn.fixedPetzThresholdPositivePart_trace_re_le_petzTrace_of_unitaryDephaseMonotone
      hρn ρn.traceLeft hρnB hlam hα_gt hα_le_two hmono_lam
  exact
    ρn.finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_petzTrace
      hρn hρnB ε η α H hM hL hn hα_opt hε_pos hε_lt hα_le_two hα_lt
      hentropy_tensor heta_tensor
      (by simpa [lam, hα_gt, hα_pos, hα_ne_one] using hpetz)

/-- Every state on a one-element system is the `1 x 1` identity matrix. -/
private theorem matrix_eq_one_of_card_eq_one {c : Type w} [Fintype c] [DecidableEq c]
    (hc : Fintype.card c = 1) (σ : MState c) : σ.m = 1 := by
  have hsub : Subsingleton c := Fintype.card_le_one_iff_subsingleton.mp hc.le
  ext i j
  have huniv : (Finset.univ : Finset c) = {i} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨Finset.mem_univ i, fun x _ => Subsingleton.elim x i⟩
  have h := σ.tr'
  simp only [Matrix.trace, Matrix.diag_apply, huniv, Finset.sum_singleton] at h
  rw [Subsingleton.elim j i, Matrix.one_apply_eq]
  exact h

/-- A one-element system carries a unique state. -/
private theorem eq_of_card_eq_one {c : Type w} [Fintype c] [DecidableEq c]
    (hc : Fintype.card c = 1) (σ τ : MState c) : σ = τ :=
  MState.ext ((matrix_eq_one_of_card_eq_one hc σ).trans
    (matrix_eq_one_of_card_eq_one hc τ).symm)

omit [DecidableEq a] in
/-- The zeroth tensor power is a one-element system. -/
private theorem card_tensorPower_zero : Fintype.card (TensorPower a 0) = 1 := by
  simp [tensorPower_card]

omit [DecidableEq a] [DecidableEq b] in
/-- The zeroth bipartite tensor power is a one-element system. -/
private theorem card_tensorPower_zero_prod :
    Fintype.card (TensorPower a 0 × TensorPower b 0) = 1 := by
  simp [tensorPower_card]

/-- Applying two right-reference isometries before taking a product state is
the same as applying their product isometry after the standard regrouping. -/
theorem conditioningIsometryApply_prod_reindex_grouped
    {a' : Type*} {c : Type*} {bPlus : Type*} {cPlus : Type*}
    [Fintype a'] [DecidableEq a'] [Fintype c] [DecidableEq c]
    [Fintype bPlus] [DecidableEq bPlus] [Fintype cPlus] [DecidableEq cPlus]
    (ρ : MState (a × b)) (σ : MState (a' × c))
    (V : ReferenceIsometry b bPlus) (W : ReferenceIsometry c cPlus) :
    ((ρ.conditioningIsometryApply V).prod (σ.conditioningIsometryApply W)).reindex
        (Equiv.prodProdProdComm a bPlus a' cPlus) =
      MState.conditioningIsometryApply
        ((ρ.prod σ).reindex (Equiv.prodProdProdComm a b a' c))
        (V.prod W) := by
  apply MState.ext
  ext x y
  rcases x with ⟨⟨xA, xA'⟩, ⟨xB, xC⟩⟩
  rcases y with ⟨⟨yA, yA'⟩, ⟨yB, yC⟩⟩
  simp [MState.conditioningIsometryApply_matrix,
    ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
    ReferenceIsometry.prod, Equiv.prodProdProdComm,
    Matrix.kroneckerMap_apply, Matrix.mul_apply,
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
    (ρ : MState (a × b)) (V : ReferenceIsometry b bPlus) :
    ∀ n : ℕ,
      (ρ.conditioningIsometryApply V).tensorPowerBipartite n =
        (ρ.tensorPowerBipartite n).conditioningIsometryApply (V.tensorPower n)
  | 0 => eq_of_card_eq_one card_tensorPower_zero_prod _ _
  | n + 1 => by
      have ih := conditioningIsometryApply_tensorPowerBipartite ρ V n
      rw [MState.tensorPowerBipartite_succ_grouped_forAlphaContinuity]
      rw [ih]
      rw [conditioningIsometryApply_prod_reindex_grouped]
      rw [← MState.tensorPowerBipartite_succ_grouped_forAlphaContinuity]
      rfl

/-- Embedding normalized states as subnormalized states commutes with applying
a right-reference isometry. -/
theorem toSubnormalized_conditioningIsometryApply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (ρ : MState (a × b)) (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).toSubnormalized =
      ρ.toSubnormalized.conditioningIsometryApply V := by
  apply SubnormalizedState.ext
  rw [MState.toSubnormalized_matrix]
  rw [SubnormalizedState.conditioningIsometryApply_matrix]
  rw [MState.conditioningIsometryApply_matrix]
  rfl

theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_succ_of_regroupedCandidate
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (hρB : ρ.traceLeft.m.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : ℕ)
    (hregroup :
      (ρ.tensorPowerBipartite (n + 1)).conditionalPetzRenyiEntropyCandidate
          (tensorPowerBipartite_posDef ρ hρ (n + 1))
          (ρ.tensorPowerBipartite (n + 1)).traceLeft
          (tensorPowerBipartite_traceLeft_posDef ρ hρB (n + 1))
          α hα_pos hα_ne_one =
        (((ρ.prod (ρ.tensorPowerBipartite n)).reindex
            (Equiv.prodProdProdComm
              a b (TensorPower a n) (TensorPower b n))).conditionalPetzRenyiEntropyCandidate
            (MState.reindex_posDef
              (ρ.prod (ρ.tensorPowerBipartite n))
              (Equiv.prodProdProdComm
                a b (TensorPower a n) (TensorPower b n))
              (MState.PosDef.kron hρ
                (tensorPowerBipartite_posDef ρ hρ n)))
            (ρ.traceLeft.prod (ρ.tensorPowerBipartite n).traceLeft)
            (MState.PosDef.kron hρB
              (tensorPowerBipartite_traceLeft_posDef ρ hρB n))
            α hα_pos hα_ne_one)) :
    (ρ.tensorPowerBipartite (n + 1)).conditionalPetzRenyiEntropyCandidate
        (tensorPowerBipartite_posDef ρ hρ (n + 1))
        (ρ.tensorPowerBipartite (n + 1)).traceLeft
        (tensorPowerBipartite_traceLeft_posDef ρ hρB (n + 1))
        α hα_pos hα_ne_one =
      ρ.conditionalPetzRenyiEntropyCandidate
          hρ ρ.traceLeft hρB α hα_pos hα_ne_one +
        (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
          (tensorPowerBipartite_posDef ρ hρ n)
          (ρ.tensorPowerBipartite n).traceLeft
          (tensorPowerBipartite_traceLeft_posDef ρ hρB n)
          α hα_pos hα_ne_one := by
  have hprod :=
    conditionalPetzRenyiEntropyCandidate_prod_grouped_posDef
      (ρ₁ := ρ) (σ₁ := ρ.traceLeft)
      (ρ₂ := ρ.tensorPowerBipartite n)
      (σ₂ := (ρ.tensorPowerBipartite n).traceLeft)
      hρ hρB
      (tensorPowerBipartite_posDef ρ hρ n)
      (tensorPowerBipartite_traceLeft_posDef ρ hρB n)
      α hα_pos hα_ne_one
  exact hregroup.trans hprod

theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_succ
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (hρB : ρ.traceLeft.m.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : ℕ) :
    (ρ.tensorPowerBipartite (n + 1)).conditionalPetzRenyiEntropyCandidate
        (tensorPowerBipartite_posDef ρ hρ (n + 1))
        (ρ.tensorPowerBipartite (n + 1)).traceLeft
        (tensorPowerBipartite_traceLeft_posDef ρ hρB (n + 1))
        α hα_pos hα_ne_one =
      ρ.conditionalPetzRenyiEntropyCandidate
          hρ ρ.traceLeft hρB α hα_pos hα_ne_one +
        (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
          (tensorPowerBipartite_posDef ρ hρ n)
          (ρ.tensorPowerBipartite n).traceLeft
          (tensorPowerBipartite_traceLeft_posDef ρ hρB n)
          α hα_pos hα_ne_one := by
  refine
    tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_succ_of_regroupedCandidate
      ρ hρ hρB α hα_pos hα_ne_one n ?_
  let τ : MState ((a × TensorPower a n) × (b × TensorPower b n)) :=
    (ρ.prod (ρ.tensorPowerBipartite n)).reindex
      (Equiv.prodProdProdComm
        a b (TensorPower a n) (TensorPower b n))
  have hτ :
      ρ.tensorPowerBipartite (n + 1) = τ :=
    tensorPowerBipartite_succ_grouped_forAlphaContinuity ρ n
  have hτB :
      τ.traceLeft = ρ.traceLeft.prod (ρ.tensorPowerBipartite n).traceLeft := by
    simpa [τ] using tensorPowerBipartite_succ_grouped_traceLeft_forAlphaContinuity ρ n
  have hτ_matrix :
      (ρ.tensorPowerBipartite (n + 1)).m = τ.m :=
    congrArg DensityOp.m hτ
  have hτB_matrix :
      (ρ.tensorPowerBipartite (n + 1)).traceLeft.m =
        (ρ.traceLeft.prod (ρ.tensorPowerBipartite n).traceLeft).m := by
    rw [hτ]
    exact congrArg DensityOp.m hτB
  have hτB_ref :
      identityTensorStateMatrix (a := TensorPower a (n + 1))
          (ρ.tensorPowerBipartite (n + 1)).traceLeft =
        identityTensorStateMatrix (a := a × TensorPower a n)
          (ρ.traceLeft.prod (ρ.tensorPowerBipartite n).traceLeft) := by
    unfold identityTensorStateMatrix
    rw [hτB_matrix]
    rfl
  dsimp [conditionalPetzRenyiEntropyCandidate, conditionalPetzRenyiTraceTerm]
  rw [hτ_matrix, hτB_ref]
  rfl

theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidateFullReference_succ
    (ρ : MState (a × b)) (hρB : ρ.traceLeft.m.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : ℕ) :
    (ρ.tensorPowerBipartite (n + 1)).conditionalPetzRenyiEntropyCandidateFullReference
        (ρ.tensorPowerBipartite (n + 1)).traceLeft
        (tensorPowerBipartite_traceLeft_posDef ρ hρB (n + 1))
        α hα_pos hα_ne_one =
      ρ.conditionalPetzRenyiEntropyCandidateFullReference
          ρ.traceLeft hρB α hα_pos hα_ne_one +
        (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidateFullReference
          (ρ.tensorPowerBipartite n).traceLeft
          (tensorPowerBipartite_traceLeft_posDef ρ hρB n)
          α hα_pos hα_ne_one := by
  let τ : MState ((a × TensorPower a n) × (b × TensorPower b n)) :=
    (ρ.prod (ρ.tensorPowerBipartite n)).reindex
      (Equiv.prodProdProdComm
        a b (TensorPower a n) (TensorPower b n))
  have hτ :
      ρ.tensorPowerBipartite (n + 1) = τ :=
    tensorPowerBipartite_succ_grouped_forAlphaContinuity ρ n
  have hτB :
      τ.traceLeft = ρ.traceLeft.prod (ρ.tensorPowerBipartite n).traceLeft := by
    simpa [τ] using tensorPowerBipartite_succ_grouped_traceLeft_forAlphaContinuity ρ n
  have hregroup :
      (ρ.tensorPowerBipartite (n + 1)).conditionalPetzRenyiEntropyCandidateFullReference
          (ρ.tensorPowerBipartite (n + 1)).traceLeft
          (tensorPowerBipartite_traceLeft_posDef ρ hρB (n + 1))
          α hα_pos hα_ne_one =
        τ.conditionalPetzRenyiEntropyCandidateFullReference
          (ρ.traceLeft.prod (ρ.tensorPowerBipartite n).traceLeft)
          (MState.PosDef.kron hρB
            (tensorPowerBipartite_traceLeft_posDef ρ hρB n))
          α hα_pos hα_ne_one := by
    have hτ_matrix :
        (ρ.tensorPowerBipartite (n + 1)).m = τ.m :=
      congrArg DensityOp.m hτ
    have hτB_matrix :
        (ρ.tensorPowerBipartite (n + 1)).traceLeft.m =
          (ρ.traceLeft.prod (ρ.tensorPowerBipartite n).traceLeft).m := by
      rw [hτ]
      exact congrArg DensityOp.m hτB
    have hτB_ref :
        identityTensorStateMatrix (a := TensorPower a (n + 1))
            (ρ.tensorPowerBipartite (n + 1)).traceLeft =
          identityTensorStateMatrix (a := a × TensorPower a n)
            (ρ.traceLeft.prod (ρ.tensorPowerBipartite n).traceLeft) := by
      unfold identityTensorStateMatrix
      rw [hτB_matrix]
      rfl
    dsimp [conditionalPetzRenyiEntropyCandidateFullReference, conditionalPetzRenyiTraceTerm]
    rw [hτ_matrix, hτB_ref]
    rfl
  have hprod :=
    conditionalPetzRenyiEntropyCandidateFullReference_prod_grouped
      (ρ₁ := ρ) (σ₁ := ρ.traceLeft)
      (ρ₂ := ρ.tensorPowerBipartite n)
      (σ₂ := (ρ.tensorPowerBipartite n).traceLeft)
      hρB
      (tensorPowerBipartite_traceLeft_posDef ρ hρB n)
      α hα_pos hα_ne_one
  exact hregroup.trans hprod

theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_zero
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (hρB : ρ.traceLeft.m.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    (ρ.tensorPowerBipartite 0).conditionalPetzRenyiEntropyCandidate
        (tensorPowerBipartite_posDef ρ hρ 0)
        (ρ.tensorPowerBipartite 0).traceLeft
        (tensorPowerBipartite_traceLeft_posDef ρ hρB 0)
        α hα_pos hα_ne_one = 0 := by
  have hmat :
      (ρ.tensorPowerBipartite 0).m =
        (1 : CMatrix (TensorPower a 0 × TensorPower b 0)) :=
    matrix_eq_one_of_card_eq_one card_tensorPower_zero_prod _
  have hBmat :
      (ρ.tensorPowerBipartite 0).traceLeft.m =
        (1 : CMatrix (TensorPower b 0)) :=
    matrix_eq_one_of_card_eq_one card_tensorPower_zero _
  have href :
      identityTensorStateMatrix (a := TensorPower a 0)
          (ρ.tensorPowerBipartite 0).traceLeft =
        (1 : CMatrix (TensorPower a 0 × TensorPower b 0)) := by
    unfold identityTensorStateMatrix
    rw [hBmat]
    exact Matrix.one_kronecker_one
  unfold conditionalPetzRenyiEntropyCandidate
  rw [hmat, href]
  dsimp only
  change 1 / (1 - α) *
      log2 ((((1 : CMatrix (TensorPower a 0 × TensorPower b 0)) ^ α) *
        ((1 : CMatrix (TensorPower a 0 × TensorPower b 0)) ^ (1 - α))).trace.re) =
    0
  rw [show ((1 : CMatrix (TensorPower a 0 × TensorPower b 0)) ^ α) = 1 by
      exact CFC.one_rpow,
    show ((1 : CMatrix (TensorPower a 0 × TensorPower b 0)) ^ (1 - α)) = 1 by
      exact CFC.one_rpow,
    one_mul, Matrix.trace_one]
  have hcard : Fintype.card (TensorPower a 0 × TensorPower b 0) = 1 := by
    change Fintype.card (PUnit × PUnit) = 1
    simp
  simp [hcard, log2]

theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidateFullReference_zero
    (ρ : MState (a × b)) (hρB : ρ.traceLeft.m.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    (ρ.tensorPowerBipartite 0).conditionalPetzRenyiEntropyCandidateFullReference
        (ρ.tensorPowerBipartite 0).traceLeft
        (tensorPowerBipartite_traceLeft_posDef ρ hρB 0)
        α hα_pos hα_ne_one = 0 := by
  have hmat :
      (ρ.tensorPowerBipartite 0).m =
        (1 : CMatrix (TensorPower a 0 × TensorPower b 0)) :=
    matrix_eq_one_of_card_eq_one card_tensorPower_zero_prod _
  have hBmat :
      (ρ.tensorPowerBipartite 0).traceLeft.m =
        (1 : CMatrix (TensorPower b 0)) :=
    matrix_eq_one_of_card_eq_one card_tensorPower_zero _
  have href :
      identityTensorStateMatrix (a := TensorPower a 0)
          (ρ.tensorPowerBipartite 0).traceLeft =
        (1 : CMatrix (TensorPower a 0 × TensorPower b 0)) := by
    unfold identityTensorStateMatrix
    rw [hBmat]
    exact Matrix.one_kronecker_one
  unfold conditionalPetzRenyiEntropyCandidateFullReference conditionalPetzRenyiTraceTerm
  rw [hmat, href]
  change 1 / (1 - α) *
      log2 ((((1 : CMatrix (TensorPower a 0 × TensorPower b 0)) ^ α) *
        ((1 : CMatrix (TensorPower a 0 × TensorPower b 0)) ^ (1 - α))).trace.re) =
    0
  rw [show ((1 : CMatrix (TensorPower a 0 × TensorPower b 0)) ^ α) = 1 by
      exact CFC.one_rpow,
    show ((1 : CMatrix (TensorPower a 0 × TensorPower b 0)) ^ (1 - α)) = 1 by
      exact CFC.one_rpow,
    one_mul, Matrix.trace_one]
  have hcard : Fintype.card (TensorPower a 0 × TensorPower b 0) = 1 := by
    change Fintype.card (PUnit × PUnit) = 1
    simp
  simp [hcard, log2]

/-- Conditional Petz alpha-entropy candidate is additive on bipartite tensor
powers relative to the corresponding tensor-power marginal reference. -/
theorem tensorPowerBipartite_conditionalPetzRenyiEntropyCandidate_additive
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (hρB : ρ.traceLeft.m.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : ℕ) :
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
        (tensorPowerBipartite_posDef ρ hρ n)
        (ρ.tensorPowerBipartite n).traceLeft
        (tensorPowerBipartite_traceLeft_posDef ρ hρB n)
        α hα_pos hα_ne_one =
      (n : ℝ) *
        ρ.conditionalPetzRenyiEntropyCandidate
          hρ ρ.traceLeft hρB α hα_pos hα_ne_one := by
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
    (ρ : MState (a × b)) (hρB : ρ.traceLeft.m.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (n : ℕ) :
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidateFullReference
        (ρ.tensorPowerBipartite n).traceLeft
        (tensorPowerBipartite_traceLeft_posDef ρ hρB n)
        α hα_pos hα_ne_one =
      (n : ℝ) *
        ρ.conditionalPetzRenyiEntropyCandidateFullReference
          ρ.traceLeft hρB α hα_pos hα_ne_one := by
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
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (hρB : ρ.traceLeft.m.PosDef)
    (α : ℝ) {n : ℕ}
    (hα_gt : 1 < α)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.finiteAEPEta hρ hρB))) :
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
        (tensorPowerBipartite_posDef ρ hρ n)
        (ρ.tensorPowerBipartite n).traceLeft
        (tensorPowerBipartite_traceLeft_posDef ρ hρB n)
        α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
      (n : ℝ) * ρ.conditionalEntropy -
        4 * (α - 1) * (n : ℝ) *
          (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  have hsingle :
      ρ.conditionalPetzRenyiEntropyCandidate
          hρ ρ.traceLeft hρB α hα_pos hα_ne_one ≥
        ρ.conditionalEntropy -
          4 * (α - 1) * (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 := by
    have h :=
      conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef
        (ρ := ρ) hρ (σ := ρ.traceLeft) hρB α hα_gt
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
            hρ ρ.traceLeft hρB α hα_pos hα_ne_one :=
    mul_le_mul_of_nonneg_left hsingle hn_nonneg
  calc
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidate
        (tensorPowerBipartite_posDef ρ hρ n)
        (ρ.tensorPowerBipartite n).traceLeft
        (tensorPowerBipartite_traceLeft_posDef ρ hρB n)
        α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
        = (n : ℝ) *
            ρ.conditionalPetzRenyiEntropyCandidate
              hρ ρ.traceLeft hρB α hα_pos hα_ne_one := by
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
    (ρ : MState (a × b))
    (hρB : ρ.traceLeft.m.PosDef)
    (α : ℝ) {n : ℕ}
    (hα_gt : 1 < α)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 ρ.finiteAEPEtaTrace)) :
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidateFullReference
        (ρ.tensorPowerBipartite n).traceLeft
        (tensorPowerBipartite_traceLeft_posDef ρ hρB n)
        α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
      (n : ℝ) * ρ.conditionalEntropy -
        4 * (α - 1) * (n : ℝ) *
          (log2 ρ.finiteAEPEtaTrace) ^ 2 := by
  let hα_pos : 0 < α := lt_trans zero_lt_one hα_gt
  let hα_ne_one : α ≠ 1 := (ne_of_lt hα_gt).symm
  have hsingle :
      ρ.conditionalPetzRenyiEntropyCandidateFullReference
          ρ.traceLeft hρB α hα_pos hα_ne_one ≥
        ρ.conditionalEntropy -
          4 * (α - 1) * (log2 ρ.finiteAEPEtaTrace) ^ 2 := by
    have h :=
      conditionalPetzRenyiEntropyCandidateFullReference_alpha_bound
        (ρ := ρ) (σ := ρ.traceLeft) hρB α hα_gt
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
            ρ.traceLeft hρB α hα_pos hα_ne_one :=
    mul_le_mul_of_nonneg_left hsingle hn_nonneg
  calc
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiEntropyCandidateFullReference
        (ρ.tensorPowerBipartite n).traceLeft
        (tensorPowerBipartite_traceLeft_posDef ρ hρB n)
        α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
        = (n : ℝ) *
            ρ.conditionalPetzRenyiEntropyCandidateFullReference
              ρ.traceLeft hρB α hα_pos hα_ne_one := by
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
    (ρn : MState (a × b))
    (σ : MState b) (hσ : σ.m.PosDef)
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
    (ρ : MState (a × b))
    (hρB : ρ.traceLeft.m.PosDef)
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
        (ρ.tensorPowerBipartite n).traceLeft.toSubnormalized ε ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε ρ.finiteAEPEtaTrace *
          Real.sqrt (n : ℝ) := by
  have hη3 : 3 ≤ ρ.finiteAEPEtaTrace := by
    simpa [finiteAEPEtaTrace] using
      conditionalAlphaConvergenceParameterTrace_ge_three
        (ρ := ρ) (σ := ρ.traceLeft) hρB
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
          (ρ.tensorPowerBipartite n).traceLeft
          (tensorPowerBipartite_traceLeft_posDef ρ hρB n)
          α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * ρ.conditionalEntropy -
          4 * (α - 1) * (n : ℝ) *
            (log2 ρ.finiteAEPEtaTrace) ^ 2 :=
    ρ.tensorPower_conditionalPetzRenyiEntropyCandidateFullReference_alpha_bound
      hρB α hα_gt hα_lt
  exact
    (ρ.tensorPowerBipartite n).finiteAEP_core_fullReference_optimized_petzAlphaBound
      (ρ.tensorPowerBipartite n).traceLeft
      (tensorPowerBipartite_traceLeft_posDef ρ hρB n)
      ε ρ.finiteAEPEtaTrace α ρ.conditionalEntropy hM hL hn hα_opt
      hε_pos hε_lt hα_le_two hpetz_alpha

/-- Tensor-power optimized finite-AEP core for optimized subnormalized smooth
min-entropy, using only a full-rank canonical marginal reference. -/
theorem tensorPowerFiniteAEP_core_fullReference_optimized_subnormalizedSmooth_additivePetz
    (ρ : MState (a × b))
    (hρB : ρ.traceLeft.m.PosDef)
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
          (ρ.tensorPowerBipartite n).traceLeft.toSubnormalized ε ≥
        (n : ℝ) * ρ.conditionalEntropy -
          QIT.finiteAEPDelta ε ρ.finiteAEPEtaTrace *
            Real.sqrt (n : ℝ) :=
    ρ.tensorPowerFiniteAEP_core_fullReference_optimized_additivePetz
      hρB ε α hM hn hα_opt hε_pos hε_lt hα_le_two hα_lt
  have hbridge :
      (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
          (ρ.tensorPowerBipartite n).traceLeft.toSubnormalized ε ≤
        ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_pos.le hε_lt :=
    (ρ.tensorPowerBipartite n)
      |>.smoothConditionalMinEntropyFixedSubnormalized_le_subnormalizedSmoothConditionalMinEntropy
        (ρ.tensorPowerBipartite n).traceLeft.toSubnormalized ε
        hε_pos.le hε_lt
        (fun ρ' _hball =>
          SubnormalizedState.conditionalMinEntropyFixed_feasibleSet_nonempty_of_posDef_reference
            (a := TensorPower a n) ρ' (ρ.tensorPowerBipartite n).traceLeft
            (tensorPowerBipartite_traceLeft_posDef ρ hρB n))
  exact le_trans hfixedCore hbridge

/-- Optimized scalar-choice finite-AEP core from a tensor/source-shaped Petz
alpha-bound.

Compared with
`finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational`, this
assembly lemma does not assume a tensor-power eta growth estimate.  It only
needs the already tensorized alpha-to-von-Neumann lower bound with the
single-copy eta parameter. -/
theorem finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational_petzAlphaBound
    (ρn : MState (a × b)) (hρn : ρn.m.PosDef)
    (hρnB : ρn.traceLeft.m.PosDef)
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
          hρn ρn.traceLeft hρnB α
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
        ρn.petzSmoothMinThresholdScale hρn ρn.traceLeft hρnB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational ρn.m
        (identityTensorStateMatrix (a := a) ρn.traceLeft) lam α) :
    ρn.smoothConditionalMinEntropyFixedSubnormalized ρn.traceLeft.toSubnormalized ε ≥
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
          hρn ρn.traceLeft hρnB
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 η * Real.sqrt (n : ℝ)))
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)) -
        (1 /
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) - 1)) *
          log2 (2 / ε ^ 2) ≤
        ρn.smoothConditionalMinEntropyFixedSubnormalized
          ρn.traceLeft.toSubnormalized ε := by
    exact
      ρn.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_effectVariational
        hρn ρn.traceLeft hρnB ε
        (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
        hε_pos hε_lt hα_gt hα_le_two
        (by simpa [hα_gt] using hvar)
  have hpetz_alpha' :
      ρn.conditionalPetzRenyiEntropyCandidate
          hρn ρn.traceLeft hρnB
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
        ρn.traceLeft.toSubnormalized ε ≥
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
    (ρn : MState (a × b)) (hρn : ρn.m.PosDef)
    (hρnB : ρn.traceLeft.m.PosDef)
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
          hρn ρn.traceLeft hρnB α
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
        ρn.petzSmoothMinThresholdScale hρn ρn.traceLeft hρnB ε α hα_pos
          hα_ne_one
      let hB : (identityTensorStateMatrix (a := a) ρn.traceLeft).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := a) ρn.traceLeft hρnB
      let Hmat : CMatrix (a × b) :=
        ρn.m - lam • identityTensorStateMatrix (a := a) ρn.traceLeft
      let hH : Hmat.IsHermitian :=
        hρn.isHermitian.sub ((Matrix.PosDef.smul hB
          (ρn.petzSmoothMinThresholdScale_pos hρn ρn.traceLeft hρnB ε α
            hα_pos hα_ne_one)).isHermitian)
      let U : Matrix.unitaryGroup (a × b) ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone ρn.m
        (identityTensorStateMatrix (a := a) ρn.traceLeft) U α) :
    ρn.smoothConditionalMinEntropyFixedSubnormalized ρn.traceLeft.toSubnormalized ε ≥
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
          hρn ρn.traceLeft hρnB
          (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
            (2 * log2 η * Real.sqrt (n : ℝ)))
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)) -
        (1 /
            (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
              (2 * log2 η * Real.sqrt (n : ℝ)) - 1)) *
          log2 (2 / ε ^ 2) ≤
        ρn.smoothConditionalMinEntropyFixedSubnormalized
          ρn.traceLeft.toSubnormalized ε := by
    exact
      ρn.smoothConditionalMinEntropyFixedSubnormalized_lower_bound_of_fixedPetzSmoothMinG_unitaryDephaseMonotone
        hρn ρn.traceLeft hρnB ε
        (1 + Real.sqrt (log2 (2 / ε ^ 2)) /
          (2 * log2 η * Real.sqrt (n : ℝ)))
        hε_pos hε_lt hα_gt hα_le_two
        (by simpa [hα_gt] using hmono)
  have hpetz_alpha' :
      ρn.conditionalPetzRenyiEntropyCandidate
          hρn ρn.traceLeft hρnB
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
        ρn.traceLeft.toSubnormalized ε ≥
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
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (hρB : ρ.traceLeft.m.PosDef)
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
      let hρn : (ρ.tensorPowerBipartite n).m.PosDef :=
        tensorPowerBipartite_posDef ρ hρ n
      let hρnB : (ρ.tensorPowerBipartite n).traceLeft.m.PosDef :=
        tensorPowerBipartite_traceLeft_posDef ρ hρB n
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
          hρn (ρ.tensorPowerBipartite n).traceLeft hρnB ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).traceLeft).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).traceLeft hρnB
      let Hmat : CMatrix (TensorPower a n × TensorPower b n) :=
        (ρ.tensorPowerBipartite n).m -
          lam • identityTensorStateMatrix (a := TensorPower a n)
            (ρ.tensorPowerBipartite n).traceLeft
      let hH : Hmat.IsHermitian :=
        hρn.isHermitian.sub ((Matrix.PosDef.smul hB
          ((ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale_pos
            hρn (ρ.tensorPowerBipartite n).traceLeft hρnB ε α hα_pos hα_ne_one)
        ).isHermitian)
      let U : Matrix.unitaryGroup (TensorPower a n × TensorPower b n) ℂ :=
        hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone (ρ.tensorPowerBipartite n).m
        (identityTensorStateMatrix (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).traceLeft) U α) :
    (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
        (ρ.tensorPowerBipartite n).traceLeft.toSubnormalized ε ≥
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
          (tensorPowerBipartite_posDef ρ hρ n)
          (ρ.tensorPowerBipartite n).traceLeft
          (tensorPowerBipartite_traceLeft_posDef ρ hρB n)
          α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * ρ.conditionalEntropy -
          4 * (α - 1) * (n : ℝ) *
            (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 :=
    ρ.tensorPower_conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef
      hρ hρB α hα_gt hα_lt
  exact
    finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_unitaryDephaseMonotone_petzAlphaBound
      (ρ.tensorPowerBipartite n)
      (tensorPowerBipartite_posDef ρ hρ n)
      (tensorPowerBipartite_traceLeft_posDef ρ hρB n)
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
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (hρB : ρ.traceLeft.m.PosDef)
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
      let hρn : (ρ.tensorPowerBipartite n).m.PosDef :=
        tensorPowerBipartite_posDef ρ hρ n
      let hρnB : (ρ.tensorPowerBipartite n).traceLeft.m.PosDef :=
        tensorPowerBipartite_traceLeft_posDef ρ hρB n
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
          hρn (ρ.tensorPowerBipartite n).traceLeft hρnB ε α hα_pos hα_ne_one
      let hB : (identityTensorStateMatrix (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).traceLeft).PosDef :=
        identityTensorStateMatrix_posDef_of_posDef (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).traceLeft hρnB
      let Hmat : CMatrix (TensorPower a n × TensorPower b n) :=
        (ρ.tensorPowerBipartite n).m -
          lam • identityTensorStateMatrix (a := TensorPower a n)
            (ρ.tensorPowerBipartite n).traceLeft
      let hH : Hmat.IsHermitian :=
        hρn.isHermitian.sub ((Matrix.PosDef.smul hB
          ((ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale_pos
            hρn (ρ.tensorPowerBipartite n).traceLeft hρnB ε α hα_pos hα_ne_one)
        ).isHermitian)
      let U : Matrix.unitaryGroup (TensorPower a n × TensorPower b n) ℂ :=
        hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone (ρ.tensorPowerBipartite n).m
        (identityTensorStateMatrix (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).traceLeft) U α) :
    ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_pos.le hε_lt ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB) *
          Real.sqrt (n : ℝ) := by
  have hfixedCore :
      (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
          (ρ.tensorPowerBipartite n).traceLeft.toSubnormalized ε ≥
        (n : ℝ) * ρ.conditionalEntropy -
          QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB) *
            Real.sqrt (n : ℝ) :=
    ρ.tensorPowerFiniteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_unitaryDephaseMonotone_additivePetz
      hρ hρB ε α hM hn hα_opt hε_pos hε_lt hα_le_two hα_lt hmono
  have hbridge :
      (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
          (ρ.tensorPowerBipartite n).traceLeft.toSubnormalized ε ≤
        ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_pos.le hε_lt :=
    (ρ.tensorPowerBipartite n)
      |>.smoothConditionalMinEntropyFixedSubnormalized_le_subnormalizedSmoothConditionalMinEntropy
        (ρ.tensorPowerBipartite n).traceLeft.toSubnormalized ε
        hε_pos.le hε_lt
        (fun ρ' _hball =>
          SubnormalizedState.conditionalMinEntropyFixed_feasibleSet_nonempty_of_posDef_reference
            (a := TensorPower a n) ρ' (ρ.tensorPowerBipartite n).traceLeft
            (tensorPowerBipartite_traceLeft_posDef ρ hρB n))
  exact le_trans hfixedCore hbridge

/-- Tensor-power optimized finite-AEP core from a global finite-uniform Petz
joint-convexity input on the tensor-power matrix dimension.

The remaining hypothesis `hjoint` is the precise noncommutative
perspective/joint-convexity theorem still needed for the source proof route.
All tensor-power bookkeeping, alpha-continuity, scalar optimization, and
subnormalized smoothing bridges are discharged here. -/
theorem tensorPowerFiniteAEP_core_posDef_optimized_subnormalizedSmooth_of_uniformJointConvex_all_additivePetz
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (hρB : ρ.traceLeft.m.PosDef)
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
        (Aκ Bκ : κ → CMatrix (TensorPower a n × TensorPower b n)) →
          cMatrixPetzTraceUniformJointConvex Aκ Bκ α) :
    ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_pos.le hε_lt ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB) *
          Real.sqrt (n : ℝ) := by
  refine
    ρ.tensorPowerFiniteAEP_core_posDef_optimized_subnormalizedSmooth_of_unitaryDephaseMonotone_additivePetz
      hρ hρB ε α hM hn hα_opt hε_pos hε_lt hα_le_two hα_lt ?_
  dsimp
  let hρn : (ρ.tensorPowerBipartite n).m.PosDef :=
    tensorPowerBipartite_posDef ρ hρ n
  let hρnB : (ρ.tensorPowerBipartite n).traceLeft.m.PosDef :=
    tensorPowerBipartite_traceLeft_posDef ρ hρB n
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
      hρn (ρ.tensorPowerBipartite n).traceLeft hρnB ε α hα_pos hα_ne_one
  let hB : (identityTensorStateMatrix (a := TensorPower a n)
      (ρ.tensorPowerBipartite n).traceLeft).PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := TensorPower a n)
      (ρ.tensorPowerBipartite n).traceLeft hρnB
  let Hmat : CMatrix (TensorPower a n × TensorPower b n) :=
    (ρ.tensorPowerBipartite n).m -
      lam • identityTensorStateMatrix (a := TensorPower a n)
        (ρ.tensorPowerBipartite n).traceLeft
  let hH : Hmat.IsHermitian :=
    hρn.isHermitian.sub ((Matrix.PosDef.smul hB
      ((ρ.tensorPowerBipartite n).petzSmoothMinThresholdScale_pos
        hρn (ρ.tensorPowerBipartite n).traceLeft hρnB ε α hα_pos hα_ne_one)
    ).isHermitian)
  let U : Matrix.unitaryGroup (TensorPower a n × TensorPower b n) ℂ :=
    hH.eigenvectorUnitary
  exact cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex_all
    (ρ.tensorPowerBipartite n).m
    (identityTensorStateMatrix (a := TensorPower a n)
      (ρ.tensorPowerBipartite n).traceLeft)
    hρn.posSemidef hB U hα_gt hα_le_two hjoint

/-- Tensor-power optimized finite-AEP core with the Petz joint-convexity input
discharged by the finite-dimensional rpow perspective theorem. -/
theorem tensorPowerFiniteAEP_core_posDef_optimized_subnormalizedSmooth_of_rpow_perspective_additivePetz
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (hρB : ρ.traceLeft.m.PosDef)
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
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (hρB : ρ.traceLeft.m.PosDef)
    (ε : ℝ) (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1) (n : ℕ)
    (hjoint :
      ∀ {κ : Type (max u v)} [Fintype κ] [Nonempty κ],
        (Aκ Bκ : κ → CMatrix (TensorPower a n × TensorPower b n)) →
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
          (Aκ Bκ : κ → CMatrix (TensorPower a n × TensorPower b n)) →
            cMatrixPetzTraceUniformJointConvex Aκ Bκ α := by
      intro κ _ _ Aκ Bκ
      simpa [α] using hjoint (κ := κ) Aκ Bκ
    ρ.tensorPowerFiniteAEP_core_posDef_optimized_subnormalizedSmooth_of_uniformJointConvex_all_additivePetz
      hρ hρB ε α hM hn hα_opt hε_pos hε_lt hα_le_two hα_lt hjointAlpha
  simpa [MState.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_eq] using
    finiteAEP_normalized_rate_of_tensor_lower_bound
      (S := ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_pos.le hε_lt)
      (H := ρ.conditionalEntropy)
      (δ := QIT.finiteAEPDelta ε (ρ.finiteAEPEta hρ hρB))
      (n := n) hn hcore

/-- Finite-N AEP statement using only the full-rank marginal reference and the
trace-term eta parameter. -/
theorem finiteNAEP_statement_traceEta_of_marginal_posDef
    (ρ : MState (a × b))
    (hρB : ρ.traceLeft.m.PosDef)
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
        (ρ := ρ) (σ := ρ.traceLeft) hρB
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
  simpa [MState.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_eq] using
    finiteAEP_normalized_rate_of_tensor_lower_bound
      (S := ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropy ε n hε_pos.le hε_lt)
      (H := ρ.conditionalEntropy)
      (δ := QIT.finiteAEPDelta ε ρ.finiteAEPEtaTrace)
      (n := n) hn hcore

/-- Tensor-power subnormalized smooth min-entropy is unchanged by compressing
the conditioning register to the support of the canonical marginal and applying
the tensor-power support isometry back, with the same smoothing radius. -/
theorem tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_conditioningSupportCompressedState
    (ρ : MState (a × b)) (ε : ℝ) (hε0 : 0 ≤ ε) (hε_lt : ε < 1) (n : ℕ) :
    ρ.conditioningSupportCompressedState.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw ε n =
      ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw ε n := by
  let ρc := ρ.conditioningSupportCompressedState
  let V : ReferenceIsometry (psdSupportIndex ρ.traceLeft.m ρ.traceLeft.psd) b :=
    psdSupportReferenceIsometry ρ.traceLeft.m ρ.traceLeft.psd
  have : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  have : Nonempty b := ⟨(Classical.choice ρ.nonempty).2⟩
  have : Nonempty (psdSupportIndex ρ.traceLeft.m ρ.traceLeft.psd) :=
    ⟨(Classical.choice ρc.nonempty).2⟩
  have : Nonempty (TensorPower a n) := tensorPower_nonempty_of_nonempty n
  have : Nonempty (TensorPower b n) := tensorPower_nonempty_of_nonempty n
  have :
      Nonempty (TensorPower (psdSupportIndex ρ.traceLeft.m ρ.traceLeft.psd) n) :=
    tensorPower_nonempty_of_nonempty n
  have hε_sqrt :
      ε < Real.sqrt ((ρc.tensorPowerBipartite n).toSubnormalized.matrix.trace.re) := by
    rw [MState.toSubnormalized_trace]
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
            rw [MState.conditioningIsometryApply_tensorPowerBipartite]
      _ = ρ.tensorPowerBipartite n := by
            rw [show ρc.conditioningIsometryApply V = ρ from by
              simp [ρc, V]]
  have hsubState :
      (ρc.tensorPowerBipartite n).toSubnormalized.conditioningIsometryApply
          (V.tensorPower n) =
        (ρ.tensorPowerBipartite n).toSubnormalized := by
    rw [← MState.toSubnormalized_conditioningIsometryApply]
    rw [htensorState]
  rw [MState.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_eq,
    MState.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_eq]
  rw [← hsubState]
  exact hsmooth.symm

/-- Canonical finite-domain support-compression invariance for the tensor-power
smooth conditional min-entropy. -/
theorem tensorPowerSubnormalizedSmoothConditionalMinEntropy_conditioningSupportCompressedState
    (ρ : MState (a × b)) (ε : ℝ) (hε0 : 0 ≤ ε) (hε_lt : ε < 1) (n : ℕ) :
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
    (ρ : MState (a × b)) (ε : ℝ) (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1) (n : ℕ) :
    QIT.finiteNAEP_statement ρ ε ρ.finiteAEPEtaTrace n hε_nonneg hε_lt := by
  let ρc := ρ.conditioningSupportCompressedState
  have hcompressed :
      QIT.finiteNAEP_statement ρc ε ρc.finiteAEPEtaTrace n hε_nonneg hε_lt :=
    finiteNAEP_statement_traceEta_of_marginal_posDef
      (ρ := ρc) (MState.conditioningSupportCompressedState_traceLeft_posDef ρ)
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
  rw [← MState.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_conditioningSupportCompressedState
    ρ ε hε0 hε_lt n]
  rw [← MState.conditionalEntropy_conditioningSupportCompressedState ρ]
  rw [← MState.finiteAEPEtaTrace_conditioningSupportCompressedState ρ]
  exact hbound

/-- The finite-N AEP theorem supplies the lower half of the source proof of
the asymptotic fully quantum AEP.

This is the Lean version of the first step in TCR 2008, proof of
`thm:qaep`: after the final tolerance is fixed, for all sufficiently small
positive smoothing radii and sufficiently large blocklengths, the normalized
smooth-min rate is at least `H(A|B)_ρ` up to that tolerance. -/
theorem SmoothMinRateLowerFromFiniteNAEP_traceEta
    (ρ : MState (a × b)) :
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
    (ρ : MState (a × b)) :
    ρ.SmoothMinRateUpperFromContinuity :=
  MState.SmoothMinRateUpperFromContinuity.afw_of_tensorPower_ordering ρ
    (by
      intro n τ
      exact τ.conditionalMinEntropy_le_conditionalEntropy)

/-- Source-aligned min-entropy half of the asymptotic AEP, with the finite-N
lower bound discharged by the finite-AEP theorem and the AFW/Fannes upper
handoff left explicit. -/
theorem asymptoticAEPMin_statement_of_traceEta_and_continuity
    (ρ : MState (a × b))
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
    (ρ : MState (a × b)) :
    ρ.SmoothMaxRateFromMinDuality := by
  refine MState.SmoothMaxRateFromMinDuality.of_all_min ρ ?_
  intro c _ _ _ σ
  exact σ.asymptoticAEPMin_statement_of_traceEta_and_continuity
    (MState.SmoothMinRateUpperFromContinuity.afw σ)

/-- Source-aligned assembly theorem for the asymptotic fully quantum AEP.

The finite-N lower half is supplied by the finite-AEP theorem.  The remaining
two inputs are exactly the source proof's later ingredients: ordering plus
AFW/Fannes continuity for the min upper half, and smooth min/max plus von
Neumann duality for the max half. -/
theorem asymptoticAEPTwoStage_statement_of_traceEta_continuity_and_duality
    (ρ : MState (a × b))
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
    (ρ : MState (a × b)) :
    QIT.asymptoticAEPTwoStage_statement ρ := by
  let : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  let : Nonempty b := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  exact ρ.asymptoticAEPTwoStage_statement_of_traceEta_continuity_and_duality
    (MState.SmoothMinRateUpperFromContinuity.afw ρ)
    (MState.SmoothMaxRateFromMinDuality.smoothDuality ρ)

/-- Positive-definite finite-N AEP statement with Petz joint convexity
discharged by the finite-dimensional rpow perspective theorem. -/
theorem finiteNAEP_statement_posDef_of_rpow_perspective_one_two
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (hρB : ρ.traceLeft.m.PosDef)
    (ε : ℝ) (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1) (n : ℕ) :
    QIT.finiteNAEP_statement ρ ε (ρ.finiteAEPEta hρ hρB) n hε_nonneg hε_lt :=
  ρ.finiteNAEP_statement_posDef_of_uniformJointConvex_all
    hρ hρB ε hε_nonneg hε_lt n
    (fun {κ} [Fintype κ] [Nonempty κ]
        (Aκ Bκ : κ → CMatrix (TensorPower a n × TensorPower b n)) =>
      cMatrixPetzTraceUniformJointConvex_of_rpow_perspective_one_two Aκ Bκ)

/-- Explicit-`η` spelling of the positive-definite finite-N AEP theorem.

This keeps the public statement parameter separate from the current
positive-definite implementation of the source convergence parameter. -/
theorem finiteNAEP_statement_posDef_explicitEta_of_rpow_perspective_one_two
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (hρB : ρ.traceLeft.m.PosDef)
    (η ε : ℝ) (hη : η = ρ.finiteAEPEta hρ hρB)
    (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1) (n : ℕ) :
    QIT.finiteNAEP_statement ρ ε η n hε_nonneg hε_lt := by
  subst η
  exact ρ.finiteNAEP_statement_posDef_of_rpow_perspective_one_two
    hρ hρB ε hε_nonneg hε_lt n

/-- Positive-definite finite-N AEP using the arbitrary-state trace-term eta
spelling of `Upsilon(A|B)_{rho|rho}`. -/
theorem finiteNAEP_statement_posDef_traceEta_of_rpow_perspective_one_two
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (hρB : ρ.traceLeft.m.PosDef)
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
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (hρB : ρ.traceLeft.m.PosDef)
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
      let hρn : (ρ.tensorPowerBipartite n).m.PosDef :=
        tensorPowerBipartite_posDef ρ hρ n
      let hρnB : (ρ.tensorPowerBipartite n).traceLeft.m.PosDef :=
        tensorPowerBipartite_traceLeft_posDef ρ hρB n
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
          hρn (ρ.tensorPowerBipartite n).traceLeft hρnB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational (ρ.tensorPowerBipartite n).m
        (identityTensorStateMatrix (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).traceLeft) lam α) :
    (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
        (ρ.tensorPowerBipartite n).traceLeft.toSubnormalized ε ≥
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
          (tensorPowerBipartite_posDef ρ hρ n)
          (ρ.tensorPowerBipartite n).traceLeft
          (tensorPowerBipartite_traceLeft_posDef ρ hρB n)
          α (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        (n : ℝ) * ρ.conditionalEntropy -
          4 * (α - 1) * (n : ℝ) *
            (log2 (ρ.finiteAEPEta hρ hρB)) ^ 2 :=
    ρ.tensorPower_conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef
      hρ hρB α hα_gt hα_lt
  exact
    (ρ.tensorPowerBipartite n).finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational_petzAlphaBound
      (tensorPowerBipartite_posDef ρ hρ n)
      (tensorPowerBipartite_traceLeft_posDef ρ hρB n)
      ε (ρ.finiteAEPEta hρ hρB) α ρ.conditionalEntropy hM hL hn hα_opt
      hε_pos hε_lt hα_le_two hpetz_alpha hvar

/-- Tensor-power instantiation of the optimized positive-definite finite-AEP
core.

This theorem discharges the tensor-power positive-definiteness bookkeeping for
`ρ_AB^{⊗ n}`, its `B^n` marginal, and conditional entropy additivity.  The eta
growth, alpha-window, and Petz effect-variational inputs remain explicit. -/
theorem tensorPowerFiniteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (hρB : ρ.traceLeft.m.PosDef)
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
          (tensorPowerBipartite_posDef ρ hρ n)
          (tensorPowerBipartite_traceLeft_posDef ρ hρB n))))
    (heta_tensor :
      (log2 ((ρ.tensorPowerBipartite n).finiteAEPEta
        (tensorPowerBipartite_posDef ρ hρ n)
        (tensorPowerBipartite_traceLeft_posDef ρ hρB n))) ^ 2 ≤
          (n : ℝ) * (log2 η) ^ 2)
    (hvar :
      let hρn : (ρ.tensorPowerBipartite n).m.PosDef :=
        tensorPowerBipartite_posDef ρ hρ n
      let hρnB : (ρ.tensorPowerBipartite n).traceLeft.m.PosDef :=
        tensorPowerBipartite_traceLeft_posDef ρ hρB n
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
          hρn (ρ.tensorPowerBipartite n).traceLeft hρnB ε α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm)
      cMatrixPetzTraceEffectVariational (ρ.tensorPowerBipartite n).m
        (identityTensorStateMatrix (a := TensorPower a n)
          (ρ.tensorPowerBipartite n).traceLeft) lam α) :
    (ρ.tensorPowerBipartite n).smoothConditionalMinEntropyFixedSubnormalized
        (ρ.tensorPowerBipartite n).traceLeft.toSubnormalized ε ≥
      (n : ℝ) * ρ.conditionalEntropy -
        QIT.finiteAEPDelta ε η * Real.sqrt (n : ℝ) := by
  exact
    (ρ.tensorPowerBipartite n).finiteAEP_core_posDef_optimized_of_fixedPetzSmoothMinG_effectVariational
      (tensorPowerBipartite_posDef ρ hρ n)
      (tensorPowerBipartite_traceLeft_posDef ρ hρB n)
      ε η α ρ.conditionalEntropy hM hL hn hα_opt hε_pos hε_lt hα_le_two hα_lt
      (MState.tensorPowerBipartite_conditionalEntropy ρ n) heta_tensor hvar

/-- Positive-definite fixed-reference finite-AEP core.

This combines the TCR alpha-to-von-Neumann estimate already proved in
`conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef` with an explicit
one-shot smooth-min/Petz lower-bound hypothesis.  That hypothesis is precisely
the fixed-reference analogue of TCR 2008 `thm:entropy-ineq`, lines 630--633;
it enters here as a hypothesis, not as a result. -/
theorem relativeFiniteAEP_core_posDef_of_smoothMinPetzBound
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (σ : MState b) (hσ : σ.m.PosDef)
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
    (ρ : MState (a × b)) (hρ : ρ.m.PosDef)
    (σ : MState b) (hσ : σ.m.PosDef)
    (ε α : ℝ)
    (hε_pos : 0 < ε)
    (hε_lt : ε < 1)
    (hα_gt : 1 < α) (hα_le_two : α ≤ 2)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)))
    (hconstruct :
      ∃ ρ' : MState (a × b), ρ.purifiedBall ε ρ' ∧
        ρ'.m ≤
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

end MState
