/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.RenyiDPI.Domain
public import QIT.Information.Entropy.Log2Lemmas

/-!
# High-alpha sandwiched Renyi DPI support

Beigi/rotated-Kraus high-alpha route, endpoint support, and `one_lt` channel
DPI reductions.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

namespace State

open RenyiDPI.Statement

/-- The single-outcome POVM with effect `1`, used as the terminal/discard
measurement channel in finite dimension. -/
def terminalPOVM (a : Type u) [Fintype a] [DecidableEq a] : POVM PUnit.{1} a where
  effects _ := 1
  pos _ := Matrix.PosSemidef.one
  sum_eq_one := by
    ext i j
    simp

/-- The terminal measurement channel associated with `terminalPOVM`. -/
def terminalMeasureChannel (a : Type u) [Fintype a] [DecidableEq a] : Channel a PUnit.{1} :=
  Channel.measure (terminalPOVM a)

/-- Measuring with the terminal one-outcome POVM maps every normalized state to
the unique unit-system state. -/
theorem terminalMeasureChannel_applyState (ρ : State a) :
    (terminalMeasureChannel a).applyState ρ = State.unit := by
  apply State.ext
  ext i j
  cases i
  cases j
  simp [terminalMeasureChannel, terminalPOVM, Channel.applyState, Channel.measure,
    Channel.measureMap, State.unit, ρ.trace_eq_one]

/-- Stinespring lift of a state through a trace-preserving Kraus family.

For a Kraus realization `K : a → b` and its trace-preserving proof, this is the
state on `B × κ` obtained by applying the Stinespring isometry and retaining
the environment register. The lifted state is generally not full-rank when the
environment is nontrivial; this is why the strict low-`α` route still needs a
regularized/support-aware partial-trace theorem rather than the current
`State + PosDef` API alone. -/
def stinespringLiftState {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) : State (Prod b κ) where
  matrix :=
    (MatrixMap.krausStinespringIsometry K hTP).matrix * ρ.matrix *
      Matrix.conjTranspose (MatrixMap.krausStinespringIsometry K hTP).matrix
  pos := by
    exact ρ.pos.mul_mul_conjTranspose_same
      (MatrixMap.krausStinespringIsometry K hTP).matrix
  trace_eq_one := by
    have hpt :=
      MatrixMap.partialTraceB_krausStinespringIsometry K hTP ρ.matrix
    have htrace := congrArg Matrix.trace hpt
    rw [partialTraceB_trace] at htrace
    rw [htrace, hTP ρ.matrix, ρ.trace_eq_one]

/-- The output marginal of the Stinespring lift is the Kraus-map output. -/
theorem stinespringLiftState_marginalA_matrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) :
    ((stinespringLiftState K hTP ρ).marginalA).matrix =
      MatrixMap.ofKraus K ρ.matrix := by
  simpa [stinespringLiftState, State.marginalA] using
    MatrixMap.partialTraceB_krausStinespringIsometry K hTP ρ.matrix

/-- The output marginal of the Stinespring lift is the corresponding channel
output whenever the channel is represented by the same Kraus family. -/
theorem stinespringLiftState_marginalA_eq_applyState {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ) (Φ : Channel a b)
    (hK : Φ.map = MatrixMap.ofKraus K)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) :
    (stinespringLiftState K hTP ρ).marginalA = Φ.applyState ρ := by
  apply State.ext
  rw [stinespringLiftState_marginalA_matrix K hTP ρ]
  simp [Channel.applyState, hK]

/-- Full-support classical stochastic maps satisfy sandwiched Renyi DPI for
diagonal states in the `α > 1` range.

This is a non-circular commuting endpoint for the pinching proof route: the
proof reduces both diagonal sandwiched Renyi divergences to classical power sums
and applies the scalar log-sum/Jensen inequality for a stochastic kernel. -/
theorem sandwichedRenyi_diagonalState_stochastic_le_of_one_lt
    (p q : a → ℝ≥0) (pOut qOut : b → ℝ≥0) (T : a → b → ℝ)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hp_pos : ∀ i, 0 < (p i : ℝ)) (hq_pos : ∀ i, 0 < (q i : ℝ))
    (hpOut_sum : ∑ y, pOut y = 1) (hqOut_sum : ∑ y, qOut y = 1)
    (hpOut_pos : ∀ y, 0 < (pOut y : ℝ)) (hqOut_pos : ∀ y, 0 < (qOut y : ℝ))
    (hT_nonneg : ∀ i y, 0 ≤ T i y)
    (hT_sum : ∀ i, ∑ y, T i y = 1)
    (hpOut_eq : ∀ y, (pOut y : ℝ) = ∑ i, (p i : ℝ) * T i y)
    (hqOut_eq : ∀ y, (qOut y : ℝ) = ∑ i, (q i : ℝ) * T i y)
    (α : ℝ) (hα_gt_one : 1 < α) :
    sandwichedRenyi (Classical.diagonalState pOut hpOut_sum)
        (Classical.diagonalState qOut hqOut_sum)
        (Classical.diagonalState_posDef pOut hpOut_sum hpOut_pos)
        (Classical.diagonalState_posDef qOut hqOut_sum hqOut_pos)
        α (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one) ≤
      sandwichedRenyi (Classical.diagonalState p hp_sum) (Classical.diagonalState q hq_sum)
        (Classical.diagonalState_posDef p hp_sum hp_pos)
        (Classical.diagonalState_posDef q hq_sum hq_pos)
        α (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one) := by
  classical
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_gt_one
  have hα_ne_one : α ≠ 1 := ne_of_gt hα_gt_one
  have hpower_raw :
      (∑ y, (∑ i, (p i : ℝ) * T i y) ^ α *
          (∑ i, (q i : ℝ) * T i y) ^ (1 - α)) ≤
        ∑ i, (p i : ℝ) ^ α * (q i : ℝ) ^ (1 - α) :=
    real_classical_renyi_stochastic_power_sum_le
      (ι := a) (ο := b) (p := fun i => (p i : ℝ))
      (q := fun i => (q i : ℝ)) (T := T) (α := α)
      (le_of_lt hα_gt_one)
      (fun i => NNReal.coe_nonneg (p i)) hq_pos hT_nonneg hT_sum
      (fun y => by
        rw [← hqOut_eq y]
        exact hqOut_pos y)
  have hpower :
      (∑ y, (pOut y : ℝ) ^ α * (qOut y : ℝ) ^ (1 - α)) ≤
        ∑ i, (p i : ℝ) ^ α * (q i : ℝ) ^ (1 - α) := by
    calc
      (∑ y, (pOut y : ℝ) ^ α * (qOut y : ℝ) ^ (1 - α)) =
          ∑ y, (∑ i, (p i : ℝ) * T i y) ^ α *
            (∑ i, (q i : ℝ) * T i y) ^ (1 - α) := by
            apply Finset.sum_congr rfl
            intro y _
            rw [hpOut_eq y, hqOut_eq y]
      _ ≤ ∑ i, (p i : ℝ) ^ α * (q i : ℝ) ^ (1 - α) := hpower_raw
  have hout_pos :
      0 < ∑ y, ((pOut y : ℝ) ^ α) * ((qOut y : ℝ) ^ (1 - α)) :=
    nnreal_classical_renyi_power_sum_pos pOut qOut hpOut_sum
      hpOut_pos hqOut_pos α
  have hlog := log2_mono_of_pos hout_pos hpower
  have hcoef_nonneg : 0 ≤ 1 / (α - 1) := by
    exact le_of_lt (one_div_pos.2 (sub_pos.mpr hα_gt_one))
  rw [sandwichedRenyi_diagonalState_eq_classicalPowerSum pOut qOut
      hpOut_sum hqOut_sum hpOut_pos hqOut_pos α hα_pos hα_ne_one,
    sandwichedRenyi_diagonalState_eq_classicalPowerSum p q
      hp_sum hq_sum hp_pos hq_pos α hα_pos hα_ne_one]
  exact mul_le_mul_of_nonneg_left hlog hcoef_nonneg

/-- Full-support classical stochastic maps satisfy sandwiched Renyi DPI for
diagonal states in the `0 < α < 1` range.

The classical power sum moves in the reverse direction in this range; the
negative logarithmic prefactor reverses it back to the DPI inequality. -/
theorem sandwichedRenyi_diagonalState_stochastic_le_of_lt_one
    (p q : a → ℝ≥0) (pOut qOut : b → ℝ≥0) (T : a → b → ℝ)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hp_pos : ∀ i, 0 < (p i : ℝ)) (hq_pos : ∀ i, 0 < (q i : ℝ))
    (hpOut_sum : ∑ y, pOut y = 1) (hqOut_sum : ∑ y, qOut y = 1)
    (hpOut_pos : ∀ y, 0 < (pOut y : ℝ)) (hqOut_pos : ∀ y, 0 < (qOut y : ℝ))
    (hT_nonneg : ∀ i y, 0 ≤ T i y)
    (hT_sum : ∀ i, ∑ y, T i y = 1)
    (hpOut_eq : ∀ y, (pOut y : ℝ) = ∑ i, (p i : ℝ) * T i y)
    (hqOut_eq : ∀ y, (qOut y : ℝ) = ∑ i, (q i : ℝ) * T i y)
    (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    sandwichedRenyi (Classical.diagonalState pOut hpOut_sum)
        (Classical.diagonalState qOut hqOut_sum)
        (Classical.diagonalState_posDef pOut hpOut_sum hpOut_pos)
        (Classical.diagonalState_posDef qOut hqOut_sum hqOut_pos)
        α hα_pos (ne_of_lt hα_lt_one) ≤
      sandwichedRenyi (Classical.diagonalState p hp_sum) (Classical.diagonalState q hq_sum)
        (Classical.diagonalState_posDef p hp_sum hp_pos)
        (Classical.diagonalState_posDef q hq_sum hq_pos)
        α hα_pos (ne_of_lt hα_lt_one) := by
  classical
  have hα_ne_one : α ≠ 1 := ne_of_lt hα_lt_one
  have hpower_raw :
      (∑ i, (p i : ℝ) ^ α * (q i : ℝ) ^ (1 - α)) ≤
        ∑ y, (∑ i, (p i : ℝ) * T i y) ^ α *
          (∑ i, (q i : ℝ) * T i y) ^ (1 - α) :=
    real_classical_renyi_stochastic_power_sum_ge
      (ι := a) (ο := b) (p := fun i => (p i : ℝ))
      (q := fun i => (q i : ℝ)) (T := T) (α := α)
      (le_of_lt hα_pos) (le_of_lt hα_lt_one)
      (fun i => NNReal.coe_nonneg (p i)) hq_pos hT_nonneg hT_sum
      (fun y => by
        rw [← hqOut_eq y]
        exact hqOut_pos y)
  have hpower :
      (∑ i, (p i : ℝ) ^ α * (q i : ℝ) ^ (1 - α)) ≤
        ∑ y, (pOut y : ℝ) ^ α * (qOut y : ℝ) ^ (1 - α) := by
    calc
      (∑ i, (p i : ℝ) ^ α * (q i : ℝ) ^ (1 - α))
          ≤ ∑ y, (∑ i, (p i : ℝ) * T i y) ^ α *
              (∑ i, (q i : ℝ) * T i y) ^ (1 - α) := hpower_raw
      _ = ∑ y, (pOut y : ℝ) ^ α * (qOut y : ℝ) ^ (1 - α) := by
            apply Finset.sum_congr rfl
            intro y _
            rw [hpOut_eq y, hqOut_eq y]
  have hin_pos :
      0 < ∑ i, ((p i : ℝ) ^ α) * ((q i : ℝ) ^ (1 - α)) :=
    nnreal_classical_renyi_power_sum_pos p q hp_sum hp_pos hq_pos α
  have hlog := log2_mono_of_pos hin_pos hpower
  have hcoef_nonpos : 1 / (α - 1) ≤ 0 := by
    have hcoef_neg : 1 / (α - 1) < 0 := by
      simpa [one_div] using (inv_lt_zero.2 (sub_neg.mpr hα_lt_one))
    exact le_of_lt hcoef_neg
  rw [sandwichedRenyi_diagonalState_eq_classicalPowerSum pOut qOut
      hpOut_sum hqOut_sum hpOut_pos hqOut_pos α hα_pos hα_ne_one,
    sandwichedRenyi_diagonalState_eq_classicalPowerSum p q
      hp_sum hq_sum hp_pos hq_pos α hα_pos hα_ne_one]
  exact mul_le_mul_of_nonpos_left hlog hcoef_nonpos

/-- Output-side Holder dual effect for the sandwiched Renyi variational route:
`σ^((1-α)/(2α)) B σ^((1-α)/(2α))`. -/
def sandwichedRenyiHolderDualEffect (σ : State a) (B : CMatrix a) (α : ℝ) :
    CMatrix a :=
  let s := (1 - α) / (2 * α)
  let C := CFC.rpow σ.matrix s
  C * B * C

/-- The Holder dual effect remains positive semidefinite when the unit-ball
witness is positive semidefinite. -/
theorem sandwichedRenyiHolderDualEffect_posSemidef
    (σ : State a) {B : CMatrix a} (hB : B.PosSemidef) (α : ℝ) :
    (sandwichedRenyiHolderDualEffect σ B α).PosSemidef := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ.matrix s
  have hC : C.PosSemidef := by
    simpa [C] using σ.rpowMatrix_posSemidef s
  have hCstar : star C = C := hC.isHermitian.eq
  have hdual : (star C * B * C).PosSemidef :=
    Matrix.PosSemidef.conjTranspose_mul_mul_same hB C
  rw [hCstar] at hdual
  simpa [sandwichedRenyiHolderDualEffect, s, C] using hdual

/-- The core trace-duality identity for the `α > 1` Holder route.

For a Kraus representation of the channel, pairing the output sandwiched inner
operator with a Holder unit-ball witness is exactly the input state paired with
the Kraus-adjoint pullback of the corresponding Holder dual effect. This is the
first nontrivial channel-specific step before proving the remaining q-unit-ball
contraction. -/
theorem sandwichedRenyi_inner_trace_eq_krausAdjoint_holderDualEffect
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (ρ σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (B : CMatrix b) (α : ℝ) :
    ((sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α * B).trace).re =
      (ρ.matrix *
        MatrixMap.krausAdjoint K
          (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)).trace.re := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix b := CFC.rpow (Φ.applyState σ).matrix s
  let X : CMatrix b := (Φ.applyState ρ).matrix
  have hcycle :
      ((sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α * B).trace) =
        (X * sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α).trace := by
    change (((C * X * C) * B).trace) = (X * (C * B * C)).trace
    calc
      ((C * X * C) * B).trace = ((C * X) * (C * B)).trace := by
        congr 1
        noncomm_ring
      _ = (((C * B) * C) * X).trace := by
        exact Matrix.trace_mul_cycle C X (C * B)
      _ = (X * (C * B * C)).trace := by
        rw [Matrix.trace_mul_comm]
  have hdual :
      (X * sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α).trace =
        (ρ.matrix *
          MatrixMap.krausAdjoint K
            (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)).trace := by
    change ((Φ.map ρ.matrix) *
        sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α).trace =
      (ρ.matrix *
        MatrixMap.krausAdjoint K
          (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)).trace
    rw [hK]
    exact MatrixMap.ofKraus_trace_duality K ρ.matrix
      (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)
  exact congrArg Complex.re (hcycle.trans hdual)

/-- The Kraus-adjoint pullback of the output Holder dual effect is positive
semidefinite. This is the positivity half of the witness transport used by the
Holder/variational proof route. -/
theorem sandwichedRenyi_krausAdjoint_holderDualEffect_posSemidef
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) {B : CMatrix b} (hB : B.PosSemidef)
    (α : ℝ) :
    (MatrixMap.krausAdjoint K
      (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)).PosSemidef := by
  exact MatrixMap.krausAdjoint_mapsPositive K
    (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)
    (sandwichedRenyiHolderDualEffect_posSemidef (Φ.applyState σ) hB α)

/-- Kadison's inequality for the pulled-back output Holder dual effect.

This is the channel-specific square inequality needed before attempting the
weighted `q`-unit-ball estimate in the α > 1 variational route. -/
theorem sandwichedRenyi_krausAdjoint_holderDualEffect_square_le
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (σ : State a) (Φ : Channel a b) {B : CMatrix b} (hB : B.PosSemidef)
    (α : ℝ) :
    MatrixMap.krausAdjoint K (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α) *
        MatrixMap.krausAdjoint K (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α) ≤
      MatrixMap.krausAdjoint K
        (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α *
          sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α) := by
  exact MatrixMap.krausAdjoint_posSemidef_mul_self_le_of_tracePreserving K hTP
    (sandwichedRenyiHolderDualEffect_posSemidef (Φ.applyState σ) hB α)

private theorem state_matrix_le_one_local (τ : State a) :
    τ.matrix ≤ 1 := by
  classical
  rw [Matrix.le_iff]
  let U : Matrix.unitaryGroup a ℂ := τ.pos.1.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => ((τ.pos.1.eigenvalues i : ℝ) : ℂ)
  have hdiag : τ.matrix = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using τ.pos.1.spectral_theorem
  have heig_sum : ∑ i, τ.pos.1.eigenvalues i = 1 := by
    have hc : (∑ i, ((τ.pos.1.eigenvalues i : ℝ) : ℂ)) = 1 := by
      exact τ.pos.1.trace_eq_sum_eigenvalues.symm.trans τ.trace_eq_one
    exact Complex.ofReal_injective (by simpa using hc)
  have heig_le_one : ∀ i, τ.pos.1.eigenvalues i ≤ 1 := by
    intro i
    have hnonneg (j : a) : 0 ≤ τ.pos.1.eigenvalues j :=
      τ.pos.eigenvalues_nonneg j
    calc
      τ.pos.1.eigenvalues i
          ≤ τ.pos.1.eigenvalues i +
              ∑ j ∈ Finset.univ.erase i, τ.pos.1.eigenvalues j :=
            le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hnonneg j)
      _ = ∑ j, τ.pos.1.eigenvalues j := by
            rw [add_comm]
            exact Finset.sum_erase_add (s := Finset.univ)
              (f := fun j => τ.pos.1.eigenvalues j) (Finset.mem_univ i)
      _ = 1 := heig_sum
  have hsub :
      1 - τ.matrix = (U : CMatrix a) * (1 - D) * star (U : CMatrix a) := by
    rw [hdiag]
    have hUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
      simp
    calc
      1 - (U : CMatrix a) * D * star (U : CMatrix a) =
          (U : CMatrix a) * 1 * star (U : CMatrix a) -
            (U : CMatrix a) * D * star (U : CMatrix a) := by
            rw [Matrix.mul_one, hUstar]
      _ = (U : CMatrix a) * (1 - D) * star (U : CMatrix a) := by
            noncomm_ring
  have hdiag_sub :
      (1 : CMatrix a) - D =
        Matrix.diagonal fun i => (((1 : ℝ) - τ.pos.1.eigenvalues i : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D]
    · simp [D, Matrix.diagonal, hij]
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (U : CMatrix a))]
  rw [hdiag_sub]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  have hnonneg : 0 ≤ (1 : ℝ) - τ.pos.1.eigenvalues i := by
    exact sub_nonneg.mpr (heig_le_one i)
  exact_mod_cast hnonneg

private theorem state_trace_mul_le_trace_of_posSemidef
    (τ : State a) {X : CMatrix a} (hX : X.PosSemidef) :
    ((τ.matrix * X).trace).re ≤ X.trace.re := by
  have htrace :=
    cMatrix_trace_mul_le_of_le_posSemidef_left
      (W := X) (A := τ.matrix) (B := 1) hX
      (state_matrix_le_one_local τ)
  rw [Matrix.trace_mul_comm X τ.matrix, Matrix.mul_one] at htrace
  exact htrace

private theorem cMatrix_trace_sandwich_sq_le_weighted_sq
    {S A : CMatrix a} (hS : S.PosSemidef) (hA : A.IsHermitian) :
    ((A * S * A * S).trace).re ≤ ((S * S * (A * A)).trace).re := by
  classical
  letI : NormedAddCommGroup (CMatrix a) :=
    Matrix.toMatrixNormedAddCommGroup (1 : CMatrix a) Matrix.PosDef.one
  letI : InnerProductSpace ℂ (CMatrix a) :=
    Matrix.toMatrixInnerProductSpace (1 : CMatrix a) Matrix.PosSemidef.one
  let x : CMatrix a := A * S
  let y : CMatrix a := S * A
  let R : ℝ := ((S * S * (A * A)).trace).re
  have hinner : inner ℂ x y = (A * S * A * S).trace := by
    dsimp [x, y]
    change ((S * A) * (1 : CMatrix a) * Matrix.conjTranspose (A * S)).trace =
      (A * S * A * S).trace
    rw [Matrix.conjTranspose_mul, hS.isHermitian.eq, hA.eq]
    calc
      ((S * A) * (1 : CMatrix a) * (S * A)).trace =
          (S * A * S * A).trace := by
            simp [Matrix.mul_assoc]
      _ = (A * S * A * S).trace := by
            calc
              (S * A * S * A).trace = ((S * A * S) * A).trace := by
                rw [Matrix.mul_assoc]
              _ = (A * (S * A * S)).trace := by
                rw [Matrix.trace_mul_comm]
              _ = (A * S * A * S).trace := by
                noncomm_ring
  have hxnorm : ‖x‖ ^ 2 = R := by
    rw [@norm_sq_eq_re_inner ℂ (CMatrix a) _ _ _ x]
    dsimp [x, R]
    change (((A * S) * (1 : CMatrix a) * Matrix.conjTranspose (A * S)).trace).re =
      ((S * S * (A * A)).trace).re
    rw [Matrix.conjTranspose_mul, hS.isHermitian.eq, hA.eq]
    congr 1
    calc
      ((A * S) * (1 : CMatrix a) * (S * A)).trace =
          (A * (S * S) * A).trace := by
            noncomm_ring
      _ = (A * A * (S * S)).trace := by
            exact Matrix.trace_mul_cycle A (S * S) A
      _ = ((S * S) * (A * A)).trace := by
            rw [Matrix.trace_mul_comm]
      _ = (S * S * (A * A)).trace := by
            rw [Matrix.mul_assoc]
  have hynorm : ‖y‖ ^ 2 = R := by
    rw [@norm_sq_eq_re_inner ℂ (CMatrix a) _ _ _ y]
    dsimp [y, R]
    change (((S * A) * (1 : CMatrix a) * Matrix.conjTranspose (S * A)).trace).re =
      ((S * S * (A * A)).trace).re
    rw [Matrix.conjTranspose_mul, hA.eq, hS.isHermitian.eq]
    congr 1
    calc
      ((S * A) * (1 : CMatrix a) * (A * S)).trace =
          (S * (A * A) * S).trace := by
            noncomm_ring
      _ = (S * S * (A * A)).trace := by
            exact Matrix.trace_mul_cycle S (A * A) S
  have hcs := norm_inner_le_norm (𝕜 := ℂ) x y
  have hprod_le : ‖x‖ * ‖y‖ ≤ R := by
    have hdiff : 0 ≤ (‖x‖ - ‖y‖) ^ 2 := sq_nonneg _
    nlinarith [hxnorm, hynorm, hdiff]
  calc
    ((A * S * A * S).trace).re = (inner ℂ x y).re := by rw [hinner]
    _ ≤ ‖inner ℂ x y‖ := Complex.re_le_norm _
    _ ≤ ‖x‖ * ‖y‖ := hcs
    _ ≤ R := hprod_le

private theorem cMatrix_quarter_sandwich_tracePower_two_le
    (σ : State a) (hσ : σ.matrix.PosDef) {A : CMatrix a} (hA : A.PosSemidef) :
    psdTracePower
        (CFC.rpow σ.matrix (1 / 4 : ℝ) * A * CFC.rpow σ.matrix (1 / 4 : ℝ))
        (by
          let C : CMatrix a := CFC.rpow σ.matrix (1 / 4 : ℝ)
          have hC : C.PosSemidef := by
            simpa [C] using σ.rpowMatrix_posSemidef (1 / 4 : ℝ)
          have hCstar : star C = C := hC.isHermitian.eq
          have hW : (star C * A * C).PosSemidef :=
            Matrix.PosSemidef.conjTranspose_mul_mul_same hA C
          rw [hCstar] at hW
          simpa [C] using hW)
        (2 : ℝ) ≤
      ((σ.matrix * (A * A)).trace).re := by
  let C : CMatrix a := CFC.rpow σ.matrix (1 / 4 : ℝ)
  let S : CMatrix a := CFC.rpow σ.matrix (1 / 2 : ℝ)
  let W : CMatrix a := C * A * C
  have hC : C.PosSemidef := by
    simpa [C] using σ.rpowMatrix_posSemidef (1 / 4 : ℝ)
  have hS : S.PosSemidef := by
    simpa [S] using σ.rpowMatrix_posSemidef (1 / 2 : ℝ)
  have hCstar : star C = C := hC.isHermitian.eq
  have hW : W.PosSemidef := by
    have hW' : (star C * A * C).PosSemidef :=
      Matrix.PosSemidef.conjTranspose_mul_mul_same hA C
    rw [hCstar] at hW'
    simpa [W] using hW'
  have hCC : C * C = S := by
    calc
      C * C =
          CFC.rpow σ.matrix (1 / 4 : ℝ) *
            CFC.rpow σ.matrix (1 / 4 : ℝ) := by rfl
      _ = CFC.rpow σ.matrix ((1 / 4 : ℝ) + (1 / 4 : ℝ)) := by
            exact (CFC.rpow_add (a := σ.matrix) (x := (1 / 4 : ℝ))
              (y := (1 / 4 : ℝ)) hσ.isUnit).symm
      _ = S := by
            norm_num [S]
  have hSS : S * S = σ.matrix := by
    calc
      S * S =
          CFC.rpow σ.matrix (1 / 2 : ℝ) *
            CFC.rpow σ.matrix (1 / 2 : ℝ) := by rfl
      _ = CFC.rpow σ.matrix ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
            exact (CFC.rpow_add (a := σ.matrix) (x := (1 / 2 : ℝ))
              (y := (1 / 2 : ℝ)) hσ.isUnit).symm
      _ = σ.matrix := by
            norm_num
            exact CFC.rpow_one σ.matrix
              (ha := Matrix.nonneg_iff_posSemidef.mpr hσ.posSemidef)
  have htraceW :
      (W * W).trace.re = (A * S * A * S).trace.re := by
    congr 1
    dsimp [W]
    calc
      ((C * A * C) * (C * A * C)).trace =
          (C * A * C * C * A * C).trace := by
            noncomm_ring
      _ = (A * C * C * A * C * C).trace := by
            calc
              (C * A * C * C * A * C).trace =
                  (C * A * (C * C * A * C)).trace := by
                    noncomm_ring
              _ = ((A * C * C * A * C) * C).trace := by
                    calc
                      (C * A * (C * C * A * C)).trace =
                          (C * (A * (C * C * A * C))).trace := by
                            rw [Matrix.mul_assoc]
                      _ = ((A * (C * C * A * C)) * C).trace := by
                            rw [Matrix.trace_mul_comm]
                      _ = ((A * C * C * A * C) * C).trace := by
                            noncomm_ring
              _ = (A * C * C * A * C * C).trace := by
                    noncomm_ring
      _ = (A * S * A * S).trace := by
            calc
              (A * C * C * A * C * C).trace =
                  (A * (C * C) * A * (C * C)).trace := by
                    noncomm_ring
              _ = (A * S * A * S).trace := by
                    rw [hCC]
  have hbridge :
      ((A * S * A * S).trace).re ≤ ((S * S * (A * A)).trace).re :=
    cMatrix_trace_sandwich_sq_le_weighted_sq hS hA.isHermitian
  calc
    psdTracePower
        (CFC.rpow σ.matrix (1 / 4 : ℝ) * A * CFC.rpow σ.matrix (1 / 4 : ℝ))
        (by
          let C : CMatrix a := CFC.rpow σ.matrix (1 / 4 : ℝ)
          have hC : C.PosSemidef := by
            simpa [C] using σ.rpowMatrix_posSemidef (1 / 4 : ℝ)
          have hCstar : star C = C := hC.isHermitian.eq
          have hW : (star C * A * C).PosSemidef :=
            Matrix.PosSemidef.conjTranspose_mul_mul_same hA C
          rw [hCstar] at hW
          simpa [C] using hW)
        (2 : ℝ) =
        (W * W).trace.re := by
          rw [psdTracePower_two]
    _ = (A * S * A * S).trace.re := htraceW
    _ ≤ ((S * S * (A * A)).trace).re := hbridge
    _ = ((σ.matrix * (A * A)).trace).re := by
          rw [hSS]

/-- Weighted trace form of Kadison's inequality for a trace-preserving Kraus
channel.

For a PSD input weight `D`, the square of the pulled-back observable is bounded
after trace pairing by the output-side square. This is the `L₂` core bridge of
the α > 1 variational route. -/
theorem sandwichedRenyi_krausAdjoint_weighted_square_trace_le
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    {D : CMatrix a} (hD : D.PosSemidef)
    {E : CMatrix b} (hE : E.IsHermitian) :
    ((D * (MatrixMap.krausAdjoint K E * MatrixMap.krausAdjoint K E)).trace).re ≤
      (((MatrixMap.ofKraus K) D * (E * E)).trace).re := by
  have hkadison :
      MatrixMap.krausAdjoint K E * MatrixMap.krausAdjoint K E ≤
        MatrixMap.krausAdjoint K (E * E) :=
    MatrixMap.krausAdjoint_mul_self_le_of_tracePreserving K hTP hE
  have htrace :=
    cMatrix_trace_mul_le_of_le_posSemidef_left (W := D)
      (A := MatrixMap.krausAdjoint K E * MatrixMap.krausAdjoint K E)
      (B := MatrixMap.krausAdjoint K (E * E)) hD hkadison
  have hdual := MatrixMap.ofKraus_trace_duality K D (E * E)
  rw [← hdual] at htrace
  exact htrace

/-- Weighted trace bridge specialized to the Holder dual effect generated by an
output PSD witness. -/
theorem sandwichedRenyi_holderDualEffect_weighted_square_trace_le
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    {B : CMatrix b} (hB : B.PosSemidef) (α : ℝ) :
    ((σ.matrix *
        (MatrixMap.krausAdjoint K
            (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α) *
          MatrixMap.krausAdjoint K
            (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α))).trace).re ≤
      (((Φ.applyState σ).matrix *
          (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α *
            sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)).trace).re := by
  have hbase :=
    sandwichedRenyi_krausAdjoint_weighted_square_trace_le
      (K := K) hTP (D := σ.matrix) σ.pos
      (E := sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)
      (sandwichedRenyiHolderDualEffect_posSemidef (Φ.applyState σ) hB α).isHermitian
  have hmap : (MatrixMap.ofKraus K) σ.matrix = (Φ.applyState σ).matrix := by
    rw [← hK]
    rfl
  simpa [hmap] using hbase

/-- The Holder dual effect weighted square bound with the output state weight
removed using `Φσ ≤ I`. This isolates the remaining hard step: comparing the
unweighted square trace of the sandwiched dual effect to the original output
unit-ball witness. -/
theorem sandwichedRenyi_holderDualEffect_square_trace_le
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    {B : CMatrix b} (hB : B.PosSemidef) (α : ℝ) :
    ((σ.matrix *
        (MatrixMap.krausAdjoint K
            (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α) *
          MatrixMap.krausAdjoint K
            (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α))).trace).re ≤
      (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α *
        sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α).trace.re := by
  let E : CMatrix b := sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α
  have hweighted :
      ((σ.matrix *
          (MatrixMap.krausAdjoint K E * MatrixMap.krausAdjoint K E)).trace).re ≤
        (((Φ.applyState σ).matrix * (E * E)).trace).re := by
    simpa [E] using
      sandwichedRenyi_holderDualEffect_weighted_square_trace_le
        K σ Φ hK hTP hB α
  have hE : E.PosSemidef := by
    simpa [E] using sandwichedRenyiHolderDualEffect_posSemidef (Φ.applyState σ) hB α
  have hEsq : (E * E).PosSemidef := by
    simpa [hE.isHermitian.eq] using Matrix.posSemidef_conjTranspose_mul_self E
  have hunweighted :
      (((Φ.applyState σ).matrix * (E * E)).trace).re ≤ (E * E).trace.re :=
    state_trace_mul_le_trace_of_posSemidef (Φ.applyState σ) hEsq
  exact hweighted.trans (by simpa [E] using hunweighted)

/-- `psdTracePower` form of `sandwichedRenyi_holderDualEffect_square_trace_le`
for the Hilbert-Schmidt/α = 2 specialization of the variational route. -/
theorem sandwichedRenyi_holderDualEffect_tracePower_two_le
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    {B : CMatrix b} (hB : B.PosSemidef) (α : ℝ) :
    ((σ.matrix *
        (MatrixMap.krausAdjoint K
            (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α) *
          MatrixMap.krausAdjoint K
            (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α))).trace).re ≤
      psdTracePower (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)
        (sandwichedRenyiHolderDualEffect_posSemidef (Φ.applyState σ) hB α) (2 : ℝ) := by
  have hsq :=
    sandwichedRenyi_holderDualEffect_square_trace_le
      K σ Φ hK hTP hB α
  rw [psdTracePower_two]
  exact hsq

/-- Input-side Holder witness obtained by pulling an output witness back through
the Kraus adjoint and conjugating by the inverse sandwiched reference factor.

The q-unit-ball estimate for this witness is the remaining noncommutative
operator inequality in the α > 1 Holder route. -/
def sandwichedRenyiKrausAdjointInputWitness
    (σ : State a) (Φ : Channel a b) {κ : Type*} [Fintype κ]
    (K : κ → Matrix b a ℂ) (B : CMatrix b) (α : ℝ) : CMatrix a :=
  let s := (1 - α) / (2 * α)
  let D := CFC.rpow σ.matrix (-s)
  D * MatrixMap.krausAdjoint K
    (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α) * D

/-- Rotated Kraus operators for the sandwiched Renyi Holder route.

For `s = (1 - α) / (2α)`, these are
`(Φσ)^s K σ^{-s}`. Their Heisenberg adjoint is exactly the input-side
Holder witness obtained by transporting an output witness through the channel.
-/
def sandwichedRenyiRotatedKraus
    (σ : State a) (τ : State b) {κ : Type*} [Fintype κ]
    (K : κ → Matrix b a ℂ) (α : ℝ) : κ → Matrix b a ℂ :=
  fun k =>
    let s := (1 - α) / (2 * α)
    CFC.rpow τ.matrix s * K k * CFC.rpow σ.matrix (-s)

/-- Alignment with the weighted map in Beigi's Schatten interpolation route.

For Holder conjugates `α` and `q`, the rotated Kraus family is exactly the
Kraus representation of `Γ_τ^{-1/q} ∘ Φ ∘ Γ_σ^{1/q}`:
`τ^{-1/(2q)} K σ^{1/(2q)}`. -/
theorem sandwichedRenyiRotatedKraus_eq_beigiWeightedKraus
    (σ : State a) (τ : State b) {κ : Type*} [Fintype κ]
    (K : κ → Matrix b a ℂ) (α q : ℝ) (hpq : α.HolderConjugate q) :
    sandwichedRenyiRotatedKraus σ τ K α =
      fun k => CFC.rpow τ.matrix (-(1 / q) / 2) * K k *
        CFC.rpow σ.matrix ((1 / q) / 2) := by
  funext k
  have hα_ne : α ≠ 0 := ne_of_gt hpq.pos
  have htheta : 1 / q = 1 - 1 / α := by
    simpa [one_div] using hpq.one_sub_inv.symm
  have hs : (1 - α) / (2 * α) = -(1 / q) / 2 := by
    rw [htheta]
    field_simp [hα_ne]
    ring
  have hneg_half : - (-(1 / q) / 2) = (1 / q) / 2 := by
    ring
  simp only [sandwichedRenyiRotatedKraus]
  rw [hs, hneg_half]

/-- Complex-weighted rotated Kraus family for the interpolation proof route.

At a real exponent `s`, this is
`τ^s K σ^{-s}` and therefore specializes to the existing
`sandwichedRenyiRotatedKraus` when `s = (1 - α) / (2α)`. On imaginary boundary
lines the two reference factors are unitary by
`cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero`, providing the
matrix-power endpoint needed for the Riesz-Thorin step. -/
def sandwichedRenyiRotatedKrausComplex
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ) (z : ℂ) :
    κ → Matrix b a ℂ :=
  fun k =>
    cMatrixPosDefComplexPower τ.matrix hτ z * K k *
      cMatrixPosDefComplexPower σ.matrix hσ (-z)

/-- Real-axis specialization of the complex rotated Kraus family. -/
theorem sandwichedRenyiRotatedKrausComplex_ofReal
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ) (s : ℝ) :
    sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K (s : ℂ) =
      fun k => CFC.rpow τ.matrix s * K k * CFC.rpow σ.matrix (-s) := by
  funext k
  have hneg : -((s : ℂ)) = ((-s : ℝ) : ℂ) := by norm_num
  unfold sandwichedRenyiRotatedKrausComplex
  rw [cMatrixPosDefComplexPower_ofReal hτ s]
  rw [hneg, cMatrixPosDefComplexPower_ofReal hσ (-s)]

/-- Analytic weighted map for the Beigi interpolation route.

For a complex strip parameter `z`, this is the source-shaped map
`X ↦ τ^z Φ(σ^{-z} X σ^{-z}) τ^z`.  On the real axis it coincides with the
Kraus map generated by `τ^z K σ^{-z}`, while avoiding the anti-holomorphic
`conjTranspose` dependence that would appear in `MatrixMap.ofKraus` away from
the real axis. -/
def sandwichedRenyiWeightedMapComplex
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ) (z : ℂ) :
    MatrixMap a b where
  toFun X :=
    let T : CMatrix b := cMatrixPosDefComplexPower τ.matrix hτ z
    let S : CMatrix a := cMatrixPosDefComplexPower σ.matrix hσ (-z)
    T * MatrixMap.ofKraus K (S * X * S) * T
  map_add' X Y := by
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  map_smul' c X := by
    simp [Matrix.mul_assoc]

/-- On real interpolation parameters, the analytic weighted map agrees with
the corresponding rotated Kraus CP map. -/
theorem sandwichedRenyiWeightedMapComplex_ofReal_eq_ofKraus
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ) (s : ℝ)
    (X : CMatrix a) :
    sandwichedRenyiWeightedMapComplex σ hσ τ hτ K (s : ℂ) X =
      MatrixMap.ofKraus (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K (s : ℂ)) X := by
  let T : CMatrix b := CFC.rpow τ.matrix s
  let S : CMatrix a := CFC.rpow σ.matrix (-s)
  have hTstar : star T = T := by
    have hTpsd : T.PosSemidef := by
      simpa [T] using cMatrix_rpow_posSemidef (A := τ.matrix) (s := s) hτ.posSemidef
    exact hTpsd.isHermitian.eq
  have hSstar : star S = S := by
    have hSpsd : S.PosSemidef := by
      simpa [S] using cMatrix_rpow_posSemidef (A := σ.matrix) (s := -s) hσ.posSemidef
    exact hSpsd.isHermitian.eq
  have hneg : -((s : ℂ)) = ((-s : ℝ) : ℂ) := by norm_num
  have hconj :
      MatrixMap.ofKraus (fun k => T * K k * S) X =
        T * MatrixMap.ofKraus K (S * X * S) * T := by
    simpa [hSstar, hTstar, Matrix.mul_assoc] using
      (MatrixMap.ofKraus_conjugated_apply K T S X)
  have hfamily :
      (fun k => T * K k * S) =
        sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K (s : ℂ) := by
    funext k
    simp [T, S, sandwichedRenyiRotatedKrausComplex_ofReal]
  calc
    sandwichedRenyiWeightedMapComplex σ hσ τ hτ K (s : ℂ) X =
        T * MatrixMap.ofKraus K (S * X * S) * T := by
          change cMatrixPosDefComplexPower τ.matrix hτ (s : ℂ) *
              MatrixMap.ofKraus K
                (cMatrixPosDefComplexPower σ.matrix hσ (-((s : ℂ))) * X *
                  cMatrixPosDefComplexPower σ.matrix hσ (-((s : ℂ)))) *
                cMatrixPosDefComplexPower τ.matrix hτ (s : ℂ) =
              T * MatrixMap.ofKraus K (S * X * S) * T
          rw [cMatrixPosDefComplexPower_ofReal hτ s]
          rw [hneg, cMatrixPosDefComplexPower_ofReal hσ (-s)]
    _ = MatrixMap.ofKraus (fun k => T * K k * S) X := hconj.symm
    _ = MatrixMap.ofKraus (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K (s : ℂ)) X := by
          rw [hfamily]

/-- The source-shaped real rotated Kraus family is the real-axis point of the
complex interpolation family. -/
theorem sandwichedRenyiRotatedKraus_eq_complex_ofReal
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ) (α : ℝ) :
    sandwichedRenyiRotatedKraus σ τ K α =
      sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K
        (((1 - α) / (2 * α) : ℝ) : ℂ) := by
  funext k
  rw [sandwichedRenyiRotatedKrausComplex_ofReal]
  simp [sandwichedRenyiRotatedKraus]

/-- The real interpolation point `z = -1/(2q)` of the complex rotated family is
the source-shaped rotated Kraus map for Holder-conjugate `α` and `q`. -/
theorem sandwichedRenyiRotatedKraus_eq_complex_holderTheta
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (α q : ℝ) (hpq : α.HolderConjugate q) :
    sandwichedRenyiRotatedKraus σ τ K α =
      sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K (-(((1 / q : ℝ) : ℂ) / 2)) := by
  have hpoint : -((1 / q : ℝ) / 2) = (1 - α) / (2 * α) := by
    have htheta : 1 / q = 1 - 1 / α := by
      simpa [one_div] using hpq.one_sub_inv.symm
    have hα_ne : α ≠ 0 := ne_of_gt hpq.pos
    rw [htheta]
    field_simp [hα_ne]
    ring
  rw [sandwichedRenyiRotatedKraus_eq_complex_ofReal σ hσ τ hτ K α]
  congr 1
  exact_mod_cast hpoint.symm

/-- At the Holder interpolation point `z = -1/(2q)`, the analytic weighted map
is the source-shaped rotated Kraus map used in the sandwiched Renyi inner
operator. -/
theorem sandwichedRenyiWeightedMapComplex_holderTheta_eq_rotatedKraus
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (α q : ℝ) (hpq : α.HolderConjugate q) (X : CMatrix a) :
    sandwichedRenyiWeightedMapComplex σ hσ τ hτ K (-(((1 / q : ℝ) : ℂ) / 2)) X =
      MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) X := by
  have hpoint : (((-(1 / q) / 2 : ℝ) : ℂ)) = -(((1 / q : ℝ) : ℂ) / 2) := by
    norm_num [one_div, div_eq_mul_inv]
  rw [← hpoint, sandwichedRenyiWeightedMapComplex_ofReal_eq_ofKraus]
  rw [hpoint]
  rw [← sandwichedRenyiRotatedKraus_eq_complex_holderTheta σ hσ τ hτ K α q hpq]

/-- Scalar trace family built from the source-faithful analytic weighted map.

The paths `Apath` and `Bpath` are the Beigi/Riesz-Thorin input and dual
witness paths.  Keeping them explicit separates the algebraic weighted-map
alignment from the later choice of analytic Schatten-normalizing paths. -/
def sandwichedRenyiWeightedTraceFamily
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (Apath : ℂ → CMatrix a) (Bpath : ℂ → CMatrix b) (z : ℂ) : ℂ :=
  ((sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z (Apath z)) * Bpath z).trace

/-- Left-boundary endpoint estimate for the source-faithful weighted trace
family, assuming the exact boundary norm facts for the path inputs.

This is the non-circular `p = 1` Beigi endpoint: trace-norm contraction comes
only from the original trace-preserving Kraus map, while the reference and dual
paths enter through finite-dimensional contraction conditions. -/
theorem sandwichedRenyiWeightedTraceFamily_left_bound_of_traceNorm
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (Apath : ℂ → CMatrix a) (Bpath : ℂ → CMatrix b)
    (C : ℝ) (z : ℂ)
    (hS : Matrix.conjTranspose (cMatrixPosDefComplexPower σ.matrix hσ (-z)) *
        cMatrixPosDefComplexPower σ.matrix hσ (-z) = 1)
    (hT : Matrix.conjTranspose (cMatrixPosDefComplexPower τ.matrix hτ z) *
        cMatrixPosDefComplexPower τ.matrix hτ z = 1)
    (hB : Matrix.conjTranspose (Bpath z) * Bpath z ≤ 1)
    (hA : traceNorm (Apath z) ≤ C) :
    ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath z‖ ≤ C := by
  let T : CMatrix b := cMatrixPosDefComplexPower τ.matrix hτ z
  let S : CMatrix a := cMatrixPosDefComplexPower σ.matrix hσ (-z)
  let X : CMatrix a := Apath z
  let Y : CMatrix b := Bpath z
  let M : CMatrix b := MatrixMap.ofKraus K (S * X * S)
  have hS' : Matrix.conjTranspose S * S = 1 := by simpa [S] using hS
  have hT' : Matrix.conjTranspose T * T = 1 := by simpa [T] using hT
  have hTle : Matrix.conjTranspose T * T ≤ 1 := by rw [hT']
  have hY : Matrix.conjTranspose Y * Y ≤ 1 := by simpa [Y] using hB
  have hYT : Matrix.conjTranspose (Y * T) * (Y * T) ≤ 1 :=
    MatrixMap.cMatrix_contraction_mul Y T hY hTle
  have hW : Matrix.conjTranspose (T * Y * T) * (T * Y * T) ≤ 1 := by
    simpa [Matrix.mul_assoc] using
      MatrixMap.cMatrix_contraction_mul T (Y * T) hTle hYT
  have htrace :
      sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath z =
        (M * (T * Y * T)).trace := by
    unfold sandwichedRenyiWeightedTraceFamily sandwichedRenyiWeightedMapComplex
    change ((T * MatrixMap.ofKraus K (S * X * S) * T) * Y).trace =
      (M * (T * Y * T)).trace
    calc
      ((T * MatrixMap.ofKraus K (S * X * S) * T) * Y).trace =
          (T * (M * T * Y)).trace := by simp [M, Matrix.mul_assoc]
      _ = ((M * T * Y) * T).trace := by rw [Matrix.trace_mul_comm]
      _ = (M * (T * Y * T)).trace := by simp [Matrix.mul_assoc]
  have hpair :
      ‖(M * (T * Y * T)).trace‖ ≤ traceNorm M := by
    simpa using traceNorm_variational_contraction_abs_trace_le M (T * Y * T) hW
  have hkraus : traceNorm M ≤ traceNorm (S * X * S) := by
    simpa [M] using MatrixMap.traceNorm_contract_ofKraus_of_tracePreserving
      K hTP (S * X * S)
  have hSX : traceNorm (S * X * S) ≤ traceNorm X :=
    MatrixMap.traceNorm_isometry_mul_contraction_mul_le S X S hS' (by rw [hS'])
  calc
    ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath z‖ =
        ‖(M * (T * Y * T)).trace‖ := by rw [htrace]
    _ ≤ traceNorm M := hpair
    _ ≤ traceNorm (S * X * S) := hkraus
    _ ≤ traceNorm X := hSX
    _ ≤ C := by simpa [X] using hA

/-- The source-faithful weighted trace family hits the rotated-Kraus trace
pairing at the Holder interpolation point when the two analytic paths hit the
chosen input and dual witness there. -/
theorem sandwichedRenyiWeightedTraceFamily_holderTheta_target
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    (Apath : ℂ → CMatrix a) (Bpath : ℂ → CMatrix b)
    (A : CMatrix a) (B : CMatrix b)
    (hAθ : Apath (-(((1 / q : ℝ) : ℂ) / 2)) = A)
    (hBθ : Bpath (-(((1 / q : ℝ) : ℂ) / 2)) = B) :
    sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath
        (-(((1 / q : ℝ) : ℂ) / 2)) =
      ((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace := by
  unfold sandwichedRenyiWeightedTraceFamily
  rw [hAθ, hBθ]
  rw [sandwichedRenyiWeightedMapComplex_holderTheta_eq_rotatedKraus
    σ hσ τ hτ K α q hpq A]

private theorem matrixPath_mul_differentiable
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {M : ℂ → Matrix m n ℂ} {N : ℂ → Matrix n p ℂ}
    (hM : Differentiable ℂ M) (hN : Differentiable ℂ N) :
    Differentiable ℂ fun z : ℂ => M z * N z := by
  change Differentiable ℂ fun z : ℂ => fun i j => (M z * N z) i j
  exact differentiable_pi.2 fun i =>
    differentiable_pi.2 fun j => by
      simp only [Matrix.mul_apply]
      change Differentiable ℂ fun z : ℂ => ∑ k, M z i k * N z k j
      have hsum : Differentiable ℂ
          (∑ k, fun z : ℂ => M z i k * N z k j) :=
        Differentiable.sum (u := Finset.univ)
        (A := fun k z => M z i k * N z k j)
        (fun k _ =>
          (differentiable_pi.mp (differentiable_pi.mp hM i) k).mul
            (differentiable_pi.mp (differentiable_pi.mp hN k) j))
      convert hsum using 1
      ext z
      simp

private theorem matrixPath_smul_differentiable
    {m n : Type*} [Fintype m] [Fintype n]
    {c : ℂ → ℂ} {M : ℂ → Matrix m n ℂ}
    (hc : Differentiable ℂ c) (hM : Differentiable ℂ M) :
    Differentiable ℂ fun z : ℂ => c z • M z := by
  change Differentiable ℂ fun z : ℂ => fun i j => (c z • M z) i j
  exact differentiable_pi.2 fun i =>
    differentiable_pi.2 fun j => by
      change Differentiable ℂ fun z : ℂ => c z * M z i j
      exact hc.mul (differentiable_pi.mp (differentiable_pi.mp hM i) j)

private theorem matrixMap_ofKraus_path_differentiable
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    {Xpath : ℂ → CMatrix a} (hX : Differentiable ℂ Xpath) :
    Differentiable ℂ fun z : ℂ => MatrixMap.ofKraus K (Xpath z) := by
  change Differentiable ℂ fun z : ℂ => fun i j => (MatrixMap.ofKraus K (Xpath z)) i j
  apply differentiable_pi.2
  intro i
  apply differentiable_pi.2
  intro j
  unfold MatrixMap.ofKraus
  change Differentiable ℂ fun z : ℂ =>
    (∑ k, K k * Xpath z * Matrix.conjTranspose (K k)) i j
  simp only [Matrix.sum_apply]
  change Differentiable ℂ fun z : ℂ =>
    ∑ k, (K k * Xpath z * Matrix.conjTranspose (K k)) i j
  have hsum : Differentiable ℂ
      (∑ k, fun z : ℂ => (K k * Xpath z * Matrix.conjTranspose (K k)) i j) :=
    Differentiable.sum (u := Finset.univ)
    (A := fun k z => (K k * Xpath z * Matrix.conjTranspose (K k)) i j)
    (fun k _ => by
      have hterm : Differentiable ℂ fun z : ℂ =>
          K k * Xpath z * Matrix.conjTranspose (K k) :=
        matrixPath_mul_differentiable
          (matrixPath_mul_differentiable (differentiable_const (c := K k)) hX)
          (differentiable_const (c := Matrix.conjTranspose (K k)))
      exact differentiable_pi.mp (differentiable_pi.mp hterm i) j)
  convert hsum using 1
  ext z
  simp

private theorem matrix_trace_path_differentiable
    {n : Type*} [Fintype n] {M : ℂ → CMatrix n}
    (hM : Differentiable ℂ M) :
    Differentiable ℂ fun z : ℂ => (M z).trace := by
  unfold Matrix.trace
  change Differentiable ℂ fun z : ℂ => ∑ i, M z i i
  have hsum : Differentiable ℂ (∑ i, fun z : ℂ => M z i i) :=
    Differentiable.sum (u := Finset.univ)
    (A := fun i z => M z i i)
    (fun i _ => differentiable_pi.mp (differentiable_pi.mp hM i) i)
  convert hsum using 1
  ext z
  simp

/-- Holomorphicity of the source-faithful weighted trace family, assuming the
input and dual witness paths are holomorphic.

This is the analytic side of the Beigi/Riesz-Thorin spine after replacing the
non-holomorphic `ofKraus L_z` family by `sandwichedRenyiWeightedMapComplex`. -/
theorem sandwichedRenyiWeightedTraceFamily_differentiable
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (Apath : ℂ → CMatrix a) (Bpath : ℂ → CMatrix b)
    (hApath : Differentiable ℂ Apath) (hBpath : Differentiable ℂ Bpath) :
    Differentiable ℂ
      (sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath) := by
  let Tfun : ℂ → CMatrix b := fun z => cMatrixPosDefComplexPower τ.matrix hτ z
  let Sfun : ℂ → CMatrix a := fun z => cMatrixPosDefComplexPower σ.matrix hσ (-z)
  have hT : Differentiable ℂ Tfun := by
    simpa [Tfun] using cMatrixPosDefComplexPower_differentiable hτ
  have hS : Differentiable ℂ Sfun := by
    have hraw := cMatrixPosDefComplexPower_affine_differentiable hσ (-1 : ℂ) 0
    convert hraw using 2
    ext z i
    simp [Sfun]
  have hinner : Differentiable ℂ fun z : ℂ => Sfun z * Apath z * Sfun z :=
    matrixPath_mul_differentiable (matrixPath_mul_differentiable hS hApath) hS
  have hkraus :
      Differentiable ℂ fun z : ℂ =>
        MatrixMap.ofKraus K (Sfun z * Apath z * Sfun z) :=
    matrixMap_ofKraus_path_differentiable K hinner
  have hweighted : Differentiable ℂ fun z : ℂ =>
      Tfun z * MatrixMap.ofKraus K (Sfun z * Apath z * Sfun z) * Tfun z :=
    matrixPath_mul_differentiable (matrixPath_mul_differentiable hT hkraus) hT
  have hpair : Differentiable ℂ fun z : ℂ =>
      (Tfun z * MatrixMap.ofKraus K (Sfun z * Apath z * Sfun z) * Tfun z) *
        Bpath z :=
    matrixPath_mul_differentiable hweighted hBpath
  have htrace : Differentiable ℂ fun z : ℂ =>
      ((Tfun z * MatrixMap.ofKraus K (Sfun z * Apath z * Sfun z) * Tfun z) *
        Bpath z).trace :=
    matrix_trace_path_differentiable hpair
  simpa [sandwichedRenyiWeightedTraceFamily, sandwichedRenyiWeightedMapComplex,
    Tfun, Sfun] using htrace

/-- The weighted trace family satisfies the `DiffContOnCl` analytic condition
required by the local Beigi three-lines handoff whenever its two matrix paths
are holomorphic. -/
theorem sandwichedRenyiWeightedTraceFamily_diffContOnCl_of_differentiable_paths
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (Apath : ℂ → CMatrix a) (Bpath : ℂ → CMatrix b)
    (hApath : Differentiable ℂ Apath) (hBpath : Differentiable ℂ Bpath) :
    DiffContOnCl ℂ
      (fun w : ℂ =>
        sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath (-(w / 2)))
      (Complex.HadamardThreeLines.verticalStrip 0 1) := by
  have hf :
      Differentiable ℂ
        (sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath) :=
    sandwichedRenyiWeightedTraceFamily_differentiable
      σ hσ τ hτ K Apath Bpath hApath hBpath
  have harg : Differentiable ℂ fun w : ℂ => -(w / 2) := by
    fun_prop
  exact (hf.comp harg).diffContOnCl

private theorem cMatrixPosDefComplexPower_one
    {A : CMatrix a} (hA : A.PosDef) :
    cMatrixPosDefComplexPower A hA (1 : ℂ) = A := by
  rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num]
  rw [cMatrixPosDefComplexPower_ofReal hA 1]
  exact CFC.rpow_one A (ha := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef)

private theorem cMatrixPosDefComplexPower_zero
    {A : CMatrix a} (hA : A.PosDef) :
    cMatrixPosDefComplexPower A hA (0 : ℂ) = 1 := by
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by norm_num]
  rw [cMatrixPosDefComplexPower_ofReal hA 0]
  exact CFC.rpow_zero A (ha := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef)

/-- Beigi input path on the local strip: `A_z = A^(2αz + α)`.

With the local convention `z = -w/2`, this is the standard path
`A^(α(1-w))`; at the Holder interpolation point it is exactly `A`. -/
def sandwichedRenyiBeigiInputPath
    (A : CMatrix a) (hA : A.PosDef) (α : ℝ) (z : ℂ) : CMatrix a :=
  cMatrixPosDefComplexPower A hA ((2 * (α : ℂ)) * z + (α : ℂ))

/-- Beigi dual-witness path on the local strip: `B_z = B^(-2qz)`.

With the local convention `z = -w/2`, this is the standard path `B^(qw)`;
at the Holder interpolation point it is exactly `B`. -/
def sandwichedRenyiBeigiDualPath
    (B : CMatrix b) (hB : B.PosDef) (q : ℝ) (z : ℂ) : CMatrix b :=
  cMatrixPosDefComplexPower B hB (-(2 * (q : ℂ) * z))

theorem sandwichedRenyiBeigiInputPath_differentiable
    (A : CMatrix a) (hA : A.PosDef) (α : ℝ) :
    Differentiable ℂ (sandwichedRenyiBeigiInputPath A hA α) := by
  simpa [sandwichedRenyiBeigiInputPath] using
    cMatrixPosDefComplexPower_affine_differentiable hA ((2 * α : ℝ) : ℂ) (α : ℂ)

theorem sandwichedRenyiBeigiDualPath_differentiable
    (B : CMatrix b) (hB : B.PosDef) (q : ℝ) :
    Differentiable ℂ (sandwichedRenyiBeigiDualPath B hB q) := by
  simpa [sandwichedRenyiBeigiDualPath] using
    cMatrixPosDefComplexPower_affine_differentiable hB ((-2 * q : ℝ) : ℂ) 0

theorem sandwichedRenyiBeigiInputPath_holderTheta
    {A : CMatrix a} (hA : A.PosDef)
    {α q : ℝ} (hpq : α.HolderConjugate q) :
    sandwichedRenyiBeigiInputPath A hA α (-(((1 / q : ℝ) : ℂ) / 2)) = A := by
  have hα_ne : α ≠ 0 := ne_of_gt hpq.pos
  have hq_ne : q ≠ 0 := ne_of_gt hpq.symm.pos
  have hexp_real : 2 * α * -(1 / q / 2) + α = 1 := by
    have hsum : 1 / α + 1 / q = 1 := by
      simpa [one_div] using hpq.inv_add_inv_eq_one
    field_simp [hα_ne, hq_ne] at hsum ⊢
    nlinarith
  have hexp :
      (2 * (α : ℂ) * (-(((1 / q : ℝ) : ℂ) / 2)) + (α : ℂ)) = 1 := by
    exact_mod_cast hexp_real
  rw [sandwichedRenyiBeigiInputPath, hexp]
  exact cMatrixPosDefComplexPower_one hA

theorem sandwichedRenyiBeigiDualPath_holderTheta
    {B : CMatrix b} (hB : B.PosDef)
    {α q : ℝ} (hpq : α.HolderConjugate q) :
    sandwichedRenyiBeigiDualPath B hB q (-(((1 / q : ℝ) : ℂ) / 2)) = B := by
  have hq_ne : q ≠ 0 := ne_of_gt hpq.symm.pos
  have hexp_real : -(2 * q * -(1 / q / 2)) = 1 := by
    field_simp [hq_ne]
  have hexp :
      (-(2 * (q : ℂ) * (-(((1 / q : ℝ) : ℂ) / 2)))) = 1 := by
    exact_mod_cast hexp_real
  rw [sandwichedRenyiBeigiDualPath, hexp]
  exact cMatrixPosDefComplexPower_one hB

theorem sandwichedRenyiBeigiInputPath_zero
    {A : CMatrix a} (hA : A.PosDef) (α : ℝ) :
    sandwichedRenyiBeigiInputPath A hA α 0 = CFC.rpow A α := by
  rw [sandwichedRenyiBeigiInputPath]
  have hexp : (2 * (α : ℂ)) * 0 + (α : ℂ) = (α : ℂ) := by ring
  rw [hexp, cMatrixPosDefComplexPower_ofReal hA α]

theorem sandwichedRenyiBeigiDualPath_zero
    {B : CMatrix b} (hB : B.PosDef) (q : ℝ) :
    sandwichedRenyiBeigiDualPath B hB q 0 = 1 := by
  rw [sandwichedRenyiBeigiDualPath]
  have hexp : -(2 * (q : ℂ) * 0) = 0 := by ring
  rw [hexp, cMatrixPosDefComplexPower_zero hB]

theorem sandwichedRenyiBeigiDualPath_star_mul_self_of_re_eq_zero
    {B : CMatrix b} (hB : B.PosDef) (q : ℝ) {z : ℂ} (hz : z.re = 0) :
    star (sandwichedRenyiBeigiDualPath B hB q z) *
        sandwichedRenyiBeigiDualPath B hB q z = 1 := by
  have hexp_re : (-(2 * (q : ℂ) * z)).re = 0 := by
    simp [hz]
  simpa [sandwichedRenyiBeigiDualPath] using
    cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero hB (z := -(2 * (q : ℂ) * z))
      hexp_re

/-- On the `p = ∞` boundary of the local Beigi strip, the dual path's trace
norm is exactly its `q`-power trace. -/
theorem sandwichedRenyiBeigiDualPath_traceNorm_of_re_eq_neg_half
    {B : CMatrix b} (hB : B.PosDef) (q : ℝ) {z : ℂ}
    (hz : z.re = -(1 / 2 : ℝ)) :
    traceNorm (sandwichedRenyiBeigiDualPath B hB q z) =
      psdTracePower B hB.posSemidef q := by
  have hexp_re : (-(2 * (q : ℂ) * z)).re = q := by
    simp [hz]
    ring
  simpa [sandwichedRenyiBeigiDualPath, hexp_re] using
    MatrixMap.traceNorm_cMatrixPosDefComplexPower_eq_psdTracePower_re hB
      (-(2 * (q : ℂ) * z))

/-- A `q`-unit-ball dual witness gives trace-norm control of the Beigi dual
path on the `p = ∞` boundary. -/
theorem sandwichedRenyiBeigiDualPath_traceNorm_le_one_of_re_eq_neg_half
    {B : CMatrix b} (hB : B.PosDef) {q : ℝ}
    (hBq : psdTracePower B hB.posSemidef q ≤ 1)
    {z : ℂ} (hz : z.re = -(1 / 2 : ℝ)) :
    traceNorm (sandwichedRenyiBeigiDualPath B hB q z) ≤ 1 := by
  rw [sandwichedRenyiBeigiDualPath_traceNorm_of_re_eq_neg_half hB q hz]
  exact hBq

theorem sandwichedRenyiBeigiInputPath_star_mul_self_of_re_eq_neg_half
    {A : CMatrix a} (hA : A.PosDef) (α : ℝ) {z : ℂ}
    (hz : z.re = -(1 / 2 : ℝ)) :
    star (sandwichedRenyiBeigiInputPath A hA α z) *
        sandwichedRenyiBeigiInputPath A hA α z = 1 := by
  have hexp_re : ((2 * (α : ℂ)) * z + (α : ℂ)).re = 0 := by
    simp [hz]
    ring
  simpa [sandwichedRenyiBeigiInputPath] using
    cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero hA
      (z := (2 * (α : ℂ)) * z + (α : ℂ)) hexp_re

/-- Normalized Beigi input path:
`‖A‖_α^(1-(2αz+α)) A^(2αz+α)`.

The scalar normalization is the standard Riesz-Thorin normalization: the path
still hits `A` at the Holder point, while its two boundary norms are scaled by
`‖A‖_α` rather than by `Tr A^α`. -/
def sandwichedRenyiBeigiNormalizedInputPath
    (A : CMatrix a) (hA : A.PosDef) (α : ℝ) (C : ℝ) (z : ℂ) : CMatrix a :=
  let e : ℂ := (2 * (α : ℂ)) * z + (α : ℂ)
  Complex.exp (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ)) •
    cMatrixPosDefComplexPower A hA e

theorem sandwichedRenyiBeigiNormalizedInputPath_differentiable
    (A : CMatrix a) (hA : A.PosDef) (α C : ℝ) :
    Differentiable ℂ (sandwichedRenyiBeigiNormalizedInputPath A hA α C) := by
  let e : ℂ → ℂ := fun z => (2 * (α : ℂ)) * z + (α : ℂ)
  have he : Differentiable ℂ e := by
    fun_prop
  have hscale : Differentiable ℂ fun z : ℂ =>
      Complex.exp (((1 : ℂ) - e z) * ((Real.log C : ℝ) : ℂ)) := by
    fun_prop
  have hpow : Differentiable ℂ fun z : ℂ => cMatrixPosDefComplexPower A hA (e z) := by
    simpa [e] using
      cMatrixPosDefComplexPower_affine_differentiable hA (2 * (α : ℂ)) (α : ℂ)
  simpa [sandwichedRenyiBeigiNormalizedInputPath, e] using
    matrixPath_smul_differentiable hscale hpow

theorem sandwichedRenyiBeigiNormalizedInputPath_holderTheta
    {A : CMatrix a} (hA : A.PosDef)
    {α q : ℝ} (hpq : α.HolderConjugate q) {C : ℝ} :
    sandwichedRenyiBeigiNormalizedInputPath A hA α C
        (-(((1 / q : ℝ) : ℂ) / 2)) = A := by
  have hα_ne : α ≠ 0 := ne_of_gt hpq.pos
  have hq_ne : q ≠ 0 := ne_of_gt hpq.symm.pos
  have hexp_real : 2 * α * -(1 / q / 2) + α = 1 := by
    have hsum : 1 / α + 1 / q = 1 := by
      simpa [one_div] using hpq.inv_add_inv_eq_one
    field_simp [hα_ne, hq_ne] at hsum ⊢
    nlinarith
  have hexp :
      (2 * (α : ℂ) * (-(((1 / q : ℝ) : ℂ) / 2)) + (α : ℂ)) = 1 := by
    exact_mod_cast hexp_real
  rw [sandwichedRenyiBeigiNormalizedInputPath, hexp]
  simp [cMatrixPosDefComplexPower_one hA]

/-- The normalized Beigi input path has trace norm at most its normalizing
Schatten value on the `Re z = 0` boundary. -/
theorem sandwichedRenyiBeigiNormalizedInputPath_traceNorm_le_of_re_eq_zero
    {A : CMatrix a} (hA : A.PosDef) {α C : ℝ} (hα : 0 < α)
    (hC : C = psdSchattenPNorm A hA.posSemidef ⟨α, hα⟩) (hCpos : 0 < C)
    {z : ℂ} (hz : z.re = 0) :
    traceNorm (sandwichedRenyiBeigiNormalizedInputPath A hA α C z) ≤ C := by
  let e : ℂ := (2 * (α : ℂ)) * z + (α : ℂ)
  let scalar : ℂ := Complex.exp (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ))
  let Q : ℝ := psdTracePower A hA.posSemidef α
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have he_re : e.re = α := by
    simp [e, hz]
  have hscalar_norm : ‖scalar‖ = C ^ (1 - α) := by
    have hre :
        (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ)).re =
          (1 - α) * Real.log C := by
      simp [Complex.mul_re, he_re]
    calc
      ‖scalar‖ = Real.exp (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ)).re := by
          simp [scalar, Complex.norm_exp]
      _ = Real.exp ((1 - α) * Real.log C) := by rw [hre]
      _ = C ^ (1 - α) := by
          rw [Real.rpow_def_of_pos hCpos]
          congr 1
          ring
  have hpower_trace :
      traceNorm (cMatrixPosDefComplexPower A hA e) = Q := by
    simpa [Q, he_re] using
      MatrixMap.traceNorm_cMatrixPosDefComplexPower_eq_psdTracePower_re hA e
  have hQ_nonneg : 0 ≤ Q := by
    simpa [Q] using psdTracePower_nonneg A hA.posSemidef α
  have hC_def : C = Q ^ (1 / α) := by
    simpa [Q, psdSchattenPNorm, Internal.psdSchattenExpression] using hC
  have hQ_eq_Cpow : Q = C ^ α := by
    calc
      Q = Q ^ ((1 / α) * α) := by
          have hmul : (1 / α) * α = (1 : ℝ) := by field_simp [hα_ne]
          rw [hmul, Real.rpow_one]
      _ = (Q ^ (1 / α)) ^ α := by rw [Real.rpow_mul hQ_nonneg]
      _ = C ^ α := by rw [← hC_def]
  have hscale :=
    MatrixMap.traceNorm_complex_smul_le scalar
      (cMatrixPosDefComplexPower A hA e)
  calc
    traceNorm (sandwichedRenyiBeigiNormalizedInputPath A hA α C z)
        ≤ ‖scalar‖ * traceNorm (cMatrixPosDefComplexPower A hA e) := by
          simpa [sandwichedRenyiBeigiNormalizedInputPath, scalar, e] using hscale
    _ = C ^ (1 - α) * Q := by rw [hscalar_norm, hpower_trace]
    _ = C ^ (1 - α) * C ^ α := by rw [hQ_eq_Cpow]
    _ = C ^ ((1 - α) + α) := by rw [← Real.rpow_add hCpos]
    _ = C := by
          ring_nf
          rw [Real.rpow_one]

section BeigiInputOperatorEndpoint

open scoped Matrix.Norms.L2Operator

/-- On the `p = ∞` boundary, the normalized Beigi input path has operator norm
at most its normalizing Schatten value. -/
theorem sandwichedRenyiBeigiNormalizedInputPath_opNorm_le_of_re_eq_neg_half
    {A : CMatrix a} (hA : A.PosDef) (α C : ℝ) (hCpos : 0 < C)
    {z : ℂ} (hz : z.re = -(1 / 2 : ℝ)) :
    ‖sandwichedRenyiBeigiNormalizedInputPath A hA α C z‖ ≤ C := by
  let e : ℂ := (2 * (α : ℂ)) * z + (α : ℂ)
  let scalar : ℂ := Complex.exp (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ))
  have he_re : e.re = 0 := by
    simp [e, hz]
    ring
  have hscalar_norm : ‖scalar‖ = C := by
    have hre :
        (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ)).re =
          Real.log C := by
      simp [Complex.mul_re, he_re]
    calc
      ‖scalar‖ = Real.exp (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ)).re := by
          simp [scalar, Complex.norm_exp]
      _ = Real.exp (Real.log C) := by rw [hre]
      _ = C := Real.exp_log hCpos
  have hpow_contract :
      ‖cMatrixPosDefComplexPower A hA e‖ ≤ (1 : ℝ) := by
    have hgram :
        Matrix.conjTranspose (cMatrixPosDefComplexPower A hA e) *
            cMatrixPosDefComplexPower A hA e ≤ 1 := by
      have hunit :
          Matrix.conjTranspose (cMatrixPosDefComplexPower A hA e) *
              cMatrixPosDefComplexPower A hA e = 1 := by
        simpa [Matrix.star_eq_conjTranspose] using
          cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero hA he_re
      rw [hunit]
    exact MatrixMap.cMatrix_l2OperatorNorm_le_one_of_conjTranspose_mul_self_le_one
      (cMatrixPosDefComplexPower A hA e) hgram
  calc
    ‖sandwichedRenyiBeigiNormalizedInputPath A hA α C z‖ =
        ‖scalar‖ * ‖cMatrixPosDefComplexPower A hA e‖ := by
          simp [sandwichedRenyiBeigiNormalizedInputPath, scalar, e, norm_smul]
    _ ≤ C * 1 := by
          rw [hscalar_norm]
          exact mul_le_mul_of_nonneg_left hpow_contract (le_of_lt hCpos)
    _ = C := by ring

/-- On the `p = ∞` boundary, the normalized Beigi input path is a matrix
contraction after dividing by its Schatten normalizing constant.

This strengthens the norm estimate above to the exact unit-ball condition used
by the trace-norm variational handoff. -/
theorem sandwichedRenyiBeigiNormalizedInputPath_scaled_contraction_of_re_eq_neg_half
    {A : CMatrix a} (hA : A.PosDef) (α C : ℝ) (hCpos : 0 < C)
    {z : ℂ} (hz : z.re = -(1 / 2 : ℝ)) :
    Matrix.conjTranspose (((C : ℂ)⁻¹) •
        sandwichedRenyiBeigiNormalizedInputPath A hA α C z) *
      (((C : ℂ)⁻¹) •
        sandwichedRenyiBeigiNormalizedInputPath A hA α C z) ≤ 1 := by
  let e : ℂ := (2 * (α : ℂ)) * z + (α : ℂ)
  let scalar : ℂ := Complex.exp (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ))
  let c : ℂ := (C : ℂ)⁻¹ * scalar
  let P : CMatrix a := cMatrixPosDefComplexPower A hA e
  have he_re : e.re = 0 := by
    simp [e, hz]
    ring
  have hscalar_norm : ‖scalar‖ = C := by
    have hre :
        (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ)).re =
          Real.log C := by
      simp [Complex.mul_re, he_re]
    calc
      ‖scalar‖ = Real.exp (((1 : ℂ) - e) * ((Real.log C : ℝ) : ℂ)).re := by
          simp [scalar, Complex.norm_exp]
      _ = Real.exp (Real.log C) := by rw [hre]
      _ = C := Real.exp_log hCpos
  have hc_norm : ‖c‖ = 1 := by
    calc
      ‖c‖ = ‖(C : ℂ)⁻¹‖ * ‖scalar‖ := by simp [c]
      _ = ‖(C : ℂ)‖⁻¹ * C := by rw [norm_inv, hscalar_norm]
      _ = C⁻¹ * C := by
            have hCnorm : ‖(C : ℂ)‖ = C := by
              rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt hCpos)]
            rw [hCnorm]
      _ = 1 := by field_simp [ne_of_gt hCpos]
  have hc_star_mul : star c * c = 1 := by
    have hnormSq : Complex.normSq c = 1 := by
      rw [Complex.normSq_eq_norm_sq, hc_norm]
      norm_num
    change (starRingEnd ℂ) c * c = 1
    rw [← Complex.normSq_eq_conj_mul_self]
    exact_mod_cast hnormSq
  have hc_mul_star : c * star c = 1 := by
    rw [mul_comm]
    exact hc_star_mul
  have hc_mul_star' : c * (starRingEnd ℂ) c = 1 := by
    simpa using hc_mul_star
  have hPunit : Matrix.conjTranspose P * P = (1 : CMatrix a) := by
    simpa [P, Matrix.star_eq_conjTranspose] using
      cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero hA he_re
  have hpath :
      ((C : ℂ)⁻¹) • sandwichedRenyiBeigiNormalizedInputPath A hA α C z =
        c • P := by
    simp [sandwichedRenyiBeigiNormalizedInputPath, scalar, c, P, e, smul_smul,
      mul_assoc]
  rw [hpath]
  have heq :
      Matrix.conjTranspose (c • P) * (c • P) = (1 : CMatrix a) := by
    simp [Matrix.conjTranspose_smul, hPunit, smul_smul, hc_mul_star']
  rw [heq]

/-- Imaginary positive-definite complex powers are contractions in matrix
unit-ball form. -/
theorem cMatrixPosDefComplexPower_contraction_of_re_eq_zero
    {A : CMatrix a} (hA : A.PosDef) {z : ℂ} (hz : z.re = 0) :
    Matrix.conjTranspose (cMatrixPosDefComplexPower A hA z) *
        cMatrixPosDefComplexPower A hA z ≤ 1 := by
  have hunit :
      Matrix.conjTranspose (cMatrixPosDefComplexPower A hA z) *
          cMatrixPosDefComplexPower A hA z = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero hA hz
  rw [hunit]

/-- Left and right multiplication by the same imaginary reference power
preserves the matrix unit ball. -/
theorem cMatrixPosDefComplexPower_mul_mul_contraction_of_re_eq_zero
    {A : CMatrix a} (hA : A.PosDef) {z : ℂ} (hz : z.re = 0)
    {X : CMatrix a} (hX : Matrix.conjTranspose X * X ≤ 1) :
    Matrix.conjTranspose
        (cMatrixPosDefComplexPower A hA z * X *
          cMatrixPosDefComplexPower A hA z) *
      (cMatrixPosDefComplexPower A hA z * X *
          cMatrixPosDefComplexPower A hA z) ≤ 1 := by
  let U : CMatrix a := cMatrixPosDefComplexPower A hA z
  have hU : Matrix.conjTranspose U * U ≤ 1 :=
    cMatrixPosDefComplexPower_contraction_of_re_eq_zero hA hz
  have hUX : Matrix.conjTranspose (U * X) * (U * X) ≤ 1 :=
    MatrixMap.cMatrix_contraction_mul U X hU hX
  simpa [Matrix.mul_assoc, U] using
    MatrixMap.cMatrix_contraction_mul (U * X) U hUX hU

/-- Beigi right-boundary factorization for the source-faithful weighted map.

On the line `Re z = -1/2`, the analytic map
`X ↦ τ^z Φ(σ^{-z} X σ^{-z}) τ^z` factors as imaginary unitary rotations of
the real `z = -1/2` unital Kraus endpoint. -/
theorem sandwichedRenyiWeightedMapComplex_eq_imaginary_conj_of_re_eq_neg_half
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (z : ℂ) (X : CMatrix a) :
    let u : ℂ := z + ((1 / 2 : ℝ) : ℂ)
    let Uτ : CMatrix b := cMatrixPosDefComplexPower τ.matrix hτ u
    let Uσ : CMatrix a := cMatrixPosDefComplexPower σ.matrix hσ (-u)
    sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z X =
      Uτ *
        MatrixMap.ofKraus
          (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K
            (((-(1 / 2 : ℝ)) : ℝ) : ℂ))
          (Uσ * X * Uσ) *
        Uτ := by
  let u : ℂ := z + ((1 / 2 : ℝ) : ℂ)
  let Uτ : CMatrix b := cMatrixPosDefComplexPower τ.matrix hτ u
  let Uσ : CMatrix a := cMatrixPosDefComplexPower σ.matrix hσ (-u)
  let T0 : CMatrix b :=
    cMatrixPosDefComplexPower τ.matrix hτ (((-(1 / 2 : ℝ)) : ℝ) : ℂ)
  let S0 : CMatrix a :=
    cMatrixPosDefComplexPower σ.matrix hσ (((1 / 2 : ℝ) : ℝ) : ℂ)
  have hT_left :
      cMatrixPosDefComplexPower τ.matrix hτ z = Uτ * T0 := by
    have h :=
      cMatrixPosDefComplexPower_add hτ u (((-(1 / 2 : ℝ)) : ℝ) : ℂ)
    have hsum : u + (((-(1 / 2 : ℝ)) : ℝ) : ℂ) = z := by
      simp [u]
    rw [hsum] at h
    exact h.symm
  have hT_right :
      cMatrixPosDefComplexPower τ.matrix hτ z = T0 * Uτ := by
    have h :=
      cMatrixPosDefComplexPower_add hτ (((-(1 / 2 : ℝ)) : ℝ) : ℂ) u
    have hsum : (((-(1 / 2 : ℝ)) : ℝ) : ℂ) + u = z := by
      simp [u]
    rw [hsum] at h
    exact h.symm
  have hS_left :
      cMatrixPosDefComplexPower σ.matrix hσ (-z) = S0 * Uσ := by
    have h :=
      cMatrixPosDefComplexPower_add hσ (((1 / 2 : ℝ) : ℝ) : ℂ) (-u)
    have hsum : (((1 / 2 : ℝ) : ℝ) : ℂ) + -u = -z := by
      simp [u]
    rw [hsum] at h
    exact h.symm
  have hS_right :
      cMatrixPosDefComplexPower σ.matrix hσ (-z) = Uσ * S0 := by
    have h :=
      cMatrixPosDefComplexPower_add hσ (-u) (((1 / 2 : ℝ) : ℝ) : ℂ)
    have hsum : -u + (((1 / 2 : ℝ) : ℝ) : ℂ) = -z := by
      simp [u]
    rw [hsum] at h
    exact h.symm
  have hM :
      MatrixMap.ofKraus
          (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K
            (((-(1 / 2 : ℝ)) : ℝ) : ℂ))
          (Uσ * X * Uσ) =
        T0 * MatrixMap.ofKraus K (S0 * (Uσ * X * Uσ) * S0) * T0 := by
    have hreal :=
      sandwichedRenyiWeightedMapComplex_ofReal_eq_ofKraus
        σ hσ τ hτ K (-(1 / 2 : ℝ)) (Uσ * X * Uσ)
    rw [← hreal]
    unfold sandwichedRenyiWeightedMapComplex
    change
      cMatrixPosDefComplexPower τ.matrix hτ (((-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          MatrixMap.ofKraus K
            (cMatrixPosDefComplexPower σ.matrix hσ
                (-((((-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
              (Uσ * X * Uσ) *
              cMatrixPosDefComplexPower σ.matrix hσ
                (-((((-(1 / 2 : ℝ)) : ℝ) : ℂ)))) *
          cMatrixPosDefComplexPower τ.matrix hτ (((-(1 / 2 : ℝ)) : ℝ) : ℂ) =
        T0 * MatrixMap.ofKraus K (S0 * (Uσ * X * Uσ) * S0) * T0
    have hneg : -((((-(1 / 2 : ℝ)) : ℝ) : ℂ)) = (((1 / 2 : ℝ) : ℝ) : ℂ) := by
      norm_num
    rw [hneg]
  unfold sandwichedRenyiWeightedMapComplex
  change
    cMatrixPosDefComplexPower τ.matrix hτ z *
        MatrixMap.ofKraus K
          (cMatrixPosDefComplexPower σ.matrix hσ (-z) * X *
            cMatrixPosDefComplexPower σ.matrix hσ (-z)) *
        cMatrixPosDefComplexPower τ.matrix hτ z =
      Uτ *
        MatrixMap.ofKraus
          (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K
            (((-(1 / 2 : ℝ)) : ℝ) : ℂ))
          (Uσ * X * Uσ) *
        Uτ
  nth_rewrite 1 [hT_left]
  nth_rewrite 1 [hT_right]
  nth_rewrite 1 [hS_left]
  nth_rewrite 1 [hS_right]
  rw [hM]
  have hinside :
      (S0 * Uσ) * X * (Uσ * S0) =
        S0 * (Uσ * X * Uσ) * S0 := by
    noncomm_ring
  rw [hinside]
  noncomm_ring

end BeigiInputOperatorEndpoint

/-- The concrete Beigi input and dual paths satisfy the analytic
`DiffContOnCl` condition required by the local three-lines handoff. -/
theorem sandwichedRenyiWeightedTraceFamily_diffContOnCl_beigiPaths
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (A : CMatrix a) (hA : A.PosDef)
    (B : CMatrix b) (hB : B.PosDef)
    (α q : ℝ) :
    DiffContOnCl ℂ
      (fun w : ℂ =>
        sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
          (sandwichedRenyiBeigiInputPath A hA α)
          (sandwichedRenyiBeigiDualPath B hB q) (-(w / 2)))
      (Complex.HadamardThreeLines.verticalStrip 0 1) :=
  sandwichedRenyiWeightedTraceFamily_diffContOnCl_of_differentiable_paths
    σ hσ τ hτ K
    (sandwichedRenyiBeigiInputPath A hA α)
    (sandwichedRenyiBeigiDualPath B hB q)
    (sandwichedRenyiBeigiInputPath_differentiable A hA α)
    (sandwichedRenyiBeigiDualPath_differentiable B hB q)

/-- The normalized Beigi input path and dual path satisfy the analytic
`DiffContOnCl` condition required by the local three-lines handoff. -/
theorem sandwichedRenyiWeightedTraceFamily_diffContOnCl_normalizedBeigiPaths
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (A : CMatrix a) (hA : A.PosDef)
    (B : CMatrix b) (hB : B.PosDef)
    (α q C : ℝ) :
    DiffContOnCl ℂ
      (fun w : ℂ =>
        sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
          (sandwichedRenyiBeigiNormalizedInputPath A hA α C)
          (sandwichedRenyiBeigiDualPath B hB q) (-(w / 2)))
      (Complex.HadamardThreeLines.verticalStrip 0 1) :=
  sandwichedRenyiWeightedTraceFamily_diffContOnCl_of_differentiable_paths
    σ hσ τ hτ K
    (sandwichedRenyiBeigiNormalizedInputPath A hA α C)
    (sandwichedRenyiBeigiDualPath B hB q)
    (sandwichedRenyiBeigiNormalizedInputPath_differentiable A hA α C)
    (sandwichedRenyiBeigiDualPath_differentiable B hB q)

section BeigiClosedStripBoundedness

open scoped Matrix.Norms.L2Operator

private theorem bddAbove_norm_mul_of_bddAbove
    {ι R : Type*} [SeminormedRing R] {s : Set ι} {f g : ι → R}
    (hf : BddAbove ((norm ∘ f) '' s))
    (hg : BddAbove ((norm ∘ g) '' s)) :
    BddAbove ((norm ∘ fun x => f x * g x) '' s) := by
  rcases hf with ⟨Cf, hCf⟩
  rcases hg with ⟨Cg, hCg⟩
  refine ⟨max (Cf * Cg) 0, ?_⟩
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hf_le : ‖f x‖ ≤ Cf := hCf ⟨x, hx, rfl⟩
  have hg_le : ‖g x‖ ≤ Cg := hCg ⟨x, hx, rfl⟩
  have hf_nonneg : 0 ≤ Cf := (norm_nonneg (f x)).trans hf_le
  have hprod : ‖f x‖ * ‖g x‖ ≤ Cf * Cg :=
    mul_le_mul hf_le hg_le (norm_nonneg (g x)) hf_nonneg
  calc
    ‖f x * g x‖ ≤ ‖f x‖ * ‖g x‖ := norm_mul_le _ _
    _ ≤ Cf * Cg := hprod
    _ ≤ max (Cf * Cg) 0 := le_max_left _ _

private theorem bddAbove_norm_smul_of_bddAbove
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {s : Set ι} {c : ι → ℂ} {f : ι → E}
    (hc : BddAbove ((norm ∘ c) '' s))
    (hf : BddAbove ((norm ∘ f) '' s)) :
    BddAbove ((norm ∘ fun x => c x • f x) '' s) := by
  rcases hc with ⟨Cc, hCc⟩
  rcases hf with ⟨Cf, hCf⟩
  refine ⟨max (Cc * Cf) 0, ?_⟩
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hc_le : ‖c x‖ ≤ Cc := hCc ⟨x, hx, rfl⟩
  have hf_le : ‖f x‖ ≤ Cf := hCf ⟨x, hx, rfl⟩
  have hc_nonneg : 0 ≤ Cc := (norm_nonneg (c x)).trans hc_le
  have hprod : ‖c x‖ * ‖f x‖ ≤ Cc * Cf :=
    mul_le_mul hc_le hf_le (norm_nonneg (f x)) hc_nonneg
  calc
    ‖c x • f x‖ = ‖c x‖ * ‖f x‖ := norm_smul _ _
    _ ≤ Cc * Cf := hprod
    _ ≤ max (Cc * Cf) 0 := le_max_left _ _

private theorem bddAbove_norm_linearMap_of_bddAbove
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {s : Set ι} {f : ι → E} (L : E →ₗ[ℂ] F)
    (hf : BddAbove ((norm ∘ f) '' s)) :
    BddAbove ((norm ∘ fun x => L (f x)) '' s) := by
  rcases hf with ⟨C, hC⟩
  let C' : ℝ := max C 0
  let Lc : E →L[ℂ] F := LinearMap.toContinuousLinearMap L
  refine ⟨‖Lc‖ * C', ?_⟩
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hf_le_C : ‖f x‖ ≤ C := hC ⟨x, hx, rfl⟩
  have hf_le : ‖f x‖ ≤ C' := hf_le_C.trans (le_max_left C 0)
  have hL : ‖L (f x)‖ ≤ ‖Lc‖ * ‖f x‖ := by
    simpa [Lc, LinearMap.coe_toContinuousLinearMap] using Lc.le_opNorm (f x)
  exact hL.trans (mul_le_mul_of_nonneg_left hf_le (norm_nonneg Lc))

/-- Positive-definite complex powers have operator norm depending only on the
real part of the exponent. This is the boundedness ingredient that prevents
the Beigi strip from growing in the imaginary direction. -/
theorem cMatrixPosDefComplexPower_l2OperatorNorm_eq_re
    {A : CMatrix a} (hA : A.PosDef) (z : ℂ) :
    ‖cMatrixPosDefComplexPower A hA z‖ =
      ‖cMatrixPosDefComplexPower A hA ((z.re : ℝ) : ℂ)‖ := by
  let Pz : CMatrix a := cMatrixPosDefComplexPower A hA z
  let Pr : CMatrix a := cMatrixPosDefComplexPower A hA ((z.re : ℝ) : ℂ)
  have hzstar : Matrix.conjTranspose Pz * Pz = CFC.rpow A (2 * z.re) := by
    simpa [Pz, Matrix.star_eq_conjTranspose] using
      cMatrixPosDefComplexPower_star_mul_self hA z
  have hr_re : (((z.re : ℝ) : ℂ)).re = z.re := by simp
  have hrstar : Matrix.conjTranspose Pr * Pr = CFC.rpow A (2 * z.re) := by
    simpa [Pr, hr_re, Matrix.star_eq_conjTranspose] using
      cMatrixPosDefComplexPower_star_mul_self hA (((z.re : ℝ) : ℂ))
  have hzsq : ‖Pz‖ * ‖Pz‖ = ‖CFC.rpow A (2 * z.re)‖ := by
    calc
      ‖Pz‖ * ‖Pz‖ = ‖Matrix.conjTranspose Pz * Pz‖ := by
        simpa [Matrix.star_eq_conjTranspose] using
          (CStarRing.norm_star_mul_self (x := Pz)).symm
      _ = ‖CFC.rpow A (2 * z.re)‖ := by rw [hzstar]
  have hrsq : ‖Pr‖ * ‖Pr‖ = ‖CFC.rpow A (2 * z.re)‖ := by
    calc
      ‖Pr‖ * ‖Pr‖ = ‖Matrix.conjTranspose Pr * Pr‖ := by
        simpa [Matrix.star_eq_conjTranspose] using
          (CStarRing.norm_star_mul_self (x := Pr)).symm
      _ = ‖CFC.rpow A (2 * z.re)‖ := by rw [hrstar]
  have hsq : ‖Pz‖ ^ 2 = ‖Pr‖ ^ 2 := by
    rw [pow_two, pow_two, hzsq, hrsq]
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).elim id (fun hneg => by
    have hpz := norm_nonneg Pz
    have hpr := norm_nonneg Pr
    nlinarith)

private theorem cMatrixPosDefComplexPower_l2OperatorNorm_bddAbove_of_affine_re_mem_Icc
    {A : CMatrix a} (hA : A.PosDef) (m c l u : ℝ) :
    BddAbove ((norm ∘
      (fun z : ℂ => cMatrixPosDefComplexPower A hA (((m : ℂ) * z + (c : ℂ))))) ''
      (Complex.re ⁻¹' Set.Icc l u)) := by
  let g : ℝ → ℝ := fun t =>
    ‖cMatrixPosDefComplexPower A hA (((m * t + c : ℝ) : ℂ))‖
  have hgcont : Continuous g := by
    have hcpow : Continuous fun t : ℝ =>
        cMatrixPosDefComplexPower A hA (((m * t + c : ℝ) : ℂ)) := by
      have hd := cMatrixPosDefComplexPower_differentiable hA
      exact hd.continuous.comp (by fun_prop)
    simpa [g] using hcpow.norm
  have hbddg : BddAbove (g '' Set.Icc l u) :=
    isCompact_Icc.bddAbove_image hgcont.continuousOn
  rcases hbddg with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  have harg_re : (((m : ℂ) * z + (c : ℂ))).re = m * z.re + c := by
    simp [Complex.mul_re]
  have hnorm :=
    cMatrixPosDefComplexPower_l2OperatorNorm_eq_re hA (((m : ℂ) * z + (c : ℂ)))
  calc
    ‖cMatrixPosDefComplexPower A hA (((m : ℂ) * z + (c : ℂ)))‖ =
        g z.re := by
          rw [hnorm]
          simp [g, harg_re]
    _ ≤ C := hC ⟨z.re, hz, rfl⟩

private theorem complex_exp_affine_norm_bddAbove_of_re_mem_Icc
    (m c C l u : ℝ) :
    BddAbove ((norm ∘
      (fun z : ℂ =>
        Complex.exp (((1 : ℂ) - ((m : ℂ) * z + (c : ℂ))) *
          ((Real.log C : ℝ) : ℂ)))) ''
      (Complex.re ⁻¹' Set.Icc l u)) := by
  let g : ℝ → ℝ := fun t =>
    ‖Complex.exp (((1 : ℂ) - (((m * t + c : ℝ) : ℂ))) *
      ((Real.log C : ℝ) : ℂ))‖
  have hgcont : Continuous g := by
    simpa [g] using
      ((Complex.continuous_exp.comp (by fun_prop : Continuous fun t : ℝ =>
        ((1 : ℂ) - (((m * t + c : ℝ) : ℂ))) *
          ((Real.log C : ℝ) : ℂ))).norm)
  have hbddg : BddAbove (g '' Set.Icc l u) :=
    isCompact_Icc.bddAbove_image hgcont.continuousOn
  rcases hbddg with ⟨D, hD⟩
  refine ⟨D, ?_⟩
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  have harg_re : (((m : ℂ) * z + (c : ℂ))).re = m * z.re + c := by
    simp [Complex.mul_re]
  have hnorm :
      ‖Complex.exp (((1 : ℂ) - ((m : ℂ) * z + (c : ℂ))) *
          ((Real.log C : ℝ) : ℂ))‖ =
        g z.re := by
    simp [g, harg_re, Complex.norm_exp, Complex.mul_re]
  calc
    ‖Complex.exp (((1 : ℂ) - ((m : ℂ) * z + (c : ℂ))) *
        ((Real.log C : ℝ) : ℂ))‖ = g z.re := hnorm
    _ ≤ D := hD ⟨z.re, hz, rfl⟩

/-- The normalized Beigi input path is bounded on the closed interpolation
strip. -/
theorem sandwichedRenyiBeigiNormalizedInputPath_bddAbove_closedStrip
    {A : CMatrix a} (hA : A.PosDef) (α C : ℝ) :
    BddAbove ((norm ∘ fun w : ℂ =>
      sandwichedRenyiBeigiNormalizedInputPath A hA α C (-(w / 2))) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  change BddAbove ((norm ∘ fun w : ℂ =>
      sandwichedRenyiBeigiNormalizedInputPath A hA α C (-(w / 2))) ''
      (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1))
  have hscalar : BddAbove ((norm ∘ fun w : ℂ =>
      Complex.exp (((1 : ℂ) - (((-α : ℝ) : ℂ) * w + (α : ℂ))) *
        ((Real.log C : ℝ) : ℂ))) ''
      (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1)) :=
    complex_exp_affine_norm_bddAbove_of_re_mem_Icc (-α) α C 0 1
  have hpow : BddAbove ((norm ∘ fun w : ℂ =>
      cMatrixPosDefComplexPower A hA (((-α : ℝ) : ℂ) * w + (α : ℂ))) ''
      (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1)) :=
    cMatrixPosDefComplexPower_l2OperatorNorm_bddAbove_of_affine_re_mem_Icc
      hA (-α) α 0 1
  have h := bddAbove_norm_smul_of_bddAbove
    (s := Complex.re ⁻¹' Set.Icc (0 : ℝ) 1) hscalar hpow
  convert h using 6
  ext w
  simp [sandwichedRenyiBeigiNormalizedInputPath]
  ring_nf

/-- The Beigi dual path is bounded on the closed interpolation strip. -/
theorem sandwichedRenyiBeigiDualPath_bddAbove_closedStrip
    {B : CMatrix b} (hB : B.PosDef) (q : ℝ) :
    BddAbove ((norm ∘ fun w : ℂ =>
      sandwichedRenyiBeigiDualPath B hB q (-(w / 2))) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  change BddAbove ((norm ∘ fun w : ℂ =>
      sandwichedRenyiBeigiDualPath B hB q (-(w / 2))) ''
      (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1))
  have hraw : BddAbove ((norm ∘ fun w : ℂ =>
      cMatrixPosDefComplexPower B hB (((q : ℂ) * w + (0 : ℂ)))) ''
      (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1)) :=
    cMatrixPosDefComplexPower_l2OperatorNorm_bddAbove_of_affine_re_mem_Icc
      hB q 0 0 1
  rcases hraw with ⟨D, hD⟩
  refine ⟨D, ?_⟩
  intro y hy
  rcases hy with ⟨w, hw, rfl⟩
  have harg : -(2 * (q : ℂ) * (-(w / 2))) = (q : ℂ) * w + 0 := by
    ring_nf
  have hle := hD ⟨w, hw, rfl⟩
  unfold sandwichedRenyiBeigiDualPath
  change ‖cMatrixPosDefComplexPower B hB (-(2 * (q : ℂ) * (-(w / 2))))‖ ≤ D
  rw [harg]
  simpa [Function.comp_def] using hle

private theorem cMatrixPosDefComplexPower_bddAbove_neg_half_closedStrip
    {A : CMatrix a} (hA : A.PosDef) :
    BddAbove ((norm ∘ fun w : ℂ =>
      cMatrixPosDefComplexPower A hA (-(w / 2))) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  change BddAbove ((norm ∘ fun w : ℂ =>
      cMatrixPosDefComplexPower A hA (-(w / 2))) ''
      (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1))
  let m : ℝ := -(1 / 2)
  have hraw :
      BddAbove ((norm ∘ fun w : ℂ =>
        cMatrixPosDefComplexPower A hA (((m : ℂ) * w + (0 : ℂ)))) ''
        (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1)) :=
    cMatrixPosDefComplexPower_l2OperatorNorm_bddAbove_of_affine_re_mem_Icc
      (A := A) hA (m := m) (c := 0) (l := 0) (u := 1)
  rcases hraw with ⟨D, hD⟩
  refine ⟨D, ?_⟩
  intro y hy
  rcases hy with ⟨w, hw, rfl⟩
  have harg : -(w / 2) = ((m : ℂ) * w + (0 : ℂ)) := by
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    calc
      -(w / 2) = -((1 / 2 : ℂ) * w) := by ring
      _ = ((m : ℂ) * w + (0 : ℂ)) := by
            simp [m, hhalf, neg_mul]
  have hle := hD ⟨w, hw, rfl⟩
  simpa [Function.comp_def, harg] using hle

private theorem cMatrixPosDefComplexPower_bddAbove_pos_half_closedStrip
    {A : CMatrix a} (hA : A.PosDef) :
    BddAbove ((norm ∘ fun w : ℂ =>
      cMatrixPosDefComplexPower A hA (w / 2)) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  change BddAbove ((norm ∘ fun w : ℂ =>
      cMatrixPosDefComplexPower A hA (w / 2)) ''
      (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1))
  let m : ℝ := 1 / 2
  have hraw : BddAbove ((norm ∘ fun w : ℂ =>
      cMatrixPosDefComplexPower A hA (((m : ℂ) * w + (0 : ℂ)))) ''
      (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1)) :=
    cMatrixPosDefComplexPower_l2OperatorNorm_bddAbove_of_affine_re_mem_Icc
      (A := A) hA (m := m) (c := 0) (l := 0) (u := 1)
  rcases hraw with ⟨D, hD⟩
  refine ⟨D, ?_⟩
  intro y hy
  rcases hy with ⟨w, hw, rfl⟩
  have harg : w / 2 = ((m : ℂ) * w + (0 : ℂ)) := by
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    calc
      w / 2 = (1 / 2 : ℂ) * w := by ring
      _ = ((m : ℂ) * w + (0 : ℂ)) := by
            simp [m, hhalf]
  have hle := hD ⟨w, hw, rfl⟩
  simpa [Function.comp_def, harg] using hle

/-- The normalized Beigi scalar trace family is bounded on the closed strip.

This discharges the remaining analytic side condition required by
Hadamard three-lines. The proof is purely a finite-dimensional boundedness
argument: each complex-power factor has norm depending only on the real part,
and the remaining operations are continuous linear maps and matrix products. -/
theorem sandwichedRenyiWeightedTraceFamily_normalizedBeigi_bddAbove_closedStrip
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (A : CMatrix a) (hA : A.PosDef)
    (B : CMatrix b) (hB : B.PosDef)
    (α q C : ℝ) :
    BddAbove
      ((norm ∘
        (fun w : ℂ =>
          sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
            (sandwichedRenyiBeigiNormalizedInputPath A hA α C)
            (sandwichedRenyiBeigiDualPath B hB q) (-(w / 2)))) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  let s : Set ℂ := Complex.HadamardThreeLines.verticalClosedStrip 0 1
  let Tpath : ℂ → CMatrix b := fun w =>
    cMatrixPosDefComplexPower τ.matrix hτ (-(w / 2))
  let Spath : ℂ → CMatrix a := fun w =>
    cMatrixPosDefComplexPower σ.matrix hσ (w / 2)
  let Apath : ℂ → CMatrix a := fun w =>
    sandwichedRenyiBeigiNormalizedInputPath A hA α C (-(w / 2))
  let Bpath : ℂ → CMatrix b := fun w =>
    sandwichedRenyiBeigiDualPath B hB q (-(w / 2))
  have hT : BddAbove ((norm ∘ Tpath) '' s) := by
    simpa [s, Tpath] using
      cMatrixPosDefComplexPower_bddAbove_neg_half_closedStrip hτ
  have hS : BddAbove ((norm ∘ Spath) '' s) := by
    simpa [s, Spath] using
      cMatrixPosDefComplexPower_bddAbove_pos_half_closedStrip hσ
  have hApath : BddAbove ((norm ∘ Apath) '' s) := by
    simpa [s, Apath] using
      sandwichedRenyiBeigiNormalizedInputPath_bddAbove_closedStrip hA α C
  have hBpath : BddAbove ((norm ∘ Bpath) '' s) := by
    simpa [s, Bpath] using
      sandwichedRenyiBeigiDualPath_bddAbove_closedStrip hB q
  have hSA : BddAbove ((norm ∘ fun w : ℂ => Spath w * Apath w) '' s) :=
    bddAbove_norm_mul_of_bddAbove hS hApath
  have hSAS : BddAbove ((norm ∘ fun w : ℂ => Spath w * Apath w * Spath w) '' s) :=
    bddAbove_norm_mul_of_bddAbove hSA hS
  have hK : BddAbove
      ((norm ∘ fun w : ℂ => MatrixMap.ofKraus K (Spath w * Apath w * Spath w)) ''
        s) :=
    bddAbove_norm_linearMap_of_bddAbove (MatrixMap.ofKraus K) hSAS
  have hTK : BddAbove
      ((norm ∘ fun w : ℂ => Tpath w *
        MatrixMap.ofKraus K (Spath w * Apath w * Spath w)) '' s) :=
    bddAbove_norm_mul_of_bddAbove hT hK
  have hTKT : BddAbove
      ((norm ∘ fun w : ℂ => Tpath w *
        MatrixMap.ofKraus K (Spath w * Apath w * Spath w) * Tpath w) '' s) :=
    bddAbove_norm_mul_of_bddAbove hTK hT
  have hPair : BddAbove
      ((norm ∘ fun w : ℂ =>
        (Tpath w * MatrixMap.ofKraus K (Spath w * Apath w * Spath w) *
          Tpath w) * Bpath w) '' s) :=
    bddAbove_norm_mul_of_bddAbove hTKT hBpath
  have hTrace : BddAbove
      ((norm ∘ fun w : ℂ =>
        (Matrix.traceLinearMap b ℂ ℂ)
          ((Tpath w * MatrixMap.ofKraus K (Spath w * Apath w * Spath w) *
            Tpath w) * Bpath w)) '' s) :=
    bddAbove_norm_linearMap_of_bddAbove (Matrix.traceLinearMap b ℂ ℂ) hPair
  simpa [s, Tpath, Spath, Apath, Bpath,
    sandwichedRenyiWeightedTraceFamily, sandwichedRenyiWeightedMapComplex,
    Matrix.mul_assoc] using hTrace

end BeigiClosedStripBoundedness

/-- Concrete left-boundary estimate for the normalized Beigi paths, reducing
the remaining endpoint work to the normalized input-path trace-norm bound.

All channel and reference-factor algebra is discharged here: the Kraus map is
used only through trace preservation, and the boundary complex powers are used
only through their contraction identities. -/
theorem sandwichedRenyiWeightedTraceFamily_normalizedBeigi_left_bound
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (A : CMatrix a) (hA : A.PosDef)
    (B : CMatrix b) (hB : B.PosDef)
    (α q C : ℝ)
    (hAtrace : ∀ z : ℂ, z.re = 0 →
      traceNorm (sandwichedRenyiBeigiNormalizedInputPath A hA α C z) ≤ C) :
    ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
          (sandwichedRenyiBeigiNormalizedInputPath A hA α C)
          (sandwichedRenyiBeigiDualPath B hB q) z‖ ≤ C := by
  intro z hzmem
  have hz : z.re = 0 := by simpa using hzmem
  have hS : Matrix.conjTranspose (cMatrixPosDefComplexPower σ.matrix hσ (-z)) *
      cMatrixPosDefComplexPower σ.matrix hσ (-z) = 1 := by
    have hneg : (-z).re = 0 := by simp [hz]
    simpa using cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero hσ hneg
  have hT : Matrix.conjTranspose (cMatrixPosDefComplexPower τ.matrix hτ z) *
      cMatrixPosDefComplexPower τ.matrix hτ z = 1 := by
    simpa using cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero hτ hz
  have hBcontraction :
      Matrix.conjTranspose (sandwichedRenyiBeigiDualPath B hB q z) *
          sandwichedRenyiBeigiDualPath B hB q z ≤ 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (show star (sandwichedRenyiBeigiDualPath B hB q z) *
          sandwichedRenyiBeigiDualPath B hB q z ≤ 1 from by
        rw [sandwichedRenyiBeigiDualPath_star_mul_self_of_re_eq_zero hB q hz])
  exact sandwichedRenyiWeightedTraceFamily_left_bound_of_traceNorm
    σ hσ τ hτ K hTP
    (sandwichedRenyiBeigiNormalizedInputPath A hA α C)
    (sandwichedRenyiBeigiDualPath B hB q) C z
    hS hT hBcontraction (hAtrace z hz)

/-- Fully discharged left-boundary estimate for the normalized Beigi paths.

This is the `p = 1` endpoint in the α > 1 Beigi interpolation spine, up to the
standard positivity of the normalizing Schatten value. -/
theorem sandwichedRenyiWeightedTraceFamily_normalizedBeigi_left_bound_of_pos
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (A : CMatrix a) (hA : A.PosDef)
    (B : CMatrix b) (hB : B.PosDef)
    {α q : ℝ} (hα : 0 < α)
    (hCpos : 0 < psdSchattenPNorm A hA.posSemidef ⟨α, hα⟩) :
    ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
          (sandwichedRenyiBeigiNormalizedInputPath A hA α
            (psdSchattenPNorm A hA.posSemidef ⟨α, hα⟩))
          (sandwichedRenyiBeigiDualPath B hB q) z‖ ≤
        psdSchattenPNorm A hA.posSemidef ⟨α, hα⟩ := by
  exact sandwichedRenyiWeightedTraceFamily_normalizedBeigi_left_bound
    σ hσ τ hτ K hTP A hA B hB α q
    (psdSchattenPNorm A hA.posSemidef ⟨α, hα⟩)
    (fun z hz =>
      sandwichedRenyiBeigiNormalizedInputPath_traceNorm_le_of_re_eq_zero
        hA hα rfl hCpos hz)

/-- Right-boundary trace-family estimate from the weighted output
operator-contraction condition.

This isolates the remaining `p = ∞` Beigi endpoint: once the weighted output
matrix is in the operator unit ball after scaling by `C`, the dual path's
trace-norm unit-ball condition gives the scalar trace-family bound. -/
theorem sandwichedRenyiWeightedTraceFamily_right_bound_of_scaled_contraction
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (Apath : ℂ → CMatrix a) (Bpath : ℂ → CMatrix b)
    {C : ℝ} (hCpos : 0 < C) :
    (∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
      Matrix.conjTranspose (((C : ℂ)⁻¹) •
          sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z (Apath z)) *
        (((C : ℂ)⁻¹) •
          sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z (Apath z)) ≤ 1) →
    (∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
      traceNorm (Bpath z) ≤ 1) →
    ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath z‖ ≤ C := by
  intro hW hB z hz
  let W : CMatrix b := sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z (Apath z)
  let Y : CMatrix b := Bpath z
  have hpair :=
    MatrixMap.abs_trace_mul_le_of_traceNorm_le_one_of_scaled_contraction
      Y W hCpos (by simpa [Y] using hB z hz) (by simpa [W] using hW z hz)
  simpa [sandwichedRenyiWeightedTraceFamily, W, Y, Complex.abs] using hpair

/-- Concrete normalized Beigi right-boundary handoff.

The theorem discharges the dual-path trace-norm endpoint from the `q`-unit-ball
hypothesis and leaves only the source-critical weighted-map operator
contraction as an assumption. -/
theorem sandwichedRenyiWeightedTraceFamily_normalizedBeigi_right_bound_of_scaled_contraction
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (A : CMatrix a) (hA : A.PosDef)
    (B : CMatrix b) (hB : B.PosDef)
    {α q : ℝ} (hα : 0 < α)
    (hCpos : 0 < psdSchattenPNorm A hA.posSemidef ⟨α, hα⟩)
    (hBq : psdTracePower B hB.posSemidef q ≤ 1)
    (hW : ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
      Matrix.conjTranspose (((psdSchattenPNorm A hA.posSemidef ⟨α, hα⟩ : ℂ)⁻¹) •
          sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z
            (sandwichedRenyiBeigiNormalizedInputPath A hA α
              (psdSchattenPNorm A hA.posSemidef ⟨α, hα⟩) z)) *
        (((psdSchattenPNorm A hA.posSemidef ⟨α, hα⟩ : ℂ)⁻¹) •
          sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z
            (sandwichedRenyiBeigiNormalizedInputPath A hA α
              (psdSchattenPNorm A hA.posSemidef ⟨α, hα⟩) z)) ≤ 1) :
    ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
          (sandwichedRenyiBeigiNormalizedInputPath A hA α
            (psdSchattenPNorm A hA.posSemidef ⟨α, hα⟩))
          (sandwichedRenyiBeigiDualPath B hB q) z‖ ≤
        psdSchattenPNorm A hA.posSemidef ⟨α, hα⟩ := by
  exact sandwichedRenyiWeightedTraceFamily_right_bound_of_scaled_contraction
    σ hσ τ hτ K
    (sandwichedRenyiBeigiNormalizedInputPath A hA α
      (psdSchattenPNorm A hA.posSemidef ⟨α, hα⟩))
    (sandwichedRenyiBeigiDualPath B hB q)
    hCpos hW
    (fun z hz =>
      sandwichedRenyiBeigiDualPath_traceNorm_le_one_of_re_eq_neg_half
        hB hBq (by simpa using hz))

/-- Heisenberg-adjoint boundary formula for the complex rotated Kraus family.

The adjoint of the complex-rotated family at the identity is the original
Kraus adjoint evaluated at `τ^(2 Re z)`, conjugated by the input reference
factor `σ^{-z}`. This is the algebraic core behind the interpolation endpoint
estimates. -/
theorem sandwichedRenyiRotatedKrausComplex_krausAdjoint_one
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ) (z : ℂ) :
    MatrixMap.krausAdjoint
        (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z) (1 : CMatrix b) =
      star (cMatrixPosDefComplexPower σ.matrix hσ (-z)) *
        MatrixMap.krausAdjoint K (CFC.rpow τ.matrix (2 * z.re)) *
          cMatrixPosDefComplexPower σ.matrix hσ (-z) := by
  let T : CMatrix b := cMatrixPosDefComplexPower τ.matrix hτ z
  let S : CMatrix a := cMatrixPosDefComplexPower σ.matrix hσ (-z)
  have hTpow : star T * T = CFC.rpow τ.matrix (2 * z.re) := by
    simpa [T] using cMatrixPosDefComplexPower_star_mul_self hτ z
  change MatrixMap.krausAdjoint (fun k => T * K k * S) (1 : CMatrix b) =
    star S * MatrixMap.krausAdjoint K (CFC.rpow τ.matrix (2 * z.re)) * S
  unfold MatrixMap.krausAdjoint
  have hterms :
      (∑ k,
        Matrix.conjTranspose (T * K k * S) * (1 : CMatrix b) *
          (T * K k * S)) =
      ∑ k,
        star S * (Matrix.conjTranspose (K k) *
          CFC.rpow τ.matrix (2 * z.re) * K k) * S := by
    apply Finset.sum_congr rfl
    intro k _
    have hTct : Matrix.conjTranspose T = star T := by
      rw [← Matrix.star_eq_conjTranspose]
    have hSct : Matrix.conjTranspose S = star S := by
      rw [← Matrix.star_eq_conjTranspose]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSct, hTct]
    calc
      (star S * (Matrix.conjTranspose (K k) * star T)) * (1 : CMatrix b) *
          (T * K k * S) =
          star S * Matrix.conjTranspose (K k) * (star T * T) * K k * S := by
            simp [Matrix.mul_assoc]
      _ = star S * Matrix.conjTranspose (K k) *
          CFC.rpow τ.matrix (2 * z.re) * K k * S := by
            rw [hTpow]
      _ = star S * (Matrix.conjTranspose (K k) *
          CFC.rpow τ.matrix (2 * z.re) * K k) * S := by
            simp [Matrix.mul_assoc]
  rw [hterms]
  simp [Matrix.mul_assoc, Finset.sum_mul, Finset.mul_sum]

/-- Schrödinger-side reference orbit for the complex rotated Kraus family.

If the original Kraus family sends the input reference state to `τ`, then the
complex-rotated family sends the reference power `σ^(1 + 2 Re z)` to
`τ^(1 + 2 Re z)`.  At the real interpolation point
`z = (1 - α)/(2α)`, this specializes to the `σ^(1/α) ↦ τ^(1/α)` endpoint.
-/
theorem sandwichedRenyiRotatedKrausComplex_apply_referencePower
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (hτK : MatrixMap.ofKraus K σ.matrix = τ.matrix) (z : ℂ) :
    MatrixMap.ofKraus (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z)
        (CFC.rpow σ.matrix (1 + 2 * z.re)) =
      CFC.rpow τ.matrix (1 + 2 * z.re) := by
  let T : CMatrix b := cMatrixPosDefComplexPower τ.matrix hτ z
  let S : CMatrix a := cMatrixPosDefComplexPower σ.matrix hσ (-z)
  have hSσ :
      S * CFC.rpow σ.matrix (1 + 2 * z.re) * star S = σ.matrix := by
    have h :=
      cMatrixPosDefComplexPower_mul_rpow_mul_star hσ (-z) (1 + 2 * z.re)
    have hexp : 1 + 2 * z.re + 2 * (-z).re = (1 : ℝ) := by
      simp
    rw [hexp] at h
    have hpow_one : CFC.rpow σ.matrix (1 : ℝ) = σ.matrix :=
      CFC.rpow_one σ.matrix
        (ha := Matrix.nonneg_iff_posSemidef.mpr hσ.posSemidef)
    simpa [S] using h.trans hpow_one
  have hTτ :
      T * τ.matrix * star T = CFC.rpow τ.matrix (1 + 2 * z.re) := by
    have h := cMatrixPosDefComplexPower_mul_rpow_mul_star hτ z (1 : ℝ)
    have hpow_one : CFC.rpow τ.matrix (1 : ℝ) = τ.matrix :=
      CFC.rpow_one τ.matrix
        (ha := Matrix.nonneg_iff_posSemidef.mpr hτ.posSemidef)
    rw [hpow_one] at h
    simpa [T, add_comm] using h
  calc
    MatrixMap.ofKraus (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z)
        (CFC.rpow σ.matrix (1 + 2 * z.re)) =
        T * MatrixMap.ofKraus K
            (S * CFC.rpow σ.matrix (1 + 2 * z.re) * star S) * star T := by
          simpa [sandwichedRenyiRotatedKrausComplex, T, S] using
            MatrixMap.ofKraus_conjugated_apply K T S
              (CFC.rpow σ.matrix (1 + 2 * z.re))
    _ = T * MatrixMap.ofKraus K σ.matrix * star T := by rw [hSσ]
    _ = T * τ.matrix * star T := by rw [hτK]
    _ = CFC.rpow τ.matrix (1 + 2 * z.re) := hTτ

/-- On the imaginary boundary line, the complex rotated Kraus family remains
trace-preserving whenever the original Kraus family is trace-preserving.

This is one of the genuine Riesz-Thorin endpoint facts for the α > 1 route:
the reference complex powers are unitary on `Re z = 0`, so left and right
reference rotations do not change the Kraus completeness relation. -/
theorem sandwichedRenyiRotatedKrausComplex_isTracePreserving_of_re_eq_zero
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    {z : ℂ} (hz : z.re = 0) :
    MatrixMap.IsTracePreserving
      (MatrixMap.ofKraus (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z)) := by
  let T : CMatrix b := cMatrixPosDefComplexPower τ.matrix hτ z
  let S : CMatrix a := cMatrixPosDefComplexPower σ.matrix hσ (-z)
  have hTunit : star T * T = (1 : CMatrix b) := by
    simpa [T] using cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero hτ hz
  have hneg_re : (-z).re = 0 := by simp [hz]
  have hSunit : star S * S = (1 : CMatrix a) := by
    simpa [S] using cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero hσ hneg_re
  have hKone : MatrixMap.krausAdjoint K (1 : CMatrix b) = (1 : CMatrix a) :=
    MatrixMap.krausAdjoint_one_of_tracePreserving K hTP
  apply MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one
  change MatrixMap.krausAdjoint (fun k => T * K k * S) (1 : CMatrix b) = 1
  calc
    MatrixMap.krausAdjoint (fun k => T * K k * S) (1 : CMatrix b) =
        star S * MatrixMap.krausAdjoint K (1 : CMatrix b) * S := by
          unfold MatrixMap.krausAdjoint
          have hterms :
              (∑ k,
                Matrix.conjTranspose (T * K k * S) * (1 : CMatrix b) *
                  (T * K k * S)) =
              ∑ k,
                star S * (Matrix.conjTranspose (K k) * (1 : CMatrix b) * K k) * S := by
            apply Finset.sum_congr rfl
            intro k _
            have hTct : Matrix.conjTranspose T = star T := by
              rw [← Matrix.star_eq_conjTranspose]
            have hSct : Matrix.conjTranspose S = star S := by
              rw [← Matrix.star_eq_conjTranspose]
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSct, hTct]
            calc
              (star S * (Matrix.conjTranspose (K k) * star T)) * (1 : CMatrix b) *
                  (T * K k * S) =
                  star S * Matrix.conjTranspose (K k) * (star T * T) * K k * S := by
                    simp [Matrix.mul_assoc]
              _ = star S * Matrix.conjTranspose (K k) * (1 : CMatrix b) * K k * S := by
                    rw [hTunit]
              _ = star S * (Matrix.conjTranspose (K k) * (1 : CMatrix b) * K k) * S := by
                    simp [Matrix.mul_assoc]
          rw [hterms]
          simp [Matrix.mul_assoc, Finset.sum_mul, Finset.mul_sum]
    _ = star S * 1 * S := by rw [hKone]
    _ = 1 := by simpa [Matrix.mul_assoc] using hSunit

/-- Trace-norm contraction on the `Re z = 0` endpoint of the Beigi weighted
interpolation family.

The previous lemma identifies this endpoint as trace-preserving; the general
finite-dimensional Kraus trace-norm contraction then gives the `p = 1`
endpoint. -/
theorem sandwichedRenyiRotatedKrausComplex_traceNorm_contract_of_re_eq_zero
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    {z : ℂ} (hz : z.re = 0) (X : CMatrix a) :
    traceNorm
      (MatrixMap.ofKraus (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z) X) ≤
      traceNorm X := by
  exact MatrixMap.traceNorm_contract_ofKraus_of_tracePreserving
    (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z)
    (sandwichedRenyiRotatedKrausComplex_isTracePreserving_of_re_eq_zero
      σ hσ τ hτ K hTP hz)
    X

/-- Unital endpoint for the local complex rotated family.

For the current convention `L_z = τ^z K σ^{-z}`, the Beigi `p = ∞` endpoint is
the vertical line `Re z = -1/2`: the reference orbit sends `σ^(1+2 Re z)` to
`τ^(1+2 Re z)`, hence sends `1` to `1` on that boundary. -/
theorem sandwichedRenyiRotatedKrausComplex_isUnital_of_re_eq_neg_half
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (hτK : MatrixMap.ofKraus K σ.matrix = τ.matrix)
    {z : ℂ} (hz : z.re = -(1 / 2 : ℝ)) :
    MatrixMap.ofKraus (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z)
      (1 : CMatrix a) = (1 : CMatrix b) := by
  have h :=
    sandwichedRenyiRotatedKrausComplex_apply_referencePower
      σ hσ τ hτ K hτK z
  have hexp : 1 + 2 * z.re = (0 : ℝ) := by
    rw [hz]
    ring
  have hσpow :
      CFC.rpow σ.matrix (1 + 2 * z.re) = (1 : CMatrix a) := by
    rw [hexp]
    exact CFC.rpow_zero σ.matrix
      (ha := Matrix.nonneg_iff_posSemidef.mpr hσ.posSemidef)
  have hτpow :
      CFC.rpow τ.matrix (1 + 2 * z.re) = (1 : CMatrix b) := by
    rw [hexp]
    exact CFC.rpow_zero τ.matrix
      (ha := Matrix.nonneg_iff_posSemidef.mpr hτ.posSemidef)
  rwa [hσpow, hτpow] at h

open scoped Matrix.Norms.L2Operator in
/-- Operator-norm contraction on the `Re z = -1/2` endpoint of the local Beigi
interpolation family.

For the convention `L_z = τ^z K σ^{-z}`, this is the `p = ∞` boundary: the
previous lemma proves the endpoint map is unital, and finite-dimensional
Kadison-Schwarz gives contraction on the matrix unit ball. -/
theorem sandwichedRenyiRotatedKrausComplex_opNorm_contract_of_re_eq_neg_half
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hτK : MatrixMap.ofKraus K σ.matrix = τ.matrix)
    {z : ℂ} (hz : z.re = -(1 / 2 : ℝ))
    {X : CMatrix a} (hX : Matrix.conjTranspose X * X ≤ 1) :
    ‖MatrixMap.ofKraus (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z) X‖ ≤
      (1 : ℝ) := by
  exact MatrixMap.opNorm_contract_ofKraus_of_unital_on_unitBall
    (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z)
    (sandwichedRenyiRotatedKrausComplex_isUnital_of_re_eq_neg_half
      σ hσ τ hτ K hτK hz)
    hX

open scoped Matrix.Norms.L2Operator in
/-- Ordinary operator-norm contraction on the `Re z = -1/2` endpoint of the
local Beigi interpolation family. -/
theorem sandwichedRenyiRotatedKrausComplex_opNorm_contract_of_re_eq_neg_half'
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hτK : MatrixMap.ofKraus K σ.matrix = τ.matrix)
    {z : ℂ} (hz : z.re = -(1 / 2 : ℝ)) (X : CMatrix a) :
    ‖MatrixMap.ofKraus (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z) X‖ ≤
      ‖X‖ := by
  exact MatrixMap.opNorm_contract_ofKraus_of_unital
    (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K z)
    (sandwichedRenyiRotatedKrausComplex_isUnital_of_re_eq_neg_half
      σ hσ τ hτ K hτK hz)
    X

open scoped Matrix.Norms.L2Operator in
/-- Beigi `p = ∞` endpoint for the normalized source-faithful weighted map,
stated as an operator-norm contraction.

The proof factors the analytic boundary map through the real `z = -1/2`
unital Kraus endpoint and imaginary reference rotations, all of which are
operator contractions. -/
theorem sandwichedRenyiWeightedMapComplex_normalizedBeigi_scaled_opNorm_le_of_re_eq_neg_half
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hτK : MatrixMap.ofKraus K σ.matrix = τ.matrix)
    {A : CMatrix a} (hA : A.PosDef) (α C : ℝ) (hCpos : 0 < C)
    {z : ℂ} (hz : z.re = -(1 / 2 : ℝ)) :
    ‖((C : ℂ)⁻¹) •
        sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z
          (sandwichedRenyiBeigiNormalizedInputPath A hA α C z)‖ ≤
      (1 : ℝ) := by
  let X0 : CMatrix a :=
    ((C : ℂ)⁻¹) • sandwichedRenyiBeigiNormalizedInputPath A hA α C z
  let u : ℂ := z + ((1 / 2 : ℝ) : ℂ)
  let Uτ : CMatrix b := cMatrixPosDefComplexPower τ.matrix hτ u
  let Uσ : CMatrix a := cMatrixPosDefComplexPower σ.matrix hσ (-u)
  let M : CMatrix b :=
    MatrixMap.ofKraus
      (sandwichedRenyiRotatedKrausComplex σ hσ τ hτ K
        (((-(1 / 2 : ℝ)) : ℝ) : ℂ))
      (Uσ * X0 * Uσ)
  have hu_re : u.re = 0 := by
    simp [u, hz]
  have hneg_u_re : (-u).re = 0 := by
    simp [hu_re]
  have hUτ : ‖Uτ‖ ≤ (1 : ℝ) :=
    MatrixMap.cMatrix_l2OperatorNorm_le_one_of_conjTranspose_mul_self_le_one Uτ
      (cMatrixPosDefComplexPower_contraction_of_re_eq_zero hτ hu_re)
  have hX0 :
      Matrix.conjTranspose X0 * X0 ≤ (1 : CMatrix a) := by
    simpa [X0] using
      sandwichedRenyiBeigiNormalizedInputPath_scaled_contraction_of_re_eq_neg_half
        hA α C hCpos hz
  have hV :
      Matrix.conjTranspose (Uσ * X0 * Uσ) * (Uσ * X0 * Uσ) ≤
        (1 : CMatrix a) :=
    cMatrixPosDefComplexPower_mul_mul_contraction_of_re_eq_zero
      hσ hneg_u_re hX0
  have hz0 : (((( -(1 / 2 : ℝ)) : ℝ) : ℂ)).re = -(1 / 2 : ℝ) := by
    norm_num
  have hMnorm : ‖M‖ ≤ (1 : ℝ) := by
    simpa [M] using
      sandwichedRenyiRotatedKrausComplex_opNorm_contract_of_re_eq_neg_half
        σ hσ τ hτ K hτK hz0 hV
  have hlinear :
      ((C : ℂ)⁻¹) •
          sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z
            (sandwichedRenyiBeigiNormalizedInputPath A hA α C z) =
        sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z X0 := by
    simp [X0]
  have hfactor :
      sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z X0 =
        Uτ * M * Uτ := by
    simpa [u, Uτ, Uσ, M] using
      sandwichedRenyiWeightedMapComplex_eq_imaginary_conj_of_re_eq_neg_half
        σ hσ τ hτ K z X0
  calc
    ‖((C : ℂ)⁻¹) •
        sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z
          (sandwichedRenyiBeigiNormalizedInputPath A hA α C z)‖ =
        ‖sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z X0‖ := by
          rw [hlinear]
    _ = ‖Uτ * M * Uτ‖ := by rw [hfactor]
    _ ≤ ‖Uτ‖ * (‖M‖ * ‖Uτ‖) := by
          calc
            ‖Uτ * M * Uτ‖ ≤ ‖Uτ * M‖ * ‖Uτ‖ := norm_mul_le _ _
            _ ≤ (‖Uτ‖ * ‖M‖) * ‖Uτ‖ := by
                  exact mul_le_mul_of_nonneg_right (norm_mul_le Uτ M) (norm_nonneg Uτ)
            _ = ‖Uτ‖ * (‖M‖ * ‖Uτ‖) := by ring
    _ ≤ (1 : ℝ) := by
          have hMU : ‖M‖ * ‖Uτ‖ ≤ (1 : ℝ) * (1 : ℝ) :=
            mul_le_mul hMnorm hUτ (norm_nonneg Uτ) zero_le_one
          have hprod : ‖Uτ‖ * (‖M‖ * ‖Uτ‖) ≤ (1 : ℝ) * (1 : ℝ) :=
            mul_le_mul hUτ (by simpa using hMU)
              (mul_nonneg (norm_nonneg M) (norm_nonneg Uτ)) zero_le_one
          simpa using hprod

/-- Beigi `p = ∞` endpoint in the matrix unit-ball form used by the local
trace-norm variational handoff. -/
theorem sandwichedRenyiWeightedMapComplex_normalizedBeigi_scaled_contraction_of_re_eq_neg_half
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hτK : MatrixMap.ofKraus K σ.matrix = τ.matrix)
    {A : CMatrix a} (hA : A.PosDef) (α C : ℝ) (hCpos : 0 < C)
    {z : ℂ} (hz : z.re = -(1 / 2 : ℝ)) :
    Matrix.conjTranspose (((C : ℂ)⁻¹) •
        sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z
          (sandwichedRenyiBeigiNormalizedInputPath A hA α C z)) *
      (((C : ℂ)⁻¹) •
        sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z
          (sandwichedRenyiBeigiNormalizedInputPath A hA α C z)) ≤ 1 := by
  exact MatrixMap.cMatrix_conjTranspose_mul_self_le_one_of_l2OperatorNorm_le_one _
    (sandwichedRenyiWeightedMapComplex_normalizedBeigi_scaled_opNorm_le_of_re_eq_neg_half
      σ hσ τ hτ K hτK hA α C hCpos hz)

/-- Beigi-strip three-lines handoff for the rotated Kraus trace pairing.

This is the remaining interpolation bridge after the endpoint contractions are
available.  It does not assume the target DPI or q-ball contraction: it says
that any source-faithful scalar family on the local strip, whose middle point
is the rotated-Kraus trace pairing and whose two boundary lines are bounded by
the candidate PSD Schatten norm, gives the required trace-pairing bound. -/
theorem sandwichedRenyi_tracePairingBound_of_beigiInterpolationFamily
    (σ : State a) (_hσ : σ.matrix.PosDef)
    (τ : State b) (_hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosSemidef) {B : CMatrix b} (_hB : B.PosSemidef)
    (f : ℂ → ℂ)
    (hCpos : 0 < psdSchattenPNorm A hA ⟨α, hpq.pos⟩)
    (hd : DiffContOnCl ℂ (fun w : ℂ => f (-(w / 2)))
      (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hBounded : BddAbove ((norm ∘ (fun w : ℂ => f (-(w / 2)))) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ),
      ‖f z‖ ≤ psdSchattenPNorm A hA ⟨α, hpq.pos⟩)
    (hright : ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
      ‖f z‖ ≤ psdSchattenPNorm A hA ⟨α, hpq.pos⟩)
    (htarget :
      f (-(((1 / q : ℝ) : ℂ) / 2)) =
        ((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace) :
    (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace).re ≤
      psdSchattenPNorm A hA ⟨α, hpq.pos⟩ := by
  have hθ := holderConjugate_inv_right_mem_unit_interval hpq
  have hnorm :
      ‖f (-(((1 / q : ℝ) : ℂ) / 2))‖ ≤ psdSchattenPNorm A hA ⟨α, hpq.pos⟩ :=
    complex_three_lines_const_bound_neg_half_strip
      (f := f) (θ := 1 / q) (C := psdSchattenPNorm A hA ⟨α, hpq.pos⟩)
      hθ.1 hθ.2 hCpos hd hBounded hleft hright
  calc
    (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace).re =
        (f (-(((1 / q : ℝ) : ℂ) / 2))).re := by
          rw [htarget]
    _ ≤ ‖f (-(((1 / q : ℝ) : ℂ) / 2))‖ := Complex.re_le_norm _
    _ ≤ psdSchattenPNorm A hA ⟨α, hpq.pos⟩ := hnorm

/-- Source-faithful Beigi weighted-map version of the three-lines handoff.

This removes the remaining target-equality bookkeeping from the interpolation
step: once the weighted trace family has analytic control and endpoint bounds,
it yields the trace-pairing bound needed for the rotated-adjoint q-ball
contraction. -/
theorem sandwichedRenyi_tracePairingBound_of_weightedInterpolationFamily
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosSemidef) {B : CMatrix b} (hB : B.PosSemidef)
    (Apath : ℂ → CMatrix a) (Bpath : ℂ → CMatrix b)
    (hAθ : Apath (-(((1 / q : ℝ) : ℂ) / 2)) = A)
    (hBθ : Bpath (-(((1 / q : ℝ) : ℂ) / 2)) = B)
    (hCpos : 0 < psdSchattenPNorm A hA ⟨α, hpq.pos⟩)
    (hd : DiffContOnCl ℂ
      (fun w : ℂ =>
        sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath (-(w / 2)))
      (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hBounded : BddAbove
      ((norm ∘
        (fun w : ℂ =>
          sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath (-(w / 2)))) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath z‖ ≤
        psdSchattenPNorm A hA ⟨α, hpq.pos⟩)
    (hright : ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath z‖ ≤
        psdSchattenPNorm A hA ⟨α, hpq.pos⟩) :
    (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace).re ≤
      psdSchattenPNorm A hA ⟨α, hpq.pos⟩ := by
  exact sandwichedRenyi_tracePairingBound_of_beigiInterpolationFamily
    σ hσ τ hτ K α q hpq hA hB
    (sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K Apath Bpath)
    hCpos hd hBounded hleft hright
    (sandwichedRenyiWeightedTraceFamily_holderTheta_target
      σ hσ τ hτ K α q hpq Apath Bpath A B hAθ hBθ)

/-- Concrete Beigi-path handoff from endpoint estimates to the trace-pairing
bound.

This theorem fixes the source-faithful analytic paths
`A_z = A^(2αz+α)` and `B_z = B^(-2qz)`, proves their analytic condition and
target-point identities internally, and leaves only the genuine endpoint
boundedness estimates as assumptions. -/
theorem sandwichedRenyi_tracePairingBound_of_beigiPaths
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosDef) {B : CMatrix b} (hB : B.PosDef)
    (hCpos : 0 < psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩)
    (hBounded : BddAbove
      ((norm ∘
        (fun w : ℂ =>
          sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
            (sandwichedRenyiBeigiInputPath A hA α)
            (sandwichedRenyiBeigiDualPath B hB q) (-(w / 2)))) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
          (sandwichedRenyiBeigiInputPath A hA α)
          (sandwichedRenyiBeigiDualPath B hB q) z‖ ≤
        psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩)
    (hright : ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
          (sandwichedRenyiBeigiInputPath A hA α)
          (sandwichedRenyiBeigiDualPath B hB q) z‖ ≤
        psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩) :
    (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace).re ≤
      psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩ := by
  exact sandwichedRenyi_tracePairingBound_of_weightedInterpolationFamily
    σ hσ τ hτ K α q hpq hA.posSemidef hB.posSemidef
    (sandwichedRenyiBeigiInputPath A hA α)
    (sandwichedRenyiBeigiDualPath B hB q)
    (sandwichedRenyiBeigiInputPath_holderTheta hA hpq)
    (sandwichedRenyiBeigiDualPath_holderTheta hB hpq)
    hCpos
    (sandwichedRenyiWeightedTraceFamily_diffContOnCl_beigiPaths
      σ hσ τ hτ K A hA B hB α q)
    hBounded hleft hright

/-- Normalized concrete Beigi-path handoff from endpoint estimates to the
trace-pairing bound.

Compared with `sandwichedRenyi_tracePairingBound_of_beigiPaths`, the input path
is scaled by the Schatten `α`-norm of `A`.  This is the source-faithful
normalization used in the Beigi weighted-`L_p` proof: the lower endpoint is
bounded by `||A||_α` rather than by `Tr(A^α)`. -/
theorem sandwichedRenyi_tracePairingBound_of_normalizedBeigiPaths
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosDef) {B : CMatrix b} (hB : B.PosDef)
    (hCpos : 0 < psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩)
    (hBounded : BddAbove
      ((norm ∘
        (fun w : ℂ =>
          sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
            (sandwichedRenyiBeigiNormalizedInputPath A hA α
              (psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩))
            (sandwichedRenyiBeigiDualPath B hB q) (-(w / 2)))) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
          (sandwichedRenyiBeigiNormalizedInputPath A hA α
            (psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩))
          (sandwichedRenyiBeigiDualPath B hB q) z‖ ≤
        psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩)
    (hright : ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
      ‖sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
          (sandwichedRenyiBeigiNormalizedInputPath A hA α
            (psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩))
          (sandwichedRenyiBeigiDualPath B hB q) z‖ ≤
        psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩) :
    (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace).re ≤
      psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩ := by
  exact sandwichedRenyi_tracePairingBound_of_weightedInterpolationFamily
    σ hσ τ hτ K α q hpq hA.posSemidef hB.posSemidef
    (sandwichedRenyiBeigiNormalizedInputPath A hA α
      (psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩))
    (sandwichedRenyiBeigiDualPath B hB q)
    (sandwichedRenyiBeigiNormalizedInputPath_holderTheta hA hpq)
    (sandwichedRenyiBeigiDualPath_holderTheta hB hpq)
    hCpos
    (sandwichedRenyiWeightedTraceFamily_diffContOnCl_normalizedBeigiPaths
      σ hσ τ hτ K A hA B hB α q (psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩))
    hBounded hleft hright

/-- Normalized Beigi trace-pairing bound from the two endpoint estimates, with
the `p = ∞` endpoint isolated as the weighted-map scaled-contraction theorem.

This is the source-aligned bridge immediately before the final
Riesz-Thorin/Beigi contraction step: it discharges analyticity and the complete
`p = 1` boundary, and it discharges the dual-path part of the `p = ∞`
boundary from the `q`-unit-ball hypothesis. -/
theorem sandwichedRenyi_tracePairingBound_of_normalizedBeigi_weightedEndpoint
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosDef) {B : CMatrix b} (hB : B.PosDef)
    (hCpos : 0 < psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩)
    (hBq : psdTracePower B hB.posSemidef q ≤ 1)
    (hBounded : BddAbove
      ((norm ∘
        (fun w : ℂ =>
          sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
            (sandwichedRenyiBeigiNormalizedInputPath A hA α
              (psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩))
            (sandwichedRenyiBeigiDualPath B hB q) (-(w / 2)))) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hWeightedEndpoint :
      ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ),
        Matrix.conjTranspose (((psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩ : ℂ)⁻¹) •
            sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z
              (sandwichedRenyiBeigiNormalizedInputPath A hA α
                (psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩) z)) *
          (((psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩ : ℂ)⁻¹) •
            sandwichedRenyiWeightedMapComplex σ hσ τ hτ K z
              (sandwichedRenyiBeigiNormalizedInputPath A hA α
                (psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩) z)) ≤ 1) :
    (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace).re ≤
      psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩ := by
  exact sandwichedRenyi_tracePairingBound_of_normalizedBeigiPaths
    σ hσ τ hτ K α q hpq hA hB hCpos hBounded
    (sandwichedRenyiWeightedTraceFamily_normalizedBeigi_left_bound_of_pos
      σ hσ τ hτ K hTP A hA B hB hpq.pos hCpos)
    (sandwichedRenyiWeightedTraceFamily_normalizedBeigi_right_bound_of_scaled_contraction
      σ hσ τ hτ K A hA B hB hpq.pos hCpos hBq hWeightedEndpoint)

/-- Normalized Beigi trace-pairing bound with the `p = ∞` weighted endpoint
fully discharged.

The only remaining analytic side condition is the standard closed-strip
boundedness hypothesis required by the local Hadamard three-lines theorem. -/
theorem sandwichedRenyi_tracePairingBound_of_normalizedBeigi
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (hτK : MatrixMap.ofKraus K σ.matrix = τ.matrix)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosDef) {B : CMatrix b} (hB : B.PosDef)
    (hCpos : 0 < psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩)
    (hBq : psdTracePower B hB.posSemidef q ≤ 1)
    (hBounded : BddAbove
      ((norm ∘
        (fun w : ℂ =>
          sandwichedRenyiWeightedTraceFamily σ hσ τ hτ K
            (sandwichedRenyiBeigiNormalizedInputPath A hA α
              (psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩))
            (sandwichedRenyiBeigiDualPath B hB q) (-(w / 2)))) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1)) :
    (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace).re ≤
      psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩ := by
  exact sandwichedRenyi_tracePairingBound_of_normalizedBeigi_weightedEndpoint
    σ hσ τ hτ K hTP α q hpq hA hB hCpos hBq hBounded
    (fun z hz =>
      sandwichedRenyiWeightedMapComplex_normalizedBeigi_scaled_contraction_of_re_eq_neg_half
        σ hσ τ hτ K hτK hA α
        (psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩) hCpos
        (by simpa using hz))

/-- Normalized Beigi trace-pairing bound with all endpoint and closed-strip
analytic side conditions discharged.

This is the source-faithful α > 1 interpolation trace-pairing theorem in the
current full-rank/PosDef domain. It no longer assumes the target DPI, the
rotated-adjoint `q`-ball contraction, or an external boundedness hypothesis. -/
theorem sandwichedRenyi_tracePairingBound_of_normalizedBeigi_closedStrip
    (σ : State a) (hσ : σ.matrix.PosDef)
    (τ : State b) (hτ : τ.matrix.PosDef)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (hτK : MatrixMap.ofKraus K σ.matrix = τ.matrix)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosDef) {B : CMatrix b} (hB : B.PosDef)
    (hCpos : 0 < psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩)
    (hBq : psdTracePower B hB.posSemidef q ≤ 1) :
    (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) * B).trace).re ≤
      psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩ := by
  exact sandwichedRenyi_tracePairingBound_of_normalizedBeigi
    σ hσ τ hτ K hTP hτK α q hpq hA hB hCpos hBq
    (sandwichedRenyiWeightedTraceFamily_normalizedBeigi_bddAbove_closedStrip
      σ hσ τ hτ K A hA B hB α q (psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩))

/-- The first marginal of white noise on a product system is full-rank. -/
theorem maximallyMixed_marginalA_posDef
    [Nonempty a] [Nonempty b] :
    ((maximallyMixed (Prod a b)).marginalA).matrix.PosDef := by
  simpa [State.maximallyMixed_marginalA] using
    State.maximallyMixed_posDef (a := a)

/-- Affine regularization of a state matrix by a fixed noise state. -/
def regularizedStateMatrix (ρ ω : State a) (ε : ℝ) : CMatrix a :=
  (((1 - ε : ℝ) : ℂ) • ρ.matrix) + (((ε : ℝ) : ℂ) • ω.matrix)

/-- The affine regularization matrix is a normalized state when
`0 ≤ ε ≤ 1`. -/
def regularizedWithState (ρ ω : State a) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : State a where
  matrix := regularizedStateMatrix ρ ω ε
  pos := by
    unfold regularizedStateMatrix
    have hleft : (0 : ℂ) ≤ ((1 - ε : ℝ) : ℂ) := by
      exact_mod_cast sub_nonneg.mpr hε1
    have hright : (0 : ℂ) ≤ ((ε : ℝ) : ℂ) := by
      exact_mod_cast hε0
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul ρ.pos hleft)
      (Matrix.PosSemidef.smul ω.pos hright)
  trace_eq_one := by
    unfold regularizedStateMatrix
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      ρ.trace_eq_one, ω.trace_eq_one]
    norm_num

@[simp]
theorem regularizedWithState_matrix (ρ ω : State a) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (regularizedWithState ρ ω ε hε0 hε1).matrix =
      regularizedStateMatrix ρ ω ε :=
  rfl

/-- Mixing any state with positive weight of a full-rank noise state gives a
full-rank state. -/
theorem regularizedWithState_posDef_of_noise
    (ρ ω : State a) (hω : ω.matrix.PosDef) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hεpos : 0 < ε) :
    (regularizedWithState ρ ω ε hε0 hε1).matrix.PosDef := by
  unfold regularizedWithState regularizedStateMatrix
  have hleft : (0 : ℂ) ≤ ((1 - ε : ℝ) : ℂ) := by
    exact_mod_cast sub_nonneg.mpr hε1
  have hright : (0 : ℂ) < ((ε : ℝ) : ℂ) := by
    exact_mod_cast hεpos
  exact Matrix.PosDef.posSemidef_add
    (Matrix.PosSemidef.smul ρ.pos hleft)
    (Matrix.PosDef.smul hω hright)

/-- The regularized matrix path tends back to the original state matrix as the
mixing parameter tends to zero from inside the probability interval. -/
theorem regularizedStateMatrix_tendsto_zero (ρ ω : State a) :
    Filter.Tendsto (fun ε : ℝ => regularizedStateMatrix ρ ω ε)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ.matrix) := by
  have hcont : Continuous fun ε : ℝ => regularizedStateMatrix ρ ω ε := by
    unfold regularizedStateMatrix
    fun_prop
  have h0 : regularizedStateMatrix ρ ω 0 = ρ.matrix := by
    simp [regularizedStateMatrix]
  simpa [h0] using
    (hcont.continuousWithinAt (x := (0 : ℝ)) (s := Set.Ioo (0 : ℝ) 1)).tendsto

/-- Partial trace of an affine state regularization is the affine
regularization of the marginals. -/
theorem regularizedStateMatrix_marginalA
    (ρ ω : State (Prod a b)) (ε : ℝ) :
    partialTraceB (a := a) (b := b) (regularizedStateMatrix ρ ω ε) =
      regularizedStateMatrix ρ.marginalA ω.marginalA ε := by
  unfold regularizedStateMatrix
  rw [partialTraceB_add, partialTraceB_smul, partialTraceB_smul]
  simp [State.marginalA_matrix]

/-- The marginal of a regularized bipartite state tends to the original
marginal as the regularization weight tends to zero. -/
theorem regularizedStateMatrix_marginalA_tendsto_zero
    (ρ ω : State (Prod a b)) :
    Filter.Tendsto
      (fun ε : ℝ => partialTraceB (a := a) (b := b)
        (regularizedStateMatrix ρ ω ε))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ρ.marginalA.matrix) := by
  have h :=
    regularizedStateMatrix_tendsto_zero ρ.marginalA ω.marginalA
  simpa [regularizedStateMatrix_marginalA] using h

/-- Channel-specialized positive-definite Beigi trace-pairing bound.

For a Kraus realization of a channel and a full-rank input reference whose
output reference is also full-rank, the source-faithful Beigi weighted-map
interpolation proves the trace-pairing bound for positive-definite input and
output witnesses. The remaining gap to the full rotated-adjoint `q`-ball
theorem is the PSD closure/regularization from positive-definite witnesses to
all positive semidefinite witnesses. -/
theorem sandwichedRenyiRotatedKraus_tracePairingBound_of_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosDef) {B : CMatrix b} (hB : B.PosDef)
    (hBq : psdTracePower B hB.posSemidef q ≤ 1) :
    (((MatrixMap.ofKraus
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A) *
        B).trace).re ≤
      psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩ := by
  haveI : Nonempty a := σ.nonempty
  have hCpos : 0 < psdSchattenPNorm A hA.posSemidef ⟨α, hpq.pos⟩ :=
    psdSchattenPNorm_pos_of_posDef hA
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  have hτK : MatrixMap.ofKraus K σ.matrix = (Φ.applyState σ).matrix := by
    rw [← hK]
    rfl
  exact sandwichedRenyi_tracePairingBound_of_normalizedBeigi_closedStrip
    σ hσ (Φ.applyState σ) hσΦ K hTP hτK α q hpq
    hA hB hCpos hBq

/-- Positive-definite regularization of a Stinespring lift by full-rank white
noise on the enlarged output-environment system. -/
def regularizedStinespringLiftState {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    State (Prod b κ) :=
  letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
  regularizedWithState
    (stinespringLiftState K hTP ρ)
    (maximallyMixed (Prod b κ)) ε hε0 hε1

/-- The regularized Stinespring lift is full-rank for positive regularization
weight. -/
theorem regularizedStinespringLiftState_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hεpos : 0 < ε) :
    (regularizedStinespringLiftState K hTP ρ ε hε0 hε1).matrix.PosDef := by
  unfold regularizedStinespringLiftState
  letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
  exact regularizedWithState_posDef_of_noise
    (stinespringLiftState K hTP ρ) (maximallyMixed (Prod b κ))
    maximallyMixed_posDef hε0 hε1 hεpos

/-- The regularized Stinespring lift converges back to the generally singular
Stinespring lift as the regularization weight tends to zero. -/
theorem regularizedStinespringLiftState_matrix_tendsto
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) :
    Filter.Tendsto
      (fun ε : ℝ =>
        regularizedStateMatrix
          (stinespringLiftState K hTP ρ)
          (letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
           maximallyMixed (Prod b κ)) ε)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1))
      (nhds (stinespringLiftState K hTP ρ).matrix) := by
  letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
  exact regularizedStateMatrix_tendsto_zero
    (stinespringLiftState K hTP ρ) (maximallyMixed (Prod b κ))

/-- Matrix form of the marginal of the regularized Stinespring lift. -/
theorem regularizedStinespringLiftState_marginalA_matrix
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ((regularizedStinespringLiftState K hTP ρ ε hε0 hε1).marginalA).matrix =
      regularizedStateMatrix
        (stinespringLiftState K hTP ρ).marginalA
        ((letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
          maximallyMixed (Prod b κ)).marginalA) ε := by
  unfold regularizedStinespringLiftState
  letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
  simpa [regularizedWithState_matrix] using
    regularizedStateMatrix_marginalA
      (stinespringLiftState K hTP ρ)
      (maximallyMixed (Prod b κ)) ε

/-- The marginal of the regularized Stinespring lift is the same affine
regularization of the channel output by the environment-noise marginal. -/
theorem regularizedStinespringLiftState_marginalA_eq_regularized_applyState
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ) (Φ : Channel a b)
    (hK : Φ.map = MatrixMap.ofKraus K)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (regularizedStinespringLiftState K hTP ρ ε hε0 hε1).marginalA =
      regularizedWithState (Φ.applyState ρ)
        ((letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
          maximallyMixed (Prod b κ)).marginalA) ε hε0 hε1 := by
  apply State.ext
  letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
  rw [regularizedStinespringLiftState_marginalA_matrix]
  have hmargin := stinespringLiftState_marginalA_eq_applyState K Φ hK hTP ρ
  rw [hmargin]
  rfl

/-- The output marginal of the regularized Stinespring lift is full-rank for
positive regularization weight. -/
theorem regularizedStinespringLiftState_marginalA_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hεpos : 0 < ε) :
    ((regularizedStinespringLiftState K hTP ρ ε hε0 hε1).marginalA).matrix.PosDef := by
  let hprod : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
  letI : Nonempty (Prod b κ) := hprod
  letI : Nonempty b := ⟨(Classical.choice hprod).1⟩
  letI : Nonempty κ := ⟨(Classical.choice hprod).2⟩
  rw [regularizedStinespringLiftState_marginalA_matrix]
  have hnoise :
      ((maximallyMixed (Prod b κ)).marginalA).matrix.PosDef :=
    maximallyMixed_marginalA_posDef (a := b) (b := κ)
  have h :=
    regularizedWithState_posDef_of_noise
      (stinespringLiftState K hTP ρ).marginalA
      ((maximallyMixed (Prod b κ)).marginalA)
      hnoise hε0 hε1 hεpos
  simpa [regularizedWithState_matrix] using h

/-- The output marginal of the regularized Stinespring lift tends back to the
Kraus-channel output as the regularization weight tends to zero. -/
theorem regularizedStinespringLiftState_marginalA_matrix_tendsto
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (ρ : State a) :
    Filter.Tendsto
      (fun ε : ℝ =>
        partialTraceB (a := b) (b := κ)
          (regularizedStateMatrix
            (stinespringLiftState K hTP ρ)
            (letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
             maximallyMixed (Prod b κ)) ε))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 1))
      (nhds (MatrixMap.ofKraus K ρ.matrix)) := by
  letI : Nonempty (Prod b κ) := (stinespringLiftState K hTP ρ).nonempty
  have h :=
    regularizedStateMatrix_marginalA_tendsto_zero
      (stinespringLiftState K hTP ρ) (maximallyMixed (Prod b κ))
  have hpt :
      partialTraceB (a := b) (b := κ) (stinespringLiftState K hTP ρ).matrix =
        MatrixMap.ofKraus K ρ.matrix := by
    simpa [State.marginalA_matrix] using
      stinespringLiftState_marginalA_matrix K hTP ρ
  simpa [hpt] using h

/-- Positive-definite Beigi trace-pairing bound applied to a regularized PSD
input witness.

For arbitrary PSD input test `A`, the source-faithful positive-definite
interpolation theorem controls the trace pairing after replacing `A` by
`A + ε I`.  This is the concrete regularization bridge needed before the final
PSD closure/continuity step in the α > 1 rotated-adjoint `q`-ball proof. -/
theorem sandwichedRenyiRotatedKraus_tracePairingBound_of_regularizedInput
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosSemidef) {B : CMatrix b} (hB : B.PosDef)
    (hBq : psdTracePower B hB.posSemidef q ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    (((MatrixMap.ofKraus
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A) *
        B).trace).re ≤
      psdSchattenPNorm (A + ε • (1 : CMatrix a))
        (cMatrix_posSemidef_add_pos_smul_one_posDef hA hε).posSemidef
        ⟨α, hpq.pos⟩ := by
  let L : κ → Matrix b a ℂ :=
    sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α
  let Aε : CMatrix a := A + ε • (1 : CMatrix a)
  have hAε : Aε.PosDef := by
    simpa [Aε] using cMatrix_posSemidef_add_pos_smul_one_posDef hA hε
  have hA_le : A ≤ Aε := by
    simpa [Aε] using cMatrix_le_add_pos_smul_one (a := a) (A := A) hε
  have hTA_le : MatrixMap.ofKraus L A ≤ MatrixMap.ofKraus L Aε := by
    rw [Matrix.le_iff] at hA_le ⊢
    have hpos :
        (MatrixMap.ofKraus L (Aε - A)).PosSemidef :=
      MatrixMap.ofKraus_mapsPositive L (Aε - A) hA_le
    simpa [map_sub] using hpos
  have htrace_order :
      (((MatrixMap.ofKraus L A) * B).trace).re ≤
        (((MatrixMap.ofKraus L Aε) * B).trace).re := by
    have hcomm_left :
        (((MatrixMap.ofKraus L A) * B).trace).re =
          ((B * MatrixMap.ofKraus L A).trace).re := by
      rw [Matrix.trace_mul_comm]
    have hcomm_right :
        (((MatrixMap.ofKraus L Aε) * B).trace).re =
          ((B * MatrixMap.ofKraus L Aε).trace).re := by
      rw [Matrix.trace_mul_comm]
    rw [hcomm_left, hcomm_right]
    exact cMatrix_trace_mul_le_of_le_posSemidef_left (W := B)
      (A := MatrixMap.ofKraus L A)
      (B := MatrixMap.ofKraus L Aε) hB.posSemidef hTA_le
  have hbeigi :
      (((MatrixMap.ofKraus
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) Aε) *
          B).trace).re ≤
        psdSchattenPNorm Aε hAε.posSemidef ⟨α, hpq.pos⟩ := by
    simpa [L, Aε] using
      sandwichedRenyiRotatedKraus_tracePairingBound_of_posDef
        K σ Φ hK hσ hσΦ α q hpq hAε hB hBq
  exact htrace_order.trans (by simpa [L, Aε] using hbeigi)

/-- Beigi trace-pairing bound for regularized input and normalized regularized
output witnesses.

Starting from arbitrary PSD test matrices `A` and `B`, this theorem replaces
`A` by `A + ε I`, replaces `B` by `B + δ I`, normalizes the latter into the
positive `q`-unit sphere, and then applies the source-faithful positive-definite
Beigi interpolation theorem.  The remaining step to the full PSD handoff is the
limit as `ε, δ → 0`. -/
theorem sandwichedRenyiRotatedKraus_tracePairingBound_of_regularizedInputOutput
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosSemidef)
    {B : CMatrix b} (hB : B.PosSemidef)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    let Bδ : CMatrix b := B + δ • (1 : CMatrix b)
    let scale : ℝ := (psdTracePower Bδ
      (cMatrix_posSemidef_add_pos_smul_one_posDef hB hδ).posSemidef q) ^ (-(1 / q))
    (((MatrixMap.ofKraus
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A) *
        (scale • Bδ : CMatrix b)).trace).re ≤
      psdSchattenPNorm (A + ε • (1 : CMatrix a))
        (cMatrix_posSemidef_add_pos_smul_one_posDef hA hε).posSemidef
        ⟨α, hpq.pos⟩ := by
  haveI : Nonempty b := (Φ.applyState σ).nonempty
  intro Bδ scale
  have hBδ : Bδ.PosDef := by
    simpa [Bδ] using cMatrix_posSemidef_add_pos_smul_one_posDef hB hδ
  have hSpos :
      0 < psdTracePower Bδ hBδ.posSemidef q := by
    exact psdTracePower_pos_of_ne_zero Bδ hBδ.posSemidef (by
      intro hzero
      have htr : (0 : ℂ) < Bδ.trace := Matrix.PosDef.trace_pos hBδ
      rw [hzero] at htr
      simp at htr)
  have hscale_pos : 0 < scale := by
    exact Real.rpow_pos_of_pos hSpos (-(1 / q))
  have hscale_nonneg : 0 ≤ scale := le_of_lt hscale_pos
  have hscaledB : (scale • Bδ : CMatrix b).PosDef :=
    Matrix.PosDef.smul hBδ hscale_pos
  have hscaledBq :
      psdTracePower (scale • Bδ : CMatrix b) hscaledB.posSemidef q ≤ 1 := by
    have heq :=
      psdTracePower_normalized_real_smul_eq_one_of_posDef hBδ hpq.symm.pos
    exact le_of_eq (by
      simpa [scale] using heq)
  exact
    sandwichedRenyiRotatedKraus_tracePairingBound_of_regularizedInput
      K σ Φ hK hσ hσΦ α q hpq hA hscaledB hscaledBq hε

/-- PSD `q`-sphere trace-pairing bound obtained by closing the positive-definite
Beigi interpolation theorem under input/output identity regularization.

This removes the positive-definite witness assumption from
`sandwichedRenyiRotatedKraus_tracePairingBound_of_posDef` for the normalized
output `q`-sphere. It is the first nontrivial PSD closure step toward the full
rotated-adjoint `q`-ball contraction. -/
theorem sandwichedRenyiRotatedKraus_tracePairingBound_of_psdTracePower_eq_one
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosSemidef)
    {B : CMatrix b} (hB : B.PosSemidef)
    (hBq : psdTracePower B hB q = 1) :
    (((MatrixMap.ofKraus
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A) *
        B).trace).re ≤
      psdSchattenPNorm A hA ⟨α, lt_trans zero_lt_one hα_gt_one⟩ := by
  let L : κ → Matrix b a ℂ :=
    sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α
  let TA : CMatrix b := MatrixMap.ofKraus L A
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_gt_one
  have hδlimit : Filter.Tendsto
      (fun δ : ℝ =>
        let Bδ : CMatrix b := B + δ • (1 : CMatrix b)
        let scale : ℝ := ((CFC.rpow Bδ q).trace.re) ^ (-(1 / q))
        ((TA * (scale • Bδ : CMatrix b)).trace).re)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((TA * B).trace.re)) := by
    have hBnorm :=
      cMatrix_normalized_regularized_tendsto_of_psdTracePower_eq_one
        hB hpq.symm.pos hBq
    have hcont : Continuous fun M : CMatrix b => ((TA * M).trace).re := by
      fun_prop
    exact hcont.tendsto B |>.comp hBnorm
  have hleft_le_regularizedInput
      {ε : ℝ} (hε : 0 < ε) :
      ((TA * B).trace).re ≤
        psdSchattenPNorm (A + ε • (1 : CMatrix a))
          (cMatrix_posSemidef_add_pos_smul_one_posDef hA hε).posSemidef
          ⟨α, hα_pos⟩ := by
    exact le_of_tendsto hδlimit (by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hreg :=
        sandwichedRenyiRotatedKraus_tracePairingBound_of_regularizedInputOutput
          K σ Φ hK hσ hσΦ α q hpq hA hB hε hδ
      simpa [L, TA, psdTracePower] using hreg)
  have hRtrace :=
    cMatrix_rpow_trace_re_tendsto_add_pos_smul_one hA hα_pos
  have hR : Filter.Tendsto
      (fun ε : ℝ =>
        ((CFC.rpow (A + ε • (1 : CMatrix a)) α).trace.re) ^ (1 / α))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (psdSchattenPNorm A hA ⟨α, hα_pos⟩)) := by
    have hcont : ContinuousAt
        (fun x : ℝ => x ^ (1 / α))
        ((CFC.rpow A α).trace.re) :=
      Real.continuousAt_rpow_const
        ((CFC.rpow A α).trace.re) (1 / α)
        (Or.inr (le_of_lt (one_div_pos.mpr hα_pos)))
    have h := hcont.tendsto.comp hRtrace
    simpa [psdSchattenPNorm, Internal.psdSchattenExpression, psdTracePower] using h
  exact ge_of_tendsto hR (by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have h := hleft_le_regularizedInput hε
    simpa [psdSchattenPNorm, Internal.psdSchattenExpression, psdTracePower] using h)

/-- PSD `q`-ball trace-pairing bound for the Beigi weighted rotated Kraus map.

The `q`-sphere result gives the bound for normalized output witnesses. A
nonzero witness in the `q`-unit ball is scaled up to the `q`-sphere; PSD
monotonicity of the trace pairing then returns the original witness. -/
theorem sandwichedRenyiRotatedKraus_tracePairingBound_of_psdTracePower_le_one
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (hA : A.PosSemidef)
    {B : CMatrix b} (hB : B.PosSemidef)
    (hBq : psdTracePower B hB q ≤ 1) :
    (((MatrixMap.ofKraus
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A) *
        B).trace).re ≤
      psdSchattenPNorm A hA ⟨α, lt_trans zero_lt_one hα_gt_one⟩ := by
  classical
  let L : κ → Matrix b a ℂ :=
    sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α
  let TA : CMatrix b := MatrixMap.ofKraus L A
  by_cases hBzero : B = 0
  · have htrace_zero : ((TA * B).trace).re = 0 := by
      simp [hBzero]
    rw [htrace_zero]
    exact psdSchattenPNorm_nonneg A hA ⟨α, lt_trans zero_lt_one hα_gt_one⟩
  · let scale : ℝ := (psdTracePower B hB q) ^ (-(1 / q))
    let Bn : CMatrix b := scale • B
    have hq_pos : 0 < q := hpq.symm.pos
    have hSpos : 0 < psdTracePower B hB q :=
      psdTracePower_pos_of_ne_zero B hB hBzero
    have hscale_nonneg : 0 ≤ scale := by
      exact Real.rpow_nonneg (le_of_lt hSpos) (-(1 / q))
    have hBn : Bn.PosSemidef := by
      simpa [Bn] using Matrix.PosSemidef.smul hB hscale_nonneg
    have hBnq : psdTracePower Bn hBn q = 1 := by
      simpa [scale, Bn] using
        psdTracePower_normalized_real_smul_eq_one_of_ne_zero hB hBzero hq_pos
    have hbound_Bn :
        ((TA * Bn).trace).re ≤
          psdSchattenPNorm A hA ⟨α, lt_trans zero_lt_one hα_gt_one⟩ := by
      simpa [L, TA, Bn] using
        sandwichedRenyiRotatedKraus_tracePairingBound_of_psdTracePower_eq_one
          K σ Φ hK hσ hσΦ α q hα_gt_one hpq hA hBn hBnq
    have hscale_ge_one : 1 ≤ scale := by
      have hSle : psdTracePower B hB q ≤ 1 := hBq
      have hnonpos : -(1 / q) ≤ 0 := by
        exact neg_nonpos.mpr (one_div_nonneg.mpr (le_of_lt hq_pos))
      simpa [scale] using
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hSpos hSle hnonpos
    have hB_le_Bn : B ≤ Bn := by
      rw [Matrix.le_iff]
      have hdiff : (Bn - B).PosSemidef := by
        have hcoeff : 0 ≤ scale - 1 := sub_nonneg.mpr hscale_ge_one
        have hscaled : ((scale - 1) • B : CMatrix b).PosSemidef :=
          Matrix.PosSemidef.smul hB hcoeff
        have hdiff_eq : Bn - B = (scale - 1) • B := by
          calc
            Bn - B = scale • B - (1 : ℝ) • B := by
              simp [Bn]
            _ = (scale - 1) • B := by
              rw [← sub_smul]
        simpa [hdiff_eq] using hscaled
      simpa [sub_eq_add_neg] using hdiff
    have hTA : TA.PosSemidef := by
      simpa [TA] using MatrixMap.ofKraus_mapsPositive L A hA
    have htrace_le :
        ((TA * B).trace).re ≤ ((TA * Bn).trace).re :=
      cMatrix_trace_mul_le_of_le_posSemidef_left (W := TA) (A := B) (B := Bn) hTA hB_le_Bn
    exact htrace_le.trans hbound_Bn

/-- The explicit input-side Holder witness is the Heisenberg adjoint of the
rotated Kraus family.

This is the algebraic normalization step for the α > 1 proof route: the
remaining hard theorem is the Schatten `q`-contraction of this rotated adjoint.
-/
theorem sandwichedRenyiKrausAdjointInputWitness_eq_rotatedKrausAdjoint
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (B : CMatrix b) (α : ℝ) :
    sandwichedRenyiKrausAdjointInputWitness σ Φ K B α =
      MatrixMap.krausAdjoint
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix b := CFC.rpow (Φ.applyState σ).matrix s
  let D : CMatrix a := CFC.rpow σ.matrix (-s)
  have hCstar : Matrix.conjTranspose C = C := by
    exact (State.rpowMatrix_posSemidef (Φ.applyState σ) s).isHermitian.eq
  have hDstar : Matrix.conjTranspose D = D := by
    exact (State.rpowMatrix_posSemidef σ (-s)).isHermitian.eq
  have hCstar' :
      Matrix.conjTranspose (CFC.rpow (Φ.applyState σ).matrix s) =
        CFC.rpow (Φ.applyState σ).matrix s := by
    simpa [C] using hCstar
  have hDstar' :
      Matrix.conjTranspose (CFC.rpow σ.matrix (-s)) =
        CFC.rpow σ.matrix (-s) := by
    simpa [D] using hDstar
  have hCstar'' :
      Matrix.conjTranspose (CFC.rpow (Φ.applyState σ).matrix ((1 - α) / (2 * α))) =
        CFC.rpow (Φ.applyState σ).matrix ((1 - α) / (2 * α)) := by
    simpa [s] using hCstar'
  have hDstar'' :
      Matrix.conjTranspose (CFC.rpow σ.matrix (-((1 - α) / (2 * α)))) =
        CFC.rpow σ.matrix (-((1 - α) / (2 * α))) := by
    simpa [s] using hDstar'
  ext i j
  simp only [sandwichedRenyiKrausAdjointInputWitness, sandwichedRenyiRotatedKraus,
    sandwichedRenyiHolderDualEffect, MatrixMap.krausAdjoint, Matrix.conjTranspose_mul]
  rw [hCstar'', hDstar'']
  simp [Matrix.mul_assoc, Finset.mul_sum, Finset.sum_mul]

/-- The rotated Kraus adjoint sends the output dual reference endpoint
`(Φσ)^(1 - 1/α)` back to the input endpoint `σ^(1 - 1/α)`.

Together with `sandwichedRenyiRotatedKraus_apply_referencePower_eq`, this gives
the two exact endpoint normalizations required by the α > 1 interpolation
route. -/
theorem sandwichedRenyiRotatedKrausAdjoint_referenceDualPower_eq
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    MatrixMap.krausAdjoint
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
        (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)) =
      CFC.rpow σ.matrix (1 - 1 / α) := by
  let τ : State b := Φ.applyState σ
  let s : ℝ := (1 - α) / (2 * α)
  let r : ℝ := 1 - 1 / α
  have hα_ne_zero : α ≠ 0 := ne_of_gt (lt_trans zero_lt_one hα_gt_one)
  have hτ_nonneg : 0 ≤ τ.matrix :=
    Matrix.nonneg_iff_posSemidef.mpr hσΦ.posSemidef
  have hσ_nonneg : 0 ≤ σ.matrix :=
    Matrix.nonneg_iff_posSemidef.mpr hσ.posSemidef
  have hsrs : (s + r) + s = 0 := by
    dsimp [s, r]
    field_simp [hα_ne_zero]
    ring
  have hnegs : -s + -s = r := by
    dsimp [s, r]
    field_simp [hα_ne_zero]
    ring
  have hdual_one :
      sandwichedRenyiHolderDualEffect τ (CFC.rpow τ.matrix r) α =
        (1 : CMatrix b) := by
    have hsr :
        CFC.rpow τ.matrix s * CFC.rpow τ.matrix r =
          CFC.rpow τ.matrix (s + r) := by
      exact (CFC.rpow_add (a := τ.matrix) (x := s) (y := r) hσΦ.isUnit).symm
    have htotal :
        CFC.rpow τ.matrix (s + r) * CFC.rpow τ.matrix s =
          CFC.rpow τ.matrix ((s + r) + s) := by
      exact (CFC.rpow_add (a := τ.matrix) (x := s + r) (y := s) hσΦ.isUnit).symm
    unfold sandwichedRenyiHolderDualEffect
    change CFC.rpow τ.matrix s * CFC.rpow τ.matrix r * CFC.rpow τ.matrix s =
      (1 : CMatrix b)
    calc
      CFC.rpow τ.matrix s * CFC.rpow τ.matrix r * CFC.rpow τ.matrix s =
          (CFC.rpow τ.matrix s * CFC.rpow τ.matrix r) * CFC.rpow τ.matrix s := by
            rw [Matrix.mul_assoc]
      _ = CFC.rpow τ.matrix (s + r) * CFC.rpow τ.matrix s := by
            rw [hsr]
      _ = CFC.rpow τ.matrix ((s + r) + s) := htotal
      _ = CFC.rpow τ.matrix 0 := by rw [hsrs]
      _ = (1 : CMatrix b) := CFC.rpow_zero τ.matrix (ha := hτ_nonneg)
  have hinput_eq :=
    sandwichedRenyiKrausAdjointInputWitness_eq_rotatedKrausAdjoint
      K σ Φ (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)) α
  rw [← hinput_eq]
  unfold sandwichedRenyiKrausAdjointInputWitness
  change CFC.rpow σ.matrix (-s) *
      MatrixMap.krausAdjoint K
        (sandwichedRenyiHolderDualEffect τ (CFC.rpow τ.matrix r) α) *
      CFC.rpow σ.matrix (-s) =
    CFC.rpow σ.matrix r
  rw [hdual_one, MatrixMap.krausAdjoint_one_of_tracePreserving K hTP]
  have hleft :
      CFC.rpow σ.matrix (-s) * (1 : CMatrix a) * CFC.rpow σ.matrix (-s) =
        CFC.rpow σ.matrix (-s) * CFC.rpow σ.matrix (-s) := by
    simp
  rw [hleft]
  calc
    CFC.rpow σ.matrix (-s) * CFC.rpow σ.matrix (-s) =
        CFC.rpow σ.matrix (-s + -s) := by
          exact (CFC.rpow_add (a := σ.matrix) (x := -s) (y := -s) hσ.isUnit).symm
    _ = CFC.rpow σ.matrix r := by rw [hnegs]

/-- The output sandwiched inner operator is obtained by applying the rotated
Kraus map to the input sandwiched inner operator.

This is the Schrödinger-picture counterpart of
`sandwichedRenyiKrausAdjointInputWitness_eq_rotatedKrausAdjoint`. It reduces
the α > 1 data-processing theorem to proving the correct Schatten contraction
for this specific rotated CP map. -/
theorem sandwichedRenyiInner_eq_rotatedKraus_apply
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (ρ σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (α : ℝ) :
    sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α =
      MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
        (sandwichedRenyiInner ρ σ α) := by
  let s : ℝ := (1 - α) / (2 * α)
  let Cσ : CMatrix a := CFC.rpow σ.matrix s
  let Dσ : CMatrix a := CFC.rpow σ.matrix (-s)
  let Cτ : CMatrix b := CFC.rpow (Φ.applyState σ).matrix s
  have hCτstar : Matrix.conjTranspose Cτ = Cτ := by
    exact (State.rpowMatrix_posSemidef (Φ.applyState σ) s).isHermitian.eq
  have hDσstar : Matrix.conjTranspose Dσ = Dσ := by
    exact (State.rpowMatrix_posSemidef σ (-s)).isHermitian.eq
  have hDσCσ : Dσ * Cσ = 1 := by
    simpa [Cσ, Dσ] using
      (CFC.rpow_neg_mul_rpow (a := σ.matrix) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  have hCσDσ : Cσ * Dσ = 1 := by
    simpa [Cσ, Dσ] using
      (CFC.rpow_mul_rpow_neg (a := σ.matrix) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  have hDσCσ_mul : ∀ X : CMatrix a, Dσ * (Cσ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hDσCσ, Matrix.one_mul]
  have hCσDσ_mul : ∀ X : CMatrix a, Cσ * (Dσ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hCσDσ, Matrix.one_mul]
  have hCσDσ_mul_rect : ∀ X : Matrix a b ℂ, Cσ * (Dσ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hCσDσ, Matrix.one_mul]
  change Cτ * (Φ.applyState ρ).matrix * Cτ =
    MatrixMap.ofKraus (fun k : κ => Cτ * K k * Dσ) (Cσ * ρ.matrix * Cσ)
  rw [show (Φ.applyState ρ).matrix = Φ.map ρ.matrix by rfl, hK]
  ext i j
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply,
    Matrix.conjTranspose_mul]
  rw [hDσstar, hCτstar]
  simp [Matrix.mul_assoc, hDσCσ_mul, hCσDσ_mul_rect,
    Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]

/-- The rotated Kraus map sends the input reference endpoint `σ^(1/α)` to the
output reference endpoint `(Φσ)^(1/α)`.

This is the Schrödinger-side endpoint normalization needed before applying the
α > 1 noncommutative interpolation/Schatten-contraction theorem. -/
theorem sandwichedRenyiRotatedKraus_apply_referencePower_eq
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
        (CFC.rpow σ.matrix (1 / α)) =
      CFC.rpow (Φ.applyState σ).matrix (1 / α) := by
  have hα_ne_zero : α ≠ 0 := ne_of_gt (lt_trans zero_lt_one hα_gt_one)
  have hinner :=
    sandwichedRenyiInner_eq_rotatedKraus_apply
      K σ σ Φ hK hσ α
  rw [sandwichedRenyiInner_self_eq_rpow σ hσ α hα_ne_zero,
    sandwichedRenyiInner_self_eq_rpow (Φ.applyState σ) hσΦ α hα_ne_zero] at hinner
  exact hinner.symm

/-- The interpolation reference endpoint `σ^(1/α)` has normalized
PSD Schatten `α` expression. -/
theorem state_rpow_one_div_psdSchattenPNorm_eq_one
    (σ : State a) (hσ : σ.matrix.PosDef) (α : ℝ) (hα_pos : 0 < α) :
    psdSchattenPNorm (CFC.rpow σ.matrix (1 / α))
        (σ.rpowMatrix_posSemidef (1 / α)) ⟨α, hα_pos⟩ = 1 := by
  rw [psdSchattenPNorm, Internal.psdSchattenExpression,
    state_rpow_one_div_psdTracePower_eq_one σ hσ α hα_pos]
  exact Real.one_rpow (1 / α)

/-- The Holder-dual interpolation reference endpoint `σ^(1-1/α)` has
normalized `q`-power trace when `q` is Holder-conjugate to `α`. -/
theorem state_rpow_one_sub_inv_psdTracePower_eq_one
    (σ : State a) (hσ : σ.matrix.PosDef) (α q : ℝ)
    (hpq : α.HolderConjugate q) :
    psdTracePower (CFC.rpow σ.matrix (1 - 1 / α))
        (σ.rpowMatrix_posSemidef (1 - 1 / α)) q = 1 := by
  have hσ_nonneg : 0 ≤ σ.matrix :=
    Matrix.nonneg_iff_posSemidef.mpr hσ.posSemidef
  have hq_nonneg : 0 ≤ q := le_of_lt hpq.symm.pos
  have hr_eq : 1 - 1 / α = q⁻¹ := by
    simpa [one_div] using hpq.one_sub_inv
  have hr_nonneg : 0 ≤ 1 - 1 / α := by
    rw [hr_eq]
    exact inv_nonneg.mpr hq_nonneg
  have hpow :
      CFC.rpow (CFC.rpow σ.matrix (1 - 1 / α)) q =
        CFC.rpow σ.matrix (1 : ℝ) := by
    calc
      CFC.rpow (CFC.rpow σ.matrix (1 - 1 / α)) q =
          CFC.rpow σ.matrix ((1 - 1 / α) * q) := by
            exact CFC.rpow_rpow_of_exponent_nonneg σ.matrix
              (1 - 1 / α) q hr_nonneg hq_nonneg hσ_nonneg
      _ = CFC.rpow σ.matrix (1 : ℝ) := by
            congr 1
            rw [hr_eq]
            field_simp [hpq.symm.ne_zero]
  have hone : CFC.rpow σ.matrix (1 : ℝ) = σ.matrix :=
    CFC.rpow_one σ.matrix (ha := hσ_nonneg)
  rw [psdTracePower, hpow, hone, σ.trace_eq_one]
  norm_num

/-- The rotated Kraus map preserves the normalized `α`-power trace of the
reference interpolation endpoint.

This is the concrete boundary-norm check for the α > 1 interpolation route:
the map sends `σ^(1/α)` to `(Φσ)^(1/α)`, and both endpoints have power trace
one. -/
theorem sandwichedRenyiRotatedKraus_apply_referencePower_psdTracePower_eq_one
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    psdTracePower
        (MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
          (CFC.rpow σ.matrix (1 / α)))
        (MatrixMap.ofKraus_mapsPositive
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
          (CFC.rpow σ.matrix (1 / α))
          (σ.rpowMatrix_posSemidef (1 / α)))
        α = 1 := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_gt_one
  rw [psdTracePower,
    sandwichedRenyiRotatedKraus_apply_referencePower_eq
      K σ Φ hK hσ hσΦ α hα_gt_one]
  simpa [psdTracePower] using
    state_rpow_one_div_psdTracePower_eq_one (Φ.applyState σ) hσΦ α hα_pos

/-- Order endpoint for the Schrödinger side of the α > 1 rotated-Kraus
interpolation route.

If an input positive witness is dominated by the input reference endpoint
`σ^(1/α)`, then its rotated Kraus image is dominated by the output endpoint
`(Φσ)^(1/α)`. -/
theorem sandwichedRenyiRotatedKraus_apply_le_referencePower_of_le
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) {A : CMatrix a}
    (hA_le : A ≤ CFC.rpow σ.matrix (1 / α)) :
    MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A ≤
      CFC.rpow (Φ.applyState σ).matrix (1 / α) := by
  rw [Matrix.le_iff] at hA_le ⊢
  have hpos :
      (MatrixMap.ofKraus
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
        (CFC.rpow σ.matrix (1 / α) - A)).PosSemidef :=
    MatrixMap.ofKraus_mapsPositive
      (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
      (CFC.rpow σ.matrix (1 / α) - A) hA_le
  rw [map_sub,
    sandwichedRenyiRotatedKraus_apply_referencePower_eq
      K σ Φ hK hσ hσΦ α hα_gt_one] at hpos
  exact hpos

/-- Schrödinger-side endpoint trace-pairing bound for the α > 1 interpolation
route.

If an input PSD test operator is dominated by the input reference endpoint
`σ^(1/α)`, then its rotated Kraus image pairs with every positive output
`q`-unit-ball witness by at most one. This is one concrete boundary estimate
needed by the eventual noncommutative interpolation proof. -/
theorem sandwichedRenyiRotatedKraus_tracePairing_le_one_of_input_le_referencePower
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q)
    {A : CMatrix a} (_hA : A.PosSemidef)
    (hA_le : A ≤ CFC.rpow σ.matrix (1 / α))
    {B : CMatrix b} (hB : B.PosSemidef)
    (hBq : psdTracePower B hB q ≤ 1) :
    (((MatrixMap.ofKraus
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A) * B).trace).re ≤
      1 := by
  have hTA_le :
      MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A ≤
        CFC.rpow (Φ.applyState σ).matrix (1 / α) :=
    sandwichedRenyiRotatedKraus_apply_le_referencePower_of_le
      K σ Φ hK hσ hσΦ α hα_gt_one hA_le
  have htrace_order :
      (((MatrixMap.ofKraus
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A) * B).trace).re ≤
        ((CFC.rpow (Φ.applyState σ).matrix (1 / α) * B).trace).re := by
    have hcomm_left :
        (((MatrixMap.ofKraus
            (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A) *
              B).trace).re =
          ((B *
            MatrixMap.ofKraus
              (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A).trace).re := by
      rw [Matrix.trace_mul_comm]
    have hcomm_right :
        ((CFC.rpow (Φ.applyState σ).matrix (1 / α) * B).trace).re =
          ((B * CFC.rpow (Φ.applyState σ).matrix (1 / α)).trace).re := by
      rw [Matrix.trace_mul_comm]
    rw [hcomm_left, hcomm_right]
    exact cMatrix_trace_mul_le_of_le_posSemidef_left (W := B)
      (A := MatrixMap.ofKraus
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) A)
      (B := CFC.rpow (Φ.applyState σ).matrix (1 / α)) hB hTA_le
  have hRpos :
      (CFC.rpow (Φ.applyState σ).matrix (1 / α)).PosSemidef :=
    (Φ.applyState σ).rpowMatrix_posSemidef (1 / α)
  have hholder :
      ((CFC.rpow (Φ.applyState σ).matrix (1 / α) * B).trace).re ≤
        psdSchattenPNorm (CFC.rpow (Φ.applyState σ).matrix (1 / α)) hRpos
          ⟨α, lt_trans zero_lt_one hα_gt_one⟩ :=
    posSemidef_trace_mul_le_psdSchattenPNorm_of_tracePower_le_one
      hRpos hB hpq (le_of_lt hpq.symm.lt) hBq
  have hnorm :
      psdSchattenPNorm (CFC.rpow (Φ.applyState σ).matrix (1 / α)) hRpos
          ⟨α, lt_trans zero_lt_one hα_gt_one⟩ = 1 := by
    simpa [hRpos] using
      state_rpow_one_div_psdSchattenPNorm_eq_one
        (Φ.applyState σ) hσΦ α (lt_trans zero_lt_one hα_gt_one)
  exact htrace_order.trans (hholder.trans_eq hnorm)

/-- The rotated Kraus adjoint preserves the normalized Holder-dual endpoint
unit ball.

For `q` Holder-conjugate to `α`, the output endpoint
`(Φσ)^(1-1/α)` has `q`-power trace one, and the rotated Kraus adjoint sends it
exactly to `σ^(1-1/α)`, which has the same normalized `q`-power trace. -/
theorem sandwichedRenyiRotatedKrausAdjoint_referenceDualPower_psdTracePower_eq_one
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q) :
    psdTracePower
        (MatrixMap.krausAdjoint
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
          (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)))
        (MatrixMap.krausAdjoint_mapsPositive
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
          (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α))
          ((Φ.applyState σ).rpowMatrix_posSemidef (1 - 1 / α)))
        q = 1 := by
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  rw [psdTracePower,
    sandwichedRenyiRotatedKrausAdjoint_referenceDualPower_eq
      K σ Φ hTP hσ hσΦ α hα_gt_one]
  simpa [psdTracePower] using
    state_rpow_one_sub_inv_psdTracePower_eq_one σ hσ α q hpq

/-- Order endpoint for the α > 1 rotated-Kraus interpolation route.

If an output witness is dominated by the output dual reference endpoint
`(Φσ)^(1-1/α)`, then its rotated Kraus adjoint is dominated by the input dual
reference endpoint `σ^(1-1/α)`. This is the order-theoretic boundary condition
used by the noncommutative interpolation/Schatten-contraction step. -/
theorem sandwichedRenyiRotatedKrausAdjoint_le_referenceDualPower_of_le
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) {B : CMatrix b}
    (hB_le :
      B ≤ CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)) :
    MatrixMap.krausAdjoint
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B ≤
      CFC.rpow σ.matrix (1 - 1 / α) := by
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  rw [Matrix.le_iff] at hB_le ⊢
  have hpos :
      (MatrixMap.krausAdjoint
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
        (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α) - B)).PosSemidef :=
    MatrixMap.krausAdjoint_mapsPositive
      (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
      (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α) - B) hB_le
  rw [MatrixMap.krausAdjoint_sub_apply,
    sandwichedRenyiRotatedKrausAdjoint_referenceDualPower_eq
      K σ Φ hTP hσ hσΦ α hα_gt_one] at hpos
  exact hpos

/-- Trace-pairing criterion for the rotated-adjoint `q`-unit-ball contraction.

This is the noncommutative Schatten-duality handoff for the α > 1 proof route:
to show that the rotated Heisenberg adjoint maps a positive output witness into
the input `q`-unit ball, it is enough to prove the matching trace-pairing bound
against every positive input test operator. The remaining mathematical content
is exactly that interpolation trace-pairing bound. -/
theorem sandwichedRenyiRotatedKrausAdjoint_qBall_of_tracePairingBound
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (τ : State b) (α q : ℝ) (hpq : α.HolderConjugate q)
    {B : CMatrix b} (hB : B.PosSemidef)
    (hbound : ∀ A : CMatrix a, ∀ hA : A.PosSemidef,
      (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) *
          B).trace).re ≤ psdSchattenPNorm A hA ⟨α, hpq.pos⟩) :
    psdTracePower
        (MatrixMap.krausAdjoint (sandwichedRenyiRotatedKraus σ τ K α) B)
        (MatrixMap.krausAdjoint_mapsPositive
          (sandwichedRenyiRotatedKraus σ τ K α) B hB) q ≤
      1 := by
  let L : κ → Matrix b a ℂ := sandwichedRenyiRotatedKraus σ τ K α
  exact
    psdTracePower_le_one_of_trace_mul_le_psdSchattenPNorm
      (MatrixMap.krausAdjoint_mapsPositive L B hB) hpq
      (fun A hA => by
        have hdual := MatrixMap.ofKraus_trace_duality L A B
        have htrace :
            ((A * MatrixMap.krausAdjoint L B).trace).re =
              (((MatrixMap.ofKraus L A) * B).trace).re :=
          (congrArg Complex.re hdual).symm
        rw [htrace]
        exact hbound A hA)

/-- Beigi weighted-map `q`-unit-ball contraction for the rotated Heisenberg
adjoint, in the full-rank reference domain.

This is the first non-circular channel-specific contraction theorem in the
α > 1 DPI route: the proof uses the normalized PSD trace-pairing theorem and
Schatten duality, not a DPI or contraction hypothesis. -/
theorem sandwichedRenyiRotatedKrausAdjoint_qBall_of_beigi
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q)
    {B : CMatrix b} (hB : B.PosSemidef)
    (hBq : psdTracePower B hB q ≤ 1) :
    psdTracePower
        (MatrixMap.krausAdjoint
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B)
        (MatrixMap.krausAdjoint_mapsPositive
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B hB) q ≤
      1 := by
  exact
    sandwichedRenyiRotatedKrausAdjoint_qBall_of_tracePairingBound
      K σ (Φ.applyState σ) α q hpq hB
      (fun A hA =>
        sandwichedRenyiRotatedKraus_tracePairingBound_of_psdTracePower_le_one
          K σ Φ hK hσ hσΦ α q hα_gt_one hpq hA hB hBq)

/-- Exact dual formulation of the rotated-adjoint `q`-unit-ball contraction.

For a fixed positive output witness `B`, the rotated Heisenberg adjoint lies in
the input-side PSD `q`-unit ball iff the Schrödinger rotated Kraus map satisfies
the matching trace-pairing bound against every positive input test operator.
This is the Lean-level form of the remaining noncommutative interpolation
obligation in the α > 1 DPI route. -/
theorem sandwichedRenyiRotatedKrausAdjoint_qBall_iff_tracePairingBound
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (τ : State b) (α q : ℝ) (hpq : α.HolderConjugate q)
    {B : CMatrix b} (hB : B.PosSemidef) :
    psdTracePower
        (MatrixMap.krausAdjoint (sandwichedRenyiRotatedKraus σ τ K α) B)
        (MatrixMap.krausAdjoint_mapsPositive
          (sandwichedRenyiRotatedKraus σ τ K α) B hB) q ≤
      1 ↔
      ∀ A : CMatrix a, ∀ hA : A.PosSemidef,
        (((MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ τ K α) A) *
            B).trace).re ≤ psdSchattenPNorm A hA ⟨α, hpq.pos⟩ := by
  let L : κ → Matrix b a ℂ := sandwichedRenyiRotatedKraus σ τ K α
  have hdual_iff :=
    psdTracePower_le_one_iff_trace_mul_le_psdSchattenPNorm
      (MatrixMap.krausAdjoint_mapsPositive L B hB) hpq
  constructor
  · intro hq A hA
    have hdual := MatrixMap.ofKraus_trace_duality L A B
    have htrace :
        (((MatrixMap.ofKraus L A) * B).trace).re =
          ((A * MatrixMap.krausAdjoint L B).trace).re :=
      congrArg Complex.re hdual
    rw [htrace]
    exact hdual_iff.mp hq A hA
  · intro hbound
    exact hdual_iff.mpr (fun A hA => by
      have hdual := MatrixMap.ofKraus_trace_duality L A B
      have htrace :
          ((A * MatrixMap.krausAdjoint L B).trace).re =
            (((MatrixMap.ofKraus L A) * B).trace).re :=
        (congrArg Complex.re hdual).symm
      rw [htrace]
      exact hbound A hA)

/-- Endpoint-order subdomain of the rotated-adjoint `q`-unit-ball contraction.

Every positive output witness dominated by the dual reference endpoint
`(Φσ)^(1-1/α)` is sent by the rotated Heisenberg adjoint into the input
`q`-unit ball. This is a genuine q-ball theorem on the interpolation boundary;
the missing full contraction is the extension from this endpoint-order subdomain
to arbitrary positive output `q`-unit-ball witnesses. -/
theorem sandwichedRenyiRotatedKrausAdjoint_qBall_of_le_referenceDualPower
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q)
    {B : CMatrix b} (hB : B.PosSemidef)
    (hB_le : B ≤ CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)) :
    psdTracePower
        (MatrixMap.krausAdjoint
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B)
        (MatrixMap.krausAdjoint_mapsPositive
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B hB) q ≤
      1 := by
  let W : CMatrix a :=
    MatrixMap.krausAdjoint
      (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B
  have hWpos : W.PosSemidef := by
    simpa [W] using
      MatrixMap.krausAdjoint_mapsPositive
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B hB
  have hW_le :
      W ≤ CFC.rpow σ.matrix (1 - 1 / α) := by
    simpa [W] using
      sandwichedRenyiRotatedKrausAdjoint_le_referenceDualPower_of_le
        K σ Φ hK hσ hσΦ α hα_gt_one hB_le
  have hσ_trace : σ.matrix.trace.re = 1 := by
    rw [σ.trace_eq_one]
    norm_num
  have hr : 1 - 1 / α = 1 / q := by
    simpa [one_div] using hpq.one_sub_inv
  have hcriterion :=
    psdTracePower_le_one_of_trace_mul_le_psdSchattenPNorm
      hWpos hpq
      (fun A hA => by
        have htrace_le :
            ((A * W).trace).re ≤
              ((A * CFC.rpow σ.matrix (1 - 1 / α)).trace).re :=
          cMatrix_trace_mul_le_of_le_posSemidef_left hA hW_le
        have hholder :
            ((A * CFC.rpow σ.matrix (1 - 1 / α)).trace).re ≤
              psdSchattenPNorm A hA ⟨α, hpq.pos⟩ :=
          psd_trace_rpow_holder_variational_upper
            hA σ.pos hσ_trace hpq hr
        exact htrace_le.trans hholder)
  simpa [W] using hcriterion

/-- Boundary data for the α > 1 rotated-Kraus interpolation route.

This packages the two exact endpoint identities and their normalized
trace-power unit-ball checks. The remaining theorem needed for full α > 1 DPI
is the noncommutative interpolation step that turns these boundary data into a
Schatten contraction for arbitrary positive inputs. -/
theorem sandwichedRenyiRotatedKraus_interpolationBoundaryData
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q) :
    MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
        (CFC.rpow σ.matrix (1 / α)) =
      CFC.rpow (Φ.applyState σ).matrix (1 / α) ∧
    MatrixMap.krausAdjoint
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
        (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)) =
      CFC.rpow σ.matrix (1 - 1 / α) ∧
    psdTracePower
        (MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
          (CFC.rpow σ.matrix (1 / α)))
        (MatrixMap.ofKraus_mapsPositive
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
          (CFC.rpow σ.matrix (1 / α))
          (σ.rpowMatrix_posSemidef (1 / α)))
        α = 1 ∧
    psdTracePower
        (MatrixMap.krausAdjoint
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
          (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)))
        (MatrixMap.krausAdjoint_mapsPositive
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
          (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α))
          ((Φ.applyState σ).rpowMatrix_posSemidef (1 - 1 / α)))
        q = 1 := by
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  exact
    ⟨sandwichedRenyiRotatedKraus_apply_referencePower_eq
        K σ Φ hK hσ hσΦ α hα_gt_one,
      sandwichedRenyiRotatedKrausAdjoint_referenceDualPower_eq
        K σ Φ hTP hσ hσΦ α hα_gt_one,
      sandwichedRenyiRotatedKraus_apply_referencePower_psdTracePower_eq_one
        K σ Φ hK hσ hσΦ α hα_gt_one,
      sandwichedRenyiRotatedKrausAdjoint_referenceDualPower_psdTracePower_eq_one
        K σ Φ hK hσ hσΦ α q hα_gt_one hpq⟩

/-- Rotated Kraus endpoint normalization package for the α > 1 interpolation
route.

The pair of endpoint identities is the finite-dimensional normalization data
needed to turn the remaining analytic interpolation theorem into the desired
Schatten contraction. -/
theorem sandwichedRenyiRotatedKraus_interpolationEndpoints
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    MatrixMap.ofKraus (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
        (CFC.rpow σ.matrix (1 / α)) =
      CFC.rpow (Φ.applyState σ).matrix (1 / α) ∧
    MatrixMap.krausAdjoint
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α)
        (CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)) =
      CFC.rpow σ.matrix (1 - 1 / α) := by
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  exact
    ⟨sandwichedRenyiRotatedKraus_apply_referencePower_eq
        K σ Φ hK hσ hσΦ α hα_gt_one,
      sandwichedRenyiRotatedKrausAdjoint_referenceDualPower_eq
        K σ Φ hTP hσ hσΦ α hα_gt_one⟩

/-- The pulled-back input-side Holder witness is positive semidefinite whenever
the output witness is positive semidefinite. -/
theorem sandwichedRenyiKrausAdjointInputWitness_posSemidef
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) {B : CMatrix b} (hB : B.PosSemidef)
    (α : ℝ) :
    (sandwichedRenyiKrausAdjointInputWitness σ Φ K B α).PosSemidef := by
  let s : ℝ := (1 - α) / (2 * α)
  let D : CMatrix a := CFC.rpow σ.matrix (-s)
  have hD : D.PosSemidef := by
    simpa [D] using σ.rpowMatrix_posSemidef (-s)
  have hDstar : star D = D := hD.isHermitian.eq
  have hE :
      (MatrixMap.krausAdjoint K
        (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)).PosSemidef :=
    sandwichedRenyi_krausAdjoint_holderDualEffect_posSemidef K σ Φ hB α
  have hW : (star D *
      MatrixMap.krausAdjoint K
        (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α) * D).PosSemidef :=
    Matrix.PosSemidef.conjTranspose_mul_mul_same hE D
  rw [hDstar] at hW
  simpa [sandwichedRenyiKrausAdjointInputWitness, s, D] using hW

/-- At the Hilbert-Schmidt endpoint `α = 2`, the explicit Kraus-adjoint input
Holder witness has no larger `2`-power trace than the output Holder dual
effect.

This is the first fully closed unit-ball transport step for the α > 1
variational route. It combines the quarter-power sandwich inequality with
Kadison's inequality for the channel Heisenberg adjoint. -/
theorem sandwichedRenyiKrausAdjointInputWitness_tracePower_two_le
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (hσ : σ.matrix.PosDef) {B : CMatrix b} (hB : B.PosSemidef) :
    psdTracePower (sandwichedRenyiKrausAdjointInputWitness σ Φ K B (2 : ℝ))
        (sandwichedRenyiKrausAdjointInputWitness_posSemidef K σ Φ hB (2 : ℝ))
        (2 : ℝ) ≤
      psdTracePower (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B (2 : ℝ))
        (sandwichedRenyiHolderDualEffect_posSemidef (Φ.applyState σ) hB (2 : ℝ))
        (2 : ℝ) := by
  let E : CMatrix b := sandwichedRenyiHolderDualEffect (Φ.applyState σ) B (2 : ℝ)
  let A : CMatrix a := MatrixMap.krausAdjoint K E
  have hA : A.PosSemidef := by
    simpa [A, E] using
      sandwichedRenyi_krausAdjoint_holderDualEffect_posSemidef
        K σ Φ hB (2 : ℝ)
  have hquarter :=
    cMatrix_quarter_sandwich_tracePower_two_le σ hσ hA
  have hkadison :=
    sandwichedRenyi_holderDualEffect_tracePower_two_le
      K σ Φ hK hTP hB (2 : ℝ)
  have hleft :
      psdTracePower (sandwichedRenyiKrausAdjointInputWitness σ Φ K B (2 : ℝ))
          (sandwichedRenyiKrausAdjointInputWitness_posSemidef K σ Φ hB (2 : ℝ))
          (2 : ℝ) ≤
        ((σ.matrix * (A * A)).trace).re := by
    have hexp : -((1 - (2 : ℝ)) / (2 * (2 : ℝ))) = (1 / 4 : ℝ) := by
      norm_num
    simpa [sandwichedRenyiKrausAdjointInputWitness, E, A, hexp] using hquarter
  have hright :
      ((σ.matrix * (A * A)).trace).re ≤
        psdTracePower E
          (sandwichedRenyiHolderDualEffect_posSemidef (Φ.applyState σ) hB (2 : ℝ))
          (2 : ℝ) := by
    simpa [E, A] using hkadison
  exact hleft.trans hright

/-- Exact witness transport identity for the α > 1 Holder route.

The output trace pairing is rewritten as a trace pairing against the input
sandwiched inner operator with the explicit pulled-back input witness. The only
missing step for the full α > 1 theorem is proving this witness satisfies the
required `q`-unit-ball power-trace bound. -/
theorem sandwichedRenyi_inner_trace_eq_inputWitness
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (ρ σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (B : CMatrix b) (α : ℝ) :
    ((sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α * B).trace).re =
      (sandwichedRenyiInner ρ σ α *
        sandwichedRenyiKrausAdjointInputWitness σ Φ K B α).trace.re := by
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ.matrix s
  let D : CMatrix a := CFC.rpow σ.matrix (-s)
  let E : CMatrix a :=
    MatrixMap.krausAdjoint K
      (sandwichedRenyiHolderDualEffect (Φ.applyState σ) B α)
  have hCD : C * D = 1 := by
    simpa [C, D] using
      (CFC.rpow_mul_rpow_neg (a := σ.matrix) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  have hDC : D * C = 1 := by
    simpa [C, D] using
      (CFC.rpow_neg_mul_rpow (a := σ.matrix) s
        (ha := Matrix.PosDef.isStrictlyPositive hσ))
  have hinput :
      (sandwichedRenyiInner ρ σ α *
        sandwichedRenyiKrausAdjointInputWitness σ Φ K B α).trace =
        (ρ.matrix * E).trace := by
    change (((C * ρ.matrix * C) * (D * E * D)).trace) =
      (ρ.matrix * E).trace
    calc
      ((C * ρ.matrix * C) * (D * E * D)).trace =
          (C * (ρ.matrix * E) * D).trace := by
          congr 1
          calc
            (C * ρ.matrix * C) * (D * E * D) =
                C * ρ.matrix * (C * D) * E * D := by
                noncomm_ring
            _ = C * ρ.matrix * 1 * E * D := by rw [hCD]
            _ = C * (ρ.matrix * E) * D := by noncomm_ring
      _ = ((D * C) * (ρ.matrix * E)).trace := by
          exact Matrix.trace_mul_cycle C (ρ.matrix * E) D
      _ = (ρ.matrix * E).trace := by
          rw [hDC, Matrix.one_mul]
  have houtput :=
    sandwichedRenyi_inner_trace_eq_krausAdjoint_holderDualEffect
      K ρ σ Φ hK B α
  simpa [E] using houtput.trans (congrArg Complex.re hinput.symm)

/-- Trace-pairing bound obtained from the rotated-Kraus adjoint `q`-unit-ball
contraction.

This is the exact handoff from the noncommutative interpolation theorem to the
current `psdSchattenPNorm` variational interface: once the rotated adjoint sends
every positive output `q`-unit-ball witness to a positive input `q`-unit-ball
witness, Holder's variational bound gives the trace-pairing estimate required
for α > 1 DPI. -/
theorem sandwichedRenyi_traceHolderUnitBall_le_of_rotatedKrausAdjoint_qBall
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (ρ σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (α q : ℝ) (hpq : α.HolderConjugate q)
    (hrotated :
      ∀ B : CMatrix b, ∀ hB : B.PosSemidef,
        psdTracePower B hB q ≤ 1 →
          psdTracePower
            (MatrixMap.krausAdjoint
              (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B)
            (MatrixMap.krausAdjoint_mapsPositive
              (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B hB)
            q ≤ 1)
    (B : CMatrix b) (hB : B.PosSemidef)
    (hBq : psdTracePower B hB q ≤ 1) :
    ((sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α * B).trace).re ≤
      psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
        (sandwichedRenyiInner_posSemidef ρ σ α) ⟨α, hpq.pos⟩ := by
  have htrace :=
    sandwichedRenyi_inner_trace_eq_inputWitness K ρ σ Φ hK hσ B α
  have hinput_eq :=
    sandwichedRenyiKrausAdjointInputWitness_eq_rotatedKrausAdjoint
      K σ Φ B α
  rw [htrace, hinput_eq]
  exact
    posSemidef_trace_mul_le_psdSchattenPNorm_of_tracePower_le_one
      (sandwichedRenyiInner_posSemidef ρ σ α)
      (MatrixMap.krausAdjoint_mapsPositive
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B hB)
      hpq (le_of_lt hpq.symm.lt)
      (hrotated B hB hBq)

/-- The reference dual endpoint already satisfies the trace-pairing bound
needed by the α > 1 variational route.

This is not the full interpolation theorem, because it covers the single
endpoint witness `B = (Φσ)^(1-1/α)` rather than every positive `q`-unit-ball
witness. It is the endpoint case of the missing rotated-adjoint Schatten
contraction. -/
theorem sandwichedRenyi_referenceDualEndpoint_traceHolder_le
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (ρ σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q) :
    ((sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α *
        CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)).trace).re ≤
      psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
        (sandwichedRenyiInner_posSemidef ρ σ α)
        ⟨α, lt_trans zero_lt_one hα_gt_one⟩ := by
  let B : CMatrix b := CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)
  have htrace :=
    sandwichedRenyi_inner_trace_eq_inputWitness K ρ σ Φ hK hσ B α
  have hinput_eq :=
    sandwichedRenyiKrausAdjointInputWitness_eq_rotatedKrausAdjoint
      K σ Φ B α
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  have hendpoint :
      MatrixMap.krausAdjoint
          (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B =
        CFC.rpow σ.matrix (1 - 1 / α) := by
    simpa [B] using
      sandwichedRenyiRotatedKrausAdjoint_referenceDualPower_eq
        K σ Φ hTP hσ hσΦ α hα_gt_one
  rw [htrace, hinput_eq, hendpoint]
  exact
    posSemidef_trace_mul_le_psdSchattenPNorm_of_tracePower_le_one
      (sandwichedRenyiInner_posSemidef ρ σ α)
      (σ.rpowMatrix_posSemidef (1 - 1 / α))
      hpq (le_of_lt hpq.symm.lt)
      (le_of_eq (state_rpow_one_sub_inv_psdTracePower_eq_one σ hσ α q hpq))

/-- Trace-pairing bound for output witnesses dominated by the dual reference
endpoint.

This is an actual boundary estimate for the interpolation route: order
domination by `(Φσ)^(1-1/α)` is transported through the rotated adjoint to order
domination by `σ^(1-1/α)`, and the source-shaped Holder variational bound then
controls the input trace pairing by the input Schatten `α` expression. -/
theorem sandwichedRenyi_traceHolder_le_of_outputWitness_le_referenceDualPower
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (ρ σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hσ : σ.matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q)
    {B : CMatrix b} (hB : B.PosSemidef)
    (hB_le : B ≤ CFC.rpow (Φ.applyState σ).matrix (1 - 1 / α)) :
    ((sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α * B).trace).re ≤
      psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
        (sandwichedRenyiInner_posSemidef ρ σ α)
        ⟨α, lt_trans zero_lt_one hα_gt_one⟩ := by
  let W : CMatrix a :=
    MatrixMap.krausAdjoint
      (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B
  have htrace :=
    sandwichedRenyi_inner_trace_eq_inputWitness K ρ σ Φ hK hσ B α
  have hinput_eq :=
    sandwichedRenyiKrausAdjointInputWitness_eq_rotatedKrausAdjoint
      K σ Φ B α
  have hW_pos : W.PosSemidef := by
    simpa [W] using
      MatrixMap.krausAdjoint_mapsPositive
        (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B hB
  have hW_le :
      W ≤ CFC.rpow σ.matrix (1 - 1 / α) := by
    simpa [W] using
      sandwichedRenyiRotatedKrausAdjoint_le_referenceDualPower_of_le
        K σ Φ hK hσ hσΦ α hα_gt_one hB_le
  have htrace_le :
      ((sandwichedRenyiInner ρ σ α * W).trace).re ≤
        ((sandwichedRenyiInner ρ σ α *
          CFC.rpow σ.matrix (1 - 1 / α)).trace).re :=
    cMatrix_trace_mul_le_of_le_posSemidef_left
      (sandwichedRenyiInner_posSemidef ρ σ α) hW_le
  have hσ_trace : σ.matrix.trace.re = 1 := by
    rw [σ.trace_eq_one]
    norm_num
  have hr : 1 - 1 / α = 1 / q := by
    simpa [one_div] using hpq.one_sub_inv
  have hholder :
      ((sandwichedRenyiInner ρ σ α *
          CFC.rpow σ.matrix (1 - 1 / α)).trace).re ≤
        psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α)
          ⟨α, lt_trans zero_lt_one hα_gt_one⟩ :=
    psd_trace_rpow_holder_variational_upper
      (sandwichedRenyiInner_posSemidef ρ σ α) σ.pos hσ_trace hpq hr
  rw [htrace, hinput_eq]
  exact htrace_le.trans hholder

/-- Channel-level Kraus witness package for the α > 1 Holder route.

For every channel and output-side positive Holder witness, the channel's CP/TP
data supplies a Kraus representation whose Heisenberg adjoint is unital, whose
pulled-back input witness is PSD, and whose trace pairing is exactly the output
pairing. The remaining hard theorem is the q-unit-ball power-trace bound for
this witness. -/
theorem sandwichedRenyi_exists_kraus_inputWitness
    (ρ σ : State a) (Φ : Channel a b)
    (hσ : σ.matrix.PosDef) {B : CMatrix b} (hB : B.PosSemidef) (α : ℝ) :
    ∃ K : (a × b) → Matrix b a ℂ,
      Φ.map = MatrixMap.ofKraus K ∧
      MatrixMap.krausAdjoint K (1 : CMatrix b) = 1 ∧
      (sandwichedRenyiKrausAdjointInputWitness σ Φ K B α).PosSemidef ∧
      ((sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α * B).trace).re =
        (sandwichedRenyiInner ρ σ α *
          sandwichedRenyiKrausAdjointInputWitness σ Φ K B α).trace.re := by
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  refine ⟨K, hK, MatrixMap.krausAdjoint_one_of_tracePreserving K hTP, ?_, ?_⟩
  · exact sandwichedRenyiKrausAdjointInputWitness_posSemidef K σ Φ hB α
  · exact sandwichedRenyi_inner_trace_eq_inputWitness K ρ σ Φ hK hσ B α

/-- A positive output-side Holder unit-ball witness is pulled back by a
trace-preserving Kraus channel to an input-side effect.

This is a non-circular CP/TP ingredient for the `α > 1` variational route: the
remaining hard step is the weighted `q`-unit-ball estimate after the additional
reference conjugations in `sandwichedRenyiKrausAdjointInputWitness`. -/
theorem sandwichedRenyi_krausAdjoint_outputWitness_effect
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    {B : CMatrix b} (hB : B.PosSemidef) {q : ℝ} (hq : 0 < q)
    (hBq : psdTracePower B hB q ≤ 1) :
    (MatrixMap.krausAdjoint K B).PosSemidef ∧ MatrixMap.krausAdjoint K B ≤ 1 :=
  MatrixMap.krausAdjoint_effect_of_tracePreserving K hTP hB
    (posSemidef_le_one_of_psdTracePower_le_one hB hq hBq)

/-- Channel-level form of `sandwichedRenyi_krausAdjoint_outputWitness_effect`
using the channel's Choi-positive Kraus representation. -/
theorem sandwichedRenyi_exists_kraus_outputWitness_effect
    (Φ : Channel a b) {B : CMatrix b} (hB : B.PosSemidef)
    {q : ℝ} (hq : 0 < q) (hBq : psdTracePower B hB q ≤ 1) :
    ∃ K : (a × b) → Matrix b a ℂ,
      Φ.map = MatrixMap.ofKraus K ∧
      MatrixMap.krausAdjoint K (1 : CMatrix b) = 1 ∧
      (MatrixMap.krausAdjoint K B).PosSemidef ∧
      MatrixMap.krausAdjoint K B ≤ 1 := by
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  refine ⟨K, hK, MatrixMap.krausAdjoint_one_of_tracePreserving K hTP, ?_, ?_⟩
  · exact (sandwichedRenyi_krausAdjoint_outputWitness_effect K hTP hB hq hBq).1
  · exact (sandwichedRenyi_krausAdjoint_outputWitness_effect K hTP hB hq hBq).2

/-- Every channel admits a Kraus representation whose Stinespring stack is an
isometry, with PSD orthogonal-complement projection.

This is the channel-level projection-positivity ingredient for the next
Kadison/variance step in the α > 1 Holder route. It uses only CP/TP channel
data and does not assume any DPI or contraction statement. -/
theorem sandwichedRenyi_exists_kraus_stinespring_projection
    (Φ : Channel a b) :
    ∃ K : (a × b) → Matrix b a ℂ,
      Φ.map = MatrixMap.ofKraus K ∧
      MatrixMap.krausAdjoint K (1 : CMatrix b) = 1 ∧
      (1 - MatrixMap.krausStinespringMatrix K *
          Matrix.conjTranspose (MatrixMap.krausStinespringMatrix K)).PosSemidef := by
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  have hAdj : MatrixMap.krausAdjoint K (1 : CMatrix b) = 1 :=
    MatrixMap.krausAdjoint_one_of_tracePreserving K hTP
  refine ⟨K, hK, hAdj, ?_⟩
  exact MatrixMap.krausStinespringMatrix_projection_complement_posSemidef K hAdj

/-- Every channel admits a Kraus representation whose Heisenberg adjoint
satisfies Kadison's inequality.

This is the first channel-specific operator inequality on the α > 1
Holder/variational route. It uses only CP/TP channel data and the Stinespring
projection positivity, not any DPI or contraction hypothesis. -/
theorem sandwichedRenyi_exists_kraus_kadison
    (Φ : Channel a b) :
    ∃ K : (a × b) → Matrix b a ℂ,
      Φ.map = MatrixMap.ofKraus K ∧
      MatrixMap.krausAdjoint K (1 : CMatrix b) = 1 ∧
      ∀ E : CMatrix b, E.IsHermitian →
        MatrixMap.krausAdjoint K E * MatrixMap.krausAdjoint K E ≤
          MatrixMap.krausAdjoint K (E * E) := by
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  have hAdj : MatrixMap.krausAdjoint K (1 : CMatrix b) = 1 :=
    MatrixMap.krausAdjoint_one_of_tracePreserving K hTP
  refine ⟨K, hK, hAdj, ?_⟩
  intro E hE
  exact MatrixMap.krausAdjoint_mul_self_le_of_krausAdjoint_one K hAdj hE

/-- At the endpoint `α = 1/2`, the sandwiched Renyi trace-power kernel is the
root fidelity `F(ρ,σ)`.

This is the definition bridge from the local sandwiched-Renyi API to the proved
Uhlmann/fidelity monotonicity theorem. -/
theorem sandwichedRenyiInner_psdTracePower_half_eq_fidelity
    (ρ σ : State a) :
    psdTracePower (sandwichedRenyiInner ρ σ (1 / 2 : ℝ))
        (sandwichedRenyiInner_posSemidef ρ σ (1 / 2 : ℝ)) (1 / 2 : ℝ) =
      ρ.fidelity σ := by
  have hinner :
      sandwichedRenyiInner ρ σ (1 / 2 : ℝ) =
        Matrix.conjTranspose (ρ.sqrtMatrix * σ.sqrtMatrix) *
          (ρ.sqrtMatrix * σ.sqrtMatrix) := by
    have hexp :
        (1 - (1 / 2 : ℝ)) / (2 * (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
      norm_num
    calc
      sandwichedRenyiInner ρ σ (1 / 2 : ℝ) =
          σ.sqrtMatrix * ρ.matrix * σ.sqrtMatrix := by
            unfold sandwichedRenyiInner
            rw [hexp]
            simp [State.sqrtMatrix, psdSqrt, CFC.sqrt_eq_rpow]
      _ = Matrix.conjTranspose (ρ.sqrtMatrix * σ.sqrtMatrix) *
            (ρ.sqrtMatrix * σ.sqrtMatrix) := by
            rw [Matrix.conjTranspose_mul, σ.sqrtMatrix_isHermitian.eq,
              ρ.sqrtMatrix_isHermitian.eq, ← ρ.sqrtMatrix_mul_self]
            noncomm_ring
  unfold psdTracePower State.fidelity traceNorm
  rw [hinner]
  simp [psdSqrt, CFC.sqrt_eq_rpow]

/-- The `α = 1/2` endpoint of full-rank sandwiched Renyi DPI for a general
finite-dimensional channel.

This theorem is non-circular: it uses the proved Uhlmann/fidelity monotonicity
for channels, together with the endpoint bridge
`sandwichedRenyiInner_psdTracePower_half_eq_fidelity`. It is a genuine endpoint
subcase, not the full source theorem over all
`α ∈ [1/2,1) ∪ (1,∞)`. -/
theorem sandwichedRenyi_dataProcessing_channel_statement_half
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ hρ hσ hρΦ hσΦ
      (1 / 2 : ℝ) (by norm_num) (by norm_num) := by
  have hfid_sq := State.squaredFidelity_le_applyState_squaredFidelity Φ ρ σ
  have hfid :
      ρ.fidelity σ ≤ (Φ.applyState ρ).fidelity (Φ.applyState σ) := by
    rw [State.squaredFidelity_eq_fidelity_sq,
      State.squaredFidelity_eq_fidelity_sq] at hfid_sq
    exact (sq_le_sq₀ (State.fidelity_nonneg ρ σ)
      (State.fidelity_nonneg (Φ.applyState ρ) (Φ.applyState σ))).mp hfid_sq
  have hpower :
      psdTracePower (sandwichedRenyiInner ρ σ (1 / 2 : ℝ))
          (sandwichedRenyiInner_posSemidef ρ σ (1 / 2 : ℝ)) (1 / 2 : ℝ) ≤
        psdTracePower
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) (1 / 2 : ℝ))
          (sandwichedRenyiInner_posSemidef
            (Φ.applyState ρ) (Φ.applyState σ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    rw [sandwichedRenyiInner_psdTracePower_half_eq_fidelity ρ σ,
      sandwichedRenyiInner_psdTracePower_half_eq_fidelity
        (Φ.applyState ρ) (Φ.applyState σ)]
    exact hfid
  unfold sandwichedRenyi_dataProcessing_channel_statement
  rw [sandwichedRenyi_eq_log2_psdTracePower_inner
      (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ (1 / 2 : ℝ)
      (by norm_num) (by norm_num),
    sandwichedRenyi_eq_log2_psdTracePower_inner
      ρ σ hρ hσ (1 / 2 : ℝ) (by norm_num) (by norm_num)]
  have hin_pos :
      0 <
        psdTracePower (sandwichedRenyiInner ρ σ (1 / 2 : ℝ))
          (sandwichedRenyiInner_posSemidef ρ σ (1 / 2 : ℝ)) (1 / 2 : ℝ) :=
    sandwichedRenyiInner_psdTracePower_pos ρ σ hρ hσ (1 / 2 : ℝ)
  have hlog := log2_mono_of_pos hin_pos hpower
  have hcoef : 1 / ((1 / 2 : ℝ) - 1) = -2 := by norm_num
  rw [hcoef]
  exact mul_le_mul_of_nonpos_left hlog (by norm_num)

/-- Classical stochastic channels satisfy the full-rank sandwiched Renyi DPI
statement for diagonal full-support inputs in the `α > 1` range.

This is a genuine channel primitive for the pinching/classical route; it uses
the CPTP `Classical.stochasticChannel` implementation and the proved classical
power-sum DPI, not a DPI hypothesis. -/
theorem sandwichedRenyi_dataProcessing_classicalStochasticChannel_statement_one_lt
    (p q : a → ℝ≥0) (T : a → b → ℝ≥0)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hT_sum : ∀ i, ∑ y, T i y = 1)
    (hp_pos : ∀ i, 0 < (p i : ℝ)) (hq_pos : ∀ i, 0 < (q i : ℝ))
    (hpOut_pos : ∀ y, 0 < (Classical.stochasticOutput p T y : ℝ))
    (hqOut_pos : ∀ y, 0 < (Classical.stochasticOutput q T y : ℝ))
    (α : ℝ) (hα_gt_one : 1 < α) :
    sandwichedRenyi_dataProcessing_channel_statement
      (Classical.diagonalState p hp_sum) (Classical.diagonalState q hq_sum)
      (Classical.stochasticChannel T hT_sum)
      (Classical.diagonalState_posDef p hp_sum hp_pos)
      (Classical.diagonalState_posDef q hq_sum hq_pos)
      (by
        rw [Classical.stochasticChannel_applyState_diagonalState]
        exact Classical.diagonalState_posDef
          (Classical.stochasticOutput p T)
          (Classical.stochasticOutput_sum p T hp_sum hT_sum) hpOut_pos)
      (by
        rw [Classical.stochasticChannel_applyState_diagonalState]
        exact Classical.diagonalState_posDef
          (Classical.stochasticOutput q T)
          (Classical.stochasticOutput_sum q T hq_sum hT_sum) hqOut_pos)
      α (by linarith) (ne_of_gt hα_gt_one) := by
  classical
  simpa [sandwichedRenyi_dataProcessing_channel_statement,
    Classical.stochasticChannel_applyState_diagonalState] using
    sandwichedRenyi_diagonalState_stochastic_le_of_one_lt
    p q (Classical.stochasticOutput p T) (Classical.stochasticOutput q T)
    (fun i y => (T i y : ℝ)) hp_sum hq_sum hp_pos hq_pos
    (Classical.stochasticOutput_sum p T hp_sum hT_sum)
    (Classical.stochasticOutput_sum q T hq_sum hT_sum)
    hpOut_pos hqOut_pos
    (fun i y => NNReal.coe_nonneg (T i y))
    (fun i => by
      change ∑ y, ((T i y : ℝ≥0) : ℝ) = 1
      exact_mod_cast hT_sum i)
    (fun y => by simp [Classical.stochasticOutput, NNReal.coe_sum, NNReal.coe_mul])
    (fun y => by simp [Classical.stochasticOutput, NNReal.coe_sum, NNReal.coe_mul])
    α hα_gt_one

/-- Classical stochastic channels satisfy the full-rank sandwiched Renyi DPI
statement for diagonal full-support inputs in the `0 < α < 1` range. -/
theorem sandwichedRenyi_dataProcessing_classicalStochasticChannel_statement_lt_one
    (p q : a → ℝ≥0) (T : a → b → ℝ≥0)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hT_sum : ∀ i, ∑ y, T i y = 1)
    (hp_pos : ∀ i, 0 < (p i : ℝ)) (hq_pos : ∀ i, 0 < (q i : ℝ))
    (hpOut_pos : ∀ y, 0 < (Classical.stochasticOutput p T y : ℝ))
    (hqOut_pos : ∀ y, 0 < (Classical.stochasticOutput q T y : ℝ))
    (α : ℝ) (hα_half : 1 / 2 ≤ α) (hα_lt_one : α < 1) :
    sandwichedRenyi_dataProcessing_channel_statement
      (Classical.diagonalState p hp_sum) (Classical.diagonalState q hq_sum)
      (Classical.stochasticChannel T hT_sum)
      (Classical.diagonalState_posDef p hp_sum hp_pos)
      (Classical.diagonalState_posDef q hq_sum hq_pos)
      (by
        rw [Classical.stochasticChannel_applyState_diagonalState]
        exact Classical.diagonalState_posDef
          (Classical.stochasticOutput p T)
          (Classical.stochasticOutput_sum p T hp_sum hT_sum) hpOut_pos)
      (by
        rw [Classical.stochasticChannel_applyState_diagonalState]
        exact Classical.diagonalState_posDef
          (Classical.stochasticOutput q T)
          (Classical.stochasticOutput_sum q T hq_sum hT_sum) hqOut_pos)
      α hα_half (ne_of_lt hα_lt_one) := by
  classical
  simpa [sandwichedRenyi_dataProcessing_channel_statement,
    Classical.stochasticChannel_applyState_diagonalState] using
    sandwichedRenyi_diagonalState_stochastic_le_of_lt_one
    p q (Classical.stochasticOutput p T) (Classical.stochasticOutput q T)
    (fun i y => (T i y : ℝ)) hp_sum hq_sum hp_pos hq_pos
    (Classical.stochasticOutput_sum p T hp_sum hT_sum)
    (Classical.stochasticOutput_sum q T hq_sum hT_sum)
    hpOut_pos hqOut_pos
    (fun i y => NNReal.coe_nonneg (T i y))
    (fun i => by
      change ∑ y, ((T i y : ℝ≥0) : ℝ) = 1
      exact_mod_cast hT_sum i)
    (fun y => by simp [Classical.stochasticOutput, NNReal.coe_sum, NNReal.coe_mul])
    (fun y => by simp [Classical.stochasticOutput, NNReal.coe_sum, NNReal.coe_mul])
    α (by linarith) hα_lt_one

/-- Classical stochastic channels satisfy the local full-rank sandwiched Renyi
DPI statement throughout the source range `1/2 ≤ α < 1` or `1 < α`, for
full-support diagonal inputs and full-support pushed-forward references. -/
theorem sandwichedRenyi_dataProcessing_classicalStochasticChannel_statement
    (p q : a → ℝ≥0) (T : a → b → ℝ≥0)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hT_sum : ∀ i, ∑ y, T i y = 1)
    (hp_pos : ∀ i, 0 < (p i : ℝ)) (hq_pos : ∀ i, 0 < (q i : ℝ))
    (hpOut_pos : ∀ y, 0 < (Classical.stochasticOutput p T y : ℝ))
    (hqOut_pos : ∀ y, 0 < (Classical.stochasticOutput q T y : ℝ))
    (α : ℝ) (hα_range : (1 / 2 ≤ α ∧ α < 1) ∨ 1 < α) :
    sandwichedRenyi_dataProcessing_channel_statement
      (Classical.diagonalState p hp_sum) (Classical.diagonalState q hq_sum)
      (Classical.stochasticChannel T hT_sum)
      (Classical.diagonalState_posDef p hp_sum hp_pos)
      (Classical.diagonalState_posDef q hq_sum hq_pos)
      (by
        rw [Classical.stochasticChannel_applyState_diagonalState]
        exact Classical.diagonalState_posDef
          (Classical.stochasticOutput p T)
          (Classical.stochasticOutput_sum p T hp_sum hT_sum) hpOut_pos)
      (by
        rw [Classical.stochasticChannel_applyState_diagonalState]
        exact Classical.diagonalState_posDef
          (Classical.stochasticOutput q T)
          (Classical.stochasticOutput_sum q T hq_sum hT_sum) hqOut_pos)
      α
      (by
        rcases hα_range with hlt | hgt
        · exact hlt.1
        · linarith)
      (by
        rcases hα_range with hlt | hgt
        · exact ne_of_lt hlt.2
        · exact ne_of_gt hgt) := by
  rcases hα_range with hlt | hgt
  · exact sandwichedRenyi_dataProcessing_classicalStochasticChannel_statement_lt_one
      p q T hp_sum hq_sum hT_sum hp_pos hq_pos hpOut_pos hqOut_pos α hlt.1 hlt.2
  · exact sandwichedRenyi_dataProcessing_classicalStochasticChannel_statement_one_lt
      p q T hp_sum hq_sum hT_sum hp_pos hq_pos hpOut_pos hqOut_pos α hgt

/-- Reference-spectral pinching commutes with the sandwiched inner operator:
pinching the state first is the same as pinching the sandwiched inner operator
in the reference eigenbasis. -/
theorem sandwichedRenyiInner_referenceSpectralPinching_eq_pinchingMap
    (ρ σ : State a) (α : ℝ) :
    sandwichedRenyiInner
        (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel
          ).applyState ρ)
        σ α =
      (ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingMap
        (sandwichedRenyiInner ρ σ α) := by
  classical
  let U : Matrix.unitaryGroup a ℂ := σ.pos.isHermitian.eigenvectorUnitary
  let P : ProjectiveMeasurement a a :=
    ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
  let s : ℝ := (1 - α) / (2 * α)
  let C : CMatrix a := CFC.rpow σ.matrix s
  let D : CMatrix a :=
    Matrix.diagonal
      (fun i => ((σ.pos.isHermitian.eigenvalues i ^ s : ℝ) : ℂ))
  let Y : CMatrix a := star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)
  let Ydiag : CMatrix a := Matrix.diagonal fun i => Y i i
  let A : CMatrix a :=
    sandwichedRenyiInner (P.pinchingChannel.applyState ρ) σ α
  let B : CMatrix a := P.pinchingMap (sandwichedRenyiInner ρ σ α)
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
    Unitary.coe_star_mul_self U
  have hUUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 :=
    Unitary.coe_mul_star_self U
  have hC : C = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [C, D, U] using cMatrix_rpow_eq_eigenbasis_diagonal σ.pos s
  have hC_conj : star (U : CMatrix a) * C * (U : CMatrix a) = D := by
    calc
      star (U : CMatrix a) * C * (U : CMatrix a) =
          star (U : CMatrix a) * ((U : CMatrix a) * D * star (U : CMatrix a)) *
            (U : CMatrix a) := by rw [hC]
      _ = (star (U : CMatrix a) * (U : CMatrix a)) * D *
            (star (U : CMatrix a) * (U : CMatrix a)) := by noncomm_ring
      _ = D := by rw [hUstarU]; simp
  have hPρ_conj :
      star (U : CMatrix a) * (P.pinchingChannel.applyState ρ).matrix *
          (U : CMatrix a) = Ydiag := by
    simpa [P, U, Y, Ydiag] using
      ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_eigenbasis ρ σ
  have hinner_conj :
      star (U : CMatrix a) * sandwichedRenyiInner ρ σ α * (U : CMatrix a) =
        D * Y * D := by
    calc
      star (U : CMatrix a) * sandwichedRenyiInner ρ σ α * (U : CMatrix a) =
          star (U : CMatrix a) * (C * ρ.matrix * C) * (U : CMatrix a) := by
            rfl
      _ = star (U : CMatrix a) *
            (((U : CMatrix a) * D * star (U : CMatrix a)) * ρ.matrix *
              ((U : CMatrix a) * D * star (U : CMatrix a))) *
            (U : CMatrix a) := by rw [hC]
      _ = (star (U : CMatrix a) * (U : CMatrix a)) * D *
            (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) * D *
            (star (U : CMatrix a) * (U : CMatrix a)) := by
            noncomm_ring
      _ = D * Y * D := by rw [hUstarU]; simp [Y, Matrix.mul_assoc]
  have hA_conj :
      star (U : CMatrix a) * A * (U : CMatrix a) = D * Ydiag * D := by
    calc
      star (U : CMatrix a) * A * (U : CMatrix a) =
          star (U : CMatrix a) *
              (C * (P.pinchingChannel.applyState ρ).matrix * C) *
            (U : CMatrix a) := by
            rfl
      _ = star (U : CMatrix a) *
            (((U : CMatrix a) * D * star (U : CMatrix a)) *
              (P.pinchingChannel.applyState ρ).matrix *
              ((U : CMatrix a) * D * star (U : CMatrix a))) *
            (U : CMatrix a) := by rw [hC]
      _ = (star (U : CMatrix a) * (U : CMatrix a)) * D *
            (star (U : CMatrix a) * (P.pinchingChannel.applyState ρ).matrix *
              (U : CMatrix a)) * D *
            (star (U : CMatrix a) * (U : CMatrix a)) := by
            noncomm_ring
      _ = D *
            (star (U : CMatrix a) * (P.pinchingChannel.applyState ρ).matrix *
              (U : CMatrix a)) * D := by
            rw [hUstarU]
            simp [Matrix.mul_assoc]
      _ = D * Ydiag * D := by rw [hPρ_conj]
  have hB_conj :
      star (U : CMatrix a) * B * (U : CMatrix a) =
        Matrix.diagonal (fun i => (D * Y * D) i i) := by
    simpa [B, P, U, hinner_conj] using
      ProjectiveMeasurement.ofHermitianEigenbasis_pinchingMap_eigenbasis
        σ.matrix σ.pos.isHermitian (sandwichedRenyiInner ρ σ α)
  have hDYD_diag :
      D * Ydiag * D = Matrix.diagonal (fun i => (D * Y * D) i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Ydiag, Matrix.mul_apply, Matrix.diagonal]
    · simp [D, Ydiag, Matrix.mul_apply, Matrix.diagonal, hij]
  have hconj : star (U : CMatrix a) * A * (U : CMatrix a) =
      star (U : CMatrix a) * B * (U : CMatrix a) := by
    rw [hA_conj, hB_conj, hDYD_diag]
  have hreconstruct_A :
      (U : CMatrix a) * (star (U : CMatrix a) * A * (U : CMatrix a)) *
        star (U : CMatrix a) = A := by
    calc
      (U : CMatrix a) * (star (U : CMatrix a) * A * (U : CMatrix a)) *
          star (U : CMatrix a) =
          ((U : CMatrix a) * star (U : CMatrix a)) * A *
            ((U : CMatrix a) * star (U : CMatrix a)) := by
            noncomm_ring
      _ = A := by rw [hUUstar]; simp
  have hreconstruct_B :
      (U : CMatrix a) * (star (U : CMatrix a) * A * (U : CMatrix a)) *
        star (U : CMatrix a) =
      (U : CMatrix a) * (star (U : CMatrix a) * B * (U : CMatrix a)) *
        star (U : CMatrix a) := by
    rw [hconj]
  have hreconstruct_B_final :
      (U : CMatrix a) * (star (U : CMatrix a) * B * (U : CMatrix a)) *
        star (U : CMatrix a) = B := by
    calc
      (U : CMatrix a) * (star (U : CMatrix a) * B * (U : CMatrix a)) *
          star (U : CMatrix a) =
          ((U : CMatrix a) * star (U : CMatrix a)) * B *
            ((U : CMatrix a) * star (U : CMatrix a)) := by
            noncomm_ring
      _ = B := by rw [hUUstar]; simp
  calc
    sandwichedRenyiInner (P.pinchingChannel.applyState ρ) σ α = A := rfl
    _ = (U : CMatrix a) * (star (U : CMatrix a) * A * (U : CMatrix a)) *
          star (U : CMatrix a) := hreconstruct_A.symm
    _ = (U : CMatrix a) * (star (U : CMatrix a) * B * (U : CMatrix a)) *
          star (U : CMatrix a) := hreconstruct_B
    _ = B := hreconstruct_B_final
    _ = P.pinchingMap (sandwichedRenyiInner ρ σ α) := rfl

/-- Trace-power contraction for the sandwiched inner operator under reference
spectral pinching, in the `α ≥ 1` range. -/
theorem sandwichedRenyiInner_referenceSpectralPinching_tracePower_le_of_one_le
    (ρ σ : State a) (α : ℝ) (hα : 1 ≤ α) :
    psdTracePower
        (sandwichedRenyiInner
          (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
            ).pinchingChannel).applyState ρ)
          σ α)
        (sandwichedRenyiInner_posSemidef
          (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
            ).pinchingChannel).applyState ρ)
          σ α)
        α ≤
      psdTracePower (sandwichedRenyiInner ρ σ α)
        (sandwichedRenyiInner_posSemidef ρ σ α) α := by
  classical
  let P : ProjectiveMeasurement a a :=
    ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
  have hpinch :=
    ProjectiveMeasurement.ofHermitianEigenbasis_pinchingMap_psdTracePower_le
      σ.matrix σ.pos.isHermitian
      (X := sandwichedRenyiInner ρ σ α)
      (sandwichedRenyiInner_posSemidef ρ σ α)
      (q := α) hα
  simpa [P, sandwichedRenyiInner_referenceSpectralPinching_eq_pinchingMap ρ σ α]
    using hpinch

/-- Trace-power expansion for the sandwiched inner operator under reference
spectral pinching, in the `0 ≤ α ≤ 1` range. -/
theorem sandwichedRenyiInner_referenceSpectralPinching_tracePower_ge_of_le_one
    (ρ σ : State a) (α : ℝ) (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1) :
    psdTracePower (sandwichedRenyiInner ρ σ α)
        (sandwichedRenyiInner_posSemidef ρ σ α) α ≤
      psdTracePower
        (sandwichedRenyiInner
          (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
            ).pinchingChannel).applyState ρ)
          σ α)
        (sandwichedRenyiInner_posSemidef
          (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
            ).pinchingChannel).applyState ρ)
          σ α)
        α := by
  classical
  let P : ProjectiveMeasurement a a :=
    ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
  have hpinch :=
    ProjectiveMeasurement.ofHermitianEigenbasis_pinchingMap_psdTracePower_ge
      σ.matrix σ.pos.isHermitian
      (X := sandwichedRenyiInner ρ σ α)
      (sandwichedRenyiInner_posSemidef ρ σ α)
      (p := α) hα_nonneg hα_le_one
  simpa [P, sandwichedRenyiInner_referenceSpectralPinching_eq_pinchingMap ρ σ α]
    using hpinch

/-- For `α > 1`, a core trace-power contraction for the sandwiched inner
operator implies the full-rank channel DPI inequality.

This is the non-circular bridge from the operator-inequality part of the
sandwiched-Renyi proof route to the logarithmic public statement. It does not
assume DPI; the remaining hard obligation is the trace-power inequality in
`hpower`. -/
theorem sandwichedRenyi_dataProcessing_le_of_inner_tracePower_le_of_one_lt
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α)
    (hpower :
      psdTracePower (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α) α ≤
        psdTracePower (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (lt_trans zero_lt_one hα_gt_one)
        (ne_of_gt hα_gt_one) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_gt_one
  have hα_ne_one : α ≠ 1 := ne_of_gt hα_gt_one
  rw [sandwichedRenyi_eq_log2_psdTracePower_inner
      (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ α hα_pos hα_ne_one,
    sandwichedRenyi_eq_log2_psdTracePower_inner
      ρ σ hρ hσ α hα_pos hα_ne_one]
  have hout_pos :
      0 <
        psdTracePower
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
          α :=
    sandwichedRenyiInner_psdTracePower_pos
      (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ α
  have hlog := log2_mono_of_pos hout_pos hpower
  have hcoef_nonneg : 0 ≤ 1 / (α - 1) := by
    exact le_of_lt (one_div_pos.2 (sub_pos.mpr hα_gt_one))
  exact mul_le_mul_of_nonneg_left hlog hcoef_nonneg

/-- For `α > 1`, a Schatten-norm contraction for the sandwiched inner operator
implies the full-rank channel DPI inequality.

This is the variational-route handoff immediately after the Holder unit-ball
step: once the channel-specific argument proves contraction of the positive
inner operator's PSD Schatten expression, the Renyi DPI follows. -/
theorem sandwichedRenyi_dataProcessing_le_of_inner_schattenPNorm_le_of_one_lt
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α)
    (hnorm :
      psdSchattenPNorm
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
          ⟨α, lt_trans zero_lt_one hα_gt_one⟩ ≤
        psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α)
          ⟨α, lt_trans zero_lt_one hα_gt_one⟩) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (lt_trans zero_lt_one hα_gt_one)
        (ne_of_gt hα_gt_one) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_gt_one
  have hpower :
      psdTracePower (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α) α ≤
        psdTracePower (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α :=
    psdTracePower_le_of_psdSchattenPNorm_le
      (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
      (sandwichedRenyiInner_posSemidef ρ σ α)
      hα_pos
      (sandwichedRenyiInner_psdTracePower_pos
        (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ α)
      (sandwichedRenyiInner_psdTracePower_pos ρ σ hρ hσ α)
      hnorm
  exact sandwichedRenyi_dataProcessing_le_of_inner_tracePower_le_of_one_lt
    ρ σ Φ hρ hσ hρΦ hσΦ α hα_gt_one hpower

/-- The reference-spectral pinching channel satisfies the full-rank sandwiched
Renyi DPI in the `α > 1` range. -/
theorem sandwichedRenyi_dataProcessing_referenceSpectralPinching_channel_statement_one_lt
    (ρ σ : State a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρP :
      (((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
        ).pinchingChannel).applyState ρ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ
      ((ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
        ).pinchingChannel)
      hρ hσ hρP
      (by
        rw [ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_self]
        exact hσ)
      α (by linarith) (ne_of_gt hα_gt_one) := by
  classical
  let P : ProjectiveMeasurement a a :=
    ProjectiveMeasurement.ofHermitianEigenbasis σ.matrix σ.pos.isHermitian
  have hσP_eq : P.pinchingChannel.applyState σ = σ := by
    simpa [P] using
      ProjectiveMeasurement.ofHermitianEigenbasis_pinchingChannel_applyState_self σ
  have hσP : (P.pinchingChannel.applyState σ).matrix.PosDef := by
    rw [hσP_eq]
    exact hσ
  have hpower :
      psdTracePower
          (sandwichedRenyiInner (P.pinchingChannel.applyState ρ)
            (P.pinchingChannel.applyState σ) α)
          (sandwichedRenyiInner_posSemidef
            (P.pinchingChannel.applyState ρ) (P.pinchingChannel.applyState σ) α)
          α ≤
        psdTracePower (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α) α := by
    simpa [hσP_eq, P] using
      sandwichedRenyiInner_referenceSpectralPinching_tracePower_le_of_one_le
        ρ σ α (le_of_lt hα_gt_one)
  have hDPI :=
    sandwichedRenyi_dataProcessing_le_of_inner_tracePower_le_of_one_lt
      ρ σ P.pinchingChannel hρ hσ hρP hσP α hα_gt_one hpower
  simpa [sandwichedRenyi_dataProcessing_channel_statement, P, hσP_eq] using hDPI

/-- For `α > 1`, the Holder variational formula reduces full-rank channel DPI
to a unit-ball trace-pairing bound for every positive output-side dual witness.

The remaining channel-specific obligation is `hbound`: transport an arbitrary
PSD `q`-unit-ball witness on the output side through the Heisenberg adjoint (or
an equivalent Stinespring/pinching construction) and compare the resulting trace
pairing with the input-side sandwiched inner operator. -/
theorem sandwichedRenyi_dataProcessing_le_of_traceHolderUnitBall_le_of_one_lt
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q)
    (hbound : ∀ B : CMatrix b, ∀ hB : B.PosSemidef,
      psdTracePower B hB q ≤ 1 →
        ((sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α * B).trace).re ≤
          psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
            (sandwichedRenyiInner_posSemidef ρ σ α)
            ⟨α, lt_trans zero_lt_one hα_gt_one⟩) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (lt_trans zero_lt_one hα_gt_one)
        (ne_of_gt hα_gt_one) := by
  have hnorm :
      psdSchattenPNorm
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
          ⟨α, lt_trans zero_lt_one hα_gt_one⟩ ≤
        psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α)
          ⟨α, lt_trans zero_lt_one hα_gt_one⟩ :=
    psdSchattenPNorm_le_of_traceHolderUnitBall_le
      (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
      (sandwichedRenyiInner_posSemidef ρ σ α)
      hpq
      hbound
  exact sandwichedRenyi_dataProcessing_le_of_inner_schattenPNorm_le_of_one_lt
    ρ σ Φ hρ hσ hρΦ hσΦ α hα_gt_one hnorm

/-- Full-rank α > 1 channel DPI follows from the rotated-Kraus adjoint
`q`-unit-ball contraction.

This theorem is the final Lean handoff to the missing noncommutative
interpolation lemma: it proves the complete logarithmic α > 1 DPI inequality
once the rotated adjoint is known to contract positive `q`-unit balls. It does
not assume DPI itself. -/
theorem sandwichedRenyi_dataProcessing_le_of_rotatedKrausAdjoint_qBall_of_one_lt
    {κ : Type*} [Fintype κ] (K : κ → Matrix b a ℂ)
    (ρ σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q)
    (hrotated :
      ∀ B : CMatrix b, ∀ hB : B.PosSemidef,
        psdTracePower B hB q ≤ 1 →
          psdTracePower
            (MatrixMap.krausAdjoint
              (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B)
            (MatrixMap.krausAdjoint_mapsPositive
              (sandwichedRenyiRotatedKraus σ (Φ.applyState σ) K α) B hB)
            q ≤ 1) :
    sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ
        α (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one) ≤
      sandwichedRenyi ρ σ hρ hσ α (lt_trans zero_lt_one hα_gt_one)
        (ne_of_gt hα_gt_one) := by
  exact
    sandwichedRenyi_dataProcessing_le_of_traceHolderUnitBall_le_of_one_lt
      ρ σ Φ hρ hσ hρΦ hσΦ α q hα_gt_one hpq
      (fun B hB hBq =>
        sandwichedRenyi_traceHolderUnitBall_le_of_rotatedKrausAdjoint_qBall
          K ρ σ Φ hK hσ α q hpq hrotated B hB hBq)

/-- α > 1 Beigi-route trace-power contraction for arbitrary input states and
positive-definite references.

This is the numeric core behind the logarithmic high-`α` DPI.  Unlike the
real-valued `sandwichedRenyi` wrapper below, it does not require the input
state or the output state to be positive definite; the new positivity side
conditions come only from the positive-definite references. -/
theorem sandwichedRenyiInner_tracePower_le_of_one_lt_channel
    (ρ σ : State a) (Φ : Channel a b)
    (hσ : σ.matrix.PosDef)
    (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    psdTracePower (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
        (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α) α ≤
      psdTracePower (sandwichedRenyiInner ρ σ α)
        (sandwichedRenyiInner_posSemidef ρ σ α) α := by
  classical
  obtain ⟨K, hK⟩ :=
    MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  let q : ℝ := Real.conjExponent α
  have hpq : α.HolderConjugate q :=
    Real.HolderConjugate.conjExponent hα_gt_one
  have hnorm :
      psdSchattenPNorm
          (sandwichedRenyiInner (Φ.applyState ρ) (Φ.applyState σ) α)
          (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
          ⟨α, lt_trans zero_lt_one hα_gt_one⟩ ≤
        psdSchattenPNorm (sandwichedRenyiInner ρ σ α)
          (sandwichedRenyiInner_posSemidef ρ σ α)
          ⟨α, lt_trans zero_lt_one hα_gt_one⟩ :=
    psdSchattenPNorm_le_of_traceHolderUnitBall_le
      (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
      (sandwichedRenyiInner_posSemidef ρ σ α)
      hpq
      (fun B hB hBq =>
        sandwichedRenyi_traceHolderUnitBall_le_of_rotatedKrausAdjoint_qBall
          K ρ σ Φ hK hσ α q hpq
          (fun B hB hBq =>
            sandwichedRenyiRotatedKrausAdjoint_qBall_of_beigi
              K σ Φ hK hσ hσΦ α q hα_gt_one hpq hB hBq)
          B hB hBq)
  exact
    psdTracePower_le_of_psdSchattenPNorm_le
      (sandwichedRenyiInner_posSemidef (Φ.applyState ρ) (Φ.applyState σ) α)
      (sandwichedRenyiInner_posSemidef ρ σ α)
      (lt_trans zero_lt_one hα_gt_one)
      (sandwichedRenyiInner_psdTracePower_pos_of_reference_posDef
        (Φ.applyState ρ) (Φ.applyState σ) hσΦ α)
      (sandwichedRenyiInner_psdTracePower_pos_of_reference_posDef ρ σ hσ α)
      hnorm

/-- α > 1 full-rank sandwiched Renyi DPI for a general channel with an explicit
finite Kraus realization.

This theorem is the current Beigi-route completion for the full-rank
`State + PosDef` local domain: it uses the proved rotated-adjoint `q`-ball
contraction and does not assume DPI or a contraction hypothesis. It is still
not the full source statement because the source statement allows a positive
semidefinite, not necessarily full-rank, reference operator and also includes
the `1 / 2 ≤ α < 1` range. -/
theorem sandwichedRenyi_dataProcessing_channel_statement_of_one_lt
    {κ : Type*} [Fintype κ] [DecidableEq κ] (K : κ → Matrix b a ℂ)
    (ρ σ : State a) (Φ : Channel a b) (hK : Φ.map = MatrixMap.ofKraus K)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α q : ℝ) (hα_gt_one : 1 < α) (hpq : α.HolderConjugate q) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ
      hρ hσ hρΦ hσΦ α (by linarith) (ne_of_gt hα_gt_one) := by
  unfold sandwichedRenyi_dataProcessing_channel_statement
  exact
    sandwichedRenyi_dataProcessing_le_of_rotatedKrausAdjoint_qBall_of_one_lt
      K ρ σ Φ hK hρ hσ hρΦ hσΦ α q hα_gt_one hpq
      (fun B hB hBq =>
        sandwichedRenyiRotatedKrausAdjoint_qBall_of_beigi
          K σ Φ hK hσ hσΦ α q hα_gt_one hpq hB hBq)

/-- α > 1 full-rank sandwiched Renyi DPI for an arbitrary finite-dimensional
channel.

This removes the explicit Kraus-realization parameter from
`sandwichedRenyi_dataProcessing_channel_statement_of_one_lt`: the channel's
Choi-positive complete-positivity proof supplies a finite Kraus family, and the
Beigi weighted-map contraction theorem proves the local full-rank statement. -/
theorem sandwichedRenyi_dataProcessing_channel_statement_of_one_lt_channel
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ
      hρ hσ hρΦ hσΦ α (by linarith) (ne_of_gt hα_gt_one) := by
  classical
  obtain ⟨K, hK⟩ :=
    MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  exact
    sandwichedRenyi_dataProcessing_channel_statement_of_one_lt
      K ρ σ Φ hK hρ hσ hρΦ hσΦ
      α (Real.conjExponent α) hα_gt_one
      (Real.HolderConjugate.conjExponent hα_gt_one)

/-- Full-rank sandwiched Renyi divergences are nonnegative in the proved
`α > 1` range.

The proof applies the already-established general-channel DPI to the terminal
one-outcome measurement channel. Both output states are the unique unit-system
state, whose self-divergence is zero. -/
theorem sandwichedRenyi_nonneg_of_one_lt
    (ρ σ : State a) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    0 ≤ sandwichedRenyi ρ σ hρ hσ α
      (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one) := by
  let Φ : Channel a PUnit.{1} := terminalMeasureChannel a
  have hρΦ_eq : Φ.applyState ρ = State.unit := by
    simpa [Φ] using terminalMeasureChannel_applyState ρ
  have hσΦ_eq : Φ.applyState σ = State.unit := by
    simpa [Φ] using terminalMeasureChannel_applyState σ
  have hunit_pos : (State.unit.matrix : CMatrix PUnit.{1}).PosDef := by
    change (1 : CMatrix PUnit.{1}).PosDef
    exact Matrix.PosDef.one
  have hρΦ_pos : (Φ.applyState ρ).matrix.PosDef := by
    rw [hρΦ_eq]
    exact hunit_pos
  have hσΦ_pos : (Φ.applyState σ).matrix.PosDef := by
    rw [hσΦ_eq]
    exact hunit_pos
  have hDPI_stmt :
      sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ
        hρ hσ hρΦ_pos hσΦ_pos α
        (by linarith) (ne_of_gt hα_gt_one) :=
    sandwichedRenyi_dataProcessing_channel_statement_of_one_lt_channel
      ρ σ Φ hρ hσ hρΦ_pos hσΦ_pos α hα_gt_one
  unfold sandwichedRenyi_dataProcessing_channel_statement at hDPI_stmt
  have hleft :
      sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ)
          hρΦ_pos hσΦ_pos α
          (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one) = 0 := by
    simpa [hρΦ_eq, hσΦ_eq] using
      sandwichedRenyi_self_eq_zero State.unit hunit_pos α
        (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one)
  rw [hleft] at hDPI_stmt
  exact hDPI_stmt

/-- Full-rank sandwiched Renyi DPI for the proved parts of the public range:
the fidelity endpoint `α = 1/2` and the Beigi interpolation range `α > 1`.

This gives a single non-circular entry point for the subrange already proved in
this sprint. It deliberately does not cover the strict subunit interval
`1 / 2 < α < 1`, whose remaining blocker is the conditional-duality/minimax
route. -/
theorem sandwichedRenyi_dataProcessing_channel_statement_of_eq_half_or_one_lt
    (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef)
    (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα_range : α = 1 / 2 ∨ 1 < α) :
    sandwichedRenyi_dataProcessing_channel_statement ρ σ Φ hρ hσ hρΦ hσΦ
      α
      (by
        rcases hα_range with rfl | hgt
        · norm_num
        · linarith)
      (by
        rcases hα_range with rfl | hgt
        · norm_num
        · exact ne_of_gt hgt) := by
  rcases hα_range with rfl | hgt
  · simpa using
      sandwichedRenyi_dataProcessing_channel_statement_half
        ρ σ Φ hρ hσ hρΦ hσΦ
  · exact
      sandwichedRenyi_dataProcessing_channel_statement_of_one_lt_channel
        ρ σ Φ hρ hσ hρΦ hσΦ α hgt

end State

end

end QIT
