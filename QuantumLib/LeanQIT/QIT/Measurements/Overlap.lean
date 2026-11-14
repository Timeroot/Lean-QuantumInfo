/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Measurements.Projective
public import QIT.Core.Pure
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Measurement overlap for two projective measurements

The arbitrary-projective-measurement overlap constant
`c = max_{i,j} ‖P_i Q_j‖∞^2` for two finite projective measurements on the same
system.  The source Maassen-Uffink formula is for two orthonormal bases, hence
for rank-one projective measurements; the trace expression `max_{i,j} Tr(P_i Q_j)`
is kept separately as `rankOneTraceOverlap`.

Source: Tomamichel2015FiniteResources, `apps.tex` (Eq. `eq:defc`).
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal
open scoped Matrix.Norms.L2Operator

open Matrix

namespace QIT

universe u v w

noncomputable section

variable {x : Type u} {y : Type v} {a : Type w}
variable [Fintype x] [Fintype y] [Fintype a] [DecidableEq a]
variable (P : ProjectiveMeasurement x a) (Q : ProjectiveMeasurement y a)

namespace ProjectiveMeasurement

noncomputable local instance instCMatrixNonUnitalCStarAlgebraForMeasurementOverlap
    (n : Type*) [Fintype n] [DecidableEq n] :
    NonUnitalCStarAlgebra (Matrix n n ℂ) := ⟨⟩

noncomputable local instance instCMatrixCStarAlgebraForMeasurementOverlap
    (n : Type*) [Fintype n] [DecidableEq n] :
    CStarAlgebra (Matrix n n ℂ) := ⟨⟩

/-- `Tr(P_i Q_j) >= 0` for projective effects.

Proved via the idempotent congruence `Tr(P_i Q_j) = Tr(P_i Q_j P_i)` with
`P_i Q_j P_i` positive semidefinite (congruence of the PSD `Q_j` by the
Hermitian `P_i`); no matrix square root is needed because `P_i` is idempotent. -/
theorem effect_mul_effect_trace_re_nonneg (i : x) (j : y) :
    0 ≤ ((P.effects i * Q.effects j).trace).re := by
  have hPSD : (P.effects i * Q.effects j * P.effects i).PosSemidef := by
    have h := (Q.effect_posSemidef j).mul_mul_conjTranspose_same (P.effects i)
    rwa [P.isHermitian i] at h
  have hEq : (P.effects i * Q.effects j * P.effects i).trace =
      (P.effects i * Q.effects j).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, P.idempotent i]
  rw [← hEq]
  exact (Matrix.PosSemidef.trace_nonneg hPSD).1

/-- Rank-one bridge data for a projective measurement.

This is intentionally a source-facing local package rather than a full
rank-one-measurement library: each effect is represented by a normalized vector,
and the elementary norm/trace bridge against normalized vector effects is
available for the overlap comparison below. -/
structure IsRankOne where
  vector : x → PureVector a
  effect_eq : ∀ outcome, P.effects outcome = (vector outcome).state.matrix
  norm_sq_mul_state_trace :
    ∀ outcome (φ : PureVector a),
      ‖P.effects outcome * φ.state.matrix‖ ^ 2 =
        ((P.effects outcome * φ.state.matrix).trace).re

/-- The arbitrary-projective-measurement overlap
`c = max_{i,j} ‖P_i Q_j‖∞^2` as a nonnegative real. -/
def measurementOverlap : ℝ≥0 :=
  (Finset.univ : Finset x).sup fun i =>
    (Finset.univ : Finset y).sup fun j =>
      ⟨‖P.effects i * Q.effects j‖ ^ 2,
        sq_nonneg ‖P.effects i * Q.effects j‖⟩

/-- The measurement overlap is nonnegative. -/
theorem measurementOverlap_nonneg : 0 ≤ P.measurementOverlap Q :=
  bot_le

/-- The overlap unfolds to the nested finite supremum of `‖P_i Q_j‖∞^2`. -/
@[simp]
theorem measurementOverlap_eq :
    P.measurementOverlap Q =
      (Finset.univ : Finset x).sup fun i =>
        (Finset.univ : Finset y).sup fun j =>
          ⟨‖P.effects i * Q.effects j‖ ^ 2,
            sq_nonneg ‖P.effects i * Q.effects j‖⟩ :=
  rfl

/-- The trace formula `max_{i,j} Tr(P_i Q_j)` used for rank-one/projective
measurements coming from orthonormal bases.

This is not the arbitrary-rank projective-measurement overlap.  It is retained
as the source-facing Maassen-Uffink/ONB expression and is related to
`measurementOverlap` by `measurementOverlap_eq_rankOneTraceOverlap` under
rank-one bridge hypotheses. -/
def rankOneTraceOverlap : ℝ≥0 :=
  (Finset.univ : Finset x).sup fun i =>
    (Finset.univ : Finset y).sup fun j =>
      ⟨((P.effects i * Q.effects j).trace).re,
        effect_mul_effect_trace_re_nonneg P Q i j⟩

/-- The rank-one trace overlap unfolds to the nested finite supremum of
`Tr(P_i Q_j)`. -/
@[simp]
theorem rankOneTraceOverlap_eq :
    P.rankOneTraceOverlap Q =
      (Finset.univ : Finset x).sup fun i =>
        (Finset.univ : Finset y).sup fun j =>
          ⟨((P.effects i * Q.effects j).trace).re,
            effect_mul_effect_trace_re_nonneg P Q i j⟩ :=
  rfl

/-- If every outcome pair has the rank-one norm/trace equality, the general
operator-norm overlap agrees with the rank-one trace formula. -/
theorem measurementOverlap_eq_rankOneTraceOverlap_of_pair
    (h : ∀ i j,
      ‖P.effects i * Q.effects j‖ ^ 2 =
        ((P.effects i * Q.effects j).trace).re) :
    P.measurementOverlap Q = P.rankOneTraceOverlap Q := by
  simp [measurementOverlap, rankOneTraceOverlap, h]

/-- For rank-one/projective measurements coming from normalized vector effects,
the arbitrary-projective-measurement overlap agrees with the source trace
formula. -/
theorem measurementOverlap_eq_rankOneTraceOverlap
    (hP : P.IsRankOne) (hQ : Q.IsRankOne) :
    P.measurementOverlap Q = P.rankOneTraceOverlap Q := by
  apply measurementOverlap_eq_rankOneTraceOverlap_of_pair
  intro i j
  rw [hQ.effect_eq j]
  exact hP.norm_sq_mul_state_trace i (hQ.vector j)

end ProjectiveMeasurement

end

end QIT
