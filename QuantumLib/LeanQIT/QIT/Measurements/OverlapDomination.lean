/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Measurements.Overlap
public import QIT.States.Purification.PureGeometry
public import QIT.Util.Matrix

/-!
# Overlap domination for two projective measurements

The Loewner-order domination behind the overlap constant
`c = max_{x,y} Tr(P_x Q_y)` in Tomamichel's entropic-uncertainty route.

For two projective measurements `P` (outcomes `x`) and `Q` (outcomes `y`) on the
same system and any positive-semidefinite family `M_y`, the weight aggregate
`Σ_{x,y} Tr(P_x Q_y) · (|x⟩⟨x| ⊗ M_y)` is dominated in Loewner order by the
scaled tensor `c · (1 ⊗ Σ_y M_y)`.  This matrix inequality is the operative step
of the measurement-overlap bound; combined with a sandwiched-Renyi
order-monotonicity hypothesis it yields the `-log₂ c` offset of the dual
uncertainty relation.

Source: Tomamichel2015FiniteResources, `apps.tex` lines 208-214 (the
overlap-domination step and the substitution into `eq:ur-proof1`).
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Kronecker
open scoped Matrix.Norms.L2Operator

open Matrix

namespace QIT

universe u v w z

noncomputable section

variable {x : Type u} {y : Type v} {a : Type w} {b : Type z}
variable [Fintype x] [DecidableEq x]
variable [Fintype y] [DecidableEq y]
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable (P : ProjectiveMeasurement x a) (Q : ProjectiveMeasurement y a)

noncomputable local instance instCMatrixNonUnitalCStarAlgebraForOverlapDomination
    (n : Type*) [Fintype n] [DecidableEq n] :
    NonUnitalCStarAlgebra (Matrix n n ℂ) := ⟨⟩

noncomputable local instance instCMatrixCStarAlgebraForOverlapDomination
    (n : Type*) [Fintype n] [DecidableEq n] :
    CStarAlgebra (Matrix n n ℂ) := ⟨⟩

namespace ProjectiveMeasurement

omit [DecidableEq x] [DecidableEq y] in
/-- A single trace weight `Tr(P_i Q_j)` is bounded above by the overlap
constant, since the constant is the finite supremum over outcome pairs. -/
theorem trace_re_le_rankOneTraceOverlap (i : x) (j : y) :
    ⟨((P.effects i * Q.effects j).trace).re, P.effect_mul_effect_trace_re_nonneg Q i j⟩ ≤
      P.rankOneTraceOverlap Q := by
  simp only [rankOneTraceOverlap_eq]
  have hinner := @Finset.le_sup _ _ _ _ _ (fun j' : y =>
        (⟨((P.effects i * Q.effects j').trace).re,
            P.effect_mul_effect_trace_re_nonneg Q i j'⟩ : ℝ≥0))
      _ (Finset.mem_univ j)
  exact hinner.trans
    (@Finset.le_sup _ _ _ _ _ (fun i' : x =>
        (Finset.univ : Finset y).sup fun j' =>
          (⟨((P.effects i' * Q.effects j').trace).re,
              P.effect_mul_effect_trace_re_nonneg Q i' j'⟩ : ℝ≥0))
      _ (Finset.mem_univ i))

omit [DecidableEq y] [DecidableEq b] in
/-- Overlap domination in Loewner order.

For projective measurements `P`, `Q` and a positive-semidefinite family `M`, the
weight aggregate `Σ_{i,j} Tr(P_i Q_j) · (|i⟩⟨i| ⊗ M_j)` is dominated by
`c · (1 ⊗ Σ_j M_j)` where `c = max_{i,j} Tr(P_i Q_j)` is the trace overlap.
The domination is the matrix inequality underpinning the measurement-overlap
bound of `apps.tex:208-213`. -/
theorem overlap_domination_le (M : y → CMatrix b) (hM : ∀ j, (M j).PosSemidef) :
    (∑ i, ∑ j, ((P.effects i * Q.effects j).trace).re •
        Matrix.kronecker (Matrix.single i i (1 : ℂ)) (M j)) ≤
      (P.rankOneTraceOverlap Q : ℝ) • Matrix.kronecker (1 : CMatrix x) (∑ j, M j) := by
  set c : ℝ := (P.rankOneTraceOverlap Q : ℝ)
  -- The outcome-basis identity matrix is the resolution `Σ_i |i><i|`.
  have hone : (1 : CMatrix x) = ∑ i, Matrix.single i i (1 : ℂ) :=
    (Matrix.sum_single_one).symm
  -- Kronecker is bilinear, hence distributes over both outcome-register sums.
  have hkron (A : x → CMatrix x) (B : y → CMatrix b) :
      Matrix.kronecker (∑ i, A i) (∑ j, B j) = ∑ i, ∑ j, Matrix.kronecker (A i) (B j) := by
    ext ⟨ia, ba⟩ ⟨ib, bb⟩
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sum_apply]
    exact Fintype.sum_mul_sum _ _
  have hpsd : (∑ i, ∑ j, (c - ((P.effects i * Q.effects j).trace).re) •
      Matrix.kronecker (Matrix.single i i (1 : ℂ)) (M j)).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro i _
    apply Matrix.posSemidef_sum
    intro j _
    refine Matrix.PosSemidef.smul ?_ ?_
    · exact (posSemidef_single i).kronecker (hM j)
    · exact sub_nonneg.mpr (mod_cast P.trace_re_le_rankOneTraceOverlap Q i j)
  rw [Matrix.le_iff]
  have heq :
      ((P.rankOneTraceOverlap Q : ℝ) • Matrix.kronecker (1 : CMatrix x) (∑ j, M j)) -
          (∑ i, ∑ j, ((P.effects i * Q.effects j).trace).re •
            Matrix.kronecker (Matrix.single i i (1 : ℂ)) (M j)) =
        ∑ i, ∑ j, (c - ((P.effects i * Q.effects j).trace).re) •
          Matrix.kronecker (Matrix.single i i (1 : ℂ)) (M j) := by
    rw [show c = (P.rankOneTraceOverlap Q : ℝ) from rfl, hone, hkron]
    simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, ← sub_smul]
  rw [heq]
  exact hpsd

omit [DecidableEq b] [DecidableEq y] in
/-- Rank-one source form of the overlap domination.

Under rank-one bridge hypotheses for `P` and `Q`, the trace weight
`Tr(P_i Q_j)` equals the squared pure-state overlap
`|⟨φ_i|ϑ_j⟩|²` (`PureVector.rankOneMatrix_mul_trace_re_eq_overlapSq`), giving the
source-facing domination through `c = max_{i,j} |⟨φ_i|ϑ_j⟩|²`. -/
theorem overlap_domination_le_rankOne (hP : P.IsRankOne) (hQ : Q.IsRankOne)
    (M : y → CMatrix b) (hM : ∀ j, (M j).PosSemidef) :
    (∑ i, ∑ j, (hP.vector i).overlapSq (hQ.vector j) •
        Matrix.kronecker (Matrix.single i i (1 : ℂ)) (M j)) ≤
      (P.rankOneTraceOverlap Q : ℝ) • Matrix.kronecker (1 : CMatrix x) (∑ j, M j) := by
  classical
  have hkey : ∀ i j,
      ((P.effects i * Q.effects j).trace).re = (hP.vector i).overlapSq (hQ.vector j) := by
    intro i j
    rw [hP.effect_eq i, hQ.effect_eq j]
    exact PureVector.rankOneMatrix_mul_trace_re_eq_overlapSq (hP.vector i) (hQ.vector j)
  simp only [← hkey]
  exact P.overlap_domination_le Q M hM

end ProjectiveMeasurement

end

end QIT
