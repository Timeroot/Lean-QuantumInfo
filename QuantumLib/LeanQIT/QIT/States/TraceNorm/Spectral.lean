/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.TraceNorm.Distance
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Average
public import QIT.Util.SDP.HermitianPSDTraceDuality

/-!
# Spectral trace-norm bridge

This module proves the finite-dimensional bridge from the local trace-norm
definition `Tr sqrt(Mᴴ * M)` to the singular-value sum used by the trace-norm
variational route. The source claim is registered as
`m5-trace-norm-definition-and-singular-values`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open Matrix

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Finite singular-value sum for a square complex matrix, expressed through
the local matrix spectral convention for `Mᴴ * M`. This is the same ordering as
`M.toEuclideanLin.singularValues`; see
`traceNormSingularValueSum_eq_linearMap_singularValues`. -/
def traceNormSingularValueSum (M : CMatrix a) : ℝ :=
  ∑ i, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues i)

/-- The operator `Mᴴ * M` is the matrix representative of
`M.toEuclideanLin.adjoint.comp M.toEuclideanLin`. -/
theorem toEuclideanLin_conjTranspose_mul_self_eq_adjoint_comp (M : CMatrix a) :
    M.toEuclideanLin.adjoint.comp M.toEuclideanLin =
      (Mᴴ * M).toEuclideanLin := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint M]
  rw [Matrix.toLpLin_mul]

/-- The matrix eigenvalues used to define the local singular-value sum agree
with the eigenvalues underlying mathlib's `LinearMap.singularValues`. -/
theorem eigenvalues_conjTranspose_mul_self_eq_adjoint_comp (M : CMatrix a) (i : a) :
    (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues i =
      (M.toEuclideanLin.isSymmetric_adjoint_comp_self).eigenvalues
        (n := Fintype.card a) (by simp)
        ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i) := by
  let hA : ((Mᴴ * M).toEuclideanLin).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_conjTranspose_mul_self M)
  have hvals :
      hA.eigenvalues (n := Fintype.card a) (by simp) =
        (M.toEuclideanLin.isSymmetric_adjoint_comp_self).eigenvalues
          (n := Fintype.card a) (by simp) := by
    rw [(LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff hA (by simp)
      M.toEuclideanLin.isSymmetric_adjoint_comp_self (by simp)).2]
    rw [toEuclideanLin_conjTranspose_mul_self_eq_adjoint_comp M]
  simpa [Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.eigenvalues₀, hA] using
    congrFun hvals ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)

/-- The local singular-value sum is the finite sum of mathlib singular values
of the Euclidean linear map represented by `M`. -/
theorem traceNormSingularValueSum_eq_linearMap_singularValues (M : CMatrix a) :
    traceNormSingularValueSum M =
      (Finset.range (Fintype.card a)).sum fun i => M.toEuclideanLin.singularValues i := by
  rw [traceNormSingularValueSum, ← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  intro i
  let hA : ((Mᴴ * M).toEuclideanLin).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_conjTranspose_mul_self M)
  have hvals :
      hA.eigenvalues (n := Fintype.card a) (by simp) =
        (M.toEuclideanLin.isSymmetric_adjoint_comp_self).eigenvalues
          (n := Fintype.card a) (by simp) := by
    rw [(LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff hA (by simp)
      M.toEuclideanLin.isSymmetric_adjoint_comp_self (by simp)).2]
    rw [toEuclideanLin_conjTranspose_mul_self_eq_adjoint_comp M]
  rw [LinearMap.singularValues_fin (T := M.toEuclideanLin) (hn := by simp)
    ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)]
  simpa [Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.eigenvalues₀, hA] using
    congrArg Real.sqrt (congrFun hvals ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i))

/-- The CFC square-root trace unfolds to the finite sum of square roots of the
eigenvalues of `Mᴴ * M`. -/
theorem psdSqrt_conjTranspose_mul_self_trace_eq_singularValueSum (M : CMatrix a) :
    (psdSqrt (Mᴴ * M)).trace =
      ∑ i, ((Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues i) : ℝ) : ℂ) := by
  have hpsd : (Mᴴ * M).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  rw [psdSqrt]
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ (Mᴴ * M), hpsd.1.cfc_eq]
  simp only [Matrix.IsHermitian.cfc]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
    Matrix.trace_diagonal]
  simp only [Function.comp_apply, Real.coe_sqrt, Real.coe_toNNReal']
  simp [hpsd.eigenvalues_nonneg]

/-- The local trace norm equals the finite singular-value sum. -/
theorem traceNorm_eq_singularValueSum (M : CMatrix a) :
    traceNorm M = traceNormSingularValueSum M := by
  rw [traceNorm, traceNormSingularValueSum]
  have htrace := psdSqrt_conjTranspose_mul_self_trace_eq_singularValueSum M
  rw [htrace]
  simp

/-- The local trace norm equals the sum over the nonzero singular-value
support of the represented Euclidean linear map. -/
theorem traceNorm_eq_singularValues_support_sum (M : CMatrix a) :
    traceNorm M = M.toEuclideanLin.singularValues.sum (fun _ x => x) := by
  rw [traceNorm_eq_singularValueSum, traceNormSingularValueSum_eq_linearMap_singularValues]
  let sv := M.toEuclideanLin.singularValues
  change (∑ i ∈ Finset.range (Fintype.card a), sv i) = sv.sum (fun _ x => x)
  rw [Finsupp.sum]
  have hsupport : sv.support =
      Finset.range (Module.finrank ℂ (LinearMap.range M.toEuclideanLin)) := by
    simp [sv]
  rw [hsupport]
  let r := Module.finrank ℂ (LinearMap.range M.toEuclideanLin)
  let n := Fintype.card a
  have hrn : r ≤ n := by
    simpa [r, n, finrank_euclideanSpace] using
      (Submodule.finrank_le (LinearMap.range M.toEuclideanLin))
  exact (Finset.sum_subset
    (by intro i hi; exact Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hrn))
    (by
      intro i _ hi_small
      have hri : r ≤ i := le_of_not_gt (by simpa [r] using hi_small)
      change M.toEuclideanLin.singularValues i = 0
      exact (M.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range).2 hri)).symm

/-- The squared singular values sum to the Hilbert-Schmidt trace
`Re Tr(Mᴴ * M)`. -/
theorem singularValues_sum_sq_eq_trace_conjTranspose_mul_self (M : CMatrix a) :
    (∑ i ∈ Finset.range (Fintype.card a), M.toEuclideanLin.singularValues i ^ 2) =
      ((star M * M).trace).re := by
  let H : CMatrix a := star M * M
  have htrace : H.trace.re = ∑ i, (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues i := by
    have h := (Matrix.isHermitian_conjTranspose_mul_self M).trace_eq_sum_eigenvalues
    exact (congrArg Complex.re h).trans (by simp)
  rw [htrace]
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  apply Fintype.sum_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  intro i
  rw [LinearMap.sq_singularValues_fin]
  exact eigenvalues_conjTranspose_mul_self_eq_adjoint_comp M i

/-- The support sum of squared singular values is the Hilbert-Schmidt trace
`Re Tr(Mᴴ * M)`. -/
theorem singularValues_support_sum_sq_eq_trace_conjTranspose_mul_self (M : CMatrix a) :
    M.toEuclideanLin.singularValues.sum (fun _ x => x ^ 2) =
      ((star M * M).trace).re := by
  rw [← singularValues_sum_sq_eq_trace_conjTranspose_mul_self M]
  let sv := M.toEuclideanLin.singularValues
  change sv.sum (fun _ x => x ^ 2) = ∑ i ∈ Finset.range (Fintype.card a), sv i ^ 2
  rw [Finsupp.sum]
  have hsupport : sv.support =
      Finset.range (Module.finrank ℂ (LinearMap.range M.toEuclideanLin)) := by
    simp [sv]
  rw [hsupport]
  let r := Module.finrank ℂ (LinearMap.range M.toEuclideanLin)
  let n := Fintype.card a
  have hrn : r ≤ n := by
    simpa [r, n, finrank_euclideanSpace] using
      (Submodule.finrank_le (LinearMap.range M.toEuclideanLin))
  exact Finset.sum_subset
    (by intro i hi; exact Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hrn))
    (by
      intro i _ hi_small
      have hri : r ≤ i := le_of_not_gt (by simpa [r] using hi_small)
      have hz : sv i = 0 := by
        change M.toEuclideanLin.singularValues i = 0
        exact (M.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range).2 hri
      rw [hz]
      norm_num)

/-- Cauchy-Schwarz bridge from the trace norm to the Hilbert-Schmidt trace,
with rank measured by the Euclidean-linear range dimension. -/
theorem traceNorm_sq_le_finrank_range_mul_hilbertSchmidt (M : CMatrix a) :
    traceNorm M ^ 2 ≤
      (Module.finrank ℂ (LinearMap.range M.toEuclideanLin) : ℝ) * ((star M * M).trace).re := by
  let sv := M.toEuclideanLin.singularValues
  have htraceNorm : traceNorm M = sv.sum (fun _ x => x) := by
    simpa [sv] using traceNorm_eq_singularValues_support_sum M
  have hsqsum : sv.sum (fun _ x => x ^ 2) = ((star M * M).trace).re := by
    simpa [sv] using singularValues_support_sum_sq_eq_trace_conjTranspose_mul_self M
  rw [htraceNorm, ← hsqsum]
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := sv.support)
    (R := ℝ)
    (r := fun i : ℕ => sv i)
    (f := fun _ : ℕ => (1 : ℝ))
    (g := fun i : ℕ => sv i ^ 2)
    (fun _ _ => by norm_num)
    (fun i _ => sq_nonneg (sv i))
    (fun i _ => by simp)
  have hcard : (sv.support.card : ℝ) =
      Module.finrank ℂ (LinearMap.range M.toEuclideanLin) := by
    have h := M.toEuclideanLin.card_support_singularValues
    exact_mod_cast h
  simpa [Finsupp.sum, hcard] using hcs

/-- Hilbert--Schmidt square used in the Step 4 variance computation. -/
def hilbertSchmidtSq [Fintype a] [DecidableEq a] (M : CMatrix a) : ℝ :=
  ((star M * M).trace).re

omit [Fintype a] [DecidableEq a] in
theorem hilbertSchmidtSq_nonneg [Fintype a] [DecidableEq a] (M : CMatrix a) :
    0 ≤ hilbertSchmidtSq M := by
  exact (Matrix.PosSemidef.trace_nonneg
    (Matrix.posSemidef_conjTranspose_mul_self M)).1

omit [Fintype a] [DecidableEq a] in
theorem hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian [Fintype a] [DecidableEq a]
    {M : CMatrix a} (hM : M.IsHermitian) :
    hilbertSchmidtSq M = (M * M).trace.re := by
  unfold hilbertSchmidtSq
  rw [show star M = M by simpa [Matrix.star_eq_conjTranspose] using hM.eq]

omit [Fintype a] [DecidableEq a] in
theorem traceNorm_sq_le_card_mul_hilbertSchmidtSq [Fintype a] [DecidableEq a]
    (M : CMatrix a) :
    traceNorm M ^ 2 ≤ (Fintype.card a : ℝ) * hilbertSchmidtSq M := by
  have hmain := traceNorm_sq_le_finrank_range_mul_hilbertSchmidt M
  have hrank : (Module.finrank ℂ (LinearMap.range M.toEuclideanLin) : ℝ) ≤
      (Fintype.card a : ℝ) := by
    have hnat : Module.finrank ℂ (LinearMap.range M.toEuclideanLin) ≤ Fintype.card a := by
      simpa [finrank_euclideanSpace] using
        (Submodule.finrank_le (LinearMap.range M.toEuclideanLin))
    exact_mod_cast hnat
  exact hmain.trans
    (mul_le_mul_of_nonneg_right hrank (hilbertSchmidtSq_nonneg M))

omit [Fintype a] [DecidableEq a] in
/-- A trace-one positive semidefinite matrix has purity at least `1 / d`.
This is the Hilbert--Schmidt Cauchy--Schwarz estimate in trace-norm form. -/
theorem State.one_le_card_mul_hilbertSchmidtSq_matrix [Fintype a] [DecidableEq a]
    (ρ : State a) :
    (1 : ℝ) ≤ (Fintype.card a : ℝ) * hilbertSchmidtSq ρ.matrix := by
  have htn : traceNorm ρ.matrix = 1 := by
    rw [traceNorm_posSemidef_eq_trace_re ρ.matrix ρ.pos]
    exact ρ.trace_re_eq_one
  have h := traceNorm_sq_le_card_mul_hilbertSchmidtSq ρ.matrix
  nlinarith

omit [Fintype a] [DecidableEq a] in
/-- If a state is bounded above by `c • I`, then its Hilbert--Schmidt purity is
at most `c`. -/
theorem State.hilbertSchmidtSq_matrix_le_of_le_smul_one [Fintype a] [DecidableEq a]
    (ρ : State a) {c : ℝ} (hc : 0 ≤ c)
    (hρ : ρ.matrix ≤ ((c : ℂ) • (1 : CMatrix a))) :
    hilbertSchmidtSq ρ.matrix ≤ c := by
  have _hcC : (0 : ℂ) ≤ (c : ℂ) := by
    exact_mod_cast hc
  have hpair :=
    cMatrix_trace_mul_le_of_le_posSemidef_left
      (A := ρ.matrix) (B := ((c : ℂ) • (1 : CMatrix a))) (W := ρ.matrix)
      ρ.pos hρ
  have hright :
      ((ρ.matrix * ((c : ℂ) • (1 : CMatrix a))).trace).re = c := by
    calc
      ((ρ.matrix * ((c : ℂ) • (1 : CMatrix a))).trace).re =
          (((c : ℂ) • ρ.matrix).trace).re := by
            rw [Matrix.mul_smul, Matrix.mul_one]
      _ = ((c : ℂ) * ρ.matrix.trace).re := by
            simp [Matrix.trace_smul]
      _ = c := by
            rw [ρ.trace_eq_one]
            simp
  calc
    hilbertSchmidtSq ρ.matrix = (ρ.matrix * ρ.matrix).trace.re :=
      hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian ρ.pos.isHermitian
    _ ≤ ((ρ.matrix * ((c : ℂ) • (1 : CMatrix a))).trace).re := hpair
    _ = c := hright

omit [Fintype a] [DecidableEq a] in
theorem traceNorm_sq_le_rankBound_mul_hilbertSchmidtSq [Fintype a] [DecidableEq a]
    (M : CMatrix a) {r : ℝ}
    (hrank : (Module.finrank ℂ (LinearMap.range M.toEuclideanLin) : ℝ) ≤ r) :
    traceNorm M ^ 2 ≤ r * hilbertSchmidtSq M := by
  have hmain := traceNorm_sq_le_finrank_range_mul_hilbertSchmidt M
  simpa [hilbertSchmidtSq] using hmain.trans
    (mul_le_mul_of_nonneg_right hrank (hilbertSchmidtSq_nonneg M))

theorem traceNorm_sq_le_card_mul_hilbertSchmidt {a : Type u}
    [Fintype a] [DecidableEq a] (M : CMatrix a) :
    traceNorm M ^ 2 ≤
      (Fintype.card a : ℝ) * ((star M * M).trace).re :=
  traceNorm_sq_le_card_mul_hilbertSchmidtSq M

namespace State

/-- Canonical non-unital C⋆-algebra structure on finite complex matrices,
needed locally for the operator-norm bound below; carried by the L2-operator
norm scope opened above. -/
noncomputable local instance : NonUnitalCStarAlgebra (CMatrix a) := ⟨⟩

/-- A positive semidefinite finite matrix is bounded above by its trace times the
identity. -/
theorem posSemidef_le_trace_re_smul_one {A : CMatrix a} (hA : A.PosSemidef) :
    A ≤ (((A.trace.re : ℝ) : ℂ) • (1 : CMatrix a)) := by
  classical
  rw [Matrix.le_iff]
  let U : Matrix.unitaryGroup a ℂ := hA.1.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => ((hA.1.eigenvalues i : ℝ) : ℂ)
  have hdiag : A = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hA.1.spectral_theorem
  have heig_sum : ∑ i, hA.1.eigenvalues i = A.trace.re := by
    have hc : A.trace = ∑ i, ((hA.1.eigenvalues i : ℝ) : ℂ) := by
      exact hA.1.trace_eq_sum_eigenvalues
    have hre := congrArg Complex.re hc
    simpa using hre.symm
  have heig_le_trace : ∀ i, hA.1.eigenvalues i ≤ A.trace.re := by
    intro i
    have hnonneg (j : a) : 0 ≤ hA.1.eigenvalues j := hA.eigenvalues_nonneg j
    calc hA.1.eigenvalues i
        ≤ hA.1.eigenvalues i +
            ∑ j ∈ Finset.univ.erase i, hA.1.eigenvalues j :=
          le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hnonneg j))
      _ = ∑ j, hA.1.eigenvalues j := by
          rw [add_comm]
          exact Finset.sum_erase_add (s := Finset.univ)
            (f := fun j => hA.1.eigenvalues j) (Finset.mem_univ i)
      _ = A.trace.re := heig_sum
  let c : ℂ := ((A.trace.re : ℝ) : ℂ)
  have hsub :
      c • (1 : CMatrix a) - A =
        (U : CMatrix a) * (c • (1 : CMatrix a) - D) * star (U : CMatrix a) := by
    have hunit_scalar :
        (U : CMatrix a) * (c • (1 : CMatrix a)) * star (U : CMatrix a) =
          c • (1 : CMatrix a) := by
      have hunit : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
        simp
      calc
        (U : CMatrix a) * (c • (1 : CMatrix a)) * star (U : CMatrix a) =
            c • ((U : CMatrix a) * (1 : CMatrix a) * star (U : CMatrix a)) := by
          simp
        _ = c • (1 : CMatrix a) := by
          simp [hunit]
    calc
      c • (1 : CMatrix a) - A =
          c • (1 : CMatrix a) - (U : CMatrix a) * D * star (U : CMatrix a) := by
        rw [hdiag]
      _ = (U : CMatrix a) * (c • (1 : CMatrix a)) * star (U : CMatrix a) -
            (U : CMatrix a) * D * star (U : CMatrix a) := by
        rw [hunit_scalar]
      _ = (U : CMatrix a) * (c • (1 : CMatrix a) - D) * star (U : CMatrix a) := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
  have hdiag_sub :
      c • (1 : CMatrix a) - D =
        Matrix.diagonal fun i => (((A.trace.re - hA.1.eigenvalues i : ℝ) : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [D, c]
    · simp [D, Matrix.diagonal, hij]
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (U : CMatrix a))]
  rw [hdiag_sub]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  exact_mod_cast sub_nonneg.mpr (heig_le_trace i)

set_option maxHeartbeats 900000 in
/-- The operator norm of a PSD matrix is controlled by its trace. -/
theorem norm_le_trace_re_mul_norm_one_of_posSemidef {A : CMatrix a} (hA : A.PosSemidef) :
    ‖A‖ ≤ A.trace.re * ‖(1 : CMatrix a)‖ := by
  have hA0 : (0 : CMatrix a) ≤ A := by
    simpa [Matrix.le_iff] using hA
  have hle := posSemidef_le_trace_re_smul_one (a := a) hA
  have hnorm :
      ‖A‖ ≤ ‖(((A.trace.re : ℝ) : ℂ) • (1 : CMatrix a))‖ :=
    CStarAlgebra.norm_le_norm_of_nonneg_of_le
      (A := CMatrix a) (a := A)
      (b := (((A.trace.re : ℝ) : ℂ) • (1 : CMatrix a))) hA0 hle
  calc
    ‖A‖ ≤ ‖(((A.trace.re : ℝ) : ℂ) • (1 : CMatrix a))‖ := hnorm
    _ = A.trace.re * ‖(1 : CMatrix a)‖ := by
      rw [norm_smul]
      have htr_nonneg : 0 ≤ A.trace.re := (Matrix.PosSemidef.trace_nonneg hA).1
      rw [Complex.norm_of_nonneg htr_nonneg]

end State

section MeasureTheoryIntegrals

open MeasureTheory

universe w

theorem integral_traceNorm_le_sqrt_integral_hilbertSchmidtSq_of_rank_bound
    {α : Type w} [MeasurableSpace α] {μ : Measure α}
    {ι : Type u} [Fintype ι] [DecidableEq ι] [IsProbabilityMeasure μ]
    {f : α → CMatrix ι} {r : ℝ}
    (hrank : ∀ x,
      (Module.finrank ℂ (LinearMap.range (f x).toEuclideanLin) : ℝ) ≤ r)
    (hf_trace : Integrable (fun x => traceNorm (f x)) μ)
    (hf_hs : Integrable (fun x => hilbertSchmidtSq (f x)) μ) :
    (∫ x, traceNorm (f x) ∂μ) ≤
      Real.sqrt (r * ∫ x, hilbertSchmidtSq (f x) ∂μ) := by
  let g : α → ℝ := fun x => traceNorm (f x)
  let h : α → ℝ := fun x => hilbertSchmidtSq (f x)
  have hg_nonneg : 0 ≤ᵐ[μ] g := by
    filter_upwards with x
    exact traceNorm_nonneg (f x)
  have hh_nonneg : 0 ≤ᵐ[μ] h := by
    filter_upwards with x
    exact hilbertSchmidtSq_nonneg (f x)
  have hg_sq_le : ∀ x, g x ^ 2 ≤ r * h x := by
    intro x
    exact traceNorm_sq_le_rankBound_mul_hilbertSchmidtSq (f x) (hrank x)
  have hg_sq_int : Integrable (fun x => g x ^ 2) μ := by
    refine Integrable.mono' (hf_hs.const_mul r) ?_ ?_
    · exact (hf_trace.aestronglyMeasurable.aemeasurable.pow_const (2 : ℕ)).aestronglyMeasurable
    · filter_upwards [hh_nonneg] with x _hhx
      have hleft : ‖g x ^ 2‖ = g x ^ 2 := by
        rw [Real.norm_of_nonneg (sq_nonneg (g x))]
      rw [hleft]
      simpa [h] using hg_sq_le x
  have hg_memLp_two : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by
    convert (memLp_two_iff_integrable_sq hf_trace.aestronglyMeasurable).2
      (by simpa [g, pow_two] using hg_sq_int) using 1
    norm_num
  have hone_memLp_two : MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ :=
    memLp_const (1 : ℝ)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two
    (f := fun _ : α => (1 : ℝ)) (g := g)
    (by filter_upwards with _; norm_num) hg_nonneg hone_memLp_two hg_memLp_two
  have hleft :
      (∫ x, (1 : ℝ) * g x ∂μ) = ∫ x, g x ∂μ := by simp
  rw [hleft] at hholder
  have hone_int : (∫ _ : α, (1 : ℝ) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = 1 := by
    simp [measureReal_def]
  rw [hone_int, one_mul] at hholder
  have hholder_nat :
      (∫ x, g x ∂μ) ≤ (∫ x, g x ^ 2 ∂μ) ^ (1 / (2 : ℝ)) := by
    simpa [Real.rpow_natCast] using hholder
  have hsquare_int_le :
      (∫ x, g x ^ 2 ∂μ) ≤ r * ∫ x, h x ∂μ := by
    have hpoint : ∀ᵐ x ∂μ, g x ^ 2 ≤ r * h x := by
      filter_upwards with x
      exact hg_sq_le x
    have hright_int : Integrable (fun x => r * h x) μ := hf_hs.const_mul r
    calc
      (∫ x, g x ^ 2 ∂μ) ≤ ∫ x, r * h x ∂μ :=
        integral_mono_ae hg_sq_int hright_int
          (show (fun x => g x ^ 2) ≤ᶠ[ae μ] fun x => r * h x from hpoint)
      _ = r * ∫ x, h x ∂μ := by
        rw [integral_const_mul]
  have hsqrt_step :
      (∫ x, g x ^ 2 ∂μ) ^ (1 / (2 : ℝ)) ≤
        Real.sqrt (r * ∫ x, h x ∂μ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hsquare_int_le
  exact hholder_nat.trans hsqrt_step

theorem integral_traceNorm_le_sqrt_integral_hilbertSchmidtSq
    {α : Type w} [MeasurableSpace α] {μ : Measure α}
    {ι : Type u} [Fintype ι] [DecidableEq ι] [IsProbabilityMeasure μ]
    {f : α → CMatrix ι}
    (hf_trace : Integrable (fun x => traceNorm (f x)) μ)
    (hf_hs : Integrable (fun x => hilbertSchmidtSq (f x)) μ) :
    (∫ x, traceNorm (f x) ∂μ) ≤
      Real.sqrt ((Fintype.card ι : ℝ) * ∫ x, hilbertSchmidtSq (f x) ∂μ) := by
  let g : α → ℝ := fun x => traceNorm (f x)
  let h : α → ℝ := fun x => hilbertSchmidtSq (f x)
  have hg_nonneg : 0 ≤ᵐ[μ] g := by
    filter_upwards with x
    exact traceNorm_nonneg (f x)
  have hh_nonneg : 0 ≤ᵐ[μ] h := by
    filter_upwards with x
    exact hilbertSchmidtSq_nonneg (f x)
  have hg_sq_le : ∀ x, g x ^ 2 ≤ (Fintype.card ι : ℝ) * h x := by
    intro x
    exact traceNorm_sq_le_card_mul_hilbertSchmidtSq (f x)
  have hg_sq_int : Integrable (fun x => g x ^ 2) μ := by
    refine Integrable.mono' (hf_hs.const_mul (Fintype.card ι : ℝ)) ?_ ?_
    · exact (hf_trace.aestronglyMeasurable.aemeasurable.pow_const (2 : ℕ)).aestronglyMeasurable
    · filter_upwards [hh_nonneg] with x hhx
      have hleft : ‖g x ^ 2‖ = g x ^ 2 := by
        rw [Real.norm_of_nonneg (sq_nonneg (g x))]
      rw [hleft]
      exact (hg_sq_le x).trans_eq (by ring)
  have hg_memLp_two : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by
    convert (memLp_two_iff_integrable_sq hf_trace.aestronglyMeasurable).2
      (by simpa [g, pow_two] using hg_sq_int) using 1
    norm_num
  have hone_memLp_two : MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ :=
    memLp_const (1 : ℝ)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two
    (f := fun _ : α => (1 : ℝ)) (g := g)
    (by filter_upwards with _; norm_num) hg_nonneg hone_memLp_two hg_memLp_two
  have hleft :
      (∫ x, (1 : ℝ) * g x ∂μ) = ∫ x, g x ∂μ := by simp
  rw [hleft] at hholder
  have hone_int : (∫ _ : α, (1 : ℝ) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = 1 := by
    simp [measureReal_def]
  rw [hone_int, one_mul] at hholder
  have hholder_nat :
      (∫ x, g x ∂μ) ≤ (∫ x, g x ^ 2 ∂μ) ^ (1 / (2 : ℝ)) := by
    simpa [Real.rpow_natCast] using hholder
  have hsquare_int_le :
      (∫ x, g x ^ 2 ∂μ) ≤
        (Fintype.card ι : ℝ) * ∫ x, h x ∂μ := by
    have hpoint : ∀ᵐ x ∂μ, g x ^ 2 ≤ (Fintype.card ι : ℝ) * h x := by
      filter_upwards with x
      exact hg_sq_le x
    have hright_int : Integrable (fun x => (Fintype.card ι : ℝ) * h x) μ :=
      hf_hs.const_mul (Fintype.card ι : ℝ)
    calc
      (∫ x, g x ^ 2 ∂μ) ≤ ∫ x, (Fintype.card ι : ℝ) * h x ∂μ :=
        integral_mono_ae hg_sq_int hright_int
          (show (fun x => g x ^ 2) ≤ᶠ[ae μ] fun x =>
            (Fintype.card ι : ℝ) * h x from hpoint)
      _ = (Fintype.card ι : ℝ) * ∫ x, h x ∂μ := by
        rw [integral_const_mul]
  have hsqrt_step :
      (∫ x, g x ^ 2 ∂μ) ^ (1 / (2 : ℝ)) ≤
        Real.sqrt ((Fintype.card ι : ℝ) * ∫ x, h x ∂μ) := by
    have hnonneg_int : 0 ≤ ∫ x, g x ^ 2 ∂μ :=
      integral_nonneg (fun x => sq_nonneg (g x))
    have hright_nonneg : 0 ≤ (Fintype.card ι : ℝ) * ∫ x, h x ∂μ := by
      exact mul_nonneg (Nat.cast_nonneg _) (integral_nonneg_of_ae hh_nonneg)
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hsquare_int_le
  exact hholder_nat.trans hsqrt_step

end MeasureTheoryIntegrals

end

end QIT
