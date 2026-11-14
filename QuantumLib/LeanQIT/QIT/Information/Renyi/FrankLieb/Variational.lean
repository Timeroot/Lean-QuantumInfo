/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.FrankLieb.ScalarOperator

/-!
# Frank--Lieb variational representation

Epstein/Frank--Lieb variational objectives and value-set machinery for the
low-alpha sandwiched Renyi route.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Topology Matrix.Norms.L2Operator

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

/-- Rank-one PSD tensor weight obtained by vectorizing the fixed matrix in an
Epstein trace term. -/
def cMatrixVecWeight (K : CMatrix a) : CMatrix (a × a) :=
  rankOneMatrix (fun p : a × a => K p.1 p.2)

omit [DecidableEq a] in
/-- The vectorized Epstein weight is positive semidefinite. -/
theorem cMatrixVecWeight_posSemidef (K : CMatrix a) :
    (cMatrixVecWeight K).PosSemidef := by
  simpa [cMatrixVecWeight] using rankOneMatrix_pos (fun p : a × a => K p.1 p.2)

omit [DecidableEq a] in
/-- Vectorized trace identity for the Epstein trace term.

The transpose on the second tensor factor is the finite-dimensional
vectorization convention:
`Tr((K† A K) B) = Tr(|K⟩⟨K| (A ⊗ Bᵀ))`. -/
theorem epstein_traceTerm_tensor_trace_transpose (K A B : CMatrix a) :
    (((star K * A * K) * B).trace) =
      ((cMatrixVecWeight K * Matrix.kronecker A B.transpose).trace) := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    cMatrixVecWeight, rankOneMatrix_apply, Matrix.transpose_apply]
  simp only [Finset.sum_mul]
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  let e : (((a × a) × a) × a) ≃ (a × a) × (a × a) := {
    toFun x := ((x.1.2, x.1.1.2), (x.2, x.1.1.1))
    invFun y := (((y.2.2, y.1.2), y.1.1), y.2.1)
    left_inv := by
      intro x
      rcases x with ⟨⟨⟨x, x_1⟩, x_2⟩, x_3⟩
      rfl
    right_inv := by
      intro y
      rcases y with ⟨⟨p1, p2⟩, ⟨q1, q2⟩⟩
      rfl
  }
  refine Fintype.sum_equiv e _ _ ?_
  intro x
  simp [e, mul_assoc, mul_left_comm, mul_comm]

omit [DecidableEq a] in
/-- Real-part version of `epstein_traceTerm_tensor_trace_transpose`. -/
theorem epstein_traceTerm_tensor_trace_transpose_re (K A B : CMatrix a) :
    ((((star K * A * K) * B).trace).re) =
      (((cMatrixVecWeight K * Matrix.kronecker A B.transpose).trace).re) := by
  exact congrArg Complex.re (epstein_traceTerm_tensor_trace_transpose K A B)

/-- Entrywise complex conjugation as a real star-algebra equivalence on
complex matrices. -/
def cMatrixConjStarAlgEquiv : CMatrix a ≃⋆ₐ[ℝ] CMatrix a :=
  StarAlgEquiv.ofAlgEquiv (AlgEquiv.mapMatrix (Complex.conjAe)) (by
    intro A
    ext i j
    simp)

omit [Fintype a] [DecidableEq a] in
/-- For Hermitian/PSD matrices, entrywise conjugation is the ordinary
transpose. -/
theorem cMatrix_map_star_eq_transpose_of_posSemidef
    {A : CMatrix a} (hA : A.PosSemidef) :
    A.map star = A.transpose := by
  ext i j
  simpa using hA.isHermitian.apply j i

/-- Nonnegative real powers commute with entrywise conjugation on PSD matrices. -/
theorem cMatrix_rpow_map_star_nonneg
    {A : CMatrix a} (hA : A.PosSemidef) {s : ℝ} (hs : 0 ≤ s) :
    CFC.rpow (A.map star) s = (CFC.rpow A s).map star := by
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  have hmap_nonneg : 0 ≤ A.map star := by
    rw [cMatrix_map_star_eq_transpose_of_posSemidef hA]
    exact Matrix.nonneg_iff_posSemidef.mpr hA.transpose
  change (A.map star) ^ s = (A ^ s).map star
  rw [CFC.rpow_eq_cfc_real (a := A.map star) (y := s) hmap_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s) hA_nonneg]
  simpa [cMatrixConjStarAlgEquiv] using
    (StarAlgHomClass.map_cfc
      (cMatrixConjStarAlgEquiv (a := a))
      (fun x : ℝ => x ^ s) A
      (hf := (Real.continuous_rpow_const hs).continuousOn)
      (hφ := by
        change Continuous fun A : CMatrix a => A.map star
        fun_prop)).symm

/-- Nonnegative real powers commute with transpose on PSD matrices. -/
theorem cMatrix_rpow_transpose_nonneg
    {A : CMatrix a} (hA : A.PosSemidef) {s : ℝ} (hs : 0 ≤ s) :
    CFC.rpow A.transpose s = (CFC.rpow A s).transpose := by
  have hmapA : A.map star = A.transpose :=
    cMatrix_map_star_eq_transpose_of_posSemidef hA
  have hpowmap :
      CFC.rpow (A.map star) s = (CFC.rpow A s).map star :=
    cMatrix_rpow_map_star_nonneg hA hs
  have hpowPSD : (CFC.rpow A s).PosSemidef :=
    cMatrix_rpow_posSemidef (A := A) (s := s) hA
  have hpowmapTranspose :
      (CFC.rpow A s).map star = (CFC.rpow A s).transpose :=
    cMatrix_map_star_eq_transpose_of_posSemidef hpowPSD
  rw [← hmapA, hpowmap, hpowmapTranspose]


/-- Binary convex combination of complex matrices, with real weights coerced
to complex scalars. -/
def cMatrixConvexCombination (t : ℝ) (A B : CMatrix a) : CMatrix a :=
  ((t : ℂ) • A) + (((1 - t : ℝ) : ℂ) • B)

omit [Fintype a] [DecidableEq a] in
@[simp]
theorem cMatrixConvexCombination_apply
    (t : ℝ) (A B : CMatrix a) (i j : a) :
    cMatrixConvexCombination t A B i j =
      (t : ℂ) * A i j + ((1 - t : ℝ) : ℂ) * B i j := by
  simp [cMatrixConvexCombination]

omit [Fintype a] [DecidableEq a] in
/-- The local complex-scalar matrix convex-combination notation agrees with
the ambient real vector-space convex combination. -/
theorem cMatrixConvexCombination_eq_real_smul
    (t : ℝ) (A B : CMatrix a) :
    cMatrixConvexCombination t A B = t • A + (1 - t) • B := by
  ext i j
  simp [cMatrixConvexCombination]

omit [Fintype a] [DecidableEq a] in
/-- Positive semidefiniteness is preserved by complex scalar multiplication
by a nonnegative real scalar. -/
theorem posSemidef_complex_smul_of_real_nonneg
    {A : CMatrix a} (hA : A.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    (((t : ℂ) • A) : CMatrix a).PosSemidef := by
  have htC : (0 : ℂ) ≤ (t : ℂ) := by
    exact_mod_cast ht
  exact Matrix.PosSemidef.smul hA htC

omit [Fintype a] [DecidableEq a] in
/-- PSD matrices are closed under binary convex combinations written with
complex scalar multiplication by real weights. -/
theorem cMatrixConvexCombination_posSemidef
    {A B : CMatrix a} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (cMatrixConvexCombination t A B).PosSemidef := by
  unfold cMatrixConvexCombination
  exact Matrix.PosSemidef.add
    (posSemidef_complex_smul_of_real_nonneg hA ht0)
    (posSemidef_complex_smul_of_real_nonneg hB (sub_nonneg.mpr ht1))

omit [DecidableEq a] in
/-- Positive definite matrices are closed under binary convex combinations. -/
theorem cMatrixConvexCombination_posDef
    {A B : CMatrix a} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (cMatrixConvexCombination t A B).PosDef := by
  have hconv : (t • A + (1 - t) • B).PosDef :=
    Matrix.PosDef.convexCombination hA hB ht0 ht1
  simpa [cMatrixConvexCombination_eq_real_smul] using hconv

/-- PSD identity regularization by the positive part of a real parameter. -/
def cMatrixPSDRegularization (A : CMatrix a) (ε : ℝ) : CMatrix a :=
  A + max ε 0 • (1 : CMatrix a)

omit [Fintype a] in
/-- PSD identity regularization is PSD for every real parameter. -/
theorem cMatrixPSDRegularization_posSemidef
    {A : CMatrix a} (hA : A.PosSemidef) (ε : ℝ) :
    (cMatrixPSDRegularization A ε).PosSemidef := by
  exact cMatrix_posSemidef_add_nonneg_smul_one_posSemidef hA
    (show 0 ≤ max ε 0 from le_max_right ε 0)

omit [Fintype a] in
/-- PSD identity regularization is positive definite for positive parameter. -/
theorem cMatrixPSDRegularization_posDef_of_pos
    {A : CMatrix a} (hA : A.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (cMatrixPSDRegularization A ε).PosDef := by
  have hmax : max ε 0 = ε := max_eq_left hε.le
  simpa [cMatrixPSDRegularization, hmax] using
    State.cMatrix_posSemidef_add_pos_smul_one_posDef hA hε

omit [Fintype a] in
/-- PSD identity regularization tends back to the original matrix as
`ε → 0+`. -/
theorem cMatrixPSDRegularization_tendsto_zero (A : CMatrix a) :
    Filter.Tendsto (fun ε : ℝ => cMatrixPSDRegularization A ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds A) := by
  have hcont : Continuous fun ε : ℝ => cMatrixPSDRegularization A ε := by
    unfold cMatrixPSDRegularization
    fun_prop
  simpa [cMatrixPSDRegularization] using
    (hcont.continuousWithinAt (x := (0 : ℝ)) (s := Set.Ioi (0 : ℝ))).tendsto

omit [DecidableEq a] in
/-- The real trace of a binary complex-matrix convex combination is the same
binary convex combination of the real traces. -/
theorem cMatrixConvexCombination_trace_re
    (t : ℝ) (A B : CMatrix a) :
    ((cMatrixConvexCombination t A B).trace).re =
      t * A.trace.re + (1 - t) * B.trace.re := by
  simp [cMatrixConvexCombination, Matrix.trace_add, Matrix.trace_smul,
    Complex.mul_re]

/-- Power-of-power cancellation for PSD matrices and a positive real exponent. -/
theorem cMatrix_rpow_rpow_inv_of_pos
    {A : CMatrix a} (hA : A.PosSemidef) {c : ℝ} (hc_pos : 0 < c) :
    CFC.rpow (CFC.rpow A c) (1 / c) = A := by
  have hinv_nonneg : 0 ≤ (1 / c : ℝ) :=
    div_nonneg zero_le_one hc_pos.le
  have hmul : c * (1 / c) = (1 : ℝ) := by
    field_simp [hc_pos.ne']
  calc
    CFC.rpow (CFC.rpow A c) (1 / c) = CFC.rpow A (1 : ℝ) :=
      cMatrix_rpow_rpow_of_nonneg hA hc_pos.le hinv_nonneg hmul
    _ = A := by
      exact CFC.rpow_one A (ha := Matrix.nonneg_iff_posSemidef.mpr hA)

/-- Power-of-power reduction for positive-definite matrices and arbitrary
real exponents.

This is the positive-definite counterpart of
`cMatrix_rpow_rpow_of_nonneg`; it is needed for the Gour/Frank--Lieb
low-`α` Young optimizer, where the relevant exponent is negative. -/
theorem cMatrix_rpow_rpow_of_posDef
    {A : CMatrix a} (hA : A.PosDef)
    {r t s : ℝ} (hr_ne : r ≠ 0) (hrt : r * t = s) :
    CFC.rpow (CFC.rpow A r) t = CFC.rpow A s := by
  calc
    CFC.rpow (CFC.rpow A r) t = CFC.rpow A (r * t) := by
      exact CFC.rpow_rpow A r t hr_ne
        (ha := Matrix.PosDef.isStrictlyPositive hA)
    _ = CFC.rpow A s := by
      rw [hrt]

/-- Nonnegative real powers of the same PSD matrix multiply by adding
exponents. -/
theorem cMatrix_rpow_mul_rpow_of_nonneg
    {A : CMatrix a} (hA : A.PosSemidef) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    CFC.rpow A r * CFC.rpow A s = CFC.rpow A (r + s) := by
  let rNN : ℝ≥0 := ⟨r, hr⟩
  let sNN : ℝ≥0 := ⟨s, hs⟩
  by_cases hr_zero : rNN = 0
  · have hr' : r = 0 := by
      have hcoe := congrArg (fun x : ℝ≥0 => x.val) hr_zero
      simpa [rNN] using hcoe
    have hzero : CFC.rpow A (0 : ℝ) = 1 := by
      simp only [CFC.rpow]
      simpa using cfc_const_one (R := ℝ≥0) A
    rw [hr', zero_add, hzero, Matrix.one_mul]
  · by_cases hs_zero : sNN = 0
    · have hs' : s = 0 := by
        have hcoe := congrArg (fun x : ℝ≥0 => x.val) hs_zero
        simpa [sNN] using hcoe
      have hzero : CFC.rpow A (0 : ℝ) = 1 := by
        simp only [CFC.rpow]
        simpa using cfc_const_one (R := ℝ≥0) A
      rw [hs', add_zero, hzero, Matrix.mul_one]
    · have hsum : ((rNN + sNN : ℝ≥0) : ℝ) = r + s := by rfl
      have hrNN_pos : 0 < rNN := pos_iff_ne_zero.mpr hr_zero
      have hsNN_pos : 0 < sNN := pos_iff_ne_zero.mpr hs_zero
      have hadd : A ^ (rNN + sNN) = A ^ rNN * A ^ sNN :=
        CFC.nnrpow_add (a := A) hrNN_pos hsNN_pos
      have hrpow : A ^ rNN = CFC.rpow A r := by
        simpa [rNN] using (CFC.nnrpow_eq_rpow (a := A) hrNN_pos)
      have hspow : A ^ sNN = CFC.rpow A s := by
        simpa [sNN] using (CFC.nnrpow_eq_rpow (a := A) hsNN_pos)
      have hsumpow : A ^ (rNN + sNN) = CFC.rpow A (r + s) := by
        simpa [rNN, sNN, hsum] using (CFC.nnrpow_eq_rpow (a := A)
          (add_pos hrNN_pos hsNN_pos))
      rw [← hrpow, ← hspow, ← hsumpow, hadd]

/-- Epstein's trace functional primitive
`Tr[(K† σ^c K)^(1/c)]`, written as a real trace.

This is the matrix term appearing in the Frank--Lieb low-`α` proof after
the reverse-Holder reduction.  The unrestricted concavity theorem is the
remaining source theorem; this definition only fixes the local expression
used by its closed helper lemmas. -/
def epsteinTraceTerm (K σ : CMatrix a) (c : ℝ) : ℝ :=
  ((CFC.rpow (star K * CFC.rpow σ c * K) (1 / c)).trace).re

/-- Epstein--Young dual objective for the trace functional
`Tr[(K† σ^c K)^(1/c)]`.

For `0 < c < 1`, the missing unrestricted Frank--Lieb theorem can be routed
through the variational formula saying that the supremum of this objective
over PSD `X` is `epsteinTraceTerm K σ c`; the remaining hard input is Lieb
trace concavity for the first trace term. -/
def epsteinDualObjective (K σ X : CMatrix a) (c : ℝ) : ℝ :=
  (1 / c) * (((star K * CFC.rpow σ c * K) *
    CFC.rpow X (1 - c)).trace).re - ((1 - c) / c) * X.trace.re

/-- Epstein--Young dual objective values over PSD side matrices. -/
def epsteinDualObjectiveValueSet
    (K σ : CMatrix a) (c : ℝ) : Set ℝ :=
  {y | ∃ X : CMatrix a, X.PosSemidef ∧
    y = epsteinDualObjective K σ X c}

/-- The inner Epstein matrix `K† σ^c K` is PSD for PSD `σ`. -/
theorem epsteinTraceTerm_inner_posSemidef
    (K : CMatrix a) {σ : CMatrix a} (hσ : σ.PosSemidef) (c : ℝ) :
    (star K * CFC.rpow σ c * K).PosSemidef := by
  have hσc : (CFC.rpow σ c).PosSemidef :=
    cMatrix_rpow_posSemidef (A := σ) (s := c) hσ
  exact Matrix.PosSemidef.conjTranspose_mul_mul_same hσc K

/-- Epstein's trace functional is nonnegative on PSD inputs. -/
theorem epsteinTraceTerm_nonneg
    (K : CMatrix a) {σ : CMatrix a} (hσ : σ.PosSemidef) (c : ℝ) :
    0 ≤ epsteinTraceTerm K σ c := by
  have hinner : (star K * CFC.rpow σ c * K).PosSemidef :=
    epsteinTraceTerm_inner_posSemidef K hσ c
  have hpow :
      (CFC.rpow (star K * CFC.rpow σ c * K) (1 / c)).PosSemidef :=
    cMatrix_rpow_posSemidef
      (A := star K * CFC.rpow σ c * K) (s := 1 / c) hinner
  simpa [epsteinTraceTerm] using (Matrix.PosSemidef.trace_nonneg hpow).1

/-- The first trace term in the Epstein--Young objective is nonnegative on
PSD inputs. -/
theorem epsteinDualObjective_traceTerm_nonneg
    (K : CMatrix a) {σ X : CMatrix a}
    (hσ : σ.PosSemidef) (hX : X.PosSemidef) {c : ℝ} (_hc_le_one : c ≤ 1) :
    0 ≤ (((star K * CFC.rpow σ c * K) *
      CFC.rpow X (1 - c)).trace).re := by
  have hM : (star K * CFC.rpow σ c * K).PosSemidef :=
    epsteinTraceTerm_inner_posSemidef K hσ c
  have hXpow : (CFC.rpow X (1 - c)).PosSemidef :=
    cMatrix_rpow_posSemidef (A := X) (s := 1 - c) hX
  exact cMatrix_trace_mul_posSemidef_re_nonneg hM hXpow

omit [Fintype a] [DecidableEq a] in
private theorem epstein_young_scalar_bound
    {A S c : ℝ} (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hc_pos : 0 < c) (hc_lt_one : c < 1) :
    (1 / c) * (A ^ c * S ^ (1 - c)) - ((1 - c) / c) * S ≤ A := by
  have hc_le : 0 ≤ c := le_of_lt hc_pos
  have hone_sub_nonneg : 0 ≤ 1 - c := sub_nonneg.mpr hc_lt_one.le
  have hweights : c + (1 - c) = (1 : ℝ) := by ring
  have hgeom :
      A ^ c * S ^ (1 - c) ≤ c * A + (1 - c) * S :=
    Real.geom_mean_le_arith_mean2_weighted hc_le hone_sub_nonneg hA hS hweights
  have hinv_nonneg : 0 ≤ 1 / c := div_nonneg zero_le_one hc_pos.le
  calc
    (1 / c) * (A ^ c * S ^ (1 - c)) - ((1 - c) / c) * S
        ≤ (1 / c) * (c * A + (1 - c) * S) - ((1 - c) / c) * S :=
          sub_le_sub_right (mul_le_mul_of_nonneg_left hgeom hinv_nonneg) _
    _ = A := by
          field_simp [hc_pos.ne']
          ring

/-- Unnormalized PSD Holder handoff used by the Epstein--Young variational
upper bound.

This is the positive-power side of the Schatten variational formula after
normalizing the PSD side variable by its trace. -/
theorem posSemidef_trace_mul_rpow_le_psdSchattenPNorm_mul_trace_rpow
    {M X : CMatrix a} (hM : M.PosSemidef) (hX : X.PosSemidef)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1) :
    ((M * CFC.rpow X (1 - c)).trace).re ≤
      psdSchattenPNorm M hM ⟨1 / c, one_div_pos.mpr hc_pos⟩ *
        X.trace.re ^ (1 - c) := by
  let S : ℝ := X.trace.re
  let T : ℝ := ((M * CFC.rpow X (1 - c)).trace).re
  have hS_nonneg : 0 ≤ S := by
    simpa [S] using (Matrix.PosSemidef.trace_nonneg hX).1
  have hr_pos : 0 < 1 - c := sub_pos.mpr hc_lt_one
  by_cases hS_zero : S = 0
  · have hX_trace_im : X.trace.im = 0 :=
      (Matrix.PosSemidef.trace_nonneg hX).2.symm
    have hX_trace_zero : X.trace = 0 := by
      exact Complex.ext (by simpa [S] using hS_zero) hX_trace_im
    have hX_zero : X = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hX).mp hX_trace_zero
    have hXpow_zero : CFC.rpow X (1 - c) = 0 := by
      rw [hX_zero]
      simpa using (CFC.zero_rpow (A := CMatrix a) (x := 1 - c) (ne_of_gt hr_pos))
    rw [hXpow_zero]
    simp [S, hS_zero, Real.zero_rpow (ne_of_gt hr_pos)]
  · have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS_zero)
    let N : CMatrix a := (S⁻¹ : ℝ) • X
    have hscale_nonneg : 0 ≤ S⁻¹ := inv_nonneg.mpr hS_nonneg
    have hN : N.PosSemidef := by
      simpa [N] using Matrix.PosSemidef.smul hX hscale_nonneg
    have hNtr : N.trace.re = 1 := by
      have hX_trace_im : X.trace.im = 0 :=
        (Matrix.PosSemidef.trace_nonneg hX).2.symm
      simp [N, S, Matrix.trace_smul, Complex.mul_re, hX_trace_im,
        inv_mul_cancel₀ hS_zero]
    have hpq : (1 / c).HolderConjugate (1 / (1 - c)) := by
      simpa [one_div] using Real.HolderConjugate.inv_one_sub_inv hc_pos hc_lt_one
    have hr : 1 - c = 1 / (1 / (1 - c)) := by
      field_simp [ne_of_gt hr_pos]
    have hholder :
        ((M * CFC.rpow N (1 - c)).trace).re ≤
          psdSchattenPNorm M hM ⟨1 / c, one_div_pos.mpr hc_pos⟩ :=
      psd_trace_rpow_holder_variational_upper
        (M := M) (N := N) hM hN hNtr hpq hr
    have hNpow :
        CFC.rpow N (1 - c) =
          (S⁻¹ ^ (1 - c) : ℝ) • CFC.rpow X (1 - c) := by
      simpa [N] using
        cMatrix_rpow_real_smul_posSemidef_schatten
          (A := X) (s := 1 - c) hX hscale_nonneg
    have hholder' :
        ((M * ((S⁻¹ ^ (1 - c) : ℝ) • CFC.rpow X (1 - c))).trace).re ≤
          psdSchattenPNorm M hM ⟨1 / c, one_div_pos.mpr hc_pos⟩ := by
      have hholder' := hholder
      rw [hNpow] at hholder'
      exact hholder'
    have htrace_smul :
        ((M * ((S⁻¹ ^ (1 - c) : ℝ) • CFC.rpow X (1 - c))).trace).re =
          S⁻¹ ^ (1 - c) * T := by
      simp [T, Matrix.trace_smul, Complex.mul_re]
    have hscaled :
        S⁻¹ ^ (1 - c) * T ≤
          psdSchattenPNorm M hM ⟨1 / c, one_div_pos.mpr hc_pos⟩ := by
      simpa [htrace_smul] using hholder'
    have hSr_nonneg : 0 ≤ S ^ (1 - c) := Real.rpow_nonneg hS_nonneg _
    have hSr_pos : 0 < S ^ (1 - c) := Real.rpow_pos_of_pos hS_pos _
    have hscale_mul : S⁻¹ ^ (1 - c) * S ^ (1 - c) = 1 := by
      rw [Real.inv_rpow hS_nonneg]
      exact inv_mul_cancel₀ (ne_of_gt hSr_pos)
    have hmul :
        (S⁻¹ ^ (1 - c) * T) * S ^ (1 - c) ≤
          psdSchattenPNorm M hM ⟨1 / c, one_div_pos.mpr hc_pos⟩ * S ^ (1 - c) :=
      mul_le_mul_of_nonneg_right hscaled hSr_nonneg
    calc
      T = (S⁻¹ ^ (1 - c) * T) * S ^ (1 - c) := by
            exact
              (calc
                (S⁻¹ ^ (1 - c) * T) * S ^ (1 - c) =
                    T * (S⁻¹ ^ (1 - c) * S ^ (1 - c)) := by ring
                _ = T := by rw [hscale_mul, mul_one]).symm
      _ ≤ psdSchattenPNorm M hM ⟨1 / c, one_div_pos.mpr hc_pos⟩ *
          S ^ (1 - c) := hmul

/-- Upper-bound side of the finite-dimensional Epstein--Young variational
formula for the Epstein trace primitive. -/
theorem epsteinDualObjective_le_epsteinTraceTerm
    (K : CMatrix a) {σ X : CMatrix a}
    (hσ : σ.PosSemidef) (hX : X.PosSemidef)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1) :
    epsteinDualObjective K σ X c ≤ epsteinTraceTerm K σ c := by
  let M : CMatrix a := star K * CFC.rpow σ c * K
  let A : ℝ := epsteinTraceTerm K σ c
  let S : ℝ := X.trace.re
  let T : ℝ := ((M * CFC.rpow X (1 - c)).trace).re
  have hM : M.PosSemidef := by
    simpa [M] using epsteinTraceTerm_inner_posSemidef K hσ c
  have hA_nonneg : 0 ≤ A := by
    simpa [A] using epsteinTraceTerm_nonneg K hσ c
  have hS_nonneg : 0 ≤ S := by
    simpa [S] using (Matrix.PosSemidef.trace_nonneg hX).1
  have htrace_holder :
      T ≤ psdSchattenPNorm M hM ⟨1 / c, one_div_pos.mpr hc_pos⟩ *
        S ^ (1 - c) := by
    simpa [T, S] using
      posSemidef_trace_mul_rpow_le_psdSchattenPNorm_mul_trace_rpow
        (M := M) (X := X) hM hX hc_pos hc_lt_one
  have hnorm :
      psdSchattenPNorm M hM ⟨1 / c, one_div_pos.mpr hc_pos⟩ = A ^ c := by
    have hpower_eq : psdTracePower M hM (1 / c) = A := by
      change (CFC.rpow M (1 / c)).trace.re = A
      rfl
    have hinv : 1 / (1 / c) = c := by
      field_simp [hc_pos.ne']
    rw [psdSchattenPNorm, Internal.psdSchattenExpression, hpower_eq, hinv]
    rfl
  have htrace_bound : T ≤ A ^ c * S ^ (1 - c) := by
    rw [hnorm] at htrace_holder
    exact htrace_holder
  have hinv_nonneg : 0 ≤ 1 / c := div_nonneg zero_le_one hc_pos.le
  have hscaled :
      (1 / c) * T - ((1 - c) / c) * S ≤
        (1 / c) * (A ^ c * S ^ (1 - c)) - ((1 - c) / c) * S :=
    sub_le_sub_right (mul_le_mul_of_nonneg_left htrace_bound hinv_nonneg) _
  have hyoung :
      (1 / c) * (A ^ c * S ^ (1 - c)) - ((1 - c) / c) * S ≤ A :=
    epstein_young_scalar_bound hA_nonneg hS_nonneg hc_pos hc_lt_one
  have hmain :
      (1 / c) * T - ((1 - c) / c) * S ≤ A := hscaled.trans hyoung
  simpa [epsteinDualObjective, A, S, T, M] using hmain

omit [DecidableEq a] in
/-- The linear penalty term in the Epstein--Young objective is affine in the
side variable. -/
theorem epsteinDualObjective_penalty_convexCombination
    (X₁ X₂ : CMatrix a) (c t : ℝ) :
    ((1 - c) / c) * (cMatrixConvexCombination t X₁ X₂).trace.re =
      t * (((1 - c) / c) * X₁.trace.re) +
        (1 - t) * (((1 - c) / c) * X₂.trace.re) := by
  rw [cMatrixConvexCombination_trace_re]
  ring

/-- Lieb--Ando supplies the Epstein--Young first trace-term concavity.

This is the concrete Frank--Lieb bridge for the dual objective: vectorize the
fixed matrix `K` into the PSD tensor weight `|K⟩⟨K|`, apply the tensor
positive-functional Lieb--Ando concavity theorem to
`σ ↦ σ^c` and `X ↦ X^(1-c)`, then convert back with the vectorized trace
identity. -/
theorem epsteinDualObjective_traceTerm_concave
    (K σ₁ σ₂ X₁ X₂ : CMatrix a)
    {c t : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    (hX₁ : X₁.PosSemidef) (hX₂ : X₂.PosSemidef)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * ((((star K * CFC.rpow σ₁ c * K) *
              CFC.rpow X₁ (1 - c)).trace).re) +
          (1 - t) * ((((star K * CFC.rpow σ₂ c * K) *
              CFC.rpow X₂ (1 - c)).trace).re) ≤
        ((((star K * CFC.rpow (cMatrixConvexCombination t σ₁ σ₂) c * K) *
            CFC.rpow (cMatrixConvexCombination t X₁ X₂) (1 - c)).trace).re) := by
  let p : ℝ≥0 := ⟨c, hc_pos.le⟩
  have hp : p ∈ Set.Ioo (0 : ℝ≥0) 1 := by
    constructor
    · exact_mod_cast hc_pos
    · exact_mod_cast hc_lt_one
  have hX₁T : X₁.transpose.PosSemidef := hX₁.transpose
  have hX₂T : X₂.transpose.PosSemidef := hX₂.transpose
  have hW : (cMatrixVecWeight K).PosSemidef := cMatrixVecWeight_posSemidef K
  have htensor :=
    liebAndo_tensorWeightedTraceConcavity_posSemidef
      (a := a) (b := a) (p := p) hp
      (A₁ := σ₁) (A₂ := σ₂)
      (B₁ := X₁.transpose) (B₂ := X₂.transpose)
      (W := cMatrixVecWeight K)
      hσ₁ hσ₂ hX₁T hX₂T hW ht0 ht1
  have h1c_nonneg : 0 ≤ 1 - c := sub_nonneg.mpr hc_lt_one.le
  have hX₁powT :
      CFC.rpow X₁.transpose (1 - (p : ℝ)) =
        (CFC.rpow X₁ (1 - c)).transpose := by
    simpa [p] using cMatrix_rpow_transpose_nonneg (A := X₁) hX₁ h1c_nonneg
  have hX₂powT :
      CFC.rpow X₂.transpose (1 - (p : ℝ)) =
        (CFC.rpow X₂ (1 - c)).transpose := by
    simpa [p] using cMatrix_rpow_transpose_nonneg (A := X₂) hX₂ h1c_nonneg
  have hXmix : (cMatrixConvexCombination t X₁ X₂).PosSemidef :=
    cMatrixConvexCombination_posSemidef hX₁ hX₂ ht0 ht1
  have hXmixT :
      t • X₁.transpose + (1 - t) • X₂.transpose =
        (cMatrixConvexCombination t X₁ X₂).transpose := by
    ext i j
    simp [cMatrixConvexCombination]
  have hXmixpowT :
      CFC.rpow (t • X₁.transpose + (1 - t) • X₂.transpose) (1 - (p : ℝ)) =
        (CFC.rpow (cMatrixConvexCombination t X₁ X₂) (1 - c)).transpose := by
    rw [hXmixT]
    simpa [p] using
      cMatrix_rpow_transpose_nonneg
        (A := cMatrixConvexCombination t X₁ X₂) hXmix h1c_nonneg
  have hσmix :
      t • σ₁ + (1 - t) • σ₂ = cMatrixConvexCombination t σ₁ σ₂ :=
    (cMatrixConvexCombination_eq_real_smul t σ₁ σ₂).symm
  have htrace₁ :=
    epstein_traceTerm_tensor_trace_transpose_re K
      (CFC.rpow σ₁ c) (CFC.rpow X₁ (1 - c))
  have htrace₂ :=
    epstein_traceTerm_tensor_trace_transpose_re K
      (CFC.rpow σ₂ c) (CFC.rpow X₂ (1 - c))
  have htracet :=
    epstein_traceTerm_tensor_trace_transpose_re K
      (CFC.rpow (cMatrixConvexCombination t σ₁ σ₂) c)
      (CFC.rpow (cMatrixConvexCombination t X₁ X₂) (1 - c))
  have htensor' := htensor
  rw [hX₁powT, hX₂powT, hXmixpowT, hσmix] at htensor'
  have hpcoe : (p : ℝ) = c := rfl
  rw [hpcoe] at htensor'
  rw [htrace₁, htrace₂, htracet]
  simpa using htensor'

/-- Algebraic handoff from Lieb trace concavity to concavity of the
Epstein--Young dual objective.

The hard theorem is the hypothesis `htrace`, i.e. Lieb trace concavity for
the first term. This lemma only transports that theorem through the affine
penalty in `X`. -/
theorem epsteinDualObjective_concave_of_traceTerm
    (K σ₁ σ₂ X₁ X₂ : CMatrix a)
    {c t : ℝ} (hc_pos : 0 < c)
    (htrace :
      t * ((((star K * CFC.rpow σ₁ c * K) *
              CFC.rpow X₁ (1 - c)).trace).re) +
          (1 - t) * ((((star K * CFC.rpow σ₂ c * K) *
              CFC.rpow X₂ (1 - c)).trace).re) ≤
        ((((star K * CFC.rpow (cMatrixConvexCombination t σ₁ σ₂) c * K) *
            CFC.rpow (cMatrixConvexCombination t X₁ X₂) (1 - c)).trace).re)) :
    t * epsteinDualObjective K σ₁ X₁ c +
        (1 - t) * epsteinDualObjective K σ₂ X₂ c ≤
      epsteinDualObjective K (cMatrixConvexCombination t σ₁ σ₂)
        (cMatrixConvexCombination t X₁ X₂) c := by
  let T₁ : ℝ :=
    ((((star K * CFC.rpow σ₁ c * K) *
      CFC.rpow X₁ (1 - c)).trace).re)
  let T₂ : ℝ :=
    ((((star K * CFC.rpow σ₂ c * K) *
      CFC.rpow X₂ (1 - c)).trace).re)
  let Tt : ℝ :=
    ((((star K * CFC.rpow (cMatrixConvexCombination t σ₁ σ₂) c * K) *
      CFC.rpow (cMatrixConvexCombination t X₁ X₂) (1 - c)).trace).re)
  have htrace' : t * T₁ + (1 - t) * T₂ ≤ Tt := by
    simpa [T₁, T₂, Tt] using htrace
  have hinv_nonneg : 0 ≤ 1 / c := div_nonneg zero_le_one hc_pos.le
  have hscaled :
      (1 / c) * (t * T₁ + (1 - t) * T₂) ≤ (1 / c) * Tt :=
    mul_le_mul_of_nonneg_left htrace' hinv_nonneg
  have hpenalty :
      ((1 - c) / c) * (cMatrixConvexCombination t X₁ X₂).trace.re =
        t * (((1 - c) / c) * X₁.trace.re) +
          (1 - t) * (((1 - c) / c) * X₂.trace.re) :=
    epsteinDualObjective_penalty_convexCombination X₁ X₂ c t
  unfold epsteinDualObjective
  dsimp [T₁, T₂, Tt] at hscaled
  rw [hpenalty]
  nlinarith

/-- Concavity of the Epstein--Young dual objective in the two PSD inputs.

This is the first complete Frank--Lieb handoff: the hard first trace term is
provided by `epsteinDualObjective_traceTerm_concave`; the remaining penalty is
affine. -/
theorem epsteinDualObjective_concave
    (K σ₁ σ₂ X₁ X₂ : CMatrix a)
    {c t : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    (hX₁ : X₁.PosSemidef) (hX₂ : X₂.PosSemidef)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * epsteinDualObjective K σ₁ X₁ c +
        (1 - t) * epsteinDualObjective K σ₂ X₂ c ≤
      epsteinDualObjective K (cMatrixConvexCombination t σ₁ σ₂)
        (cMatrixConvexCombination t X₁ X₂) c := by
  exact
    epsteinDualObjective_concave_of_traceTerm K σ₁ σ₂ X₁ X₂ hc_pos
      (epsteinDualObjective_traceTerm_concave K σ₁ σ₂ X₁ X₂
        hc_pos hc_lt_one hσ₁ hσ₂ hX₁ hX₂ ht0 ht1)

/-- The Epstein--Young objective attains the Epstein trace term at the
natural optimizer `X = (K† σ^c K)^(1/c)`.

This is the equality side of the finite-dimensional Young variational formula.
The complementary upper-bound direction remains the hard analytic ingredient. -/
theorem epsteinDualObjective_eq_epsteinTraceTerm_at_optimizer
    (K : CMatrix a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1) :
    epsteinDualObjective K σ
      (CFC.rpow (star K * CFC.rpow σ c * K) (1 / c)) c =
        epsteinTraceTerm K σ c := by
  let M : CMatrix a := star K * CFC.rpow σ c * K
  have hM : M.PosSemidef := by
    simpa [M] using epsteinTraceTerm_inner_posSemidef K hσ c
  have hinv_nonneg : 0 ≤ (1 / c : ℝ) := div_nonneg zero_le_one hc_pos.le
  have hsub_nonneg : 0 ≤ (1 - c : ℝ) := sub_nonneg.mpr hc_lt_one.le
  have hpowX :
      CFC.rpow (CFC.rpow M (1 / c)) (1 - c) =
        CFC.rpow M ((1 / c) * (1 - c)) :=
    cMatrix_rpow_rpow_of_nonneg hM hinv_nonneg hsub_nonneg rfl
  have hMone : CFC.rpow M (1 : ℝ) = M :=
    CFC.rpow_one M (ha := Matrix.nonneg_iff_posSemidef.mpr hM)
  have hadd :
      (1 : ℝ) + (1 / c) * (1 - c) = 1 / c := by
    field_simp [hc_pos.ne']
    ring
  have hmul :
      M * CFC.rpow M ((1 / c) * (1 - c)) =
        CFC.rpow M (1 / c) := by
    calc
      M * CFC.rpow M ((1 / c) * (1 - c))
          = CFC.rpow M (1 : ℝ) *
              CFC.rpow M ((1 / c) * (1 - c)) := by rw [hMone]
      _ = CFC.rpow M ((1 : ℝ) + (1 / c) * (1 - c)) :=
          cMatrix_rpow_mul_rpow_of_nonneg hM zero_le_one
            (mul_nonneg hinv_nonneg hsub_nonneg)
      _ = CFC.rpow M (1 / c) := by rw [hadd]
  have hfirst :
      (((star K * CFC.rpow σ c * K) *
          CFC.rpow (CFC.rpow (star K * CFC.rpow σ c * K) (1 / c))
            (1 - c)).trace).re =
        epsteinTraceTerm K σ c := by
    change ((M * CFC.rpow (CFC.rpow M (1 / c)) (1 - c)).trace).re =
      epsteinTraceTerm K σ c
    rw [hpowX, hmul]
    rfl
  have hoptimizerTrace :
      ((CFC.rpow (star K * CFC.rpow σ c * K) (1 / c)).trace).re =
        epsteinTraceTerm K σ c := by
    rfl
  unfold epsteinDualObjective
  rw [hfirst, hoptimizerTrace]
  field_simp [hc_pos.ne']
  ring

theorem epsteinDualObjectiveValueSet_mem
    {K σ X : CMatrix a} (hX : X.PosSemidef) (c : ℝ) :
    epsteinDualObjective K σ X c ∈
      epsteinDualObjectiveValueSet K σ c :=
  ⟨X, hX, rfl⟩

/-- Finite-dimensional Epstein--Young variational formula as a greatest-value
statement.

This packages the already proved Young upper bound and optimizer equality:
for `0 < c < 1`, the trace primitive
`Tr[(K† σ^c K)^(1/c)]` is the supremal value of the Epstein--Young dual
objective over PSD side matrices. -/
theorem epsteinDualObjectiveValueSet_isGreatest
    (K : CMatrix a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1) :
    IsGreatest (epsteinDualObjectiveValueSet K σ c)
      (epsteinTraceTerm K σ c) := by
  let X : CMatrix a :=
    CFC.rpow (star K * CFC.rpow σ c * K) (1 / c)
  have hinner : (star K * CFC.rpow σ c * K).PosSemidef :=
    epsteinTraceTerm_inner_posSemidef K hσ c
  have hX : X.PosSemidef := by
    simpa [X] using
      cMatrix_rpow_posSemidef
        (A := star K * CFC.rpow σ c * K) (s := 1 / c) hinner
  constructor
  · refine ⟨X, hX, ?_⟩
    simpa [X] using
      (epsteinDualObjective_eq_epsteinTraceTerm_at_optimizer
        (a := a) K hσ hc_pos hc_lt_one).symm
  · intro y hy
    rcases hy with ⟨Y, hY, rfl⟩
    exact epsteinDualObjective_le_epsteinTraceTerm
      (a := a) K hσ hY hc_pos hc_lt_one

/-- `sSup` form of the finite-dimensional Epstein--Young variational
formula. -/
theorem epsteinDualObjectiveValueSet_sSup_eq
    (K : CMatrix a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1) :
    sSup (epsteinDualObjectiveValueSet K σ c) =
      epsteinTraceTerm K σ c :=
  (epsteinDualObjectiveValueSet_isGreatest
    (a := a) K hσ hc_pos hc_lt_one).csSup_eq

end

end QIT
