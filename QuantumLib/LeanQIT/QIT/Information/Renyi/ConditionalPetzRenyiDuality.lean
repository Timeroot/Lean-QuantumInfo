/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.ConditionalRenyiSource
public import QIT.Information.Renyi.ConditionalRenyiClassical
public import QIT.Information.AlickiFannesWinter
public import QIT.Measurements.Support

/-!
# Downward Petz Renyi duality trace preparation

Source-shaped trace lemmas for Tomamichel2015FiniteResources, `cond.tex`,
Proposition `pr:dual-old`, lines 317--336.

This module formalizes the normalized non-endpoint part currently expressible
by the local API.  The trace route starts with the source rewrite
`Tr(ρ_AB^α ρ_B^(1-α)) =
  Tr(ρ_AB^(α-1) |ρ⟩⟨ρ|_ABC ρ_B^(1-α))`
for a pure tripartite state, then proves the Schmidt/intertwiner bridge from
the `AB|C` side to the `AC|B` side before closing the scalar entropy identity.
The boundary points `alpha = 0` and `alpha = 2` are closed by the
support-projection bookend `cMatrix_rpow_neg_one_mul_self_eq_rangeProjection`
(the `alpha = 0` replacement for the singular-PSD exponent law), yielding the
closed-interval duality `PureVector.conditionalPetzRenyiDown_duality` on
`Set.Icc 0 2`.  Subnormalized-state variants are intentionally not claimed
here.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

omit [DecidableEq a] in
private theorem trace_mul_kronecker_one_right_eq_partialTraceB_forPetz
    (X : CMatrix (Prod a b)) (U : CMatrix a) :
    (X * Matrix.kronecker U (1 : CMatrix b)).trace =
      (partialTraceB (a := a) (b := b) X * U).trace := by
  have hpartial :
      partialTraceB (a := a) (b := b) (X * Matrix.kronecker U (1 : CMatrix b)) =
        partialTraceB (a := a) (b := b) X * U :=
    partialTraceB_mul_leftKroneckerOne X U
  rw [← hpartial, partialTraceB_trace]

/-- Product rule for real powers of a positive semidefinite matrix away from the
zero-exponent sum convention.

This is used by source trace rewrites that combine adjacent marginal powers,
for example `rho^s * rho^t = rho^(s+t)`. -/
theorem cMatrix_rpow_add_psd_forPetz
    {d : Type*} [Fintype d] [DecidableEq d] {A : CMatrix d}
    (hA : A.PosSemidef) {p q : Real} (hpq : p + q ≠ 0) :
    CFC.rpow A p * CFC.rpow A q = CFC.rpow A (p + q) := by
  let U : Matrix.unitaryGroup d Complex := hA.isHermitian.eigenvectorUnitary
  let eigen : d → Real := hA.isHermitian.eigenvalues
  have heigen_nonneg : ∀ i, 0 ≤ eigen i := fun i => hA.eigenvalues_nonneg i
  have hA_spec :
      A = (U : CMatrix d) *
        (Matrix.diagonal fun i => (eigen i : Complex)) *
        star (U : CMatrix d) := by
    simpa [U, eigen, Function.comp_def] using hA.isHermitian.spectral_theorem
  have hp :
      CFC.rpow A p =
        (U : CMatrix d) *
          (Matrix.diagonal fun i => ((eigen i ^ p : Real) : Complex)) *
          star (U : CMatrix d) := by
    rw [hA_spec]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal U eigen heigen_nonneg p
  have hq :
      CFC.rpow A q =
        (U : CMatrix d) *
          (Matrix.diagonal fun i => ((eigen i ^ q : Real) : Complex)) *
          star (U : CMatrix d) := by
    rw [hA_spec]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal U eigen heigen_nonneg q
  have hpq_pow :
      CFC.rpow A (p + q) =
        (U : CMatrix d) *
          (Matrix.diagonal fun i => ((eigen i ^ (p + q) : Real) : Complex)) *
          star (U : CMatrix d) := by
    rw [hA_spec]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal U eigen heigen_nonneg (p + q)
  have hconj (M : CMatrix d) :
      (U : CMatrix d) * M * star (U : CMatrix d) =
        (Unitary.conjStarAlgAut Complex (CMatrix d) U) M := by
    simp [Unitary.conjStarAlgAut_apply]
  have hdiag :
      (Matrix.diagonal fun i => ((eigen i ^ p : Real) : Complex) : CMatrix d) *
        (Matrix.diagonal fun i => ((eigen i ^ q : Real) : Complex)) =
        Matrix.diagonal (fun i => ((eigen i ^ (p + q) : Real) : Complex)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Real.rpow_add' (heigen_nonneg i) hpq]
    · simp [hij]
  rw [hp, hq, hpq_pow, hconj, hconj, hconj, ← map_mul, hdiag]

/-- Inverse square law for a positive semidefinite matrix with the CFC
zero-on-kernel convention: `A^(-1) * A * A = A`.

The exponent law `cMatrix_rpow_add_psd_forPetz` excludes the zero exponent
sum, so the `(-1) + 1 + 1 = 1` combination needed at the `alpha = 0` Petz
boundary is proved separately here by diagonalization: on each eigenvalue the
identity is `λ⁻¹ * λ * λ = λ` for `λ > 0`, and the junk value `0^(-1) = 0`
absorbs the kernel.  No full-rank hypothesis is needed. -/
theorem cMatrix_rpow_neg_one_mul_self_mul_self
    {d : Type*} [Fintype d] [DecidableEq d] {A : CMatrix d}
    (hA : A.PosSemidef) :
    CFC.rpow A (-1) * A * A = A := by
  let U : Matrix.unitaryGroup d Complex := hA.isHermitian.eigenvectorUnitary
  let eigen : d → Real := hA.isHermitian.eigenvalues
  have heigen_nonneg : ∀ i, 0 ≤ eigen i := fun i => hA.eigenvalues_nonneg i
  have hA_spec :
      A = (U : CMatrix d) *
        (Matrix.diagonal fun i => (eigen i : Complex)) *
        star (U : CMatrix d) := by
    simpa [U, eigen, Function.comp_def] using hA.isHermitian.spectral_theorem
  have hinv :
      CFC.rpow A (-1) =
        (U : CMatrix d) *
          (Matrix.diagonal fun i => ((eigen i ^ (-1 : Real) : Real) : Complex)) *
          star (U : CMatrix d) := by
    rw [hA_spec]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal U eigen heigen_nonneg (-1)
  have hconj (M : CMatrix d) :
      (U : CMatrix d) * M * star (U : CMatrix d) =
        (Unitary.conjStarAlgAut Complex (CMatrix d) U) M := by
    simp [Unitary.conjStarAlgAut_apply]
  have hdiag :
      (Matrix.diagonal fun i => ((eigen i ^ (-1 : Real) : Real) : Complex) :
          CMatrix d) *
        (Matrix.diagonal fun i => (eigen i : Complex)) *
        (Matrix.diagonal fun i => (eigen i : Complex)) =
        Matrix.diagonal (fun i => (eigen i : Complex)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases h0 : eigen i = 0
      · simp [h0]
      · have hreal : eigen i ^ (-1 : Real) * eigen i * eigen i = eigen i := by
          rw [Real.rpow_neg_one, inv_mul_cancel₀ h0, one_mul]
        simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, ↓reduceIte,
          ← Complex.ofReal_mul, hreal]
    · simp [hij]
  rw [hinv, hA_spec]
  simp only [hconj]
  rw [← map_mul, ← map_mul, hdiag]

/-- The `alpha = 0` Petz bookend: for a positive semidefinite matrix,
`A^(-1) * A` is the orthogonal projection onto the range of `A`.

Both sides act as the identity on the range of `A` (by
`cMatrix_rpow_neg_one_mul_self_mul_self`) and vanish on its orthogonal
complement (the kernel of the Hermitian matrix `A`, where the CFC junk value
`0^(-1) = 0` absorbs the inverse power).  This replaces the exponent law
`cMatrix_rpow_add_psd_forPetz`, whose `p + q ≠ 0` side condition fails exactly
at the `alpha = 0` boundary; no full-rank hypothesis is needed. -/
theorem cMatrix_rpow_neg_one_mul_self_eq_rangeProjection
    {d : Type*} [Fintype d] [DecidableEq d] {A : CMatrix d}
    (hA : A.PosSemidef) :
    CFC.rpow A (-1) * A = Matrix.rangeProjection A := by
  have hTAA : ∀ x : EuclideanSpace Complex d,
      (CFC.rpow A (-1)).toEuclideanLin (A.toEuclideanLin (A.toEuclideanLin x)) =
        A.toEuclideanLin x := by
    intro x
    have hmat : (CFC.rpow A (-1) * A * A).toEuclideanLin = A.toEuclideanLin :=
      congrArg Matrix.toEuclideanLin (cMatrix_rpow_neg_one_mul_self_mul_self hA)
    have hx : (CFC.rpow A (-1) * A * A).toEuclideanLin x = A.toEuclideanLin x :=
      LinearMap.ext_iff.mp hmat x
    rw [Matrix.toLpLin_mul, Matrix.toLpLin_mul] at hx
    simpa [LinearMap.comp_apply] using hx
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, Matrix.rangeProjection_toEuclideanLin]
  set K : Submodule Complex (EuclideanSpace Complex d) :=
    LinearMap.range A.toEuclideanLin with hK
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply]
  show (CFC.rpow A (-1)).toEuclideanLin (A.toEuclideanLin v) = K.starProjection v
  have hsym : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian
  have hker : Kᗮ = LinearMap.ker A.toEuclideanLin := hsym.orthogonal_range
  have hdecomp : v = K.starProjection v + (v - K.starProjection v) :=
    (add_sub_cancel _ _).symm
  rcases K.starProjection_apply_mem v with ⟨w, hw⟩
  have hu : v - K.starProjection v ∈ Kᗮ := K.sub_starProjection_mem_orthogonal v
  have hAu : A.toEuclideanLin (v - K.starProjection v) = 0 :=
    LinearMap.mem_ker.mp (hker ▸ hu)
  calc (CFC.rpow A (-1)).toEuclideanLin (A.toEuclideanLin v)
      = (CFC.rpow A (-1)).toEuclideanLin
          (A.toEuclideanLin (K.starProjection v + (v - K.starProjection v))) := by
        rw [← hdecomp]
    _ = (CFC.rpow A (-1)).toEuclideanLin
          (A.toEuclideanLin (A.toEuclideanLin w)) := by
        rw [map_add, map_add, hAu, map_zero, add_zero, ← hw]
    _ = A.toEuclideanLin w := hTAA w
    _ = K.starProjection v := hw

private theorem cMatrix_rpow_mulVec_of_posSemidef_eigen_forPetz
    {d : Type*} [Fintype d] [DecidableEq d] {A : CMatrix d}
    (hA : A.PosSemidef) {v : d -> Complex} {lambda : Real}
    (_hlambda : 0 <= lambda)
    (hev : A.mulVec v = (lambda : Complex) • v) (p : Real) :
    (CFC.rpow A p).mulVec v = ((lambda ^ p : Real) : Complex) • v := by
  let U : Matrix.unitaryGroup d Complex := hA.isHermitian.eigenvectorUnitary
  let eigen : d -> Real := hA.isHermitian.eigenvalues
  let D : CMatrix d := Matrix.diagonal fun i => ((eigen i : Real) : Complex)
  let Dp : CMatrix d := Matrix.diagonal fun i => ((eigen i ^ p : Real) : Complex)
  let w : d -> Complex := (star (U : CMatrix d)).mulVec v
  have hA_spec :
      A = (U : CMatrix d) * D * star (U : CMatrix d) := by
    simpa [U, eigen, D, Function.comp_def] using hA.isHermitian.spectral_theorem
  have hpow :
      CFC.rpow A p = (U : CMatrix d) * Dp * star (U : CMatrix d) := by
    simpa [U, eigen, Dp] using cMatrix_rpow_eq_eigenbasis_diagonal hA p
  have hcoord_left :
      (star (U : CMatrix d)).mulVec (A.mulVec v) = D.mulVec w := by
    rw [hA_spec]
    have hUU : star (U : CMatrix d) * (U : CMatrix d) = 1 :=
      Unitary.coe_star_mul_self U
    have hmat :
        star (U : CMatrix d) * ((U : CMatrix d) * (D * star (U : CMatrix d))) =
          D * star (U : CMatrix d) := by
      calc
        star (U : CMatrix d) * ((U : CMatrix d) * (D * star (U : CMatrix d))) =
            (star (U : CMatrix d) * (U : CMatrix d)) * (D * star (U : CMatrix d)) := by
              noncomm_ring
        _ = 1 * (D * star (U : CMatrix d)) := by rw [hUU]
        _ = D * star (U : CMatrix d) := by simp
    simpa [w, Matrix.mulVec_mulVec, Matrix.mul_assoc] using
      congrArg (fun M : CMatrix d => M.mulVec v) hmat
  have hcoord : D.mulVec w = (lambda : Complex) • w := by
    calc
      D.mulVec w = (star (U : CMatrix d)).mulVec (A.mulVec v) := hcoord_left.symm
      _ = (star (U : CMatrix d)).mulVec ((lambda : Complex) • v) := by rw [hev]
      _ = (lambda : Complex) • w := by
            rw [Matrix.mulVec_smul]
  have hDp_coord : Dp.mulVec w = ((lambda ^ p : Real) : Complex) • w := by
    ext i
    have hi := congrFun hcoord i
    by_cases hwi : w i = 0
    · simp [Dp, Matrix.mulVec, dotProduct, Matrix.diagonal, hwi]
    · have heq_complex : (eigen i : Complex) = (lambda : Complex) := by
        have hi' : (eigen i : Complex) * w i = (lambda : Complex) * w i := by
          simpa [D, Matrix.mulVec, dotProduct, Matrix.diagonal] using hi
        exact mul_right_cancel₀ hwi hi'
      have heq : eigen i = lambda := Complex.ofReal_injective heq_complex
      simp [Dp, Matrix.mulVec, dotProduct, Matrix.diagonal, heq]
  have hv : (U : CMatrix d).mulVec w = v := by
    calc
      (U : CMatrix d).mulVec w =
          ((U : CMatrix d) * star (U : CMatrix d)).mulVec v := by
            simp [w, Matrix.mulVec_mulVec]
      _ = (1 : CMatrix d).mulVec v := by
            have hUU : (U : CMatrix d) * star (U : CMatrix d) = 1 :=
              Unitary.coe_mul_star_self U
            rw [hUU]
      _ = v := by simp
  calc
    (CFC.rpow A p).mulVec v =
        ((U : CMatrix d) * Dp * star (U : CMatrix d)).mulVec v := by rw [hpow]
    _ = (U : CMatrix d).mulVec (Dp.mulVec w) := by
          simp [w, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = (U : CMatrix d).mulVec (((lambda ^ p : Real) : Complex) • w) := by
          rw [hDp_coord]
    _ = ((lambda ^ p : Real) : Complex) • (U : CMatrix d).mulVec w := by
          rw [Matrix.mulVec_smul]
    _ = ((lambda ^ p : Real) : Complex) • v := by rw [hv]

private theorem cMatrix_rpow_mulVec_eigenvectorUnitary_forPetz
    {d : Type*} [Fintype d] [DecidableEq d] {A : CMatrix d}
    (hA : A.PosSemidef) (k : d) (p : Real) :
    (CFC.rpow A p).mulVec
        (fun x => (hA.isHermitian.eigenvectorUnitary : CMatrix d) x k) =
      ((hA.isHermitian.eigenvalues k ^ p : Real) : Complex) •
        fun x => (hA.isHermitian.eigenvectorUnitary : CMatrix d) x k := by
  apply cMatrix_rpow_mulVec_of_posSemidef_eigen_forPetz
    hA (hA.eigenvalues_nonneg k) ?_ p
  simpa [Matrix.IsHermitian.eigenvectorUnitary_apply] using
    hA.isHermitian.mulVec_eigenvectorBasis k

omit [DecidableEq a] in
/-- Two-sided trace lifting through `Tr_C`.

This is the trace bookkeeping used in Tomamichel2015FiniteResources,
`cond.tex:329-331`, when a trace over `AB` is rewritten as a trace over a
purifying `ABC` system with an identity on `C`. -/
theorem trace_left_right_kronecker_one_eq_partialTraceB
    (R : CMatrix (Prod a b)) (L M : CMatrix a) :
    ((Matrix.kronecker L (1 : CMatrix b) * R *
      Matrix.kronecker M (1 : CMatrix b)).trace).re =
      ((L * partialTraceB (a := a) (b := b) R * M).trace).re := by
  calc
    ((Matrix.kronecker L (1 : CMatrix b) * R *
        Matrix.kronecker M (1 : CMatrix b)).trace).re =
        (((R * Matrix.kronecker M (1 : CMatrix b)) *
          Matrix.kronecker L (1 : CMatrix b)).trace).re := by
          rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
    _ = ((partialTraceB (a := a) (b := b)
          (R * Matrix.kronecker M (1 : CMatrix b)) * L).trace).re := by
          rw [trace_mul_kronecker_one_right_eq_partialTraceB_forPetz]
    _ = (((partialTraceB (a := a) (b := b) R * M) * L).trace).re := by
          rw [partialTraceB_mul_leftKroneckerOne]
    _ = ((L * partialTraceB (a := a) (b := b) R * M).trace).re := by
          exact congrArg Complex.re
            (Matrix.trace_mul_cycle (partialTraceB (a := a) (b := b) R) M L)

private theorem trace_mul_rankOneMatrix_mul_eq_dotProduct
    {d : Type*} [Fintype d] [DecidableEq d]
    (L R : CMatrix d) (v : d -> Complex) :
    (L * rankOneMatrix v * R).trace =
      dotProduct (star ((Matrix.conjTranspose R).mulVec v)) (L.mulVec v) := by
  simp [Matrix.trace, Matrix.mul_apply, rankOneMatrix_apply, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm,
    mul_comm]
  apply Finset.sum_congr rfl
  intro _ _
  rw [Finset.sum_comm]

private theorem trace_mul_rankOneMatrix_mul_re_eq_of_mulVec_eq
    {d : Type*} [Fintype d] [DecidableEq d]
    {L R L' R' : CMatrix d} {v : d -> Complex}
    (hL : L.mulVec v = L'.mulVec v)
    (hR : (Matrix.conjTranspose R).mulVec v = (Matrix.conjTranspose R').mulVec v) :
    ((L * rankOneMatrix v * R).trace).re =
      ((L' * rankOneMatrix v * R').trace).re := by
  rw [trace_mul_rankOneMatrix_mul_eq_dotProduct L R v]
  rw [trace_mul_rankOneMatrix_mul_eq_dotProduct L' R' v]
  rw [hL, hR]

private theorem trace_mul_rankOneMatrix_mul_re_eq_of_hermitian_mulVec_eq
    {d : Type*} [Fintype d] [DecidableEq d]
    {L R L' R' : CMatrix d} {v : d -> Complex}
    (hL : L.mulVec v = L'.mulVec v)
    (hR : R.mulVec v = R'.mulVec v)
    (hRherm : Matrix.conjTranspose R = R)
    (hR'herm : Matrix.conjTranspose R' = R') :
    ((L * rankOneMatrix v * R).trace).re =
      ((L' * rankOneMatrix v * R').trace).re := by
  exact trace_mul_rankOneMatrix_mul_re_eq_of_mulVec_eq
    (L := L) (R := R) (L' := L') (R' := R') (v := v) hL
    (by simpa [hRherm, hR'herm] using hR)

private theorem trace_rankOneMatrix_hermitian_swap_re
    {d : Type*} [Fintype d] [DecidableEq d]
    (L R : CMatrix d) (v : d -> Complex)
    (hL : Matrix.conjTranspose L = L) (hR : Matrix.conjTranspose R = R) :
    ((L * rankOneMatrix v * R).trace).re =
      ((R * rankOneMatrix v * L).trace).re := by
  have hct :
      Matrix.conjTranspose (L * rankOneMatrix v * R) =
        R * rankOneMatrix v * L := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp [hL, hR, rankOneMatrix_conjTranspose, Matrix.mul_assoc]
  calc
    ((L * rankOneMatrix v * R).trace).re =
        (star ((L * rankOneMatrix v * R).trace)).re := by simp
    _ = ((Matrix.conjTranspose (L * rankOneMatrix v * R)).trace).re := by
          rw [Matrix.trace_conjTranspose]
    _ = ((R * rankOneMatrix v * L).trace).re := by rw [hct]

private theorem kronecker_left_mulVec_apply_forPetz
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (W : CMatrix d) (v : Prod d e -> Complex) (i : d) (k : e) :
    (Matrix.kronecker W (1 : CMatrix e)).mulVec v (i, k) =
      W.mulVec (fun j => v (j, k)) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Matrix.one_apply]

private theorem kronecker_right_mulVec_apply_forPetz
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (W : CMatrix e) (v : Prod d e -> Complex) (i : d) (k : e) :
    (Matrix.kronecker (1 : CMatrix d) W).mulVec v (i, k) =
      W.mulVec (fun l => v (i, l)) k := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Matrix.one_apply]

/-- Parameter bookkeeping for the old Petz downward-duality conjugacy
`alpha + beta = 2`. -/
private theorem petzRenyiDualParam_beta_eq_two_sub
    {alpha beta : Real} (hdual : alpha + beta = 2) :
    beta = 2 - alpha := by
  linarith

/-- Under `alpha + beta = 2`, the state exponent on the `AC` side is
`beta - 1 = 1 - alpha`. -/
private theorem petzRenyiDualParam_beta_sub_one_eq_one_sub
    {alpha beta : Real} (hdual : alpha + beta = 2) :
    beta - 1 = 1 - alpha := by
  linarith

/-- Under `alpha + beta = 2`, the reference exponent on the `C` side is
`1 - beta = alpha - 1`. -/
private theorem petzRenyiDualParam_one_sub_beta_eq_sub_one
    {alpha beta : Real} (hdual : alpha + beta = 2) :
    1 - beta = alpha - 1 := by
  linarith

namespace State

/-- Entropy-level Petz duality algebra from equality of the two trace terms.

This lemma is deliberately only the final scalar algebra shell of
Tomamichel2015FiniteResources, `cond.tex:335-336`.  The mathematical content
needed upstream is the source trace bridge equating the two Petz trace terms;
once that equality is available, `alpha + beta = 2` makes the two prefactors
`1/(1-alpha)` and `1/(1-beta)` cancel. -/
theorem conditionalPetzRenyiEntropyCandidateFullReference_add_eq_zero_of_traceTerm_eq
    (rhoAB : State (Prod a b)) (sigmaB : State b) (hsigmaB : sigmaB.matrix.PosDef)
    (rhoAC : State (Prod a c)) (tauC : State c) (htauC : tauC.matrix.PosDef)
    {alpha beta : Real} (halpha_pos : 0 < alpha) (hbeta_pos : 0 < beta)
    (halpha_ne_one : alpha ≠ 1) (hbeta_ne_one : beta ≠ 1)
    (hdual : alpha + beta = 2)
    (htrace :
      rhoAB.conditionalPetzRenyiTraceTerm sigmaB alpha =
        rhoAC.conditionalPetzRenyiTraceTerm tauC beta) :
    rhoAB.conditionalPetzRenyiEntropyCandidateFullReference sigmaB hsigmaB
        alpha halpha_pos halpha_ne_one +
      rhoAC.conditionalPetzRenyiEntropyCandidateFullReference tauC htauC
        beta hbeta_pos hbeta_ne_one =
      0 := by
  let L : Real := log2 (rhoAC.conditionalPetzRenyiTraceTerm tauC beta)
  have halpha_den : 1 - alpha ≠ 0 := by
    intro h
    apply halpha_ne_one
    linarith
  have hbeta_den : 1 - beta ≠ 0 := by
    intro h
    apply hbeta_ne_one
    linarith
  have hcoeff : 1 / (1 - alpha) + 1 / (1 - beta) = 0 := by
    field_simp [halpha_den, hbeta_den]
    linarith
  dsimp [conditionalPetzRenyiEntropyCandidateFullReference]
  rw [htrace]
  change 1 / (1 - alpha) * L + 1 / (1 - beta) * L = 0
  calc
    1 / (1 - alpha) * L + 1 / (1 - beta) * L =
        (1 / (1 - alpha) + 1 / (1 - beta)) * L := by
          ring
    _ = 0 := by
          rw [hcoeff]
          ring

/-- PosDef-free entropy-level Petz duality algebra from equality of the two
trace terms.

This is the support-aware sibling of
`conditionalPetzRenyiEntropyCandidateFullReference_add_eq_zero_of_traceTerm_eq`:
the scalar algebra `1/(α-1) + 1/(β-1) = 0` (for `α + β = 2`) is independent of
the reference being full-rank, so we state it for `petzRenyiReferenceFinite`
with a `PosSemidef` identity-tensor reference.  The strict positivity of the
trace term is assumed so the result plugs into the EReal duality; the algebra
itself only uses `α + β = 2`. -/
theorem conditionalPetzRenyiReferenceFinite_add_eq_zero_of_traceTerm_eq
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    (rhoAC : State (Prod a c)) (tauC : State c)
    {alpha beta : Real} (halpha_pos : 0 < alpha) (hbeta_pos : 0 < beta)
    (halpha_ne_one : alpha ≠ 1) (hbeta_ne_one : beta ≠ 1)
    (hdual : alpha + beta = 2)
    (htrace : rhoAB.conditionalPetzRenyiTraceTerm sigmaB alpha =
      rhoAC.conditionalPetzRenyiTraceTerm tauC beta)
    (_htrace_pos : 0 < rhoAB.conditionalPetzRenyiTraceTerm sigmaB alpha) :
    rhoAB.petzRenyiReferenceFinite (identityTensorStateMatrix (a := a) sigmaB)
        (identityTensorStateMatrix_posSemidef_of_state (a := a) sigmaB)
        alpha halpha_pos halpha_ne_one +
      rhoAC.petzRenyiReferenceFinite (identityTensorStateMatrix (a := a) tauC)
        (identityTensorStateMatrix_posSemidef_of_state (a := a) tauC)
        beta hbeta_pos hbeta_ne_one =
      0 := by
  have halpha_den : alpha - 1 ≠ 0 := by
    intro h
    apply halpha_ne_one
    linarith
  have hbeta_den : beta - 1 ≠ 0 := by
    intro h
    apply hbeta_ne_one
    linarith
  have hcoeff : 1 / (alpha - 1) + 1 / (beta - 1) = 0 := by
    field_simp [halpha_den, hbeta_den]
    linarith
  have htrace_raw :
      ((CFC.rpow rhoAB.matrix alpha *
          CFC.rpow (identityTensorStateMatrix (a := a) sigmaB) (1 - alpha)).trace).re =
        ((CFC.rpow rhoAC.matrix beta *
          CFC.rpow (identityTensorStateMatrix (a := a) tauC) (1 - beta)).trace).re := by
    simpa [conditionalPetzRenyiTraceTerm] using htrace
  let L : Real := log2
    ((CFC.rpow rhoAC.matrix beta *
        CFC.rpow (identityTensorStateMatrix (a := a) tauC) (1 - beta)).trace).re
  unfold petzRenyiReferenceFinite
  rw [htrace_raw]
  change 1 / (alpha - 1) * L + 1 / (beta - 1) * L = 0
  calc 1 / (alpha - 1) * L + 1 / (beta - 1) * L =
      (1 / (alpha - 1) + 1 / (beta - 1)) * L := by ring
    _ = 0 := by rw [hcoeff]; ring

end State

namespace PureVector

def conditionalPetzRenyiABCToACBEquiv :
    Prod (Prod a b) c ≃ Prod (Prod a c) b where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv x := by rcases x with ⟨⟨_, _⟩, _⟩; rfl
  right_inv x := by rcases x with ⟨⟨_, _⟩, _⟩; rfl

private theorem conditionalPetzRenyiABCToACB_marginalAB
    (psi : PureVector (Prod (Prod a b) c)) :
    ((psi.reindex (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state).marginalAB =
      psi.state.marginalAC := by
  apply State.ext
  ext x y
  rcases x with ⟨i, k⟩
  rcases y with ⟨i', k'⟩
  simp [State.marginalAC_matrix, State.marginalAB, State.marginalA,
    partialTraceB, PureVector.reindex_state, State.reindex,
    conditionalPetzRenyiABCToACBEquiv]

private theorem conditionalPetzRenyiABCToACB_marginalBOfABC
    (psi : PureVector (Prod (Prod a b) c)) :
    ((psi.reindex (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state).marginalBOfABC =
      psi.state.marginalAC.marginalB := by
  apply State.ext
  ext k k'
  simp [State.marginalBOfABC, State.marginalAB, State.marginalA,
    State.marginalB, State.marginalAC_matrix, partialTraceA, partialTraceB,
    PureVector.reindex_state, State.reindex, conditionalPetzRenyiABCToACBEquiv]

private theorem conditionalPetzRenyiABCToACB_marginalB
    (psi : PureVector (Prod (Prod a b) c)) :
    ((psi.reindex (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state).marginalB =
      psi.state.marginalBOfABC := by
  apply State.ext
  ext k k'
  simp [State.marginalBOfABC, State.marginalAB, State.marginalA, State.marginalB,
    partialTraceA, partialTraceB, PureVector.reindex_state, State.reindex,
    conditionalPetzRenyiABCToACBEquiv, Fintype.sum_prod_type]

private theorem conditionalPetzRenyiABCToACB_marginalAC
    (psi : PureVector (Prod (Prod a b) c)) :
    ((psi.reindex (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state).marginalAC =
      psi.state.marginalAB := by
  apply State.ext
  ext x y
  rcases x with ⟨i, k⟩
  rcases y with ⟨i', k'⟩
  simp [State.marginalAC_matrix, State.marginalAB, State.marginalA,
    partialTraceB, PureVector.reindex_state, State.reindex,
    conditionalPetzRenyiABCToACBEquiv]

private theorem marginalAC_marginalB_eq_marginalB
    (psi : PureVector (Prod (Prod a b) c)) :
    psi.state.marginalAC.marginalB = psi.state.marginalB := by
  apply State.ext
  ext k k'
  simp [State.marginalAC, State.marginalB, partialTraceA, Fintype.sum_prod_type]

omit [Fintype a] [Fintype b] [Fintype c] [DecidableEq c] in
/-- Reindexing the `ABC` tensor order to `ACB` moves a C-reference operator
from `I_AB \otimes T_C` to `I_A \otimes T_C \otimes I_B`. -/
theorem conditionalPetzRenyiABCToACB_submatrix_refC
    (T : CMatrix c) :
    (Matrix.kronecker (1 : CMatrix (Prod a b)) T).submatrix
        (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c)).symm
        (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c)).symm =
      Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) T) (1 : CMatrix b) := by
  ext x y
  rcases x with ⟨⟨i, k⟩, j⟩
  rcases y with ⟨⟨i', k'⟩, j'⟩
  by_cases hi : i = i'
  · subst i'
    by_cases hj : j = j'
    · subst j'
      simp [Matrix.kronecker, conditionalPetzRenyiABCToACBEquiv]
    · simp [Matrix.kronecker, conditionalPetzRenyiABCToACBEquiv, hj]
  · simp [Matrix.kronecker, conditionalPetzRenyiABCToACBEquiv, hi]

omit [Fintype a] [Fintype b] [DecidableEq b] [Fintype c] in
private theorem conditionalPetzRenyiABCToACB_submatrix_refB
    (T : CMatrix b) :
    (Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) T) (1 : CMatrix c)).submatrix
        (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c)).symm
        (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c)).symm =
      Matrix.kronecker (1 : CMatrix (Prod a c)) T := by
  ext x y
  rcases x with ⟨⟨i, k⟩, j⟩
  rcases y with ⟨⟨i', k'⟩, j'⟩
  by_cases hi : i = i'
  · subst i'
    by_cases hk : k = k'
    · subst k'
      simp [Matrix.kronecker, conditionalPetzRenyiABCToACBEquiv]
    · simp [Matrix.kronecker, conditionalPetzRenyiABCToACBEquiv, hk]
  · simp [Matrix.kronecker, conditionalPetzRenyiABCToACBEquiv, hi]

private theorem conditionalPetzRenyiABCToACB_projectorTrace_reindex
    (psi : PureVector (Prod (Prod a b) c)) (TC : CMatrix c) (SB : CMatrix b) :
    ((Matrix.kronecker (1 : CMatrix (Prod a b)) TC *
      psi.state.matrix *
      Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) SB) (1 : CMatrix c)).trace).re =
      ((Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) TC) (1 : CMatrix b) *
        (psi.reindex
          (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state.matrix *
        Matrix.kronecker (1 : CMatrix (Prod a c)) SB).trace).re := by
  let e := conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c)
  let A : CMatrix (Prod (Prod a b) c) := Matrix.kronecker (1 : CMatrix (Prod a b)) TC
  let B : CMatrix (Prod (Prod a b) c) := psi.state.matrix
  let C : CMatrix (Prod (Prod a b) c) :=
    Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) SB) (1 : CMatrix c)
  let phi : PureVector (Prod (Prod a c) b) := psi.reindex e
  have hA :
      A.submatrix e.symm e.symm =
        Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) TC) (1 : CMatrix b) := by
    simpa [A, e] using conditionalPetzRenyiABCToACB_submatrix_refC
      (a := a) (b := b) (c := c) TC
  have hB : B.submatrix e.symm e.symm = phi.state.matrix := by
    simp [B, phi, PureVector.reindex_state, State.reindex]
  have hC :
      C.submatrix e.symm e.symm =
        Matrix.kronecker (1 : CMatrix (Prod a c)) SB := by
    simpa [C, e] using conditionalPetzRenyiABCToACB_submatrix_refB
      (a := a) (b := b) (c := c) SB
  change ((A * B * C).trace).re =
    ((Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) TC) (1 : CMatrix b) *
      phi.state.matrix *
      Matrix.kronecker (1 : CMatrix (Prod a c)) SB).trace).re
  calc
    ((A * B * C).trace).re =
        (((A * B * C).submatrix e.symm e.symm).trace).re := by
          exact congrArg Complex.re
            (State.trace_submatrix_equiv e.symm (A * B * C)).symm
    _ =
        ((A.submatrix e.symm e.symm * B.submatrix e.symm e.symm *
          C.submatrix e.symm e.symm).trace).re := by
          congr 1
          rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    _ =
        ((Matrix.kronecker (Matrix.kronecker (1 : CMatrix a) TC) (1 : CMatrix b) *
          phi.state.matrix *
          Matrix.kronecker (1 : CMatrix (Prod a c)) SB).trace).re := by
          rw [hA, hB, hC]

private theorem sum_r_s_s_reorder
    {r s : Type*} [Fintype r] [Fintype s]
    (f : r -> s -> s -> Complex) :
    (∑ x : r, ∑ y : s, ∑ z : s, f x y z) =
      ∑ z : s, ∑ y : s, ∑ x : r, f x y z := by
  calc
    (∑ x : r, ∑ y : s, ∑ z : s, f x y z) =
        ∑ x : r, ∑ z : s, ∑ y : s, f x y z := by
          apply Finset.sum_congr rfl
          intro _ _
          rw [Finset.sum_comm]
    _ = ∑ z : s, ∑ x : r, ∑ y : s, f x y z := by
          rw [Finset.sum_comm]
    _ = ∑ z : s, ∑ y : s, ∑ x : r, f x y z := by
          apply Finset.sum_congr rfl
          intro _ _
          rw [Finset.sum_comm]

private def rightSchmidtSlice
    {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (psi : PureVector (Prod r s)) (k : s) : r -> Complex :=
  fun i => ∑ x : s,
    star ((psi.state.marginalB.pos.isHermitian.eigenvectorUnitary : CMatrix s) x k) *
      psi.amp (i, x)

private theorem rightSchmidtSlice_marginalB_left_eigen_sum
    {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (psi : PureVector (Prod r s)) (k x : s) :
    (∑ y : s,
      star ((psi.state.marginalB.pos.isHermitian.eigenvectorUnitary : CMatrix s) y k) *
        psi.state.marginalB.matrix y x) =
      (psi.state.marginalB.pos.isHermitian.eigenvalues k : Complex) *
        star ((psi.state.marginalB.pos.isHermitian.eigenvectorUnitary : CMatrix s) x k) := by
  let U : Matrix.unitaryGroup s Complex :=
    psi.state.marginalB.pos.isHermitian.eigenvectorUnitary
  let lambda : Real := psi.state.marginalB.pos.isHermitian.eigenvalues k
  have hentry : ∀ i j : s,
      star (psi.state.marginalB.matrix i j) = psi.state.marginalB.matrix j i := by
    intro i j
    simpa [Matrix.conjTranspose_apply] using
      congrFun (congrFun psi.state.marginalB.pos.isHermitian.eq j) i
  have hentry_partial : ∀ i j : s,
      star (partialTraceA (a := r) (b := s) (rankOneMatrix psi.amp) i j) =
        partialTraceA (a := r) (b := s) (rankOneMatrix psi.amp) j i := by
    intro i j
    simpa [State.marginalB] using hentry i j
  have hright := psi.state.marginalB.pos.isHermitian.mulVec_eigenvectorBasis k
  have hcomp :
      (∑ y : s, psi.state.marginalB.matrix x y * (U : CMatrix s) y k) =
        (lambda : Complex) * (U : CMatrix s) x k := by
    have h := congrFun hright x
    simpa [U, lambda, Matrix.mulVec, dotProduct,
      Matrix.IsHermitian.eigenvectorUnitary_apply] using h
  have hstar := congrArg star hcomp
  simpa [U, lambda, State.marginalB, hentry_partial, Finset.mul_sum, mul_assoc,
    mul_left_comm, mul_comm] using hstar

private theorem rightSchmidtSlice_marginalA_eigen
    {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (psi : PureVector (Prod r s)) (k : s) :
    psi.state.marginalA.matrix.mulVec (rightSchmidtSlice psi k) =
      (psi.state.marginalB.pos.isHermitian.eigenvalues k : Complex) •
        rightSchmidtSlice psi k := by
  let U : Matrix.unitaryGroup s Complex :=
    psi.state.marginalB.pos.isHermitian.eigenvectorUnitary
  let lambda : Real := psi.state.marginalB.pos.isHermitian.eigenvalues k
  ext i
  have hrewrite :
      (psi.state.marginalA.matrix.mulVec (rightSchmidtSlice psi k)) i =
        ∑ x : s, psi.amp (i, x) *
          (∑ y : s, star ((U : CMatrix s) y k) * psi.state.marginalB.matrix y x) := by
    simpa [U, rightSchmidtSlice, State.marginalA, State.marginalB, partialTraceA,
      partialTraceB, Matrix.mulVec, dotProduct, rankOneMatrix_apply, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm] using
      (sum_r_s_s_reorder
        (f := fun x y z =>
          psi.amp (i, z) *
            (psi.amp (x, y) *
              (star (psi.amp (x, z)) * star ((U : CMatrix s) y k)))))
  calc
    (psi.state.marginalA.matrix.mulVec (rightSchmidtSlice psi k)) i =
        ∑ x : s, psi.amp (i, x) *
          (∑ y : s, star ((U : CMatrix s) y k) * psi.state.marginalB.matrix y x) := hrewrite
    _ = ∑ x : s, psi.amp (i, x) *
          ((lambda : Complex) * star ((U : CMatrix s) x k)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [rightSchmidtSlice_marginalB_left_eigen_sum (psi := psi) k x]
    _ = ((lambda : Complex) • rightSchmidtSlice psi k) i := by
          simp [U, lambda, rightSchmidtSlice, Finset.mul_sum, mul_assoc, mul_comm]

private theorem rightSchmidtSlice_marginalA_rpow
    {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (psi : PureVector (Prod r s)) (k : s) (p : Real) :
    (CFC.rpow psi.state.marginalA.matrix p).mulVec (rightSchmidtSlice psi k) =
      ((psi.state.marginalB.pos.isHermitian.eigenvalues k ^ p : Real) : Complex) •
        rightSchmidtSlice psi k := by
  exact cMatrix_rpow_mulVec_of_posSemidef_eigen_forPetz
    psi.state.marginalA.pos (psi.state.marginalB.pos.eigenvalues_nonneg k)
    (rightSchmidtSlice_marginalA_eigen psi k) p

private theorem rightSchmidtSlice_reconstruct
    {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (psi : PureVector (Prod r s)) (i : r) (x : s) :
    (∑ k : s,
      rightSchmidtSlice psi k i *
        (psi.state.marginalB.pos.isHermitian.eigenvectorUnitary : CMatrix s) x k) =
      psi.amp (i, x) := by
  let U : Matrix.unitaryGroup s Complex :=
    psi.state.marginalB.pos.isHermitian.eigenvectorUnitary
  have hunit : (U : CMatrix s) * star (U : CMatrix s) = 1 :=
    Unitary.coe_mul_star_self U
  calc
    (∑ k : s, rightSchmidtSlice psi k i * (U : CMatrix s) x k) =
        ∑ y : s, psi.amp (i, y) * ((U : CMatrix s) * star (U : CMatrix s)) x y := by
          simp [U, rightSchmidtSlice, Matrix.mul_apply, Finset.mul_sum, mul_left_comm,
            mul_comm]
          rw [Finset.sum_comm]
    _ = psi.amp (i, x) := by
          rw [hunit]
          simp [Matrix.one_apply]

/-- Schmidt/intertwiner movement for powers of complementary pure-state marginals.

For a pure vector on `r ⊗ s`, applying `ρ_r^p` on the left tensor factor gives
the same vector as applying `ρ_s^p` on the right tensor factor.  This is the
finite-dimensional bridge used in Tomamichel2015FiniteResources, `cond.tex`,
when source proofs move a marginal power through a pure rank-one projector. -/
theorem pureVector_rpow_marginalA_tensor_one_mulVec_eq_one_tensor_marginalB_rpow_mulVec
    {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (psi : PureVector (Prod r s)) (p : Real) :
    (Matrix.kronecker (CFC.rpow psi.state.marginalA.matrix p) (1 : CMatrix s)).mulVec
        psi.amp =
      (Matrix.kronecker (1 : CMatrix r) (CFC.rpow psi.state.marginalB.matrix p)).mulVec
        psi.amp := by
  let U : Matrix.unitaryGroup s Complex :=
    psi.state.marginalB.pos.isHermitian.eigenvectorUnitary
  let lambda : s -> Real := psi.state.marginalB.pos.isHermitian.eigenvalues
  ext z
  rcases z with ⟨i, x⟩
  have hleft :
      (Matrix.kronecker (CFC.rpow psi.state.marginalA.matrix p) (1 : CMatrix s)).mulVec
          psi.amp (i, x) =
        ∑ k : s, ((lambda k ^ p : Real) : Complex) *
          rightSchmidtSlice psi k i * (U : CMatrix s) x k := by
    rw [kronecker_left_mulVec_apply_forPetz]
    have hvec :
        (fun j : r => psi.amp (j, x)) =
          fun j : r => ∑ k : s, rightSchmidtSlice psi k j * (U : CMatrix s) x k := by
      ext j
      exact (rightSchmidtSlice_reconstruct psi j x).symm
    rw [hvec]
    calc
      (CFC.rpow psi.state.marginalA.matrix p).mulVec
          (fun j : r => ∑ k : s, rightSchmidtSlice psi k j * (U : CMatrix s) x k) i =
          ∑ k : s,
            (CFC.rpow psi.state.marginalA.matrix p).mulVec
              (rightSchmidtSlice psi k) i * (U : CMatrix s) x k := by
            simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm]
            rw [Finset.sum_comm]
      _ = ∑ k : s, ((lambda k ^ p : Real) : Complex) *
            rightSchmidtSlice psi k i * (U : CMatrix s) x k := by
            apply Finset.sum_congr rfl
            intro k _
            have hk := congrFun (rightSchmidtSlice_marginalA_rpow psi k p) i
            simpa [U, lambda, Pi.smul_apply, mul_assoc] using
              congrArg (fun z => z * (U : CMatrix s) x k) hk
  have hright :
      (Matrix.kronecker (1 : CMatrix r) (CFC.rpow psi.state.marginalB.matrix p)).mulVec
          psi.amp (i, x) =
        ∑ k : s, ((lambda k ^ p : Real) : Complex) *
          rightSchmidtSlice psi k i * (U : CMatrix s) x k := by
    rw [kronecker_right_mulVec_apply_forPetz]
    have hvec :
        (fun y : s => psi.amp (i, y)) =
          fun y : s => ∑ k : s, rightSchmidtSlice psi k i * (U : CMatrix s) y k := by
      ext y
      exact (rightSchmidtSlice_reconstruct psi i y).symm
    rw [hvec]
    calc
      (CFC.rpow psi.state.marginalB.matrix p).mulVec
          (fun y : s => ∑ k : s, rightSchmidtSlice psi k i * (U : CMatrix s) y k) x =
          ∑ k : s, rightSchmidtSlice psi k i *
            (CFC.rpow psi.state.marginalB.matrix p).mulVec
              (fun y : s => (U : CMatrix s) y k) x := by
            simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
            rw [Finset.sum_comm]
      _ = ∑ k : s, rightSchmidtSlice psi k i *
            (((lambda k ^ p : Real) : Complex) * (U : CMatrix s) x k) := by
            apply Finset.sum_congr rfl
            intro k _
            have hk := congrFun
              (cMatrix_rpow_mulVec_eigenvectorUnitary_forPetz
                psi.state.marginalB.pos k p) x
            simpa [U, lambda, Pi.smul_apply] using
              congrArg (fun z => rightSchmidtSlice psi k i * z) hk
      _ = ∑ k : s, ((lambda k ^ p : Real) : Complex) *
            rightSchmidtSlice psi k i * (U : CMatrix s) x k := by
            apply Finset.sum_congr rfl
            intro k _
            ring
  rw [hleft, hright]

private theorem pureVector_projectorTrace_move_left_rpow
    {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (psi : PureVector (Prod r s)) (K : CMatrix (Prod r s)) (p : Real) :
    ((Matrix.kronecker (CFC.rpow psi.state.marginalA.matrix p) (1 : CMatrix s) *
      psi.state.matrix * K).trace).re =
      ((Matrix.kronecker (1 : CMatrix r) (CFC.rpow psi.state.marginalB.matrix p) *
        psi.state.matrix * K).trace).re := by
  simpa [PureVector.state_matrix] using
    trace_mul_rankOneMatrix_mul_re_eq_of_mulVec_eq
      (L := Matrix.kronecker (CFC.rpow psi.state.marginalA.matrix p) (1 : CMatrix s))
      (R := K)
      (L' := Matrix.kronecker (1 : CMatrix r) (CFC.rpow psi.state.marginalB.matrix p))
      (R' := K)
      (v := psi.amp)
      (pureVector_rpow_marginalA_tensor_one_mulVec_eq_one_tensor_marginalB_rpow_mulVec
        psi p)
      rfl

private theorem pureVector_projectorTrace_move_right_rpow
    {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (psi : PureVector (Prod r s)) (K : CMatrix (Prod r s)) (p : Real) :
    ((K * psi.state.matrix *
      Matrix.kronecker (1 : CMatrix r) (CFC.rpow psi.state.marginalB.matrix p)).trace).re =
      ((K * psi.state.matrix *
        Matrix.kronecker (CFC.rpow psi.state.marginalA.matrix p) (1 : CMatrix s)).trace).re := by
  let R : CMatrix (Prod r s) :=
    Matrix.kronecker (1 : CMatrix r) (CFC.rpow psi.state.marginalB.matrix p)
  let R' : CMatrix (Prod r s) :=
    Matrix.kronecker (CFC.rpow psi.state.marginalA.matrix p) (1 : CMatrix s)
  have hR : R.mulVec psi.amp = R'.mulVec psi.amp :=
    (pureVector_rpow_marginalA_tensor_one_mulVec_eq_one_tensor_marginalB_rpow_mulVec
      psi p).symm
  have hRherm : Matrix.conjTranspose R = R := by
    have hpsd : R.PosSemidef := by
      dsimp [R]
      exact Matrix.PosSemidef.one.kronecker
        (cMatrix_rpow_posSemidef (A := psi.state.marginalB.matrix) (s := p)
          psi.state.marginalB.pos)
    exact hpsd.isHermitian.eq
  have hR'herm : Matrix.conjTranspose R' = R' := by
    have hpsd : R'.PosSemidef := by
      dsimp [R']
      exact
        (cMatrix_rpow_posSemidef (A := psi.state.marginalA.matrix) (s := p)
          psi.state.marginalA.pos).kronecker Matrix.PosSemidef.one
    exact hpsd.isHermitian.eq
  simpa [PureVector.state_matrix, R, R'] using
    trace_mul_rankOneMatrix_mul_re_eq_of_hermitian_mulVec_eq
      (L := K) (R := R) (L' := K) (R' := R') (v := psi.amp)
      rfl hR hRherm hR'herm

/-- Middle source trace bridge for downward Petz duality.

This is the formal version of the nontrivial middle equality in
Tomamichel2015FiniteResources, `cond.tex:331-334`:
`Tr(rho_AB^(alpha-1) |psi><psi| rho_B^(1-alpha)) =
  Tr(rho_AC^(1-alpha) |psi><psi| rho_C^(alpha-1))`, with the right-hand side
written in the `ACB` ordering used by the `A|C` Petz trace term.

The proof follows the source route: Schmidt/intertwiner movement across the
pure projector, finite basis relabeling from `ABC` to `ACB`, the corresponding
movement on the `AC|B` split, and a Hermitian trace swap to align with the
existing AC-side projector trace convention. -/
theorem conditionalPetzRenyi_projectorTrace_marginalAB_eq_acbProjectorTrace_dualParam
    (psi : PureVector (Prod (Prod a b) c)) {alpha : Real} :
    ((Matrix.kronecker
        (CFC.rpow psi.state.marginalAB.matrix (alpha - 1))
        (1 : CMatrix c) *
      psi.state.matrix *
      Matrix.kronecker
        (Matrix.kronecker (1 : CMatrix a)
          (CFC.rpow psi.state.marginalBOfABC.matrix (1 - alpha)))
        (1 : CMatrix c)).trace).re =
      ((Matrix.kronecker
          (CFC.rpow psi.state.marginalAC.matrix (1 - alpha))
          (1 : CMatrix b) *
        (psi.reindex
          (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state.matrix *
        Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalAC.marginalB.matrix (alpha - 1)))
          (1 : CMatrix b)).trace).re := by
  let e := conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c)
  let phi : PureVector (Prod (Prod a c) b) := psi.reindex e
  let p : Real := alpha - 1
  let q : Real := 1 - alpha
  let KBABC : CMatrix (Prod (Prod a b) c) :=
    Matrix.kronecker
      (Matrix.kronecker (1 : CMatrix a)
        (CFC.rpow psi.state.marginalBOfABC.matrix q))
      (1 : CMatrix c)
  let KCABC₀ : CMatrix (Prod (Prod a b) c) :=
    Matrix.kronecker (1 : CMatrix (Prod a b))
      (CFC.rpow psi.state.marginalB.matrix p)
  let KACB₀ : CMatrix (Prod (Prod a c) b) :=
    Matrix.kronecker
      (Matrix.kronecker (1 : CMatrix a)
        (CFC.rpow psi.state.marginalB.matrix p))
      (1 : CMatrix b)
  let KACB : CMatrix (Prod (Prod a c) b) :=
    Matrix.kronecker
      (Matrix.kronecker (1 : CMatrix a)
        (CFC.rpow psi.state.marginalAC.marginalB.matrix p))
      (1 : CMatrix b)
  let RBACB : CMatrix (Prod (Prod a c) b) :=
    Matrix.kronecker (1 : CMatrix (Prod a c))
      (CFC.rpow psi.state.marginalBOfABC.matrix q)
  let RACACB : CMatrix (Prod (Prod a c) b) :=
    Matrix.kronecker (CFC.rpow psi.state.marginalAC.matrix q) (1 : CMatrix b)
  have hC : psi.state.marginalAC.marginalB = psi.state.marginalB :=
    marginalAC_marginalB_eq_marginalB psi
  have hKACB : KACB₀ = KACB := by
    simpa [KACB₀, KACB] using
      congrArg
        (fun τ : State c =>
          Matrix.kronecker
            (Matrix.kronecker (1 : CMatrix a) (CFC.rpow τ.matrix p))
            (1 : CMatrix b))
        hC.symm
  have hleft :
      ((Matrix.kronecker
          (CFC.rpow psi.state.marginalAB.matrix p)
          (1 : CMatrix c) *
        psi.state.matrix * KBABC).trace).re =
        ((KCABC₀ * psi.state.matrix * KBABC).trace).re := by
    have h :=
      pureVector_projectorTrace_move_left_rpow
        (r := Prod a b) (s := c) psi KBABC p
    simpa [KCABC₀, State.marginalAB, State.marginalA] using h
  have hreindex :
      ((KCABC₀ * psi.state.matrix * KBABC).trace).re =
        ((KACB₀ * phi.state.matrix * RBACB).trace).re := by
    have h :=
      conditionalPetzRenyiABCToACB_projectorTrace_reindex
        (a := a) (b := b) (c := c) psi
        (CFC.rpow psi.state.marginalB.matrix p)
        (CFC.rpow psi.state.marginalBOfABC.matrix q)
    simpa [KCABC₀, KBABC, KACB₀, RBACB, phi, e] using h
  have hphiA : phi.state.marginalA = psi.state.marginalAC := by
    simpa [phi, e, State.marginalAB, State.marginalA] using
      conditionalPetzRenyiABCToACB_marginalAB (a := a) (b := b) (c := c) psi
  have hphiB : phi.state.marginalB = psi.state.marginalBOfABC := by
    simpa [phi, e] using
      conditionalPetzRenyiABCToACB_marginalB (a := a) (b := b) (c := c) psi
  have hright :
      ((KACB₀ * phi.state.matrix * RBACB).trace).re =
        ((KACB₀ * phi.state.matrix * RACACB).trace).re := by
    have h :=
      pureVector_projectorTrace_move_right_rpow
        (r := Prod a c) (s := b) phi KACB₀ q
    simpa [RBACB, RACACB, hphiA, hphiB] using h
  have hKherm : Matrix.conjTranspose KACB = KACB := by
    have hpsd : KACB.PosSemidef := by
      dsimp [KACB]
      exact
        (Matrix.PosSemidef.one.kronecker
          (cMatrix_rpow_posSemidef
            (A := psi.state.marginalAC.marginalB.matrix) (s := p)
            psi.state.marginalAC.marginalB.pos)).kronecker
          Matrix.PosSemidef.one
    exact hpsd.isHermitian.eq
  have hRherm : Matrix.conjTranspose RACACB = RACACB := by
    have hpsd : RACACB.PosSemidef := by
      dsimp [RACACB]
      exact
        (cMatrix_rpow_posSemidef
          (A := psi.state.marginalAC.matrix) (s := q)
          psi.state.marginalAC.pos).kronecker Matrix.PosSemidef.one
    exact hpsd.isHermitian.eq
  have hswap :
      ((KACB * phi.state.matrix * RACACB).trace).re =
        ((RACACB * phi.state.matrix * KACB).trace).re := by
    simpa [PureVector.state_matrix] using
      trace_rankOneMatrix_hermitian_swap_re KACB RACACB phi.amp hKherm hRherm
  calc
    ((Matrix.kronecker
        (CFC.rpow psi.state.marginalAB.matrix (alpha - 1))
        (1 : CMatrix c) *
      psi.state.matrix *
      Matrix.kronecker
        (Matrix.kronecker (1 : CMatrix a)
          (CFC.rpow psi.state.marginalBOfABC.matrix (1 - alpha)))
        (1 : CMatrix c)).trace).re =
        ((KCABC₀ * psi.state.matrix * KBABC).trace).re := by
          simpa [p, q, KBABC] using hleft
    _ = ((KACB₀ * phi.state.matrix * RBACB).trace).re := hreindex
    _ = ((KACB₀ * phi.state.matrix * RACACB).trace).re := hright
    _ = ((KACB * phi.state.matrix * RACACB).trace).re := by rw [hKACB]
    _ = ((RACACB * phi.state.matrix * KACB).trace).re := hswap
    _ =
        ((Matrix.kronecker
          (CFC.rpow psi.state.marginalAC.matrix (1 - alpha))
          (1 : CMatrix b) *
        (psi.reindex
          (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state.matrix *
        Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalAC.marginalB.matrix (alpha - 1)))
          (1 : CMatrix b)).trace).re := by
          simp [phi, e, p, q, KACB, RACACB]

/-- First source trace rewrite for downward Petz duality.

For a normalized pure state `ψ_ABC`, this is the formal version of the first
line in Tomamichel2015FiniteResources, `cond.tex:329-331`:
`Tr(ρ_AB^α ρ_B^(1-α)) =
  Tr(ρ_AB^(α-1) |ψ⟩⟨ψ|_ABC ρ_B^(1-α))`.

The assumption `α ≠ 0` is exactly the nonzero-exponent side condition needed
by the current singular-PSD exponent law when combining
`ρ_AB^(α-1) ρ_AB = ρ_AB^α`. -/
theorem conditionalPetzRenyiTraceTerm_marginalAB_eq_projectorTrace
    (psi : PureVector (Prod (Prod a b) c)) {alpha : Real}
    (halpha_ne_zero : alpha ≠ 0) :
    psi.state.marginalAB.conditionalPetzRenyiTraceTerm
        psi.state.marginalBOfABC alpha =
      ((Matrix.kronecker
          (CFC.rpow psi.state.marginalAB.matrix (alpha - 1))
          (1 : CMatrix c) *
        psi.state.matrix *
        Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalBOfABC.matrix (1 - alpha)))
          (1 : CMatrix c)).trace).re := by
  let rhoAB : State (Prod a b) := psi.state.marginalAB
  let rhoB : State b := psi.state.marginalBOfABC
  let L : CMatrix (Prod a b) := CFC.rpow rhoAB.matrix (alpha - 1)
  let M : CMatrix (Prod a b) :=
    Matrix.kronecker (1 : CMatrix a) (CFC.rpow rhoB.matrix (1 - alpha))
  have hpow_one : CFC.rpow rhoAB.matrix (1 : Real) = rhoAB.matrix :=
    CFC.rpow_one rhoAB.matrix (ha := Matrix.nonneg_iff_posSemidef.mpr rhoAB.pos)
  have hpq : (alpha - 1) + 1 ≠ 0 := by
    intro hzero
    apply halpha_ne_zero
    linarith
  have hpow : L * rhoAB.matrix = CFC.rpow rhoAB.matrix alpha := by
    calc
      L * rhoAB.matrix =
          CFC.rpow rhoAB.matrix (alpha - 1) * CFC.rpow rhoAB.matrix (1 : Real) := by
            rw [hpow_one]
      _ = CFC.rpow rhoAB.matrix ((alpha - 1) + 1) := by
            exact cMatrix_rpow_add_psd_forPetz rhoAB.pos hpq
      _ = CFC.rpow rhoAB.matrix alpha := by
            congr 1
            ring
  have hside :
      CFC.rpow (State.identityTensorStateMatrix (a := a) rhoB) (1 - alpha) = M := by
    simpa [M, State.identityTensorStateMatrix] using
      State.cMatrix_rpow_identity_kronecker (a := a) rhoB.matrix rhoB.pos (1 - alpha)
  dsimp [State.conditionalPetzRenyiTraceTerm]
  change
    ((CFC.rpow rhoAB.matrix alpha *
      CFC.rpow (State.identityTensorStateMatrix (a := a) rhoB) (1 - alpha)).trace).re =
      ((Matrix.kronecker L (1 : CMatrix c) * psi.state.matrix *
        Matrix.kronecker M (1 : CMatrix c)).trace).re
  rw [hside]
  calc
    ((CFC.rpow rhoAB.matrix alpha * M).trace).re =
        ((L * rhoAB.matrix * M).trace).re := by
          rw [← hpow]
    _ =
        ((Matrix.kronecker L (1 : CMatrix c) * psi.state.matrix *
          Matrix.kronecker M (1 : CMatrix c)).trace).re := by
          have htrace :=
            trace_left_right_kronecker_one_eq_partialTraceB
              (a := Prod a b) (b := c) psi.state.matrix L M
          simpa [rhoAB, State.marginalAB, State.marginalA] using htrace.symm

/-- Boundary trace rewrite at `alpha = 0` for downward Petz duality.

This is the `alpha = 0` analogue of
`conditionalPetzRenyiTraceTerm_marginalAB_eq_projectorTrace`: the source trace
term collapses to the support-projection trace
`Tr(Π_{supp rho_AB} (I_A ⊗ rho_B))`, and the single step of the interior proof
that fails at `alpha = 0` (the exponent law `rho_AB^(alpha-1) rho_AB =
rho_AB^alpha`, which needs `alpha ≠ 0`) is replaced by the range-projection
bookend `cMatrix_rpow_neg_one_mul_self_eq_rangeProjection`.  The remaining
trace-lifting step is `alpha`-independent and is reused verbatim. -/
theorem conditionalPetzRenyiTraceTermZero_marginalAB_eq_projectorTrace
    (psi : PureVector (Prod (Prod a b) c)) :
    ((Matrix.rangeProjection psi.state.marginalAB.matrix *
      State.identityTensorStateMatrix (a := a) psi.state.marginalBOfABC).trace).re =
      ((Matrix.kronecker
          (CFC.rpow psi.state.marginalAB.matrix (0 - 1))
          (1 : CMatrix c) *
        psi.state.matrix *
        Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalBOfABC.matrix (1 - 0)))
          (1 : CMatrix c)).trace).re := by
  have hbook : Matrix.rangeProjection psi.state.marginalAB.matrix =
      CFC.rpow psi.state.marginalAB.matrix (0 - 1) * psi.state.marginalAB.matrix := by
    have h :=
      cMatrix_rpow_neg_one_mul_self_eq_rangeProjection psi.state.marginalAB.pos
    rw [zero_sub]
    exact h.symm
  have hT : State.identityTensorStateMatrix (a := a) psi.state.marginalBOfABC =
      CFC.rpow (State.identityTensorStateMatrix (a := a) psi.state.marginalBOfABC)
        (1 - 0) := by
    rw [sub_zero]
    exact (CFC.rpow_one _ (ha := Matrix.nonneg_iff_posSemidef.mpr
      (State.identityTensorStateMatrix_posSemidef_of_state (a := a)
        psi.state.marginalBOfABC))).symm
  have hside :
      CFC.rpow (State.identityTensorStateMatrix (a := a) psi.state.marginalBOfABC)
          (1 - 0) =
        Matrix.kronecker (1 : CMatrix a)
          (CFC.rpow psi.state.marginalBOfABC.matrix (1 - 0)) := by
    simpa [State.identityTensorStateMatrix] using
      State.cMatrix_rpow_identity_kronecker (a := a)
        psi.state.marginalBOfABC.matrix psi.state.marginalBOfABC.pos (1 - 0)
  rw [hbook]
  conv_lhs => rw [hT, hside]
  have htrace :=
    trace_left_right_kronecker_one_eq_partialTraceB
      (a := Prod a b) (b := c) psi.state.matrix
      (CFC.rpow psi.state.marginalAB.matrix (0 - 1))
      (Matrix.kronecker (1 : CMatrix a)
        (CFC.rpow psi.state.marginalBOfABC.matrix (1 - 0)))
  simpa [State.marginalAB, State.marginalA] using htrace.symm

/-- AC-side source trace rewrite for downward Petz duality.

For the reindexed `AC:B` presentation of the same pure vector, this is the
formal version of the final source trace contraction in
Tomamichel2015FiniteResources, `cond.tex:334-335`, read from the Petz trace
term side:
`Tr(ρ_AC^(β-1) |ψ⟩⟨ψ|_ACB ρ_C^(1-β)) =
  Tr(ρ_AC^β ρ_C^(1-β))`.

The theorem is stated with the left side as the Petz trace term so it can be
used directly when closing the `H_β(A|C)` half of Proposition `pr:dual-old`.
The ACB ordering is only a basis relabeling of the original `ABC` pure state;
the declaration names keep the original namespaces unchanged. -/
theorem conditionalPetzRenyiTraceTerm_marginalAC_eq_acbProjectorTrace
    (psi : PureVector (Prod (Prod a b) c)) {beta : Real}
    (hbeta_ne_zero : beta ≠ 0) :
    psi.state.marginalAC.conditionalPetzRenyiTraceTerm
        psi.state.marginalAC.marginalB beta =
      ((Matrix.kronecker
          (CFC.rpow psi.state.marginalAC.matrix (beta - 1))
          (1 : CMatrix b) *
        (psi.reindex
          (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state.matrix *
        Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalAC.marginalB.matrix (1 - beta)))
          (1 : CMatrix b)).trace).re := by
  let e := conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c)
  let phi : PureVector (Prod (Prod a c) b) := psi.reindex e
  have hsource :=
    conditionalPetzRenyiTraceTerm_marginalAB_eq_projectorTrace
      (a := a) (b := c) (c := b) phi hbeta_ne_zero
  have hAB : phi.state.marginalAB = psi.state.marginalAC := by
    simpa [phi, e] using conditionalPetzRenyiABCToACB_marginalAB (a := a) (b := b)
      (c := c) psi
  have hB : phi.state.marginalBOfABC = psi.state.marginalAC.marginalB := by
    simpa [phi, e] using
      conditionalPetzRenyiABCToACB_marginalBOfABC (a := a) (b := b) (c := c) psi
  simpa [phi, hAB, hB] using hsource

/-- AC-side projector trace rewrite with the source dual parameter
`alpha + beta = 2` already substituted.

This is the same trace contraction as
`conditionalPetzRenyiTraceTerm_marginalAC_eq_acbProjectorTrace`, but the
exponents are displayed in the form used in Tomamichel2015FiniteResources,
`cond.tex:332-335`: `rho_AC^(1-alpha)` and `rho_C^(alpha-1)`. -/
theorem conditionalPetzRenyiTraceTerm_marginalAC_eq_acbProjectorTrace_dualParam
    (psi : PureVector (Prod (Prod a b) c)) {alpha beta : Real}
    (hbeta_ne_zero : beta ≠ 0) (hdual : alpha + beta = 2) :
    psi.state.marginalAC.conditionalPetzRenyiTraceTerm
        psi.state.marginalAC.marginalB beta =
      ((Matrix.kronecker
          (CFC.rpow psi.state.marginalAC.matrix (1 - alpha))
          (1 : CMatrix b) *
        (psi.reindex
          (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state.matrix *
        Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalAC.marginalB.matrix (alpha - 1)))
          (1 : CMatrix b)).trace).re := by
  have hbase :=
    conditionalPetzRenyiTraceTerm_marginalAC_eq_acbProjectorTrace
      (a := a) (b := b) (c := c) psi hbeta_ne_zero
  have hstate := petzRenyiDualParam_beta_sub_one_eq_one_sub hdual
  have href := petzRenyiDualParam_one_sub_beta_eq_sub_one hdual
  simpa [hstate, href] using hbase

/-- Equality of the two old-Petz trace terms in Proposition `pr:dual-old`.

This combines the first source trace contraction, the Schmidt/intertwiner
middle bridge, and the AC-side final contraction.  The hypotheses `alpha ≠ 0`
and `beta ≠ 0` are the singular-PSD exponent side conditions required by the
current finite-dimensional CFC power API when contracting a projector trace
back to `Tr(rho^alpha sigma^(1-alpha))`. -/
theorem conditionalPetzRenyiTraceTerm_marginalAB_eq_marginalAC_dualParam
    (psi : PureVector (Prod (Prod a b) c)) {alpha beta : Real}
    (halpha_ne_zero : alpha ≠ 0) (hbeta_ne_zero : beta ≠ 0)
    (hdual : alpha + beta = 2) :
    psi.state.marginalAB.conditionalPetzRenyiTraceTerm
        psi.state.marginalBOfABC alpha =
      psi.state.marginalAC.conditionalPetzRenyiTraceTerm
        psi.state.marginalAC.marginalB beta := by
  have hAB :=
    conditionalPetzRenyiTraceTerm_marginalAB_eq_projectorTrace
      (a := a) (b := b) (c := c) psi halpha_ne_zero
  have hbridge :=
    conditionalPetzRenyi_projectorTrace_marginalAB_eq_acbProjectorTrace_dualParam
      (a := a) (b := b) (c := c) (alpha := alpha) psi
  have hAC :=
    conditionalPetzRenyiTraceTerm_marginalAC_eq_acbProjectorTrace_dualParam
      (a := a) (b := b) (c := c) psi hbeta_ne_zero hdual
  calc
    psi.state.marginalAB.conditionalPetzRenyiTraceTerm
        psi.state.marginalBOfABC alpha =
        ((Matrix.kronecker
          (CFC.rpow psi.state.marginalAB.matrix (alpha - 1))
          (1 : CMatrix c) *
        psi.state.matrix *
        Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalBOfABC.matrix (1 - alpha)))
          (1 : CMatrix c)).trace).re := hAB
    _ =
        ((Matrix.kronecker
          (CFC.rpow psi.state.marginalAC.matrix (1 - alpha))
          (1 : CMatrix b) *
        (psi.reindex
          (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c))).state.matrix *
        Matrix.kronecker
          (Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow psi.state.marginalAC.marginalB.matrix (alpha - 1)))
          (1 : CMatrix b)).trace).re := hbridge
    _ =
        psi.state.marginalAC.conditionalPetzRenyiTraceTerm
          psi.state.marginalAC.marginalB beta := hAC.symm

/-- Normalized non-endpoint old-Petz downward duality.

This is the current Lean realization of Tomamichel2015FiniteResources,
`cond.tex`, Proposition `pr:dual-old`, lines 317--336, under the local API's
non-endpoint hypotheses.  The theorem assumes full-rank side marginals because
`conditionalPetzRenyiDown` is currently defined through the full-reference
candidate.  It does not claim endpoint conventions at `alpha = 0` or
`alpha = 1`, nor any subnormalized-state extension. -/
theorem conditionalPetzRenyiDown_duality_source
    (psi : PureVector (Prod (Prod a b) c))
    (hB : psi.state.marginalBOfABC.matrix.PosDef)
    (hC : psi.state.marginalAC.marginalB.matrix.PosDef)
    {alpha beta : Real}
    (halpha_pos : 0 < alpha) (hbeta_pos : 0 < beta)
    (_halpha_le_two : alpha ≤ 2) (_hbeta_le_two : beta ≤ 2)
    (halpha_ne_one : alpha ≠ 1) (hbeta_ne_one : beta ≠ 1)
    (hdual : alpha + beta = 2) :
    psi.state.marginalAB.conditionalPetzRenyiDown
        hB alpha halpha_pos halpha_ne_one +
      psi.state.marginalAC.conditionalPetzRenyiDown
        hC beta hbeta_pos hbeta_ne_one =
      0 := by
  have htrace :=
    conditionalPetzRenyiTraceTerm_marginalAB_eq_marginalAC_dualParam
      (a := a) (b := b) (c := c) psi
      (ne_of_gt halpha_pos) (ne_of_gt hbeta_pos) hdual
  have hscalar :=
    State.conditionalPetzRenyiEntropyCandidateFullReference_add_eq_zero_of_traceTerm_eq
      (a := a) (b := b) (c := c)
      psi.state.marginalAB psi.state.marginalBOfABC hB
      psi.state.marginalAC psi.state.marginalAC.marginalB hC
      halpha_pos hbeta_pos halpha_ne_one hbeta_ne_one hdual htrace
  simpa [State.conditionalPetzRenyiDown] using hscalar

/-- Interior singular-marginal downward Petz Renyi duality.

For a pure tripartite state `psi` and interior dual parameters
`alpha, beta ∈ (0, 2) \ {1}` with `alpha + beta = 2`, the two downward Petz
conditional Renyi entropies sum to zero in `EReal`, with NO `PosDef` marginal
hypotheses.  This is the interior part of Tomamichel2015FiniteResources,
`cond.tex`, Proposition `pr:dual-old`; singular marginals are handled by the
support-aware kernel `State.conditionalPetzRenyiDownGeneralE` rather than by a
full-rank assumption.  Endpoint conventions at `alpha = 0` and `alpha = 1` are
not claimed here. -/
theorem conditionalPetzRenyiDownGeneralE_duality_interior
    (psi : PureVector (Prod (Prod a b) c))
    {alpha beta : Real}
    (halpha_pos : 0 < alpha) (hbeta_pos : 0 < beta)
    (halpha_ne_one : alpha ≠ 1) (hbeta_ne_one : beta ≠ 1)
    (hdual : alpha + beta = 2) :
    psi.state.marginalAB.conditionalPetzRenyiDownGeneralE alpha halpha_pos halpha_ne_one +
      psi.state.marginalAC.conditionalPetzRenyiDownGeneralE beta hbeta_pos hbeta_ne_one =
      0 := by
  -- The AB side's canonical reference marginal is the B marginal of `psi`.
  -- The bridge is phrased with `marginalBOfABC`; rewrite it to `marginalAB.marginalB`.
  have hbridge :=
    conditionalPetzRenyiTraceTerm_marginalAB_eq_marginalAC_dualParam
      (a := a) (b := b) (c := c) psi
      (ne_of_gt halpha_pos) (ne_of_gt hbeta_pos) hdual
  rw [State.marginalBOfABC_eq] at hbridge
  -- The AB trace term `Tr(rho_AB^alpha (I ⊗ rho_B)^(1-alpha))` is strictly
  -- positive for every interior `alpha`, since `rho_AB` is supported on
  -- `I_A ⊗ rho_B`.  This supplies the `≠ 0` side condition of the EReal coe.
  have hMne : CFC.rpow psi.state.marginalAB.matrix alpha ≠ 0 := by
    have hpow_pos :
        0 < psdTracePower psi.state.marginalAB.matrix psi.state.marginalAB.pos
          (p := alpha) :=
      psdTracePower_pos_of_ne_zero psi.state.marginalAB.matrix
        psi.state.marginalAB.pos psi.state.marginalAB.matrix_ne_zero
    intro hzero
    have htrace_zero :
        psdTracePower psi.state.marginalAB.matrix psi.state.marginalAB.pos
          (p := alpha) = 0 := by
      simpa [psdTracePower] using
        congrArg (fun X : CMatrix (a × b) => X.trace.re) hzero
    linarith
  have hposAB :
      0 < psi.state.marginalAB.conditionalPetzRenyiTraceTerm
        psi.state.marginalAB.marginalB alpha := by
    exact
      trace_mul_cMatrix_rpow_pos_of_support
        (cMatrix_rpow_posSemidef (A := psi.state.marginalAB.matrix) (s := alpha)
          psi.state.marginalAB.pos)
        (State.identityTensorStateMatrix_posSemidef_of_state (a := a)
          psi.state.marginalAB.marginalB)
        hMne
        ((cMatrix_rpow_supports_self psi.state.marginalAB.pos halpha_pos).trans
          (State.matrix_supports_identityTensor_marginalB psi.state.marginalAB))
        (1 - alpha)
  -- Real-valued scalar cancellation across the two finite references.
  have hcancel :=
    State.conditionalPetzRenyiReferenceFinite_add_eq_zero_of_traceTerm_eq
      (a := a) (b := b) (c := c)
      psi.state.marginalAB psi.state.marginalAB.marginalB
      psi.state.marginalAC psi.state.marginalAC.marginalB
      halpha_pos hbeta_pos halpha_ne_one hbeta_ne_one hdual hbridge hposAB
  -- Reduce both support-aware wrappers to coes of the finite reference.
  rw [State.conditionalPetzRenyiDownGeneralE_eq_coe
        psi.state.marginalAB alpha halpha_pos halpha_ne_one,
    State.conditionalPetzRenyiDownGeneralE_eq_coe
        psi.state.marginalAC beta hbeta_pos hbeta_ne_one]
  -- Close in `EReal`: both sides are coes of finite reals, so the negations
  -- fold into a single coe and the real cancellation `hcancel` finishes.
  have hkey :
      (- psi.state.marginalAB.petzRenyiReferenceFinite
          (State.identityTensorStateMatrix (a := a) psi.state.marginalAB.marginalB)
          (State.identityTensorStateMatrix_posSemidef_of_state (a := a)
            psi.state.marginalAB.marginalB)
          alpha halpha_pos halpha_ne_one +
        - psi.state.marginalAC.petzRenyiReferenceFinite
          (State.identityTensorStateMatrix (a := a) psi.state.marginalAC.marginalB)
          (State.identityTensorStateMatrix_posSemidef_of_state (a := a)
            psi.state.marginalAC.marginalB)
          beta hbeta_pos hbeta_ne_one : Real) = 0 := by linarith
  simp only [← EReal.coe_neg, ← EReal.coe_add]
  exact_mod_cast hkey

end PureVector

namespace State

/-- Open-interval downward Petz Renyi entropy, extending the support-aware
interior wrapper to the Umegaki point `alpha = 1`.

At `alpha = 1` the value is the ordinary conditional von Neumann entropy
`rho.conditionalEntropy` embedded into `EReal`; for `alpha ≠ 1` it coincides
with the support-aware `conditionalPetzRenyiDownGeneralE`.  The parameter is
restricted to the open interval `(0, 2)`; the boundary points `alpha = 0` and
`alpha = 2` are intentionally NOT covered here, since they require the
`H^down_0` / support-projection endpoint layer and are deferred to a later PR.
No `PosDef` hypothesis is required on the reference marginal. -/
noncomputable def conditionalPetzRenyiDownExtended
    (rho : State (Prod a b)) (alpha : Real)
    (halpha_pos : 0 < alpha) (_halpha_lt_two : alpha < 2) : EReal := by
  classical
  exact
    if halpha_ne_one : alpha = 1 then (rho.conditionalEntropy : EReal)
    else rho.conditionalPetzRenyiDownGeneralE alpha halpha_pos halpha_ne_one

/-- Reduction of the extended wrapper to the support-aware interior wrapper
away from `alpha = 1` (so the `alpha ≠ 1` arm of the open-interval duality can
dispatch to the PR1 interior theorem). -/
theorem conditionalPetzRenyiDownExtended_of_ne_one
    (rho : State (Prod a b)) (alpha : Real)
    (halpha_pos : 0 < alpha) (halpha_lt_two : alpha < 2)
    (halpha_ne_one : alpha ≠ 1) :
    rho.conditionalPetzRenyiDownExtended alpha halpha_pos halpha_lt_two =
      rho.conditionalPetzRenyiDownGeneralE alpha halpha_pos halpha_ne_one := by
  classical
  unfold conditionalPetzRenyiDownExtended
  rw [dif_neg halpha_ne_one]

end State

namespace PureVector

/-- Open-interval downward Petz Renyi duality for a pure tripartite state.

For `alpha, beta` in the open interval `(0, 2)` with `alpha + beta = 2`, the two
downward Petz conditional Renyi entropies sum to zero in `EReal`, with NO
`PosDef` marginal hypotheses.  This closes the open interval `(0, 2)`:
  * the interior `(0, 2) \ {1}` is PR1's
    `conditionalPetzRenyiDownGeneralE_duality_interior`;
  * the Umegaki point `(alpha, beta) = (1, 1)` reduces to the pure-state
    conditional-entropy duality
    `State.PureVector.conditionalEntropy_marginalAB_eq_neg_marginalAC`.

The boundary points `alpha = 0` / `alpha = 2` (i.e. `(0, 2)` and `(2, 0)`) are
intentionally deferred to PR3, pending the `H^down_0` plus support-projection
endpoint layer; they are NOT claimed here. -/
theorem conditionalPetzRenyiDownExtended_duality
    (psi : PureVector (Prod (Prod a b) c)) {alpha beta : Real}
    (halpha_pos : 0 < alpha) (halpha_lt_two : alpha < 2)
    (hbeta_pos : 0 < beta) (hbeta_lt_two : beta < 2)
    (hdual : alpha + beta = 2) :
    psi.state.marginalAB.conditionalPetzRenyiDownExtended alpha halpha_pos halpha_lt_two +
      psi.state.marginalAC.conditionalPetzRenyiDownExtended beta hbeta_pos hbeta_lt_two = 0 := by
  -- `beta`'s bounds follow from `alpha ∈ (0, 2)` and `alpha + beta = 2`; they
  -- are taken as explicit hypotheses only because the type of this theorem
  -- must already supply them to the extended wrapper on the `AC` side.
  classical
  by_cases ha : alpha = 1
  · -- Umegaki point: `alpha = beta = 1`. Both extended wrappers reduce to the
    -- conditional von Neumann entropy, whose pure-state duality
    -- `H(A|B) = -H(A|C)` is already `conditionalEntropy_marginalAB_eq_neg_marginalAC`.
    have hbeta_eq_one : beta = 1 := by linarith
    unfold State.conditionalPetzRenyiDownExtended
    rw [dif_pos ha, dif_pos hbeta_eq_one]
    have hdual_ent : psi.state.marginalAB.conditionalEntropy =
        -psi.state.marginalAC.conditionalEntropy :=
      State.PureVector.conditionalEntropy_marginalAB_eq_neg_marginalAC psi
    have hkey : psi.state.marginalAB.conditionalEntropy +
        psi.state.marginalAC.conditionalEntropy = 0 := by linarith
    simp only [← EReal.coe_add]
    exact_mod_cast hkey
  · -- Interior point `alpha ≠ 1` (hence `beta ≠ 1`): reduce both extended
    -- wrappers to `conditionalPetzRenyiDownGeneralE` and dispatch to PR1's
    -- interior duality, which needs no `PosDef` hypothesis.
    have hbeta_ne_one : beta ≠ 1 := by
      intro hbe; apply ha; linarith
    rw [psi.state.marginalAB.conditionalPetzRenyiDownExtended_of_ne_one alpha
          halpha_pos halpha_lt_two ha,
        psi.state.marginalAC.conditionalPetzRenyiDownExtended_of_ne_one beta
          hbeta_pos hbeta_lt_two hbeta_ne_one]
    exact conditionalPetzRenyiDownGeneralE_duality_interior psi
      halpha_pos hbeta_pos ha hbeta_ne_one hdual

end PureVector

namespace State

/-- Boundary value of the downward Petz conditional Renyi entropy at
`alpha = 0`, in the source-faithful support-projection form
`H^down_0(A|B) = log2 Tr(Π_{supp rho_AB} (id_A ⊗ rho_B))`.

This is the `alpha = 0` endpoint of the downward Petz family: the signed
prefactor `-1/(alpha - 1)` evaluates to `1`, and the `rho_AB^(alpha-1)` factor
of the interior trace term is replaced by the projection onto the support of
`rho_AB` (equivalently, by `rho_AB^(-1) rho_AB`, via
`cMatrix_rpow_neg_one_mul_self_eq_rangeProjection`).  No `PosDef` hypothesis
on the marginal is required. -/
noncomputable def conditionalPetzRenyiDownZero (rho : State (Prod a b)) : Real :=
  log2 ((Matrix.rangeProjection rho.matrix *
    identityTensorStateMatrix (a := a) rho.marginalB).trace.re)

/-- Closed-interval downward Petz Renyi entropy for `alpha ∈ [0, 2]`.

At the boundary points this is the support-projection value
`conditionalPetzRenyiDownZero` (`alpha = 0`) respectively the support-aware
`conditionalPetzRenyiDownGeneralE 2` (`alpha = 2`); on the open interval
`(0, 2)` it agrees with `conditionalPetzRenyiDownExtended` (Umegaki point
included).  No `PosDef` hypothesis is required anywhere. -/
noncomputable def conditionalPetzRenyiDownClosed
    (rho : State (Prod a b)) (alpha : Real) (h0 : 0 ≤ alpha) (h2 : alpha ≤ 2) :
    EReal := by
  classical
  exact
    if h00 : alpha = 0 then (rho.conditionalPetzRenyiDownZero : EReal)
    else if h02 : alpha = 2 then
      rho.conditionalPetzRenyiDownGeneralE 2 (by norm_num) (by norm_num)
    else rho.conditionalPetzRenyiDownExtended alpha
      (lt_of_le_of_ne h0 (Ne.symm h00)) (lt_of_le_of_ne h2 h02)

/-- Reduction of the closed-interval wrapper at the boundary `alpha = 0`. -/
theorem conditionalPetzRenyiDownClosed_of_zero
    (rho : State (Prod a b)) (h0 : 0 ≤ (0 : Real)) (h2 : (0 : Real) ≤ 2) :
    rho.conditionalPetzRenyiDownClosed 0 h0 h2 =
      (rho.conditionalPetzRenyiDownZero : EReal) := by
  classical
  unfold conditionalPetzRenyiDownClosed
  rw [dif_pos rfl]

/-- Reduction of the closed-interval wrapper at the boundary `alpha = 2`. -/
theorem conditionalPetzRenyiDownClosed_of_two
    (rho : State (Prod a b)) (h0 : 0 ≤ (2 : Real)) (h2 : (2 : Real) ≤ 2) :
    rho.conditionalPetzRenyiDownClosed 2 h0 h2 =
      rho.conditionalPetzRenyiDownGeneralE 2 (by norm_num) (by norm_num) := by
  classical
  unfold conditionalPetzRenyiDownClosed
  rw [dif_neg (by norm_num : (2 : Real) ≠ 0), dif_pos rfl]

/-- Reduction of the closed-interval wrapper to the open-interval wrapper
away from the two boundary points. -/
theorem conditionalPetzRenyiDownClosed_of_ne_zero_ne_two
    (rho : State (Prod a b)) (alpha : Real) (h0 : 0 ≤ alpha) (h2 : alpha ≤ 2)
    (h00 : alpha ≠ 0) (h02 : alpha ≠ 2) :
    rho.conditionalPetzRenyiDownClosed alpha h0 h2 =
      rho.conditionalPetzRenyiDownExtended alpha
        (lt_of_le_of_ne h0 (Ne.symm h00)) (lt_of_le_of_ne h2 h02) := by
  classical
  unfold conditionalPetzRenyiDownClosed
  rw [dif_neg h00, dif_neg h02]

end State

namespace PureVector

/-- Boundary downward Petz duality at `(alpha, beta) = (0, 2)`: the
support-projection value on the `AB` side plus the `alpha = 2` Petz value on
the `AC` side sum to zero, with NO `PosDef` hypotheses.

The proof chains the `alpha = 0` boundary trace rewrite
(`conditionalPetzRenyiTraceTermZero_marginalAB_eq_projectorTrace`, built on
the range-projection bookend), the Schmidt/intertwiner middle bridge reused
verbatim at `alpha = 0`, and the AC-side contraction at `beta = 2`; the scalar
entropy identity then closes because the two trace terms are equal as reals,
so no positivity side condition is needed for the `log2` cancellation. -/
theorem conditionalPetzRenyiDownZero_add_generalE_two_eq_zero
    (psi : PureVector (Prod (Prod a b) c)) :
    (psi.state.marginalAB.conditionalPetzRenyiDownZero : EReal) +
      psi.state.marginalAC.conditionalPetzRenyiDownGeneralE 2
        (by norm_num) (by norm_num) = 0 := by
  have h2pos : (0 : Real) < 2 := by norm_num
  have h2ne1 : (2 : Real) ≠ 1 := by norm_num
  -- Chain the three trace steps at `(alpha, beta) = (0, 2)`: boundary
  -- rewrite, middle bridge, AC-side contraction.
  have hQ0 :=
    conditionalPetzRenyiTraceTermZero_marginalAB_eq_projectorTrace
      (a := a) (b := b) (c := c) psi
  have hbridge :=
    conditionalPetzRenyi_projectorTrace_marginalAB_eq_acbProjectorTrace_dualParam
      (a := a) (b := b) (c := c) (alpha := 0) psi
  have hAC :=
    conditionalPetzRenyiTraceTerm_marginalAC_eq_acbProjectorTrace_dualParam
      (a := a) (b := b) (c := c) psi
      (show (2 : Real) ≠ 0 by norm_num) (show (0 : Real) + 2 = 2 by norm_num)
  have hQ := hQ0.trans (hbridge.trans hAC.symm)
  rw [State.marginalBOfABC_eq] at hQ
  -- The boundary value is `log2` of the shared trace term.
  have hzero : psi.state.marginalAB.conditionalPetzRenyiDownZero =
      log2 (psi.state.marginalAC.conditionalPetzRenyiTraceTerm
        psi.state.marginalAC.marginalB 2) := by
    unfold State.conditionalPetzRenyiDownZero
    rw [hQ]
  -- The `alpha = 2` Petz value is `-log2` of the same trace term.
  have hfin : psi.state.marginalAC.petzRenyiReferenceFinite
      (State.identityTensorStateMatrix (a := a) psi.state.marginalAC.marginalB)
      (State.identityTensorStateMatrix_posSemidef_of_state (a := a)
        psi.state.marginalAC.marginalB) 2 h2pos h2ne1 =
      log2 (psi.state.marginalAC.conditionalPetzRenyiTraceTerm
        psi.state.marginalAC.marginalB 2) := by
    show (1 / (2 - 1 : Real)) *
        log2 (psi.state.marginalAC.conditionalPetzRenyiTraceTerm
          psi.state.marginalAC.marginalB 2) =
      log2 (psi.state.marginalAC.conditionalPetzRenyiTraceTerm
        psi.state.marginalAC.marginalB 2)
    have hone : (1 : Real) / (2 - 1) = 1 := by norm_num
    rw [hone, one_mul]
  have hgen : psi.state.marginalAC.conditionalPetzRenyiDownGeneralE 2 h2pos h2ne1 =
      (-(log2 (psi.state.marginalAC.conditionalPetzRenyiTraceTerm
        psi.state.marginalAC.marginalB 2)) : EReal) := by
    rw [State.conditionalPetzRenyiDownGeneralE_eq_coe
      psi.state.marginalAC 2 h2pos h2ne1, hfin]
  -- Close in `EReal`: both sides are coes of finite reals.
  change (psi.state.marginalAB.conditionalPetzRenyiDownZero : EReal) +
    psi.state.marginalAC.conditionalPetzRenyiDownGeneralE 2 h2pos h2ne1 = 0
  rw [hgen, hzero]
  have hkey : (log2 (psi.state.marginalAC.conditionalPetzRenyiTraceTerm
        psi.state.marginalAC.marginalB 2) +
      -(log2 (psi.state.marginalAC.conditionalPetzRenyiTraceTerm
        psi.state.marginalAC.marginalB 2)) : Real) = 0 :=
    add_neg_cancel _
  simp only [← EReal.coe_neg, ← EReal.coe_add]
  exact_mod_cast hkey

/-- Boundary downward Petz duality at `(alpha, beta) = (2, 0)`, obtained from
the `(0, 2)` boundary by reindexing the purifying system from `ABC` to `ACB`.
No `PosDef` hypotheses. -/
theorem conditionalPetzRenyiDownGeneralETwo_add_zero_eq_zero
    (psi : PureVector (Prod (Prod a b) c)) :
    psi.state.marginalAB.conditionalPetzRenyiDownGeneralE 2
        (by norm_num) (by norm_num) +
      (psi.state.marginalAC.conditionalPetzRenyiDownZero : EReal) = 0 := by
  have h := conditionalPetzRenyiDownZero_add_generalE_two_eq_zero
    (psi.reindex (conditionalPetzRenyiABCToACBEquiv (a := a) (b := b) (c := c)))
  rw [conditionalPetzRenyiABCToACB_marginalAB psi,
    conditionalPetzRenyiABCToACB_marginalAC psi] at h
  rw [add_comm]
  exact h

/-- Closed-interval old-Petz downward duality for a pure tripartite state.

For `alpha, beta ∈ Set.Icc 0 2` with `alpha + beta = 2`, the two downward
Petz conditional Renyi entropies of the complementary marginals sum to zero
in `EReal`, with NO `PosDef` marginal hypotheses.  This is the closed-interval
form of Tomamichel2015FiniteResources, `cond.tex`, Proposition `pr:dual-old`:
the interior `(0, 2)` is PR2's `conditionalPetzRenyiDownExtended_duality`
(with the Umegaki point `alpha = 1` included), and the boundary points
`(0, 2)` and `(2, 0)` are closed by the support-projection bookend
`cMatrix_rpow_neg_one_mul_self_eq_rangeProjection` via
`conditionalPetzRenyiDownZero_add_generalE_two_eq_zero` and its reindexed
sibling. -/
theorem conditionalPetzRenyiDown_duality
    (psi : PureVector (Prod (Prod a b) c)) {alpha beta : Real}
    (halpha : alpha ∈ Set.Icc (0 : Real) 2) (hbeta : beta ∈ Set.Icc (0 : Real) 2)
    (hdual : alpha + beta = 2) :
    psi.state.marginalAB.conditionalPetzRenyiDownClosed alpha halpha.1 halpha.2 +
      psi.state.marginalAC.conditionalPetzRenyiDownClosed beta hbeta.1 hbeta.2 = 0 := by
  classical
  by_cases h00 : alpha = 0
  · -- Boundary `(alpha, beta) = (0, 2)`.
    have hbeta2 : beta = 2 := by linarith
    subst h00
    subst hbeta2
    rw [State.conditionalPetzRenyiDownClosed_of_zero
          psi.state.marginalAB halpha.1 halpha.2,
        State.conditionalPetzRenyiDownClosed_of_two
          psi.state.marginalAC hbeta.1 hbeta.2]
    exact conditionalPetzRenyiDownZero_add_generalE_two_eq_zero psi
  · by_cases h02 : alpha = 2
    · -- Boundary `(alpha, beta) = (2, 0)`.
      have hbeta0 : beta = 0 := by linarith
      subst h02
      subst hbeta0
      rw [State.conditionalPetzRenyiDownClosed_of_two
            psi.state.marginalAB halpha.1 halpha.2,
          State.conditionalPetzRenyiDownClosed_of_zero
            psi.state.marginalAC hbeta.1 hbeta.2]
      exact conditionalPetzRenyiDownGeneralETwo_add_zero_eq_zero psi
    · -- Interior `alpha ∈ (0, 2)`: reduce both closed wrappers to the
      -- open-interval wrapper and dispatch to PR2.
      have halpha_pos : 0 < alpha := lt_of_le_of_ne halpha.1 (Ne.symm h00)
      have halpha_lt_two : alpha < 2 := lt_of_le_of_ne halpha.2 h02
      have hb0 : beta ≠ 0 := by
        intro hbe
        apply h02
        linarith
      have hb2 : beta ≠ 2 := by
        intro hbe
        apply h00
        linarith
      have hbeta_pos : 0 < beta := lt_of_le_of_ne hbeta.1 (Ne.symm hb0)
      have hbeta_lt_two : beta < 2 := lt_of_le_of_ne hbeta.2 hb2
      rw [State.conditionalPetzRenyiDownClosed_of_ne_zero_ne_two
            psi.state.marginalAB alpha halpha.1 halpha.2 h00 h02,
          State.conditionalPetzRenyiDownClosed_of_ne_zero_ne_two
            psi.state.marginalAC beta hbeta.1 hbeta.2 hb0 hb2]
      exact conditionalPetzRenyiDownExtended_duality psi
        halpha_pos halpha_lt_two hbeta_pos hbeta_lt_two hdual

end PureVector

end

end QIT
