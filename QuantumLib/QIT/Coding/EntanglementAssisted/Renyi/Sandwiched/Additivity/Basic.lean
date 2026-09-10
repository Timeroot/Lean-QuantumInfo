/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Basic
public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Petz.Additivity
public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.CBNorm
public import QuantumLib.QIT.Information.Renyi.ConditionalRenyiMinimax
public import QuantumLib.QIT.Information.Renyi.SandwichedRenyiOptimizedUSC
public import QuantumLib.QIT.HypothesisTesting.DPI
public import QuantumLib.QIT.States.Purification.Canonical
public import QuantumLib.QIT.Util.Matrix
public import QuantumLib.QIT.Util.Order.EReal

/-!
# Basic support and order lemmas for sandwiched EA additivity

This module is part of the Khatri--Wilde sandwiched-Renyi additivity proof
spine for entanglement-assisted classical communication.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Pointwise

namespace QIT

universe u1 v1 u2 v2

noncomputable section

/-- If a positive-definite matrix is supported by a positive-semidefinite
reference, the reference is positive definite.  This local closure lemma is
used to rule out singular side references in the high-`alpha` KW support
convention. -/
theorem Matrix.Supports.posDef_right_of_left_posDef
    {a : Type u1} [Fintype a] [DecidableEq a]
    {M N : CMatrix a} (hM : M.PosDef) (hN : N.PosSemidef)
    (hSupport : Matrix.Supports M N) : N.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hN.isHermitian ?_
  intro x hx
  have hnonneg : 0 ≤ star x ⬝ᵥ N.mulVec x :=
    hN.dotProduct_mulVec_nonneg x
  have hne : star x ⬝ᵥ N.mulVec x ≠ 0 := by
    intro hzero
    have hNzero : N.mulVec x = 0 := (hN.dotProduct_mulVec_zero_iff x).mp hzero
    have hMzero : M.mulVec x = 0 := hSupport x hNzero
    have hMquad_zero : star x ⬝ᵥ M.mulVec x = 0 := by
      rw [hMzero, dotProduct_zero]
    have hpos : 0 < star x ⬝ᵥ M.mulVec x :=
      hM.dotProduct_mulVec_pos hx
    rw [hMquad_zero] at hpos
    exact (lt_irrefl (0 : ℂ)) hpos
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- If a PSD matrix is supported by a nonnegative diagonal reference, then its
diagonal entries vanish wherever the reference diagonal vanishes. -/
theorem Matrix.Supports.diagonal_zero_of_posSemidef
    {a : Type u1} [Fintype a] [DecidableEq a]
    {M : CMatrix a} (_hM : M.PosSemidef) {d : a → ℝ} (_hd : ∀ i, 0 ≤ d i)
    (hSupport :
      Matrix.Supports M (Matrix.diagonal fun i => ((d i : ℝ) : ℂ) : CMatrix a))
    {i : a} (hdi : d i = 0) :
    M i i = 0 := by
  let e : a → ℂ := Pi.single i 1
  have hDe : (Matrix.diagonal fun j => ((d j : ℝ) : ℂ) : CMatrix a).mulVec e = 0 := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [e, Matrix.mulVec, dotProduct, Matrix.diagonal, hdi]
    · simp [e, Matrix.mulVec, dotProduct, Matrix.diagonal, hji]
  have hMe : M.mulVec e = 0 := hSupport e hDe
  have hii := congrFun hMe i
  have hsum : (∑ x, M i x * e x) = 0 := by
    simpa [Matrix.mulVec, dotProduct] using hii
  have hsingle : (∑ x, M i x * e x) = M i i := by
    rw [Finset.sum_eq_single i]
    · simp [e]
    · intro j _hj hji
      simp [e, Pi.single_eq_of_ne hji]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rwa [hsingle] at hsum

/-- PSD support domination is stable under Kronecker products.

This support-closure lemma is the matrix-level support convention needed for
the KW product-state additivity proof: if each factor state is supported by its
factor reference, then the product state is supported by the product reference. -/
theorem Matrix.Supports.kronecker_of_posSemidef
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    {rhoA refA : CMatrix a} {rhoB refB : CMatrix b}
    (hRhoA : rhoA.PosSemidef) (hRefA : refA.PosSemidef)
    (hRhoB : rhoB.PosSemidef) (hRefB : refB.PosSemidef)
    (h1 : Matrix.Supports rhoA refA) (h2 : Matrix.Supports rhoB refB) :
    Matrix.Supports (Matrix.kronecker rhoA rhoB) (Matrix.kronecker refA refB) := by
  classical
  let U1 : Matrix.unitaryGroup a ℂ := star hRefA.isHermitian.eigenvectorUnitary
  let U2 : Matrix.unitaryGroup b ℂ := star hRefB.isHermitian.eigenvectorUnitary
  let U : Matrix.unitaryGroup (a × b) ℂ :=
    ⟨Matrix.kronecker (U1 : CMatrix a) (U2 : CMatrix b),
      kronecker_mem_unitaryGroup U1 U2⟩
  let d1 : a → ℝ := fun i => hRefA.isHermitian.eigenvalues i
  let d2 : b → ℝ := fun j => hRefB.isHermitian.eigenvalues j
  let d : a × b → ℝ := fun x => d1 x.1 * d2 x.2
  let rhoA' : CMatrix a := (U1 : CMatrix a) * rhoA * star (U1 : CMatrix a)
  let rhoB' : CMatrix b := (U2 : CMatrix b) * rhoB * star (U2 : CMatrix b)
  let D1 : CMatrix a := Matrix.diagonal fun i => ((d1 i : ℝ) : ℂ)
  let D2 : CMatrix b := Matrix.diagonal fun j => ((d2 j : ℝ) : ℂ)
  have hd1_nonneg : ∀ i, 0 ≤ d1 i := by
    intro i
    exact hRefA.eigenvalues_nonneg i
  have hd2_nonneg : ∀ j, 0 ≤ d2 j := by
    intro j
    exact hRefB.eigenvalues_nonneg j
  have hd_nonneg : ∀ x, 0 ≤ d x := by
    intro x
    exact mul_nonneg (hd1_nonneg x.1) (hd2_nonneg x.2)
  have hRefA_diag :
      (U1 : CMatrix a) * refA * star (U1 : CMatrix a) = D1 := by
    let V1 : Matrix.unitaryGroup a ℂ := hRefA.isHermitian.eigenvectorUnitary
    have hspec := hRefA.isHermitian.spectral_theorem
    have hRefA_spec :
        refA = (V1 : CMatrix a) * D1 * star (V1 : CMatrix a) := by
      simpa [V1, D1, d1, Matrix.IsHermitian.spectral_theorem,
        Unitary.conjStarAlgAut_apply, Function.comp_def]
        using hspec
    have hdiagV : star (V1 : CMatrix a) * refA * (V1 : CMatrix a) = D1 := by
      calc
        star (V1 : CMatrix a) * refA * (V1 : CMatrix a) =
            star (V1 : CMatrix a) * ((V1 : CMatrix a) * D1 * star (V1 : CMatrix a)) *
              (V1 : CMatrix a) := by rw [hRefA_spec]
        _ = (star (V1 : CMatrix a) * (V1 : CMatrix a)) * D1 *
              (star (V1 : CMatrix a) * (V1 : CMatrix a)) := by
              noncomm_ring
        _ = D1 := by
              rw [Unitary.coe_star_mul_self]
              simp
    simpa [U1, V1] using hdiagV
  have hRefB_diag :
      (U2 : CMatrix b) * refB * star (U2 : CMatrix b) = D2 := by
    let V2 : Matrix.unitaryGroup b ℂ := hRefB.isHermitian.eigenvectorUnitary
    have hspec := hRefB.isHermitian.spectral_theorem
    have hRefB_spec :
        refB = (V2 : CMatrix b) * D2 * star (V2 : CMatrix b) := by
      simpa [V2, D2, d2, Matrix.IsHermitian.spectral_theorem,
        Unitary.conjStarAlgAut_apply, Function.comp_def]
        using hspec
    have hdiagV : star (V2 : CMatrix b) * refB * (V2 : CMatrix b) = D2 := by
      calc
        star (V2 : CMatrix b) * refB * (V2 : CMatrix b) =
            star (V2 : CMatrix b) * ((V2 : CMatrix b) * D2 * star (V2 : CMatrix b)) *
              (V2 : CMatrix b) := by rw [hRefB_spec]
        _ = (star (V2 : CMatrix b) * (V2 : CMatrix b)) * D2 *
              (star (V2 : CMatrix b) * (V2 : CMatrix b)) := by
              noncomm_ring
        _ = D2 := by
              rw [Unitary.coe_star_mul_self]
              simp
    simpa [U2, V2] using hdiagV
  have h1diag : Matrix.Supports rhoA' D1 := by
    simpa [rhoA', D1, hRefA_diag] using h1.unitary_conj U1
  have h2diag : Matrix.Supports rhoB' D2 := by
    simpa [rhoB', D2, hRefB_diag] using h2.unitary_conj U2
  have hRhoA' : rhoA'.PosSemidef := by
    simpa [rhoA', Matrix.star_eq_conjTranspose] using
      hRhoA.conjTranspose_mul_mul_same (star (U1 : CMatrix a))
  have hRhoB' : rhoB'.PosSemidef := by
    simpa [rhoB', Matrix.star_eq_conjTranspose] using
      hRhoB.conjTranspose_mul_mul_same (star (U2 : CMatrix b))
  have hdiagZero1 : ∀ i, d1 i = 0 → rhoA' i i = 0 := by
    intro i hi
    exact Matrix.Supports.diagonal_zero_of_posSemidef hRhoA' hd1_nonneg h1diag hi
  have hdiagZero2 : ∀ j, d2 j = 0 → rhoB' j j = 0 := by
    intro j hj
    exact Matrix.Supports.diagonal_zero_of_posSemidef hRhoB' hd2_nonneg h2diag hj
  have hprodDiag :
      Matrix.Supports (Matrix.kronecker rhoA' rhoB')
        (Matrix.diagonal fun x : a × b => ((d x : ℝ) : ℂ) : CMatrix (a × b)) := by
    refine Matrix.Supports.of_posSemidef_diagonal (hRhoA'.kronecker hRhoB') hd_nonneg ?_
    intro x hx
    rcases x with ⟨i, j⟩
    have hcases : d1 i = 0 ∨ d2 j = 0 := mul_eq_zero.mp hx
    rcases hcases with hi | hj
    · simp [Matrix.kroneckerMap_apply, hdiagZero1 i hi]
    · simp [Matrix.kroneckerMap_apply, hdiagZero2 j hj]
  have hprodDiag' :
      Matrix.Supports
        ((U : CMatrix (a × b)) * Matrix.kronecker rhoA rhoB * star (U : CMatrix (a × b)))
        ((U : CMatrix (a × b)) * Matrix.kronecker refA refB * star (U : CMatrix (a × b))) := by
    have hleft :
        (U : CMatrix (a × b)) * Matrix.kronecker rhoA rhoB * star (U : CMatrix (a × b)) =
          Matrix.kronecker rhoA' rhoB' := by
      simp [U, rhoA', rhoB', Matrix.conjTranspose_kronecker, Matrix.star_eq_conjTranspose,
        Matrix.mul_kronecker_mul, Matrix.mul_assoc]
    have hright :
        (U : CMatrix (a × b)) * Matrix.kronecker refA refB * star (U : CMatrix (a × b)) =
          Matrix.diagonal fun x : a × b => ((d x : ℝ) : ℂ) := by
      calc
        (U : CMatrix (a × b)) * Matrix.kronecker refA refB * star (U : CMatrix (a × b)) =
            Matrix.kronecker ((U1 : CMatrix a) * refA * star (U1 : CMatrix a))
              ((U2 : CMatrix b) * refB * star (U2 : CMatrix b)) := by
              simp [U, Matrix.conjTranspose_kronecker, Matrix.star_eq_conjTranspose,
                Matrix.mul_kronecker_mul, Matrix.mul_assoc]
        _ = Matrix.kronecker D1 D2 := by
              rw [hRefA_diag, hRefB_diag]
        _ = Matrix.diagonal fun x : a × b => ((d x : ℝ) : ℂ) := by
              simpa [D1, D2, d] using
                (Matrix.diagonal_kronecker_diagonal
                  (fun i : a => ((d1 i : ℝ) : ℂ))
                  (fun j : b => ((d2 j : ℝ) : ℂ)))
    rw [hleft, hright]
    exact hprodDiag
  intro v hv
  let Umat : CMatrix (a × b) := (U : CMatrix (a × b))
  let rhoProd : CMatrix (a × b) := Matrix.kronecker rhoA rhoB
  let refProd : CMatrix (a × b) := Matrix.kronecker refA refB
  have hstarU_U : star Umat * Umat = 1 := by
    change star (U : CMatrix (a × b)) * (U : CMatrix (a × b)) = 1
    exact Unitary.coe_star_mul_self U
  have hmatRef : (Umat * refProd * star Umat) * Umat = Umat * refProd := by
    calc
      (Umat * refProd * star Umat) * Umat =
          Umat * refProd * (star Umat * Umat) := by
          noncomm_ring
      _ = Umat * refProd := by
          rw [hstarU_U]
          simp
  have hmatRho : (Umat * rhoProd * star Umat) * Umat = Umat * rhoProd := by
    calc
      (Umat * rhoProd * star Umat) * Umat =
          Umat * rhoProd * (star Umat * Umat) := by
          noncomm_ring
      _ = Umat * rhoProd := by
          rw [hstarU_U]
          simp
  have hRefv : refProd.mulVec v = 0 := by
    simpa [refProd] using hv
  have hkill :
      (Umat * refProd * star Umat).mulVec (Umat.mulVec v) = 0 := by
    calc
      (Umat * refProd * star Umat).mulVec (Umat.mulVec v) =
          ((Umat * refProd * star Umat) * Umat).mulVec v := by
          rw [Matrix.mulVec_mulVec]
      _ = (Umat * refProd).mulVec v := by rw [hmatRef]
      _ = Umat.mulVec (refProd.mulVec v) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by
          rw [hRefv]
          simp
  have hconj :
      (Umat * rhoProd * star Umat).mulVec (Umat.mulVec v) = 0 :=
    hprodDiag' (Umat.mulVec v) hkill
  have hURho :
      Umat.mulVec (rhoProd.mulVec v) = 0 := by
    calc
      Umat.mulVec (rhoProd.mulVec v) =
          (Umat * rhoProd).mulVec v := by rw [Matrix.mulVec_mulVec]
      _ = ((Umat * rhoProd * star Umat) * Umat).mulVec v := by rw [hmatRho]
      _ = (Umat * rhoProd * star Umat).mulVec (Umat.mulVec v) := by
          rw [Matrix.mulVec_mulVec]
      _ = 0 := hconj
  have hback := congrArg (fun w => (star Umat).mulVec w) hURho
  have hback_zero :
      (star Umat).mulVec (Umat.mulVec (rhoProd.mulVec v)) = 0 := by
    simpa using hback
  have hconj_back :
      (((star Umat * Umat) * rhoProd).mulVec v) = 0 := by
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using hback_zero
  have hidRho : (star Umat * Umat) * rhoProd = rhoProd := by
    rw [hstarU_U]
    simp
  calc
    rhoProd.mulVec v = ((star Umat * Umat) * rhoProd).mulVec v := by
        rw [hidRho]
    _ = 0 := hconj_back

/-- Support domination is preserved by relabelling finite bases. -/
theorem Matrix.Supports.reindex
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    {M N : CMatrix a} (h : Matrix.Supports M N) (e : a ≃ b) :
    Matrix.Supports (M.submatrix e.symm e.symm) (N.submatrix e.symm e.symm) := by
  intro v hv
  let w : a → ℂ := fun i => v (e i)
  have hNw : N.mulVec w = 0 := by
    ext i
    have hi := congrFun hv (e i)
    simp [Matrix.mulVec, dotProduct] at hi ⊢
    have hsum :
        (∑ x : a, N i x * v (e x)) =
          ∑ y : b, N i (e.symm y) * v y := by
      exact Fintype.sum_equiv e
        (fun x : a => N i x * v (e x))
        (fun y : b => N i (e.symm y) * v y)
        (by intro x; simp)
    rw [hsum]
    exact hi
  have hMw : M.mulVec w = 0 := h w hNw
  ext j
  have hj := congrFun hMw (e.symm j)
  simp [w, Matrix.mulVec, dotProduct] at hj ⊢
  have hsum :
      (∑ x : b, M (e.symm j) (e.symm x) * v x) =
        ∑ y : a, M (e.symm j) y * v (e y) := by
    exact Fintype.sum_equiv e.symm
      (fun x : b => M (e.symm j) (e.symm x) * v x)
      (fun y : a => M (e.symm j) y * v (e y))
      (by intro x; simp)
  rw [hsum]
  exact hj

/-- Spectral multiplication rule for PSD matrix powers under the repository's
support convention.

This is deliberately scalar-parametric: callers supply the pointwise
nonnegative-real identity, so singular eigenvalues are handled explicitly
instead of silently adding a positive-definiteness hypothesis. -/
theorem cMatrix_rpow_mul_rpow_of_posSemidef_scalar
    {a : Type u1} [Fintype a] [DecidableEq a]
    {A : CMatrix a} (hA : A.PosSemidef) {r s t : ℝ}
    (hscalar : ∀ x : ℝ, 0 ≤ x → x ^ r * x ^ s = x ^ t) :
    CFC.rpow A r * CFC.rpow A s = CFC.rpow A t := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hA.isHermitian.eigenvectorUnitary
  let d : a → ℝ := hA.isHermitian.eigenvalues
  let Dr : CMatrix a := Matrix.diagonal fun i => ((d i ^ r : ℝ) : ℂ)
  let Ds : CMatrix a := Matrix.diagonal fun i => ((d i ^ s : ℝ) : ℂ)
  let Dt : CMatrix a := Matrix.diagonal fun i => ((d i ^ t : ℝ) : ℂ)
  have hd : ∀ i, 0 ≤ d i := fun i => hA.eigenvalues_nonneg i
  have hUstar : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
    Unitary.coe_star_mul_self U
  have hr :
      CFC.rpow A r = (U : CMatrix a) * Dr * star (U : CMatrix a) := by
    simpa [U, d, Dr] using cMatrix_rpow_eq_eigenbasis_diagonal hA r
  have hs :
      CFC.rpow A s = (U : CMatrix a) * Ds * star (U : CMatrix a) := by
    simpa [U, d, Ds] using cMatrix_rpow_eq_eigenbasis_diagonal hA s
  have ht :
      CFC.rpow A t = (U : CMatrix a) * Dt * star (U : CMatrix a) := by
    simpa [U, d, Dt] using cMatrix_rpow_eq_eigenbasis_diagonal hA t
  have hdiag : Dr * Ds = Dt := by
    dsimp [Dr, Ds, Dt]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      rw [← Complex.ofReal_mul, hscalar (d i) (hd i)]
    · simp [Matrix.diagonal, hij]
  rw [hr, hs, ht]
  calc
    ((U : CMatrix a) * Dr * star (U : CMatrix a)) *
        ((U : CMatrix a) * Ds * star (U : CMatrix a)) =
        (U : CMatrix a) * (Dr * Ds) * star (U : CMatrix a) := by
          calc
            ((U : CMatrix a) * Dr * star (U : CMatrix a)) *
                ((U : CMatrix a) * Ds * star (U : CMatrix a)) =
                (U : CMatrix a) * Dr * (star (U : CMatrix a) * (U : CMatrix a)) *
                  Ds * star (U : CMatrix a) := by
                  noncomm_ring
            _ = (U : CMatrix a) * Dr * 1 * Ds * star (U : CMatrix a) := by
                  rw [hUstar]
            _ = (U : CMatrix a) * (Dr * Ds) * star (U : CMatrix a) := by
                  noncomm_ring
    _ = (U : CMatrix a) * Dt * star (U : CMatrix a) := by
          rw [hdiag]

private theorem real_sandwiched_left_rpow_mul_sqrt
    {x alpha : ℝ} (hx : 0 ≤ x) (halpha : 1 < alpha) :
    x ^ ((1 - alpha) / (2 * alpha)) * x ^ (1 / 2 : ℝ) =
      x ^ (1 / (2 * alpha)) := by
  by_cases hx0 : x = 0
  · subst x
    have hs_ne : (1 - alpha) / (2 * alpha) ≠ 0 := by
      have hnum : 1 - alpha ≠ 0 := by linarith
      have hden : 2 * alpha ≠ 0 := by nlinarith [lt_trans zero_lt_one halpha]
      exact div_ne_zero hnum hden
    have ht_ne : (1 / (2 * alpha) : ℝ) ≠ 0 := by
      have hden : 2 * alpha ≠ 0 := by nlinarith [lt_trans zero_lt_one halpha]
      exact one_div_ne_zero hden
    have ht_ne' : (alpha⁻¹ * 2⁻¹ : ℝ) ≠ 0 := by
      have ha : alpha ≠ 0 := by linarith [lt_trans zero_lt_one halpha]
      exact mul_ne_zero (inv_ne_zero ha) (by norm_num)
    simp [Real.zero_rpow hs_ne, Real.zero_rpow ht_ne']
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [← Real.rpow_add hxpos]
    congr 1
    field_simp [ne_of_gt (lt_trans zero_lt_one halpha)]
    ring

/-- PSD version of the KW exponent cancellation
`tau^((1-alpha)/(2 alpha)) * tau^(1/2) = tau^(1/(2 alpha))`.

The positive-definite proof uses `CFC.rpow_add`.  This support-aware variant
keeps the same source equality for singular input states, using the local
spectral convention `0^s = 0`. -/
theorem cMatrix_sandwiched_left_rpow_mul_sqrt
    {a : Type u1} [Fintype a] [DecidableEq a]
    {A : CMatrix a} (hA : A.PosSemidef) {alpha : ℝ} (halpha : 1 < alpha) :
    CFC.rpow A ((1 - alpha) / (2 * alpha)) * CFC.rpow A (1 / 2 : ℝ) =
      CFC.rpow A (1 / (2 * alpha)) :=
  cMatrix_rpow_mul_rpow_of_posSemidef_scalar hA
    (fun _ hx => real_sandwiched_left_rpow_mul_sqrt hx halpha)

/-- Right-handed version of `cMatrix_sandwiched_left_rpow_mul_sqrt`.

Both factors are functions of the same PSD matrix, so the spectral proof is
identical with the scalar factors reversed. -/
theorem cMatrix_sqrt_mul_sandwiched_left_rpow
    {a : Type u1} [Fintype a] [DecidableEq a]
    {A : CMatrix a} (hA : A.PosSemidef) {alpha : ℝ} (halpha : 1 < alpha) :
  CFC.rpow A (1 / 2 : ℝ) * CFC.rpow A ((1 - alpha) / (2 * alpha)) =
      CFC.rpow A (1 / (2 * alpha)) := by
  refine cMatrix_rpow_mul_rpow_of_posSemidef_scalar hA ?_
  intro _ hx
  rw [mul_comm]
  exact real_sandwiched_left_rpow_mul_sqrt hx halpha

theorem _root_.MState.prod_right_posDef_of_posDef
    {a : Type u1} {b : Type v1} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Nonempty a]
    (rhoA : MState a) (sigmaB : MState b)
    (hprod : (rhoA.prod sigmaB).m.PosDef) :
    sigmaB.m.PosDef := by
  have hpt :
      (Matrix.traceLeft (rhoA.prod sigmaB).m).PosDef :=
    _root_.QIT.traceLeft_posDef_of_posDef
      (a := a) (b := b) (M := (rhoA.prod sigmaB).m) hprod
  rw [MState.traceLeft_prod rhoA sigmaB] at hpt
  exact hpt

/-- Infimum of independently optimized real-valued objectives over a product
domain.  This is the order-theoretic scalar step used in the KW source when an
`inf` over product side-information states separates into two independent
`inf`s. -/
theorem real_sInf_range_prod_add_eq_add_sInf_range
    {ι κ : Type*} [Nonempty ι] [Nonempty κ] (f : ι → ℝ) (g : κ → ℝ)
    (hf : BddBelow (Set.range f)) (hg : BddBelow (Set.range g)) :
    sInf (Set.range fun p : ι × κ => f p.1 + g p.2) =
      sInf (Set.range f) + sInf (Set.range g) := by
  let hpair : BddBelow (Set.range fun p : ι × κ => f p.1 + g p.2) := by
    rcases hf with ⟨lf, hlf⟩
    rcases hg with ⟨lg, hlg⟩
    refine ⟨lf + lg, ?_⟩
    rintro x ⟨p, rfl⟩
    exact add_le_add (hlf ⟨p.1, rfl⟩) (hlg ⟨p.2, rfl⟩)
  apply le_antisymm
  · rw [Real.sInf_le_iff hpair (Set.range_nonempty _)]
    intro ε hε
    have hhalf : 0 < ε / 2 := by linarith
    rcases Real.lt_sInf_add_pos (s := Set.range f) (Set.range_nonempty f) hhalf with
      ⟨xf, ⟨i, rfl⟩, hi⟩
    rcases Real.lt_sInf_add_pos (s := Set.range g) (Set.range_nonempty g) hhalf with
      ⟨xg, ⟨j, rfl⟩, hj⟩
    refine ⟨f i + g j, ⟨(i, j), rfl⟩, ?_⟩
    linarith
  · refine le_csInf (Set.range_nonempty _) ?_
    rintro x ⟨p, rfl⟩
    exact add_le_add (csInf_le hf ⟨p.1, rfl⟩) (csInf_le hg ⟨p.2, rfl⟩)

/-- Infimum of a nonnegative extended-real family, computed in `ENNReal`.

Sandwiched-Renyi divergence candidates are never negative; this bridge lets the
KW product-side-state `inf` split use the `ENNReal` complete-lattice API rather
than full-rank real-valued reductions. -/
theorem ereal_sInf_range_nonneg_eq_coe_ennreal_iInf
    {ι : Type*} [Nonempty ι] (f : ι → EReal) (hf : ∀ i, 0 ≤ f i) :
    sInf (Set.range f) = ENNReal.toEReal (⨅ i, (f i).toENNReal) := by
  have hbdd : BddBelow (Set.range f) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hf i
  apply le_antisymm
  · rw [csInf_le_iff hbdd (Set.range_nonempty f)]
    intro b hb
    by_cases hb_nonpos : b ≤ 0
    · exact hb_nonpos.trans (EReal.coe_ennreal_nonneg _)
    · have hb_nonneg : 0 ≤ b := le_of_lt (lt_of_not_ge hb_nonpos)
      have hb_to :
          b.toENNReal ≤ ⨅ i, (f i).toENNReal := by
        refine le_iInf fun i => ?_
        exact EReal.toENNReal_le_toENNReal (hb ⟨i, rfl⟩)
      rw [← EReal.coe_toENNReal hb_nonneg]
      exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr hb_to
  · refine le_csInf (Set.range_nonempty f) ?_
    rintro _ ⟨i, rfl⟩
    have hi :
        (⨅ j, (f j).toENNReal) ≤ (f i).toENNReal :=
      iInf_le (fun j => (f j).toENNReal) i
    have hE :
        ENNReal.toEReal (⨅ j, (f j).toENNReal) ≤ ((f i).toENNReal : EReal) :=
      EReal.coe_ennreal_le_coe_ennreal_iff.mpr hi
    simpa [EReal.coe_toENNReal (hf i)] using hE

/-- Product infimum split for nonnegative extended-real objectives.

This is the order-theoretic form of the KW step that separates the independent
`inf_{sigma_1, sigma_2}` after the fixed product candidate has been rewritten
as a sum of two factor candidates. -/
theorem ereal_sInf_range_prod_add_eq_add_sInf_range_nonneg
    {ι κ : Type*} [Nonempty ι] [Nonempty κ] (f : ι → EReal) (g : κ → EReal)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ j, 0 ≤ g j) :
    sInf (Set.range fun p : ι × κ => f p.1 + g p.2) =
      sInf (Set.range f) + sInf (Set.range g) := by
  have hfg : ∀ p : ι × κ, 0 ≤ f p.1 + g p.2 := by
    intro p
    exact add_nonneg (hf p.1) (hg p.2)
  rw [ereal_sInf_range_nonneg_eq_coe_ennreal_iInf
        (fun p : ι × κ => f p.1 + g p.2) hfg]
  rw [ereal_sInf_range_nonneg_eq_coe_ennreal_iInf f hf]
  rw [ereal_sInf_range_nonneg_eq_coe_ennreal_iInf g hg]
  rw [← EReal.coe_ennreal_add]
  congr 1
  have hterm : ∀ p : ι × κ,
      (f p.1 + g p.2).toENNReal = (f p.1).toENNReal + (g p.2).toENNReal := by
    intro p
    exact EReal.toENNReal_add (hf p.1) (hg p.2)
  simp_rw [hterm]
  calc
    (⨅ p : ι × κ, (f p.1).toENNReal + (g p.2).toENNReal) =
        ⨅ i : ι, ⨅ j : κ, (f i).toENNReal + (g j).toENNReal := by
          simp [iInf_prod]
    _ = ⨅ i : ι, (f i).toENNReal + ⨅ j : κ, (g j).toENNReal := by
          simp_rw [ENNReal.add_iInf]
    _ = (⨅ i : ι, (f i).toENNReal) + ⨅ j : κ, (g j).toENNReal := by
          rw [ENNReal.iInf_add]

/-- Supremum of independently optimized real-valued objectives over a product
domain.  This is the scalar optimization split used in the product-input
superadditivity step of KW `EA_capacity.tex:1239-1244`. -/
theorem real_sSup_range_prod_add_eq_add_sSup_range
    {ι κ : Type*} [Nonempty ι] [Nonempty κ] (f : ι → ℝ) (g : κ → ℝ)
    (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g)) :
    sSup (Set.range fun p : ι × κ => f p.1 + g p.2) =
      sSup (Set.range f) + sSup (Set.range g) := by
  let hpair : BddAbove (Set.range fun p : ι × κ => f p.1 + g p.2) := by
    rcases hf with ⟨uf, huf⟩
    rcases hg with ⟨ug, hug⟩
    refine ⟨uf + ug, ?_⟩
    rintro x ⟨p, rfl⟩
    exact add_le_add (huf ⟨p.1, rfl⟩) (hug ⟨p.2, rfl⟩)
  apply le_antisymm
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro x ⟨p, rfl⟩
    exact add_le_add (le_csSup hf ⟨p.1, rfl⟩) (le_csSup hg ⟨p.2, rfl⟩)
  · rw [Real.le_sSup_iff hpair (Set.range_nonempty _)]
    intro ε hε
    have hhalf : ε / 2 < 0 := by linarith
    rcases Real.add_neg_lt_sSup (s := Set.range f) (Set.range_nonempty f) hhalf with
      ⟨xf, ⟨i, rfl⟩, hi⟩
    rcases Real.add_neg_lt_sSup (s := Set.range g) (Set.range_nonempty g) hhalf with
      ⟨xg, ⟨j, rfl⟩, hj⟩
    refine ⟨f i + g j, ⟨(i, j), rfl⟩, ?_⟩
    linarith

/-- On a nonempty bounded-below set with strictly positive infimum, `log2`
sends the infimum to the infimum of the image. -/
theorem real_log2_sInf_image_eq {s : Set ℝ}
    (hne : s.Nonempty) (hbdd : BddBelow s) (hinf_pos : 0 < sInf s) :
    sInf (log2 '' s) = log2 (sInf s) := by
  unfold log2
  have hcont : ContinuousWithinAt (fun x : ℝ => Real.log x / Real.log 2) s (sInf s) :=
    (Real.continuousAt_log hinf_pos.ne').div_const _ |>.continuousWithinAt
  have hmono : MonotoneOn (fun x : ℝ => Real.log x / Real.log 2) s := by
    intro x hx y hy hxy
    have hxpos : 0 < x := lt_of_lt_of_le hinf_pos (csInf_le hbdd hx)
    exact div_le_div_of_nonneg_right (Real.log_le_log hxpos hxy)
      (le_of_lt (Real.log_pos one_lt_two))
  have hmap := MonotoneOn.map_csInf_of_continuousWithinAt
    (f := fun x : ℝ => Real.log x / Real.log 2) (A := s) hcont hmono hne hbdd
  simpa using hmap.symm

/-- KW scalar optimization split for the reverse product-state inequality:
after restricting the source supremum to product side-information states, the
logarithm of the supremum of products separates into the sum of two independent
logarithmic suprema. -/
theorem real_log2_sSup_range_prod_mul_eq_add
    {ι κ : Type*} [Nonempty ι] [Nonempty κ] (f : ι → ℝ) (g : κ → ℝ)
    (hfpos : ∀ i, 0 < f i) (hgpos : ∀ j, 0 < g j)
    (hprod : BddAbove (Set.range fun p : ι × κ => f p.1 * g p.2))
    (hlogf : BddAbove (Set.range fun i : ι => log2 (f i)))
    (hlogg : BddAbove (Set.range fun j : κ => log2 (g j))) :
    log2 (sSup (Set.range fun p : ι × κ => f p.1 * g p.2)) =
      sSup (Set.range fun i : ι => log2 (f i)) +
        sSup (Set.range fun j : κ => log2 (g j)) := by
  let prodSet : Set ℝ := Set.range fun p : ι × κ => f p.1 * g p.2
  have hprod_nonempty : prodSet.Nonempty := Set.range_nonempty _
  have hprod_pos : ∀ x ∈ prodSet, 0 < x := by
    rintro x ⟨p, rfl⟩
    exact mul_pos (hfpos p.1) (hgpos p.2)
  have hlogsup :
      sSup (log2 '' prodSet) = log2 (sSup prodSet) :=
    log2_sSup_image_eq hprod_nonempty hprod hprod_pos
  have himage :
      log2 '' prodSet =
        Set.range fun p : ι × κ => log2 (f p.1 * g p.2) := by
    ext x
    constructor
    · rintro ⟨y, ⟨p, rfl⟩, rfl⟩
      exact ⟨p, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨f p.1 * g p.2, ⟨p, rfl⟩, rfl⟩
  have hlogpoint :
      (fun p : ι × κ => log2 (f p.1 * g p.2)) =
        (fun p : ι × κ => log2 (f p.1) + log2 (g p.2)) := by
    funext p
    rw [log2_mul (ne_of_gt (hfpos p.1)) (ne_of_gt (hgpos p.2))]
  rw [← hlogsup]
  rw [himage, hlogpoint]
  exact real_sSup_range_prod_add_eq_add_sSup_range
    (fun i : ι => log2 (f i)) (fun j : κ => log2 (g j)) hlogf hlogg

/-- Supremum of a product objective factors into the product of independent
suprema when both objectives are nonnegative.

This is the scalar form needed for the all-state `tau_C` side of the KW
alternate expression, where singular references are allowed and pointwise
strict positivity is therefore unavailable. -/
theorem real_sSup_range_prod_mul_eq_mul_sSup_range_of_nonneg
    {ι κ : Type*} [Nonempty ι] [Nonempty κ] (f : ι → ℝ) (g : κ → ℝ)
    (hfnonneg : ∀ i, 0 ≤ f i) (hgnonneg : ∀ j, 0 ≤ g j)
    (hprod : BddAbove (Set.range fun p : ι × κ => f p.1 * g p.2)) :
    sSup (Set.range fun p : ι × κ => f p.1 * g p.2) =
      sSup (Set.range f) * sSup (Set.range g) := by
  rw [sSup_range, sSup_range, sSup_range]
  rw [ciSup_prod hprod]
  calc
    (⨆ (i : ι) (j : κ), f i * g j) =
        ⨆ i : ι, f i * (⨆ j : κ, g j) := by
      congr
      ext i
      rw [Real.mul_iSup_of_nonneg (hfnonneg i)]
    _ = (⨆ i : ι, f i) * (⨆ j : κ, g j) := by
      rw [Real.iSup_mul_of_nonneg (Real.iSup_nonneg hgnonneg)]

/-- Logarithmic version of
`real_sSup_range_prod_mul_eq_mul_sSup_range_of_nonneg`.  The assumptions only
require strict positivity of the two independent suprema, not pointwise
strict positivity. -/
theorem real_log2_sSup_range_prod_mul_eq_add_of_nonneg
    {ι κ : Type*} [Nonempty ι] [Nonempty κ] (f : ι → ℝ) (g : κ → ℝ)
    (hfnonneg : ∀ i, 0 ≤ f i) (hgnonneg : ∀ j, 0 ≤ g j)
    (hprod : BddAbove (Set.range fun p : ι × κ => f p.1 * g p.2))
    (hfsup_pos : 0 < sSup (Set.range f)) (hgsup_pos : 0 < sSup (Set.range g)) :
    log2 (sSup (Set.range fun p : ι × κ => f p.1 * g p.2)) =
      log2 (sSup (Set.range f)) + log2 (sSup (Set.range g)) := by
  rw [real_sSup_range_prod_mul_eq_mul_sSup_range_of_nonneg f g hfnonneg hgnonneg hprod]
  exact log2_mul (ne_of_gt hfsup_pos) (ne_of_gt hgsup_pos)

/-- Coefficient-weighted form of
`real_log2_sSup_range_prod_mul_eq_add`, matching the scalar shell of
KW `EA_capacity.tex:1208-1214` for `alpha > 1`. -/
theorem real_sandwichedCoeff_log2_sSup_range_prod_mul_eq_add
    {ι κ : Type*} [Nonempty ι] [Nonempty κ] (f : ι → ℝ) (g : κ → ℝ)
    (hfpos : ∀ i, 0 < f i) (hgpos : ∀ j, 0 < g j)
    (hprod : BddAbove (Set.range fun p : ι × κ => f p.1 * g p.2))
    (hlogf : BddAbove (Set.range fun i : ι => log2 (f i)))
    (hlogg : BddAbove (Set.range fun j : κ => log2 (g j)))
    {alpha : ℝ} (halpha : 1 < alpha) :
    alpha / (alpha - 1) *
        log2 (sSup (Set.range fun p : ι × κ => f p.1 * g p.2)) =
      alpha / (alpha - 1) *
          sSup (Set.range fun i : ι => log2 (f i)) +
        alpha / (alpha - 1) *
          sSup (Set.range fun j : κ => log2 (g j)) := by
  have _halpha_ne : alpha - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt halpha)
  rw [real_log2_sSup_range_prod_mul_eq_add f g hfpos hgpos hprod hlogf hlogg]
  ring

/-- For `alpha > 1`, the source exponent `(alpha - 1) / alpha` lies in
`(0, 1)`.  This is the parameter conversion used in KW
`EA_capacity.tex:2016-2023` before invoking Sion. -/
theorem sandwichedAlphaPrime_pos_lt_one {alpha : ℝ} (halpha : 1 < alpha) :
    0 < (alpha - 1) / alpha ∧ (alpha - 1) / alpha < 1 := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  constructor
  · exact div_pos (sub_pos.mpr halpha) halpha_pos
  · rw [div_lt_one halpha_pos]
    linarith

/-- Closed-interval form of `sandwichedAlphaPrime_pos_lt_one`, matching the
operator-concavity side condition in the Sion step of KW
`EA_capacity.tex:2032-2039`. -/
theorem sandwichedAlphaPrime_mem_Icc_zero_one {alpha : ℝ} (halpha : 1 < alpha) :
    (alpha - 1) / alpha ∈ Set.Icc (0 : ℝ) 1 := by
  have hp := sandwichedAlphaPrime_pos_lt_one halpha
  exact ⟨le_of_lt hp.1, le_of_lt hp.2⟩

/-- KW high-`alpha` specialization of the Sion exchange for the raw
alternate-expression trace bracket.

This packages the minimax step in `EA_capacity.tex:2020-2025` with the exact
parameter `p = (alpha - 1) / alpha`.  The compact full-support lower-bound
domain is kept explicit; removing this restriction and passing to all side
states is part of the remaining alternate-expression closure. -/
theorem sandwichedAlpha_sion_abcSidePowerTraceRe_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    {R : CMatrix ((a × b) × c)} (hR : R.PosSemidef)
    (halpha : 1 < alpha) :
    (⨅ σ ∈ MState.uniformlyPositiveDensityMatrixSet delta b,
        ⨆ τ ∈ MState.densityMatrixSet c,
          (MState.abcSidePowerTraceRe (a := a) R σ τ ((alpha - 1) / alpha) :
            EReal)) =
      ⨆ τ ∈ MState.densityMatrixSet c,
        ⨅ σ ∈ MState.uniformlyPositiveDensityMatrixSet delta b,
          (MState.abcSidePowerTraceRe (a := a) R σ τ ((alpha - 1) / alpha) :
            EReal) := by
  have hp := sandwichedAlphaPrime_pos_lt_one halpha
  exact MState.uniformlyPositiveDensityMatrixSet_sion_abcSidePowerTraceRe_EReal
    (a := a) (b := b) (c := c)
    hdelta_pos
    (MState.uniformlyPositiveDensityMatrixSet_nonempty (a := b) hdelta_le)
    hR hp.1 (le_of_lt hp.2)

/-- On normalized side states, the matrix-domain Sion function used above is
the real part of the source pure-state bracket.

This bridges the reusable `ConditionalRenyiMinimax` matrix API back to the
KW trace expression in `EA_capacity.tex:2016-2025`. -/
theorem upwardRenyiDualityBracketRe_state_matrices
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (ψ : Ket ((a × b) × c)) (σB : MState b) (τC : MState c)
    (alphaPrime : ℝ) :
    MState.upwardRenyiDualityBracketRe (a := a)
        ψ σB.m τC.m alphaPrime =
      (ψ.upwardRenyiDualityCommonBracket σB τC alphaPrime).re := by
  have hσ :
      MState.densityMatrixSetState σB.m
          (MState.state_matrix_mem_densityMatrixSet σB) = σB := by
    apply MState.ext
    exact MState.densityMatrixSetState_matrix σB.m
      (MState.state_matrix_mem_densityMatrixSet σB)
  have hτ :
      MState.densityMatrixSetState τC.m
          (MState.state_matrix_mem_densityMatrixSet τC) = τC := by
    apply MState.ext
    exact MState.densityMatrixSetState_matrix τC.m
      (MState.state_matrix_mem_densityMatrixSet τC)
  rw [MState.upwardRenyiDualityBracketRe_of_mem (a := a) ψ
    (MState.state_matrix_mem_densityMatrixSet σB)
    (MState.state_matrix_mem_densityMatrixSet τC)
    alphaPrime]
  rw [hσ, hτ]

/-- The compact full-support matrix domain used by Sion is equivalent to
optimizing over states whose density matrix has the same lower spectral bound. -/
theorem uniformlyPositiveState_iInf_matrix_eq_uniformlyPositiveDensityMatrixSet_iInf
    {b : Type v1} [Fintype b] [DecidableEq b] {delta : ℝ}
    (f : CMatrix b → EReal) :
    (⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
        f σ.val.m) =
      ⨅ M : CMatrix b,
        ⨅ _hM : M ∈ MState.uniformlyPositiveDensityMatrixSet delta b, f M := by
  apply le_antisymm
  · refine le_iInf ?_
    intro M
    refine le_iInf ?_
    intro hM
    let σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m} :=
      ⟨MState.densityMatrixSetState M hM.1, by
        rw [MState.densityMatrixSetState_matrix]
        exact hM.2⟩
    calc
      (⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
          f σ.val.m) ≤ f σ.val.m := iInf_le _ _
      _ = f M := by rw [MState.densityMatrixSetState_matrix]
  · refine le_iInf ?_
    intro σ
    exact le_trans
      (iInf_le
        (fun M : CMatrix b =>
          ⨅ hM : M ∈ MState.uniformlyPositiveDensityMatrixSet delta b, f M)
        σ.val.m)
      (iInf_le
        (fun hM : σ.val.m ∈ MState.uniformlyPositiveDensityMatrixSet delta b =>
          f σ.val.m)
        ⟨MState.state_matrix_mem_densityMatrixSet σ.val, σ.property⟩)

/-- Supremum version of
`uniformlyPositiveState_iInf_matrix_eq_uniformlyPositiveDensityMatrixSet_iInf`. -/
theorem uniformlyPositiveState_iSup_matrix_eq_uniformlyPositiveDensityMatrixSet_iSup
    {b : Type v1} [Fintype b] [DecidableEq b] {delta : ℝ}
    (f : CMatrix b → EReal) :
    (⨆ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
        f σ.val.m) =
      ⨆ M : CMatrix b,
        ⨆ _hM : M ∈ MState.uniformlyPositiveDensityMatrixSet delta b, f M := by
  apply le_antisymm
  · refine iSup_le ?_
    intro σ
    calc
      f σ.val.m ≤
          (⨆ hM : σ.val.m ∈ MState.uniformlyPositiveDensityMatrixSet delta b,
            f σ.val.m) :=
        le_iSup
          (fun hM : σ.val.m ∈ MState.uniformlyPositiveDensityMatrixSet delta b =>
            f σ.val.m)
          ⟨MState.state_matrix_mem_densityMatrixSet σ.val, σ.property⟩
      _ ≤ ⨆ M : CMatrix b,
          ⨆ hM : M ∈ MState.uniformlyPositiveDensityMatrixSet delta b, f M :=
        le_iSup
          (fun M : CMatrix b =>
            ⨆ hM : M ∈ MState.uniformlyPositiveDensityMatrixSet delta b, f M)
          σ.val.m
  · refine iSup_le ?_
    intro M
    refine iSup_le ?_
    intro hM
    let σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m} :=
      ⟨MState.densityMatrixSetState M hM.1, by
        rw [MState.densityMatrixSetState_matrix]
        exact hM.2⟩
    calc
      f M = f σ.val.m := by rw [MState.densityMatrixSetState_matrix]
      _ ≤ (⨆ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
          f σ.val.m) :=
        le_iSup
          (fun σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m} =>
            f σ.val.m)
          σ

/-- The uniformly-positive state domain used by the compact Sion step is a
subdomain of the full-rank state domain.

This is the EReal order bridge used when passing from the compact
`delta • I ≤ sigma_B` domain back to the full-rank branch of the KW
alternate-expression proof. -/
theorem fullRankState_iInf_le_uniformlyPositiveState_iInf_EReal
    {b : Type v1} [Fintype b] [DecidableEq b] {delta : ℝ}
    (hdelta : 0 < delta) (f : MState b → EReal) :
    (⨅ σ : {σ : MState b // σ.m.PosDef}, f σ.val) ≤
      ⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m}, f σ.val := by
  refine le_iInf ?_
  intro σ
  have hσpos : σ.val.m.PosDef :=
    MState.uniformlyPositiveDensityMatrixSet_subset_posDef (a := b) hdelta
      ⟨MState.state_matrix_mem_densityMatrixSet σ.val, σ.property⟩
  exact iInf_le (fun τ : {σ : MState b // σ.m.PosDef} => f τ.val)
    ⟨σ.val, hσpos⟩
end

end QIT
