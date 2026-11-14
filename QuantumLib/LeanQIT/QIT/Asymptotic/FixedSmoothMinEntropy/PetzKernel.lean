/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.Smooth
public import QIT.OneShot.SmoothEndpoint
public import QIT.Information.Renyi.AlphaEntropyContinuity
public import QIT.Information.Renyi.ConditionalPetzRenyi
public import QIT.Asymptotic.AEP
public import QIT.Information.Renyi.RpowOperatorConvex
public import QIT.Information.Renyi.FrankLieb.ScalarOperator
public import QIT.States.Geometry.FuchsVdG
public import QIT.OneShot.GentleMeasurement
public import QIT.States.TraceNorm.Audenaert
import QIT.Util.CMatrixCLM
public import QIT.States.PosSqrtOrder
public import QIT.Util.BlockMatrix
public import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Fixed-side smooth conditional min-entropy

This module adds the fixed-reference side of the conditional min-entropy API.
The existing `State.conditionalMinEntropy` optimizes over the conditioning
state, while the source-facing `State.smoothConditionalMinEntropy` delegates to
the subnormalized smoothing convention. For the finite fully quantum AEP route,
we also need the candidate where the same reference state `σ_B` is kept fixed
through the purified-distance smoothing ball, plus the order bridge into the
optimized quantity.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker NNReal
open Filter

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The Petz trace functional `Tr(A^α B^(1-α))`, kept as a real scalar.

The positive-definite hypotheses needed by most analytic uses stay on the
lemmas that consume the definition. -/
def cMatrixPetzTrace
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (alpha : ℝ) : ℝ :=
  ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re

/-- Vectorized form of the complex Petz trace kernel.

This is the Hilbert-Schmidt-space entry point for the Petz perspective route:
left multiplication by `A^α` and right multiplication by `B^(1-α)` are encoded
as a Kronecker matrix acting on `Matrix.vec 1`. -/
theorem cMatrixPetzTrace_trace_eq_vec_one_kronecker
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (alpha : ℝ) :
    (CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace =
      dotProduct (star (Matrix.vec (1 : CMatrix ι)))
        (Matrix.mulVec
          (Matrix.kronecker (Matrix.transpose (CFC.rpow B (1 - alpha)))
            (CFC.rpow A alpha))
          (Matrix.vec (1 : CMatrix ι))) := by
  have hmulvec :
      Matrix.mulVec
          (Matrix.kronecker (Matrix.transpose (CFC.rpow B (1 - alpha)))
            (CFC.rpow A alpha))
          (Matrix.vec (1 : CMatrix ι)) =
        Matrix.vec (CFC.rpow A alpha * (1 : CMatrix ι) *
          (Matrix.transpose (Matrix.transpose (CFC.rpow B (1 - alpha))))) := by
    simpa using
      (Matrix.kronecker_mulVec_vec
        (A := CFC.rpow A alpha) (X := (1 : CMatrix ι))
        (B := Matrix.transpose (CFC.rpow B (1 - alpha))))
  rw [hmulvec]
  rw [Matrix.mul_one]
  rw [Matrix.transpose_transpose]
  rw [Matrix.star_vec_dotProduct_vec]
  rw [Matrix.conjTranspose_one]
  rw [Matrix.one_mul]

/-- Real-valued vectorized form of `cMatrixPetzTrace`. -/
theorem cMatrixPetzTrace_eq_vec_one_kronecker_re
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (alpha : ℝ) :
    cMatrixPetzTrace A B alpha =
      (dotProduct (star (Matrix.vec (1 : CMatrix ι)))
        (Matrix.mulVec
          (Matrix.kronecker (Matrix.transpose (CFC.rpow B (1 - alpha)))
            (CFC.rpow A alpha))
          (Matrix.vec (1 : CMatrix ι)))).re := by
  rw [cMatrixPetzTrace]
  exact congrArg Complex.re (cMatrixPetzTrace_trace_eq_vec_one_kronecker A B alpha)

private theorem cMatrix_rpow_unitary_conj_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CMatrix ι} (hA : A.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) (s : ℝ) :
    CFC.rpow (star (U : CMatrix ι) * A * (U : CMatrix ι)) s =
      star (U : CMatrix ι) * CFC.rpow A s * (U : CMatrix ι) := by
  change (star (U : CMatrix ι) * A * (U : CMatrix ι)) ^ s =
    star (U : CMatrix ι) * (A ^ s) * (U : CMatrix ι)
  have hmap_nonneg : 0 ≤ star (U : CMatrix ι) * A * (U : CMatrix ι) :=
    Matrix.nonneg_iff_posSemidef.mpr (by
      simpa [Matrix.mul_assoc] using
        hA.posSemidef.conjTranspose_mul_mul_same (U : CMatrix ι))
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
  rw [CFC.rpow_eq_cfc_real (a := star (U : CMatrix ι) * A * (U : CMatrix ι))
    (y := s) hmap_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s) hA_nonneg]
  simpa [Unitary.conjStarAlgAut_symm_apply] using
    (StarAlgHomClass.map_cfc
      ((Unitary.conjStarAlgAut ℂ (CMatrix ι) U).symm)
      (fun x : ℝ => x ^ s) A
      (hf := by
        intro x hx
        exact
          (Real.continuousAt_rpow_const x s
            (.inl (ne_of_gt
              ((Matrix.PosDef.isStrictlyPositive hA).spectrum_pos hx)))).continuousWithinAt)
      (hφ := by
        change Continuous fun A : CMatrix ι => star (U : CMatrix ι) * A * (U : CMatrix ι)
        fun_prop)).symm

/-- Petz trace is invariant under simultaneous unitary conjugation, for
positive-definite inputs and every real exponent. -/
theorem cMatrixPetzTrace_unitary_conj_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosDef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) (alpha : ℝ) :
    cMatrixPetzTrace (star (U : CMatrix ι) * A * (U : CMatrix ι))
        (star (U : CMatrix ι) * B * (U : CMatrix ι)) alpha =
      cMatrixPetzTrace A B alpha := by
  unfold cMatrixPetzTrace
  rw [cMatrix_rpow_unitary_conj_posDef hA U alpha,
    cMatrix_rpow_unitary_conj_posDef hB U (1 - alpha)]
  let Apow : CMatrix ι := CFC.rpow A alpha
  let Bpow : CMatrix ι := CFC.rpow B (1 - alpha)
  change (((star (U : CMatrix ι) * Apow * (U : CMatrix ι)) *
      (star (U : CMatrix ι) * Bpow * (U : CMatrix ι))).trace).re =
    (Apow * Bpow).trace.re
  have hU : (U : CMatrix ι) * star (U : CMatrix ι) = 1 :=
    Unitary.coe_mul_star_self U
  have hprod :
      (star (U : CMatrix ι) * Apow * (U : CMatrix ι)) *
          (star (U : CMatrix ι) * Bpow * (U : CMatrix ι)) =
        star (U : CMatrix ι) * (Apow * Bpow) * (U : CMatrix ι) := by
    rw [show
        (star (U : CMatrix ι) * Apow * (U : CMatrix ι)) *
            (star (U : CMatrix ι) * Bpow * (U : CMatrix ι)) =
          star (U : CMatrix ι) * Apow *
            ((U : CMatrix ι) * star (U : CMatrix ι)) *
              Bpow * (U : CMatrix ι) by noncomm_ring]
    rw [hU]
    noncomm_ring
  have htrace :
      (star (U : CMatrix ι) * (Apow * Bpow) * (U : CMatrix ι)).trace =
        (Apow * Bpow).trace := by
    calc
      (star (U : CMatrix ι) * (Apow * Bpow) * (U : CMatrix ι)).trace =
          ((U : CMatrix ι) * (star (U : CMatrix ι) * (Apow * Bpow))).trace := by
            exact Matrix.trace_mul_comm
              (star (U : CMatrix ι) * (Apow * Bpow)) (U : CMatrix ι)
      _ = (((U : CMatrix ι) * star (U : CMatrix ι)) * (Apow * Bpow)).trace := by
            congr 1
            rw [Matrix.mul_assoc]
      _ = (Apow * Bpow).trace := by
            rw [hU, Matrix.one_mul]
  rw [hprod]
  exact congrArg Complex.re htrace

/-- Petz trace is invariant under simultaneous unitary conjugation when the
left input is PSD and the left exponent is nonnegative. -/
theorem cMatrixPetzTrace_unitary_conj_eq_posSemidef_left
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ} (halpha_nonneg : 0 ≤ alpha) :
    cMatrixPetzTrace (star (U : CMatrix ι) * A * (U : CMatrix ι))
        (star (U : CMatrix ι) * B * (U : CMatrix ι)) alpha =
      cMatrixPetzTrace A B alpha := by
  unfold cMatrixPetzTrace
  rw [cMatrix_rpow_unitary_conj hA U halpha_nonneg,
    cMatrix_rpow_unitary_conj_posDef hB U (1 - alpha)]
  let Apow : CMatrix ι := CFC.rpow A alpha
  let Bpow : CMatrix ι := CFC.rpow B (1 - alpha)
  change (((star (U : CMatrix ι) * Apow * (U : CMatrix ι)) *
      (star (U : CMatrix ι) * Bpow * (U : CMatrix ι))).trace).re =
    (Apow * Bpow).trace.re
  have hU : (U : CMatrix ι) * star (U : CMatrix ι) = 1 :=
    Unitary.coe_mul_star_self U
  have hprod :
      (star (U : CMatrix ι) * Apow * (U : CMatrix ι)) *
          (star (U : CMatrix ι) * Bpow * (U : CMatrix ι)) =
        star (U : CMatrix ι) * (Apow * Bpow) * (U : CMatrix ι) := by
    rw [show
        (star (U : CMatrix ι) * Apow * (U : CMatrix ι)) *
            (star (U : CMatrix ι) * Bpow * (U : CMatrix ι)) =
          star (U : CMatrix ι) * Apow *
            ((U : CMatrix ι) * star (U : CMatrix ι)) *
              Bpow * (U : CMatrix ι) by noncomm_ring]
    rw [hU]
    noncomm_ring
  have htrace :
      (star (U : CMatrix ι) * (Apow * Bpow) * (U : CMatrix ι)).trace =
        (Apow * Bpow).trace := by
    calc
      (star (U : CMatrix ι) * (Apow * Bpow) * (U : CMatrix ι)).trace =
          ((U : CMatrix ι) * (star (U : CMatrix ι) * (Apow * Bpow))).trace := by
            exact Matrix.trace_mul_comm
              (star (U : CMatrix ι) * (Apow * Bpow)) (U : CMatrix ι)
      _ = (((U : CMatrix ι) * star (U : CMatrix ι)) * (Apow * Bpow)).trace := by
            congr 1
            rw [Matrix.mul_assoc]
      _ = (Apow * Bpow).trace := by
            rw [hU, Matrix.one_mul]
  rw [hprod]
  exact congrArg Complex.re htrace

/-- The Petz trace effect-variational inequality needed to turn a spectral
threshold into a positive-part bound.

This is the remaining noncommutative input in the TCR smooth-min route: it
should follow from the operator-convex/perspective form of `x ↦ x^α` for
`1 < α ≤ 2` (or an equivalent Petz-Hölder/Young inequality). Instantiating this
at the positive spectral projector of `A - λB` gives
`Tr((A - λB)⁺) ≤ λ^(1-α) Tr(A^α B^(1-α))`. -/
def cMatrixPetzTraceEffectVariational
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (lambda alpha : ℝ) : Prop :=
  ∀ E : CMatrix ι, E.PosSemidef → E ≤ 1 →
    (((E * A).trace).re - lambda * ((E * B).trace).re) ≤
      lambda ^ (1 - alpha) *
        ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re

/-- Dephasing/pinching in the orthonormal basis encoded by a unitary `U`.

This is the finite matrix form of
`X ↦ ∑ᵢ |ψᵢ⟩⟨ψᵢ| X |ψᵢ⟩⟨ψᵢ|`, written by moving `X` into the `U` basis,
discarding off-diagonal entries, and conjugating back. The diagonal values are
taken as real parts, which is the source-facing form used for Hermitian
positive inputs. -/
def cMatrixUnitaryDephase
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (X : CMatrix ι) : CMatrix ι :=
  (U : CMatrix ι) *
    (Matrix.diagonal fun i =>
      ((((star (U : CMatrix ι) * X * (U : CMatrix ι)) i i).re : ℝ) : ℂ) :
        CMatrix ι) *
      star (U : CMatrix ι)

/-- The coordinate sign attached to a Boolean sign choice. -/
def cMatrixSignScalar
    {ι : Type*} (s : ι → Bool) (i : ι) : ℂ :=
  if s i then -1 else 1

@[simp]
theorem cMatrixSignScalar_star
    {ι : Type*} (s : ι → Bool) (i : ι) :
    star (cMatrixSignScalar s i) = cMatrixSignScalar s i := by
  by_cases h : s i <;> simp [cMatrixSignScalar, h]

@[simp]
theorem cMatrixSignScalar_mul_self
    {ι : Type*} (s : ι → Bool) (i : ι) :
    cMatrixSignScalar s i * cMatrixSignScalar s i = 1 := by
  by_cases h : s i <;> simp [cMatrixSignScalar, h]

/-- Diagonal sign unitary for a Boolean sign choice on coordinates. -/
def cMatrixSignUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → Bool) : Matrix.unitaryGroup ι ℂ :=
  ⟨Matrix.diagonal fun i => cMatrixSignScalar s i, by
    rw [Matrix.mem_unitaryGroup_iff']
    have hstar :
        star (Matrix.diagonal fun i => cMatrixSignScalar s i : CMatrix ι) =
          (Matrix.diagonal fun i => cMatrixSignScalar s i : CMatrix ι) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.star_apply, Matrix.diagonal]
      · have hji : j ≠ i := fun h => hij h.symm
        simp [Matrix.star_apply, Matrix.diagonal, hij, hji]
    rw [hstar, Matrix.diagonal_mul_diagonal]
    ext i j
    simp [Matrix.diagonal, Matrix.one_apply]⟩

@[simp]
theorem cMatrixSignUnitary_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → Bool) (i j : ι) :
    (cMatrixSignUnitary s : CMatrix ι) i j =
      if i = j then cMatrixSignScalar s i else 0 := by
  simp [cMatrixSignUnitary, Matrix.diagonal]

/-- Conjugating by a coordinate sign unitary multiplies an entry by the two
endpoint signs. -/
theorem cMatrixSignUnitary_conj_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → Bool) (X : CMatrix ι) (i j : ι) :
    (star (cMatrixSignUnitary s : CMatrix ι) * X *
        (cMatrixSignUnitary s : CMatrix ι)) i j =
      cMatrixSignScalar s i * X i j * cMatrixSignScalar s j := by
  change (star (Matrix.diagonal fun i => cMatrixSignScalar s i : CMatrix ι) * X *
      (Matrix.diagonal fun i => cMatrixSignScalar s i : CMatrix ι)) i j =
    cMatrixSignScalar s i * X i j * cMatrixSignScalar s j
  have hstar :
      star (Matrix.diagonal fun i => cMatrixSignScalar s i : CMatrix ι) =
        (Matrix.diagonal fun i => cMatrixSignScalar s i : CMatrix ι) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.star_apply, Matrix.diagonal]
    · have hji : j ≠ i := fun h => hij h.symm
      simp [Matrix.star_apply, Matrix.diagonal, hij, hji]
  rw [hstar, Matrix.mul_diagonal, Matrix.diagonal_mul]

private def cMatrixSignToggle
    {ι : Type*} [DecidableEq ι] (i : ι) : (ι → Bool) ≃ (ι → Bool) where
  toFun s := Function.update s i (!(s i))
  invFun s := Function.update s i (!(s i))
  left_inv := by
    intro s
    funext k
    by_cases hk : k = i
    · subst k
      simp
    · simp [Function.update, hk]
  right_inv := by
    intro s
    funext k
    by_cases hk : k = i
    · subst k
      simp
    · simp [Function.update, hk]

private theorem cMatrixSignScalar_toggle_self
    {ι : Type*} [DecidableEq ι] (s : ι → Bool) (i : ι) :
    cMatrixSignScalar (cMatrixSignToggle i s) i = -cMatrixSignScalar s i := by
  by_cases h : s i <;> simp [cMatrixSignScalar, cMatrixSignToggle, Function.update, h]

private theorem cMatrixSignScalar_toggle_of_ne
    {ι : Type*} [DecidableEq ι] (s : ι → Bool) {i j : ι} (hij : i ≠ j) :
    cMatrixSignScalar (cMatrixSignToggle i s) j = cMatrixSignScalar s j := by
  have hji : j ≠ i := fun h => hij h.symm
  simp [cMatrixSignScalar, cMatrixSignToggle, Function.update, hji]

private theorem cMatrixSign_sum_offDiag
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CMatrix ι) {i j : ι} (hij : i ≠ j) :
    ∑ s : ι → Bool, cMatrixSignScalar s i * X i j * cMatrixSignScalar s j = 0 := by
  classical
  let f : (ι → Bool) → ℂ := fun s =>
    cMatrixSignScalar s i * X i j * cMatrixSignScalar s j
  let S : ℂ := ∑ s : ι → Bool, f s
  have htoggle : S = ∑ s : ι → Bool, f (cMatrixSignToggle i s) := by
    simpa [S] using ((cMatrixSignToggle i).sum_comp f).symm
  have hneg_terms : ∀ s : ι → Bool, f (cMatrixSignToggle i s) = -f s := by
    intro s
    simp [f, cMatrixSignScalar_toggle_self, cMatrixSignScalar_toggle_of_ne s hij,
      neg_mul]
  have hS_neg : S = -S := by
    calc
      S = ∑ s : ι → Bool, f (cMatrixSignToggle i s) := htoggle
      _ = ∑ s : ι → Bool, -f s := by
          exact Finset.sum_congr rfl fun s _ => hneg_terms s
      _ = -S := by simp [S]
  have hdouble : S + S = 0 := by
    nth_rw 1 [hS_neg]
    abel
  have htwo : (2 : ℂ) * S = 0 := by
    simpa [two_mul] using hdouble
  have htwo_ne : (2 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp htwo).resolve_left htwo_ne

/-- Entrywise form of the sign-unitary average: it keeps diagonal entries and
cancels off-diagonal entries. -/
theorem cMatrixSignAverage_conj_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CMatrix ι) (i j : ι) :
    (((Fintype.card (ι → Bool) : ℂ)⁻¹) •
        ∑ s : ι → Bool,
          star (cMatrixSignUnitary s : CMatrix ι) * X *
            (cMatrixSignUnitary s : CMatrix ι)) i j =
      if i = j then X i j else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    have hsum :
        (∑ s : ι → Bool,
          (star (cMatrixSignUnitary s : CMatrix ι) * X *
            (cMatrixSignUnitary s : CMatrix ι)) i i) =
          Fintype.card (ι → Bool) • X i i := by
      calc
        (∑ s : ι → Bool,
          (star (cMatrixSignUnitary s : CMatrix ι) * X *
            (cMatrixSignUnitary s : CMatrix ι)) i i)
            = ∑ _s : ι → Bool, X i i := by
                apply Finset.sum_congr rfl
                intro s _
                rw [cMatrixSignUnitary_conj_apply]
                calc
                  cMatrixSignScalar s i * X i i * cMatrixSignScalar s i =
                      (cMatrixSignScalar s i * cMatrixSignScalar s i) * X i i := by ring
                  _ = X i i := by simp
        _ = Fintype.card (ι → Bool) • X i i := by
              simp [Finset.sum_const]
    rw [Matrix.smul_apply, Matrix.sum_apply, hsum, nsmul_eq_mul]
    simp
  · have hsum :
        (∑ s : ι → Bool,
          (star (cMatrixSignUnitary s : CMatrix ι) * X *
            (cMatrixSignUnitary s : CMatrix ι)) i j) = 0 := by
      simpa [cMatrixSignUnitary_conj_apply] using
        cMatrixSign_sum_offDiag X (i := i) (j := j) hij
    simp [Matrix.smul_apply, Matrix.sum_apply, hsum, hij]

/-- Off-diagonal cancellation under the coordinate sign average. -/
theorem cMatrixSignAverage_conj_offDiag
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CMatrix ι) {i j : ι} (hij : i ≠ j) :
    (((Fintype.card (ι → Bool) : ℂ)⁻¹) •
        ∑ s : ι → Bool,
          star (cMatrixSignUnitary s : CMatrix ι) * X *
            (cMatrixSignUnitary s : CMatrix ι)) i j = 0 := by
  simpa [hij] using cMatrixSignAverage_conj_apply X i j

/-- Diagonal entries are fixed by the coordinate sign average. -/
theorem cMatrixSignAverage_conj_diag
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CMatrix ι) (i : ι) :
    (((Fintype.card (ι → Bool) : ℂ)⁻¹) •
        ∑ s : ι → Bool,
          star (cMatrixSignUnitary s : CMatrix ι) * X *
            (cMatrixSignUnitary s : CMatrix ι)) i i = X i i := by
  simpa using cMatrixSignAverage_conj_apply X i i

/-- For Hermitian inputs, coordinate dephasing in the standard basis is the
uniform average over coordinate sign-unitary conjugates. -/
theorem cMatrixUnitaryDephase_one_eq_signAverage_of_isHermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : CMatrix ι} (hX : X.IsHermitian) :
    cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) X =
      ((Fintype.card (ι → Bool) : ℂ)⁻¹) •
        ∑ s : ι → Bool,
          star (cMatrixSignUnitary s : CMatrix ι) * X *
            (cMatrixSignUnitary s : CMatrix ι) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    have hdiag_star : star (X i i) = X i i := by
      simpa [Matrix.star_apply] using congr_fun (congr_fun hX.eq i) i
    have hdiag_im : (X i i).im = 0 := by
      have h := congrArg Complex.im hdiag_star
      simp at h
      linarith
    have hdiag : (((X i i).re : ℝ) : ℂ) = X i i := by
      apply Complex.ext <;> simp [hdiag_im]
    rw [cMatrixSignAverage_conj_diag X i]
    unfold cMatrixUnitaryDephase
    simp [Matrix.diagonal, hdiag]
  · rw [cMatrixSignAverage_conj_offDiag X hij]
    unfold cMatrixUnitaryDephase
    simp [Matrix.diagonal, hij]

theorem cMatrixUnitaryDephase_trace_re
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (X : CMatrix ι) :
    (cMatrixUnitaryDephase U X).trace.re = X.trace.re := by
  let X' : CMatrix ι := star (U : CMatrix ι) * X * (U : CMatrix ι)
  let D : CMatrix ι := Matrix.diagonal fun i => (((X' i i).re : ℝ) : ℂ)
  have hdephase : cMatrixUnitaryDephase U X =
      (U : CMatrix ι) * D * star (U : CMatrix ι) := by
    simp [cMatrixUnitaryDephase, X', D]
  have htrace_conj :
      ((U : CMatrix ι) * D * star (U : CMatrix ι)).trace = D.trace := by
    calc
      ((U : CMatrix ι) * D * star (U : CMatrix ι)).trace =
          (star (U : CMatrix ι) * ((U : CMatrix ι) * D)).trace := by
            exact Matrix.trace_mul_comm ((U : CMatrix ι) * D) (star (U : CMatrix ι))
      _ = ((star (U : CMatrix ι) * (U : CMatrix ι)) * D).trace := by
            congr 1
            rw [Matrix.mul_assoc]
      _ = D.trace := by
            rw [Unitary.coe_star_mul_self U, Matrix.one_mul]
  have htrace_basis : X'.trace = X.trace := by
    calc
      X'.trace = (((star (U : CMatrix ι) * X) * (U : CMatrix ι)).trace) := by
          simp [X', Matrix.mul_assoc]
      _ = ((U : CMatrix ι) * (star (U : CMatrix ι) * X)).trace := by
          exact Matrix.trace_mul_comm (star (U : CMatrix ι) * X) (U : CMatrix ι)
      _ = (((U : CMatrix ι) * star (U : CMatrix ι)) * X).trace := by
          congr 1
          rw [Matrix.mul_assoc]
      _ = X.trace := by
          have hU : (U : CMatrix ι) * star (U : CMatrix ι) = 1 := by
            exact Unitary.coe_mul_star_self U
          rw [hU, Matrix.one_mul]
  have hD_trace_re : D.trace.re = X'.trace.re := by
    simp [D, X', Matrix.trace]
  rw [hdephase, htrace_conj]
  exact hD_trace_re.trans (congrArg Complex.re htrace_basis)

private theorem trace_mul_diagonal_ofReal_re
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : CMatrix ι) (d : ι → ℝ) :
    ((M * (Matrix.diagonal fun i => ((d i : ℝ) : ℂ) : CMatrix ι)).trace).re =
      ∑ i, (M i i).re * d i := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal, Complex.mul_re]

private theorem trace_mul_unitary_diagonal_conj_re
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : CMatrix ι) (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℝ) :
    ((E * ((U : CMatrix ι) *
        (Matrix.diagonal fun i => ((d i : ℝ) : ℂ) : CMatrix ι) *
          star (U : CMatrix ι))).trace).re =
      (((star (U : CMatrix ι) * E * (U : CMatrix ι)) *
        (Matrix.diagonal fun i => ((d i : ℝ) : ℂ) : CMatrix ι)).trace).re := by
  let D : CMatrix ι := Matrix.diagonal fun i => ((d i : ℝ) : ℂ)
  have htrace :
      (E * ((U : CMatrix ι) * D * star (U : CMatrix ι))).trace =
        (((star (U : CMatrix ι) * E * (U : CMatrix ι)) * D).trace) := by
    calc
      (E * ((U : CMatrix ι) * D * star (U : CMatrix ι))).trace =
          (((E * (U : CMatrix ι)) * D) * star (U : CMatrix ι)).trace := by
            congr 1
            noncomm_ring
      _ = (star (U : CMatrix ι) * ((E * (U : CMatrix ι)) * D)).trace := by
            exact Matrix.trace_mul_comm (((E * (U : CMatrix ι)) * D))
              (star (U : CMatrix ι))
      _ = (((star (U : CMatrix ι) * E * (U : CMatrix ι)) * D).trace) := by
            congr 1
            noncomm_ring
  simpa [D] using congrArg Complex.re htrace

private theorem scalar_effect_threshold_le_scaled_petz
    {e a b lambda alpha : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (ha : 0 ≤ a) (hb : 0 < b) (hlambda : 0 < lambda)
    (halpha : 1 ≤ alpha) :
    e * (a - lambda * b) ≤ lambda ^ (1 - alpha) * (a ^ alpha * b ^ (1 - alpha)) := by
  have hrhs_nonneg :
      0 ≤ lambda ^ (1 - alpha) * (a ^ alpha * b ^ (1 - alpha)) := by
    positivity
  by_cases hgap : a - lambda * b ≤ 0
  · have hleft_nonpos : e * (a - lambda * b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos he0 hgap
    exact hleft_nonpos.trans hrhs_nonneg
  · have hgap_nonneg : 0 ≤ a - lambda * b := le_of_lt (lt_of_not_ge hgap)
    have hleft_le_gap : e * (a - lambda * b) ≤ 1 * (a - lambda * b) :=
      mul_le_mul_of_nonneg_right he1 hgap_nonneg
    have hratio_ge_one : 1 ≤ a / (lambda * b) := by
      rw [one_le_div (mul_pos hlambda hb)]
      linarith
    have ha_pos : 0 < a := by
      nlinarith [mul_pos hlambda hb]
    have hratio_le_rpow : a / (lambda * b) ≤ (a / (lambda * b)) ^ alpha :=
      Real.self_le_rpow_of_one_le hratio_ge_one halpha
    have hscalar :
        a - lambda * b ≤
          lambda ^ (1 - alpha) * (a ^ alpha * b ^ (1 - alpha)) := by
      have hden_pos : 0 < lambda * b := mul_pos hlambda hb
      have hden_nonneg : 0 ≤ lambda * b := le_of_lt hden_pos
      have hmul :
          (lambda * b) * (a / (lambda * b)) ≤
            (lambda * b) * ((a / (lambda * b)) ^ alpha) :=
        mul_le_mul_of_nonneg_left hratio_le_rpow hden_nonneg
      have hleft_eq : (lambda * b) * (a / (lambda * b)) = a := by
        field_simp [ne_of_gt hden_pos]
      have hright_eq :
          (lambda * b) * ((a / (lambda * b)) ^ alpha) =
            lambda ^ (1 - alpha) * (a ^ alpha * b ^ (1 - alpha)) := by
        calc
          (lambda * b) * ((a / (lambda * b)) ^ alpha)
              = (lambda * b) * (a ^ alpha / (lambda * b) ^ alpha) := by
                  rw [Real.div_rpow (le_of_lt ha_pos) hden_nonneg]
          _ = a ^ alpha * ((lambda * b) / (lambda * b) ^ alpha) := by ring
          _ = a ^ alpha * ((lambda * b) ^ (1 : ℝ) / (lambda * b) ^ alpha) := by
                rw [Real.rpow_one]
          _ = a ^ alpha * ((lambda * b) ^ (1 - alpha)) := by
                rw [Real.rpow_sub hden_pos 1 alpha]
          _ = a ^ alpha * (lambda ^ (1 - alpha) * b ^ (1 - alpha)) := by
                rw [Real.mul_rpow (le_of_lt hlambda) (le_of_lt hb)]
          _ = lambda ^ (1 - alpha) * (a ^ alpha * b ^ (1 - alpha)) := by ring
      rw [hleft_eq, hright_eq] at hmul
      linarith
    exact hleft_le_gap.trans (by simpa using hscalar)

private theorem posDef_unitary_conj_diag_re_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CMatrix ι} (hA : A.PosDef) (U : Matrix.unitaryGroup ι ℂ) (i : ι) :
    0 < ((star (U : CMatrix ι) * A * (U : CMatrix ι)) i i).re := by
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  have hA' : A'.PosDef := by
    dsimp [A']
    rw [Matrix.IsUnit.posDef_star_left_conjugate_iff (Unitary.isUnit_coe :
      IsUnit (U : CMatrix ι))]
    exact hA
  exact (Complex.pos_iff.mp (hA'.diag_pos (i := i))).1

private theorem posSemidef_unitary_conj_diag_re_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CMatrix ι} (hA : A.PosSemidef) (U : Matrix.unitaryGroup ι ℂ) (i : ι) :
    0 ≤ ((star (U : CMatrix ι) * A * (U : CMatrix ι)) i i).re := by
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  have hA' : A'.PosSemidef := by
    simpa [A'] using posSemidef_unitary_conj hA U
  simpa [A'] using posSemidef_diagonal_re_nonneg hA' i

theorem cMatrixUnitaryDephase_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : CMatrix ι} (hX : X.PosSemidef) (U : Matrix.unitaryGroup ι ℂ) :
    (cMatrixUnitaryDephase U X).PosSemidef := by
  let X' : CMatrix ι := star (U : CMatrix ι) * X * (U : CMatrix ι)
  let D : CMatrix ι := Matrix.diagonal fun i => (((X' i i).re : ℝ) : ℂ)
  have hX' : X'.PosSemidef := by
    simpa [X'] using posSemidef_unitary_conj hX U
  have hD : D.PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    change 0 ≤ (((X' i i).re : ℝ) : ℂ)
    exact_mod_cast posSemidef_diagonal_re_nonneg hX' i
  have hconj : ((U : CMatrix ι) * D * star (U : CMatrix ι)).PosSemidef := by
    rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff
      (Unitary.isUnit_coe : IsUnit (U : CMatrix ι))]
    exact hD
  simpa [cMatrixUnitaryDephase, X', D] using hconj

theorem cMatrixUnitaryDephase_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : CMatrix ι} (hX : X.PosDef) (U : Matrix.unitaryGroup ι ℂ) :
    (cMatrixUnitaryDephase U X).PosDef := by
  let X' : CMatrix ι := star (U : CMatrix ι) * X * (U : CMatrix ι)
  let D : CMatrix ι := Matrix.diagonal fun i => (((X' i i).re : ℝ) : ℂ)
  have hD : D.PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    change 0 < (((X' i i).re : ℝ) : ℂ)
    exact_mod_cast (by
      simpa [X'] using posDef_unitary_conj_diag_re_pos hX U i)
  have hconj : ((U : CMatrix ι) * D * star (U : CMatrix ι)).PosDef := by
    rw [Matrix.IsUnit.posDef_star_right_conjugate_iff
      (Unitary.isUnit_coe : IsUnit (U : CMatrix ι))]
    exact hD
  simpa [cMatrixUnitaryDephase, X', D] using hconj

theorem cMatrixUnitaryDephase_one_eq_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : CMatrix ι) :
    cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) X =
      (Matrix.diagonal fun i => (((X i i).re : ℝ) : ℂ) : CMatrix ι) := by
  unfold cMatrixUnitaryDephase
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal]
  · simp [Matrix.diagonal, hij]

theorem cMatrixUnitaryDephase_eq_unitary_conj_coordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (X : CMatrix ι) :
    cMatrixUnitaryDephase U X =
      (U : CMatrix ι) *
        cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ)
          (star (U : CMatrix ι) * X * (U : CMatrix ι)) *
        star (U : CMatrix ι) := by
  let X' : CMatrix ι := star (U : CMatrix ι) * X * (U : CMatrix ι)
  rw [cMatrixUnitaryDephase_one_eq_diagonal X']
  simp [cMatrixUnitaryDephase, X', Matrix.mul_assoc]

theorem cMatrixPetzTrace_unitaryDephase_eq_coordinate_conj
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ} (halpha_nonneg : 0 ≤ alpha) :
    cMatrixPetzTrace (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B) alpha =
      cMatrixPetzTrace
        (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ)
          (star (U : CMatrix ι) * A * (U : CMatrix ι)))
        (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ)
          (star (U : CMatrix ι) * B * (U : CMatrix ι))) alpha := by
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
  have hB' : B'.PosDef := by
    dsimp [B']
    rw [Matrix.IsUnit.posDef_star_left_conjugate_iff
      (Unitary.isUnit_coe : IsUnit (U : CMatrix ι))]
    exact hB
  have hdephA :
      cMatrixUnitaryDephase U A =
        (U : CMatrix ι) *
          cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A' *
          star (U : CMatrix ι) := by
    simpa [A'] using cMatrixUnitaryDephase_eq_unitary_conj_coordinate U A
  have hdephB :
      cMatrixUnitaryDephase U B =
        (U : CMatrix ι) *
          cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B' *
          star (U : CMatrix ι) := by
    simpa [B'] using cMatrixUnitaryDephase_eq_unitary_conj_coordinate U B
  have hA_coord :
      star (U : CMatrix ι) * cMatrixUnitaryDephase U A * (U : CMatrix ι) =
        cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A' := by
    rw [hdephA]
    have hUU : star (U : CMatrix ι) * (U : CMatrix ι) = 1 :=
      Unitary.coe_star_mul_self U
    calc
      star (U : CMatrix ι) *
            ((U : CMatrix ι) *
              cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A' *
              star (U : CMatrix ι)) *
            (U : CMatrix ι) =
          (star (U : CMatrix ι) * (U : CMatrix ι)) *
            cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A' *
            (star (U : CMatrix ι) * (U : CMatrix ι)) := by
            noncomm_ring
      _ = cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A' := by
            rw [hUU, Matrix.one_mul, Matrix.mul_one]
  have hB_coord :
      star (U : CMatrix ι) * cMatrixUnitaryDephase U B * (U : CMatrix ι) =
        cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B' := by
    rw [hdephB]
    have hUU : star (U : CMatrix ι) * (U : CMatrix ι) = 1 :=
      Unitary.coe_star_mul_self U
    calc
      star (U : CMatrix ι) *
            ((U : CMatrix ι) *
              cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B' *
              star (U : CMatrix ι)) *
            (U : CMatrix ι) =
          (star (U : CMatrix ι) * (U : CMatrix ι)) *
            cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B' *
            (star (U : CMatrix ι) * (U : CMatrix ι)) := by
            noncomm_ring
      _ = cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B' := by
            rw [hUU, Matrix.one_mul, Matrix.mul_one]
  have hconj :=
    (cMatrixPetzTrace_unitary_conj_eq_posSemidef_left
      (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B)
      (cMatrixUnitaryDephase_posSemidef hA U)
      (cMatrixUnitaryDephase_posDef hB U) U halpha_nonneg)
  rw [hA_coord, hB_coord] at hconj
  exact hconj.symm

/-- Finite uniform joint convexity for the Petz trace functional.

This is the smallest reusable Jensen shape needed by the sign-twirl proof
below: if the operator-convex perspective theorem for `x ↦ x^alpha` is
available, it should instantiate this statement for finite families with a
positive-semidefinite left input, positive-definite reference input, and
`1 < alpha ≤ 2`. -/
def cMatrixPetzTraceUniformJointConvex
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [DecidableEq ι]
    (A B : κ → CMatrix ι) (alpha : ℝ) : Prop :=
  (∀ k, (A k).PosSemidef) →
  (∀ k, (B k).PosDef) →
  1 < alpha → alpha ≤ 2 →
    cMatrixPetzTrace
        (((Fintype.card κ : ℂ)⁻¹) • ∑ k, A k)
        (((Fintype.card κ : ℂ)⁻¹) • ∑ k, B k)
        alpha ≤
      ∑ k, ((Fintype.card κ : ℝ)⁻¹) * cMatrixPetzTrace (A k) (B k) alpha

/-- The linear-minus-resolvent integrand that appears in the operator-convex
perspective integral for `x ↦ x^α`, `1 < α ≤ 2`.

The coefficient is left explicit: in the Audenaert/Ando integral it will be a
positive scalar depending on the integration variable. -/
def cMatrixPetzPerspectiveResolventIntegrand
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (r coeff : ℝ) (A : CMatrix a) (B : CMatrix b) : CMatrix (a × b) :=
  Matrix.kronecker A (1 : CMatrix b) -
    coeff • Matrix.andoResolventIntegrand (a := a) (b := b) r A B

private theorem cMatrix_rpowIntegrand₁₂_eq_resolvent_affine
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p r : ℝ} {A : CMatrix ι}
    (hp : p ∈ Set.Ioo (1 : ℝ) 2) (hr : 0 < r) (hA : A.PosSemidef) :
    cfcₙ (Real.rpowIntegrand₁₂ p r) A =
      (r ^ (p - 1)) •
        (r⁻¹ • A + r • (A + r • (1 : CMatrix ι))⁻¹ -
          (1 : CMatrix ι)) := by
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  have hself : IsSelfAdjoint A := hA.isHermitian
  have hq_nonneg : quasispectrum ℝ A ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    exact NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg A hA_nonneg x hx
  have hx_nonneg : ∀ x ∈ spectrum ℝ A, 0 ≤ x := by
    intro x hx
    exact hq_nonneg (spectrum_subset_quasispectrum ℝ A hx)
  have hden : ∀ x ∈ spectrum ℝ A, r + x ≠ 0 := by
    intro x hx hzero
    have hx0 := hx_nonneg x hx
    linarith
  have hfcont : ContinuousOn (Real.rpowIntegrand₁₂ p r) (quasispectrum ℝ A) := by
    exact (Real.continuousOn_rpowIntegrand₁₂_uncurry hp.1
      (quasispectrum ℝ A) hq_nonneg).uncurry_left r hr
  have halg : algebraMap ℝ (CMatrix ι) r = r • (1 : CMatrix ι) := by
    ext i j
    rw [Matrix.algebraMap_matrix_apply]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  calc
    cfcₙ (Real.rpowIntegrand₁₂ p r) A =
        cfc (Real.rpowIntegrand₁₂ p r) A := by
      rw [cfcₙ_eq_cfc (a := A) (f := Real.rpowIntegrand₁₂ p r) (hf := hfcont)
        (hf0 := Real.rpowIntegrand₁₂_zero (p := p) hr)]
    _ = cfc (fun x : ℝ =>
          r ^ (p - 1) * (r⁻¹ * x + r * (r + x)⁻¹ - 1)) A := by
      rfl
    _ =
        r ^ (p - 1) •
          (r⁻¹ • A + r • Ring.inverse (algebraMap ℝ (CMatrix ι) r + A) -
            (1 : CMatrix ι)) := by
      rw [cfc_const_mul
        (r ^ (p - 1))
        (fun x : ℝ => r⁻¹ * x + r * (r + x)⁻¹ - 1) A
        (hf := by fun_prop (disch := grind -abstractProof))]
      rw [cfc_sub
        (f := fun x : ℝ => r⁻¹ * x + r * (r + x)⁻¹)
        (g := fun _ : ℝ => 1) (a := A)
        (hf := by fun_prop (disch := grind -abstractProof))
        (hg := by fun_prop)]
      rw [cfc_add
        (f := fun x : ℝ => r⁻¹ * x)
        (g := fun x : ℝ => r * (r + x)⁻¹) (a := A)
        (hf := by fun_prop)
        (hg := by fun_prop (disch := grind -abstractProof))]
      rw [cfc_const_mul_id (R := ℝ) r⁻¹ A (ha := hself)]
      rw [cfc_const_mul r (fun x : ℝ => (r + x)⁻¹) A
        (hf := by fun_prop (disch := grind -abstractProof))]
      rw [cfc_inv
        (fun x : ℝ => r + x) A hden
        (hf := by fun_prop)
        (ha := hself)]
      rw [cfc_const_add (R := ℝ) (r := r) (f := fun x : ℝ => x)
        (a := A) (ha := hself)]
      rw [cfc_id' (R := ℝ) (a := A) (ha := hself)]
      rw [cfc_const (R := ℝ) (A := CMatrix ι) 1 A (ha := hself)]
      simp
    _ =
        (r ^ (p - 1)) •
          (r⁻¹ • A + r • (A + r • (1 : CMatrix ι))⁻¹ -
            (1 : CMatrix ι)) := by
      rw [halg]
      congr 2
      congr 1
      congr 1
      rw [add_comm]
      rw [Matrix.nonsing_inv_eq_ringInverse]

theorem cMatrix_rpowIntegrand₁₂_kronecker_inv_mul_right_eq_petzPerspective
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {p r : ℝ} {A : CMatrix a} {B : CMatrix b}
    (hp : p ∈ Set.Ioo (1 : ℝ) 2) (hr : 0 < r)
    (hA : A.PosSemidef) (hB : B.PosDef) :
    cfcₙ (Real.rpowIntegrand₁₂ p r) (Matrix.kronecker A B⁻¹) *
        Matrix.kronecker (1 : CMatrix a) B =
      (r ^ (p - 2)) •
        cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r r A B := by
  let C : CMatrix (a × b) := Matrix.kronecker A B⁻¹
  let X : CMatrix (a × b) := Matrix.kronecker A (1 : CMatrix b)
  let Y : CMatrix (a × b) := Matrix.kronecker (1 : CMatrix a) B
  let D : CMatrix (a × b) := X + r • Y
  have hCpsd : C.PosSemidef := by
    simpa [C] using hA.kronecker hB.inv.posSemidef
  have hCmulY : C * Y = X := by
    simpa [C, Y, X] using
      cMatrix_kronecker_inv_ref_mul_right
        (a := a) (b := b) (A := A) (B := B) hB
  have hinv : (C + r • (1 : CMatrix (a × b)))⁻¹ = Y * D⁻¹ := by
    simpa [C, X, Y, D] using
      cMatrix_shiftedKroneckerInv_inv_eq_ref_mul_andoDenom_inv
        (a := a) (b := b) (A := A) (B := B) (r := r) hA hB hr
  have hDright : D * D⁻¹ = 1 := by
    have hDpd : D.PosDef := by
      simpa [X, Y, D] using Matrix.andoDenom_posDef (a := a) (b := b) hA hB hr
    have hDdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hDpd.isUnit
    exact Matrix.mul_nonsing_inv D hDdet
  have hresolvent_complement : Y - r • (Y * D⁻¹ * Y) = X * D⁻¹ * Y := by
    calc
      Y - r • (Y * D⁻¹ * Y) =
          (X + r • Y) * D⁻¹ * Y - r • (Y * D⁻¹ * Y) := by
        change Y - r • (Y * D⁻¹ * Y) = D * D⁻¹ * Y - r • (Y * D⁻¹ * Y)
        rw [hDright]
        simp [Matrix.mul_assoc]
      _ = X * D⁻¹ * Y := by
        simp [Matrix.add_mul, Matrix.mul_assoc, sub_eq_add_neg]
  have hpow : r ^ (p - 1) * r⁻¹ = r ^ (p - 2) := by
    calc
      r ^ (p - 1) * r⁻¹ = r ^ (p - 1) * r ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]
      _ = r ^ ((p - 1) + (-1 : ℝ)) := by
        rw [← Real.rpow_add hr (p - 1) (-1 : ℝ)]
      _ = r ^ (p - 2) := by
        ring_nf
  have hpow_mul : r * r ^ (p - 2) = r ^ (p - 1) := by
    calc
      r * r ^ (p - 2) = r ^ (1 : ℝ) * r ^ (p - 2) := by
        rw [Real.rpow_one]
      _ = r ^ ((1 : ℝ) + (p - 2)) := by
        rw [← Real.rpow_add hr (1 : ℝ) (p - 2)]
      _ = r ^ (p - 1) := by
        ring_nf
  have hpowEntry :
      ((r ^ (p - 1) : ℝ) : ℂ) * ((r⁻¹ : ℝ) : ℂ) =
        ((r ^ (p - 2) : ℝ) : ℂ) := by
    simpa using congrArg (fun x : ℝ => (x : ℂ)) hpow
  have hpowMulEntry :
      (r : ℂ) * ((r ^ (p - 2) : ℝ) : ℂ) =
        ((r ^ (p - 1) : ℝ) : ℂ) := by
    simpa using congrArg (fun x : ℝ => (x : ℂ)) hpow_mul
  calc
    cfcₙ (Real.rpowIntegrand₁₂ p r) (Matrix.kronecker A B⁻¹) *
        Matrix.kronecker (1 : CMatrix a) B =
      ((r ^ (p - 1)) •
        (r⁻¹ • C + r • (C + r • (1 : CMatrix (a × b)))⁻¹ -
          (1 : CMatrix (a × b)))) * Y := by
        rw [cMatrix_rpowIntegrand₁₂_eq_resolvent_affine
          (p := p) (r := r) (A := C) hp hr hCpsd]
    _ =
      (r ^ (p - 1)) •
        ((r⁻¹ • C) * Y + (r • (C + r • (1 : CMatrix (a × b)))⁻¹) * Y -
          Y) := by
        simp [sub_eq_add_neg, add_mul]
    _ =
      (r ^ (p - 1)) •
        (r⁻¹ • X + r • (Y * D⁻¹ * Y) - Y) := by
        simp [hinv, hCmulY, Matrix.mul_assoc]
    _ =
      (r ^ (p - 1)) •
        (r⁻¹ • X - (Y - r • (Y * D⁻¹ * Y))) := by
        abel_nf
    _ =
      (r ^ (p - 1)) •
        (r⁻¹ • X - X * D⁻¹ * Y) := by
        rw [hresolvent_complement]
    _ =
      (r ^ (p - 2)) •
        (X - r • (X * D⁻¹ * Y)) := by
        ext i j
        simp only [Matrix.smul_apply, Matrix.sub_apply, Complex.real_smul]
        let W : ℂ := (X * D⁻¹ * Y) i j
        change ((r ^ (p - 1) : ℝ) : ℂ) * (((r⁻¹ : ℝ) : ℂ) * X i j - W) =
          ((r ^ (p - 2) : ℝ) : ℂ) * (X i j - (r : ℂ) * W)
        calc
          ((r ^ (p - 1) : ℝ) : ℂ) * (((r⁻¹ : ℝ) : ℂ) * X i j - W) =
              (((r ^ (p - 1) : ℝ) : ℂ) * ((r⁻¹ : ℝ) : ℂ)) * X i j -
                ((r ^ (p - 1) : ℝ) : ℂ) * W := by ring
          _ =
              ((r ^ (p - 2) : ℝ) : ℂ) * X i j -
                ((r : ℂ) * ((r ^ (p - 2) : ℝ) : ℂ)) * W := by
            rw [hpowEntry, hpowMulEntry]
          _ =
              ((r ^ (p - 2) : ℝ) : ℂ) * (X i j - (r : ℂ) * W) := by
            ring
    _ =
      (r ^ (p - 2)) •
        cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r r A B := by
        simp [cMatrixPetzPerspectiveResolventIntegrand,
          Matrix.andoResolventIntegrand, X, Y, D]

private theorem cMatrixPetz_integrableOn_mul_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : MeasureTheory.Measure ℝ} {s : Set ℝ} {f : ℝ → CMatrix ι}
    (hf : MeasureTheory.IntegrableOn f s μ) (R : CMatrix ι) :
    MeasureTheory.IntegrableOn (fun r => f r * R) s μ := by
  have hf' : MeasureTheory.Integrable f (μ.restrict s) := by
    simpa [MeasureTheory.IntegrableOn] using hf
  have h :=
    (ContinuousLinearMap.mulLeftRight ℝ (CMatrix ι) (1 : CMatrix ι) R).integrable_comp hf'
  simpa [ContinuousLinearMap.mulLeftRight_apply, MeasureTheory.IntegrableOn] using h

private theorem cMatrixPetz_setIntegral_mul_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : MeasureTheory.Measure ℝ} {s : Set ℝ} {f : ℝ → CMatrix ι}
    (hf : MeasureTheory.IntegrableOn f s μ) (R : CMatrix ι) :
    (∫ r in s, f r ∂μ) * R = ∫ r in s, f r * R ∂μ := by
  have hf' : MeasureTheory.Integrable f (μ.restrict s) := by
    simpa [MeasureTheory.IntegrableOn] using hf
  have h :=
    (ContinuousLinearMap.mulLeftRight ℝ (CMatrix ι) (1 : CMatrix ι) R).integral_comp_comm hf'
  simpa [ContinuousLinearMap.mulLeftRight_apply] using h.symm

private theorem cMatrixPetz_integral_conjTranspose
    {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : MeasureTheory.Integrable f μ) :
    Matrix.conjTranspose (∫ x, f x ∂μ) =
      ∫ x, Matrix.conjTranspose (f x) ∂μ := by
  simpa [cMatrixConjTransposeCLM] using
    ((cMatrixConjTransposeCLM (ι := ι)).integral_comp_comm hf).symm

private theorem cMatrixPetz_integral_dotProduct_mulVec
    {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : MeasureTheory.Integrable f μ) (x : ι → ℂ) :
    dotProduct (star x) (Matrix.mulVec (∫ t, f t ∂μ) x) =
      ∫ t, dotProduct (star x) (Matrix.mulVec (f t) x) ∂μ := by
  simp_rw [← cMatrixQuadraticCLM_apply x]
  exact
    ((cMatrixQuadraticCLM x).integral_comp_comm hf).symm

private theorem cMatrixPetz_integral_posSemidef_of_ae
    {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : MeasureTheory.Integrable f μ)
    (hpos : ∀ᵐ t ∂μ, (f t).PosSemidef) :
    (∫ t, f t ∂μ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian, cMatrixPetz_integral_conjTranspose (hf := hf)]
    apply MeasureTheory.integral_congr_ae
    exact hpos.mono fun _ ht => ht.isHermitian.eq
  · intro x
    rw [cMatrixPetz_integral_dotProduct_mulVec (hf := hf) x]
    exact MeasureTheory.integral_nonneg_of_ae
      (hpos.mono fun _ ht => ht.dotProduct_mulVec_nonneg x)

private theorem cMatrixPetz_setIntegral_mono
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : MeasureTheory.Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {f g : ℝ → CMatrix ι}
    (hf : MeasureTheory.IntegrableOn f s μ) (hg : MeasureTheory.IntegrableOn g s μ)
    (hle : ∀ r ∈ s, f r ≤ g r) :
    ∫ r in s, f r ∂μ ≤ ∫ r in s, g r ∂μ := by
  have hdiffInt : MeasureTheory.IntegrableOn (fun r : ℝ => g r - f r) s μ := hg.sub hf
  have hdiffPSD :
      (∫ r in s, (g r - f r) ∂μ).PosSemidef := by
    have hdiffInt' :
        MeasureTheory.Integrable (fun r : ℝ => g r - f r) (μ.restrict s) := by
      simpa [MeasureTheory.IntegrableOn] using hdiffInt
    exact
      cMatrixPetz_integral_posSemidef_of_ae (μ := μ.restrict s) hdiffInt'
        ((MeasureTheory.ae_restrict_iff' hs).mpr
          (MeasureTheory.ae_of_all μ fun r hr => Matrix.le_iff.mp (hle r hr)))
  have hsub :
      ∫ r in s, (g r - f r) ∂μ =
        (∫ r in s, g r ∂μ) - (∫ r in s, f r ∂μ) := by
    simpa [MeasureTheory.IntegrableOn] using
      MeasureTheory.integral_sub (μ := μ.restrict s)
        (by simpa [MeasureTheory.IntegrableOn] using hg)
        (by simpa [MeasureTheory.IntegrableOn] using hf)
  rw [hsub] at hdiffPSD
  exact Matrix.le_iff.mpr hdiffPSD

private theorem cMatrixPetz_setIntegral_finset_sum_smul
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {μ : MeasureTheory.Measure ℝ} {s : Set ℝ} {f : κ → ℝ → CMatrix ι}
    (c : ℝ) (hf : ∀ k, MeasureTheory.IntegrableOn (f k) s μ) :
    ∫ r in s, (∑ k, c • f k r) ∂μ =
      ∑ k, c • ∫ r in s, f k r ∂μ := by
  have hf' :
      ∀ k, MeasureTheory.Integrable (f k) (μ.restrict s) := by
    intro k
    simpa [MeasureTheory.IntegrableOn] using hf k
  calc
    ∫ r in s, (∑ k, c • f k r) ∂μ =
        ∫ r, (∑ k, c • f k r) ∂(μ.restrict s) := rfl
    _ = ∑ k, ∫ r, c • f k r ∂(μ.restrict s) := by
        rw [MeasureTheory.integral_finsetSum]
        intro k _
        exact (hf' k).smul c
    _ = ∑ k, c • ∫ r, f k r ∂(μ.restrict s) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [MeasureTheory.integral_smul]
    _ = ∑ k, c • ∫ r in s, f k r ∂μ := rfl

private theorem cMatrixPetz_rpow_nonsing_inv_eq_rpow_neg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : CMatrix ι} (hB : B.PosDef) (p : ℝ) :
    CFC.rpow B⁻¹ p = CFC.rpow B (-p) := by
  obtain ⟨u, hu⟩ := hB.isUnit
  have hBnonneg : (0 : CMatrix ι) ≤ B :=
    Matrix.nonneg_iff_posSemidef.mpr hB.posSemidef
  have hinv : B⁻¹ = (↑u⁻¹ : CMatrix ι) := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu]
    simp
  calc
    CFC.rpow B⁻¹ p = CFC.rpow (↑u⁻¹ : CMatrix ι) p := by
      rw [hinv]
    _ = CFC.rpow (↑u : CMatrix ι) (-p) := by
      exact (CFC.rpow_neg u p (ha' := by simpa [hu] using hBnonneg)).symm
    _ = CFC.rpow B (-p) := by
      rw [hu]

private theorem cMatrixPetz_rpow_kronecker_inv_mul_right_eq_tensor_one_sub
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A : CMatrix a} {B : CMatrix b}
    (hA : A.PosSemidef) (hB : B.PosDef)
    {p : ℝ} (hp0 : 0 ≤ p) :
    CFC.rpow (Matrix.kronecker A B⁻¹) p *
        Matrix.kronecker (1 : CMatrix a) B =
      Matrix.kronecker (CFC.rpow A p) (CFC.rpow B (1 - p)) := by
  have hBinv_psd : B⁻¹.PosSemidef := hB.inv.posSemidef
  have hpowK :
      CFC.rpow (Matrix.kronecker A B⁻¹) p =
        Matrix.kronecker (CFC.rpow A p) (CFC.rpow B⁻¹ p) := by
    simpa using
      cMatrix_rpow_kronecker_nonneg
        (A := A) (B := B⁻¹) hA hBinv_psd hp0
  have hBpow : CFC.rpow B⁻¹ p * B = CFC.rpow B (1 - p) := by
    rw [cMatrixPetz_rpow_nonsing_inv_eq_rpow_neg hB p]
    have hBpowone : CFC.rpow B (1 : ℝ) = B :=
      CFC.rpow_one B (ha := Matrix.nonneg_iff_posSemidef.mpr hB.posSemidef)
    calc
      CFC.rpow B (-p) * B =
          CFC.rpow B (-p) * CFC.rpow B (1 : ℝ) := by
        rw [hBpowone]
      _ = CFC.rpow B (-p + 1) := by
        exact (CFC.rpow_add (a := B) (x := -p) (y := 1) hB.isUnit).symm
      _ = CFC.rpow B (1 - p) := by
        ring_nf
  calc
    CFC.rpow (Matrix.kronecker A B⁻¹) p *
        Matrix.kronecker (1 : CMatrix a) B =
      Matrix.kronecker (CFC.rpow A p) (CFC.rpow B⁻¹ p) *
        Matrix.kronecker (1 : CMatrix a) B := by
        rw [hpowK]
    _ =
      Matrix.kronecker (CFC.rpow A p * (1 : CMatrix a))
        (CFC.rpow B⁻¹ p * B) := by
        simpa [Matrix.kronecker] using
          (Matrix.mul_kronecker_mul
            (CFC.rpow A p) (1 : CMatrix a) (CFC.rpow B⁻¹ p) B).symm
    _ = Matrix.kronecker (CFC.rpow A p) (CFC.rpow B (1 - p)) := by
        rw [hBpow]
        simp

/-- High-alpha integral representation for the Petz perspective resolvent
integrand. -/
theorem cMatrixPetzPerspectiveIntegralRepresentation_Ioo_one_two
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {p : ℝ} (hp : p ∈ Set.Ioo (1 : ℝ) 2) :
    ∃ μ : MeasureTheory.Measure ℝ,
      (∀ ⦃A : CMatrix a⦄ ⦃B : CMatrix b⦄,
        A.PosSemidef → B.PosDef →
        MeasureTheory.IntegrableOn (fun r : ℝ => (r ^ (p - 2)) •
          cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r r A B)
          (Set.Ioi 0) μ) ∧
      (∀ ⦃A : CMatrix a⦄ ⦃B : CMatrix b⦄,
        A.PosSemidef → B.PosDef →
        Matrix.kronecker (CFC.rpow A p) (CFC.rpow B (1 - p)) =
          ∫ r in Set.Ioi 0, (r ^ (p - 2)) •
            cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r r A B ∂μ) := by
  let pNN : ℝ≥0 := ⟨p, le_trans zero_le_one hp.1.le⟩
  have hpNN : pNN ∈ Set.Ioo (1 : ℝ≥0) 2 := by
    constructor
    · exact_mod_cast hp.1
    · exact_mod_cast hp.2
  obtain ⟨μ, hμ⟩ :=
    CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂
      (CMatrix (a × b)) hpNN
  refine ⟨μ, ?_, ?_⟩
  · intro A B hA hB
    let C : CMatrix (a × b) := Matrix.kronecker A B⁻¹
    let Y : CMatrix (a × b) := Matrix.kronecker (1 : CMatrix a) B
    have hCpsd : C.PosSemidef := by
      simpa [C] using hA.kronecker hB.inv.posSemidef
    have hCnonneg : C ∈ Set.Ici (0 : CMatrix (a × b)) :=
      Matrix.nonneg_iff_posSemidef.mpr hCpsd
    have hCInt :
        MeasureTheory.IntegrableOn
          (fun r : ℝ => cfcₙ (Real.rpowIntegrand₁₂ p r) C)
          (Set.Ioi 0) μ := by
      simpa [pNN] using (hμ C hCnonneg).1
    have hRightInt :
        MeasureTheory.IntegrableOn
          (fun r : ℝ => cfcₙ (Real.rpowIntegrand₁₂ p r) C * Y)
          (Set.Ioi 0) μ :=
      cMatrixPetz_integrableOn_mul_right hCInt Y
    let F : ℝ → CMatrix (a × b) := fun r =>
      cfcₙ (Real.rpowIntegrand₁₂ p r) C * Y
    let G : ℝ → CMatrix (a × b) := fun r =>
      (r ^ (p - 2)) •
        cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r r A B
    have hEqOn : Set.EqOn F G (Set.Ioi 0) := by
      intro r hr
      simpa [F, G, C, Y] using
        cMatrix_rpowIntegrand₁₂_kronecker_inv_mul_right_eq_petzPerspective
          (a := a) (b := b) (p := p) (r := r) (A := A) (B := B)
          hp hr hA hB
    have hGInt : MeasureTheory.IntegrableOn G (Set.Ioi 0) μ :=
      hRightInt.congr_fun hEqOn measurableSet_Ioi
    simpa [G] using hGInt
  · intro A B hA hB
    let C : CMatrix (a × b) := Matrix.kronecker A B⁻¹
    let Y : CMatrix (a × b) := Matrix.kronecker (1 : CMatrix a) B
    have hp0 : 0 ≤ p := le_trans zero_le_one hp.1.le
    have hpNN_pos : 0 < pNN := by
      exact lt_trans zero_lt_one hpNN.1
    have hCpsd : C.PosSemidef := by
      simpa [C] using hA.kronecker hB.inv.posSemidef
    have hCnonneg : C ∈ Set.Ici (0 : CMatrix (a × b)) :=
      Matrix.nonneg_iff_posSemidef.mpr hCpsd
    have hCInt :
        MeasureTheory.IntegrableOn
          (fun r : ℝ => cfcₙ (Real.rpowIntegrand₁₂ p r) C)
          (Set.Ioi 0) μ := by
      simpa [pNN] using (hμ C hCnonneg).1
    let F : ℝ → CMatrix (a × b) := fun r =>
      cfcₙ (Real.rpowIntegrand₁₂ p r) C * Y
    let G : ℝ → CMatrix (a × b) := fun r =>
      (r ^ (p - 2)) •
        cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r r A B
    have hEqOn : Set.EqOn F G (Set.Ioi 0) := by
      intro r hr
      simpa [F, G, C, Y] using
        cMatrix_rpowIntegrand₁₂_kronecker_inv_mul_right_eq_petzPerspective
          (a := a) (b := b) (p := p) (r := r) (A := A) (B := B)
          hp hr hA hB
    have hCpow :
        CFC.rpow C p =
          ∫ r in Set.Ioi 0, cfcₙ (Real.rpowIntegrand₁₂ p r) C ∂μ := by
      calc
        CFC.rpow C p = C ^ pNN := by
          exact (by
            simpa [pNN] using
              (CFC.nnrpow_eq_rpow (a := C) hpNN_pos).symm)
        _ = ∫ r in Set.Ioi 0, cfcₙ (Real.rpowIntegrand₁₂ p r) C ∂μ := by
          simpa [pNN] using (hμ C hCnonneg).2
    have hLeft : CFC.rpow C p * Y = ∫ r in Set.Ioi 0, F r ∂μ := by
      calc
        CFC.rpow C p * Y =
            (∫ r in Set.Ioi 0, cfcₙ (Real.rpowIntegrand₁₂ p r) C ∂μ) * Y := by
          rw [hCpow]
        _ = ∫ r in Set.Ioi 0, cfcₙ (Real.rpowIntegrand₁₂ p r) C * Y ∂μ := by
          rw [cMatrixPetz_setIntegral_mul_right hCInt Y]
        _ = ∫ r in Set.Ioi 0, F r ∂μ := by
          rfl
    have hFGint : ∫ r in Set.Ioi 0, F r ∂μ = ∫ r in Set.Ioi 0, G r ∂μ := by
      apply MeasureTheory.integral_congr_ae
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hEqOn
    have hTensor :
        CFC.rpow C p * Y =
          Matrix.kronecker (CFC.rpow A p) (CFC.rpow B (1 - p)) := by
      simpa [C, Y] using
        cMatrixPetz_rpow_kronecker_inv_mul_right_eq_tensor_one_sub
          (a := a) (b := b) (A := A) (B := B) hA hB hp0
    calc
      Matrix.kronecker (CFC.rpow A p) (CFC.rpow B (1 - p)) =
          CFC.rpow C p * Y := by
        exact hTensor.symm
      _ = ∫ r in Set.Ioi 0, F r ∂μ := hLeft
      _ = ∫ r in Set.Ioi 0, G r ∂μ := hFGint
      _ = ∫ r in Set.Ioi 0, (r ^ (p - 2)) •
          cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r r A B ∂μ := by
        rfl

theorem cMatrixPetzPerspectiveResolventIntegrand_convex_posDef
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {r coeff t : ℝ} (hr : 0 < r) (hcoeff : 0 ≤ coeff)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r coeff
        (t • A₁ + (1 - t) • A₂) (t • B₁ + (1 - t) • B₂) ≤
      t • cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r coeff A₁ B₁ +
        (1 - t) • cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b)
          r coeff A₂ B₂ := by
  let I₁ := Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁
  let I₂ := Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂
  let Ibar := Matrix.andoResolventIntegrand (a := a) (b := b) r
    (t • A₁ + (1 - t) • A₂) (t • B₁ + (1 - t) • B₂)
  let Xbar : CMatrix (a × b) :=
    Matrix.kronecker (t • A₁ + (1 - t) • A₂) (1 : CMatrix b)
  have hconc : t • I₁ + (1 - t) • I₂ ≤ Ibar := by
    simpa [I₁, I₂, Ibar] using
      Matrix.andoResolventIntegrand_concave_posDef
        (a := a) (b := b) hA₁ hA₂ hB₁ hB₂ hr ht0 ht1
  have hscaled : coeff • (t • I₁ + (1 - t) • I₂) ≤ coeff • Ibar :=
    smul_le_smul_of_nonneg_left hconc hcoeff
  have hsub : Xbar - coeff • Ibar ≤ Xbar - coeff • (t • I₁ + (1 - t) • I₂) :=
    sub_le_sub_left hscaled Xbar
  calc
    cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r coeff
        (t • A₁ + (1 - t) • A₂) (t • B₁ + (1 - t) • B₂) =
      Xbar - coeff • Ibar := by rfl
    _ ≤ Xbar - coeff • (t • I₁ + (1 - t) • I₂) := hsub
    _ = t • cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r coeff A₁ B₁ +
        (1 - t) • cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b)
          r coeff A₂ B₂ := by
      ext i j
      simp [cMatrixPetzPerspectiveResolventIntegrand, Xbar, I₁, I₂,
        Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply,
        Matrix.sub_apply, add_mul]
      ring

theorem cMatrixPetzPerspectiveResolventIntegrand_convexOn_posDef
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {r coeff : ℝ} (hr : 0 < r) (hcoeff : 0 ≤ coeff) :
    ConvexOn ℝ ({P : CMatrix a × CMatrix b | P.1.PosSemidef ∧ P.2.PosDef})
      (fun P : CMatrix a × CMatrix b =>
        cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r coeff P.1 P.2) := by
  refine ⟨?hconv, ?hineq⟩
  · intro x hx y hy s t hs ht hst
    have ht_eq : t = 1 - s := by linarith
    have hs_le_one : s ≤ 1 := by linarith
    constructor
    · simpa [Prod.smul_mk, ht_eq] using
        Matrix.PosSemidef.add
          (Matrix.PosSemidef.smul hx.1 hs)
          (Matrix.PosSemidef.smul hy.1 (sub_nonneg.mpr hs_le_one))
    · simpa [Prod.smul_mk, ht_eq] using
        Matrix.PosDef.convexCombination hx.2 hy.2 hs hs_le_one
  · intro x hx y hy s t hs ht hst
    have ht_eq : t = 1 - s := by linarith
    have hs_le_one : s ≤ 1 := by linarith
    obtain ⟨A₁, B₁⟩ := x
    obtain ⟨A₂, B₂⟩ := y
    simpa [Prod.smul_mk, ht_eq] using
      cMatrixPetzPerspectiveResolventIntegrand_convex_posDef
        (a := a) (b := b) hx.1 hy.1 hx.2 hy.2 hr hcoeff hs hs_le_one

private theorem cMatrixPetz_fst_weighted_pair_sum
    {κ a b : Type*} [Fintype κ]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (A : κ → CMatrix a) (B : κ → CMatrix b) (w : ℝ) :
    (∑ i, (fun _ : κ => w) i • (fun k : κ => (A k, B k)) i).1 =
      ∑ k, w • A k := by
  let fstLin : (CMatrix a × CMatrix b) →ₗ[ℝ] CMatrix a :=
    { toFun := Prod.fst
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  show fstLin (∑ i, (fun _ : κ => w) i • (fun k : κ => (A k, B k)) i) =
    ∑ k, w • A k
  rw [map_sum]
  simp [fstLin]

private theorem cMatrixPetz_snd_weighted_pair_sum
    {κ a b : Type*} [Fintype κ]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (A : κ → CMatrix a) (B : κ → CMatrix b) (w : ℝ) :
    (∑ i, (fun _ : κ => w) i • (fun k : κ => (A k, B k)) i).2 =
      ∑ k, w • B k := by
  let sndLin : (CMatrix a × CMatrix b) →ₗ[ℝ] CMatrix b :=
    { toFun := Prod.snd
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  show sndLin (∑ i, (fun _ : κ => w) i • (fun k : κ => (A k, B k)) i) =
    ∑ k, w • B k
  rw [map_sum]
  simp [sndLin]

/-- Finite uniform Jensen for the resolvent integrand in the Petz perspective
route.

This is the finite-matrix Effros/Ando step before integrating the
Audenaert-resolvent representation of `x ↦ x^α`, `1 < α ≤ 2`. -/
theorem cMatrixPetzPerspectiveResolvent_uniform_average_le
    {κ a b : Type*} [Fintype κ] [Nonempty κ]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (A : κ → CMatrix a) (B : κ → CMatrix b)
    {r coeff : ℝ} (hr : 0 < r) (hcoeff : 0 ≤ coeff)
    (hA : ∀ k, (A k).PosSemidef) (hB : ∀ k, (B k).PosDef) :
    cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r coeff
        (∑ k, ((Fintype.card κ : ℝ)⁻¹) • A k)
        (∑ k, ((Fintype.card κ : ℝ)⁻¹) • B k) ≤
      ∑ k, ((Fintype.card κ : ℝ)⁻¹) •
        cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b)
          r coeff (A k) (B k) := by
  classical
  let w : ℝ := (Fintype.card κ : ℝ)⁻¹
  have hcard_pos : 0 < (Fintype.card κ : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty κ› : 0 < Fintype.card κ)
  have hweight_nonneg :
      ∀ k ∈ (Finset.univ : Finset κ), 0 ≤ w := by
    intro _ _
    exact inv_nonneg.mpr hcard_pos.le
  have hweight_sum :
      ∑ k ∈ (Finset.univ : Finset κ), w = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    change (Fintype.card κ : ℝ) * w = 1
    dsimp [w]
    field_simp [ne_of_gt hcard_pos]
  have hmem :
      ∀ k ∈ (Finset.univ : Finset κ),
        (A k, B k) ∈
          ({P : CMatrix a × CMatrix b | P.1.PosSemidef ∧ P.2.PosDef}) := by
    intro k _
    exact ⟨hA k, hB k⟩
  have hjensen :=
    (cMatrixPetzPerspectiveResolventIntegrand_convexOn_posDef
      (a := a) (b := b) (r := r) (coeff := coeff) hr hcoeff).map_sum_le
      (t := (Finset.univ : Finset κ))
      (w := fun _ : κ => w)
      (p := fun k : κ => (A k, B k))
      hweight_nonneg hweight_sum hmem
  rw [cMatrixPetz_fst_weighted_pair_sum (A := A) (B := B) (w := w),
    cMatrixPetz_snd_weighted_pair_sum (A := A) (B := B) (w := w)] at hjensen
  simpa [w] using hjensen

/-- Loewner monotonicity after evaluating a complex matrix on a fixed
Hilbert-space vector. -/
theorem cMatrix_quadraticForm_re_mono
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : CMatrix ι} (hMN : M ≤ N) (x : ι → ℂ) :
    (dotProduct (star x) (Matrix.mulVec M x)).re ≤
      (dotProduct (star x) (Matrix.mulVec N x)).re := by
  have hdiff : (N - M).PosSemidef := Matrix.le_iff.mp hMN
  have hnonneg : 0 ≤ dotProduct (star x) (Matrix.mulVec (N - M) x) :=
    hdiff.dotProduct_mulVec_nonneg x
  have hnonneg_re :
      0 ≤ (dotProduct (star x) (Matrix.mulVec (N - M) x)).re := by
    exact (Complex.le_def.mp hnonneg).1
  have hdiff_eval :
      dotProduct (star x) (Matrix.mulVec (N - M) x) =
        dotProduct (star x) (Matrix.mulVec N x) -
          dotProduct (star x) (Matrix.mulVec M x) := by
    simp [Matrix.sub_mulVec, dotProduct_sub]
  rw [hdiff_eval, Complex.sub_re] at hnonneg_re
  linarith

/-- Quadratic forms are real-linear in a finite weighted sum of matrices. -/
theorem cMatrix_quadraticForm_re_sum_smul
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (K : κ → CMatrix ι) (w : ℝ) (x : ι → ℂ) :
    (dotProduct (star x) (Matrix.mulVec (∑ k, w • K k) x)).re =
      ∑ k, w * (dotProduct (star x) (Matrix.mulVec (K k) x)).re := by
  rw [Matrix.sum_mulVec]
  simp [dotProduct_sum, Matrix.smul_mulVec, Complex.real_smul]

/-- Hilbert-Schmidt quadratic-form version of the finite uniform Jensen step
for the Petz perspective resolvent integrand.

This is the concrete bridge from the existing matrix-valued resolvent layer to
the Petz kernel layer: any fixed Hilbert-Schmidt vector, in particular
`Matrix.vec 1`, can be evaluated against the Loewner-order Jensen inequality.
The remaining high-exponent Petz step is the explicit integral/functional
calculus identity identifying the rpow Petz kernel with the integral of these
resolvent kernels. -/
theorem cMatrixPetzPerspectiveResolvent_uniform_average_quadratic_le
    {κ a b : Type*} [Fintype κ] [Nonempty κ]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (A : κ → CMatrix a) (B : κ → CMatrix b)
    {r coeff : ℝ} (hr : 0 < r) (hcoeff : 0 ≤ coeff)
    (hA : ∀ k, (A k).PosSemidef) (hB : ∀ k, (B k).PosDef)
    (x : a × b → ℂ) :
    (dotProduct (star x)
      (Matrix.mulVec
        (cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r coeff
          (∑ k, ((Fintype.card κ : ℝ)⁻¹) • A k)
          (∑ k, ((Fintype.card κ : ℝ)⁻¹) • B k)) x)).re ≤
      (dotProduct (star x)
        (Matrix.mulVec
          (∑ k, ((Fintype.card κ : ℝ)⁻¹) •
            cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b)
              r coeff (A k) (B k)) x)).re := by
  exact cMatrix_quadraticForm_re_mono
    (cMatrixPetzPerspectiveResolvent_uniform_average_le
      (a := a) (b := b) A B hr hcoeff hA hB) x

/-- Finite uniform Jensen packaging for the matrix power map.

The hypothesis is the matrix-specialized operator-convexity input supplied by
`CFC.convexOn_rpow_one_two` for `1 ≤ α ≤ 2`.  This lemma turns that input into
the finite-uniform averaging shape used by the Petz sign-orbit bridge.  The
remaining Petz blocker is the noncommutative perspective/relative-modular step
that turns this single-variable Jensen input into joint convexity of
`Tr(A^α B^(1-α))`. -/
theorem cMatrix_rpow_uniform_average_le_uniform_average_rpow_of_convexOn
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [DecidableEq ι]
    (A : κ → CMatrix ι) {alpha : ℝ}
    (hconv :
      ConvexOn ℝ (Set.Ici (0 : CMatrix ι)) (fun X : CMatrix ι => X ^ alpha))
    (hA : ∀ k, 0 ≤ A k) :
    (∑ k, ((Fintype.card κ : ℝ)⁻¹) • A k) ^ alpha ≤
      ∑ k, ((Fintype.card κ : ℝ)⁻¹) • (A k) ^ alpha := by
  classical
  have hcard_pos : 0 < (Fintype.card κ : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty κ› : 0 < Fintype.card κ)
  have hweight_nonneg :
      ∀ k ∈ (Finset.univ : Finset κ), 0 ≤ ((Fintype.card κ : ℝ)⁻¹) := by
    intro _ _
    exact inv_nonneg.mpr hcard_pos.le
  have hweight_sum :
      ∑ k ∈ (Finset.univ : Finset κ), ((Fintype.card κ : ℝ)⁻¹) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    change (Fintype.card κ : ℝ) * (Fintype.card κ : ℝ)⁻¹ = 1
    field_simp [ne_of_gt hcard_pos]
  have hmem :
      ∀ k ∈ (Finset.univ : Finset κ), A k ∈ Set.Ici (0 : CMatrix ι) := by
    intro k _
    exact hA k
  simpa using
    hconv.map_sum_le
      (t := (Finset.univ : Finset κ))
      (w := fun _ : κ => ((Fintype.card κ : ℝ)⁻¹))
      (p := A) hweight_nonneg hweight_sum hmem

/-- The finite Jensen/joint-convexity instance needed by the sign-unitary
averaging proof of coordinate pinching monotonicity for the Petz trace. -/
def cMatrixPetzTraceSignUnitaryJensen
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (alpha : ℝ) : Prop :=
  cMatrixPetzTrace
      (((Fintype.card (ι → Bool) : ℂ)⁻¹) •
        ∑ s : ι → Bool,
          star (cMatrixSignUnitary s : CMatrix ι) * A *
            (cMatrixSignUnitary s : CMatrix ι))
      (((Fintype.card (ι → Bool) : ℂ)⁻¹) •
        ∑ s : ι → Bool,
          star (cMatrixSignUnitary s : CMatrix ι) * B *
            (cMatrixSignUnitary s : CMatrix ι))
      alpha ≤
    ∑ s : ι → Bool,
      ((Fintype.card (ι → Bool) : ℝ)⁻¹) *
        cMatrixPetzTrace
          (star (cMatrixSignUnitary s : CMatrix ι) * A *
            (cMatrixSignUnitary s : CMatrix ι))
          (star (cMatrixSignUnitary s : CMatrix ι) * B *
            (cMatrixSignUnitary s : CMatrix ι))
          alpha

/-- The sign-unitary Jensen component follows from finite uniform joint
convexity of the Petz trace, specialized to the sign orbit. -/
theorem cMatrixPetzTraceSignUnitaryJensen_of_uniformJointConvex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef) {alpha : ℝ}
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hconv :
      cMatrixPetzTraceUniformJointConvex
        (fun s : ι → Bool =>
          star (cMatrixSignUnitary s : CMatrix ι) * A *
            (cMatrixSignUnitary s : CMatrix ι))
        (fun s : ι → Bool =>
          star (cMatrixSignUnitary s : CMatrix ι) * B *
            (cMatrixSignUnitary s : CMatrix ι))
        alpha) :
    cMatrixPetzTraceSignUnitaryJensen A B alpha := by
  classical
  have hAorbit :
      ∀ s : ι → Bool,
        (star (cMatrixSignUnitary s : CMatrix ι) * A *
          (cMatrixSignUnitary s : CMatrix ι)).PosSemidef := by
    intro s
    simpa using posSemidef_unitary_conj hA (cMatrixSignUnitary s)
  have hBorbit :
      ∀ s : ι → Bool,
        (star (cMatrixSignUnitary s : CMatrix ι) * B *
          (cMatrixSignUnitary s : CMatrix ι)).PosDef := by
    intro s
    rw [Matrix.IsUnit.posDef_star_left_conjugate_iff
      (Unitary.isUnit_coe : IsUnit (cMatrixSignUnitary s : CMatrix ι))]
    exact hB
  simpa [cMatrixPetzTraceUniformJointConvex, cMatrixPetzTraceSignUnitaryJensen]
    using hconv hAorbit hBorbit halpha_gt halpha_le_two

theorem cMatrixPetzTrace_dephase_one_le_of_signUnitary_jensen
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef) {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (hJ : cMatrixPetzTraceSignUnitaryJensen A B alpha) :
    cMatrixPetzTrace (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A)
        (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B) alpha ≤
      cMatrixPetzTrace A B alpha := by
  classical
  have hAavg := cMatrixUnitaryDephase_one_eq_signAverage_of_isHermitian hA.isHermitian
  have hBavg := cMatrixUnitaryDephase_one_eq_signAverage_of_isHermitian hB.isHermitian
  have hJ' :
      cMatrixPetzTrace (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A)
          (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B) alpha ≤
        ∑ s : ι → Bool,
          ((Fintype.card (ι → Bool) : ℝ)⁻¹) *
            cMatrixPetzTrace
              (star (cMatrixSignUnitary s : CMatrix ι) * A *
                (cMatrixSignUnitary s : CMatrix ι))
              (star (cMatrixSignUnitary s : CMatrix ι) * B *
                (cMatrixSignUnitary s : CMatrix ι))
              alpha := by
    simpa [cMatrixPetzTraceSignUnitaryJensen, hAavg, hBavg] using hJ
  have hterm (s : ι → Bool) :
      cMatrixPetzTrace
          (star (cMatrixSignUnitary s : CMatrix ι) * A *
            (cMatrixSignUnitary s : CMatrix ι))
          (star (cMatrixSignUnitary s : CMatrix ι) * B *
            (cMatrixSignUnitary s : CMatrix ι))
          alpha =
        cMatrixPetzTrace A B alpha :=
    cMatrixPetzTrace_unitary_conj_eq_posSemidef_left
      A B hA hB (cMatrixSignUnitary s) halpha_nonneg
  have hweights :
      (∑ _s : ι → Bool, ((Fintype.card (ι → Bool) : ℝ)⁻¹)) = 1 := by
    have hcard_pos : 0 < (Fintype.card (ι → Bool) : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨fun _ => false⟩ :
        0 < Fintype.card (ι → Bool))
    rw [Finset.sum_const, nsmul_eq_mul]
    change (Fintype.card (ι → Bool) : ℝ) *
        (Fintype.card (ι → Bool) : ℝ)⁻¹ = 1
    field_simp [ne_of_gt hcard_pos]
  calc
    cMatrixPetzTrace (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A)
        (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B) alpha
        ≤ ∑ s : ι → Bool,
          ((Fintype.card (ι → Bool) : ℝ)⁻¹) *
            cMatrixPetzTrace
              (star (cMatrixSignUnitary s : CMatrix ι) * A *
                (cMatrixSignUnitary s : CMatrix ι))
              (star (cMatrixSignUnitary s : CMatrix ι) * B *
                (cMatrixSignUnitary s : CMatrix ι))
              alpha := hJ'
    _ = cMatrixPetzTrace A B alpha := by
      simp_rw [hterm]
      rw [← Finset.sum_mul, hweights, one_mul]

theorem cMatrixPetzTrace_unitaryDephase_le_of_coordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ} (halpha_nonneg : 0 ≤ alpha)
    (hcoord :
      let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
      let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
      cMatrixPetzTrace
          (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A')
          (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B') alpha ≤
        cMatrixPetzTrace A' B' alpha) :
    cMatrixPetzTrace (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B) alpha ≤
      cMatrixPetzTrace A B alpha := by
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
  calc
    cMatrixPetzTrace (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B) alpha =
        cMatrixPetzTrace
          (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) A')
          (cMatrixUnitaryDephase (1 : Matrix.unitaryGroup ι ℂ) B') alpha := by
          simpa [A', B'] using
            cMatrixPetzTrace_unitaryDephase_eq_coordinate_conj A B hA hB U
              (alpha := alpha)
              halpha_nonneg
    _ ≤ cMatrixPetzTrace A' B' alpha := hcoord
    _ = cMatrixPetzTrace A B alpha := by
          simpa [A', B'] using
            cMatrixPetzTrace_unitary_conj_eq_posSemidef_left A B hA hB U
              halpha_nonneg

theorem cMatrixPetzTrace_unitaryDephase_le_of_signUnitary_jensen
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ}
    (halpha_gt : 1 < alpha) (_halpha_le_two : alpha ≤ 2)
    (hJ :
      cMatrixPetzTraceSignUnitaryJensen
        (star (U : CMatrix ι) * A * (U : CMatrix ι))
        (star (U : CMatrix ι) * B * (U : CMatrix ι)) alpha) :
    cMatrixPetzTrace (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B) alpha ≤
      cMatrixPetzTrace A B alpha := by
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
  have hA' : A'.PosSemidef := by
    simpa [A'] using posSemidef_unitary_conj hA U
  have hB' : B'.PosDef := by
    dsimp [B']
    rw [Matrix.IsUnit.posDef_star_left_conjugate_iff
      (Unitary.isUnit_coe : IsUnit (U : CMatrix ι))]
    exact hB
  exact cMatrixPetzTrace_unitaryDephase_le_of_coordinate A B hA hB U
    (alpha := alpha) (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1) halpha_gt)) (by
      dsimp [A', B']
      exact cMatrixPetzTrace_dephase_one_le_of_signUnitary_jensen
        A' B' hA' hB' (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1) halpha_gt)) hJ)

theorem cMatrixPetzTrace_unitaryDephase_le_of_uniformJointConvex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ}
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hconv :
      let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
      let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
      cMatrixPetzTraceUniformJointConvex
        (fun s : ι → Bool =>
          star (cMatrixSignUnitary s : CMatrix ι) * A' *
            (cMatrixSignUnitary s : CMatrix ι))
        (fun s : ι → Bool =>
          star (cMatrixSignUnitary s : CMatrix ι) * B' *
            (cMatrixSignUnitary s : CMatrix ι))
        alpha) :
    cMatrixPetzTrace (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B) alpha ≤
      cMatrixPetzTrace A B alpha := by
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
  have hA' : A'.PosSemidef := by
    simpa [A'] using posSemidef_unitary_conj hA U
  have hB' : B'.PosDef := by
    dsimp [B']
    rw [Matrix.IsUnit.posDef_star_left_conjugate_iff
      (Unitary.isUnit_coe : IsUnit (U : CMatrix ι))]
    exact hB
  exact cMatrixPetzTrace_unitaryDephase_le_of_signUnitary_jensen
    A B hA hB U halpha_gt halpha_le_two
    (cMatrixPetzTraceSignUnitaryJensen_of_uniformJointConvex
      A' B' hA' hB' halpha_gt halpha_le_two (by simpa [A', B'] using hconv))

/-- The source Petz monotonicity input for a single unitary dephasing map.

This is the narrow noncommutative bridge still needed after the scalar
threshold and diagonal-sum bookkeeping have been discharged. -/
def cMatrixPetzTraceUnitaryDephaseMonotone
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (U : Matrix.unitaryGroup ι ℂ) (alpha : ℝ) : Prop :=
  cMatrixPetzTrace (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B) alpha ≤
    cMatrixPetzTrace A B alpha

/-- Hilbert-Schmidt kernel for the Petz trace quadratic form.

Under `Matrix.vec`, this is left multiplication by `A^α` and right
multiplication by `B^(1-α)`. It is the finite-dimensional relative-modular
entry point for the Petz quasi-entropy route. -/
def cMatrixPetzTraceKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (alpha : ℝ) : Matrix (ι × ι) (ι × ι) ℂ :=
  Matrix.kronecker (Matrix.transpose (CFC.rpow B (1 - alpha)))
    (CFC.rpow A alpha)

/-- Hilbert-Schmidt kernel for left multiplication by `A` under `Matrix.vec`. -/
def cMatrixLeftMulKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CMatrix ι) : Matrix (ι × ι) (ι × ι) ℂ :=
  Matrix.kronecker (1 : CMatrix ι) A

/-- Hilbert-Schmidt kernel for right multiplication by `B` under `Matrix.vec`. -/
def cMatrixRightMulKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : CMatrix ι) : Matrix (ι × ι) (ι × ι) ℂ :=
  Matrix.kronecker (Matrix.transpose B) (1 : CMatrix ι)

theorem cMatrixLeftMulKernel_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CMatrix ι} (hA : A.PosSemidef) :
    (cMatrixLeftMulKernel A).PosSemidef := by
  simpa [cMatrixLeftMulKernel] using Matrix.PosSemidef.one.kronecker hA

theorem cMatrixRightMulKernel_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : CMatrix ι} (hB : B.PosSemidef) :
    (cMatrixRightMulKernel B).PosSemidef := by
  simpa [cMatrixRightMulKernel] using hB.transpose.kronecker Matrix.PosSemidef.one

theorem cMatrixLeftMulKernel_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CMatrix ι} (hA : A.PosDef) :
    (cMatrixLeftMulKernel A).PosDef := by
  simpa [cMatrixLeftMulKernel] using Matrix.PosDef.one.kronecker hA

theorem cMatrixRightMulKernel_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : CMatrix ι} (hB : B.PosDef) :
    (cMatrixRightMulKernel B).PosDef := by
  simpa [cMatrixRightMulKernel] using hB.transpose.kronecker Matrix.PosDef.one

theorem cMatrixLeftRightMulKernel_commute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) :
    cMatrixLeftMulKernel A * cMatrixRightMulKernel B =
      cMatrixRightMulKernel B * cMatrixLeftMulKernel A := by
  calc
    cMatrixLeftMulKernel A * cMatrixRightMulKernel B =
        Matrix.kronecker ((1 : CMatrix ι) * Matrix.transpose B)
          (A * (1 : CMatrix ι)) := by
          simpa [cMatrixLeftMulKernel, cMatrixRightMulKernel, Matrix.kronecker]
            using
              (Matrix.mul_kronecker_mul (1 : CMatrix ι) (Matrix.transpose B)
                A (1 : CMatrix ι)).symm
    _ = Matrix.kronecker (Matrix.transpose B * (1 : CMatrix ι))
          ((1 : CMatrix ι) * A) := by
          rw [Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
    _ = cMatrixRightMulKernel B * cMatrixLeftMulKernel A := by
          simpa [cMatrixLeftMulKernel, cMatrixRightMulKernel, Matrix.kronecker]
            using
              (Matrix.mul_kronecker_mul (Matrix.transpose B) (1 : CMatrix ι)
                (1 : CMatrix ι) A)

/-- The relative-modular Hilbert-Schmidt kernel `R(B⁻¹)L(A)` as a Kronecker
matrix. -/
theorem cMatrixRightInvMulLeftKernel_eq_kronecker
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) :
    cMatrixRightMulKernel B⁻¹ * cMatrixLeftMulKernel A =
      Matrix.kronecker (Matrix.transpose B⁻¹) A := by
  calc
    cMatrixRightMulKernel B⁻¹ * cMatrixLeftMulKernel A =
        Matrix.kronecker (Matrix.transpose B⁻¹ * (1 : CMatrix ι))
          ((1 : CMatrix ι) * A) := by
          simpa [cMatrixLeftMulKernel, cMatrixRightMulKernel, Matrix.kronecker]
            using
              (Matrix.mul_kronecker_mul (Matrix.transpose B⁻¹) (1 : CMatrix ι)
                (1 : CMatrix ι) A).symm
    _ = Matrix.kronecker (Matrix.transpose B⁻¹) A := by
          simp

/-- The Kronecker-shaped Petz kernel is the product of right- and
left-multiplication Hilbert-Schmidt kernels after applying the two scalar
functional-calculus powers.

This is the concrete finite-dimensional perspective identity
`R(B)^(1-α) L(A)^α = R(B^(1-α)) L(A^α)` at the kernel level; the remaining
Step-4 analytic input is the Jensen/Loewner inequality for this powered
perspective kernel. -/
theorem cMatrixPetzTraceKernel_eq_rightLeftPowerKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (alpha : ℝ) :
    cMatrixPetzTraceKernel A B alpha =
      cMatrixRightMulKernel (CFC.rpow B (1 - alpha)) *
        cMatrixLeftMulKernel (CFC.rpow A alpha) := by
  calc
    cMatrixPetzTraceKernel A B alpha =
        Matrix.kronecker (Matrix.transpose (CFC.rpow B (1 - alpha)))
          (CFC.rpow A alpha) := by
          rfl
    _ = Matrix.kronecker
          (Matrix.transpose (CFC.rpow B (1 - alpha)) * (1 : CMatrix ι))
          ((1 : CMatrix ι) * CFC.rpow A alpha) := by
          simp
    _ = cMatrixRightMulKernel (CFC.rpow B (1 - alpha)) *
        cMatrixLeftMulKernel (CFC.rpow A alpha) := by
          simpa [cMatrixLeftMulKernel, cMatrixRightMulKernel, Matrix.kronecker]
            using
              (Matrix.mul_kronecker_mul
                (Matrix.transpose (CFC.rpow B (1 - alpha))) (1 : CMatrix ι)
                (1 : CMatrix ι) (CFC.rpow A alpha))

/-- Equivalent left/right order for the Petz powered kernel.  The two
Hilbert-Schmidt multiplication kernels commute, so the perspective kernel can
be read as `L(A^α) R(B^(1-α))` as well as `R(B^(1-α)) L(A^α)`. -/
theorem cMatrixPetzTraceKernel_eq_leftRightPowerKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (alpha : ℝ) :
    cMatrixPetzTraceKernel A B alpha =
      cMatrixLeftMulKernel (CFC.rpow A alpha) *
        cMatrixRightMulKernel (CFC.rpow B (1 - alpha)) := by
  rw [cMatrixPetzTraceKernel_eq_rightLeftPowerKernel]
  exact (cMatrixLeftRightMulKernel_commute
    (CFC.rpow A alpha) (CFC.rpow B (1 - alpha))).symm

/-- Petz trace as the quadratic form of `cMatrixPetzTraceKernel` at `vec 1`. -/
theorem cMatrixPetzTrace_eq_kernel_vec_one_re
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (alpha : ℝ) :
    cMatrixPetzTrace A B alpha =
      (dotProduct (star (Matrix.vec (1 : CMatrix ι)))
        (Matrix.mulVec (cMatrixPetzTraceKernel A B alpha)
          (Matrix.vec (1 : CMatrix ι)))).re := by
  simpa [cMatrixPetzTraceKernel] using
    cMatrixPetzTrace_eq_vec_one_kronecker_re A B alpha

private theorem cMatrixPetz_real_uniform_average_eq_complex_smul_sum
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (X : κ → CMatrix ι) :
    (∑ k, ((Fintype.card κ : ℝ)⁻¹) • X k) =
      (((Fintype.card κ : ℂ)⁻¹) • ∑ k, X k) := by
  ext i j
  have hcoeff : (((Fintype.card κ : ℝ)⁻¹ : ℝ) : ℂ) =
      ((Fintype.card κ : ℂ)⁻¹) := by
    norm_num [Complex.ofReal_inv]
  calc
    (∑ k, ((Fintype.card κ : ℝ)⁻¹) • X k) i j =
        ∑ k, (((Fintype.card κ : ℝ)⁻¹ : ℝ) : ℂ) * X k i j := by
          rw [Matrix.sum_apply]
          apply Finset.sum_congr rfl
          intro k _
          simp [Matrix.smul_apply]
    _ = ∑ k, ((Fintype.card κ : ℂ)⁻¹) * X k i j := by
          simp [hcoeff]
    _ = ((Fintype.card κ : ℂ)⁻¹) * ∑ k, X k i j := by
          rw [Finset.mul_sum]
    _ = (((Fintype.card κ : ℂ)⁻¹) • ∑ k, X k) i j := by
          change ((Fintype.card κ : ℂ)⁻¹) * ∑ k, X k i j =
            ((Fintype.card κ : ℂ)⁻¹) * ((∑ k, X k) i j)
          rw [Matrix.sum_apply]

private theorem cMatrixPetz_real_uniform_average_transpose
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (X : κ → CMatrix ι) :
    (∑ k, ((Fintype.card κ : ℝ)⁻¹) • (X k).transpose) =
      (∑ k, ((Fintype.card κ : ℝ)⁻¹) • X k).transpose := by
  ext i j
  calc
    (∑ k, ((Fintype.card κ : ℝ)⁻¹) • (X k).transpose) i j =
        ∑ k, (((Fintype.card κ : ℝ)⁻¹ : ℝ) : ℂ) * (X k j i) := by
          rw [Matrix.sum_apply]
          apply Finset.sum_congr rfl
          intro k _
          simp [Matrix.smul_apply, Matrix.transpose_apply]
    _ = (∑ k, ((Fintype.card κ : ℝ)⁻¹) • X k) j i := by
          rw [Matrix.sum_apply]
          apply Finset.sum_congr rfl
          intro k _
          simp [Matrix.smul_apply]

private theorem cMatrixPetz_reindex_le
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) {M N : CMatrix α} (hMN : M ≤ N) :
    Matrix.reindex e e M ≤ Matrix.reindex e e N := by
  have hdiff : (N - M).PosSemidef := Matrix.le_iff.mp hMN
  have hdiff_reindex : (Matrix.reindex e e (N - M)).PosSemidef := by
    simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using
      hdiff.submatrix e.symm
  have hsub :
      Matrix.reindex e e (N - M) =
        Matrix.reindex e e N - Matrix.reindex e e M := by
    ext i j
    simp [Matrix.reindex_apply, Matrix.sub_apply]
  rw [hsub] at hdiff_reindex
  exact Matrix.le_iff.mpr hdiff_reindex

private theorem cMatrixPetz_reindex_prodComm_kronecker
    {a b : Type*} [Fintype a] [Fintype b]
    (M : CMatrix a) (N : CMatrix b) :
    Matrix.reindex (Equiv.prodComm a b) (Equiv.prodComm a b)
        (Matrix.kronecker M N) =
      Matrix.kronecker N M := by
  ext x y
  cases x
  cases y
  simp [Matrix.reindex_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, mul_comm]

private theorem cMatrixPetz_reindex_finset_sum_smul
    {κ α β : Type*} [Fintype κ] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (c : ℝ) (M : κ → CMatrix α) :
    Matrix.reindex e e (∑ k, c • M k) =
      ∑ k, c • Matrix.reindex e e (M k) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.sum_apply, Matrix.smul_apply]

private theorem cMatrixPetz_submatrix_prodSwap_kronecker
    {a b : Type*} [Fintype a] [Fintype b]
    (M : CMatrix a) (N : CMatrix b) :
    (Matrix.kronecker M N).submatrix (Prod.swap : b × a → a × b) Prod.swap =
      Matrix.kronecker N M := by
  ext x y
  cases x
  cases y
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_comm]

private theorem cMatrixPetz_submatrix_prodSwap_kroneckerMap_mul
    {a b : Type*} [Fintype a] [Fintype b]
    (M : CMatrix a) (N : CMatrix b) :
    (Matrix.kroneckerMap (fun x y : ℂ => x * y) M N).submatrix
        (Prod.swap : b × a → a × b) Prod.swap =
      Matrix.kroneckerMap (fun x y : ℂ => x * y) N M := by
  ext x y
  cases x
  cases y
  simp [Matrix.kroneckerMap_apply, mul_comm]

private theorem cMatrixPetz_submatrix_prodSwap_finset_sum_smul
    {κ α β : Type*} [Fintype κ] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (c : ℝ) (M : κ → CMatrix (α × β)) :
    (∑ k, c • M k).submatrix (Prod.swap : β × α → α × β) Prod.swap =
      ∑ k, c • (M k).submatrix (Prod.swap : β × α → α × β) Prod.swap := by
  ext i j
  simp [Matrix.sum_apply, Matrix.smul_apply]

private theorem cMatrixPetz_submatrix_prodSwap_smul_finset_sum
    {κ α β : Type*} [Fintype κ] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (c : ℝ) (M : κ → CMatrix (α × β)) :
    (c • ∑ k, M k).submatrix (Prod.swap : β × α → α × β) Prod.swap =
      c • ∑ k, (M k).submatrix (Prod.swap : β × α → α × β) Prod.swap := by
  ext i j
  simp [Matrix.sum_apply, Matrix.smul_apply]

private theorem cMatrixPetz_submatrix_prodSwap_complex_smul_finset_sum
    {κ α β : Type*} [Fintype κ] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (c : ℂ) (M : κ → CMatrix (α × β)) :
    (c • ∑ k, M k).submatrix (Prod.swap : β × α → α × β) Prod.swap =
      c • ∑ k, (M k).submatrix (Prod.swap : β × α → α × β) Prod.swap := by
  ext i j
  simp [Matrix.sum_apply, Matrix.smul_apply]

private def cMatrixPetzConjStarAlgEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] : CMatrix ι ≃⋆ₐ[ℝ] CMatrix ι :=
  StarAlgEquiv.ofAlgEquiv (AlgEquiv.mapMatrix (Complex.conjAe)) (by
    intro A
    ext i j
    simp)

private theorem cMatrixPetz_map_star_eq_transpose_of_posSemidef
    {ι : Type*} {A : CMatrix ι} (hA : A.PosSemidef) :
    A.map star = A.transpose := by
  ext i j
  simpa using hA.isHermitian.apply j i

private theorem cMatrixPetz_rpow_map_star_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CMatrix ι} (hA : A.PosDef) (s : ℝ) :
    CFC.rpow (A.map star) s = (CFC.rpow A s).map star := by
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
  have hmap_eq : A.map star = A.transpose :=
    cMatrixPetz_map_star_eq_transpose_of_posSemidef hA.posSemidef
  have hmap_nonneg : 0 ≤ A.map star := by
    rw [hmap_eq]
    exact Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef.transpose
  change (A.map star) ^ s = (A ^ s).map star
  rw [CFC.rpow_eq_cfc_real (a := A.map star) (y := s) hmap_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s) hA_nonneg]
  simpa [cMatrixPetzConjStarAlgEquiv] using
    (StarAlgHomClass.map_cfc
      (cMatrixPetzConjStarAlgEquiv (ι := ι))
      (fun x : ℝ => x ^ s) A
      (hf := by
        intro x hx
        exact
          (Real.continuousAt_rpow_const x s
            (.inl (ne_of_gt
              ((Matrix.PosDef.isStrictlyPositive hA).spectrum_pos hx)))).continuousWithinAt)
      (hφ := by
        change Continuous fun A : CMatrix ι => A.map star
        fun_prop)
      (hφa := by
        change IsSelfAdjoint (A.map star)
        rw [hmap_eq]
        exact hA.posSemidef.transpose.isHermitian)).symm

private theorem cMatrixPetz_rpow_transpose_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : CMatrix ι} (hA : A.PosDef) (s : ℝ) :
    CFC.rpow A.transpose s = (CFC.rpow A s).transpose := by
  have hmapA : A.map star = A.transpose :=
    cMatrixPetz_map_star_eq_transpose_of_posSemidef hA.posSemidef
  have hpowmap :
      CFC.rpow (A.map star) s = (CFC.rpow A s).map star :=
    cMatrixPetz_rpow_map_star_posDef hA s
  have hpowPSD : (CFC.rpow A s).PosSemidef :=
    cMatrix_rpow_posSemidef (A := A) (s := s) hA.posSemidef
  have hpowmapTranspose :
      (CFC.rpow A s).map star = (CFC.rpow A s).transpose :=
    cMatrixPetz_map_star_eq_transpose_of_posSemidef hpowPSD
  rw [← hmapA, hpowmap, hpowmapTranspose]

set_option maxHeartbeats 800000 in
private theorem cMatrixPetz_rawTensorUniformJointConvex_Ioo_one_two
    {κ a b : Type*} [Fintype κ] [Nonempty κ]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (A : κ → CMatrix a) (B : κ → CMatrix b) {alpha : ℝ}
    (halpha : alpha ∈ Set.Ioo (1 : ℝ) 2)
    (hA : ∀ k, (A k).PosSemidef) (hB : ∀ k, (B k).PosDef) :
    Matrix.kronecker
        (CFC.rpow (∑ k, ((Fintype.card κ : ℝ)⁻¹) • A k) alpha)
        (CFC.rpow (∑ k, ((Fintype.card κ : ℝ)⁻¹) • B k) (1 - alpha)) ≤
      ∑ k, ((Fintype.card κ : ℝ)⁻¹) •
        Matrix.kronecker (CFC.rpow (A k) alpha) (CFC.rpow (B k) (1 - alpha)) := by
  classical
  let w : ℝ := (Fintype.card κ : ℝ)⁻¹
  let Abar : CMatrix a := ∑ k, w • A k
  let Bbar : CMatrix b := ∑ k, w • B k
  have hcard_pos : 0 < (Fintype.card κ : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty κ› : 0 < Fintype.card κ)
  have hw_pos : 0 < w := by
    dsimp [w]
    exact inv_pos.mpr hcard_pos
  have hw_nonneg : 0 ≤ w := le_of_lt hw_pos
  have hAbar : Abar.PosSemidef := by
    dsimp [Abar]
    exact Matrix.posSemidef_sum Finset.univ fun k _ =>
      Matrix.PosSemidef.smul (hA k) hw_nonneg
  have hBbar : Bbar.PosDef := by
    dsimp [Bbar]
    exact Matrix.posDef_sum Finset.univ_nonempty fun k _ =>
      Matrix.PosDef.smul (hB k) hw_pos
  obtain ⟨μ, hint, hrep⟩ :=
    cMatrixPetzPerspectiveIntegralRepresentation_Ioo_one_two
      (a := a) (b := b) (p := alpha) halpha
  let Fbar : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (alpha - 2)) •
      cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r r Abar Bbar
  let Fk : κ → ℝ → CMatrix (a × b) := fun k r =>
    (r ^ (alpha - 2)) •
      cMatrixPetzPerspectiveResolventIntegrand (a := a) (b := b) r r (A k) (B k)
  have hFbarInt : MeasureTheory.IntegrableOn Fbar (Set.Ioi 0) μ := by
    simpa [Fbar, Abar, Bbar] using hint hAbar hBbar
  have hFkInt : ∀ k, MeasureTheory.IntegrableOn (Fk k) (Set.Ioi 0) μ := by
    intro k
    simpa [Fk] using hint (hA k) (hB k)
  have hsumInt :
      MeasureTheory.IntegrableOn (fun r : ℝ => ∑ k, w • Fk k r) (Set.Ioi 0) μ := by
    have hsum :
        ∀ s : Finset κ,
          MeasureTheory.IntegrableOn (fun r : ℝ => ∑ k ∈ s, w • Fk k r)
            (Set.Ioi 0) μ := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          have hz :
              MeasureTheory.Integrable (fun _r : ℝ => (0 : CMatrix (a × b)))
                (μ.restrict (Set.Ioi 0)) :=
            MeasureTheory.integrable_zero ℝ (CMatrix (a × b)) (μ.restrict (Set.Ioi 0))
          change MeasureTheory.Integrable (fun _r : ℝ => (0 : CMatrix (a × b)))
            (μ.restrict (Set.Ioi 0))
          exact hz
      | insert k s hks ih =>
          have hk : MeasureTheory.IntegrableOn (fun r : ℝ => w • Fk k r) (Set.Ioi 0) μ := by
            have hk' : MeasureTheory.Integrable (Fk k) (μ.restrict (Set.Ioi 0)) := by
              simpa [MeasureTheory.IntegrableOn] using hFkInt k
            have hksmul : MeasureTheory.Integrable (fun r : ℝ => w • Fk k r)
                (μ.restrict (Set.Ioi 0)) := hk'.smul w
            simpa [MeasureTheory.IntegrableOn] using hksmul
          have hadd := hk.add ih
          simpa [Finset.sum_insert hks, Pi.add_apply] using hadd
    simpa using hsum (Finset.univ : Finset κ)
  have hmono :
      ∀ r ∈ Set.Ioi (0 : ℝ), Fbar r ≤ ∑ k, w • Fk k r := by
    intro r hr
    have hr_pos : 0 < r := hr
    have hbase :=
      cMatrixPetzPerspectiveResolvent_uniform_average_le
        (a := a) (b := b) A B (r := r) (coeff := r)
        hr_pos hr_pos.le hA hB
    have hscaled :=
      smul_le_smul_of_nonneg_left hbase
        (Real.rpow_nonneg hr_pos.le (alpha - 2))
    simpa [Fbar, Fk, Abar, Bbar, w, Finset.smul_sum, smul_smul,
      mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hintegral_le :
      ∫ r in Set.Ioi 0, Fbar r ∂μ ≤
        ∫ r in Set.Ioi 0, (∑ k, w • Fk k r) ∂μ :=
    cMatrixPetz_setIntegral_mono measurableSet_Ioi hFbarInt hsumInt hmono
  have hrepbar :
      Matrix.kronecker (CFC.rpow Abar alpha) (CFC.rpow Bbar (1 - alpha)) =
        ∫ r in Set.Ioi 0, Fbar r ∂μ := by
    simpa [Fbar, Abar, Bbar] using hrep hAbar hBbar
  have hrepks :
      ∀ k, Matrix.kronecker (CFC.rpow (A k) alpha) (CFC.rpow (B k) (1 - alpha)) =
        ∫ r in Set.Ioi 0, Fk k r ∂μ := by
    intro k
    simpa [Fk] using hrep (hA k) (hB k)
  have hsumIntegral :
      ∫ r in Set.Ioi 0, (∑ k, w • Fk k r) ∂μ =
        ∑ k, w • ∫ r in Set.Ioi 0, Fk k r ∂μ :=
    cMatrixPetz_setIntegral_finset_sum_smul (κ := κ) (ι := a × b)
      (μ := μ) (s := Set.Ioi 0) (f := Fk) w hFkInt
  calc
    Matrix.kronecker
        (CFC.rpow (∑ k, ((Fintype.card κ : ℝ)⁻¹) • A k) alpha)
        (CFC.rpow (∑ k, ((Fintype.card κ : ℝ)⁻¹) • B k) (1 - alpha)) =
        ∫ r in Set.Ioi 0, Fbar r ∂μ := by
          simpa [Abar, Bbar, w] using hrepbar
    _ ≤ ∫ r in Set.Ioi 0, (∑ k, w • Fk k r) ∂μ := hintegral_le
    _ = ∑ k, w • ∫ r in Set.Ioi 0, Fk k r ∂μ := hsumIntegral
    _ = ∑ k, ((Fintype.card κ : ℝ)⁻¹) •
        Matrix.kronecker (CFC.rpow (A k) alpha) (CFC.rpow (B k) (1 - alpha)) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [← hrepks k]

/-- The finite-uniform rpow-perspective Jensen statement at the Hilbert-Schmidt
kernel level.

This is the exact remaining kernel inequality produced by the
Hansen-Pedersen/Effros perspective theorem for `x ↦ x^α`, `1 < α ≤ 2`.
It is intentionally matrix-valued: `cMatrixPetzTraceUniformJointConvex` is then
obtained by evaluating this Loewner inequality on `Matrix.vec 1`. -/
def cMatrixPetzTraceKernelUniformJointConvex
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [DecidableEq ι]
    (A B : κ → CMatrix ι) (alpha : ℝ) : Prop :=
  (∀ k, (A k).PosSemidef) →
  (∀ k, (B k).PosDef) →
  1 < alpha → alpha ≤ 2 →
    cMatrixPetzTraceKernel
        (((Fintype.card κ : ℂ)⁻¹) • ∑ k, A k)
        (((Fintype.card κ : ℂ)⁻¹) • ∑ k, B k)
        alpha ≤
      ∑ k, ((Fintype.card κ : ℝ)⁻¹) •
        cMatrixPetzTraceKernel (A k) (B k) alpha

theorem cMatrixPetzTraceKernelUniformJointConvex_Ioo_one_two
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [DecidableEq ι]
    (A B : κ → CMatrix ι) {alpha : ℝ}
    (halpha : alpha ∈ Set.Ioo (1 : ℝ) 2) :
    cMatrixPetzTraceKernelUniformJointConvex A B alpha := by
  classical
  intro hA hB _halpha_gt _halpha_le_two
  let w : ℝ := (Fintype.card κ : ℝ)⁻¹
  let e : ι × ι ≃ ι × ι := Equiv.prodComm ι ι
  have hraw :=
    cMatrixPetz_rawTensorUniformJointConvex_Ioo_one_two
      (A := A) (B := fun k => (B k).transpose) (alpha := alpha) halpha
      hA (fun k => (hB k).transpose)
  have hreindex := cMatrixPetz_reindex_le (e := e) hraw
  have hcard_pos : 0 < (Fintype.card κ : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty κ› : 0 < Fintype.card κ)
  have hw_pos : 0 < w := by
    dsimp [w]
    exact inv_pos.mpr hcard_pos
  have hBbar : (∑ k, w • B k).PosDef := by
    exact Matrix.posDef_sum Finset.univ_nonempty fun k _ =>
      Matrix.PosDef.smul (hB k) hw_pos
  have hBavg_rpow :
      CFC.rpow (∑ k, ((Fintype.card κ : ℝ)⁻¹) • (B k).transpose) (1 - alpha) =
        (CFC.rpow ((((Fintype.card κ : ℂ)⁻¹) • ∑ k, B k)) (1 - alpha)).transpose := by
    rw [cMatrixPetz_real_uniform_average_transpose]
    rw [cMatrixPetz_rpow_transpose_posDef hBbar]
    rw [cMatrixPetz_real_uniform_average_eq_complex_smul_sum]
  have hBavgC_rpow :
      CFC.rpow (((Fintype.card κ : ℂ)⁻¹) • ∑ k, (B k).transpose) (1 - alpha) =
        (CFC.rpow ((((Fintype.card κ : ℂ)⁻¹) • ∑ k, B k)) (1 - alpha)).transpose := by
    rw [← cMatrixPetz_real_uniform_average_eq_complex_smul_sum
      (fun k => (B k).transpose)]
    exact hBavg_rpow
  have hBk_rpow :
      ∀ k, CFC.rpow (B k).transpose (1 - alpha) =
        (CFC.rpow (B k) (1 - alpha)).transpose := by
    intro k
    exact cMatrixPetz_rpow_transpose_posDef (hB k) (1 - alpha)
  rw [hBavg_rpow] at hreindex
  simp_rw [hBk_rpow] at hreindex
  simpa [cMatrixPetzTraceKernel, e, w,
    cMatrixPetz_reindex_prodComm_kronecker,
    cMatrixPetz_reindex_finset_sum_smul,
    cMatrixPetz_submatrix_prodSwap_kronecker,
    cMatrixPetz_submatrix_prodSwap_kroneckerMap_mul,
    cMatrixPetz_submatrix_prodSwap_finset_sum_smul,
    cMatrixPetz_submatrix_prodSwap_smul_finset_sum,
    cMatrixPetz_submatrix_prodSwap_complex_smul_finset_sum,
    cMatrixPetz_real_uniform_average_eq_complex_smul_sum,
    hBavg_rpow, hBavgC_rpow, hBk_rpow] using hreindex

private theorem cMatrixPetz_squarePerspective_uniform_average_le
    {κ n : Type*} [Fintype κ] [Nonempty κ] [Fintype n] [DecidableEq n]
    (X Y : κ → CMatrix n)
    (hX : ∀ k, (X k).IsHermitian)
    (hY : ∀ k, (Y k).PosDef) :
    let w : ℝ := (Fintype.card κ : ℝ)⁻¹
    let Xbar : CMatrix n := ∑ k, w • X k
    let Ybar : CMatrix n := ∑ k, w • Y k
    Xbar * Ybar⁻¹ * Xbar ≤ ∑ k, w • (X k * (Y k)⁻¹ * X k) := by
  classical
  let w : ℝ := (Fintype.card κ : ℝ)⁻¹
  let Xbar : CMatrix n := ∑ k, w • X k
  let Ybar : CMatrix n := ∑ k, w • Y k
  have hcard_pos : 0 < (Fintype.card κ : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty κ› : 0 < Fintype.card κ)
  have hw_pos : 0 < w := by
    dsimp [w]
    exact inv_pos.mpr hcard_pos
  have hw_nonneg : 0 ≤ w := le_of_lt hw_pos
  have hYbar : Ybar.PosDef := by
    dsimp [Ybar]
    exact Matrix.posDef_sum Finset.univ_nonempty fun k _ =>
      Matrix.PosDef.smul (hY k) hw_pos
  have hw_self : IsSelfAdjoint w := by
    rw [isSelfAdjoint_iff]
    simp
  have hXbar : Xbar.IsHermitian := by
    dsimp [Xbar]
    induction (Finset.univ : Finset κ) using Finset.induction_on with
    | empty =>
        simp
    | insert k s hks ih =>
        rw [Finset.sum_insert hks]
        exact Matrix.IsHermitian.add (Matrix.IsHermitian.smul (hX k) hw_self) ih
  have hblock_k : ∀ k,
      (Matrix.fromBlocks (X k * (Y k)⁻¹ * X k) (X k) (X k) (Y k) :
        CMatrix (Sum n n)).PosSemidef := by
    intro k
    letI : Invertible (Y k) := (hY k).isUnit.invertible
    have hschur := Matrix.PosDef.fromBlocks₂₂
      (X k * (Y k)⁻¹ * X k) (X k) (D := Y k) (hY k)
    have hblock' := hschur.mpr (by
      simpa [hX k |>.eq] using (Matrix.PosSemidef.zero : (0 : CMatrix n).PosSemidef))
    simpa [hX k |>.eq] using hblock'
  have hsumBlock :
      (∑ k, w • (Matrix.fromBlocks (X k * (Y k)⁻¹ * X k) (X k) (X k) (Y k) :
        CMatrix (Sum n n))).PosSemidef := by
    exact Matrix.posSemidef_sum Finset.univ fun k _ =>
      Matrix.PosSemidef.smul (hblock_k k) hw_nonneg
  have hblockAvg :
      (Matrix.fromBlocks (∑ k, w • (X k * (Y k)⁻¹ * X k)) Xbar Xbar Ybar :
        CMatrix (Sum n n)).PosSemidef := by
    convert hsumBlock using 1
    ext (_ | _) (_ | _) <;>
      simp [Xbar, Ybar, Matrix.sum_apply, Matrix.smul_apply, Matrix.fromBlocks_smul]
  have hschurAvg :
      ((∑ k, w • (X k * (Y k)⁻¹ * X k)) - Xbar * Ybar⁻¹ * Xbar).PosSemidef := by
    letI : Invertible Ybar := hYbar.isUnit.invertible
    have hschur := Matrix.PosDef.fromBlocks₂₂
      (∑ k, w • (X k * (Y k)⁻¹ * X k)) Xbar (D := Ybar) hYbar
    have hschur' := hschur.mp (by simpa [hXbar.eq] using hblockAvg)
    simpa [hXbar.eq] using hschur'
  exact Matrix.le_iff.mpr hschurAvg

private theorem cMatrixLeftMulKernel_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A C : CMatrix ι) :
    cMatrixLeftMulKernel A * cMatrixLeftMulKernel C =
      cMatrixLeftMulKernel (A * C) := by
  calc
    cMatrixLeftMulKernel A * cMatrixLeftMulKernel C =
        Matrix.kronecker ((1 : CMatrix ι) * (1 : CMatrix ι)) (A * C) := by
          simpa [cMatrixLeftMulKernel, Matrix.kronecker] using
            (Matrix.mul_kronecker_mul (1 : CMatrix ι) (1 : CMatrix ι) A C).symm
    _ = cMatrixLeftMulKernel (A * C) := by
          simp [cMatrixLeftMulKernel]

private theorem cMatrixRightMulKernel_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : CMatrix ι} (hB : B.PosDef) :
    (cMatrixRightMulKernel B)⁻¹ = cMatrixRightMulKernel B⁻¹ := by
  apply Matrix.inv_eq_right_inv
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit
  have hBT : B.transpose * B⁻¹.transpose = (1 : CMatrix ι) := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul B hdet]
    ext i j
    simp [Matrix.one_apply, eq_comm]
  calc
    cMatrixRightMulKernel B * cMatrixRightMulKernel B⁻¹ =
        Matrix.kronecker (B.transpose * B⁻¹.transpose)
          ((1 : CMatrix ι) * (1 : CMatrix ι)) := by
          simpa [cMatrixRightMulKernel, Matrix.kronecker] using
            (Matrix.mul_kronecker_mul B.transpose B⁻¹.transpose
              (1 : CMatrix ι) (1 : CMatrix ι)).symm
    _ = 1 := by
          rw [hBT]
          ext x y
          rcases x with ⟨x₁, x₂⟩
          rcases y with ⟨y₁, y₂⟩
          by_cases h₁ : x₁ = y₁ <;> by_cases h₂ : x₂ = y₂ <;>
          simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
            Prod.ext_iff, h₁, h₂]

private theorem cMatrixLeftMulKernel_uniform_average
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (A : κ → CMatrix ι) :
    cMatrixLeftMulKernel (((Fintype.card κ : ℂ)⁻¹) • ∑ k, A k) =
      ∑ k, ((Fintype.card κ : ℝ)⁻¹) • cMatrixLeftMulKernel (A k) := by
  rw [← cMatrixPetz_real_uniform_average_eq_complex_smul_sum A]
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  by_cases hxy : x₁ = y₁
  · subst y₁
    simp [cMatrixLeftMulKernel, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.sum_apply, Matrix.smul_apply, Finset.mul_sum]
  · simp [cMatrixLeftMulKernel, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.sum_apply, Matrix.smul_apply, hxy]

private theorem cMatrixRightMulKernel_uniform_average
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (B : κ → CMatrix ι) :
    cMatrixRightMulKernel (((Fintype.card κ : ℂ)⁻¹) • ∑ k, B k) =
      ∑ k, ((Fintype.card κ : ℝ)⁻¹) • cMatrixRightMulKernel (B k) := by
  rw [← cMatrixPetz_real_uniform_average_eq_complex_smul_sum B]
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  by_cases hxy : x₂ = y₂
  · subst y₂
    simp [cMatrixRightMulKernel, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.sum_apply, Matrix.smul_apply]
  · simp [cMatrixRightMulKernel, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.sum_apply, Matrix.smul_apply, hxy]

private theorem cMatrixPetzTraceKernel_two_eq_squarePerspective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : CMatrix ι} (hA : A.PosSemidef) (hB : B.PosDef) :
    cMatrixPetzTraceKernel A B 2 =
      cMatrixLeftMulKernel A * (cMatrixRightMulKernel B)⁻¹ *
        cMatrixLeftMulKernel A := by
  have hA_two : CFC.rpow A (2 : ℝ) = A * A := by
    simpa [pow_two] using
      (CFC.rpow_natCast A 2 (Matrix.nonneg_iff_posSemidef.mpr hA))
  have hB_neg_one : CFC.rpow B (-1 : ℝ) = B⁻¹ := by
    have h := cMatrixPetz_rpow_nonsing_inv_eq_rpow_neg hB (1 : ℝ)
    have hBpow1 : CFC.rpow B⁻¹ (1 : ℝ) = B⁻¹ :=
      CFC.rpow_one B⁻¹ (ha := Matrix.nonneg_iff_posSemidef.mpr hB.inv.posSemidef)
    rw [hBpow1] at h
    exact h.symm
  have hB_one_sub_two : CFC.rpow B (1 - (2 : ℝ)) = B⁻¹ := by
    rw [show (1 - (2 : ℝ)) = -1 by norm_num]
    exact hB_neg_one
  calc
    cMatrixPetzTraceKernel A B 2 =
        cMatrixLeftMulKernel (A * A) * cMatrixRightMulKernel B⁻¹ := by
          rw [cMatrixPetzTraceKernel_eq_leftRightPowerKernel, hA_two, hB_one_sub_two]
    _ = cMatrixLeftMulKernel A * cMatrixRightMulKernel B⁻¹ *
        cMatrixLeftMulKernel A := by
          rw [← cMatrixLeftMulKernel_mul A A]
          calc
            (cMatrixLeftMulKernel A * cMatrixLeftMulKernel A) *
                cMatrixRightMulKernel B⁻¹ =
                cMatrixLeftMulKernel A *
                  (cMatrixLeftMulKernel A * cMatrixRightMulKernel B⁻¹) := by
                  rw [Matrix.mul_assoc]
            _ = cMatrixLeftMulKernel A *
                  (cMatrixRightMulKernel B⁻¹ * cMatrixLeftMulKernel A) := by
                  rw [cMatrixLeftRightMulKernel_commute]
            _ = cMatrixLeftMulKernel A * cMatrixRightMulKernel B⁻¹ *
                  cMatrixLeftMulKernel A := by
                  rw [Matrix.mul_assoc]
    _ = cMatrixLeftMulKernel A * (cMatrixRightMulKernel B)⁻¹ *
        cMatrixLeftMulKernel A := by
          rw [cMatrixRightMulKernel_inv hB]

theorem cMatrixPetzTraceKernelUniformJointConvex_two
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [DecidableEq ι]
    (A B : κ → CMatrix ι) :
    cMatrixPetzTraceKernelUniformJointConvex A B 2 := by
  classical
  intro hA hB _halpha_gt _halpha_le_two
  let w : ℝ := (Fintype.card κ : ℝ)⁻¹
  let X : κ → CMatrix (ι × ι) := fun k => cMatrixLeftMulKernel (A k)
  let Y : κ → CMatrix (ι × ι) := fun k => cMatrixRightMulKernel (B k)
  let Abar : CMatrix ι := ((Fintype.card κ : ℂ)⁻¹) • ∑ k, A k
  let Bbar : CMatrix ι := ((Fintype.card κ : ℂ)⁻¹) • ∑ k, B k
  have hcard_pos : 0 < (Fintype.card κ : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty κ› : 0 < Fintype.card κ)
  have hw_pos : 0 < w := by
    dsimp [w]
    exact inv_pos.mpr hcard_pos
  have hw_nonneg : 0 ≤ w := le_of_lt hw_pos
  have hAbar : Abar.PosSemidef := by
    dsimp [Abar]
    rw [← cMatrixPetz_real_uniform_average_eq_complex_smul_sum A]
    exact Matrix.posSemidef_sum Finset.univ fun k _ =>
      Matrix.PosSemidef.smul (hA k) hw_nonneg
  have hBbar : Bbar.PosDef := by
    dsimp [Bbar]
    rw [← cMatrixPetz_real_uniform_average_eq_complex_smul_sum B]
    exact Matrix.posDef_sum Finset.univ_nonempty fun k _ =>
      Matrix.PosDef.smul (hB k) hw_pos
  have hsq :=
    cMatrixPetz_squarePerspective_uniform_average_le X Y
      (fun k => (cMatrixLeftMulKernel_posSemidef (hA k)).isHermitian)
      (fun k => cMatrixRightMulKernel_posDef (hB k))
  have hsq' :
      cMatrixLeftMulKernel Abar * (cMatrixRightMulKernel Bbar)⁻¹ *
          cMatrixLeftMulKernel Abar ≤
        ∑ k, w •
          (cMatrixLeftMulKernel (A k) * (cMatrixRightMulKernel (B k))⁻¹ *
            cMatrixLeftMulKernel (A k)) := by
    simpa [X, Y, Abar, Bbar, w,
      cMatrixLeftMulKernel_uniform_average,
      cMatrixRightMulKernel_uniform_average] using hsq
  have hleft :
      cMatrixPetzTraceKernel Abar Bbar 2 =
        cMatrixLeftMulKernel Abar * (cMatrixRightMulKernel Bbar)⁻¹ *
          cMatrixLeftMulKernel Abar :=
    cMatrixPetzTraceKernel_two_eq_squarePerspective hAbar hBbar
  have hright :
      ∀ k, cMatrixPetzTraceKernel (A k) (B k) 2 =
        cMatrixLeftMulKernel (A k) * (cMatrixRightMulKernel (B k))⁻¹ *
          cMatrixLeftMulKernel (A k) := by
    intro k
    exact cMatrixPetzTraceKernel_two_eq_squarePerspective (hA k) (hB k)
  calc
    cMatrixPetzTraceKernel
        (((Fintype.card κ : ℂ)⁻¹) • ∑ k, A k)
        (((Fintype.card κ : ℂ)⁻¹) • ∑ k, B k)
        2 =
        cMatrixLeftMulKernel Abar * (cMatrixRightMulKernel Bbar)⁻¹ *
          cMatrixLeftMulKernel Abar := by
          simpa [Abar, Bbar] using hleft
    _ ≤ ∑ k, w •
          (cMatrixLeftMulKernel (A k) * (cMatrixRightMulKernel (B k))⁻¹ *
            cMatrixLeftMulKernel (A k)) := hsq'
    _ = ∑ k, ((Fintype.card κ : ℝ)⁻¹) •
          cMatrixPetzTraceKernel (A k) (B k) 2 := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hright k]

theorem cMatrixPetzTraceKernelUniformJointConvex_of_rpow_perspective_one_two
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [DecidableEq ι]
    (A B : κ → CMatrix ι) {alpha : ℝ} :
    cMatrixPetzTraceKernelUniformJointConvex A B alpha := by
  classical
  intro hA hB halpha_gt halpha_le_two
  by_cases halpha_lt_two : alpha < 2
  · exact
      cMatrixPetzTraceKernelUniformJointConvex_Ioo_one_two
        A B ⟨halpha_gt, halpha_lt_two⟩ hA hB halpha_gt halpha_le_two
  · have halpha_eq_two : alpha = 2 :=
      le_antisymm halpha_le_two (le_of_not_gt halpha_lt_two)
    subst alpha
    exact cMatrixPetzTraceKernelUniformJointConvex_two
      A B hA hB (by norm_num) (by norm_num)

/-- Kernel-level finite uniform Jensen implies the scalar Petz trace
finite-uniform joint convexity used by the dephasing bridge. -/
theorem cMatrixPetzTraceUniformJointConvex_of_kernel_uniformJointConvex
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [DecidableEq ι]
    (A B : κ → CMatrix ι) {alpha : ℝ}
    (hkernel : cMatrixPetzTraceKernelUniformJointConvex A B alpha) :
    cMatrixPetzTraceUniformJointConvex A B alpha := by
  intro hA hB halpha_gt halpha_le_two
  let x : ι × ι → ℂ := Matrix.vec (1 : CMatrix ι)
  have hquad :=
    cMatrix_quadraticForm_re_mono
      (hkernel hA hB halpha_gt halpha_le_two) x
  have hsum :
      (dotProduct (star x)
        (Matrix.mulVec
          (∑ k, ((Fintype.card κ : ℝ)⁻¹) •
            cMatrixPetzTraceKernel (A k) (B k) alpha) x)).re =
        ∑ k, ((Fintype.card κ : ℝ)⁻¹) *
          cMatrixPetzTrace (A k) (B k) alpha := by
    rw [cMatrix_quadraticForm_re_sum_smul]
    simp_rw [cMatrixPetzTrace_eq_kernel_vec_one_re]
    rfl
  rw [← cMatrixPetzTrace_eq_kernel_vec_one_re
      (((Fintype.card κ : ℂ)⁻¹) • ∑ k, A k)
      (((Fintype.card κ : ℂ)⁻¹) • ∑ k, B k) alpha] at hquad
  rw [hsum] at hquad
  exact hquad

/-- Uniform joint convexity of the Petz trace from the rpow perspective route.

The resolvent layer already supplies finite Jensen for each positive
Audenaert/Effros integrand.  After the remaining rpow-perspective integral
identity has produced the corresponding Hilbert-Schmidt kernel Loewner
Jensen statement, this theorem closes the exact scalar
`cMatrixPetzTraceUniformJointConvex` shape consumed by the finite-AEP
dephasing chain. -/
theorem cMatrixPetzTraceUniformJointConvex_of_rpow_perspective_one_two
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [DecidableEq ι]
    (A B : κ → CMatrix ι) {alpha : ℝ} :
    cMatrixPetzTraceUniformJointConvex A B alpha :=
  cMatrixPetzTraceUniformJointConvex_of_kernel_uniformJointConvex
    A B (cMatrixPetzTraceKernelUniformJointConvex_of_rpow_perspective_one_two A B)

/-- The remaining Petz Jensen/monotonicity input expressed directly on the
Hilbert-Schmidt quadratic kernels.

This is intentionally narrower than full Petz quasi-entropy monotonicity: it
only asks for the vector/kernel comparison needed by the unitary pinching map
used in the TCR finite-AEP proof. -/
def cMatrixPetzTraceKernelDephaseMonotone
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (U : Matrix.unitaryGroup ι ℂ) (alpha : ℝ) : Prop :=
  (dotProduct (star (Matrix.vec (1 : CMatrix ι)))
      (Matrix.mulVec
        (cMatrixPetzTraceKernel
          (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B) alpha)
        (Matrix.vec (1 : CMatrix ι)))).re ≤
    (dotProduct (star (Matrix.vec (1 : CMatrix ι)))
      (Matrix.mulVec (cMatrixPetzTraceKernel A B alpha)
        (Matrix.vec (1 : CMatrix ι)))).re

theorem cMatrixPetzTraceUnitaryDephaseMonotone_of_kernelDephaseMonotone
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (U : Matrix.unitaryGroup ι ℂ) (alpha : ℝ)
    (hkernel : cMatrixPetzTraceKernelDephaseMonotone A B U alpha) :
    cMatrixPetzTraceUnitaryDephaseMonotone A B U alpha := by
  unfold cMatrixPetzTraceUnitaryDephaseMonotone
  rw [cMatrixPetzTrace_eq_kernel_vec_one_re
      (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B) alpha,
    cMatrixPetzTrace_eq_kernel_vec_one_re A B alpha]
  exact hkernel

/-- Sign-coordinate Jensen supplies the narrow unitary-dephasing monotonicity
predicate. -/
theorem cMatrixPetzTraceUnitaryDephaseMonotone_of_signUnitaryJensen
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ}
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hJ :
      cMatrixPetzTraceSignUnitaryJensen
        (star (U : CMatrix ι) * A * (U : CMatrix ι))
        (star (U : CMatrix ι) * B * (U : CMatrix ι)) alpha) :
    cMatrixPetzTraceUnitaryDephaseMonotone A B U alpha := by
  unfold cMatrixPetzTraceUnitaryDephaseMonotone
  exact cMatrixPetzTrace_unitaryDephase_le_of_signUnitary_jensen
    A B hA hB U halpha_gt halpha_le_two hJ

/-- Finite uniform joint convexity on the sign orbit supplies the narrow
unitary-dephasing monotonicity predicate. -/
theorem cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ}
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hconv :
      let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
      let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
      cMatrixPetzTraceUniformJointConvex
        (fun s : ι → Bool =>
          star (cMatrixSignUnitary s : CMatrix ι) * A' *
            (cMatrixSignUnitary s : CMatrix ι))
        (fun s : ι → Bool =>
          star (cMatrixSignUnitary s : CMatrix ι) * B' *
            (cMatrixSignUnitary s : CMatrix ι))
        alpha) :
    cMatrixPetzTraceUnitaryDephaseMonotone A B U alpha := by
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
  have hA' : A'.PosSemidef := by
    simpa [A'] using posSemidef_unitary_conj hA U
  have hB' : B'.PosDef := by
    dsimp [B']
    rw [Matrix.IsUnit.posDef_star_left_conjugate_iff
      (Unitary.isUnit_coe : IsUnit (U : CMatrix ι))]
    exact hB
  exact cMatrixPetzTraceUnitaryDephaseMonotone_of_signUnitaryJensen
    A B hA hB U halpha_gt halpha_le_two
    (cMatrixPetzTraceSignUnitaryJensen_of_uniformJointConvex
      A' B' hA' hB' halpha_gt halpha_le_two (by simpa [A', B'] using hconv))

/-- A global finite-uniform Petz joint-convexity input supplies the narrow
unitary-dephasing monotonicity predicate for any finite matrix pair.

This wrapper is intentionally light: it composes the already-proved sign-orbit
pinching bridge with a reusable universal joint-convexity hypothesis.  The
remaining analytic theorem is the production of `hjoint` from the Petz
perspective/operator-convexity route for `1 < α ≤ 2`. -/
theorem cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex_all
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ}
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hjoint :
      ∀ {κ : Type w} [Fintype κ] [Nonempty κ],
        (Aκ Bκ : κ → CMatrix ι) →
          cMatrixPetzTraceUniformJointConvex Aκ Bκ alpha) :
    cMatrixPetzTraceUnitaryDephaseMonotone A B U alpha :=
  cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex
    A B hA hB U halpha_gt halpha_le_two
    (by
      let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
      let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
      simpa [A', B'] using
        hjoint (κ := ι → Bool)
          (fun s : ι → Bool =>
            star (cMatrixSignUnitary s : CMatrix ι) * A' *
              (cMatrixSignUnitary s : CMatrix ι))
          (fun s : ι → Bool =>
            star (cMatrixSignUnitary s : CMatrix ι) * B' *
              (cMatrixSignUnitary s : CMatrix ι)))

/-- Petz trace is monotone under unitary dephasing for `1 < α ≤ 2`, using the
finite-dimensional rpow perspective/Jensen theorem. -/
theorem cMatrixPetzTraceUnitaryDephaseMonotone_of_rpow_perspective_one_two
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ}
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2) :
    cMatrixPetzTraceUnitaryDephaseMonotone A B U alpha :=
  cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex_all
    A B hA hB U halpha_gt halpha_le_two
    (fun {κ} [Fintype κ] [Nonempty κ] (Aκ Bκ : κ → CMatrix ι) =>
      cMatrixPetzTraceUniformJointConvex_of_rpow_perspective_one_two Aκ Bκ)

/-- Petz trace of the dephased pair is exactly the source diagonal sum.

This discharges the unitary-basis, CFC-power, and trace bookkeeping around TCR
lines 664--670. The remaining mathematical input is the Petz quasi-entropy
monotonicity inequality comparing this dephased Petz trace with the original
noncommutative Petz trace. -/
theorem cMatrix_petzTrace_unitaryDephase_eq_diag_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) (alpha : ℝ) :
    ((CFC.rpow (cMatrixUnitaryDephase U A) alpha *
        CFC.rpow (cMatrixUnitaryDephase U B) (1 - alpha)).trace).re =
      ∑ i,
        ((star (U : CMatrix ι) * A * (U : CMatrix ι)) i i).re ^ alpha *
          ((star (U : CMatrix ι) * B * (U : CMatrix ι)) i i).re ^
            (1 - alpha) := by
  classical
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
  let a : ι → ℝ := fun i => (A' i i).re
  let b : ι → ℝ := fun i => (B' i i).re
  have ha_nonneg : ∀ i, 0 ≤ a i := by
    intro i
    simpa [A', a] using posSemidef_unitary_conj_diag_re_nonneg hA U i
  have hb_nonneg : ∀ i, 0 ≤ b i := by
    intro i
    exact le_of_lt (by
      simpa [B', b] using posDef_unitary_conj_diag_re_pos hB U i)
  have hApow :
      CFC.rpow (cMatrixUnitaryDephase U A) alpha =
        (U : CMatrix ι) *
          (Matrix.diagonal fun i => (((a i) ^ alpha : ℝ) : ℂ) : CMatrix ι) *
            star (U : CMatrix ι) := by
    unfold cMatrixUnitaryDephase
    simpa [A', a] using
      cMatrix_rpow_unitary_conj_diagonal_ofReal U a ha_nonneg alpha
  have hBpow :
      CFC.rpow (cMatrixUnitaryDephase U B) (1 - alpha) =
        (U : CMatrix ι) *
          (Matrix.diagonal fun i => (((b i) ^ (1 - alpha) : ℝ) : ℂ) :
            CMatrix ι) *
            star (U : CMatrix ι) := by
    unfold cMatrixUnitaryDephase
    simpa [B', b] using
      cMatrix_rpow_unitary_conj_diagonal_ofReal U b hb_nonneg (1 - alpha)
  rw [hApow, hBpow]
  simpa [A', B', a, b] using
    trace_mul_unitary_conj_diagonal_ofReal_re U
      (fun i => (a i) ^ alpha) (fun i => (b i) ^ (1 - alpha))

/-- Source-facing dephasing/Petz comparison with the true monotonicity step as
an explicit hypothesis.

The hypothesis is exactly the Petz quasi-entropy monotonicity for the pinching
map in TCR lines 664--670, specialized to `g(t)=t^alpha` and the unitary basis
`U`. This theorem removes the scalar/unitary/reindex bookkeeping from callers:
from that monotonicity statement it returns the diagonal-sum comparison used by
the positive-part trace bound. -/
theorem cMatrix_dephased_eigenbasis_sum_le_petzTrace_of_dephasing_monotonicity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (U : Matrix.unitaryGroup ι ℂ) {alpha : ℝ}
    (_halpha_gt : 1 < alpha) (_halpha_le_two : alpha ≤ 2)
    (hmono :
      ((CFC.rpow (cMatrixUnitaryDephase U A) alpha *
          CFC.rpow (cMatrixUnitaryDephase U B) (1 - alpha)).trace).re ≤
        ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re) :
    let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
    let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
    ∑ i, (A' i i).re ^ alpha * (B' i i).re ^ (1 - alpha) ≤
      ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re := by
  classical
  dsimp
  rw [← cMatrix_petzTrace_unitaryDephase_eq_diag_sum A B hA hB U alpha]
  exact hmono

/-- Source-shaped scalar/eigenbasis part of the TCR positive-part trace step.

For `H = A - λB`, diagonalize `H` and set
`r_i = ⟨ψ_i,Aψ_i⟩`, `s_i = ⟨ψ_i,Bψ_i⟩`.  This proves the threshold estimate up
to the dephasing/Petz monotonicity comparison
`∑ r_i^α s_i^(1-α) ≤ Tr(A^α B^(1-α))`. -/
theorem cMatrix_posPart_trace_re_le_scaled_dephased_eigenbasis_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    {lambda alpha : ℝ} (hlambda : 0 < lambda)
    (halpha_gt : 1 < alpha)
    (hH : (A - lambda • B).IsHermitian) :
    let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
    let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
    let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
    ((A - lambda • B)⁺).trace.re ≤
      lambda ^ (1 - alpha) *
        ∑ i, (A' i i).re ^ alpha * (B' i i).re ^ (1 - alpha) := by
  classical
  let H : CMatrix ι := A - lambda • B
  let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
  let p : ι → ℝ := fun i => if 0 < hH.eigenvalues i then 1 else 0
  have hp_nonneg : ∀ i, 0 ≤ p i := by
    intro i
    by_cases hi : 0 < hH.eigenvalues i <;> simp [p, hi]
  have hp_le_one : ∀ i, p i ≤ 1 := by
    intro i
    by_cases hi : 0 < hH.eigenvalues i <;> simp [p, hi]
  have hA_diag_nonneg : ∀ i, 0 ≤ (A' i i).re := by
    intro i
    simpa [A'] using posSemidef_unitary_conj_diag_re_nonneg hA U i
  have hB_diag_pos : ∀ i, 0 < (B' i i).re := by
    intro i
    simpa [B'] using posDef_unitary_conj_diag_re_pos hB U i
  have hHdiag (i : ι) :
      ((star (U : CMatrix ι) * H * (U : CMatrix ι)) i i).re =
        (A' i i).re - lambda * (B' i i).re := by
    have hmat :
        star (U : CMatrix ι) * H * (U : CMatrix ι) =
          A' - lambda • B' := by
      dsimp [H, A', B']
      noncomm_ring
    rw [hmat]
    simp [Complex.real_smul]
  have htrace_projector :
      ((H * positiveSpectralProjector H hH).trace).re =
        ∑ i, (((star (U : CMatrix ι) * H * (U : CMatrix ι)) i i).re * p i) := by
    unfold positiveSpectralProjector
    have hmask :
        (Matrix.diagonal (fun i =>
          if 0 < hH.eigenvalues i then (1 : ℂ) else 0) : CMatrix ι) =
            Matrix.diagonal (fun i => ((p i : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        by_cases hi : 0 < hH.eigenvalues i <;> simp [p, hi]
      · simp [Matrix.diagonal, hij]
    rw [hmask]
    have htrace := trace_mul_unitary_diagonal_conj_re H U p
    have hdiag :=
      trace_mul_diagonal_ofReal_re
        (star (U : CMatrix ι) * H * (U : CMatrix ι)) p
    simpa [H, U] using htrace.trans hdiag
  have hpos_trace :
      ((A - lambda • B)⁺).trace.re =
        ∑ i, p i * ((A' i i).re - lambda * (B' i i).re) := by
    have hscore := positiveSpectralProjector_score_eq_posPart_trace H hH
    calc
      ((A - lambda • B)⁺).trace.re = (H⁺).trace.re := by rfl
      _ = ((H * positiveSpectralProjector H hH).trace).re := hscore.symm
      _ = ∑ i, (((star (U : CMatrix ι) * H * (U : CMatrix ι)) i i).re * p i) :=
          htrace_projector
      _ = ∑ i, p i * ((A' i i).re - lambda * (B' i i).re) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hHdiag i]
          ring
  calc
    ((A - lambda • B)⁺).trace.re =
        ∑ i, p i * ((A' i i).re - lambda * (B' i i).re) := hpos_trace
    _ ≤ ∑ i, lambda ^ (1 - alpha) *
        ((A' i i).re ^ alpha * (B' i i).re ^ (1 - alpha)) :=
          Finset.sum_le_sum fun i _ =>
            scalar_effect_threshold_le_scaled_petz (hp_nonneg i) (hp_le_one i)
              (hA_diag_nonneg i) (hB_diag_pos i) hlambda (le_of_lt halpha_gt)
    _ = lambda ^ (1 - alpha) *
        ∑ i, (A' i i).re ^ alpha * (B' i i).re ^ (1 - alpha) := by
          rw [Finset.mul_sum]

/-- Positive-part trace bound from the source scalar threshold plus the
remaining Petz monotonicity/dephasing comparison. -/
theorem cMatrix_posPart_trace_re_le_scaled_petzTrace_of_dephased_eigenbasis_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    {lambda alpha : ℝ} (hlambda : 0 < lambda)
    (halpha_gt : 1 < alpha) (_halpha_le_two : alpha ≤ 2)
    (hH : (A - lambda • B).IsHermitian)
    (hdephase :
      let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
      let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
      let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
      ∑ i, (A' i i).re ^ alpha * (B' i i).re ^ (1 - alpha) ≤
        ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re) :
    ((A - lambda • B)⁺).trace.re ≤
      lambda ^ (1 - alpha) *
        ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re := by
  classical
  let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
  let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
  let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
  have hscalar :
      ((A - lambda • B)⁺).trace.re ≤
        lambda ^ (1 - alpha) *
          ∑ i, (A' i i).re ^ alpha * (B' i i).re ^ (1 - alpha) := by
    simpa [U, A', B'] using
      cMatrix_posPart_trace_re_le_scaled_dephased_eigenbasis_sum
        A B hA hB hlambda halpha_gt hH
  have hlambda_pow_nonneg : 0 ≤ lambda ^ (1 - alpha) := by
    positivity
  exact hscalar.trans (mul_le_mul_of_nonneg_left hdephase hlambda_pow_nonneg)

/-- Positive-part trace bound from the source scalar threshold plus Petz
quasi-entropy monotonicity for the dephasing/pinching map.

Compared with
`cMatrix_posPart_trace_re_le_scaled_petzTrace_of_dephased_eigenbasis_bound`,
this exposes the remaining source input in its Petz form: monotonicity says the
Petz trace cannot increase after dephasing in the eigenbasis of `A - λB`. -/
theorem cMatrix_posPart_trace_re_le_scaled_petzTrace_of_dephasing_monotonicity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    {lambda alpha : ℝ} (hlambda : 0 < lambda)
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hH : (A - lambda • B).IsHermitian)
    (hmono :
      let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
      ((CFC.rpow (cMatrixUnitaryDephase U A) alpha *
          CFC.rpow (cMatrixUnitaryDephase U B) (1 - alpha)).trace).re ≤
        ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re) :
    ((A - lambda • B)⁺).trace.re ≤
      lambda ^ (1 - alpha) *
        ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re := by
  classical
  let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
  have hdephase :
      let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
      let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
      ∑ i, (A' i i).re ^ alpha * (B' i i).re ^ (1 - alpha) ≤
        ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re := by
    exact cMatrix_dephased_eigenbasis_sum_le_petzTrace_of_dephasing_monotonicity
      A B hA hB U halpha_gt halpha_le_two (by simpa [U] using hmono)
  exact cMatrix_posPart_trace_re_le_scaled_petzTrace_of_dephased_eigenbasis_bound
    A B hA hB hlambda halpha_gt halpha_le_two hH (by simpa [U] using hdephase)

/-- Positive-part trace bound with the remaining dephasing monotonicity input
packaged through `cMatrixPetzTrace`. -/
theorem cMatrix_posPart_trace_re_le_scaled_cMatrixPetzTrace_of_dephasing_monotonicity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    {lambda alpha : ℝ} (hlambda : 0 < lambda)
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hH : (A - lambda • B).IsHermitian)
    (hmono :
      let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
      cMatrixPetzTrace (cMatrixUnitaryDephase U A) (cMatrixUnitaryDephase U B) alpha ≤
        cMatrixPetzTrace A B alpha) :
    ((A - lambda • B)⁺).trace.re ≤
      lambda ^ (1 - alpha) * cMatrixPetzTrace A B alpha := by
  exact cMatrix_posPart_trace_re_le_scaled_petzTrace_of_dephasing_monotonicity
    A B hA hB hlambda halpha_gt halpha_le_two hH (by
      simpa [cMatrixPetzTrace] using hmono)

/-- Positive-part trace bound from the narrow unitary-dephasing monotonicity
predicate. -/
theorem cMatrix_posPart_trace_re_le_scaled_petzTrace_of_unitaryDephaseMonotone
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    {lambda alpha : ℝ} (hlambda : 0 < lambda)
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hH : (A - lambda • B).IsHermitian)
    (hmono :
      let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceUnitaryDephaseMonotone A B U alpha) :
    ((A - lambda • B)⁺).trace.re ≤
      lambda ^ (1 - alpha) * cMatrixPetzTrace A B alpha := by
  exact cMatrix_posPart_trace_re_le_scaled_cMatrixPetzTrace_of_dephasing_monotonicity
    A B hA hB hlambda halpha_gt halpha_le_two hH (by
      simpa [cMatrixPetzTraceUnitaryDephaseMonotone] using hmono)

/-- Positive-part trace bound from the Hilbert-Schmidt kernel form of the
remaining Petz dephasing monotonicity input. -/
theorem cMatrix_posPart_trace_re_le_scaled_petzTrace_of_kernelDephaseMonotone
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    {lambda alpha : ℝ} (hlambda : 0 < lambda)
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hH : (A - lambda • B).IsHermitian)
    (hkernel :
      let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
      cMatrixPetzTraceKernelDephaseMonotone A B U alpha) :
    ((A - lambda • B)⁺).trace.re ≤
      lambda ^ (1 - alpha) * cMatrixPetzTrace A B alpha := by
  let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
  have hmono :
      cMatrixPetzTraceUnitaryDephaseMonotone A B U alpha :=
    cMatrixPetzTraceUnitaryDephaseMonotone_of_kernelDephaseMonotone
      A B U alpha (by simpa [U] using hkernel)
  exact cMatrix_posPart_trace_re_le_scaled_petzTrace_of_unitaryDephaseMonotone
    A B hA hB hlambda halpha_gt halpha_le_two hH (by simpa [U] using hmono)

/-- Positive-part trace bound with the remaining noncommutative input packaged
as finite uniform joint convexity on the sign orbit of the eigenbasis of
`A - λB`. -/
theorem cMatrix_posPart_trace_re_le_scaled_petzTrace_of_uniformJointConvex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    {lambda alpha : ℝ} (hlambda : 0 < lambda)
    (halpha_gt : 1 < alpha) (halpha_le_two : alpha ≤ 2)
    (hconv :
      let H : CMatrix ι := A - lambda • B
      let hH : H.IsHermitian :=
        hA.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
      let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
      let A' : CMatrix ι := star (U : CMatrix ι) * A * (U : CMatrix ι)
      let B' : CMatrix ι := star (U : CMatrix ι) * B * (U : CMatrix ι)
      cMatrixPetzTraceUniformJointConvex
        (fun s : ι → Bool =>
          star (cMatrixSignUnitary s : CMatrix ι) * A' *
            (cMatrixSignUnitary s : CMatrix ι))
        (fun s : ι → Bool =>
          star (cMatrixSignUnitary s : CMatrix ι) * B' *
            (cMatrixSignUnitary s : CMatrix ι))
        alpha) :
    ((A - lambda • B)⁺).trace.re ≤
      lambda ^ (1 - alpha) * cMatrixPetzTrace A B alpha := by
  let H : CMatrix ι := A - lambda • B
  have hH : H.IsHermitian := by
    dsimp [H]
    exact hA.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
  let U : Matrix.unitaryGroup ι ℂ := hH.eigenvectorUnitary
  have hmono :
      cMatrixPetzTraceUnitaryDephaseMonotone A B U alpha :=
    cMatrixPetzTraceUnitaryDephaseMonotone_of_uniformJointConvex
      A B hA hB U halpha_gt halpha_le_two (by
        simpa [H, hH, U] using hconv)
  exact cMatrix_posPart_trace_re_le_scaled_petzTrace_of_unitaryDephaseMonotone
    A B hA hB hlambda halpha_gt halpha_le_two hH (by
      simpa [U] using hmono)

/-- Checked commutative/simultaneously diagonal bridge for the Petz
effect-variational inequality.

This does not close the noncommutative `A,B` bridge, but it proves the exact
predicate when `A` and `B` are positive diagonal in one unitary basis. -/
theorem cMatrixPetzTraceEffectVariational_of_simultaneously_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (U : Matrix.unitaryGroup ι ℂ) (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    {lambda alpha : ℝ} (hlambda : 0 < lambda)
    (halpha_gt : 1 < alpha)
    (hA :
      A = (U : CMatrix ι) *
        (Matrix.diagonal fun i => ((a i : ℝ) : ℂ) : CMatrix ι) *
          star (U : CMatrix ι))
    (hB :
      B = (U : CMatrix ι) *
        (Matrix.diagonal fun i => ((b i : ℝ) : ℂ) : CMatrix ι) *
          star (U : CMatrix ι)) :
    cMatrixPetzTraceEffectVariational A B lambda alpha := by
  intro E hEpos hEle
  let E' : CMatrix ι := star (U : CMatrix ι) * E * (U : CMatrix ι)
  have hE'pos : E'.PosSemidef := by
    simpa [E'] using posSemidef_unitary_conj hEpos U
  have hE'le : E' ≤ 1 := by
    rw [Matrix.le_iff]
    have hdiff : ((1 : CMatrix ι) - E).PosSemidef := by
      simpa [Matrix.le_iff] using hEle
    have hconj : (star (U : CMatrix ι) * ((1 : CMatrix ι) - E) *
        (U : CMatrix ι)).PosSemidef := by
      simpa using posSemidef_unitary_conj hdiff U
    have hmatrix :
        star (U : CMatrix ι) * ((1 : CMatrix ι) - E) * (U : CMatrix ι) =
          (1 : CMatrix ι) - E' := by
      dsimp [E']
      have hU : star (U : CMatrix ι) * (U : CMatrix ι) = 1 := by
        exact Unitary.coe_star_mul_self U
      calc
        star (U : CMatrix ι) * ((1 : CMatrix ι) - E) * (U : CMatrix ι) =
            star (U : CMatrix ι) * (1 : CMatrix ι) * (U : CMatrix ι) -
              star (U : CMatrix ι) * E * (U : CMatrix ι) := by
              noncomm_ring
        _ = (1 : CMatrix ι) - star (U : CMatrix ι) * E * (U : CMatrix ι) := by
              rw [Matrix.mul_one, hU]
    simpa [hmatrix] using hconj
  have hdiag_nonneg : ∀ i, 0 ≤ (E' i i).re :=
    fun i => posSemidef_diagonal_re_nonneg hE'pos i
  have hdiag_le_one : ∀ i, (E' i i).re ≤ 1 := by
    intro i
    have hcompl : ((1 : CMatrix ι) - E').PosSemidef := by
      simpa [Matrix.le_iff] using hE'le
    have hnonneg := posSemidef_diagonal_re_nonneg hcompl i
    have hentry :
        (((1 : CMatrix ι) - E') i i).re = 1 - (E' i i).re := by
      simp
    linarith
  have hEA :
      ((E * A).trace).re = ∑ i, (E' i i).re * a i := by
    rw [hA]
    rw [trace_mul_unitary_diagonal_conj_re]
    exact trace_mul_diagonal_ofReal_re E' a
  have hEB :
      ((E * B).trace).re = ∑ i, (E' i i).re * b i := by
    rw [hB]
    rw [trace_mul_unitary_diagonal_conj_re]
    exact trace_mul_diagonal_ofReal_re E' b
  have hApow :
      CFC.rpow A alpha =
        (U : CMatrix ι) *
          (Matrix.diagonal fun i => (((a i) ^ alpha : ℝ) : ℂ) : CMatrix ι) *
            star (U : CMatrix ι) := by
    rw [hA]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal U a (fun i => le_of_lt (ha i)) alpha
  have hBpow :
      CFC.rpow B (1 - alpha) =
        (U : CMatrix ι) *
          (Matrix.diagonal fun i => (((b i) ^ (1 - alpha) : ℝ) : ℂ) : CMatrix ι) *
            star (U : CMatrix ι) := by
    rw [hB]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal U b (fun i => le_of_lt (hb i))
      (1 - alpha)
  have hpetz :
      ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re =
        ∑ i, (a i) ^ alpha * (b i) ^ (1 - alpha) := by
    rw [hApow, hBpow]
    simpa using trace_mul_unitary_conj_diagonal_ofReal_re U
      (fun i => (a i) ^ alpha) (fun i => (b i) ^ (1 - alpha))
  have hsum :
      (∑ i, (E' i i).re * a i) -
          lambda * (∑ i, (E' i i).re * b i) ≤
        lambda ^ (1 - alpha) *
          (∑ i, (a i) ^ alpha * (b i) ^ (1 - alpha)) := by
    calc
      (∑ i, (E' i i).re * a i) -
          lambda * (∑ i, (E' i i).re * b i)
          = ∑ i, (E' i i).re * (a i - lambda * b i) := by
              rw [Finset.mul_sum]
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ ≤ ∑ i, lambda ^ (1 - alpha) * ((a i) ^ alpha * (b i) ^ (1 - alpha)) :=
          Finset.sum_le_sum fun i _ =>
            scalar_effect_threshold_le_scaled_petz (hdiag_nonneg i) (hdiag_le_one i)
              (le_of_lt (ha i)) (hb i) hlambda (le_of_lt halpha_gt)
      _ = lambda ^ (1 - alpha) *
          (∑ i, (a i) ^ alpha * (b i) ^ (1 - alpha)) := by
            rw [Finset.mul_sum]
  rw [hEA, hEB, hpetz]
  exact hsum

/-- Reduction from the Petz effect-variational inequality to the desired
positive-part trace threshold inequality. -/
theorem cMatrix_posPart_trace_re_le_scaled_petzTrace_of_effect_variational
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : CMatrix ι) (hA : A.PosSemidef) (hB : B.PosDef)
    {lambda alpha : ℝ} (hlambda : 0 < lambda)
    (_halpha_gt : 1 < alpha) (_halpha_le_two : alpha ≤ 2)
    (hvar : cMatrixPetzTraceEffectVariational A B lambda alpha) :
    ((A - lambda • B)⁺).trace.re ≤
      lambda ^ (1 - alpha) *
        ((CFC.rpow A alpha * CFC.rpow B (1 - alpha)).trace).re := by
  let H : CMatrix ι := A - lambda • B
  have hH : H.IsHermitian := by
    dsimp [H]
    exact hA.isHermitian.sub ((Matrix.PosDef.smul hB hlambda).isHermitian)
  let P : CMatrix ι := positiveSpectralProjector H hH
  have hPpos : P.PosSemidef := by
    simpa [P] using positiveSpectralProjector_posSemidef H hH
  have hPle : P ≤ 1 := by
    simpa [P] using positiveSpectralProjector_le_one H hH
  have hvarP := hvar P hPpos hPle
  have htrace :
      (((P * A).trace).re - lambda * ((P * B).trace).re) =
        ((P * H).trace).re := by
    dsimp [H]
    simp [Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_smul,
      Complex.real_smul]
  have hscore :
      ((P * H).trace).re = (H⁺).trace.re := by
    have h := positiveSpectralProjector_score_eq_posPart_trace H hH
    rw [Matrix.trace_mul_comm] at h
    simpa [P] using h
  simpa [H] using (hscore ▸ htrace ▸ hvarP)

end

end QIT
