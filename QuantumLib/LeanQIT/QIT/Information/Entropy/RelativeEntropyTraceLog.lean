/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy.Entropy
public import QIT.States.Schatten
public import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Trace-log quantum relative entropy

Low-level definitions for the ordinary/Umegaki relative entropy with the
support convention: the trace-log branch is used on supported inputs, and
`+infty` otherwise.

This module intentionally contains only the definitions and immediate branch
facts.  The right-limit bridge from sandwiched Renyi and the data-processing
proofs live in `QIT.Information.Entropy.RelativeEntropyDPI`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QIT

universe u

noncomputable section

noncomputable local instance cMatrixCStarAlgebraForRelativeEntropyTraceLog
    {n : Type*} [Fintype n] [DecidableEq n] : CStarAlgebra (CMatrix n) := {}

namespace Matrix

private theorem relativeEntropyTraceLog_roots_X_pow_map_re_xlog2_sum_zero (n : ℕ) :
    ((Polynomial.X ^ n : Polynomial ℂ).roots.map (fun z : ℂ => xlog2 z.re)).sum = 0 := by
  rw [Polynomial.roots_X_pow, Multiset.map_nsmul, Multiset.sum_nsmul,
    Multiset.map_singleton, Multiset.sum_singleton]
  simp [xlog2]

private theorem relativeEntropyTraceLog_roots_re_xlog2_sum_eq_of_X_pow_mul_eq
    {P Q : Polynomial ℂ} {m n : ℕ} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : Polynomial.X ^ m * P = Polynomial.X ^ n * Q) :
    (P.roots.map (fun z : ℂ => xlog2 z.re)).sum =
      (Q.roots.map (fun z : ℂ => xlog2 z.re)).sum := by
  have hXm : (Polynomial.X ^ m : Polynomial ℂ) ≠ 0 := by simp
  have hXn : (Polynomial.X ^ n : Polynomial ℂ) ≠ 0 := by simp
  have hleft_ne : (Polynomial.X ^ m : Polynomial ℂ) * P ≠ 0 := mul_ne_zero hXm hP
  have hright_ne : (Polynomial.X ^ n : Polynomial ℂ) * Q ≠ 0 := mul_ne_zero hXn hQ
  have hroots := congrArg Polynomial.roots h
  rw [Polynomial.roots_mul hleft_ne, Polynomial.roots_mul hright_ne] at hroots
  have hsum :=
    congrArg (fun s : Multiset ℂ => (s.map (fun z : ℂ => xlog2 z.re)).sum) hroots
  simp only [Multiset.map_add, Multiset.sum_add] at hsum
  rw [relativeEntropyTraceLog_roots_X_pow_map_re_xlog2_sum_zero m,
    relativeEntropyTraceLog_roots_X_pow_map_re_xlog2_sum_zero n] at hsum
  simpa using hsum

end Matrix

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]

theorem relativeEntropyTraceLog_vonNeumann_psdSupportCompressedState_eq
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma) :
    (_root_.QIT.psdSupportCompressedState rho hSigma hSupport).vonNeumann =
      rho.vonNeumann := by
  classical
  let rhoC : State (psdSupportIndex sigma hSigma) :=
    _root_.QIT.psdSupportCompressedState rho hSigma hSupport
  let V : Matrix a (psdSupportIndex sigma hSigma) ℂ := psdSupportIsometry sigma hSigma
  have hV : Matrix.conjTranspose V * V = (1 : CMatrix (psdSupportIndex sigma hSigma)) := by
    simpa [V] using psdSupportIsometry_isometry sigma hSigma
  have hrec : V * rhoC.matrix * Matrix.conjTranspose V = rho.matrix := by
    simpa [V, rhoC] using
      psdSupportCompress_reconstruct_of_supports
        (M := rho.matrix) (N := sigma) rho.pos hSigma hSupport
  rw [State.vonNeumann_eq_neg_sum_eigenvalueMultiset,
    State.vonNeumann_eq_neg_sum_eigenvalueMultiset]
  have hpoly := Matrix.charpoly_isometry_conj (V := V) rhoC.matrix hV
  rw [hrec] at hpoly
  have hP : rho.matrix.charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hQ : rhoC.matrix.charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hroot :=
    Matrix.relativeEntropyTraceLog_roots_re_xlog2_sum_eq_of_X_pow_mul_eq
      (P := rho.matrix.charpoly) (Q := rhoC.matrix.charpoly) hP hQ hpoly
  have hrootsRho := rho.pos.isHermitian.roots_charpoly_eq_eigenvalues
  have hrootsRhoC := rhoC.pos.isHermitian.roots_charpoly_eq_eigenvalues
  rw [hrootsRho, hrootsRhoC] at hroot
  have hsum :
      ((eigenvalueMultiset rhoC.pos.isHermitian).map xlog2).sum =
        ((eigenvalueMultiset rho.pos.isHermitian).map xlog2).sum := by
    simpa [eigenvalueMultiset, Multiset.map_map, Function.comp_def] using hroot.symm
  rw [hsum]

private theorem relativeEntropyTraceLog_psdSupportLog_embedding_eq_cfc_logZero
    (sigma : CMatrix a) (hSigma : sigma.PosSemidef) :
    let V : Matrix a (psdSupportIndex sigma hSigma) ℂ := psdSupportIsometry sigma hSigma
    V * State.psdLog (psdSupportCompress sigma hSigma sigma)
        (psdSupportCompress_self_posDef sigma hSigma) *
        Matrix.conjTranspose V =
      cfc (fun x : ℝ => if x = 0 then 0 else Real.log x) sigma := by
  classical
  let V : Matrix a (psdSupportIndex sigma hSigma) ℂ := psdSupportIsometry sigma hSigma
  let U : Matrix.unitaryGroup a ℂ := hSigma.isHermitian.eigenvectorUnitary
  let d : a → ℝ := hSigma.isHermitian.eigenvalues
  let f : ℝ → ℝ := fun x => if x = 0 then 0 else Real.log x
  have hSigmaSpec :
      sigma = (U : CMatrix a) * (Matrix.diagonal fun i => ((d i : ℝ) : ℂ)) *
        star (U : CMatrix a) := by
    simpa [U, d, Matrix.IsHermitian.spectral_theorem,
      Unitary.conjStarAlgAut_apply, Function.comp_def]
      using hSigma.isHermitian.spectral_theorem
  have hlogSigma :
      cfc f sigma =
        (U : CMatrix a) * (Matrix.diagonal fun i => ((f (d i) : ℝ) : ℂ)) *
          star (U : CMatrix a) := by
    rw [hSigmaSpec]
    exact cfc_unitary_conj_diagonal_ofReal U d f
  have hSigmaC :
      psdSupportCompress sigma hSigma sigma =
        (Matrix.diagonal fun i : psdSupportIndex sigma hSigma => ((d i.1 : ℝ) : ℂ)) := by
    simpa [d] using psdSupportCompress_self_eq_diagonal sigma hSigma
  have hlogC :
      State.psdLog (psdSupportCompress sigma hSigma sigma)
          (psdSupportCompress_self_posDef sigma hSigma) =
        (Matrix.diagonal fun i : psdSupportIndex sigma hSigma =>
          ((Real.log (d i.1) : ℝ) : ℂ)) := by
    rw [State.psdLog, hSigmaC]
    exact cfc_diagonal_ofReal (fun i : psdSupportIndex sigma hSigma => d i.1) Real.log
  rw [hlogSigma, hlogC]
  ext r s
  simp [psdSupportIsometry, U, f, Matrix.mul_apply, Matrix.diagonal,
    Matrix.conjTranspose_apply]
  let g : a → ℂ := fun x =>
    (hSigma.isHermitian.eigenvectorUnitary : CMatrix a) r x * ↑(Real.log (d x)) *
      star ((hSigma.isHermitian.eigenvectorUnitary : CMatrix a) s x)
  change (∑ x : psdSupportIndex sigma hSigma, g x.1) =
    ∑ x : a,
      (hSigma.isHermitian.eigenvectorUnitary : CMatrix a) r x *
        ↑(if d x = 0 then 0 else Real.log (d x)) *
        star ((hSigma.isHermitian.eigenvectorUnitary : CMatrix a) s x)
  have hleft :
      (∑ x : psdSupportIndex sigma hSigma, g x.1) =
        ∑ x ∈ (Finset.univ : Finset a) with 0 < d x, g x := by
    simpa [g, d] using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset a))
        (p := fun x => 0 < d x) (f := g))
  rw [hleft]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  by_cases hxpos : 0 < d x
  · have hxne : d x ≠ 0 := ne_of_gt hxpos
    simp [g, hxpos, hxne]
  · have hzero : d x = 0 := by
      exact le_antisymm (not_lt.mp hxpos) (hSigma.eigenvalues_nonneg x)
    simp [g, hzero]

theorem relativeEntropyTraceLog_trace_mul_psdSupportLog_eq_trace_mul_cfc_logZero
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma) :
    ((psdSupportCompress sigma hSigma rho.matrix *
      State.psdLog (psdSupportCompress sigma hSigma sigma)
        (psdSupportCompress_self_posDef sigma hSigma)).trace).re =
      ((rho.matrix * cfc (fun x : ℝ => if x = 0 then 0 else Real.log x) sigma).trace).re := by
  classical
  let V : Matrix a (psdSupportIndex sigma hSigma) ℂ := psdSupportIsometry sigma hSigma
  let rhoC : CMatrix (psdSupportIndex sigma hSigma) := psdSupportCompress sigma hSigma rho.matrix
  let L : CMatrix (psdSupportIndex sigma hSigma) :=
    State.psdLog (psdSupportCompress sigma hSigma sigma)
      (psdSupportCompress_self_posDef sigma hSigma)
  let f : ℝ → ℝ := fun x => if x = 0 then 0 else Real.log x
  have htrace : ((rhoC * L).trace).re =
      ((V * (rhoC * L) * Matrix.conjTranspose V).trace).re := by
    simpa [V] using
      (congrArg Complex.re (psdSupportIsometry_conj_trace sigma hSigma (rhoC * L))).symm
  have hrec : V * rhoC * Matrix.conjTranspose V = rho.matrix := by
    simpa [V, rhoC] using
      psdSupportCompress_reconstruct_of_supports
        (M := rho.matrix) (N := sigma) rho.pos hSigma hSupport
  have hlog : V * L * Matrix.conjTranspose V = cfc f sigma := by
    simpa [V, L, f] using
      relativeEntropyTraceLog_psdSupportLog_embedding_eq_cfc_logZero sigma hSigma
  have hmul : V * (rhoC * L) * Matrix.conjTranspose V =
      (V * rhoC * Matrix.conjTranspose V) * (V * L * Matrix.conjTranspose V) := by
    symm
    calc
      (V * rhoC * Matrix.conjTranspose V) * (V * L * Matrix.conjTranspose V) =
          V * rhoC * (Matrix.conjTranspose V * V) * L * Matrix.conjTranspose V := by
            simp [Matrix.mul_assoc]
      _ = V * rhoC * L * Matrix.conjTranspose V := by
            rw [psdSupportIsometry_isometry sigma hSigma]
            simp [Matrix.mul_assoc]
      _ = V * (rhoC * L) * Matrix.conjTranspose V := by
            simp [Matrix.mul_assoc]
  calc
    ((psdSupportCompress sigma hSigma rho.matrix *
      State.psdLog (psdSupportCompress sigma hSigma sigma)
        (psdSupportCompress_self_posDef sigma hSigma)).trace).re =
        ((rhoC * L).trace).re := by rfl
    _ = ((V * (rhoC * L) * Matrix.conjTranspose V).trace).re := htrace
    _ = (((V * rhoC * Matrix.conjTranspose V) *
          (V * L * Matrix.conjTranspose V)).trace).re := by rw [hmul]
    _ = ((rho.matrix * cfc f sigma).trace).re := by rw [hrec, hlog]
    _ = ((rho.matrix * cfc (fun x : ℝ => if x = 0 then 0 else Real.log x) sigma).trace).re := by
          rfl

theorem relativeEntropyTraceLog_cfc_logZero_eq_psdLog_of_posDef
    (sigma : CMatrix a) (hSigma : sigma.PosDef) :
    cfc (fun x : ℝ => if x = 0 then 0 else Real.log x) sigma =
      State.psdLog sigma hSigma := by
  rw [State.psdLog]
  apply cfc_congr
  intro x hx
  have hxpos : 0 < x := (Matrix.PosDef.isStrictlyPositive hSigma).spectrum_pos hx
  simp [ne_of_gt hxpos]

/-- Finite trace-log branch of PSD-reference quantum relative entropy.

The branch is written on the positive spectral support of the PSD reference.
The compressed reference is positive definite there, so `psdLog` is the usual
functional-calculus logarithm on the source-supported domain. -/
noncomputable def relativeEntropyPSDReferenceTraceLogFinite
    (rho : State a) (sigma : CMatrix a) (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma) : Real := by
  classical
  let rhoC : State (psdSupportIndex sigma hSigma) :=
    psdSupportCompressedState rho hSigma hSupport
  let sigmaC : CMatrix (psdSupportIndex sigma hSigma) :=
    psdSupportCompress sigma hSigma sigma
  have hSigmaC : sigmaC.PosDef := by
    simpa [sigmaC] using psdSupportCompressedState_reference_posDef hSigma
  exact
    -rhoC.vonNeumann -
      ((rhoC.matrix * psdLog sigmaC hSigmaC).trace.re / Real.log 2)

/-- Source-facing extended-real trace-log PSD-reference relative entropy.

This is the Khatri--Wilde/Tomamichel support convention: the trace-log finite
branch is used when `rho` is supported by `sigma`; otherwise the value is
`+infty`. -/
noncomputable def relativeEntropyPSDReferenceTraceLogE
    (rho : State a) (sigma : CMatrix a) (hSigma : sigma.PosSemidef) : EReal := by
  classical
  exact
    if hSupport : Matrix.Supports rho.matrix sigma then
      (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport : EReal)
    else
      (⊤ : EReal)

/-- Canonical state-state quantum relative entropy as an extended real, using
the trace-log support convention. -/
noncomputable def relativeEntropy (rho sigma : State a) : EReal :=
  relativeEntropyPSDReferenceTraceLogE rho sigma.matrix sigma.pos

@[simp]
theorem relativeEntropyPSDReferenceTraceLogE_eq_top_of_not_supports
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : ¬ Matrix.Supports rho.matrix sigma) :
    relativeEntropyPSDReferenceTraceLogE rho sigma hSigma = (⊤ : EReal) := by
  simp [relativeEntropyPSDReferenceTraceLogE, hSupport]

@[simp]
theorem relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma) :
    relativeEntropyPSDReferenceTraceLogE rho sigma hSigma =
      (relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport : EReal) := by
  simp [relativeEntropyPSDReferenceTraceLogE, hSupport]

/-- The finite trace-log branch against a positive-definite matrix reference
can be evaluated without assuming that the input state is full rank. -/
theorem relativeEntropyPSDReferenceTraceLogFinite_eq_posDef_formula
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    (hSupport : Matrix.Supports rho.matrix sigma) :
    relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma.posSemidef hSupport =
      -rho.vonNeumann -
        ((rho.matrix * State.psdLog sigma hSigma).trace.re / Real.log 2) := by
  have hEntropy :
      (_root_.QIT.psdSupportCompressedState rho hSigma.posSemidef hSupport).vonNeumann =
        rho.vonNeumann :=
    relativeEntropyTraceLog_vonNeumann_psdSupportCompressedState_eq
      rho hSigma.posSemidef hSupport
  have hTrace :
      ((psdSupportCompress sigma hSigma.posSemidef rho.matrix *
        State.psdLog (psdSupportCompress sigma hSigma.posSemidef sigma)
          (psdSupportCompress_self_posDef sigma hSigma.posSemidef)).trace).re =
        ((rho.matrix *
          cfc (fun x : Real => if x = 0 then 0 else Real.log x) sigma).trace).re :=
    relativeEntropyTraceLog_trace_mul_psdSupportLog_eq_trace_mul_cfc_logZero
      rho hSigma.posSemidef hSupport
  have hLog :
      cfc (fun x : Real => if x = 0 then 0 else Real.log x) sigma =
        State.psdLog sigma hSigma :=
    relativeEntropyTraceLog_cfc_logZero_eq_psdLog_of_posDef sigma hSigma
  have hTrace' :
      (((_root_.QIT.psdSupportCompressedState rho hSigma.posSemidef hSupport).matrix *
        State.psdLog (psdSupportCompress sigma hSigma.posSemidef sigma)
          (psdSupportCompress_self_posDef sigma hSigma.posSemidef)).trace).re =
        ((rho.matrix *
          cfc (fun x : Real => if x = 0 then 0 else Real.log x) sigma).trace).re := by
    simpa [_root_.QIT.psdSupportCompressedState] using hTrace
  rw [relativeEntropyPSDReferenceTraceLogFinite]
  rw [hEntropy, hTrace', hLog]

/-- Multiplying a positive-definite reference by a positive scalar shifts
support-aware Umegaki relative entropy by `-log2 scale`. -/
theorem relativeEntropyPSDReferenceTraceLogE_real_smul_reference
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    {scale : Real} (hScale : 0 < scale) :
    relativeEntropyPSDReferenceTraceLogE rho (scale • sigma)
        (Matrix.PosDef.smul hSigma hScale).posSemidef =
      relativeEntropyPSDReferenceTraceLogE rho sigma hSigma.posSemidef -
        (log2 scale : EReal) := by
  let hSupport : Matrix.Supports rho.matrix sigma :=
    Matrix.Supports.of_right_posDef rho.matrix sigma hSigma
  let hSupportScaled : Matrix.Supports rho.matrix (scale • sigma) :=
    Matrix.Supports.of_right_posDef rho.matrix (scale • sigma)
      (Matrix.PosDef.smul hSigma hScale)
  rw [relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports
      rho (Matrix.PosDef.smul hSigma hScale).posSemidef hSupportScaled,
    relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports
      rho hSigma.posSemidef hSupport]
  rw [relativeEntropyPSDReferenceTraceLogFinite_eq_posDef_formula
      rho (Matrix.PosDef.smul hSigma hScale) hSupportScaled,
    relativeEntropyPSDReferenceTraceLogFinite_eq_posDef_formula
      rho hSigma hSupport]
  have hLog :
      State.psdLog (scale • sigma) (Matrix.PosDef.smul hSigma hScale) =
        algebraMap Real (CMatrix a) (Real.log scale) + State.psdLog sigma hSigma := by
    exact CFC.log_smul' sigma hScale
      (ha := by exact Matrix.PosDef.isStrictlyPositive hSigma)
  rw [hLog]
  simp [Matrix.mul_add, Matrix.trace_add, Algebra.algebraMap_eq_smul_one,
    Matrix.trace_smul, rho.trace_eq_one, log2]
  norm_cast
  ring

@[simp]
theorem relativeEntropy_eq_top_of_not_supports
    (rho sigma : State a) (hSupport : ¬ Matrix.Supports rho.matrix sigma.matrix) :
    rho.relativeEntropy sigma = (⊤ : EReal) := by
  simp [relativeEntropy, hSupport]

@[simp]
theorem relativeEntropy_eq_coe_of_supports
    (rho sigma : State a) (hSupport : Matrix.Supports rho.matrix sigma.matrix) :
    rho.relativeEntropy sigma =
      (relativeEntropyPSDReferenceTraceLogFinite rho sigma.matrix sigma.pos hSupport : EReal) := by
  simp [relativeEntropy, hSupport]

theorem relativeEntropy_eq_coe_posDefFinite_of_posDef
    (rho sigma : State a) (hRho : rho.matrix.PosDef) (hSigma : sigma.matrix.PosDef) :
    rho.relativeEntropy sigma =
      (rho.relativeEntropyPosDefFinite sigma hRho hSigma : EReal) := by
  classical
  let hSupport : Matrix.Supports rho.matrix sigma.matrix :=
    Matrix.Supports.of_right_posDef rho.matrix sigma.matrix hSigma
  rw [relativeEntropy_eq_coe_of_supports rho sigma hSupport]
  congr 1
  have hEntropy :
      (_root_.QIT.psdSupportCompressedState rho sigma.pos hSupport).vonNeumann =
        rho.vonNeumann :=
    relativeEntropyTraceLog_vonNeumann_psdSupportCompressedState_eq rho sigma.pos hSupport
  have hTrace :
      ((psdSupportCompress sigma.matrix sigma.pos rho.matrix *
        State.psdLog (psdSupportCompress sigma.matrix sigma.pos sigma.matrix)
          (psdSupportCompress_self_posDef sigma.matrix sigma.pos)).trace).re =
        ((rho.matrix *
          cfc (fun x : ℝ => if x = 0 then 0 else Real.log x) sigma.matrix).trace).re :=
    relativeEntropyTraceLog_trace_mul_psdSupportLog_eq_trace_mul_cfc_logZero
      rho sigma.pos hSupport
  have hLogZero :
      cfc (fun x : ℝ => if x = 0 then 0 else Real.log x) sigma.matrix =
        State.psdLog sigma.matrix hSigma :=
    relativeEntropyTraceLog_cfc_logZero_eq_psdLog_of_posDef sigma.matrix hSigma
  have hVon :
      rho.vonNeumann =
        -((rho.matrix * State.psdLog rho.matrix hRho).trace.re) / Real.log 2 :=
    State.vonNeumann_eq_neg_trace_mul_psdLog_div_log_two rho hRho
  calc
    relativeEntropyPSDReferenceTraceLogFinite rho sigma.matrix sigma.pos hSupport =
        -(_root_.QIT.psdSupportCompressedState rho sigma.pos hSupport).vonNeumann -
          ((psdSupportCompress sigma.matrix sigma.pos rho.matrix *
            State.psdLog (psdSupportCompress sigma.matrix sigma.pos sigma.matrix)
              (psdSupportCompress_self_posDef sigma.matrix sigma.pos)).trace).re /
            Real.log 2 := by
          rfl
    _ = -rho.vonNeumann -
          ((rho.matrix *
            cfc (fun x : ℝ => if x = 0 then 0 else Real.log x) sigma.matrix).trace).re /
            Real.log 2 := by
          rw [hEntropy, hTrace]
    _ = -rho.vonNeumann -
          ((rho.matrix * State.psdLog sigma.matrix hSigma).trace).re /
            Real.log 2 := by
          rw [hLogZero]
    _ = rho.relativeEntropyPosDefFinite sigma hRho hSigma := by
          rw [hVon]
          simp [State.relativeEntropyPosDefFinite]
          ring

end State

variable {a : Type u} [Fintype a] [DecidableEq a]

omit [DecidableEq a] in
theorem supports_real_smul_left
    {M N : CMatrix a} (c : ℝ) (hM : Matrix.Supports M N) :
    Matrix.Supports (c • M) N := by
  intro v hv
  simp [Matrix.smul_mulVec, hM v hv]

/-- Finite branch of Tomamichel's source-domain quantum divergence.

For a nonzero PSD operator `rho` supported by the PSD reference `sigma`, this is
the source trace-normalized value.  It is implemented through the normalized
state `rho / Tr rho` plus the trace-scaling correction, avoiding a separate
singular matrix-log API while keeping the same mathematical value. -/
def relativeEntropyPSDTraceLogFinite
    (rho sigma : CMatrix a) (hRho : rho.PosSemidef) (hRho_ne : rho ≠ 0)
    (hSigma : sigma.PosSemidef) (hSupport : Matrix.Supports rho sigma) : ℝ := by
  classical
  let hRhoTr : 0 < rho.trace.re :=
    State.posSemidef_trace_pos_of_ne_zero hRho hRho_ne
  let rhoNorm : State a := State.normalizePSD rho hRho hRhoTr.ne'
  have hSupportNorm : Matrix.Supports rhoNorm.matrix sigma := by
    simpa [rhoNorm, State.normalizePSD] using
      supports_real_smul_left ((rho.trace.re)⁻¹ : ℝ) hSupport
  exact
    log2 rho.trace.re +
      State.relativeEntropyPSDReferenceTraceLogFinite
        rhoNorm sigma hSigma hSupportNorm

/-- Source-exact extended-real quantum divergence for nonzero PSD operators.

This matches Tomamichel's Definition `df:rel`: the finite trace-log branch is
used when `rho` is supported by `sigma`, and the value is `+infty` otherwise. -/
def relativeEntropyPSDTraceLogE
    (rho sigma : CMatrix a) (hRho : rho.PosSemidef) (hRho_ne : rho ≠ 0)
    (hSigma : sigma.PosSemidef) : EReal := by
  classical
  exact
    if hSupport : Matrix.Supports rho sigma then
      (relativeEntropyPSDTraceLogFinite rho sigma hRho hRho_ne hSigma hSupport : EReal)
    else
      (⊤ : EReal)

@[simp]
theorem relativeEntropyPSDTraceLogE_eq_top_of_not_supports
    (rho sigma : CMatrix a) (hRho : rho.PosSemidef) (hRho_ne : rho ≠ 0)
    (hSigma : sigma.PosSemidef) (hSupport : ¬ Matrix.Supports rho sigma) :
    relativeEntropyPSDTraceLogE rho sigma hRho hRho_ne hSigma = (⊤ : EReal) := by
  simp [relativeEntropyPSDTraceLogE, hSupport]

@[simp]
theorem relativeEntropyPSDTraceLogE_eq_coe_of_supports
    (rho sigma : CMatrix a) (hRho : rho.PosSemidef) (hRho_ne : rho ≠ 0)
    (hSigma : sigma.PosSemidef) (hSupport : Matrix.Supports rho sigma) :
    relativeEntropyPSDTraceLogE rho sigma hRho hRho_ne hSigma =
      (relativeEntropyPSDTraceLogFinite rho sigma hRho hRho_ne hSigma hSupport : EReal) := by
  simp [relativeEntropyPSDTraceLogE, hSupport]

theorem relativeEntropyPSDTraceLogFinite_state_eq
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma) :
    relativeEntropyPSDTraceLogFinite
        rho.matrix sigma rho.pos rho.density_matrix_ne_zero hSigma hSupport =
      State.relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma hSupport := by
  simp [relativeEntropyPSDTraceLogFinite, State.normalizePSD_self, rho.trace_re_eq_one, log2]

/-- The source-exact PSD-operator definition specializes to the existing
normalized-state PSD-reference API used by the DPI theorems. -/
theorem relativeEntropyPSDTraceLogE_state_eq
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosSemidef) :
    relativeEntropyPSDTraceLogE rho.matrix sigma rho.pos rho.density_matrix_ne_zero hSigma =
      State.relativeEntropyPSDReferenceTraceLogE rho sigma hSigma := by
  classical
  by_cases hSupport : Matrix.Supports rho.matrix sigma
  · rw [relativeEntropyPSDTraceLogE_eq_coe_of_supports
        rho.matrix sigma rho.pos rho.density_matrix_ne_zero hSigma hSupport,
      State.relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports rho hSigma hSupport,
      relativeEntropyPSDTraceLogFinite_state_eq rho hSigma hSupport]
  · rw [relativeEntropyPSDTraceLogE_eq_top_of_not_supports
        rho.matrix sigma rho.pos rho.density_matrix_ne_zero hSigma hSupport,
      State.relativeEntropyPSDReferenceTraceLogE_eq_top_of_not_supports rho hSigma hSupport]

end

end QIT
