/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Classical.CQState
public import QIT.OneShot.SmoothEndpoint.Companion
public import QIT.Protocols.LOCC.ConditionalMinEntropy

/-!
# Smooth conditional min-entropy under refined finite instruments

This module prepares the Uhlmann lifting step in
`Berta2009SingleShotStateMerging`, `diploma_thesis_berta_08_v1.tex:840-867`.
The source uses normalized trace-distance smoothing elsewhere in the thesis.
The repository's canonical smooth min-entropy instead uses purified distance.
Accordingly, the target lift here is a same-radius purified-distance statement;
a trace-distance input would require the explicit Fuchs--van de Graaf radius
conversion rather than an identification of the two metrics.

The classical record retains the complete positive refined Alice outcome
(operational outcome together with the chosen Kraus index).  The cq state is
reordered as `A' | (R x I)`, matching the conditional-min-entropy partition
used by the state-merging converse.
-/

@[expose] public section

namespace QIT

universe u v w x

noncomputable section

/-- Reorder a refined cq state so that Alice's quantum output is the source
and the untouched reference together with the refined outcome is the
conditioning system. -/
def finiteInstrumentRecordedSourceReferenceEquiv
    (I : Type u) (A' : Type v) (R : Type w) :
    Prod I (Prod A' R) ≃ Prod A' (Prod R I) where
  toFun t := (t.2.1, (t.2.2, t.1))
  invFun t := (t.2.2, (t.1, t.2.1))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

/-- Reassociate a coherent classical record so that the quantum output and
record form the source system while the untouched reference remains the
conditioning system. -/
def projectiveSourceReferenceEquiv
    (I : Type u) (A' : Type v) (R : Type w) :
    Prod I (Prod A' R) ≃ Prod (Prod A' I) R where
  toFun t := ((t.2.1, t.1), t.2.2)
  invFun t := (t.1.2, (t.1.1, t.2))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

/-- Berta's copy-basis isometry `|i⟩ ↦ |i⟩ ⊗ |i⟩`.  Its range is the
diagonal subspace used in the projective-measurement Uhlmann lift. -/
def classicalCopyIsometry (I : Type u) [Fintype I] [DecidableEq I] :
    ReferenceIsometry I (Prod I I) :=
  ReferenceIsometry.ofInjective (fun i => (i, i)) (by
    intro i j hij
    exact congrArg Prod.fst hij)

@[simp]
theorem classicalCopyIsometry_matrix_apply
    (I : Type u) [Fintype I] [DecidableEq I] (ij : Prod I I) (k : I) :
    (classicalCopyIsometry I).matrix ij k = if ij = (k, k) then 1 else 0 :=
  rfl

/-- Orthogonal projector onto the diagonal image of `classicalCopyIsometry`.
This is the finite-dimensional `Q` used in Berta's projective lift. -/
def classicalCopyProjector (I : Type u) [Fintype I] [DecidableEq I] :
    CMatrix (Prod I I) :=
  (classicalCopyIsometry I).matrix *
    Matrix.conjTranspose (classicalCopyIsometry I).matrix

namespace ProjectiveMeasurementLift

open scoped ComplexOrder MatrixOrder
open Matrix

local postfix:1024 "†" => Matrix.conjTranspose

variable {I : Type u} {B : Type v} {E : Type w}
variable [Fintype I] [DecidableEq I]
variable [Fintype B] [DecidableEq B]
variable [Fintype E] [DecidableEq E]

/-- The `i`th row block of an amplitude matrix on `I x B`. -/
def blockAmplitude (X : Matrix (Prod I B) E Complex) (i : I) :
    Matrix B E Complex :=
  fun b e => X (i, b) e

/-- Pad a block amplitude into a reference containing both its old reference
and a canonical `B`-sized Uhlmann reserve. -/
def padAmplitude {D : Type*} (X : Matrix B E Complex) :
    Matrix B (Sum E D) Complex
  | b, Sum.inl e => X b e
  | _, Sum.inr _ => 0

def padBlockAmplitude (X : Matrix B E Complex) :
    Matrix B (Sum E B) Complex :=
  padAmplitude X

omit [Fintype B] [DecidableEq B] [DecidableEq E] in
theorem padAmplitude_gram {D : Type*} [Fintype D]
    (X : Matrix B E Complex) :
    padAmplitude (D := D) X * (padAmplitude (D := D) X)† = X * X† := by
  classical
  ext b b'
  simp [padAmplitude, Matrix.mul_apply]

omit [DecidableEq B] [DecidableEq E] in
theorem padBlockAmplitude_gram (X : Matrix B E Complex) :
    padBlockAmplitude X * (padBlockAmplitude X)† = X * X† := by
  exact padAmplitude_gram X

/-- Put a canonical square-root amplitude entirely in the reserve summand. -/
def reserveAmplitude (S : CMatrix B) : Matrix B (Sum E B) Complex
  | _, Sum.inl _ => 0
  | b, Sum.inr b' => psdSqrt S b b'

omit [DecidableEq E] in
theorem reserveAmplitude_gram (S : CMatrix B) (hS : S.PosSemidef) :
    reserveAmplitude (E := E) S * (reserveAmplitude (E := E) S)† = S := by
  classical
  ext b b'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
    reserveAmplitude, zero_mul, Finset.sum_const_zero, zero_add]
  calc
    (∑ x : B, psdSqrt S b x * star (psdSqrt S b' x)) =
        (psdSqrt S * psdSqrt S) b b' := by
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro x _
      rw [← (psdSqrt_isHermitian S).apply x b']
    _ = S b b' := by rw [psdSqrt_mul_self_of_posSemidef hS]

omit [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B] [DecidableEq E] in
theorem blockAmplitude_gram_eq_block
    (X : Matrix (Prod I B) E Complex) (i : I) :
    blockAmplitude X i * (blockAmplitude X i)† =
      Classical.block (X * X†) i i := by
  classical
  ext b b'
  simp [blockAmplitude, Classical.block, Matrix.mul_apply]

omit [Fintype I] [DecidableEq I] [DecidableEq B] [DecidableEq E] in
theorem padBlockAmplitude_inner
    (X : Matrix B E Complex) (Y : Matrix B (Sum E B) Complex) :
    (((padBlockAmplitude X)† * Y).trace) =
      Finset.univ.sum fun e : E =>
        Finset.univ.sum fun b : B => star (X b e) * Y b (Sum.inl e) := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, padBlockAmplitude, padAmplitude]

omit [Fintype I] [DecidableEq I] [DecidableEq B] [DecidableEq E] in
theorem padAmplitude_inner {D : Type*} [Fintype D]
    (X : Matrix B E Complex) (Y : Matrix B (Sum E D) Complex) :
    (((padAmplitude (D := D) X)† * Y).trace) =
      Finset.univ.sum fun e : E =>
        Finset.univ.sum fun b : B => star (X b e) * Y b (Sum.inl e) := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, padAmplitude]

omit [DecidableEq B] [DecidableEq E] in
theorem amplitudeGram_pos (X : Matrix B E Complex) :
    (X * X†).PosSemidef := by
  simpa [Matrix.conjTranspose_conjTranspose] using
    Matrix.posSemidef_conjTranspose_mul_self X†

omit [DecidableEq B] [Fintype E] [DecidableEq E] in
/-- Summing the reference sandwich of the row blocks is the same as inserting
the block-diagonal reference into the full amplitude. -/
theorem sum_blockAmplitude_sandwich
    (X : Matrix (Prod I B) E Complex) (Q : CMatrix B) :
    (∑ i : I, (blockAmplitude X i)† * Q * blockAmplitude X i) =
      X† * Matrix.kronecker (1 : CMatrix I) Q * X := by
  classical
  ext e e'
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    blockAmplitude, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.sum_ite_eq']

/-- A positive matrix whose diagonal record blocks have a common weighted
reference is bounded by the identity on the coherent record tensor that
reference.  This is the Schur-complement core of Berta's projective lift. -/
theorem matrix_le_identity_kronecker_of_diagonal_blocks_le_posDef
    (T : CMatrix (Prod I B)) (hT : T.PosSemidef)
    (Q : CMatrix B) (hQ : Q.PosDef) (weights : I → Real)
    (hweights_nonneg : ∀ i, 0 ≤ weights i)
    (hweights_sum : ∑ i, weights i = 1)
    (hblock : ∀ i, Classical.block T i i ≤ (weights i : Complex) • Q) :
    T ≤ Matrix.kronecker (1 : CMatrix I) Q := by
  classical
  let X : CMatrix (Prod I B) := psdSqrt T
  let Xi : I → Matrix B (Prod I B) Complex := fun i ↦ blockAmplitude X i
  have hXGram : X * X† = T := by
    rw [(psdSqrt_isHermitian T).eq, psdSqrt_mul_self_of_posSemidef hT]
  have hXiGram : ∀ i, Xi i * (Xi i)† = Classical.block T i i := by
    intro i
    simpa only [Xi, hXGram] using blockAmplitude_gram_eq_block X i
  have hcomponent : ∀ i,
      (Xi i)† * Q⁻¹ * Xi i ≤
        (weights i : Complex) • (1 : CMatrix (Prod I B)) := by
    intro i
    by_cases hi : 0 < weights i
    · exact
        (Matrix.conjTranspose_mul_inv_mul_self_le_smul_one_iff_self_mul_conjTranspose_le_smul
          (Xi i) Q hQ hi).2 (by simpa only [hXiGram i] using hblock i)
    · have hzero : weights i = 0 :=
        le_antisymm (not_lt.mp hi) (hweights_nonneg i)
      have hgramZero : Xi i * (Xi i)† = 0 := by
        apply le_antisymm
        · simpa [hXiGram i, hzero] using hblock i
        · rw [Matrix.le_iff]
          simpa using amplitudeGram_pos (Xi i)
      have hXiZero : Xi i = 0 := Matrix.self_mul_conjTranspose_eq_zero.mp hgramZero
      simp [hXiZero, hzero]
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ (Finset.univ : Finset I)) =>
    hcomponent i
  have hweightsComplex : (∑ i : I, (weights i : Complex)) = 1 := by
    exact_mod_cast hweights_sum
  have hsumWeights :
      (∑ i : I, (weights i : Complex) • (1 : CMatrix (Prod I B))) =
        (1 : CMatrix (Prod I B)) := by
    rw [← Finset.sum_smul, hweightsComplex, one_smul]
  have hcomplement :
      X† * (Matrix.kronecker (1 : CMatrix I) Q)⁻¹ * X ≤
        (1 : CMatrix (Prod I B)) := by
    have hinv :
        (Matrix.kronecker (1 : CMatrix I) Q)⁻¹ =
          Matrix.kronecker (1 : CMatrix I) Q⁻¹ := by
      simpa only [Matrix.kronecker, inv_one] using
        (Matrix.inv_kronecker (1 : CMatrix I) Q)
    rw [hinv]
    simpa only [inv_one, sum_blockAmplitude_sandwich, hsumWeights, Xi] using hsum
  have hQglobal : (Matrix.kronecker (1 : CMatrix I) Q).PosDef :=
    Matrix.PosDef.one.kronecker hQ
  have hcomplement' :
      X† * (Matrix.kronecker (1 : CMatrix I) Q)⁻¹ * X ≤
        (((1 : Real) : Complex) • (1 : CMatrix (Prod I B))) := by
    norm_num
    exact hcomplement
  have hresult :=
    (Matrix.conjTranspose_mul_inv_mul_self_le_smul_one_iff_self_mul_conjTranspose_le_smul
      X (Matrix.kronecker (1 : CMatrix I) Q) hQglobal
      (c := 1) zero_lt_one).1 hcomplement'
  norm_num at hresult
  simpa only [hXGram] using hresult

/-- Positive-semidefinite version of
`matrix_le_identity_kronecker_of_diagonal_blocks_le_posDef`.  A small identity
regularization is removed by closedness of the PSD cone. -/
theorem matrix_le_identity_kronecker_of_diagonal_blocks_le
    (T : CMatrix (Prod I B)) (hT : T.PosSemidef)
    (Q : CMatrix B) (hQ : Q.PosSemidef) (weights : I → Real)
    (hweights_nonneg : ∀ i, 0 ≤ weights i)
    (hweights_sum : ∑ i, weights i = 1)
    (hblock : ∀ i, Classical.block T i i ≤ (weights i : Complex) • Q) :
    T ≤ Matrix.kronecker (1 : CMatrix I) Q := by
  classical
  let D : CMatrix (Prod I B) := Matrix.kronecker (1 : CMatrix I) Q - T
  have hDherm : D.IsHermitian :=
    ((Matrix.PosSemidef.one.kronecker hQ).isHermitian).sub hT.isHermitian
  have hreg : ∀ epsilon : Real, 0 < epsilon →
      (D + (epsilon : Complex) • (1 : CMatrix (Prod I B))).PosSemidef := by
    intro epsilon hepsilon
    let Qepsilon : CMatrix B := Q + (epsilon : Complex) • (1 : CMatrix B)
    have hQepsilon : Qepsilon.PosDef := by
      simpa only [Qepsilon] using
        State.cMatrix_posSemidef_add_pos_smul_one_posDef hQ hepsilon
    have hQle : Q ≤ Qepsilon := by
      rw [Matrix.le_iff]
      have hepsilonComplex : (0 : Complex) ≤ (epsilon : Complex) := by
        exact_mod_cast hepsilon.le
      simpa [Qepsilon, sub_eq_add_neg, add_assoc] using
        (Matrix.PosSemidef.one.smul hepsilonComplex)
    have hblockEpsilon : ∀ i,
        Classical.block T i i ≤ (weights i : Complex) • Qepsilon := by
      intro i
      have hweightComplex : (0 : Complex) ≤ (weights i : Complex) := by
        exact_mod_cast hweights_nonneg i
      have hscaled := (Matrix.le_iff.mp hQle).smul hweightComplex
      have hscaledOrder :
          (weights i : Complex) • Q ≤ (weights i : Complex) • Qepsilon := by
        rw [Matrix.le_iff]
        simpa [smul_sub] using hscaled
      exact (hblock i).trans hscaledOrder
    have hglobal := matrix_le_identity_kronecker_of_diagonal_blocks_le_posDef
      T hT Qepsilon hQepsilon weights hweights_nonneg hweights_sum hblockEpsilon
    have hglobalPsd := Matrix.le_iff.mp hglobal
    simpa [D, Qepsilon, Matrix.kronecker_add, Matrix.kronecker_smul,
      sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hglobalPsd
  rw [Matrix.le_iff]
  exact Matrix.posSemidef_of_add_pos_smul_one_posSemidef D hDherm hreg

/-- Normalize a positive matrix of nonzero trace to a state. -/
def stateOfPsdTracePos (A : CMatrix B) (hA : A.PosSemidef)
    (htrace : 0 < A.trace.re) : State B where
  matrix := (A.trace.re)⁻¹ • A
  pos := Matrix.PosSemidef.smul hA (by
    exact_mod_cast inv_nonneg.mpr htrace.le)
  trace_eq_one := by
    rw [Matrix.trace_smul]
    have hne : (A.trace.re : Complex) ≠ 0 := by exact_mod_cast htrace.ne'
    have him : A.trace.im = 0 := (Matrix.PosSemidef.trace_nonneg hA).2.symm
    apply Complex.ext
    · simp [Complex.real_smul, htrace.ne']
    · simp [Complex.real_smul, him]

@[simp]
theorem stateOfPsdTracePos_matrix (A : CMatrix B) (hA : A.PosSemidef)
    (htrace : 0 < A.trace.re) :
    (stateOfPsdTracePos A hA htrace).matrix = (A.trace.re)⁻¹ • A :=
  rfl

theorem sqrtMatrix_stateOfPsdTracePos
    (A : CMatrix B) (hA : A.PosSemidef) (htrace : 0 < A.trace.re) :
    (stateOfPsdTracePos A hA htrace).sqrtMatrix =
      (((Real.sqrt A.trace.re)⁻¹ : Real) : Complex) • psdSqrt A := by
  rw [State.sqrtMatrix, stateOfPsdTracePos_matrix]
  change psdSqrt ((((A.trace.re)⁻¹ : Real) : Complex) • A) =
    (((Real.sqrt A.trace.re)⁻¹ : Real) : Complex) • psdSqrt A
  have hinv : 0 ≤ (A.trace.re)⁻¹ := inv_nonneg.mpr htrace.le
  rw [psdSqrt_real_smul hinv hA]
  congr 1
  rw [Real.sqrt_inv]

omit [DecidableEq E] in
theorem normalizedAmplitude_gram
    (X : Matrix B E Complex) (htrace : 0 < (X * X†).trace.re) :
    let A := X * X†
    let c : Complex := ((Real.sqrt A.trace.re)⁻¹ : Real)
    (c • X) * (c • X)† =
      (stateOfPsdTracePos A (amplitudeGram_pos X) htrace).matrix := by
  let A := X * X†
  change
    ((((Real.sqrt A.trace.re)⁻¹ : Real) : Complex) • X) *
        ((((Real.sqrt A.trace.re)⁻¹ : Real) : Complex) • X)† =
      (stateOfPsdTracePos A (amplitudeGram_pos X) htrace).matrix
  rw [stateOfPsdTracePos_matrix]
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  change
    (((((Real.sqrt A.trace.re)⁻¹ : Real) : Complex) *
        star (((Real.sqrt A.trace.re)⁻¹ : Real) : Complex)) • A) =
      (((A.trace.re)⁻¹ : Real) : Complex) • A
  congr 1
  have hstar :
      star ((((Real.sqrt A.trace.re)⁻¹ : Real) : Complex)) =
        (((Real.sqrt A.trace.re)⁻¹ : Real) : Complex) := by
    simp
  rw [hstar]
  rw [← Complex.ofReal_mul]
  congr 1
  have hsqrt : Real.sqrt A.trace.re ≠ 0 := (Real.sqrt_pos.mpr htrace).ne'
  field_simp [hsqrt, htrace.ne']
  rw [Real.sq_sqrt htrace.le]
  simp [A, htrace.ne']

theorem scaledPurificationAmplitude_gram
    (phi : PureVector (Prod E B)) (sigma : State B)
    (hphi : phi.Purifies sigma) (t : Real) (ht : 0 ≤ t) :
    (((Real.sqrt t : Real) : Complex) • phi.amplitudeMatrix) *
        (((Real.sqrt t : Real) : Complex) • phi.amplitudeMatrix)† =
      (t : Complex) • sigma.matrix := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [PureVector.purifies_amplitudeMatrix_mul_conjTranspose_eq hphi]
  congr 1
  have hstar : star ((Real.sqrt t : Real) : Complex) =
      ((Real.sqrt t : Real) : Complex) := by simp
  rw [hstar]
  norm_cast
  exact Real.mul_self_sqrt ht

/-- Unit phase that rotates a complex overlap onto the nonnegative real axis. -/
def alignPhase (z : Complex) : Complex :=
  if z = 0 then 1 else star z / (‖z‖ : Complex)

theorem alignPhase_mul (z : Complex) :
    alignPhase z * z = (‖z‖ : Complex) := by
  by_cases hz : z = 0
  · simp [alignPhase, hz]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    rw [alignPhase, if_neg hz]
    calc
      star z / (‖z‖ : Complex) * z =
          (star z * z) / (‖z‖ : Complex) := by ring
      _ = (Complex.normSq z : Complex) / (‖z‖ : Complex) := by
        change (starRingEnd Complex) z * z / (‖z‖ : Complex) = _
        rw [Complex.normSq_eq_conj_mul_self]
      _ = ((‖z‖ ^ 2 : Real) : Complex) / (‖z‖ : Complex) := by
        rw [Complex.normSq_eq_norm_sq]
      _ = (‖z‖ : Complex) := by
        push_cast
        field_simp [hn]

theorem alignPhase_mul_star (z : Complex) :
    alignPhase z * star (alignPhase z) = 1 := by
  by_cases hz : z = 0
  · simp [alignPhase, hz]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hnorm : ‖alignPhase z‖ = 1 := by
      simp [alignPhase, hz, hn]
    change alignPhase z * (starRingEnd Complex) (alignPhase z) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    norm_num

/-- Uhlmann attainment for one projective-measurement block.  The returned
amplitude uses the padded reference and has phase-aligned overlap with the
center amplitude. -/
theorem exists_alignedBlockAmplitude
    [Nonempty B] (X : Matrix B E Complex) (S : CMatrix B)
    (hS : S.PosSemidef) (hXtrace : 0 < (X * X†).trace.re)
    (hStrace : 0 < S.trace.re) :
    Exists fun Y : Matrix B (Sum E B) Complex =>
      Y * Y† = S /\
        (((padBlockAmplitude X)† * Y).trace) =
          (traceNorm (psdSqrt (X * X†) * psdSqrt S) : Complex) := by
  classical
  let A : CMatrix B := X * X†
  have hA : A.PosSemidef := amplitudeGram_pos X
  let Xpad : Matrix B (Sum E B) Complex := padBlockAmplitude X
  let rho : State B := stateOfPsdTracePos A hA hXtrace
  let sigma : State B := stateOfPsdTracePos S hS hStrace
  let cA : Complex := (((Real.sqrt A.trace.re)⁻¹ : Real) : Complex)
  let Xn : Matrix B (Sum E B) Complex := cA • Xpad
  have hXnGram : Xn * Xn† = rho.matrix := by
    have hnorm := normalizedAmplitude_gram X hXtrace
    change (cA • Xpad) * (cA • Xpad)† = rho.matrix
    subst cA
    subst Xpad
    subst rho
    simpa only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, padBlockAmplitude_gram] using hnorm
  have hXnTrace : (Xn * Xn†).trace = 1 := by
    rw [hXnGram, rho.trace_eq_one]
  let psi : PureVector (Prod (Sum E B) B) :=
    PureVector.ofAmplitudeMatrix Xn hXnTrace
  have hpsi : psi.Purifies rho :=
    PureVector.ofAmplitudeMatrix_purifies hXnGram hXnTrace
  have hcard : Fintype.card B ≤ Fintype.card (Sum E B) := by
    simp [Fintype.card_sum]
  obtain ⟨phi, hphi, hoverlapSq⟩ :=
    PureVector.exists_purification_with_overlapSq_eq_squaredFidelity
      (Ψ := psi) (ρ := rho) (σ := sigma) hpsi hcard
  have hoverlapAbs : Complex.abs (psi.overlap phi) = rho.fidelity sigma := by
    rw [PureVector.overlapSq_eq_normSq, Complex.normSq_eq_norm_sq,
      State.squaredFidelity_eq_fidelity_sq] at hoverlapSq
    exact (sq_eq_sq₀ (norm_nonneg _) (State.fidelity_nonneg rho sigma)).mp hoverlapSq
  let cS : Complex := ((Real.sqrt S.trace.re : Real) : Complex)
  let Yraw : Matrix B (Sum E B) Complex := cS • phi.amplitudeMatrix
  have hYrawGram : Yraw * Yraw† = S := by
    have hscaled := scaledPurificationAmplitude_gram phi sigma hphi S.trace.re
      (Matrix.PosSemidef.trace_nonneg hS).1
    rw [stateOfPsdTracePos_matrix] at hscaled
    change Yraw * Yraw† = S
    rw [hscaled]
    simp [ smul_smul, hStrace.ne']
  have hoverlapTrace :
      psi.overlap phi = (Xn† * phi.amplitudeMatrix).trace := by
    rw [PureVector.overlap_eq_trace_conjTranspose_amplitudeMatrix_mul]
    simp [psi, PureVector.ofAmplitudeMatrix_amplitudeMatrix]
  let a : Real := Real.sqrt A.trace.re
  let s : Real := Real.sqrt S.trace.re
  let k : Real := a * s
  have ha : 0 < a := by simpa [a, A] using Real.sqrt_pos.mpr hXtrace
  have hs : 0 < s := by simpa [s] using Real.sqrt_pos.mpr hStrace
  have hk : 0 < k := mul_pos ha hs
  have hoverlapScale :
      Complex.abs (psi.overlap phi) =
        k⁻¹ * Complex.abs ((Xpad† * Yraw).trace) := by
    rw [hoverlapTrace]
    subst Xn
    subst Xpad
    subst Yraw
    subst cA
    subst cS
    subst k
    subst a
    subst s
    simp [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_smul, Complex.abs, Real.sqrt_nonneg, abs_of_nonneg,
      mul_assoc, mul_left_comm, mul_comm]
    field_simp [ha.ne', hs.ne']
  have hfidelityScale :
      rho.fidelity sigma =
        k⁻¹ * traceNorm (psdSqrt A * psdSqrt S) := by
    rw [State.fidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix]
    rw [sqrtMatrix_stateOfPsdTracePos A hA hXtrace,
      sqrtMatrix_stateOfPsdTracePos S hS hStrace]
    subst k
    subst a
    subst s
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hscale :
        (0 : Real) ≤
          (Real.sqrt A.trace.re)⁻¹ * (Real.sqrt S.trace.re)⁻¹ :=
      mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
    rw [← Complex.ofReal_mul]
    rw [traceNorm_real_smul_eq hscale]
    congr 1
    field_simp [ha.ne', hs.ne']
  have hrawAbs :
      Complex.abs ((Xpad† * Yraw).trace) =
        traceNorm (psdSqrt A * psdSqrt S) := by
    have hscaled :
        k⁻¹ * Complex.abs ((Xpad† * Yraw).trace) =
          k⁻¹ * traceNorm (psdSqrt A * psdSqrt S) := by
      rw [← hoverlapScale, ← hfidelityScale, hoverlapAbs]
    exact (mul_left_cancel₀ (inv_ne_zero hk.ne') hscaled)
  let z : Complex := (Xpad† * Yraw).trace
  let Y : Matrix B (Sum E B) Complex := alignPhase z • Yraw
  refine ⟨Y, ?_, ?_⟩
  · dsimp only [Y]
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [alignPhase_mul_star, one_smul, hYrawGram]
  · calc
      (Xpad† * Y).trace = alignPhase z * z := by
        simp [Y, z, Matrix.mul_smul, Matrix.trace_smul]
      _ = (‖z‖ : Complex) := alignPhase_mul z
      _ = (traceNorm (psdSqrt A * psdSqrt S) : Complex) := by
        exact_mod_cast hrawAbs
      _ = (traceNorm (psdSqrt (X * X†) * psdSqrt S) : Complex) := by
        rfl

/-- The block Uhlmann amplitude, including zero center or candidate blocks. -/
theorem exists_alignedBlockAmplitude_of_posSemidef
    [Nonempty B] (X : Matrix B E Complex) (S : CMatrix B)
    (hS : S.PosSemidef) :
    Exists fun Y : Matrix B (Sum E B) Complex =>
      Y * Y† = S /\
        (((padBlockAmplitude X)† * Y).trace) =
          (traceNorm (psdSqrt (X * X†) * psdSqrt S) : Complex) := by
  classical
  by_cases hStrace0 : S.trace.re = 0
  · have hStrace : S.trace = 0 := by
      apply Complex.ext
      · exact hStrace0
      · exact (Matrix.PosSemidef.trace_nonneg hS).2.symm
    have hSzero : S = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hS).mp hStrace
    refine ⟨0, by simp [hSzero], ?_⟩
    simp [hSzero]
  have hStrace : 0 < S.trace.re :=
    lt_of_le_of_ne (Matrix.PosSemidef.trace_nonneg hS).1 (Ne.symm hStrace0)
  have hX : (X * X†).PosSemidef := amplitudeGram_pos X
  by_cases hXtrace0 : (X * X†).trace.re = 0
  · have hXtrace : (X * X†).trace = 0 := by
      apply Complex.ext
      · exact hXtrace0
      · exact (Matrix.PosSemidef.trace_nonneg hX).2.symm
    have hgramZero : X * X† = 0 :=
      (Matrix.PosSemidef.trace_eq_zero_iff hX).mp hXtrace
    have hXzero : X = 0 := Matrix.self_mul_conjTranspose_eq_zero.mp hgramZero
    refine ⟨reserveAmplitude (E := E) S, reserveAmplitude_gram S hS, ?_⟩
    have hpadzero : padBlockAmplitude (0 : Matrix B E Complex) = 0 := by
      ext b e
      cases e <;> rfl
    rw [hXzero, hpadzero]
    simp
  · exact exists_alignedBlockAmplitude X S hS
      (lt_of_le_of_ne (Matrix.PosSemidef.trace_nonneg hX).1 (Ne.symm hXtrace0))
      hStrace

/-- Any amplitude overlap is bounded by the fidelity of its two Gram matrices.
The left amplitude is embedded into the same reserve used by the block lift. -/
theorem amplitudeOverlap_le_traceNorm
    {D : Type*} [Fintype D] [DecidableEq D]
    [Nonempty B] (X : Matrix B E Complex) (Y : Matrix B (Sum E D) Complex) :
    Complex.abs (((padAmplitude (D := D) X)† * Y).trace) ≤
      traceNorm (psdSqrt (X * X†) * psdSqrt (Y * Y†)) := by
  classical
  let A : CMatrix B := X * X†
  let S : CMatrix B := Y * Y†
  have hA : A.PosSemidef := amplitudeGram_pos X
  have hS : S.PosSemidef := amplitudeGram_pos Y
  by_cases hAtrace0 : A.trace.re = 0
  · have hAtrace : A.trace = 0 := by
      apply Complex.ext
      · exact hAtrace0
      · exact (Matrix.PosSemidef.trace_nonneg hA).2.symm
    have hAzero : A = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hA).mp hAtrace
    have hXzero : X = 0 := Matrix.self_mul_conjTranspose_eq_zero.mp (by simpa [A] using hAzero)
    have hpadzero : padAmplitude (D := D) (0 : Matrix B E Complex) = 0 := by
      ext b e
      cases e <;> simp [padAmplitude]
    rw [hXzero, hpadzero]
    simp
  by_cases hStrace0 : S.trace.re = 0
  · have hStrace : S.trace = 0 := by
      apply Complex.ext
      · exact hStrace0
      · exact (Matrix.PosSemidef.trace_nonneg hS).2.symm
    have hSzero : S = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hS).mp hStrace
    have hYzero : Y = 0 := Matrix.self_mul_conjTranspose_eq_zero.mp (by simpa [S] using hSzero)
    simp [hYzero]
  have hAtrace : 0 < A.trace.re :=
    lt_of_le_of_ne (Matrix.PosSemidef.trace_nonneg hA).1 (Ne.symm hAtrace0)
  have hStrace : 0 < S.trace.re :=
    lt_of_le_of_ne (Matrix.PosSemidef.trace_nonneg hS).1 (Ne.symm hStrace0)
  let Xpad : Matrix B (Sum E D) Complex := padAmplitude X
  let rho : State B := stateOfPsdTracePos A hA hAtrace
  let sigma : State B := stateOfPsdTracePos S hS hStrace
  let cA : Complex := (((Real.sqrt A.trace.re)⁻¹ : Real) : Complex)
  let cS : Complex := (((Real.sqrt S.trace.re)⁻¹ : Real) : Complex)
  let Xn : Matrix B (Sum E D) Complex := cA • Xpad
  let Yn : Matrix B (Sum E D) Complex := cS • Y
  have hXnGram : Xn * Xn† = rho.matrix := by
    have hnorm := normalizedAmplitude_gram X hAtrace
    change (cA • Xpad) * (cA • Xpad)† = rho.matrix
    subst cA
    subst Xpad
    subst rho
    simpa only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, padAmplitude_gram] using hnorm
  have hYnGram : Yn * Yn† = sigma.matrix := by
    change (cS • Y) * (cS • Y)† = sigma.matrix
    subst cS
    subst sigma
    subst S
    exact normalizedAmplitude_gram Y hStrace
  have hXnTrace : (Xn * Xn†).trace = 1 := by rw [hXnGram, rho.trace_eq_one]
  have hYnTrace : (Yn * Yn†).trace = 1 := by rw [hYnGram, sigma.trace_eq_one]
  let psi : PureVector (Prod (Sum E D) B) :=
    PureVector.ofAmplitudeMatrix Xn hXnTrace
  let phi : PureVector (Prod (Sum E D) B) :=
    PureVector.ofAmplitudeMatrix Yn hYnTrace
  have hpsi : psi.Purifies rho :=
    PureVector.ofAmplitudeMatrix_purifies hXnGram hXnTrace
  have hphi : phi.Purifies sigma :=
    PureVector.ofAmplitudeMatrix_purifies hYnGram hYnTrace
  have hbound :
      Complex.abs ((Xn† * Yn).trace) ≤
        traceNorm (rho.sqrtMatrix * sigma.sqrtMatrix) := by
    have h := PureVector.abs_overlap_le_fidelity hpsi hphi
    have hoverlap : psi.overlap phi = (Xn† * Yn).trace := by
      rw [PureVector.overlap_eq_trace_conjTranspose_amplitudeMatrix_mul]
      simp [psi, phi, PureVector.ofAmplitudeMatrix_amplitudeMatrix]
    simpa [hoverlap, State.fidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix] using h
  let a : Real := Real.sqrt A.trace.re
  let s : Real := Real.sqrt S.trace.re
  let k : Real := a * s
  have ha : 0 < a := by simpa [a] using Real.sqrt_pos.mpr hAtrace
  have hs : 0 < s := by simpa [s] using Real.sqrt_pos.mpr hStrace
  have hk : 0 < k := mul_pos ha hs
  have hleft :
      Complex.abs ((Xn† * Yn).trace) =
        k⁻¹ * Complex.abs ((Xpad† * Y).trace) := by
    subst Xn
    subst Yn
    subst cA
    subst cS
    subst k
    subst a
    subst s
    simp [Matrix.conjTranspose_smul, Matrix.trace_smul, Complex.abs,
      Real.sqrt_nonneg, abs_of_nonneg, mul_assoc, mul_comm]
    ring
  have hright :
      traceNorm (rho.sqrtMatrix * sigma.sqrtMatrix) =
        k⁻¹ * traceNorm (psdSqrt A * psdSqrt S) := by
    rw [sqrtMatrix_stateOfPsdTracePos A hA hAtrace,
      sqrtMatrix_stateOfPsdTracePos S hS hStrace]
    subst k
    subst a
    subst s
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [← Complex.ofReal_mul]
    rw [traceNorm_real_smul_eq (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (inv_nonneg.mpr (Real.sqrt_nonneg _)))]
    congr 1
    field_simp [ha.ne', hs.ne']
  have hscaled := mul_le_mul_of_nonneg_left hbound hk.le
  rw [hleft, hright] at hscaled
  have hkne : k ≠ 0 := hk.ne'
  field_simp [hkne] at hscaled
  simpa [A, S, Xpad] using hscaled

end ProjectiveMeasurementLift

namespace SubnormalizedState

open scoped ComplexOrder MatrixOrder
open Matrix ProjectiveMeasurementLift

local postfix:1024 "†" => Matrix.conjTranspose

/-- Berta's copy-basis/projective-measurement lift.  A diagonal candidate near
the pinched center has a preimage near the unmeasured center at exactly the same
purified-distance radius.  The proof uses blockwise Uhlmann attainment on the
hat extension; no surjectivity property of a general channel is used. -/
theorem exists_projectiveMeasurementPreimage_of_purifiedBall
    {I : Type u} {B : Type v}
    [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
    (rho : State (Prod I B)) (sigma : SubnormalizedState (Prod I B))
    (epsilon : Real) (hsigma : sigma.sourceCoordinatePinch = sigma)
    (hball : rho.toSubnormalized.sourceCoordinatePinch.purifiedBall epsilon sigma) :
    Exists fun tau : SubnormalizedState (Prod I B) =>
      rho.toSubnormalized.purifiedBall epsilon tau /\
        tau.sourceCoordinatePinch = sigma := by
  classical
  letI : Nonempty (Prod I B) := rho.nonempty
  letI : Nonempty I := ⟨rho.nonempty.some.1⟩
  letI : Nonempty B := ⟨rho.nonempty.some.2⟩
  let psi : PureVector (Prod (Prod I B) (Prod I B)) := rho.canonicalPurification
  let X : Matrix (Prod I B) (Prod I B) Complex := psi.amplitudeMatrix
  let A : I → CMatrix B := fun i => Classical.block rho.matrix i i
  let S : I → CMatrix B := fun i => Classical.block sigma.matrix i i
  have hA : ∀ i, (A i).PosSemidef := by
    intro i
    exact rho.pos.submatrix (fun b : B => (i, b))
  have hS : ∀ i, (S i).PosSemidef := by
    intro i
    exact sigma.pos.submatrix (fun b : B => (i, b))
  let Xi : I → Matrix B (Prod I B) Complex := fun i => blockAmplitude X i
  have hXGram : X * X† = rho.matrix := by
    simpa [X, psi] using
      (PureVector.purifies_amplitudeMatrix_mul_conjTranspose_eq
        rho.canonicalPurification_purifies)
  have hXiGram : ∀ i, Xi i * (Xi i)† = A i := by
    intro i
    dsimp only [Xi]
    rw [blockAmplitude_gram_eq_block, hXGram]
  have hex : ∀ i, ∃ Yi : Matrix B (Sum (Prod I B) B) Complex,
      Yi * Yi† = S i /\
        (((padBlockAmplitude (Xi i))† * Yi).trace) =
          (traceNorm (psdSqrt (A i) * psdSqrt (S i)) : Complex) := by
    intro i
    simpa only [hXiGram i] using
      (exists_alignedBlockAmplitude_of_posSemidef (Xi i) (S i) (hS i))
  let Yi : I → Matrix B (Sum (Prod I B) B) Complex := fun i => (hex i).choose
  have hYiGram : ∀ i, Yi i * (Yi i)† = S i := fun i => (hex i).choose_spec.1
  have hYiOverlap : ∀ i,
      (((padBlockAmplitude (Xi i))† * Yi i).trace) =
        (traceNorm (psdSqrt (A i) * psdSqrt (S i)) : Complex) :=
    fun i => (hex i).choose_spec.2
  let Y : Matrix (Prod I B) (Sum (Prod I B) B) Complex :=
    fun ib e => Yi ib.1 ib.2 e
  have hYBlock : ∀ i, Classical.block (Y * Y†) i i = S i := by
    intro i
    rw [← blockAmplitude_gram_eq_block Y i]
    simpa only [Y, blockAmplitude] using hYiGram i
  have htrace : (Y * Y†).trace = sigma.matrix.trace := by
    calc
      (Y * Y†).trace =
          ∑ i : I, (Classical.block (Y * Y†) i i).trace :=
        (Classical.sum_block_trace (Y * Y†)).symm
      _ = ∑ i : I, (S i).trace := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hYBlock i]
      _ = sigma.matrix.trace := by
        rw [← Classical.sum_block_trace sigma.matrix]
  let tau : SubnormalizedState (Prod I B) := {
    matrix := Y * Y†
    pos := amplitudeGram_pos Y
    trace_le_one := by
      rw [htrace]
      exact sigma.trace_le_one }
  have hsigmaMatrix : Classical.blockDiagonal S = sigma.matrix := by
    have h := congrArg SubnormalizedState.matrix hsigma
    rw [sourceCoordinatePinch_matrix_eq_blockDiagonal] at h
    simpa only [S] using h
  have htauPinch : tau.sourceCoordinatePinch = sigma := by
    apply SubnormalizedState.ext
    rw [sourceCoordinatePinch_matrix_eq_blockDiagonal, ← hsigmaMatrix]
    apply congrArg Classical.blockDiagonal
    funext i
    simpa only [tau] using hYBlock i
  have hglobalOverlap :
      (((padAmplitude (D := B) X)† * Y).trace) =
        ∑ i : I,
          (traceNorm (psdSqrt (A i) * psdSqrt (S i)) : Complex) := by
    calc
      (((padAmplitude (D := B) X)† * Y).trace) =
          ∑ i : I, (((padBlockAmplitude (Xi i))† * Yi i).trace) := by
        rw [padAmplitude_inner]
        simp_rw [padBlockAmplitude_inner]
        simp only [Y, Xi, blockAmplitude]
        calc
          (∑ e : Prod I B, ∑ ib : Prod I B,
              star (X ib e) * Yi ib.1 ib.2 (Sum.inl e)) =
              ∑ e : Prod I B, ∑ i : I, ∑ b : B,
                star (X (i, b) e) * Yi i b (Sum.inl e) := by
            apply Finset.sum_congr rfl
            intro e _
            rw [Fintype.sum_prod_type]
          _ = ∑ i : I, ∑ e : Prod I B, ∑ b : B,
              star (X (i, b) e) * Yi i b (Sum.inl e) := by
            rw [Finset.sum_comm]
      _ = ∑ i : I,
          (traceNorm (psdSqrt (A i) * psdSqrt (S i)) : Complex) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hYiOverlap i
  have hsumNonneg :
      0 ≤ ∑ i : I, traceNorm (psdSqrt (A i) * psdSqrt (S i)) :=
    Finset.sum_nonneg fun i _ => traceNorm_nonneg _
  have habsOverlap :
      Complex.abs (((padAmplitude (D := B) X)† * Y).trace) =
        ∑ i : I, traceNorm (psdSqrt (A i) * psdSqrt (S i)) := by
    rw [hglobalOverlap]
    have hcast :
        (∑ i : I, (traceNorm (psdSqrt (A i) * psdSqrt (S i)) : Complex)) =
          ((∑ i : I, traceNorm (psdSqrt (A i) * psdSqrt (S i)) : Real) : Complex) := by
      apply Complex.ext <;> simp
    rw [hcast]
    change ‖((∑ i : I, traceNorm (psdSqrt (A i) * psdSqrt (S i)) : Real) : Complex)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsumNonneg]
  have hoverlapBound := amplitudeOverlap_le_traceNorm X Y
  rw [hXGram] at hoverlapBound
  have hright :
      ∑ i : I, traceNorm (psdSqrt (A i) * psdSqrt (S i)) ≤
        traceNorm (psdSqrt rho.matrix * psdSqrt tau.matrix) := by
    rw [← habsOverlap]
    simpa only [tau] using hoverlapBound
  have hnorm :
      traceNorm
          (psdSqrt rho.toSubnormalized.sourceCoordinatePinch.matrix *
            psdSqrt sigma.matrix) ≤
        traceNorm (psdSqrt rho.toSubnormalized.matrix * psdSqrt tau.matrix) := by
    rw [sourceCoordinatePinch_matrix_eq_blockDiagonal, State.toSubnormalized_matrix,
      ← hsigmaMatrix]
    change traceNorm (psdSqrt (Classical.blockDiagonal A) *
      psdSqrt (Classical.blockDiagonal S)) ≤ _
    rw [Classical.traceNorm_psdSqrt_blockDiagonal_mul_psdSqrt_blockDiagonal A S hA hS]
    simpa only [A, S, State.toSubnormalized_matrix] using hright
  have hpinchTrace :
      rho.toSubnormalized.sourceCoordinatePinch.matrix.trace.re = 1 := by
    rw [sourceCoordinatePinch_trace_re, State.toSubnormalized_matrix, rho.trace_eq_one]
    norm_num
  have hrhoTrace : rho.toSubnormalized.matrix.trace.re = 1 := by
    rw [State.toSubnormalized_matrix, rho.trace_eq_one]
    norm_num
  have hfid :
      rho.toSubnormalized.sourceCoordinatePinch.generalizedFidelity sigma ≤
        rho.toSubnormalized.generalizedFidelity tau :=
    generalizedFidelity_le_of_traceNorm_psdSqrt_mul_le_of_trace_one
      hpinchTrace hrhoTrace hnorm
  have hhat :
      (rho.toSubnormalized.sourceCoordinatePinch.hatExtension :
          State (Sum PUnit.{max u v + 1} (Prod I B))).purifiedBall epsilon
        (sigma.hatExtension : State (Sum PUnit.{max u v + 1} (Prod I B))) :=
    (purifiedBall_iff_hatExtension_purifiedBall
      rho.toSubnormalized.sourceCoordinatePinch sigma epsilon).mp hball
  have hhatF :
      (rho.toSubnormalized.sourceCoordinatePinch.hatExtension :
          State (Sum PUnit.{max u v + 1} (Prod I B))).squaredFidelity
          (sigma.hatExtension : State (Sum PUnit.{max u v + 1} (Prod I B))) ≤
        (rho.toSubnormalized.hatExtension :
          State (Sum PUnit.{max u v + 1} (Prod I B))).squaredFidelity
          (tau.hatExtension : State (Sum PUnit.{max u v + 1} (Prod I B))) := by
    simpa only [← generalizedFidelity_eq_squaredFidelity_hatExtension] using hfid
  have hhatBall :
      (rho.toSubnormalized.hatExtension :
          State (Sum PUnit.{max u v + 1} (Prod I B))).purifiedBall epsilon
        (tau.hatExtension : State (Sum PUnit.{max u v + 1} (Prod I B))) :=
    State.purifiedBall_of_squaredFidelity_le hhatF hhat
  refine ⟨tau, ?_, htauPinch⟩
  exact (purifiedBall_iff_hatExtension_purifiedBall
    rho.toSubnormalized tau epsilon).mpr hhatBall

end SubnormalizedState

open scoped ComplexOrder MatrixOrder

/-- Fixed-reference feasibility survives the coherent projective lift.  The
diagonal record blocks may carry different probabilities, but they all use the
same side-information state.  This is the matrix-order step behind Berta's
projective-measurement smooth-min-entropy argument. -/
theorem projectiveRecorded_conditionalMinEntropyFeasible
    {I : Type u} {A' : Type v} {R : Type w}
    [Fintype I] [DecidableEq I]
    [Fintype A'] [DecidableEq A']
    [Fintype R] [DecidableEq R]
    (tau : State (Prod I (Prod A' R))) (sigmaR : State R)
    (weights : I → Real) (hweights_nonneg : ∀ i, 0 ≤ weights i)
    (hweights_sum : ∑ i, weights i = 1) (lam : Real)
    (hblocks : ∀ i,
      Classical.block tau.matrix i i ≤
        (weights i : Complex) •
          ((Real.rpow 2 (-lam) : Complex) •
            State.identityTensorStateMatrix (a := A') sigmaR)) :
    State.ConditionalMinEntropyFeasible (a := Prod A' I)
      (tau.reindex (projectiveSourceReferenceEquiv I A' R)) sigmaR lam := by
  classical
  let Q : CMatrix (Prod A' R) :=
    (Real.rpow 2 (-lam) : Complex) •
      State.identityTensorStateMatrix (a := A') sigmaR
  have hcpos : 0 < Real.rpow 2 (-lam) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hQ : Q.PosSemidef := by
    exact Matrix.PosSemidef.smul
      (State.identityTensorStateMatrix_posSemidef (a := A') sigmaR)
      (by exact_mod_cast hcpos.le)
  have hglobal :
      tau.matrix ≤ Matrix.kronecker (1 : CMatrix I) Q :=
    ProjectiveMeasurementLift.matrix_le_identity_kronecker_of_diagonal_blocks_le
      tau.matrix tau.pos Q hQ weights hweights_nonneg hweights_sum
      (by simpa only [Q] using hblocks)
  let e := projectiveSourceReferenceEquiv I A' R
  have hreference :
      (Matrix.kronecker (1 : CMatrix I) Q).submatrix e.symm e.symm =
        (Real.rpow 2 (-lam) : Complex) •
          State.identityTensorStateMatrix (a := Prod A' I) sigmaR := by
    ext x y
    rcases x with ⟨⟨a, i⟩, r⟩
    rcases y with ⟨⟨a', i'⟩, r'⟩
    simp [e, Q, projectiveSourceReferenceEquiv,
      State.identityTensorStateMatrix, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.one_apply]
    by_cases ha : a = a' <;> by_cases hi : i = i' <;> simp [ha, hi]
  rw [State.ConditionalMinEntropyFeasible, Matrix.le_iff]
  have hsub := (Matrix.le_iff.mp hglobal).submatrix e.symm
  change
    ((Matrix.kronecker (1 : CMatrix I) Q).submatrix e.symm e.symm -
      tau.matrix.submatrix e.symm e.symm).PosSemidef at hsub
  rw [hreference] at hsub
  simpa only [State.reindex_matrix] using hsub

namespace FiniteInstrument

variable {A : Type u} {A' : Type v} {R : Type w} {E : Type x} {X : Type*}
variable [Fintype A] [DecidableEq A]
variable [Fintype A'] [DecidableEq A']
variable [Fintype R] [DecidableEq R]
variable [Fintype E] [DecidableEq E]
variable [Fintype X]

local instance outcomeDecidableEq : DecidableEq X := Classical.decEq _

local instance positiveSupportDecidableEq
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E))) :
    DecidableEq (M.positiveSupport psi) :=
  Classical.decEq _

/-- The positive refined Alice branches, with their physical probabilities
and normalized `A'R` states.  Zero-probability Kraus branches are absent from
the classical alphabet rather than being assigned an arbitrary state. -/
def recordedSourceReferenceEnsemble
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E))) :
    Ensemble (M.positiveSupport psi) (Prod A' R) where
  probs i := M.branchWeight psi i.1
  weights_sum := M.sum_positiveSupport_branchWeight_eq_one psi
  states i := M.positiveBranchSourceReferenceState psi i

/-- The physical refined-outcome cq center, represented as
`A' | (R x I)` for conditional min-entropy. -/
def recordedSourceReferenceState
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E))) :
    State (Prod A' (Prod R (M.positiveSupport psi))) :=
  (M.recordedSourceReferenceEnsemble psi).cqState.reindex
    (finiteInstrumentRecordedSourceReferenceEquiv
      (M.positiveSupport psi) A' R)

/-- The same refined-outcome distribution paired with one common untouched
reference state.  Keeping this reference fixed across all branches is the
essential hypothesis in Berta's projective smooth-min-entropy lift. -/
def recordedFixedReferenceEnsemble
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (sigmaR : State R) :
    Ensemble (M.positiveSupport psi) R where
  probs i := M.branchWeight psi i.1
  weights_sum := M.sum_positiveSupport_branchWeight_eq_one psi
  states _ := sigmaR

/-- The common fixed reference on `R x I`, with the physical refined-branch
weights on the classical record. -/
def recordedFixedReferenceState
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (sigmaR : State R) :
    State (Prod R (M.positiveSupport psi)) :=
  (M.recordedFixedReferenceEnsemble psi sigmaR).cqState.reindex
    (Equiv.prodComm (M.positiveSupport psi) R)

/-- The source-faithful ideal endpoint used in the one-shot converse: a
uniform retained register independent of the fixed recorded reference. -/
def recordedMaximallyMixedFixedReferenceState
    [Nonempty A']
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (sigmaR : State R) :
    State (Prod A' (Prod R (M.positiveSupport psi))) :=
  (State.maximallyMixed A').prod (M.recordedFixedReferenceState psi sigmaR)

/-- Complete-record physical ensemble.  Zero-probability refined branches use
an arbitrary normalized filler whose weight is zero. -/
def fullRecordedSourceReferenceEnsemble
    [Nonempty A'] [Nonempty R]
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E))) :
    Ensemble M.refinedBranchIndex (Prod A' R) where
  probs i := M.branchWeight psi i
  weights_sum := M.sum_branchWeight_eq_one psi
  states i :=
    if hi : 0 < M.branchWeight psi i then
      M.positiveBranchSourceReferenceState psi ⟨i, hi⟩
    else
      State.maximallyMixed (Prod A' R)

/-- Complete-record ideal ensemble with the same physical branch weights and
one common maximally-mixed/source-reference product state. -/
def fullRecordedIdealReferenceEnsemble
    [Nonempty A']
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (sigmaR : State R) :
    Ensemble M.refinedBranchIndex (Prod A' R) where
  probs i := M.branchWeight psi i
  weights_sum := M.sum_branchWeight_eq_one psi
  states _ := (State.maximallyMixed A').prod sigmaR

/-- The positive-record version of the fixed ideal ensemble. -/
def recordedIdealReferenceEnsemble
    [Nonempty A']
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (sigmaR : State R) :
    Ensemble (M.positiveSupport psi) (Prod A' R) where
  probs i := M.branchWeight psi i.1
  weights_sum := M.sum_positiveSupport_branchWeight_eq_one psi
  states _ := (State.maximallyMixed A').prod sigmaR

/-- Embed the positive refined record into the complete refined record. -/
def positiveRecordSourceIsometry
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E))) :
    ReferenceIsometry (M.positiveSupport psi) M.refinedBranchIndex :=
  ReferenceIsometry.ofInjective Subtype.val Subtype.val_injective

/-- Each weighted complete-record physical branch is its unnormalized branch
Gram matrix, including the zero-probability case. -/
theorem fullRecordedSourceReferenceEnsemble_weightedState_matrix
    [Nonempty A'] [Nonempty R]
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (i : M.refinedBranchIndex) :
    (M.fullRecordedSourceReferenceEnsemble psi).probs i •
        ((M.fullRecordedSourceReferenceEnsemble psi).states i).matrix =
      M.branchSourceReferenceAmplitude psi i *
        Matrix.conjTranspose (M.branchSourceReferenceAmplitude psi i) := by
  classical
  by_cases hi : 0 < M.branchWeight psi i
  · simpa [fullRecordedSourceReferenceEnsemble, hi] using
      M.branchWeight_smul_positiveBranchSourceReferenceState_matrix
        psi ⟨i, hi⟩
  · have hzero : M.branchWeight psi i = 0 :=
      le_antisymm (not_lt.mp hi) bot_le
    have hamp := M.branchSourceReferenceAmplitude_eq_zero_of_branchWeight_eq_zero
      psi i hzero
    simp [fullRecordedSourceReferenceEnsemble, hzero, hamp]

/-- The complete fixed-reference ideal cq state is already projectively
dephased. -/
theorem fullRecordedIdealReferenceEnsemble_sourceCoordinatePinch
    [Nonempty A']
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (sigmaR : State R) :
    ((M.fullRecordedIdealReferenceEnsemble psi sigmaR).cqState.toSubnormalized).sourceCoordinatePinch =
      (M.fullRecordedIdealReferenceEnsemble psi sigmaR).cqState.toSubnormalized := by
  apply SubnormalizedState.ext
  rw [SubnormalizedState.sourceCoordinatePinch_matrix_eq_blockDiagonal,
    State.toSubnormalized_matrix]
  exact (Classical.cqState_eq_blockDiagonal_blocks
    (M.fullRecordedIdealReferenceEnsemble psi sigmaR)).symm

/-- The complete physical cq matrix is the positive-support sum, because all
other refined branches have zero probability. -/
theorem fullRecordedSourceReferenceEnsemble_cqState_matrix_eq_positiveSupport_sum
    [Nonempty A'] [Nonempty R]
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E))) :
    (M.fullRecordedSourceReferenceEnsemble psi).cqState.matrix =
      ∑ i : M.positiveSupport psi,
        M.branchWeight psi i.1 •
          Matrix.kronecker (Matrix.single i.1 i.1 (1 : Complex))
            (M.positiveBranchSourceReferenceState psi i).matrix := by
  classical
  rw [Ensemble.cqState_matrix]
  conv_lhs =>
    rw [← Fintype.sum_subtype_add_sum_subtype
      (fun i : M.refinedBranchIndex => 0 < M.branchWeight psi i)
      (fun i =>
        (M.fullRecordedSourceReferenceEnsemble psi).probs i •
          Matrix.kronecker (Matrix.single i i (1 : Complex))
            ((M.fullRecordedSourceReferenceEnsemble psi).states i).matrix)]
  have hzero :
      (∑ i : {i : M.refinedBranchIndex // ¬ 0 < M.branchWeight psi i},
        (M.fullRecordedSourceReferenceEnsemble psi).probs i.1 •
          Matrix.kronecker (Matrix.single i.1 i.1 (1 : Complex))
            ((M.fullRecordedSourceReferenceEnsemble psi).states i.1).matrix) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    have hweight : M.branchWeight psi i.1 = 0 :=
      le_antisymm (not_lt.mp i.2) bot_le
    simp [fullRecordedSourceReferenceEnsemble, hweight]
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro i _hi
  simp [fullRecordedSourceReferenceEnsemble, i.2]

/-- The complete ideal cq matrix is likewise the positive-support sum. -/
theorem fullRecordedIdealReferenceEnsemble_cqState_matrix_eq_positiveSupport_sum
    [Nonempty A']
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (sigmaR : State R) :
    (M.fullRecordedIdealReferenceEnsemble psi sigmaR).cqState.matrix =
      ∑ i : M.positiveSupport psi,
        M.branchWeight psi i.1 •
          Matrix.kronecker (Matrix.single i.1 i.1 (1 : Complex))
            ((State.maximallyMixed A').prod sigmaR).matrix := by
  classical
  rw [Ensemble.cqState_matrix]
  conv_lhs =>
    rw [← Fintype.sum_subtype_add_sum_subtype
      (fun i : M.refinedBranchIndex => 0 < M.branchWeight psi i)
      (fun i =>
        (M.fullRecordedIdealReferenceEnsemble psi sigmaR).probs i •
          Matrix.kronecker (Matrix.single i i (1 : Complex))
            ((M.fullRecordedIdealReferenceEnsemble psi sigmaR).states i).matrix)]
  have hzero :
      (∑ i : {i : M.refinedBranchIndex // ¬ 0 < M.branchWeight psi i},
        (M.fullRecordedIdealReferenceEnsemble psi sigmaR).probs i.1 •
          Matrix.kronecker (Matrix.single i.1 i.1 (1 : Complex))
            ((M.fullRecordedIdealReferenceEnsemble psi sigmaR).states i.1).matrix) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    have hweight : M.branchWeight psi i.1 = 0 :=
      le_antisymm (not_lt.mp i.2) bot_le
    simp [fullRecordedIdealReferenceEnsemble, hweight]
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro i _hi
  simp [fullRecordedIdealReferenceEnsemble]

/-- Padding the positive physical record by the source-label isometry gives
the complete physical cq record. -/
theorem recordedSourceReferenceEnsemble_sourceIsometryApply
    [Nonempty A'] [Nonempty R]
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E))) :
    (M.recordedSourceReferenceEnsemble psi).cqState.toSubnormalized.sourceIsometryApply
        (M.positiveRecordSourceIsometry psi) =
      (M.fullRecordedSourceReferenceEnsemble psi).cqState.toSubnormalized := by
  classical
  apply SubnormalizedState.ext
  rw [SubnormalizedState.sourceIsometryApply_matrix,
    State.toSubnormalized_matrix, State.toSubnormalized_matrix]
  rw [← MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft]
  change
    MatrixMap.kron
        (MatrixMap.ofReferenceIsometry (M.positiveRecordSourceIsometry psi))
        (Channel.idChannel (Prod A' R)).map
        (M.recordedSourceReferenceEnsemble psi).cqState.matrix =
      (M.fullRecordedSourceReferenceEnsemble psi).cqState.matrix
  rw [Ensemble.cqState_matrix,
    M.fullRecordedSourceReferenceEnsemble_cqState_matrix_eq_positiveSupport_sum psi]
  simp only [NNReal.smul_def, recordedSourceReferenceEnsemble]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [LinearMap.map_smul_of_tower, MatrixMap.kron_apply_kronecker]
  congr 1
  rw [positiveRecordSourceIsometry,
    MatrixMap.ofReferenceIsometry_ofInjective_single
      Subtype.val Subtype.val_injective i i]
  simp [Channel.idChannel, MatrixMap.ofKraus]

/-- Padding the positive ideal record by the same source-label isometry gives
the complete ideal cq record. -/
theorem recordedIdealReferenceEnsemble_sourceIsometryApply
    [Nonempty A']
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (sigmaR : State R) :
    (M.recordedIdealReferenceEnsemble psi sigmaR).cqState.toSubnormalized.sourceIsometryApply
        (M.positiveRecordSourceIsometry psi) =
      (M.fullRecordedIdealReferenceEnsemble psi sigmaR).cqState.toSubnormalized := by
  classical
  apply SubnormalizedState.ext
  rw [SubnormalizedState.sourceIsometryApply_matrix,
    State.toSubnormalized_matrix, State.toSubnormalized_matrix]
  rw [← MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft]
  change
    MatrixMap.kron
        (MatrixMap.ofReferenceIsometry (M.positiveRecordSourceIsometry psi))
        (Channel.idChannel (Prod A' R)).map
        (M.recordedIdealReferenceEnsemble psi sigmaR).cqState.matrix =
      (M.fullRecordedIdealReferenceEnsemble psi sigmaR).cqState.matrix
  rw [Ensemble.cqState_matrix,
    M.fullRecordedIdealReferenceEnsemble_cqState_matrix_eq_positiveSupport_sum psi sigmaR]
  simp only [NNReal.smul_def, recordedIdealReferenceEnsemble]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [LinearMap.map_smul_of_tower, MatrixMap.kron_apply_kronecker]
  congr 1
  rw [positiveRecordSourceIsometry,
    MatrixMap.ofReferenceIsometry_ofInjective_single
      Subtype.val Subtype.val_injective i i]
  simp [Channel.idChannel, MatrixMap.ofKraus]

/-- The product-form ideal used by the operational converse is exactly the
positive fixed-reference cq ensemble in the standard recorded-state order. -/
theorem recordedMaximallyMixedFixedReferenceState_eq_recordedIdealReferenceEnsemble
    [Nonempty A']
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (sigmaR : State R) :
    M.recordedMaximallyMixedFixedReferenceState psi sigmaR =
      (M.recordedIdealReferenceEnsemble psi sigmaR).cqState.reindex
        (finiteInstrumentRecordedSourceReferenceEquiv
          (M.positiveSupport psi) A' R) := by
  classical
  apply State.ext
  ext i j
  simp [recordedMaximallyMixedFixedReferenceState, recordedFixedReferenceState,
    recordedFixedReferenceEnsemble, recordedIdealReferenceEnsemble,
    finiteInstrumentRecordedSourceReferenceEquiv, Ensemble.cqState,
    State.reindex, State.prod, State.maximallyMixed, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  simp [NNReal.smul_def, mul_assoc, mul_comm]
  ring

/-- The Stinespring isometry of the complete refined Kraus family.  The
environment records both the operational outcome and the chosen Kraus index.
This uses all refined branches: restricting the matrix to the positive support
of one particular input would not be an isometry on arbitrary inputs. -/
def refinedStinespringIsometry
    (M : FiniteInstrument A A' X) :
    ReferenceIsometry A (Prod A' M.refinedBranchIndex) where
  matrix := MatrixMap.krausStinespringMatrix M.refinedKraus
  isometry := by
    apply MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one
    simpa [MatrixMap.krausAdjoint] using
      M.sum_conjTranspose_refinedKraus_mul_refinedKraus

@[simp]
theorem refinedStinespringIsometry_matrix_apply
    (M : FiniteInstrument A A' X) (a'i : Prod A' M.refinedBranchIndex) (a : A) :
    (M.refinedStinespringIsometry).matrix a'i a =
      M.refinedKraus a'i.2 a'i.1 a :=
  rfl

/-- The coherent refined-instrument output before its Kraus record is
projectively dephased.  This is the enlarged-source center that is compressed
back to `sourceReferenceState` after the Berta Uhlmann lift. -/
def coherentSourceReferenceState
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E))) :
    SubnormalizedState (Prod (Prod A' M.refinedBranchIndex) R) :=
  (sourceReferenceState psi).toSubnormalized.sourceIsometryApply
    M.refinedStinespringIsometry

@[simp]
theorem coherentSourceReferenceState_trace_re
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E))) :
    (M.coherentSourceReferenceState psi).matrix.trace.re = 1 := by
  rw [coherentSourceReferenceState,
    SubnormalizedState.sourceIsometryApply_trace_re]
  change (sourceReferenceState psi).matrix.trace.re = 1
  rw [(sourceReferenceState psi).trace_eq_one]
  norm_num

/-- The coherent refined-instrument output has trace one, so it can be used as
the normalized center in the projective Uhlmann lift. -/
def coherentSourceReferenceNormalizedState
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E))) :
    State (Prod (Prod A' M.refinedBranchIndex) R) where
  matrix := (M.coherentSourceReferenceState psi).matrix
  pos := (M.coherentSourceReferenceState psi).pos
  trace_eq_one := by
    apply Complex.ext
    · exact M.coherentSourceReferenceState_trace_re psi
    · exact (M.coherentSourceReferenceState psi).trace_im_zero

/-- Reorder the coherent output so that the complete refined record is the
coordinate measured by the projective lift. -/
def coherentProjectiveSourceReferenceState
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E))) :
    State (Prod M.refinedBranchIndex (Prod A' R)) :=
  (M.coherentSourceReferenceNormalizedState psi).reindex
    (projectiveSourceReferenceEquiv M.refinedBranchIndex A' R).symm

/-- Reassociating the projective coherent state back to `A'I | R` recovers
the original coherent subnormalized state. -/
theorem coherentProjectiveSourceReferenceState_reindex_toSubnormalized
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E))) :
    ((M.coherentProjectiveSourceReferenceState psi).reindex
        (projectiveSourceReferenceEquiv M.refinedBranchIndex A' R)).toSubnormalized =
      M.coherentSourceReferenceState psi := by
  apply SubnormalizedState.ext
  simp [coherentProjectiveSourceReferenceState,
    coherentSourceReferenceNormalizedState, State.reindex]

/-- Each diagonal block of the coherent refined output is the unnormalized
Gram matrix of that refined branch. -/
theorem coherentProjectiveSourceReferenceState_block
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (i : M.refinedBranchIndex) :
    Classical.block (M.coherentProjectiveSourceReferenceState psi).matrix i i =
      M.branchSourceReferenceAmplitude psi i *
        Matrix.conjTranspose (M.branchSourceReferenceAmplitude psi i) := by
  classical
  rw [M.branchSourceReferenceAmplitude_eq_kronecker_mul psi i,
    Matrix.conjTranspose_mul]
  ext ar ar'
  rcases ar with ⟨a', r⟩
  rcases ar' with ⟨a'', r'⟩
  simp only [coherentProjectiveSourceReferenceState, State.reindex_matrix,
    coherentSourceReferenceNormalizedState, coherentSourceReferenceState,
    SubnormalizedState.sourceIsometryApply_matrix,
    Classical.block, Matrix.submatrix_apply, projectiveSourceReferenceEquiv]
  change
    (M.refinedStinespringIsometry.matrix *
        ReferenceIsometry.targetBlock
          (sourceReferenceAmplitude psi *
            Matrix.conjTranspose (sourceReferenceAmplitude psi)) r r' *
        Matrix.conjTranspose M.refinedStinespringIsometry.matrix)
          (a', i) (a'', i) =
      ((Matrix.kronecker (M.refinedKraus i) (1 : CMatrix R) *
          sourceReferenceAmplitude psi) *
        (Matrix.conjTranspose (sourceReferenceAmplitude psi) *
          Matrix.conjTranspose
            (Matrix.kronecker (M.refinedKraus i) (1 : CMatrix R))))
          (a', r) (a'', r')
  have hstarIf (x : A) (s : R) :
      star (if r' = s then M.refinedKraus i a'' x else 0) =
        if r' = s then star (M.refinedKraus i a'' x) else 0 := by
    by_cases h : r' = s
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      exact map_zero (starRingEnd Complex)
  simp only [ReferenceIsometry.targetBlock, refinedStinespringIsometry_matrix_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul]
  simp only [mul_ite, mul_one, mul_zero]
  simp_rw [hstarIf]
  simp only [mul_ite, ite_mul, zero_mul, mul_zero
    ]
  simp [ Finset.sum_ite_eq]
  conv_lhs =>
    enter [2, j]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- Projectively dephasing the coherent refined output gives the complete
physical cq record. -/
theorem coherentProjectiveSourceReferenceState_sourceCoordinatePinch
    [Nonempty A'] [Nonempty R]
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E))) :
    ((M.coherentProjectiveSourceReferenceState psi).toSubnormalized).sourceCoordinatePinch =
      (M.fullRecordedSourceReferenceEnsemble psi).cqState.toSubnormalized := by
  classical
  apply SubnormalizedState.ext
  rw [SubnormalizedState.sourceCoordinatePinch_matrix_eq_blockDiagonal,
    State.toSubnormalized_matrix]
  change
    Classical.blockDiagonal
        (fun i => Classical.block
          (M.coherentProjectiveSourceReferenceState psi).matrix i i) =
      (M.fullRecordedSourceReferenceEnsemble psi).cqState.matrix
  rw [Classical.cqState_eq_blockDiagonal]
  apply congrArg Classical.blockDiagonal
  funext i
  rw [M.coherentProjectiveSourceReferenceState_block psi i]
  exact (M.fullRecordedSourceReferenceEnsemble_weightedState_matrix psi i).symm

/-- A purified ball between the operational positive-record states transports
to the complete projective record used by Berta's Uhlmann lift. -/
theorem recordedFixedReference_purifiedBall_projective
    [Nonempty A'] [Nonempty R]
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (sigmaR : State R) {epsilon : Real}
    (hball :
      (M.recordedSourceReferenceState psi).toSubnormalized.purifiedBall epsilon
        (M.recordedMaximallyMixedFixedReferenceState psi sigmaR).toSubnormalized) :
    (((M.coherentProjectiveSourceReferenceState psi).toSubnormalized).sourceCoordinatePinch)
        |>.purifiedBall epsilon
          (M.fullRecordedIdealReferenceEnsemble psi sigmaR).cqState.toSubnormalized := by
  let e := finiteInstrumentRecordedSourceReferenceEquiv
    (M.positiveSupport psi) A' R
  rw [M.recordedMaximallyMixedFixedReferenceState_eq_recordedIdealReferenceEnsemble
    psi sigmaR] at hball
  have hballCqRaw := State.toSubnormalized_purifiedBall_reindex e.symm hball
  have hballCq :
      (M.recordedSourceReferenceEnsemble psi).cqState.toSubnormalized.purifiedBall
        epsilon
        (M.recordedIdealReferenceEnsemble psi sigmaR).cqState.toSubnormalized := by
    simpa [e, recordedSourceReferenceState, State.reindex] using hballCqRaw
  have hballFull :=
    SubnormalizedState.purifiedBall_sourceIsometryApply
      (M.positiveRecordSourceIsometry psi) hballCq
  rw [M.recordedSourceReferenceEnsemble_sourceIsometryApply psi,
    M.recordedIdealReferenceEnsemble_sourceIsometryApply psi sigmaR] at hballFull
  rw [M.coherentProjectiveSourceReferenceState_sourceCoordinatePinch psi]
  exact hballFull

/-- The general-instrument Stinespring part of Berta's smooth lift is already
handled by source-isometry compression: a candidate around the coherent
refined output compresses to a candidate around the input center at the same
purified-distance radius, with no smaller ordinary min-entropy endpoint. -/
theorem coherentSourceReferenceCandidate_compress
    [Nonempty A] [Nonempty A'] [Nonempty R] [Nonempty X]
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    {epsilon h : Real} (hepsilon : epsilon < 1)
    (hcand :
      SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw
        (a := Prod A' M.refinedBranchIndex)
        (M.coherentSourceReferenceState psi) epsilon h) :
    Exists fun h' : Real =>
      And
        (SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw
          (a := A) (sourceReferenceState psi).toSubnormalized epsilon h')
        (h <= h') := by
  have hepsilonSource :
      epsilon < Real.sqrt
        (sourceReferenceState psi).toSubnormalized.matrix.trace.re := by
    change epsilon < Real.sqrt (sourceReferenceState psi).matrix.trace.re
    rw [(sourceReferenceState psi).trace_eq_one, Complex.one_re, Real.sqrt_one]
    exact hepsilon
  simpa only [coherentSourceReferenceState] using
    (SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw.sourceIsometryApply_compress
      (sourceReferenceState psi).toSubnormalized M.refinedStinespringIsometry
      hepsilonSource hcand)

/-- Berta's common-fixed-reference projective lift, specialized to the actual
uniform retained-register endpoint used by state merging.  A candidate near
the recorded ideal state lifts through the coherent instrument and compresses
back to the pre-instrument source without losing the `log₂ |A'|` bound. -/
theorem recordedFixedReferenceCandidate_compress
    [Nonempty A] [Nonempty A'] [Nonempty R] [Nonempty X]
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (sigmaR : State R) {epsilon : Real} (hepsilon : epsilon < 1)
    (hball :
      (M.recordedSourceReferenceState psi).toSubnormalized.purifiedBall epsilon
        (M.recordedMaximallyMixedFixedReferenceState psi sigmaR).toSubnormalized) :
    ∃ h' : Real,
      SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw
          (a := A) (sourceReferenceState psi).toSubnormalized epsilon h' ∧
        log2 (Fintype.card A' : Real) ≤ h' := by
  classical
  let rhoProjective := M.coherentProjectiveSourceReferenceState psi
  let idealFull := (M.fullRecordedIdealReferenceEnsemble psi sigmaR).cqState
  have hprojectiveBall :
      rhoProjective.toSubnormalized.sourceCoordinatePinch.purifiedBall epsilon
        idealFull.toSubnormalized := by
    simpa only [rhoProjective, idealFull] using
      M.recordedFixedReference_purifiedBall_projective psi sigmaR hball
  obtain ⟨tau, hcoherentBall, htauPinch⟩ :=
    SubnormalizedState.exists_projectiveMeasurementPreimage_of_purifiedBall
      rhoProjective idealFull.toSubnormalized epsilon
      (by
        simpa only [idealFull] using
          M.fullRecordedIdealReferenceEnsemble_sourceCoordinatePinch psi sigmaR)
      hprojectiveBall
  have htauTraceRe : tau.matrix.trace.re = 1 := by
    calc
      tau.matrix.trace.re =
          tau.sourceCoordinatePinch.matrix.trace.re :=
        (SubnormalizedState.sourceCoordinatePinch_trace_re tau).symm
      _ = idealFull.toSubnormalized.matrix.trace.re := by rw [htauPinch]
      _ = 1 := by
        rw [State.toSubnormalized_matrix, idealFull.trace_eq_one]
        norm_num
  let tauState : State (Prod M.refinedBranchIndex (Prod A' R)) := {
    matrix := tau.matrix
    pos := tau.pos
    trace_eq_one := by
      apply Complex.ext
      · exact htauTraceRe
      · simpa using tau.trace_im_zero }
  have htauStateToSubnormalized : tauState.toSubnormalized = tau := by
    apply SubnormalizedState.ext
    rfl
  have hblockEq (i : M.refinedBranchIndex) :
      Classical.block tauState.matrix i i =
        (M.branchWeight psi i : Complex) •
          ((State.maximallyMixed A').prod sigmaR).matrix := by
    have hmatrix := congrArg SubnormalizedState.matrix htauPinch
    have hblock := congrArg (fun T => Classical.block T i i) hmatrix
    rw [SubnormalizedState.sourceCoordinatePinch_matrix_eq_blockDiagonal] at hblock
    change
      Classical.block
          (Classical.blockDiagonal fun x => Classical.block tau.matrix x x) i i =
        Classical.block idealFull.matrix i i at hblock
    rw [Classical.blockDiagonal_block_self] at hblock
    dsimp only [idealFull] at hblock
    rw [Classical.cqState_block_self] at hblock
    simpa [tauState, idealFull, fullRecordedIdealReferenceEnsemble] using hblock
  have hblocks : ∀ i : M.refinedBranchIndex,
      Classical.block tauState.matrix i i ≤
        (((M.branchWeight psi i : Real) : Complex)) •
          ((Real.rpow 2 (-log2 (Fintype.card A' : Real)) : Complex) •
            State.identityTensorStateMatrix (a := A') sigmaR) := by
    intro i
    have hbase :=
      State.conditionalMinEntropyFeasible_maximallyMixed_prod (a := A') sigmaR
    have hweightComplex :
        (0 : Complex) ≤ ((M.branchWeight psi i : Real) : Complex) := by
      exact_mod_cast M.branchWeight_nonneg psi i
    have hscaled := (Matrix.le_iff.mp hbase).smul hweightComplex
    rw [Matrix.le_iff, hblockEq i]
    simpa [smul_sub] using hscaled
  have hweightsNonneg :
      ∀ i : M.refinedBranchIndex, 0 ≤ (M.branchWeight psi i : Real) :=
    M.branchWeight_nonneg psi
  have hweightsSum :
      (∑ i : M.refinedBranchIndex, (M.branchWeight psi i : Real)) = 1 := by
    exact_mod_cast M.sum_branchWeight_eq_one psi
  let e := projectiveSourceReferenceEquiv M.refinedBranchIndex A' R
  let tauGrouped := tauState.reindex e
  have hfeasible :
      State.ConditionalMinEntropyFeasible (a := Prod A' M.refinedBranchIndex)
        tauGrouped sigmaR (log2 (Fintype.card A' : Real)) := by
    simpa only [tauGrouped, e] using
      projectiveRecorded_conditionalMinEntropyFeasible
        tauState sigmaR (fun i => (M.branchWeight psi i : Real))
        hweightsNonneg hweightsSum (log2 (Fintype.card A' : Real)) hblocks
  have hlogLe :
      log2 (Fintype.card A' : Real) ≤ tauGrouped.conditionalMinEntropy := by
    rw [State.conditionalMinEntropy_eq]
    exact le_csSup
      (State.conditionalMinEntropyFeasibleExponentValueSet_bddAbove
        (a := Prod A' M.refinedBranchIndex) tauGrouped)
      ⟨sigmaR, hfeasible⟩
  rw [← htauStateToSubnormalized] at hcoherentBall
  have hgroupedBallRaw :=
    State.toSubnormalized_purifiedBall_reindex e hcoherentBall
  have hgroupedBall :
      (M.coherentSourceReferenceState psi).purifiedBall epsilon
        tauGrouped.toSubnormalized := by
    dsimp only [rhoProjective] at hgroupedBallRaw
    rw [M.coherentProjectiveSourceReferenceState_reindex_toSubnormalized psi]
      at hgroupedBallRaw
    simpa only [tauGrouped] using hgroupedBallRaw
  have hcandCoherent :
      SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw
        (a := Prod A' M.refinedBranchIndex)
        (M.coherentSourceReferenceState psi) epsilon
        tauGrouped.conditionalMinEntropy := by
    refine ⟨tauGrouped.toSubnormalized, hgroupedBall, ?_⟩
    exact (State.toSubnormalized_conditionalMinEntropyRaw_eq
      (a := Prod A' M.refinedBranchIndex) tauGrouped).symm
  obtain ⟨h', hcandInput, hle⟩ :=
    M.coherentSourceReferenceCandidate_compress psi hepsilon hcandCoherent
  exact ⟨h', hcandInput, hlogLe.trans hle⟩

end FiniteInstrument

end

end QIT
