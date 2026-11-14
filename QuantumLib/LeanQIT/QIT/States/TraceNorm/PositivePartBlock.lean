/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.TraceNorm.PositivePart
public import QIT.Util.BlockMatrix

/-!
# Positive-part spectral block API

This module packages the positive/nonpositive spectral split determined by
`positiveSpectralProjector`, identifies the diagonal blocks with the positive
and negative CFC parts of a Hermitian matrix, and proves the terminal
trace-nonnegativity closure used by the Appendix A block argument.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Eigenvalue indices on which a Hermitian matrix is strictly positive. -/
abbrev positiveSpectralIndex (H : CMatrix a) (hH : H.IsHermitian) : Type u :=
  {i : a // 0 < hH.eigenvalues i}

/-- Eigenvalue indices on which a Hermitian matrix is nonpositive. -/
abbrev nonpositiveSpectralIndex (H : CMatrix a) (hH : H.IsHermitian) : Type u :=
  {i : a // ¬ 0 < hH.eigenvalues i}

/-- Reindex the eigenvalue index type by the positive/nonpositive spectral split. -/
def spectralSignIndexEquiv (H : CMatrix a) (hH : H.IsHermitian) :
    Sum (positiveSpectralIndex H hH) (nonpositiveSpectralIndex H hH) ≃ a :=
  Equiv.sumCompl fun i : a => 0 < hH.eigenvalues i

/-- Conjugate a matrix into the Hermitian eigenbasis of `H`. -/
def hermitianEigenbasisConjugate (H : CMatrix a) (hH : H.IsHermitian)
    (X : CMatrix a) : CMatrix a :=
  star (hH.eigenvectorUnitary : CMatrix a) * X * (hH.eigenvectorUnitary : CMatrix a)

/-- Reindex the Hermitian eigenbasis by positive and nonpositive eigenvalue indices. -/
def spectralSignBlockMatrix (H : CMatrix a) (hH : H.IsHermitian)
    (X : CMatrix a) :
    CMatrix (Sum (positiveSpectralIndex H hH) (nonpositiveSpectralIndex H hH)) :=
  (hermitianEigenbasisConjugate H hH X).submatrix
    (spectralSignIndexEquiv H hH) (spectralSignIndexEquiv H hH)

/-- Lift a positive/nonpositive spectral block matrix back to the original coordinates. -/
def spectralSignUnblockMatrix (H : CMatrix a) (hH : H.IsHermitian)
    (B : CMatrix (Sum (positiveSpectralIndex H hH) (nonpositiveSpectralIndex H hH))) :
    CMatrix a :=
  (hH.eigenvectorUnitary : CMatrix a) *
    B.submatrix (spectralSignIndexEquiv H hH).symm (spectralSignIndexEquiv H hH).symm *
      star (hH.eigenvectorUnitary : CMatrix a)

private theorem trace_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M : Matrix κ κ ℂ) :
    (M.submatrix e e).trace = M.trace := by
  rw [Matrix.trace, Matrix.trace]
  exact Fintype.sum_equiv e (fun i : ι => M (e i) (e i)) (fun j : κ => M j j)
    (fun _ => rfl)

/-- Trace is preserved by the sign reindexing and eigenbasis conjugation. -/
theorem spectralSignBlockMatrix_trace (H : CMatrix a) (hH : H.IsHermitian)
    (X : CMatrix a) :
    (spectralSignBlockMatrix H hH X).trace = X.trace := by
  unfold spectralSignBlockMatrix hermitianEigenbasisConjugate
  rw [trace_submatrix_equiv (spectralSignIndexEquiv H hH)]
  calc
    (star (hH.eigenvectorUnitary : CMatrix a) * X *
        (hH.eigenvectorUnitary : CMatrix a)).trace =
        ((hH.eigenvectorUnitary : CMatrix a) *
          star (hH.eigenvectorUnitary : CMatrix a) * X).trace := by
          rw [Matrix.trace_mul_cycle]
    _ = X.trace := by simp

/-- Trace is preserved by lifting a sign-block matrix back to original coordinates. -/
theorem spectralSignUnblockMatrix_trace (H : CMatrix a) (hH : H.IsHermitian)
    (B : CMatrix (Sum (positiveSpectralIndex H hH) (nonpositiveSpectralIndex H hH))) :
    (spectralSignUnblockMatrix H hH B).trace = B.trace := by
  unfold spectralSignUnblockMatrix
  rw [Matrix.trace_mul_cycle]
  simp [trace_submatrix_equiv (spectralSignIndexEquiv H hH).symm]

/-- The sign-block matrix is recovered from its four blocks. -/
theorem spectralSignBlockMatrix_blockDecomposition (H : CMatrix a) (hH : H.IsHermitian)
    (X : CMatrix a) :
    Matrix.fromBlocks
        (Matrix.sumBlock11 (spectralSignBlockMatrix H hH X))
        (Matrix.sumBlock12 (spectralSignBlockMatrix H hH X))
        (Matrix.sumBlock21 (spectralSignBlockMatrix H hH X))
        (Matrix.sumBlock22 (spectralSignBlockMatrix H hH X)) =
      spectralSignBlockMatrix H hH X :=
  Matrix.fromBlocks_sumBlocks _

/-- The positive diagonal block, equivalently the restriction of `H⁺`. -/
def positiveEigenvalueBlock (H : CMatrix a) (hH : H.IsHermitian) :
    CMatrix (positiveSpectralIndex H hH) :=
  Matrix.diagonal fun i => ((hH.eigenvalues i.1 : ℝ) : ℂ)

/-- The PSD negative-part block, with diagonal entries `-min λ 0` on nonpositive eigenvalues. -/
def negativeEigenvalueBlock (H : CMatrix a) (hH : H.IsHermitian) :
    CMatrix (nonpositiveSpectralIndex H hH) :=
  Matrix.diagonal fun i => ((-hH.eigenvalues i.1 : ℝ) : ℂ)

/-- The positive eigenvalue block is positive semidefinite. -/
theorem positiveEigenvalueBlock_posSemidef (H : CMatrix a) (hH : H.IsHermitian) :
    (positiveEigenvalueBlock H hH).PosSemidef := by
  rw [positiveEigenvalueBlock, Matrix.posSemidef_diagonal_iff]
  intro i
  exact_mod_cast i.2.le

/-- The nonpositive-side negative-part block is positive semidefinite. -/
theorem negativeEigenvalueBlock_posSemidef (H : CMatrix a) (hH : H.IsHermitian) :
    (negativeEigenvalueBlock H hH).PosSemidef := by
  rw [negativeEigenvalueBlock, Matrix.posSemidef_diagonal_iff]
  intro i
  have hi : hH.eigenvalues i.1 ≤ 0 := le_of_not_gt i.2
  exact_mod_cast (neg_nonneg.mpr hi)

private theorem real_negPart_eq_if (x : ℝ) : x⁻ = if 0 < x then 0 else -x := by
  rw [_root_.negPart_def]
  split_ifs with hx
  · have hx0 : 0 ≤ x := hx.le
    simp [hx0]
  · have hx0 : x ≤ 0 := le_of_not_gt hx
    simp [hx0]

private theorem posPart_spectral_decomposition (H : CMatrix a) (hH : H.IsHermitian) :
    H⁺ =
      (hH.eigenvectorUnitary : CMatrix a) *
        Matrix.diagonal (fun i => (((hH.eigenvalues i)⁺ : ℝ) : ℂ)) *
          star (hH.eigenvectorUnitary : CMatrix a) := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc]
  rw [hH.cfc_eq]
  rw [Matrix.IsHermitian.cfc]
  simp [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.mul_assoc]

private theorem negPart_spectral_decomposition (H : CMatrix a) (hH : H.IsHermitian) :
    H⁻ =
      (hH.eigenvectorUnitary : CMatrix a) *
        Matrix.diagonal (fun i => (((hH.eigenvalues i)⁻ : ℝ) : ℂ)) *
          star (hH.eigenvectorUnitary : CMatrix a) := by
  rw [CFC.negPart_def, cfcₙ_eq_cfc]
  rw [hH.cfc_eq]
  rw [Matrix.IsHermitian.cfc]
  simp [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.mul_assoc]

private theorem hermitianEigenbasisConjugate_posPart
    (H : CMatrix a) (hH : H.IsHermitian) :
    hermitianEigenbasisConjugate H hH H⁺ =
      Matrix.diagonal (fun i => (((hH.eigenvalues i)⁺ : ℝ) : ℂ)) := by
  rw [posPart_spectral_decomposition H hH]
  unfold hermitianEigenbasisConjugate
  let U : CMatrix a := hH.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => (((hH.eigenvalues i)⁺ : ℝ) : ℂ)
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hH.eigenvectorUnitary]
  change star U * (U * D * star U) * U = D
  calc
    star U * (U * D * star U) * U =
        (star U * U) * D * (star U * U) := by noncomm_ring
    _ = 1 * D * 1 := by rw [hU]
    _ = D := by simp

private theorem hermitianEigenbasisConjugate_negPart
    (H : CMatrix a) (hH : H.IsHermitian) :
    hermitianEigenbasisConjugate H hH H⁻ =
      Matrix.diagonal (fun i => (((hH.eigenvalues i)⁻ : ℝ) : ℂ)) := by
  rw [negPart_spectral_decomposition H hH]
  unfold hermitianEigenbasisConjugate
  let U : CMatrix a := hH.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => (((hH.eigenvalues i)⁻ : ℝ) : ℂ)
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hH.eigenvectorUnitary]
  change star U * (U * D * star U) * U = D
  calc
    star U * (U * D * star U) * U =
        (star U * U) * D * (star U * U) := by noncomm_ring
    _ = 1 * D * 1 := by rw [hU]
    _ = D := by simp

private theorem projector_spectral_diagonal (H : CMatrix a) (hH : H.IsHermitian) :
    positiveSpectralProjector H hH =
      (hH.eigenvectorUnitary : CMatrix a) *
        Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0) *
          star (hH.eigenvectorUnitary : CMatrix a) :=
  rfl

/-- Left selection of the positive part by the positive spectral projector. -/
theorem positiveSpectralProjector_mul_posPart (H : CMatrix a) (hH : H.IsHermitian) :
    positiveSpectralProjector H hH * H⁺ = H⁺ := by
  classical
  rw [projector_spectral_diagonal H hH, posPart_spectral_decomposition H hH]
  let U : CMatrix a := hH.eigenvectorUnitary
  let P : CMatrix a := Matrix.diagonal fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0
  let D : CMatrix a := Matrix.diagonal fun i => (((hH.eigenvalues i)⁺ : ℝ) : ℂ)
  have hPD : P * D = D := by
    change
      Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0) *
          Matrix.diagonal (fun i => (((hH.eigenvalues i)⁺ : ℝ) : ℂ)) =
        Matrix.diagonal (fun i => (((hH.eigenvalues i)⁺ : ℝ) : ℂ))
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : 0 < hH.eigenvalues i
      · simp [hi, real_posPart_eq_if]
      · simp [hi, real_posPart_eq_if]
    · simp [Matrix.diagonal, hij]
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hH.eigenvectorUnitary]
  change (U * P * star U) * (U * D * star U) = U * D * star U
  calc
    (U * P * star U) * (U * D * star U) =
        U * P * (star U * U) * D * star U := by noncomm_ring
    _ = U * P * 1 * D * star U := by rw [hU]
    _ = U * (P * D) * star U := by noncomm_ring
    _ = U * D * star U := by rw [hPD]

/-- Right selection of the positive part by the positive spectral projector. -/
theorem posPart_mul_positiveSpectralProjector (H : CMatrix a) (hH : H.IsHermitian) :
    H⁺ * positiveSpectralProjector H hH = H⁺ := by
  classical
  rw [projector_spectral_diagonal H hH, posPart_spectral_decomposition H hH]
  let U : CMatrix a := hH.eigenvectorUnitary
  let P : CMatrix a := Matrix.diagonal fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0
  let D : CMatrix a := Matrix.diagonal fun i => (((hH.eigenvalues i)⁺ : ℝ) : ℂ)
  have hDP : D * P = D := by
    change
      Matrix.diagonal (fun i => (((hH.eigenvalues i)⁺ : ℝ) : ℂ)) *
          Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0) =
        Matrix.diagonal (fun i => (((hH.eigenvalues i)⁺ : ℝ) : ℂ))
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : 0 < hH.eigenvalues i
      · simp [hi, real_posPart_eq_if]
      · simp [hi, real_posPart_eq_if]
    · simp [Matrix.diagonal, hij]
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hH.eigenvectorUnitary]
  change (U * D * star U) * (U * P * star U) = U * D * star U
  calc
    (U * D * star U) * (U * P * star U) =
        U * D * (star U * U) * P * star U := by noncomm_ring
    _ = U * D * 1 * P * star U := by rw [hU]
    _ = U * (D * P) * star U := by noncomm_ring
    _ = U * D * star U := by rw [hDP]

/-- Left annihilation of the negative part by the positive spectral projector. -/
theorem positiveSpectralProjector_mul_negPart (H : CMatrix a) (hH : H.IsHermitian) :
    positiveSpectralProjector H hH * H⁻ = 0 := by
  classical
  rw [projector_spectral_diagonal H hH, negPart_spectral_decomposition H hH]
  let U : CMatrix a := hH.eigenvectorUnitary
  let P : CMatrix a := Matrix.diagonal fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0
  let D : CMatrix a := Matrix.diagonal fun i => (((hH.eigenvalues i)⁻ : ℝ) : ℂ)
  have hPD : P * D = 0 := by
    change
      Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0) *
          Matrix.diagonal (fun i => (((hH.eigenvalues i)⁻ : ℝ) : ℂ)) =
        0
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : 0 < hH.eigenvalues i
      · simp [hi, real_negPart_eq_if]
      · simp [hi, Matrix.diagonal]
    · simp [Matrix.diagonal, hij]
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hH.eigenvectorUnitary]
  change (U * P * star U) * (U * D * star U) = 0
  calc
    (U * P * star U) * (U * D * star U) =
        U * P * (star U * U) * D * star U := by noncomm_ring
    _ = U * P * 1 * D * star U := by rw [hU]
    _ = U * (P * D) * star U := by noncomm_ring
    _ = 0 := by rw [hPD]; simp

/-- Right annihilation of the negative part by the positive spectral projector. -/
theorem negPart_mul_positiveSpectralProjector (H : CMatrix a) (hH : H.IsHermitian) :
    H⁻ * positiveSpectralProjector H hH = 0 := by
  classical
  rw [projector_spectral_diagonal H hH, negPart_spectral_decomposition H hH]
  let U : CMatrix a := hH.eigenvectorUnitary
  let P : CMatrix a := Matrix.diagonal fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0
  let D : CMatrix a := Matrix.diagonal fun i => (((hH.eigenvalues i)⁻ : ℝ) : ℂ)
  have hDP : D * P = 0 := by
    change
      Matrix.diagonal (fun i => (((hH.eigenvalues i)⁻ : ℝ) : ℂ)) *
          Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0) =
        0
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : 0 < hH.eigenvalues i
      · simp [hi, real_negPart_eq_if]
      · simp [hi, Matrix.diagonal]
    · simp [Matrix.diagonal, hij]
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hH.eigenvectorUnitary]
  change (U * D * star U) * (U * P * star U) = 0
  calc
    (U * D * star U) * (U * P * star U) =
        U * D * (star U * U) * P * star U := by noncomm_ring
    _ = U * D * 1 * P * star U := by rw [hU]
    _ = U * (D * P) * star U := by noncomm_ring
    _ = 0 := by rw [hDP]; simp

/-- The sign-block transform preserves Hermitian matrices. -/
theorem spectralSignBlockMatrix_isHermitian (H : CMatrix a) (hH : H.IsHermitian)
    {X : CMatrix a} (hX : X.IsHermitian) :
    (spectralSignBlockMatrix H hH X).IsHermitian := by
  unfold spectralSignBlockMatrix hermitianEigenbasisConjugate
  rw [Matrix.star_eq_conjTranspose (hH.eigenvectorUnitary : CMatrix a)]
  exact (Matrix.isHermitian_conjTranspose_mul_mul
    (hH.eigenvectorUnitary : CMatrix a) hX).submatrix _

/-- The positive block of the sign-split `H⁺` is the positive eigenvalue block. -/
theorem sumBlock11_spectralSignBlockMatrix_posPart
    (H : CMatrix a) (hH : H.IsHermitian) :
    Matrix.sumBlock11 (spectralSignBlockMatrix H hH H⁺) =
      positiveEigenvalueBlock H hH := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    unfold Matrix.sumBlock11 spectralSignBlockMatrix positiveEigenvalueBlock
    rw [hermitianEigenbasisConjugate_posPart H hH]
    simp [Matrix.diagonal, spectralSignIndexEquiv, Equiv.sumCompl_apply_inl,
      real_posPart_eq_if, i.2]
  · unfold Matrix.sumBlock11 spectralSignBlockMatrix positiveEigenvalueBlock
    rw [hermitianEigenbasisConjugate_posPart H hH]
    have hijcoe : (i : a) ≠ (j : a) := by
      intro h
      exact hij (Subtype.ext h)
    simp [Matrix.diagonal, spectralSignIndexEquiv, Equiv.sumCompl_apply_inl, hij, hijcoe]

/-- The nonpositive block of the sign-split `H⁻` is the PSD negative eigenvalue block. -/
theorem sumBlock22_spectralSignBlockMatrix_negPart
    (H : CMatrix a) (hH : H.IsHermitian) :
    Matrix.sumBlock22 (spectralSignBlockMatrix H hH H⁻) =
      negativeEigenvalueBlock H hH := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    unfold Matrix.sumBlock22 spectralSignBlockMatrix negativeEigenvalueBlock
    rw [hermitianEigenbasisConjugate_negPart H hH]
    have hi : ¬ 0 < hH.eigenvalues i.1 := i.2
    simp [Matrix.diagonal, spectralSignIndexEquiv, Equiv.sumCompl_apply_inr,
      real_negPart_eq_if, hi]
  · unfold Matrix.sumBlock22 spectralSignBlockMatrix negativeEigenvalueBlock
    rw [hermitianEigenbasisConjugate_negPart H hH]
    have hijcoe : (i : a) ≠ (j : a) := by
      intro h
      exact hij (Subtype.ext h)
    simp [Matrix.diagonal, spectralSignIndexEquiv, Equiv.sumCompl_apply_inr, hij, hijcoe]

variable {p : Type v} {n : Type w} [Fintype p] [Fintype n]

/-- Terminal block trace nonnegativity with the exact Appendix A expression shape. -/
theorem positiveSpectralTerminalTrace_nonneg
    (DeltaPos : Matrix p p ℂ) (DeltaNeg : Matrix n n ℂ)
    (V12 : Matrix p n ℂ) (V21 : Matrix n p ℂ)
    (hPos : DeltaPos.PosSemidef) (hNeg : DeltaNeg.PosSemidef)
    (hAdj : V21 = Matrix.conjTranspose V12) :
    0 ≤ ((DeltaPos * V12 * V21 + V12 * DeltaNeg * V21).trace).re := by
  have hFirstPSD : (V21 * DeltaPos * V12).PosSemidef := by
    rw [hAdj]
    exact hPos.conjTranspose_mul_mul_same V12
  have hFirst :
      0 ≤ ((DeltaPos * V12 * V21).trace).re := by
    rw [Matrix.trace_mul_cycle]
    exact (Matrix.PosSemidef.trace_nonneg hFirstPSD).1
  have hSecondPSD : (V12 * DeltaNeg * V21).PosSemidef := by
    rw [hAdj]
    exact hNeg.mul_mul_conjTranspose_same V12
  have hSecond :
      0 ≤ ((V12 * DeltaNeg * V21).trace).re :=
    (Matrix.PosSemidef.trace_nonneg hSecondPSD).1
  rw [Matrix.trace_add, Complex.add_re]
  exact add_nonneg hFirst hSecond

/-- The terminal block expression owned by the positive/nonpositive split of `H`. -/
def appendixATerminalBlock (H V : CMatrix a) (hH : H.IsHermitian) :
    CMatrix (positiveSpectralIndex H hH) :=
  positiveEigenvalueBlock H hH *
      Matrix.sumBlock12 (spectralSignBlockMatrix H hH V) *
        Matrix.sumBlock21 (spectralSignBlockMatrix H hH V) +
    Matrix.sumBlock12 (spectralSignBlockMatrix H hH V) *
      negativeEigenvalueBlock H hH *
        Matrix.sumBlock21 (spectralSignBlockMatrix H hH V)

/-- The same terminal expression, lifted back through the sign reindexing and eigenbasis unitary. -/
def appendixATerminalOriginal (H V : CMatrix a) (hH : H.IsHermitian) : CMatrix a :=
  spectralSignUnblockMatrix H hH
    (Matrix.sumBlockEmbed11
      (β := nonpositiveSpectralIndex H hH)
      (appendixATerminalBlock H V hH))

/-- The original-coordinate terminal trace is the sign-block terminal trace. -/
theorem appendixATerminalOriginal_trace_eq_block
    (H V : CMatrix a) (hH : H.IsHermitian) (_hV : V.IsHermitian) :
    ((appendixATerminalOriginal H V hH).trace).re =
      ((positiveEigenvalueBlock H hH *
          Matrix.sumBlock12 (spectralSignBlockMatrix H hH V) *
          Matrix.sumBlock21 (spectralSignBlockMatrix H hH V) +
        Matrix.sumBlock12 (spectralSignBlockMatrix H hH V) *
          negativeEigenvalueBlock H hH *
          Matrix.sumBlock21 (spectralSignBlockMatrix H hH V)).trace).re := by
  unfold appendixATerminalOriginal appendixATerminalBlock
  rw [spectralSignUnblockMatrix_trace, Matrix.trace_sumBlockEmbed11]

/-- Closure theorem for the Appendix A terminal trace expression. -/
theorem positiveSpectralTerminalTrace_original_nonneg
    (H V : CMatrix a) (hH : H.IsHermitian) (hV : V.IsHermitian) :
    0 ≤ ((appendixATerminalOriginal H V hH).trace).re := by
  rw [appendixATerminalOriginal_trace_eq_block H V hH hV]
  let B := spectralSignBlockMatrix H hH V
  have hB : B.IsHermitian := spectralSignBlockMatrix_isHermitian H hH hV
  exact positiveSpectralTerminalTrace_nonneg
    (positiveEigenvalueBlock H hH)
    (negativeEigenvalueBlock H hH)
    (Matrix.sumBlock12 B)
    (Matrix.sumBlock21 B)
    (positiveEigenvalueBlock_posSemidef H hH)
    (negativeEigenvalueBlock_posSemidef H hH)
    (Matrix.sumBlock21_eq_conjTranspose_sumBlock12_of_isHermitian hB)

end

end QIT
